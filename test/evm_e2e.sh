#!/usr/bin/env bash
# End-to-end test for Lemma EVM codegen output.
# Deploys the generated ERC-20 bytecode to anvil and verifies mint / totalSupply / balanceOf.
#
# Requirements: foundry (anvil, cast) on PATH.
# Usage: ./test/evm_e2e.sh
set -euo pipefail

# ── Config ───────────────────────────────────────────────────────────────────

RPC_URL="http://127.0.0.1:8545"
PRIVATE_KEY="0xac0974bec39a17e36ba4a6b4d238ff944bacb478cbed5efcae784d7bf4f2ff80"
DEAD="0x000000000000000000000000000000000000dead"

# Extract creation bytecode dynamically from Lean build
echo "Building Lean to extract bytecode..."
BYTECODE=$("$HOME/.elan/bin/lake" env lean --run Lemma/EVM/Hex.lean 2>/dev/null || true)
BYTECODE=$(echo "$BYTECODE" | head -1)
if [[ -z "$BYTECODE" || "$BYTECODE" == ERROR* ]]; then
  echo "FATAL: could not extract bytecode from Lean build"
  exit 1
fi

PASS=0
FAIL=0

# ── Helpers ──────────────────────────────────────────────────────────────────

cleanup() {
  if [[ -n "${ANVIL_PID:-}" ]]; then
    kill "$ANVIL_PID" 2>/dev/null || true
    wait "$ANVIL_PID" 2>/dev/null || true
  fi
}
trap cleanup EXIT

assert_eq() {
  local label="$1" expected="$2" actual="$3"
  if [[ "$actual" == "$expected" ]]; then
    echo "  PASS  $label (got $actual)"
    PASS=$((PASS + 1))
  else
    echo "  FAIL  $label (expected $expected, got $actual)"
    FAIL=$((FAIL + 1))
  fi
}

# ── Start anvil ──────────────────────────────────────────────────────────────

if cast chain-id --rpc-url "$RPC_URL" &>/dev/null; then
  echo "FATAL: port 8545 already in use"
  exit 1
fi

echo "Starting anvil..."
anvil &>/dev/null &
ANVIL_PID=$!

# Wait for anvil to accept connections (up to 5 s)
for _ in $(seq 1 10); do
  if cast chain-id --rpc-url "$RPC_URL" &>/dev/null; then break; fi
  sleep 0.5
done

if ! cast chain-id --rpc-url "$RPC_URL" &>/dev/null; then
  echo "FATAL: anvil did not start"
  exit 1
fi
echo "Anvil ready (pid $ANVIL_PID)."

# ── Deploy ───────────────────────────────────────────────────────────────────

echo ""
echo "Deploying contract..."
CONTRACT=$(cast send --rpc-url "$RPC_URL" \
  --private-key "$PRIVATE_KEY" \
  --create "$BYTECODE" --json 2>&1 | jq -r '.contractAddress')

if [[ -z "$CONTRACT" || "$CONTRACT" == "null" ]]; then
  echo "FATAL: deployment failed — no contract address"
  exit 1
fi
echo "Contract deployed at $CONTRACT"

# ── Mint 100 to 0x...dead ───────────────────────────────────────────────────

echo ""
echo "Minting 100 to $DEAD ..."
cast send --rpc-url "$RPC_URL" \
  --private-key "$PRIVATE_KEY" \
  "$CONTRACT" "mint(address,uint256)" "$DEAD" 100 &>/dev/null

TOTAL=$(cast call --rpc-url "$RPC_URL" "$CONTRACT" "totalSupply()(uint256)")
BAL=$(cast call --rpc-url "$RPC_URL" "$CONTRACT" "balanceOf(address)(uint256)" "$DEAD")

assert_eq "totalSupply after first mint" "100" "$TOTAL"
assert_eq "balanceOf(dead) after first mint" "100" "$BAL"

# ── Mint 50 more — verify accumulation ───────────────────────────────────────

echo ""
echo "Minting 50 more to $DEAD ..."
cast send --rpc-url "$RPC_URL" \
  --private-key "$PRIVATE_KEY" \
  "$CONTRACT" "mint(address,uint256)" "$DEAD" 50 &>/dev/null

TOTAL=$(cast call --rpc-url "$RPC_URL" "$CONTRACT" "totalSupply()(uint256)")
BAL=$(cast call --rpc-url "$RPC_URL" "$CONTRACT" "balanceOf(address)(uint256)" "$DEAD")

assert_eq "totalSupply after second mint" "150" "$TOTAL"
assert_eq "balanceOf(dead) after second mint" "150" "$BAL"

# ── Summary ──────────────────────────────────────────────────────────────────

echo ""
echo "════════════════════════════════════════"
echo "  Results: $PASS passed, $FAIL failed"
echo "════════════════════════════════════════"

if [[ "$FAIL" -gt 0 ]]; then
  exit 1
fi
