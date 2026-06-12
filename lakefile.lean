import Lake
open Lake DSL

package «lean-evm» where
  leanOptions := #[⟨`autoImplicit, false⟩]

-- Pinned to the rev compatible with lean4 v4.29.0-rc1 (see lean-toolchain).
require «mathlib» from git
  "https://github.com/leanprover-community/mathlib4" @ "a274af57fd3b68064ab1c8d31e3980547e58a656"

@[default_target]
lean_lib «Lemma» where
  srcDir := "."
  -- Build every module under Lemma/ (EVM semantics, codegen, proofs + the
  -- two Scaled files the ledger-bridge theorems depend on).
  globs := #[Glob.submodules `Lemma]
