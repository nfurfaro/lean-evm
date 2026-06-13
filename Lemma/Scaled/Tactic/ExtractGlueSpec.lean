import Lean

open Lean Elab Tactic Meta

/-- Extract the current proof goal as a standalone theorem stub.
    Logs the theorem to InfoView and fails so the file doesn't silently compile. -/
elab "extract_glue_spec" : tactic => withMainContext do
  let goalType ← getMainTarget
  let lctx ← getLCtx
  let mut params : Array String := #[]
  for decl in lctx do
    if decl.isAuxDecl then continue
    let name := toString decl.userName
    let ty := toString (← ppExpr decl.type)
    match decl.binderInfo with
    | .instImplicit =>
      params := params.push s!"[{ty}]"
    | .implicit | .strictImplicit =>
      params := params.push <| "{" ++ name ++ " : " ++ ty ++ "}"
    | _ =>
      params := params.push s!"({name} : {ty})"
  let goalStr := toString (← ppExpr goalType)
  let paramBlock := "\n    ".intercalate params.toList
  logInfo m!"theorem glue_spec\n    {paramBlock}\n    : {goalStr} := by\n  sorry"
  throwError "extract_glue_spec: spec extracted, proof needed"
