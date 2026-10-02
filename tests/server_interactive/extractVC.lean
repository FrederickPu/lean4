module

/-!
`extract_vc` code action: the edit inserted above the declaration, and applying that edit.
-/

/-- doc -/
@[inline] theorem womp (x : Nat) : x = x := by
  extract_vc
--^ codeAction
--^ sync
--^ codeActionApply: Extract goal as theorem
--^ sync
--^ collectDiagnostics
