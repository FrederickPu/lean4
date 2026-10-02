module

/-!
Clicking a `Try this` suggestion from the command line.

`codeActionApply` applies the same workspace edit as the lightbulb and as the `[apply]` button on
a tactic or library suggestion. `simp?` is the smallest such suggestion.
-/

example : True := by simp?
                     --^ codeActionApply: simp only
                     --^ sync
                     --^ collectDiagnostics
