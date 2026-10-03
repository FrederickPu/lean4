module

/-!
`codeActionApply` applies a code action as selecting it in the editor would. Here it replaces
`simp?` by its suggestion, after which the `Try this` message is gone.
-/

example : True := by simp?
                     --^ collectDiagnostics
                     --^ codeActionApply: simp only
                     --^ collectDiagnostics
