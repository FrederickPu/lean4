/-!
`extract_goal into M` fails on a goal whose statement uses notation that is local to this file, and
then offers no code action.
-/

def twice (n : Nat) := n + n

local notation "dbl! " n:max => twice n

example (n : Nat) : dbl! n = n + n := by
  extract_goal into Example.VCs
--^ codeAction
