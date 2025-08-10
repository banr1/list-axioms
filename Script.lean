import Lean
open Lean Elab Command

/-- 現在の環境にある「本物の axiom」だけを列挙） -/
elab "#list_axioms" : command => do
  let env ← getEnv
  let mut n := 0
  for (c, info) in env.constants.toList do
    if info.isAxiom then
      n := n + 1
      logInfo m!"{c}"
  logInfo m!"(total: {n})"

#list_axioms
