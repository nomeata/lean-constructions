import LeanConstructions
import Mathlib

namespace Lean
open Meta

run_meta checkInd ``PSet

run_meta checkInd ``Lean.Json
run_meta checkInd ``Mathlib.Tactic.Ring.ExSum

run_meta do
  let env ← getEnv
  let mut count := 0
  for (n, ci) in env.constants do
    if ci.isInductive then
      -- IO.eprintln s!"Checking {n}"
      checkInd n
      count := count+1
  logInfo m!"Checked {count} definitions"
