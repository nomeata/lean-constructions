import LeanConstructions
import Mathlib

open Lean Meta

run_meta do
  let env ← getEnv
  let mut count := 0
  for (n, ci) in env.constants do
    if ci.isInductive then
      -- IO.eprintln s!"Checking {n}"
      checkInd n
      count := count+1
  logInfo m!"Checked {count} definitions"
