import LeanConstructions
import Mathlib

namespace Lean
open Meta

set_option pp.universes true in
run_meta checkInd ``PSet

set_option pp.all true in
run_meta checkInd ``Lean.Json

run_meta do
  let env ← getEnv
  let mut count := 0
  for (n, ci) in env.constants do
    if ci.isInductive then
      -- IO.eprintln s!"Checking {n}"
      checkInd n
      count := count+1
  logInfo m!"Checked {count} definitions"
