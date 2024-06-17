import LeanConstructions
import Mathlib

open Lean Meta

deriving instance BEq for ReducibilityHints
deriving instance BEq for DefinitionVal

run_meta do
  let env ← getEnv
  let mut count := 0
  for (n, ci) in env.constants do
    if ci.isInductive then
      let recOnName := mkRecOnName n
      unless env.contains  recOnName do
        -- happens on .below and ._impl inductives. how to filter them?
        -- logInfo m!"Missing {recOnName}"
        continue

      let newRecOnVal ← mkRecOnValDefinitionVal n
      let oldVal ← getConstInfoDefn recOnName
      unless newRecOnVal == oldVal  do
        throwError m!"Mismatch for {n}" -- ":{oldVal}\nvs{newRecOnVal}"
      count := count+1
  logInfo m!"Checked {count} definitions"

  return ()
