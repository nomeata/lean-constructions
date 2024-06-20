import Lean
import LeanConstructions.RecOn
import LeanConstructions.Below

namespace Lean
open Meta

deriving instance BEq for ReducibilityHints
deriving instance BEq for DefinitionVal
deriving instance BEq for InductiveVal

def canon (e : Expr) : CoreM Expr := do
  Core.transform (← Core.betaReduce e) (pre := fun
    | .const n ls  => return .done (.const n (ls.map (·.normalize)))
    | .sort l => return .done (.sort l.normalize)
    | _ => return .continue)

def checkDefnVal (n : Name) (suffix : String) (f : Name → MetaM DefinitionVal) : MetaM Unit := do
  let n' := .str n suffix
  if (← hasConst n') then
    if let .defnInfo oldVal ← getConstInfo n' then
      let newVal ← f n
      check newVal.type
      check newVal.value
      -- ignore inductives, to not get confused by the `.below` generated for inductive predicates
      unless (← canon newVal.type) == (← canon oldVal.type) do
        throwError m!"Mismatch for type of {n'}:{indentExpr oldVal.type}\nvs{indentExpr newVal.type}"
      unless (← canon newVal.value) == (← canon oldVal.value) do
        throwError m!"Mismatch for value of {n'}:{indentExpr (← canon oldVal.value)}\nvs{indentExpr (← canon newVal.value)}"
      -- unless newVal == oldVal do
        throwError m!"Mismatch for {n'}" -- ":{oldVal}\nvs{newRecOnVal}"

def checkInd (n : Name) : MetaM Unit := do
  let ci ← getConstInfo n
  unless ci.isInductive do throwError m!"Not an inductive: {n}"

  checkDefnVal n "recOn" mkRecOnValDefinitionVal
  checkDefnVal n "below" (mkBelowOrIBelow · false)
  checkDefnVal n "ibelow" (mkBelowOrIBelow . true)

-- #print Nat.below
run_meta checkInd ``Acc

set_option pp.universes true in
run_meta checkInd ``Nat
