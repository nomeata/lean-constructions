import Lean

open Lean Meta

def mkDefinitionValInferrringUnsafe (name : Name) (levelParams : List Name) (type : Expr)
    (value : Expr) : MetaM DefinitionVal := do
  let env ← getEnv
  return {
    name, levelParams, type, value,
    hints := ReducibilityHints.abbrev
    safety := if env.hasUnsafe type || env.hasUnsafe value then DefinitionSafety.unsafe else DefinitionSafety.safe
  }

def mkRecOnValDefinitionVal (n : Name) : MetaM DefinitionVal := do
  let .recInfo recInfo ← getConstInfo (mkRecName n)
    | throwError "{mkRecName n} not a recinfo"
  forallTelescope recInfo.type fun xs t => do
    let e := .const recInfo.name (recInfo.levelParams.map (.param ·))
    let e := mkAppN e xs
    -- We reorder the parameters
    -- before: As Cs minor_premises indices major-premise
    -- fow:    As Cs indices major-premise minor-premises
    let AC_size := xs.size - recInfo.numMinors - recInfo.numIndices - 1
    let vs :=
      xs[:AC_size] ++
      xs[AC_size + recInfo.numMinors:AC_size + recInfo.numMinors + 1 + recInfo.numIndices] ++
      xs[AC_size:AC_size + recInfo.numMinors]
    let type ← mkForallFVars vs t
    let value ← mkLambdaFVars vs e
    mkDefinitionValInferrringUnsafe (mkRecOnName n) recInfo.levelParams type value

def mkPProd (prop : Bool) (e1 e2 : Expr) : MetaM Expr :=
  if prop then
    mkAppM ``And #[e1, e2]
  else
    mkAppM ``PProd #[e1, e2]

def mkNProd (lvl : Level) (es : Array Expr) : MetaM Expr :=
  if let .zero := lvl then
    es.foldrM (init := .const ``True []) (mkPProd true)
  else
    es.foldrM (init := .const ``PUnit [lvl]) (mkPProd false)

def withModifyFVarCodomain (e : Expr) (fvar : Expr) (k : MetaM α) : MetaM α := do
  let type ← forallTelescope (← inferType fvar) fun args _ => mkForallFVars args e
  let lctx := (← getLCtx).modifyLocalDecl fvar.fvarId! fun decl => decl.setType type
  withReader (fun ctx => { ctx with lctx := lctx }) k

def withModifyFVarsCodomain (e : Expr) (fvars : Array Expr) (k : MetaM α) : MetaM α :=
  fvars.foldr (init := k) fun fvar k => withModifyFVarCodomain e fvar k

def buildMinorPremise (rlvl : Level) (typeFormers : Array Expr) (args : Array Expr) : MetaM Expr :=
  go 0 #[]
where
  ibelow := rlvl matches .zero
  -- e0 := if ibelow then .const ``True [] else .const ``PUnit [rlvl]
  go (i : Nat) (prods : Array Expr) : MetaM Expr := do
    if h : i < args.size then
      let arg := args[i]
      let argType ← inferType arg
      forallTelescope argType fun arg_args arg_type => do
        if typeFormers.contains arg_type.getAppFn then
          withModifyFVarCodomain (.sort rlvl) arg do
            let snd ← mkForallFVars arg_args (mkAppN arg arg_args)
            let e' ← mkPProd ibelow argType snd
            go (i + 1) (prods.push e')
        else
          go (i + 1) prods
    else
      mkLambdaFVars args (← mkNProd rlvl prods)


def mkBelowOrIBelow (indName : Name) (ibelow : Bool) : MetaM DefinitionVal := do
  let indVal ← getConstInfoInduct indName
  let recName := mkRecName indName
  let .recInfo recVal ← getConstInfo recName
    | throwError "{recName} not a recinfo"
  let lvl::lvls := recVal.levelParams.map (Level.param ·)
    | throwError "recursor {recName} has no levelParams"
  let lvlParam := recVal.levelParams.head!
  let blvls := -- universe parameter names of ibelow/below
    if ibelow then recVal.levelParams.tail!
              else recVal.levelParams
  let rlvl : Level :=  -- universe level of the resultant type
    if ibelow then 0
    -- TODO: reflexive
              else .max 1 lvl

  let refType :=
    if ibelow then
      recVal.type.instantiateLevelParams [lvlParam] [0]
    else if indVal.isReflexive then
      recVal.type.instantiateLevelParams [lvlParam] [lvl.succ]
    else
      recVal.type
  forallTelescope refType fun refArgs _ => do
    assert! refArgs.size == indVal.numParams + recVal.numMotives + recVal.numMinors + indVal.numIndices + 1
    let params      : Array Expr := refArgs[:indVal.numParams]
    let typeFormers : Array Expr := refArgs[indVal.numParams:indVal.numParams + recVal.numMotives]
    let minors      : Array Expr := refArgs[indVal.numParams + recVal.numMotives:indVal.numParams + recVal.numMotives + recVal.numMinors]
    let remaining   : Array Expr := refArgs[indVal.numParams + recVal.numMotives + recVal.numMinors:]
    let args := params ++ typeFormers ++ remaining

    let mut val := .const recName (rlvl.succ :: lvls)
    -- add parameters
    val := mkAppN val params
    -- add type formers
    for typeFormer in typeFormers do
      let arg ← forallTelescope (← inferType typeFormer) fun targs _ =>
        mkLambdaFVars targs (.sort rlvl)
      val := .app val arg
    -- add minor premises
    for minor in minors do
      let arg ← forallTelescope (← inferType minor) fun minor_args _ => do
        buildMinorPremise rlvl typeFormers minor_args
      val := .app val arg
    -- add indices and major premise
    val := mkAppN val remaining
    let name := if ibelow then .str indName "ibelow" else mkBelowName indName
    let type ← mkForallFVars args (.sort rlvl)
    val ← mkLambdaFVars args val
    mkDefinitionValInferrringUnsafe name blvls type val

deriving instance BEq for ReducibilityHints
deriving instance BEq for DefinitionVal
deriving instance BEq for InductiveVal

def checkDefnVal (n : Name) (suffix : String) (f : Name → MetaM DefinitionVal) : MetaM Unit := do
  let n' := .str n suffix
  if (← hasConst n') then
    if let .defnInfo oldVal ← getConstInfo n' then
      let newVal ← f n
      -- ignore inductives, to not get confused by the `.below` generated for inductive predicates
      unless newVal == oldVal do
        unless newVal.type == oldVal.type do
          throwError m!"Mismatch for type of {n'}:{indentExpr oldVal.type}\nvs{indentExpr newVal.type}"
        unless newVal.value == oldVal.value do
          throwError m!"Mismatch for value of {n'}:{indentExpr oldVal.value}\nvs{indentExpr newVal.value}"
        throwError m!"Mismatch for {n'}" -- ":{oldVal}\nvs{newRecOnVal}"

def checkInd (n : Name) : MetaM Unit := do
  let ci ← getConstInfo n
  unless ci.isInductive do throwError m!"Not an inductive: {n}"

  checkDefnVal n "recOn" mkRecOnValDefinitionVal
  checkDefnVal n "below" (mkBelowOrIBelow · false)
  -- checkDefnVal n "ibelow" mkRecOnValDefinitionVal

-- #print Nat.below
run_meta checkInd ``Acc

set_option pp.explicit true in
run_meta checkInd ``Nat
