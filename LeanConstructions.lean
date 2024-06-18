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

def getLevelC (e : Expr) : MetaM Level := do
  let type ← inferType e
  let type ← ofExceptKernelException (Kernel.whnf (← getEnv) (← getLCtx) type)
  match type with
  | .sort lvl => return lvl
  | _ => throwError "not a type"

def mkPProd (e1 e2 : Expr) : MetaM Expr := do
  let lvl1 ← getLevel e1
  let lvl2 ← getLevel e2
  if lvl1 matches .zero && lvl2 matches .zero then
    return mkApp2 (.const `And []) e1 e2
  else
    return mkApp2 (.const ``PProd [lvl1, lvl2]) e1 e2

def mkNProd (lvl : Level) (es : Array Expr) : MetaM Expr :=
  if let .zero := lvl then
    es.foldrM (init := .const ``True []) mkPProd
  else
    es.foldrM (init := .const ``PUnit [lvl]) mkPProd

def withModifyFVarCodomain (e : Expr) (fvar : Expr) (k : MetaM α) : MetaM α := do
  let type ← forallTelescope (← inferType fvar) fun args _ => mkForallFVars args e
  let lctx := (← getLCtx).modifyLocalDecl fvar.fvarId! fun decl => decl.setType type
  withReader (fun ctx => { ctx with lctx := lctx }) k

def withModifyFVarsCodomain (e : Expr) (fvars : Array Expr) (k : MetaM α) : MetaM α :=
  fvars.foldr (init := k) fun fvar k => withModifyFVarCodomain e fvar k

def buildMinorPremise (rlvl : Level) (typeFormers : Array Expr) (args : Array Expr) : MetaM Expr :=
  go args 0 #[]
where
  ibelow := rlvl matches .zero
  -- e0 := if ibelow then .const ``True [] else .const ``PUnit [rlvl]
  go (args : Array Expr) (i : Nat) (prods : Array Expr) : MetaM Expr := do
    if h : i < args.size then
      let arg := args[i]
      let argType ← inferType arg
      forallTelescope argType fun arg_args arg_type => do
        if typeFormers.contains arg_type.getAppFn then
          let name ← arg.fvarId!.getUserName
          let type' ← forallTelescope argType fun args _ => mkForallFVars args (.sort rlvl)
          withLocalDeclD name type' fun arg' => do
            let snd ← mkForallFVars arg_args (mkAppN arg' arg_args)
            let e' ← mkPProd argType snd
            go (args.set ⟨i, h⟩ arg') (i + 1) (prods.push e')
        else
          go args (i + 1) prods
    else
      mkLambdaFVars args (← mkNProd rlvl prods)

-- ported from C. TODO: can this be unified with mkLevelMax'?
def mkLevelMaxC (u v : Level) : Level := Id.run do
  if u.isExplicit && v.isExplicit then
     return if u.getOffset ≥ v.getOffset then u else v
  if u == v then return u
  if u.isZero then return v
  if v.isZero then return u
  if let .max v1 v2 := v then
    if u == v1 || u == v2 then return v
  if let .max u1 u2 := u then
    if v == u1 || v == u2 then return u
  if u.getLevelOffset == v.getLevelOffset then
    return if u.getOffset ≥ v.getOffset then u else v
  return .max u v

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
  let .some ilvl ← typeFormerTypeLevel indVal.type
    | throwError "type {indVal.type} of inductive {indVal.name} not a type former?"
  let rlvl : Level :=  -- universe level of the resultant type
    if ibelow then
      0
    else if indVal.isReflexive then
      if let .max 1 lvl := ilvl then
        mkLevelMaxC (.succ lvl) lvl
      else
        mkLevelMaxC (.succ lvl) ilvl
    else
      mkLevelMaxC 1 lvl

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

def eraseLevels (e : Expr) : CoreM Expr := do
  Core.transform (← Core.betaReduce e) (pre := fun
    | .const n _  => return .done (.const n [])
    | .sort _ => return .done (.sort .zero)
    | _ => return .continue)

def checkDefnVal (n : Name) (suffix : String) (f : Name → MetaM DefinitionVal) : MetaM Unit := do
  let n' := .str n suffix
  if (← hasConst n') then
    if let .defnInfo oldVal ← getConstInfo n' then
      let newVal ← f n
      check newVal.type
      check newVal.value
      -- ignore inductives, to not get confused by the `.below` generated for inductive predicates
      unless (← eraseLevels newVal.type) == (← eraseLevels oldVal.type) do
        throwError m!"Mismatch for type of {n'}:{indentExpr oldVal.type}\nvs{indentExpr newVal.type}"
      unless (← eraseLevels newVal.value) == (← eraseLevels oldVal.value) do
        throwError m!"Mismatch for value of {n'}:{indentExpr (← eraseLevels oldVal.value)}\nvs{indentExpr (← eraseLevels newVal.value)}"
      -- unless newVal == oldVal do
        throwError m!"Mismatch for {n'}" -- ":{oldVal}\nvs{newRecOnVal}"

def checkInd (n : Name) : MetaM Unit := do
  let ci ← getConstInfo n
  unless ci.isInductive do throwError m!"Not an inductive: {n}"

  checkDefnVal n "recOn" mkRecOnValDefinitionVal
  checkDefnVal n "below" (mkBelowOrIBelow · false)
  -- checkDefnVal n "ibelow" mkRecOnValDefinitionVal

-- #print Nat.below
run_meta checkInd ``Acc

set_option pp.universes true in
run_meta checkInd ``Nat
