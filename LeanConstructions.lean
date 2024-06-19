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

def mkPUnit : Level → Expr
  | .zero => .const ``True []
  | lvl   => .const ``PUnit [lvl]

def mkPProd (e1 e2 : Expr) : MetaM Expr := do
  let lvl1 ← getLevel e1
  let lvl2 ← getLevel e2
  if lvl1 matches .zero && lvl2 matches .zero then
    return mkApp2 (.const `And []) e1 e2
  else
    return mkApp2 (.const ``PProd [lvl1, lvl2]) e1 e2

def mkNProd (lvl : Level) (es : Array Expr) : MetaM Expr :=
  es.foldrM (init := mkPUnit lvl) mkPProd

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
        mkLevelMax' (.succ lvl) lvl
      else
        mkLevelMax' (.succ lvl) ilvl
    else
      mkLevelMax' 1 lvl

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
