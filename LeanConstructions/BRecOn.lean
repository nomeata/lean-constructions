/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Joachim Breitner
-/
prelude
import LeanConstructions.Utils
import Lean.Meta.InferType

namespace Lean
open Meta

private def mkPUnit : Level → Expr
  | .zero => .const ``True []
  | lvl   => .const ``PUnit [lvl]

private def mkPUnitMk : Level → Expr
  | .zero => .const ``True.intro []
  | lvl   => .const ``PUnit.unit [lvl]

private def mkPProd (e1 e2 : Expr) : MetaM Expr := do
  let lvl1 ← getLevel e1
  let lvl2 ← getLevel e2
  if lvl1 matches .zero && lvl2 matches .zero then
    return mkApp2 (.const `And []) e1 e2
  else
    return mkApp2 (.const ``PProd [lvl1, lvl2]) e1 e2

private def mkPProdMk (e1 e2 : Expr) : MetaM Expr := do
  let t1 ← inferType e1
  let t2 ← inferType e2
  let lvl1 ← getLevel t1
  let lvl2 ← getLevel t2
  if lvl1 matches .zero && lvl2 matches .zero then
    return mkApp4 (.const ``And.intro []) t1 t2 e1 e2
  else
    return mkApp4 (.const ``PProd.mk [lvl1, lvl2]) t1 t2 e1 e2

private def mkNProd (lvl : Level) (es : Array Expr) : MetaM Expr :=
  es.foldrM (init := mkPUnit lvl) mkPProd

private def mkNProdMk (lvl : Level) (es : Array Expr) : MetaM Expr :=
  es.foldrM (init := mkPUnitMk lvl) mkPProdMk

/-- `PProd.fst` or `And.left` -/
private def mkPProdFst (e : Expr) : MetaM Expr := do
  let t ← whnf (← inferType e)
  match_expr t with
  | PProd t₁ t₂ => return mkApp3 (.const ``PProd.fst t.getAppFn.constLevels!) t₁ t₂ e
  | And t₁ t₂ =>   return mkApp3 (.const ``And.left []) t₁ t₂ e
  | _ => throwError "Cannot project out of{indentExpr e}\nof Type{indentExpr t}"

/-- `PProd.snd` or `And.right` -/
private def mkPProdSnd (e : Expr) : MetaM Expr := do
  let t ← whnf (← inferType e)
  match_expr t with
  | PProd t₁ t₂ => return mkApp3 (.const ``PProd.snd t.getAppFn.constLevels!) t₁ t₂ e
  | And t₁ t₂ =>   return mkApp3 (.const ``And.right []) t₁ t₂ e
  | _ => throwError "Cannot project out of{indentExpr e}\nof Type{indentExpr t}"

/--
If `minorType` is the type of a minor premies of a recursor, such as
```
  (cons : (head : α) → (tail : List α) → (tail_hs : motive tail) → motive (head :: tail))
```
of `List.rec`, constructs the corresponding argument to `List.rec` in the construction
of `.brecOn` definition; in this case
```
fun head tail tail_ih =>
  ⟨F_1 (head :: tail) ⟨tail_ih, PUnit.unit⟩, ⟨tail_ih, PUnit.unit⟩⟩
```
of type
```
(head : α) → (tail : List α) →
  PProd (motive tail) (List.below tail) →
  PProd (motive (head :: tail)) (PProd (PProd (motive tail) (List.below tail)) PUnit)
```
The parameter `typeFormers` are the `motive`s.
-/
private def buildMinorPremise (rlvl : Level) (typeFormers : Array Expr) (below : Expr)
    (fs : Array Expr) (minorType : Expr) : MetaM Expr :=
  forallTelescope minorType fun minor_args minor_type => do
    let rec go (prods : Array Expr) : List Expr → MetaM Expr
      | [] => do
        let b ← mkNProdMk rlvl prods
        let f := fs[0]! -- TODO
        let fArgs := minor_type.getAppArgs
        mkPProdMk (mkAppN f (fArgs.push b)) b
      | arg::args => do
        let argType ← inferType arg
        forallTelescope argType fun arg_args arg_type => do
          arg_type.withApp fun arg_type_fn arg_type_args => do
            if typeFormers.contains arg_type_fn then
              let name ← arg.fvarId!.getUserName
              let type' ← mkForallFVars arg_args
                (← mkPProd arg_type (mkAppN below arg_type_args) )
              withLocalDeclD name type' fun arg' => do
                if arg_args.isEmpty then
                  mkLambdaFVars #[arg'] (← go (prods.push arg') args)
                else
                  let r := mkAppN arg arg_args
                  let r₁ ← mkLambdaFVars arg_args (← mkPProdFst r)
                  let r₂ ← mkLambdaFVars arg_args (← mkPProdSnd r)
                  let r ← mkPProdMk r₁ r₂
                  mkLambdaFVars #[arg'] (← go (prods.push r) args)
            else
              mkLambdaFVars #[arg] (← go prods args)
    go #[] minor_args.toList

/--
Constructs the `.brecon` or `.binductionon` definition for a inductive predicate.

For example for the `List` type, it constructs,
```
@[reducible] protected def List.brecOn.{u_1, u} : {α : Type u} → {motive : List α → Sort u_1} →
  (t : List α) → ((t : List α) → List.below t → motive t) → motive t :=
fun {α} {motive} t (F_1 : (t : List α) → List.below t → motive t) => (
  @List.rec α (fun t => PProd (motive t) (@List.below α motive t))
    ⟨F_1 [] PUnit.unit, PUnit.unit⟩
    (fun head tail tail_ih => ⟨F_1 (head :: tail) ⟨tail_ih, PUnit.unit⟩, ⟨tail_ih, PUnit.unit⟩⟩)
    t
  ).1
```
and
```
@[reducible] protected def List.binductionOn.{u} : ∀ {α : Type u} {motive : List α → Prop}
  (t : List α), (∀ (t : List α), List.ibelow t → motive t) → motive t :=
fun {α} {motive} t F_1 => (
  @List.rec α (fun t => And (motive t) (@List.ibelow α motive t))
    ⟨F_1 [] True.intro, True.intro⟩
    (fun head tail tail_ih => ⟨F_1 (head :: tail) ⟨tail_ih, True.intro⟩, ⟨tail_ih, True.intro⟩⟩)
    t
  ).1
```
-/
def mkBRecOnOrBInductionOn (indName : Name) (ind : Bool) : MetaM DefinitionVal := do
  let indVal ← getConstInfoInduct indName
  let recName := mkRecName indName
  -- The construction follows the type of `ind.rec`
  let .recInfo recVal ← getConstInfo recName
    | throwError "{recName} not a .recInfo"
  let lvl::lvls := recVal.levelParams.map (Level.param ·)
    | throwError "recursor {recName} has no levelParams"
  let lvlParam := recVal.levelParams.head!
  -- universe parameter names of brecOn/binductionOn
  let blps := if ind then recVal.levelParams.tail!  else recVal.levelParams
  -- universe arguments of below/ibelow
  let blvls := if ind then lvls else lvl::lvls

  let .some ilvl ← typeFormerTypeLevel indVal.type
    | throwError "type {indVal.type} of inductive {indVal.name} not a type former?"
  -- universe level of the resultant type
  let rlvl : Level :=
    if ind then
      0
    else if indVal.isReflexive then
      if let .max 1 lvl := ilvl then
        mkLevelMax' (.succ lvl) lvl
      else
        mkLevelMax' (.succ lvl) ilvl
    else
      mkLevelMax' 1 lvl

  let refType :=
    if ind then
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

    -- TODO: Need multiple belows if we have multiple type formers
    let below := Expr.const (if ind then mkIBelowName indName else mkBelowName indName) blvls
    let below := mkAppN below (params ++ typeFormers)

    -- create types of functionals (one for each type former)
    --   (F_1 : (t : List α) → (f : List.below t) → motive t)
    -- and bring parameters of that type into scope
    let mut fDecls : Array (Name × (Array Expr -> MetaM Expr)) := #[]
    for typeFormer in typeFormers, i in [:typeFormers.size] do
      let fType ← forallTelescope (← inferType typeFormer) fun targs _ => do
        withLocalDeclD `f (mkAppN below targs) fun f =>
          mkForallFVars (targs.push f) (mkAppN typeFormer targs)
      let fName := .mkSimple s!"F_{i + 1}"
      fDecls := fDecls.push (fName, fun _ => pure fType)
    withLocalDeclsD fDecls fun fs => do

      let mut val := .const recName (rlvl :: lvls)
      -- add parameters
      val := mkAppN val params
      -- add type formers
      for typeFormer in typeFormers do
        -- example: (motive := fun t => PProd (motive t) (@List.below α motive t))
        let arg ← forallTelescope (← inferType typeFormer) fun targs _ => do
          let cType := mkAppN typeFormer targs
          let belowType := mkAppN below targs
          let arg ← mkPProd cType belowType
          mkLambdaFVars targs arg
        val := .app val arg
      -- add minor premises
      for minor in minors do
        let arg ← buildMinorPremise rlvl typeFormers below fs (← inferType minor)
        val := .app val arg
      -- add indices and major premise
      val := mkAppN val remaining
      -- project out first component
      val ← mkPProdFst val

      -- All paramaters of `.rec` besides the `minors` become parameters of `.bRecOn`, and the `fs`
      let below_params := params ++ typeFormers ++ remaining ++ fs
      let type ← mkForallFVars below_params (mkAppN typeFormers[0]! remaining)
      val ← mkLambdaFVars below_params val

      let name := if ind then mkIBelowName indName else mkBelowName indName
      mkDefinitionValInferrringUnsafe name blps type val .abbrev
