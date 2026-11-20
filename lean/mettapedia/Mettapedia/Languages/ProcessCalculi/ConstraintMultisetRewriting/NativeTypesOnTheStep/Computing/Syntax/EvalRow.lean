import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Syntax.Settler

/-!
# The interpreter's add row on the converting step

The typed interpreter's row for addition, `eval t (add x y) = add (eval tnum x) (eval tnum y)`, is a
firing of the converting step over the qualified typed-syntax package: its frame holds `x y : exp tnum`
and, newest, the call's index `t : ty`; matching `add` teaches `t ≐ tnum` (the second constructor at the
index `tnum`, beside the literal); it makes `add (eval tnum x) (eval tnum y)` at the call's declared type
`val t`.

* Admission is decided by kernel evaluation of the package's computable settler and executable
  conversion (`add_decided`): the settler solves `t ≐ tnum` and the conversion takes `val tnum` to `num`,
  the made row's own type. So the computable converting step admits the row (`add_admitted`), and it is
  typed after its match (`add_typedAfterMatch`). In its frame it is not typed (`addRow_not_frameTyped`):
  the made row lies in the bidirectional fragment, its synthesized type is `num`, which is below every
  type of the row, and `num` is no stuck `val t`. So the present step refuses it (`add_present_refused`).
* **The literal row** `eval t (lit k) = k`, the other constructor at `tnum`, gets the full set: decided by
  the kernel (`lit_decided`), admitted (`lit_admitted`), typed after its match (`lit_typedAfterMatch`),
  not typed in its frame (`litRow_not_frameTyped`, `val t` is stuck on the variable index), so refused by
  the present step (`lit_present_refused`).
* **Control**: the add row answering `true` is not typed after the match, `val tnum ≡ num` not being
  the Booleans, and is refused for every settler (`boolRow_refused`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.Computing.Syntax

open _root_.CategoryTheory Opposite Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open Interface.DependentFull (Make State Firing)
open TowerNumbersModel (num zero succ numRec ctors u)
open TowerVectorsModel (U0 numC zeroC succC unitC ttC addC)
open TowerSyntaxModel

/-- The package of the step side. -/
abbrev spkg : Rules Tower.Head := rules level0

/-- `ty`, over any frame. -/
def tyType (Γ : Context spkg) : TypeOver Γ := ⟨tyC, u, LevelTower.IsUniverse.sort _, TowerSyntaxModel.ty_typed level0⟩

/-- `exp tnum`, over any frame. -/
def expNumType (Γ : Context spkg) : TypeOver Γ :=
  ⟨expC tnumC, u, LevelTower.IsUniverse.sort _,
    TowerSyntaxModel.exp_typed level0 (TowerSyntaxModel.tnum_typed level0)⟩

/-- The frame `x : exp tnum`. -/
abbrev addCtxX : Context spkg := extend (empty spkg) (expNumType _)

/-- The frame `x y : exp tnum`. -/
abbrev addCtxY : Context spkg := extend addCtxX (expNumType _)

/-- **The frame of the add row**: `x y : exp tnum`, then the call's index `t : ty`, newest. -/
abbrev addFrame : Context spkg := extend addCtxY (tyType _)

/-- The call's declared type, `val t`. -/
def addCallType : TypeOver addFrame :=
  ⟨valC (.var 0), u, LevelTower.IsUniverse.sort _, TowerSyntaxModel.val_typed level0 (Derivable.var (0 : Fin 3))⟩

/-- **The add row** `eval t (add x y) = add (eval tnum x) (eval tnum y)`, made at the call's declared
type. -/
def addRow : Make addFrame := ⟨addCallType, addC (evalC tnumC (.var 2)) (evalC tnumC (.var 1))⟩

/-- The made row's own type, `num`. -/
def numOwn : TypeOver addFrame := ⟨numC, u, LevelTower.IsUniverse.sort _, TowerSyntaxModel.num_typed level0⟩

theorem addRow_frameTyped : FrameTypedAt addRow numOwn := by
  have tx : Typed spkg addFrame.raw (.var 2) (expC tnumC) := Derivable.var (2 : Fin 3)
  have ty' : Typed spkg addFrame.raw (.var 1) (expC tnumC) := Derivable.var (1 : Fin 3)
  have ex : Typed spkg addFrame.raw (evalC tnumC (.var 2)) numC :=
    Typed.convType (TowerSyntaxModel.eval_typed level0 (TowerSyntaxModel.tnum_typed level0) tx)
      ⟨_, LevelTower.IsUniverse.sort _, TowerSyntaxModel.val_tnum_eq level0⟩
  have ey : Typed spkg addFrame.raw (evalC tnumC (.var 1)) numC :=
    Typed.convType (TowerSyntaxModel.eval_typed level0 (TowerSyntaxModel.tnum_typed level0) ty')
      ⟨_, LevelTower.IsUniverse.sort _, TowerSyntaxModel.val_tnum_eq level0⟩
  have tAdd : Typed spkg addFrame.raw (.const TowerVectorsModel.add) (.pi numC (.pi numC numC)) :=
    .const (type := .pi numC (.pi numC numC)) rfl
      ((tw_rules level0).pi_small (TowerSyntaxModel.num_typed level0)
        ((tw_rules level0).pi_small (TowerSyntaxModel.num_typed level0) (TowerSyntaxModel.num_typed level0)))
      (LevelTower.IsUniverse.sort _)
  exact .appElim (A := numC) (B := numC) (.appElim (A := numC) (B := .pi numC numC) tAdd ex) ey

/-- `tnum`, over `x y`. -/
def tnumValue : Term addCtxY (tyType _) := ⟨tnumC, TowerSyntaxModel.tnum_typed level0⟩

/-- **What matching `add` teaches**: `t ≐ tnum`. -/
def matchAdd : Equation (TotalTerm addFrame) := Elimination.definition addCtxY tnumValue

/-- The call's index, as a row of the state. -/
def addState : State spkg Nat := ⟨addFrame, [], ∅, fun _ => ⟨tyType _, ⟨.var 0, Derivable.var (0 : Fin 3)⟩⟩⟩

/-- **The add row as a firing**: told what the match teaches, it makes
`add (eval tnum x) (eval tnum y)` at `val t`. -/
def addFiring : Firing synS.levels addState where
  helpers := .nil _
  taken := []
  read := []
  takes := []
  reads := []
  makes := [(0, addRow)]
  tells := [matchAdd]
  guards := []
  queries := []

def addFrameType : ∀ m ∈ addFiring.makes, Σ' B : TypeOver addFiring.helpers.frame, FrameTypedAt m.2 B :=
  fun m member => ⟨numOwn, by obtain rfl := List.mem_singleton.mp member; exact addRow_frameTyped⟩

/-- **Decided by the kernel**: the settler solves `t ≐ tnum`, and at the solution the executable
conversion takes `val tnum` to `num`, the made row's own type. -/
theorem add_decided : synAdmits? [synFamily 16 4] 16 addFiring addFrameType = some true := by
  decide +kernel

/-- **The computable converting step admits the add row.** -/
theorem add_admitted : (convertingStep synS.levels Nat (synSettler 16 4)).Admits addFiring :=
  synAdmits?_sound add_decided

/-- **The add row is typed after its match**, at every solution of `t ≐ tnum`. -/
theorem add_typedAfterMatch : TypedAfterMatch synS.levels addFiring.information addRow :=
  converting_typedAfterMatch synS.levels (synSettler 16 4) add_admitted (0, addRow) (List.mem_singleton_self _)

/-- `val t` is stuck on the variable index, in the add row's frame. -/
theorem addCall_stuck : Neutral TowerSyntaxModel.roles (valC (.var 0) : Tower.Tm 3) :=
  Neutral.stuck_single (before := []) (after := []) roles_val rfl (.var 0)

/-- The head typing of the package is a function. -/
theorem syn_headsTyped {h u u' : Tower.Head} (first : synS.R.headTyping h u)
    (second : synS.R.headTyping h u') : u = u' := by
  cases first <;> cases second <;> rfl

/-- The made row is in the bidirectional fragment: abstractions only at checked positions. -/
theorem addRow_fragment :
    Bidirectional .synth (addC (evalC tnumC (.var 2)) (evalC tnumC (.var 1)) : Tower.Tm 3) := by
  repeat' constructor

/-- **Not typed in its frame**: the made row's least type is `num`, by synthesis, and `num` is no stuck
`val t`. -/
theorem addRow_not_frameTyped : ¬ addRow.WellTyped := by
  intro typed
  have formed : CtxFormed spkg addFrame.raw := addFrame.formed
  have typed' : Typed spkg addFrame.raw (addC (evalC tnumC (.var 2)) (evalC tnumC (.var 1))) (valC (.var 0)) :=
    typed
  obtain ⟨T, s⟩ := (Synth.exists_iff_typable (S := synS) (TowerSyntaxModel.facts level0)
    (TowerSyntaxModel.algebra level0) syn_headsTyped addRow_fragment formed).mpr ⟨_, typed'⟩
  have le := (Synth.principal (S := synS) (TowerSyntaxModel.facts level0) (TowerSyntaxModel.algebra level0)
    syn_headsTyped s formed).2 typed'
  cases s with
  | app s₁ red₁ _ =>
    cases s₁ with
    | app s₂ red₂ _ =>
      cases s₂ with
      | const declared _ _ =>
        have known : synS.R.constantType TowerVectorsModel.add = some (.pi numC (.pi numC numC)) := rfl
        rw [known] at declared
        obtain rfl := Option.some.inj declared
        have first := WhRed.eq_of_whnf (S := synS) (pi_whnf (TowerSyntaxModel.shape level0) _ _) red₂.red
        injection first with _ _ sameB
        subst sameB
        have second := WhRed.eq_of_whnf (S := synS) (pi_whnf (TowerSyntaxModel.shape level0) _ _) red₁.red
        injection second with _ _ sameB'
        subst sameB'
        have le' : TypeLe spkg addFrame.raw numC (valC (.var 0)) := le
        have equal : TypeEq spkg addFrame.raw numC (valC (.var 0)) :=
          TypeLe.rigid (S := synS) le' addCallType.isType formed
            (fun _ _ e => TypeEq.inductive_ne_head (TowerSyntaxModel.facts level0) roles_num formed e)
            (fun _ _ e => TypeEq.inductive_ne_pi (TowerSyntaxModel.facts level0) roles_num formed e)
            (fun _ _ e => TypeEq.inductive_ne_sigma (TowerSyntaxModel.facts level0) roles_num formed e)
        exact (TypeEq.neutral_form (TowerSyntaxModel.facts level0) equal.symm formed addCall_stuck
          (.inr (.inr (.inr (.inr (.inr ⟨num, ctors, roles_num, rfl⟩)))))).ne_inductive roles_num rfl

/-- **So the present step refuses the add row.** -/
theorem add_present_refused : ¬ (DependentFull.step synS.levels Nat).Admits addFiring := fun admitted =>
  addRow_not_frameTyped (admitted.1.2.2.2.2 (0, addRow) (List.mem_singleton_self _))

/-! ## The literal row `eval t (lit k) = k` -/

/-- `num`, over any frame. -/
def numType (Γ : Context spkg) : TypeOver Γ := ⟨numC, u, LevelTower.IsUniverse.sort _, TowerSyntaxModel.num_typed level0⟩

/-- The frame `k : num`. -/
abbrev litCtxK : Context spkg := extend (empty spkg) (numType _)

/-- **The frame of the literal row**: `k : num`, then the call's index `t : ty`, newest. -/
abbrev litFrame : Context spkg := extend litCtxK (tyType _)

/-- The call's declared type, `val t`. -/
def litCallType : TypeOver litFrame :=
  ⟨valC (.var 0), u, LevelTower.IsUniverse.sort _, TowerSyntaxModel.val_typed level0 (Derivable.var (0 : Fin 2))⟩

/-- **The literal row** `eval t (lit k) = k`: `k`, made at the call's declared type. -/
def litRow : Make litFrame := ⟨litCallType, .var 1⟩

/-- `k`'s own type, `num`. -/
def kOwn : TypeOver litFrame := ⟨numC, u, LevelTower.IsUniverse.sort _, TowerSyntaxModel.num_typed level0⟩

theorem litRow_frameTyped : FrameTypedAt litRow kOwn := Derivable.var (1 : Fin 2)

/-- `tnum`, over `k`. -/
def tnumAtK : Term litCtxK (tyType _) := ⟨tnumC, TowerSyntaxModel.tnum_typed level0⟩

/-- **What matching `lit` teaches**: `t ≐ tnum`, the same index as matching `add`. -/
def matchLit : Equation (TotalTerm litFrame) := Elimination.definition litCtxK tnumAtK

def litState : State spkg Nat := ⟨litFrame, [], ∅, fun _ => ⟨tyType _, ⟨.var 0, Derivable.var (0 : Fin 2)⟩⟩⟩

/-- **The literal row as a firing.** -/
def litFiring : Firing synS.levels litState where
  helpers := .nil _
  taken := []
  read := []
  takes := []
  reads := []
  makes := [(0, litRow)]
  tells := [matchLit]
  guards := []
  queries := []

def litFrameType : ∀ m ∈ litFiring.makes, Σ' B : TypeOver litFiring.helpers.frame, FrameTypedAt m.2 B :=
  fun m member => ⟨kOwn, by obtain rfl := List.mem_singleton.mp member; exact litRow_frameTyped⟩

/-- **Decided by the kernel**: at the solution `t ↦ tnum`, `val tnum` computes to `num`. -/
theorem lit_decided : synAdmits? [synFamily 16 4] 16 litFiring litFrameType = some true := by
  decide +kernel

theorem lit_admitted : (convertingStep synS.levels Nat (synSettler 16 4)).Admits litFiring :=
  synAdmits?_sound lit_decided

/-- **The literal row is typed after its match.** -/
theorem lit_typedAfterMatch : TypedAfterMatch synS.levels litFiring.information litRow :=
  converting_typedAfterMatch synS.levels (synSettler 16 4) lit_admitted (0, litRow) (List.mem_singleton_self _)

/-- `val t` is stuck on the variable index. -/
theorem litCall_stuck : Neutral TowerSyntaxModel.roles (valC (.var 0) : Tower.Tm 2) :=
  Neutral.stuck_single (before := []) (after := []) roles_val rfl (.var 0)

/-- **Not typed in its frame**: `num` is no stuck `val t`. -/
theorem litRow_not_frameTyped : ¬ litRow.WellTyped := by
  intro typed
  have formed : CtxFormed spkg litFrame.raw := litFrame.formed
  have le : TypeLe spkg litFrame.raw numC (valC (.var 0)) := Typed.generation typed
  have equal : TypeEq spkg litFrame.raw numC (valC (.var 0)) :=
    TypeLe.rigid (S := synS) le litCallType.isType formed
      (fun _ _ e => TypeEq.inductive_ne_head (TowerSyntaxModel.facts level0) roles_num formed e)
      (fun _ _ e => TypeEq.inductive_ne_pi (TowerSyntaxModel.facts level0) roles_num formed e)
      (fun _ _ e => TypeEq.inductive_ne_sigma (TowerSyntaxModel.facts level0) roles_num formed e)
  exact (TypeEq.neutral_form (TowerSyntaxModel.facts level0) equal.symm formed litCall_stuck
    (.inr (.inr (.inr (.inr (.inr ⟨num, ctors, roles_num, rfl⟩)))))).ne_inductive roles_num rfl

/-- **So the present step refuses it.** -/
theorem lit_present_refused : ¬ (DependentFull.step synS.levels Nat).Admits litFiring := fun admitted =>
  litRow_not_frameTyped (admitted.1.2.2.2.2 (0, litRow) (List.mem_singleton_self _))

/-! ## Control: the add row answering a Boolean -/

/-- `true`, made at the call's declared type. -/
def boolRow : Make addFrame := ⟨addCallType, btrueC⟩

/-- The add row answering `true`. -/
def boolFiring : Firing synS.levels addState := { addFiring with makes := [(0, boolRow)] }

/-- **Not typed after the match**: at the solution `t ↦ tnum` the type is `val tnum ≡ num`, and `true`
is a Boolean. -/
theorem boolRow_not_typedAfterMatch : ¬ TypedAfterMatch synS.levels [matchAdd] boolRow := by
  intro after
  have typed := (typedAfterMatch_iff synS.levels _ boolRow).mp after addCtxY
    (Elimination.instantiate addCtxY tnumValue) (definition_initial synS.levels addCtxY tnumValue).solves
  have formed : CtxFormed spkg addCtxY.raw := addCtxY.formed
  have atNum : Typed spkg addCtxY.raw btrueC (valC tnumC) := typed
  have toNum : Typed spkg addCtxY.raw btrueC numC :=
    Typed.convType atNum ⟨_, LevelTower.IsUniverse.sort _, TowerSyntaxModel.val_tnum_eq level0⟩
  obtain ⟨type, w, declared, _, _, le⟩ := Typed.generation toNum
  have known : spkg.constantType btrue = some boolC := rfl
  rw [known] at declared
  obtain rfl := Option.some.inj declared
  have equal : TypeEq spkg addCtxY.raw boolC numC :=
    TypeLe.rigid (S := synS) le ⟨_, LevelTower.IsUniverse.sort _, TowerSyntaxModel.num_typed level0⟩ formed
      (fun _ _ e => TypeEq.inductive_ne_head (TowerSyntaxModel.facts level0) roles_bool formed e)
      (fun _ _ e => TypeEq.inductive_ne_pi (TowerSyntaxModel.facts level0) roles_bool formed e)
      (fun _ _ e => TypeEq.inductive_ne_sigma (TowerSyntaxModel.facts level0) roles_bool formed e)
  exact absurd (TypeEq.inductive_injective (TowerSyntaxModel.facts level0) roles_bool roles_num equal formed)
    (by decide)

/-- **Refused, for every settler.** -/
theorem boolRow_refused (settler : Settler synS.levels) :
    ¬ (convertingStep synS.levels Nat settler).Admits boolFiring := fun admitted =>
  boolRow_not_typedAfterMatch
    (converting_typedAfterMatch synS.levels settler admitted (0, boolRow) (List.mem_singleton_self _))

end NativeTypesOnTheStep.Computing.Syntax

#print axioms NativeTypesOnTheStep.Computing.Syntax.addRow_frameTyped
#print axioms NativeTypesOnTheStep.Computing.Syntax.add_decided
#print axioms NativeTypesOnTheStep.Computing.Syntax.add_admitted
#print axioms NativeTypesOnTheStep.Computing.Syntax.add_typedAfterMatch
#print axioms NativeTypesOnTheStep.Computing.Syntax.addRow_not_frameTyped
#print axioms NativeTypesOnTheStep.Computing.Syntax.add_present_refused
#print axioms NativeTypesOnTheStep.Computing.Syntax.lit_decided
#print axioms NativeTypesOnTheStep.Computing.Syntax.lit_admitted
#print axioms NativeTypesOnTheStep.Computing.Syntax.lit_typedAfterMatch
#print axioms NativeTypesOnTheStep.Computing.Syntax.litRow_not_frameTyped
#print axioms NativeTypesOnTheStep.Computing.Syntax.lit_present_refused
#print axioms NativeTypesOnTheStep.Computing.Syntax.boolRow_not_typedAfterMatch
#print axioms NativeTypesOnTheStep.Computing.Syntax.boolRow_refused

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
