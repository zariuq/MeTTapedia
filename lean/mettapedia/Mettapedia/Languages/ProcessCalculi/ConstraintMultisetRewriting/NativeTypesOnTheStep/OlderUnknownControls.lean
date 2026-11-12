import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.OlderUnknown
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.TemplateControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPatternFiringControls

/-!
# D2's coerce firing, admitted by a computable settler

`ProgrammingOnTheStep.Refinement.coerceFiring` makes the helpers `x : X` and `g : Ground` over `X : U₀`,
tells `(x : X) ≐ (g : Ground)` and makes the row `x` at `Ground`. The present step refuses it
(`coerce_refused`), and N3's computable settler leaves its information undecided
(`ComputableControls.coerce_undecided`).

**Evaluated by the kernel.**
* The in-place solver alone does not decide the coerce store (`coerce_inPlace_alone`): its one equation
  is heterogeneous, and no rule reads a type equation from it.
* The extraction adds the type equation `X ≐ Ground` at `U₀` (`coerce_extract`), and the older-unknown
  family settles the store (`coerce_older_settled`): `X` is solved at its own prefix, the answer is
  carried past `x` and `g`, and the woken equation `(x : Ground) ≐ (g : Ground)` is solved.
* **The computable converting step admits D2's coerce firing** (`coerce_decided`, `coerce_admitted`);
  the present step refuses it (`coerce_computable_separation`). The templating step admits it too
  (`coerce_templated`), the made row is typed at every solution (`coerce_typedAfterMatch_computably`), and
  the admission is the semantic settler's (`coerce_agrees`).

**The class, on D2's firing** (`coerce_in_class`): its information entails the definition of `X` by
`Ground`, carried past its helpers, through its heterogeneous equation; so the older-unknown transition is
exact on it (`coerce_transition_exact`).

**The tree's own stuck store**: `snd (X, refl X) ≐ refl Ground` over `X : U₀`, on which the tree's driver
is stuck (`wake_driver_undecided`), is settled by the older-unknown family (`wake_older_settled`): its
extracted type equation `Id U₀ (fst (X, refl X)) (fst (X, refl X)) ≐ Id U₀ Ground Ground` solves `X`.

**Negative controls.**
* Telling also `X ≐ Ground → Ground`: the store has no solution (`arrow_unsolvable`, from the rigid clash
  of `Ground` and `Ground → Ground`), and the kernel refutes it (`arrow_decided`, `arrow_refused`).
* The cross store of N2 is solvable and has no initial solution, so **no family decides it**
  (`cross_undecided`): every sound family, the older-unknown family included, declines it, and the
  computable settler postpones.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.OlderUnknown.Controls

open _root_.CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open Interface.DependentFull Interface.DependentFull.Controls
open ProgrammingOnTheStep.Refinement (coerceFiring coerce_refused)
open ComputableControls
open UnificationWithLevels (InitialSolution)
open ContextualDependentSweep.Witnesses ContextualDependentDynamicFragment

/-- A settled decision is decisive. -/
theorem decisive_of_isSettled {Δ : Context setting.R} {I : EquationStore (TotalTerm Δ)}
    {d : Decision setting.levels I} (settled : d.isSettled = true) : d.Decisive := by
  cases d with
  | settled _ _ _ => trivial
  | refuted _ => cases settled
  | undecided => cases settled

/-! ## D2's coerce store -/

/-- The four codes of an equation over `X : U₀, x : X, g : Ground`: left type, left term, right type,
right term. -/
def codes (e : Equation (TotalTerm triple)) : Tower.Tm 3 × Tower.Tm 3 × Tower.Tm 3 × Tower.Tm 3 :=
  (e.1.1.code, e.1.2.code, e.2.1.code, e.2.2.code)

/-- The coerce information, over its frame. -/
abbrev coerceStore : EquationStore (TotalTerm triple) := coerceFiring.information

/-- **The extraction of the coerce store**: the type equation `X ≐ Ground` at `U₀`, then the
heterogeneous equation itself. -/
theorem coerce_extract :
    (extract setting.levels ExecutableTowerChoices.choices coerceStore).map codes =
      [(.head (.sort Tower.zero), .var 2, .head (.sort Tower.zero), ground),
        (.var 2, .var 1, ground, .var 0)] := by
  decide +kernel

/-- **Without the extraction, the in-place solver does not decide the coerce store.** -/
theorem coerce_inPlace_alone :
    (driverFamily setting.levels inPlace 4 coerceFiring.information).isSettled = false ∧
      (driverFamily setting.levels inPlace 4 coerceFiring.information).isRefuted = false := by
  decide +kernel

/-- **The older-unknown family settles the coerce store.** -/
theorem coerce_older_settled : (olderFamily olderFuel coerceFiring.information).isSettled = true := by
  decide +kernel

/-- **Decided by the kernel: the computable converting step admits D2's coerce firing.** -/
theorem coerce_decided : admits? olderFamilies coerceFiring = some true := by decide +kernel

/-- **The computable converting step admits D2's coerce firing.** -/
theorem coerce_admitted : (convertingStep setting.levels Nat olderSettler).Admits coerceFiring :=
  (admits?_sound olderFamilies coerce_decided).mp rfl

/-- **The separation**: the computable converting step admits D2's coerce firing, the present step
refuses it. -/
theorem coerce_computable_separation :
    (convertingStep setting.levels Nat olderSettler).Admits coerceFiring ∧
      ¬ (step setting.levels Nat).Admits coerceFiring :=
  ⟨coerce_admitted, coerce_refused⟩

/-- **The templating step with the computable settler admits it too.** -/
theorem coerce_templated : (templatingStep setting.levels Nat olderSettler).Admits coerceFiring :=
  converting_le_templating setting.levels olderSettler coerce_admitted

/-- **Its made row is typed at every solution of its information**, by the soundness of the converting
step. -/
theorem coerce_typedAfterMatch_computably :
    TypedAfterMatch setting.levels coerceFiring.information Coerce.coerceRow :=
  converting_typedAfterMatch setting.levels olderSettler coerce_admitted (8, Coerce.coerceRow)
    (List.mem_singleton_self _)

/-- The coerce store is decided by the families. -/
theorem coerce_decidedBy : DecidedBy setting.levels olderFamilies coerceFiring.information :=
  ⟨olderFamily olderFuel, List.mem_append_right _ (List.mem_singleton_self _),
    decisive_of_isSettled coerce_older_settled⟩

/-- **The computable admission is the semantic settler's.** -/
theorem coerce_agrees :
    (convertingStep setting.levels Nat olderSettler).Admits coerceFiring ↔
      (convertingStep setting.levels Nat (Settler.ideal setting.levels)).Admits coerceFiring :=
  older_converting_iff_ideal coerce_decidedBy

/-! ## D2's coerce store is in the class -/

/-- `Ground` as a term of `U₀` over the empty frame: the value of the older unknown. -/
def groundValue : Term (empty Tower.rules) (smallUniverse (empty Tower.rules)) := ⟨ground, ground_typed _⟩

/-- The definition of `X` by `Ground`, carried past the coerce firing's helpers `x : X, g : Ground`. -/
abbrev coerceDefinition : EquationStore (TotalTerm triple) :=
  weakenStore setting.levels coerceFiring.helpers [Elimination.definition (empty Tower.rules) groundValue]

/-- The carried definition compares `X`, now the variable `2`, with `Ground`, at `U₀`. -/
theorem coerceDefinition_codes :
    coerceDefinition.map codes = [(.head (.sort Tower.zero), .var 2, .head (.sort Tower.zero), ground)] := by
  decide +kernel

/-- **D2's coerce information is in the class**: its heterogeneous equation entails the definition of its
older type unknown `X` by `Ground`, carried past `x` and `g`. -/
theorem coerce_in_class (Θ : Context setting.R) (τ : Θ ⟶ triple)
    (solved : (frames setting.levels).Models τ coerceStore) :
    (frames setting.levels).Models τ coerceDefinition := by
  intro d member
  have read : codes d = (.head (.sort Tower.zero), .var 2, .head (.sort Tower.zero), ground) := by
    have mapped := List.mem_map_of_mem (f := codes) member
    rw [coerceDefinition_codes] at mapped
    exact List.mem_singleton.mp mapped
  have universeCode : d.1.1.code = .head (.sort Tower.zero) := congrArg (fun c => c.1) read
  have leftTerm : d.1.2.code = .var 2 := congrArg (fun c => c.2.1) read
  have rightType : d.2.1.code = .head (.sort Tower.zero) := congrArg (fun c => c.2.2.1) read
  have rightTerm : d.2.2.code = ground := congrArg (fun c => c.2.2.2) read
  exact entails_definition_of_twin (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra rigid TowerModel.complete (xRow, gRow) d (u := .sort Tower.zero)
    (LevelTower.IsUniverse.sort _) universeCode (rightType.trans universeCode.symm) leftTerm.symm
    rightTerm.symm xRow.1.formed gRow.1.formed τ (solved _ (List.mem_singleton_self _))

/-- **The older-unknown transition is exact on D2's coerce information.** -/
theorem coerce_transition_exact :
    UnificationWithLevels.Exact (frames setting.levels) coerceStore
      (olderTransition setting.levels (empty Tower.rules) groundValue coerceFiring.helpers).answer
      ((frames setting.levels).applyStore
        (olderTransition setting.levels (empty Tower.rules) groundValue coerceFiring.helpers).answer
        coerceStore) :=
  olderTransition_exact setting.levels (empty Tower.rules) groundValue coerceFiring.helpers _ coerce_in_class

/-! ## Refuted: the coerce store with `X ≐ Ground → Ground` told -/

/-- The coerce firing, telling also `X ≐ Ground → Ground` at `U₀`. -/
def arrowFiring : Firing setting.levels baseState :=
  { coerceFiring with tells := [(xRow, gRow), (xUniverse, arrowUniverse)] }

/-- Its information, over its frame. -/
abbrev arrowStore : EquationStore (TotalTerm triple) := arrowFiring.information

/-- **The store has no solution**: `X` would be `Ground` and `Ground → Ground`, a rigid clash. -/
theorem arrow_unsolvable : ¬ (frames setting.levels).Solvable arrowStore := by
  rintro ⟨Θ, τ, solved⟩
  have twin := (tell_heterogeneous setting.levels arrowFiring solved (List.mem_cons_self ..)).1
  change TypeEq Tower.rules Θ.raw (subst τ.substitution (.var 2)) ground at twin
  have known := (solved _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))).2
  change Equal Tower.rules Θ.raw (subst τ.substitution (.var 2)) arrow (.head (.sort Tower.zero)) at known
  have typeX : TypeEq Tower.rules Θ.raw (subst τ.substitution (.var 2)) arrow := ⟨.sort Tower.zero, .sort _, known⟩
  exact ground_arrow_clash Θ.formed (twin.symm.trans setting.levels typeX)

/-- **Decided by the kernel: refused.** -/
theorem arrow_decided : admits? olderFamilies arrowFiring = some false := by decide +kernel

theorem arrow_refused : ¬ (convertingStep setting.levels Nat olderSettler).Admits arrowFiring :=
  fun admitted => Bool.false_ne_true ((admits?_sound olderFamilies arrow_decided).mpr admitted)

/-! ## Across universes: `X : U₁` fixed to `Ground : U₀` -/

/-- The frame `X : U₁`. -/
abbrev bigBase : Context Tower.rules := extend (empty Tower.rules) (bigUniverse _)

/-- The frame `X : U₁, x : X`. -/
abbrev bigPair : Context Tower.rules := extend bigBase TemplateControls.xBig

/-- The frame `X : U₁, x : X, g : Ground`. -/
abbrev bigTriple : Context Tower.rules := extend bigPair (groundType _)

/-- The row `x : X`. -/
def xBigRow : TotalTerm bigTriple :=
  TotalTerm.reindex (⟨TemplateControls.xBig.reindex (projectionHom bigBase TemplateControls.xBig),
    newest bigBase TemplateControls.xBig⟩ : TotalTerm bigPair) (projectionHom bigPair (groundType _))

/-- The row `g : Ground`. -/
def gBigRow : TotalTerm bigTriple :=
  ⟨(groundType bigPair).reindex (projectionHom bigPair (groundType _)), newest bigPair (groundType _)⟩

/-- The state `X : U₁` with no knowledge and no rows. -/
def bigState : State Tower.rules Nat := ⟨bigBase, [], ∅, fun _ => ⟨bigUniverse _, ⟨.var 0, Derivable.var 0⟩⟩⟩

/-- **The coerce firing across universes**: over `X : U₁`, make `x : X` and `g : Ground`, tell
`(x : X) ≐ (g : Ground)`, and make `x` at `Ground`. The two types are formed at `U₁` and `U₀`. -/
def bigCoerceFiring : Firing setting.levels bigState where
  helpers := .cons TemplateControls.xBig (.cons (groundType _) (.nil _))
  taken := []
  read := []
  takes := []
  reads := []
  makes := [(8, ⟨groundType _, (.var 1 : Tower.Tm 3)⟩)]
  tells := [(xBigRow, gBigRow)]
  guards := []
  queries := []

/-- `x` is not of type `Ground` in its frame: its type is the variable `X`. -/
theorem xBig_not_ground : ¬ Typed Tower.rules bigTriple.raw (.var 1) ground := by
  intro typed
  have le : TypeLe Tower.rules bigTriple.raw (.var 2) ground := Typed.generation typed
  have formed : CtxFormed Tower.rules bigTriple.raw := bigTriple.formed
  have neutral : Neutral (TowerModel.roles (L := Nat)) (.var 2 : Tower.Tm 3) := .var 2
  have equal : TypeEq Tower.rules bigTriple.raw (.var 2) ground :=
    TypeLe.rigid (S := setting) le ⟨.sort Tower.zero, .sort _, ground_typed _⟩ formed
      (fun u _ e => (TypeEq.neutral_form (TowerModel.facts (L := Nat)) e formed neutral
        (.inl ⟨u, rfl⟩)).not_former.1 u rfl)
      (fun A B e => (TypeEq.neutral_form (TowerModel.facts (L := Nat)) e formed neutral
        (.inr (.inl ⟨A, B, rfl⟩))).not_former.2.1 A B rfl)
      (fun A B e => (TypeEq.neutral_form (TowerModel.facts (L := Nat)) e formed neutral
        (.inr (.inr (.inl ⟨A, B, rfl⟩)))).not_former.2.2.1 A B rfl)
  exact (TypeEq.neutral_form (TowerModel.facts (L := Nat)) equal formed neutral
    (.inl ⟨_, rfl⟩)).not_former.1 _ rfl

/-- The present step refuses it. -/
theorem bigCoerce_refused : ¬ (step setting.levels Nat).Admits bigCoerceFiring := by
  rintro ⟨⟨-, -, -, -, typed⟩, -⟩
  exact xBig_not_ground (typed _ (List.mem_singleton_self _))

/-- N3's settler leaves it undecided. -/
theorem bigCoerce_tower_undecided : admits? towerFamilies bigCoerceFiring = none := by decide +kernel

/-- **Decided by the kernel: the computable converting step admits it**: the type equation is extracted
at `U₁`, where `Ground` is typed by cumulativity. -/
theorem bigCoerce_decided : admits? olderFamilies bigCoerceFiring = some true := by decide +kernel

/-- **The separation across universes.** -/
theorem bigCoerce_computable_separation :
    (convertingStep setting.levels Nat olderSettler).Admits bigCoerceFiring ∧
      ¬ (step setting.levels Nat).Admits bigCoerceFiring :=
  ⟨(admits?_sound olderFamilies bigCoerce_decided).mp rfl, bigCoerce_refused⟩

/-! ## Outside the class: the type of the pattern variable is an unknown applied -/

/-- `F : U₀ → U₀`. -/
abbrev fBase : Context Tower.rules := extend (empty Tower.rules) TemplateControls.arrowType

/-- `F Ground`, over `F`. -/
def appliedType : TypeOver fBase :=
  ContextualDependentPatternFiring.Controls.formIn fBase (.app (.var 0) ground) (by decide +kernel)

/-- `F : U₀ → U₀, x : F Ground`. -/
abbrev fPair : Context Tower.rules := extend fBase appliedType

/-- `F : U₀ → U₀, x : F Ground, g : Ground`. -/
abbrev fTriple : Context Tower.rules := extend fPair (groundType _)

/-- The row `x : F Ground`. -/
def xApplied : TotalTerm fTriple :=
  TotalTerm.reindex (⟨appliedType.reindex (projectionHom fBase appliedType), newest fBase appliedType⟩ :
    TotalTerm fPair) (projectionHom fPair (groundType _))

/-- The row `g : Ground`. -/
def gApplied : TotalTerm fTriple :=
  ⟨(groundType fPair).reindex (projectionHom fPair (groundType _)), newest fPair (groundType _)⟩

/-- `(x : F Ground) ≐ (g : Ground)`. -/
abbrev appliedStore : EquationStore (TotalTerm fTriple) := [(xApplied, gApplied)]

/-- **Outside the class, declined**: the type of `x` is the unknown `F` applied to `Ground`, so the
extracted type equation `F Ground ≐ Ground` is no pattern, and the older-unknown family neither settles
nor refutes the store. -/
theorem applied_undecided :
    (olderFamily olderFuel appliedStore).isSettled = false ∧ (olderFamily olderFuel appliedStore).isRefuted = false := by
  decide +kernel

/-! ## The tree's own stuck heterogeneous store -/

/-- The wake-up store of the tree: `snd (X, refl X) ≐ refl Ground` over `X : U₀`, alone. -/
abbrev wakeStore : EquationStore (TotalTerm ContextualDependentFlex.Wakeup.frame) :=
  [ContextualDependentFlex.Wakeup.pending]

/-- **The tree's driver is stuck on it** (as `heterogeneous_alone_is_stuck` shows for its run): its family
neither settles nor refutes it. -/
theorem wake_driver_undecided :
    (driverFamily setting.levels ContextualDependentWorklist.Controls.step 4 wakeStore).isSettled = false ∧
      (driverFamily setting.levels ContextualDependentWorklist.Controls.step 4 wakeStore).isRefuted = false := by
  decide +kernel

/-- **The older-unknown family settles it**: the extracted type equation
`Id U₀ (fst (X, refl X)) (fst (X, refl X)) ≐ Id U₀ Ground Ground` at `U₁` solves `X`, and the woken
equation is discharged. -/
theorem wake_older_settled : (olderFamily olderFuel wakeStore).isSettled = true := by decide +kernel

/-! ## Outside every family: the cross store -/

/-- **No family decides the cross store**: it is solvable and has no initial solution, so a family can
neither settle nor refute it. -/
theorem cross_undecided (F : Family setting.levels) : ¬ (F crossStore).Decisive := by
  intro decisive
  rcases Decision.decided decisive with ⟨M, σ, initial⟩ | none
  · exact cross_no_initial M σ initial
  · exact none fragment_without_principal_answer.2.1

/-- In particular the older-unknown family declines it, and so does the computable settler. -/
theorem cross_older_undecided : ¬ (olderFamily olderFuel crossStore).Decisive ∧ olderSettler crossStore = .postponed :=
  ⟨cross_undecided _, cross_postponed _⟩

end NativeTypesOnTheStep.OlderUnknown.Controls

#print axioms NativeTypesOnTheStep.OlderUnknown.Controls.coerce_extract
#print axioms NativeTypesOnTheStep.OlderUnknown.Controls.coerce_inPlace_alone
#print axioms NativeTypesOnTheStep.OlderUnknown.Controls.coerce_older_settled
#print axioms NativeTypesOnTheStep.OlderUnknown.Controls.coerce_decided
#print axioms NativeTypesOnTheStep.OlderUnknown.Controls.coerce_admitted
#print axioms NativeTypesOnTheStep.OlderUnknown.Controls.coerce_computable_separation
#print axioms NativeTypesOnTheStep.OlderUnknown.Controls.coerce_templated
#print axioms NativeTypesOnTheStep.OlderUnknown.Controls.coerce_typedAfterMatch_computably
#print axioms NativeTypesOnTheStep.OlderUnknown.Controls.coerce_decidedBy
#print axioms NativeTypesOnTheStep.OlderUnknown.Controls.coerce_agrees
#print axioms NativeTypesOnTheStep.OlderUnknown.Controls.coerceDefinition_codes
#print axioms NativeTypesOnTheStep.OlderUnknown.Controls.coerce_in_class
#print axioms NativeTypesOnTheStep.OlderUnknown.Controls.coerce_transition_exact
#print axioms NativeTypesOnTheStep.OlderUnknown.Controls.arrow_unsolvable
#print axioms NativeTypesOnTheStep.OlderUnknown.Controls.arrow_decided
#print axioms NativeTypesOnTheStep.OlderUnknown.Controls.arrow_refused
#print axioms NativeTypesOnTheStep.OlderUnknown.Controls.xBig_not_ground
#print axioms NativeTypesOnTheStep.OlderUnknown.Controls.bigCoerce_refused
#print axioms NativeTypesOnTheStep.OlderUnknown.Controls.bigCoerce_tower_undecided
#print axioms NativeTypesOnTheStep.OlderUnknown.Controls.bigCoerce_decided
#print axioms NativeTypesOnTheStep.OlderUnknown.Controls.bigCoerce_computable_separation
#print axioms NativeTypesOnTheStep.OlderUnknown.Controls.applied_undecided
#print axioms NativeTypesOnTheStep.OlderUnknown.Controls.wake_driver_undecided
#print axioms NativeTypesOnTheStep.OlderUnknown.Controls.wake_older_settled
#print axioms NativeTypesOnTheStep.OlderUnknown.Controls.cross_undecided
#print axioms NativeTypesOnTheStep.OlderUnknown.Controls.cross_older_undecided

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
