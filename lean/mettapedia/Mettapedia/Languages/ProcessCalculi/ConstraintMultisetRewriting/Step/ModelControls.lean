import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ModelFirstOrder

/-!
# Controls for the model family

All controls live in the first-order run layer, over small first-order signatures.

* **The case split** (`boolSig`, `caseSplit_separates`). With constants `true` and `false` and no
  function symbols, `X = true ∨ X = false` is not asked over the empty store: the identity solution
  keeps `X` a variable. It holds at every point of the Herbrand model, where every value is one of
  the two constants. It is not forced at the identity, and it is forced at each branch of the case
  split. A coverage containing the case split would therefore force it and change the ask; the
  presheaf semantics has no covers.
* **Excluded middle** (`excludedMiddle_separates`): `X = true ∨ ¬ X = true` is asked at every
  solution, read pointwise, and is not forced at the identity. Asks agree with forcing on the flat
  fragment only (`Frames.entails_iff_forces`).
* **Absence is forced** (`absence_forced`): over `X = false`, the absence of `true` among the labels
  `{X}` is asked, and by the flat-fragment theorem it is forced at every solution.
* **Confusion** (`unarySig`, `confusion_separates`). With one unary function `f`, the store
  `f X = f Y` asks `X = Y` (constructors are injective in the syntax). In the set model on `Bool`
  where `f` is constant, a point satisfies the store and not `X = Y`. Asks are not sound for set
  points, and that model is not free (`constantModel_not_free`).
* **Occurrences a model cannot tell apart** (`indistinguishable_separates`): in the constant model
  two occurrences labelled `f X` and `f Y` have the same value; taking either is admitted, the
  results differ, and the present values are the same multiset. The multiset readout forgets
  occurrence identity; admission does not depend on the model.
* **The occurs check** (`occurs_separates`): `X = f X` is not solvable, and has a point in the
  one-element set model. A set point does not imply solvability.
* **The empty sort** (`freeSig`, `emptySort_separates`). In a signature with no constants and no
  function symbols, the idle firing at the empty configuration is admitted, and the set model on the
  empty type has no point at all. Realizing admitted firings needs inhabited sorts.
* **The term model is not a point** (`constructorFree_separates`): in the same signature there is no
  ground term, so the Herbrand model has no point while the idle firing is admitted; the free term
  algebra has one (the identity substitution).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

namespace ModelControls

open Interface (Frames GuardFormula)
open Mettapedia.Logic.LP
open Mettapedia.Logic.LP.FirstOrderBridge (language realizeTerm)

/-! ## The case split -/

/-- Two constants, `true` and `false`; no function symbols; variables are numbers. -/
abbrev boolSig : LPSignature where
  constants := Bool
  vars := Nat
  relationSymbols := Empty
  relationArity := Empty.elim
  functionSymbols := Empty
  functionArity := Empty.elim

/-- The one-frame first-order frames over `boolSig`. -/
abbrev boolFrames := Frames.ofSubstitution (FirstOrder.action boolSig)

/-- The variable `X`. -/
def xVar : Term boolSig := .var (0 : Nat)

/-- `X = true ∨ X = false`. -/
def caseSplit : GuardFormula (Term boolSig) Nat :=
  .or (.eq xVar (.const true)) (.eq xVar (.const false))

/-- The branch `X := b` of the case split. -/
def branch (b : Bool) : Subst boolSig := fun n => if n = (0 : Nat) then .const b else .var n

theorem not_eq_const_of_var {n : Nat} {b : Bool} :
    (Term.var n : Term boolSig) ≠ Term.const b := fun same => by cases same

theorem caseSplit_not_identity :
    ¬ boolFrames.Satisfies (a := PUnit.unit) (b := PUnit.unit) (Subst.id boolSig) caseSplit := by
  rintro (same | same)
  · exact not_eq_const_of_var same
  · exact not_eq_const_of_var same

/-- Every ground term over `boolSig` is one of the two constants. -/
theorem groundTerm_cases (g : GroundTerm boolSig) : g = .const true ∨ g = .const false := by
  cases g with
  | const b => cases b <;> simp
  | app symbol _ => exact symbol.elim

/-- **The case split separates asks from closed points and from covers.** -/
theorem caseSplit_separates :
    ¬ boolFrames.Entails (a := PUnit.unit) ([] : EquationStore (Term boolSig))
        (fun b θ => boolFrames.Satisfies (a := PUnit.unit) (b := b) θ caseSplit) ∧
      (∀ g : boolSig.vars → GroundTerm boolSig, (herbrandModel boolSig).Satisfies (a := PUnit.unit) g caseSplit) ∧
      ¬ boolFrames.Forces (a := PUnit.unit) caseSplit PUnit.unit (Subst.id boolSig) ∧
      boolFrames.Forces (a := PUnit.unit) caseSplit PUnit.unit (branch true) ∧
      boolFrames.Forces (a := PUnit.unit) caseSplit PUnit.unit (branch false) := by
  refine ⟨fun asked => caseSplit_not_identity (asked PUnit.unit _ (Frames.models_nil _)), fun g => ?_,
    caseSplit_not_identity, Or.inl rfl, Or.inr rfl⟩
  show g 0 = GroundTerm.const true ∨ g 0 = GroundTerm.const false
  exact groundTerm_cases (g 0)

/-! ## Excluded middle -/

/-- `X = true ∨ ¬ X = true`. -/
def excludedMiddle : GuardFormula (Term boolSig) Nat :=
  .or (.eq xVar (.const true)) (.not (.eq xVar (.const true)))

/-- **Excluded middle is asked pointwise and not forced.** -/
theorem excludedMiddle_separates :
    boolFrames.Entails (a := PUnit.unit) ([] : EquationStore (Term boolSig))
        (fun b θ => boolFrames.Satisfies (a := PUnit.unit) (b := b) θ excludedMiddle) ∧
      ¬ boolFrames.Forces (a := PUnit.unit) excludedMiddle PUnit.unit (Subst.id boolSig) := by
  refine ⟨fun _ _ _ => Classical.em _, ?_⟩
  rintro (forced | forced)
  · exact not_eq_const_of_var forced
  · exact forced PUnit.unit (branch true) rfl

/-! ## Absence -/

/-- The absence of `true` among the labels of `{0}`, where occurrence `0` is labelled `X`. -/
def trueAbsent : GuardFormula (Term boolSig) Nat :=
  .absent (.const true) {0} fun _ => xVar

/-- **Absence over `X = false` is asked and forced.** -/
theorem absence_forced :
    boolFrames.Entails (a := PUnit.unit) [(xVar, .const false)]
        (fun b θ => boolFrames.Satisfies (a := PUnit.unit) (b := b) θ trueAbsent) ∧
      ∀ (b : PUnit) (θ : Subst boolSig), boolFrames.Models (a := PUnit.unit) (b := b) θ [(xVar, .const false)] →
        boolFrames.Forces (a := PUnit.unit) trueAbsent b θ := by
  have asked : boolFrames.Entails (a := PUnit.unit) [(xVar, .const false)]
      (fun b θ => boolFrames.Satisfies (a := PUnit.unit) (b := b) θ trueAbsent) := by
    intro _ θ solved o _ same
    have isFalse : θ 0 = Term.const false := solved _ (List.mem_singleton_self _)
    have isTrue : Term.const true = θ 0 := same
    rw [isFalse] at isTrue
    cases isTrue
  exact ⟨asked, (Frames.entails_iff_forces _ (.absent _ _ _)).mp asked⟩

/-! ## Confusion and the occurs check -/

/-- One constant and one unary function symbol; variables are numbers. -/
abbrev unarySig : LPSignature where
  constants := Unit
  vars := Nat
  relationSymbols := Empty
  relationArity := Empty.elim
  functionSymbols := Unit
  functionArity := fun _ => 1

abbrev unaryFrames := Frames.ofSubstitution (FirstOrder.action unarySig)

/-- `f t`. -/
def apply (t : Term unarySig) : Term unarySig := .app () fun _ => t

/-- The variables `X` and `Y`. -/
def vX : Term unarySig := .var (0 : Nat)
def vY : Term unarySig := .var (1 : Nat)

/-- `Bool` with every symbol interpreted as `false`. -/
@[instance_reducible] def constantStructure : (language unarySig).Structure Bool where
  funMap _ _ := false
  RelMap _ _ := False

/-- The set model on `Bool` where `f` is constant. -/
abbrev constantModel := @setModel unarySig Bool constantStructure

/-- `X := true`, `Y := false`. -/
def splitPoint : unarySig.vars → Bool := fun n => n == (0 : Nat)

/-- **Confusion**: `f X = f Y` asks `X = Y`, and a set point satisfies the store and not `X = Y`. -/
theorem confusion_separates :
    unaryFrames.Entails (a := PUnit.unit) [(apply vX, apply vY)]
        (fun b θ => unaryFrames.Satisfies (O := Nat) (a := PUnit.unit) (b := b) θ (.eq vX vY)) ∧
      constantModel.Models (a := PUnit.unit) splitPoint [(apply vX, apply vY)] ∧
      ¬ constantModel.Satisfies (O := Nat) (a := PUnit.unit) splitPoint (.eq vX vY) := by
  refine ⟨fun _ θ solved => ?_, fun e member => ?_, fun same => ?_⟩
  · have both : (Term.app () fun _ => θ 0 : Term unarySig) = Term.app () fun _ => θ 1 :=
      solved _ (List.mem_singleton_self _)
    exact congrFun (eq_of_heq (Term.app.inj both).2) (0 : Fin 1)
  · obtain rfl := List.mem_singleton.mp member
    rfl
  · exact Bool.noConfusion (same : true = false)

/-- **The constant model is not free.** -/
theorem constantModel_not_free : ¬ constantModel.Free := fun free =>
  confusion_separates.2.2
    (Frames.HenkinModel.sound free confusion_separates.1 splitPoint confusion_separates.2.1)

/-- The one-element structure. -/
@[instance_reducible] def unitStructure : (language unarySig).Structure Unit where
  funMap _ _ := ()
  RelMap _ _ := False

abbrev unitModel := @setModel unarySig Unit unitStructure

/-- **The occurs check**: `X = f X` is not solvable, and has a point in the one-element model. -/
theorem occurs_separates :
    ¬ unaryFrames.Solvable (a := PUnit.unit) [(vX, apply vX)] ∧
      unitModel.Models (a := PUnit.unit) (fun _ => ()) [(vX, apply vX)] := by
  refine ⟨?_, fun _ _ => rfl⟩
  rintro ⟨_, θ, solved⟩
  have cyclic : θ 0 = Term.app () fun _ => θ 0 := solved _ (List.mem_singleton_self _)
  have smaller := Term.size_subterm (f := ()) (ts := fun _ : Fin 1 => θ 0) 0
  rw [← cyclic] at smaller
  exact lt_irrefl _ smaller

/-! ## Occurrences a model cannot tell apart -/

/-- Occurrence `1` is labelled `f X`, every other occurrence `f Y`. -/
def twoLabel : Nat → Term unarySig := fun o => if o = 1 then apply vX else apply vY

/-- Occurrences `1` and `2`, and no knowledge. -/
def twoStart : Configuration (Term unarySig) Nat := ⟨[], {1, 2}⟩

/-- Take occurrence `o` by its own label. -/
def takeOwn (o : Nat) : Firing (Term unarySig) (Subst unarySig) Nat :=
  ⟨⟨[twoLabel o], [], [], [], []⟩, [], ⟨[o], [], []⟩⟩

theorem takeOwn_valid {o : Nat} (present : o = 1 ∨ o = 2) :
    (takeOwn o).Valid (FirstOrder.action unarySig) twoLabel twoStart := by
  refine ⟨⟨List.nodup_singleton o, List.nodup_nil, rfl, rfl, rfl, ?_,
    ⟨Subst.id unarySig, fun e member => ?_⟩, by simp [takeOwn]⟩, by simp [takeOwn]⟩
  · rcases present with rfl | rfl <;> decide
  · have same : e = (twoLabel o, twoLabel o) := by
      simpa [Selection.problem, Selection.equations, takeOwn, twoStart] using member
    subst same
    rfl

/-- **An occurrence the model cannot tell apart from another does not change admission.** In the
constant model the occurrences labelled `f X` and `f Y` have the same value. Taking either is
admitted, the two results differ, and their present values are the same multiset. -/
theorem indistinguishable_separates :
    (takeOwn 1).Valid (FirstOrder.action unarySig) twoLabel twoStart ∧
      (takeOwn 2).Valid (FirstOrder.action unarySig) twoLabel twoStart ∧
      ((takeOwn 1).result twoLabel twoStart).present ≠ ((takeOwn 2).result twoLabel twoStart).present ∧
      ∀ ρ : unarySig.vars → Bool,
        ((takeOwn 1).result twoLabel twoStart).present.val.map
            (fun o => constantModel.eval (a := PUnit.unit) (twoLabel o) ρ) =
          ((takeOwn 2).result twoLabel twoStart).present.val.map
            (fun o => constantModel.eval (a := PUnit.unit) (twoLabel o) ρ) := by
  refine ⟨takeOwn_valid (Or.inl rfl), takeOwn_valid (Or.inr rfl), by decide, fun ρ => ?_⟩
  have allFalse : ∀ o, constantModel.eval (a := PUnit.unit) (twoLabel o) ρ = false := fun o => by
    unfold twoLabel
    split <;> rfl
  simp only [allFalse]
  decide

/-! ## The empty sort and the constructor-free signature -/

/-- No constants and no function symbols; variables are numbers. -/
abbrev freeSig : LPSignature where
  constants := Empty
  vars := Nat
  relationSymbols := Empty
  relationArity := Empty.elim
  functionSymbols := Empty
  functionArity := Empty.elim

/-- The empty type as a structure. -/
@[instance_reducible] def emptyStructure : (language freeSig).Structure Empty where
  funMap
    | .constant symbol, _ => symbol.elim
    | .function symbol, _ => symbol.elim
  RelMap _ _ := False

abbrev emptyModel := @setModel freeSig Empty emptyStructure

/-- The firing that takes, reads, tells, checks and makes nothing. -/
def idle : Firing (Term freeSig) (Subst freeSig) Nat := ⟨⟨[], [], [], [], []⟩, [], ⟨[], [], []⟩⟩

/-- The empty configuration. -/
def start : Configuration (Term freeSig) Nat := ⟨[], ∅⟩

/-- Every occurrence labelled by the variable `0`. -/
def freeLabel : Nat → Term freeSig := fun _ => .var (0 : Nat)

theorem idle_valid : idle.Valid (FirstOrder.action freeSig) freeLabel start :=
  ⟨⟨List.nodup_nil, List.nodup_nil, rfl, rfl, rfl, by decide,
    ⟨Subst.id freeSig, fun _ member => by simp [Selection.problem, Selection.equations, idle, start] at member⟩,
    by simp [idle]⟩, by simp [idle]⟩

/-- **The empty sort**: the idle firing is admitted, and the empty structure has no point. -/
theorem emptySort_separates :
    idle.Valid (FirstOrder.action freeSig) freeLabel start ∧ IsEmpty (freeSig.vars → Empty) :=
  ⟨idle_valid, ⟨fun ρ => (ρ (0 : Nat)).elim⟩⟩

theorem groundTerm_freeSig_empty : IsEmpty (GroundTerm freeSig) :=
  ⟨fun g => by
    cases g with
    | const symbol => exact symbol.elim
    | app symbol _ => exact symbol.elim⟩

/-- **The term model is not a point**: the idle firing is admitted, the Herbrand model of the
constructor-free signature has no point, and the free term algebra has one, which satisfies the
firing's information. -/
theorem constructorFree_separates :
    idle.Valid (FirstOrder.action freeSig) freeLabel start ∧
      IsEmpty (freeSig.vars → GroundTerm freeSig) ∧
      (termModel freeSig).Models (a := PUnit.unit) (Subst.id freeSig) (idle.result freeLabel start).equations :=
  ⟨idle_valid, ⟨fun g => groundTerm_freeSig_empty.false (g (0 : Nat))⟩,
    fun _ member => by simp [Firing.result, Selection.result, Selection.problem, Selection.equations, idle, start] at member⟩

end ModelControls

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting

#print axioms AnnotatedRuns.ModelControls.caseSplit_separates
#print axioms AnnotatedRuns.ModelControls.excludedMiddle_separates
#print axioms AnnotatedRuns.ModelControls.absence_forced
#print axioms AnnotatedRuns.ModelControls.confusion_separates
#print axioms AnnotatedRuns.ModelControls.constantModel_not_free
#print axioms AnnotatedRuns.ModelControls.occurs_separates
#print axioms AnnotatedRuns.ModelControls.takeOwn_valid
#print axioms AnnotatedRuns.ModelControls.indistinguishable_separates
#print axioms AnnotatedRuns.ModelControls.idle_valid
#print axioms AnnotatedRuns.ModelControls.emptySort_separates
#print axioms AnnotatedRuns.ModelControls.constructorFree_separates

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
