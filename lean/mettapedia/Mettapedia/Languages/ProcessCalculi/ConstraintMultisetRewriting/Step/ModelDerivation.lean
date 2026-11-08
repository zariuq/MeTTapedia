import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ModelFirstOrder
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrderChecks

/-!
# A proof logic for the first-order checks, sound and complete for Henkin models

Henkin completeness needs three things: a syntax, a derivability relation and a model class.

* **Syntax**: the checks of the first-order run layer (equality, absence, count), read as guard
  formulas by `checkGuard`.
* **Derivability** (`CertainChecks.Derives problem label world check`): the certain-check calculus.
  Its rules read the principal answer of the occurs-checked unifier `unifyTotal` and refute
  candidate matches by unification (`FirstOrderChecks.compatible`):
  - `equal`: the answer identifies both sides;
  - `absent`: no occurrence of the region is compatible with the pattern;
  - `count`: the answer matches exactly `number` occurrences, and every other occurrence of the
    region is incompatible with the pattern.
  The calculus is the existing executable `acceptsCertainCheck` (`derives_iff_accepts`).
* **Model class**: the free Henkin models of the one-frame first-order frames (`ModelHenkin`).

**Soundness and completeness.** A derived check holds at every point, satisfying the store, of
every free model in every universe (`derives_sound_free`); a check that holds at every generic point
of a store with a generic point is derivable (`derives_complete_generic`); the generic model is free.
**One set model suffices** (`derives_iff_termModel`): the free term algebra, with the substitutions
as its points, in the universe of the terms. The Herbrand model is sound and not
complete (`oneConstant_separates`): over one constant `c`, `X = c` holds at every ground point and is
not derivable.

**Admission as derivation** (`admitsDerivably_iff`): a query-free first-order firing is admitted
exactly when its shapes and enabling hold, the unifier accepts its information, and each of its
checks is derivable from its information.

**Consistency of the proof logic** (`not_derives_clash`, `not_admitsDerivably_clash`): for distinct
constants `c ≠ d`, the judgment `c = d` is derivable from no store, and the admission of the firing
that tells `c = d` is not derivable. The proof is semantic: a derivation would make `c = d` hold at
a point of the free term algebra. Hypotheses: two distinct constants. Axioms: `propext`,
`Quot.sound`, `Classical.choice`. Universe: that of the signature's terms.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

/-- The firing that tells `c = d` and does nothing else. -/
def tellClash {σ : Mettapedia.Logic.LP.LPSignature} {O : Type*} (c d : σ.constants) :
    Firing (Mettapedia.Logic.LP.Term σ) (Mettapedia.Logic.LP.Subst σ) O :=
  ⟨⟨[], [], [(.const c, .const d)], [], []⟩, [], ⟨[], [], []⟩⟩

namespace CertainChecks

open Interface (Frames GuardFormula)
open Mettapedia.Logic.LP
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled)
open FirstOrderChecks (compatible compatible_iff possible certain acceptsCertainCheck accepts_iff)

variable {σ : LPSignature} [DecidableEq σ.vars] [DecidableEq σ.constants]
  [DecidableEq σ.functionSymbols] {O : Type} [DecidableEq O]

/-- **The certain-check calculus**: the judgment that a check holds at every solution of a store,
over the labelled region `world`. -/
inductive Derives (problem : EquationStore (Term σ)) (label : O → Term σ) (world : Finset O) :
    Check (Term σ) → Prop
  | equal {answer : Subst σ} {left right : Term σ} :
      unifyTotal problem = some answer → answer.applyTerm left = answer.applyTerm right →
      Derives problem label world (.equal left right)
  | absent {answer : Subst σ} {pattern : Term σ} :
      unifyTotal problem = some answer →
      (∀ o ∈ world, compatible problem pattern (label o) = false) →
      Derives problem label world (.absent pattern)
  | count {answer : Subst σ} {pattern : Term σ} {number : Nat} :
      unifyTotal problem = some answer →
      (certain answer label world pattern).card = number →
      (∀ o ∈ world, answer.applyTerm pattern = answer.applyTerm (label o) ∨
        compatible problem pattern (label o) = false) →
      Derives problem label world (.count pattern number)

/-- An occurrence the answer matches is compatible with the pattern. -/
theorem compatible_of_answer {problem : EquationStore (Term σ)} {answer : Subst σ}
    (computed : unifyTotal problem = some answer) {left right : Term σ}
    (same : answer.applyTerm left = answer.applyTerm right) : compatible problem left right = true := by
  apply (compatible_iff problem left right).mpr
  refine ⟨answer, ((FirstOrder.action σ).models_append _ _ _).mpr ⟨unifyTotal_sound problem answer computed, ?_⟩⟩
  intro e member
  obtain rfl := List.mem_singleton.mp member
  exact same

/-- **The calculus is the executable certain-check acceptance.** -/
theorem derives_iff_accepts (problem : EquationStore (Term σ)) (label : O → Term σ) (world : Finset O)
    (check : Check (Term σ)) :
    Derives problem label world check ↔ acceptsCertainCheck problem label world check = true := by
  constructor
  · intro derivation
    cases derivation with
    | equal computed same =>
        simp only [acceptsCertainCheck, computed, same, decide_true]
    | @absent _ pattern computed refuted =>
        simp only [acceptsCertainCheck, computed, decide_eq_true_eq]
        apply Finset.filter_eq_empty_iff.mpr
        intro o member
        simp [refuted o member]
    | @count answer pattern number computed card covered =>
        simp only [acceptsCertainCheck, computed, decide_eq_true_eq]
        refine ⟨card, ?_⟩
        ext o
        simp only [possible, certain, Finset.mem_filter]
        constructor
        · rintro ⟨member, compat⟩
          exact ⟨member, (covered o member).resolve_right (by simp [compat])⟩
        · rintro ⟨member, same⟩
          exact ⟨member, compatible_of_answer computed same⟩
  · intro accepted
    cases computed : unifyTotal problem with
    | none => simp [acceptsCertainCheck, computed] at accepted
    | some answer =>
        cases check with
        | equal left right =>
            simp only [acceptsCertainCheck, computed, decide_eq_true_eq] at accepted
            exact .equal computed accepted
        | absent pattern =>
            simp only [acceptsCertainCheck, computed, decide_eq_true_eq] at accepted
            refine .absent computed fun o member => ?_
            have outside := Finset.filter_eq_empty_iff.mp accepted member
            simpa using outside
        | count pattern number =>
            simp only [acceptsCertainCheck, computed, decide_eq_true_eq] at accepted
            obtain ⟨card, same⟩ := accepted
            refine .count computed card fun o member => ?_
            by_cases compat : compatible problem pattern (label o) = true
            · left
              have inPossible : o ∈ possible problem label world pattern :=
                Finset.mem_filter.mpr ⟨member, compat⟩
              rw [same] at inPossible
              exact (Finset.mem_filter.mp inPossible).2
            · right
              simpa using compat

/-- **Derivability is consistency and the ask.** -/
theorem derives_iff_entails (problem : EquationStore (Term σ)) (label : O → Term σ) (world : Finset O)
    (check : Check (Term σ)) :
    Derives problem label world check ↔ (FirstOrder.action σ).Consistent problem ∧
      (FirstOrder.action σ).Entails problem fun θ => check.Holds (FirstOrder.action σ) θ label world :=
  (derives_iff_accepts problem label world check).trans (accepts_iff problem label world check)

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] [DecidableEq O] in
/-- The ask of a check, read at the frames. -/
theorem entails_iff_frames (problem : EquationStore (Term σ)) (label : O → Term σ) (world : Finset O)
    (check : Check (Term σ)) :
    (FirstOrder.action σ).Entails problem (fun θ => check.Holds (FirstOrder.action σ) θ label world) ↔
      (Frames.ofSubstitution (FirstOrder.action σ)).Entails (a := PUnit.unit) problem
        (fun b θ => (Frames.ofSubstitution (FirstOrder.action σ)).Satisfies (a := PUnit.unit) (b := b) θ
          (checkGuard label world check)) :=
  ⟨fun asked _ θ solved => (checkGuard_sat (FirstOrder.action σ) θ label world check).mpr (asked θ solved),
    fun asked θ solved => (checkGuard_sat (FirstOrder.action σ) θ label world check).mp
      (asked PUnit.unit θ solved)⟩

/-- **Soundness for the free Henkin models**: a derived check holds at every point, satisfying the
store, of every free model, in every universe. -/
theorem derives_sound_free {problem : EquationStore (Term σ)} {label : O → Term σ} {world : Finset O}
    {check : Check (Term σ)} (derivation : Derives problem label world check) {V : Type*}
    {Q : PUnit.{1} → Type*} (M : (Frames.ofSubstitution (FirstOrder.action σ)).HenkinModel V Q)
    (free : M.Free) (q : Q PUnit.unit) (known : M.Models q problem) :
    M.Satisfies q (checkGuard label world check) :=
  Frames.HenkinModel.sound free ((entails_iff_frames problem label world check).mp
    ((derives_iff_entails problem label world check).mp derivation).2) q known

/-- **Completeness at the generic model**: a check that holds at every generic point satisfying a
store with a generic point is derivable. The generic model is free (`Frames.generic_free`), so the
free Henkin models are a sound and complete class for the calculus. -/
theorem derives_complete_generic {problem : EquationStore (Term σ)} {label : O → Term σ}
    {world : Finset O} {check : Check (Term σ)}
    (consistent : ∃ q : Σ _ : PUnit.{1}, Subst σ,
      (Frames.generic (Frames.ofSubstitution (FirstOrder.action σ))).Models (a := PUnit.unit) q problem)
    (valid : ∀ q : Σ _ : PUnit.{1}, Subst σ,
      (Frames.generic (Frames.ofSubstitution (FirstOrder.action σ))).Models (a := PUnit.unit) q problem →
        (Frames.generic (Frames.ofSubstitution (FirstOrder.action σ))).Satisfies (a := PUnit.unit) q
          (checkGuard label world check)) :
    Derives problem label world check := by
  refine (derives_iff_entails problem label world check).mpr ⟨?_, ?_⟩
  · obtain ⟨q, known⟩ := consistent
    exact (Frames.ofSubstitution_solvable_iff _ _).mp
      ((Frames.solvable_iff_generic (X := Frames.ofSubstitution (FirstOrder.action σ)) (a := PUnit.unit)
        problem).mpr ⟨q, known⟩)
  · exact (entails_iff_frames problem label world check).mpr (Frames.complete valid)

/-- **One set model suffices**: the free term algebra, whose points are the substitutions. -/
theorem derives_iff_termModel (problem : EquationStore (Term σ)) (label : O → Term σ) (world : Finset O)
    (check : Check (Term σ)) :
    Derives problem label world check ↔
      (∃ θ : σ.vars → Term σ, (termModel σ).Models (a := PUnit.unit) θ problem) ∧
      ∀ θ : σ.vars → Term σ, (termModel σ).Models (a := PUnit.unit) θ problem →
        (termModel σ).Satisfies (a := PUnit.unit) θ (checkGuard label world check) := by
  rw [derives_iff_entails, entails_iff_frames, entails_iff_termModel]
  refine and_congr ⟨fun ⟨θ, solved⟩ => ⟨θ, (Frames.HenkinModel.models_iff_of_realizes
      (termModel_realizes θ) problem).mpr solved⟩, fun ⟨θ, known⟩ => ⟨θ, (Frames.HenkinModel.models_iff_of_realizes
      (termModel_realizes θ) problem).mp known⟩⟩ Iff.rfl

/-- **Soundness in the Herbrand model.** -/
theorem derives_herbrand_sound {problem : EquationStore (Term σ)} {label : O → Term σ} {world : Finset O}
    {check : Check (Term σ)} (derivation : Derives problem label world check) (g : σ.vars → GroundTerm σ)
    (known : (herbrandModel σ).Models (a := PUnit.unit) g problem) :
    (herbrandModel σ).Satisfies (a := PUnit.unit) g (checkGuard label world check) :=
  herbrand_sound ((entails_iff_frames problem label world check).mp
    ((derives_iff_entails problem label world check).mp derivation).2) g known

/-! ## Admission as derivation -/

variable (label : O → Term σ)

/-- **Derivable admission** of a first-order firing: its shapes and enabling, the unifier's acceptance
of its information, and a derivation of each of its checks from its information. -/
def AdmitsDerivably (C : Configuration (Term σ) O) (f : Firing (Term σ) (Subst σ) O) : Prop :=
  (firstOrder (FirstOrder.action σ) label).Shapes (s := C) f ∧
    Enabled (fun _ : O => ()) C.present (f.selection.commit (T := Unit)) ∧
    (unifyTotal (f.selection.problem label f.rule C)).isSome ∧
    ∀ check ∈ f.rule.checks, Derives (f.selection.problem label f.rule C) label C.present check

/-- **A query-free firing is admitted exactly when its admission is derivable.** -/
theorem admitsDerivably_iff {C : Configuration (Term σ) O} {f : Firing (Term σ) (Subst σ) O}
    (noQueries : f.queries = []) : AdmitsDerivably label C f ↔ f.Valid (FirstOrder.action σ) label C := by
  rw [firstOrder_admits_iff, Frames.ofSubstitution_solvable_iff]
  unfold AdmitsDerivably
  have consistent : (unifyTotal (f.selection.problem label f.rule C)).isSome = true ↔
      (FirstOrder.action σ).Consistent (f.selection.problem label f.rule C) := by
    rw [Option.isSome_iff_exists]
    exact FirstOrder.accepted_iff_consistent _
  refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
  rw [consistent]
  constructor
  · rintro ⟨solvable, derived⟩
    refine ⟨solvable, fun b θ solved => ⟨fun check member =>
      ((derives_iff_entails _ label C.present check).mp (derived check member)).2 θ solved, ?_⟩⟩
    intro query member
    rw [noQueries] at member
    cases member
  · rintro ⟨solvable, asked⟩
    exact ⟨solvable, fun check member => (derives_iff_entails _ label C.present check).mpr
      ⟨solvable, fun θ solved => (asked PUnit.unit θ solved).1 check member⟩⟩

/-! ## Consistency of the proof logic -/

variable {label}

/-- A derivation needs a consistent store. -/
theorem Derives.consistent {problem : EquationStore (Term σ)} {world : Finset O} {check : Check (Term σ)}
    (derivation : Derives problem label world check) : (FirstOrder.action σ).Consistent problem :=
  ((derives_iff_entails problem label world check).mp derivation).1

/-- **The judgment `c = d` is not derivable for distinct constants**, from any store. A derivation
would make `c = d` hold at a point of the free term algebra. -/
theorem not_derives_clash {c d : σ.constants} (distinct : c ≠ d) (problem : EquationStore (Term σ))
    (world : Finset O) : ¬ Derives problem label world (.equal (.const c) (.const d)) := by
  intro derivation
  obtain ⟨⟨θ, solved⟩, valid⟩ := (derives_iff_termModel problem label world _).mp derivation
  have holds := valid θ solved
  change @FirstOrderBridge.realizeTerm σ (Term σ) termStructure θ (.const c) =
    @FirstOrderBridge.realizeTerm σ (Term σ) termStructure θ (.const d) at holds
  have left := realizeTerm_termStructure θ (.const c)
  have right := realizeTerm_termStructure θ (.const d)
  rw [left, right] at holds
  exact distinct (Term.const.inj holds)

/-- **The admission of the firing that tells `c = d` is not derivable.** -/
theorem not_admitsDerivably_clash {c d : σ.constants} (distinct : c ≠ d) (C : Configuration (Term σ) O) :
    ¬ AdmitsDerivably label C (tellClash (O := O) c d) := by
  rintro ⟨_, _, accepted, _⟩
  obtain ⟨θ, solved⟩ := (FirstOrder.accepted_iff_consistent _).mp (Option.isSome_iff_exists.mp accepted)
  have told : (FirstOrder.action σ).Solves θ (.const c, .const d) :=
    solved _ (by simp [Selection.problem, tellClash])
  exact distinct (Term.const.inj told)

/-! ## Control: the Herbrand model is not complete -/

/-- One constant, no function symbols, variables are numbers. -/
abbrev oneSig : LPSignature where
  constants := Unit
  vars := Nat
  relationSymbols := Empty
  relationArity := Empty.elim
  functionSymbols := Empty
  functionArity := Empty.elim

/-- `X = c`. -/
def xIsC : Check (Term oneSig) := .equal (.var (0 : Nat)) (.const ())

/-- **The Herbrand model is sound and not complete**: over one constant, `X = c` holds at every
ground point and is not derivable from the empty store. -/
theorem oneConstant_separates :
    (∀ g : oneSig.vars → GroundTerm oneSig,
      (herbrandModel oneSig).Satisfies (a := PUnit.unit) g (checkGuard (fun _ : Nat => Term.const ()) ∅ xIsC)) ∧
      ¬ Derives (σ := oneSig) ([] : EquationStore (Term oneSig)) (fun _ : Nat => Term.const ()) ∅ xIsC := by
  refine ⟨fun g => ?_, fun derivation => ?_⟩
  · show g 0 = GroundTerm.const ()
    cases g 0 with
    | const _ => rfl
    | app symbol _ => exact symbol.elim
  · have asked := ((derives_iff_entails (σ := oneSig) _ _ _ _).mp derivation).2 (Subst.id oneSig)
      (fun _ member => by simp at member)
    have same : (Term.var (0 : Nat) : Term oneSig) = Term.const () := asked
    cases same

end CertainChecks

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting

#print axioms AnnotatedRuns.CertainChecks.derives_iff_accepts
#print axioms AnnotatedRuns.CertainChecks.derives_iff_entails
#print axioms AnnotatedRuns.CertainChecks.derives_sound_free
#print axioms AnnotatedRuns.CertainChecks.derives_complete_generic
#print axioms AnnotatedRuns.CertainChecks.derives_iff_termModel
#print axioms AnnotatedRuns.CertainChecks.derives_herbrand_sound
#print axioms AnnotatedRuns.CertainChecks.admitsDerivably_iff
#print axioms AnnotatedRuns.CertainChecks.not_derives_clash
#print axioms AnnotatedRuns.CertainChecks.not_admitsDerivably_clash
#print axioms AnnotatedRuns.CertainChecks.oneConstant_separates

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
