import Mettapedia.GSLT.Logic.SaturatedRelativeBisimilarity
import Mettapedia.TypeTheory.Authority

/-!
# Bubbles: an observer class, commitments, and verdict guarantees

A *bubble* packages three components:

* an **observer class** (`observers`, `observations`), whose saturated
  relative equivalence is the bubble's equality;
* **commitments**, a set of principles from a fixed inventory;
* **verdict guarantees**: an `Authority` whose meaning for equality judgments
  is exactly the observer equivalence (`equality_holds`), and a budgeted
  verdict whose outcomes refine as the budget grows (`verdict_budget_mono`).

Decided verdicts are sound for the observer equivalence
(`equality_established_sound`, `equality_refuted_sound`), the bubble's
equality is a congruence for its own observers (`equality_closedUnder`), and a
bubble with more observers over the same observations has a finer equality
(`equality_antitone`).

**Carve-out.**  A `FragmentDecision` decides a strong relation *restricted* to
a decidable fragment: on the fragment its Boolean answer is exact, outside it
the verdict is `outsideFragment`, and the strong relation itself is not
redefined.  The restriction of the strong relation to the fragment is then
decidable (`FragmentDecision.decidableRestriction`).

**Budgeted normal forms.**  A `NormalFormObserver` returns normal forms within
a budget; its `verdict` refines as the budget grows
(`NormalFormObserver.verdict_budget_mono`), and its `certifiedDecision` decides
the strong relation on the fragment where the budget suffices.

**Class observations.**  When an observation reads the equational class of a
term and nothing reduces, every relative equivalence is the equational theory
(`relEquiv_classObservations_iff`): the destructor-complete end of the
observer dial.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ObserverBubble

open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.GSLT.MinimalEnablingContext
open Mettapedia.GSLT.AdmissibleContextCongruence
open Mettapedia.TypeTheory.AuthorityTheory

universe uS uContext uRule uAtom uBudget uJudgment uEvidence uObstruction uBoundary uReceipt
  uTerm

/-- Principles a bubble may commit to.  The inventory carries no compatibility
table: an incompatibility between two principles is a theorem about models,
proved where it is used. -/
inductive Principle where
  | uniquenessOfIdentityProofs
  | functionExtensionality
  | propositionalExtensionality
  | proofIrrelevance
  | univalence
  | excludedMiddle
  | countableChoice
  | dependentChoice
  | choice
  | impredicativeProp
  deriving DecidableEq, Repr

-- The data fields live in independent universes, which occur only together
-- in the universe of the record.
set_option linter.checkUnivs false in
/-- **A bubble.**  Its equality judgment means the saturated equivalence of its
observer class, and its verdicts refine as the budget grows. -/
structure Bubble (S : GSLT.{uS}) (rules : ContextualRules.{uContext, uRule} S)
    (Budget : Type uBudget) [Preorder Budget] where
  observers : AdmissibleClass rules
  observations : ContextualRules.Observations.{uAtom} S
  commitments : Set Principle
  Judgment : Type uJudgment
  authority : Authority.{uJudgment, uEvidence, uObstruction} Judgment
  Boundary : Type uBoundary
  Receipt : Type uReceipt
  verdict : (judgment : Judgment) → Budget → AuthorizedOutcome authority Boundary Receipt judgment
  verdict_budget_mono : ∀ (judgment : Judgment) {small large : Budget}, small ≤ large →
    Outcome.BudgetRefines (verdict judgment small) (verdict judgment large)
  equality : S.Term → S.Term → Judgment
  equality_holds : ∀ left right,
    authority.Holds (equality left right) ↔ observers.RelEquiv observations left right

namespace Bubble

variable {S : GSLT.{uS}} {rules : ContextualRules.{uContext, uRule} S}
variable {Budget : Type uBudget} [Preorder Budget]
variable (bubble : Bubble S rules Budget)

/-- An established equality verdict proves the observer equivalence. -/
theorem equality_established_sound {left right : S.Term} {budget : Budget}
    (answer : (bubble.verdict (bubble.equality left right) budget).asBool = some true) :
    bubble.observers.RelEquiv bubble.observations left right := by
  obtain ⟨evidence, _⟩ := (Outcome.asBool_eq_true_iff _).mp answer
  exact (bubble.equality_holds left right).mp (bubble.authority.evidenceSound _ evidence)

/-- A refuted equality verdict disproves the observer equivalence. -/
theorem equality_refuted_sound {left right : S.Term} {budget : Budget}
    (answer : (bubble.verdict (bubble.equality left right) budget).asBool = some false) :
    ¬ bubble.observers.RelEquiv bubble.observations left right := by
  obtain ⟨obstruction, _⟩ := (Outcome.asBool_eq_false_iff _).mp answer
  exact fun related => bubble.authority.obstructionSound _ obstruction
    ((bubble.equality_holds left right).mpr related)

/-- The bubble's equality is a congruence for the bubble's own observers. -/
theorem equality_closedUnder :
    bubble.observers.ClosedUnder
      (fun left right => bubble.authority.Holds (bubble.equality left right)) := by
  intro context left right admissible holds
  exact (bubble.equality_holds _ _).mpr
    (bubble.observers.relEquiv_closedUnder bubble.observations admissible
      ((bubble.equality_holds _ _).mp holds))

/-- A larger budget never turns an established verdict into a refutation. -/
theorem not_established_then_refuted (judgment : bubble.Judgment) {small large : Budget}
    (le : small ≤ large) {evidence : bubble.authority.Evidence judgment}
    {obstruction : bubble.authority.Obstruction judgment}
    (before : bubble.verdict judgment small = .established evidence) :
    bubble.verdict judgment large ≠ .refuted obstruction := by
  intro after
  have refines := bubble.verdict_budget_mono judgment le
  rw [before, after] at refines
  exact Outcome.not_budget_flip_established_refuted evidence obstruction refines

/-- A larger budget never resolves an outside-fragment verdict. -/
theorem outside_stable (judgment : bubble.Judgment) {small large : Budget} (le : small ≤ large)
    {reason : bubble.Boundary} (before : bubble.verdict judgment small = .outsideFragment reason) :
    bubble.verdict judgment large = .outsideFragment reason := by
  have refines := bubble.verdict_budget_mono judgment le
  rw [before] at refines
  exact Outcome.budget_does_not_resolve_outside reason _ refines

end Bubble

/-- A bubble with more observers over the same observations has a finer
equality. -/
theorem equality_antitone {S : GSLT.{uS}} {rules : ContextualRules.{uContext, uRule} S}
    {Budget : Type uBudget} [Preorder Budget]
    (coarse fine : Bubble S rules Budget)
    (sameObservations : coarse.observations = fine.observations)
    (moreObservers : coarse.observers ≤ fine.observers) {left right : S.Term}
    (holds : fine.authority.Holds (fine.equality left right)) :
    coarse.authority.Holds (coarse.equality left right) := by
  apply (coarse.equality_holds left right).mpr
  rw [sameObservations]
  exact AdmissibleClass.relEquiv_antitone fine.observations moreObservers
    ((fine.equality_holds left right).mp holds)

/-! ## Carve-out: deciding a restriction of a strong relation -/

/-- **A decision for a fragment.**  The fragment is decidable, and on it the
Boolean answer is exactly the strong relation.  The strong relation is a
parameter: it is never redefined. -/
structure FragmentDecision {Term : Type uTerm} (Strong : Term → Term → Prop) where
  Fragment : Term → Prop
  fragmentDecidable : DecidablePred Fragment
  answer : (left right : Term) → Fragment left → Fragment right → Bool
  answer_exact : ∀ left right (leftIn : Fragment left) (rightIn : Fragment right),
    answer left right leftIn rightIn = true ↔ Strong left right

namespace FragmentDecision

variable {Term : Type uTerm} {Strong : Term → Term → Prop}
variable (decision : FragmentDecision Strong)

/-- **The restriction of the strong relation to the fragment is decidable.** -/
@[instance_reducible]
def decidableRestriction :
    DecidableRel (fun left right : {term // decision.Fragment term} => Strong left.1 right.1) :=
  fun left right =>
    decidable_of_iff _ (decision.answer_exact left.1 right.1 left.2 right.2)

/-- The implication form: fragment membership implies the strong relation. -/
@[instance_reducible]
def decidableImplication :
    DecidableRel (fun left right : Term =>
      decision.Fragment left → decision.Fragment right → Strong left right) := fun left right =>
  haveI := decision.fragmentDecidable
  if leftIn : decision.Fragment left then
    if rightIn : decision.Fragment right then
      decidable_of_iff (decision.answer left right leftIn rightIn = true)
        ((decision.answer_exact left right leftIn rightIn).trans
          ⟨fun holds _ _ => holds, fun implied => implied leftIn rightIn⟩)
    else isTrue fun _ rightIn' => absurd rightIn' rightIn
  else isTrue fun leftIn' => absurd leftIn' leftIn

/-- The verdict of a fragment decision: exact inside the fragment, and
`outsideFragment` outside it. -/
def verdict (left right : Term) : Outcome (Strong left right) (¬ Strong left right) Unit Empty :=
  haveI := decision.fragmentDecidable
  if inside : decision.Fragment left ∧ decision.Fragment right then
    if answered : decision.answer left right inside.1 inside.2 = true then
      .established ((decision.answer_exact left right inside.1 inside.2).mp answered)
    else
      .refuted fun holds =>
        answered ((decision.answer_exact left right inside.1 inside.2).mpr holds)
  else
    .outsideFragment ()

/-- Outside the fragment the verdict is `outsideFragment`. -/
theorem verdict_outside {left right : Term}
    (outside : ¬ (decision.Fragment left ∧ decision.Fragment right)) :
    decision.verdict left right = .outsideFragment () := by
  unfold verdict
  rw [dif_neg outside]

/-- Inside the fragment the verdict is decided. -/
theorem verdict_isDecided {left right : Term} (leftIn : decision.Fragment left)
    (rightIn : decision.Fragment right) : (decision.verdict left right).isDecided = true := by
  unfold verdict
  rw [dif_pos ⟨leftIn, rightIn⟩]
  by_cases answered : decision.answer left right leftIn rightIn = true
  · rw [dif_pos answered]
    rfl
  · rw [dif_neg answered]
    rfl

/-- **Inside the fragment the verdict is exact**: established exactly when the
strong relation holds. -/
theorem verdict_asBool_true_iff {left right : Term} (leftIn : decision.Fragment left)
    (rightIn : decision.Fragment right) :
    (decision.verdict left right).asBool = some true ↔ Strong left right := by
  unfold verdict
  rw [dif_pos ⟨leftIn, rightIn⟩]
  by_cases answered : decision.answer left right leftIn rightIn = true
  · rw [dif_pos answered]
    exact ⟨fun _ => (decision.answer_exact left right leftIn rightIn).mp answered,
      fun _ => rfl⟩
  · rw [dif_neg answered]
    exact ⟨fun impossible => absurd impossible (by simp [Outcome.asBool]),
      fun holds => absurd ((decision.answer_exact left right leftIn rightIn).mpr holds) answered⟩

end FragmentDecision

/-! ## Budgeted normal-form observers -/

/-- **A budgeted normaliser for a strong relation.**  With some budget it may
return a normal form; a larger budget returns the same one; and wherever both
normal forms are returned they decide the strong relation. -/
structure NormalFormObserver {Term : Type uTerm} [DecidableEq Term]
    (Strong : Term → Term → Prop) where
  normalForm : ℕ → Term → Option Term
  normalForm_mono : ∀ {fuel fuel' : ℕ} {term result : Term}, fuel ≤ fuel' →
    normalForm fuel term = some result → normalForm fuel' term = some result
  normalForm_exact : ∀ {fuel fuel' : ℕ} {left right leftNormal rightNormal : Term},
    normalForm fuel left = some leftNormal → normalForm fuel' right = some rightNormal →
      (Strong left right ↔ leftNormal = rightNormal)

namespace NormalFormObserver

variable {Term : Type uTerm} [DecidableEq Term] {Strong : Term → Term → Prop}
variable (observer : NormalFormObserver Strong)

/-- Both normal forms, if both are reached within `fuel`. -/
def pair (fuel : ℕ) (left right : Term) : Option (Term × Term) :=
  match observer.normalForm fuel left, observer.normalForm fuel right with
  | some leftNormal, some rightNormal => some (leftNormal, rightNormal)
  | _, _ => none

theorem pair_sound {fuel : ℕ} {left right leftNormal rightNormal : Term}
    (found : observer.pair fuel left right = some (leftNormal, rightNormal)) :
    observer.normalForm fuel left = some leftNormal ∧
      observer.normalForm fuel right = some rightNormal := by
  unfold pair at found
  cases leftFound : observer.normalForm fuel left with
  | none => simp [leftFound] at found
  | some leftNormal' =>
      cases rightFound : observer.normalForm fuel right with
      | none => simp [leftFound, rightFound] at found
      | some rightNormal' =>
          simp only [leftFound, rightFound, Option.some.injEq, Prod.mk.injEq] at found
          obtain ⟨rfl, rfl⟩ := found
          exact ⟨rfl, rfl⟩

theorem pair_mono {fuel fuel' : ℕ} (le : fuel ≤ fuel') {left right : Term} {pair : Term × Term}
    (found : observer.pair fuel left right = some pair) :
    observer.pair fuel' left right = some pair := by
  obtain ⟨leftFound, rightFound⟩ := observer.pair_sound (leftNormal := pair.1)
    (rightNormal := pair.2) found
  unfold NormalFormObserver.pair
  rw [observer.normalForm_mono le leftFound, observer.normalForm_mono le rightFound]

/-- Where both normal forms are reached, the strong relation is their
equality. -/
theorem pair_exact {fuel : ℕ} {left right : Term}
    (found : (observer.pair fuel left right).isSome = true) :
    Strong left right ↔
      ((observer.pair fuel left right).get found).1 = ((observer.pair fuel left right).get found).2 := by
  have equation : observer.pair fuel left right = some ((observer.pair fuel left right).get found) :=
    (Option.some_get found).symm
  obtain ⟨leftFound, rightFound⟩ := observer.pair_sound equation
  exact observer.normalForm_exact leftFound rightFound

/-- **The budgeted verdict**: `outsideFragment` outside the fragment, the
answer of the normal forms when both are reached within `fuel`, and
`incomplete` otherwise. -/
def verdict (Fragment : Term → Prop) [DecidablePred Fragment] (left right : Term) (fuel : ℕ) :
    Outcome (Strong left right) (¬ Strong left right) Unit Unit :=
  if Fragment left ∧ Fragment right then
    if found : (observer.pair fuel left right).isSome = true then
      if same : ((observer.pair fuel left right).get found).1 =
          ((observer.pair fuel left right).get found).2 then
        .established ((observer.pair_exact found).mpr same)
      else
        .refuted fun holds => same ((observer.pair_exact found).mp holds)
    else
      .incomplete ()
  else
    .outsideFragment ()

/-- **Budget monotonicity**: a larger budget only resolves incomplete
verdicts. -/
theorem verdict_budget_mono (Fragment : Term → Prop) [DecidablePred Fragment]
    (left right : Term) {fuel fuel' : ℕ} (le : fuel ≤ fuel') :
    Outcome.BudgetRefines (observer.verdict Fragment left right fuel)
      (observer.verdict Fragment left right fuel') := by
  unfold verdict
  by_cases inside : Fragment left ∧ Fragment right
  · rw [if_pos inside, if_pos inside]
    by_cases found : (observer.pair fuel left right).isSome = true
    · have pairEq : observer.pair fuel left right = some ((observer.pair fuel left right).get found) :=
        (Option.some_get found).symm
      have pairEq' := observer.pair_mono le pairEq
      have found' : (observer.pair fuel' left right).isSome = true := by
        rw [pairEq']
        rfl
      have getEq : (observer.pair fuel' left right).get found' =
          (observer.pair fuel left right).get found := by
        obtain ⟨_, getSome⟩ := Option.eq_some_iff_get_eq.mp pairEq'
        exact getSome
      rw [dif_pos found, dif_pos found']
      by_cases same : ((observer.pair fuel left right).get found).1 =
          ((observer.pair fuel left right).get found).2
      · have same' : ((observer.pair fuel' left right).get found').1 =
            ((observer.pair fuel' left right).get found').2 := by
          rw [getEq]
          exact same
        rw [dif_pos same, dif_pos same']
        exact .established _ _
      · have same' : ¬ ((observer.pair fuel' left right).get found').1 =
            ((observer.pair fuel' left right).get found').2 := by
          rw [getEq]
          exact same
        rw [dif_neg same, dif_neg same']
        exact .refuted _ _
    · rw [dif_neg found]
      split_ifs
      · exact .incompleteEstablished _ _
      · exact .incompleteRefuted _ _
      · exact .incomplete _ _
  · rw [if_neg inside, if_neg inside]
    exact .outsideFragment _

/-- The fragment of terms whose normal form is reached within `budget term`. -/
def Certified (budget : Term → ℕ) (term : Term) : Prop :=
  (observer.normalForm (budget term) term).isSome = true

instance (budget : Term → ℕ) : DecidablePred (observer.Certified budget) :=
  fun term => inferInstanceAs (Decidable ((observer.normalForm (budget term) term).isSome = true))

/-- **Carve-out.**  The strong relation restricted to a certified fragment,
decided by comparing normal forms. -/
def certifiedDecision (budget : Term → ℕ) : FragmentDecision Strong where
  Fragment := observer.Certified budget
  fragmentDecidable := inferInstance
  answer left right leftIn rightIn :=
    decide ((observer.normalForm (budget left) left).get leftIn =
      (observer.normalForm (budget right) right).get rightIn)
  answer_exact left right leftIn rightIn := by
    rw [decide_eq_true_iff]
    exact (observer.normalForm_exact (Option.some_get leftIn).symm
      (Option.some_get rightIn).symm).symm

end NormalFormObserver

/-! ## Class observations: the destructor-complete end -/

/-- Observations that read the equational class of a term. -/
def classObservations (S : GSLT.{uS}) : ContextualRules.Observations.{uS} S where
  Atom := S.Term
  observes representative term := S.Equiv term representative
  observes_resp _ _ _ equivalent :=
    ⟨fun held => S.equations.iseqv.trans (S.equations.iseqv.symm equivalent) held,
      fun held => S.equations.iseqv.trans equivalent held⟩

/-- **When nothing reduces and observations read the equational class, every
relative equivalence is the equational theory.** -/
theorem relEquiv_classObservations_iff {S : GSLT.{uS}} {rules : ContextualRules.{uContext, uRule} S}
    (inert : ∀ source target : S.Term, ¬ S.Step source target) (A : AdmissibleClass rules)
    (left right : S.Term) :
    A.RelEquiv (classObservations S) left right ↔ S.Equiv left right := by
  constructor
  · intro related
    have agree := AdmissibleContextCongruence.bisimilar_observes related
      (right, ⟨rules.identity, A.identity_mem⟩)
    change S.Equiv (rules.plug rules.identity left) right ↔
      S.Equiv (rules.plug rules.identity right) right at agree
    exact S.equations.iseqv.trans (S.equations.iseqv.symm (rules.plug_identity left))
      (agree.mpr (rules.plug_identity right))
  · intro equivalent
    refine ⟨S.Equiv, ⟨?_, ?_, ?_⟩, equivalent⟩
    · intro first _ _ label first' step
      exact absurd step (inert _ _)
    · intro _ second _ label second' step
      exact absurd step (inert _ _)
    · intro first second held atom
      exact (classObservations S).observes_resp atom.1 (rules.plug_resp atom.2.1 held)

end Mettapedia.GSLT.ObserverBubble
