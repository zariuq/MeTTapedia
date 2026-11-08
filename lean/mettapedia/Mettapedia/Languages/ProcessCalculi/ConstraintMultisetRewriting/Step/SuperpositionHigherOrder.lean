import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.SuperpositionGuarded
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.SearchOutcome

/-!
# λ-superposition on the step: the unifier interface and the readings of a side condition

## The rule shapes

λ-superposition (Bentkamp, Blanchette, Tourret, Vukmirović, Waldmann, *Superposition for
higher-order logic*, arXiv 2102.00453) keeps the first-order rule shapes over βη-normal λ-terms,
with unification replaced by a complete set of unifiers:

* `Sup`: `D' ∨ t ≈ t'` into `C' ∨ s[u] ⋈ s'`, for each `σ` in a complete set of unifiers of `t`
  and `u`, `u` not a variable or a fluid term; conclusion `(D' ∨ C' ∨ s[t'] ⋈ s')σ`;
* `FluidSup`: into fluid subterms `u` (applied variables, or λ-terms whose βη-normal form has a
  free head variable), through a fresh variable `z` and a unifier of `z t` and `u`;
* `ERes`, `EFact`: as in the first-order case, with complete sets of unifiers;
* `ArgCong`: from `C' ∨ s ≈ s'`, for fresh variables `x̄`, the conclusion `C' ∨ s x̄ ≈ s' x̄`;
* the extensionality and clausification rules of the variant in use.

On the step, every rule is the shape `unifyFiring` already has: read the premises, tell the
unification problem, make the conclusion, guard the side conditions. What changes is the unifier.

## The unifier interface

A **budgeted unifier enumeration** (`UnifierEnumeration`) reports, at each budget, an outcome in
the outcome algebra (`Search.Outcome`): the unifiers found and whether the enumeration finished.
Every reported unifier solves the problem; a finished report is a complete set of unifiers.

* **A bounded unifier suspends** (`UnifierEnumeration.not_refuted_of_cutOff`): a cut-off enumeration
  never reads as "no unifier", and its unifiers need not form a complete set. The completeness of
  λ-superposition rests on the completeness of its unifier (Bentkamp et al.), not on the step.
* **Pattern fragment.** In the higher-order pattern fragment unification is unitary: the tree's
  contextual pattern solver returns an answer through which every model factors
  (`ContextualPatternTermination.solves_or_refutes`, `ContextualPatternCompleteness`), and the
  dependent solvers (`ContextualDependent*`) extend the same interface. There the three readings
  below coincide (`readings_principal`).

## Where the step's admission differs from committing to one unifier

Let the side condition `G` be co-stable, and let `U` be a minimal complete set of unifiers of the
told problem (`readings_complete`):

* **one firing of the step**, guarded by the closure of `G` and asked at every solution, is admitted
  exactly when `G` holds at **every** member of `U`;
* **a firing committed to one unifier** `u ∈ U` (its told problem having `u` as principal answer) is
  admitted exactly when `G` holds at `u`;
* `G` holds at **some** solution exactly when it holds at some member of `U`.

λ-superposition performs the committed firings, one per unifier satisfying the side conditions.
The single firing of the step is admitted only when all of them are; when unification is unitary
the readings coincide.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Superposition

open Search (Outcome Status)

universe uT uS

variable {T : Type uT} {S : Type uS} (A : SubstitutionAction T S)

/-- **A complete set of unifiers**: every member solves, and every solution is an instance of one. -/
structure CompleteSet (store : EquationStore T) (U : Set S) : Prop where
  sound : ∀ u ∈ U, A.Models u store
  complete : ∀ σ, A.Models σ store → ∃ u ∈ U, Factors A σ u

/-- **A budgeted unifier enumeration**, reporting outcomes of the outcome algebra. -/
structure UnifierEnumeration (store : EquationStore T) where
  report : ℕ → Outcome S
  sound : ∀ n, ∀ u ∈ (report n).answers, A.Models u store
  complete : ∀ n, (report n).status = .finished → ∀ σ, A.Models σ store → ∃ u ∈ (report n).answers, Factors A σ u

variable {A}

/-- **A finished report is a complete set of unifiers.** -/
theorem UnifierEnumeration.completeSet {store : EquationStore T} (enumeration : UnifierEnumeration A store)
    {n : ℕ} (finished : (enumeration.report n).status = .finished) :
    CompleteSet A store {u | u ∈ (enumeration.report n).answers} :=
  ⟨fun u member => enumeration.sound n u member, enumeration.complete n finished⟩

/-- **A bounded unifier suspends**: a cut-off report never reads as "no unifier". -/
theorem UnifierEnumeration.not_refuted_of_cutOff {store : EquationStore T}
    (enumeration : UnifierEnumeration A store) {n : ℕ} (cut : (enumeration.report n).status = .cutOff) :
    (enumeration.report n).verdict ≠ .refuted :=
  Outcome.verdict_ne_refuted_of_cutOff cut

/-- **A refuted report is a proof that there is no unifier.** -/
theorem UnifierEnumeration.no_unifier_of_refuted {store : EquationStore T}
    (enumeration : UnifierEnumeration A store) {n : ℕ} (refuted : (enumeration.report n).verdict = .refuted) :
    ¬ A.Consistent store := by
  rintro ⟨σ, solved⟩
  have zero := (Outcome.verdict_eq_refuted_iff _).mp refuted
  have finished : (enumeration.report n).status = .finished := by rw [zero]; rfl
  obtain ⟨u, member, -⟩ := enumeration.complete n finished σ solved
  rw [zero] at member
  exact Multiset.notMem_zero u member

/-- Over a complete set, the closure of a guard holding at every member is asked at every solution. -/
theorem entails_closure_of_complete {store : EquationStore T} {U : Set S} {G : S → Prop}
    (complete : CompleteSet A store U) (holds : ∀ u ∈ U, G u) : A.Entails store (Closure A store G) := by
  intro σ solved
  obtain ⟨u, member, factors⟩ := complete.complete σ solved
  exact ⟨u, complete.sound u member, factors, holds u member⟩

/-- **The three readings over a minimal complete set of unifiers.** The step's single firing asks the
guard at every member; a firing committed to a member asks it there; existence asks it at some
member. -/
theorem readings_complete {store : EquationStore T} {U : Set S} {G : S → Prop}
    (complete : MinimalComplete A store U) (respects : Respects A G) (coStable : CoStable A G) :
    (A.Entails store (Closure A store G) ↔ ∀ u ∈ U, G u) ∧
      (∀ u ∈ U, ∀ committed : EquationStore T, A.Principal committed u →
        (A.Entails committed (Closure A committed G) ↔ G u)) ∧
      ((∃ σ, A.Models σ store ∧ G σ) ↔ ∃ u ∈ U, G u) :=
  ⟨entails_closure_iff_complete complete respects coStable,
    fun _ _ _ principal => entails_closure_iff principal respects coStable,
    exists_iff_complete complete respects coStable⟩

/-- **The single firing is admitted only when every committed firing is.** -/
theorem single_implies_committed {store : EquationStore T} {U : Set S} {G : S → Prop}
    (complete : MinimalComplete A store U) (respects : Respects A G) (coStable : CoStable A G)
    (single : A.Entails store (Closure A store G)) {u : S} (member : u ∈ U)
    {committed : EquationStore T} (principal : A.Principal committed u) :
    A.Entails committed (Closure A committed G) :=
  (entails_closure_iff principal respects coStable).mpr
    ((entails_closure_iff_complete complete respects coStable).mp single u member)

/-- **With a principal answer the readings coincide**: this is the pattern-fragment case. -/
theorem readings_principal {store : EquationStore T} {μ : S} {G : S → Prop}
    (principal : A.Principal store μ) (respects : Respects A G) (coStable : CoStable A G) :
    (A.Entails store (Closure A store G) ↔ G μ) ∧ ((∃ σ, A.Models σ store ∧ G σ) ↔ G μ) :=
  ⟨entails_closure_iff principal respects coStable, exists_iff_of_coStable principal respects coStable⟩

#print axioms UnifierEnumeration.completeSet
#print axioms UnifierEnumeration.not_refuted_of_cutOff
#print axioms UnifierEnumeration.no_unifier_of_refuted
#print axioms entails_closure_of_complete
#print axioms readings_complete
#print axioms single_implies_committed
#print axioms readings_principal

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Superposition
