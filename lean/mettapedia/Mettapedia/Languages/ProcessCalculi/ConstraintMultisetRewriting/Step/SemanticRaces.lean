import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.SemanticCalculi
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RacePair
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RaceCopying
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RaceDeterminate
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RaceHistories
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RaceWeakBranching
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RaceWeakControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RaceStepControls

/-!
# The race programs are programs of the ordinary step

A program (`offers ℓ f`: the firings offered under each label) is **ordinary** (`Ordinary`) when
every firing it offers reads labels through solutions. An ordinary program moves exactly as its
restriction to the ordinary step (`moves_semantic_iff`, `bisimilar_semantic_iff`), and equivalence
modulo the knowledge relative to the identities its firings name is a bisimulation for it
(`Ordinary.bisimilar`, from `Observation.ModuloEquivalent.program_bisimilar`).

* **General classes**: programs whose firings have no predicate query (`ordinary_of_queries`), the
  determinate fragment of ground firings (`fragment_ordinary`), and pure programs
  (`pureProgram_ordinary`).
* **The race programs of `Step/Race*`**: the race pair (`pair_ordinary`), the triggered race pair
  (`triggered_ordinary`), the copying pair (`copying_ordinary`), Milner's third τ-law program
  (`milner_ordinary`), the weak controls (`weak_ordinary`, `inert_ordinary`) and the step controls
  (`step₃_ordinary`, `step₄_ordinary`). No firing in those modules carries a predicate query.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Semantic

open AnnotatedRuns (Firing)
open Observation (ModuloEquivalent)

universe uT uS uO uL

section Programs

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O] {L : Type uL}
  (A : SubstitutionAction T S) (offers : L → Firing T S O → Prop)

/-- **An ordinary program**: every firing it offers reads labels through solutions. -/
def Ordinary : Prop := ∀ ℓ f, offers ℓ f → IsSemantic A f

/-- **The restriction of a program to the ordinary step.** -/
def semanticOffers (ℓ : L) (f : Firing T S O) : Prop := offers ℓ f ∧ IsSemantic A f

variable {A offers}

omit [DecidableEq O] in
/-- **A program whose firings have no predicate query is ordinary.** -/
theorem ordinary_of_queries (none : ∀ ℓ f, offers ℓ f → f.queries = []) : Ordinary A offers :=
  fun ℓ f offered => isSemantic_of_queries_nil (none ℓ f offered)

omit [DecidableEq O] in
/-- An ordinary program is its own restriction to the ordinary step. -/
theorem semanticOffers_eq (ordinary : Ordinary A offers) : semanticOffers A offers = offers :=
  funext fun ℓ => funext fun f => propext ⟨And.left, fun offered => ⟨offered, ordinary ℓ f offered⟩⟩

/-- **An ordinary program moves as in the ordinary step.** -/
theorem moves_semantic_iff (label : O → T) (ordinary : Ordinary A offers) {C D : Configuration T O}
    {ℓ : L} : Race.Moves A label offers C ℓ D ↔ Race.Moves A label (semanticOffers A offers) C ℓ D := by
  rw [semanticOffers_eq ordinary]

/-- **An ordinary program has the bisimilarity of its restriction to the ordinary step.** -/
theorem bisimilar_semantic_iff (label : O → T) (ordinary : Ordinary A offers)
    {C D : Configuration T O} :
    Race.Bisimilar A label offers C D ↔ Race.Bisimilar A label (semanticOffers A offers) C D := by
  rw [semanticOffers_eq ordinary]

/-- **Equivalence modulo the knowledge is a bisimulation for an ordinary program**, relative to
identities that include every identity its firings name. -/
theorem Ordinary.bisimilar {label : O → T} {E : Finset O} (ordinary : Ordinary A offers)
    (named : ∀ ℓ f, offers ℓ f → f.names ⊆ E) {C D : Configuration T O}
    (h : ModuloEquivalent A label E C D) : Race.Bisimilar A label offers C D :=
  h.program_bisimilar fun ℓ f offered => ⟨named ℓ f offered, ordinary ℓ f offered⟩

/-- **The determinate fragment is ordinary**: its firings are ground. -/
theorem fragment_ordinary {label : O → T} (fragment : Race.Fragment label offers) :
    Ordinary A offers :=
  fun ℓ f offered => isSemantic_of_ground A (fragment.ground ℓ f offered)

/-- **A pure program is ordinary.** -/
theorem pureProgram_ordinary (pure : Race.PureProgram offers) : Ordinary A offers :=
  fun ℓ f offered => isSemantic_of_pure A (pure ℓ f offered)

end Programs

/-! ## The race programs -/

section Races

variable {T : Type uT} {S : Type uS} (A : SubstitutionAction T S)

/-- **The race pair is ordinary.** -/
theorem pair_ordinary (t : Race.Pair.Tags T) : Ordinary A (Race.Pair.offers (S := S) t) := by
  refine ordinary_of_queries fun r f offered => ?_
  have none : ∀ g ∈ Race.Pair.alphabet (S := S) t, g.queries = [] := by
    simp [Race.Pair.alphabet, Race.Pair.aP, Race.Pair.aQb, Race.Pair.aQc, Race.Pair.bP, Race.Pair.cP,
      Race.Pair.bQ, Race.Pair.cQ]
  exact none f offered.1

/-- **The triggered race pair is ordinary.** -/
theorem triggered_ordinary (τ : T) : Ordinary A (Race.Triggered.offers (S := S) τ) :=
  fun ℓ f offered => triggered_isSemantic A τ (ℓ, f) offered

/-- **The copying pair is ordinary.** -/
theorem copying_ordinary (τ : T) : Ordinary A (Race.Copying.offers (S := S) τ) := by
  refine ordinary_of_queries fun ℓ f offered => ?_
  have none : ∀ x ∈ Race.Copying.alphabet (S := S) τ, x.2.queries = [] := by
    simp [Race.Copying.alphabet, Race.Copying.firing]
  exact none (ℓ, f) offered

/-- **Milner's third τ-law program is ordinary.** -/
theorem milner_ordinary (τ : T) : Ordinary A (Race.Milner.offers (S := S) τ) := by
  refine ordinary_of_queries fun ℓ f offered => ?_
  have none : ∀ x ∈ Race.Milner.alphabet (S := S) τ, x.2.queries = [] := by
    simp [Race.Milner.alphabet, Race.Milner.firing]
  exact none (ℓ, f) offered

/-- **The program of the weak controls is ordinary.** -/
theorem weak_ordinary (τ : T) : Ordinary A (Race.WeakControls.offers (S := S) τ) := by
  refine ordinary_of_queries fun ℓ f offered => ?_
  have none : ∀ x ∈ Race.WeakControls.alphabet (S := S) τ, x.2.queries = [] := by
    simp [Race.WeakControls.alphabet, Race.WeakControls.pA, Race.WeakControls.pB,
      Race.WeakControls.pC, Race.WeakControls.qA, Race.WeakControls.qb, Race.WeakControls.qc,
      Race.WeakControls.qB, Race.WeakControls.qC, Race.WeakControls.tx, Race.WeakControls.ay,
      Race.WeakControls.az, Race.WeakControls.spin, Race.WeakControls.firing,
      Race.WeakControls.reader]
  exact none (ℓ, f) offered

/-- **The program of the inert control is ordinary.** -/
theorem inert_ordinary (τ : T) : Ordinary A (Race.WeakControls.Inert.offers₂ (S := S) τ) := by
  refine ordinary_of_queries fun ℓ f offered => ?_
  have none : ∀ x ∈ Race.WeakControls.Inert.alphabet₂ (S := S) τ, x.2.queries = [] := by
    simp [Race.WeakControls.Inert.alphabet₂, Race.WeakControls.Inert.tz, Race.WeakControls.Inert.bz,
      Race.WeakControls.firing]
  exact none (ℓ, f) offered

/-- **The programs of the step controls are ordinary.** -/
theorem step₃_ordinary (τ : T) :
    Ordinary A (Race.StepControls.offers (Race.StepControls.alphabet₃ (S := S) τ)) := by
  refine ordinary_of_queries fun ℓ f offered => ?_
  have none : ∀ x ∈ Race.StepControls.alphabet₃ (S := S) τ, x.2.queries = [] := by
    simp [Race.StepControls.alphabet₃, Race.StepControls.fa, Race.StepControls.fb,
      Race.StepControls.ga₁, Race.StepControls.gb₁, Race.StepControls.gb₂, Race.StepControls.ga₂,
      Race.StepControls.firing]
  exact none (ℓ, f) offered

theorem step₄_ordinary (τ : T) :
    Ordinary A (Race.StepControls.offers (Race.StepControls.alphabet₄ (S := S) τ)) := by
  refine ordinary_of_queries fun ℓ f offered => ?_
  have none : ∀ x ∈ Race.StepControls.alphabet₄ (S := S) τ, x.2.queries = [] := by
    simp [Race.StepControls.alphabet₄, Race.StepControls.fa, Race.StepControls.fb,
      Race.StepControls.ha, Race.StepControls.hb, Race.StepControls.hs, Race.StepControls.ht,
      Race.StepControls.firing]
  exact none (ℓ, f) offered

end Races

#print axioms ordinary_of_queries
#print axioms semanticOffers_eq
#print axioms moves_semantic_iff
#print axioms bisimilar_semantic_iff
#print axioms Ordinary.bisimilar
#print axioms fragment_ordinary
#print axioms pureProgram_ordinary
#print axioms pair_ordinary
#print axioms triggered_ordinary
#print axioms copying_ordinary
#print axioms milner_ordinary
#print axioms weak_ordinary
#print axioms inert_ordinary
#print axioms step₃_ordinary
#print axioms step₄_ordinary

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Semantic
