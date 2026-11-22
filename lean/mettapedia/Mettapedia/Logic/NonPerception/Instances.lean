import Mettapedia.Logic.NonPerception
import Mettapedia.GSLT.Topos.PresheafEventAbsence
import Mettapedia.OSLF.Syntax.RhoScopedNativeAbsence
import Mettapedia.OSLF.NativeTypes.Decision.Reference.Core
import Mettapedia.GSLT.Logic.ObserverBubble
import Mettapedia.Logic.Propositions.Totality
import Mettapedia.KR.ConceptOntology.ConstructionBase
import Mettapedia.GSLT.Dynamics.CacheCoherence
import Mettapedia.GSLT.Causality.FundedAssayCompletion

/-!
# The non-perception law at work

Eight results across the library state, each for its own carrier, when an absence
of evidence is a negation.  Each is the law of `Mettapedia.Logic.NonPerception` on a
frame built from that carrier; this module builds the frames and re-derives the key
statements from the law, using only each carrier's own structural lemmas (its
reflection proofs, its membership characterizations).

**Absence established under perceptibility.**
1. Presheaf events: present absence is native negation under reflection of source
   fibres (`presheaf_absent_iff_present`; the frame of elements, `presheafFrame`).
2. Scoped rho reactions over retractable futures: native absence is current
   non-enabledness (`rho_permitted_absence_iff_current`), through the reflection of
   the restricted site.
3. Decision backends: a possibility is refuted only on a closed frontier, whose
   coverage makes the listed receipts perceptible (`possibility_refuted_of_closed`).
4. Fragment decisions: inside its fragment a decision is perceptible, so a negative
   answer is a refutation (`fragment_answer_false_iff`).
5. Positive scenario bases: the that's-all truth is perceptibility of every sentence
   at the actual scenario (`thatsAll_iff_perceptible`), so the positive truths settle
   every truth exactly when every sentence is perceptible there
   (`scrutabilityBase_iff_perceptible`).
6. Concept construction at a vantage: "that's all" at a vantage is perceptibility of
   every counterexample (`thatsAllAt_iff_perceptible`).

**Absence without perceptibility is doubt.**
7. Fuel-bounded runs: an exhausted run of an answerable query is in doubt, and
   recording it as a refusal books doubt as absence (`exhaustedAsRefusal_books_doubt`),
   while the sound cache records nothing (`logicalEntry_exhausted_records_nothing`).
8. Funded assays: below the cost the assay is quiet whatever the verdict
   (`underfunded_quiet_both_verdicts`), the budget is in doubt
   (`underfunded_doubt`), and at the cost it becomes perceptible
   (`funded_perceptible`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.NonPerception.Instances

open Mettapedia.Logic.NonPerception

/-! ## 1. Presheaf events -/

section Presheaf

open _root_.CategoryTheory Mettapedia.GSLT.Topos.PresheafEventAbsence

universe u v w

variable {C : Type u} [Category.{v} C] {E P : Cᵒᵖ ⥤ Type w}

/-- The frame of elements: a state is a program at a world; its futures are its
images along the maps out of the world; it is perceived when an admitted event has
it as source. -/
def presheafFrame (source : E ⟶ P) (admitted : Subfunctor E) :
    Frame (Σ world : Cᵒᵖ, P.obj world) where
  Future a b := ∃ change : a.1 ⟶ b.1, b.2 = P.map change a.2
  future_refl a := ⟨𝟙 a.1, by simp⟩
  Perceived a := ∃ event : E.obj a.1, event ∈ admitted.obj a.1 ∧ source.app a.1 event = a.2

/-- Native absence is the frame's absence. -/
theorem presheaf_absent_iff (source : E ⟶ P) (admitted : Subfunctor E)
    (world : Cᵒᵖ) (program : P.obj world) :
    program ∈ (absent source admitted).obj world ↔
      (presheafFrame source admitted).Absent ⟨world, program⟩ := by
  rw [mem_absent]
  constructor
  · intro holds later future perceived
    obtain ⟨change, equal⟩ := future
    obtain ⟨event, member, sourced⟩ := perceived
    exact holds later.1 change ⟨event, member, sourced.trans equal⟩
  · intro absentHere future change perceived
    exact absentHere ⟨future, P.map change program⟩ ⟨change, rfl⟩ perceived

/-- Reflection of source fibres is perceptibility at every element. -/
theorem reflectsAvailability_iff_perceptible (source : E ⟶ P) (admitted : Subfunctor E) :
    ReflectsAvailability source admitted ↔
      ∀ a, (presheafFrame source admitted).Perceptible a := by
  constructor
  · intro reflection here later future perceived
    obtain ⟨change, equal⟩ := future
    obtain ⟨event, member, sourced⟩ := perceived
    exact reflection change here.2 event member (sourced.trans equal)
  · intro perceptible world future change program event member sourced
    exact perceptible ⟨world, program⟩ ⟨future, P.map change program⟩ ⟨change, rfl⟩
      ⟨event, member, sourced⟩

/-- **Present absence is native negation under reflection**, from the law. -/
theorem presheaf_absent_iff_present (source : E ⟶ P) (admitted : Subfunctor E)
    (reflection : ReflectsAvailability source admitted) (world : Cᵒᵖ) (program : P.obj world) :
    program ∈ (absent source admitted).obj world ↔
      ¬ ∃ event : E.obj world, event ∈ admitted.obj world ∧ source.app world event = program := by
  rw [presheaf_absent_iff]
  exact Frame.absent_iff_not_perceived
    ((reflectsAvailability_iff_perceptible source admitted).mp reflection ⟨world, program⟩)

end Presheaf

/-! ## 2. Scoped rho reactions over retractable futures -/

section Rho

open _root_.CategoryTheory Mettapedia.GSLT.Topos.PresheafEventAbsence
open Mettapedia.OSLF.Binding RhoSchema RhoQuotationClassFibres RhoScopedParallelEvents
open RhoScopedEventPresheaf SyntacticRetractionContexts SyntacticRetractionEventAbsence
open RhoScopedNativeAbsence

/-- **Native absence of a reaction over retractable futures is current
non-enabledness**: the law on the restricted site, whose source fibres reflect. -/
theorem rho_permitted_absence_iff_current (admitted : SourceRule → Prop)
    (world : (Object sig)ᵒᵖ) (process : Process world.unop.context.vars) :
    process ∈ (permittedAbsent admitted).obj world ↔ ¬ Enabled admitted process := by
  have law := presheaf_absent_iff_present (restrictSource (source admitted)) ⊤
    (source_fibre_reflection (source admitted)) world process
  simp only [Subfunctor.top_obj, Set.top_eq_univ, Set.mem_univ, true_and] at law
  exact law.trans
    (not_congr (source_fibre_iff_step admitted (Opposite.op world.unop.context) process))

end Rho

/-! ## 3. Decision backends -/

section Decision

open Mettapedia.OSLF.NativeTypes.Decision.Reference.Core Mettapedia.OSLF.Framework
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis Mettapedia.GSLT

universe uS vR

variable {system : GSLT.{uS}} {admitted : system.Term → Prop}

/-- Two stages: the frontier listed at a budget (`false`), and the steps themselves
(`true`). -/
def backendFrame (backend : Backend.{uS, vR} system admitted)
    (predicate : EquationPredicate system) (budget : Nat) (source : system.Term) : Frame Bool where
  Future early late := early = false ∨ early = late
  future_refl _ := Or.inr rfl
  Perceived
    | false => ∃ receipt, receipt ∈ backend.frontier budget source ∧
        predicate (backend.target source receipt)
    | true => ∃ target, system.Step source target ∧ predicate target

/-- **A closed frontier is perceptible**: its coverage lists a witness for every
actual step. -/
theorem backendFrame_perceptible_of_closed (backend : Backend.{uS, vR} system admitted)
    (predicate : EquationPredicate system) (budget : Nat) (source : system.Term)
    (closed : backend.closed budget source = true) :
    (backendFrame backend predicate budget source).Perceptible false := by
  rintro (_ | _) _ perceived
  · exact perceived
  · obtain ⟨actual, step, satisfies⟩ :
        ∃ target, system.Step source target ∧ predicate target := perceived
    obtain ⟨receipt, listed, related⟩ := backend.coverage budget source closed actual step
    exact ⟨receipt, listed, (predicate.2 related).mp satisfies⟩

/-- **The refutation of a possibility on a closed frontier**, from the law. -/
theorem possibility_refuted_of_closed (backend : Backend.{uS, vR} system admitted)
    (predicate : EquationPredicate system) (budget : Nat) (source : system.Term)
    (closed : backend.closed budget source = true)
    (unlisted : ¬ ∃ receipt, receipt ∈ backend.frontier budget source ∧
      predicate (backend.target source receipt)) :
    ¬ ∃ target, system.Step source target ∧ predicate target := by
  have absent := (Frame.absent_iff_not_perceived
    (backendFrame_perceptible_of_closed backend predicate budget source closed)).mpr unlisted
  exact absent true (Or.inl rfl : false = false ∨ false = true)

end Decision

/-! ## 4. Fragment decisions -/

section Fragment

open Mettapedia.GSLT.ObserverBubble

universe uTerm

variable {Term : Type uTerm} {Strong : Term → Term → Prop}

/-- Two stages: the decision's answer (`false`) and the relation itself (`true`), for
a pair inside the fragment. -/
def fragmentFrame (decision : FragmentDecision Strong) (left right : Term)
    (leftIn : decision.Fragment left) (rightIn : decision.Fragment right) : Frame Bool where
  Future early late := early = false ∨ early = late
  future_refl _ := Or.inr rfl
  Perceived
    | false => decision.answer left right leftIn rightIn = true
    | true => Strong left right

/-- Inside its fragment a decision is perceptible. -/
theorem fragmentFrame_perceptible (decision : FragmentDecision Strong) (left right : Term)
    (leftIn : decision.Fragment left) (rightIn : decision.Fragment right) :
    (fragmentFrame decision left right leftIn rightIn).Perceptible false := by
  rintro (_ | _) _ perceived
  · exact perceived
  · exact (decision.answer_exact left right leftIn rightIn).mpr perceived

/-- **A negative answer inside the fragment is a refutation**, from the law. -/
theorem fragment_answer_false_iff (decision : FragmentDecision Strong) (left right : Term)
    (leftIn : decision.Fragment left) (rightIn : decision.Fragment right) :
    decision.answer left right leftIn rightIn = false ↔ ¬ Strong left right := by
  have law := Frame.absent_iff_not_perceived
    (fragmentFrame_perceptible decision left right leftIn rightIn)
  constructor
  · intro answeredFalse
    have notPerceived : ¬ (fragmentFrame decision left right leftIn rightIn).Perceived false := by
      show ¬ decision.answer left right leftIn rightIn = true
      rw [answeredFalse]
      exact Bool.false_ne_true
    exact law.mpr notPerceived true (Or.inl rfl)
  · intro notStrong
    cases answered : decision.answer left right leftIn rightIn with
    | false => rfl
    | true =>
      exact (notStrong ((decision.answer_exact left right leftIn rightIn).mp answered)).elim

end Fragment

/-! ## 5. Positive scenario bases -/

section Scenarios

open Mettapedia.Logic.Propositions

universe uS uW uD uN uP

variable {S : Type uS} {W : Type uW} {D : Type uD} {N : Type uN} {P : Type uP}
variable (I : Interpretation S W D N P) (positive : Set (Sentence N P))

/-- Scenarios ordered by extension, with a sentence perceived where it is verified. -/
def scenarioFrame (sentence : Sentence N P) : Frame S where
  Future actual scenario := I.Extends positive scenario actual
  future_refl actual := Interpretation.Extends.refl I positive actual
  Perceived scenario := scenario ∈ I.primary sentence

/-- **The that's-all truth is perceptibility of every sentence.** -/
theorem thatsAll_iff_perceptible (actual : S) :
    I.ThatsAll positive actual ↔ ∀ sentence, (scenarioFrame I positive sentence).Perceptible actual := by
  constructor
  · intro thatsAll sentence scenario extension verified
    exact (thatsAll scenario extension sentence).mpr verified
  · intro perceptible scenario extension sentence
    constructor
    · intro actualVerifies
      by_cases scenarioVerifies : scenario ∈ I.primary sentence
      · exact scenarioVerifies
      · have negated : scenario ∈ I.primary (.neg sentence) := by
          rw [Interpretation.primary_neg]
          exact scenarioVerifies
        have back : actual ∈ I.primary (.neg sentence) :=
          perceptible (.neg sentence) scenario extension negated
        rw [Interpretation.primary_neg] at back
        exact (back actualVerifies).elim
    · exact perceptible sentence scenario extension

/-- **The positive truths settle every truth exactly when every sentence is
perceptible at the actual scenario.** -/
theorem scrutabilityBase_iff_perceptible (actual : S) :
    I.ScrutabilityBase actual (I.truthsIn actual positive) ↔
      ∀ sentence, (scenarioFrame I positive sentence).Perceptible actual :=
  (I.scrutabilityBase_positiveTruths_iff positive actual).trans
    (thatsAll_iff_perceptible I positive actual)

end Scenarios

/-! ## 6. Concept construction at a vantage -/

section Construction

open Mettapedia.KR.ConceptOntology

universe u v w

variable (B : ConstructionBase.{u, v, w})

/-- Two stages: what is visible at a vantage (`false`) and all phenomena (`true`); a
counterexample to `premise → a` is perceived where one is found. -/
def constructionFrame (vantage : B.Indexicality) (premise : Set B.Abstract) (a : B.Abstract) :
    Frame Bool where
  Future early late := early = false ∨ early = late
  future_refl _ := Or.inr rfl
  Perceived
    | false => ∃ x, x ∈ B.visibleAt vantage ∧ (∀ b, b ∈ premise → B.incidence x b) ∧
        ¬ B.incidence x a
    | true => ∃ x, (∀ b, b ∈ premise → B.incidence x b) ∧ ¬ B.incidence x a

theorem mem_closureAt_iff_not_perceived (vantage : B.Indexicality) (premise : Set B.Abstract)
    (a : B.Abstract) :
    a ∈ B.closureAt vantage premise ↔ ¬ (constructionFrame B vantage premise a).Perceived false := by
  rw [B.mem_closureAt_iff]
  show _ ↔ ¬ ∃ x, x ∈ B.visibleAt vantage ∧ (∀ b, b ∈ premise → B.incidence x b) ∧
    ¬ B.incidence x a
  constructor
  · rintro holds ⟨x, visible, satisfies, notIncident⟩
    exact notIncident (holds x visible satisfies)
  · intro none x visible satisfies
    by_contra notIncident
    exact none ⟨x, visible, satisfies, notIncident⟩

theorem mem_fullClosure_iff_not_perceived (vantage : B.Indexicality) (premise : Set B.Abstract)
    (a : B.Abstract) :
    a ∈ B.fullClosure premise ↔ ¬ (constructionFrame B vantage premise a).Perceived true := by
  rw [B.mem_fullClosure_iff]
  show _ ↔ ¬ ∃ x, (∀ b, b ∈ premise → B.incidence x b) ∧ ¬ B.incidence x a
  constructor
  · rintro holds ⟨x, satisfies, notIncident⟩
    exact notIncident (holds x satisfies)
  · intro none x satisfies
    by_contra notIncident
    exact none ⟨x, satisfies, notIncident⟩

/-- **"That's all" at a vantage is perceptibility of every counterexample.** -/
theorem thatsAllAt_iff_perceptible (vantage : B.Indexicality) (premise : Set B.Abstract) :
    B.thatsAllAt vantage premise ↔
      ∀ a, (constructionFrame B vantage premise a).Perceptible false := by
  unfold ConstructionBase.thatsAllAt
  constructor
  · intro equal a
    rw [Frame.perceptible_iff]
    intro notPerceived
    have inFull : a ∈ B.fullClosure premise := by
      rw [← equal]
      exact (mem_closureAt_iff_not_perceived B vantage premise a).mpr notPerceived
    rintro (_ | _) _ perceived
    · exact notPerceived perceived
    · exact (mem_fullClosure_iff_not_perceived B vantage premise a).mp inFull perceived
  · intro perceptible
    apply Set.Subset.antisymm
    · intro a inClosure
      have notPerceived := (mem_closureAt_iff_not_perceived B vantage premise a).mp inClosure
      have absent := (Frame.absent_iff_not_perceived (perceptible a)).mpr notPerceived
      exact (mem_fullClosure_iff_not_perceived B vantage premise a).mpr
        (absent true (Or.inl rfl))
    · exact B.fullClosure_subset_closureAt vantage premise

end Construction

/-! ## 7. Fuel-bounded runs -/

section Runs

open Mettapedia.GSLT.Dynamics.CacheCoherence

variable {Query Answer : Type}

/-- Two stages: the run at a fuel (`false`) and the logical observation (`true`); an
answer is perceived where it is produced. -/
def runFrame (logical : Query → Option Answer) (run : Query → Nat → RunOutcome Answer)
    (query : Query) (fuel : Nat) : Frame Bool where
  Future early late := early = false ∨ early = late
  future_refl _ := Or.inr rfl
  Perceived
    | false => ∃ answer, run query fuel = .answered answer
    | true => ∃ answer, logical query = some answer

/-- **An exhausted run of an answerable query is in doubt.** -/
theorem exhausted_doubt {logical : Query → Option Answer} {run : Query → Nat → RunOutcome Answer}
    {query : Query} {fuel : Nat} {answer : Answer}
    (exhausted : run query fuel = .exhausted) (answerable : logical query = some answer) :
    (runFrame logical run query fuel).Doubt false := by
  refine ⟨?_, ?_⟩
  · rintro ⟨answer', produced⟩
    rw [exhausted] at produced
    cases produced
  · intro absent
    exact absent true (Or.inl rfl) ⟨answer, answerable⟩

/-- **Recording exhaustion as refusal books doubt as absence**: the frame is in
doubt, yet the faulty policy records "no answer". -/
theorem exhaustedAsRefusal_books_doubt {logical : Query → Option Answer}
    {run : Query → Nat → RunOutcome Answer} {query : Query} {fuel : Nat} {answer : Answer}
    (exhausted : run query fuel = .exhausted) (answerable : logical query = some answer) :
    (runFrame logical run query fuel).Doubt false ∧
      exhaustedAsRefusal (run query fuel) = some none :=
  ⟨exhausted_doubt exhausted answerable, by rw [exhausted]; rfl⟩

/-- The sound cache records nothing at exhaustion. -/
theorem logicalEntry_exhausted_records_nothing {run : Query → Nat → RunOutcome Answer}
    {query : Query} {fuel : Nat} (exhausted : run query fuel = .exhausted) :
    logicalEntry (run query fuel) = none := by
  rw [exhausted]
  rfl

end Runs

/-! ## 8. Funded assays -/

section Assays

open Mettapedia.GSLT.Causality.ComplementaryAssay
open Mettapedia.GSLT.Causality.ResourceInteraction Mettapedia.GSLT.Causality.OccurrenceHistory

universe uX uO

variable {X : Type uX} {Origins : Type uO}

/-- Budgets ordered by size; the verdict is perceived at a budget that affords the
test (`maximal_affordable_verdict`), and not below it (`underfunded_prefix_quiet`). -/
def assayFrame (cost : X → Nat) (value : X) : Frame Nat where
  Future early late := early ≤ late
  future_refl _ := le_refl _
  Perceived budget := cost value ≤ budget

/-- **Below the cost the budget is in doubt.** -/
theorem underfunded_doubt (cost : X → Nat) (value : X) {budget : Nat}
    (underfunded : budget < cost value) : (assayFrame cost value).Doubt budget := by
  refine ⟨fun affordable => absurd affordable (Nat.not_le.mpr underfunded), ?_⟩
  intro absent
  exact absent (cost value) (Nat.le_of_lt underfunded) (le_refl _)

/-- At the cost the verdict is perceptible. -/
theorem funded_perceptible (cost : X → Nat) (value : X) {budget : Nat}
    (affordable : cost value ≤ budget) : (assayFrame cost value).Perceptible budget :=
  Frame.perceptible_of_perceived affordable

/-- **Below the cost the assay is quiet whatever the verdict**: a test and its
negation, which give opposite verdicts, leave the same quiet prefix. -/
theorem underfunded_quiet_both_verdicts [DecidableEq X] [DecidableEq Origins]
    (test : X → Bool) (cost : X → Nat) (session : Nat)
    (origin : Origins) (value : X) (budget : Nat) (underfunded : budget < cost value)
    {target target' : Multiset (Resource X Origins ⊕ Unit)}
    (path : OccurrencePath (paid test cost).presentation
      (marking (ready session origin value) (purse budget)) target)
    (path' : OccurrencePath (paid (fun x => !test x) cost).presentation
      (marking (ready session origin value) (purse budget)) target') :
    outputs (leftPart target) = 0 ∧ outputs (leftPart target') = 0 :=
  ⟨(underfunded_prefix_quiet test cost session origin value budget underfunded path).2.1,
    (underfunded_prefix_quiet (fun x => !test x) cost session origin value budget underfunded
      path').2.1⟩

end Assays

end Mettapedia.Logic.NonPerception.Instances
