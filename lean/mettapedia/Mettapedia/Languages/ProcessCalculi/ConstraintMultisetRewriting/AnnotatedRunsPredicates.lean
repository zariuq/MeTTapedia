import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsPaths
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsAnnotations
import Mettapedia.CategoryTheory.PredicateDoctrine

/-!
# Predicates over runs: a first-order doctrine and its fibration

Every object of the run category is a single configuration class, so a predicate on the state at
an object would not change along a run. Predicates over runs are predicates on **histories**: at
a class `x`, a predicate is a set of runs from a fixed root to `x`.

## The doctrine of histories

For any category and any root (`historyDoctrine`, `historyFirstOrder`):

* the fibre at `x` is the Boolean algebra of sets of arrows from the root to `x`;
* **reindexing along a run** `p : x ⟶ y` takes a predicate on histories at `y` to the histories at
  `x` whose extension by `p` satisfies it (`reindex_iff`);
* **existence along `p`** is the image: the strongest postcondition. **Universality along `p`** is
  the kernel image. They are the two adjoints of reindexing, Frobenius reciprocity holds, and both
  satisfy Beck–Chevalley on every pullback square, because arrows out of the root turn pullbacks
  into pullbacks of sets.

This is a `PredicateDoctrine.FirstOrder` doctrine. Its total category is fibred over the base by
`PredicateDoctrine.IndexedHeyting.projection_fibered`, and its arrows are **Hoare triples on
histories** (`hoare_iff`): an arrow from `(x, φ)` to `(y, ψ)` is a run `p` such that every
history in `φ`, extended by `p`, lies in `ψ`.

## Descent along a functor

Pulling history predicates back along a functor commutes with reindexing and preserves the
Boolean operations (`pullbackAlong_reindex`, `pullbackAlong_himp`, ...). A predicate is a pullback
exactly when it does not separate arrows with one image (`descends_iff`); when the functor is
surjective on arrows out of the root, the pullback is injective (`pullbackAlong_injective`).

## Predicates on traces are predicates closed under round equivalence

For the run category of the candidate step and its contextual traces (`ContextualTraces`), a
predicate on runs from `C₀` is a predicate on traces exactly when it is closed under round
equivalence of words (`tracePredicate_iff`, from `trace_eq_iff_roundEquiv`).

* `PredicateControls.order_not_trace_predicate`: "the taker fired first" holds of one order of the
  round of the taker and the reader and not of the other: it is a predicate on runs and not on
  traces.
* `PredicateControls.taker_fired_trace_predicate`: "the taker fired" is a predicate on traces.
-/

set_option autoImplicit false

open CategoryTheory

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

open Mettapedia.CategoryTheory.PredicateDoctrine

/-! ## The doctrine of histories -/

section Histories

universe uB vB uB' vB'

variable {B : Type uB} [Category.{vB} B] (root : B)

/-- **Predicates on histories**: at `x`, the sets of arrows from the root to `x`; reindexing along
an arrow extends a history by it. -/
abbrev historyDoctrine : IndexedHeyting.{uB, vB, vB} B where
  Fiber x := Set (root ⟶ x)
  reindex f φ := (· ≫ f) ⁻¹' φ
  reindex_mono _ := fun _ _ sub => Set.preimage_mono sub
  reindex_id _ φ := by
    ext h
    simp
  reindex_comp f g φ := by
    ext h
    simp
  reindex_top _ := Set.preimage_univ
  reindex_bot _ := Set.preimage_empty
  reindex_inf _ _ _ := Set.preimage_inter
  reindex_sup _ _ _ := Set.preimage_union
  reindex_himp f φ ψ := by
    ext h
    simp only [himp_eq, Set.sup_eq_union, Set.mem_preimage, Set.mem_union, Set.mem_compl_iff]

theorem reindex_iff {x y : B} (p : x ⟶ y) (ψ : Set (root ⟶ y)) (h : root ⟶ x) :
    h ∈ (historyDoctrine root).reindex p ψ ↔ h ≫ p ∈ ψ := Iff.rfl

/-- **The first-order doctrine of histories**: existence is the image along postcomposition,
universality its kernel image. -/
abbrev historyFirstOrder : FirstOrder.{uB, vB, vB} B where
  toIndexedHeyting := historyDoctrine root
  existsAlong f φ := (· ≫ f) '' φ
  forallAlong f φ := Set.kernImage (· ≫ f) φ
  exists_mono _ := Set.image_preimage.monotone_l
  forall_mono _ := Set.preimage_kernImage.monotone_u
  exists_adj _ := Set.image_preimage
  forall_adj _ := Set.preimage_kernImage
  frobenius f φ ψ := Set.image_inter_preimage (· ≫ f) φ ψ
  exists_baseChange := by
    intro P Q R S top left right bottom pullback φ
    ext k
    change k ≫ bottom ∈ (· ≫ right) '' φ ↔ k ∈ (· ≫ left) '' ((· ≫ top) ⁻¹' φ)
    constructor
    · rintro ⟨h, inφ, same⟩
      obtain ⟨g, gTop, gLeft⟩ := pullback.exists_lift h k same
      exact ⟨g, by simpa [Set.mem_preimage, gTop] using inφ, gLeft⟩
    · rintro ⟨g, inφ, rfl⟩
      exact ⟨g ≫ top, inφ, by simp only [Category.assoc, pullback.w]⟩
  forall_baseChange := by
    intro P Q R S top left right bottom pullback φ
    ext k
    change k ≫ bottom ∈ Set.kernImage (· ≫ right) φ ↔
      k ∈ Set.kernImage (· ≫ left) ((· ≫ top) ⁻¹' φ)
    constructor
    · intro all g gLeft
      have gLeft' : g ≫ left = k := gLeft
      exact all (show (g ≫ top) ≫ right = k ≫ bottom by
        rw [Category.assoc, pullback.w, ← Category.assoc, gLeft'])
    · intro all h same
      obtain ⟨g, gTop, gLeft⟩ := pullback.exists_lift h k same
      have := all gLeft
      rw [Set.mem_preimage, gTop] at this
      exact this

theorem exists_iff {x y : B} (p : x ⟶ y) (φ : Set (root ⟶ x)) (k : root ⟶ y) :
    k ∈ (historyFirstOrder root).existsAlong p φ ↔ ∃ h ∈ φ, h ≫ p = k := Iff.rfl

theorem forall_iff {x y : B} (p : x ⟶ y) (φ : Set (root ⟶ x)) (k : root ⟶ y) :
    k ∈ (historyFirstOrder root).forallAlong p φ ↔ ∀ h : root ⟶ x, h ≫ p = k → h ∈ φ :=
  ⟨fun all _ same => all same, fun all _ same => all _ same⟩

/-- **Arrows of the total category are Hoare triples on histories.** -/
theorem hoare_iff (a b : (historyDoctrine root).Total) :
    Nonempty (a ⟶ b) ↔
      ∃ p : a.base ⟶ b.base, ∀ h : root ⟶ a.base,
        h ∈ (show Set (root ⟶ a.base) from a.fiber) →
          h ≫ p ∈ (show Set (root ⟶ b.base) from b.fiber) := by
  constructor
  · rintro ⟨arrow⟩
    obtain ⟨p, entails⟩ := (historyDoctrine root).totalHomEquiv a b arrow
    exact ⟨p, fun _ member => entails member⟩
  · rintro ⟨p, entails⟩
    exact ⟨((historyDoctrine root).totalHomEquiv a b).symm ⟨p, fun h member => entails h member⟩⟩

/-! ### Descent along a functor -/

variable {B' : Type uB'} [Category.{vB'} B'] (F : B ⥤ B')

/-- Pull a predicate on histories of `F` back to histories. -/
def pullbackAlong {x : B} (ψ : Set (F.obj root ⟶ F.obj x)) : Set (root ⟶ x) := F.map ⁻¹' ψ

/-- **Pulling back commutes with reindexing.** -/
theorem pullbackAlong_reindex {x y : B} (p : x ⟶ y) (ψ : Set (F.obj root ⟶ F.obj y)) :
    pullbackAlong root F ((historyDoctrine (F.obj root)).reindex (F.map p) ψ) =
      (historyDoctrine root).reindex p (pullbackAlong root F ψ) := by
  ext h
  change F.map h ≫ F.map p ∈ ψ ↔ F.map (h ≫ p) ∈ ψ
  rw [F.map_comp]

theorem pullbackAlong_inf {x : B} (φ ψ : Set (F.obj root ⟶ F.obj x)) :
    pullbackAlong root F (φ ⊓ ψ) = pullbackAlong root F φ ⊓ pullbackAlong root F ψ :=
  Set.preimage_inter

theorem pullbackAlong_sup {x : B} (φ ψ : Set (F.obj root ⟶ F.obj x)) :
    pullbackAlong root F (φ ⊔ ψ) = pullbackAlong root F φ ⊔ pullbackAlong root F ψ :=
  Set.preimage_union

theorem pullbackAlong_himp {x : B} (φ ψ : Set (F.obj root ⟶ F.obj x)) :
    pullbackAlong root F (φ ⇨ ψ) = pullbackAlong root F φ ⇨ pullbackAlong root F ψ := by
  ext h
  simp only [pullbackAlong, himp_eq, Set.sup_eq_union, Set.mem_preimage, Set.mem_union,
    Set.mem_compl_iff]

theorem pullbackAlong_top {x : B} : pullbackAlong root F (⊤ : Set (F.obj root ⟶ F.obj x)) = ⊤ :=
  Set.preimage_univ

theorem pullbackAlong_bot {x : B} : pullbackAlong root F (⊥ : Set (F.obj root ⟶ F.obj x)) = ⊥ :=
  Set.preimage_empty

/-- **A predicate is a pullback exactly when it does not separate arrows with one image.** -/
theorem descends_iff {x : B} (φ : Set (root ⟶ x)) :
    (∃ ψ : Set (F.obj root ⟶ F.obj x), pullbackAlong root F ψ = φ) ↔
      ∀ h h' : root ⟶ x, F.map h = F.map h' → (h ∈ φ ↔ h' ∈ φ) := by
  constructor
  · rintro ⟨ψ, rfl⟩ h h' same
    change F.map h ∈ ψ ↔ F.map h' ∈ ψ
    rw [same]
  · intro closed
    refine ⟨F.map '' φ, Set.Subset.antisymm ?_ fun h member => ⟨h, member, rfl⟩⟩
    rintro h ⟨h', member, same⟩
    exact (closed h' h same).mp member

/-- **When every arrow of `F` out of the root is an image, pulling back is injective.** -/
theorem pullbackAlong_injective {x : B}
    (surjective : Function.Surjective (F.map : (root ⟶ x) → (F.obj root ⟶ F.obj x))) :
    Function.Injective (pullbackAlong root F (x := x)) :=
  Set.preimage_injective.mpr surjective

end Histories

/-! ## Predicates over runs of the candidate step -/

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

section RunPredicates

open Mettapedia.GSLT.Causality.OccurrenceHistory (OccurrencePath)
open Mettapedia.GSLT.Causality.EventConcurrency (Trace)
open Mettapedia.GSLT.Causality.TraceCostValuation (traceFunctor)

variable (A : SubstitutionAction T S) (label : O → T) (C₀ : Configuration T O)

/-- The class of a configuration, as an object of the run category. -/
abbrev runObject (C : Configuration T O) : Runs A label := classOf A label C

/-- **The doctrine of predicates over runs from `C₀`**: at a class, the sets of runs from `C₀` to
it; reindexing along a run extends by it. -/
abbrev runPredicates : FirstOrder (Runs A label) :=
  historyFirstOrder (B := Runs A label) (classOf A label C₀)

/-- **The doctrine of predicates over contextual traces from `C₀`.** -/
abbrev tracePredicates : FirstOrder (ContextualTraces A label) :=
  historyFirstOrder (B := ContextualTraces A label) (classOf A label C₀)

/-- Every trace from `C₀` is the trace of a run. -/
theorem trace_surjective (y : Runs A label) :
    Function.Surjective ((traceFunctor (concurrency A label).tiles).map :
      (runObject A label C₀ ⟶ y) →
        ((traceFunctor (concurrency A label).tiles).obj (classOf A label C₀) ⟶
          (traceFunctor (concurrency A label).tiles).obj y)) := by
  intro trace
  obtain ⟨p, rfl⟩ := Quotient.exists_rep trace
  exact ⟨p, rfl⟩

/-- **A predicate on runs is a predicate on contextual traces exactly when it is closed under
round equivalence.** -/
theorem tracePredicate_iff {y : Runs A label}
    (φ : Set (runObject A label C₀ ⟶ y)) :
    (∃ ψ : Set ((traceFunctor (concurrency A label).tiles).obj (classOf A label C₀) ⟶
        (traceFunctor (concurrency A label).tiles).obj y),
      pullbackAlong (runObject A label C₀) (traceFunctor (concurrency A label).tiles)
        ψ = φ) ↔
      ∀ p q : OccurrencePath (presentation A label) (classOf A label C₀) y,
        RoundEquiv A label C₀ (OccurrencePath.sites p) (OccurrencePath.sites q) →
          (p ∈ φ ↔ q ∈ φ) := by
  refine (descends_iff (runObject A label C₀) (traceFunctor (concurrency A label).tiles) φ).trans ?_
  constructor
  · intro closed p q equivalent
    exact closed p q ((trace_eq_iff_roundEquiv A label p q).mpr equivalent)
  · intro closed p q same
    exact closed p q ((trace_eq_iff_roundEquiv A label p q).mp same)

/-- Predicates on traces embed into predicates on runs. -/
theorem tracePredicates_embed (y : Runs A label) :
    Function.Injective (pullbackAlong (runObject A label C₀)
      (traceFunctor (concurrency A label).tiles) (x := y)) :=
  pullbackAlong_injective _ _ (trace_surjective A label C₀ y)

end RunPredicates

/-! ## Controls -/

namespace PredicateControls

open Mettapedia.Logic.LP
open ConstraintMultisetRewriting.Controls (signature A)
open AnnotatedRuns.Controls (label Run taker reader start)
open Mettapedia.GSLT.Causality.OccurrenceHistory (OccurrencePath)
open Mettapedia.GSLT.Causality.TraceCostValuation (traceFunctor)

/-- The class the round of the taker and the reader reaches. -/
abbrev roundEnd : Runs A label := classOf A label (follow label start [taker, reader])

/-- "The taker fired first." -/
def takerFirst : Set (runObject A label start ⟶ roundEnd) :=
  {p | OccurrencePath.sites p = [taker, reader]}

/-- "The taker fired." -/
def takerFired : Set (runObject A label start ⟶ roundEnd) :=
  {p | taker ∈ OccurrencePath.sites p}

/-- **Negative control: an order is a predicate on runs, not on traces.** -/
theorem order_not_trace_predicate :
    ¬ ∃ ψ, pullbackAlong (runObject A label start)
      (traceFunctor (concurrency A label).tiles) ψ = takerFirst := by
  intro descends
  have closed := (tracePredicate_iff A label start takerFirst).mp descends
  obtain ⟨p, q, pSites, qSites, related⟩ := PathControls.round_paths_one_trace
  have equivalent := (traceEq_iff_roundEquiv A label p q).mp related
  have inQ : OccurrencePath.sites q = [taker, reader] := (closed p q equivalent).mp pSites
  have both : [reader, taker] = [taker, reader] := qSites.symm.trans inQ
  exact AnnotationControls.taker_ne_reader (List.cons.inj both).1.symm

/-- **Positive control: a bag property is a predicate on traces.** -/
theorem taker_fired_trace_predicate :
    ∃ ψ, pullbackAlong (runObject A label start)
      (traceFunctor (concurrency A label).tiles) ψ = takerFired := by
  refine (tracePredicate_iff A label start takerFired).mpr ?_
  intro p q equivalent
  exact (RoundEquiv.perm A label equivalent).mem_iff

end PredicateControls

#print axioms historyDoctrine
#print axioms historyFirstOrder
#print axioms reindex_iff
#print axioms exists_iff
#print axioms forall_iff
#print axioms hoare_iff
#print axioms pullbackAlong_reindex
#print axioms pullbackAlong_himp
#print axioms descends_iff
#print axioms pullbackAlong_injective
#print axioms trace_surjective
#print axioms tracePredicate_iff
#print axioms tracePredicates_embed
#print axioms PredicateControls.order_not_trace_predicate
#print axioms PredicateControls.taker_fired_trace_predicate

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns
