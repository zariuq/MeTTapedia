import Mettapedia.Logic.Relation.Normalization

/-!
# Observations along exact embeddings of reduction relations

An exact embedding identifies the successors of an embedded element with the
images of its original successors. It preserves and reflects may, must,
reachable and deterministic observations. Normal forms are conserved; conversion
additionally requires confluence of the larger relation.

The fork and confluent-entry controls separate these obligations without fixing
a syntax, a language, or an evaluator.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Relation.ObservationTransport

open _root_.Relation
open Mettapedia.Logic.Relation (IsNormal Confluent)

/-! ## Observation classes -/

/-- What an observer says of a term, given a step relation and a claim on
terms. -/
abbrev ObservationClass : Type 1 :=
  ∀ {Term : Type}, (Term → Term → Prop) → (Term → Prop) → Term → Prop

/-- Some successor satisfies the claim. -/
def May : ObservationClass := fun step claim term => ∃ next, step term next ∧ claim next

/-- Every successor satisfies the claim. -/
def Must : ObservationClass := fun step claim term => ∀ next, step term next → claim next

/-- Some reduct satisfies the claim. -/
def MayReach : ObservationClass := fun step claim term =>
  ∃ reduct, ReflTransGen step term reduct ∧ claim reduct

/-- Every reduct satisfies the claim. -/
def MustReach : ObservationClass := fun step claim term =>
  ∀ reduct, ReflTransGen step term reduct → claim reduct

/-- At most one successor. -/
def Functional {Term : Type} (step : Term → Term → Prop) (term : Term) : Prop :=
  ∀ first second, step term first → step term second → first = second

/-- Determinism: every reduct has at most one successor.  It reads no claim. -/
def Deterministic : ObservationClass := fun step _ term =>
  ∀ reduct, ReflTransGen step term reduct → Functional step reduct

/-! ## Exact embeddings -/

/-- An exact embedding of one step relation into another: the successors of an
embedded term are exactly the images of the successors of the term. -/
structure ExactEmbedding {Term Term' : Type} (step : Term → Term → Prop)
    (step' : Term' → Term' → Prop) where
  embed : Term → Term'
  injective : Function.Injective embed
  exact : ∀ term next', step' (embed term) next' ↔ ∃ next, step term next ∧ embed next = next'

/-- The image of a claim along an embedding. -/
def imageClaim {Term Term' : Type} (embed : Term → Term') (claim : Term → Prop) :
    Term' → Prop :=
  fun next' => ∃ next, embed next = next' ∧ claim next

/-- An observation class is transport-invariant when exact embeddings neither
create nor destroy its observations. -/
def TransportInvariant (observe : ObservationClass) : Prop :=
  ∀ {Term Term' : Type} {step : Term → Term → Prop} {step' : Term' → Term' → Prop}
    (embedding : ExactEmbedding step step') (claim : Term → Prop) (term : Term),
    observe step' (imageClaim embedding.embed claim) (embedding.embed term) ↔
      observe step claim term

/-- An observation class grows with steps when adding steps never destroys an
observation. -/
def GrowsWithSteps (observe : ObservationClass) : Prop :=
  ∀ {Term : Type} {step step' : Term → Term → Prop},
    (∀ source target, step source target → step' source target) →
      ∀ claim term, observe step claim term → observe step' claim term

namespace ExactEmbedding

variable {Term Term' : Type} {step : Term → Term → Prop} {step' : Term' → Term' → Prop}
  (embedding : ExactEmbedding step step')

/-- The reducts of an embedded term are exactly the images of its reducts. -/
theorem reach_iff (term : Term) (reduct' : Term') :
    ReflTransGen step' (embedding.embed term) reduct' ↔
      ∃ reduct, ReflTransGen step term reduct ∧ embedding.embed reduct = reduct' := by
  constructor
  · intro reaches
    induction reaches with
    | refl => exact ⟨term, ReflTransGen.refl, rfl⟩
    | tail _ stepped inductionHypothesis =>
        obtain ⟨reduct, reachesReduct, rfl⟩ := inductionHypothesis
        obtain ⟨next, stepNext, rfl⟩ := (embedding.exact reduct _).mp stepped
        exact ⟨next, reachesReduct.tail stepNext, rfl⟩
  · rintro ⟨reduct, reaches, rfl⟩
    induction reaches with
    | refl => exact ReflTransGen.refl
    | tail _ stepped inductionHypothesis =>
        exact inductionHypothesis.tail ((embedding.exact _ _).mpr ⟨_, stepped, rfl⟩)

theorem imageClaim_embed_iff (claim : Term → Prop) (term : Term) :
    imageClaim embedding.embed claim (embedding.embed term) ↔ claim term := by
  constructor
  · rintro ⟨other, same, holds⟩
    rwa [embedding.injective same] at holds
  · intro holds
    exact ⟨term, rfl, holds⟩

/-- An embedded term has at most one successor exactly when the term has. -/
theorem functional_iff (term : Term) :
    Functional step' (embedding.embed term) ↔ Functional step term := by
  constructor
  · intro functional first second stepFirst stepSecond
    exact embedding.injective (functional _ _
      ((embedding.exact _ _).mpr ⟨first, stepFirst, rfl⟩)
      ((embedding.exact _ _).mpr ⟨second, stepSecond, rfl⟩))
  · intro functional first' second' stepFirst' stepSecond'
    obtain ⟨first, firstStep, rfl⟩ := (embedding.exact _ _).mp stepFirst'
    obtain ⟨second, secondStep, rfl⟩ := (embedding.exact _ _).mp stepSecond'
    rw [functional first second firstStep secondStep]

end ExactEmbedding

theorem may_transportInvariant : TransportInvariant May := by
  intro Term Term' step step' embedding claim term
  constructor
  · rintro ⟨next', stepped, holds⟩
    obtain ⟨next, stepNext, rfl⟩ := (embedding.exact term next').mp stepped
    exact ⟨next, stepNext, (embedding.imageClaim_embed_iff claim next).mp holds⟩
  · rintro ⟨next, stepped, holds⟩
    exact ⟨embedding.embed next, (embedding.exact term _).mpr ⟨next, stepped, rfl⟩,
      next, rfl, holds⟩

theorem must_transportInvariant : TransportInvariant Must := by
  intro Term Term' step step' embedding claim term
  constructor
  · intro must next stepped
    exact (embedding.imageClaim_embed_iff claim next).mp
      (must _ ((embedding.exact term _).mpr ⟨next, stepped, rfl⟩))
  · intro must next' stepped
    obtain ⟨next, stepNext, rfl⟩ := (embedding.exact term next').mp stepped
    exact ⟨next, rfl, must next stepNext⟩

theorem mayReach_transportInvariant : TransportInvariant MayReach := by
  intro Term Term' step step' embedding claim term
  constructor
  · rintro ⟨reduct', reaches, holds⟩
    obtain ⟨reduct, reachesReduct, rfl⟩ := (embedding.reach_iff term reduct').mp reaches
    exact ⟨reduct, reachesReduct, (embedding.imageClaim_embed_iff claim reduct).mp holds⟩
  · rintro ⟨reduct, reaches, holds⟩
    exact ⟨embedding.embed reduct, (embedding.reach_iff term _).mpr ⟨reduct, reaches, rfl⟩,
      reduct, rfl, holds⟩

theorem mustReach_transportInvariant : TransportInvariant MustReach := by
  intro Term Term' step step' embedding claim term
  constructor
  · intro must reduct reaches
    exact (embedding.imageClaim_embed_iff claim reduct).mp
      (must _ ((embedding.reach_iff term _).mpr ⟨reduct, reaches, rfl⟩))
  · intro must reduct' reaches
    obtain ⟨reduct, reachesReduct, rfl⟩ := (embedding.reach_iff term reduct').mp reaches
    exact ⟨reduct, rfl, must reduct reachesReduct⟩

theorem deterministic_transportInvariant : TransportInvariant Deterministic := by
  intro Term Term' step step' embedding claim term
  constructor
  · intro deterministic reduct reaches
    exact (embedding.functional_iff reduct).mp
      (deterministic _ ((embedding.reach_iff term _).mpr ⟨reduct, reaches, rfl⟩))
  · intro deterministic reduct' reaches
    obtain ⟨reduct, reachesReduct, rfl⟩ := (embedding.reach_iff term reduct').mp reaches
    exact (embedding.functional_iff reduct).mpr (deterministic reduct reachesReduct)

theorem may_growsWithSteps : GrowsWithSteps May := by
  intro Term step step' included claim term
  rintro ⟨next, stepped, holds⟩
  exact ⟨next, included _ _ stepped, holds⟩

theorem mayReach_growsWithSteps : GrowsWithSteps MayReach := by
  intro Term step step' included claim term
  rintro ⟨reduct, reaches, holds⟩
  exact ⟨reduct, ReflTransGen.mono included term reduct reaches, holds⟩

/-! ## Normal forms and conversion along exact embeddings -/

/-- **Normal forms are conserved**: normality is the must-observation of the
empty claim. -/
theorem isNormal_transport {Term Term' : Type} {step : Term → Term → Prop}
    {step' : Term' → Term' → Prop} (embedding : ExactEmbedding step step') (term : Term) :
    IsNormal step' (embedding.embed term) ↔ IsNormal step term := by
  have observed := must_transportInvariant embedding (fun _ => False) term
  simp only [Must, imageClaim, and_false, exists_false] at observed
  exact observed

namespace ExactEmbedding

variable {Term Term' : Type} {step : Term → Term → Prop} {step' : Term' → Term' → Prop}
  (embedding : ExactEmbedding step step')

/-- Conversions of a term are conversions of its image. -/
theorem eqvGen_embed {term other : Term} (converted : EqvGen step term other) :
    EqvGen step' (embedding.embed term) (embedding.embed other) := by
  induction converted with
  | rel _ _ stepped => exact EqvGen.rel _ _ ((embedding.exact _ _).mpr ⟨_, stepped, rfl⟩)
  | refl => exact EqvGen.refl _
  | symm _ _ _ ih => exact EqvGen.symm _ _ ih
  | trans _ _ _ _ _ first second => exact EqvGen.trans _ _ _ first second

/-- **Conversion is conserved along an exact embedding into a confluent step
relation.** -/
theorem eqvGen_iff (confluent : Confluent step') (term other : Term) :
    EqvGen step' (embedding.embed term) (embedding.embed other) ↔ EqvGen step term other := by
  refine ⟨fun converted => ?_, embedding.eqvGen_embed⟩
  obtain ⟨common, fromTerm, fromOther⟩ := confluent.eqvGen_iff_join.mp converted
  obtain ⟨reduct, reaches, rfl⟩ := (embedding.reach_iff term common).mp fromTerm
  obtain ⟨reduct', reaches', same⟩ := (embedding.reach_iff other _).mp fromOther
  rw [embedding.injective same] at reaches'
  exact EqvGen.trans _ _ _ (EqvGen.reflTransGen_le_eqvGen step _ _ reaches)
    (EqvGen.symm _ _ (EqvGen.reflTransGen_le_eqvGen step _ _ reaches'))

end ExactEmbedding

/-- The empty step relation converts only equal terms. -/
private theorem eqvGen_empty {Term : Type} {term other : Term}
    (converted : EqvGen (fun (_ _ : Term) => False) term other) : term = other := by
  induction converted with
  | rel _ _ stepped => exact stepped.elim
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ first second => exact first.trans second

/-- A fork outside the image: the extra value steps to every embedded value. -/
def forkStep (source target : Option Bool) : Prop :=
  source = none ∧ target ≠ none

/-- The truth values embed exactly into the fork: no embedded value steps. -/
def forkEmbedding : ExactEmbedding (fun (_ _ : Bool) => False) forkStep where
  embed := some
  injective := fun _ _ same => Option.some.inj same
  exact := by
    intro term next'
    simp [forkStep]

/-- **Without confluence, conversion is not conserved**: the two embedded
values become convertible through the fork. -/
theorem fork_conversion_not_conserved :
    EqvGen forkStep (forkEmbedding.embed true) (forkEmbedding.embed false) ∧
      ¬ EqvGen (fun (_ _ : Bool) => False) true false :=
  ⟨EqvGen.trans _ none _ (EqvGen.symm _ _ (EqvGen.rel _ _ ⟨rfl, Option.some_ne_none _⟩))
      (EqvGen.rel _ _ ⟨rfl, Option.some_ne_none _⟩),
    fun converted => Bool.noConfusion (eqvGen_empty converted)⟩

/-- Confluence is exactly what the fork lacks. -/
theorem fork_not_confluent : ¬ Confluent forkStep := fun confluent =>
  fork_conversion_not_conserved.2
    ((forkEmbedding.eqvGen_iff confluent true false).mp fork_conversion_not_conserved.1)

/-- One step from outside the image into it. -/
def entryStep (source target : Option Bool) : Prop :=
  source = none ∧ target = some true

/-- The truth values embed exactly beside the entry step. -/
def entryEmbedding : ExactEmbedding (fun (_ _ : Bool) => False) entryStep where
  embed := some
  injective := fun _ _ same => Option.some.inj same
  exact := by
    intro term next'
    simp [entryStep]

theorem entryStep_confluent : Confluent entryStep := by
  have reach : ∀ source target, ReflTransGen entryStep source target →
      target = source ∨ target = some true := by
    intro source target reaches
    induction reaches with
    | refl => exact Or.inl rfl
    | tail _ stepped _ => exact Or.inr stepped.2
  intro source left right toLeft toRight
  rcases reach _ _ toLeft with sameLeft | entered
  · rcases reach _ _ toRight with sameRight | entered'
    · exact ⟨source, sameLeft ▸ ReflTransGen.refl, sameRight ▸ ReflTransGen.refl⟩
    · exact ⟨right, sameLeft ▸ toRight, ReflTransGen.refl⟩
  · rcases reach _ _ toRight with sameRight | entered'
    · exact ⟨left, ReflTransGen.refl, sameRight ▸ toLeft⟩
    · exact ⟨left, ReflTransGen.refl, entered ▸ entered' ▸ ReflTransGen.refl⟩

/-- **Positive control**: beside a confluent entry into the image, the two
embedded values stay apart. -/
theorem entry_conversion_conserved :
    ¬ EqvGen entryStep (entryEmbedding.embed true) (entryEmbedding.embed false) :=
  fun converted => Bool.noConfusion
    (eqvGen_empty ((entryEmbedding.eqvGen_iff entryStep_confluent true false).mp converted))

end Mettapedia.Logic.Relation.ObservationTransport
