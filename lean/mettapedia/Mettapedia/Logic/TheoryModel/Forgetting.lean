import Mettapedia.Logic.TheoryModel.Universe
import Mathlib.Data.Setoid.Basic

/-!
# Forgetting as weakening

An equivalence relation can act on two different sides of a satisfaction
relation, with opposite effects on the strength of the resulting theory.

**Observers.** An equivalence `E` on structures is an observer that cannot tell
`E`-related structures apart. Forgetting is coarsening `E`. The observer can
evaluate only the `E`-invariant sentences, `observable Sat E`, and sees the
theory `observedTheory Sat E K` of a class `K`. Coarsening the observer shrinks
the observable language and the observed theory and enlarges its model class:
forgetting is weakening. The observed theory cannot exclude any structure
indistinguishable from a member of `K`.

`observable` and `indistinguishable` form an order-reversing Galois connection
between observers and languages. It is not a Galois insertion as soon as some
sentence is valid: the valid sentences are observable by every observer, so the
empty language is not the observable language of any observer. It is a Galois
coinsertion exactly when every observer is recovered from its observable
language; the full predicate language has this property, and a language with a
single valid sentence does not.

**Identifications.** An equivalence `E` on the objects themselves (terms,
proofs) read as a set of equations is a theory about interpretations of those
objects. Its models are the interpretations that factor through the quotient,
so a coarser `E` has fewer models: imposing an identification, such as
identifying all proofs of an identity, strengthens the theory. With all
interpretations into the same universe available, the consequences of a set of
equations are exactly its equivalence closure, witnessed by the quotient map;
the closed equational theories are exactly the equivalence relations, and
Mathlib's `Setoid.gi` is the corresponding Galois insertion. A universe of
subsingletons validates every identification, so it hosts an equational theory
faithfully only when the equivalence closure of the theory relates all
objects.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TheoryModel

open Set Order OrderDual

universe uStr uSent uX

variable {Str : Type uStr} {Sent : Type uSent} (Sat : Str → Sent → Prop)

/-! ## Observers -/

/-- The sentences an observer can evaluate: those whose truth is invariant
under its indistinguishability `E`. -/
def observable (E : Setoid Str) : Set Sent :=
  {φ | ∀ ⦃m m'⦄, E m m' → (Sat m φ ↔ Sat m' φ)}

/-- Structures that no sentence of `Φ` separates. -/
def indistinguishable (Φ : Set Sent) : Setoid Str where
  r m m' := ∀ ⦃φ⦄, φ ∈ Φ → (Sat m φ ↔ Sat m' φ)
  iseqv := ⟨fun _ _ _ => Iff.rfl, fun related _ member => (related member).symm,
    fun related related' _ member => (related member).trans (related' member)⟩

/-- The theory of `K` visible to the observer `E`. -/
def observedTheory (E : Setoid Str) (K : Set Str) : Set Sent :=
  theoryOf Sat K ∩ observable Sat E

/-- The structures an observer cannot separate from some member of `K`. -/
def saturation (E : Setoid Str) (K : Set Str) : Set Str :=
  {m | ∃ m' ∈ K, E m' m}

/-- The observer `E` is recovered from its observable language. -/
def Separates (E : Setoid Str) : Prop :=
  indistinguishable Sat (observable Sat E) ≤ E

variable {Sat}

/-- **The adjunction between observers and languages**, elementwise. -/
theorem subset_observable_iff {Φ : Set Sent} {E : Setoid Str} :
    Φ ⊆ observable Sat E ↔ E ≤ indistinguishable Sat Φ := by
  constructor
  · intro included m m' related φ member
    exact included member related
  · intro finer φ member m m' related
    exact finer related member

/-- **Forgetting shrinks the observable language.** -/
theorem observable_anti {E E' : Setoid Str} (coarser : E ≤ E') :
    observable Sat E' ⊆ observable Sat E :=
  fun _ invariant _ _ related => invariant (coarser related)

/-- A larger language separates more structures. -/
theorem indistinguishable_anti {Φ Φ' : Set Sent} (included : Φ ⊆ Φ') :
    indistinguishable Sat Φ' ≤ indistinguishable Sat Φ :=
  fun _ _ related _ member => related (included member)

/-- **Forgetting weakens the observed theory.** -/
theorem observedTheory_anti {E E' : Setoid Str} (coarser : E ≤ E') (K : Set Str) :
    observedTheory Sat E' K ⊆ observedTheory Sat E K :=
  fun _ member => ⟨member.1, observable_anti coarser member.2⟩

/-- **Forgetting enlarges the model class** of the observed theory. -/
theorem models_observedTheory_mono {E E' : Setoid Str} (coarser : E ≤ E') (K : Set Str) :
    models Sat (observedTheory Sat E K) ⊆ models Sat (observedTheory Sat E' K) :=
  models_anti (observedTheory_anti coarser K)

theorem subset_saturation (E : Setoid Str) (K : Set Str) : K ⊆ saturation E K :=
  fun m member => ⟨m, member, E.refl' m⟩

theorem saturation_mono {E E' : Setoid Str} (coarser : E ≤ E') (K : Set Str) :
    saturation E K ⊆ saturation E' K :=
  fun _ ⟨m', member, related⟩ => ⟨m', member, coarser related⟩

/-- The observed theory cannot exclude a structure indistinguishable from a
member of `K`. -/
theorem saturation_subset_models_observedTheory (E : Setoid Str) (K : Set Str) :
    saturation E K ⊆ models Sat (observedTheory Sat E K) := by
  rintro m ⟨m', member, related⟩ φ ⟨holds, invariant⟩
  exact (invariant related).mp (holds member)

/-- Passing to the saturation leaves the observed theory unchanged. -/
theorem observedTheory_saturation (E : Setoid Str) (K : Set Str) :
    observedTheory Sat E (saturation E K) = observedTheory Sat E K := by
  apply Subset.antisymm
  · exact fun φ member => ⟨theoryOf_anti (subset_saturation E K) member.1, member.2⟩
  · rintro φ ⟨holds, invariant⟩
    refine ⟨?_, invariant⟩
    rintro m ⟨m', member, related⟩
    exact (invariant related).mp (holds member)

/-- Forgetting through saturation weakens the full theory as well. -/
theorem theoryOf_saturation_anti {E E' : Setoid Str} (coarser : E ≤ E') (K : Set Str) :
    theoryOf Sat (saturation E' K) ⊆ theoryOf Sat (saturation E K) :=
  theoryOf_anti (saturation_mono coarser K)

/-! ## Galois insertion or coinsertion -/

/-- A valid sentence is observable by every observer. -/
theorem valid_mem_observable {φ : Sent} (valid : ∀ m, Sat m φ) (E : Setoid Str) :
    φ ∈ observable Sat E :=
  fun m m' _ => ⟨fun _ => valid m', fun _ => valid m⟩

/-- Every observer is at most as fine as the indistinguishability of its
observable language. -/
theorem le_indistinguishable_observable (E : Setoid Str) :
    E ≤ indistinguishable Sat (observable Sat E) :=
  subset_observable_iff.mp Subset.rfl

section Packaging

variable (Sat)

/-- **The order-reversing Galois connection between observers and languages**:
forgetting, `E ↦ observable Sat E`, is the lower adjoint into languages ordered
by reverse inclusion. -/
theorem observable_galoisConnection :
    GaloisConnection (toDual ∘ observable Sat) (indistinguishable Sat ∘ ofDual) :=
  fun _ _ => subset_observable_iff

/-- Forgetting as a monotone map from observers ordered by coarseness to
languages ordered by weakness. -/
def forgetting : Setoid Str →o (Set Sent)ᵒᵈ where
  toFun E := toDual (observable Sat E)
  monotone' _ _ coarser := observable_anti coarser

/-- **Forgetting is not a Galois insertion** when some sentence is valid. -/
theorem not_galoisInsertion {φ : Sent} (valid : ∀ m, Sat m φ) :
    IsEmpty (GaloisInsertion (toDual ∘ observable Sat) (indistinguishable Sat ∘ ofDual)) := by
  refine ⟨fun insertion => ?_⟩
  have equal := insertion.l_u_eq (toDual (∅ : Set Sent))
  have member : φ ∈ observable Sat (indistinguishable Sat (∅ : Set Sent)) :=
    valid_mem_observable valid _
  have empty : observable Sat (indistinguishable Sat (∅ : Set Sent)) = ∅ :=
    congrArg ofDual equal
  rw [empty] at member
  exact member

/-- **Forgetting is a Galois coinsertion when every observer is recovered from
its observable language.** -/
def coinsertionOfSeparates (separates : ∀ E : Setoid Str, Separates Sat E) :
    GaloisCoinsertion (toDual ∘ observable Sat) (indistinguishable Sat ∘ ofDual) :=
  (observable_galoisConnection Sat).toGaloisCoinsertion separates

/-- Conversely, a coinsertion recovers every observer. -/
theorem separates_of_coinsertion
    (coinsertion : GaloisCoinsertion (toDual ∘ observable Sat) (indistinguishable Sat ∘ ofDual))
    (E : Setoid Str) : Separates Sat E :=
  coinsertion.u_l_le E

end Packaging

/-! ## The full predicate language separates every observer -/

/-- The full predicate language: every class of structures is a sentence. -/
def predicateSat (m : Str) (S : Set Str) : Prop :=
  m ∈ S

/-- Every equivalence class is an observable predicate. -/
theorem predicate_separates (E : Setoid Str) : Separates predicateSat E := by
  intro m m' related
  have invariant : {x | E m x} ∈ observable predicateSat E :=
    fun x y relatedXY => ⟨fun relatedMX => E.trans' relatedMX relatedXY,
      fun relatedMY => E.trans' relatedMY (E.symm' relatedXY)⟩
  exact (related invariant).mp (E.refl' m)

/-- For the full predicate language, forgetting is a Galois coinsertion. -/
def predicateCoinsertion :
    GaloisCoinsertion (toDual ∘ observable (predicateSat (Str := Str)))
      (indistinguishable predicateSat ∘ ofDual) :=
  coinsertionOfSeparates _ predicate_separates

/-! ## Identifications as axioms -/

section Identification

variable {X : Type uX}

/-- An interpretation of the objects `X` into some type of the same universe
satisfies an equation when it identifies its two sides. -/
def equates (f : Σ Y : Type uX, X → Y) (p : X × X) : Prop :=
  f.2 p.1 = f.2 p.2

/-- The equations imposed by an identification `E` of objects. -/
def equationsOf (E : Setoid X) : Set (X × X) :=
  {p | E p.1 p.2}

/-- An interpretation satisfies the identification `E` exactly when it factors
through the quotient by `E`. -/
theorem mem_models_equationsOf {E : Setoid X} {f : Σ Y : Type uX, X → Y} :
    f ∈ models equates (equationsOf E) ↔ E ≤ Setoid.ker f.2 :=
  ⟨fun model x y related =>
      (model (show (x, y) ∈ equationsOf E from related) : f.2 x = f.2 y),
    fun factors p related => (factors related : f.2 p.1 = f.2 p.2)⟩

/-- **Imposing a coarser identification strengthens the theory**: fewer
interpretations satisfy it. -/
theorem models_equationsOf_anti {E E' : Setoid X} (coarser : E ≤ E') :
    models equates (equationsOf E') ⊆ models equates (equationsOf E) :=
  models_anti fun _ related => coarser related

/-- The relation underlying a set of equations. -/
def relationOf (R : Set (X × X)) (x y : X) : Prop :=
  (x, y) ∈ R

/-- The quotient map by the equivalence closure satisfies the equations. -/
def quotientInterpretation (R : Set (X × X)) : Σ Y : Type uX, X → Y :=
  ⟨Quot (relationOf R), Quot.mk _⟩

theorem quotientInterpretation_mem_models (R : Set (X × X)) :
    quotientInterpretation R ∈ models equates R :=
  fun p member => Quot.sound (show relationOf R p.1 p.2 from member)

/-- **The consequences of a set of equations are its equivalence closure**,
computed over all interpretations into the objects' universe. -/
theorem consequences_equations (R : Set (X × X)) :
    theoryOf equates (models equates R) =
      {p | Relation.EqvGen (relationOf R) p.1 p.2} := by
  ext p
  constructor
  · intro consequence
    exact Quot.eqvGen_exact (consequence (quotientInterpretation_mem_models R))
  · intro generated f model
    obtain ⟨x, y⟩ := p
    change Relation.EqvGen (relationOf R) x y at generated
    change f.2 x = f.2 y
    induction generated with
    | rel a b related => exact model (show (a, b) ∈ R from related)
    | refl => rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih ih' => exact ih.trans ih'

/-- Closed equational theories are exactly the identifications. -/
theorem consequences_equationsOf (E : Setoid X) :
    theoryOf equates (models equates (equationsOf E)) = equationsOf E := by
  rw [consequences_equations]
  ext p
  constructor
  · intro generated
    obtain ⟨x, y⟩ := p
    change Relation.EqvGen (relationOf (equationsOf E)) x y at generated
    change E x y
    induction generated with
    | rel a b related => exact related
    | refl a => exact E.refl' a
    | symm a b _ ih => exact E.symm' ih
    | trans a b c _ _ ih ih' => exact E.trans' ih ih'
  · exact fun related => Relation.EqvGen.rel _ _ related

/-- **The closed equational theories are exactly the identifications.** -/
theorem isIntent_equates_iff {R : Set (X × X)} :
    IsIntent (equates (X := X)) R ↔ ∃ E : Setoid X, R = equationsOf E := by
  constructor
  · intro closed
    have closure := isIntent_iff_consequences_eq.mp closed
    rw [consequences_equations] at closure
    exact ⟨Relation.EqvGen.setoid (relationOf R), closure.symm⟩
  · rintro ⟨E, rfl⟩
    exact isIntent_iff_consequences_eq.mpr (consequences_equationsOf E)

/-- The identification map from equivalences to their equations is the upper
adjoint of Mathlib's Galois insertion `Setoid.gi`, with the equivalence closure
as lower adjoint. -/
def identificationInsertion : GaloisInsertion Relation.EqvGen.setoid (@Setoid.r X) :=
  Setoid.gi

/-- The equivalence closure of no equations is equality. -/
theorem eq_of_eqvGen_empty {x y : X}
    (generated : Relation.EqvGen (relationOf (∅ : Set (X × X))) x y) : x = y := by
  induction generated with
  | rel _ _ related => exact related.elim
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

/-- The universe of interpretations into subsingletons. -/
def subsingletonUniverse : Set (Σ Y : Type uX, X → Y) :=
  {f | Subsingleton f.1}

/-- A universe of subsingletons validates every equation. -/
theorem consequencesIn_subsingletonUniverse (R : Set (X × X)) :
    consequencesIn equates (subsingletonUniverse (X := X)) R = univ :=
  eq_univ_of_forall fun _ _ hosted => @Subsingleton.elim _ hosted.1 _ _

/-- **A universe of subsingletons does not host an equational theory
faithfully** as soon as two objects are not related by its equivalence
closure. -/
theorem not_hostsFaithfully_subsingletonUniverse {R : Set (X × X)} {x y : X}
    (unrelated : ¬ Relation.EqvGen (relationOf R) x y) :
    ¬ HostsFaithfully equates (subsingletonUniverse (X := X)) R := by
  apply not_hostsFaithfully_of (φ := (x, y))
  · rw [consequencesIn_subsingletonUniverse]
    exact mem_univ _
  · intro entailed
    have generated : (x, y) ∈ theoryOf equates (models equates R) := entailed
    rw [consequences_equations] at generated
    exact unrelated generated

/-- In particular the empty theory, on objects with two distinct elements. -/
theorem not_hostsFaithfully_subsingletonUniverse_empty {x y : X} (distinct : x ≠ y) :
    ¬ HostsFaithfully equates (subsingletonUniverse (X := X)) ∅ :=
  not_hostsFaithfully_subsingletonUniverse fun generated =>
    distinct (eq_of_eqvGen_empty generated)

/-- The identity interpretation hosts every equational theory faithfully
together with the quotient interpretations: the full universe does. -/
theorem hostsFaithfully_univ_equations (R : Set (X × X)) :
    HostsFaithfully equates (univ : Set (Σ Y : Type uX, X → Y)) R :=
  hostsFaithfully_univ R

end Identification

/-! ## Controls -/

namespace Control

/-- Two proofs of one proposition, as the structures `true` and `false`. -/
abbrev Proof := Bool

/-- The proof-relevant observer distinguishes the two proofs. -/
def relevant : Setoid Proof := ⊥

/-- The proof-irrelevant observer identifies them. -/
def irrelevant : Setoid Proof := ⊤

theorem relevant_le_irrelevant : relevant ≤ irrelevant := fun _ _ _ => trivial

/-- The predicate "the proof is `true`". -/
def isTrueProof : Set Proof := {m | m = true}

/-- Positive control: the proof-relevant observer evaluates `isTrueProof`. -/
theorem isTrueProof_observable_relevant :
    isTrueProof ∈ observable (predicateSat (Str := Proof)) relevant := by
  intro m m' related
  have equal : m = m' := related
  rw [equal]

/-- Negative control: the proof-irrelevant observer cannot evaluate it. -/
theorem isTrueProof_not_observable_irrelevant :
    isTrueProof ∉ observable (predicateSat (Str := Proof)) irrelevant := by
  intro invariant
  have transfer := (invariant (show irrelevant true false from trivial)).mp rfl
  exact Bool.noConfusion transfer

/-- The relevant observer sees that the proof is `true`; the irrelevant one
does not. -/
theorem forgetting_weakens :
    isTrueProof ∈ observedTheory predicateSat relevant {true} ∧
      isTrueProof ∉ observedTheory predicateSat irrelevant {true} :=
  ⟨⟨fun _ member => member, isTrueProof_observable_relevant⟩,
    fun member => isTrueProof_not_observable_irrelevant member.2⟩

/-- **Forgetting the proof admits the other proof as a model.** -/
theorem forgetting_admits_false :
    false ∉ models predicateSat (observedTheory predicateSat relevant {true}) ∧
      false ∈ models predicateSat (observedTheory predicateSat irrelevant {true}) := by
  constructor
  · intro model
    exact Bool.noConfusion (model forgetting_weakens.1 : false ∈ isTrueProof)
  · exact saturation_subset_models_observedTheory irrelevant {true} ⟨true, rfl, trivial⟩

/-- A language with a single valid sentence. -/
def poorSat : Proof → PUnit.{1} → Prop :=
  fun _ _ => True

/-- Negative control: the poor language does not separate the proof-relevant
observer, so forgetting is not a coinsertion for it. -/
theorem poor_not_separates : ¬ Separates poorSat relevant := by
  intro separates
  have related : indistinguishable poorSat (observable poorSat relevant) true false :=
    fun _ _ => ⟨fun _ => trivial, fun _ => trivial⟩
  exact Bool.noConfusion (separates related)

theorem poor_not_coinsertion :
    IsEmpty (GaloisCoinsertion (toDual ∘ observable poorSat)
      (indistinguishable poorSat ∘ ofDual)) :=
  ⟨fun coinsertion =>
    poor_not_separates (separates_of_coinsertion poorSat coinsertion relevant)⟩

/-- Negative control for insertions: forgetting over the full predicate language
is not a Galois insertion, because `univ` is valid. -/
theorem predicate_not_insertion :
    IsEmpty (GaloisInsertion (toDual ∘ observable (predicateSat (Str := Proof)))
      (indistinguishable predicateSat ∘ ofDual)) :=
  not_galoisInsertion predicateSat (φ := univ) fun _ => mem_univ _

/-- Identification control: identifying the two proofs strengthens the
equational theory; the identity interpretation of `Bool` is lost. -/
theorem identification_strengthens :
    (⟨Proof, id⟩ : Σ Y : Type, Proof → Y) ∈ models equates (equationsOf relevant) ∧
      (⟨Proof, id⟩ : Σ Y : Type, Proof → Y) ∉ models equates (equationsOf irrelevant) := by
  constructor
  · intro p related
    exact related
  · intro model
    exact Bool.noConfusion
      (model (show (true, false) ∈ equationsOf irrelevant from trivial) : true = false)

end Control

end Mettapedia.Logic.TheoryModel
