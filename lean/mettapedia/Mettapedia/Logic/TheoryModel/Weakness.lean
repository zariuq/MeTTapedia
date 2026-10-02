import Mettapedia.Logic.TheoryModel.Basic
import Mathlib.Data.Set.Card

/-!
# Weakest theories and largest model classes

A constraint on theories is given by the model classes it admits. A theory is a
weakest admissible theory when it is admissible and every admissible theory
entails all of it. For every constraint:

* the weakest admissible theories are exactly the theories whose model class is
  the largest admissible elementary class, and the theory of that class is one;
* for any monotone measure of model classes, a weakest admissible theory has
  maximal weakness among admissible theories, and weakness is antitone in the
  theory.

Two constraint shapes are then analysed:

* entailment constraints (the theory must entail given sentences): the largest
  admissible class always exists and the weakest theory is the consequence
  closure, a closure operator on theories;
* region constraints (every model must lie in a given region): the largest
  admissible class is the elementary interior of the region when that interior
  is elementary. The elementary interior is an interior operator on classes.
  Without disjunction in the language it need not be elementary, and then no
  weakest admissible theory exists: the control exhibits two incomparable
  admissible theories of equal cardinal weakness.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TheoryModel

open Set Order OrderDual

universe uStr uSent uW

variable {Str : Type uStr} {Sent : Type uSent} (Sat : Str → Sent → Prop)

/-! ## Weakest theories are theories of largest classes -/

/-- `K` is the largest admissible elementary class. -/
def IsLargestAdmissible (Adm : Set (Set Str)) (K : Set Str) : Prop :=
  IsExtent Sat K ∧ K ∈ Adm ∧ ∀ ⦃K'⦄, IsExtent Sat K' → K' ∈ Adm → K' ⊆ K

/-- `T` is a weakest admissible theory: its model class is admissible and every
theory with an admissible model class entails every sentence of `T`. -/
def IsWeakestAdmissible (Adm : Set (Set Str)) (T : Set Sent) : Prop :=
  models Sat T ∈ Adm ∧
    ∀ ⦃T'⦄, models Sat T' ∈ Adm → ∀ ⦃φ⦄, φ ∈ T → Entails Sat T' φ

variable {Sat}

/-- **The weakest admissible theory is the theory of the largest admissible
model class.** -/
theorem isWeakestAdmissible_theoryOf {Adm : Set (Set Str)} {K : Set Str}
    (largest : IsLargestAdmissible Sat Adm K) :
    IsWeakestAdmissible Sat Adm (theoryOf Sat K) := by
  obtain ⟨elementary, admissible, maximal⟩ := largest
  refine ⟨(isExtent_iff_hull_eq.mp elementary).symm ▸ admissible, ?_⟩
  intro T' admissible' φ member m model
  exact member (maximal ⟨T', rfl⟩ admissible' model)

/-- Conversely, the model class of a weakest admissible theory is the largest
admissible elementary class. -/
theorem isLargestAdmissible_models {Adm : Set (Set Str)} {T : Set Sent}
    (weakest : IsWeakestAdmissible Sat Adm T) :
    IsLargestAdmissible Sat Adm (models Sat T) := by
  obtain ⟨admissible, entailed⟩ := weakest
  refine ⟨⟨T, rfl⟩, admissible, ?_⟩
  rintro K' ⟨T', rfl⟩ admissible' m model φ member
  exact entailed admissible' member model

/-- **A theory is a weakest admissible theory exactly when its model class is
the largest admissible elementary class.** -/
theorem isWeakestAdmissible_iff {Adm : Set (Set Str)} {T : Set Sent} :
    IsWeakestAdmissible Sat Adm T ↔ IsLargestAdmissible Sat Adm (models Sat T) :=
  ⟨isLargestAdmissible_models, fun largest =>
    ⟨largest.2.1, fun T' admissible' _ member _ model =>
      largest.2.2 ⟨T', rfl⟩ admissible' model member⟩⟩

/-- Weakest admissible theories are unique up to their model class. -/
theorem IsWeakestAdmissible.models_eq {Adm : Set (Set Str)} {T T' : Set Sent}
    (weakest : IsWeakestAdmissible Sat Adm T) (weakest' : IsWeakestAdmissible Sat Adm T') :
    models Sat T = models Sat T' :=
  Subset.antisymm
    ((isLargestAdmissible_models weakest').2.2 ⟨T, rfl⟩ weakest.1)
    ((isLargestAdmissible_models weakest).2.2 ⟨T', rfl⟩ weakest'.1)

/-! ## Weakness measures -/

section Measure

variable {W : Type uW} [Preorder W]

/-- A measure of model classes is monotone when larger classes measure at least
as much. -/
def MonotoneMeasure (μ : Set Str → W) : Prop :=
  ∀ ⦃K K'⦄, K ⊆ K' → μ K ≤ μ K'

variable (Sat)

/-- The weakness of a theory under a measure of model classes. -/
def weaknessOf (μ : Set Str → W) (T : Set Sent) : W :=
  μ (models Sat T)

variable {Sat}

/-- **Weakness is antitone in the theory**: more axioms, less weakness. -/
theorem weaknessOf_anti {μ : Set Str → W} (monotone : MonotoneMeasure μ) {T T' : Set Sent}
    (included : T ⊆ T') : weaknessOf Sat μ T' ≤ weaknessOf Sat μ T :=
  monotone (models_anti included)

/-- Weakness is antitone along entailment: if `T'` entails every sentence of
`T`, then `T'` is at most as weak as `T`. -/
theorem weaknessOf_anti_of_entails {μ : Set Str → W} (monotone : MonotoneMeasure μ)
    {T T' : Set Sent} (entails : ∀ ⦃φ⦄, φ ∈ T → Entails Sat T' φ) :
    weaknessOf Sat μ T' ≤ weaknessOf Sat μ T :=
  monotone fun _ model _ member => entails member model

/-- A weakest admissible theory has maximal weakness among admissible
theories, for every monotone measure. -/
theorem IsWeakestAdmissible.weaknessOf_le {Adm : Set (Set Str)} {T : Set Sent}
    (weakest : IsWeakestAdmissible Sat Adm T) {μ : Set Str → W}
    (monotone : MonotoneMeasure μ) {T' : Set Sent} (admissible : models Sat T' ∈ Adm) :
    weaknessOf Sat μ T' ≤ weaknessOf Sat μ T :=
  weaknessOf_anti_of_entails monotone (weakest.2 admissible)

end Measure

/-! ## Entailment constraints: the consequence closure -/

variable (Sat)

/-- The model classes of theories entailing every sentence of `Φ`. -/
def entailing (Φ : Set Sent) : Set (Set Str) :=
  {K | K ⊆ models Sat Φ}

theorem isLargestAdmissible_entailing (Φ : Set Sent) :
    IsLargestAdmissible Sat (entailing Sat Φ) (models Sat Φ) :=
  ⟨⟨Φ, rfl⟩, Subset.rfl, fun _ _ admissible => admissible⟩

/-- **Under entailment constraints the weakest theory is the consequence
closure.** -/
theorem isWeakestAdmissible_entailing (Φ : Set Sent) :
    IsWeakestAdmissible Sat (entailing Sat Φ) (theoryOf Sat (models Sat Φ)) :=
  isWeakestAdmissible_theoryOf (isLargestAdmissible_entailing Sat Φ)

/-- A theory meets the entailment constraint exactly when it entails every
constraint sentence. -/
theorem models_mem_entailing_iff {Φ T : Set Sent} :
    models Sat T ∈ entailing Sat Φ ↔ ∀ ⦃φ⦄, φ ∈ Φ → Entails Sat T φ :=
  ⟨fun included _ member _ model => included model member,
    fun entails _ model _ member => entails member model⟩

/-! ## Region constraints: the elementary interior -/

/-- The model classes contained in a region of structures. -/
def within (A : Set Str) : Set (Set Str) :=
  {K | K ⊆ A}

/-- The elementary interior of a region: the union of the elementary classes
it contains. -/
def elementaryInterior (A : Set Str) : Set Str :=
  {m | ∃ K, IsExtent Sat K ∧ K ⊆ A ∧ m ∈ K}

variable {Sat}

theorem elementaryInterior_subset (A : Set Str) : elementaryInterior Sat A ⊆ A :=
  fun _ ⟨_, _, included, member⟩ => included member

theorem elementaryInterior_mono {A B : Set Str} (included : A ⊆ B) :
    elementaryInterior Sat A ⊆ elementaryInterior Sat B :=
  fun _ ⟨K, elementary, inside, member⟩ =>
    ⟨K, elementary, Subset.trans inside included, member⟩

theorem subset_elementaryInterior {A K : Set Str} (elementary : IsExtent Sat K)
    (inside : K ⊆ A) : K ⊆ elementaryInterior Sat A :=
  fun _ member => ⟨K, elementary, inside, member⟩

theorem elementaryInterior_idem (A : Set Str) :
    elementaryInterior Sat (elementaryInterior Sat A) = elementaryInterior Sat A :=
  Subset.antisymm (elementaryInterior_subset _)
    fun _ ⟨K, elementary, inside, member⟩ =>
      ⟨K, elementary, subset_elementaryInterior elementary inside, member⟩

/-- The theory of the elementary interior consists of the sentences entailed by
every theory whose models lie in the region: it is the candidate weakest
theory for every region. -/
theorem mem_theoryOf_elementaryInterior {A : Set Str} {φ : Sent} :
    φ ∈ theoryOf Sat (elementaryInterior Sat A) ↔
      ∀ ⦃T⦄, models Sat T ⊆ A → Entails Sat T φ := by
  constructor
  · intro member T inside m model
    exact member ⟨models Sat T, ⟨T, rfl⟩, inside, model⟩
  · rintro entailed m ⟨K, ⟨T, rfl⟩, inside, model⟩
    exact entailed inside model

/-- A largest admissible class for a region exists exactly when the elementary
interior of the region is elementary, and it is then that interior. -/
theorem isLargestAdmissible_within_iff {A K : Set Str} :
    IsLargestAdmissible Sat (within A) K ↔
      IsExtent Sat (elementaryInterior Sat A) ∧ K = elementaryInterior Sat A := by
  constructor
  · rintro ⟨elementary, inside, maximal⟩
    have equal : K = elementaryInterior Sat A :=
      Subset.antisymm (subset_elementaryInterior elementary inside)
        fun _ ⟨K', elementary', inside', member⟩ => maximal elementary' inside' member
    exact ⟨equal ▸ elementary, equal⟩
  · rintro ⟨elementary, rfl⟩
    exact ⟨elementary, elementaryInterior_subset A,
      fun _ elementary' inside' => subset_elementaryInterior elementary' inside'⟩

/-- **Under a region constraint, the weakest theory is the theory of the
elementary interior**, whenever that interior is elementary. -/
theorem isWeakestAdmissible_within {A : Set Str}
    (elementary : IsExtent Sat (elementaryInterior Sat A)) :
    IsWeakestAdmissible Sat (within A) (theoryOf Sat (elementaryInterior Sat A)) :=
  isWeakestAdmissible_theoryOf (isLargestAdmissible_within_iff.mpr ⟨elementary, rfl⟩)

/-- A weakest admissible theory for a region exists exactly when the elementary
interior of the region is elementary. -/
theorem exists_isWeakestAdmissible_within_iff {A : Set Str} :
    (∃ T, IsWeakestAdmissible Sat (within A) T) ↔ IsExtent Sat (elementaryInterior Sat A) :=
  ⟨fun ⟨_, weakest⟩ =>
      (isLargestAdmissible_within_iff.mp (isLargestAdmissible_models weakest)).1,
    fun elementary => ⟨_, isWeakestAdmissible_within elementary⟩⟩

/-- When elementary classes are closed under arbitrary unions, for instance when
the language has arbitrary disjunctions, every region has a weakest admissible
theory. -/
theorem isExtent_elementaryInterior_of_sUnion
    (sUnion : ∀ 𝒦 : Set (Set Str),
      (∀ K ∈ 𝒦, IsExtent Sat K) → IsExtent Sat (⋃₀ 𝒦))
    (A : Set Str) : IsExtent Sat (elementaryInterior Sat A) := by
  have equal : elementaryInterior Sat A = ⋃₀ {K | IsExtent Sat K ∧ K ⊆ A} := by
    ext m
    constructor
    · rintro ⟨K, elementary, inside, member⟩
      exact ⟨K, ⟨elementary, inside⟩, member⟩
    · rintro ⟨K, ⟨elementary, inside⟩, member⟩
      exact ⟨K, elementary, inside, member⟩
  rw [equal]
  exact sUnion _ fun _ member => member.1

/-! ## Order-theoretic packaging -/

section Packaging

variable (Sat)

/-- The weakest theory meeting entailment constraints, as Mathlib's closure
operator on theories. -/
theorem weakestEntailing_closure (Φ : Set Sent) :
    consequences Sat Φ = theoryOf Sat (models Sat Φ) :=
  consequences_apply Sat Φ

/-- The elementary interior is an interior operator on classes of structures,
that is, a closure operator on the order dual. -/
def elementaryInteriorOperator : ClosureOperator (Set Str)ᵒᵈ :=
  ClosureOperator.mk' (fun A => toDual (elementaryInterior Sat (ofDual A)))
    (fun _ _ included => elementaryInterior_mono included)
    (fun A => elementaryInterior_subset (ofDual A))
    (fun A => (elementaryInterior_idem (Sat := Sat) (ofDual A)).symm.subset)

end Packaging

/-! ## Controls -/

namespace Control

/-- Three structures. -/
inductive Point
  | a
  | b
  | c
  deriving DecidableEq

open Point

/-- Two atomic sentences: `false` says "the structure is `a`", `true` says
"the structure is `b`". The structure `c` satisfies neither. -/
def atomSat : Point → Bool → Prop
  | a, false => True
  | b, true => True
  | _, _ => False

/-- The same two sentences and their disjunction `none`. -/
def disjSat : Point → Option Bool → Prop
  | m, some s => atomSat m s
  | m, none => m = a ∨ m = b

/-- The region `{a, b}`. -/
def region : Set Point := {m | m = a ∨ m = b}

theorem models_atom_false : models atomSat {false} = {a} := by
  ext m
  constructor
  · intro model
    cases m with
    | a => rfl
    | b => exact (model rfl).elim
    | c => exact (model rfl).elim
  · rintro rfl φ rfl
    trivial

theorem models_atom_true : models atomSat {true} = {b} := by
  ext m
  constructor
  · intro model
    cases m with
    | a => exact (model rfl).elim
    | b => rfl
    | c => exact (model rfl).elim
  · rintro rfl φ rfl
    trivial

/-- The region contains no elementary class containing both `a` and `b`, but
its elementary interior is the whole region. -/
theorem elementaryInterior_region : elementaryInterior atomSat region = region := by
  apply Subset.antisymm (elementaryInterior_subset region)
  rintro m (rfl | rfl)
  · refine ⟨{a}, ⟨{false}, models_atom_false⟩, ?_, rfl⟩
    rintro _ rfl
    exact Or.inl rfl
  · refine ⟨{b}, ⟨{true}, models_atom_true⟩, ?_, rfl⟩
    rintro _ rfl
    exact Or.inr rfl

/-- The theory of the region is empty: no sentence holds at both `a` and `b`. -/
theorem theoryOf_region : theoryOf atomSat region = ∅ := by
  ext φ
  constructor
  · intro member
    cases φ with
    | false => exact member (Or.inr rfl : b = a ∨ b = b)
    | true => exact member (Or.inl rfl : a = a ∨ a = b)
  · intro member
    exact member.elim

/-- Negative control: without disjunction the region is not elementary; its
elementary hull adds `c`. -/
theorem region_not_isExtent : ¬ IsExtent atomSat region := by
  intro elementary
  have hull := isExtent_iff_hull_eq.mp elementary
  rw [theoryOf_region, models_empty] at hull
  have member : c ∈ region := hull ▸ mem_univ c
  rcases member with equal | equal <;> exact Point.noConfusion equal

/-- **No weakest admissible theory exists for the region** in the language
without disjunction. -/
theorem no_weakest_within_region :
    ¬ ∃ T, IsWeakestAdmissible atomSat (within region) T := by
  rw [exists_isWeakestAdmissible_within_iff, elementaryInterior_region]
  exact region_not_isExtent

/-- The two atomic theories are both admissible for the region. -/
theorem atoms_admissible :
    models atomSat {false} ∈ within region ∧ models atomSat {true} ∈ within region := by
  rw [models_atom_false, models_atom_true]
  exact ⟨fun _ equal => Or.inl equal, fun _ equal => Or.inr equal⟩

/-- Neither admissible atomic theory entails the other: they are incomparable. -/
theorem atoms_incomparable :
    ¬ Entails atomSat {false} true ∧ ¬ Entails atomSat {true} false := by
  constructor
  · intro entails
    exact entails (show a ∈ models atomSat {false} from models_atom_false ▸ rfl)
  · intro entails
    exact entails (show b ∈ models atomSat {true} from models_atom_true ▸ rfl)

/-- The two incomparable admissible theories have equinumerous model classes. -/
def atomsModelsEquiv : models atomSat {false} ≃ models atomSat {true} :=
  (Equiv.setCongr models_atom_false).trans <|
    (Equiv.Set.singleton.{0} a).trans <|
      (Equiv.Set.singleton.{0} b).symm.trans (Equiv.setCongr models_atom_true).symm

/-- The two incomparable admissible theories have equal cardinal weakness:
maximal weakness does not single out a weakest theory. -/
theorem atoms_equal_cardinal_weakness :
    weaknessOf atomSat Set.encard {false} = weaknessOf atomSat Set.encard {true} := by
  unfold weaknessOf
  rw [models_atom_false, models_atom_true, encard_singleton, encard_singleton]

/-- Positive control: with the disjunction in the language, the region is
elementary. -/
theorem region_isExtent_disj : IsExtent disjSat region := by
  refine ⟨{none}, ?_⟩
  ext m
  constructor
  · intro model
    exact model rfl
  · rintro member φ rfl
    exact member

/-- With the disjunction, the elementary interior of the region is the region. -/
theorem elementaryInterior_region_disj : elementaryInterior disjSat region = region :=
  Subset.antisymm (elementaryInterior_subset region)
    (subset_elementaryInterior region_isExtent_disj Subset.rfl)

/-- **With disjunction, the weakest admissible theory exists**: the theory of
the region. -/
theorem weakest_within_region_disj :
    IsWeakestAdmissible disjSat (within region) (theoryOf disjSat region) := by
  have elementary : IsExtent disjSat (elementaryInterior disjSat region) := by
    rw [elementaryInterior_region_disj]
    exact region_isExtent_disj
  have weakest := isWeakestAdmissible_within elementary
  rwa [elementaryInterior_region_disj] at weakest

/-- The weakest theory for the region contains the disjunction. -/
theorem none_mem_weakest_disj : none ∈ theoryOf disjSat region :=
  fun _ member => member

/-- Entailment constraint control: the weakest theory entailing `some false`
has exactly the model `a`. -/
theorem weakest_entailing_atom :
    models disjSat (theoryOf disjSat (models disjSat {some false})) = {a} := by
  rw [models_theoryOf_models]
  ext m
  constructor
  · intro model
    cases m with
    | a => rfl
    | b => exact (model rfl).elim
    | c => exact (model rfl).elim
  · rintro rfl φ rfl
    trivial

end Control

end Mettapedia.Logic.TheoryModel
