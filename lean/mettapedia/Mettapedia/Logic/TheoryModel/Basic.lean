import Mathlib.Order.Concept

/-!
# Theories and model classes: the order-reversing Galois connection

A satisfaction relation `Sat : Str → Sent → Prop` between candidate structures
and sentences determines two antitone maps:

* `models Sat T`, the structures satisfying every sentence of `T`;
* `theoryOf Sat K`, the sentences true in every structure of `K`.

They are the lower and upper polars of `Sat` from `Mathlib.Order.Concept`, so
they form an order-reversing Galois connection. Its composites are closure
operators: semantic consequence `theoryOf ∘ models` on theories and the
elementary hull `models ∘ theoryOf` on classes of structures. Closed theories
and elementary classes are anti-isomorphic, and a theory is weaker than another
exactly when its model class is larger. Adding an axiom shrinks the model
class, strictly exactly when the axiom is not already a consequence.
Satisfaction-preserving translations transport both maps, whether structures
move with the sentences or are reduced against them. A two-structure control
closes the file.

The elementwise laws are stated with `⊆` and membership. The packaging as a
`GaloisConnection`, `ClosureOperator` and `OrderIso` uses Mathlib's order on
`Set`, whose instance is the complete atomic Boolean algebra of sets; that
instance term is where `Classical.choice` enters those declarations.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TheoryModel

open Set Order OrderDual

universe uStr uSent uStr' uSent'

variable {Str : Type uStr} {Sent : Type uSent} (Sat : Str → Sent → Prop)

/-! ## Models and theories -/

/-- The models of a theory: the structures satisfying every sentence of it. -/
abbrev models (T : Set Sent) : Set Str := lowerPolar Sat T

/-- The theory of a class of structures: the sentences true in all of them. -/
abbrev theoryOf (K : Set Str) : Set Sent := upperPolar Sat K

variable {Sat}

theorem mem_models {T : Set Sent} {m : Str} :
    m ∈ models Sat T ↔ ∀ ⦃φ⦄, φ ∈ T → Sat m φ :=
  Iff.rfl

theorem mem_theoryOf {K : Set Str} {φ : Sent} :
    φ ∈ theoryOf Sat K ↔ ∀ ⦃m⦄, m ∈ K → Sat m φ :=
  Iff.rfl

/-- **The adjunction**, elementwise: every sentence of `T` holds in every
structure of `K`, read from either side. -/
theorem subset_theoryOf_iff {T : Set Sent} {K : Set Str} :
    T ⊆ theoryOf Sat K ↔ K ⊆ models Sat T :=
  subset_upperPolar_iff_subset_lowerPolar

/-- A larger theory has fewer models. -/
theorem models_anti {T T' : Set Sent} (included : T ⊆ T') :
    models Sat T' ⊆ models Sat T :=
  fun _ member _ axiomMember => member (included axiomMember)

/-- A larger class has a smaller theory. -/
theorem theoryOf_anti {K K' : Set Str} (included : K ⊆ K') :
    theoryOf Sat K' ⊆ theoryOf Sat K :=
  fun _ member _ classMember => member (included classMember)

theorem subset_theoryOf_models (T : Set Sent) : T ⊆ theoryOf Sat (models Sat T) :=
  fun _ axiomMember _ member => member axiomMember

theorem subset_models_theoryOf (K : Set Str) : K ⊆ models Sat (theoryOf Sat K) :=
  fun _ classMember _ member => member classMember

/-- Closing a theory under consequence does not change its models. -/
theorem models_theoryOf_models (T : Set Sent) :
    models Sat (theoryOf Sat (models Sat T)) = models Sat T :=
  Subset.antisymm (models_anti (subset_theoryOf_models T)) (subset_models_theoryOf _)

/-- Closing a class to its elementary hull does not change its theory. -/
theorem theoryOf_models_theoryOf (K : Set Str) :
    theoryOf Sat (models Sat (theoryOf Sat K)) = theoryOf Sat K :=
  Subset.antisymm (theoryOf_anti (subset_models_theoryOf K)) (subset_theoryOf_models _)

variable (Sat)

theorem models_union (T T' : Set Sent) :
    models Sat (T ∪ T') = models Sat T ∩ models Sat T' :=
  lowerPolar_union Sat T T'

theorem theoryOf_union (K K' : Set Str) :
    theoryOf Sat (K ∪ K') = theoryOf Sat K ∩ theoryOf Sat K' :=
  upperPolar_union Sat K K'

theorem models_empty : models Sat (∅ : Set Sent) = univ :=
  eq_univ_of_forall fun _ _ member => member.elim

theorem theoryOf_empty : theoryOf Sat (∅ : Set Str) = univ :=
  eq_univ_of_forall fun _ _ member => member.elim

/-! ## Entailment and consequence -/

/-- A theory entails a sentence when every model of the theory satisfies it. -/
def Entails (T : Set Sent) (φ : Sent) : Prop :=
  ∀ ⦃m⦄, m ∈ models Sat T → Sat m φ

variable {Sat}

theorem entails_iff_mem {T : Set Sent} {φ : Sent} :
    Entails Sat T φ ↔ φ ∈ theoryOf Sat (models Sat T) :=
  Iff.rfl

theorem entails_iff_models_subset {T : Set Sent} {φ : Sent} :
    Entails Sat T φ ↔ models Sat T ⊆ models Sat {φ} :=
  ⟨fun entails _ member _ equal => equal ▸ entails member,
    fun included _ member => included member rfl⟩

/-- **Weaker theories have larger model classes.** `T` has fewer consequences
than `T'` exactly when every model of `T'` is a model of `T`. -/
theorem consequences_subset_iff {T T' : Set Sent} :
    theoryOf Sat (models Sat T) ⊆ theoryOf Sat (models Sat T') ↔
      models Sat T' ⊆ models Sat T := by
  constructor
  · intro included m member φ axiomMember
    exact included (subset_theoryOf_models T axiomMember) member
  · intro included φ consequence m member
    exact consequence (included member)

/-! ## Adding axioms -/

theorem mem_models_insert {T : Set Sent} {φ : Sent} {m : Str} :
    m ∈ models Sat (insert φ T) ↔ Sat m φ ∧ m ∈ models Sat T :=
  ⟨fun h => ⟨h (mem_insert φ T), fun _ member => h (mem_insert_of_mem φ member)⟩,
    fun h _ member => member.elim (fun equal => equal ▸ h.1) (fun member => h.2 member)⟩

variable (Sat)

/-- **Adding an axiom shrinks the model class.** -/
theorem models_insert_subset (φ : Sent) (T : Set Sent) :
    models Sat (insert φ T) ⊆ models Sat T :=
  models_anti (subset_insert φ T)

variable {Sat}

/-- Adding an axiom leaves the model class unchanged exactly when the axiom is
already a consequence. -/
theorem models_insert_eq_iff {T : Set Sent} {φ : Sent} :
    models Sat (insert φ T) = models Sat T ↔ Entails Sat T φ := by
  constructor
  · intro equal m member
    have inserted : m ∈ models Sat (insert φ T) := by
      rw [equal]
      exact member
    exact (mem_models_insert.mp inserted).1
  · intro consequence
    apply Subset.antisymm (models_insert_subset Sat φ T)
    intro m member
    exact mem_models_insert.mpr ⟨consequence member, member⟩

/-- Adding an axiom loses a model exactly when the axiom is not a consequence. -/
theorem not_models_subset_insert_iff {T : Set Sent} {φ : Sent} :
    ¬ models Sat T ⊆ models Sat (insert φ T) ↔ ¬ Entails Sat T φ := by
  constructor
  · intro notBack consequence
    exact notBack fun m member => mem_models_insert.mpr ⟨consequence member, member⟩
  · intro notConsequence back
    exact notConsequence fun m member => (mem_models_insert.mp (back member)).1

/-! ## Closed theories and elementary classes -/

/-- Mathlib's intents of the polarity are exactly the theories equal to their
consequences. -/
theorem isIntent_iff_consequences_eq {T : Set Sent} :
    IsIntent Sat T ↔ theoryOf Sat (models Sat T) = T :=
  ⟨fun ⟨K, equal⟩ => equal ▸ theoryOf_models_theoryOf K, fun equal => ⟨_, equal⟩⟩

/-- Mathlib's extents of the polarity are exactly the classes equal to their
elementary hulls. -/
theorem isExtent_iff_hull_eq {K : Set Str} :
    IsExtent Sat K ↔ models Sat (theoryOf Sat K) = K :=
  ⟨fun ⟨T, equal⟩ => equal ▸ models_theoryOf_models T, fun equal => ⟨_, equal⟩⟩

/-- A closed theory is determined by its model class, reversing inclusion. -/
theorem subset_iff_models_subset_of_isIntent {T T' : Set Sent}
    (closed : IsIntent Sat T) (closed' : IsIntent Sat T') :
    T ⊆ T' ↔ models Sat T' ⊆ models Sat T := by
  rw [← isIntent_iff_consequences_eq.mp closed, ← isIntent_iff_consequences_eq.mp closed',
    models_theoryOf_models, models_theoryOf_models]
  exact consequences_subset_iff

/-! ## Translations preserving and reflecting satisfaction -/

section Translation

variable {Str' : Type uStr'} {Sent' : Type uSent'} {Sat' : Str' → Sent' → Prop}

/-- Along a translation of structures and sentences that preserves and reflects
satisfaction, models are the preimage of the models of the translated theory. -/
theorem models_eq_preimage (f : Str → Str') (g : Sent → Sent')
    (sat_iff : ∀ m φ, Sat m φ ↔ Sat' (f m) (g φ)) (T : Set Sent) :
    models Sat T = f ⁻¹' models Sat' (g '' T) := by
  ext m
  constructor
  · rintro member _ ⟨φ, axiomMember, rfl⟩
    exact (sat_iff m φ).mp (member axiomMember)
  · intro member φ axiomMember
    exact (sat_iff m φ).mpr (member ⟨φ, axiomMember, rfl⟩)

/-- Along the same translation, a theory is the preimage of the theory of the
translated class. -/
theorem theoryOf_eq_preimage (f : Str → Str') (g : Sent → Sent')
    (sat_iff : ∀ m φ, Sat m φ ↔ Sat' (f m) (g φ)) (K : Set Str) :
    theoryOf Sat K = g ⁻¹' theoryOf Sat' (f '' K) := by
  ext φ
  constructor
  · rintro member _ ⟨m, classMember, rfl⟩
    exact (sat_iff m φ).mp (member classMember)
  · intro member m classMember
    exact (sat_iff m φ).mpr (member ⟨m, classMember, rfl⟩)

/-- With sentences translated forward and structures reduced backward, the
models of a translated theory are the structures whose reducts are models. -/
theorem models_image_eq_preimage (reduce : Str' → Str) (translate : Sent → Sent')
    (sat_iff : ∀ m φ, Sat' m (translate φ) ↔ Sat (reduce m) φ) (T : Set Sent) :
    models Sat' (translate '' T) = reduce ⁻¹' models Sat T := by
  ext m
  constructor
  · intro member φ axiomMember
    exact (sat_iff m φ).mp (member ⟨φ, axiomMember, rfl⟩)
  · rintro member _ ⟨φ, axiomMember, rfl⟩
    exact (sat_iff m φ).mpr (member axiomMember)

/-- Dually, a sentence belongs to the theory of the reducts of a class exactly
when its translation belongs to the theory of the class. -/
theorem theoryOf_image_eq_preimage (reduce : Str' → Str) (translate : Sent → Sent')
    (sat_iff : ∀ m φ, Sat' m (translate φ) ↔ Sat (reduce m) φ) (K : Set Str') :
    theoryOf Sat (reduce '' K) = translate ⁻¹' theoryOf Sat' K := by
  ext φ
  constructor
  · intro member m classMember
    exact (sat_iff m φ).mpr (member ⟨m, classMember, rfl⟩)
  · rintro member _ ⟨m, classMember, rfl⟩
    exact (sat_iff m φ).mp (member classMember)

end Translation

/-! ## Order-theoretic packaging

These declarations restate the laws above with Mathlib's order on `Set`. -/

section Packaging

variable (Sat)

/-- **The order-reversing Galois connection between classes and theories.**
`theoryOf` is the lower adjoint into theories ordered by reverse inclusion. -/
theorem galoisConnection :
    GaloisConnection (toDual ∘ theoryOf Sat) (models Sat ∘ ofDual) :=
  gc_upperPolar_lowerPolar Sat

/-- The same connection with `models` as the lower adjoint into classes ordered
by reverse inclusion. -/
theorem galoisConnection_models :
    GaloisConnection (toDual ∘ models Sat) (theoryOf Sat ∘ ofDual) :=
  gc_lowerPolar_upperPolar Sat

theorem models_antitone : Antitone (models Sat) :=
  fun _ _ included => models_anti included

theorem theoryOf_antitone : Antitone (theoryOf Sat) :=
  fun _ _ included => theoryOf_anti included

/-- Semantic consequence: the closure operator `theoryOf ∘ models` on
theories. -/
abbrev consequences : ClosureOperator (Set Sent) :=
  intentClosure Sat

/-- The elementary hull: the closure operator `models ∘ theoryOf` on classes of
structures. -/
abbrev elementaryHull : ClosureOperator (Set Str) :=
  extentClosure Sat

theorem consequences_apply (T : Set Sent) :
    consequences Sat T = theoryOf Sat (models Sat T) :=
  rfl

theorem elementaryHull_apply (K : Set Str) :
    elementaryHull Sat K = models Sat (theoryOf Sat K) :=
  rfl

/-- Adding an axiom shrinks the model class strictly exactly when the axiom is
not a consequence. -/
theorem models_insert_ssubset_iff {T : Set Sent} {φ : Sent} :
    models Sat (insert φ T) ⊂ models Sat T ↔ ¬ Entails Sat T φ := by
  rw [ssubset_iff_subset_not_subset]
  exact ⟨fun strict => not_models_subset_insert_iff.mp strict.2,
    fun notConsequence =>
      ⟨models_insert_subset Sat φ T, not_models_subset_insert_iff.mpr notConsequence⟩⟩

/-- **Closed theories are anti-isomorphic to elementary classes.** -/
def closedTheoryEquiv :
    {T : Set Sent // IsIntent Sat T} ≃o {K : Set Str // IsExtent Sat K}ᵒᵈ where
  toFun T := toDual ⟨models Sat T.1, isExtent_lowerPolar⟩
  invFun K := ⟨theoryOf Sat (ofDual K).1, isIntent_upperPolar⟩
  left_inv T := Subtype.ext (isIntent_iff_consequences_eq.mp T.2)
  right_inv K := Subtype.ext (isExtent_iff_hull_eq.mp (ofDual K).2)
  map_rel_iff' {T T'} := by
    change models Sat T'.1 ⊆ models Sat T.1 ↔ T.1 ⊆ T'.1
    exact (subset_iff_models_subset_of_isIntent T.2 T'.2).symm

end Packaging

/-! ## Control: two structures, three sentences -/

namespace Control

/-- Structures `true` and `false`; the sentence `none` holds everywhere and
`some b` holds exactly in the structure `b`. -/
def sat : Bool → Option Bool → Prop
  | _, none => True
  | m, some b => m = b

theorem models_some_true : models sat {some true} = {true} := by
  ext m
  constructor
  · intro member
    exact member rfl
  · rintro rfl φ rfl
    rfl

/-- Positive control: the valid sentence is a consequence of every theory. -/
theorem entails_none : Entails sat {some true} none :=
  fun _ _ => trivial

/-- Negative control: `some false` is not a consequence of `{some true}`. -/
theorem not_entails_some_false : ¬ Entails sat {some true} (some false) := by
  intro consequence
  have member : true ∈ models sat {some true} := by
    rw [models_some_true]
    rfl
  exact Bool.noConfusion (consequence member)

/-- Adding a consequence leaves the model class unchanged. -/
theorem insert_consequence_models :
    models sat (insert none {some true}) = models sat {some true} :=
  models_insert_eq_iff.mpr entails_none

/-- Adding a non-consequence loses a model. -/
theorem insert_nonconsequence_models :
    ¬ models sat {some true} ⊆ models sat (insert (some false) {some true}) :=
  not_models_subset_insert_iff.mpr not_entails_some_false

/-- The contradictory theory has no models. -/
theorem models_contradiction :
    models sat (insert (some false) {some true}) = ∅ := by
  ext m
  constructor
  · intro member
    have isFalse : m = false := (mem_models_insert.mp member).1
    have isTrue : m = true := (mem_models_insert.mp member).2 rfl
    exact Bool.noConfusion (isFalse.symm.trans isTrue)
  · intro member
    exact member.elim

/-- Negative control for the adjunction: `some false` is not in the theory of
`{true}`, and correspondingly `true` is not a model of `{some false}`. -/
theorem adjunction_negative :
    ¬ ({some false} : Set (Option Bool)) ⊆ theoryOf sat {true} ∧
      ¬ ({true} : Set Bool) ⊆ models sat {some false} := by
  constructor
  · intro included
    exact Bool.noConfusion (included rfl (rfl : true = true))
  · intro included
    exact Bool.noConfusion (included rfl (rfl : some false = some false))

end Control

end Mettapedia.Logic.TheoryModel
