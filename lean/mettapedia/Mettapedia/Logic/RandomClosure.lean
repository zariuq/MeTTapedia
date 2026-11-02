import Mettapedia.GSLT.OpenEnded.ClosureSystems
import Mettapedia.Logic.DerivationClosure
import Mettapedia.InformationTheory.FiniteProbability
import Mathlib.Combinatorics.Enumerative.InclusionExclusion

/-!
# Random closure responses

A component is observed through its response to every interface seed.
Joining closure operators intersects their fixed-point families. Independent
random components therefore multiply the probabilities that prescribed
families remain closed. Query extraction uses inclusion-exclusion, retaining
the dependence between different closed-set observations.

This is the commonality construction for random closure systems, using the
classical Horn/Moore correspondence and finite inclusion-exclusion. These
ingredients are established mathematics; the interface interpretation and
its probability laws specify their use for recursive program components.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.RandomClosure

open Set Finset
open scoped BigOperators
open Mettapedia.GSLT.OpenEnded.ClosureSystems

section Join
variable {L : Type*} [CompleteLattice L]

/-- The closure whose closed elements satisfy both supplied closures. -/
def join (c d : ClosureOperator L) : ClosureOperator L :=
  closureOf (F := {x | c.IsClosed x ∧ d.IsClosed x}) (by
    intro S included
    exact ⟨ClosureOperator.sInf_isClosed (fun x hx => (included hx).1),
      ClosureOperator.sInf_isClosed (fun x hx => (included hx).2)⟩)

@[simp] theorem join_closed (c d : ClosureOperator L) (x : L) :
    (join c d).IsClosed x ↔ c.IsClosed x ∧ d.IsClosed x := Iff.rfl

theorem le_join_left (c d : ClosureOperator L) (x : L) : c x ≤ join c d x :=
  c.closure_min ((join c d).le_closure x) ((join c d).isClosed_closure x).1

theorem le_join_right (c d : ClosureOperator L) (x : L) : d x ≤ join c d x :=
  d.closure_min ((join c d).le_closure x) ((join c d).isClosed_closure x).2

/-- The constructed operator is the least upper bound in the pointwise order. -/
theorem join_le (c d e : ClosureOperator L) (hc : ∀ x, c x ≤ e x) (hd : ∀ x, d x ≤ e x)
    (x : L) : join c d x ≤ e x := by
  apply (join c d).closure_min (e.le_closure x)
  constructor
  · apply c.isClosed_iff_closure_le.mpr
    simpa only [e.idempotent] using hc (e x)
  · apply d.isClosed_iff_closure_le.mpr
    simpa only [e.idempotent] using hd (e x)

theorem join_comm (c d : ClosureOperator L) : join c d = join d c :=
  ClosureOperator.ext_isClosed _ _ (fun _ => and_comm)

theorem join_assoc (a b c : ClosureOperator L) : join (join a b) c = join a (join b c) :=
  ClosureOperator.ext_isClosed _ _ (fun _ => and_assoc)

@[simp] theorem join_self (c : ClosureOperator L) : join c c = c :=
  ClosureOperator.ext_isClosed _ _ (fun _ => by simp)

@[simp] theorem join_identity (c : ClosureOperator L) : join (ClosureOperator.id L) c = c :=
  ClosureOperator.ext_isClosed _ _ (fun _ => by simp [ClosureOperator.id])

def Closes (c : ClosureOperator L) (family : Finset L) : Prop := ∀ x ∈ family, c.IsClosed x

/-- Arbitrarily many components, including the empty family. -/
def joinFamily {I : Type*} (c : I → ClosureOperator L) : ClosureOperator L :=
  closureOf (F := {x | ∀ i, (c i).IsClosed x}) (by
    intro S included i
    exact ClosureOperator.sInf_isClosed (fun x hx => included hx i))

@[simp] theorem joinFamily_closed {I : Type*} (c : I → ClosureOperator L) (x : L) :
    (joinFamily c).IsClosed x ↔ ∀ i, (c i).IsClosed x := Iff.rfl

theorem le_joinFamily {I : Type*} (c : I → ClosureOperator L) (i : I) (x : L) :
    c i x ≤ joinFamily c x :=
  (c i).closure_min ((joinFamily c).le_closure x) ((joinFamily c).isClosed_closure x i)

@[simp] theorem closes_joinFamily {I : Type*} (c : I → ClosureOperator L) (family : Finset L) :
    Closes (joinFamily c) family ↔ ∀ i, Closes (c i) family :=
  ⟨fun h i x hx => h x hx i, fun h x hx i => h i x hx⟩

@[simp] theorem closes_join (c d : ClosureOperator L) (family : Finset L) :
    Closes (join c d) family ↔ Closes c family ∧ Closes d family := by
  simp only [Closes, join_closed, forall_and]

/-- Canonical finite intersection closure, including the empty intersection. -/
noncomputable def meetHull (family : Finset L) : Finset L := by
  classical
  exact family.powerset.image fun members : Finset L => sInf (members : Set L)

theorem closes_meetHull (c : ClosureOperator L) (family : Finset L) :
    Closes c (meetHull family) ↔ Closes c family := by
  classical
  constructor
  · intro closed x member
    have generated : x ∈ meetHull family := by
      apply Finset.mem_image.mpr
      exact ⟨{x}, Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr member), by simp⟩
    exact closed x generated
  · intro closed x member
    obtain ⟨members, included, rfl⟩ := Finset.mem_image.mp member
    exact ClosureOperator.sInf_isClosed (fun y hy => closed y ((Finset.mem_powerset.mp included) hy))

end Join

section Components
variable {A : Type*}

/-- The scope records every atom a component can read or derive. -/
structure Component (A : Type*) where
  scope : Set A
  rules : List A → A → Prop
  base : Set A
  base_scoped : base ⊆ scope
  rule_scoped : ∀ premises conclusion, rules premises conclusion →
    conclusion ∈ scope ∧ ∀ a ∈ premises, a ∈ scope

namespace Component

/-- Actual finite derivations from the fixed base and the supplied seeds. -/
def closure (component : Component A) : ClosureOperator (Set A) where
  toFun seed := {a | FinitaryClosure.close component.rules (fun b => b ∈ component.base ∪ seed) a}
  monotone' _ _ included a member := FinitaryClosure.close_mono _
    (fun b hb => hb.elim Or.inl (fun h => Or.inr (included h))) a member
  le_closure' seed a member := FinitaryClosure.seeds_le_close _ _ a (Or.inr member)
  idempotent' seed := by
    ext a
    constructor
    · intro member
      exact FinitaryClosure.close_le _
        (fun b hb => hb.elim (fun h => FinitaryClosure.seeds_le_close _ _ b (Or.inl h)) id)
        (FinitaryClosure.close_closed _ _) a member
    · intro member
      exact FinitaryClosure.seeds_le_close _ _ a (Or.inr member)

theorem base_le (component : Component A) (seed : Set A) : component.base ⊆ component.closure seed :=
  fun a member => FinitaryClosure.seeds_le_close _ _ a (Or.inl member)

theorem rules_closed (component : Component A) (seed : Set A) :
    FinitaryClosure.Closed component.rules (fun a => a ∈ component.closure seed) := FinitaryClosure.close_closed _ _

theorem closed_iff (component : Component A) (candidate : Set A) :
    component.closure.IsClosed candidate ↔
      component.base ⊆ candidate ∧ FinitaryClosure.Closed component.rules (fun a => a ∈ candidate) := by
  constructor
  · intro closed
    have equal := component.closure.isClosed_iff.mp closed
    exact ⟨equal ▸ component.base_le candidate, equal ▸ component.rules_closed candidate⟩
  · rintro ⟨base, rules⟩
    apply component.closure.isClosed_iff_closure_le.mpr
    exact fun a ha => FinitaryClosure.close_le _ (fun b hb => hb.elim (fun h => base h) id) rules a ha

theorem closure_scoped (component : Component A) {seed : Set A} (inside : seed ⊆ component.scope) :
    component.closure seed ⊆ component.scope :=
  fun a ha => FinitaryClosure.close_le _ (fun _ hb => hb.elim (fun h => component.base_scoped h) (fun h => inside h))
    (fun premises conclusion rule _ => (component.rule_scoped premises conclusion rule).1) a ha

/-- Rules cannot change an input atom that never occurs as a rule head. -/
theorem closure_readonly (component : Component A) (inputs : Set A)
    (readonly : ∀ body head, component.rules body head → head ∉ inputs)
    (seed : Set A) {a : A} (input : a ∈ inputs) :
    a ∈ component.closure seed ↔ a ∈ component.base ∪ seed := by
  constructor
  · intro derived
    exact FinitaryClosure.close_le component.rules
      (candidate := fun x => x ∈ inputs → x ∈ component.base ∪ seed)
      (fun _ seeded _ => seeded)
      (fun body head rule _ immutable => (readonly body head rule immutable).elim) a derived input
  · intro seeded
    exact FinitaryClosure.seeds_le_close _ _ a seeded

def combine (left right : Component A) : Component A where
  scope := left.scope ∪ right.scope
  rules premises conclusion := left.rules premises conclusion ∨ right.rules premises conclusion
  base := left.base ∪ right.base
  base_scoped := Set.union_subset_union left.base_scoped right.base_scoped
  rule_scoped premises conclusion rule := by
    rcases rule with first | second
    · have h := left.rule_scoped _ _ first
      exact ⟨Or.inl h.1, fun a ha => Or.inl (h.2 a ha)⟩
    · have h := right.rule_scoped _ _ second
      exact ⟨Or.inr h.1, fun a ha => Or.inr (h.2 a ha)⟩

theorem combine_closure (left right : Component A) :
    (combine left right).closure = join left.closure right.closure := by
  apply ClosureOperator.ext_isClosed
  intro candidate
  rw [join_closed, closed_iff, closed_iff, closed_iff]
  constructor
  · rintro ⟨base, rules⟩
    exact ⟨⟨fun a ha => base (Or.inl ha), fun p a hp hs => rules p a (Or.inl hp) hs⟩,
      ⟨fun a ha => base (Or.inr ha), fun p a hp hs => rules p a (Or.inr hp) hs⟩⟩
  · rintro ⟨⟨baseL, rulesL⟩, ⟨baseR, rulesR⟩⟩
    refine ⟨Set.union_subset baseL baseR, ?_⟩
    intro p a rule hs
    rcases rule with first | second
    · exact rulesL p a first hs
    · exact rulesR p a second hs

theorem closed_union_of_scope (component : Component A) (seed extra : Set A)
    (inside : extra ∩ component.scope ⊆ component.closure seed) :
    component.closure.IsClosed (component.closure seed ∪ extra) := by
  apply (closed_iff _ _).mpr
  refine ⟨fun a ha => Or.inl (component.base_le seed ha), ?_⟩
  intro premises conclusion rule body
  apply Or.inl
  apply component.rules_closed seed premises conclusion rule
  intro a member
  rcases body a member with owned | other
  · exact owned
  · exact inside ⟨other, (component.rule_scoped _ _ rule).2 a member⟩

def combineFamily {I : Type*} (components : I → Component A) : Component A where
  scope := ⋃ i, (components i).scope
  rules premises conclusion := ∃ i, (components i).rules premises conclusion
  base := ⋃ i, (components i).base
  base_scoped := by
    intro a member
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp member
    exact Set.mem_iUnion.mpr ⟨i, (components i).base_scoped hi⟩
  rule_scoped premises conclusion rule := by
    obtain ⟨i, hi⟩ := rule
    have coverage := (components i).rule_scoped premises conclusion hi
    exact ⟨Set.mem_iUnion.mpr ⟨i, coverage.1⟩,
      fun a ha => Set.mem_iUnion.mpr ⟨i, coverage.2 a ha⟩⟩

theorem combineFamily_closure {I : Type*} (components : I → Component A) :
    (combineFamily components).closure = joinFamily (fun i => (components i).closure) := by
  apply ClosureOperator.ext_isClosed
  intro candidate
  rw [joinFamily_closed, closed_iff]
  constructor
  · rintro ⟨base, rules⟩ i
    apply (closed_iff _ _).mpr
    exact ⟨fun a ha => base (Set.mem_iUnion.mpr ⟨i, ha⟩),
      fun p a hr hs => rules p a ⟨i, hr⟩ hs⟩
  · intro allClosed
    refine ⟨?_, ?_⟩
    · intro a ha
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ha
      exact ((closed_iff _ _).mp (allClosed i)).1 hi
    · rintro p a ⟨i, hi⟩ hs
      exact ((closed_iff _ _).mp (allClosed i)).2 p a hi hs

end Component

def expand (boundary : Set A) (seed : Set boundary) : Set A := Subtype.val '' seed

theorem expand_subset (boundary : Set A) (seed : Set boundary) : expand boundary seed ⊆ boundary := by
  rintro _ ⟨a, _, rfl⟩
  exact a.property

/-- Hiding retains the response to every possible boundary input. -/
def response (boundary : Set A) (c : ClosureOperator (Set A)) : ClosureOperator (Set boundary) where
  toFun seed := Subtype.val ⁻¹' c (expand boundary seed)
  monotone' _ _ included := fun _ member => c.monotone (Set.image_mono included) member
  le_closure' _ := fun a member => c.le_closure _ ⟨a, member, rfl⟩
  idempotent' seed := by
    ext a
    constructor
    · intro member
      have included : expand boundary (Subtype.val ⁻¹' c (expand boundary seed)) ⊆ c (expand boundary seed) := by
        rintro _ ⟨b, hb, rfl⟩
        exact hb
      change a.val ∈ c (expand boundary seed)
      simpa only [c.idempotent] using c.monotone included member
    · intro member
      exact c.le_closure _ ⟨a, member, rfl⟩

theorem response_closed_iff (boundary : Set A) (c : ClosureOperator (Set A)) (seed : Set boundary) :
    (response boundary c).IsClosed seed ↔ c (expand boundary seed) ∩ boundary ⊆ expand boundary seed := by
  rw [ClosureOperator.isClosed_iff_closure_le]
  constructor
  · intro closed a member
    exact ⟨⟨a, member.2⟩, closed member.1, rfl⟩
  · intro closed a member
    obtain ⟨b, hb, equal⟩ := closed ⟨member, a.property⟩
    have same : b = a := Subtype.ext equal
    exact same ▸ hb

/-- Distinct private scopes can interact only through the retained interface.
The resulting response includes all alternating feedback, not one evaluation pass. -/
theorem response_combine (left right : Component A) (boundary : Set A)
    (inLeft : boundary ⊆ left.scope) (inRight : boundary ⊆ right.scope)
    (private_disjoint : left.scope ∩ right.scope ⊆ boundary) :
    response boundary (Component.combine left right).closure =
      join (response boundary left.closure) (response boundary right.closure) := by
  rw [Component.combine_closure]
  apply ClosureOperator.ext_isClosed
  intro seed
  rw [join_closed, response_closed_iff, response_closed_iff, response_closed_iff]
  let X := expand boundary seed
  have leftScope := left.closure_scoped ((expand_subset boundary seed).trans inLeft)
  have rightScope := right.closure_scoped ((expand_subset boundary seed).trans inRight)
  constructor
  · intro closed
    exact ⟨fun a ha => closed ⟨le_join_left left.closure right.closure X ha.1, ha.2⟩,
      fun a ha => closed ⟨le_join_right left.closure right.closure X ha.1, ha.2⟩⟩
  · rintro ⟨closedLeft, closedRight⟩
    have leftFixed := left.closed_union_of_scope X (right.closure X) (by
      intro a ha
      exact left.closure.le_closure X (closedRight ⟨ha.1, private_disjoint ⟨ha.2, rightScope ha.1⟩⟩))
    have rightFixed := right.closed_union_of_scope X (left.closure X) (by
      intro a ha
      exact right.closure.le_closure X (closedLeft ⟨ha.1, private_disjoint ⟨leftScope ha.1, ha.2⟩⟩))
    have combined : join left.closure right.closure X ⊆ left.closure X ∪ right.closure X :=
      (join left.closure right.closure).closure_min
        (fun a ha => Or.inl (left.closure.le_closure X ha))
        ⟨leftFixed, by simpa only [Set.union_comm] using rightFixed⟩
    intro a ha
    rcases combined ha.1 with first | second
    · exact closedLeft ⟨first, ha.2⟩
    · exact closedRight ⟨second, ha.2⟩

theorem response_combineFamily_readonly {I : Type*} (components : I → Component A) (boundary inputs : Set A)
    (inside : ∀ i, boundary ⊆ (components i).scope)
    (private_disjoint : ∀ i j, i ≠ j → (components i).scope ∩ (components j).scope ⊆ boundary ∪ inputs)
    (readonly : ∀ i body head, (components i).rules body head → head ∉ inputs)
    (consistent : ∀ i j a, a ∈ inputs → (a ∈ (components i).base ↔ a ∈ (components j).base)) :
    response boundary (Component.combineFamily components).closure =
      joinFamily (fun i => response boundary (components i).closure) := by
  classical
  rw [Component.combineFamily_closure]
  apply ClosureOperator.ext_isClosed
  intro seed
  rw [joinFamily_closed, response_closed_iff]
  simp only [response_closed_iff]
  let X := expand boundary seed
  have coverage (i : I) := (components i).closure_scoped ((expand_subset boundary seed).trans (inside i))
  constructor
  · intro allClosed i a ha
    exact allClosed ⟨le_joinFamily (fun j => (components j).closure) i X ha.1, ha.2⟩
  · intro eachClosed
    let Y : Set A := X ∪ ⋃ i, (components i).closure X
    have includes (i : I) : (components i).closure X ⊆ Y :=
      fun a ha => Or.inr (Set.mem_iUnion.mpr ⟨i, ha⟩)
    have fixed (i : I) : (components i).closure.IsClosed Y := by
      have current := (components i).closed_union_of_scope X Y (by
        intro a ha
        rcases ha.1 with seedMember | derived
        · exact (components i).closure.le_closure X seedMember
        · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp derived
          by_cases same : i = j
          · simpa only [same] using hj
          · rcases private_disjoint i j same ⟨ha.2, coverage j hj⟩ with port | input
            · exact (components i).closure.le_closure X (eachClosed j ⟨hj, port⟩)
            · rcases ((components j).closure_readonly inputs (readonly j) X input).mp hj with base | seeded
              · exact (components i).base_le X ((consistent j i a input).mp base)
              · exact (components i).closure.le_closure X seeded)
      simpa only [Set.union_eq_right.mpr (includes i)] using current
    have combined : joinFamily (fun i => (components i).closure) X ⊆ Y :=
      (joinFamily (fun i => (components i).closure)).closure_min Set.subset_union_left fixed
    intro a ha
    rcases combined ha.1 with seedMember | derived
    · exact seedMember
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp derived
      exact eachClosed i ⟨hi, ha.2⟩

theorem response_combineFamily {I : Type*} (components : I → Component A) (boundary : Set A)
    (inside : ∀ i, boundary ⊆ (components i).scope)
    (private_disjoint : ∀ i j, i ≠ j → (components i).scope ∩ (components j).scope ⊆ boundary) :
    response boundary (Component.combineFamily components).closure =
      joinFamily (fun i => response boundary (components i).closure) := by
  apply response_combineFamily_readonly components boundary ∅ inside
  · simpa only [Set.union_empty] using private_disjoint
  · intro i body head rule
    exact Set.notMem_empty head
  · intro i j a absent
    exact absent.elim

end Components

section Weights
variable {L Ω Ψ R : Type*} [CompleteLattice L] [Fintype Ω] [Fintype Ψ] [CommSemiring R]

/-- Unnormalized weights permit local evidence without premature division. -/
noncomputable def commonality (weight : Ω → R) (response : Ω → ClosureOperator L) (family : Finset L) : R := by
  classical
  exact ∑ world, if Closes (response world) family then weight world else 0

theorem commonality_product (p : Ω → R) (q : Ψ → R)
    (c : Ω → ClosureOperator L) (d : Ψ → ClosureOperator L) (family : Finset L) :
    commonality (fun world : Ω × Ψ => p world.1 * q world.2)
      (fun world => join (c world.1) (d world.2)) family =
        commonality p c family * commonality q d family := by
  classical
  unfold commonality
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  simp only [closes_join]
  by_cases first : Closes (c a) family <;> by_cases second : Closes (d b) family <;>
    simp [first, second]

open scoped Classical in
theorem commonality_family {I : Type*} [Fintype I] {World : I → Type*} [∀ i, Fintype (World i)]
    (p : ∀ i, World i → R) (c : ∀ i, World i → ClosureOperator L) (family : Finset L) :
    commonality (fun world : ∀ i, World i => ∏ i, p i (world i))
      (fun world => joinFamily (fun i => c i (world i))) family =
        ∏ i, commonality (p i) (c i) family := by
  classical
  have factor (world : ∀ i, World i) :
      (if Closes (joinFamily (fun i => c i (world i))) family then ∏ i, p i (world i) else 0) =
        ∏ i, if Closes (c i (world i)) family then p i (world i) else 0 := by
    by_cases closed : ∀ i, Closes (c i (world i)) family
    · simp [closed]
    · rw [if_neg (fun h => closed ((closes_joinFamily _ _).mp h))]
      obtain ⟨i, absent⟩ := not_forall.mp closed
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg absent)
  simp only [commonality, factor]
  exact (Fintype.prod_sum (fun i (world : World i) => if Closes (c i world) family then p i world else 0)).symm

@[simp] theorem commonality_empty (p : Ω → R) (c : Ω → ClosureOperator L) :
    commonality p c ∅ = ∑ world, p world := by simp [commonality, Closes]

theorem commonality_meetHull (p : Ω → R) (c : Ω → ClosureOperator L) (family : Finset L) :
    commonality p c (meetHull family) = commonality p c family := by
  classical
  unfold commonality
  apply Finset.sum_congr rfl
  intro world _
  by_cases closed : Closes (c world) family
  · have hull := (closes_meetHull (c world) family).mpr closed
    simp [closed, hull]
  · have hull : ¬ Closes (c world) (meetHull family) := fun h => closed ((closes_meetHull _ _).mp h)
    simp [closed, hull]

theorem commonality_congr_hull (p : Ω → R) (c : Ω → ClosureOperator L) {first second : Finset L}
    (same : meetHull first = meetHull second) : commonality p c first = commonality p c second := by
  rw [← commonality_meetHull p c first, same, commonality_meetHull]

end Weights

section Observation
variable {B : Type*} [Fintype B]
open scoped Classical

noncomputable def avoiding (seed : Set B) (query : B) : Finset (Set B) := by
  classical
  exact Finset.univ.filter fun candidate => seed ⊆ candidate ∧ query ∉ candidate

@[simp] theorem mem_avoiding (seed : Set B) (query : B) (candidate : Set B) :
    candidate ∈ avoiding seed query ↔ seed ⊆ candidate ∧ query ∉ candidate := by
  classical
  simp [avoiding]

theorem absent_iff_closed_witness (c : ClosureOperator (Set B)) (seed : Set B) (query : B) :
    query ∉ c seed ↔ ∃ candidate ∈ avoiding seed query, c.IsClosed candidate := by
  constructor
  · intro absent
    exact ⟨c seed, (mem_avoiding _ _ _).mpr ⟨c.le_closure seed, absent⟩, c.isClosed_closure seed⟩
  · rintro ⟨candidate, member, closed⟩ belongs
    exact ((mem_avoiding _ _ _).mp member).2
      (c.closure_min ((mem_avoiding _ _ _).mp member).1 closed belongs)

variable {Ω R : Type*} [Fintype Ω] [CommRing R]

/-- Signed extraction retains joint closed-set events, including the empty family. -/
noncomputable def extract (p : Ω → R) (c : Ω → ClosureOperator (Set B)) (seed : Set B) (query : B) : R :=
  ∑ family ∈ (avoiding seed query).powerset, (-1 : R) ^ family.card * commonality p c family

theorem extract_correct (p : Ω → R) (c : Ω → ClosureOperator (Set B)) (seed : Set B) (query : B) :
    extract p c seed query = ∑ world, if query ∈ c world seed then p world else 0 := by
  classical
  let event : Set B → Finset Ω := fun candidate => Finset.univ.filter fun world => (c world).IsClosed candidate
  have observed : (avoiding seed query).inf (fun candidate => (event candidate)ᶜ) =
      Finset.univ.filter (fun world => query ∈ c world seed) := by
    ext world
    simp only [Finset.mem_inf, Finset.mem_compl, event, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro none
      by_contra absent
      obtain ⟨candidate, member, closed⟩ := (absent_iff_closed_witness (c world) seed query).mp absent
      exact none candidate member closed
    · intro present candidate member closed
      exact ((absent_iff_closed_witness (c world) seed query).mpr ⟨candidate, member, closed⟩) present
  have joint (family : Finset (Set B)) : (∑ world ∈ family.inf event, p world) = commonality p c family := by
    have indexing : family.inf event = Finset.univ.filter (fun world => Closes (c world) family) := by
      ext world
      constructor
      · intro member
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ world, fun candidate hc => ?_⟩
        exact (Finset.mem_filter.mp (Finset.mem_inf.mp member candidate hc)).2
      · intro member
        apply Finset.mem_inf.mpr
        intro candidate hc
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ world, (Finset.mem_filter.mp member).2 candidate hc⟩
    rw [indexing, Finset.sum_filter]
    rfl
  have result := Finset.inclusion_exclusion_sum_inf_compl (avoiding seed query) event p
  rw [observed, Finset.sum_filter] at result
  simpa only [joint, zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, extract] using result.symm

/-- Merge equal intersection closures and add their signed coefficients. -/
noncomputable def preparedExtract (p : Ω → R) (c : Ω → ClosureOperator (Set B))
    (seed : Set B) (query : B) : R :=
  let families := (avoiding seed query).powerset
  ∑ row ∈ families.image meetHull,
    (∑ family ∈ families with meetHull family = row, (-1 : R) ^ family.card) * commonality p c row

theorem preparedExtract_eq_extract (p : Ω → R) (c : Ω → ClosureOperator (Set B))
    (seed : Set B) (query : B) : preparedExtract p c seed query = extract p c seed query := by
  classical
  unfold preparedExtract extract
  simp_rw [Finset.sum_mul]
  have grouped := Finset.sum_fiberwise_of_maps_to
    (s := (avoiding seed query).powerset) (t := (avoiding seed query).powerset.image meetHull)
    (g := meetHull) (fun family member => Finset.mem_image_of_mem meetHull member)
    (fun family => (-1 : R) ^ family.card * commonality p c family)
  rw [← grouped]
  apply Finset.sum_congr rfl
  intro row _
  apply Finset.sum_congr rfl
  intro family member
  rw [← (Finset.mem_filter.mp member).2, commonality_meetHull]

theorem preparedExtract_correct (p : Ω → R) (c : Ω → ClosureOperator (Set B))
    (seed : Set B) (query : B) :
    preparedExtract p c seed query = ∑ world, if query ∈ c world seed then p world else 0 :=
  (preparedExtract_eq_extract p c seed query).trans (extract_correct p c seed query)

end Observation

section FactoredPrograms
variable {A I R : Type*} [Fintype I] {World : I → Type*} [∀ i, Fintype (World i)] [CommRing R]
variable (components : ∀ i, World i → Component A) (boundary : Set A) [Fintype boundary]
variable (inside : ∀ i world, boundary ⊆ (components i world).scope)
variable (separated : ∀ i j, i ≠ j → ∀ first second,
  (components i first).scope ∩ (components j second).scope ⊆ boundary)
open scoped Classical
include inside separated

omit [Fintype boundary] in
/-- Independent local choices factor after the actual component rules are joined. -/
theorem component_commonality (p : ∀ i, World i → R) (family : Finset (Set boundary)) :
    commonality (fun world : ∀ i, World i => ∏ i, p i (world i))
      (fun world => response boundary (Component.combineFamily (fun i => components i (world i))).closure) family =
        ∏ i, commonality (p i) (fun world => response boundary (components i world).closure) family := by
  have responses (world : ∀ i, World i) := response_combineFamily (fun i => components i (world i)) boundary
    (fun i => inside i (world i)) (fun i j unequal => separated i j unequal (world i) (world j))
  simp_rw [commonality, responses]
  exact commonality_family p (fun i world => response boundary (components i world).closure) family

/-- The transformed product computes the query mass of combined rule execution. -/
theorem component_query_mass (p : ∀ i, World i → R) (seed : Set boundary) (query : boundary) :
    (∑ family ∈ (avoiding seed query).powerset, (-1 : R) ^ family.card *
      ∏ i, commonality (p i) (fun world => response boundary (components i world).closure) family) =
        ∑ world : ∀ i, World i,
          if query ∈ response boundary (Component.combineFamily (fun i => components i (world i))).closure seed
          then ∏ i, p i (world i) else 0 := by
  rw [← extract_correct (fun world : ∀ i, World i => ∏ i, p i (world i))
    (fun world => response boundary (Component.combineFamily (fun i => components i (world i))).closure) seed query]
  unfold extract
  apply Finset.sum_congr rfl
  intro family _
  rw [component_commonality components boundary inside separated]

end FactoredPrograms

open scoped Classical in
/-- Condition on shared inputs once. Every component agrees on those fixed
base facts and no rule can redefine them; private choices then factor. -/
theorem conditioned_component_query_mass
    {A I H R : Type*} [Fintype I] [Fintype H] {World : I → Type*}
    [∀ i, Fintype (World i)] [CommRing R]
    (components : H → ∀ i, World i → Component A) (boundary inputs : Set A) [Fintype boundary]
    (inside : ∀ h i w, boundary ⊆ (components h i w).scope)
    (separated : ∀ h i j, i ≠ j → ∀ x y,
      (components h i x).scope ∩ (components h j y).scope ⊆ boundary ∪ inputs)
    (readonly : ∀ h i w body head, (components h i w).rules body head → head ∉ inputs)
    (consistent : ∀ h i j x y a, a ∈ inputs →
      (a ∈ (components h i x).base ↔ a ∈ (components h j y).base))
    (shared : H → R) (weight : H → ∀ i, World i → R) (seed : Set boundary) (query : boundary) :
    (∑ h, shared h * ∑ family ∈ (avoiding seed query).powerset, (-1 : R) ^ family.card *
      ∏ i, commonality (weight h i) (fun w => response boundary (components h i w).closure) family) =
      ∑ h, shared h * ∑ world : ∀ i, World i,
        if query ∈ response boundary (Component.combineFamily (fun i => components h i (world i))).closure seed
        then ∏ i, weight h i (world i) else 0 := by
  classical
  apply Finset.sum_congr rfl
  intro h _
  congr 1
  have responses (world : ∀ i, World i) := response_combineFamily_readonly
    (fun i => components h i (world i)) boundary inputs (fun i => inside h i (world i))
    (fun i j ne => separated h i j ne (world i) (world j))
    (fun i => readonly h i (world i)) (fun i j a ha => consistent h i j (world i) (world j) a ha)
  rw [← extract_correct (fun world : ∀ i, World i => ∏ i, weight h i (world i))
    (fun world => response boundary (Component.combineFamily (fun i => components h i (world i))).closure) seed query]
  unfold extract
  apply Finset.sum_congr rfl
  intro family _
  congr 1
  symm
  simp_rw [commonality, responses]
  exact commonality_family (weight h) (fun i w => response boundary (components h i w).closure) family

namespace Controls
open scoped Classical

/-- A single implication, interpreted by the same derivation closure as programs. -/
def implication {A : Type*} (premise conclusion : A) : Component A where
  scope := Set.univ
  rules body head := body = [premise] ∧ head = conclusion
  base := ∅
  base_scoped := Set.empty_subset _
  rule_scoped _ _ _ := ⟨Set.mem_univ _, fun _ _ => Set.mem_univ _⟩

theorem implication_apply {A : Type*} (a b : A) (seed : Set A) :
    (implication a b).closure seed = if a ∈ seed then insert b seed else seed := by
  classical
  by_cases present : a ∈ seed
  · rw [if_pos present]
    apply Set.Subset.antisymm
    · apply (implication a b).closure.closure_min (Set.subset_insert _ _)
      apply (Component.closed_iff _ _).mpr
      refine ⟨Set.empty_subset _, ?_⟩
      rintro p head ⟨rfl, rfl⟩ _
      exact Set.mem_insert _ _
    · intro x hx
      rcases hx with equal | seeded
      · rw [equal]
        exact (implication a b).rules_closed seed [a] b ⟨rfl, rfl⟩
          (fun x hx => (List.mem_singleton.mp hx) ▸ (implication a b).closure.le_closure seed present)
      · exact (implication a b).closure.le_closure seed seeded
  · rw [if_neg present]
    apply Set.Subset.antisymm
    · apply (implication a b).closure.closure_min Set.Subset.rfl
      apply (Component.closed_iff _ _).mpr
      refine ⟨Set.empty_subset _, ?_⟩
      rintro p head ⟨rfl, rfl⟩ body
      exact (present (body a (List.mem_singleton_self a))).elim
    · exact (implication a b).closure.le_closure seed

theorem empty_snapshot_loses_future_response :
    (implication (0 : Fin 3) 1).closure ∅ = (ClosureOperator.id (Set (Fin 3))) ∅ ∧
      (implication (0 : Fin 3) 1).closure {0} ≠ (ClosureOperator.id (Set (Fin 3))) {0} := by
  constructor
  · simpa only [implication_apply, Set.notMem_empty, ↓reduceIte] using
      (show (∅ : Set (Fin 3)) = (ClosureOperator.id (Set (Fin 3))) ∅ from rfl)
  · intro equal
    have member : (1 : Fin 3) ∈ (implication (0 : Fin 3) 1).closure {0} := by simp [implication_apply]
    rw [equal] at member
    change (1 : Fin 3) ∈ ({0} : Set (Fin 3)) at member
    norm_num at member

theorem one_pass_misses_feedback :
    (2 : Fin 3) ∉ (implication 0 1).closure ((implication 1 2).closure {0}) ∧
      (2 : Fin 3) ∈ (Component.combine (implication 1 2) (implication 0 1)).closure {0} := by
  constructor
  · norm_num [implication_apply]
    decide
  · let c := Component.combine (implication (1 : Fin 3) 2) (implication 0 1)
    have first : (1 : Fin 3) ∈ c.closure {0} :=
      c.rules_closed {0} [0] 1 (Or.inr ⟨rfl, rfl⟩)
        (fun x hx => (List.mem_singleton.mp hx) ▸ c.closure.le_closure {0} (Set.mem_singleton 0))
    exact c.rules_closed {0} [1] 2 (Or.inl ⟨rfl, rfl⟩)
      (fun x hx => (List.mem_singleton.mp hx) ▸ first)

theorem self_loop_creates_no_support : (implication () ()).closure ∅ = ∅ := by
  simp [implication_apply]

/-- Randomly enabled facts give a minimal shared-choice counterexample. -/
def factResponse (enabled : Bool) : ClosureOperator (Set Unit) where
  toFun seed := {a | enabled = true ∨ a ∈ seed}
  monotone' _ _ included _ h := h.elim Or.inl (fun h => Or.inr (included h))
  le_closure' _ _ h := Or.inr h
  idempotent' seed := by
    ext a
    change (enabled = true ∨ enabled = true ∨ a ∈ seed) ↔ (enabled = true ∨ a ∈ seed)
    tauto

theorem shared_choice_is_not_an_independent_copy :
    commonality (fun _ : Bool => (1 / 2 : ℚ)) (fun w => join (factResponse w) (factResponse w)) {∅} = 1 / 2 ∧
      commonality (fun _ : Bool × Bool => (1 / 4 : ℚ))
        (fun w => join (factResponse w.1) (factResponse w.2)) {∅} = 1 / 4 := by
  have fixed (w : Bool) : Closes (factResponse w) {∅} ↔ w = false := by
    simp only [Closes, Finset.mem_singleton, forall_eq, ClosureOperator.isClosed_iff]
    change ({a : Unit | w = true ∨ a ∈ (∅ : Set Unit)} : Set Unit) = ∅ ↔ w = false
    cases w <;> simp
  constructor
  · simp [commonality, fixed]
  · simp [commonality, closes_join, fixed, Fintype.sum_prod_type]

end Controls

end Mettapedia.Logic.RandomClosure
