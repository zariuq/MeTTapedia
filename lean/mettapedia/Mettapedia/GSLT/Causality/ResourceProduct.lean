import Mettapedia.GSLT.Causality.ResourceExploration
import Mettapedia.GSLT.Causality.TraceCostValuation
import Mettapedia.GSLT.Core.GSLTConstructions
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Data.Multiset.Filter
import Mathlib.Data.Multiset.Sum

/-!
# Two resource systems fired together, and paying as a product

Two systems on the same resources are fired together by joint instances: a
joint instance names one instance of each system and consumes, reads and
produces what the two do. When a predicate on resources keeps the two parts
apart, a joint instance is enabled exactly when its parts are, two joint
instances are concurrent exactly when their parts are, and firing fires both
parts.

The product of two systems is the case in which the two parts use resources of
different types: each system is seen in the sum of the two carriers, and the
two are fired together there. This is the synchronous product of transition
systems (Arnold and Nivat) and of nets (Winskel), with the joint instances as
the allowed synchronisations. Every bag over two kinds of resource is a bag of
the first kind beside a bag of the second, in one way, so the statements about
the product are made for such pairs. A joint instance is enabled exactly when
its two parts are, firing it fires both, and a run of the product is a run of
each system on its own part of the bag.

Splitting a bag into its two parts sends every step of the product to a step of
the synchronous product of the two theories. The converse holds when every pair
of instances is named by a joint instance. It fails for paying: a paying
instance is paired with its own price only.

A finite run is a path of occurrences, and a grade of the instances fired is a
valuation of such paths. What a run changes is one law: the bag before a run,
with all that its firings produce, is the bag after it with all that they
consume. Such a grade is a property of the trace of the run: two concurrent
firings fire the same two instances in either order. What a run consumes and
what it produces are therefore accounts of its trace, and the law holds trace
by trace. Conservation laws are instances of the one law, read through an
additive observation of bags.

Paying is the product with a purse system. An unordered purse is a bag of
tokens, and a firing takes its price from the bag. Ordered purses are lists of
cells kept at places, and a firing takes the top cell of each purse in a chosen
bag of purses at its place. A law of payment is a law of the product or of the
purse system alone: a funded instance is enabled exactly when the instance is
enabled and its price is in the purse, and two funded firings are concurrent
exactly when the firings are concurrent and both prices are in the purse
together. Along every run, the cells of the purses before are the cells after
with the top cells taken, and a run of a product takes from its second side
what its firings pay. A purse at another place does not pay.
Two firings that name one purse need that purse twice: a purse present once
pays for one firing at a time.

A system funded twice has two purses. Pouring the second purse into the first
is a map of resources, and the system funded once with the summed price is the
system funded twice seen through it. A map of resources sends steps to steps.
The converse fails: the merged purse does not tell which purse held a token.
So paying is a monad graded by prices: the unit pays nothing, the
multiplication pours two purses together, and the laws are equalities of
systems.  Paying twice costs twice.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.ResourceInteraction

open Mettapedia.GSLT
open Mettapedia.GSLT.Causality.OccurrenceHistory (Occurrence OccurrencePath OccurrenceValuation)
open Mettapedia.GSLT.Causality.EventConcurrency (Concurrency Descends descends_iff_tiles)

universe uRes uImage uTok uRule uPurse uJoint uPlace uObs uVal

variable {R : Type uRes} {T : Type uTok}

/-! ## Bags over two kinds of resource -/

/-- A bag over two kinds of resource: a bag of the first kind beside a bag of
the second. It is the disjoint sum of the two bags. -/
def marking (left : Multiset R) (right : Multiset T) : Multiset (R ⊕ T) :=
  left.disjSum right

/-- The resources of the first kind in a bag. -/
def leftPart (M : Multiset (R ⊕ T)) : Multiset R :=
  M.filterMap Sum.getLeft?

/-- The resources of the second kind in a bag. -/
def rightPart (M : Multiset (R ⊕ T)) : Multiset T :=
  M.filterMap Sum.getRight?

theorem marking_cons_left (a : R) (A : Multiset R) (B : Multiset T) :
    marking (a ::ₘ A) B = Sum.inl a ::ₘ marking A B := by
  unfold marking Multiset.disjSum
  rw [Multiset.map_cons, Multiset.cons_add]

theorem marking_cons_right (b : T) (A : Multiset R) (B : Multiset T) :
    marking A (b ::ₘ B) = Sum.inr b ::ₘ marking A B := by
  unfold marking Multiset.disjSum
  rw [Multiset.map_cons, Multiset.add_cons]

theorem leftPart_cons_inl (a : R) (M : Multiset (R ⊕ T)) :
    leftPart (Sum.inl a ::ₘ M) = a ::ₘ leftPart M :=
  Multiset.filterMap_cons_some Sum.getLeft? (Sum.inl a) M rfl

theorem leftPart_cons_inr (b : T) (M : Multiset (R ⊕ T)) :
    leftPart (Sum.inr b ::ₘ M) = leftPart M :=
  Multiset.filterMap_cons_none (f := Sum.getLeft?) (Sum.inr b) M rfl

theorem rightPart_cons_inl (a : R) (M : Multiset (R ⊕ T)) :
    rightPart (Sum.inl a ::ₘ M) = rightPart M :=
  Multiset.filterMap_cons_none (f := Sum.getRight?) (Sum.inl a) M rfl

theorem rightPart_cons_inr (b : T) (M : Multiset (R ⊕ T)) :
    rightPart (Sum.inr b ::ₘ M) = b ::ₘ rightPart M :=
  Multiset.filterMap_cons_some Sum.getRight? (Sum.inr b) M rfl

theorem rightPart_add (M N : Multiset (R ⊕ T)) : rightPart (M + N) = rightPart M + rightPart N :=
  Multiset.filterMap_add _ _ _

theorem leftPart_marking (A : Multiset R) (B : Multiset T) : leftPart (marking A B) = A := by
  induction B using Multiset.induction_on with
  | empty =>
      induction A using Multiset.induction_on with
      | empty => rfl
      | cons a A ih => rw [marking_cons_left, leftPart_cons_inl, ih]
  | cons b B ih => rw [marking_cons_right, leftPart_cons_inr, ih]

theorem rightPart_marking (A : Multiset R) (B : Multiset T) : rightPart (marking A B) = B := by
  induction A using Multiset.induction_on with
  | empty =>
      induction B using Multiset.induction_on with
      | empty => rfl
      | cons b B ih => rw [marking_cons_right, rightPart_cons_inr, ih]
  | cons a A ih => rw [marking_cons_left, rightPart_cons_inl, ih]

/-- **Every bag over two kinds of resource is a marking**, of its two parts. -/
theorem marking_leftPart_rightPart (M : Multiset (R ⊕ T)) :
    marking (leftPart M) (rightPart M) = M := by
  induction M using Multiset.induction_on with
  | empty => rfl
  | cons x M ih =>
      cases x with
      | inl a => rw [leftPart_cons_inl, rightPart_cons_inl, marking_cons_left, ih]
      | inr b => rw [leftPart_cons_inr, rightPart_cons_inr, marking_cons_right, ih]

theorem exists_marking (M : Multiset (R ⊕ T)) : ∃ A B, M = marking A B :=
  ⟨leftPart M, rightPart M, (marking_leftPart_rightPart M).symm⟩

/-- A bag over two kinds of resource, as the pair of its two parts. -/
def parts : Multiset (R ⊕ T) ≃ Multiset R × Multiset T where
  toFun M := (leftPart M, rightPart M)
  invFun pair := marking pair.1 pair.2
  left_inv := marking_leftPart_rightPart
  right_inv pair := Prod.ext (leftPart_marking pair.1 pair.2) (rightPart_marking pair.1 pair.2)

/-- Equal markings have equal parts. -/
theorem marking_injective :
    Function.Injective2 (marking : Multiset R → Multiset T → Multiset (R ⊕ T)) := by
  intro A A' B B' equal
  have left := congrArg leftPart equal
  have right := congrArg rightPart equal
  rw [leftPart_marking, leftPart_marking] at left
  rw [rightPart_marking, rightPart_marking] at right
  exact ⟨left, right⟩

theorem marking_le_iff (A A' : Multiset R) (B B' : Multiset T) :
    marking A B ≤ marking A' B' ↔ A ≤ A' ∧ B ≤ B' := by
  constructor
  · intro le
    have left : leftPart (marking A B) ≤ leftPart (marking A' B') :=
      Multiset.filterMap_le_filterMap _ le
    have right : rightPart (marking A B) ≤ rightPart (marking A' B') :=
      Multiset.filterMap_le_filterMap _ le
    rw [leftPart_marking, leftPart_marking] at left
    rw [rightPart_marking, rightPart_marking] at right
    exact ⟨left, right⟩
  · rintro ⟨left, right⟩
    exact Multiset.disjSum_mono left right

theorem marking_add (A A' : Multiset R) (B B' : Multiset T) :
    marking A B + marking A' B' = marking (A + A') (B + B') := by
  unfold marking Multiset.disjSum
  rw [Multiset.map_add, Multiset.map_add, add_add_add_comm]

theorem count_inl [DecidableEq R] [DecidableEq T] (a : R) (A : Multiset R) (B : Multiset T) :
    (marking A B).count (Sum.inl a) = A.count a := by
  have none : (B.map (Sum.inr : T → R ⊕ T)).count (Sum.inl a) = 0 :=
    Multiset.count_eq_zero.mpr (by simp)
  unfold marking Multiset.disjSum
  rw [Multiset.count_add, Multiset.count_map_eq_count' _ _ Sum.inl_injective, none, add_zero]

theorem count_inr [DecidableEq R] [DecidableEq T] (b : T) (A : Multiset R) (B : Multiset T) :
    (marking A B).count (Sum.inr b) = B.count b := by
  have none : (A.map (Sum.inl : R → R ⊕ T)).count (Sum.inr b) = 0 :=
    Multiset.count_eq_zero.mpr (by simp)
  unfold marking Multiset.disjSum
  rw [Multiset.count_add, Multiset.count_map_eq_count' _ _ Sum.inr_injective, none, zero_add]

theorem marking_sub [DecidableEq R] [DecidableEq T] (A A' : Multiset R) (B B' : Multiset T) :
    marking A B - marking A' B' = marking (A - A') (B - B') := by
  ext entry
  cases entry with
  | inl a => rw [Multiset.count_sub, count_inl, count_inl, count_inl, Multiset.count_sub]
  | inr b => rw [Multiset.count_sub, count_inr, count_inr, count_inr, Multiset.count_sub]

/-- A bag over two kinds of resource, seen through a map of each kind. -/
theorem map_elim_marking {R' : Type uImage} (f : R → R') (g : T → R') (A : Multiset R)
    (B : Multiset T) : (marking A B).map (Sum.elim f g) = A.map f + B.map g :=
  Multiset.map_disjSum _

/-! ## Bags: the two sides of a predicate, and injective maps -/

section Sides

variable (kind : R → Prop) [DecidablePred kind]

/-- A bag of resources outside `kind` beside a bag of resources in it fits in a
bag exactly when each fits on its own side. -/
theorem add_le_iff_filter {a b : Multiset R} (outside : ∀ r ∈ a, ¬ kind r)
    (inside : ∀ r ∈ b, kind r) (M : Multiset R) :
    a + b ≤ M ↔ a ≤ M.filter (fun r => ¬ kind r) ∧ b ≤ M.filter kind := by
  constructor
  · intro fits
    exact ⟨Multiset.le_filter.mpr ⟨le_trans (Multiset.le_add_right _ _) fits, outside⟩,
      Multiset.le_filter.mpr ⟨le_trans (Multiset.le_add_left _ _) fits, inside⟩⟩
  · rintro ⟨left, right⟩
    calc a + b ≤ M.filter (fun r => ¬ kind r) + M.filter kind := add_le_add left right
      _ = M := by rw [add_comm]; exact Multiset.filter_add_not kind M

/-- Taking such a pair of bags from a bag takes each from its own side. -/
theorem sub_add_eq_filter [DecidableEq R] {a b : Multiset R} (outside : ∀ r ∈ a, ¬ kind r)
    (inside : ∀ r ∈ b, kind r) (M : Multiset R) :
    M - (a + b) = (M.filter (fun r => ¬ kind r) - a) + (M.filter kind - b) := by
  have aOut : a.filter (fun r => ¬ kind r) = a := Multiset.filter_eq_self.mpr outside
  have aIn : a.filter kind = 0 := Multiset.filter_eq_nil.mpr outside
  have bIn : b.filter kind = b := Multiset.filter_eq_self.mpr inside
  have bOut : b.filter (fun r => ¬ kind r) = 0 :=
    Multiset.filter_eq_nil.mpr fun r member => not_not_intro (inside r member)
  conv_lhs => rw [← Multiset.filter_add_not kind (M - (a + b))]
  rw [Multiset.filter_sub, Multiset.filter_sub, Multiset.filter_add, Multiset.filter_add,
    aOut, aIn, bIn, bOut, zero_add, add_zero, add_comm]

/-- A property of the members of three bags holds of the members of their sum. -/
private theorem forall_mem_add₃ {p : R → Prop} {a c e : Multiset R} (inA : ∀ r ∈ a, p r)
    (inC : ∀ r ∈ c, p r) (inE : ∀ r ∈ e, p r) : ∀ r ∈ a + c + e, p r := by
  intro r member
  rcases Multiset.mem_add.mp member with member | member
  · rcases Multiset.mem_add.mp member with member | member
    exacts [inA r member, inC r member]
  · exact inE r member

end Sides

/-- Subtraction of bags commutes with an injective map. -/
theorem map_sub_of_injective {R' : Type uImage} [DecidableEq R] [DecidableEq R'] {f : R → R'}
    (injective : Function.Injective f) (M c : Multiset R) :
    (M - c).map f = M.map f - c.map f :=
  Quotient.inductionOn₂ M c fun _ _ => congrArg Multiset.ofList (List.map_diff injective)

/-! ## Systems with the same sites and instances -/

/-- Systems with the same sites and instances are equal when their instances
consume, read and produce the same bags. -/
theorem System.mk_congr {Site : Type uRule} {Instance : Site → Type uRule}
    {consume consume' read read' produce produce' :
      ∀ {site : Site}, Instance site → Multiset R}
    (consumes : ∀ {site : Site} (i : Instance site), consume i = consume' i)
    (reads : ∀ {site : Site} (i : Instance site), read i = read' i)
    (produces : ∀ {site : Site} (i : Instance site), produce i = produce' i) :
    (System.mk Site Instance consume read produce : System.{uRes, uRule} R) =
      System.mk Site Instance consume' read' produce' := by
  have sameConsume : @consume = @consume' := funext fun _ => funext fun i => consumes i
  have sameRead : @read = @read' := funext fun _ => funext fun i => reads i
  have sameProduce : @produce = @produce' := funext fun _ => funext fun i => produces i
  subst sameConsume sameRead sameProduce
  rfl

namespace System

/-! ## A system seen through a map of resources -/

section Map

variable {R' : Type uImage} (S : System.{uRes, uRule} R) (f : R → R')

/-- A system seen through a map of resources: the same sites and instances,
with every bag mapped. -/
def map : System.{uImage, uRule} R' where
  Site := S.Site
  Instance := S.Instance
  consume := fun i => (S.consume i).map f
  read := fun i => (S.read i).map f
  produce := fun i => (S.produce i).map f

/-- Seen through the identity, a system is itself. -/
theorem map_id : S.map id = S := by
  cases S
  exact System.mk_congr (fun _ => Multiset.map_id _) (fun _ => Multiset.map_id _)
    (fun _ => Multiset.map_id _)

/-- An enabled instance stays enabled on the mapped bag, for every map. -/
theorem map_enables (M : Multiset R) {site : S.Site} (i : S.Instance site)
    (enabled : S.Enables M i) : (S.map f).Enables (M.map f) (site := site) i := by
  change (S.consume i).map f + (S.read i).map f ≤ M.map f
  rw [← Multiset.map_add]
  exact Multiset.map_le_map enabled

/-- Concurrent instances stay concurrent on the mapped bag, for every map. -/
theorem map_concurrent (M : Multiset R) {site₁ site₂ : S.Site} (i : S.Instance site₁)
    (j : S.Instance site₂) (concurrent : S.Concurrent M i j) :
    (S.map f).Concurrent (M.map f) (site₁ := site₁) (site₂ := site₂) i j := by
  change (S.consume i).map f + (S.consume j).map f + (S.read i).map f ≤ M.map f ∧
    (S.consume i).map f + (S.consume j).map f + (S.read j).map f ≤ M.map f
  simp only [← Multiset.map_add]
  exact ⟨Multiset.map_le_map concurrent.1, Multiset.map_le_map concurrent.2⟩

/-- Firing an instance whose consumption is present commutes with mapping the
bag, for every map. -/
theorem map_fire_of_le [DecidableEq R] [DecidableEq R'] (M : Multiset R) {site : S.Site}
    (i : S.Instance site) (present : S.consume i ≤ M) :
    (S.map f).fire (M.map f) (site := site) i = (S.fire M i).map f := by
  change M.map f - (S.consume i).map f + (S.produce i).map f =
    (M - S.consume i + S.produce i).map f
  rw [Multiset.map_add]
  congr 1
  conv_lhs => rw [← tsub_add_cancel_of_le present, Multiset.map_add]
  exact add_tsub_cancel_right _ _

/-- **Mapping the resources sends steps to steps**, for every map. -/
theorem map_rewrites [DecidableEq R] [DecidableEq R'] {M N : Multiset R}
    (step : S.theory.rewrites M N) : (S.map f).theory.rewrites (M.map f) (N.map f) := by
  obtain ⟨site, i, enabled, rfl⟩ := step
  exact ⟨site, i, S.map_enables f M i enabled,
    (S.map_fire_of_le f M i (le_trans (Multiset.le_add_right _ _) enabled)).symm⟩

variable {f}

/-- Along an injective map, an instance is enabled on the mapped bag exactly
when it is enabled. -/
theorem map_enables_iff (injective : Function.Injective f) (M : Multiset R) {site : S.Site}
    (i : S.Instance site) : (S.map f).Enables (M.map f) (site := site) i ↔ S.Enables M i := by
  change (S.consume i).map f + (S.read i).map f ≤ M.map f ↔ _
  rw [← Multiset.map_add, Multiset.map_le_map_iff injective]
  rfl

/-- Along an injective map, instances are concurrent on the mapped bag exactly
when they are concurrent. -/
theorem map_concurrent_iff (injective : Function.Injective f) (M : Multiset R)
    {site₁ site₂ : S.Site} (i : S.Instance site₁) (j : S.Instance site₂) :
    (S.map f).Concurrent (M.map f) (site₁ := site₁) (site₂ := site₂) i j ↔
      S.Concurrent M i j := by
  change ((S.consume i).map f + (S.consume j).map f + (S.read i).map f ≤ M.map f ∧
    (S.consume i).map f + (S.consume j).map f + (S.read j).map f ≤ M.map f) ↔ _
  simp only [← Multiset.map_add, Multiset.map_le_map_iff injective]
  rfl

/-- Along an injective map, firing commutes with mapping the bag. -/
theorem map_fire [DecidableEq R] [DecidableEq R'] (injective : Function.Injective f)
    (M : Multiset R) {site : S.Site} (i : S.Instance site) :
    (S.map f).fire (M.map f) (site := site) i = (S.fire M i).map f := by
  change M.map f - (S.consume i).map f + (S.produce i).map f =
    (M - S.consume i + S.produce i).map f
  rw [Multiset.map_add, map_sub_of_injective injective]

/-- Along an injective map, the steps from a mapped bag are the mapped steps. -/
theorem map_rewrites_iff [DecidableEq R] [DecidableEq R'] (injective : Function.Injective f)
    (M : Multiset R) (N' : Multiset R') :
    (S.map f).theory.rewrites (M.map f) N' ↔ ∃ N, N' = N.map f ∧ S.theory.rewrites M N := by
  constructor
  · rintro ⟨site, i, enabled, rfl⟩
    exact ⟨S.fire M i, S.map_fire injective M i,
      site, i, (S.map_enables_iff injective M i).mp enabled, rfl⟩
  · rintro ⟨N, rfl, step⟩
    exact S.map_rewrites f step

end Map

/-! ## Two systems on the same resources, fired together -/

section Joint

variable (S : System.{uRes, uRule} R) (P : System.{uRes, uPurse} R)

/-- Two systems on the same resources fired together. A joint instance names
one instance of each, and consumes, reads and produces what the two do. -/
def joint (Site : Type uJoint) (Joint : Site → Type uJoint)
    (left : ∀ {site : Site}, Joint site → S.Entry)
    (right : ∀ {site : Site}, Joint site → P.Entry) : System.{uRes, uJoint} R where
  Site := Site
  Instance := Joint
  consume := fun j => S.consume (left j).2 + P.consume (right j).2
  read := fun j => S.read (left j).2 + P.read (right j).2
  produce := fun j => S.produce (left j).2 + P.produce (right j).2

variable {Site : Type uJoint} {Joint : Site → Type uJoint}
  (left : ∀ {site : Site}, Joint site → S.Entry)
  (right : ∀ {site : Site}, Joint site → P.Entry)

variable (kind : R → Prop) [DecidablePred kind]

/-- **A joint instance is enabled exactly when its two parts are, each on its
own side of the bag**, when the first part consumes and reads only resources
outside `kind` and the second only resources in it. -/
theorem joint_enables_iff (M : Multiset R) {site : Site} (j : Joint site)
    (leftUses : ∀ r ∈ S.consume (left j).2 + S.read (left j).2, ¬ kind r)
    (rightUses : ∀ r ∈ P.consume (right j).2 + P.read (right j).2, kind r) :
    (S.joint P Site Joint @left @right).Enables M j ↔
      S.Enables (M.filter fun r => ¬ kind r) (left j).2 ∧
        P.Enables (M.filter kind) (right j).2 := by
  change S.consume (left j).2 + P.consume (right j).2 +
    (S.read (left j).2 + P.read (right j).2) ≤ M ↔ _
  rw [add_add_add_comm]
  exact add_le_iff_filter kind leftUses rightUses M

/-- **Two joint instances are concurrent exactly when their parts are, each
pair on its own side of the bag**, under the same condition on both. -/
theorem joint_concurrent_iff (M : Multiset R) {site₁ site₂ : Site} (j : Joint site₁)
    (k : Joint site₂)
    (leftUses : ∀ r ∈ S.consume (left j).2 + S.read (left j).2, ¬ kind r)
    (rightUses : ∀ r ∈ P.consume (right j).2 + P.read (right j).2, kind r)
    (leftUses' : ∀ r ∈ S.consume (left k).2 + S.read (left k).2, ¬ kind r)
    (rightUses' : ∀ r ∈ P.consume (right k).2 + P.read (right k).2, kind r) :
    (S.joint P Site Joint @left @right).Concurrent M j k ↔
      S.Concurrent (M.filter fun r => ¬ kind r) (left j).2 (left k).2 ∧
        P.Concurrent (M.filter kind) (right j).2 (right k).2 := by
  simp only [Multiset.mem_add, or_imp, forall_and] at leftUses rightUses leftUses' rightUses'
  change (S.consume (left j).2 + P.consume (right j).2 +
        (S.consume (left k).2 + P.consume (right k).2) +
        (S.read (left j).2 + P.read (right j).2) ≤ M ∧
      S.consume (left j).2 + P.consume (right j).2 +
        (S.consume (left k).2 + P.consume (right k).2) +
        (S.read (left k).2 + P.read (right k).2) ≤ M) ↔ _
  rw [add_add_add_comm (S.consume (left j).2), add_add_add_comm _ _ (S.read (left j).2),
    add_add_add_comm _ _ (S.read (left k).2),
    add_le_iff_filter kind (forall_mem_add₃ leftUses.1 leftUses'.1 leftUses.2)
      (forall_mem_add₃ rightUses.1 rightUses'.1 rightUses.2) M,
    add_le_iff_filter kind (forall_mem_add₃ leftUses.1 leftUses'.1 leftUses'.2)
      (forall_mem_add₃ rightUses.1 rightUses'.1 rightUses'.2) M]
  exact and_and_and_comm

variable [DecidableEq R]

/-- **Firing a joint instance fires its two parts, each on its own side of the
bag**, when the first part consumes only resources outside `kind` and the
second only resources in it. Nothing is asked of what the parts produce: a part
may produce resources of either kind, and they are all in the result. -/
theorem joint_fire (M : Multiset R) {site : Site} (j : Joint site)
    (leftConsumes : ∀ r ∈ S.consume (left j).2, ¬ kind r)
    (rightConsumes : ∀ r ∈ P.consume (right j).2, kind r) :
    (S.joint P Site Joint @left @right).fire M j =
      S.fire (M.filter fun r => ¬ kind r) (left j).2 + P.fire (M.filter kind) (right j).2 := by
  change M - (S.consume (left j).2 + P.consume (right j).2) +
      (S.produce (left j).2 + P.produce (right j).2) =
    (M.filter (fun r => ¬ kind r) - S.consume (left j).2 + S.produce (left j).2) +
      (M.filter kind - P.consume (right j).2 + P.produce (right j).2)
  rw [sub_add_eq_filter kind leftConsumes rightConsumes M, add_add_add_comm]

/-- **The resources of `kind` after a joint firing**, when the second part
produces only such resources: the second part fired on those before, with
whatever of `kind` the first part produced. -/
theorem joint_fire_filter (M : Multiset R) {site : Site} (j : Joint site)
    (leftConsumes : ∀ r ∈ S.consume (left j).2, ¬ kind r)
    (rightConsumes : ∀ r ∈ P.consume (right j).2, kind r)
    (rightProduces : ∀ r ∈ P.produce (right j).2, kind r) :
    ((S.joint P Site Joint @left @right).fire M j).filter kind =
      P.fire (M.filter kind) (right j).2 + (S.produce (left j).2).filter kind := by
  rw [S.joint_fire P @left @right kind M j leftConsumes rightConsumes]
  change ((M.filter (fun r => ¬ kind r) - S.consume (left j).2 + S.produce (left j).2) +
      (M.filter kind - P.consume (right j).2 + P.produce (right j).2)).filter kind =
    (M.filter kind - P.consume (right j).2 + P.produce (right j).2) +
      (S.produce (left j).2).filter kind
  have none : (M.filter (fun r => ¬ kind r) - S.consume (left j).2).filter kind = 0 :=
    Multiset.filter_eq_nil.mpr fun r member =>
      (Multiset.mem_filter.mp (Multiset.mem_of_le (Multiset.sub_le_self _ _) member)).2
  have all : (M.filter kind - P.consume (right j).2).filter kind =
      M.filter kind - P.consume (right j).2 :=
    Multiset.filter_eq_self.mpr fun r member =>
      (Multiset.mem_filter.mp (Multiset.mem_of_le (Multiset.sub_le_self _ _) member)).2
  rw [Multiset.filter_add, Multiset.filter_add, Multiset.filter_add, none, all,
    Multiset.filter_eq_self.mpr rightProduces, zero_add, add_comm]

/-- **The resources outside `kind` after a joint firing**, when the second part
produces only resources of `kind`: those before less what the first part
consumed, with whatever outside `kind` the first part produced. -/
theorem joint_fire_filter_not (M : Multiset R) {site : Site} (j : Joint site)
    (leftConsumes : ∀ r ∈ S.consume (left j).2, ¬ kind r)
    (rightConsumes : ∀ r ∈ P.consume (right j).2, kind r)
    (rightProduces : ∀ r ∈ P.produce (right j).2, kind r) :
    ((S.joint P Site Joint @left @right).fire M j).filter (fun r => ¬ kind r) =
      M.filter (fun r => ¬ kind r) - S.consume (left j).2 +
        (S.produce (left j).2).filter fun r => ¬ kind r := by
  rw [S.joint_fire P @left @right kind M j leftConsumes rightConsumes]
  change ((M.filter (fun r => ¬ kind r) - S.consume (left j).2 + S.produce (left j).2) +
      (M.filter kind - P.consume (right j).2 + P.produce (right j).2)).filter
        (fun r => ¬ kind r) = _
  have all : (M.filter (fun r => ¬ kind r) - S.consume (left j).2).filter (fun r => ¬ kind r) =
      M.filter (fun r => ¬ kind r) - S.consume (left j).2 :=
    Multiset.filter_eq_self.mpr fun r member =>
      (Multiset.mem_filter.mp (Multiset.mem_of_le (Multiset.sub_le_self _ _) member)).2
  have none : (M.filter kind - P.consume (right j).2).filter (fun r => ¬ kind r) = 0 :=
    Multiset.filter_eq_nil.mpr fun r member => not_not_intro
      (Multiset.mem_filter.mp (Multiset.mem_of_le (Multiset.sub_le_self _ _) member)).2
  have none' : (P.produce (right j).2).filter (fun r => ¬ kind r) = 0 :=
    Multiset.filter_eq_nil.mpr fun r member => not_not_intro (rightProduces r member)
  rw [Multiset.filter_add, Multiset.filter_add, Multiset.filter_add, all, none, none',
    add_zero, add_zero]

/-- **The result splits when the first part produces nothing of `kind`.** Then
each side of the bag after a joint firing is the firing of one part on that
side before. Without this condition both equations fail: what the first part
produces of `kind` is on the second side, as `joint_fire_filter` and
`joint_fire_filter_not` say. -/
theorem joint_fire_split (M : Multiset R) {site : Site} (j : Joint site)
    (leftConsumes : ∀ r ∈ S.consume (left j).2, ¬ kind r)
    (rightConsumes : ∀ r ∈ P.consume (right j).2, kind r)
    (leftProduces : ∀ r ∈ S.produce (left j).2, ¬ kind r)
    (rightProduces : ∀ r ∈ P.produce (right j).2, kind r) :
    ((S.joint P Site Joint @left @right).fire M j).filter (fun r => ¬ kind r) =
        S.fire (M.filter fun r => ¬ kind r) (left j).2 ∧
      ((S.joint P Site Joint @left @right).fire M j).filter kind =
        P.fire (M.filter kind) (right j).2 := by
  constructor
  · rw [S.joint_fire_filter_not P @left @right kind M j leftConsumes rightConsumes
      rightProduces, Multiset.filter_eq_self.mpr leftProduces]
    rfl
  · rw [S.joint_fire_filter P @left @right kind M j leftConsumes rightConsumes rightProduces,
      Multiset.filter_eq_nil.mpr leftProduces, add_zero]

end Joint

/-! ## The product of two systems -/

section Product

variable (S : System.{uRes, uRule} R) (P : System.{uTok, uPurse} T)

/-- The product of two systems: each seen in the sum of the two carriers, and
the two fired together there. A joint instance names one instance of each. -/
def product (Site : Type uJoint) (Joint : Site → Type uJoint)
    (left : ∀ {site : Site}, Joint site → S.Entry)
    (right : ∀ {site : Site}, Joint site → P.Entry) :
    System.{max uRes uTok, uJoint} (R ⊕ T) :=
  (S.map Sum.inl).joint (P.map Sum.inr) Site Joint left right

variable {Site : Type uJoint} {Joint : Site → Type uJoint}
  (left : ∀ {site : Site}, Joint site → S.Entry)
  (right : ∀ {site : Site}, Joint site → P.Entry)

/-- **The product is its two factors, each seen in the sum of the carriers,
fired together.** It is the case of firing together in which the two parts use
resources of different types. -/
theorem product_eq_joint :
    S.product P Site Joint @left @right =
      (S.map Sum.inl).joint (P.map Sum.inr) Site Joint @left @right :=
  rfl

/-- **A product seen on one carrier is its two factors, each seen there, fired
together.** -/
theorem map_product {R' : Type uImage} (f : R → R') (g : T → R') :
    (S.product P Site Joint @left @right).map (Sum.elim f g) =
      (S.map f).joint (P.map g) Site Joint @left @right :=
  System.mk_congr (fun _ => map_elim_marking f g _ _) (fun _ => map_elim_marking f g _ _)
    (fun _ => map_elim_marking f g _ _)

/-- A joint instance is enabled exactly when its two parts are. -/
theorem product_enables_iff (A : Multiset R) (B : Multiset T) {site : Site} (j : Joint site) :
    (S.product P Site Joint @left @right).Enables (marking A B) j ↔
      S.Enables A (left j).2 ∧ P.Enables B (right j).2 := by
  change marking (S.consume (left j).2) (P.consume (right j).2) +
    marking (S.read (left j).2) (P.read (right j).2) ≤ marking A B ↔ _
  rw [marking_add, marking_le_iff]
  rfl

/-- Firing a joint instance fires its two parts. -/
theorem product_fire [DecidableEq R] [DecidableEq T] (A : Multiset R) (B : Multiset T)
    {site : Site} (j : Joint site) :
    (S.product P Site Joint @left @right).fire (marking A B) j =
      marking (S.fire A (left j).2) (P.fire B (right j).2) := by
  change marking A B - marking (S.consume (left j).2) (P.consume (right j).2) +
    marking (S.produce (left j).2) (P.produce (right j).2) = _
  rw [marking_sub, marking_add]
  rfl

/-- Two joint instances are concurrent exactly when their parts are. -/
theorem product_concurrent_iff (A : Multiset R) (B : Multiset T) {site₁ site₂ : Site}
    (j : Joint site₁) (k : Joint site₂) :
    (S.product P Site Joint @left @right).Concurrent (marking A B) j k ↔
      S.Concurrent A (left j).2 (left k).2 ∧ P.Concurrent B (right j).2 (right k).2 := by
  change (marking _ _ + marking _ _ + marking _ _ ≤ marking A B ∧
    marking _ _ + marking _ _ + marking _ _ ≤ marking A B) ↔ _
  rw [marking_add, marking_add, marking_add, marking_le_iff, marking_le_iff]
  exact and_and_and_comm

/-- A joint instance whose two parts are enabled is a step of the product. -/
theorem product_rewrites_of_enables [DecidableEq R] [DecidableEq T] (A : Multiset R)
    (B : Multiset T) {site : Site} (j : Joint site) (leftEnabled : S.Enables A (left j).2)
    (rightEnabled : P.Enables B (right j).2) :
    (S.product P Site Joint @left @right).theory.rewrites (marking A B)
      (marking (S.fire A (left j).2) (P.fire B (right j).2)) :=
  ⟨site, j, (S.product_enables_iff P @left @right A B j).mpr ⟨leftEnabled, rightEnabled⟩,
    (S.product_fire P @left @right A B j).symm⟩

/-- The steps of the product are the joint instances whose two parts are enabled. -/
theorem product_rewrites_iff [DecidableEq R] [DecidableEq T] (A : Multiset R)
    (B : Multiset T) (N : Multiset (R ⊕ T)) :
    (S.product P Site Joint @left @right).theory.rewrites (marking A B) N ↔
      ∃ site, ∃ j : Joint site, S.Enables A (left j).2 ∧ P.Enables B (right j).2 ∧
        N = marking (S.fire A (left j).2) (P.fire B (right j).2) := by
  constructor
  · rintro ⟨site, j, enabled, rfl⟩
    obtain ⟨leftEnabled, rightEnabled⟩ :=
      (S.product_enables_iff P @left @right A B j).mp enabled
    exact ⟨site, j, leftEnabled, rightEnabled, S.product_fire P @left @right A B j⟩
  · rintro ⟨site, j, leftEnabled, rightEnabled, rfl⟩
    exact S.product_rewrites_of_enables P @left @right A B j leftEnabled rightEnabled

/-- **Forgetting either factor sends steps to steps.** A step of the product is a
step of each system on its own part of the bag. -/
theorem product_rewrites [DecidableEq R] [DecidableEq T] {A : Multiset R} {B : Multiset T}
    {N : Multiset (R ⊕ T)}
    (step : (S.product P Site Joint @left @right).theory.rewrites (marking A B) N) :
    ∃ A' B', N = marking A' B' ∧ S.theory.rewrites A A' ∧ P.theory.rewrites B B' := by
  obtain ⟨site, j, leftEnabled, rightEnabled, rfl⟩ :=
    (S.product_rewrites_iff P @left @right A B N).mp step
  exact ⟨_, _, rfl, ⟨_, _, leftEnabled, rfl⟩, ⟨_, _, rightEnabled, rfl⟩⟩

/-- Forgetting the second factor sends steps to steps, from any bag. -/
theorem product_rewrites_leftPart [DecidableEq R] [DecidableEq T] {M N : Multiset (R ⊕ T)}
    (step : (S.product P Site Joint @left @right).theory.rewrites M N) :
    S.theory.rewrites (leftPart M) (leftPart N) := by
  obtain ⟨A, B, rfl⟩ := exists_marking M
  obtain ⟨A', B', rfl, leftStep, -⟩ := S.product_rewrites P @left @right step
  rw [leftPart_marking, leftPart_marking]
  exact leftStep

/-- Forgetting the first factor sends steps to steps, from any bag. -/
theorem product_rewrites_rightPart [DecidableEq R] [DecidableEq T] {M N : Multiset (R ⊕ T)}
    (step : (S.product P Site Joint @left @right).theory.rewrites M N) :
    P.theory.rewrites (rightPart M) (rightPart N) := by
  obtain ⟨A, B, rfl⟩ := exists_marking M
  obtain ⟨A', B', rfl, -, rightStep⟩ := S.product_rewrites P @left @right step
  rw [rightPart_marking, rightPart_marking]
  exact rightStep

/-- **A run of the product is a run of each system on its own part of the
bag**, through the instances the joint instances name. -/
theorem product_fires_iff [DecidableEq R] [DecidableEq T] :
    ∀ (run : List (S.product P Site Joint @left @right).Entry) (A : Multiset R)
      (B : Multiset T) (N : Multiset (R ⊕ T)),
      (S.product P Site Joint @left @right).Fires run (marking A B) N ↔
        ∃ A' B', N = marking A' B' ∧ S.Fires (run.map fun entry => left entry.2) A A' ∧
          P.Fires (run.map fun entry => right entry.2) B B'
  | [], A, B, N => by
      constructor
      · rintro rfl
        exact ⟨A, B, rfl, rfl, rfl⟩
      · rintro ⟨A', B', rfl, rfl, rfl⟩
        rfl
  | entry :: rest, A, B, N => by
      have fired := S.product_fire P @left @right A B entry.2
      constructor
      · rintro ⟨enabled, restFires⟩
        obtain ⟨leftEnabled, rightEnabled⟩ :=
          (S.product_enables_iff P @left @right A B entry.2).mp enabled
        obtain ⟨A', B', rfl, leftFires, rightFires⟩ :=
          (product_fires_iff rest _ _ N).mp (fired ▸ restFires)
        exact ⟨A', B', rfl, ⟨leftEnabled, leftFires⟩, ⟨rightEnabled, rightFires⟩⟩
      · rintro ⟨A', B', rfl, ⟨leftEnabled, leftFires⟩, ⟨rightEnabled, rightFires⟩⟩
        exact ⟨(S.product_enables_iff P @left @right A B entry.2).mpr
            ⟨leftEnabled, rightEnabled⟩,
          fired ▸ (product_fires_iff rest _ _ _).mpr ⟨A', B', rfl, leftFires, rightFires⟩⟩

end Product

/-! ## The product and firing together on one carrier -/

section JointProduct

variable (S : System.{uRes, uRule} R) (P : System.{uRes, uPurse} R)
  {Site : Type uJoint} {Joint : Site → Type uJoint}
  (left : ∀ {site : Site}, Joint site → S.Entry)
  (right : ∀ {site : Site}, Joint site → P.Entry)

/-- **Firing together on one carrier is the product, with the two kinds of
resource no longer told apart.** -/
theorem joint_eq_map_product :
    S.joint P Site Joint @left @right =
      (S.product P Site Joint @left @right).map (Sum.elim id id) :=
  have collapse : ∀ A B : Multiset R, A + B = (marking A B).map (Sum.elim id id) := fun A B => by
    rw [map_elim_marking, Multiset.map_id, Multiset.map_id]
  System.mk_congr (fun _ => collapse _ _) (fun _ => collapse _ _) (fun _ => collapse _ _)

/-- What the product enables on a pair of bags, firing together enables on
their sum. -/
theorem joint_enables_of_product (A B : Multiset R) {site : Site} (j : Joint site)
    (enabled : (S.product P Site Joint @left @right).Enables (marking A B) j) :
    (S.joint P Site Joint @left @right).Enables (A + B) j := by
  obtain ⟨leftEnabled, rightEnabled⟩ := (S.product_enables_iff P @left @right A B j).mp enabled
  change S.consume (left j).2 + P.consume (right j).2 +
    (S.read (left j).2 + P.read (right j).2) ≤ A + B
  rw [add_add_add_comm]
  exact add_le_add leftEnabled rightEnabled

variable (kind : R → Prop) [DecidablePred kind]

/-- Firing together at a bag is the product at the bag split into its two
sides, for enabling. -/
theorem joint_enables_iff_product (M : Multiset R) {site : Site} (j : Joint site)
    (leftUses : ∀ r ∈ S.consume (left j).2 + S.read (left j).2, ¬ kind r)
    (rightUses : ∀ r ∈ P.consume (right j).2 + P.read (right j).2, kind r) :
    (S.joint P Site Joint @left @right).Enables M j ↔
      (S.product P Site Joint @left @right).Enables
        (marking (M.filter fun r => ¬ kind r) (M.filter kind)) j :=
  (S.joint_enables_iff P @left @right kind M j leftUses rightUses).trans
    (S.product_enables_iff P @left @right _ _ j).symm

/-- Firing together at a bag is the product at the bag split into its two
sides, for concurrency. -/
theorem joint_concurrent_iff_product (M : Multiset R) {site₁ site₂ : Site} (j : Joint site₁)
    (k : Joint site₂)
    (leftUses : ∀ r ∈ S.consume (left j).2 + S.read (left j).2, ¬ kind r)
    (rightUses : ∀ r ∈ P.consume (right j).2 + P.read (right j).2, kind r)
    (leftUses' : ∀ r ∈ S.consume (left k).2 + S.read (left k).2, ¬ kind r)
    (rightUses' : ∀ r ∈ P.consume (right k).2 + P.read (right k).2, kind r) :
    (S.joint P Site Joint @left @right).Concurrent M j k ↔
      (S.product P Site Joint @left @right).Concurrent
        (marking (M.filter fun r => ¬ kind r) (M.filter kind)) j k :=
  (S.joint_concurrent_iff P @left @right kind M j k leftUses rightUses leftUses'
      rightUses').trans
    (S.product_concurrent_iff P @left @right _ _ j k).symm

/-- When the result splits, firing together and then splitting the bag is
splitting the bag and then firing the product. -/
theorem joint_fire_split_product [DecidableEq R] (M : Multiset R) {site : Site} (j : Joint site)
    (leftConsumes : ∀ r ∈ S.consume (left j).2, ¬ kind r)
    (rightConsumes : ∀ r ∈ P.consume (right j).2, kind r)
    (leftProduces : ∀ r ∈ S.produce (left j).2, ¬ kind r)
    (rightProduces : ∀ r ∈ P.produce (right j).2, kind r) :
    marking (((S.joint P Site Joint @left @right).fire M j).filter fun r => ¬ kind r)
        (((S.joint P Site Joint @left @right).fire M j).filter kind) =
      (S.product P Site Joint @left @right).fire
        (marking (M.filter fun r => ¬ kind r) (M.filter kind)) j := by
  obtain ⟨outside, inside⟩ := S.joint_fire_split P @left @right kind M j leftConsumes
    rightConsumes leftProduces rightProduces
  rw [outside, inside, S.product_fire P @left @right]

end JointProduct

/-! ## Frames, and what a run changes -/

section Frame

variable (S : System.{uRes, uRule} R) [DecidableEq R]

/-- **Enabled and fired, by a frame.** An instance that reads nothing is enabled
at a bag and fires to another exactly when the first bag is its consumption
beside some other resources and the second is its production beside the same. -/
theorem enables_fire_iff_frame (M N : Multiset R) {site : S.Site} (i : S.Instance site)
    (reads : S.read i = 0) :
    S.Enables M i ∧ N = S.fire M i ↔
      ∃ frame, M = frame + S.consume i ∧ N = frame + S.produce i := by
  unfold Enables fire
  rw [reads, add_zero]
  constructor
  · rintro ⟨present, rfl⟩
    exact ⟨M - S.consume i, (tsub_add_cancel_of_le present).symm, rfl⟩
  · rintro ⟨frame, rfl, rfl⟩
    exact ⟨Multiset.le_add_left _ _, by rw [add_tsub_cancel_right]⟩

/-- A run with one firing: an enabled instance, fired. -/
def firing (M : Multiset R) {site : S.Site} (i : S.Instance site) (enabled : S.Enables M i) :
    OccurrencePath S.presentation M (S.fire M i) :=
  .cons ⟨site, ⟨i, enabled, rfl⟩⟩ (.refl _)

variable {A : Type uObs} [AddCommMonoid A]

/-- Every firing of a run graded by the instance it fires. -/
def instanceValuation (f : ∀ {site : S.Site}, S.Instance site → A) :
    OccurrenceValuation S.presentation A where
  grade o := f o.evidence.val

/-- Every firing of a run graded by what its instance consumes. -/
abbrev consumedValuation : OccurrenceValuation S.presentation (Multiset R) :=
  S.instanceValuation S.consume

/-- Every firing of a run graded by what its instance produces. -/
abbrev producedValuation : OccurrenceValuation S.presentation (Multiset R) :=
  S.instanceValuation S.produce

theorem instanceValuation_firing (f : ∀ {site : S.Site}, S.Instance site → A)
    {M : Multiset R} {site : S.Site} (i : S.Instance site) (enabled : S.Enables M i) :
    (S.instanceValuation f).onPath (S.firing M i enabled) = f i :=
  add_zero (f i)

/-- Grades equal on every instance are equal along every run. -/
theorem instanceValuation_congr {f g : ∀ {site : S.Site}, S.Instance site → A}
    (same : ∀ {site : S.Site} (i : S.Instance site), f i = g i) :
    ∀ {M N : Multiset R} (p : OccurrencePath S.presentation M N),
      (S.instanceValuation f).onPath p = (S.instanceValuation g).onPath p
  | _, _, .refl _ => rfl
  | _, _, .cons o rest => by
      change f o.evidence.val + _ = g o.evidence.val + _
      exact congrArg₂ (· + ·) (same o.evidence.val) (instanceValuation_congr same rest)

/-- The grade of a sum along a run is the sum of the grades. -/
theorem instanceValuation_add (f g : ∀ {site : S.Site}, S.Instance site → A) :
    ∀ {M N : Multiset R} (p : OccurrencePath S.presentation M N),
      (S.instanceValuation fun i => f i + g i).onPath p =
        (S.instanceValuation f).onPath p + (S.instanceValuation g).onPath p
  | _, _, .refl _ => (add_zero 0).symm
  | _, _, .cons o rest => by
      change f o.evidence.val + g o.evidence.val + _ =
        (f o.evidence.val + _) + (g o.evidence.val + _)
      exact (congrArg (f o.evidence.val + g o.evidence.val + ·)
        (instanceValuation_add f g rest)).trans (add_add_add_comm _ _ _ _)

/-- A grade that is zero on every instance is zero along every run. -/
theorem instanceValuation_zero :
    ∀ {M N : Multiset R} (p : OccurrencePath S.presentation M N),
      (S.instanceValuation fun _ => (0 : A)).onPath p = 0
  | _, _, .refl _ => rfl
  | _, _, .cons _ rest => by
      change 0 + _ = 0
      rw [instanceValuation_zero rest, add_zero]

/-- An additive observation of the grades along a run is the grade of the
observed instances. -/
theorem instanceValuation_map {B : Type uVal} [AddCommMonoid B] (obs : A → B)
    (zero : obs 0 = 0) (additive : ∀ a b, obs (a + b) = obs a + obs b)
    (f : ∀ {site : S.Site}, S.Instance site → A) :
    ∀ {M N : Multiset R} (p : OccurrencePath S.presentation M N),
      obs ((S.instanceValuation f).onPath p) =
        (S.instanceValuation fun i => obs (f i)).onPath p
  | _, _, .refl _ => zero
  | _, _, .cons o rest => by
      change obs (f o.evidence.val + _) = obs (f o.evidence.val) + _
      exact (additive _ _).trans
        (congrArg (obs (f o.evidence.val) + ·) (instanceValuation_map obs zero additive f rest))

/-- **A grade that vanishes where a property holds vanishes along every run from
it**, when every enabled firing keeps the property. -/
theorem instanceValuation_eq_zero (f : ∀ {site : S.Site}, S.Instance site → A)
    {Q : Multiset R → Prop}
    (kept : ∀ (M : Multiset R) {site : S.Site} (i : S.Instance site), Q M → S.Enables M i →
      Q (S.fire M i))
    (vanishes : ∀ (M : Multiset R) {site : S.Site} (i : S.Instance site), Q M →
      S.Enables M i → f i = 0) :
    ∀ {M N : Multiset R} (p : OccurrencePath S.presentation M N), Q M →
      (S.instanceValuation f).onPath p = 0
  | _, _, .refl _, _ => rfl
  | M, _, .cons o rest, holds => by
      obtain ⟨enabled, fired⟩ := o.evidence.property
      change f o.evidence.val + _ = 0
      exact (congrArg₂ (· + ·) (vanishes M o.evidence.val holds enabled)
        (instanceValuation_eq_zero f kept vanishes rest
          (fired ▸ kept M o.evidence.val holds enabled))).trans (add_zero 0)

/-- One firing in the balance of a run. -/
private theorem balance_cons {M c p Pr N Cr middle : Multiset R} (present : c ≤ M)
    (fired : middle = M - c + p) (tail : middle + Pr = N + Cr) : M + (p + Pr) = N + (c + Cr) := by
  subst fired
  calc M + (p + Pr) = (M - c + c) + (p + Pr) := by rw [tsub_add_cancel_of_le present]
    _ = (M - c + p) + Pr + c := by ac_rfl
    _ = N + (c + Cr) := by rw [tail]; abel

/-- **What a run changes.** The bag before a run, with all that its firings
produce, is the bag after it with all that they consume. -/
theorem balance : ∀ {M N : Multiset R} (p : OccurrencePath S.presentation M N),
    M + S.producedValuation.onPath p = N + S.consumedValuation.onPath p
  | _, _, .refl _ => rfl
  | _, _, .cons o rest =>
      balance_cons (le_trans (Multiset.le_add_right _ _) o.evidence.property.1)
        o.evidence.property.2 (balance rest)

variable {M N : Multiset R}

/-- **What a run changes, in an additive observation of bags.** -/
theorem balance_observed {B : Type uVal} [AddCommMonoid B] (obs : Multiset R → B)
    (zero : obs 0 = 0) (additive : ∀ M N, obs (M + N) = obs M + obs N)
    (p : OccurrencePath S.presentation M N) :
    obs M + (S.instanceValuation fun i => obs (S.produce i)).onPath p =
      obs N + (S.instanceValuation fun i => obs (S.consume i)).onPath p := by
  have observed := congrArg obs (S.balance p)
  rwa [additive, additive, S.instanceValuation_map obs zero additive,
    S.instanceValuation_map obs zero additive] at observed

/-- **What a run takes, in an additive observation of bags.** When every
instance consumes, as observed, what it produces with something more beside it,
the observation before a run is the observation after it with all that more. -/
theorem balance_taken {B : Type uVal} [AddCancelCommMonoid B] (obs : Multiset R → B)
    (zero : obs 0 = 0) (additive : ∀ M N, obs (M + N) = obs M + obs N)
    (taken : ∀ {site : S.Site}, S.Instance site → B)
    (splits : ∀ {site : S.Site} (i : S.Instance site),
      obs (S.consume i) = taken i + obs (S.produce i))
    (p : OccurrencePath S.presentation M N) :
    obs M = obs N + (S.instanceValuation taken).onPath p := by
  have balanced := S.balance_observed obs zero additive p
  rw [S.instanceValuation_congr splits p, S.instanceValuation_add, ← add_assoc] at balanced
  exact add_right_cancel balanced

/-- What one firing changes: the bag before, with what the instance produces,
is the bag after with what it consumes. -/
theorem fire_balance {site : S.Site} (i : S.Instance site) (enabled : S.Enables M i) :
    M + S.produce i = S.fire M i + S.consume i := by
  simpa only [instanceValuation_firing] using S.balance (S.firing M i enabled)

/-- The value of a valuation does not see a change of the name of the end of a
path. -/
private theorem onPath_cast (v : OccurrenceValuation S.presentation A) {s t t' : S.theory.Term}
    (same : t = t') (p : OccurrencePath S.presentation s t) :
    v.onPath (same ▸ p) = v.onPath p := by
  cases same
  rfl

/-- The value of a valuation on the second route of a pair of concurrent
firings: the second firing, then what remains of the first. -/
private theorem onPath_swapped (v : OccurrenceValuation S.presentation A) {M : S.theory.Term}
    (pair : S.concurrency.Pair M) :
    v.onPath (pair.swapped S.concurrency) =
      v.grade (Concurrency.occ pair.second) +
        (v.grade (Concurrency.occ (S.concurrency.residual (S.concurrency.symm pair.independent))) +
          0) := by
  unfold Concurrency.Pair.swapped
  rw [onPath_cast]
  rfl

/-- **Every grade of the instances fired is a property of the trace.** The two
routes of a pair of concurrent firings fire the same two instances, in the two
orders. -/
theorem instanceValuation_descends (f : ∀ {site : S.Site}, S.Instance site → A) :
    Descends S.concurrency.tiles (S.instanceValuation f) := by
  refine (descends_iff_tiles S.concurrency.tiles (S.instanceValuation f)).2
    fun {M} (pair : S.concurrency.Pair M) => ?_
  change (S.instanceValuation f).onPath (pair.route S.concurrency) =
    (S.instanceValuation f).onPath (pair.swapped S.concurrency)
  rw [onPath_swapped]
  change f (S.inst pair.first) + (f (S.inst pair.second) + 0) =
    f (S.inst pair.second) + (f (S.inst pair.first) + 0)
  rw [add_zero, add_zero, add_comm]

/-- What a run consumes is a property of its trace. -/
theorem consumedValuation_descends : Descends S.concurrency.tiles S.consumedValuation :=
  S.instanceValuation_descends S.consume

/-- What a run produces is a property of its trace. -/
theorem producedValuation_descends : Descends S.concurrency.tiles S.producedValuation :=
  S.instanceValuation_descends S.produce

end Frame

/-! ## Conservation is a property of the trace -/

section TraceAccounts

open Mettapedia.Effects
open Mettapedia.GSLT.Causality.TraceCostValuation

variable (S : System.{uRes, uRule} R) [DecidableEq R]

/-- What a run consumes, as an account of its trace. -/
def consumedTraceAccount :
    RunAccount (EventConcurrency.TraceCat S.concurrency.tiles) (Multiplicative (Multiset R)) :=
  traceAccount S.concurrency.tiles S.consumedValuation S.consumedValuation_descends

/-- What a run produces, as an account of its trace. -/
def producedTraceAccount :
    RunAccount (EventConcurrency.TraceCat S.concurrency.tiles) (Multiplicative (Multiset R)) :=
  traceAccount S.concurrency.tiles S.producedValuation S.producedValuation_descends

/-- **Conservation is a property of the trace.**  For every trace of runs from
`M` to `N`, the bag before with what the trace produces is the bag after with
what it consumes. -/
theorem balance_trace {M N : Multiset R}
    (trace : EventConcurrency.Trace S.concurrency.tiles M N) :
    M + Multiplicative.toAdd (S.producedTraceAccount.of (source := M) (target := N) trace) =
      N + Multiplicative.toAdd (S.consumedTraceAccount.of (source := M) (target := N) trace) := by
  induction trace using Quotient.inductionOn with
  | h path => exact S.balance path

end TraceAccounts

/-! ## The product and the synchronous product of the two theories -/

section Synchronous

variable [DecidableEq R] [DecidableEq T] (S : System.{uRes, uRule} R)
  (P : System.{uTok, uPurse} T) {Site : Type uJoint} {Joint : Site → Type uJoint}
  (left : ∀ {site : Site}, Joint site → S.Entry)
  (right : ∀ {site : Site}, Joint site → P.Entry)

/-- **A step of the product is a step of both theories together.** Splitting a
bag into its two parts sends the steps of the product to steps of the
synchronous product of the two theories, whatever the joint instances are. -/
theorem product_step_synchronous {M N : Multiset (R ⊕ T)}
    (step : (S.product P Site Joint @left @right).theory.Step M N) :
    (GSLT.synchronousProduct S.theory P.theory).Step (parts M) (parts N) :=
  ⟨S.product_rewrites_leftPart P @left @right step,
    S.product_rewrites_rightPart P @left @right step⟩

/-- **A step of both theories together is a step of the product when every pair
of instances is named by a joint instance.** -/
theorem synchronous_step_product
    (covers : ∀ (s : S.Entry) (p : P.Entry),
      ∃ site, ∃ j : Joint site, left j = s ∧ right j = p)
    {M N : Multiset (R ⊕ T)}
    (step : (GSLT.synchronousProduct S.theory P.theory).Step (parts M) (parts N)) :
    (S.product P Site Joint @left @right).theory.Step M N := by
  obtain ⟨⟨siteS, i, enabledS, firedS⟩, ⟨siteP, p, enabledP, firedP⟩⟩ := step
  obtain ⟨site, j, sameLeft, sameRight⟩ := covers ⟨siteS, i⟩ ⟨siteP, p⟩
  have leftStep : S.Enables (leftPart M) (left j).2 ∧
      leftPart N = S.fire (leftPart M) (left j).2 := by
    rw [sameLeft]
    exact ⟨enabledS, firedS⟩
  have rightStep : P.Enables (rightPart M) (right j).2 ∧
      rightPart N = P.fire (rightPart M) (right j).2 := by
    rw [sameRight]
    exact ⟨enabledP, firedP⟩
  have target :
      N = marking (S.fire (leftPart M) (left j).2) (P.fire (rightPart M) (right j).2) := by
    rw [← leftStep.2, ← rightStep.2, marking_leftPart_rightPart]
  have source := marking_leftPart_rightPart M
  rw [← source]
  exact (S.product_rewrites_iff P @left @right _ _ N).mpr
    ⟨site, j, leftStep.1, rightStep.1, target⟩

/-- **The product is the synchronous product of the two theories, when every
pair of instances is named by a joint instance**: the splitting of a bag into
its two parts then sends steps to steps and reflects them. -/
theorem product_step_iff_synchronous
    (covers : ∀ (s : S.Entry) (p : P.Entry),
      ∃ site, ∃ j : Joint site, left j = s ∧ right j = p)
    (M N : Multiset (R ⊕ T)) :
    (S.product P Site Joint @left @right).theory.Step M N ↔
      (GSLT.synchronousProduct S.theory P.theory).Step (parts M) (parts N) :=
  ⟨S.product_step_synchronous P @left @right, S.synchronous_step_product P @left @right covers⟩

/-- Bags are equal in the product exactly when their parts are equal in the
synchronous product, whatever the joint instances are. -/
theorem product_equiv_iff_synchronous (M N : Multiset (R ⊕ T)) :
    (S.product P Site Joint @left @right).theory.Equiv M N ↔
      (GSLT.synchronousProduct S.theory P.theory).Equiv (parts M) (parts N) := by
  change M = N ↔ leftPart M = leftPart N ∧ rightPart M = rightPart N
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨sameLeft, sameRight⟩
    rw [← marking_leftPart_rightPart M, ← marking_leftPart_rightPart N, sameLeft, sameRight]

/-- When every pair of instances is named by a joint instance, bags bisimilar
in the product have parts bisimilar in the synchronous product. -/
theorem product_bisimilar_synchronous
    (covers : ∀ (s : S.Entry) (p : P.Entry),
      ∃ site, ∃ j : Joint site, left j = s ∧ right j = p)
    {M N : Multiset (R ⊕ T)}
    (bisimilar : (S.product P Site Joint @left @right).theory.Bisimilar M N) :
    (GSLT.synchronousProduct S.theory P.theory).Bisimilar (parts M) (parts N) :=
  GSLT.bisimilar_map_of_step_iff (source := (S.product P Site Joint @left @right).theory)
    (target := GSLT.synchronousProduct S.theory P.theory) parts
    (S.product_step_iff_synchronous P @left @right covers) bisimilar

end Synchronous

end System

/-! ## An unordered purse -/

/-- An unordered purse: a bag of tokens. An instance is a bag, its price. Firing
it takes the price from the purse and gives nothing back. -/
def tokens (T : Type uTok) : System.{uTok, uTok} T where
  Site := PUnit
  Instance := fun _ => Multiset T
  consume := fun price => price
  read := fun _ => 0
  produce := fun _ => 0

/-- A price is enabled exactly when it is in the purse. -/
theorem tokens_enables_iff (B price : Multiset T) :
    (tokens T).Enables B (site := PUnit.unit) price ↔ price ≤ B := by
  change price + 0 ≤ B ↔ price ≤ B
  rw [add_zero]

/-- Firing takes the price from the purse. -/
theorem tokens_fire [DecidableEq T] (B price : Multiset T) :
    (tokens T).fire B (site := PUnit.unit) price = B - price :=
  add_zero (B - price)

/-- **Along a run, the purse loses exactly the prices of the run.** -/
theorem tokens_run_conserved [DecidableEq T] {B B' : Multiset T}
    (p : OccurrencePath (tokens T).presentation B B') :
    B = B' + (tokens T).consumedValuation.onPath p := by
  have nothing : (tokens T).producedValuation.onPath p = 0 := (tokens T).instanceValuation_zero p
  have balanced := (tokens T).balance p
  rwa [nothing, add_zero] at balanced

/-- **Tokens are conserved**: the purse before is the purse after with the price. -/
theorem tokens_conserved [DecidableEq T] (B price : Multiset T)
    (enabled : (tokens T).Enables B (site := PUnit.unit) price) :
    B = (tokens T).fire B (site := PUnit.unit) price + price :=
  (tokens_run_conserved ((tokens T).firing B price enabled)).trans
    (congrArg (_ + ·) ((tokens T).instanceValuation_firing (tokens T).consume price enabled))

/-- A firing removes as many tokens as its price has. -/
theorem tokens_card [DecidableEq T] (B price : Multiset T)
    (enabled : (tokens T).Enables B (site := PUnit.unit) price) :
    B.card = ((tokens T).fire B (site := PUnit.unit) price).card + price.card :=
  (congrArg Multiset.card (tokens_conserved B price enabled)).trans (Multiset.card_add _ _)

/-- Two prices are concurrent exactly when both are in the purse together. -/
theorem tokens_concurrent_iff (B price price' : Multiset T) :
    (tokens T).Concurrent B (site₁ := PUnit.unit) (site₂ := PUnit.unit) price price' ↔
      price + price' ≤ B := by
  change (price + price' + 0 ≤ B ∧ price + price' + 0 ≤ B) ↔ price + price' ≤ B
  rw [add_zero, and_self]

/-! ## Ordered purses kept at places -/

section Purses

variable {Place Cell : Type uPlace}

/-- Ordered purses kept at places, any number of them paying one firing. A
resource is one purse: a place with a list of cells, the top cell first. An
instance at a place is a bag of chosen purses there, each named by its top cell
and its rest. Firing takes each chosen purse and leaves its rest at that
place. -/
def pursesMany (Place Cell : Type uPlace) : System.{uPlace, uPlace} (Place × List Cell) where
  Site := Place
  Instance := fun _ => Multiset (Cell × List Cell)
  consume := fun {place} chosen => chosen.map fun purse => (place, purse.1 :: purse.2)
  read := fun _ => 0
  produce := fun {place} chosen => chosen.map fun purse => (place, purse.2)

/-- **A choice is enabled exactly when the chosen purses are in the bag.** -/
theorem pursesMany_enables_iff (M : Multiset (Place × List Cell)) (place : Place)
    (chosen : Multiset (Cell × List Cell)) :
    (pursesMany Place Cell).Enables M (site := place) chosen ↔
      chosen.map (fun purse => (place, purse.1 :: purse.2)) ≤ M := by
  change chosen.map (fun purse => (place, purse.1 :: purse.2)) + 0 ≤ M ↔ _
  rw [add_zero]

/-- Firing takes the chosen purses and adds their rests. -/
theorem pursesMany_fire [DecidableEq Place] [DecidableEq Cell]
    (M : Multiset (Place × List Cell)) (place : Place) (chosen : Multiset (Cell × List Cell)) :
    (pursesMany Place Cell).fire M (site := place) chosen =
      M - chosen.map (fun purse => (place, purse.1 :: purse.2)) +
        chosen.map (fun purse => (place, purse.2)) :=
  rfl

/-- **Firing replaces each chosen purse by its rest**, at the same place, and
leaves every other purse as it is. -/
theorem pursesMany_fire_add [DecidableEq Place] [DecidableEq Cell]
    (others : Multiset (Place × List Cell)) (place : Place)
    (chosen : Multiset (Cell × List Cell)) :
    (pursesMany Place Cell).fire (others + chosen.map fun purse => (place, purse.1 :: purse.2))
        (site := place) chosen =
      others + chosen.map fun purse => (place, purse.2) := by
  rw [pursesMany_fire, add_tsub_cancel_right]

/-- Each chosen purse keeps its place and loses exactly its top cell. -/
theorem pursesMany_produce_eq (place : Place) (chosen : Multiset (Cell × List Cell)) :
    (pursesMany Place Cell).produce (site := place) chosen =
      ((pursesMany Place Cell).consume (site := place) chosen).map
        fun purse => (purse.1, purse.2.tail) := by
  change chosen.map _ = (chosen.map _).map _
  rw [Multiset.map_map]
  rfl

/-- **Two choices are concurrent exactly when both chosen bags are in the bag
together.** A purse present once pays for one of them. -/
theorem pursesMany_concurrent_iff (M : Multiset (Place × List Cell)) (place place' : Place)
    (chosen chosen' : Multiset (Cell × List Cell)) :
    (pursesMany Place Cell).Concurrent M (site₁ := place) (site₂ := place') chosen chosen' ↔
      chosen.map (fun purse => (place, purse.1 :: purse.2)) +
        chosen'.map (fun purse => (place', purse.1 :: purse.2)) ≤ M := by
  change (chosen.map (fun purse => (place, purse.1 :: purse.2)) +
      chosen'.map (fun purse => (place', purse.1 :: purse.2)) + 0 ≤ M ∧
    chosen.map (fun purse => (place, purse.1 :: purse.2)) +
      chosen'.map (fun purse => (place', purse.1 :: purse.2)) + 0 ≤ M) ↔ _
  rw [add_zero, and_self]

/-- **Only the purses at the place pay.** A choice at a place is enabled in a
bag exactly when it is enabled among the purses of the bag at that place. -/
theorem pursesMany_enables_iff_at [DecidableEq Place] (M : Multiset (Place × List Cell))
    (place : Place) (chosen : Multiset (Cell × List Cell)) :
    (pursesMany Place Cell).Enables M (site := place) chosen ↔
      (pursesMany Place Cell).Enables (M.filter fun purse => purse.1 = place) (site := place)
        chosen := by
  rw [pursesMany_enables_iff, pursesMany_enables_iff, Multiset.le_filter]
  refine (and_iff_left ?_).symm
  intro purse member
  obtain ⟨_, _, rfl⟩ := Multiset.mem_map.mp member
  rfl

/-- **Only a purse holding a cell pays.** When no purse at a place holds a
cell, no choice of at least one purse there is enabled. -/
theorem pursesMany_disabled_of_no_cell (M : Multiset (Place × List Cell)) (place : Place)
    (chosen : Multiset (Cell × List Cell)) (noCell : ∀ top rest, (place, top :: rest) ∉ M)
    (pays : chosen ≠ 0) : ¬ (pursesMany Place Cell).Enables M (site := place) chosen := by
  intro enabled
  obtain ⟨purse, member⟩ := Multiset.exists_mem_of_ne_zero pays
  exact noCell purse.1 purse.2
    (Multiset.mem_of_le ((pursesMany_enables_iff M place chosen).mp enabled)
      (Multiset.mem_map_of_mem _ member))

/-- **A purse at another place does not pay.** With no purse at a place, no
choice of at least one purse there is enabled, whatever the other purses hold. -/
theorem pursesMany_disabled_elsewhere (M : Multiset (Place × List Cell)) (place : Place)
    (chosen : Multiset (Cell × List Cell)) (elsewhere : ∀ purse ∈ M, purse.1 ≠ place)
    (pays : chosen ≠ 0) : ¬ (pursesMany Place Cell).Enables M (site := place) chosen :=
  pursesMany_disabled_of_no_cell M place chosen (fun _ _ member => elsewhere _ member rfl) pays

/-! ### One purse chosen -/

/-- Choosing one purse is enabled exactly when that purse is in the bag. -/
theorem pursesMany_enables_singleton_iff (M : Multiset (Place × List Cell)) (place : Place)
    (top : Cell) (rest : List Cell) :
    (pursesMany Place Cell).Enables M (site := place)
        ({(top, rest)} : Multiset (Cell × List Cell)) ↔ (place, top :: rest) ∈ M := by
  rw [pursesMany_enables_iff, Multiset.map_singleton, Multiset.singleton_le]

/-- Choosing one purse replaces it by its rest. -/
theorem pursesMany_fire_singleton [DecidableEq Place] [DecidableEq Cell]
    (M : Multiset (Place × List Cell)) (place : Place) (top : Cell) (rest : List Cell) :
    (pursesMany Place Cell).fire M (site := place)
        ({(top, rest)} : Multiset (Cell × List Cell)) =
      (place, rest) ::ₘ M.erase (place, top :: rest) := by
  rw [pursesMany_fire, Multiset.map_singleton, Multiset.map_singleton, Multiset.sub_singleton,
    add_comm, Multiset.singleton_add]

/-- Two choices of one purse are concurrent exactly when the two purses they
name are in the bag together. -/
theorem pursesMany_concurrent_singleton_iff (M : Multiset (Place × List Cell))
    (place place' : Place) (top top' : Cell) (rest rest' : List Cell) :
    (pursesMany Place Cell).Concurrent M (site₁ := place) (site₂ := place')
        ({(top, rest)} : Multiset (Cell × List Cell))
        ({(top', rest')} : Multiset (Cell × List Cell)) ↔
      {(place, top :: rest), (place', top' :: rest')} ≤ M := by
  rw [pursesMany_concurrent_iff, Multiset.map_singleton, Multiset.map_singleton,
    Multiset.singleton_add]
  rfl

/-! ### The cells of the purses -/

/-- The number of cells in all the purses of a bag. -/
def cells (M : Multiset (Place × List Cell)) : ℕ :=
  (M.map fun purse => purse.2.length).sum

theorem cells_cons (purse : Place × List Cell) (M : Multiset (Place × List Cell)) :
    cells (purse ::ₘ M) = purse.2.length + cells M := by
  unfold cells
  rw [Multiset.map_cons, Multiset.sum_cons]

/-- All the cells of all the purses of a bag, as one bag. -/
def cellBag (M : Multiset (Place × List Cell)) : Multiset Cell :=
  (M.map fun purse => (purse.2 : Multiset Cell)).sum

theorem cellBag_zero : cellBag (0 : Multiset (Place × List Cell)) = 0 := rfl

theorem cellBag_cons (purse : Place × List Cell) (M : Multiset (Place × List Cell)) :
    cellBag (purse ::ₘ M) = (purse.2 : Multiset Cell) + cellBag M := by
  unfold cellBag
  rw [Multiset.map_cons, Multiset.sum_cons]

theorem cellBag_add (M N : Multiset (Place × List Cell)) :
    cellBag (M + N) = cellBag M + cellBag N := by
  unfold cellBag
  rw [Multiset.map_add, Multiset.sum_add]

/-- The number of cells is the size of the bag of cells. -/
theorem card_cellBag (M : Multiset (Place × List Cell)) : (cellBag M).card = cells M := by
  induction M using Multiset.induction_on with
  | empty => rfl
  | cons purse M ih =>
      rw [cellBag_cons, cells_cons, Multiset.card_add, ih, Multiset.coe_card]

/-- The cells of the chosen purses are their top cells and the cells of their
rests. -/
theorem cellBag_chosen (place : Place) (chosen : Multiset (Cell × List Cell)) :
    cellBag (chosen.map fun purse => (place, purse.1 :: purse.2)) =
      chosen.map Prod.fst + cellBag (chosen.map fun purse => (place, purse.2)) := by
  induction chosen using Multiset.induction_on with
  | empty => rfl
  | cons purse chosen ih =>
      rw [Multiset.map_cons, Multiset.map_cons, Multiset.map_cons, cellBag_cons, cellBag_cons,
        ih, ← Multiset.cons_coe, Multiset.cons_add, Multiset.cons_add, add_left_comm]

theorem cells_add (M N : Multiset (Place × List Cell)) : cells (M + N) = cells M + cells N := by
  unfold cells
  rw [Multiset.map_add, Multiset.sum_add]

/-- The chosen purses hold one cell more each than their rests. -/
theorem cells_chosen (place : Place) (chosen : Multiset (Cell × List Cell)) :
    cells (chosen.map fun purse => (place, purse.1 :: purse.2)) =
      chosen.card + cells (chosen.map fun purse => (place, purse.2)) := by
  rw [← card_cellBag, cellBag_chosen, Multiset.card_add, Multiset.card_map, card_cellBag]

variable [DecidableEq Place] [DecidableEq Cell]

/-- **Along a run, exactly the chosen top cells leave the purses.** The cells
before the run are the cells after it with the top cell of each purse chosen by
a firing of the run. -/
theorem pursesMany_run_cells_taken {M N : Multiset (Place × List Cell)}
    (p : OccurrencePath (pursesMany Place Cell).presentation M N) :
    cellBag M = cellBag N +
      ((pursesMany Place Cell).instanceValuation fun chosen => chosen.map Prod.fst).onPath p :=
  (pursesMany Place Cell).balance_taken cellBag cellBag_zero cellBag_add _
    (fun {place} chosen => cellBag_chosen place chosen) p

/-- **Along a run, the number of cells drops by the number of purses chosen.** -/
theorem pursesMany_run_cells {M N : Multiset (Place × List Cell)}
    (p : OccurrencePath (pursesMany Place Cell).presentation M N) :
    cells M = cells N +
      ((pursesMany Place Cell).instanceValuation fun chosen => chosen.card).onPath p :=
  (pursesMany Place Cell).balance_taken cells rfl cells_add _
    (fun {place} chosen => cells_chosen place chosen) p

/-- **A run neither adds nor removes a purse**: an emptied purse stays, empty. -/
theorem pursesMany_run_card {M N : Multiset (Place × List Cell)}
    (p : OccurrencePath (pursesMany Place Cell).presentation M N) : N.card = M.card := by
  have balanced := (pursesMany Place Cell).balance_taken Multiset.card Multiset.card_zero
    Multiset.card_add (fun _ => 0)
    (fun chosen => (Multiset.card_map _ chosen).trans
      ((Multiset.card_map _ chosen).symm.trans (zero_add _).symm)) p
  rw [(pursesMany Place Cell).instanceValuation_zero p, add_zero] at balanced
  exact balanced.symm

/-- **The cells taken by one firing are exactly the chosen top cells.** -/
theorem pursesMany_cells_taken (M : Multiset (Place × List Cell)) (place : Place)
    (chosen : Multiset (Cell × List Cell))
    (enabled : (pursesMany Place Cell).Enables M (site := place) chosen) :
    cellBag M =
      cellBag ((pursesMany Place Cell).fire M (site := place) chosen) + chosen.map Prod.fst :=
  (pursesMany_run_cells_taken ((pursesMany Place Cell).firing M chosen enabled)).trans
    (congrArg (_ + ·) ((pursesMany Place Cell).instanceValuation_firing _ chosen enabled))

/-- **The number of cells drops by the number of chosen purses.** -/
theorem pursesMany_cells (M : Multiset (Place × List Cell)) (place : Place)
    (chosen : Multiset (Cell × List Cell))
    (enabled : (pursesMany Place Cell).Enables M (site := place) chosen) :
    cells M = cells ((pursesMany Place Cell).fire M (site := place) chosen) + chosen.card :=
  (pursesMany_run_cells ((pursesMany Place Cell).firing M chosen enabled)).trans
    (congrArg (_ + ·) ((pursesMany Place Cell).instanceValuation_firing _ chosen enabled))

/-- A firing neither adds nor removes a purse: an emptied purse stays, empty. -/
theorem pursesMany_card (M : Multiset (Place × List Cell)) (place : Place)
    (chosen : Multiset (Cell × List Cell))
    (enabled : (pursesMany Place Cell).Enables M (site := place) chosen) :
    ((pursesMany Place Cell).fire M (site := place) chosen).card = M.card :=
  pursesMany_run_card ((pursesMany Place Cell).firing M chosen enabled)

end Purses

/-! ## Paying -/

section Funded

variable (S : System.{uRes, uRule} R) (price : ∀ {site : S.Site}, S.Instance site → Multiset T)

/-- **Paying from an unordered purse.** Each instance of `S` also takes its
price in tokens: the product of `S` with the purse. -/
def funded : System.{max uRes uTok, uRule} (R ⊕ T) :=
  S.product (tokens T) S.Site S.Instance (fun i => ⟨_, i⟩) (fun i => ⟨PUnit.unit, price i⟩)

/-- A funded instance is enabled exactly when the instance is enabled and its
price is in the purse. -/
theorem funded_enables_iff (A : Multiset R) (B : Multiset T) {site : S.Site}
    (i : S.Instance site) :
    (funded S @price).Enables (marking A B) i ↔ S.Enables A i ∧ price i ≤ B :=
  (S.product_enables_iff (tokens T) _ _ A B i).trans
    (and_congr_right' (tokens_enables_iff B (price i)))

/-- Firing a funded instance fires the instance and takes its price from the
purse. Forgetting the purse therefore sends funded steps to steps. -/
theorem funded_fire [DecidableEq R] [DecidableEq T] (A : Multiset R) (B : Multiset T)
    {site : S.Site} (i : S.Instance site) :
    (funded S @price).fire (marking A B) i = marking (S.fire A i) (B - price i) :=
  (S.product_fire (tokens T) _ _ A B i).trans
    (congrArg (marking (S.fire A i)) (tokens_fire B (price i)))

/-- **Tokens are conserved**: the purse before is the purse after with the price. -/
theorem funded_tokens_conserved [DecidableEq T] (A : Multiset R) (B : Multiset T)
    {site : S.Site} (i : S.Instance site)
    (enabled : (funded S @price).Enables (marking A B) i) :
    B = (B - price i) + price i :=
  (tokens_conserved B (price i)
    ((tokens_enables_iff B (price i)).mpr ((funded_enables_iff S @price A B i).mp enabled).2)).trans
    (congrArg (· + price i) (tokens_fire B (price i)))

/-- With one cell per firing, a firing removes exactly one cell. -/
theorem funded_one_cell [DecidableEq T] (A : Multiset R) (B : Multiset T) {site : S.Site}
    (i : S.Instance site) (enabled : (funded S @price).Enables (marking A B) i)
    (oneCell : (price i).card = 1) :
    B.card = (B - price i).card + 1 := by
  have conserved := congrArg Multiset.card (funded_tokens_conserved S @price A B i enabled)
  rw [Multiset.card_add, oneCell] at conserved
  exact conserved

/-- Two funded firings are concurrent exactly when the firings are concurrent
and both prices are in the purse together. -/
theorem funded_concurrent_iff (A : Multiset R) (B : Multiset T) {site₁ site₂ : S.Site}
    (i : S.Instance site₁) (j : S.Instance site₂) :
    (funded S @price).Concurrent (marking A B) i j ↔
      S.Concurrent A i j ∧ price i + price j ≤ B :=
  (S.product_concurrent_iff (tokens T) _ _ A B i j).trans
    (and_congr_right' (tokens_concurrent_iff B (price i) (price j)))

/-- An instance whose price is zero is enabled exactly when it is enabled in `S`. -/
theorem funded_zero_price_enables (A : Multiset R) (B : Multiset T) {site : S.Site}
    (i : S.Instance site) (free : price i = 0) :
    (funded S @price).Enables (marking A B) i ↔ S.Enables A i := by
  rw [funded_enables_iff, free]
  exact and_iff_left (Multiset.zero_le B)

/-- An instance whose price is zero leaves the purse alone. -/
theorem funded_zero_price_fire [DecidableEq R] [DecidableEq T] (A : Multiset R)
    (B : Multiset T) {site : S.Site} (i : S.Instance site) (free : price i = 0) :
    (funded S @price).fire (marking A B) i = marking (S.fire A i) B := by
  rw [funded_fire, free, tsub_zero]

/-- **Along a run of funded firings, the purse loses exactly the prices of the
run.** This is what a run of the product takes from the second side. -/
theorem funded_run_conserved [DecidableEq R] [DecidableEq T] {A : Multiset R} {B : Multiset T}
    {N : Multiset (R ⊕ T)} (p : OccurrencePath (funded S @price).presentation (marking A B) N) :
    B = rightPart N + ((funded S @price).instanceValuation @price).onPath p := by
  have taken := (funded S @price).balance_taken rightPart rfl rightPart_add @price
    (fun i => by
      change rightPart (marking (S.consume i) (price i)) =
        price i + rightPart (marking (S.produce i) 0)
      rw [rightPart_marking, rightPart_marking, add_zero]) p
  rwa [rightPart_marking] at taken

end Funded

section FundedAt

variable (S : System.{uRes, uPlace} R) {Place Cell : Type uPlace}
  (place : ∀ {site : S.Site}, S.Instance site → Place)
  (key : ∀ {site : S.Site}, S.Instance site → Cell)

/-- **Paying from the top of a purse at a place.** Instance `i` of `S` also takes
the cell `key i` from the top of one purse at `place i`: the product of `S` with
the purses, with one purse chosen. A joint instance names `i` and the rest of
the purse that pays. -/
def fundedAt : System.{max uRes uPlace, uPlace} (R ⊕ (Place × List Cell)) :=
  S.product (pursesMany Place Cell) S.Site (fun site => S.Instance site × List Cell)
    (fun j => ⟨_, j.1⟩)
    (fun j => ⟨place j.1, ({(key j.1, j.2)} : Multiset (Cell × List Cell))⟩)

/-- A funded instance is enabled exactly when the instance is enabled and the
purse it names is at its place, with its key on top. -/
theorem fundedAt_enables_iff (A : Multiset R) (B : Multiset (Place × List Cell))
    {site : S.Site} (i : S.Instance site) (rest : List Cell) :
    (fundedAt S @place @key).Enables (marking A B) (i, rest) ↔
      S.Enables A i ∧ (place i, key i :: rest) ∈ B :=
  (S.product_enables_iff (pursesMany Place Cell)
      (Joint := fun site => S.Instance site × List Cell) _ _ A B (site := site) (i, rest)).trans
    (and_congr_right' (pursesMany_enables_singleton_iff B (place i) (key i) rest))

/-- **An instance can pay exactly when it is enabled and some purse at its place
has its key on top.** -/
theorem fundedAt_exists_enables_iff (A : Multiset R) (B : Multiset (Place × List Cell))
    {site : S.Site} (i : S.Instance site) :
    (∃ rest, (fundedAt S @place @key).Enables (marking A B) (i, rest)) ↔
      S.Enables A i ∧ ∃ rest, (place i, key i :: rest) ∈ B := by
  constructor
  · rintro ⟨rest, enabled⟩
    obtain ⟨base, member⟩ := (fundedAt_enables_iff S @place @key A B i rest).mp enabled
    exact ⟨base, rest, member⟩
  · rintro ⟨base, rest, member⟩
    exact ⟨rest, (fundedAt_enables_iff S @place @key A B i rest).mpr ⟨base, member⟩⟩

/-- Firing a funded instance fires the instance and leaves the rest of the purse
at its place. -/
theorem fundedAt_fire [DecidableEq R] [DecidableEq Place] [DecidableEq Cell] (A : Multiset R)
    (B : Multiset (Place × List Cell)) {site : S.Site} (i : S.Instance site)
    (rest : List Cell) :
    (fundedAt S @place @key).fire (marking A B) (i, rest) =
      marking (S.fire A i) ((place i, rest) ::ₘ B.erase (place i, key i :: rest)) :=
  (S.product_fire (pursesMany Place Cell) (Joint := fun site => S.Instance site × List Cell)
      _ _ A B (site := site) (i, rest)).trans
    (congrArg (marking (S.fire A i)) (pursesMany_fire_singleton B (place i) (key i) rest))

/-- **Exactly one cell leaves the purses.** -/
theorem fundedAt_one_cell [DecidableEq R] [DecidableEq Place] [DecidableEq Cell]
    (A : Multiset R) (B : Multiset (Place × List Cell)) {site : S.Site} (i : S.Instance site)
    (rest : List Cell)
    (enabled : (fundedAt S @place @key).Enables (marking A B) (i, rest)) :
    cells B =
      cells (rightPart ((fundedAt S @place @key).fire (marking A B) (i, rest))) + 1 := by
  have member := ((fundedAt_enables_iff S @place @key A B i rest).mp enabled).2
  rw [fundedAt_fire, rightPart_marking, ← pursesMany_fire_singleton]
  exact pursesMany_cells B (place i) {(key i, rest)}
    ((pursesMany_enables_singleton_iff B _ _ _).mpr member)

/-- **Along a run of funded firings, one cell leaves the purses for each
firing.** This is what a run of the product takes from the second side. -/
theorem fundedAt_run_cells [DecidableEq R] [DecidableEq Place] [DecidableEq Cell]
    {A : Multiset R} {B : Multiset (Place × List Cell)}
    {N : Multiset (R ⊕ (Place × List Cell))}
    (p : OccurrencePath (fundedAt S @place @key).presentation (marking A B) N) :
    cells B = cells (rightPart N) +
      ((fundedAt S @place @key).instanceValuation fun _ => (1 : ℕ)).onPath p := by
  have taken := (fundedAt S @place @key).balance_taken (fun M => cells (rightPart M)) rfl
    (fun M N => by rw [rightPart_add, cells_add]) (fun _ => 1)
    (fun j => by
      change cells (rightPart (marking (S.consume j.1)
          (({(key j.1, j.2)} : Multiset (Cell × List Cell)).map
            fun purse => (place j.1, purse.1 :: purse.2)))) =
        1 + cells (rightPart (marking (S.produce j.1)
          (({(key j.1, j.2)} : Multiset (Cell × List Cell)).map
            fun purse => (place j.1, purse.2))))
      simp only [rightPart_marking, Multiset.map_singleton, cells, Multiset.sum_singleton,
        List.length_cons]
      exact add_comm _ _) p
  rwa [rightPart_marking] at taken

/-- Two funded firings are concurrent exactly when the firings are concurrent
and the two purses they name are in the bag together. Two payments from one
purse need that purse twice. -/
theorem fundedAt_concurrent_iff (A : Multiset R) (B : Multiset (Place × List Cell))
    {site₁ site₂ : S.Site} (i : S.Instance site₁) (j : S.Instance site₂)
    (rest rest' : List Cell) :
    (fundedAt S @place @key).Concurrent (marking A B) (i, rest) (j, rest') ↔
      S.Concurrent A i j ∧ {(place i, key i :: rest), (place j, key j :: rest')} ≤ B :=
  (S.product_concurrent_iff (pursesMany Place Cell)
      (Joint := fun site => S.Instance site × List Cell) _ _ A B
      (site₁ := site₁) (site₂ := site₂) (i, rest) (j, rest')).trans
    (and_congr_right'
      (pursesMany_concurrent_singleton_iff B (place i) (place j) (key i) (key j) rest rest'))

/-- **The right key at the wrong place does not pay.** With no purse at the place
of an instance, the instance is not enabled, whatever the other purses hold. -/
theorem fundedAt_disabled_elsewhere (A : Multiset R) (B : Multiset (Place × List Cell))
    {site : S.Site} (i : S.Instance site) (rest : List Cell)
    (elsewhere : ∀ purse ∈ B, purse.1 ≠ place i) :
    ¬ (fundedAt S @place @key).Enables (marking A B) (i, rest) := fun enabled =>
  elsewhere _ ((fundedAt_enables_iff S @place @key A B i rest).mp enabled).2 rfl

end FundedAt

/-! ## Paying twice, and merging the two purses

A system funded twice pays `price` from a first purse and `outer` from a second.
Pouring the second purse into the first is a map of resources. The system
funded once with the summed price is the system funded twice, seen through
it. -/

/-- Pour the second purse into the first: the map of resources. -/
def pour : (R ⊕ T) ⊕ T → R ⊕ T := Sum.elim id Sum.inr

/-- Pour the second purse into the first: the map on bags. -/
def merge (M : Multiset ((R ⊕ T) ⊕ T)) : Multiset (R ⊕ T) :=
  M.map pour

theorem merge_marking (A : Multiset R) (B₁ B₂ : Multiset T) :
    merge (marking (marking A B₁) B₂) = marking A (B₁ + B₂) := by
  unfold merge pour marking Multiset.disjSum
  rw [Multiset.map_add, Multiset.map_map, Multiset.map_map, Sum.elim_comp_inl,
    Sum.elim_comp_inr, Multiset.map_id, Multiset.map_add, add_assoc]

section FundedTwice

variable (S : System.{uRes, uRule} R)
  (price outer : ∀ {site : S.Site}, S.Instance site → Multiset T)

/-- The system funded twice: `price` from a first purse, `outer` from a second. -/
abbrev fundedTwice : System.{max uRes uTok, uRule} ((R ⊕ T) ⊕ T) :=
  funded (funded S @price) @outer

/-- The system funded once, with the sum of the two prices. -/
abbrev fundedSum : System.{max uRes uTok, uRule} (R ⊕ T) :=
  funded S (fun i => price i + outer i)

/-- **Funding once with the summed price is funding twice, seen with the second
purse poured into the first.** -/
theorem fundedSum_eq_map :
    fundedSum S @price @outer = (fundedTwice S @price @outer).map pour := by
  have poured : ∀ (A : Multiset R) (B₁ B₂ : Multiset T),
      marking A (B₁ + B₂) = (marking (marking A B₁) B₂).map pour :=
    fun A B₁ B₂ => (merge_marking A B₁ B₂).symm
  exact System.mk_congr (fun i => poured (S.consume i) (price i) (outer i))
    (fun i => poured (S.read i) 0 0) (fun i => poured (S.produce i) 0 0)

/-- Enabled under two fundings: enabled, and each price in its own purse. -/
theorem fundedTwice_enables_iff (A : Multiset R) (B₁ B₂ : Multiset T) {site : S.Site}
    (i : S.Instance site) :
    (fundedTwice S @price @outer).Enables (marking (marking A B₁) B₂) i ↔
      S.Enables A i ∧ price i ≤ B₁ ∧ outer i ≤ B₂ :=
  (funded_enables_iff (funded S @price) @outer (marking A B₁) B₂ i).trans
    ((and_congr_left' (funded_enables_iff S @price A B₁ i)).trans and_assoc)

/-- Firing under two fundings: fire, and take each price from its own purse. -/
theorem fundedTwice_fire [DecidableEq R] [DecidableEq T] (A : Multiset R)
    (B₁ B₂ : Multiset T) {site : S.Site} (i : S.Instance site) :
    (fundedTwice S @price @outer).fire (marking (marking A B₁) B₂) i =
      marking (marking (S.fire A i) (B₁ - price i)) (B₂ - outer i) :=
  (funded_fire (funded S @price) @outer (marking A B₁) B₂ i).trans
    (congrArg (fun inner => marking inner (B₂ - outer i)) (funded_fire S @price A B₁ i))

/-- **Merging sends steps to steps**: the law for maps of resources. -/
theorem merged_rewrites [DecidableEq R] [DecidableEq T] {M N : Multiset ((R ⊕ T) ⊕ T)}
    (step : (fundedTwice S @price @outer).theory.rewrites M N) :
    (fundedSum S @price @outer).theory.rewrites (merge M) (merge N) := by
  rw [fundedSum_eq_map]
  exact (fundedTwice S @price @outer).map_rewrites _ step

/-- **Merging forgets which purse paid.** With both prices in the first purse,
one funding with the summed price fires from the merged purse, and the two
fundings do not fire: the second purse is empty. -/
theorem merged_not_reflected (A : Multiset R) {site : S.Site} (i : S.Instance site)
    (enabled : S.Enables A i) (costs : outer i ≠ 0) :
    (fundedSum S @price @outer).Enables
        (merge (marking (marking A (price i + outer i)) 0)) i ∧
      ¬ (fundedTwice S @price @outer).Enables (marking (marking A (price i + outer i)) 0) i := by
  refine ⟨?_, fun twice => ?_⟩
  · rw [merge_marking, add_zero]
    exact (funded_enables_iff S _ A (price i + outer i) i).mpr ⟨enabled, le_rfl⟩
  · exact costs (Multiset.le_zero.mp
      ((fundedTwice_enables_iff S @price @outer A (price i + outer i) 0 i).mp twice).2.2)

end FundedTwice

/-! ## Paying is a monad graded by prices

Paying at a price is an operation on systems: `funded S price` is `S` fired
together with a purse.  Its unit is the price zero: a system is the system
paid at price zero, seen through the inclusion of its resources.  Its
multiplication pours two purses into one: paying `price` and then `outer`,
with the purses poured together, is paying their sum.  Both are maps of
resources, so both send steps to steps.  The unit, multiplication and
associativity laws are equalities of systems and of maps of resources, and
paying is natural in the resources of the system.  The multiplication is not
idempotent: paying twice costs twice, and merging forgets which purse paid. -/

/-- Pouring three purses into one: the inner two first, or the outer two. -/
theorem pour_assoc :
    (pour ∘ Sum.map pour id : ((R ⊕ T) ⊕ T) ⊕ T → R ⊕ T) = pour ∘ pour := by
  funext x
  rcases x with ((r | t) | t) | t <;> rfl

/-- Pouring an empty second purse in changes nothing. -/
theorem pour_comp_inl : (pour ∘ Sum.inl : R ⊕ T → R ⊕ T) = id := by
  funext x
  rcases x with r | t <;> rfl

/-- Pouring a purse into an empty first purse changes nothing. -/
theorem pour_comp_map_inl : (pour ∘ Sum.map Sum.inl id : R ⊕ T → R ⊕ T) = id := by
  funext x
  rcases x with r | t <;> rfl

/-- Seeing a system through two maps of resources is seeing it through their
composite. -/
theorem System.map_map {R' : Type*} {R'' : Type*} (S : System.{uRes, uRule} R)
    (f : R → R') (g : R' → R'') : (S.map f).map g = S.map (g ∘ f) :=
  System.mk_congr (fun _ => Multiset.map_map _ _ _) (fun _ => Multiset.map_map _ _ _)
    (fun _ => Multiset.map_map _ _ _)

section PayingMonad

variable (S : System.{uRes, uRule} R)

/-- **Unit.** A system is the system paid at price zero, seen through the
inclusion of its resources. -/
theorem map_inl_eq_funded_zero :
    S.map (Sum.inl : R → R ⊕ T) = funded S (fun _ => (0 : Multiset T)) := by
  refine System.mk_congr (fun i => ?_) (fun i => ?_) (fun i => ?_) <;>
    simp [System.map, tokens]

/-- **Paying is natural in the resources**: renaming the resources and then
paying is paying and then renaming, the purse untouched. -/
theorem funded_map {R' : Type uRes} (f : R → R')
    (price : ∀ {site : S.Site}, S.Instance site → Multiset T) :
    (funded S @price).map (Sum.map f id) = funded (S.map f) @price := by
  refine System.mk_congr (fun i => ?_) (fun i => ?_) (fun i => ?_) <;>
    simp [funded, System.product, System.joint, System.map, tokens, Multiset.map_map,
      Function.comp_def]

/-- **Multiplication.** Paying `price` and then `outer`, with the two purses
poured together, is paying their sum. -/
theorem funded_funded_map_pour (price outer : ∀ {site : S.Site}, S.Instance site → Multiset T) :
    (funded (funded S @price) @outer).map pour = funded S (fun i => price i + outer i) :=
  (fundedSum_eq_map S @price @outer).symm

/-- **Left unit.** Paying, then seeing the result beside an empty new purse,
then pouring the purses together, is paying. -/
theorem funded_unit_left (price : ∀ {site : S.Site}, S.Instance site → Multiset T) :
    ((funded S @price).map (Sum.inl : R ⊕ T → (R ⊕ T) ⊕ T)).map pour = funded S @price := by
  rw [System.map_map, pour_comp_inl, System.map_id]

/-- **Right unit.** Seeing the resources beside an empty first purse, paying,
and pouring the purses together, is paying. -/
theorem funded_unit_right (price : ∀ {site : S.Site}, S.Instance site → Multiset T) :
    ((funded S @price).map (Sum.map (Sum.inl : R → R ⊕ T) id)).map pour = funded S @price := by
  rw [System.map_map, pour_comp_map_inl, System.map_id]

/-- **Associativity.** Three purses poured into one give one system in either
order. -/
theorem funded_assoc (system : System.{max uRes uTok, uRule} (((R ⊕ T) ⊕ T) ⊕ T)) :
    (system.map (Sum.map pour id)).map pour = (system.map pour).map pour := by
  rw [System.map_map, System.map_map, pour_assoc]

/-- Paying three prices and pouring the purses together is paying their sum. -/
theorem funded_three (price middle outer : ∀ {site : S.Site}, S.Instance site → Multiset T) :
    ((funded (funded (funded S @price) @middle) @outer).map pour).map pour =
      funded S (fun i => price i + (middle i + outer i)) := by
  rw [funded_funded_map_pour (funded S @price) @middle @outer]
  exact funded_funded_map_pour S @price fun i => middle i + outer i

/-- **Paying twice costs twice**: the multiplication is not idempotent.  An
instance whose price is in the purse is enabled when paid once, and not when
paid twice with the purses poured together, unless the price is zero. -/
theorem pour_twice_costs_twice (price : ∀ {site : S.Site}, S.Instance site → Multiset T)
    (A : Multiset R) {site : S.Site} (i : S.Instance site) (enabled : S.Enables A i)
    (costs : price i ≠ 0) :
    (funded S @price).Enables (marking A (price i)) i ∧
      ¬ ((funded (funded S @price) @price).map pour).Enables (marking A (price i)) i := by
  refine ⟨(funded_enables_iff S @price A (price i) i).mpr ⟨enabled, le_rfl⟩, fun twice => ?_⟩
  change (marking (marking (S.consume i) (price i)) (price i)).map pour +
      (marking (marking (S.read i) 0) 0).map pour ≤ marking A (price i) at twice
  rw [← merge, ← merge, merge_marking, merge_marking, marking_add, marking_le_iff] at twice
  have : price i + price i ≤ price i + 0 := by
    simpa using le_trans (Multiset.le_add_right _ _) twice.2
  exact costs (Multiset.le_zero.mp (le_of_add_le_add_left this))

end PayingMonad

/-! ## Controls: a replicated input that pays for each message

The replicated input of `Controls` takes both messages, in either order. Paying
one token for each message, it takes as many messages as the purse has tokens.
Paying from the top of a purse at the place of the message, it takes a message
only when a purse at that place has the right cell on top. -/

namespace ProductControls

open Controls

/-- The replicated input, paying one token for each message it takes. -/
def paidReceiver : System (Res ⊕ Unit) :=
  funded persistentReceiver (fun _ => {()})

/-- Taking message `value` and paying one token for it. -/
def takePaid (value : ℕ) : paidReceiver.Instance () := takeAgain value

/-- **It fires when funded.** With one token the first message is taken, and the
token is spent. -/
theorem fires_when_funded :
    paidReceiver.Enables (marking twoMessages {()}) (takePaid 1) ∧
      paidReceiver.fire (marking twoMessages {()}) (takePaid 1) =
        marking {Res.message 2, Res.receiver, Res.received 1} 0 :=
  ⟨by unfold System.Enables; decide, by unfold System.fire; decide⟩

/-- **It does not fire from an empty purse**, where the unpaid input fires. -/
theorem empty_purse_disabled :
    persistentReceiver.Enables twoMessages (takeAgain 1) ∧
      ¬ paidReceiver.Enables (marking twoMessages 0) (takePaid 1) :=
  ⟨by unfold System.Enables; decide, by unfold System.Enables; decide⟩

/-- **One token pays for one message.** The unpaid input takes the second
message after the first. With one token, nothing fires after the first. -/
theorem one_token_one_firing (value : ℕ) :
    persistentReceiver.Enables (persistentReceiver.fire twoMessages (takeAgain 1))
        (takeAgain 2) ∧
      ¬ paidReceiver.Enables (paidReceiver.fire (marking twoMessages {()}) (takePaid 1))
        (takePaid value) := by
  refine ⟨by unfold System.Enables System.fire; decide, fun enabled => ?_⟩
  have spent : paidReceiver.fire (marking twoMessages {()}) (takePaid 1) =
      marking (persistentReceiver.fire twoMessages (takeAgain 1)) ({()} - {()}) :=
    funded_fire persistentReceiver _ twoMessages {()} (takeAgain 1)
  rw [spent] at enabled
  exact absurd
    ((funded_enables_iff persistentReceiver _ _ _ (takeAgain value)).mp enabled).2 (by decide)

/-- **Two firings need two tokens.** The two messages are taken concurrently
from a purse of two tokens, and not from a purse of one. -/
theorem two_tokens_two_firings :
    paidReceiver.Concurrent (marking twoMessages {(), ()}) (takePaid 1) (takePaid 2) ∧
      ¬ paidReceiver.Concurrent (marking twoMessages {()}) (takePaid 1) (takePaid 2) :=
  ⟨by unfold System.Concurrent; decide, by unfold System.Concurrent; decide⟩

/-- **The merged purse does not tell which purse held a token.** Two tokens in
the first purse pay the summed price. They do not pay one price from each
purse. -/
theorem merging_forgets_the_purse :
    (fundedSum persistentReceiver (T := Unit) (fun _ => {()}) (fun _ => {()})).Enables
        (merge (marking (marking twoMessages {(), ()}) 0)) (site := ()) (takeAgain 1) ∧
      ¬ (fundedTwice persistentReceiver (T := Unit) (fun _ => {()}) (fun _ => {()})).Enables
        (marking (marking twoMessages {(), ()}) 0) (site := ()) (takeAgain 1) :=
  merged_not_reflected persistentReceiver _ _ twoMessages (takeAgain 1)
    (by unfold System.Enables; decide) (by decide)

/-- The replicated input, paying for each message with a `true` cell from the
top of a purse at place `0`. -/
def paidAtReceiver : System (Res ⊕ (ℕ × List Bool)) :=
  fundedAt persistentReceiver (fun _ => 0) (fun _ => true)

/-- Taking message `value` and paying from a purse whose other cells are `rest`. -/
def takeFrom (value : ℕ) (rest : List Bool) : paidAtReceiver.Instance () :=
  (takeAgain value, rest)

/-- **A purse at the place pays**, and its top cell leaves. -/
theorem purse_pays_at_its_place :
    paidAtReceiver.Enables (marking twoMessages {(0, [true, false])}) (takeFrom 1 [false]) ∧
      paidAtReceiver.fire (marking twoMessages {(0, [true, false])}) (takeFrom 1 [false]) =
        marking {Res.message 2, Res.receiver, Res.received 1} {(0, [false])} :=
  ⟨by unfold System.Enables; decide, by unfold System.fire; decide⟩

/-- **A purse at the wrong place does not pay**, whatever it holds. -/
theorem purse_elsewhere_does_not_pay (value : ℕ) (rest : List Bool) :
    ¬ paidAtReceiver.Enables (marking twoMessages {(1, [true, false])})
      (takeFrom value rest) :=
  fundedAt_disabled_elsewhere persistentReceiver _ _ twoMessages {(1, [true, false])}
    (takeAgain value) rest (by decide)

/-- **A cell under the top does not pay.** The purse is at the right place and
holds the right cell, under another. -/
theorem buried_cell_does_not_pay (value : ℕ) (rest : List Bool) :
    ¬ paidAtReceiver.Enables (marking twoMessages {(0, [false, true])})
      (takeFrom value rest) := by
  intro enabled
  have member : ((0, true :: rest) : ℕ × List Bool) ∈
      ({(0, [false, true])} : Multiset (ℕ × List Bool)) :=
    ((fundedAt_enables_iff persistentReceiver _ _ twoMessages {(0, [false, true])}
      (takeAgain value) rest).mp enabled).2
  cases Multiset.mem_singleton.mp member

/-- Two messages, the receiver, and one purse of two cells. -/
def onePurse : Multiset (Res ⊕ (ℕ × List Bool)) :=
  marking twoMessages {(0, [true, true])}

/-- **One purse orders its payments.** Either message can be paid for from the
purse, and the two firings are not concurrent: both need the purse. After the
first, the second message is paid for from the rest of the purse. Two tokens in
an unordered purse pay concurrently (`two_tokens_two_firings`). -/
theorem one_purse_orders_payments :
    paidAtReceiver.Enables onePurse (takeFrom 1 [true]) ∧
      paidAtReceiver.Enables onePurse (takeFrom 2 [true]) ∧
      ¬ paidAtReceiver.Concurrent onePurse (takeFrom 1 [true]) (takeFrom 2 [true]) ∧
      paidAtReceiver.Enables (paidAtReceiver.fire onePurse (takeFrom 1 [true]))
        (takeFrom 2 []) :=
  ⟨by unfold System.Enables; decide, by unfold System.Enables; decide,
    by unfold System.Concurrent; decide, by unfold System.Enables System.fire; decide⟩

/-- **Two purses pay concurrently.** -/
theorem two_purses_two_firings :
    paidAtReceiver.Concurrent (marking twoMessages {(0, [true]), (0, [true])})
      (takeFrom 1 []) (takeFrom 2 []) := by
  unfold System.Concurrent
  decide

/-- **A run of two payments takes two cells, in the order of the purse.** The
two messages are paid for one after the other from the one purse, which is
left empty. Naming the full purse twice is not a run: after the first payment
that purse is no longer there. -/
theorem two_payments_take_two_cells :
    paidAtReceiver.Fires [⟨(), takeFrom 1 [true]⟩, ⟨(), takeFrom 2 []⟩] onePurse
        (marking {Res.receiver, Res.received 1, Res.received 2} {(0, [])}) ∧
      ¬ paidAtReceiver.Fires [⟨(), takeFrom 1 [true]⟩, ⟨(), takeFrom 2 [true]⟩] onePurse
        (marking {Res.receiver, Res.received 1, Res.received 2} {(0, [])}) := by
  refine ⟨⟨by unfold System.Enables; decide, by unfold System.Enables System.fire; decide,
    by unfold System.Fires System.fire; decide⟩, fun fires => ?_⟩
  exact absurd fires.2.1 (by unfold System.Enables System.fire; decide)

/-- **The balance of a firing needs its consumption to be present.** A price
that is not in the purse is not taken from it, and nothing accounts for it. -/
theorem balance_needs_presence :
    ¬ (tokens Unit).Enables 0 (site := PUnit.unit) ({()} : Multiset Unit) ∧
      Multiset.card (0 : Multiset Unit) + Multiset.card ((tokens Unit).produce
          (site := PUnit.unit) ({()} : Multiset Unit)) ≠
        Multiset.card ((tokens Unit).fire 0 (site := PUnit.unit) ({()} : Multiset Unit)) +
          Multiset.card ((tokens Unit).consume (site := PUnit.unit) ({()} : Multiset Unit)) :=
  ⟨by unfold System.Enables; decide, by unfold System.fire; decide⟩

/-! ### What a run consumes, and the bags it passes through -/

/-- The replicated input takes the two messages, in either order. -/
def receiverPair : persistentReceiver.concurrency.Pair twoMessages where
  first := persistentReceiver.event twoMessages (takeAgain 1) (by unfold System.Enables; decide)
  second := persistentReceiver.event twoMessages (takeAgain 2) (by unfold System.Enables; decide)
  independent := persistent_receiver_concurrent

/-- Every firing graded by the copies of message `1` in the bag where it fires. -/
def messageOneSeen : OccurrenceValuation persistentReceiver.presentation ℕ where
  grade {M _} _ := (M : Multiset Res).count (Res.message 1)

/-- **What a run consumes is a property of its trace; the bags it passes
through are not.** Taking the two messages in either order consumes both
messages. Grading each firing by the copies of message `1` where it fires tells
the two orders apart: taken first, message `1` is seen once; taken second, it
is seen twice. -/
theorem consumed_of_the_trace_bags_not :
    persistentReceiver.consumedValuation.onPath
          (receiverPair.route persistentReceiver.concurrency) =
        persistentReceiver.consumedValuation.onPath
          (receiverPair.swapped persistentReceiver.concurrency) ∧
      ¬ Descends persistentReceiver.concurrency.tiles messageOneSeen := by
  refine ⟨(descends_iff_tiles _ _).mp persistentReceiver.consumedValuation_descends receiverPair,
    fun descends => ?_⟩
  have routes := ((descends_iff_tiles _ _).mp descends receiverPair).trans
    (System.onPath_swapped persistentReceiver messageOneSeen receiverPair)
  exact absurd routes (by decide)

/-! ### The synchronous product of the two theories -/

/-- The replicated input beside a purse of tokens, with every payment allowed:
a joint instance names a message and any price. -/
def anyPayment : System (Res ⊕ Unit) :=
  persistentReceiver.product (tokens Unit) Unit (fun _ => ℕ × Multiset Unit)
    (fun j => ⟨(), takeAgain j.1⟩) (fun j => ⟨PUnit.unit, j.2⟩)

/-- **With every pair of instances allowed, the product is the synchronous
product of the two theories.** -/
theorem any_payment_is_synchronous (M N : Multiset (Res ⊕ Unit)) :
    anyPayment.theory.Step M N ↔
      (GSLT.synchronousProduct persistentReceiver.theory (tokens Unit).theory).Step
        (parts M) (parts N) :=
  persistentReceiver.product_step_iff_synchronous (tokens Unit) _ _
    (fun s p => ⟨(), (s.2, p.2), rfl, rfl⟩) M N

/-- **Paying is not the synchronous product of the two theories.** With an empty
purse, the input takes a message while the purse pays the empty price: a step
of both theories together. No paying instance fires: each is paired with its
own price, one token. -/
theorem paying_is_not_synchronous :
    (GSLT.synchronousProduct persistentReceiver.theory (tokens Unit).theory).Step
        (parts (marking twoMessages 0))
        (parts (marking (persistentReceiver.fire twoMessages (takeAgain 1)) 0)) ∧
      ∀ N, ¬ paidReceiver.theory.Step (marking twoMessages 0) N := by
  refine ⟨?_, fun N step => ?_⟩
  · change persistentReceiver.theory.Step (leftPart (marking twoMessages 0))
        (leftPart (marking (persistentReceiver.fire twoMessages (takeAgain 1)) 0)) ∧
      (tokens Unit).theory.Step (rightPart (marking twoMessages 0))
        (rightPart (marking (persistentReceiver.fire twoMessages (takeAgain 1)) 0))
    rw [leftPart_marking, leftPart_marking, rightPart_marking, rightPart_marking]
    exact ⟨⟨(), takeAgain 1, by unfold System.Enables; decide, rfl⟩,
      ⟨PUnit.unit, (0 : Multiset Unit), by unfold System.Enables; decide, rfl⟩⟩
  · obtain ⟨site, i, enabled, -⟩ := step
    exact absurd ((funded_enables_iff persistentReceiver _ twoMessages 0 i).mp enabled).2
      (by decide)

end ProductControls

/-! ## Controls: several purses, maps, and firing together -/

namespace JointControls

open Controls

/-- Three purses: two at place `0` and one at place `1`. -/
def threePurses : Multiset (ℕ × List Bool) := {(0, [true]), (0, [true, false]), (1, [true])}

/-- The choice, at place `0`, of the purses with the given top cells and rests. -/
def atZero (chosen : Multiset (Bool × List Bool)) : (pursesMany ℕ Bool).Instance (0 : ℕ) :=
  chosen

/-- **Two purses pay one firing.** Each gives its top cell and keeps its rest at
its place; the purse at the other place is as it was. Of the four cells, the
two top cells leave. -/
theorem two_purses_pay_one_firing :
    (pursesMany ℕ Bool).Enables threePurses (atZero {(true, []), (true, [false])}) ∧
      (pursesMany ℕ Bool).fire threePurses (atZero {(true, []), (true, [false])}) =
        {(0, []), (0, [false]), (1, [true])} ∧
      cellBag threePurses = {true, true, false, true} ∧
      cellBag ((pursesMany ℕ Bool).fire threePurses (atZero {(true, []), (true, [false])})) =
        {false, true} :=
  ⟨by unfold System.Enables; decide, by unfold System.fire; decide, by decide,
    by unfold System.fire; decide⟩

/-- **A purse pays once in a firing, and not from another place.** Two purses
holding `[true]` are in the bag, one at each place. A choice at place `0` of
two such purses is not enabled. -/
theorem one_purse_pays_once :
    ¬ (pursesMany ℕ Bool).Enables threePurses (atZero {(true, []), (true, [])}) := by
  unfold System.Enables
  decide

/-- Every resource seen as one token. -/
def asToken : Res → Unit := fun _ => ()

/-- **A map that is not injective does not reflect enabling.** The input cannot
take message `1` from a bag holding message `2`. Seen as tokens, the bag holds
the two tokens the instance asks for. -/
theorem map_does_not_reflect_enabling :
    ¬ linearReceiver.Enables {Res.message 2, Res.receiver} (take 1) ∧
      (linearReceiver.map asToken).Enables
        (({Res.message 2, Res.receiver} : Multiset Res).map asToken) (site := ()) (take 1) :=
  ⟨by unfold System.Enables; decide, by unfold System.Enables; decide⟩

/-- **Every map keeps an enabled instance enabled.** -/
theorem map_keeps_enabling :
    linearReceiver.Enables twoMessages (take 1) ∧
      (linearReceiver.map asToken).Enables (twoMessages.map asToken) (site := ()) (take 1) :=
  ⟨by unfold System.Enables; decide,
    linearReceiver.map_enables asToken twoMessages (take 1) (by unfold System.Enables; decide)⟩

/-- Two inputs fired together: a joint instance names the message each takes. -/
def twoInputs : System Res :=
  linearReceiver.joint linearReceiver Unit (fun _ => ℕ × ℕ) (fun j => ⟨(), take j.1⟩)
    (fun j => ⟨(), take j.2⟩)

/-- **With nothing keeping the two parts apart, enabled parts do not make an
enabled joint instance.** Each input can take its message from the bag. Fired
together they ask for the receiver twice, and it is there once. -/
theorem enabled_parts_not_enabled_together :
    linearReceiver.Enables twoMessages (take 1) ∧ linearReceiver.Enables twoMessages (take 2) ∧
      ¬ twoInputs.Enables twoMessages (site := ()) (1, 2) :=
  ⟨by unfold System.Enables; decide, by unfold System.Enables; decide,
    by unfold System.Enables; decide⟩

/-- **A paid instance is two parts kept apart by the type of their resources**,
and is enabled exactly when both are. The replicated input paying a token is the
input and the purse fired together on the sum of their carriers. -/
theorem paid_input_is_fired_together :
    ProductControls.paidReceiver =
        (persistentReceiver.map Sum.inl).joint ((tokens Unit).map Sum.inr) Unit (fun _ => ℕ)
          (fun value => ⟨(), takeAgain value⟩)
          (fun _ => ⟨PUnit.unit, ({()} : Multiset Unit)⟩) ∧
      ProductControls.paidReceiver.Enables (marking twoMessages {()})
        (ProductControls.takePaid 1) :=
  ⟨rfl, ProductControls.fires_when_funded.1⟩

end JointControls

end Mettapedia.GSLT.Causality.ResourceInteraction
