import Mettapedia.GSLT.Causality.SemiringFactStores
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreClosure

/-!
# The graded store: rows annotated in a semiring, and every match of a keep-only rule fired at once

A **graded store** annotates each row with an element of a semiring `K`. It is a space of the weighted answer
algebra, `Space K G = G →₀ K`; a row is present when its annotation is nonzero. Rows annotated in `K` are the
K-relations of Green, Karvounarakis and Tannen (*Provenance semirings*, PODS 2007). The construction, by the
five choices of the step:
* **store**: graded over a semiring `K`, which need not be commutative;
* **commit**: every match at once, each read in the store the firing starts from;
* **guards**: none; a rule reads and makes and takes nothing (keep-only);
* **rules**: one rule, presented by its ground instances, one per binding of its variables (`KeepRule`);
  written with variables, a rule is a list of read atoms and made atoms (`PatternRule`);
* **knowledge**: none beyond the store; rows are ground.

## Matches and the firing

A **match** at a store is a binding whose every read row is present (`Matches`); for a rule written with
variables, a binding of the rule's variables under which every read atom denotes a present row
(`PatternRule.matches_iff`). Its **value** is the product of its reads' annotations in written order (`value`).
The **every-grain firing** keeps every annotation and adds to each made row the sum over matches of the value
times the number of times the binding makes that row (`fireOn_apply`); the value multiplies on the left.
* It may run over any finite catalogue of bindings that contains the matches (`fireOn_eq_of_covers`), and is
  defined at a store when the matches are finitely many (`fire`, `fire_eq_fireOn`). A rule with finitely many
  variables, each occurring in a read atom, has finitely many matches at every store
  (`PatternRule.matchSet_finite`); one with a variable that no read atom binds has infinitely many over an
  infinite domain (`Controls.unsafeRule_infinite`).
* **Weighted answers**: the firing adds the bind of the matches, annotated by their values, into the made rows
  (`fireOn_eq_bind`), over every semiring.
* **One step of the annotated store**: over a commutative semiring the firing is one `System.kStep` of the rule's
  resource system, with the store itself as seed, weight one, and reads read in the store (`fireOn_eq_kStep`);
  equivalently the store plus `kStep` with seed zero, which is the contributions alone
  (`fireOn_eq_add_kStep_zero`). The rule's system is keep-only (`system_keepOnly`). `kStep` with a fixed seed is
  not the firing once the store holds prior output (`Controls.firing_keeps_prior_output`): the firing keeps what
  earlier firings made, so firing again is not the next stage `kStage`, which re-derives from the fixed seed.

## Where the graded store sits among the stores

* **A semiring homomorphism commutes with the firing** (`mapK_fireOn`), over any catalogue; over commutative
  semirings this is `System.map_kStep` for the rule's system (`mapK_fireOn_eq_map_kStep`), and every stage
  commutes as well (`map_kStage_system`).
* **Presence is the set store**: over the two-element semiring the firing's present rows are the present rows
  together with the action of every catalogued ground instance of the set store on them, all at once
  (`support_fireOn_presence`). Over ℕ the present rows are the same (`support_fireOn_nat`): the set store is the
  support of the count store.
* **ℕ is the bag store, read through labels**: for a store of occurrences, the value of a binding in the count
  store is the number of its occurrence-level matches, one present occurrence for each read pattern
  (`card_keys`), and the count store with the rows made once per occurrence-level match is the graded firing of
  the count store (`countStore_keyMade`). So a commit of the occurrence layer that takes nothing and makes those
  rows fires to a store whose count store is the graded firing (`countStore_fire`); such a commit exists when
  identities are natural numbers (`exists_countStore_commit`).
* Homomorphisms go one way: there is none from presence to ℕ, since `1 + 1 = 1` in presence
  (`Controls.no_hom_presence_nat`), and none from ℤ to presence, since `1 + (-1) = 0` while both are present
  (`Controls.no_hom_int_presence`). To count from a set store, read each present row as one and fire over ℕ.

## Orders of single-match firings

* **Snapshot firings in every order** (`snapshot_every_order`): firing the matches one at a time, each carrying
  its value read at the entry store, in any order that lists each binding of the catalogue once, gives the
  every-grain firing. Graded makes commute, as makes of fresh occurrences do (`RegionUpserts.makes_commute`).
  Such orders exist for every catalogue (`exists_order`).
* **In-place firings in every order** (`inPlace_every_order`): firings that read the store they fire in give the
  every-grain firing when the made rows lie in a region disjoint from a region holding every read row. This is
  the aliasing rule of a backend that accumulates into the store it reads: it may update in place when the
  regions are disjoint, and otherwise reads from the entry buffer and writes a separate one (double buffering),
  which is `snapshot_every_order`.
* Without the disjointness, in-place firings depend on the order (`Controls.inPlace_order_matters`): for
  `A += A·A` on the edges `01, 02, 12, 23` the every-grain firing gives `A 0 3 = 1`, one order gives `2`, the
  reverse order `1`. Double buffering gives `1` in both orders (`Controls.snapshot_orders_agree`).

## Controls

* **Factor order**: over two-by-two matrices, reading two rows in the other order changes the firing
  (`Controls.read_order_matters`).
* **Argmax is no keep-only rule.** Every keep-only firing over a canonically ordered semiring is monotone in the
  store (`fireOn_mono`, `fire_mono`), and commutes with the support homomorphism. Argmax over a region is
  neither: a larger store moves the argmax away (`Controls.argmax_not_monotone`), and two stores with the same
  present rows have different argmaxes (`Controls.argmax_not_homomorphic`). So no keep-only rule fires as argmax
  (`Controls.argmax_not_keepRule`, `Controls.argmax_not_keepRule_presence`): selecting the largest needs an
  exact read of the whole region, which no monotone read gives.

## Boundaries

* The change-of-annotation laws hold for semiring homomorphisms only. Rounding to a lower floating-point
  precision is not one (rounding a sum differs in general from summing rounded values, and floating-point
  addition is not even associative), so nothing here licenses a change of precision.
* Takes are not covered: subtracting annotations needs a subtraction on `K` (a monus or a ring), and every match
  at once would take one occurrence once per match.
* The laws are about annotations. Effects an implementation keeps private, such as interning rows or allocating
  buffers, are invisible to them and still use memory: being invisible to the logic does not remove a resource
  effect.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.GradedStore

open Mettapedia.Languages.MeTTa.WeightedAnswerAlgebra (Space Ans Presence supportOfCount)
open Mettapedia.GSLT.Causality.ResourceInteraction (System)
open MeTTaCalculus.OccurrenceCommits (labels)

universe uB uG uK uL uO uN uV uD

/-- **A keep-only rule, presented by its ground instances**: for each binding of the rule's variables, the rows
its read patterns denote, in written order, and the rows its make patterns denote. It takes nothing. -/
structure KeepRule (B : Type uB) (G : Type uG) where
  /-- The rows the read patterns denote at a binding, in written order. -/
  reads : B → List G
  /-- The rows the make patterns denote at a binding. -/
  makes : B → List G

namespace KeepRule

variable {B : Type uB} {G : Type uG} (rule : KeepRule B G)

/-! ## Matches, values and the every-grain firing -/

section Semiring

variable {K : Type uK} [Semiring K]

/-- **A match at a store** is a binding whose every read row is present: its annotation is nonzero. -/
def Matches (S : Space K G) (b : B) : Prop :=
  ∀ g ∈ rule.reads b, S g ≠ 0

/-- **The value of a binding** at a store: the product of its reads' annotations, in written order. -/
def value (S : Space K G) (b : B) : K :=
  ((rule.reads b).map S).prod

/-- The rows a binding makes, each annotated by one; a row made twice is annotated by two. -/
noncomputable def made (b : B) : Space K G :=
  ((rule.makes b).map fun g => Finsupp.single g 1).sum

/-- **The every-grain firing over a catalogue of bindings.** Every annotation is kept, and each binding of the
catalogue adds its value, read in the store the firing starts from, times the rows it makes. -/
noncomputable def fireOn (cat : Finset B) (S : Space K G) : Space K G :=
  S + ∑ b ∈ cat, rule.value S b • rule.made b

/-- A catalogue **covers** the matches at a store when it contains every match. -/
def Covers (S : Space K G) (cat : Finset B) : Prop :=
  ∀ b, rule.Matches S b → b ∈ cat

/-- The matches at a store. -/
def matchSet (S : Space K G) : Set B :=
  {b | rule.Matches S b}

/-- **The every-grain firing**: all matches at once, when there are finitely many. -/
noncomputable def fire (S : Space K G) (finite : (rule.matchSet S).Finite) : Space K G :=
  rule.fireOn finite.toFinset S

/-- **A binding that is not a match has value zero**: a missing read annihilates the product. -/
theorem value_eq_zero_of_not_matches {S : Space K G} {b : B} (notMatch : ¬ rule.Matches S b) :
    rule.value S b = 0 := by
  unfold Matches at notMatch
  push Not at notMatch
  obtain ⟨g, member, zero⟩ := notMatch
  exact List.prod_eq_zero (List.mem_map.mpr ⟨g, member, zero⟩)

theorem matches_of_value_ne_zero {S : Space K G} {b : B} (nonzero : rule.value S b ≠ 0) :
    rule.Matches S b := by
  by_contra notMatch
  exact nonzero (rule.value_eq_zero_of_not_matches notMatch)

/-- Bindings outside a covering catalogue add nothing. -/
theorem sum_eq_of_covers_subset {S : Space K G} {cat cat' : Finset B} (sub : cat ⊆ cat')
    (covers : rule.Covers S cat) :
    ∑ b ∈ cat, rule.value S b • (rule.made b : Space K G) =
      ∑ b ∈ cat', rule.value S b • (rule.made b : Space K G) := by
  apply Finset.sum_subset sub
  intro b _ outside
  rw [rule.value_eq_zero_of_not_matches (S := S) (b := b) fun isMatch => outside (covers b isMatch),
    zero_smul]

/-- **The firing does not depend on the catalogue**, as long as it covers the matches. -/
theorem fireOn_eq_of_covers {S : Space K G} {cat cat' : Finset B} (covers : rule.Covers S cat)
    (covers' : rule.Covers S cat') : rule.fireOn cat S = rule.fireOn cat' S := by
  classical
  unfold fireOn
  rw [rule.sum_eq_of_covers_subset (Finset.subset_union_left : cat ⊆ cat ∪ cat') covers,
    rule.sum_eq_of_covers_subset (Finset.subset_union_right : cat' ⊆ cat ∪ cat') covers']

theorem covers_toFinset (S : Space K G) (finite : (rule.matchSet S).Finite) :
    rule.Covers S finite.toFinset :=
  fun _ isMatch => finite.mem_toFinset.mpr isMatch

/-- **Any covering catalogue computes the every-grain firing.** -/
theorem fire_eq_fireOn {S : Space K G} (finite : (rule.matchSet S).Finite) {cat : Finset B}
    (covers : rule.Covers S cat) : rule.fire S finite = rule.fireOn cat S :=
  rule.fireOn_eq_of_covers (rule.covers_toFinset S finite) covers

theorem covers_univ [Fintype B] (S : Space K G) : rule.Covers S Finset.univ :=
  fun b _ => Finset.mem_univ b

/-- Over finitely many bindings, the every-grain firing runs over all of them. -/
theorem fire_eq_fireOn_univ [Fintype B] (S : Space K G) :
    rule.fire S (Set.toFinite _) = rule.fireOn Finset.univ S :=
  rule.fire_eq_fireOn _ (rule.covers_univ S)

theorem made_apply [DecidableEq G] (b : B) (g : G) :
    (rule.made b : Space K G) g = ((rule.makes b).count g : K) := by
  unfold made
  generalize rule.makes b = makes
  induction makes with
  | nil => simp
  | cons head rest ih =>
      rw [List.map_cons, List.sum_cons, Finsupp.add_apply, ih, Finsupp.single_apply, List.count_cons]
      by_cases same : head = g
      · subst same
        simp [add_comm]
      · simp [same]

/-- **What the firing does to an annotation**: the row keeps its annotation and gains, for each binding, the
binding's value times the number of times the binding makes it. -/
theorem fireOn_apply [DecidableEq G] (cat : Finset B) (S : Space K G) (g : G) :
    rule.fireOn cat S g = S g + ∑ b ∈ cat, rule.value S b * ((rule.makes b).count g : K) := by
  simp only [fireOn, Finsupp.add_apply, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul,
    made_apply]

/-! ### The firing as weighted answers -/

/-- **The matches, annotated by their values**, as weighted answers over bindings. -/
noncomputable def matchSpace (S : Space K G) (cat : Finset B) (covers : rule.Covers S cat) : Ans K B :=
  Finsupp.onFinset cat (rule.value S) fun b nonzero => covers b (rule.matches_of_value_ne_zero nonzero)

theorem matchSpace_apply (S : Space K G) (cat : Finset B) (covers : rule.Covers S cat) (b : B) :
    rule.matchSpace S cat covers b = rule.value S b :=
  Finsupp.onFinset_apply

/-- **The every-grain firing adds the bind of the matches into the made rows**, over every semiring: the
matches are joined by multiplying their reads in written order, and projected onto the made rows by summing. -/
theorem fireOn_eq_bind (S : Space K G) (cat : Finset B) (covers : rule.Covers S cat) :
    rule.fireOn cat S = S + Ans.bind (rule.matchSpace S cat covers) rule.made := by
  unfold fireOn Ans.bind matchSpace
  rw [Finsupp.onFinset_sum _ fun b => zero_smul K (rule.made b)]

/-! ### Change of annotation -/

/-- **A semiring homomorphism commutes with the every-grain firing**, over any catalogue and every semiring. -/
theorem mapK_fireOn {L : Type uL} [Semiring L] (φ : K →+* L) (cat : Finset B) (S : Space K G) :
    Ans.mapK φ (rule.fireOn cat S) = rule.fireOn cat (Ans.mapK φ S) := by
  classical
  ext g
  simp only [Ans.mapK, Finsupp.mapRange_apply, fireOn_apply, map_add, map_sum, map_mul, map_natCast,
    value, map_list_prod, List.map_map]
  rfl

end Semiring

/-! ## Commutative annotations: one step of the annotated store -/

section Commutative

/-- **The resource system of a keep-only rule**: one site, one instance per binding; an instance consumes
nothing, reads its read rows and produces its made rows. -/
abbrev system : System.{uG, uB} G where
  Site := PUnit
  Instance := fun _ => B
  consume := fun _ => 0
  read := fun b => (rule.reads b : Multiset G)
  produce := fun b => (rule.makes b : Multiset G)

/-- The rule's resource system is keep-only. -/
theorem system_keepOnly : rule.system.KeepOnly :=
  fun _ => rfl

/-- A finite set of bindings, as a catalogue of instances of the rule's resource system. -/
noncomputable def catalogue (cat : Finset B) : List rule.system.Entry :=
  cat.toList.map fun b => ⟨PUnit.unit, b⟩

variable {K : Type uK} [CommSemiring K] [DecidableEq G]

/-- **Over a commutative semiring the every-grain firing is one step of the annotated store**: the seed is the
store, every instance weighs one, and the reads are read in the store. -/
theorem fireOn_eq_kStep (cat : Finset B) (S : Space K G) :
    ⇑(rule.fireOn cat S) = rule.system.kStep (rule.catalogue cat) S (fun _ => 1) S := by
  funext g
  rw [fireOn_apply]
  simp only [System.kStep, System.firingValue, catalogue, List.map_map]
  rw [Finset.sum_map_toList]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  simp only [Function.comp_apply, Multiset.coe_count, Multiset.map_coe, Multiset.prod_coe, one_mul, value]
  exact mul_comm _ _

/-- **The firing adds the step's contributions to the store**: `kStep` with seed zero is the contributions alone,
and the firing keeps the store it starts from. -/
theorem fireOn_eq_add_kStep_zero (cat : Finset B) (S : Space K G) :
    ⇑(rule.fireOn cat S) = ⇑S + rule.system.kStep (rule.catalogue cat) 0 (fun _ => 1) S := by
  rw [rule.fireOn_eq_kStep]
  funext g
  simp only [System.kStep, Pi.add_apply, Pi.zero_apply, zero_add]

/-- Over commutative semirings, `mapK_fireOn` is the existing law `System.map_kStep` of the rule's system. -/
theorem mapK_fireOn_eq_map_kStep {L : Type uL} [CommSemiring L] (φ : K →+* L) (cat : Finset B)
    (S : Space K G) :
    (fun g => φ (rule.fireOn cat S g)) =
      rule.system.kStep (rule.catalogue cat) (φ ∘ S) (φ ∘ fun _ => 1) (φ ∘ S) := by
  rw [rule.fireOn_eq_kStep]
  exact rule.system.map_kStep φ (rule.catalogue cat) S (fun _ => 1) S

/-- **Every stage of the rule's annotated store commutes with a semiring homomorphism** (`System.map_kStage`). -/
theorem map_kStage_system {L : Type uL} [CommSemiring L] (φ : K →+* L) (cat : Finset B) (seed : G → K)
    (n : ℕ) :
    (fun g => φ (rule.system.kStage (rule.catalogue cat) seed (fun _ => 1) n g)) =
      rule.system.kStage (rule.catalogue cat) (φ ∘ seed) (φ ∘ fun _ => 1) n :=
  rule.system.map_kStage φ (rule.catalogue cat) seed (fun _ => 1) n

end Commutative

/-! ## Presence is the set store -/

section Presence

theorem presence_list_prod (l : List Presence) : l.prod.present = true ↔ ∀ x ∈ l, x.present = true := by
  induction l with
  | nil => simp
  | cons x rest ih => simp [List.prod_cons, ih]

theorem presence_sum {ι : Type*} (s : Finset ι) (f : ι → Presence) :
    (∑ i ∈ s, f i).present = true ↔ ∃ i ∈ s, (f i).present = true := by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro i s notIn ih
  rw [Finset.sum_insert notIn, Presence.add_present, Bool.or_eq_true, ih]
  simp

theorem presence_natCast (n : ℕ) : (n : Presence).present = decide (n ≠ 0) := by
  induction n with
  | zero => simp
  | succ n _ => simp [Nat.cast_succ]

variable [DecidableEq G]

/-- **Over presence a row is present after the firing exactly when it was present, or a catalogued match makes
it.** -/
theorem mem_support_fireOn_presence (cat : Finset B) (S : Space Presence G) (g : G) :
    g ∈ (rule.fireOn cat S).support ↔
      g ∈ S.support ∨ ∃ b ∈ cat, rule.Matches S b ∧ g ∈ rule.makes b := by
  rw [Finsupp.mem_support_iff, Presence.ne_zero_iff, rule.fireOn_apply, Presence.add_present,
    Bool.or_eq_true, presence_sum, Finsupp.mem_support_iff, Presence.ne_zero_iff]
  apply or_congr Iff.rfl
  apply exists_congr
  intro b
  apply and_congr_right
  intro _
  rw [Presence.mul_present, Bool.and_eq_true, presence_natCast, value, presence_list_prod,
    List.forall_mem_map, decide_eq_true_eq]
  simp only [Matches, Presence.ne_zero_iff]
  rw [Ne, List.count_eq_zero, not_not]

/-- The ground instance of a binding in the set store: its read rows and its made rows. -/
def setInstance (b : B) : SetStoreClosure.Instance G :=
  ⟨(rule.reads b).toFinset, (rule.makes b).toFinset⟩

/-- **Over presence the every-grain firing is the set store's**: the present rows afterwards are the present rows
together with the action of every catalogued ground instance on them, all at once. -/
theorem support_fireOn_presence (cat : Finset B) (S : Space Presence G) :
    ((rule.fireOn cat S).support : Set G) =
      (S.support : Set G) ∪ ⋃ b ∈ cat, SetStoreClosure.action (rule.setInstance b) (S.support : Set G) := by
  ext g
  simp only [Finset.mem_coe, mem_support_fireOn_presence, Set.mem_union, Set.mem_iUnion, exists_prop]
  apply or_congr Iff.rfl
  apply exists_congr
  intro b
  apply and_congr_right
  intro _
  show _ ↔ (↑(rule.setInstance b).read ⊆ (S.support : Set G) ∧ g ∈ (rule.setInstance b).made)
  simp [setInstance, Matches, Set.subset_def, Finsupp.mem_support_iff]

omit [DecidableEq G] in
theorem support_mapK_supportOfCount (X : Space ℕ G) : (Ans.mapK supportOfCount X).support = X.support := by
  ext g
  rw [Finsupp.mem_support_iff, Finsupp.mem_support_iff, Ans.mapK_apply, Presence.ne_zero_iff]
  exact decide_eq_true_iff

/-- **The set store is the support of the count store**: over ℕ the firing's present rows are the set store's
firing of the present rows. -/
theorem support_fireOn_nat (cat : Finset B) (S : Space ℕ G) :
    ((rule.fireOn cat S).support : Set G) =
      (S.support : Set G) ∪ ⋃ b ∈ cat, SetStoreClosure.action (rule.setInstance b) (S.support : Set G) := by
  have mapped := congrArg Finsupp.support (rule.mapK_fireOn supportOfCount cat S)
  rw [support_mapK_supportOfCount] at mapped
  rw [mapped, support_fireOn_presence, support_mapK_supportOfCount]

end Presence

/-! ## ℕ is the bag store, read through labels -/

section Occurrences

variable {O : Type uO} [DecidableEq G]

/-- **The count store of an occurrence store**: each row annotated by the number of present occurrences that
carry it. -/
noncomputable def countStore (label : O → G) (present : Finset O) : Space ℕ G :=
  Multiset.toFinsupp (labels label present)

/-- **The occurrence-level matches of a binding**: one present occurrence for each read pattern, carrying that
pattern's row. The bag store's `every` identifies a match by such a list of selected occurrences
(`JointFirings.firingKey`). -/
def keys (label : O → G) (present : Finset O) (b : B) : Finset (Fin (rule.reads b).length → O) :=
  Fintype.piFinset fun i => present.filter fun o => label o = (rule.reads b)[i.1]

/-- **Over ℕ the value of a binding is the number of its occurrence-level matches.** -/
theorem card_keys (label : O → G) (present : Finset O) (b : B) :
    (rule.keys label present b).card = rule.value (countStore label present) b := by
  rw [keys, Fintype.card_piFinset, value, ← Fin.prod_univ_fun_getElem]
  apply Finset.prod_congr rfl
  intro i _
  rw [countStore, Multiset.toFinsupp_apply, labels, Multiset.count_map, Finset.card_def,
    Finset.filter_val]
  congr 1
  apply Multiset.filter_congr
  intro o _
  exact eq_comm

/-- The rows the bag store's every-grain firing makes: for each binding of the catalogue, its made rows once
per occurrence-level match. -/
noncomputable def keyMade (label : O → G) (present : Finset O) (cat : Finset B) : Multiset G :=
  ∑ b ∈ cat, (rule.keys label present b).card • (rule.makes b : Multiset G)

/-- **Over ℕ the graded firing counts the bag store's firing**: the present labels together with the rows made
once per occurrence-level match are the graded firing of the count store. -/
theorem countStore_keyMade (label : O → G) (present : Finset O) (cat : Finset B) :
    Multiset.toFinsupp (labels label present + rule.keyMade label present cat) =
      rule.fireOn cat (countStore label present) := by
  ext g
  rw [rule.fireOn_apply, Multiset.toFinsupp_apply, Multiset.count_add, keyMade, Multiset.count_sum']
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  rw [Multiset.count_nsmul, Multiset.coe_count, card_keys, Nat.cast_id]

end Occurrences

/-! ### The occurrence layer's commit, counted -/

section Commits

open MeTTaCalculus.OccurrenceCommits (Commit Enabled labels_fire)

variable {O : Type uO} [DecidableEq G]

/-- **The occurrence layer's firing, counted, is the graded firing over ℕ.** A commit that takes nothing, is
enabled, keeps the labels of the present occurrences, and makes occurrences carrying the rows made once per
occurrence-level match, fires to a store whose count store is the graded firing of the count store. -/
theorem countStore_fire [DecidableEq O] (label label' : O → G) (present : Finset O) (cat : Finset B)
    (c : Commit O G) (noTake : c.taken = ∅) (enabled : Enabled label' present c)
    (keepsLabels : ∀ o ∈ present, label' o = label o)
    (madeRows : labels label' c.made = rule.keyMade label present cat) :
    countStore label' (MeTTaCalculus.OccurrenceCommits.fire present c) =
      rule.fireOn cat (countStore label present) := by
  have noLabels : labels label' (∅ : Finset O) = 0 := by
    simp [labels]
  have sameLabels : labels label' present = labels label present :=
    Multiset.map_congr rfl keepsLabels
  rw [countStore, labels_fire enabled, noTake, noLabels, tsub_zero, sameLabels, madeRows,
    rule.countStore_keyMade]

/-- **Such a commit exists** when occurrence identities are natural numbers: fresh identities above the present
ones carry the made rows. -/
theorem exists_countStore_commit (label : ℕ → G) (present : Finset ℕ) (cat : Finset B) :
    ∃ (label' : ℕ → G) (c : Commit ℕ G), c.taken = ∅ ∧ Enabled label' present c ∧
      (∀ o ∈ present, label' o = label o) ∧ labels label' c.made = rule.keyMade label present cat := by
  obtain ⟨rows, rowsEq⟩ : ∃ rows : List G, (rows : Multiset G) = rule.keyMade label present cat :=
    ⟨_, Multiset.coe_toList _⟩
  obtain ⟨N, below⟩ : ∃ N, ∀ o ∈ present, o < N :=
    ⟨present.sup id + 1, fun o member => Nat.lt_succ_of_le (Finset.le_sup (f := id) member)⟩
  refine ⟨fun o => if o < N then label o else rows.getD (o - N) (label o),
    ⟨∅, ∅, (Finset.range rows.length).map (addRightEmbedding N), []⟩, rfl,
    ⟨Finset.empty_subset _, Finset.empty_subset _, Finset.disjoint_empty_left _, ?_, ?_⟩, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro o made inPresent
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp made
    have above := below _ inPresent
    rw [addRightEmbedding_apply] at above
    omega
  · intro read member
    cases member
  · intro o inPresent
    simp [below o inPresent]
  · rw [← rowsEq]
    show Multiset.map _ ((Finset.range rows.length).map (addRightEmbedding N)).val = (rows : Multiset G)
    rw [Finset.map_val, Finset.range_val, Multiset.map_map, ← Multiset.coe_range, Multiset.map_coe]
    congr 1
    apply List.ext_getElem (by simp)
    intro i _ inRows
    simp only [List.getElem_map, List.getElem_range, Function.comp_apply, addRightEmbedding_apply]
    rw [if_neg (by omega), Nat.add_sub_cancel, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inRows,
      Option.getD_some]

end Commits

/-! ## Monotonicity over canonically ordered annotations -/

section Ordered

variable {K : Type uK} [Semiring K] [PartialOrder K] [CanonicallyOrderedAdd K] [IsOrderedAddMonoid K]

omit [IsOrderedAddMonoid K] in
theorem value_mono {S S' : Space K G} (le : S ≤ S') (b : B) : rule.value S b ≤ rule.value S' b :=
  List.prod_le_prod' fun g _ => Finsupp.le_def.mp le g

/-- **Over canonically ordered annotations the firing is monotone in the store**, over any catalogue. -/
theorem fireOn_mono [DecidableEq G] (cat : Finset B) {S S' : Space K G} (le : S ≤ S') :
    rule.fireOn cat S ≤ rule.fireOn cat S' := by
  rw [Finsupp.le_def]
  intro g
  rw [rule.fireOn_apply, rule.fireOn_apply]
  exact add_le_add (Finsupp.le_def.mp le g)
    (Finset.sum_le_sum fun b _ => mul_le_mul' (rule.value_mono le b) le_rfl)

omit [IsOrderedAddMonoid K] in
/-- A larger store has more matches. -/
theorem matchSet_mono {S S' : Space K G} (le : S ≤ S') : rule.matchSet S ⊆ rule.matchSet S' := by
  intro b isMatch g member
  have positive : 0 < S g := pos_iff_ne_zero.mpr (isMatch g member)
  exact (positive.trans_le (Finsupp.le_def.mp le g)).ne'

/-- **The every-grain firing is monotone in the store.** -/
theorem fire_mono [DecidableEq G] {S S' : Space K G} (le : S ≤ S') (finite : (rule.matchSet S).Finite)
    (finite' : (rule.matchSet S').Finite) : rule.fire S finite ≤ rule.fire S' finite' := by
  have covers : rule.Covers S finite'.toFinset :=
    fun b isMatch => finite'.mem_toFinset.mpr (rule.matchSet_mono le isMatch)
  rw [rule.fire_eq_fireOn finite covers]
  exact rule.fireOn_mono _ le

end Ordered

/-! ## Orders of single-match firings -/

section Sequential

variable {K : Type uK} [Semiring K]

/-- **A single-match firing with its value read at the entry store** (double buffering). -/
noncomputable def fireSnapshot (entry : Space K G) (b : B) (T : Space K G) : Space K G :=
  T + rule.value entry b • rule.made b

/-- **A single-match firing in place**: it reads the store it fires in. -/
noncomputable def fireInPlace (b : B) (T : Space K G) : Space K G :=
  T + rule.value T b • rule.made b

/-- Every catalogue has an order that lists each of its bindings once. -/
theorem exists_order [DecidableEq B] (cat : Finset B) : ∃ l : List B, l.Nodup ∧ l.toFinset = cat :=
  ⟨cat.toList, cat.nodup_toList, cat.toList_toFinset⟩

theorem foldl_fireSnapshot (entry : Space K G) (l : List B) (T : Space K G) :
    l.foldl (fun T b => rule.fireSnapshot entry b T) T =
      T + (l.map fun b => rule.value entry b • rule.made b).sum := by
  induction l generalizing T with
  | nil => simp
  | cons b rest ih => rw [List.foldl_cons, ih, fireSnapshot, List.map_cons, List.sum_cons, add_assoc]

/-- **Snapshot firings in every order are the every-grain firing**: firing the bindings of the catalogue one at
a time, in any order that lists each once, each with its value read at the entry store. Graded makes commute. -/
theorem snapshot_every_order [DecidableEq B] (cat : Finset B) (entry : Space K G) {l : List B}
    (nodup : l.Nodup) (enumerates : l.toFinset = cat) :
    l.foldl (fun T b => rule.fireSnapshot entry b T) entry = rule.fireOn cat entry := by
  unfold fireOn
  rw [rule.foldl_fireSnapshot, ← enumerates, List.sum_toFinset _ nodup]

/-- **In-place firings in every order are the every-grain firing when no made row is read**: the made rows lie in
a region disjoint from a region that holds every read row. This is the aliasing rule of a backend that
accumulates into the store it reads: in place when the regions are disjoint; otherwise it reads the entry
buffer and writes a separate one (double buffering, `snapshot_every_order`). -/
theorem inPlace_every_order [DecidableEq B] [DecidableEq G] (cat : Finset B) (entry : Space K G)
    (readRegion madeRegion : G → Bool)
    (readsIn : ∀ b ∈ cat, ∀ g ∈ rule.reads b, readRegion g = true)
    (makesIn : ∀ b ∈ cat, ∀ g ∈ rule.makes b, madeRegion g = true)
    (disjoint : ∀ g, madeRegion g = true → readRegion g = false)
    {l : List B} (nodup : l.Nodup) (enumerates : l.toFinset = cat) :
    l.foldl (fun T b => rule.fireInPlace b T) entry = rule.fireOn cat entry := by
  rw [← rule.snapshot_every_order cat entry nodup enumerates]
  have inCat : ∀ b ∈ l, b ∈ cat := fun b member => enumerates ▸ List.mem_toFinset.mpr member
  suffices key : ∀ (l : List B), (∀ b ∈ l, b ∈ cat) → ∀ T : Space K G,
      (∀ g, readRegion g = true → T g = entry g) →
      l.foldl (fun T b => rule.fireInPlace b T) T = l.foldl (fun T b => rule.fireSnapshot entry b T) T from
    key l inCat entry fun _ _ => rfl
  intro l
  induction l with
  | nil => intro _ T _; rfl
  | cons b rest ih =>
      intro inCat T agree
      have bIn : b ∈ cat := inCat b (List.mem_cons.mpr (Or.inl rfl))
      have sameValue : rule.value T b = rule.value entry b := by
        unfold value
        congr 1
        apply List.map_congr_left
        intro g member
        exact agree g (readsIn b bIn g member)
      have step : rule.fireInPlace b T = rule.fireSnapshot entry b T := by
        rw [fireInPlace, fireSnapshot, sameValue]
      rw [List.foldl_cons, List.foldl_cons, step]
      apply ih (fun b' member => inCat b' (List.mem_cons.mpr (Or.inr member)))
      intro g inRead
      rw [fireSnapshot, Finsupp.add_apply, Finsupp.smul_apply, rule.made_apply]
      have notMade : (rule.makes b).count g = 0 := by
        rw [List.count_eq_zero]
        intro made
        have outside := disjoint g (makesIn b bIn g made)
        rw [inRead] at outside
        exact absurd outside (by decide)
      rw [notMade, Nat.cast_zero, smul_zero, add_zero]
      exact agree g inRead

end Sequential

end KeepRule

/-! ## Rules written with variables -/

/-- **An atom pattern**: a relation name and arguments, each a variable or a constant. -/
structure Atom (N : Type uN) (V : Type uV) (D : Type uD) where
  /-- The relation name. -/
  name : N
  /-- The arguments, each a variable or a constant. -/
  args : List (V ⊕ D)

/-- The row an atom denotes at a binding of its variables. -/
def Atom.inst {N : Type uN} {V : Type uV} {D : Type uD} (σ : V → D) (a : Atom N V D) : N × List D :=
  (a.name, a.args.map (Sum.elim σ id))

/-- **A keep-only rule written with variables**: its read atoms, in written order, and its made atoms. -/
structure PatternRule (N : Type uN) (V : Type uV) (D : Type uD) where
  /-- The read atoms, in written order. -/
  reads : List (Atom N V D)
  /-- The made atoms. -/
  makes : List (Atom N V D)

namespace PatternRule

variable {N : Type uN} {V : Type uV} {D : Type uD}

/-- Its ground instances: one per binding of its variables. -/
def toKeepRule (r : PatternRule N V D) : KeepRule (V → D) (N × List D) :=
  ⟨fun σ => r.reads.map (Atom.inst σ), fun σ => r.makes.map (Atom.inst σ)⟩

/-- **A match is a binding of the rule's variables under which every read atom denotes a present row.** -/
theorem matches_iff {K : Type uK} [Semiring K] (r : PatternRule N V D) (S : Space K (N × List D))
    (σ : V → D) : r.toKeepRule.Matches S σ ↔ ∀ a ∈ r.reads, a.inst σ ∈ S.support := by
  simp [KeepRule.Matches, toKeepRule, Finsupp.mem_support_iff]

/-- **Safe**: every variable of the rule occurs in a read atom. -/
def Safe (r : PatternRule N V D) : Prop :=
  ∀ v : V, ∃ a ∈ r.reads, Sum.inl v ∈ a.args

/-- **A safe rule has finitely many matches at every store**: a match binds every variable to a constant of a
present row. -/
theorem matchSet_finite [Finite V] {K : Type uK} [Semiring K] (r : PatternRule N V D) (safe : r.Safe)
    (S : Space K (N × List D)) : (r.toKeepRule.matchSet S).Finite := by
  classical
  have constants : (⋃ row ∈ (S.support : Set (N × List D)), (row.2.toFinset : Set D)).Finite :=
    S.support.finite_toSet.biUnion fun row _ => row.2.toFinset.finite_toSet
  refine (Set.Finite.pi' fun _ : V => constants).subset ?_
  intro σ isMatch v
  obtain ⟨a, inReads, occurs⟩ := safe v
  have present := (r.matches_iff S σ).mp isMatch a inReads
  exact Set.mem_iUnion₂.mpr ⟨a.inst σ, present,
    List.mem_toFinset.mpr (List.mem_map.mpr ⟨Sum.inl v, occurs, rfl⟩)⟩

end PatternRule

/-! ## Controls -/

namespace Controls

open KeepRule

/-! ### Rules written with variables: safe and unsafe -/

/-- The matrix product written with variables: `(read (A $i $j) (B $j $k)) (make (C $i $k))`, with the names
`A, B, C` as `0, 1, 2` and the variables `i, j, k` as `0, 1, 2`. -/
def matmulPattern : PatternRule (Fin 3) (Fin 3) ℕ :=
  ⟨[⟨0, [Sum.inl 0, Sum.inl 1]⟩, ⟨1, [Sum.inl 1, Sum.inl 2]⟩], [⟨2, [Sum.inl 0, Sum.inl 2]⟩]⟩

/-- **The matrix product rule is safe**, so its every-grain firing is defined at every store. -/
theorem matmulPattern_safe : matmulPattern.Safe := by
  intro v
  fin_cases v
  · exact ⟨⟨0, [Sum.inl 0, Sum.inl 1]⟩, by simp [matmulPattern], by simp⟩
  · exact ⟨⟨0, [Sum.inl 0, Sum.inl 1]⟩, by simp [matmulPattern], by simp⟩
  · exact ⟨⟨1, [Sum.inl 1, Sum.inl 2]⟩, by simp [matmulPattern], by simp⟩

/-- A rule that reads nothing and makes `(P $x)`: its variable is bound by no read atom. -/
def unsafeRule : PatternRule Unit Unit ℕ :=
  ⟨[], [⟨(), [Sum.inl ()]⟩]⟩

theorem unsafeRule_not_safe : ¬ unsafeRule.Safe := by
  intro safe
  obtain ⟨a, inReads, _⟩ := safe ()
  simp [unsafeRule] at inReads

/-- **An unsafe rule over an infinite domain has infinitely many matches**, at every store: every binding
matches, since nothing is read. -/
theorem unsafeRule_infinite {K : Type uK} [Semiring K] (S : Space K (Unit × List ℕ)) :
    (unsafeRule.toKeepRule.matchSet S).Infinite :=
  Set.infinite_of_injective_forall_mem (f := fun n : ℕ => fun _ : Unit => n)
    (fun _ _ same => congrFun same ())
    (fun _ g member => by simp [unsafeRule, PatternRule.toKeepRule] at member)

/-! ### Factor order -/

open Mettapedia.Languages.MeTTa.WeightedAnswerAlgebra.Controls (upper lower upper_mul_lower_ne)

/-- Read the rows `first` and `second`, in that order, and make the row `2`. -/
def orderedRule (first second : Fin 3) : KeepRule Unit (Fin 3) :=
  ⟨fun _ => [first, second], fun _ => [2]⟩

/-- Two noncommuting annotations on the rows `0` and `1`. -/
noncomputable def matrixStore : Space (Matrix (Fin 2) (Fin 2) ℕ) (Fin 3) :=
  Finsupp.single 0 upper + Finsupp.single 1 lower

theorem orderedRule_made_row (first second : Fin 3) :
    (orderedRule first second).fireOn Finset.univ matrixStore 2 =
      matrixStore first * matrixStore second := by
  rw [fireOn_apply]
  simp [orderedRule, value, matrixStore, Finsupp.single_apply]

/-- **The factor order is the read order**: over two-by-two matrices, reading the two rows in the other order
changes the firing. -/
theorem read_order_matters :
    (orderedRule 0 1).fireOn Finset.univ matrixStore ≠ (orderedRule 1 0).fireOn Finset.univ matrixStore := by
  intro same
  have atMade := congrArg (fun S => S 2) same
  simp only [orderedRule_made_row] at atMade
  have first : matrixStore 0 = upper := by simp [matrixStore]
  have second : matrixStore 1 = lower := by simp [matrixStore]
  rw [first, second] at atMade
  exact upper_mul_lower_ne atMade

/-! ### In place and the every-grain firing -/

/-- `A += A·A` over four nodes: the binding `(i, j, k)` reads `A i j` and `A j k` and makes `A i k`. -/
def squareRule : KeepRule (Fin 4 × Fin 4 × Fin 4) (Fin 4 × Fin 4) :=
  ⟨fun b => [(b.1, b.2.1), (b.2.1, b.2.2)], fun b => [(b.1, b.2.2)]⟩

/-- The edges `01, 02, 12, 23`. -/
def edges : Finset (Fin 4 × Fin 4) :=
  {(0, 1), (0, 2), (1, 2), (2, 3)}

/-- The store holding each edge once. -/
noncomputable def graph : Space ℕ (Fin 4 × Fin 4) :=
  ∑ e ∈ edges, Finsupp.single e 1

theorem graph_apply (e : Fin 4 × Fin 4) : graph e = if e ∈ edges then 1 else 0 := by
  simp [graph, Finsupp.finsetSum_apply, Finsupp.single_apply]

/-- The three matches at the entry store. -/
def snapshotMatches : Finset (Fin 4 × Fin 4 × Fin 4) :=
  {(0, 1, 2), (0, 2, 3), (1, 2, 3)}

theorem matches_listed : ∀ b : Fin 4 × Fin 4 × Fin 4,
    (b.1, b.2.1) ∈ edges → (b.2.1, b.2.2) ∈ edges → b ∈ snapshotMatches := by
  decide

theorem squareRule_covers : squareRule.Covers graph snapshotMatches := by
  intro b isMatch
  have first := isMatch (b.1, b.2.1) (by simp [squareRule])
  have second := isMatch (b.2.1, b.2.2) (by simp [squareRule])
  rw [graph_apply] at first second
  exact matches_listed b (by simpa using first) (by simpa using second)

/-- **Without the disjointness, in-place firings depend on the order and differ from the every-grain firing.**
The every-grain firing gives `A 0 3 = 1`. Firing `(0,1,2)` first makes `A 0 2 = 2`, which `(0,2,3)` then reads:
`A 0 3 = 2`. The reverse order gives `1`. -/
theorem inPlace_order_matters :
    squareRule.fire graph (Set.toFinite _) (0, 3) = 1 ∧
      ([(0, 1, 2), (0, 2, 3), (1, 2, 3)].foldl (fun T b => squareRule.fireInPlace b T) graph) (0, 3) = 2 ∧
      ([(1, 2, 3), (0, 2, 3), (0, 1, 2)].foldl (fun T b => squareRule.fireInPlace b T) graph) (0, 3) = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [squareRule.fire_eq_fireOn _ squareRule_covers, fireOn_apply]
    simp [snapshotMatches, squareRule, value, graph_apply, edges, List.count_cons]
  · simp [fireInPlace, squareRule, value, made_apply, graph_apply, edges]
  · simp [fireInPlace, squareRule, value, made_apply, graph_apply, edges]

/-- Both orders list each snapshot match once. -/
theorem orders_enumerate :
    [((0 : Fin 4), (1 : Fin 4), (2 : Fin 4)), (0, 2, 3), (1, 2, 3)].Nodup ∧
      [((0 : Fin 4), (1 : Fin 4), (2 : Fin 4)), (0, 2, 3), (1, 2, 3)].toFinset = snapshotMatches ∧
      [((1 : Fin 4), (2 : Fin 4), (3 : Fin 4)), (0, 2, 3), (0, 1, 2)].Nodup ∧
      [((1 : Fin 4), (2 : Fin 4), (3 : Fin 4)), (0, 2, 3), (0, 1, 2)].toFinset = snapshotMatches := by
  decide

/-- **Double buffering repairs the order**: the same two orders, each binding reading the entry store, both give
the every-grain value `A 0 3 = 1`. -/
theorem snapshot_orders_agree :
    ([(0, 1, 2), (0, 2, 3), (1, 2, 3)].foldl (fun T b => squareRule.fireSnapshot graph b T) graph) (0, 3) = 1 ∧
      ([(1, 2, 3), (0, 2, 3), (0, 1, 2)].foldl (fun T b => squareRule.fireSnapshot graph b T) graph) (0, 3) = 1 := by
  obtain ⟨nodup₁, enum₁, nodup₂, enum₂⟩ := orders_enumerate
  rw [squareRule.snapshot_every_order snapshotMatches graph nodup₁ enum₁,
    squareRule.snapshot_every_order snapshotMatches graph nodup₂ enum₂,
    ← squareRule.fire_eq_fireOn (Set.toFinite _) squareRule_covers]
  exact ⟨inPlace_order_matters.1, inPlace_order_matters.1⟩

/-! ### The firing keeps prior output -/

/-- `(read A) (make B)`, with the row `false` for `A` and the row `true` for `B`. -/
def copyRule : KeepRule Unit Bool :=
  ⟨fun _ => [false], fun _ => [true]⟩

/-- The seed: `A` once. -/
noncomputable def seedStore : Space ℕ Bool :=
  Finsupp.single false 1

/-- **A firing keeps what earlier firings made.** Firing twice from the seed gives `B` twice; the step with the
seed fixed, read in the store after one firing, gives `B` once. So a firing is one `kStep` with the store itself
as seed (`fireOn_eq_kStep`), or the store plus the contributions (`fireOn_eq_add_kStep_zero`), and not the step
from a fixed seed once the store holds prior output. -/
theorem firing_keeps_prior_output :
    copyRule.fireOn Finset.univ (copyRule.fireOn Finset.univ seedStore) true = 2 ∧
      copyRule.system.kStep (copyRule.catalogue Finset.univ) seedStore (fun _ => 1)
        (copyRule.fireOn Finset.univ seedStore) true = 1 := by
  constructor
  · simp [fireOn_apply, copyRule, value, seedStore]
  · simp [System.kStep, System.firingValue, KeepRule.catalogue, copyRule, seedStore, fireOn_apply, value]

/-! ### Homomorphisms between the stores go one way -/

/-- **No semiring homomorphism goes from presence to ℕ**: one plus one is one in presence and two in ℕ. To
count from a set store, read each present row as one and fire over ℕ. -/
theorem no_hom_presence_nat : IsEmpty (Presence →+* ℕ) :=
  ⟨fun φ => by
    have h := map_add φ 1 1
    rw [Presence.add_self, map_one] at h
    omega⟩

/-- **The support of an integer is no homomorphism**: one plus minus one is zero, while both are present. -/
theorem no_hom_int_presence : IsEmpty (ℤ →+* Presence) :=
  ⟨fun φ => by
    have h := map_add φ 1 (-1)
    rw [add_neg_cancel, map_zero, map_one] at h
    have present := congrArg Presence.present h
    simp at present⟩

/-! ### Argmax is no keep-only rule -/

/-- Rows for argmax over a region of two candidates: `inl c` carries candidate `c`'s weight, `inr c` says that
`c` has the largest weight. -/
abbrev ArgRow := Bool ⊕ Bool

/-- **Argmax over the region `inl`**: it makes `inr c` for the candidate `c` of largest weight, `false` on a
tie. -/
noncomputable def argmax (S : Space ℕ ArgRow) : Space ℕ ArgRow :=
  S + Finsupp.single (Sum.inr (decide (S (Sum.inl false) < S (Sum.inl true)))) 1

/-- Weights `2` and `1`. -/
noncomputable def lowStore : Space ℕ ArgRow :=
  Finsupp.single (Sum.inl false) 2 + Finsupp.single (Sum.inl true) 1

/-- Weights `2` and `3`: the second candidate has grown. -/
noncomputable def highStore : Space ℕ ArgRow :=
  Finsupp.single (Sum.inl false) 2 + Finsupp.single (Sum.inl true) 3

/-- Weights `1` and `2`: the same present rows as `lowStore`. -/
noncomputable def swappedStore : Space ℕ ArgRow :=
  Finsupp.single (Sum.inl false) 1 + Finsupp.single (Sum.inl true) 2

theorem lowStore_le_highStore : lowStore ≤ highStore := by
  rw [Finsupp.le_def]
  intro g
  rcases g with c | c <;> cases c <;> simp [lowStore, highStore]

/-- **Argmax is not monotone**: the second candidate grows, and the first stops being the argmax. -/
theorem argmax_not_monotone : ¬ argmax lowStore ≤ argmax highStore := by
  intro le
  have atFirst := Finsupp.le_def.mp le (Sum.inr false)
  simp [argmax, lowStore, highStore] at atFirst

/-- **Argmax does not commute with the support homomorphism**: two stores with the same present rows have
different argmaxes. -/
theorem argmax_not_homomorphic :
    Ans.mapK supportOfCount lowStore = Ans.mapK supportOfCount swappedStore ∧
      Ans.mapK supportOfCount (argmax lowStore) ≠ Ans.mapK supportOfCount (argmax swappedStore) := by
  refine ⟨?_, ?_⟩
  · have twoPresent : supportOfCount 2 = supportOfCount 1 := rfl
    simp only [lowStore, swappedStore, Ans.mapK_add, Ans.mapK_single, twoPresent]
  · intro same
    have atFirst := congrArg (fun S => (S (Sum.inr false)).present) same
    simp [argmax, lowStore, swappedStore, supportOfCount] at atFirst

/-- **No keep-only rule fires as argmax**: its every-grain firing is monotone in the store, and argmax is not. -/
theorem argmax_not_keepRule {B : Type uB} (rule : KeepRule B ArgRow)
    (finiteLow : (rule.matchSet lowStore).Finite) (finiteHigh : (rule.matchSet highStore).Finite) :
    ¬ (rule.fire lowStore finiteLow = argmax lowStore ∧ rule.fire highStore finiteHigh = argmax highStore) := by
  rintro ⟨low, high⟩
  apply argmax_not_monotone
  rw [← low, ← high]
  exact rule.fire_mono lowStore_le_highStore finiteLow finiteHigh

/-- **No keep-only rule fires as argmax, over any catalogue**: its firing commutes with the support
homomorphism, and argmax does not. -/
theorem argmax_not_keepRule_presence {B : Type uB} (rule : KeepRule B ArgRow) (cat : Finset B) :
    ¬ (rule.fireOn cat lowStore = argmax lowStore ∧ rule.fireOn cat swappedStore = argmax swappedStore) := by
  rintro ⟨low, swapped⟩
  apply argmax_not_homomorphic.2
  rw [← low, ← swapped, rule.mapK_fireOn, rule.mapK_fireOn, argmax_not_homomorphic.1]

end Controls

#print axioms KeepRule.fireOn_eq_of_covers
#print axioms KeepRule.fire_eq_fireOn
#print axioms KeepRule.fireOn_apply
#print axioms KeepRule.fireOn_eq_bind
#print axioms KeepRule.mapK_fireOn
#print axioms KeepRule.fireOn_eq_kStep
#print axioms KeepRule.fireOn_eq_add_kStep_zero
#print axioms KeepRule.mapK_fireOn_eq_map_kStep
#print axioms KeepRule.map_kStage_system
#print axioms KeepRule.support_fireOn_presence
#print axioms KeepRule.support_fireOn_nat
#print axioms KeepRule.card_keys
#print axioms KeepRule.countStore_keyMade
#print axioms KeepRule.countStore_fire
#print axioms KeepRule.exists_countStore_commit
#print axioms KeepRule.fireOn_mono
#print axioms KeepRule.fire_mono
#print axioms KeepRule.snapshot_every_order
#print axioms KeepRule.inPlace_every_order
#print axioms PatternRule.matches_iff
#print axioms PatternRule.matchSet_finite
#print axioms Controls.matmulPattern_safe
#print axioms Controls.unsafeRule_infinite
#print axioms Controls.read_order_matters
#print axioms Controls.inPlace_order_matters
#print axioms Controls.orders_enumerate
#print axioms Controls.snapshot_orders_agree
#print axioms KeepRule.exists_order
#print axioms Controls.firing_keeps_prior_output
#print axioms Controls.no_hom_presence_nat
#print axioms Controls.no_hom_int_presence
#print axioms Controls.argmax_not_monotone
#print axioms Controls.argmax_not_homomorphic
#print axioms Controls.argmax_not_keepRule
#print axioms Controls.argmax_not_keepRule_presence

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.GradedStore
