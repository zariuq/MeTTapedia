import Mettapedia.SetTheory.Profiles.Instances
import Mettapedia.SetTheory.Profiles.AntiFoundationViews
import Mettapedia.SetTheory.AntiFoundation.Library

/-!
# The well-founded bubble

Inside any carrier with a membership relation, the **bubble** is the accessible part of
membership: the sets below which membership is well founded.

* **Induction is a theorem about the bubble.** Membership induction holds on the bubble of
  every carrier (`bubble_memInduction`), and the bubble is the largest transitive part with
  that property (`acc_of_transitive_of_memInduction`): any transitive part on which induction
  holds lies inside the bubble.
* **What the bubble drops.** A Quine atom `Ω = {Ω}` is never in a bubble
  (`not_acc_of_quine`). For hypersets, the bubble is exactly `WellFoundedPart`, which is
  Mathlib's `ZFSet` with membership preserved in both directions (`hsetBubble`), and the
  bubble's readout `toZFSet` sends `Ω` to `∅`.
* **The bubble does not depend on the anti-foundation choice.** Proved in general, not only
  on the finite menu of pictures:
  - a decoration of a well-founded graph lands in the bubble (`acc_of_isDecoration`);
  - into any extensional membership, a well-founded graph has at most one decoration
    (`isDecoration_unique_of_acc`), and two nodes receive the same set exactly when they are
    bisimilar (`isDecoration_eq_iff_bisimilar`);
  - a map that decorates one carrier's membership in another carries decorations of
    well-founded graphs to decorations (`IsDecoration.comp`), so any two such views agree on
    every well-founded node (`views_agree_of_acc`).

  Foundation (`ZFSet`), Aczel (`HSet`), and the finite carriers of Scott, Finsler and Boffa
  are all extensional, so they all give a well-founded graph the same decoration. For `HSet`
  and `ZFSet` this is `decorate_eq_ofZFSet`: the hyperset of a well-founded node is the
  `ZFSet` of that node, read as a hyperset. On the finite menu the bubble of every carrier is
  the single empty set (`menuBubbles`).

No choice principle is used in this module; the hyperset comparison inherits only `propext`
and `Quot.sound`.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.CarveOuts

open Mettapedia.SetTheory.Profiles
open Mettapedia.SetTheory.AntiFoundation
open Mettapedia.TypeTheory.MaterialSets
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open Mettapedia.GSLT.QuotientObservers

universe u

/-! ## The bubble of a membership -/

section Bubble

variable {V : Type u} (mem : V → V → Prop)

/-- The bubble of a membership: the sets that are accessible for membership. -/
abbrev Bubble : Type u := {x : V // Acc mem x}

/-- Membership restricted to the bubble. -/
def bubbleMem : Bubble mem → Bubble mem → Prop :=
  fun a b => mem a.1 b.1

variable {mem}

/-- The bubble is transitive: a member of a set in the bubble is in the bubble. -/
theorem bubble_transitive {x y : V} (hx : Acc mem x) (hy : mem y x) : Acc mem y :=
  hx.inv hy

variable (mem)

/-- **Membership induction is a theorem about the bubble.** -/
theorem bubble_memInduction : HasMemInduction (bubbleMem mem) := by
  intro P step s
  rcases s with ⟨x, hx⟩
  induction hx with
  | intro y pred ih =>
    refine step ⟨y, Acc.intro y pred⟩ ?_
    intro z hz
    exact ih z.1 hz

/-- **The bubble is the largest transitive part with membership induction.** -/
theorem acc_of_transitive_of_memInduction (T : V → Prop)
    (transitive : ∀ x y, T x → mem y x → T y)
    (induction : HasMemInduction (fun a b : {x // T x} => mem a.1 b.1)) :
    ∀ x, T x → Acc mem x := by
  intro x hx
  exact induction (fun t => Acc mem t.1)
    (fun t ih => Acc.intro t.1 fun y hy => ih ⟨y, transitive _ _ t.2 hy⟩ hy) ⟨x, hx⟩

variable {mem}

/-- A Quine atom is never in the bubble. -/
theorem not_acc_of_quine {q : V} (quine : IsQuine mem q) : ¬ Acc mem q :=
  not_acc_of_rel_self ((quine q).mpr rfl)

/-- A carrier with a Quine atom is strictly larger than its bubble. -/
theorem exists_not_acc_of_hasQuineAtom (atom : HasQuineAtom mem) : ∃ q, ¬ Acc mem q := by
  obtain ⟨q, hq⟩ := atom
  exact ⟨q, not_acc_of_quine hq⟩

end Bubble

/-! ## Decorations of well-founded graphs -/

section Decorations

universe v w x

/-- `d` decorates the graph `edge` in the membership `mem`: the members of `d a` are the
values of `d` at the children of `a`. This is `AntiFoundation.IsDecoration`, with the graph
and the carrier allowed in different universes (`decorates_iff_isDecoration`). -/
def Decorates {α : Type v} {V : Type w} (edge : α → α → Prop) (mem : V → V → Prop)
    (d : α → V) : Prop :=
  ∀ a y, mem y (d a) ↔ ∃ b, edge a b ∧ y = d b

theorem decorates_iff_isDecoration {α V : Type u} {edge : Edge α} {mem : MemRel V}
    {d : α → V} : Decorates edge mem d ↔ IsDecoration edge mem d :=
  Iff.rfl

variable {α : Type v} {V : Type w} {W : Type x} {edge : α → α → Prop} {mem : V → V → Prop}
  {memW : W → W → Prop}

/-- A decoration sends a well-founded node into the bubble. -/
theorem acc_of_decorates {d : α → V} (hd : Decorates edge mem d) {a : α}
    (ha : Acc (flip edge) a) : Acc mem (d a) := by
  induction ha with
  | intro a _ ih =>
    refine Acc.intro _ fun y hy => ?_
    obtain ⟨b, hb, rfl⟩ := (hd a y).mp hy
    exact ih b hb

/-- Into an extensional membership, two decorations agree at every well-founded node. -/
theorem decorates_unique_of_acc (ext : Extensional mem) {d d' : α → V}
    (hd : Decorates edge mem d) (hd' : Decorates edge mem d') {a : α}
    (ha : Acc (flip edge) a) : d a = d' a := by
  induction ha with
  | intro a _ ih =>
    refine ext _ _ fun z => ?_
    rw [hd a z, hd' a z]
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨b, hb, ih b hb⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨b, hb, (ih b hb).symm⟩

/-- The kernel of any decoration is a bisimulation: nodes with equal values are bisimilar. -/
theorem decorates_kernel_bisimilar {d : α → V} (hd : Decorates edge mem d) {a b : α}
    (h : d a = d b) : Bisimilar edge edge a b := by
  refine IsBisimulation.bisimilar (R := fun x y => d x = d y) ?_ h
  intro x y hxy
  constructor
  · intro x' hx
    have memx : mem (d x') (d x) := (hd x (d x')).mpr ⟨x', hx, rfl⟩
    obtain ⟨y', hy, he⟩ := (hd y (d x')).mp (hxy ▸ memx)
    exact ⟨y', hy, he⟩
  · intro y' hy
    have memy : mem (d y') (d y) := (hd y (d y')).mpr ⟨y', hy, rfl⟩
    obtain ⟨x', hx, he⟩ := (hd x (d y')).mp (hxy.symm ▸ memy)
    exact ⟨x', hx, he.symm⟩

/-- Into an extensional membership, bisimilar well-founded nodes receive the same set. -/
theorem decorates_eq_of_bisimilar (ext : Extensional mem) {d : α → V}
    (hd : Decorates edge mem d) {a : α} (ha : Acc (flip edge) a) :
    ∀ b, Bisimilar edge edge a b → d a = d b := by
  induction ha with
  | intro a _ ih =>
    intro b hab
    refine ext _ _ fun z => ?_
    rw [hd a z, hd b z]
    constructor
    · rintro ⟨a', ha', rfl⟩
      obtain ⟨b', hb', hab'⟩ := hab.exists_child_left ha'
      exact ⟨b', hb', ih a' ha' b' hab'⟩
    · rintro ⟨b', hb', rfl⟩
      obtain ⟨a', ha', hab'⟩ := hab.exists_child_right hb'
      exact ⟨a', ha', (ih a' ha' b' hab').symm⟩

/-- **The kernel of a decoration at a well-founded node.** Into an extensional membership, two
nodes, the first well-founded, receive the same set exactly when they are bisimilar. -/
theorem decorates_eq_iff_bisimilar (ext : Extensional mem) {d : α → V}
    (hd : Decorates edge mem d) {a b : α} (ha : Acc (flip edge) a) :
    d a = d b ↔ Bisimilar edge edge a b :=
  ⟨decorates_kernel_bisimilar hd, decorates_eq_of_bisimilar ext hd ha b⟩

/-- A map that decorates the membership graph of `V` in `W` carries decorations into `V` to
decorations into `W`. -/
theorem Decorates.comp {e : V → W} (he : Decorates (memChild mem) memW e)
    {d : α → V} (hd : Decorates edge mem d) : Decorates edge memW (e ∘ d) := by
  intro a w
  rw [Function.comp_apply, he (d a) w]
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨b, hb, rfl⟩ := (hd a v).mp hv
    exact ⟨b, hb, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨d b, (hd a (d b)).mpr ⟨b, hb, rfl⟩, rfl⟩

/-- **Every view agrees on the well-founded graphs.** Given a decoration of `V`'s membership
in an extensional `W`, a decoration into `V` and a decoration into `W` agree, through that
map, at every well-founded node. -/
theorem views_agree_of_acc (extW : Extensional memW) {e : V → W}
    (he : Decorates (memChild mem) memW e) {d : α → V} {d' : α → W}
    (hd : Decorates edge mem d) (hd' : Decorates edge memW d') {a : α}
    (ha : Acc (flip edge) a) : e (d a) = d' a :=
  decorates_unique_of_acc extW (he.comp hd) hd' ha

end Decorations

/-! ## The hyperset bubble is `ZFSet` -/

section Hypersets

/-- The membership of hypersets is extensional. -/
theorem hset_extensional : Extensional (S := HSet.{u}) (· ∈ ·) :=
  fun _ _ h => HSet.ext h

/-- The membership of `ZFSet` is extensional. -/
theorem zfSet_extensional : Extensional (S := ZFSet.{u}) (· ∈ ·) :=
  fun _ _ h => ZFSet.ext h

/-- `ofZFSet` decorates the membership graph of `ZFSet` in the hypersets. -/
theorem ofZFSet_decorates :
    Decorates (memChild (fun x y : ZFSet.{u} => x ∈ y)) (fun x y : HSet.{u} => x ∈ y)
      HSet.ofZFSet := by
  intro x y
  show y ∈ HSet.ofZFSet x ↔ ∃ z, z ∈ x ∧ y = HSet.ofZFSet z
  rw [HSet.mem_ofZFSet_iff]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, rfl⟩

/-- The hyperset decoration of a graph, in the form of the general scheme. -/
theorem decorate_decorates {α : Type u} (r : α → α → Prop) :
    Decorates r (fun x y : HSet.{u} => x ∈ y) (HSet.decorate r) := by
  intro a y
  show y ∈ HSet.decorate r a ↔ ∃ b, r a b ∧ y = HSet.decorate r b
  rw [HSet.mem_decorate]
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b, hb, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b, hb, rfl⟩

/-- On a well-founded graph, the `ZFSet` readouts of the hyperset decoration decorate the
graph in `ZFSet`. -/
theorem toZFSet_decorate_decorates {α : Type u} {r : α → α → Prop}
    (wf : ∀ a, Acc (flip r) a) :
    Decorates r (fun x y : ZFSet.{u} => x ∈ y) (fun a => HSet.toZFSet (HSet.decorate r a)) := by
  have back : ∀ a, HSet.ofZFSet (HSet.toZFSet (HSet.decorate r a)) = HSet.decorate r a :=
    fun a => HSet.ofZFSet_toZFSet_of_wf (HSet.wf_decorate_iff.mpr (wf a))
  intro a z
  show z ∈ HSet.toZFSet (HSet.decorate r a) ↔
    ∃ b, r a b ∧ z = HSet.toZFSet (HSet.decorate r b)
  rw [← HSet.ofZFSet_mem_ofZFSet_iff, back a, HSet.mem_decorate]
  constructor
  · rintro ⟨b, hb, hz⟩
    refine ⟨b, hb, HSet.ofZFSet_injective ?_⟩
    rw [back b, hz]
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b, hb, (back b).symm⟩

/-- **Foundation and Aczel agree on well-founded graphs.** The hyperset of a well-founded
node is the value of any `ZFSet` decoration at that node, read as a hyperset. -/
theorem decorate_eq_ofZFSet {α : Type u} {r : α → α → Prop} {d : α → ZFSet.{u}}
    (hd : Decorates r (fun x y : ZFSet.{u} => x ∈ y) d) {a : α}
    (ha : Acc (flip r) a) : HSet.ofZFSet (d a) = HSet.decorate r a :=
  views_agree_of_acc hset_extensional ofZFSet_decorates hd (decorate_decorates r) ha

/-- A well-founded graph has exactly one `ZFSet` decoration. -/
theorem existsUnique_zfSet_decoration {α : Type u} {r : α → α → Prop}
    (wf : ∀ a, Acc (flip r) a) :
    ∃! d : α → ZFSet.{u}, Decorates r (fun x y : ZFSet.{u} => x ∈ y) d :=
  ⟨_, toZFSet_decorate_decorates wf, fun _ hd =>
    funext fun a => decorates_unique_of_acc zfSet_extensional hd
      (toZFSet_decorate_decorates wf) (wf a)⟩

/-- The hyperset bubble is the accessible part of hyperset membership. -/
theorem hset_wf_iff_acc (x : HSet.{u}) : x.WF ↔ Acc (fun a b : HSet.{u} => a ∈ b) x :=
  Iff.rfl

/-- **The hyperset bubble, packed.** -/
structure HSetBubble : Prop where
  /-- The bubble is the accessible part of membership. -/
  accessible : ∀ x : HSet.{u}, x.WF ↔ Acc (fun a b : HSet.{u} => a ∈ b) x
  /-- It is transitive. -/
  transitive : ∀ {x y : HSet.{u}}, x.WF → y ∈ x → y.WF
  /-- Membership induction holds on it. -/
  induction : HasMemInduction (fun x y : WellFoundedPart.{u} => x.1 ∈ y.1)
  /-- It is the largest transitive part with membership induction. -/
  largest : ∀ T : HSet.{u} → Prop, (∀ x y, T x → y ∈ x → T y) →
    HasMemInduction (fun a b : {x // T x} => a.1 ∈ b.1) → ∀ x, T x → x.WF
  /-- It is `ZFSet`: the equivalence preserves and reflects membership. -/
  zfSet : ∀ x y : WellFoundedPart.{u},
    x.1 ∈ y.1 ↔ HSet.wellFoundedPartEquivZFSet x ∈ HSet.wellFoundedPartEquivZFSet y
  /-- The carrier has a Quine atom. -/
  quineAtom : HasQuineAtom (S := HSet.{u}) (· ∈ ·)
  /-- The bubble drops it. -/
  quineDropped : ¬ HSet.quineAtom.{u}.WF
  /-- The bubble's readout sends it to the empty set. -/
  quineReadout : HSet.toZFSet HSet.quineAtom.{u} = ∅
  /-- Foundation and Aczel agree on well-founded graphs. -/
  decorationsAgree : ∀ {α : Type u} {r : α → α → Prop} {d : α → ZFSet.{u}},
    Decorates r (fun x y : ZFSet.{u} => x ∈ y) d → ∀ {a : α}, Acc (flip r) a →
      HSet.ofZFSet (d a) = HSet.decorate r a

theorem hsetBubble : HSetBubble.{u} where
  accessible := hset_wf_iff_acc
  transitive hx hy := hx.mem hy
  induction := wellFoundedPart_memInduction
  largest T transitive induction :=
    acc_of_transitive_of_memInduction (fun a b : HSet.{u} => a ∈ b) T transitive induction
  zfSet _ _ := wellFoundedPart_mem_iff_zfSet
  quineAtom := hset_hasQuineAtom
  quineDropped := HSet.not_wf_quineAtom
  quineReadout := HSet.toZFSet_quineAtom
  decorationsAgree hd _ ha := decorate_eq_ofZFSet hd ha

end Hypersets

/-! ## On the finite menu -/

/-- The finite Scott carrier receives Aczel's by a decoration of its membership graph. -/
theorem afaToSafa_isDecoration : IsDecoration (memChild aMem) sMem afaToSafa := by
  intro x y
  constructor
  · intro h
    cases x <;> cases y <;>
      first
      | exact h.elim
      | exact ⟨.empty, trivial, rfl⟩
      | exact ⟨.omega, trivial, rfl⟩
      | exact ⟨.nest, trivial, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    cases x <;> cases b <;> first | exact hb.elim | exact trivial

/-- Scott's finite carrier is extensional. -/
theorem sSet_extensional : Extensional sMem := by
  intro x y h
  cases x <;> cases y <;>
    first
    | rfl
    | exact ((h .empty).mp trivial).elim
    | exact ((h .empty).mpr trivial).elim
    | exact ((h .omega).mp trivial).elim
    | exact ((h .omega).mpr trivial).elim
    | exact ((h .nest).mp trivial).elim
    | exact ((h .nest).mpr trivial).elim
    | exact ((h .self).mp trivial).elim
    | exact ((h .self).mpr trivial).elim
    | exact ((h .finT).mp trivial).elim
    | exact ((h .finT).mpr trivial).elim
    | exact ((h .finS).mp trivial).elim
    | exact ((h .finS).mpr trivial).elim

/-- Aczel's and Scott's finite carriers give a well-founded graph the same decoration. -/
theorem afa_safa_agree_of_acc {α : Type} {edge : Edge α} {d : α → ASet} {d' : α → SSet}
    (hd : IsDecoration edge aMem d) (hd' : IsDecoration edge sMem d') {a : α}
    (ha : Acc (flip edge) a) : afaToSafa (d a) = d' a :=
  views_agree_of_acc sSet_extensional (decorates_iff_isDecoration.mpr afaToSafa_isDecoration)
    (decorates_iff_isDecoration.mpr hd) (decorates_iff_isDecoration.mpr hd') ha

/-- On the finite menu, every view's bubble is its empty set alone, and every view gives the
empty picture that set. -/
structure MenuBubbles : Prop where
  foundation : HasMemInduction foundMem
  aczel : ∀ x : ASet, Acc aMem x ↔ x = .empty
  scott : ∀ x : SSet, Acc sMem x ↔ x = .empty
  finsler : ∀ x : FSet, Acc fMem x ↔ x = .empty
  boffa : ∀ x : BSet, Acc bMem x ↔ x = .empty
  emptyAgrees : denoteFoundation .empty = some .empty ∧ denoteAFA .empty = .empty ∧
    denoteSAFA .empty = .empty ∧ denoteFAFA .empty = .empty ∧ denoteBAFA .empty = .empty

theorem menuBubbles : MenuBubbles where
  foundation := found_induction
  aczel := aSet_acc_iff
  scott := sSet_acc_iff
  finsler := fSet_acc_iff
  boffa := bSet_acc_iff
  emptyAgrees := all_agree_empty

end Mettapedia.SetTheory.CarveOuts
