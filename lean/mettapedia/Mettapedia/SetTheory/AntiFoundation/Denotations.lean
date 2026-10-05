import Mettapedia.SetTheory.AntiFoundation.Core
import Mettapedia.SetTheory.AntiFoundation.Graphs
import Mettapedia.SetTheory.Profiles.Foundation

/-!
# Finite carriers for the five views

Each axiom is read on the same finite menu of pictures. The carrier is only as
large as the distinctions that axiom keeps.

* `ASet` keeps the empty set, the Quine atom `Ω = {Ω}`, and the nest `x = {∅, x}`.
  Membership is strongly extensional, so a graph has at most one decoration.
* `SSet` adds the Scott set `s = {Ω, s}` and the collapsed Finsler pair.
* `FSet` adds the three-element Finsler picture and keeps the collapsed pair.
* `BSet` adds a second Quine atom and an exact picture of the two-cycle.
* `FoundSet` is one empty point. The loop and the nest have no decoration.

These are not the full universes. In each anti-foundation carrier the only
accessible point is the empty set: the well-founded part is that point, and
membership induction holds there. A Quine atom refutes induction on the whole
carrier. Embeddings between the carriers preserve membership. The canonical
embeddings of the full universes, and a proper class of Quine atoms, are the
claims in Aczel and are not proved here.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.AntiFoundation

open Mettapedia.SetTheory.Profiles
open Mettapedia.GSLT.QuotientObservers
open Mettapedia.TypeTheory.MaterialSets.Hypersets

/-! ## Accessibility -/

/-- A self-member is not accessible. -/
theorem not_acc_of_loop {α : Type} {r : α → α → Prop} {x : α} (loop : r x x) : ¬ Acc r x := by
  intro accessible
  revert loop
  induction accessible with
  | intro y _ ih => exact fun loopAt => ih y loopAt loopAt

/-- Membership induction holds on the accessible part of any membership. -/
theorem wf_part_induction {V : Type} (mem : V → V → Prop) :
    HasMemInduction (fun a b : {x : V // Acc mem x} => mem a.1 b.1) := by
  intro P step s
  rcases s with ⟨_, hx⟩
  induction hx with
  | intro y pred ih =>
    refine step ⟨y, Acc.intro y pred⟩ ?_
    intro z hz
    have eq : (⟨z.1, pred z.1 hz⟩ : {w // Acc mem w}) = z := Subtype.ext rfl
    exact eq ▸ ih z.1 hz

/-! ## Aczel's carrier -/

inductive ASet where
  | empty
  | omega
  | nest
  deriving DecidableEq

/-- `aMem m s` means `m` is a member of `s`. -/
def aMem : ASet → ASet → Prop
  | .omega, .omega => True
  | .empty, .nest => True
  | .nest, .nest => True
  | _, _ => False

theorem a_omega_quine : IsQuine aMem .omega := by
  intro y
  cases y <;> constructor <;> intro h <;> first | rfl | exact trivial | exact h.elim | cases h

theorem aSet_quine_iff (x : ASet) : IsQuine aMem x ↔ x = .omega := by
  constructor
  · intro hx
    cases x with
    | omega => rfl
    | empty => exact ((hx .empty).mpr rfl).elim
    | nest => cases (hx .empty).mp trivial
  · intro h
    cases h
    exact a_omega_quine

theorem aSet_one_quine : ∃ q : ASet, IsQuine aMem q ∧ ∀ q', IsQuine aMem q' → q' = q :=
  ⟨.omega, a_omega_quine, fun q' hq => (aSet_quine_iff q').mp hq⟩

theorem aSet_has_quine : HasQuineAtom aMem :=
  ⟨.omega, a_omega_quine⟩

theorem aSet_refutes_induction : ¬ HasMemInduction aMem :=
  quineAtom_refutes_induction aSet_has_quine

theorem aSet_strong : StronglyExtensional (memChild aMem) := by
  intro R hR x y hxy
  cases x with
  | empty =>
    cases y with
    | empty => rfl
    | omega =>
      obtain ⟨b, hb, _⟩ := (hR hxy).2 .omega trivial
      cases b <;> exact hb.elim
    | nest =>
      obtain ⟨b, hb, _⟩ := (hR hxy).2 .empty trivial
      cases b <;> exact hb.elim
  | omega =>
    cases y with
    | empty =>
      obtain ⟨b, hb, _⟩ := (hR hxy).1 .omega trivial
      cases b <;> exact hb.elim
    | omega => rfl
    | nest =>
      obtain ⟨a', ha, hrel⟩ := (hR hxy).2 .empty trivial
      cases a' with
      | empty => exact ha.elim
      | nest => exact ha.elim
      | omega =>
        obtain ⟨b, hb, _⟩ := (hR hrel).1 .omega trivial
        cases b <;> exact hb.elim
  | nest =>
    cases y with
    | empty =>
      obtain ⟨a', ha, _⟩ := (hR hxy).1 .empty trivial
      cases a' <;> exact ha.elim
    | omega =>
      obtain ⟨b', hb, hrel⟩ := (hR hxy).1 .empty trivial
      cases b' with
      | empty => exact hb.elim
      | nest => exact hb.elim
      | omega =>
        obtain ⟨a', ha, _⟩ := (hR hrel).2 .omega trivial
        cases a' <;> exact ha.elim
    | nest => rfl

theorem aSet_acc_empty : Acc aMem ASet.empty :=
  Acc.intro ASet.empty fun y hy => by cases y <;> exact hy.elim

theorem aSet_acc_iff (x : ASet) : Acc aMem x ↔ x = .empty := by
  constructor
  · intro hx
    cases x with
    | empty => rfl
    | omega => exact False.elim (not_acc_of_loop trivial hx)
    | nest => exact False.elim (not_acc_of_loop trivial hx)
  · rintro rfl
    exact aSet_acc_empty

/-- A graph decorated in `ASet` has one canonical bisimilarity-decoration. -/
theorem afa_canonical_of_decoration {α : Type} {edge : Edge α} {d : α → ASet}
    (hd : IsDecoration edge aMem d) :
    CanonicalAxiom edge (Bisimilar edge edge) aMem := by
  refine ⟨d, ⟨hd, respects_regular_of_strong (.bisimilarity edge) hd aSet_strong,
      fun a b h => decoration_kernel_bisim hd h⟩, ?_⟩
  intro d' hd' a
  exact (unique_decoration_of_strong hd hd'.decoration aSet_strong a).symm

/-! ## Scott's carrier -/

inductive SSet where
  | empty
  | omega
  | nest
  | self
  | finT
  | finS
  deriving DecidableEq

def sMem : SSet → SSet → Prop
  | .omega, .omega => True
  | .empty, .nest => True
  | .nest, .nest => True
  | .omega, .self => True
  | .self, .self => True
  | .finS, .finT => True
  | .finT, .finS => True
  | .finS, .finS => True
  | _, _ => False

theorem sMem_omega (y : SSet) : sMem y .omega ↔ y = .omega := by
  cases y <;> constructor <;> intro h <;> first | rfl | exact trivial | exact h.elim | cases h

theorem sMem_finT (y : SSet) : sMem y .finT ↔ y = .finS := by
  cases y <;> constructor <;> intro h <;> first | rfl | exact trivial | exact h.elim | cases h

theorem sMem_self (y : SSet) : sMem y .self ↔ y = .omega ∨ y = .self := by
  match y with
  | .omega => exact ⟨fun _ => Or.inl rfl, fun _ => trivial⟩
  | .self => exact ⟨fun _ => Or.inr rfl, fun _ => trivial⟩
  | .empty | .nest | .finT | .finS =>
    exact ⟨fun h => h.elim, fun h => by
      cases h with
      | inl eq => cases eq
      | inr eq => cases eq⟩

theorem sMem_finS (y : SSet) : sMem y .finS ↔ y = .finT ∨ y = .finS := by
  match y with
  | .finT => exact ⟨fun _ => Or.inl rfl, fun _ => trivial⟩
  | .finS => exact ⟨fun _ => Or.inr rfl, fun _ => trivial⟩
  | .empty | .omega | .nest | .self =>
    exact ⟨fun h => h.elim, fun h => by
      cases h with
      | inl eq => cases eq
      | inr eq => cases eq⟩

theorem s_omega_quine : IsQuine sMem .omega := sMem_omega

theorem sSet_quine_iff (x : SSet) : IsQuine sMem x ↔ x = .omega := by
  constructor
  · intro hx
    cases x with
    | omega => rfl
    | empty => exact ((hx .empty).mpr rfl).elim
    | nest => cases (hx .empty).mp trivial
    | self => cases (hx .omega).mp trivial
    | finT => cases (hx .finS).mp trivial
    | finS => cases (hx .finT).mp trivial
  · intro h
    cases h
    exact s_omega_quine

theorem sSet_has_quine : HasQuineAtom sMem :=
  ⟨.omega, s_omega_quine⟩

theorem sSet_refutes_induction : ¬ HasMemInduction sMem :=
  quineAtom_refutes_induction sSet_has_quine

theorem sSet_unique_member (x : SSet) (h : ∃! y, sMem y x) : x = .omega ∨ x = .finT := by
  obtain ⟨y, hy, only⟩ := h
  cases x with
  | omega => exact Or.inl rfl
  | finT => exact Or.inr rfl
  | empty => cases y <;> exact hy.elim
  | nest => cases (only .empty trivial).trans (only .nest trivial).symm
  | self => cases (only .omega trivial).trans (only .self trivial).symm
  | finS => cases (only .finT trivial).trans (only .finS trivial).symm

theorem sSet_acc_empty : Acc sMem SSet.empty :=
  Acc.intro SSet.empty fun y hy => by cases y <;> exact hy.elim

theorem sSet_acc_iff (x : SSet) : Acc sMem x ↔ x = .empty := by
  constructor
  · intro hx
    cases x with
    | empty => rfl
    | omega => exact False.elim (not_acc_of_loop trivial hx)
    | nest => exact False.elim (not_acc_of_loop trivial hx)
    | self => exact False.elim (not_acc_of_loop trivial hx)
    | finS => exact False.elim (not_acc_of_loop trivial hx)
    | finT =>
      have loop : sMem SSet.finS SSet.finS := trivial
      have step : sMem SSet.finS SSet.finT := trivial
      exact False.elim (not_acc_of_loop loop (hx.inv step))
  · rintro rfl
    exact sSet_acc_empty

/-! ## Finsler's carrier -/

inductive FSet where
  | empty
  | omega
  | nest
  | self
  | f0
  | f1
  | f2
  | colT
  | colS
  deriving DecidableEq

def fMem : FSet → FSet → Prop
  | .omega, .omega => True
  | .empty, .nest => True
  | .nest, .nest => True
  | .omega, .self => True
  | .self, .self => True
  | .f1, .f0 => True
  | .f0, .f1 => True
  | .f2, .f1 => True
  | .f0, .f2 => True
  | .f1, .f2 => True
  | .colS, .colT => True
  | .colT, .colS => True
  | .colS, .colS => True
  | _, _ => False

theorem fMem_omega (y : FSet) : fMem y .omega ↔ y = .omega := by
  cases y <;> constructor <;> intro h <;> first | rfl | exact trivial | exact h.elim | cases h

theorem fMem_f0 (y : FSet) : fMem y .f0 ↔ y = .f1 := by
  cases y <;> constructor <;> intro h <;> first | rfl | exact trivial | exact h.elim | cases h

theorem fMem_colT (y : FSet) : fMem y .colT ↔ y = .colS := by
  cases y <;> constructor <;> intro h <;> first | rfl | exact trivial | exact h.elim | cases h

theorem fMem_self (y : FSet) : fMem y .self ↔ y = .omega ∨ y = .self := by
  match y with
  | .omega => exact ⟨fun _ => Or.inl rfl, fun _ => trivial⟩
  | .self => exact ⟨fun _ => Or.inr rfl, fun _ => trivial⟩
  | .empty | .nest | .f0 | .f1 | .f2 | .colT | .colS =>
    exact ⟨fun h => h.elim, fun h => by
      cases h with
      | inl eq => cases eq
      | inr eq => cases eq⟩

theorem fMem_f1 (y : FSet) : fMem y .f1 ↔ y = .f0 ∨ y = .f2 := by
  match y with
  | .f0 => exact ⟨fun _ => Or.inl rfl, fun _ => trivial⟩
  | .f2 => exact ⟨fun _ => Or.inr rfl, fun _ => trivial⟩
  | .empty | .omega | .nest | .self | .f1 | .colT | .colS =>
    exact ⟨fun h => h.elim, fun h => by
      cases h with
      | inl eq => cases eq
      | inr eq => cases eq⟩

theorem fMem_f2 (y : FSet) : fMem y .f2 ↔ y = .f0 ∨ y = .f1 := by
  match y with
  | .f0 => exact ⟨fun _ => Or.inl rfl, fun _ => trivial⟩
  | .f1 => exact ⟨fun _ => Or.inr rfl, fun _ => trivial⟩
  | .empty | .omega | .nest | .self | .f2 | .colT | .colS =>
    exact ⟨fun h => h.elim, fun h => by
      cases h with
      | inl eq => cases eq
      | inr eq => cases eq⟩

theorem fMem_colS (y : FSet) : fMem y .colS ↔ y = .colT ∨ y = .colS := by
  match y with
  | .colT => exact ⟨fun _ => Or.inl rfl, fun _ => trivial⟩
  | .colS => exact ⟨fun _ => Or.inr rfl, fun _ => trivial⟩
  | .empty | .omega | .nest | .self | .f0 | .f1 | .f2 =>
    exact ⟨fun h => h.elim, fun h => by
      cases h with
      | inl eq => cases eq
      | inr eq => cases eq⟩

theorem f_omega_quine : IsQuine fMem .omega := fMem_omega

theorem fSet_quine_iff (x : FSet) : IsQuine fMem x ↔ x = .omega := by
  constructor
  · intro hx
    cases x with
    | omega => rfl
    | empty => exact ((hx .empty).mpr rfl).elim
    | nest => cases (hx .empty).mp trivial
    | self => cases (hx .omega).mp trivial
    | f0 => cases (hx .f1).mp trivial
    | f1 => cases (hx .f0).mp trivial
    | f2 => cases (hx .f0).mp trivial
    | colT => cases (hx .colS).mp trivial
    | colS => cases (hx .colT).mp trivial
  · intro h
    cases h
    exact f_omega_quine

theorem fSet_has_quine : HasQuineAtom fMem :=
  ⟨.omega, f_omega_quine⟩

theorem fSet_refutes_induction : ¬ HasMemInduction fMem :=
  quineAtom_refutes_induction fSet_has_quine

theorem fSet_unique_member (x : FSet) (h : ∃! y, fMem y x) :
    x = .omega ∨ x = .f0 ∨ x = .colT := by
  obtain ⟨y, hy, only⟩ := h
  cases x with
  | omega => exact Or.inl rfl
  | f0 => exact Or.inr (Or.inl rfl)
  | colT => exact Or.inr (Or.inr rfl)
  | empty => cases y <;> exact hy.elim
  | nest => cases (only .empty trivial).trans (only .nest trivial).symm
  | self => cases (only .omega trivial).trans (only .self trivial).symm
  | f1 => cases (only .f0 trivial).trans (only .f2 trivial).symm
  | f2 => cases (only .f0 trivial).trans (only .f1 trivial).symm
  | colS => cases (only .colT trivial).trans (only .colS trivial).symm

theorem f_acc_not_finsler (x : FSet) (hx : Acc fMem x) : x ≠ .f0 ∧ x ≠ .f1 ∧ x ≠ .f2 := by
  induction hx with
  | intro y _ ih =>
    refine ⟨?_, ?_, ?_⟩
    · intro hy
      exact (ih .f1 (hy.symm ▸ (trivial : fMem .f1 .f0))).2.1 rfl
    · intro hy
      exact (ih .f2 (hy.symm ▸ (trivial : fMem .f2 .f1))).2.2 rfl
    · intro hy
      exact (ih .f0 (hy.symm ▸ (trivial : fMem .f0 .f2))).1 rfl

theorem fSet_acc_empty : Acc fMem FSet.empty :=
  Acc.intro FSet.empty fun y hy => by cases y <;> exact hy.elim

theorem fSet_acc_iff (x : FSet) : Acc fMem x ↔ x = .empty := by
  constructor
  · intro hx
    cases x with
    | empty => rfl
    | omega => exact False.elim (not_acc_of_loop trivial hx)
    | nest => exact False.elim (not_acc_of_loop trivial hx)
    | self => exact False.elim (not_acc_of_loop trivial hx)
    | colS => exact False.elim (not_acc_of_loop trivial hx)
    | colT =>
      have loop : fMem FSet.colS FSet.colS := trivial
      have step : fMem FSet.colS FSet.colT := trivial
      exact False.elim (not_acc_of_loop loop (hx.inv step))
    | f0 => exact False.elim ((f_acc_not_finsler .f0 hx).1 rfl)
    | f1 => exact False.elim ((f_acc_not_finsler .f1 hx).2.1 rfl)
    | f2 => exact False.elim ((f_acc_not_finsler .f2 hx).2.2 rfl)
  · rintro rfl
    exact fSet_acc_empty

/-! ## Boffa's carrier -/

inductive BSet where
  | empty
  | atomA
  | atomB
  | nest
  | self
  | f0
  | f1
  | f2
  | colT
  | colS
  | cycL
  | cycR
  deriving DecidableEq

def bMem : BSet → BSet → Prop
  | .atomA, .atomA => True
  | .atomB, .atomB => True
  | .empty, .nest => True
  | .nest, .nest => True
  | .atomA, .self => True
  | .self, .self => True
  | .f1, .f0 => True
  | .f0, .f1 => True
  | .f2, .f1 => True
  | .f0, .f2 => True
  | .f1, .f2 => True
  | .colS, .colT => True
  | .colT, .colS => True
  | .colS, .colS => True
  | .cycR, .cycL => True
  | .cycL, .cycR => True
  | _, _ => False

theorem b_atomA_quine : IsQuine bMem .atomA := by
  intro y
  cases y <;> constructor <;> intro h <;> first | rfl | exact trivial | exact h.elim | cases h

theorem b_atomB_quine : IsQuine bMem .atomB := by
  intro y
  cases y <;> constructor <;> intro h <;> first | rfl | exact trivial | exact h.elim | cases h

theorem bSet_two_quines :
    IsQuine bMem BSet.atomA ∧ IsQuine bMem BSet.atomB ∧ BSet.atomA ≠ BSet.atomB :=
  ⟨b_atomA_quine, b_atomB_quine, by intro h; cases h⟩

theorem bSet_has_quine : HasQuineAtom bMem :=
  ⟨.atomA, b_atomA_quine⟩

theorem bSet_refutes_induction : ¬ HasMemInduction bMem :=
  quineAtom_refutes_induction bSet_has_quine

theorem bMem_cycL (y : BSet) : bMem y .cycL ↔ y = .cycR := by
  cases y <;> constructor <;> intro h <;> first | rfl | exact trivial | exact h.elim | cases h

theorem bMem_cycR (y : BSet) : bMem y .cycR ↔ y = .cycL := by
  cases y <;> constructor <;> intro h <;> first | rfl | exact trivial | exact h.elim | cases h

theorem b_acc_not_finsler (x : BSet) (hx : Acc bMem x) : x ≠ .f0 ∧ x ≠ .f1 ∧ x ≠ .f2 := by
  induction hx with
  | intro y _ ih =>
    refine ⟨?_, ?_, ?_⟩
    · intro hy
      exact (ih .f1 (hy.symm ▸ (trivial : bMem .f1 .f0))).2.1 rfl
    · intro hy
      exact (ih .f2 (hy.symm ▸ (trivial : bMem .f2 .f1))).2.2 rfl
    · intro hy
      exact (ih .f0 (hy.symm ▸ (trivial : bMem .f0 .f2))).1 rfl

theorem b_acc_not_cycle (x : BSet) (hx : Acc bMem x) : x ≠ .cycL ∧ x ≠ .cycR := by
  induction hx with
  | intro y _ ih =>
    refine ⟨?_, ?_⟩
    · intro hy
      exact (ih .cycR (hy.symm ▸ (trivial : bMem .cycR .cycL))).2 rfl
    · intro hy
      exact (ih .cycL (hy.symm ▸ (trivial : bMem .cycL .cycR))).1 rfl

theorem bSet_acc_empty : Acc bMem BSet.empty :=
  Acc.intro BSet.empty fun y hy => by cases y <;> exact hy.elim

theorem bSet_acc_iff (x : BSet) : Acc bMem x ↔ x = .empty := by
  constructor
  · intro hx
    cases x with
    | empty => rfl
    | atomA => exact False.elim (not_acc_of_loop trivial hx)
    | atomB => exact False.elim (not_acc_of_loop trivial hx)
    | nest => exact False.elim (not_acc_of_loop trivial hx)
    | self => exact False.elim (not_acc_of_loop trivial hx)
    | colS => exact False.elim (not_acc_of_loop trivial hx)
    | colT =>
      have loop : bMem BSet.colS BSet.colS := trivial
      have step : bMem BSet.colS BSet.colT := trivial
      exact False.elim (not_acc_of_loop loop (hx.inv step))
    | f0 => exact False.elim ((b_acc_not_finsler .f0 hx).1 rfl)
    | f1 => exact False.elim ((b_acc_not_finsler .f1 hx).2.1 rfl)
    | f2 => exact False.elim ((b_acc_not_finsler .f2 hx).2.2 rfl)
    | cycL => exact False.elim ((b_acc_not_cycle .cycL hx).1 rfl)
    | cycR => exact False.elim ((b_acc_not_cycle .cycR hx).2 rfl)
  · rintro rfl
    exact bSet_acc_empty

/-! ## Foundation's carrier -/

inductive FoundSet where
  | empty
  deriving DecidableEq

def foundMem : FoundSet → FoundSet → Prop
  | _, _ => False

theorem found_induction : HasMemInduction foundMem := by
  intro P step x
  cases x
  exact step .empty fun y hy => hy.elim

theorem found_no_quine : ¬ HasQuineAtom foundMem := by
  intro ⟨q, hq⟩
  cases q
  exact ((hq .empty).mpr rfl).elim

theorem foundation_loop_none (d : Loop → FoundSet) : ¬ IsDecoration loopEdge foundMem d := by
  intro hd
  have hq := (loop_decoration_iff (fun a => by cases a; rfl) trivial d).mp hd
  cases d .node
  exact ((hq .empty).mpr rfl).elim

theorem foundation_nest_none (d : Nest → FoundSet) : ¬ IsDecoration nestEdge foundMem d := by
  intro hd
  have h := (hd .point .empty).mpr ⟨.blank, trivial, by cases d .blank; rfl⟩
  exact h.elim

/-! ## Embeddings of the finite carriers -/

def afaToSafa : ASet → SSet
  | .empty => .empty
  | .omega => .omega
  | .nest => .nest

def safaToFafa : SSet → FSet
  | .empty => .empty
  | .omega => .omega
  | .nest => .nest
  | .self => .self
  | .finT => .colT
  | .finS => .colS

def fafaToBafa : FSet → BSet
  | .empty => .empty
  | .omega => .atomA
  | .nest => .nest
  | .self => .self
  | .f0 => .f0
  | .f1 => .f1
  | .f2 => .f2
  | .colT => .colT
  | .colS => .colS

theorem afaToSafa_mem (x y : ASet) : aMem x y ↔ sMem (afaToSafa x) (afaToSafa y) := by
  cases x <;> cases y <;> exact Iff.rfl

theorem afaToSafa_inj {x y : ASet} (h : afaToSafa x = afaToSafa y) : x = y := by
  cases x <;> cases y <;> cases h <;> rfl

theorem safaToFafa_mem (x y : SSet) : sMem x y ↔ fMem (safaToFafa x) (safaToFafa y) := by
  cases x <;> cases y <;> exact Iff.rfl

theorem safaToFafa_inj {x y : SSet} (h : safaToFafa x = safaToFafa y) : x = y := by
  cases x <;> cases y <;> cases h <;> rfl

theorem fafaToBafa_mem (x y : FSet) : fMem x y ↔ bMem (fafaToBafa x) (fafaToBafa y) := by
  cases x <;> cases y <;> exact Iff.rfl

theorem fafaToBafa_inj {x y : FSet} (h : fafaToBafa x = fafaToBafa y) : x = y := by
  cases x <;> cases y <;> cases h <;> rfl

/-! ## The menu of pictures -/

inductive Pic where
  | empty
  | loopA
  | loopB
  | cycL
  | cycR
  | scott0
  | scott1
  | fin0
  | fin1
  | fin2
  | nest
  deriving DecidableEq

def denoteAFA : Pic → ASet
  | .empty => .empty
  | .nest => .nest
  | _ => .omega

def denoteSAFA : Pic → SSet
  | .empty => .empty
  | .nest => .nest
  | .scott1 => .self
  | .fin0 => .finT
  | .fin1 => .finS
  | .fin2 => .finS
  | _ => .omega

def denoteFAFA : Pic → FSet
  | .empty => .empty
  | .nest => .nest
  | .scott1 => .self
  | .fin0 => .f0
  | .fin1 => .f1
  | .fin2 => .f2
  | _ => .omega

def denoteBAFA : Pic → BSet
  | .empty => .empty
  | .nest => .nest
  | .loopA => .atomA
  | .loopB => .atomB
  | .scott0 => .atomA
  | .scott1 => .self
  | .cycL => .cycL
  | .cycR => .cycR
  | .fin0 => .f0
  | .fin1 => .f1
  | .fin2 => .f2

/-- Foundation keeps the empty picture and refuses every other picture on this menu. -/
def denoteFoundation : Pic → Option FoundSet
  | .empty => some .empty
  | _ => none

/-! ## Decorations -/

theorem empty_afa : IsDecoration emptyEdge aMem (fun _ => .empty) := by
  intro _ y
  constructor
  · intro hy
    cases y <;> exact hy.elim
  · intro ⟨_, hb, _⟩
    exact hb.elim

theorem loop_afa : IsDecoration loopEdge aMem (fun _ => .omega) :=
  isDecoration_const_quine loop_has_child a_omega_quine

theorem loop_safa : IsDecoration loopEdge sMem (fun _ => .omega) :=
  isDecoration_const_quine loop_has_child s_omega_quine

theorem loop_fafa : IsDecoration loopEdge fMem (fun _ => .omega) :=
  isDecoration_const_quine loop_has_child f_omega_quine

theorem loop_bafa_a : IsDecoration loopEdge bMem (fun _ => .atomA) :=
  isDecoration_const_quine loop_has_child b_atomA_quine

theorem loop_bafa_b : IsDecoration loopEdge bMem (fun _ => .atomB) :=
  isDecoration_const_quine loop_has_child b_atomB_quine

theorem loop_unique_value {V : Type} {mem : V → V → Prop} {q : V}
    (onlyQ : ∀ x, IsQuine mem x → x = q) (d : Loop → V)
    (hd : IsDecoration loopEdge mem d) : d .node = q :=
  onlyQ _ ((loop_decoration_iff (fun a => by cases a; rfl) trivial d).mp hd)

theorem loop_unique_afa (d : Loop → ASet) (hd : IsDecoration loopEdge aMem d) :
    d .node = .omega :=
  loop_unique_value (fun x hx => (aSet_quine_iff x).mp hx) d hd

theorem loop_unique_safa (d : Loop → SSet) (hd : IsDecoration loopEdge sMem d) :
    d .node = .omega :=
  loop_unique_value (fun x hx => (sSet_quine_iff x).mp hx) d hd

theorem loop_unique_fafa (d : Loop → FSet) (hd : IsDecoration loopEdge fMem d) :
    d .node = .omega :=
  loop_unique_value (fun x hx => (fSet_quine_iff x).mp hx) d hd

theorem loop_not_unique_bafa :
    ∃ d d' : Loop → BSet, IsDecoration loopEdge bMem d ∧ IsDecoration loopEdge bMem d' ∧
      d .node ≠ d' .node :=
  ⟨fun _ => .atomA, fun _ => .atomB, loop_bafa_a, loop_bafa_b, by intro h; cases h⟩

theorem respects_eq {α V : Type} (d : α → V) : Respects (fun a b : α => a = b) d :=
  fun _ _ h => congrArg d h

theorem bafa_loop_not_canonical :
    ¬ CanonicalAxiom loopEdge (fun a b : Loop => a = b) bMem := by
  intro h
  obtain ⟨_, _, unique⟩ := h
  have hA : CanonicalDecoration loopEdge (fun a b : Loop => a = b) bMem (fun _ => .atomA) :=
    ⟨loop_bafa_a, respects_eq _, fun a b _ => by cases a; cases b; rfl⟩
  have hB : CanonicalDecoration loopEdge (fun a b : Loop => a = b) bMem (fun _ => .atomB) :=
    ⟨loop_bafa_b, respects_eq _, fun a b _ => by cases a; cases b; rfl⟩
  exact absurd ((unique _ hA Loop.node).trans (unique _ hB Loop.node).symm)
    (by intro eq; cases eq)

def nestAfa : Nest → ASet
  | .blank => .empty
  | .point => .nest

theorem nest_afa : IsDecoration nestEdge aMem nestAfa := by
  intro a y
  cases a with
  | blank =>
    constructor
    · intro hy
      cases y <;> exact hy.elim
    · intro ⟨b, hb, _⟩
      cases b <;> exact hb.elim
  | point =>
    cases y with
    | empty => exact ⟨fun _ => ⟨.blank, trivial, rfl⟩, fun _ => trivial⟩
    | nest => exact ⟨fun _ => ⟨.point, trivial, rfl⟩, fun _ => trivial⟩
    | omega => exact ⟨fun h => h.elim, fun ⟨b, _, eq⟩ => by cases b <;> cases eq⟩

theorem afa_loop_canonical : CanonicalAxiom loopEdge (Bisimilar loopEdge loopEdge) aMem :=
  afa_canonical_of_decoration loop_afa

theorem afa_nest_canonical : CanonicalAxiom nestEdge (Bisimilar nestEdge nestEdge) aMem :=
  afa_canonical_of_decoration nest_afa

theorem afa_empty_canonical :
    CanonicalAxiom emptyEdge (Bisimilar emptyEdge emptyEdge) aMem :=
  afa_canonical_of_decoration empty_afa

theorem cycle_afa : IsDecoration cycleEdge aMem (fun _ => .omega) :=
  isDecoration_const_quine cycle_has_child a_omega_quine

theorem scott_afa : IsDecoration scottEdge aMem (fun _ => .omega) :=
  isDecoration_const_quine scott_has_child a_omega_quine

theorem fin_afa : IsDecoration finEdge aMem (fun _ => .omega) :=
  isDecoration_const_quine fin_has_child a_omega_quine

theorem afa_cycle_canonical : CanonicalAxiom cycleEdge (Bisimilar cycleEdge cycleEdge) aMem :=
  afa_canonical_of_decoration cycle_afa

theorem afa_scott_canonical : CanonicalAxiom scottEdge (Bisimilar scottEdge scottEdge) aMem :=
  afa_canonical_of_decoration scott_afa

theorem afa_fin_canonical : CanonicalAxiom finEdge (Bisimilar finEdge finEdge) aMem :=
  afa_canonical_of_decoration fin_afa

def scottSafa : Scott → SSet
  | .s0 => .omega
  | .s1 => .self

theorem scottSafa_decoration : IsDecoration scottEdge sMem scottSafa := by
  intro a y
  cases a with
  | s0 =>
    unfold scottSafa
    rw [sMem_omega]
    constructor
    · intro h
      exact ⟨.s0, trivial, h⟩
    · intro ⟨b, hb, eq⟩
      cases b with
      | s0 => exact eq
      | s1 => exact hb.elim
  | s1 =>
    unfold scottSafa
    rw [sMem_self]
    constructor
    · intro h
      cases h with
      | inl h => exact ⟨.s0, trivial, h⟩
      | inr h => exact ⟨.s1, trivial, h⟩
    · intro ⟨b, _, eq⟩
      cases b with
      | s0 => exact Or.inl eq
      | s1 => exact Or.inr eq

theorem scott_collapse_safa : IsDecoration scottEdge sMem (fun _ => .omega) :=
  isDecoration_const_quine scott_has_child s_omega_quine

theorem scott_two_solutions :
    ∃ d d' : Scott → SSet, IsDecoration scottEdge sMem d ∧ IsDecoration scottEdge sMem d' ∧
      d .s1 ≠ d' .s1 :=
  ⟨scottSafa, fun _ => .omega, scottSafa_decoration, scott_collapse_safa, by intro h; cases h⟩

theorem scott_classified (d : Scott → SSet) (hd : IsDecoration scottEdge sMem d) :
    d .s0 = .omega ∧ (d .s1 = .omega ∨ d .s1 = .self) := by
  have hq : IsQuine sMem (d .s0) := by
    intro y
    constructor
    · intro hy
      obtain ⟨b, hb, eq⟩ := (hd .s0 y).mp hy
      cases b with
      | s0 => exact eq
      | s1 => exact hb.elim
    · intro hy
      exact (hd .s0 y).mpr ⟨.s0, trivial, hy⟩
  refine ⟨(sSet_quine_iff _).mp hq, ?_⟩
  have memOmega : sMem .omega (d .s1) :=
    (hd .s1 .omega).mpr ⟨.s0, trivial, ((sSet_quine_iff _).mp hq).symm⟩
  cases h1 : d .s1 with
  | omega => exact Or.inl rfl
  | self => exact Or.inr rfl
  | empty => exact (h1 ▸ memOmega).elim
  | nest => exact (h1 ▸ memOmega).elim
  | finT => exact (h1 ▸ memOmega).elim
  | finS => exact (h1 ▸ memOmega).elim

theorem scott_canonical_unique (d : Scott → SSet)
    (hd : CanonicalDecoration scottEdge (fun a b : Scott => a = b) sMem d) :
    ∀ a, d a = scottSafa a := by
  intro a
  obtain ⟨h0, h1⟩ := scott_classified d hd.decoration
  cases a with
  | s0 => exact h0
  | s1 =>
    cases h1 with
    | inl h => cases hd.reflects .s0 .s1 (h0.trans h.symm)
    | inr h => exact h

theorem scott_canonical_axiom : CanonicalAxiom scottEdge (fun a b : Scott => a = b) sMem := by
  refine ⟨scottSafa, ⟨scottSafa_decoration, respects_eq _, ?_⟩, scott_canonical_unique⟩
  intro a b h
  cases a <;> cases b <;> first | rfl | cases h

/-- On the two-cycle the unfolding identification relates every pair of nodes. -/
def cycleIdent : Cycle → Cycle → Prop := fun _ _ => True

theorem cycleIdent_bisim : IsBisimulation cycleEdge cycleEdge cycleIdent :=
  cycle_total_bisim

theorem cycle_sa_unique (d : Cycle → SSet) (hd : IsDecoration cycleEdge sMem d) :
    d .l = .omega ∧ d .r = .omega := by
  have sole : ∃! y, sMem y (d .l) := by
    refine ⟨d .r, (hd .l (d .r)).mpr ⟨.r, trivial, rfl⟩, ?_⟩
    intro y hy
    obtain ⟨b, hb, eq⟩ := (hd .l y).mp hy
    cases b with
    | l => exact hb.elim
    | r => exact eq
  have onlyR : ∀ y, sMem y (d .r) → y = d .l := by
    intro y hy
    obtain ⟨b, hb, eq⟩ := (hd .r y).mp hy
    cases b with
    | r => exact hb.elim
    | l => exact eq
  cases sSet_unique_member _ sole with
  | inl h =>
    have hr : d .r = .omega := (sMem_omega _).mp (h ▸ (hd .l (d .r)).mpr ⟨.r, trivial, rfl⟩)
    exact ⟨h, hr⟩
  | inr h =>
    have hr : d .r = .finS := (sMem_finT _).mp (h ▸ (hd .l (d .r)).mpr ⟨.r, trivial, rfl⟩)
    have ht : sMem .finT (d .r) := hr.symm ▸ (trivial : sMem .finT .finS)
    have hs : sMem .finS (d .r) := hr.symm ▸ (trivial : sMem .finS .finS)
    cases (onlyR _ ht).trans (onlyR _ hs).symm

theorem cycle_safa : IsDecoration cycleEdge sMem (fun _ => .omega) :=
  isDecoration_const_quine cycle_has_child s_omega_quine

theorem cycle_safa_canonical : CanonicalAxiom cycleEdge cycleIdent sMem := by
  refine ⟨fun _ => .omega, ⟨cycle_safa, fun _ _ _ => rfl, fun _ _ _ => trivial⟩, ?_⟩
  intro d' hd' a
  obtain ⟨hl, hr⟩ := cycle_sa_unique d' hd'.decoration
  cases a with
  | l => exact hl
  | r => exact hr

theorem cycle_fa_unique (d : Cycle → FSet) (hd : IsDecoration cycleEdge fMem d) :
    d .l = .omega ∧ d .r = .omega := by
  have sole : ∃! y, fMem y (d .l) := by
    refine ⟨d .r, (hd .l (d .r)).mpr ⟨.r, trivial, rfl⟩, ?_⟩
    intro y hy
    obtain ⟨b, hb, eq⟩ := (hd .l y).mp hy
    cases b with
    | l => exact hb.elim
    | r => exact eq
  have onlyR : ∀ y, fMem y (d .r) → y = d .l := by
    intro y hy
    obtain ⟨b, hb, eq⟩ := (hd .r y).mp hy
    cases b with
    | r => exact hb.elim
    | l => exact eq
  cases fSet_unique_member _ sole with
  | inl h =>
    have hr : d .r = .omega := (fMem_omega _).mp (h ▸ (hd .l (d .r)).mpr ⟨.r, trivial, rfl⟩)
    exact ⟨h, hr⟩
  | inr h =>
    cases h with
    | inl h =>
      have hr : d .r = .f1 := (fMem_f0 _).mp (h ▸ (hd .l (d .r)).mpr ⟨.r, trivial, rfl⟩)
      have h0 : fMem .f0 (d .r) := hr.symm ▸ (trivial : fMem .f0 .f1)
      have h2 : fMem .f2 (d .r) := hr.symm ▸ (trivial : fMem .f2 .f1)
      cases (onlyR _ h0).trans (onlyR _ h2).symm
    | inr h =>
      have hr : d .r = .colS := (fMem_colT _).mp (h ▸ (hd .l (d .r)).mpr ⟨.r, trivial, rfl⟩)
      have hT : fMem .colT (d .r) := hr.symm ▸ (trivial : fMem .colT .colS)
      have hS : fMem .colS (d .r) := hr.symm ▸ (trivial : fMem .colS .colS)
      cases (onlyR _ hT).trans (onlyR _ hS).symm

theorem cycle_fafa : IsDecoration cycleEdge fMem (fun _ => .omega) :=
  isDecoration_const_quine cycle_has_child f_omega_quine

theorem cycle_fafa_collapses (d : Cycle → FSet) (hd : IsDecoration cycleEdge fMem d) :
    d .l = d .r := by
  obtain ⟨hl, hr⟩ := cycle_fa_unique d hd
  exact hl.trans hr.symm

def cycleBafa : Cycle → BSet
  | .l => .cycL
  | .r => .cycR

theorem cycleBafa_decoration : IsDecoration cycleEdge bMem cycleBafa := by
  intro a y
  cases a with
  | l =>
    unfold cycleBafa
    rw [bMem_cycL]
    constructor
    · intro h
      exact ⟨.r, trivial, h⟩
    · intro ⟨b, hb, eq⟩
      cases b with
      | l => exact hb.elim
      | r => exact eq
  | r =>
    unfold cycleBafa
    rw [bMem_cycR]
    constructor
    · intro h
      exact ⟨.l, trivial, h⟩
    · intro ⟨b, hb, eq⟩
      cases b with
      | r => exact hb.elim
      | l => exact eq

theorem cycle_bafa_collapse : IsDecoration cycleEdge bMem (fun _ => .atomA) :=
  isDecoration_const_quine cycle_has_child b_atomA_quine

theorem bafa_cycle_two :
    ∃ d d' : Cycle → BSet, IsDecoration cycleEdge bMem d ∧ IsDecoration cycleEdge bMem d' ∧
      d .l ≠ d' .l :=
  ⟨fun _ => .atomA, cycleBafa, cycle_bafa_collapse, cycleBafa_decoration, by intro h; cases h⟩

theorem cycle_weak : WeaklyExtensional cycleEdge := by
  intro a b h
  cases a <;> cases b
  · rfl
  · exact (cycle_not_same_children h).elim
  · exact (cycle_not_same_children (fun c => (h c).symm)).elim
  · rfl

theorem scott_not_strong : ¬ StronglyExtensional scottEdge := by
  intro h
  cases h (fun _ _ => True) scott_total_bisim .s0 .s1 trivial

theorem fin_not_strong : ¬ StronglyExtensional finEdge := by
  intro h
  cases h finRelate fin_bisim .n1 .n2 trivial

def finFafa : Fin3 → FSet
  | .n0 => .f0
  | .n1 => .f1
  | .n2 => .f2

def finCol : Fin3 → FSet
  | .n0 => .colT
  | .n1 => .colS
  | .n2 => .colS

theorem finFafa_decoration : IsDecoration finEdge fMem finFafa := by
  intro a y
  cases a with
  | n0 =>
    unfold finFafa
    rw [fMem_f0]
    constructor
    · intro h
      exact ⟨.n1, trivial, h⟩
    · intro ⟨b, hb, eq⟩
      cases b with
      | n0 => exact hb.elim
      | n1 => exact eq
      | n2 => exact hb.elim
  | n1 =>
    unfold finFafa
    rw [fMem_f1]
    constructor
    · intro h
      cases h with
      | inl h => exact ⟨.n0, trivial, h⟩
      | inr h => exact ⟨.n2, trivial, h⟩
    · intro ⟨b, hb, eq⟩
      cases b with
      | n0 => exact Or.inl eq
      | n1 => exact hb.elim
      | n2 => exact Or.inr eq
  | n2 =>
    unfold finFafa
    rw [fMem_f2]
    constructor
    · intro h
      cases h with
      | inl h => exact ⟨.n0, trivial, h⟩
      | inr h => exact ⟨.n1, trivial, h⟩
    · intro ⟨b, hb, eq⟩
      cases b with
      | n0 => exact Or.inl eq
      | n1 => exact Or.inr eq
      | n2 => exact hb.elim

theorem finCol_decoration : IsDecoration finEdge fMem finCol := by
  intro a y
  cases a with
  | n0 =>
    unfold finCol
    rw [fMem_colT]
    constructor
    · intro h
      exact ⟨.n1, trivial, h⟩
    · intro ⟨b, hb, eq⟩
      cases b with
      | n0 => exact hb.elim
      | n1 => exact eq
      | n2 => exact hb.elim
  | n1 =>
    unfold finCol
    rw [fMem_colS]
    constructor
    · intro h
      cases h with
      | inl h => exact ⟨.n0, trivial, h⟩
      | inr h => exact ⟨.n2, trivial, h⟩
    · intro ⟨b, hb, eq⟩
      cases b with
      | n0 => exact Or.inl eq
      | n1 => exact hb.elim
      | n2 => exact Or.inr eq
  | n2 =>
    unfold finCol
    rw [fMem_colS]
    constructor
    · intro h
      cases h with
      | inl h => exact ⟨.n0, trivial, h⟩
      | inr h => exact ⟨.n1, trivial, h⟩
    · intro ⟨b, hb, eq⟩
      cases b with
      | n0 => exact Or.inl eq
      | n1 => exact Or.inr eq
      | n2 => exact hb.elim

theorem finOmega_decoration : IsDecoration finEdge fMem (fun _ => .omega) :=
  isDecoration_const_quine fin_has_child f_omega_quine

theorem fin_three_solutions :
    ∃ d1 d2 d3 : Fin3 → FSet, IsDecoration finEdge fMem d1 ∧ IsDecoration finEdge fMem d2 ∧
      IsDecoration finEdge fMem d3 ∧ d1 Fin3.n1 ≠ d2 Fin3.n1 ∧ d2 Fin3.n1 ≠ d3 Fin3.n1 ∧
      d1 Fin3.n1 ≠ d3 Fin3.n1 := by
  refine ⟨fun _ => FSet.omega, finCol, finFafa, finOmega_decoration, finCol_decoration,
    finFafa_decoration, ?_, ?_, ?_⟩
  · intro h; cases h
  · intro h; cases h
  · intro h; cases h

theorem fin_omega_not_canonical :
    ¬ CanonicalDecoration finEdge (fun a b : Fin3 => a = b) fMem (fun _ => .omega) := by
  intro h
  cases h.reflects .n0 .n1 rfl

theorem fin_canonical_unique (d : Fin3 → FSet)
    (hd : CanonicalDecoration finEdge (fun a b : Fin3 => a = b) fMem d) :
    ∀ a, d a = finFafa a := by
  have sole : ∃! y, fMem y (d .n0) := by
    refine ⟨d .n1, (hd.decoration .n0 (d .n1)).mpr ⟨.n1, trivial, rfl⟩, ?_⟩
    intro y hy
    obtain ⟨b, hb, eq⟩ := (hd.decoration .n0 y).mp hy
    cases b with
    | n0 => exact hb.elim
    | n1 => exact eq
    | n2 => exact hb.elim
  cases fSet_unique_member _ sole with
  | inl h0 =>
    have h1 : d .n1 = .omega :=
      (fMem_omega _).mp (h0 ▸ (hd.decoration .n0 (d .n1)).mpr ⟨.n1, trivial, rfl⟩)
    have h2 : d .n2 = .omega :=
      (fMem_omega _).mp (h1 ▸ (hd.decoration .n1 (d .n2)).mpr ⟨.n2, trivial, rfl⟩)
    cases hd.reflects .n0 .n2 (h0.trans h2.symm)
  | inr hrest =>
    cases hrest with
    | inl h0 =>
      have h1 : d .n1 = .f1 :=
        (fMem_f0 _).mp (h0 ▸ (hd.decoration .n0 (d .n1)).mpr ⟨.n1, trivial, rfl⟩)
      have hm2 : fMem (d .n2) .f1 :=
        h1 ▸ (hd.decoration .n1 (d .n2)).mpr ⟨.n2, trivial, rfl⟩
      have h2 : d .n2 = .f2 := by
        cases (fMem_f1 _).mp hm2 with
        | inl h => cases hd.reflects .n2 .n0 (h.trans h0.symm)
        | inr h => exact h
      intro a
      cases a with
      | n0 => exact h0
      | n1 => exact h1
      | n2 => exact h2
    | inr h0 =>
      have h1 : d .n1 = .colS :=
        (fMem_colT _).mp (h0 ▸ (hd.decoration .n0 (d .n1)).mpr ⟨.n1, trivial, rfl⟩)
      have hm2 : fMem (d .n2) .colS :=
        h1 ▸ (hd.decoration .n1 (d .n2)).mpr ⟨.n2, trivial, rfl⟩
      cases (fMem_colS _).mp hm2 with
      | inl h => cases hd.reflects .n2 .n0 (h.trans h0.symm)
      | inr h => cases hd.reflects .n2 .n1 (h.trans h1.symm)

theorem fin_canonical_axiom : CanonicalAxiom finEdge (fun a b : Fin3 => a = b) fMem := by
  refine ⟨finFafa, ⟨finFafa_decoration, respects_eq _, ?_⟩, fin_canonical_unique⟩
  intro a b h
  cases a <;> cases b <;> first | rfl | cases h

end Mettapedia.SetTheory.AntiFoundation
