import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic

/-!
# Finite observation refinement for labelled machines

The carrier and action alphabet are finite; successor lists give set-valued
nondeterminism. An empty list represents an unavailable action. Refinement
removes pairs whose current observations differ or whose successors fail
back-and-forth matching. The implementation terminates by a strict decrease
in the finite pair set and returns the greatest stable relation below the
input relation. The proof is carried by the result and erased in execution.

This computes a behavioural relation, not a constraint-solver frame map.
It intentionally forgets successor multiplicity and probability.
-/
set_option autoImplicit false
namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DistinctionFinite
universe uS uA uV
variable {S : Type uS} {A : Type uA} {V : Type uV}

structure Machine (S : Type uS) (A : Type uA) (V : Type uV) where
  read : S → V
  next : S → A → List S

namespace Machine
variable (M : Machine S A V) [DecidableEq S] [Fintype A] [DecidableEq V]

def Matches (r : Finset (S × S)) (xs ys : List S) : Prop :=
  ∀ x ∈ xs, ∃ y ∈ ys, (x, y) ∈ r

instance (r : Finset (S × S)) (xs ys : List S) : Decidable (Matches r xs ys) := by
  unfold Matches
  infer_instance

def Good (r : Finset (S × S)) (s t : S) : Prop :=
  M.read s = M.read t ∧ ∀ a,
    Matches r (M.next s a) (M.next t a) ∧
    Matches (r.image Prod.swap) (M.next t a) (M.next s a)

instance (r : Finset (S × S)) (s t : S) : Decidable (M.Good r s t) := by
  unfold Good
  infer_instance

def refine (r : Finset (S × S)) : Finset (S × S) := r.filter fun p => M.Good r p.1 p.2

theorem refine_subset (r : Finset (S × S)) : M.refine r ⊆ r := Finset.filter_subset _ _

omit [DecidableEq S] in
theorem matches_mono {r t : Finset (S × S)} (sub : r ⊆ t) {xs ys : List S}
    (h : Matches r xs ys) : Matches t xs ys := by
  intro x member
  obtain ⟨y, inY, related⟩ := h x member
  exact ⟨y, inY, sub related⟩

omit [Fintype A] [DecidableEq V] in
theorem good_mono {r t : Finset (S × S)} (sub : r ⊆ t) {s u : S}
    (h : M.Good r s u) : M.Good t s u :=
  ⟨h.1, fun a => ⟨matches_mono sub (h.2 a).1,
    matches_mono (Finset.image_subset_image sub) (h.2 a).2⟩⟩

theorem refine_mono {r t : Finset (S × S)} (sub : r ⊆ t) : M.refine r ⊆ M.refine t := by
  intro p member
  obtain ⟨inside, good⟩ := Finset.mem_filter.mp member
  exact Finset.mem_filter.mpr ⟨sub inside, M.good_mono sub good⟩

def Stable (r : Finset (S × S)) : Prop := M.refine r = r

theorem stable_good {r : Finset (S × S)} (stable : M.Stable r) {s t : S}
    (inside : (s, t) ∈ r) : M.Good r s t := by
  have member : (s, t) ∈ M.refine r := stable.symm ▸ inside
  exact (Finset.mem_filter.mp member).2

theorem stable_subset_refine {r t : Finset (S × S)} (sub : t ⊆ r) (stable : M.Stable t) :
    t ⊆ M.refine r := by
  rw [← stable]
  exact M.refine_mono sub

/-- Terminating refinement with a greatest-fixed-subset certificate. -/
def normalize (r : Finset (S × S)) :
    {out : Finset (S × S) // out ⊆ r ∧ M.Stable out ∧
      ∀ t, t ⊆ r → M.Stable t → t ⊆ out} :=
  if fixed : M.refine r = r then
    ⟨r, Finset.Subset.refl _, fixed, fun _ sub _ => sub⟩
  else
    let out := normalize (M.refine r)
    ⟨out.val, Finset.Subset.trans out.property.1 (M.refine_subset r), out.property.2.1,
      fun t sub stable => out.property.2.2 t (M.stable_subset_refine sub stable) stable⟩
termination_by r.card
decreasing_by
  exact Finset.card_lt_card (ssubset_iff_subset_ne.mpr ⟨M.refine_subset r, fixed⟩)

variable [Fintype S]

def seed : Finset (S × S) := Finset.univ.filter fun p => M.read p.1 = M.read p.2

def behaviour : Finset (S × S) := (M.normalize M.seed).val

theorem behaviour_stable : M.Stable M.behaviour := (M.normalize M.seed).property.2.1

theorem behaviour_preserves {s t : S} (related : (s, t) ∈ M.behaviour) : M.read s = M.read t :=
  (Finset.mem_filter.mp ((M.normalize M.seed).property.1 related)).2

theorem behaviour_greatest {r : Finset (S × S)} (stable : M.Stable r) : r ⊆ M.behaviour := by
  apply (M.normalize M.seed).property.2.2 r _ stable
  intro p member
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (M.stable_good stable member).1⟩

/-- Exact finite compatibility of a supplied encoding, with the original observations protected. -/
def checkEncoding {Q : Type*} [DecidableEq Q] (encode : S → Q) : Bool :=
  decide (∀ s t, encode s = encode t → M.Good
    (Finset.univ.filter fun p => encode p.1 = encode p.2) s t)

theorem checkEncoding_iff {Q : Type*} [DecidableEq Q] (encode : S → Q) :
    M.checkEncoding encode = true ↔
      M.Stable (Finset.univ.filter fun p => encode p.1 = encode p.2) := by
  rw [checkEncoding, decide_eq_true_eq]
  constructor
  · intro h
    apply Finset.Subset.antisymm (M.refine_subset _)
    intro p member
    exact Finset.mem_filter.mpr ⟨member, h p.1 p.2 (Finset.mem_filter.mp member).2⟩
  · intro stable s t equal
    exact M.stable_good stable (Finset.mem_filter.mpr ⟨Finset.mem_univ _, equal⟩)

end Machine
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DistinctionFinite
