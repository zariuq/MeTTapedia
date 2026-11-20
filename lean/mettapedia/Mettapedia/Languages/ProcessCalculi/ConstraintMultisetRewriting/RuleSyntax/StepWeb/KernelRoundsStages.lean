import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreClosure
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Immediate-consequence stages and minimum proof depth

This is positive, non-consuming propagation with finite premises and conclusions,
set observations and no told knowledge or negative guards. The instances are
the existing `SetStoreClosure.Instance`; the rule-syntax adapter supplies ground
instances of actual rules. No commit discipline is chosen here.

A stage applies every consequence enabled at its entry. Stages retain old rows,
including at a fixed point; an actual set-store step additionally requires change.
Proof depth below is a minimum: redundant cyclic proofs do not delay closure.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.KernelRounds

open Mettapedia.GSLT.OpenEnded

universe u v
variable {G : Type u} {I : Type v}

def immediate (rules : I → SetStoreClosure.Instance G) (rows : Set G) : Set G :=
  rows ∪ {value | ∃ i, (∀ premise ∈ (rules i).read, premise ∈ rows) ∧ value ∈ (rules i).made}

theorem immediate_extensive (rules : I → SetStoreClosure.Instance G) (rows : Set G) :
    rows ⊆ immediate rules rows := fun _ member => Or.inl member

theorem immediate_mono (rules : I → SetStoreClosure.Instance G) : Monotone (immediate rules) := by
  intro rows later included value member
  rcases member with old | ⟨i, enabled, made⟩
  · exact Or.inl (included old)
  · exact Or.inr ⟨i, fun premise present => included (enabled premise present), made⟩

def stage (rules : I → SetStoreClosure.Instance G) (seed : Set G) : Nat → Set G
  | 0 => seed
  | n + 1 => immediate rules (stage rules seed n)

@[simp] theorem stage_zero (rules : I → SetStoreClosure.Instance G) (seed : Set G) :
    stage rules seed 0 = seed := rfl

@[simp] theorem stage_succ (rules : I → SetStoreClosure.Instance G) (seed : Set G) (n : Nat) :
    stage rules seed (n + 1) = immediate rules (stage rules seed n) := rfl

theorem stage_mono (rules : I → SetStoreClosure.Instance G) (seed : Set G) :
    Monotone (stage rules seed) :=
  monotone_nat_of_le_succ fun n => immediate_extensive rules (stage rules seed n)

theorem seed_subset_stage (rules : I → SetStoreClosure.Instance G) (seed : Set G) (n : Nat) :
    seed ⊆ stage rules seed n := stage_mono rules seed (Nat.zero_le n)

/-- Finite proof trees, with an explicit upper bound on their inference height. -/
inductive ProofWithin (rules : I → SetStoreClosure.Instance G) (seed : Set G) : Nat → G → Prop
  | seed {value : G} (member : value ∈ seed) : ProofWithin rules seed 0 value
  | retain {n : Nat} {value : G} (earlier : ProofWithin rules seed n value) :
      ProofWithin rules seed (n + 1) value
  | apply {n : Nat} (i : I) {value : G}
      (premises : ∀ premise ∈ (rules i).read, ProofWithin rules seed n premise)
      (made : value ∈ (rules i).made) : ProofWithin rules seed (n + 1) value

theorem proofWithin_mem_stage (rules : I → SetStoreClosure.Instance G) (seed : Set G)
    {n : Nat} {value : G} (proof : ProofWithin rules seed n value) : value ∈ stage rules seed n := by
  induction proof with
  | seed member => exact member
  | retain _ ih => exact Or.inl ih
  | apply i _ made ih => exact Or.inr ⟨i, ih, made⟩

theorem mem_stage_iff_proofWithin (rules : I → SetStoreClosure.Instance G) (seed : Set G)
    (n : Nat) (value : G) : value ∈ stage rules seed n ↔ ProofWithin rules seed n value := by
  constructor
  · induction n generalizing value with
    | zero => exact ProofWithin.seed
    | succ n ih =>
      intro member
      rcases member with old | ⟨i, enabled, made⟩
      · exact .retain (ih value old)
      · exact .apply i (fun premise inside => ih premise (enabled premise inside)) made
  · exact proofWithin_mem_stage rules seed

def finiteProofs (rules : I → SetStoreClosure.Instance G) (seed : Set G) : Set G :=
  {value | ∃ n, value ∈ stage rules seed n}

theorem finite_premises_have_a_stage [DecidableEq G] (rules : I → SetStoreClosure.Instance G)
    (seed : Set G) (premises : Finset G)
    (covered : ∀ value ∈ premises, value ∈ finiteProofs rules seed) :
    ∃ n, ∀ value ∈ premises, value ∈ stage rules seed n := by
  induction premises using Finset.induction_on with
  | empty => exact ⟨0, fun _ member => False.elim (Finset.notMem_empty _ member)⟩
  | @insert value rest _ ih =>
    obtain ⟨first, present⟩ := covered value (Finset.mem_insert_self _ _)
    obtain ⟨later, restCovered⟩ := ih (fun row member => covered row (Finset.mem_insert_of_mem member))
    refine ⟨max first later, fun row member => ?_⟩
    rcases Finset.mem_insert.mp member with rfl | inside
    · exact stage_mono rules seed (Nat.le_max_left _ _) present
    · exact stage_mono rules seed (Nat.le_max_right _ _) (restCovered row inside)

theorem finiteProofs_closed [DecidableEq G] (rules : I → SetStoreClosure.Instance G)
    (seed : Set G) (i : I) (enabled : ∀ premise ∈ (rules i).read, premise ∈ finiteProofs rules seed)
    {value : G} (made : value ∈ (rules i).made) : value ∈ finiteProofs rules seed := by
  obtain ⟨n, premises⟩ := finite_premises_have_a_stage rules seed (rules i).read enabled
  exact ⟨n + 1, Or.inr ⟨i, premises, made⟩⟩

theorem stage_le_target (rules : I → SetStoreClosure.Instance G) (seed : Set G) (n : Nat) :
    stage rules seed n ⊆ ChaoticIteration.target (fun i => SetStoreClosure.action (rules i)) seed := by
  have least := ChaoticIteration.isLeast_target (fun i => SetStoreClosure.action (rules i)) seed
  induction n with
  | zero => exact least.1.1
  | succ n ih =>
    intro value member
    rcases member with old | ⟨i, enabled, made⟩
    · exact ih old
    · exact least.1.2 i ⟨fun _ member => ih (enabled _ member), made⟩

theorem finiteProofs_eq_target [DecidableEq G] (rules : I → SetStoreClosure.Instance G) (seed : Set G) :
    finiteProofs rules seed = ChaoticIteration.target (fun i => SetStoreClosure.action (rules i)) seed := by
  apply Set.Subset.antisymm
  · rintro value ⟨n, member⟩
    exact stage_le_target rules seed n member
  · apply (Mettapedia.GSLT.OpenEnded.ChaoticIteration.isLeast_target
      (fun i => SetStoreClosure.action (rules i)) seed).2
    refine ⟨fun _ member => ⟨0, member⟩, ?_⟩
    intro i value member
    exact finiteProofs_closed rules seed i (fun premise inside => member.1 inside) member.2

theorem stage_le_closure (rules : I → SetStoreClosure.Instance G) (seed : Finset G) (n : Nat) :
    stage rules (seed : Set G) n ⊆ SetStoreClosure.closure rules seed :=
  stage_le_target rules (seed : Set G) n

theorem finiteProofs_eq_closure [DecidableEq G] (rules : I → SetStoreClosure.Instance G)
    (seed : Finset G) : finiteProofs rules (seed : Set G) = SetStoreClosure.closure rules seed :=
  finiteProofs_eq_target rules (seed : Set G)

theorem stage_eq_closure_iff_fixed [DecidableEq G] (rules : I → SetStoreClosure.Instance G)
    (seed : Finset G) (n : Nat) :
    stage rules (seed : Set G) n = SetStoreClosure.closure rules seed ↔
      immediate rules (stage rules (seed : Set G) n) = stage rules (seed : Set G) n := by
  constructor
  · intro complete
    apply Set.Subset.antisymm
    · rw [complete]
      intro value member
      rcases member with old | ⟨i, enabled, made⟩
      · exact old
      · exact SetStoreClosure.closure_closed rules seed i ⟨fun _ inside => enabled _ inside, made⟩
    · exact immediate_extensive rules _
  · intro fixed
    apply Set.Subset.antisymm (stage_le_closure rules seed n)
    apply (Mettapedia.GSLT.OpenEnded.ChaoticIteration.isLeast_target
      (fun i => SetStoreClosure.action (rules i)) (seed : Set G)).2
    refine ⟨seed_subset_stage rules (seed : Set G) n, ?_⟩
    intro i value member
    rw [← fixed]
    exact Or.inr ⟨i, fun _ inside => member.1 inside, member.2⟩

noncomputable def minimumDepth (rules : I → SetStoreClosure.Instance G) (seed : Set G)
    (value : G) (derived : value ∈ finiteProofs rules seed) : Nat := by
  classical
  exact Nat.find derived

theorem minimumDepth_le_iff (rules : I → SetStoreClosure.Instance G) (seed : Set G)
    (value : G) (derived : value ∈ finiteProofs rules seed) (n : Nat) :
    minimumDepth rules seed value derived ≤ n ↔ value ∈ stage rules seed n := by
  classical
  constructor
  · intro bound
    exact stage_mono rules seed bound (Nat.find_spec derived)
  · exact Nat.find_min' derived

theorem closure_by_depth_iff [DecidableEq G] (rules : I → SetStoreClosure.Instance G)
    (seed : Finset G) (n : Nat) :
    stage rules (seed : Set G) n = SetStoreClosure.closure rules seed ↔
      ∀ value (derived : value ∈ finiteProofs rules (seed : Set G)),
        minimumDepth rules (seed : Set G) value derived ≤ n := by
  constructor
  · intro complete value derived
    apply (minimumDepth_le_iff rules (seed : Set G) value derived n).mpr
    rw [complete, ← finiteProofs_eq_closure rules seed]
    exact derived
  · intro bounded
    apply Set.Subset.antisymm (stage_le_closure rules seed n)
    intro value member
    have derived : value ∈ finiteProofs rules (seed : Set G) := by
      rwa [finiteProofs_eq_closure rules seed]
    exact (minimumDepth_le_iff rules (seed : Set G) value derived n).mp (bounded value derived)

#print axioms mem_stage_iff_proofWithin
#print axioms finiteProofs_eq_target
#print axioms finiteProofs_eq_closure
#print axioms stage_eq_closure_iff_fixed
#print axioms closure_by_depth_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.KernelRounds
