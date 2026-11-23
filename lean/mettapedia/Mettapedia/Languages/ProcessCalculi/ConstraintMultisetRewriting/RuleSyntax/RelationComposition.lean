import Mettapedia.Machines.Specialization.RelationComposition
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreClosure

/-! # Publishing first-class relation composition by a positive transform

The declaration and both premise occurrences are reads. The made row retains the
two proof trees and their common endpoint. The set observer identifies identical
rows. An occurrence-sensitive producer supplies distinct identifiers in its leaves.
Declarations bound the set of relation expressions that the store may publish. -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RelationComposition

open Mettapedia.Machines.Specialization.RelationComposition
open Mettapedia.GSLT.OpenEnded

variable {N K P : Type} [DecidableEq N] [DecidableEq K] [DecidableEq P]

inductive Fact (N K P : Type) where
  | declare (rel : Expr N)
  | holds (rel : Expr N) (row : Row K (Proof K P))
  deriving DecidableEq

structure Binding (N K P : Type) where
  left : Expr N
  right : Expr N
  x : K
  middle : K
  z : K
  first : Proof K P
  second : Proof K P

def rule (b : Binding N K P) : SetStoreClosure.Instance (Fact N K P) where
  read := {.declare (.chain b.left b.right), .holds b.left ⟨b.x, b.middle, b.first⟩,
           .holds b.right ⟨b.middle, b.z, b.second⟩}
  made := {.holds (.chain b.left b.right) ⟨b.x, b.z, .via b.middle b.first b.second⟩}

variable (declared : Finset (Expr N)) (inputs : List (N × Row K P))

def provider (name : N) := ((inputs.filter fun entry => decide (entry.1 = name)).map Prod.snd)

def seed : Finset (Fact N K P) :=
  declared.image Fact.declare ∪ (inputs.map (fun (name, row) => Fact.holds (.base name) (liftRow row))).toFinset

def permitted : Expr N → Prop
  | .base _ => True
  | .chain r s => .chain r s ∈ declared ∧ permitted r ∧ permitted s

def meaning : Set (Fact N K P) := fun fact => match fact with
  | .declare expr => expr ∈ declared
  | .holds expr row => permitted declared expr ∧ Holds (provider inputs) expr row

omit [DecidableEq K] [DecidableEq P] in
theorem mem_provider_iff {name : N} {row : Row K P} :
    row ∈ provider inputs name ↔ (name, row) ∈ inputs := by
  simp [provider, List.mem_map]

private theorem no_invention : SetStoreClosure.closure rule (seed declared inputs) ⊆ meaning declared inputs := by
  apply (ChaoticIteration.isLeast_target _ _).2
  constructor
  · intro fact member
    rcases Finset.mem_union.mp member with d | i
    · obtain ⟨expr, hx, rfl⟩ := Finset.mem_image.mp d
      exact hx
    · obtain ⟨⟨name, row⟩, hr, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp i)
      exact ⟨trivial, .fact name row ((mem_provider_iff inputs).mpr hr)⟩
  · intro b fact hf
    obtain ⟨reads, made⟩ := hf
    obtain rfl := Finset.mem_singleton.mp made
    have decl := reads (show Fact.declare (.chain b.left b.right) ∈ (rule b).read by simp [rule])
    have left := reads (show Fact.holds b.left ⟨b.x, b.middle, b.first⟩ ∈ (rule b).read by simp [rule])
    have right := reads (show Fact.holds b.right ⟨b.middle, b.z, b.second⟩ ∈ (rule b).read by simp [rule])
    exact ⟨⟨decl, left.1, right.1⟩, Holds.fire left.2 right.2 rfl⟩

private theorem fires_in_store {expr : Expr N} {row : Row K (Proof K P)} (fired : Holds (provider inputs) expr row)
    (enabled : permitted declared expr) : Fact.holds expr row ∈ SetStoreClosure.closure rule (seed declared inputs) := by
  induction fired with
  | fact name row supplied =>
    apply SetStoreClosure.seed_subset_closure
    apply Finset.mem_union_right
    apply List.mem_toFinset.mpr
    exact List.mem_map.mpr ⟨(name, row), (mem_provider_iff inputs).mp supplied, rfl⟩
  | @fire a b l r _ _ same left right =>
    obtain ⟨x, m, p⟩ := l
    obtain ⟨m', z, q⟩ := r
    change m' = m at same
    subst m'
    let binding : Binding N K P := ⟨a, b, x, m, z, p, q⟩
    apply SetStoreClosure.closure_closed rule (seed declared inputs) binding
    constructor
    · intro fact h
      simp only [rule, binding, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with rfl | rfl | rfl
      · apply SetStoreClosure.seed_subset_closure
        exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨_, enabled.1, rfl⟩)
      · exact left enabled.2.1
      · exact right enabled.2.2
    · exact Finset.mem_singleton_self _

theorem closure_iff_indexed (tables) (expr : Expr N) (row : Row K (Proof K P)) :
    Fact.holds expr row ∈ SetStoreClosure.closure rule (seed declared inputs) ↔
      permitted declared expr ∧ row ∈ indexed (provider inputs) tables expr := by
  rw [indexed_exact, mem_iff_fires]
  exact ⟨fun h => no_invention declared inputs h, fun h => fires_in_store declared inputs h.2 h.1⟩

theorem terminal_iff_indexed (tables) {result : Finset (Fact N K P)}
    (run : Relation.ReflTransGen (SetStoreClosure.Step rule) (seed declared inputs) result)
    (terminal : SetStoreClosure.Terminal rule result) (expr : Expr N) (row : Row K (Proof K P)) :
    Fact.holds expr row ∈ result ↔ permitted declared expr ∧ row ∈ indexed (provider inputs) tables expr := by
  change Fact.holds expr row ∈ (result : Set _) ↔ _
  rw [SetStoreClosure.terminal_eq_closure rule _ run terminal, closure_iff_indexed]

/-- Finite declared expressions bound the closure even when the key and proof
types are infinite. No bound on the height of independently supplied terms is
required. -/
theorem finite_closure : (SetStoreClosure.closure rule (seed declared inputs)).Finite := by
  let carrier := seed declared inputs ∪ declared.biUnion (fun expr =>
    ((denote (provider inputs) expr).map (Fact.holds expr)).toFinset)
  apply carrier.finite_toSet.subset
  intro fact hf
  have valid := no_invention declared inputs hf
  cases fact with
  | declare expr =>
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨expr, valid, rfl⟩))
  | holds expr row =>
    obtain ⟨permission, justification⟩ := valid
    cases expr with
    | base name =>
      cases justification with
      | fact _ r stored =>
        exact Finset.mem_union_left _ (Finset.mem_union_right _ (List.mem_toFinset.mpr
          (List.mem_map.mpr ⟨(name, r), (mem_provider_iff inputs).mp stored, rfl⟩)))
    | chain a b =>
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨_, permission.1,
        List.mem_toFinset.mpr (List.mem_map.mpr ⟨row, (mem_iff_fires ..).mpr justification, rfl⟩)⟩)

theorem exists_terminal :
    ∃ result, Relation.ReflTransGen (SetStoreClosure.Step rule) (seed declared inputs) result ∧
      SetStoreClosure.Terminal rule result := by
  let bounded := finite_closure declared inputs
  apply SetStoreClosure.exists_terminal rule bounded.toFinset
  · intro b included row made
    apply bounded.mem_toFinset.mpr
    exact SetStoreClosure.closure_closed rule _ b
      ⟨fun _ h => bounded.mem_toFinset.mp (included h), made⟩
  · intro row hr
    exact bounded.mem_toFinset.mpr (SetStoreClosure.seed_subset_closure rule _ hr)

/-- Simultaneous reads use the preceding world. Prior rows remain present. -/
def waves : Nat → Set (Fact N K P)
  | 0 => seed declared inputs
  | n + 1 =>
    let before := waves n
    ChaoticIteration.allRules (fun b => SetStoreClosure.action (rule b)) before before

def depth : Expr N → Nat
  | .base _ => 0
  | .chain a b => max (depth a) (depth b) + 1

private theorem waves_mono : Monotone (waves declared inputs) := by
  apply monotone_nat_of_le_succ
  intro n
  apply le_sup_left

theorem waves_subset_closure (n : Nat) :
    waves declared inputs n ⊆ SetStoreClosure.closure rule (seed declared inputs) := by
  induction n with
  | zero => exact SetStoreClosure.seed_subset_closure _ _
  | succ n prior =>
    apply sup_le prior
    apply iSup_le
    intro b
    exact ((SetStoreClosure.action (rule b)).monotone prior).trans
      (SetStoreClosure.closure_closed rule _ b)

private theorem fires_by_depth {expr : Expr N} {row : Row K (Proof K P)}
    (fired : Holds (provider inputs) expr row) (enabled : permitted declared expr) :
    Fact.holds expr row ∈ waves declared inputs (depth expr) := by
  induction fired with
  | fact name row supplied =>
    exact Finset.mem_union_right _ (List.mem_toFinset.mpr
      (List.mem_map.mpr ⟨(name, row), (mem_provider_iff inputs).mp supplied, rfl⟩))
  | @fire a b l r _ _ same left right =>
    obtain ⟨x, m, p⟩ := l
    obtain ⟨m', z, q⟩ := r
    change m' = m at same
    subst m'
    let binding : Binding N K P := ⟨a, b, x, m, z, p, q⟩
    let before := waves declared inputs (max (depth a) (depth b))
    have ready : Fact.holds (.chain a b) ⟨x, z, .via m p q⟩ ∈
        SetStoreClosure.action (rule binding) before := by
      refine ⟨?_, Finset.mem_singleton_self _⟩
      intro fact h
      simp only [rule, binding, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with rfl | rfl | rfl
      · apply waves_mono declared inputs (Nat.zero_le _)
        exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨_, enabled.1, rfl⟩)
      · exact waves_mono declared inputs (Nat.le_max_left ..) (left enabled.2.1)
      · exact waves_mono declared inputs (Nat.le_max_right ..) (right enabled.2.2)
    have included : SetStoreClosure.action (rule binding) before ≤ before ⊔
        ⨆ i, SetStoreClosure.action (rule i) before := le_sup_of_le_right (le_iSup (fun i : Binding N K P => SetStoreClosure.action (rule i) before) binding)
    exact included ready

theorem waves_iff_indexed (tables) (expr : Expr N) (row : Row K (Proof K P)) (n : Nat)
    (enough : depth expr ≤ n) :
    Fact.holds expr row ∈ waves declared inputs n ↔
      permitted declared expr ∧ row ∈ indexed (provider inputs) tables expr := by
  constructor
  · intro hit
    exact (closure_iff_indexed declared inputs tables expr row).mp (waves_subset_closure declared inputs n hit)
  · rintro ⟨allowed, member⟩
    rw [indexed_exact, mem_iff_fires] at member
    exact waves_mono declared inputs enough (fires_by_depth declared inputs member allowed)

open scoped Classical in
/-- When each supplied occurrence is distinguishable within its own
relation, set publication recovers the exact count of each full witness. -/
theorem wave_count (tables) (expr : Expr N) (row : Row K (Proof K P)) (n : Nat)
    (enough : depth expr ≤ n) (allowed : permitted declared expr)
    (distinct : ∀ name, (provider inputs name).Nodup) :
    (indexed (provider inputs) tables expr).count row =
      if Fact.holds expr row ∈ waves declared inputs n then 1 else 0 := by
  classical
  have exactRows := waves_iff_indexed declared inputs tables expr row n enough
  by_cases hit : Fact.holds expr row ∈ waves declared inputs n
  · rw [if_pos hit]
    apply List.count_eq_one_of_mem _ (exactRows.mp hit).2
    rw [indexed_exact]
    exact denote_nodup _ distinct expr
  · rw [if_neg hit]
    exact List.count_eq_zero.mpr fun member => hit (exactRows.mpr ⟨allowed, member⟩)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RelationComposition
