import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreOutcomes

/-! # One constructor rule grows forever from one ground input row -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreGrowthControls

open Mettapedia.Logic.LP
open OneFrame (Terms frames ext)
open SetStoreSyntax

abbrev signature : LPSignature := ⟨Unit, ℕ, Empty, Empty.elim, Unit, fun _ => 1⟩
def next (term : Term signature) : Term signature := .app () (fun _ => term)
def tower : ℕ → Term signature
  | 0 => .const ()
  | n + 1 => next (tower n)
def rule : Rule (Terms (Term signature)) := ⟨PUnit.unit, ⟨[], [.var 0], [], [], [next (.var 0)]⟩, []⟩
def program : Program (Terms (Term signature)) := {rule}

theorem rule_propagates : Propagates rule := by
  refine ⟨rfl, rfl, ⟨?_, rfl⟩, ?_, ?_⟩
  · intro check inside
    cases inside
  · simp [rule, varsIn, next, Term.freeVars]
  · simp [rule, varsIn]

theorem program_pure : ∀ r ∈ program, Propagates r := by
  intro r member
  obtain rfl := Set.mem_singleton_iff.mp member
  exact rule_propagates

theorem tower_ground (n : ℕ) : (tower n).isGround := by
  induction n with
  | zero => trivial
  | succ n ih => exact fun _ => ih

theorem tower_size (n : ℕ) : (tower n).size = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [tower, next, Term.size, signature, Nat.add_comm] using ih

theorem tower_injective : Function.Injective tower := by
  intro n m same
  have sizes := congrArg Term.size same
  rw [tower_size, tower_size] at sizes
  omega

def matchAt (n : ℕ) : GroundMatch program where
  rule := rule
  member := rfl
  propagates := rule_propagates
  assignment := fun _ => tower n
  groundReads term inside := by
    obtain rfl := List.mem_singleton.mp inside
    exact tower_ground n
  checked _ _ inside := by cases inside

def rows (n : ℕ) : Finset (Term signature) := (Finset.range (n + 1)).image tower

theorem rows_ground (n : ℕ) : GroundRows (rows n) := by
  intro term inside
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp inside
  exact tower_ground i

theorem grows (timing : SetStore.AskTiming) (n : ℕ) :
    SetStore.Step timing program (rows n) (rows (n + 1)) := by
  have enabled : (consequence (matchAt n)).read ⊆ rows n := by
    change {tower n} ⊆ rows n
    rw [Finset.singleton_subset_iff]
    exact Finset.mem_image.mpr ⟨n, Finset.mem_range.mpr (by omega), rfl⟩
  have outside : ¬ (consequence (matchAt n)).made ⊆ rows n := by
    intro all
    have made : tower (n + 1) ∈ (consequence (matchAt n)).made := by
      simp [consequence, matchAt, rule, tower, next, Subst.applyTerm]
    obtain ⟨i, bounded, same⟩ := Finset.mem_image.mp (all made)
    have indices := tower_injective same
    have bound := Finset.mem_range.mp bounded
    omega
  have target : rows n ∪ (consequence (matchAt n)).made = rows (n + 1) := by
    simp only [consequence, matchAt, rule, List.map_cons, List.map_nil, Subst.applyTerm,
      List.toFinset_cons, List.toFinset_nil]
    change rows n ∪ {tower (n + 1)} = rows (n + 1)
    simp only [rows, Finset.range_add_one, Finset.image_insert, Finset.union_singleton]
  apply lift_step timing (rows_ground n)
  refine ⟨matchAt n, enabled, ?_, ?_⟩
  · simpa [SetStore.update] using target.symm
  · intro same
    apply outside
    intro term made
    have member : term ∈ rows n ∪ (consequence (matchAt n)).made := Finset.mem_union_right _ made
    rwa [target, same] at member

theorem finite_input_no_closed_carrier (carrier : Finset (Term signature)) (seed : tower 0 ∈ carrier) :
    ¬ SetStoreClosure.Closed (consequence (P := program)) carrier := by
  intro closed
  apply actual_no_infinite_run .beforeTells program_pure carrier closed rows
    (by simpa [rows] using seed) (rows_ground 0)
  exact grows .beforeTells

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreGrowthControls
