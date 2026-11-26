import Mettapedia.GSLT.LanguageDef.DefinitionalNormalForms
import Mettapedia.Machines.DemandSummary

/-! The *size* of an equational key is distinct from the number of keys
invalidated by an edit. A name alias cannot grow the constructor tree. A
single duplicating definition can, despite being acyclic and well sorted.
The same normal form has a linear shared construction. -/
set_option autoImplicit false
namespace Mettapedia.GSLT.LanguageDef.DefinitionalKeySize

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match (applyBindings)
open DefinitionalEquations
open Mettapedia.Machines

mutual
  /-- Constructor occurrences, rather than bytes of their names or the
  number of distinct shared subterms. -/
  def nodes : Pattern → Nat
    | .apply _ xs => 1 + forest xs
    | .bvar _ | .fvar _ => 0
    | .lambda _ p | .multiLambda _ _ p => nodes p
    | .subst p q => nodes p + nodes q
    | .collection _ xs _ => forest xs
  def forest : List Pattern → Nat
    | [] => 0
    | x :: xs => nodes x + forest xs
end

private theorem forest_map (f : Pattern → Pattern) (xs : List Pattern)
    (same : ∀ x ∈ xs, nodes (f x) = nodes x) : forest (xs.map f) = forest xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, forest, same x List.mem_cons_self,
      ih (fun y h => same y (List.mem_cons_of_mem _ h))]

def rename (fromName into : String) : Row := ⟨fromName, [], .apply into []⟩

theorem rename_size (a b : String) (p : Pattern) :
    nodes (unfoldOne (rename a b) p) = nodes p := by
  induction p using Pattern.inductionOn with
  | hbvar i => rw [unfoldOne_bvar]
  | hfvar v => rw [unfoldOne_fvar]
  | happly h xs ih =>
    rw [unfoldOne_apply]
    split
    · rename_i chosen
      have nil : xs = [] := List.length_eq_zero_iff.mp chosen.2
      subst xs
      simp [rename, applyBindings, nodes, forest]
    · exact congrArg (1 + ·) (forest_map _ xs ih)
  | hlambda _ _ ih => simpa only [unfoldOne_lambda, nodes] using ih
  | hmultiLambda _ _ _ ih => simpa only [unfoldOne_multiLambda, nodes] using ih
  | hsubst _ _ ih₁ ih₂ => simp only [unfoldOne_subst, nodes, ih₁, ih₂]
  | hcollection _ xs _ ih => exact (by rw [unfoldOne_collection]; exact forest_map _ xs ih)

theorem flat_aliases_preserve_size (aliases : List (String × String)) (p : Pattern) :
    nodes (expand (aliases.map fun ab => rename ab.1 ab.2) p) = nodes p := by
  induction aliases with
  | nil => rfl
  | cons ab rest ih => simpa only [List.map_cons, expand_cons, rename_size] using ih

def duplicate : Row := ⟨"Dup", ["x"], .apply "Pair" [.fvar "x", .fvar "x"]⟩
def input : Nat → Pattern
  | 0 => .apply "Z" []
  | n+1 => .apply "Dup" [input n]
def tree : Nat → Pattern
  | 0 => .apply "Z" []
  | n+1 => .apply "Pair" [tree n, tree n]

theorem normalize_input (n : Nat) : expand [duplicate] (input n) = tree n := by
  change unfoldOne duplicate (input n) = _
  induction n with
  | zero => rw [input, unfoldOne_apply]; rfl
  | succ n ih =>
    rw [input, unfoldOne_apply]
    simp [duplicate, applyBindings, tree]
    exact ih

theorem input_size (n : Nat) : nodes (input n) = n+1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [input, nodes, forest, ih, Nat.add_comm]

theorem tree_size (n : Nat) : nodes (tree n) + 1 = 2^(n+1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [tree, nodes, forest, forest, forest, pow_succ]
    omega

def graph : DemandSummary.Graph String where
  label
    | 0 => "Z"
    | _+1 => "Pair"
  children
    | 0 => []
    | n+1 => [⟨n, Nat.lt_succ_self n⟩, ⟨n, Nat.lt_succ_self n⟩]

private theorem eager_tree (n : Nat) : DemandSummary.eager graph Pattern.apply n = tree n := by
  induction n with
  | zero => rw [DemandSummary.eager]; rfl
  | succ n ih =>
    rw [DemandSummary.eager]
    change Pattern.apply "Pair" [DemandSummary.eager graph Pattern.apply n,
      DemandSummary.eager graph Pattern.apply n] = _
    rw [ih]; rfl

/-- The same key, not an approximation: at most n+1 distinct node
combinations versus 2^(n+1)-1 constructor occurrences if fully emitted.
This is not a time bound for hashing, printing, or deep equality. -/
theorem shared_normal_form (n : Nat) :
    let built := DemandSummary.demand graph Pattern.apply n (fun _ => none)
    built.value = expand [duplicate] (input n) ∧ built.computed.length ≤ n+1 ∧
      nodes built.value + 1 = 2^(n+1) := by
  have valid := DemandSummary.demand_valid graph Pattern.apply n _ (DemandSummary.empty_sound _ _)
  have same := valid.value_eq.trans (eager_tree n)
  refine ⟨same.trans (normalize_input n).symm, ?_, same ▸ tree_size n⟩
  rw [← List.toFinset_card_of_nodup valid.nodup]
  refine (Finset.card_le_card (t := Finset.range (n+1)) ?_).trans (Finset.card_range _).le
  intro i hi
  exact Finset.mem_range.mpr (valid.bounded i (List.mem_toFinset.mp hi))

end Mettapedia.GSLT.LanguageDef.DefinitionalKeySize
