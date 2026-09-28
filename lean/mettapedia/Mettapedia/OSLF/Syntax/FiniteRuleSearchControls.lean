import Mettapedia.OSLF.Syntax.FiniteRuleSearchCompleteness

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.FiniteRuleSearch.Controls

open Mettapedia.TypeTheory
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists

inductive Goal where
  | atom | pair | loop | impossible | delayed
  deriving DecidableEq

inductive Shape : Goal → Type where
  | left : Shape .atom
  | right : Shape .atom
  | pair : Shape .pair
  | loop : Shape .loop
  | blocked : Shape .delayed
  | available : Shape .delayed

def theory : FinitePresentation Unit (fun _ => Goal) where
  Shape _ := Shape
  premises _ _ shape := match shape with
    | .left | .right | .available => []
    | .pair => [.atom, .atom]
    | .loop => [.loop]
    | .blocked => [.loop, .impossible]

def selected : (j : Goal) → Candidates theory j
  | .atom => ⟨[.left, .right], true, by
      intro _ s
      cases s with
      | left => exact List.mem_cons_self ..
      | right => exact List.mem_cons_of_mem _ (List.mem_cons_self ..)⟩
  | .pair => ⟨[.pair], true, by
      intro _ s; cases s; exact List.mem_cons_self ..⟩
  | .loop => ⟨[.loop], true, by
      intro _ s; cases s; exact List.mem_cons_self ..⟩
  | .impossible => ⟨[], true, by intro _ s; cases s⟩
  | .delayed => ⟨[.blocked, .available], true, by
      intro _ s
      cases s with
      | blocked => exact List.mem_cons_self ..
      | available => exact List.mem_cons_of_mem _ (List.mem_cons_self ..)⟩

def leafLeft : theory.Derivation () .atom := .roll .left (noEvidence _)
def leafRight : theory.Derivation () .atom := .roll .right (noEvidence _)

def leftRight : theory.Derivation () .pair :=
  .roll .pair (consEvidence _ leafLeft (consEvidence _ leafRight (noEvidence _)))
def rightLeft : theory.Derivation () .pair :=
  .roll .pair (consEvidence _ leafRight (consEvidence _ leafLeft (noEvidence _)))

theorem leaves_distinct : leafLeft ≠ leafRight := by intro h; cases h

def first (tree : theory.Derivation () .pair) : theory.Derivation () .atom :=
  match tree with | .roll .pair children => children ⟨0, by decide⟩

theorem histories_distinct : leftRight ≠ rightLeft := by
  intro equal
  exact leaves_distinct (congrArg first equal)

theorem pair_established : (search theory selected 2 .pair).isEstablished = true := rfl
theorem pair_exhausted : (search theory selected 1 .pair).isIncomplete = true := rfl
theorem loop_exhausted : (search theory selected 8 .loop).isIncomplete = true := rfl
theorem impossible_refuted : (search theory selected 1 .impossible).isRefuted = true := rfl
theorem impossible_has_no_derivation : theory.Derivation () .impossible → False :=
  search_refuted_sound theory selected 1 .impossible impossible_refuted

theorem later_candidate_establishes :
    (search theory selected 1 .delayed).isEstablished = true := rfl

/-- An unfinished first premise does not hide a later disproved premise. -/
theorem disproved_premise_rules_out_candidate :
    (premises (search theory selected 1) [.loop, .impossible]).isRefuted = true := rfl

def omitted : (j : Goal) → Candidates theory j :=
  fun _ => ⟨[], false, by intro impossible; cases impossible⟩

/-- Empty partial selection cannot refute even this inhabited atomic goal. -/
theorem omitted_is_incomplete : (search theory omitted 3 .atom).isIncomplete = true := rfl
theorem omitted_goal_inhabited : Nonempty (theory.Derivation () .atom) := ⟨leafLeft⟩

theorem supplied_history_covered : Covered theory selected 2 rightLeft := by
  constructor
  · exact List.mem_cons_self ..
  · intro p
    change Fin 2 at p
    cases p using Fin.cases with
    | zero => exact ⟨List.mem_cons_of_mem _ (List.mem_cons_self ..), fun p => Fin.elim0 p⟩
    | succ p =>
        cases p using Fin.cases with
        | zero => exact ⟨List.mem_cons_self .., fun p => Fin.elim0 p⟩
        | succ impossible => exact Fin.elim0 impossible

theorem covered_search_succeeds : (search theory selected 2 .pair).isEstablished = true :=
  search_complete_for_covered theory selected 2 rightLeft supplied_history_covered

def pairLeftLeft : theory.Derivation () .pair :=
  .roll .pair (consEvidence _ leafLeft (consEvidence _ leafLeft (noEvidence _)))

theorem selected_first_history : search theory selected 2 .pair = .established pairLeftLeft := rfl

theorem producer_need_not_return_witness : pairLeftLeft ≠ rightLeft := by
  intro equal
  exact leaves_distinct (congrArg first equal)

#eval (search theory selected 2 .pair).isEstablished
#eval (search theory selected 8 .loop).isIncomplete
#eval (search theory selected 1 .impossible).isRefuted
#eval (search theory omitted 3 .atom).isIncomplete

#print axioms search
#print axioms search_refuted_sound
#print axioms search_complete_for_covered
#print axioms histories_distinct
#print axioms supplied_history_covered

end Mettapedia.OSLF.Binding.FiniteRuleSearch.Controls
