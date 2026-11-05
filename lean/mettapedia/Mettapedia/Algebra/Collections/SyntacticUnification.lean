import Mettapedia.Algebra.Collections.Unification
import Mettapedia.Logic.Unification.ListSpliceEncoding

/-!
# Syntactic collection unification has an empty or singleton complete basis

The existing first-order list-splice solver supplies the basis. Expressions,
proper lists and one-tail open spines retain their distinct constructors;
the declared splice equations are the only quotient used. A successful basis
contains one MGU representative, not the entire solution set. Any other
singleton complete basis is equivalent by mutual source factorization.
This does not classify unrestricted associative sequence-variable equations.
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.Collections.SyntacticUnification

open Mettapedia.Logic.Unification.ListSplice
open Encoding (MoreGeneral encodeSubst)
open Collections.Unification (IsComplete Unitary)

variable {Leaf Var : Type}

abbrev Substitution (Leaf Var : Type) := Var → Term Leaf Var

def Solves (left right : Term Leaf Var) (substitution : Substitution Leaf Var) : Prop :=
  Equivalent (subst substitution left) (subst substitution right)

theorem factor_refl (substitution : Substitution Leaf Var) : MoreGeneral substitution substitution :=
  (Encoding.moreGeneral_iff _ _).mpr (Mettapedia.Logic.LP.Subst.moreGeneral_refl _)

theorem factor_trans {first middle last : Substitution Leaf Var}
    (earlier : MoreGeneral first middle) (later : MoreGeneral middle last) : MoreGeneral first last :=
  (Encoding.moreGeneral_iff _ _).mpr (Mettapedia.Logic.LP.Subst.moreGeneral_trans
    ((Encoding.moreGeneral_iff _ _).mp earlier) ((Encoding.moreGeneral_iff _ _).mp later))

/-- Instantiation of a source solution preserves the equation modulo exactly
the existing splice congruence. -/
theorem instance_solves (left right : Term Leaf Var) (general specific : Substitution Leaf Var)
    (solved : Solves left right general) (instanceOf : MoreGeneral general specific) : Solves left right specific := by
  apply (Encoding.solution_iff _ _ _).mpr
  obtain ⟨residual, factors⟩ := (Encoding.moreGeneral_iff _ _).mp instanceOf
  have same : encodeSubst specific = Mettapedia.Logic.LP.Subst.comp residual (encodeSubst general) := funext factors
  rw [same, Mettapedia.Logic.LP.Subst.applyTerm_comp, Mettapedia.Logic.LP.Subst.applyTerm_comp]
  exact congrArg residual.applyTerm ((Encoding.solution_iff _ _ _).mp solved)

variable [DecidableEq Leaf] [DecidableEq Var]

/-- The basis is the actual solver's optional result, viewed as a set. -/
def basis (left right : Term Leaf Var) : Set (Substitution Leaf Var) :=
  {substitution | Encoding.solve left right = some substitution}

@[simp] theorem mem_basis (left right : Term Leaf Var) (substitution : Substitution Leaf Var) :
    substitution ∈ basis left right ↔ Encoding.solve left right = some substitution := Iff.rfl

theorem basis_complete (left right : Term Leaf Var) :
    IsComplete (Solves left right) MoreGeneral (basis left right) := by
  constructor
  · intro substitution accepted
    exact Encoding.solve_sound left right substitution accepted
  · intro candidate solved
    obtain ⟨substitution, accepted⟩ := Encoding.solve_complete left right ⟨candidate, solved⟩
    exact ⟨substitution, accepted, Encoding.solve_mgu left right substitution accepted candidate solved⟩

theorem basis_subsingleton (left right : Term Leaf Var) : (basis left right).Subsingleton := by
  intro first firstIn second secondIn
  exact Option.some.inj (firstIn.symm.trans secondIn)

theorem unitary (left right : Term Leaf Var) : Unitary (Solves left right) MoreGeneral :=
  ⟨basis left right, basis_complete left right, basis_subsingleton left right⟩

theorem basis_of_some (left right : Term Leaf Var) (substitution : Substitution Leaf Var)
    (accepted : Encoding.solve left right = some substitution) : basis left right = {substitution} := by
  ext candidate
  simp only [mem_basis, accepted, Option.some.injEq, Set.mem_singleton_iff]
  exact eq_comm

theorem singleton_complete (left right : Term Leaf Var) (substitution : Substitution Leaf Var)
    (accepted : Encoding.solve left right = some substitution) :
    IsComplete (Solves left right) MoreGeneral {substitution} := by
  rw [← basis_of_some left right substitution accepted]
  exact basis_complete left right

theorem basis_empty_iff_failure (left right : Term Leaf Var) :
    basis left right = ∅ ↔ Encoding.solve left right = none := by
  constructor
  · intro empty
    cases result : Encoding.solve left right with
    | none => rfl
    | some substitution =>
        have member : substitution ∈ basis left right := result
        rw [empty] at member
        cases member
  · intro failed
    ext substitution
    simp [basis, failed]

theorem basis_empty_iff_unsatisfiable (left right : Term Leaf Var) :
    basis left right = ∅ ↔ ¬∃ substitution, Solves left right substitution := by
  rw [basis_empty_iff_failure]
  exact Encoding.solve_none_iff left right

/-- Existence of a solution produces a singleton complete basis through the
actual solver. Unsatisfiable problems use the empty basis instead. -/
theorem solvable_has_singleton_basis (left right : Term Leaf Var)
    (solvable : ∃ substitution, Solves left right substitution) :
    ∃ substitution, Encoding.solve left right = some substitution ∧
      IsComplete (Solves left right) MoreGeneral {substitution} := by
  obtain ⟨substitution, accepted⟩ := Encoding.solve_complete left right solvable
  exact ⟨substitution, accepted, singleton_complete left right substitution accepted⟩

omit [DecidableEq Leaf] [DecidableEq Var] in
/-- Generality, not equality of raw substitution syntax, is the uniqueness
criterion for most-general representatives. -/
theorem singleton_bases_mutually_factor (left right : Term Leaf Var) (first second : Substitution Leaf Var)
    (firstComplete : IsComplete (Solves left right) MoreGeneral {first})
    (secondComplete : IsComplete (Solves left right) MoreGeneral {second}) :
    MoreGeneral first second ∧ MoreGeneral second first := by
  obtain ⟨representative, member, forward⟩ := firstComplete.covers second (secondComplete.sound second (by simp))
  have firstEq : representative = first := Set.mem_singleton_iff.mp member
  subst representative
  obtain ⟨representative, member, backward⟩ := secondComplete.covers first (firstComplete.sound first (by simp))
  have secondEq : representative = second := Set.mem_singleton_iff.mp member
  subst representative
  exact ⟨forward, backward⟩

theorem solver_mgu_unique_up_to_factorization (left right : Term Leaf Var)
    (actual other : Substitution Leaf Var) (accepted : Encoding.solve left right = some actual)
    (otherComplete : IsComplete (Solves left right) MoreGeneral {other}) :
    MoreGeneral actual other ∧ MoreGeneral other actual :=
  singleton_bases_mutually_factor left right actual other (singleton_complete left right actual accepted) otherComplete

theorem expression_unitary (left right : List (Term Leaf Var)) :
    Unitary (Solves (.expr left) (.expr right)) MoreGeneral := unitary _ _

theorem proper_list_unitary (left right : List (Term Leaf Var)) :
    Unitary (Solves (.list left) (.list right)) MoreGeneral := unitary _ _

theorem open_rest_unitary (left right : List (Term Leaf Var)) (leftTail rightTail : Term Leaf Var) :
    Unitary (Solves (.rest left leftTail) (.rest right rightTail)) MoreGeneral := unitary _ _

namespace Controls

theorem expression_has_an_actual_singleton_basis :
    ∃ substitution, Encoding.solve (Term.expr [.var 0, .atom 9] : Term Nat Nat) (.expr [.atom 7, .atom 9]) = some substitution ∧
      IsComplete (Solves (.expr [.var 0, .atom 9]) (.expr [.atom 7, .atom 9])) MoreGeneral {substitution} := by
  apply solvable_has_singleton_basis
  refine ⟨fun _ => .atom 7, ?_⟩
  simp only [Solves, subst, List.map_cons, List.map_nil]
  exact Equivalent.refl _

theorem proper_list_has_an_actual_singleton_basis :
    ∃ substitution, Encoding.solve (Term.list [.var 0] : Term Nat Nat) (.list [.atom 7]) = some substitution ∧
      IsComplete (Solves (.list [.var 0]) (.list [.atom 7])) MoreGeneral {substitution} := by
  apply solvable_has_singleton_basis
  refine ⟨fun _ => .atom 7, ?_⟩
  simp only [Solves, subst, List.map_cons, List.map_nil]
  exact Equivalent.refl _

theorem open_rest_has_an_actual_singleton_basis :
    ∃ substitution, Encoding.solve (Term.rest [.var 0] (.var 1) : Term Nat Nat) (.list [.atom 1, .atom 2]) = some substitution ∧
      IsComplete (Solves (.rest [.var 0] (.var 1)) (.list [.atom 1, .atom 2])) MoreGeneral {substitution} := by
  apply solvable_has_singleton_basis
  refine ⟨fun name : Nat => if name = 0 then .atom 1 else .list [.atom 2], ?_⟩
  apply (equivalent_iff_normalize_eq _ _).mpr
  simp [subst, normalize]

theorem expression_and_list_clash : basis (Term.expr [] : Term Nat Nat) (.list []) = ∅ := by
  rw [basis_empty_iff_unsatisfiable]
  rintro ⟨substitution, solved⟩
  have impossible := solved.normalize_eq
  simp [subst, normalize] at impossible

theorem tuple_arity_clash : basis (Term.expr [.var 0] : Term Nat Nat) (.expr []) = ∅ := by
  rw [basis_empty_iff_unsatisfiable]
  rintro ⟨substitution, solved⟩
  have impossible := solved.normalize_eq
  simp [subst, normalize] at impossible

theorem constant_clash : basis (Term.atom 1 : Term Nat Nat) (.atom 2) = ∅ := by
  rw [basis_empty_iff_unsatisfiable]
  rintro ⟨substitution, solved⟩
  have impossible := solved.normalize_eq
  simp [subst, normalize] at impossible

theorem occurs_cycle_has_empty_basis : basis (Term.var 0 : Term Nat Nat) (.rest [.atom 1] (.var 0)) = ∅ := by
  rw [basis_empty_iff_failure, Encoding.solve_none_iff]
  rintro ⟨substitution, solved⟩
  apply Mettapedia.Logic.Unification.ListPrefixMeeting.occurs_rest_unsatisfiable (Leaf := Nat) (Var := Nat) 0 (.const (.atom 1))
  refine ⟨encodeSubst substitution, ?_⟩
  simpa only [Encoding.encode, List.map_cons, List.map_nil] using (Encoding.solution_iff _ _ _).mp solved

theorem empty_splice_is_not_an_occurs_cycle :
    ∃ substitution, Encoding.solve (Term.var 0 : Term Nat Nat) (.rest [] (.var 0)) = some substitution := by
  apply Encoding.solve_complete
  refine ⟨Term.var, ?_⟩
  simpa only [subst, List.map_nil] using (Equivalent.emptyRest (Term.var 0 : Term Nat Nat)).symm

theorem unitary_does_not_mean_one_raw_solution :
    ∃ first second : Substitution Nat Nat,
      Solves (.var 0) (.var 0) first ∧ Solves (.var 0) (.var 0) second ∧ first ≠ second := by
  refine ⟨fun _ => .atom 1, fun _ => .atom 2, Equivalent.refl _, Equivalent.refl _, ?_⟩
  intro same
  have impossible := congrFun same 0
  cases impossible

end Controls

end Mettapedia.Algebra.Collections.SyntacticUnification

#print axioms Mettapedia.Algebra.Collections.SyntacticUnification.basis_complete
#print axioms Mettapedia.Algebra.Collections.SyntacticUnification.unitary
#print axioms Mettapedia.Algebra.Collections.SyntacticUnification.solver_mgu_unique_up_to_factorization
