import Mettapedia.Languages.MeTTa.PeTTa.AtomFreshNamespaces

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.AtomFreshNamespaces.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.SubstitutionAlgebra (Subst subst)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MetaMeTTaComparison (atomAction)
open RuleSyntax OneFrame JointFirings LibTransformStep

private def clause : Atom := .expression [.symbol "pm:clause", .symbol "f", .grounded (.int 0),
  .expression [.symbol "pm:head", .var "x"], .expression [.symbol "pm:lit", .var "x"]]

private def schema : Rule (Terms Atom) := ⟨PUnit.unit, ⟨[], [], [], [], [clause]⟩, []⟩

private def member (bound index : Nat) : OneMember atomAction Nat (Set.univ : Program (Terms Atom)) :=
  ⟨schema, Set.mem_univ _, opening bound index, ⟨[], [], []⟩, []⟩

private def caller : Subst := fun name => if name = "x" then some (.grounded (.int 42)) else none
private def wanted : Nat → Subst := fun index name =>
  if name = "x" then some (.grounded (.int (Int.ofNat (index + 7)))) else none

theorem untagged_caller_variable_is_bounded : Bounded 0 (.var "x") := by
  intro name member scope original decoded
  have same : name = "x" := List.mem_singleton.mp member
  subst name
  have plain : untag "x" = none := rfl
  rw [plain] at decoded
  cases decoded

theorem caller_and_local_use_same_source_spelling :
    subst (combine 0 caller wanted) (.var "x") = .grounded (.int 42) := by decide +kernel

theorem first_local_assignment_is_independent :
    subst (combine 0 caller wanted) (subst (opening 0 0) (.var "x")) = .grounded (.int 7) := by
  decide +kernel

theorem second_local_assignment_is_independent :
    subst (combine 0 caller wanted) (subst (opening 0 1) (.var "x")) = .grounded (.int 8) := by
  decide +kernel

theorem unanswered_local_does_not_capture_caller :
    subst (combine 0 caller (fun _ _ => none)) (subst (opening 0 1) (.var "x")) = .var "x" := by
  decide +kernel

theorem arbitrary_encoded_source_names_are_reserved :
    Bounded (supportBound [.var (tag 9 "λ"), .var "unencoded"])
      (.var (tag 9 "λ")) := bounded_of_mem (List.mem_cons_self)

theorem zero_bound_would_alias_an_existing_tag : ¬ Bounded 0 (.var (tag 0 "x")) := by
  intro bounded
  have impossible := bounded _ (by simp [Mettapedia.Languages.MeTTa.SubstitutionAlgebra.vars])
    0 "x" (untag_tag _ _)
  omega

private def knowledge : EquationStore Atom := [(.var "caller", .var "retained")]
private def present : Finset Nat := {0}
private def label (_ : Nat) : Atom := .expression [.symbol "saved", .var "x", .var (tag 9 "λ")]
private noncomputable def bound : Nat := supportBound (sourceTerms knowledge present label)

/-- The same non-ground clause schema can be opened twice beside an open
retained caller. Both namespaces and the caller are jointly realizable. -/
theorem two_clause_uses_are_actually_fresh :
    Bag.Fresh X (⟨PUnit.unit, knowledge, present, label⟩ : State (Terms Atom) Nat)
      (⟨PUnit.unit, [member bound 0, member bound 1]⟩ :
        Bag Nat E (Set.univ : Program (Terms Atom)) PUnit.unit) := by
  exact fresh_from_support knowledge present label
    [(0, member bound 0), (1, member bound 1)] (by decide +kernel)
    (by
      intro entry inside
      simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
      rcases inside with rfl | rfl <;> rfl)

/-- Reusing one opening is not freshness: the two clause uses can ask for
different values of their own parameter. -/
theorem shared_clause_opening_is_not_fresh :
    ¬ Bag.Fresh X (⟨PUnit.unit, [], ∅, fun _ : Nat => .symbol "unused"⟩ : State (Terms Atom) Nat)
      (⟨PUnit.unit, [member 0 0, member 0 0]⟩ :
        Bag Nat E (Set.univ : Program (Terms Atom)) PUnit.unit) := by
  intro fresh
  have realized := fresh PUnit.unit atomAction.identity
  have first := realized (fun _ => some (.symbol "a"))
  obtain ⟨assignment, together⟩ := first (fun _ => some (.symbol "b"))
  have left := together.1.2 clause (by simp [member, schema, Rule.terms])
  have right := together.2 clause (by simp [member, schema, Rule.terms])
  have impossible := left.symm.trans right
  change subst (fun _ => some (.symbol "a")) clause =
    subst (fun _ => some (.symbol "b")) clause at impossible
  simp [clause, subst, subst.substList] at impossible

end Mettapedia.Languages.MeTTa.PeTTa.AtomFreshNamespaces.Controls
