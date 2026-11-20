import Mettapedia.Languages.MeTTa.PeTTa.AtomNegativeFreshNamespaces

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.AtomNegativeFreshNamespaces.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.SubstitutionAlgebra (Subst subst)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MetaMeTTaComparison (atomAction)

private def integer (value : Int) : Atom := .grounded (.int value)
private def source : Frame := ⟨[(.var "x", integer 7)], by
  intro equation member
  obtain rfl := List.mem_singleton.mp member
  change Atom.var "x" ≠ integer 7
  decide +kernel⟩

private def callerAssignment : Subst := fun name =>
  if name = "x" then some (integer 9) else none

private theorem caller_separates : Disequality.Separates atomAction callerAssignment source.1 := by
  intro equation member
  obtain rfl := List.mem_singleton.mp member
  change integer 9 ≠ integer 7
  decide +kernel

private def target : Frame := Disequality.image callerAssignment source.1 caller_separates
private def caller : Hom source target := Disequality.toImage source callerAssignment caller_separates
private def protectedTerms : List Atom := [.var "x", .var "later"]
private def requested (index : Nat) : Subst := fun _ => some (integer (if index = 0 then 7 else 8))
private def joined : Hom source target := combine protectedTerms caller requested

theorem caller_and_first_local_keep_distinct_values :
    X.act joined (.var "x") = integer 9 ∧
      X.act joined (subst (AtomFreshNamespaces.opening (bound source protectedTerms) 0) (.var "x")) =
        integer 7 := by decide +kernel

theorem two_local_openings_are_independent :
    X.act joined (subst (AtomFreshNamespaces.opening (bound source protectedTerms) 0) (.var "x")) =
        integer 7 ∧
      X.act joined (subst (AtomFreshNamespaces.opening (bound source protectedTerms) 1) (.var "x")) =
        integer 8 := by decide +kernel

theorem joined_action_is_not_identity : X.act joined (.var "x") ≠ Atom.var "x" := by
  change integer 9 ≠ Atom.var "x"
  decide +kernel

theorem negative_frame_is_preserved : Disequality.Separates atomAction joined.1 source.1 :=
  combine_separates protectedTerms caller requested

private def refinementAssignment : Subst := fun name =>
  if name = "later" then some (integer 40) else none

private def refinement : Hom target target := ⟨refinementAssignment, by
  intro later separated equation member
  obtain rfl := List.mem_singleton.mp member
  change integer 9 ≠ integer 7
  decide +kernel⟩

theorem later_refinement_really_changes_a_protected_open_value :
    X.act joined (.var "later") = Atom.var "later" ∧
      X.act (X.comp refinement joined) (.var "later") = integer 40 := by decide +kernel

theorem later_refinement_preserves_caller_agreement :
    X.act (X.comp refinement joined) (.var "later") =
      X.act (X.comp refinement caller) (.var "later") :=
  combine_protected_after protectedTerms caller requested refinement (.var "later") (by simp [protectedTerms])

end Mettapedia.Languages.MeTTa.PeTTa.AtomNegativeFreshNamespaces.Controls
