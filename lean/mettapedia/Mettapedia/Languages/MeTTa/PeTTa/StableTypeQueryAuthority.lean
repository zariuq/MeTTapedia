import Mettapedia.Languages.MeTTa.PeTTa.Effects

/-!
# Reached-world admission for the base intrinsic guard

The base relational guard and the explicitly selected committed-contract
profile are different boundaries. Intrinsic substitution also requires that
the current source does not extend its classifiers. Unsupported equation
heads conservatively prevent admission rather than disappearing from lookup.
Native protection flags and region-local dependency checks remain separate
refinements of this sufficient source condition.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.StableTypeQueryAuthority

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

def classifierName (head : String) : Bool := head == "get-type" || head == "get-metatype"

def equationKeepsIntrinsic : Atom → Bool
  | .expression [.symbol "=", .expression (.symbol head :: arguments), _] =>
      !(classifierName head && arguments.length == 1)
  | .expression [.symbol "=", _, _] => false
  | _ => true

def symbolAnnotation : Atom → Bool
  | .expression [.symbol ":", .symbol _, _] => true
  | .expression [.symbol ":", _, _] => false
  | _ => true

def admitted (callContracts : Bool) (state : Effects.State) : Bool :=
  !callContracts && state.core.all equationKeepsIntrinsic && state.core.all symbolAnnotation

theorem committed_profile_is_distinct (state : Effects.State) : admitted true state = false := rfl

theorem admits_current_rows (state : Effects.State) (accepted : admitted false state = true) :
    (∀ row ∈ state.core, equationKeepsIntrinsic row = true) ∧
      (∀ row ∈ state.core, symbolAnnotation row = true) := by
  simpa [admitted] using accepted

theorem authored_classifier_blocks (state : Effects.State) (head : String) (argument body : Atom)
    (classifier : classifierName head = true)
    (present : .expression [.symbol "=", .expression [.symbol head, argument], body] ∈ state.core) :
    admitted false state = false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  have safe := (admits_current_rows state accepted).1 _ present
  simp [equationKeepsIntrinsic, classifier] at safe

theorem subject_refining_annotation_blocks (state : Effects.State) (subject type : Atom)
    (notSymbol : ∀ name, subject ≠ .symbol name)
    (present : .expression [.symbol ":", subject, type] ∈ state.core) :
    admitted false state = false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  have safe := (admits_current_rows state accepted).2 _ present
  cases subject with
  | symbol name => exact notSymbol name rfl
  | var _ | grounded _ | expression _ => simp [symbolAnnotation] at safe

theorem admitted_empty : admitted false Effects.empty = true := rfl

end Mettapedia.Languages.MeTTa.PeTTa.StableTypeQueryAuthority
