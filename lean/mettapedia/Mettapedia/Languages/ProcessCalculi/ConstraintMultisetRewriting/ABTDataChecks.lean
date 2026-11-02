import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ABTProtectedParameters

/-!
# Boolean data conditions as ordinary ABT equality checks

The two Boolean codes are existing nullary ABT heads. A computed decision
becomes an equality check against the true code, and the protected-parameter
action fixes both codes. This proves the representation law; an application
must still retain and justify the computation that produced its decision.
An independently supplied true code has no such computational provenance.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ABTDataChecks

open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT

variable {Head : Type}

def boolean (falseHead trueHead : Head) : Bool → Term Head
  | false => .node falseHead .nil
  | true => .node trueHead .nil

theorem boolean_supported (falseHead trueHead : Head) (width : Nat) (decision : Bool) :
    Term.supportedAt width (boolean falseHead trueHead decision) = true := by
  cases decision <;> rfl

theorem boolean_fixed (falseHead trueHead : Head) (width : Nat) (decision : Bool) :
    FixedMatching.Fixed (ABTProtectedParameters.action width) (boolean falseHead trueHead decision) :=
  ABTProtectedParameters.fixed_of_supported _ _ (boolean_supported falseHead trueHead width decision)

theorem boolean_eq_true_iff (falseHead trueHead : Head) (distinct : falseHead ≠ trueHead)
    (decision : Bool) :
    boolean falseHead trueHead decision = boolean falseHead trueHead true ↔ decision = true := by
  cases decision <;> simp [boolean, distinct]

def check (falseHead trueHead : Head) (decision : Bool) : Check (Term Head) :=
  .equal (boolean falseHead trueHead decision) (boolean falseHead trueHead true)

theorem holds_iff {O : Type*} (falseHead trueHead : Head) (distinct : falseHead ≠ trueHead)
    (width : Nat) (decision : Bool) (assignment : ABTProtectedParameters.Assignment Head width)
    (label : O → Term Head) (world : Finset O) :
    (check falseHead trueHead decision).Holds (ABTProtectedParameters.action width) assignment label world ↔
      decision = true := by
  change (ABTProtectedParameters.action width).apply assignment (boolean falseHead trueHead decision) =
    (ABTProtectedParameters.action width).apply assignment (boolean falseHead trueHead true) ↔ _
  rw [boolean_fixed falseHead trueHead width decision assignment,
    boolean_fixed falseHead trueHead width true assignment]
  exact boolean_eq_true_iff falseHead trueHead distinct decision

theorem entails_iff {O : Type*} (falseHead trueHead : Head) (distinct : falseHead ≠ trueHead)
    (width : Nat) (decision : Bool) (problem : EquationStore (Term Head))
    (consistent : (ABTProtectedParameters.action width).Consistent problem)
    (label : O → Term Head) (world : Finset O) :
    (ABTProtectedParameters.action width).Entails problem
      (fun assignment => (check falseHead trueHead decision).Holds
        (ABTProtectedParameters.action width) assignment label world) ↔ decision = true := by
  constructor
  · intro entailed
    obtain ⟨assignment, models⟩ := consistent
    exact (holds_iff falseHead trueHead distinct width decision assignment label world).mp
      (entailed assignment models)
  · intro computed assignment _
    exact (holds_iff falseHead trueHead distinct width decision assignment label world).mpr computed

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ABTDataChecks
