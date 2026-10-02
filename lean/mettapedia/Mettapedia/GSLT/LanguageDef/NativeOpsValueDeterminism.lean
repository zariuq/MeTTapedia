import Mettapedia.GSLT.LanguageDef.NativeOpsTargetValues

/-!
# Exact values of the native target

Pure reads and typed initializers cannot choose an additional result. These
uniqueness laws support reflection of emitted control fragments; they do not
assume determinism of physical allocation or external calls.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps

mutual
  theorem target_zero_unique {interface : Interface} {type : NativeType}
      {left right : TargetValue} (first : TargetZero interface type left)
      (second : TargetZero interface type right) : left = right := by
    cases first with
    | scalarUnit => cases second; rfl
    | unsignedWord => cases second; rfl
    | unsignedByte => cases second; rfl
    | boolean => cases second; rfl
    | nullPointer element => cases second; rfl
    | emptyView element => cases second; rfl
    | compound layout initializers =>
        cases second with
        | compound otherLayout otherInitializers =>
            have same := Option.some.inj (layout.symm.trans otherLayout)
            subst same
            exact congrArg _ (target_zero_fields_unique initializers otherInitializers)
  termination_by sizeOf left
  decreasing_by all_goals subst_vars; simp_wf; omega

  theorem target_zero_fields_unique {interface : Interface} {fields : List Parameter}
      {left right : List TargetValue} (first : TargetZeroFields interface fields left)
      (second : TargetZeroFields interface fields right) : left = right := by
    cases first with
    | endFields => cases second; rfl
    | nextField initializer remaining =>
        cases second with
        | nextField otherInitializer otherRemaining =>
            rw [target_zero_unique initializer otherInitializer,
              target_zero_fields_unique remaining otherRemaining]
  termination_by sizeOf left
  decreasing_by all_goals subst_vars; simp_wf; omega
end

theorem target_atom_unique {World : Type} {interface : Interface}
    {frame : TargetFrame} {state : TargetState World} {atom : NativeIR.Atom}
    {left right : TargetValue} (first : TargetAtomEval interface frame state atom left)
    (second : TargetAtomEval interface frame state atom right) : left = right := by
  cases first with
  | temporary found _ =>
      cases second with
      | temporary otherFound _ => exact Option.some.inj (found.symm.trans otherFound)
  | iterationCounter found _ =>
      cases second with
      | iterationCounter otherFound _ => exact Option.some.inj (found.symm.trans otherFound)
  | localAddress found =>
      cases second with
      | localAddress otherFound =>
          exact congrArg (fun address => TargetValue.reference (some address))
            (Option.some.inj (found.symm.trans otherFound))
  | word => cases second; rfl
  | zero initialized =>
      cases second with
      | zero otherInitialized => exact target_zero_unique initialized otherInitialized
  | unit => cases second; rfl

theorem target_atoms_unique {World : Type} {interface : Interface}
    {frame : TargetFrame} {state : TargetState World} {atoms : List NativeIR.Atom}
    {left right : List TargetValue} (first : TargetAtomsEval interface frame state atoms left)
    (second : TargetAtomsEval interface frame state atoms right) : left = right := by
  induction first generalizing right with
  | nil => cases second; rfl
  | cons head _ ih =>
      cases second with
      | cons otherHead otherTail => rw [target_atom_unique head otherHead, ih otherTail]

theorem target_pure_unique {World : Type} {interface : Interface}
    {frame : TargetFrame} {state : TargetState World} {operation : NativeIR.PureOperation}
    {left right : TargetValue} (first : TargetPureEval interface frame state operation left)
    (second : TargetPureEval interface frame state operation right) : left = right := by
  cases first with
  | word => cases second; rfl
  | byte => cases second; rfl
  | bool => cases second; rfl
  | zero initialized =>
      cases second with
      | zero otherInitialized => exact target_zero_unique initialized otherInitialized
  | copy read =>
      cases second with
      | copy otherRead => exact target_atom_unique read otherRead
  | «local» read =>
      cases second with
      | «local» otherRead => exact Option.some.inj (read.symm.trans otherRead)
  | fieldValue read field =>
      cases second with
      | fieldValue otherRead otherField =>
          have same := TargetValue.record.inj (target_atom_unique read otherRead)
          rcases same with ⟨_, same⟩
          subst same
          exact Option.some.inj (field.symm.trans otherField)
  | fieldAddress read =>
      cases second with
      | fieldAddress otherRead =>
          cases target_atom_unique read otherRead
          rfl
  | elementAddress view offset =>
      cases second with
      | elementAddress otherView otherOffset =>
          cases target_atom_unique view otherView
          cases target_atom_unique offset otherOffset
          rfl
  | indirect pointer read =>
      cases second with
      | indirect otherPointer otherRead =>
          cases target_atom_unique pointer otherPointer
          exact Option.some.inj (read.symm.trans otherRead)
  | length view =>
      cases second with
      | length otherView =>
          cases target_atom_unique view otherView
          rfl
  | unary read computed =>
      cases second with
      | unary otherRead otherComputed =>
          cases target_atom_unique read otherRead
          exact Option.some.inj (computed.symm.trans otherComputed)
  | binary readLeft readRight computed =>
      cases second with
      | binary otherLeft otherRight otherComputed =>
          cases target_atom_unique readLeft otherLeft
          cases target_atom_unique readRight otherRight
          exact Option.some.inj (computed.symm.trans otherComputed)

end Mettapedia.GSLT.LanguageDef.NativeOps
