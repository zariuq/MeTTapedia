import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.SourceBindingAction

/-!
# Definition support and source admission under name bijections

The source gate checks closedness and the support of displayed type
parameters, independently of binder spelling. These conditions are preserved
and reflected on the actual source syntax; declaration freshness is handled
by the real name context. Type-definition existence remains separate.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.SourceDefinitionAction

open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight.DefinitionAdapters
open SourceNameAction SourceSignatureAction SourceBindingAction

mutual
  theorem type_parameters (names : Names) (type : Ty) :
      (mapType names type).typeVariables = type.typeVariables.image names.parameters := by
    cases type <;> simp [mapType, Ty.typeVariables, types_parameters]
  termination_by structural type

  theorem types_parameters (names : Names) (types : List Ty) :
      Ty.typeVariablesList (mapTypes names types) = (Ty.typeVariablesList types).image names.parameters := by
    cases types <;> simp [mapTypes, Ty.typeVariablesList, type_parameters, types_parameters, Finset.image_union]
  termination_by structural types
end

theorem term_parameters (names : Names) (term : DBTerm) :
    (mapDB names term).typeVariables = term.typeVariables.image names.parameters := by
  induction term <;> simp_all [mapDB, DBTerm.typeVariables, mapVariable, type_parameters, Finset.image_union]

theorem closed_test (names : Names) (term : DBTerm) :
    (mapDB names term).hasNoFreeVariables = term.hasNoFreeVariables := by
  induction term <;> simp_all [mapDB, DBTerm.hasNoFreeVariables]

theorem closedness (names : Names) (term : DBTerm) :
    (mapDB names term).HasNoFreeVariables ↔ term.HasNoFreeVariables := by
  rw [← DBTerm.hasNoFreeVariables_eq_true_iff, ← DBTerm.hasNoFreeVariables_eq_true_iff, closed_test]

theorem checked_source_shape {source : SourceTerm} {result : CanonicalTerm}
    (accepted : source.check = some result) :
    result.term = source.toDB [] ∧ source.inferType = some result.ty := by
  simp only [SourceTerm.check] at accepted
  split at accepted
  · rename_i type found
    cases Option.some.inj accepted
    exact ⟨rfl, (DBTerm.inferType_toDB [] source).symm.trans found⟩
  · cases accepted

theorem source_check {source : SourceTerm} {result : CanonicalTerm}
    (shape : result.term = source.toDB []) : source.check = some result := by
  have typed : (source.toDB []).inferType [] = some result.ty := shape ▸ result.checked
  simp only [SourceTerm.check]
  split
  · rename_i type found
    apply congrArg some
    apply CanonicalTerm.ext_term
    exact shape.symm
  · rename_i absent
    rw [typed] at absent
    cases absent

theorem check_action (names : Names) (fixed : FunctionFixed names) (source : SourceTerm) :
    (mapTerm names source).check = source.check.map (mapCanonical names fixed) := by
  cases accepted : source.check with
  | none =>
      have absent := (SourceTerm.check_eq_none_iff source).mp accepted
      apply (SourceTerm.check_eq_none_iff _).mpr
      rw [inference names fixed, absent]
      rfl
  | some result =>
      simp only [Option.map_some]
      apply source_check
      change mapDB names result.term = _
      rw [(checked_source_shape accepted).1]
      exact (canonicalization names [] source).symm

theorem function_fixed_symm (names : Names) (fixed : FunctionFixed names) : FunctionFixed names.symm := by
  change names.operators.symm (Name.global "->") = Name.global "->"
  apply names.operators.injective
  simpa only [Equiv.apply_symm_apply] using fixed.symm

theorem constant_admissible_forward (names : Names) (fixed : FunctionFixed names) (source : SourceTerm)
    (admitted : ConstantDefinitionAdmissible source) : ConstantDefinitionAdmissible (mapTerm names source) := by
  obtain ⟨body, checked, closed, supported⟩ := admitted
  refine ⟨mapCanonical names fixed body, ?_, ?_, ?_⟩
  · rw [check_action names fixed, checked]
    rfl
  · exact (closedness names body.term).mpr closed
  · change (mapDB names body.term).typeVariables ⊆ (mapType names body.ty).typeVariables
    rw [term_parameters, type_parameters]
    exact Finset.image_subset_image supported

theorem constant_admissible (names : Names) (fixed : FunctionFixed names) (source : SourceTerm) :
    ConstantDefinitionAdmissible (mapTerm names source) ↔ ConstantDefinitionAdmissible source := by
  constructor
  · intro admitted
    have back := constant_admissible_forward names.symm (function_fixed_symm names fixed)
      (mapTerm names source) admitted
    simpa only [term_roundtrip] using back
  · exact constant_admissible_forward names fixed source

theorem named_constant_admissible (names : Names) (fixed : FunctionFixed names)
    (context : NameContext) (name : Name) (source : SourceTerm) :
    ConstantAdmissible (mapNameContext names context) (names.constants name) (mapTerm names source) ↔
      ConstantAdmissible context name source := by
  change (mapDeclaredName names (.constant name) ∉ mapNameContext names context ∧ _) ↔ _
  simp only [ConstantAdmissible, declared_member, constant_admissible names fixed]

/-- This is the actual freshness-and-definition gate, not a new gate with
the transported judgment supplied as an admission field. -/
theorem constant_gate (names : Names) (fixed : FunctionFixed names)
    (context : NameContext) (name : Name) (source : SourceTerm) :
    (admitConstant (mapNameContext names context) (names.constants name) (mapTerm names source)).isSome =
      (admitConstant context name source).isSome := by
  apply Bool.eq_iff_iff.mpr
  simp only [admitConstant_isSome_iff, named_constant_admissible names fixed]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.SourceDefinitionAction
