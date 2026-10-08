import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalJudgmentRegularity
import Mettapedia.TypeTheory.Calculi.NativeDependent.Examples.ExternalSigmaEliminationControls

/-!
# Regularity with changing dependent annotations

A higher-order family distinguishes raw annotations at a function and its eta
expansion. Actual generated equations recover both admissions and the common
typed second side. The full-pair eliminator recovers a supplied witness at the
result type mentioning an actual first projection, beyond its original raw
declaration annotation. Raw syntax equality does not follow from regularity.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External.RegularityControls

open Contextual ContextualControls TypeOperationControls SigmaEliminationControls
open JudgmentRegularity

theorem family_equation_recovers_both_admissions :
    Holds signature (.type functionContext.raw firstFamily.code) ∧
      Holds signature (.type functionContext.raw secondFamily.code) :=
  typeEquality annotations_equal

theorem function_equation_recovers_both_terms :
    Holds signature (.term functionContext.raw expandedFunction (functionType 1)) ∧
      Holds signature (.term functionContext.raw suppliedFunction (functionType 1)) :=
  termEquality function_eta

theorem arguments_equation_recovers_both_substitutions :
    Holds signature (.substitution functionContext.raw functionContext.raw firstArguments) ∧
      Holds signature (.substitution functionContext.raw functionContext.raw secondArguments) :=
  substitutionEquality arguments_equal

theorem annotation_contexts_equal : Holds signature
    (.contextEq (extend functionContext firstFamily).raw (extend functionContext secondFamily).raw) :=
  conclude (.contextExtendEquality functionContext.raw functionContext.raw firstFamily.code secondFamily.code)
    ⟨conclude (.contextReflexivity functionContext.raw) ⟨functionContext.formed.judgment, trivial⟩,
      annotations_equal, secondFamily.formed, trivial⟩

theorem context_equation_recovers_both_telescopes :
    Formed signature (extend functionContext firstFamily).raw ∧
      Formed signature (extend functionContext secondFamily).raw :=
  contextEquality annotation_contexts_equal

theorem regularity_does_not_identify_raw_contexts :
    (extend functionContext firstFamily).raw ≠ (extend functionContext secondFamily).raw :=
  extension_changes_annotation

theorem mixed_lambda_equation : Holds signature (.termEq functionContext.raw
    firstIdentity.code secondIdentity.code (DependentTypes.rawPi firstFamily firstAnnotation).code) :=
  ((QTerm.mk_eq_iff _ _).mp mixed_identity_annotations).2

theorem mixed_lambda_recovers_common_second_type : Holds signature
    (.term functionContext.raw secondIdentity.code (DependentTypes.rawPi firstFamily firstAnnotation).code) :=
  (termEquality mixed_lambda_equation).2

theorem common_lambda_type_differs_from_original_annotation :
    (DependentTypes.rawPi firstFamily firstAnnotation).code ≠
      (DependentTypes.rawPi secondFamily rightAnnotation).code := by
  intro same
  exact different_annotation_syntax (TypeExpr.pi.inj same).1

theorem full_motive_equation : Holds signature
    (.termEq witnessContext.raw literalEliminator.code witness.code
      (completeMotive.reindex (QuotientComprehensionSyntax.nativeSection dependentPair)).code) :=
  ((QTerm.mk_eq_iff _ _).mp literal_elimination_retains_supplied_witness).2

theorem full_motive_witness_retyped : Holds signature
    (.term witnessContext.raw witness.code
      (completeMotive.reindex (QuotientComprehensionSyntax.nativeSection dependentPair)).code) :=
  (termEquality full_motive_equation).2

theorem full_motive_context_and_type_formed :
    Formed signature witnessContext.raw ∧ Holds signature
      (.type witnessContext.raw
        (completeMotive.reindex (QuotientComprehensionSyntax.nativeSection dependentPair)).code) :=
  ⟨(holds full_motive_equation).contextFormed, (holds full_motive_equation).typeFormed⟩

theorem common_result_differs_from_original_witness_annotation :
    (completeMotive.reindex (QuotientComprehensionSyntax.nativeSection dependentPair)).code ≠
      firstAnnotation.code := by
  rw [motive_at_supplied_pair, projection_shifts_parameter]
  intro same
  have arguments := eq_of_heq (TypeExpr.family.inj same).2
  have values := congrFun arguments 0
  cases values

end Mettapedia.TypeTheory.Calculi.NativeDependent.External.RegularityControls
