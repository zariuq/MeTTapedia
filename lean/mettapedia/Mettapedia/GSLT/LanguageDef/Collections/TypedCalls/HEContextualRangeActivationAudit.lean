import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEContextualArithmeticSourceAudit
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEFreshEquationFramesAudit
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEIfSourceActivation

/-! Checked contextual arithmetic, equation frames and conditional activation.
The recursive range result and standard-library collapse lowering remain separate.
-/

#print axioms Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEStatefulSelectedComposition.selected_of_parts
#print axioms Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEBinaryNumericSource.return_demand
#print axioms Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEBinaryNumericSource.signature_match
#print axioms Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEBinaryNumericSource.signature_lookup
#print axioms Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEBinaryNumericSource.selection
#print axioms Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEBinaryNumericSource.operator_atom
#print axioms Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEBinaryNumericSource.call_read
#print axioms Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEBinaryNumericSource.source_call
#print axioms Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEBinaryNumericSource.addition_executes
#print axioms Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEBinaryNumericSource.greaterEqual_executes
#print axioms Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEBinaryNumericSource.primitive_source
#print axioms Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEBinaryNumericSource.addition_source
#print axioms Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEBinaryNumericSource.comparison_source
#print axioms Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEBinaryNumericSource.Controls.expression_range_projection
#print axioms Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEIfSourceSelection.signature_variant
#print axioms Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEIfSourceSelection.signature_lookup
#print axioms Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEIfSourceSelection.unknown_lookup
#print axioms Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEIfSourceSelection.unknown_argument
#print axioms Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEIfSourceSelection.selection
#print axioms Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEIfSourceSelection.Range.source_shape
#print axioms Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEIfSourceSelection.Range.condition_unknown
#print axioms Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEIfSourceSelection.Range.yes_unknown
#print axioms Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEIfSourceSelection.Range.no_unknown
#print axioms Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEIfSourceSelection.Range.if_declared
#print axioms Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEIfSourceSelection.Range.source_selection
#print axioms Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEIfSourceSelection.Range.raw_annotation_changes_applicability
#print axioms Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEHeldSourceArguments.metatype
#print axioms Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEHeldSourceArguments.held
#print axioms Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEHeldSourceArguments.pair
#print axioms Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEHeldSourceArguments.conditional
#print axioms Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEHeldSourceArguments.ground_read
#print axioms Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEHeldSourceArguments.Range.arguments
#print axioms Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEHeldSourceArguments.Range.recursive_branch_retained
#print axioms Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEIfOperatorSource.source
#print axioms Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEIfSourceActivation.selected_name_fresh
#print axioms Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEIfSourceActivation.source_activation
#print axioms Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEIfSourceActivation.retained_activation

