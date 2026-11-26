import Mettapedia.GSLT.LanguageDef.InferenceChecker

/-! A node check after its local rule has been instantiated. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.InferenceChecker

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- After instantiation, replay at the exact conclusion checks the ordered child
proofs against the ordered premises. A missing or invalid child can still reject
this node. -/
theorem checkRaw_node_eq_of_instantiation {definition : ValidatedCalculusLanguageDef}
    {ruleInstance : RuleInstance} {premises : List Pattern} {conclusion : Pattern}
    (children : List RawProof)
    (instantiated : instantiateRule? definition ruleInstance = some (premises, conclusion)) :
    checkRaw definition conclusion (.node ruleInstance children) =
      checkRawChildren definition premises children := by
  rw [checkRaw, instantiated]
  simp

/-- The local declaration, valid arguments, and exact instantiations suffice to
select the child check. There is no dependence on the other rule bodies. -/
theorem checkRaw_node_eq_of_schema {definition : ValidatedCalculusLanguageDef}
    {schema : RuleSchema} {ruleInstance : RuleInstance} {premises : List Pattern}
    {conclusion : Pattern} (children : List RawProof)
    (lookup : definition.1.lookupRule? ruleInstance.ruleId = some schema)
    (valid : argumentsValidAt schema.metavariables ruleInstance.arguments = true)
    (side : RuleSchema.sideConditionsHold schema ruleInstance.arguments = true)
    (premisesInstance : instantiateSchemas? schema.metavariables ruleInstance.arguments
      schema.premises = some premises)
    (conclusionInstance : instantiateSchema? schema.metavariables ruleInstance.arguments
      schema.conclusion = some conclusion) :
    checkRaw definition conclusion (.node ruleInstance children) =
      checkRawChildren definition premises children :=
  checkRaw_node_eq_of_instantiation children <|
    instantiateRule?_eq_some_iff_application.mpr <|
      .intro schema lookup valid side (instantiateSchemasAt?_sound premisesInstance)
        (instantiateSchemaAt?_sound conclusionInstance)

/-- Compose a checked local application with the checks of its children. -/
theorem checkRaw_node_true_of_schema {definition : ValidatedCalculusLanguageDef}
    {schema : RuleSchema} {ruleInstance : RuleInstance} {premises : List Pattern}
    {conclusion : Pattern} {children : List RawProof}
    (lookup : definition.1.lookupRule? ruleInstance.ruleId = some schema)
    (valid : argumentsValidAt schema.metavariables ruleInstance.arguments = true)
    (side : RuleSchema.sideConditionsHold schema ruleInstance.arguments = true)
    (premisesInstance : instantiateSchemas? schema.metavariables ruleInstance.arguments
      schema.premises = some premises)
    (conclusionInstance : instantiateSchema? schema.metavariables ruleInstance.arguments
      schema.conclusion = some conclusion)
    (checked : checkRawChildren definition premises children = true) :
    checkRaw definition conclusion (.node ruleInstance children) = true :=
  (checkRaw_node_eq_of_schema children lookup valid side premisesInstance conclusionInstance).trans checked

end Mettapedia.GSLT.LanguageDef.InferenceChecker
