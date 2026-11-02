import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRBindingAdmission
import Mettapedia.OSLF.MeTTaIL.GeneralEquationCanonicalSyntax

/-! Successfully compiled positive clauses satisfy the existing canonical
template checks. The proof covers both atom queries and comparison guards. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.CanonicalAdmission

open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL Syntax GeneralRuleBindingInference

theorem premise_canonical (pools : Join.Pools) (position : Nat)
    (source : Mettapedia.Languages.Datalog.Premise) (code : Syntax.Premise)
    (compiled : Join.bodyPremise? pools position source = some code) :
    GeneralEquationCanonicalTemplates.checkPremise (Query.lowerPremise code) = true := by
  cases source with
  | atom atom =>
    obtain ⟨target,formed,same⟩ := BodyCompilation.atom_premise pools position atom code compiled
    rw [same]
    simp only [GeneralEquationCanonicalTemplates.checkPremise,List.all_cons,List.all_nil,Bool.and_true]
    exact vector_canonical (InstanceMatching.atom_shape pools position atom target formed)
  | comparison guard =>
    obtain ⟨left,right,leftFormed,rightFormed,same⟩ := BodyCompilation.guard_premise pools position guard code compiled
    obtain ⟨leftName,rfl⟩ := ClauseDictionary.argument_variable pools position 0 guard.left left leftFormed
    obtain ⟨rightName,rfl⟩ := ClauseDictionary.argument_variable pools position 1 guard.right right rightFormed
    rw [same]
    rfl

private theorem bodies_canonical (pools : Join.Pools)
    (entries : List (Mettapedia.Languages.Datalog.Premise × Nat)) (codes : List Syntax.Premise)
    (compiled : List.Forall₂ (fun entry code => Join.bodyPremise? pools entry.2 entry.1 = some code) entries codes) :
    (codes.map Query.lowerPremise).all GeneralEquationCanonicalTemplates.checkPremise = true := by
  induction compiled with
  | nil => rfl
  | @cons entry code entries codes first rest ih =>
    simp only [List.map_cons,List.all_cons,premise_canonical pools entry.2 entry.1 code first,Bool.true_and]
    exact ih

theorem rule_canonical (pools : Join.Pools) (ordinal : Nat) (clause : Clause) (rule : RewriteRule)
    (compiled : Query.compileClause? pools ordinal clause = some rule) :
    GeneralEquationCanonicalTemplates.checkRule rule = true := by
  obtain ⟨left,right⟩ := FiringReading.compiled_fields pools ordinal clause rule compiled
  have leftCanonical : rule.left.hasCanonicalBinderMetadata = true := by
    rw [left]
    exact vector_canonical (RequestInstances.request_shape pools)
  have rightCanonical := vector_canonical (InstanceMatching.atom_shape pools clause.body.length clause.head rule.right right)
  obtain ⟨_,original,formed,premises⟩ := BodyCompilation.compiled_body pools ordinal clause rule compiled
  simp only [GeneralEquationCanonicalTemplates.checkRule,leftCanonical,rightCanonical,Bool.true_and,premises]
  exact bodies_canonical pools _ _ (CompilationFlow.mapM_relation _ _ _ formed)

theorem binding_canonical (rule : RewriteRule) :
    GeneralEquationCanonicalTemplates.checkBinding (inferredSpec rule) = true := rfl

#print axioms premise_canonical
#print axioms rule_canonical

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.CanonicalAdmission
