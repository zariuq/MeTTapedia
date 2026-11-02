import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudePeanoStageReflection
import Mettapedia.OSLF.Framework.GeneralReferenceAgreement
import Mettapedia.OSLF.MeTTaIL.GeneralPlanEnvironment

/-! The compiled stage's independently defined typed root firings agree
with Peano source equation steps. The checked directed profile supplies
child-witness eligibility; it does not grant backend admission authority. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation.NormalizationStage.PeanoProducer

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax Match
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Framework.GeneralCanonicalAgreement
open QuantifiedReference
open PeanoSimulation

def compiledPlan (context : Maude.VariableContext) : GeneralExecutionAdmission.Plan :=
  plan peano (context.map fun entry => (entry.1, TypeExpr.base entry.2))

def environment (context : Maude.VariableContext) : GeneralPremise.Environment :=
  GeneralPlanEnvironment.environment (compiledPlan context)

theorem uniform_checked (context : Maude.VariableContext) :
    checkUniformDirectedProfile (environment context) [.base "Nat"] = true := by cbv

theorem uniform_profile (context : Maude.VariableContext) :
    UniformDirectedProfile (fun schema => binderFree schema = true) (environment context) [.base "Nat"] :=
  UniformDirectedProfile.of_check (uniform_checked context)

theorem same_core (context : Maude.VariableContext) :
    (environment context).language.rewrites.map ruleCore = (language peano).rewrites.map ruleCore := by cbv

theorem free_exact (context : Maude.VariableContext) : (environment context).free = freeContext context := by
  funext name
  change ((context.map fun entry => (entry.1, TypeExpr.base entry.2)).find?
    (fun entry => entry.1 == name)).map Prod.snd = _
  induction context with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨key, sort⟩
      by_cases same : key = name
      · subst key
        simp [freeContext, List.lookup]
      · have skip : (key == name) = false := beq_eq_false_iff_ne.mpr same
        have skipReverse : (name == key) = false := beq_eq_false_iff_ne.mpr (Ne.symm same)
        simpa only [List.map_cons, List.find?_cons, skip, Bool.false_eq_true, if_false,
          freeContext, List.lookup_cons, skipReverse] using ih

theorem source_typed (context : Maude.VariableContext) (source : Maude.Term)
    (typed : Maude.HasSort Maude.Examples.peano.signature context source "Nat") :
    OpenPatternWellSorted (environment context).language (environment context).free [] (.base "Nat") (encode source) := by
  have original := (prepared_typing_iff peano context source "Nat").mpr (by simpa only [source_exact] using typed)
  have preserved : HasType (environment context).language (freeContext context) [] (encode source) (.base "Nat") :=
    HasType.of_terms_subset (source := peano.language) (target := (environment context).language)
      (fun _ member => member) original
  rw [free_exact]
  exact ⟨preserved, encode_canonical source, encode_object source, preserved.isWellScopedAt⟩

theorem roots_iff_reference {context : Maude.VariableContext} {source : Maude.Term} {target : Pattern}
    (typed : Maude.HasSort Maude.Examples.peano.signature context source "Nat") :
    (∃ index trace captured completed history,
      GeneralPremise.RootFiring (environment context) [] (.base "Nat") (encode source)
        index trace captured completed history target) ↔
      ReferenceStep.Step Engine.RelationEnv.empty (language peano) (encode source) target :=
  ((uniform_profile context).roots_iff_reference Engine.RelationEnv.empty
    (ReadsProvider.empty _) (by simp) (source_typed context source typed)).trans
    (reference_step_same_core_iff (same_core context) Engine.RelationEnv.empty)

theorem roots_iff_source {context : Maude.VariableContext} {source target : Maude.Term}
    (typed : Maude.HasSort Maude.Examples.peano.signature context source "Nat") :
    (∃ index trace captured completed history,
      GeneralPremise.RootFiring (environment context) [] (.base "Nat") (encode source)
        index trace captured completed history (encode target)) ↔
      Maude.EquationReduction Maude.Examples.peano context "Nat" source target :=
  (roots_iff_reference typed).trans (PeanoReflection.reference_step_iff Engine.RelationEnv.empty typed)

theorem root_readback {context : Maude.VariableContext} {source : Maude.Term} {target : Pattern}
    (typed : Maude.HasSort Maude.Examples.peano.signature context source "Nat")
    (fired : ∃ index trace captured completed history,
      GeneralPremise.RootFiring (environment context) [] (.base "Nat") (encode source)
        index trace captured completed history target) :
    ∃ result, target = encode result ∧ Maude.EquationReduction Maude.Examples.peano context "Nat" source result :=
  PeanoReflection.reference_reflect Engine.RelationEnv.empty typed ((roots_iff_reference typed).mp fired)

end Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation.NormalizationStage.PeanoProducer
