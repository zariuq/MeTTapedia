import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudePreparation
import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeSortedBindings
import Mettapedia.Languages.Maude.Examples
import Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission

/-! A separate GSLT stage for the chosen orientation of authored equations.
The original prepared language remains its semantic reference. Algebra
equations stay equations; original transition rules are absent from this
stage. Treating a completed stage result as a Maude canonical form requires
the module's normalization, confluence and coherence certificates. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation.NormalizationStage

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax Match ContextualStep
open Mettapedia.GSLT.LanguageDef.EquationSemantics

def language (prepared : Prepared) : LanguageDef :=
  {prepared.language with
    name := prepared.language.name ++ ":equations"
    equations := prepared.language.equations.drop prepared.source.equations.length
    rewrites := (prepared.language.equations.take prepared.source.equations.length).map
      (fun equation => ScopedEquationExecution.orientedRule equation .forward) ++
      prepared.source.signature.operators.flatMap congruences}

def provider : GeneralPremise.ProviderSnapshot := {signatures := [], rows := []}
def permissions : GeneralExecutionAdmission.Permissions := {sites := .rootOnly, includeDerivedEquations := false}
def plan (prepared : Prepared) (freeTypes : List (String × TypeExpr) := []) : GeneralExecutionAdmission.Plan :=
  GeneralExecutionAdmission.compile ⟨language prepared, freeTypes, provider⟩ permissions

theorem sorted_bindings_original (prepared : Prepared) (ambient : Maude.VariableContext)
    {declarations : List (String × TypeExpr)} {bindings : Bindings}
    (sorted : SortedBindingsIn (language prepared) (freeContext ambient) declarations bindings) :
    SortedBindingsIn prepared.language (freeContext ambient) declarations bindings := by
  intro name type member
  obtain ⟨object, typed⟩ := sorted name type member
  exact ⟨object, WellSorted.HasType.of_terms_subset (source := language prepared) (target := prepared.language)
    (fun _ declared => declared) typed⟩

theorem root_is_original_equation (prepared : Prepared) (ambient : Maude.VariableContext)
    (base : BasePremiseEvaluator) {equation : Equation} {source target : Pattern} {bindings : Bindings}
    (member : equation ∈ prepared.language.equations.take prepared.source.equations.length)
    (raw : readsRaw equation = true) (empty : equation.premises = [])
    (matched : bindings ∈ matchPattern (ScopedEquationExecution.orientedRule equation .forward).left source)
    (applied : applyBindings bindings (ScopedEquationExecution.orientedRule equation .forward).right = target)
    (sorted : SortedBindingsIn (language prepared) (freeContext ambient) equation.typeContext bindings) :
    OpenSortedEquationInstance (freeContext ambient) base prepared.language source target := by
  refine ⟨0, OpenSortedEquationInstanceAt.forward (initialBindings := bindings) (finalBindings := bindings)
    (List.mem_of_mem_take member) raw matched ?_ (sorted_bindings_original prepared ambient sorted) applied⟩
  rw [empty]
  exact PremisesAt.nil bindings

def peano : Prepared := (prepare Maude.Examples.peano).toOption.get (by decide_cbv)

#guard (language peano).validate.isEmpty
#guard (language peano).equations.isEmpty
#guard (language peano).rewrites.length == 9
#eval (plan peano).obligations
#guard (plan peano).obligations.all (fun obligation => obligation == .childStratification)

end Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation.NormalizationStage
