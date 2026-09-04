import Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenSyntax

/-!
# GSLT and generated native types for maximal-token MM2 syntax

This module exposes the authored syntax language through the generic
LanguageDef-to-GSLT and OSLF constructions.  Syntax has no rewrite rules;
execution remains the responsibility of the independently authored MM2
work-queue GSLT.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenNTT

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.CarrierWellSorted
open Mettapedia.GSLT.LanguageDef.TotalGSLT
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenSyntax

abbrev theory : Mettapedia.GSLT.GSLT :=
  langGSLT language

theorem theory_no_step (source target : theory.Term) :
    ¬ theory.Step source target := by
  intro reduction
  change langSemanticReduces language source target at reduction
  have rawReduction : langReduces language source target :=
    (langSemanticReduces_iff_langReduces_of_equation_free
      (by rfl) source target).mp reduction
  change langReducesUsing RelationEnv.empty language source target at rawReduction
  unfold langReducesUsing at rawReduction
  rcases rawReduction with ⟨_, step⟩
  cases step with
  | rule ruleMember =>
      change _ ∈ ([] : List RewriteRule) at ruleMember
      simp at ruleMember

def mm2MaximalTokenOSLF := langOSLF language "MM2Program"

/-- Native type generated from the exact authored top-level program sort. -/
def programNativeType : langNativeType language "MM2Program" where
  sort := "MM2Program"
  pred := equationPredicateOfEquationFree (by rfl) fun term =>
    checkHasType language WellSorted.FreeTypeContext.empty [] term
      (.base "MM2Program") = true

private def emptyProgram : Pattern :=
  .apply "mm2:program-empty" []

private def emptyAtomList : Pattern :=
  .apply "mm2:atoms-empty" []

theorem empty_program_inhabits_native_type :
    programNativeType.pred.1 emptyProgram := by
  change checkHasType language WellSorted.FreeTypeContext.empty []
      emptyProgram (.base "MM2Program") = true
  decide +kernel

/-- A nested atom-list carrier cannot masquerade as a top-level program. -/
theorem atom_list_does_not_inhabit_program_native_type :
    ¬ programNativeType.pred.1 emptyAtomList := by
  change ¬ (checkHasType language WellSorted.FreeTypeContext.empty []
      emptyAtomList (.base "MM2Program") = true)
  decide +kernel

theorem exact_target_native_type_empty (source target : theory.Term) :
    ¬ (exactTargetNativeType theory target).pred.1 source := by
  intro holds
  change gsltDiamond theory _ source at holds
  rw [gsltDiamond_spec] at holds
  obtain ⟨middle, step, _⟩ := holds
  exact theory_no_step source middle step

#print axioms theory_no_step
#print axioms empty_program_inhabits_native_type
#print axioms atom_list_does_not_inhabit_program_native_type
#print axioms exact_target_native_type_empty

end Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenNTT
