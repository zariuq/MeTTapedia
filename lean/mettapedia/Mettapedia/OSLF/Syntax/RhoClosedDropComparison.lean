import Mettapedia.OSLF.Syntax.RhoEquationRuleModels
import Mettapedia.OSLF.Syntax.RhoIntrinsicEncoding
import Mettapedia.OSLF.Syntax.RhoCanonicalConditionalRuleFrames

/-!
# Closed-carrier comparison for the intrinsic and authored rho Drop rule

The intrinsic rule polynomial has a Drop constructor for every closed process.
The canonical authored rule matcher can also fire on raw patterns, but its
closed rho carrier admits an encoded intrinsic Drop source exactly when the
process respects the quotation boundary. On that domain, the same authored
rule has a retained derivation tree. A concrete unsafe process rules out a
total closed-carrier map from all intrinsic Drop constructors.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoClosedDropComparison

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.Binding.RhoSchema
open Mettapedia.OSLF.Binding.RhoSchema.Authored
open Mettapedia.OSLF.Binding.RhoSchema.IntrinsicEncoding
open Mettapedia.OSLF.Binding.RhoSemanticRulePolynomial
open Mettapedia.OSLF.Binding.RhoRulePolynomialMorphism
open Mettapedia.OSLF.Binding.CanonicalConditionalRuleFrames
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem

theorem drop_step_all (p : Pattern) :
    Mettapedia.OSLF.MeTTaIL.ContextualStep.Step
      (engineBasePremises RelationEnv.empty) rhoCalcWithDrop
      (Pattern.apply "PDrop" [Pattern.apply "NQuote" [p]]) p := by
  refine ⟨1, .rule (rule := rhoDropRewrite)
    (initialBindings := [("P", p)]) (finalBindings := [("P", p)]) ?_ ?_ ?_ ?_⟩
  · simp [rhoCalcWithDrop]
  · simp [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic,
      rhoDropRewrite, matchPattern, matchArgs, mergeBindings]
  · exact .nil _
  · simp [rhoDropRewrite, applyRuleBindings, applyBindingsScoped,
      Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_zero]
    split <;> rfl

private abbrev raw := BindingCloneAlgebra.terms sig

def intrinsicDropSource (t : Term sig [] Srt.pr) : Term sig [] Srt.pr :=
  RhoSemanticRulePolynomial.drop raw (quote raw t)

theorem encoded_drop_source_eq (t : Term sig [] Srt.pr) :
    encodeTerm (intrinsicDropSource t) =
      Pattern.apply "PDrop" [Pattern.apply "NQuote" [encodeTerm t]] := rfl

theorem encoded_drop_source_admitted_iff (t : Term sig [] Srt.pr) :
    RhoClosedTermWellSorted
      Mettapedia.OSLF.Framework.ConstructorCategory.rhoProc
      (encodeTerm (intrinsicDropSource t)) ↔
    intrinsicQuoteSafe 0 t = true := by
  rw [encoded_process_admitted_iff_quoteSafe]
  have expanded : intrinsicDropSource t =
      Term.op Op.drp (.cons (Term.op Op.quo (.cons t .nil)) .nil) := rfl
  rw [expanded]
  simp [intrinsicQuoteSafe, intrinsicQuoteSafeArgs]

/-- The intrinsic rule constructor exists for every closed process, with no
premise and without silently imposing the authored quotation boundary. -/
def intrinsicDropTree (t : Term sig [] Srt.pr) :
    (rules raw).Fix ()
      (judgment raw (intrinsicDropSource t) t) :=
  .roll (RuleShape.drop (A := raw) (Γ := []) t)
    (fun impossible => impossible.elim)

private noncomputable abbrev sourceAlgebra :=
  (FreeBindingEquationModel.presented rhoSourceE).algebra

/-- The raw Drop constructor is transported through the complete intrinsic
source equation quotient, retaining its rule occurrence. -/
noncomputable def sourceEquationDropTree (t : Term sig [] Srt.pr) :
    (rules sourceAlgebra).Fix ()
      (mapJudgment (FreeBindingClone.interpretHom sourceAlgebra)
        (judgment raw (intrinsicDropSource t) t)) :=
  interpretTree (FreeBindingClone.interpretHom sourceAlgebra) _
    (intrinsicDropTree t)

theorem encoded_drop_tree_of_safe (t : Term sig [] Srt.pr)
    (safe : intrinsicQuoteSafe 0 t = true) :
    RhoClosedTermWellSorted
      Mettapedia.OSLF.Framework.ConstructorCategory.rhoProc
      (encodeTerm (intrinsicDropSource t)) ∧
    RhoClosedTermWellSorted
      Mettapedia.OSLF.Framework.ConstructorCategory.rhoProc
      (encodeTerm t) ∧
    ∃ fuel, Nonempty ((authoredPresentation
      (engineBasePremises RelationEnv.empty) rhoCalcWithDrop).Derivation ()
      (fuel, encodeTerm (intrinsicDropSource t), encodeTerm t)) := by
  refine ⟨(encoded_drop_source_admitted_iff t).mpr safe,
    (encoded_process_admitted_iff_quoteSafe t).mpr safe, ?_⟩
  apply (derivation_nonempty_iff_step _ _ _ _).mpr
  rw [encoded_drop_source_eq]
  exact drop_step_all (encodeTerm t)

theorem crossing_drop_raw_step :
    Mettapedia.OSLF.MeTTaIL.ContextualStep.Step
      (engineBasePremises RelationEnv.empty) rhoCalcWithDrop
      (encodeTerm (intrinsicDropSource crossingQuote))
      (encodeTerm crossingQuote) := by
  rw [encoded_drop_source_eq]
  exact drop_step_all _

theorem crossing_drop_not_closed :
    ¬ RhoClosedTermWellSorted
      Mettapedia.OSLF.Framework.ConstructorCategory.rhoProc
      (encodeTerm (intrinsicDropSource crossingQuote)) := by
  rw [encoded_drop_source_admitted_iff]
  rw [crossingQuote_intrinsically_unsafe]
  decide

theorem crossing_intrinsic_drop_tree :
    Nonempty ((rules raw).Fix ()
      (judgment raw (intrinsicDropSource crossingQuote) crossingQuote)) :=
  ⟨intrinsicDropTree crossingQuote⟩

/-- The precise obstruction to a total closed-carrier comparison: there is
an intrinsic Drop constructor over a closed process whose encoded source
cannot inhabit the authored closed-process sort, despite a raw matcher step. -/
theorem no_total_closed_drop_image :
    ¬ ∀ t : Term sig [] Srt.pr,
      Nonempty ((rules raw).Fix ()
        (judgment raw (intrinsicDropSource t) t)) →
      RhoClosedTermWellSorted
        Mettapedia.OSLF.Framework.ConstructorCategory.rhoProc
        (encodeTerm (intrinsicDropSource t)) := by
  intro total
  exact crossing_drop_not_closed
    (total crossingQuote crossing_intrinsic_drop_tree)

theorem zero_drop_safe : intrinsicQuoteSafe 0 nilP = true := by
  decide +kernel

theorem zero_drop_two_presentations :
    Nonempty ((rules raw).Fix ()
      (judgment raw (intrinsicDropSource nilP) nilP)) ∧
    RhoClosedTermWellSorted
      Mettapedia.OSLF.Framework.ConstructorCategory.rhoProc
      (encodeTerm (intrinsicDropSource nilP)) ∧
    ∃ fuel, Nonempty ((authoredPresentation
      (engineBasePremises RelationEnv.empty) rhoCalcWithDrop).Derivation ()
      (fuel, encodeTerm (intrinsicDropSource nilP), encodeTerm nilP)) := by
  refine ⟨⟨intrinsicDropTree nilP⟩, ?_⟩
  have admitted := encoded_drop_tree_of_safe nilP zero_drop_safe
  exact ⟨admitted.1, admitted.2.2⟩

/-- Every safe closed intrinsic Drop instance has both a constructor in the
combined equation/rule initial model and a retained authored rule tree at its
encoded raw endpoints. This is existence on a common instance, not yet a
history-preserving comparison functor. -/
theorem source_drop_and_authored_tree_of_safe
    (t : Term sig [] Srt.pr)
    (safe : intrinsicQuoteSafe 0 t = true) :
    Nonempty ((rules sourceAlgebra).Fix ()
      (mapJudgment (FreeBindingClone.interpretHom sourceAlgebra)
        (judgment raw (intrinsicDropSource t) t))) ∧
    RhoClosedTermWellSorted
      Mettapedia.OSLF.Framework.ConstructorCategory.rhoProc
      (encodeTerm (intrinsicDropSource t)) ∧
    ∃ fuel, Nonempty ((authoredPresentation
      (engineBasePremises RelationEnv.empty) rhoCalcWithDrop).Derivation ()
      (fuel, encodeTerm (intrinsicDropSource t), encodeTerm t)) := by
  have admitted := encoded_drop_tree_of_safe t safe
  exact ⟨⟨sourceEquationDropTree t⟩, admitted.1, admitted.2.2⟩

#print axioms drop_step_all
#print axioms encoded_drop_source_admitted_iff
#print axioms encoded_drop_tree_of_safe
#print axioms crossing_drop_raw_step
#print axioms crossing_drop_not_closed
#print axioms crossing_intrinsic_drop_tree
#print axioms no_total_closed_drop_image
#print axioms zero_drop_two_presentations
#print axioms source_drop_and_authored_tree_of_safe

end Mettapedia.OSLF.Binding.RhoClosedDropComparison
