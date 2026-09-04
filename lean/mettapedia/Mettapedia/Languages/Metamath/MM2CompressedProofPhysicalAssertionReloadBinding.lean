import Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalDecoratedAssertionLaunch

/-!
# Assertion reload binding

The pending input and reload output share one proof-owner variable.  This
small inversion lemma records that connection independently of the generated
assertion launcher and its complete physical workspace.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionReloadBinding

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionSurface
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalDecoratedAssertionLaunch
open Mettapedia.Languages.ProcessCalculi.MORK

/-- Replaying the pending factor fixes the proof-owner binding used by the
reload output.  The result does not assume that owners are ground atoms. -/
theorem reload_exact_of_pending_replay
    (context : DirectAssertionContext) (substitution : Subst) (reload : Atom)
    (pendingReplay :
      applySubst substitution directAssertionPendingTemplate =
        context.pendingRow)
    (instantiates : instantiateRuleTemplateAtom?
      decoratedDirectAssertionDirective.rule.input substitution
        directAssertionReloadTemplate = some reload) :
    reload = context.reloadRow := by
  have ownerExact :
      applySubst substitution (.var "proof-owner") = context.proofOwner := by
    have projected := congrArg
      (fun atom => match atom with
        | .expression (_ :: _ :: owner :: _) => owner
        | _ => .symbol "mm-missing-proof-owner")
      pendingReplay
    simpa [directAssertionPendingTemplate, DirectAssertionContext.pendingRow,
      applySubst, applySubst.applySubstList] using projected
  have reloadInherited : ruleTemplateVariablesInherited
      decoratedDirectAssertionDirective.rule.input
        directAssertionReloadTemplate = true := by
    rw [decoratedDirectAssertionDirective_input_exact]
    decide +kernel
  rw [instantiateRuleTemplateAtom?_eq_instantiateTemplateAtom?
    _ _ _ reloadInherited] at instantiates
  cases covered : templateCovered substitution directAssertionReloadTemplate with
  | false => simp [instantiateTemplateAtom?, covered] at instantiates
  | true =>
      have instantiatedExact := instantiateTemplateAtom_of_covered substitution
        directAssertionReloadTemplate covered
      have reloadExact : reload =
          applySubst substitution directAssertionReloadTemplate :=
        Option.some.inj (instantiates.symm.trans instantiatedExact)
      rw [reloadExact]
      unfold directAssertionReloadTemplate DirectAssertionContext.reloadRow
      simp only [applySubst, applySubst.applySubstList]
      exact congrArg
        (fun owner => Atom.expression
          [.symbol "mm-reload-compressed-normal-dispatch", owner])
        ownerExact

#print axioms reload_exact_of_pending_replay

end Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionReloadBinding
