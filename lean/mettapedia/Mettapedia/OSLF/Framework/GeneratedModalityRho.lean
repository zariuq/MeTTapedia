import Mettapedia.OSLF.Framework.GeneratedModality
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.SubstitutionInterpretationCanary

/-!
# The generated modality on a real rho synchronization

The rules of `GeneratedModality` say what the modality delivers; they do not by
themselves say that anything delivers it.  This module supplies the witness.

The redex position is the input's continuation, the instantiation is the one a
closed synchronization produces, and the step the modality's step rule returns
is the engine's own step on that synchronization — not a step of some term the
generator invented.  The path condition is checked in both directions: the
continuation position survives instantiation, and a position below the
right-hand side's explicit substitution does not.
-/

namespace Mettapedia.OSLF.Framework.GeneratedModalityRho

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework.RedexPosition
open Mettapedia.OSLF.Framework.GeneratedModality
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.SubstitutionInterpretationCanary

/-- The input's continuation in the communication redex. -/
def rhoCommPos : Position := [0, 1]

/-- The chosen subterm. -/
def rhoCommFocus : Pattern := .lambda none (.fvar "p")

theorem rhoComm_focus_eq : subtermAt rhoCommRewrite.left rhoCommPos = some rhoCommFocus := by
  rfl

/-- The continuation position survives instantiation. -/
theorem rhoComm_stable : StablePath rhoCommRewrite.left rhoCommPos = true := by rfl

/-- A position below the right-hand side's explicit substitution does not:
applying bindings eliminates that node, so no modality may be generated there
by this route.  This is the negative half of the path condition. -/
theorem rhoComm_right_not_stable : StablePath rhoCommRewrite.right [0, 0] = false := by
  rfl

/-- Instantiating the left-hand side at the synchronization's bindings gives
the closed source the engine steps from. -/
theorem rhoComm_instantiate_left :
    applyBindings commBindings rhoCommRewrite.left = dropReceiverSource := by
  decide +kernel

/-- The assumptions of the modality are satisfiable: the rule fires here. -/
theorem rhoComm_fires :
    RuleFires GSLT.LanguageDef.defaultBasePremises rhoCalc rhoCommRewrite commBindings := by
  show Step GSLT.LanguageDef.defaultBasePremises rhoCalc
    (applyBindings commBindings rhoCommRewrite.left)
    (Mettapedia.OSLF.MeTTaIL.Match.applyRuleBindings rhoCommRewrite commBindings)
  rw [rhoComm_instantiate_left,
    Mettapedia.OSLF.MeTTaIL.Match.applyRuleBindings_eq_applyBindings
      rhoCommRewrite _ (by decide),
    syntactic_comm_instantiate]
  exact syntactic_step

/-- The focus inhabits the generated modality at the trivial result predicate.

This is *not* evidence that the modality is non-vacuous: the same proof goes
through for every language, rule, stable position and rely predicate, since
`relyPossibly_intro` needs only that the result predicate hold of the right-hand
side instances, which `fun _ => True` does for free.  The content is in
`rhoComm_step_witness_concrete` below, which pins the source and the step to a
real closed synchronization.  A genuinely non-vacuous inhabitation would need a
result predicate with content and a filling other than the authored focus. -/
theorem rhoComm_focus_inhabits :
    RelyPossibly GSLT.LanguageDef.defaultBasePremises rhoCalc rhoCommRewrite rhoCommPos
      (fun _ _ => True) (fun _ => True) rhoCommFocus :=
  relyPossibly_intro rhoComm_stable rhoComm_focus_eq (fun _ _ _ => trivial)

/-- The rely assumptions are met by the synchronization's bindings. -/
theorem rhoComm_rely :
    RelySatisfied rhoCommRewrite rhoCommPos (fun _ _ => True) commBindings :=
  fun _ _ _ _ => trivial

/-- **The step rule delivers.**  Applying M-STEP at the authored focus returns
a source and a step of the engine to the rule's own right-hand side instance. -/
theorem rhoComm_step_witness :
    ∃ source : Pattern,
      plug (applyBindings commBindings rhoCommRewrite.left) rhoCommPos
          (applyBindings commBindings rhoCommFocus) = some source ∧
        Step GSLT.LanguageDef.defaultBasePremises rhoCalc source
          (applyBindings commBindings rhoCommRewrite.right) := by
  have witness :=
    relyPossibly_step_authored commBindings rhoComm_stable rhoComm_focus_eq rhoComm_fires
  rwa [Mettapedia.OSLF.MeTTaIL.Match.applyRuleBindings_eq_applyBindings
    rhoCommRewrite _ (by decide)] at witness

/-- **The witness is the real synchronization.**  The source M-STEP returns is
the closed process `dropReceiverSource`, and the step is the engine's own step
to `syntacticContractum`.  This is the part that carries content: the
generator's decomposition names a real redex and the step it reports is the
engine's, not one the generator invented. -/
theorem rhoComm_step_witness_concrete :
    plug (applyBindings commBindings rhoCommRewrite.left) rhoCommPos
        (applyBindings commBindings rhoCommFocus) = some dropReceiverSource ∧
      Step GSLT.LanguageDef.defaultBasePremises rhoCalc dropReceiverSource syntacticContractum := by
  refine ⟨?_, syntactic_step⟩
  exact (plug_applyBindings commBindings rhoComm_stable rhoComm_focus_eq).trans
    (congrArg some rhoComm_instantiate_left)

end Mettapedia.OSLF.Framework.GeneratedModalityRho
