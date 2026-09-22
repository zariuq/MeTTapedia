import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeJudgmentReplayTransport
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralTypingReplayFormation

/-!
# Computed result-type formation for native checked judgments

Every accepted native typing certificate computes a finite formation
certificate for its displayed type. The output comes from the input trees,
not proof search or classical selection from the regularity theorem.
The public checked entry point first replays the source certificate.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeJudgmentReplay

open Presentation StructuralTypingReplay NativeIndexedFamilies

theorem universeSuccessor_qualified (u : Tower.Head) (isUniverse : IntrinsicRelator.rules.isUniverse u) :
    IntrinsicRelator.rules.isUniverse (TowerDecisions.headTarget u) ∧
      IntrinsicRelator.rules.headTyping u (TowerDecisions.headTarget u) := by
  cases isUniverse with
  | sort level => exact ⟨.sort _, .sort _⟩

def resultFormation {n : Nat} (contextCode : ContextCode n) (subject type : Tower.Tm n)
    (code : Code n) : Option (Tower.Head × Code n) :=
  code.resultFormation NativeRelatorConversionChecking.rename NativeRelatorConversionChecking.substitute
    TowerDecisions.headTarget contextCode subject type

theorem resultFormation_checked {n : Nat} {context : Tower.Ctx n} {subject type : Tower.Tm n}
    {contextCode : ContextCode n} {code : Code n}
    (accepted : check context subject type contextCode code = true) :
    ∃ u formation, resultFormation contextCode subject type code = some (u, formation) ∧
      IntrinsicRelator.rules.isUniverse u ∧
      check context type (.head u) contextCode formation = true := by
  have inputs := accepted
  simp only [check, checkJudgment, Bool.and_eq_true] at inputs
  obtain ⟨u, formation, computed, isU, formed⟩ := Code.resultFormation_checked
    IntrinsicRelator.rules NativeRelatorConversionChecking.check
    NativeRelatorConversionChecking.rename NativeRelatorConversionChecking.check_rename
    NativeRelatorConversionChecking.substitute NativeRelatorConversionChecking.check_substitute
    TowerDecisions.headTarget FormationSensitiveNativeRelatorElimination.universes
    universeSuccessor_qualified code contextCode inputs.1 inputs.2
  refine ⟨u, formation, computed, isU, ?_⟩
  simp only [check, checkJudgment, Bool.and_eq_true]
  exact ⟨inputs.1, formed⟩

/-- The total value on accepted inputs is obtained by executing the extractor. -/
def resultFormationValue {n : Nat} {context : Tower.Ctx n} {subject type : Tower.Tm n}
    {contextCode : ContextCode n} {code : Code n}
    (accepted : check context subject type contextCode code = true) : Tower.Head × Code n :=
  (resultFormation contextCode subject type code).get (by
    obtain ⟨u, formation, computed, _, _⟩ := resultFormation_checked accepted
    simp only [computed, Option.isSome_some])

theorem resultFormationValue_spec {n : Nat} {context : Tower.Ctx n} {subject type : Tower.Tm n}
    {contextCode : ContextCode n} {code : Code n}
    (accepted : check context subject type contextCode code = true) :
    resultFormation contextCode subject type code = some (resultFormationValue accepted) ∧
      IntrinsicRelator.rules.isUniverse (resultFormationValue accepted).1 ∧
      check context type (.head (resultFormationValue accepted).1) contextCode
        (resultFormationValue accepted).2 = true := by
  obtain ⟨u, formation, computed, isU, formed⟩ := resultFormation_checked accepted
  simp only [resultFormationValue, computed, Option.get_some]
  exact ⟨True.intro, isU, formed⟩

def checkedResultFormation {n : Nat} (context : Tower.Ctx n) (subject type : Tower.Tm n)
    (contextCode : ContextCode n) (code : Code n) : Option (Tower.Head × Code n) :=
  if check context subject type contextCode code then resultFormation contextCode subject type code else none

theorem checkedResultFormation_iff {n : Nat} (context : Tower.Ctx n) (subject type : Tower.Tm n)
    (contextCode : ContextCode n) (code : Code n) (u : Tower.Head) (formation : Code n) :
    checkedResultFormation context subject type contextCode code = some (u, formation) ↔
      check context subject type contextCode code = true ∧
        resultFormation contextCode subject type code = some (u, formation) := by
  unfold checkedResultFormation
  split <;> simp_all

theorem checkedResultFormation_sound {n : Nat} {context : Tower.Ctx n} {subject type : Tower.Tm n}
    {contextCode : ContextCode n} {code : Code n} {u : Tower.Head} {formation : Code n}
    (computed : checkedResultFormation context subject type contextCode code = some (u, formation)) :
    check context subject type contextCode code = true ∧ IntrinsicRelator.rules.isUniverse u ∧
      check context type (.head u) contextCode formation = true := by
  obtain ⟨accepted, output⟩ := (checkedResultFormation_iff _ _ _ _ _ _ _).mp computed
  obtain ⟨v, certificate, actual, isV, formed⟩ := resultFormation_checked accepted
  have equal := Option.some.inj (output.symm.trans actual)
  cases equal
  exact ⟨accepted, isV, formed⟩

/-- Formation extraction succeeds exactly on the original checker's accepted
inputs; it adds neither an oracle nor a stricter admission restriction. -/
theorem checkedResultFormation_isSome {n : Nat} (context : Tower.Ctx n) (subject type : Tower.Tm n)
    (contextCode : ContextCode n) (code : Code n) :
    (checkedResultFormation context subject type contextCode code).isSome =
      check context subject type contextCode code := by
  cases accepted : check context subject type contextCode code with
  | false => simp [checkedResultFormation, accepted]
  | true =>
      obtain ⟨u, formation, computed, _, _⟩ := resultFormation_checked accepted
      simp [checkedResultFormation, accepted, computed]

/-- The join used by this cumulative presentation, with non-universe inputs
left outside the qualified domain of the construction. -/
def universeJoin : Tower.Head → Tower.Head → Tower.Head
  | .sort u, .sort v => .sort (.max u v)
  | _, _ => .legacyGround

theorem universeJoin_qualified (u v : Tower.Head)
    (isU : IntrinsicRelator.rules.isUniverse u) (isV : IntrinsicRelator.rules.isUniverse v) :
    IntrinsicRelator.rules.join u v (universeJoin u v) := by
  cases isU
  cases isV
  exact .sorts _ _

def applyLambda {n : Nat} (contextCode : ContextCode n)
    (argument A : Tower.Tm n) (body B : Tower.Tm (n + 1))
    (argumentCode : Code n) (bodyCode : Code (n + 1)) : Option (Code n) :=
  StructuralTypingReplay.Code.applyLambda NativeRelatorConversionChecking.rename
    NativeRelatorConversionChecking.substitute TowerDecisions.headTarget universeJoin
    contextCode argument A body B argumentCode bodyCode

/-- The concrete rules discharge the universe and conversion obligations of
the shared construction. The body checker uses the argument's actual type. -/
theorem applyLambda_checked {n : Nat} {context : Tower.Ctx n} {contextCode : ContextCode n}
    {argument A : Tower.Tm n} {body B : Tower.Tm (n + 1)}
    {argumentCode : Code n} {bodyCode : Code (n + 1)}
    (argumentAccepted : check context argument A contextCode argumentCode = true)
    (bodyAccepted : StructuralTypingReplay.check IntrinsicRelator.rules
      NativeRelatorConversionChecking.check (.snoc context A) body B bodyCode = true) :
    ∃ code, applyLambda contextCode argument A body B argumentCode bodyCode = some code ∧
      check context (.app (.lam body) argument) (inst0 argument B) contextCode code = true := by
  simp only [check, checkJudgment, Bool.and_eq_true] at argumentAccepted
  obtain ⟨code, computed, checked⟩ := StructuralTypingReplay.Code.applyLambda_checked
    IntrinsicRelator.rules NativeRelatorConversionChecking.check
    NativeRelatorConversionChecking.rename NativeRelatorConversionChecking.check_rename
    NativeRelatorConversionChecking.substitute NativeRelatorConversionChecking.check_substitute
    TowerDecisions.headTarget FormationSensitiveNativeRelatorElimination.universes
    universeSuccessor_qualified universeJoin universeJoin_qualified
    argumentAccepted.1 argumentAccepted.2 bodyAccepted
  refine ⟨code, computed, ?_⟩
  simpa only [check, checkJudgment, Bool.and_eq_true] using
    (And.intro argumentAccepted.1 checked)

namespace FormationControls

open NativeRelatorConversionChecking.Examples (ground betaArgument)

theorem converted_type_formation_computes :
    checkedResultFormation Controls.context (.refl (.var 0)) Controls.targetType
      Controls.contextCode Controls.proofCode = some (.sort Tower.zero, Controls.targetFormation) := by
  rfl

def applicationType : Tower.Tm 1 :=
  inst0 (betaArgument (.var 0)) (.id ground (.var 0) (.var 0))

def functionFormation : Code 1 :=
  .piForm (.sort Tower.zero) (.sort Tower.zero) .headType
    (.idForm (.sort Tower.zero) .headType .var .var)

def applicationCode : Code 1 :=
  .appElim ground (.id ground (.var 0) (.var 0))
    (.lamIntro (.sort (.max Tower.zero Tower.zero)) functionFormation (.reflIntro ground .var))
    Controls.betaArgumentCode

def application : Tower.Tm 1 :=
  .app (.lam (.refl (.var 0))) (betaArgument (.var 0))

theorem dependent_application_certificate_constructed :
    applyLambda Controls.contextCode (betaArgument (.var 0)) ground
      (.refl (.var 0)) (.id ground (.var 0) (.var 0))
      Controls.betaArgumentCode (.reflIntro ground .var) = some applicationCode := by
  rfl

theorem constructed_application_checks :
    check Controls.context application applicationType Controls.contextCode applicationCode = true := by
  obtain ⟨code, computed, accepted⟩ := applyLambda_checked
    (show check Controls.context (betaArgument (.var 0)) ground Controls.contextCode
      Controls.betaArgumentCode = true from by decide +kernel)
    (show StructuralTypingReplay.check IntrinsicRelator.rules NativeRelatorConversionChecking.check
      (.snoc Controls.context ground) (.refl (.var 0)) (.id ground (.var 0) (.var 0))
      (.reflIntro ground .var) = true from by decide +kernel)
  rw [dependent_application_certificate_constructed] at computed
  cases Option.some.inj computed
  exact accepted

theorem malformed_argument_not_hidden_by_redex :
    check Controls.context (.app (.lam (.var 1)) (.app (.var 0) (.var 0))) ground
      Controls.contextCode
      (.appElim ground ground
        (.lamIntro (.sort (.max Tower.zero Tower.zero))
          (.piForm (.sort Tower.zero) (.sort Tower.zero) .headType .headType) .var)
        (.appElim ground ground .var .var)) = false := by decide +kernel

def instantiatedFormation : Code 1 :=
  .idForm (.sort Tower.zero) .headType Controls.betaArgumentCode Controls.betaArgumentCode

/-- A genuinely dependent application computes the substituted formation
tree, retaining both copies of the supplied argument proof. -/
theorem dependent_application_formation_computes :
    checkedResultFormation Controls.context application applicationType Controls.contextCode applicationCode =
      some (.sort Tower.zero, instantiatedFormation) := by
  rfl

theorem dependent_application_formation_replays :
    check Controls.context applicationType (.head (.sort Tower.zero))
      Controls.contextCode instantiatedFormation = true := by
  decide +kernel

def pairType : Tower.Tm 1 := .sigma ground (.id ground (.var 1) (.var 0))
def pairTerm : Tower.Tm 1 := .pair (.var 0) (.refl (.var 0))
def pairCode : Code 1 :=
  .pairIntro (.sort (.max Tower.zero Tower.zero))
    (.sigmaForm (.sort Tower.zero) (.sort Tower.zero) .headType
      (.idForm (.sort Tower.zero) .headType .var .var)) .var (.reflIntro ground .var)

theorem dependent_second_projection_computes :
    checkedResultFormation Controls.context (.snd pairTerm)
      (inst0 (.fst pairTerm) (.id ground (.var 1) (.var 0))) Controls.contextCode
      (.sndElim ground (.id ground (.var 1) (.var 0)) pairCode) =
      some (.sort Tower.zero,
        .idForm (.sort Tower.zero) .headType .var (.fstElim (.id ground (.var 1) (.var 0)) pairCode)) := by
  rfl

/-- Changing the displayed index without changing this supplied certificate
fails replay. A conversion-bearing certificate could justify this annotation. -/
theorem changed_dependent_index_rejected :
    checkedResultFormation Controls.context application (.id ground (.var 0) (.var 0))
      Controls.contextCode applicationCode = none := by
  decide +kernel

theorem unformed_context_rejected :
    checkedResultFormation Controls.unformedContext (.var 0)
      (Ctx.lookup Controls.unformedContext 0) Controls.contextCode .var = none := by
  decide +kernel

theorem universe_formation_advances_level :
    checkedResultFormation (.nil : Tower.Ctx 0) (.head (.sort Tower.zero))
      (.head (.sort (.succ Tower.zero))) .nil .headType =
      some (.sort (.succ (.succ Tower.zero)), .headType) := by
  rfl

theorem self_universe_rejected :
    checkedResultFormation (.nil : Tower.Ctx 0) (.head (.sort Tower.zero))
      (.head (.sort Tower.zero)) .nil .headType = none := by
  decide +kernel

end FormationControls

#print axioms resultFormation_checked
#print axioms applyLambda_checked
#print axioms FormationControls.dependent_application_certificate_constructed
#print axioms FormationControls.constructed_application_checks
#print axioms FormationControls.malformed_argument_not_hidden_by_redex
#print axioms resultFormationValue_spec
#print axioms checkedResultFormation_sound
#print axioms checkedResultFormation_isSome
#print axioms FormationControls.converted_type_formation_computes
#print axioms FormationControls.dependent_application_formation_computes
#print axioms FormationControls.dependent_application_formation_replays
#print axioms FormationControls.dependent_second_projection_computes
#print axioms FormationControls.changed_dependent_index_rejected
#print axioms FormationControls.unformed_context_rejected
#print axioms FormationControls.universe_formation_advances_level
#print axioms FormationControls.self_universe_rejected

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeJudgmentReplay
