import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.ScopedNeedMachineControlTyping
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.NeedTyping

/-! # Dependent need-machine control: positive and negative instances -/

open Mettapedia.Machines.BranchLocalNeed.NeedReference
namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ScopedNeedMachine
open ScopedNeedComputation (Code)

namespace ControlExamples

open ScopedNeedComputation.Examples

def primitive : Empty → Tower.Tm 1 → Produced (Tower.Tm 1) Empty Empty :=
  fun operation => nomatch operation

theorem primitive_sound : PrimitiveSoundness Tower.rules operationSignature context primitive := by
  intro operation
  exact nomatch operation

/-- The actual independently typed effectful sharing source starts with a
qualified local allocation action, before any evaluation or heap admission. -/
theorem dependent_source_action :
    ActionTyping Tower.rules operationSignature context (fun _ => none)
      (action primitive (.evaluate ⟨1, 0, source, ids, Fin.elim0⟩ .done))
      (.sigma ground identityFamily) := by
  have captured : ClosureTyping Tower.rules operationSignature context (fun _ => none)
      (⟨1, 0, source, ids, Fin.elim0⟩ : Closure Tower.Head Empty Bool 1)
      (subst ids (.sigma ground identityFamily)) :=
    .captured source_typing (fun index => by simpa only [subst_ids, ids] using
      (FormationSensitive.Typing.var (R := Tower.rules) (Γ := context) index))
      (fun index => Fin.elim0 index)
  have typed : LocalTyping (StableFault := Empty) (NativeFault := Empty)
      Tower.rules operationSignature context (fun _ => none)
      (.evaluate ⟨1, 0, source, ids, Fin.elim0⟩ .done)
      (.sigma ground identityFamily) := by
    apply LocalTyping.evaluate _ (.done _)
    simpa only [subst_ids] using captured
  exact typed.action primitive_sound

/-- Treating the source's new-handle body as a value-demand continuation is
rejected independently of what values a primitive or cache might return. -/
theorem need_body_not_demanded (A B : Tower.Tm 1) :
    ¬ DemandTyping Tower.rules operationSignature context (fun _ => none)
      (.bindNeed (⟨1, 0, boundBody, ids, Fin.elim0⟩ : NeedBody Tower.Head Empty Bool 1) .done) A B :=
  not_demand_bindNeed _ _ A B

/-- A type-level beta redex, distinct from its opaque ground normal form. -/
def betaExpanded : Tower.Tm 1 := .app (.lam (ground : Tower.Tm 2)) (.var 0)

theorem betaExpanded_step : Step Tower.HeadEq betaExpanded ground Tower.rules.computation :=
  .betaPi ground (.var 0)

theorem betaExpanded_ne_ground : betaExpanded ≠ (ground : Tower.Tm 1) := by
  intro equal
  cases equal

/-- Formation is derived independently by native Pi formation, lambda
introduction and application, not inferred from the beta conversion. -/
theorem betaExpanded_formed :
    FormationSensitive.Typing Tower.rules context betaExpanded (sortTm Tower.zero) := by
  apply FormationSensitive.Typing.appElim
    (A := ground) (B := sortTm Tower.zero) _ (.var 0)
  apply FormationSensitive.Typing.lamIntro
  · exact .piForm (.headType .legacyGround) (.sort Tower.zero)
      (.headType (.sort Tower.zero)) (.sort (.succ Tower.zero))
      (.sorts Tower.zero (.succ Tower.zero))
  · exact .sort _
  · exact .headType .legacyGround

theorem ground_converts_betaExpanded :
    Conv Tower.HeadEq (ground : Tower.Tm 1) betaExpanded Tower.rules.computation :=
  .symm _ _ (.rel _ _ betaExpanded_step)

/-- The unchanged `done` continuation changes the displayed result type only
with genuine native beta evidence and the independently formed target. -/
theorem beta_done_conversion :
    ConversionKontTyping Tower.rules context .done ground betaExpanded :=
  .inputConversion betaExpanded_formed (.sort Tower.zero) ground_converts_betaExpanded (.done _)

theorem beta_finish_preserves :
    OutcomeTyping Tower.rules context betaExpanded
      (finish (.value (.var 0) : Outcome Tower.Head Empty Empty 1) .done) :=
  beta_done_conversion.finish_preserves (.value (.var 0))

/-- The actual finished payload keeps full native admission at the beta-
expanded type, although runtime completion has not changed its syntax. -/
theorem beta_finished_judgment :
    FormationSensitive.Judgment Tower.rules context (.var 0) betaExpanded := by
  have admitted := beta_finish_preserves
  cases admitted with
  | value typed => exact ⟨source_judgment.context, typed⟩

/-- A real source conversion tail passes through the generic action theorem;
the machine still returns the original native variable. -/
theorem beta_source_action :
    ActionTyping Tower.rules operationSignature context (fun _ => none)
      (action primitive (.evaluate
        (⟨1, 0, .returnValue (.var 0), ids, Fin.elim0⟩ : Closure Tower.Head Empty Bool 1) .done))
      betaExpanded := by
  have source : ScopedNeedComputation.Typing Tower.rules operationSignature context noNeeds
      (.returnValue (.var 0) : Code Tower.Head Empty Bool 1 0) betaExpanded :=
    .conv (.returnValue (.var 0)) betaExpanded_formed (.sort Tower.zero) ground_converts_betaExpanded
  have captured : ClosureTyping Tower.rules operationSignature context (fun _ => none)
      (⟨1, 0, .returnValue (.var 0), ids, Fin.elim0⟩ : Closure Tower.Head Empty Bool 1)
      (subst ids betaExpanded) :=
    .captured source (fun index => by simpa only [subst_ids, ids] using
      (FormationSensitive.Typing.var (R := Tower.rules) (Γ := context) index))
      (fun index => Fin.elim0 index)
  have localTyped : LocalTyping (StableFault := Empty) (NativeFault := Empty)
      Tower.rules operationSignature context (fun _ => none)
      (.evaluate (⟨1, 0, .returnValue (.var 0), ids, Fin.elim0⟩ : Closure Tower.Head Empty Bool 1) .done)
      betaExpanded := by
    apply LocalTyping.evaluate _ (.done _)
    simpa only [subst_ids] using captured
  exact localTyped.action primitive_sound

end ControlExamples

#print axioms ControlExamples.dependent_source_action
#print axioms ControlExamples.need_body_not_demanded
#print axioms ControlExamples.betaExpanded_step
#print axioms ControlExamples.betaExpanded_ne_ground
#print axioms ControlExamples.betaExpanded_formed
#print axioms ControlExamples.beta_done_conversion
#print axioms ControlExamples.beta_finish_preserves
#print axioms ControlExamples.beta_finished_judgment
#print axioms ControlExamples.beta_source_action

end ScopedNeedMachine
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
