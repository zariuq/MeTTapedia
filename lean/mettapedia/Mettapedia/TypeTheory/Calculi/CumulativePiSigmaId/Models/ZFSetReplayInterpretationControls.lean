import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayComputation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayRenaming
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayContext
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayElimination
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayIntroduction
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayCoherence
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.ZFSetReplayUniverseFormation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.CumulativeReplay
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.ZFSetTraceUniverseInterpretation

/-!
# Checked closures and dependent pairs in the set interpretation

These programs use the actual cumulative rules and finite structural replay.
The semantic head map uses the existing internal universe tower. The ground
type is an actual two-element set, so capture and wrong projections can be
distinguished. This is not a universal replay-soundness theorem.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayInterpretationControls

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation StructuralTypingReplay ZFSetReplayInterpretation
open ZFSetTypeExpressionInterpretation (Environment)
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.TypeTheory.UniverseLevel.ZFSetInterpretation
open Mettapedia.TypeTheory.UniverseLevel.ZFSetInterpretation.Controls (twoCode)
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (CofinalInaccessibles)
open ZFSetDependentProducts (graph sigmaSet)
open ZFSetTraceProducts (traceLam traceApp traceApp_graph_beta)
open ZFSetTraceProofDecoding (truthCode mem_truthCode)
open ZFSetTraceUniverseInterpretation (interpretHead)

universe u

private def zero : Tower.Head := .sort Tower.zero
private def pairLevel : Tower.Head := .sort (.max Tower.zero Tower.zero)
private def functionLevel : Tower.Head := .sort (.max Tower.zero (.max Tower.zero Tower.zero))
private def ground {n : Nat} : Tower.Tm n := .head .legacyGround
private abbrev Replay (n : Nat) := StructuralTypingReplay.Code Tower.Head NoConversion n

private def arrowFormation {n : Nat} : Replay n := .piForm zero zero .headType .headType

def keep : Tower.Tm 0 := .lam (.lam (.var 1))
def keepType : Tower.Tm 0 := .pi ground (.pi ground ground)
def keepCode : Replay 0 :=
  .lamIntro functionLevel (.piForm zero pairLevel .headType arrowFormation)
    (.lamIntro pairLevel arrowFormation .var)

theorem keep_checked : check Tower.rules noConversionCheck .nil keep keepType keepCode = true := by
  decide

noncomputable def keepMeaning (h : CofinalInaccessibles.{u}) : Meaning.{u} 0 :=
  .plain (fun _ => traceLam (graph (twoCode h).1
    (fun x => traceLam (graph (twoCode h).1 (fun _ => x)))))

theorem keep_assembles (h : CofinalInaccessibles.{u}) (constants : DeclName → ZFSet.{u}) :
    assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      keepCode keep keepType = some (keepMeaning h) := rfl

theorem keep_computes (h : CofinalInaccessibles.{u}) (constants : DeclName → ZFSet.{u})
    (meaning : Meaning.{u} 0)
    (assembled : assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      keepCode keep keepType = some meaning)
    (x y : ZFSet.{u}) (insideX : x ∈ (twoCode h).1) (insideY : y ∈ (twoCode h).1) :
    traceApp (traceApp (meaning.value Fin.elim0) x) y = x := by
  rw [keep_assembles] at assembled
  cases Option.some.inj assembled
  change traceApp (traceApp (traceLam (graph (twoCode h).1 _)) x) y = x
  rw [traceApp_graph_beta _ insideX, traceApp_graph_beta _ insideY]

theorem keep_rejects_capture (h : CofinalInaccessibles.{u}) (constants : DeclName → ZFSet.{u})
    (meaning : Meaning.{u} 0)
    (assembled : assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      keepCode keep keepType = some meaning) :
    traceApp (traceApp (meaning.value Fin.elim0) ∅) (ZFSet.powerset ∅) ≠ ZFSet.powerset ∅ := by
  rw [keep_computes h constants meaning assembled _ _
    ZFSetDependentProducts.Controls.empty_mem_two ZFSetDependentProducts.Controls.power_empty_mem_two]
  intro equal
  have member : (∅ : ZFSet.{u}) ∈ ZFSet.powerset ∅ := by simp
  rw [← equal] at member
  exact ZFSet.notMem_empty _ member

def anchoredType {n : Nat} : Tower.Tm (n + 1) :=
  .sigma ground (.id ground (.var 1) (.var 0))

def anchor : Tower.Tm 0 := .lam (.pair (.var 0) (.refl (.var 0)))
def anchorType : Tower.Tm 0 := .pi ground anchoredType

private def anchoredFormation {n : Nat} : Replay (n + 1) :=
  .sigmaForm zero zero .headType (.idForm zero .headType .var .var)

def anchorCode : Replay 0 :=
  .lamIntro functionLevel (.piForm zero pairLevel .headType anchoredFormation)
    (.pairIntro pairLevel anchoredFormation .var (.reflIntro ground .var))

theorem anchor_checked : check Tower.rules noConversionCheck .nil anchor anchorType anchorCode = true := by
  decide

noncomputable def anchorMeaning (h : CofinalInaccessibles.{u}) : Meaning.{u} 0 :=
  .plain (fun _ => traceLam (graph (twoCode h).1 (fun x => ZFSet.pair x ∅)))

theorem anchor_assembles (h : CofinalInaccessibles.{u}) (constants : DeclName → ZFSet.{u}) :
    assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      anchorCode anchor anchorType = some (anchorMeaning h) := rfl

theorem anchor_computes (h : CofinalInaccessibles.{u}) (constants : DeclName → ZFSet.{u})
    (meaning : Meaning.{u} 0)
    (assembled : assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      anchorCode anchor anchorType = some meaning) (x : ZFSet.{u}) (inside : x ∈ (twoCode h).1) :
    traceApp (meaning.value Fin.elim0) x = ZFSet.pair x ∅ := by
  rw [anchor_assembles] at assembled
  cases Option.some.inj assembled
  exact traceApp_graph_beta _ inside

theorem anchor_result_in_dependent_fibre (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) (meaning : Meaning.{u} 0)
    (assembled : assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      anchorCode anchor anchorType = some meaning) (x : ZFSet.{u}) (inside : x ∈ (twoCode h).1) :
    traceApp (meaning.value Fin.elim0) x ∈ sigmaSet (twoCode h).1 (fun y => truthCode (x = y)) := by
  rw [anchor_computes h constants meaning assembled x inside]
  exact ZFSetDependentProducts.mem_sigmaSet.mpr
    ⟨x, inside, ∅, (mem_truthCode _ _).mpr ⟨rfl, rfl⟩, rfl⟩

/-- The returned pair cannot be consumed at another index. -/
theorem anchor_result_not_in_other_fibre (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) (meaning : Meaning.{u} 0)
    (assembled : assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      anchorCode anchor anchorType = some meaning) (x y : ZFSet.{u})
    (inside : x ∈ (twoCode h).1) (different : x ≠ y) :
    traceApp (meaning.value Fin.elim0) x ∉ sigmaSet (twoCode h).1 (fun z => truthCode (y = z)) := by
  rw [anchor_computes h constants meaning assembled x inside]
  intro member
  obtain ⟨z, _, proof, atProof, equal⟩ := ZFSetDependentProducts.mem_sigmaSet.mp member
  obtain ⟨_, same⟩ := (mem_truthCode _ _).mp atProof
  exact different ((ZFSet.pair_inj.mp equal).1.trans same.symm)

theorem anchor_projections (h : CofinalInaccessibles.{u}) (constants : DeclName → ZFSet.{u})
    (meaning : Meaning.{u} 0)
    (assembled : assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      anchorCode anchor anchorType = some meaning) (x : ZFSet.{u}) (inside : x ∈ (twoCode h).1) :
    Mettapedia.SetTheory.ZFSetOrderedPair.first (traceApp (meaning.value Fin.elim0) x) = x ∧
      Mettapedia.SetTheory.ZFSetOrderedPair.second (traceApp (meaning.value Fin.elim0) x) = ∅ := by
  rw [anchor_computes h constants meaning assembled x inside]
  exact ⟨Mettapedia.SetTheory.ZFSetOrderedPair.first_pair _ _,
    Mettapedia.SetTheory.ZFSetOrderedPair.second_pair _ _⟩

def anchorApplication : Tower.Tm 1 := .app (liftClosed anchor) (.var 0)
def anchorApplicationType : Tower.Tm 1 := inst0 (.var 0) anchoredType
def anchorApplicationCode : Replay 1 :=
  .appElim ground anchoredType (anchorCode.rename noConversionRename Fin.elim0) .var
def anchorReduct : Tower.Tm 1 := .pair (.var 0) (.refl (.var 0))
def anchorReductCode : Replay 1 :=
  .pairIntro pairLevel anchoredFormation .var (.reflIntro ground .var)

theorem anchor_application_checked : check Tower.rules noConversionCheck (.snoc .nil ground)
    anchorApplication anchorApplicationType anchorApplicationCode = true := by decide

theorem anchor_reduct_checked : check Tower.rules noConversionCheck (.snoc .nil ground)
    anchorReduct anchorApplicationType anchorReductCode = true := by decide

theorem anchor_application_step :
    StepCore RootComputation.empty (fun (_ _ : Tower.Head) => False) anchorApplication anchorReduct :=
  .betaPi (.pair (.var 0) (.refl (.var 0))) (.var 0)

/-- Actual native application and its checked reduct, interpreted by the same
recursive assembly function, agree at every well-typed input environment. -/
theorem anchor_application_preserves_meaning (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) (before after : Meaning.{u} 1)
    (atBefore : assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      anchorApplicationCode anchorApplication anchorApplicationType = some before)
    (atAfter : assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      anchorReductCode anchorReduct anchorApplicationType = some after)
    (env : Environment.{u} 1) (inside : env 0 ∈ (twoCode h).1) :
    before.value env = after.value env := by
  have lifted := assemble_rename noConversionRename
    (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants anchorCode anchor anchorType
    (anchorMeaning h) (anchor_assembles h constants) (Fin.elim0 : Ren 0 1)
  change assemble _ constants (anchorCode.rename noConversionRename Fin.elim0)
    (liftClosed anchor) (.pi ground anchoredType) = some _ at lifted
  simp [anchorApplicationCode, anchorApplication, assemble, lifted] at atBefore
  have reduct : assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      anchorReductCode anchorReduct anchorApplicationType =
        some (.plain (fun env => ZFSet.pair (env 0) ∅)) := rfl
  rw [reduct] at atAfter
  cases Option.some.inj atAfter
  subst before
  exact traceApp_graph_beta _ inside

def keepOpenBody : Tower.Tm 2 := .lam (.var 1)
def keepOpenBodyCode : Replay 2 := .lamIntro pairLevel arrowFormation .var
def keepOpenApplication : Tower.Tm 1 := .app (liftClosed keep) (.var 0)
def keepOpenApplicationCode : Replay 1 :=
  .appElim ground (.pi ground ground) (keepCode.rename noConversionRename Fin.elim0) .var
def keepOpenReduct : Tower.Tm 1 := inst0 (.var 0) keepOpenBody
def keepOpenReductCode : Replay 1 :=
  Code.instantiate noConversionRename noConversionSubstitute
    keepOpenBody (.pi ground ground) (.var 0) keepOpenBodyCode .var

theorem keep_open_body_checked : check Tower.rules noConversionCheck
    (.snoc (.snoc .nil ground) ground) keepOpenBody (.pi ground ground) keepOpenBodyCode = true := by decide

theorem keep_open_application_checked : check Tower.rules noConversionCheck (.snoc .nil ground)
    keepOpenApplication (.pi ground ground) keepOpenApplicationCode = true := by decide

theorem keep_open_reduct_checked : check Tower.rules noConversionCheck (.snoc .nil ground)
    keepOpenReduct (.pi ground ground) keepOpenReductCode = true := by decide

theorem keep_open_step : StepCore RootComputation.empty (fun (_ _ : Tower.Head) => False)
    keepOpenApplication keepOpenReduct := .betaPi keepOpenBody (.var 0)

/-- The generic instantiation law constructs the meaning of a returned closure
whose free variable has crossed a binder. The reduct's certificate is generated
by Code.instantiate, not replaced by a separately selected typing proof. -/
theorem keep_open_instantiated_meaning (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) :
    ∃ result, assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
        keepOpenReductCode keepOpenReduct (.pi ground ground) = some result ∧
      ∀ env, result.value env = traceLam (graph (twoCode h).1 (fun _ => env 0)) := by
  let bodyMeaning : Meaning.{u} 2 :=
    .plain (fun env => traceLam (graph (twoCode h).1 (fun _ => env 0)))
  have atBody : assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      keepOpenBodyCode keepOpenBody (.pi ground ground) = some bodyMeaning := rfl
  have atArgument : assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      (Code.var : Replay 1) (.var 0) ground = some (.plain (fun env => env 0)) := rfl
  obtain ⟨result, assembled, values⟩ :=
    assemble_instantiate noConversionRename noConversionSubstitute
      (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants Tower.rules noConversionCheck
      keepOpenBodyCode .var bodyMeaning (.plain (fun env => env 0))
      keep_open_body_checked atBody atArgument
  exact ⟨result, assembled, values⟩

theorem keep_open_rejects_capture (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) :
    ∃ result, assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
        keepOpenReductCode keepOpenReduct (.pi ground ground) = some result ∧
      traceApp (result.value (fun _ => ∅)) (ZFSet.powerset ∅) ≠ ZFSet.powerset ∅ := by
  obtain ⟨result, assembled, values⟩ := keep_open_instantiated_meaning h constants
  refine ⟨result, assembled, ?_⟩
  have inside : ZFSet.powerset (∅ : ZFSet.{u}) ∈ (twoCode h).1 :=
    ZFSetDependentProducts.Controls.power_empty_mem_two
  rw [values, traceApp_graph_beta _ inside]
  intro equal
  have member : (∅ : ZFSet.{u}) ∈ ZFSet.powerset ∅ := by simp
  rw [← equal] at member
  exact ZFSet.notMem_empty _ member

theorem keep_open_beta_preserves_meaning (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) (env : Environment.{u} 1) (inside : env 0 ∈ (twoCode h).1) :
    ∃ before after,
      assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
        keepOpenApplicationCode keepOpenApplication (.pi ground ground) = some before ∧
      assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
        keepOpenReductCode keepOpenReduct (.pi ground ground) = some after ∧
      before.value env = after.value env := by
  let bodyMeaning : Meaning.{u} 2 :=
    .plain (fun env => traceLam (graph (twoCode h).1 (fun _ => env 0)))
  let formed : Meaning.{u} 1 :=
    ⟨fun _ => ZFSetTraceProducts.tracePiSet (twoCode h).1
      (fun _ => ZFSetTraceProducts.tracePiSet (twoCode h).1 (fun _ => (twoCode h).1)),
      some (fun _ => (twoCode h).1)⟩
  let before : Meaning.{u} 1 := .plain (fun env =>
    traceApp (traceLam (graph (twoCode h).1
      (fun x => traceLam (graph (twoCode h).1 (fun _ => x))))) (env 0))
  have atBefore : assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      keepOpenApplicationCode keepOpenApplication (.pi ground ground) = some before := rfl
  obtain ⟨after, atAfter, same⟩ := application_lambda_instantiated_value
    (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
    noConversionRename noConversionSubstitute Tower.rules noConversionCheck
    (.snoc .nil ground) functionLevel ground (.pi ground ground) keepOpenBody (.var 0)
    (.piForm zero pairLevel .headType arrowFormation) .var keepOpenBodyCode
    formed (.plain (fun env => env 0)) before bodyMeaning (fun _ => (twoCode h).1)
    keep_open_body_checked rfl rfl rfl rfl atBefore env inside
  exact ⟨before, after, atBefore, atAfter, same⟩

def identityContext : Ctx Tower.Head 2 :=
  .snoc (.snoc .nil ground) (.id ground (.var 0) (.var 0))
def identityContextCode : ContextCode Tower.Head NoConversion 2 :=
  .snoc (.snoc .nil zero .headType) zero (.idForm zero .headType .var .var)

theorem identity_context_checked : checkContext Tower.rules noConversionCheck
    identityContext identityContextCode = true := by decide

/-- The semantic context admits the actual reflexivity value and rejects a
nonempty set substituted for it, while retaining a nonempty object value. -/
theorem identity_context_values (h : CofinalInaccessibles.{u}) (constants : DeclName → ZFSet.{u}) :
    ∃ valid, assembleContext (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
        identityContextCode identityContext = some valid ∧
      valid (Fin.cases ∅ (fun _ => ZFSet.powerset ∅)) ∧
      ¬ valid (fun _ => ZFSet.powerset ∅) := by
  let valid : Environment.{u} 2 → Prop := fun env =>
    (True ∧ env 1 ∈ (twoCode h).1) ∧ env 0 ∈ truthCode (env 1 = env 1)
  refine ⟨valid, rfl, ?_, ?_⟩
  · exact ⟨⟨True.intro, ZFSetDependentProducts.Controls.power_empty_mem_two⟩,
      (mem_truthCode _ _).mpr ⟨rfl, rfl⟩⟩
  · intro holds
    have equal := ((mem_truthCode _ _).mp holds.2).1
    change ZFSet.powerset (∅ : ZFSet.{u}) = ∅ at equal
    have member : (∅ : ZFSet.{u}) ∈ ZFSet.powerset ∅ := by simp
    rw [equal] at member
    exact ZFSet.notMem_empty _ member

theorem identity_context_lookup (h : CofinalInaccessibles.{u}) (constants : DeclName → ZFSet.{u})
    {valid : Environment.{u} 2 → Prop}
    (assembled : assembleContext (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      identityContextCode identityContext = some valid)
    (index : Fin 2) (env : Environment.{u} 2) (holds : valid env) :
    ∃ meaning,
      assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
        (identityContextCode.lookupFormation noConversionRename index).2 (identityContext.lookup index)
        (.head (identityContextCode.lookupFormation noConversionRename index).1) = some meaning ∧
      env index ∈ meaning.value env :=
  lookupFormation_membership noConversionRename (interpretHead h ∅ (twoCode h).1 (fun _ => 0))
    constants identityContextCode assembled index env holds

private def inputContextCode : ContextCode Tower.Head NoConversion 1 :=
  .snoc .nil zero .headType

/-- Execute extraction on the checked higher-order application. -/
theorem anchor_application_resultFormation :
    anchorApplicationCode.resultFormation noConversionRename noConversionSubstitute
      TowerDecisions.headTarget inputContextCode anchorApplication anchorApplicationType =
        some (pairLevel, anchoredFormation) := rfl

noncomputable def anchorApplicationMeaning (h : CofinalInaccessibles.{u}) : Meaning.{u} 1 :=
  .plain (fun env => traceApp ((anchorMeaning h).value Fin.elim0) (env 0))

noncomputable def anchorApplicationTypeMeaning (h : CofinalInaccessibles.{u}) : Meaning.{u} 1 :=
  .plain (fun env => sigmaSet (twoCode h).1 (fun x => truthCode (env 0 = x)))

/-- The pair introduction consumes the reflexivity constructor's actual
extracted identity formation. Both general introduction laws are used here. -/
theorem anchor_pair_member (h : CofinalInaccessibles.{u}) (constants : DeclName → ZFSet.{u})
    (env : Environment.{u} 1) (inside : env 0 ∈ (twoCode h).1) :
    ZFSet.pair (env 0) ∅ ∈ (anchorApplicationTypeMeaning h).value env := by
  let heads := interpretHead h ∅ (twoCode h).1 (fun _ => 0)
  have proofTyped : (∅ : ZFSet.{u}) ∈ truthCode (env 0 = env 0) := by
    obtain ⟨proof, proofType, _, atProof, atType, member⟩ := reflexivity_result_membership
      heads constants noConversionRename noConversionSubstitute TowerDecisions.headTarget
      inputContextCode ground (.var 0) .var .headType zero (.plain (fun env => env 0)) rfl rfl
    change some (.plain (fun _ => (∅ : ZFSet.{u}))) = some proof at atProof
    change some (.plain (fun env => truthCode (env 0 = env 0))) = some proofType at atType
    cases Option.some.inj atProof
    cases Option.some.inj atType
    exact member env
  exact (pair_result_membership heads constants noConversionRename noConversionSubstitute
    TowerDecisions.headTarget Tower.rules noConversionCheck (.snoc .nil ground) inputContextCode
    ground (.var 0) (.refl (.var 0)) (.id ground (.var 1) (.var 0))
    anchoredFormation .headType .var (.reflIntro ground .var) (.idForm zero .headType .var .var)
    pairLevel zero zero (anchorApplicationTypeMeaning h) (.plain (fun _ => (twoCode h).1))
    (.plain (fun env => env 0)) (.plain (fun _ => ∅))
    (.plain (fun env => truthCode (env 0 = env 0))) (.plain (fun env => ZFSet.pair (env 0) ∅))
    (.plain (fun env => truthCode (env 1 = env 0)))
    rfl rfl rfl rfl (by decide) rfl rfl rfl rfl env inside proofTyped).2

/-- Contextual lambda introduction closes the pair-producing program.
Its body membership comes from the preceding pair/reflexivity composition. -/
theorem anchor_function_member (h : CofinalInaccessibles.{u}) (constants : DeclName → ZFSet.{u}) :
    (anchorMeaning h).value Fin.elim0 ∈ ZFSetTraceProducts.tracePiSet (twoCode h).1
      (fun x => sigmaSet (twoCode h).1 (fun y => truthCode (x = y))) := by
  let formed : Meaning.{u} 0 := ⟨fun _ => ZFSetTraceProducts.tracePiSet (twoCode h).1
    (fun x => sigmaSet (twoCode h).1 (fun y => truthCode (x = y))), some (fun _ => (twoCode h).1)⟩
  exact (lambda_result_membership (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
    noConversionRename noConversionSubstitute TowerDecisions.headTarget .nil .nil
    ground anchoredType (.pair (.var 0) (.refl (.var 0)))
    (.piForm zero pairLevel .headType anchoredFormation) .headType anchoredFormation
    anchorReductCode functionLevel zero pairLevel formed (.plain (fun _ => (twoCode h).1))
    (anchorMeaning h) (anchorApplicationTypeMeaning h) (.plain (fun env => ZFSet.pair (env 0) ∅))
    (fun _ => True) (fun env => True ∧ env 0 ∈ (twoCode h).1)
    rfl rfl rfl rfl rfl rfl rfl rfl
    (fun env admitted => anchor_pair_member h constants env admitted.2) Fin.elim0 True.intro).2

/-- The generic application soundness case supplies the membership used by
both subsequent projections, discharging its function premise by trace-product
introduction rather than assuming a whole-derivation soundness theorem. -/
theorem anchor_application_member (h : CofinalInaccessibles.{u}) (constants : DeclName → ZFSet.{u})
    (env : Environment.{u} 1) (inside : env 0 ∈ (twoCode h).1) :
    (anchorApplicationMeaning h).value env ∈ (anchorApplicationTypeMeaning h).value env := by
  let heads := interpretHead h ∅ (twoCode h).1 (fun _ => 0)
  let formed : Meaning.{u} 1 := ⟨fun _ => ZFSetTraceProducts.tracePiSet (twoCode h).1
    (fun x => sigmaSet (twoCode h).1 (fun y => truthCode (x = y))),
    some (fun _ => (twoCode h).1)⟩
  let body : Meaning.{u} 2 :=
    .plain (fun env => sigmaSet (twoCode h).1 (fun y => truthCode (env 0 = y)))
  have functionTyped : (anchorMeaning h).value Fin.elim0 ∈ formed.value env := by
    change traceLam (graph (twoCode h).1 (fun x => ZFSet.pair x ∅)) ∈
      ZFSetTraceProducts.tracePiSet (twoCode h).1
        (fun x => sigmaSet (twoCode h).1 (fun y => truthCode (x = y)))
    exact anchor_function_member h constants
  obtain ⟨resultType, _, assembled, member⟩ := application_result_membership
    heads constants noConversionRename noConversionSubstitute TowerDecisions.headTarget
    Tower.rules noConversionCheck (.snoc .nil ground) inputContextCode
    ground (liftClosed anchor) (.var 0) anchoredType
    (anchorCode.rename noConversionRename Fin.elim0) .var
    (.piForm zero pairLevel .headType anchoredFormation) .headType anchoredFormation
    functionLevel zero pairLevel
    ((anchorMeaning h).reindex Fin.elim0) formed (.plain (fun _ => (twoCode h).1))
    (.plain (fun env => env 0)) (anchorApplicationMeaning h) body
    rfl rfl (by decide) rfl rfl rfl rfl rfl rfl env functionTyped inside
  have expected : assemble heads constants
      (anchoredFormation.instantiateFormation noConversionRename noConversionSubstitute
        anchoredType pairLevel (.var 0) .var) (inst0 (.var 0) anchoredType) (.head pairLevel) =
      some (anchorApplicationTypeMeaning h) := rfl
  rw [expected] at assembled
  cases Option.some.inj assembled
  exact member

def anchorFirstCode : Replay 1 := .fstElim (.id ground (.var 1) (.var 0)) anchorApplicationCode
def anchorSecondCode : Replay 1 := .sndElim ground (.id ground (.var 1) (.var 0)) anchorApplicationCode
def anchorSecondType : Tower.Tm 1 :=
  inst0 (.fst anchorApplication) (.id ground (.var 1) (.var 0))
def anchorSecondFormation : Replay 1 :=
  Code.instantiateFormation noConversionRename noConversionSubstitute
    (.id ground (.var 1) (.var 0)) zero (.fst anchorApplication)
    (.idForm zero .headType .var .var) anchorFirstCode

theorem anchor_first_checked : check Tower.rules noConversionCheck (.snoc .nil ground)
    (.fst anchorApplication) ground anchorFirstCode = true := by decide

theorem anchor_second_checked : check Tower.rules noConversionCheck (.snoc .nil ground)
    (.snd anchorApplication) anchorSecondType anchorSecondCode = true := by decide

theorem anchor_second_formation_checked : check Tower.rules noConversionCheck (.snoc .nil ground)
    anchorSecondType (.head zero) anchorSecondFormation = true := by decide

theorem anchor_first_member (h : CofinalInaccessibles.{u}) (constants : DeclName → ZFSet.{u})
    (env : Environment.{u} 1) (inside : env 0 ∈ (twoCode h).1) :
    anchorFirstCode.resultFormation noConversionRename noConversionSubstitute TowerDecisions.headTarget
        inputContextCode (.fst anchorApplication) ground = some (zero, .headType) ∧
      Mettapedia.SetTheory.ZFSetOrderedPair.first ((anchorApplicationMeaning h).value env) ∈
        (twoCode h).1 := by
  exact first_result_membership (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
    noConversionRename noConversionSubstitute TowerDecisions.headTarget inputContextCode
    ground anchorApplication (.id ground (.var 1) (.var 0)) anchorApplicationCode
    anchoredFormation .headType (.idForm zero .headType .var .var) pairLevel zero zero
    (anchorApplicationMeaning h) (anchorApplicationTypeMeaning h) (.plain (fun _ => (twoCode h).1))
    (.plain (fun env => Mettapedia.SetTheory.ZFSetOrderedPair.first
      ((anchorApplicationMeaning h).value env)))
    anchor_application_resultFormation rfl rfl rfl rfl rfl env
    (anchor_application_member h constants env inside)

/-- A dependent proof consumer uses the computed first projection as its
index. Its result formation contains that very first-projection certificate. -/
theorem anchor_second_member (h : CofinalInaccessibles.{u}) (constants : DeclName → ZFSet.{u})
    (env : Environment.{u} 1) (inside : env 0 ∈ (twoCode h).1) :
    ∃ resultType,
      anchorSecondCode.resultFormation noConversionRename noConversionSubstitute
        TowerDecisions.headTarget inputContextCode (.snd anchorApplication) anchorSecondType =
          some (zero, anchorSecondFormation) ∧
      assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants anchorSecondFormation
        anchorSecondType (.head zero) = some resultType ∧
      Mettapedia.SetTheory.ZFSetOrderedPair.second ((anchorApplicationMeaning h).value env) ∈
        resultType.value env := by
  exact second_result_membership (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
    noConversionRename noConversionSubstitute TowerDecisions.headTarget Tower.rules noConversionCheck
    (.snoc .nil ground) inputContextCode ground anchorApplication (.id ground (.var 1) (.var 0))
    anchorApplicationCode anchoredFormation .headType (.idForm zero .headType .var .var)
    pairLevel zero zero (anchorApplicationMeaning h) (anchorApplicationTypeMeaning h)
    (.plain (fun env => Mettapedia.SetTheory.ZFSetOrderedPair.second
      ((anchorApplicationMeaning h).value env))) (.plain (fun env => truthCode (env 1 = env 0)))
    anchor_application_resultFormation rfl (by decide) rfl rfl rfl rfl env
    (anchor_application_member h constants env inside)

theorem anchor_second_wrong_carrier_rejected : check Tower.rules noConversionCheck
    (.snoc .nil ground) (.snd anchorApplication)
    (.id (.head zero) (.var 0) (.fst anchorApplication)) anchorSecondCode = false := by decide

/-- A non-proof object cannot inhabit the generated identity fibre, even
though it is a legitimate object in the chosen ground carrier. -/
theorem anchor_second_rejects_nonproof (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) (resultType : Meaning.{u} 1)
    (assembled : assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      anchorSecondFormation anchorSecondType (.head zero) = some resultType)
    (env : Environment.{u} 1) : ZFSet.powerset ∅ ∉ resultType.value env := by
  have expected : assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      anchorSecondFormation anchorSecondType (.head zero) =
      some (.plain (fun env => truthCode (env 0 =
        Mettapedia.SetTheory.ZFSetOrderedPair.first ((anchorApplicationMeaning h).value env)))) := rfl
  rw [expected] at assembled
  cases Option.some.inj assembled
  intro member
  have equal := ((mem_truthCode _ _).mp member).1
  have emptyMember : (∅ : ZFSet.{u}) ∈ ZFSet.powerset ∅ := by simp
  rw [equal] at emptyMember
  exact ZFSet.notMem_empty _ emptyMember

/-- The source formation is structural, but its actual first-projection
instance is not. Agreement is transported by certificate instantiation. -/
def anchorSecondRaisedFormation : Replay 1 :=
  Code.instantiate noConversionRename noConversionSubstitute
    (.id ground (.var 1) (.var 0)) (.head (.sort (.succ Tower.zero))) (.fst anchorApplication)
    (.cumul zero (.idForm zero .headType .var .var)) anchorFirstCode

theorem anchor_second_raised_formation_checked : check Tower.rules noConversionCheck
    (.snoc .nil ground) anchorSecondType (.head (.sort (.succ Tower.zero)))
    anchorSecondRaisedFormation = true := by decide

theorem anchor_second_formation_codes_differ :
    anchorSecondFormation ≠ anchorSecondRaisedFormation := by
  intro equal
  cases equal

theorem anchor_second_support_boundary :
    ZFSetTypeExpressionInterpretation.supported
      (.id ground (.var 1) (.var 0) : Tower.Tm 2) = true ∧
    ZFSetTypeExpressionInterpretation.supported anchorSecondType = false := ⟨rfl, rfl⟩

theorem anchor_second_formation_values_agree (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) :
    ∃ lower upper,
      assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants anchorSecondFormation
        anchorSecondType (.head zero) = some lower ∧
      assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants anchorSecondRaisedFormation
        anchorSecondType (.head (.sort (.succ Tower.zero))) = some upper ∧
      lower.value = upper.value := by
  exact assemble_instantiate_supported_values (interpretHead h ∅ (twoCode h).1 (fun _ => 0))
    constants noConversionRename noConversionSubstitute Tower.rules noConversionCheck
    (.idForm zero .headType .var .var) (.cumul zero (.idForm zero .headType .var .var))
    anchorFirstCode (.plain (fun env => truthCode (env 1 = env 0)))
    (.plain (fun env => truthCode (env 1 = env 0)))
    (.plain (fun env => Mettapedia.SetTheory.ZFSetOrderedPair.first
      ((anchorApplicationMeaning h).value env)))
    (context := .snoc .nil ground) (A := ground)
    (subject := .id ground (.var 1) (.var 0)) (argument := .fst anchorApplication)
    (firstType := .head zero) (secondType := .head (.sort (.succ Tower.zero)))
    rfl (by decide) (by decide) rfl rfl rfl

/-- The proof produced by second projection remains a member when a later
consumer uses the distinct, cumulatively raised formation certificate. -/
theorem anchor_second_member_raised (h : CofinalInaccessibles.{u}) (constants : DeclName → ZFSet.{u})
    (env : Environment.{u} 1) (inside : env 0 ∈ (twoCode h).1) :
    ∃ raised,
      assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants anchorSecondRaisedFormation
        anchorSecondType (.head (.sort (.succ Tower.zero))) = some raised ∧
      Mettapedia.SetTheory.ZFSetOrderedPair.second ((anchorApplicationMeaning h).value env) ∈
        raised.value env := by
  obtain ⟨resultType, _, atResultType, member⟩ := anchor_second_member h constants env inside
  obtain ⟨lower, upper, atLower, atUpper, values⟩ := anchor_second_formation_values_agree h constants
  rw [atResultType] at atLower
  cases Option.some.inj atLower
  exact ⟨upper, atUpper, values ▸ member⟩

/-- Universe formation for the actual function type composes the Pi, Sigma
and identity replay cases over the existing cumulative set hierarchy. -/
theorem anchor_type_in_universe (h : CofinalInaccessibles.{u}) (constants : DeclName → ZFSet.{u}) :
    ∃ formed,
      assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
        (.piForm zero pairLevel .headType anchoredFormation : Replay 0) anchorType (.head functionLevel) =
          some formed ∧
      formed.value Fin.elim0 ∈ interpretHead h ∅ (twoCode h).1 (fun _ => 0) functionLevel := by
  let formed : Meaning.{u} 0 := ⟨fun _ => ZFSetTraceProducts.tracePiSet (twoCode h).1
    (fun x => sigmaSet (twoCode h).1 (fun y => truthCode (x = y))), some (fun _ => (twoCode h).1)⟩
  refine ⟨formed, rfl, ?_⟩
  apply ZFSetReplayUniverseFormation.pi_formation_membership h ∅ (twoCode h).1 (fun _ => 0) constants
    ground anchoredType .headType anchoredFormation zero pairLevel functionLevel
    (.plain (fun _ => (twoCode h).1)) formed (anchorApplicationTypeMeaning h)
    (.sorts _ _) rfl rfl rfl Fin.elim0 (twoCode h).2
  intro x _
  have atSigma : assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      (anchoredFormation : Replay 1) anchoredType (.head pairLevel) =
        some (anchorApplicationTypeMeaning h) := rfl
  apply ZFSetReplayUniverseFormation.sigma_formation_membership h ∅ (twoCode h).1 (fun _ => 0) constants
    ground (.id ground (.var 1) (.var 0)) .headType (.idForm zero .headType .var .var)
    zero zero pairLevel (.plain (fun _ => (twoCode h).1)) (anchorApplicationTypeMeaning h)
    (.plain (fun env => truthCode (env 1 = env 0))) (.sorts _ _) rfl rfl atSigma
    (ZFSetTypeExpressionInterpretation.extend Fin.elim0 x) (twoCode h).2
  intro y _
  exact ZFSetReplayUniverseFormation.identity_formation_membership h ∅ (twoCode h).1 (fun _ => 0)
    (ConversionCode := NoConversion) (n := 2)
    constants ground (.var 1) (.var 0) .headType .var .var zero
    (.plain (fun env => env 1)) (.plain (fun env => env 0))
    (.plain (fun env => truthCode (env 1 = env 0))) (.sort _)
    rfl rfl rfl (ZFSetTypeExpressionInterpretation.extend
      (ZFSetTypeExpressionInterpretation.extend Fin.elim0 x) y)

#print axioms anchor_second_raised_formation_checked
#print axioms anchor_second_formation_codes_differ
#print axioms anchor_second_support_boundary
#print axioms anchor_second_formation_values_agree
#print axioms anchor_second_member_raised
#print axioms anchor_type_in_universe
#print axioms anchor_pair_member
#print axioms anchor_function_member
#print axioms anchor_second_wrong_carrier_rejected
#print axioms anchor_second_rejects_nonproof
#print axioms anchor_application_resultFormation
#print axioms anchor_application_member
#print axioms anchor_first_checked
#print axioms anchor_second_checked
#print axioms anchor_second_formation_checked
#print axioms anchor_first_member
#print axioms anchor_second_member
#print axioms keep_open_beta_preserves_meaning
#print axioms identity_context_checked
#print axioms identity_context_values
#print axioms identity_context_lookup
#print axioms keep_open_body_checked
#print axioms keep_open_application_checked
#print axioms keep_open_reduct_checked
#print axioms keep_open_step
#print axioms keep_open_instantiated_meaning
#print axioms keep_open_rejects_capture
#print axioms keep_checked
#print axioms keep_computes
#print axioms keep_rejects_capture
#print axioms anchor_checked
#print axioms anchor_result_in_dependent_fibre
#print axioms anchor_result_not_in_other_fibre
#print axioms anchor_projections
#print axioms anchor_application_checked
#print axioms anchor_reduct_checked
#print axioms anchor_application_step
#print axioms anchor_application_preserves_meaning

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayInterpretationControls
