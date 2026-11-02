import Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeProofEvaluation
import Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeProducerChecks
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveElaborationAssembly
import Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeRightBundleComponents

/-!
# Original VectorTree branch-target publication

The outer method applications retain the original variable checks and their
exact intermediate types. The inner bundle is checked at its actual budget
254; the same retained code is replayed before publication at the original
endpoint budget 256. No fuel monotonicity or replacement evidence is used.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation NativeNaturalVectorFamilies
open Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeGuest
namespace Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeGuest.BranchRightOuterComponents

local instance : DecidableRel inventoryRules.headTyping :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headTyping h u))
local instance : DecidablePred inventoryRules.isUniverse :=
  fun h => inferInstanceAs (Decidable (Tower.rules.isUniverse h))
local instance : ∀ u v w, Decidable (inventoryRules.join u v w) :=
  fun h u v => inferInstanceAs (Decidable (Tower.rules.join h u v))
local instance : DecidableRel inventoryRules.cumulative :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.cumulative h u))
local instance : DecidableRel inventoryRules.headEq :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headEq h u))

def type0 : Tower.Tm 5 := Ctx.lookup branchContext 2
def body0 : Tower.Tm 6 := match type0 with | .pi _ body => body | _ => .head .legacyGround
theorem shape0 : type0 = .pi natTm body0 := rfl
def type1 : Tower.Tm 5 := inst0 (.var 1) body0
def body1 : Tower.Tm 6 := match type1 with | .pi _ body => body | _ => .head .legacyGround
theorem shape1 : type1 = .pi (vecApp treeTm (.var 1)) body1 := rfl
def type2 : Tower.Tm 5 := inst0 (.var 0) body1
theorem shape2 : type2 = .pi branchBundleType (rename wk branchIotaType) := rfl
def firstTerm : Tower.Tm 5 := .app (.var 2) (.var 1)
def secondTerm : Tower.Tm 5 := .app firstTerm (.var 0)
def code1 : FormationSensitiveElaboration.Code Tower.Head inventoryDecoder.Code 5 := .appElim natTm body0 .var .var
def code2 : FormationSensitiveElaboration.Code Tower.Head inventoryDecoder.Code 5 := .appElim (vecApp treeTm (.var 1)) body1 code1 .var

theorem method_origin : FormationSensitiveElaboration.synth inventoryRules inventoryChoices 252 branchContext (.var 2) =
    some ⟨type0,(.var : FormationSensitiveElaboration.Code Tower.Head inventoryDecoder.Code 5)⟩ := rfl


theorem view0 : inventoryChoices.normalize 252 type0 = .pi natTm body0 := by
  rw [ProducerEvidence.evaluationChoices_exact]
  decide +kernel

theorem length_origin : FormationSensitiveElaboration.check inventoryRules inventoryChoices 252 branchContext (.var 1) natTm =
    some (.var : FormationSensitiveElaboration.Code Tower.Head inventoryDecoder.Code 5) := by
  rw [ProducerEvidence.evaluationChoices_exact]
  rfl

theorem first_origin : FormationSensitiveElaboration.synth inventoryRules inventoryChoices 253 branchContext firstTerm = some ⟨type1,code1⟩ := by
  have nonLambda : ∀ body, (.var 2 : Tower.Tm 5) ≠ .lam body := by intro body same; cases same
  have aligned : FormationSensitiveElaboration.align inventoryRules inventoryChoices 252 branchContext (.var 2)
      type0 (.pi natTm body0) (.var : FormationSensitiveElaboration.Code Tower.Head inventoryDecoder.Code 5) = some .var := by
    rw [← shape0]
    simp [FormationSensitiveElaboration.align]
  have application : FormationSensitiveElaboration.synth inventoryRules inventoryChoices 253 branchContext
      (.app (.var 2) (.var 1)) = some
        ⟨inst0 (.var 1) body0,StructuralTypingReplay.Code.appElim natTm body0 .var .var⟩ := by
    with_reducible
      exact FormationSensitiveElaboration.synth_application_of inventoryRules inventoryChoices 252 branchContext
        (.var 2) (.var 1) nonLambda ⟨type0,.var⟩ natTm body0 .var .var method_origin view0 aligned length_origin
  simpa only [firstTerm,type1,code1] using application

theorem view1 : inventoryChoices.normalize 253 type1 = .pi (vecApp treeTm (.var 1)) body1 := by
  rw [ProducerEvidence.evaluationChoices_exact]
  decide +kernel

theorem children_origin : FormationSensitiveElaboration.check inventoryRules inventoryChoices 253 branchContext (.var 0)
    (vecApp treeTm (.var 1)) = some (.var : FormationSensitiveElaboration.Code Tower.Head inventoryDecoder.Code 5) := by
  rw [ProducerEvidence.evaluationChoices_exact]
  rfl

theorem second_origin : FormationSensitiveElaboration.synth inventoryRules inventoryChoices 254 branchContext secondTerm = some ⟨type2,code2⟩ := by
  have nonLambda : ∀ body, firstTerm ≠ .lam body := by intro body same; cases same
  have aligned : FormationSensitiveElaboration.align inventoryRules inventoryChoices 253 branchContext firstTerm
      type1 (.pi (vecApp treeTm (.var 1)) body1) code1 = some code1 := by
    rw [← shape1]
    simp [FormationSensitiveElaboration.align]
  have application : FormationSensitiveElaboration.synth inventoryRules inventoryChoices 254 branchContext
      (.app firstTerm (.var 0)) = some
        ⟨inst0 (.var 0) body1,StructuralTypingReplay.Code.appElim (vecApp treeTm (.var 1)) body1 code1 .var⟩ := by
    with_reducible
      exact FormationSensitiveElaboration.synth_application_of inventoryRules inventoryChoices 253 branchContext
        firstTerm (.var 0) nonLambda ⟨type1,code1⟩ (vecApp treeTm (.var 1)) body1 code1 .var first_origin view1 aligned children_origin
  simpa only [secondTerm,type2,code2] using application

theorem view2 : inventoryChoices.normalize 254 type2 = .pi branchBundleType (rename wk branchIotaType) := by
  rw [ProducerEvidence.evaluationChoices_exact]
  decide +kernel

theorem method_replay : StructuralTypingReplay.check inventoryRules
    (fun code left right => code.check inventoryRules.headEq inventoryDecoder.decode left right)
    branchContext (.var 2) type0 (.var : FormationSensitiveElaboration.Code Tower.Head inventoryDecoder.Code 5) = true := by decide +kernel
theorem length_replay : StructuralTypingReplay.check inventoryRules
    (fun code left right => code.check inventoryRules.headEq inventoryDecoder.decode left right)
    branchContext (.var 1) natTm (.var : FormationSensitiveElaboration.Code Tower.Head inventoryDecoder.Code 5) = true := by decide +kernel
theorem children_replay : StructuralTypingReplay.check inventoryRules
    (fun code left right => code.check inventoryRules.headEq inventoryDecoder.decode left right)
    branchContext (.var 0) (vecApp treeTm (.var 1)) (.var : FormationSensitiveElaboration.Code Tower.Head inventoryDecoder.Code 5) = true := by decide +kernel

theorem first_replay : StructuralTypingReplay.check inventoryRules
    (fun code left right => code.check inventoryRules.headEq inventoryDecoder.decode left right)
    branchContext firstTerm type1 code1 = true := by
  unfold firstTerm code1
  rw [StructuralTypingReplay.check]
  have prior := method_replay
  rw [shape0] at prior
  rw [prior,length_replay]
  decide +kernel
theorem second_replay : StructuralTypingReplay.check inventoryRules
    (fun code left right => code.check inventoryRules.headEq inventoryDecoder.decode left right)
    branchContext secondTerm type2 code2 = true := by
  unfold secondTerm code2
  rw [StructuralTypingReplay.check]
  have prior := first_replay
  rw [shape1] at prior
  rw [prior,children_replay]
  decide +kernel


def rightCode (inner : FormationSensitiveElaboration.Code Tower.Head inventoryDecoder.Code 5) :
    FormationSensitiveElaboration.Code Tower.Head inventoryDecoder.Code 5 :=
  .appElim branchBundleType (rename wk branchIotaType) code2 inner

private theorem check_application_of {Head : Type} {RootCode : Nat → Type}
    (R : Rules Head) (choices : FormationSensitiveElaboration.Choices Head RootCode) [DecidableEq Head]
    (fuel : Nat) {n : Nat} (context : Ctx Head n) (function argument expected : Tm Head n)
    (inferred : FormationSensitiveElaboration.Inferred Head RootCode n)
    (result : FormationSensitiveElaboration.Code Head RootCode n)
    (produced : FormationSensitiveElaboration.synth R choices fuel context (.app function argument) = some inferred)
    (aligned : FormationSensitiveElaboration.align R choices fuel context (.app function argument)
      inferred.type expected inferred.evidence = some result) :
    FormationSensitiveElaboration.check R choices (fuel+1) context (.app function argument) expected = some result := by
  cases choices.normalize fuel expected <;>
    simp only [FormationSensitiveElaboration.check,produced,aligned,Option.bind_eq_bind,Option.bind_some]

theorem right_origin (inner : FormationSensitiveElaboration.Code Tower.Head inventoryDecoder.Code 5)
    (produced : FormationSensitiveElaboration.check inventoryRules inventoryChoices 254 branchContext branchBundle branchBundleType = some inner) :
    FormationSensitiveElaboration.check inventoryRules inventoryChoices 256 branchContext branchRight branchIotaType = some (rightCode inner) := by
  have nonLambda : ∀ body, secondTerm ≠ .lam body := by intro body same; cases same
  have aligned : FormationSensitiveElaboration.align inventoryRules inventoryChoices 254 branchContext
      secondTerm type2 (.pi branchBundleType (rename wk branchIotaType)) code2 = some code2 := by
    rw [← shape2]
    simp [FormationSensitiveElaboration.align]
  have computed : FormationSensitiveElaboration.synth inventoryRules inventoryChoices 255 branchContext
      (.app secondTerm branchBundle) = some
        ⟨inst0 branchBundle (rename wk branchIotaType),
          StructuralTypingReplay.Code.appElim branchBundleType (rename wk branchIotaType) code2 inner⟩ := by
    with_reducible
      exact FormationSensitiveElaboration.synth_application_of inventoryRules inventoryChoices 254 branchContext
        secondTerm branchBundle nonLambda ⟨type2,code2⟩ branchBundleType (rename wk branchIotaType) code2 inner
        second_origin view2 aligned produced
  have result : inst0 branchBundle (rename wk branchIotaType) = branchIotaType := by decide +kernel
  rw [result] at computed
  have finalAlignment : FormationSensitiveElaboration.align inventoryRules inventoryChoices 255 branchContext
      (.app secondTerm branchBundle) branchIotaType branchIotaType (rightCode inner) = some (rightCode inner) := by
    simp [FormationSensitiveElaboration.align]
  change FormationSensitiveElaboration.check inventoryRules inventoryChoices 256 branchContext (.app secondTerm branchBundle) branchIotaType = _
  exact check_application_of inventoryRules inventoryChoices 255 branchContext secondTerm branchBundle branchIotaType
    ⟨branchIotaType,rightCode inner⟩ (rightCode inner) computed finalAlignment


theorem right_replay (inner : FormationSensitiveElaboration.Code Tower.Head inventoryDecoder.Code 5)
    (replayed : StructuralTypingReplay.check inventoryRules
      (fun code left right => code.check inventoryRules.headEq inventoryDecoder.decode left right)
      branchContext branchBundle branchBundleType inner = true) :
    StructuralTypingReplay.check inventoryRules
      (fun code left right => code.check inventoryRules.headEq inventoryDecoder.decode left right)
      branchContext branchRight branchIotaType (rightCode inner) = true := by
  unfold rightCode
  change StructuralTypingReplay.check inventoryRules
    (fun code left right => code.check inventoryRules.headEq inventoryDecoder.decode left right)
    branchContext (.app secondTerm branchBundle) branchIotaType
    (.appElim branchBundleType (rename wk branchIotaType) code2 inner) = true
  rw [StructuralTypingReplay.check]
  have prior := second_replay
  rw [shape2] at prior
  rw [prior,replayed]
  decide +kernel


private theorem termReplayAccepted_of_origin {Head : Type} (R : Rules Head) [DecidableEq Head]
    [DecidableRel R.headTyping] [DecidablePred R.isUniverse]
    [∀ u v w, Decidable (R.join u v w)] [DecidableRel R.cumulative] [DecidableRel R.headEq]
    (decoder : StructuralConversionCode.RootDecoder R.computation)
    (choices : FormationSensitiveElaboration.Choices Head decoder.Code) (fuel : Nat) {n : Nat}
    (context : Ctx Head n) (term type : Tm Head n)
    (code : FormationSensitiveElaboration.Code Head decoder.Code n)
    (produced : FormationSensitiveElaboration.check R choices fuel context term type = some code)
    (replayed : StructuralTypingReplay.check R
      (fun recipe left right => recipe.check R.headEq decoder.decode left right)
      context term type code = true) :
    FormationSensitiveElaboration.termReplayAccepted R decoder choices fuel context term type = true := by
  unfold FormationSensitiveElaboration.termReplayAccepted
  rw [produced]
  exact replayed

theorem right_accepted_of (inner : FormationSensitiveElaboration.Code Tower.Head inventoryDecoder.Code 5)
    (produced : FormationSensitiveElaboration.check inventoryRules inventoryChoices 254 branchContext branchBundle branchBundleType = some inner)
    (replayed : StructuralTypingReplay.check inventoryRules
      (fun code left right => code.check inventoryRules.headEq inventoryDecoder.decode left right)
      branchContext branchBundle branchBundleType inner = true) :
    endpointAccepted branchContext branchRight branchIotaType = true := by
  exact (ProofEvaluation.branch_endpoint_eq_termReplay branchRight branchIotaType).trans
    (termReplayAccepted_of_origin inventoryRules inventoryDecoder inventoryChoices 256 branchContext
      branchRight branchIotaType (rightCode inner) (right_origin inner produced) (right_replay inner replayed))


theorem right_accepted : endpointAccepted branchContext branchRight branchIotaType = true :=
  right_accepted_of BranchRightBundleComponents.bundleCode BranchRightBundleComponents.bundle_origin
    BranchRightBundleComponents.bundle_replay

#print axioms right_accepted_of
#print axioms right_accepted
end Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeGuest.BranchRightOuterComponents
