import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeVectorAllBaseComponents
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveIntroductionReplay

/-!
# Undeclared-witness refusal in the original native Vector All producer

The unknown constant fails lookup in the actual signature. That failure
propagates through the original pair, lambda and application calls at their
unchanged fuel values. No alternative checker or typing witness is used.
-/

set_option autoImplicit false
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.ReplayComponents.Undeclared
open Presentation RussellTarski
open NativeNaturalVectorFamilies

local instance : DecidableRel NativeVectorAll.rules.headTyping :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headTyping h u))
local instance : DecidablePred NativeVectorAll.rules.isUniverse :=
  fun h => inferInstanceAs (Decidable (Tower.rules.isUniverse h))
local instance : ∀ u v w, Decidable (NativeVectorAll.rules.join u v w) :=
  fun u v w => inferInstanceAs (Decidable (Tower.rules.join u v w))
local instance : DecidableRel NativeVectorAll.rules.cumulative :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.cumulative h u))
local instance : DecidableRel NativeVectorAll.rules.headEq :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headEq h u))

private def type0 : Tower.Tm 5 := ReplayComponents.methodType
private def domain0 : Tower.Tm 5 := match type0 with | .pi a _ => a | _ => .head .legacyGround
private def type1 : Tower.Tm 6 := match type0 with | .pi _ b => b | _ => .head .legacyGround
private def context1 : Tower.Ctx 6 := .snoc contextAPWNV domain0
private def domain1 : Tower.Tm 6 := match type1 with | .pi a _ => a | _ => .head .legacyGround
private def type2 : Tower.Tm 7 := match type1 with | .pi _ b => b | _ => .head .legacyGround
private def context2 : Tower.Ctx 7 := .snoc context1 domain1
private def domain2 : Tower.Tm 7 := match type2 with | .pi a _ => a | _ => .head .legacyGround
private def type3 : Tower.Tm 8 := match type2 with | .pi _ b => b | _ => .head .legacyGround
private def context3 : Tower.Ctx 8 := .snoc context2 domain2
private def domain3 : Tower.Tm 8 := match type3 with | .pi a _ => a | _ => .head .legacyGround
private def type4 : Tower.Tm 9 := match type3 with | .pi _ b => b | _ => .head .legacyGround
private def context4 : Tower.Ctx 9 := .snoc context3 domain3
private def pairDomain : Tower.Tm 9 := match type4 with | .sigma a _ => a | _ => .head .legacyGround
private def pairBody : Tower.Tm 10 := match type4 with | .sigma _ b => b | _ => .head .legacyGround

private theorem shape0 : type0 = .pi domain0 type1 := rfl
private theorem shape1 : type1 = .pi domain1 type2 := rfl
private theorem shape2 : type2 = .pi domain2 type3 := rfl
private theorem shape3 : type3 = .pi domain3 type4 := rfl
private theorem shape4 : type4 = .sigma pairDomain pairBody := rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem view0 : NativeVectorAll.choices.normalize 123 type0 = .pi domain0 type1 := by
  rw [ReplayComponents.choices_for_proof_evaluation]
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem view1 : NativeVectorAll.choices.normalize 122 type1 = .pi domain1 type2 := by
  rw [ReplayComponents.choices_for_proof_evaluation]
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem view2 : NativeVectorAll.choices.normalize 121 type2 = .pi domain2 type3 := by
  rw [ReplayComponents.choices_for_proof_evaluation]
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem view3 : NativeVectorAll.choices.normalize 120 type3 = .pi domain3 type4 := by
  rw [ReplayComponents.choices_for_proof_evaluation]
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem view4 : NativeVectorAll.choices.normalize 119 type4 = .sigma pairDomain pairBody := by
  rw [ReplayComponents.choices_for_proof_evaluation]
  decide +kernel

private theorem lambda_none_of_body_none {Head : Type} {RootCode : Nat → Type}
    (R : Rules Head) (choices : FormationSensitiveElaboration.Choices Head RootCode) [DecidableEq Head]
    (fuel : Nat) {n : Nat} (context : Ctx Head n) (body : Tm Head (n+1))
    (expected domain : Tm Head n) (codomain : Tm Head (n+1))
    (view : choices.normalize fuel expected = .pi domain codomain)
    (refused : FormationSensitiveElaboration.check R choices fuel (.snoc context domain) body codomain = none) :
    FormationSensitiveElaboration.check R choices (fuel+1) context (.lam body) expected = none := by
  simp only [FormationSensitiveElaboration.check,view]
  cases formed : FormationSensitiveElaboration.synth R choices fuel context (.pi domain codomain) with
  | none => simp
  | some inference =>
    rcases inference with ⟨type,formation⟩
    cases type <;> simp [refused]

private theorem pair_none_of_first_none {Head : Type} {RootCode : Nat → Type}
    (R : Rules Head) (choices : FormationSensitiveElaboration.Choices Head RootCode) [DecidableEq Head]
    (fuel : Nat) {n : Nat} (context : Ctx Head n) (first second expected domain : Tm Head n)
    (codomain : Tm Head (n+1)) (view : choices.normalize fuel expected = .sigma domain codomain)
    (refused : FormationSensitiveElaboration.check R choices fuel context first domain = none) :
    FormationSensitiveElaboration.check R choices (fuel+1) context (.pair first second) expected = none := by
  simp only [FormationSensitiveElaboration.check,view]
  cases formed : FormationSensitiveElaboration.synth R choices fuel context (.sigma domain codomain) with
  | none => simp
  | some inference =>
    rcases inference with ⟨type,formation⟩
    cases type <;> simp [refused]

private def first : Tower.Tm 9 := .app (.const `Undeclared.Witness) (.var 2)
private def pairSource : Tower.Tm 9 := .pair first (.var 0)
private def body3 : Tower.Tm 8 := .lam pairSource
private def body2 : Tower.Tm 7 := .lam body3
private def body1 : Tower.Tm 6 := .lam body2
private def methodSource : Tower.Tm 5 := .lam body1

private theorem first_none : FormationSensitiveElaboration.check NativeVectorAll.rules NativeVectorAll.choices
    119 context4 first pairDomain = none := by rfl

private theorem pair_none : FormationSensitiveElaboration.check NativeVectorAll.rules NativeVectorAll.choices
    120 context4 pairSource type4 = none :=
  pair_none_of_first_none NativeVectorAll.rules NativeVectorAll.choices 119 context4 first (.var 0)
    type4 pairDomain pairBody view4 first_none

private theorem body3_none : FormationSensitiveElaboration.check NativeVectorAll.rules NativeVectorAll.choices
    121 context3 body3 type3 = none :=
  lambda_none_of_body_none NativeVectorAll.rules NativeVectorAll.choices 120 context3 pairSource
    type3 domain3 type4 view3 pair_none

private theorem body2_none : FormationSensitiveElaboration.check NativeVectorAll.rules NativeVectorAll.choices
    122 context2 body2 type2 = none :=
  lambda_none_of_body_none NativeVectorAll.rules NativeVectorAll.choices 121 context2 body3
    type2 domain2 type3 view2 body3_none

private theorem body1_none : FormationSensitiveElaboration.check NativeVectorAll.rules NativeVectorAll.choices
    123 context1 body1 type1 = none :=
  lambda_none_of_body_none NativeVectorAll.rules NativeVectorAll.choices 122 context1 body2
    type1 domain1 type2 view1 body2_none

private theorem method_none : FormationSensitiveElaboration.check NativeVectorAll.rules NativeVectorAll.choices
    124 contextAPWNV methodSource ReplayComponents.methodType = none :=
  lambda_none_of_body_none NativeVectorAll.rules NativeVectorAll.choices 123 contextAPWNV body1
    type0 domain0 type1 view0 body1_none

#print axioms method_none

private theorem synth_application_none_of_argument {Head : Type} {RootCode : Nat → Type}
    (R : Rules Head) (choices : FormationSensitiveElaboration.Choices Head RootCode) [DecidableEq Head]
    (fuel : Nat) {n : Nat} (context : Ctx Head n) (function argument : Tm Head n)
    (notLambda : ∀ body, function ≠ .lam body)
    (inferred : FormationSensitiveElaboration.Inferred Head RootCode n)
    (domain : Tm Head n) (body : Tm Head (n+1))
    (prior : FormationSensitiveElaboration.synth R choices fuel context function = some inferred)
    (view : choices.normalize fuel inferred.type = .pi domain body)
    (refused : FormationSensitiveElaboration.check R choices fuel context argument domain = none) :
    FormationSensitiveElaboration.synth R choices (fuel+1) context (.app function argument) = none := by
  cases function <;> try { exact False.elim (notLambda _ rfl) }
  all_goals simp [FormationSensitiveElaboration.synth,prior,view,refused]

private theorem synth_application_none_of_function {Head : Type} {RootCode : Nat → Type}
    (R : Rules Head) (choices : FormationSensitiveElaboration.Choices Head RootCode) [DecidableEq Head]
    (fuel : Nat) {n : Nat} (context : Ctx Head n) (function argument : Tm Head n)
    (notLambda : ∀ body, function ≠ .lam body)
    (prior : FormationSensitiveElaboration.synth R choices fuel context function = none) :
    FormationSensitiveElaboration.synth R choices (fuel+1) context (.app function argument) = none := by
  cases function <;> try { exact False.elim (notLambda _ rfl) }
  all_goals simp [FormationSensitiveElaboration.synth,prior]

private def source4 : Tower.Tm 5 := .app ReplayComponents.baseApplication methodSource
private def source5 : Tower.Tm 5 := .app source4 (.var 1)
private def source6 : Tower.Tm 5 := .app source5 (.var 0)

private theorem source6_eq : source6 = allEvidence (.var 4) (.var 3) (.const `Undeclared.Witness) (.var 1) (.var 0) := rfl

private theorem synth4_none : FormationSensitiveElaboration.synth NativeVectorAll.rules NativeVectorAll.choices
    125 contextAPWNV source4 = none := by
  have notLambda : ∀ body : Tower.Tm 6, ReplayComponents.baseApplication ≠ .lam body := by
    intro body h
    unfold ReplayComponents.baseApplication at h
    cases h
  unfold source4
  with_reducible
    exact synth_application_none_of_argument NativeVectorAll.rules NativeVectorAll.choices
      124 contextAPWNV ReplayComponents.baseApplication methodSource notLambda
      ⟨ReplayComponents.baseApplicationType,ReplayComponents.baseApplicationCode⟩
      ReplayComponents.methodType ReplayComponents.afterMethodType ReplayComponents.baseApplication_produced
      (ReplayComponents.baseApplication_viewed.trans ReplayComponents.baseApplicationType_shape) method_none

private theorem synth5_none : FormationSensitiveElaboration.synth NativeVectorAll.rules NativeVectorAll.choices
    126 contextAPWNV source5 = none := by
  have notLambda : ∀ body : Tower.Tm 6, source4 ≠ .lam body := by
    intro body h
    unfold source4 at h
    cases h
  unfold source5
  with_reducible
    exact synth_application_none_of_function NativeVectorAll.rules NativeVectorAll.choices
      125 contextAPWNV source4 (.var 1) notLambda synth4_none

private theorem synth6_none : FormationSensitiveElaboration.synth NativeVectorAll.rules NativeVectorAll.choices
    127 contextAPWNV source6 = none := by
  have notLambda : ∀ body : Tower.Tm 6, source5 ≠ .lam body := by
    intro body h
    unfold source5 at h
    cases h
  unfold source6
  with_reducible
    exact synth_application_none_of_function NativeVectorAll.rules NativeVectorAll.choices
      126 contextAPWNV source5 (.var 0) notLambda synth5_none

private theorem check_application_none {Head : Type} {RootCode : Nat → Type}
    (R : Rules Head) (choices : FormationSensitiveElaboration.Choices Head RootCode) [DecidableEq Head]
    (fuel : Nat) {n : Nat} (context : Ctx Head n) (function argument expected : Tm Head n)
    (prior : FormationSensitiveElaboration.synth R choices fuel context (.app function argument) = none) :
    FormationSensitiveElaboration.check R choices (fuel+1) context (.app function argument) expected = none := by
  cases choices.normalize fuel expected <;> simp [FormationSensitiveElaboration.check,prior]

private theorem check_none : FormationSensitiveElaboration.check NativeVectorAll.rules NativeVectorAll.choices
    128 contextAPWNV
      (allEvidence (.var 4) (.var 3) (.const `Undeclared.Witness) (.var 1) (.var 0)) allTypeControl = none := by
  rw [← source6_eq]
  have prior := synth6_none
  change FormationSensitiveElaboration.synth NativeVectorAll.rules NativeVectorAll.choices
    127 contextAPWNV (.app source5 (.var 0)) = none at prior
  unfold source6
  with_reducible
    exact check_application_none NativeVectorAll.rules NativeVectorAll.choices
      127 contextAPWNV source5 (.var 0) allTypeControl prior

#print axioms check_none

theorem evidence_with_undeclared_witness_not_produced :
    FormationSensitiveElaboration.check NativeVectorAll.rules NativeVectorAll.choices
      128 contextAPWNV
      (allEvidence (.var 4) (.var 3) (.const `Undeclared.Witness) (.var 1) (.var 0)) allTypeControl = none :=
  check_none

private theorem termReplayAccepted_of_none {Head : Type} (R : Rules Head) [DecidableEq Head]
    [DecidableRel R.headTyping] [DecidablePred R.isUniverse]
    [∀ u v w, Decidable (R.join u v w)] [DecidableRel R.cumulative] [DecidableRel R.headEq]
    (decoder : StructuralConversionCode.RootDecoder R.computation)
    (choices : FormationSensitiveElaboration.Choices Head decoder.Code) (fuel : Nat) {n : Nat}
    (context : Ctx Head n) (term type : Tm Head n)
    (produced : FormationSensitiveElaboration.check R choices fuel context term type = none) :
    FormationSensitiveElaboration.termReplayAccepted R decoder choices fuel context term type = false := by
  unfold FormationSensitiveElaboration.termReplayAccepted
  rw [produced]

theorem evidence_with_undeclared_witness_refused :
    FormationSensitiveElaboration.termReplayAccepted NativeVectorAll.rules NativeVectorAll.decoder
      NativeVectorAll.choices 128 contextAPWNV
      (allEvidence (.var 4) (.var 3) (.const `Undeclared.Witness) (.var 1) (.var 0)) allTypeControl = false :=
  termReplayAccepted_of_none NativeVectorAll.rules NativeVectorAll.decoder NativeVectorAll.choices
    128 contextAPWNV
    (allEvidence (.var 4) (.var 3) (.const `Undeclared.Witness) (.var 1) (.var 0)) allTypeControl check_none

#print axioms evidence_with_undeclared_witness_not_produced
#print axioms evidence_with_undeclared_witness_refused
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.ReplayComponents.Undeclared
