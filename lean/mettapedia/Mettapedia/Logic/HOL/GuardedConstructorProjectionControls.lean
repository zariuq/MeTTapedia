import Mettapedia.Logic.HOL.GuardedConstructorProjectionProofs
import Mettapedia.Logic.HOL.ContinuationPayloadBoundaryControls
import Mettapedia.Logic.HOL.HOLLightStandardTheory
import Mettapedia.Logic.HOL.Soundness

/-!
# Guarded field recovery with a lawful adversarial selector

At admitted inputs the constructor pairs a decoded payload bit with its
third Boolean field; an invalid payload reverses that field.
Admission requires a represented payload and relates the first numeric field
to that Boolean. The payload selector prefers an invalid raw continuation
whenever its specification permits one, and otherwise uses ordinary Hilbert
selection. Both choice principles and guarded field injectivity hold.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Mettapedia.Logic.HOL.GuardedConstructorProjections.Controls
open ContinuationPayloadBoundary
open ContinuationPayloadBoundary.Controls (readBoolean invalid)

inductive Base where | number | payload | flag | result
  deriving DecidableEq
abbrev A : Ty Base := .base .number
abbrev B : Ty Base := .base .payload
abbrev C : Ty Base := .base .flag
abbrev R : Ty Base := .base .result
abbrev Raw := Payload Unit Bool Bool

inductive Const : Ty Base → Type where
  | construct : Const (A ⇒ B ⇒ C ⇒ R)
  | domain : Const (Admission A B C)
  | selectPayload : Const (SelectionProofs.Selection B)
  | selectFlag : Const (SelectionProofs.Selection C)
  | number (value : Nat) : Const A
  | payload (value : Raw) : Const B
  | flag (value : Bool) : Const C

def carrier : Base → Type 1
  | .number => ULift.{1} Nat
  | .payload => ULift.{1} Raw
  | .flag => ULift.{1} Bool
  | .result => ULift.{1} (Bool × Bool)
def inhabitant : (type : Base) → carrier type
  | .number => .up 0
  | .payload => .up invalid
  | .flag => .up false
  | .result => .up (false,false)

noncomputable def biasedSelection (predicate : ULift.{1} Raw → ULift.{1} Prop) : ULift.{1} Raw := by
  classical
  exact if (predicate (.up invalid)).down then .up invalid
    else HOLLightStandardTheory.selectionOperation.{0,0} carrier inhabitant B predicate

noncomputable def biasedFlagSelection (predicate : ULift.{1} Bool → ULift.{1} Prop) : ULift.{1} Bool := by
  classical
  exact if (predicate (.up true)).down then .up true
    else HOLLightStandardTheory.selectionOperation.{0,0} carrier inhabitant C predicate

noncomputable def make (_number : ULift.{1} Nat) (payload : ULift.{1} Raw) (flag : ULift.{1} Bool) :
    ULift.{1} (Bool × Bool) := by
  classical
  exact if payload.down = invalid then .up (false,!flag.down) else .up (readBoolean payload.down,flag.down)

theorem represented_ne_invalid (bit : Bool) : singletonPayload (Truth := Bool) () bit ≠ invalid := by
  intro same
  exact ContinuationPayloadBoundary.Controls.invalid_not_represented ⟨bit,same⟩

noncomputable def meaning : {type : Ty Base} → Const type → Ty.denote.{0,0} carrier type
  | _, .construct => make
  | _, .domain => fun number payload flag => .up
      (payload.down ∈ Set.range (singletonPayload (Element := Bool) (Truth := Bool) ()) ∧
        number.down = if flag.down then 1 else 0)
  | _, .selectPayload => biasedSelection
  | _, .selectFlag => biasedFlagSelection
  | _, .number value => .up value
  | _, .payload value => .up value
  | _, .flag value => .up value

noncomputable def model : HenkinModel.{0,0,0} Base Const := .standard carrier meaning
def emptyValues : model.Valuation [] := fun index => nomatch index
def constructor : ClosedTerm Const (A ⇒ B ⇒ C ⇒ R) := .const .construct
def domain : ClosedTerm Const (Admission A B C) := .const .domain
def selectPayload : ClosedTerm Const (SelectionProofs.Selection B) := .const .selectPayload
def selectFlag : ClosedTerm Const (SelectionProofs.Selection C) := .const .selectFlag
def first (flag : Bool) : ClosedTerm Const A := .const (.number (if flag then 1 else 0))
def second (bit : Bool) : ClosedTerm Const B := .const (.payload (singletonPayload () bit))
def third (flag : Bool) : ClosedTerm Const C := .const (.flag flag)
def value (bit flag : Bool) := ConstructorProjections.apply constructor (first flag) (second bit) (third flag)

theorem payload_choice_holds : model.models (SelectionProofs.principle selectPayload) := by
  classical
  intro predicate _ witness _ present
  change (predicate (biasedSelection predicate)).down
  unfold biasedSelection
  split
  · assumption
  · exact HOLLightStandardTheory.selectionOperation_specified.{0,0} carrier inhabitant B predicate ⟨witness,present⟩

theorem flag_choice_holds : model.models (SelectionProofs.principle selectFlag) := by
  classical
  intro predicate _ witness _ present
  change (predicate (biasedFlagSelection predicate)).down
  unfold biasedFlagSelection
  split
  · assumption
  · exact HOLLightStandardTheory.selectionOperation_specified.{0,0} carrier inhabitant C predicate ⟨witness,present⟩

theorem guarded_injectivity_holds : model.models (fieldInjective constructor domain) := by
  classical
  intro number _ payload _ flag _ original number' _ payload' _ flag' _ candidate same
  change make number' payload' flag' = make number payload flag at same
  change payload.down ∈ Set.range (singletonPayload (Element := Bool) (Truth := Bool) ()) ∧ _ at original
  change payload'.down ∈ Set.range (singletonPayload (Element := Bool) (Truth := Bool) ()) ∧ _ at candidate
  have originalValid : payload.down ≠ invalid := by
    intro equal
    exact ContinuationPayloadBoundary.Controls.invalid_not_represented (equal ▸ original.1)
  have candidateValid : payload'.down ≠ invalid := by
    intro equal
    exact ContinuationPayloadBoundary.Controls.invalid_not_represented (equal ▸ candidate.1)
  have pairSame : (readBoolean payload'.down,flag'.down) = (readBoolean payload.down,flag.down) := by
    simpa only [make,if_neg originalValid,if_neg candidateValid] using congrArg ULift.down same
  have payloadSame := ContinuationPayloadBoundary.Controls.represented_reader_injective candidate.1 original.1
    (congrArg Prod.fst pairSame)
  exact ⟨ULift.ext _ _ payloadSame,ULift.ext _ _ (congrArg Prod.snd pairSame)⟩

theorem source_admitted (bit flag : Bool) : model.models (admitted domain (first flag) (second bit) (third flag)) := by
  exact ⟨⟨bit,rfl⟩,rfl⟩

theorem source_output (bit flag : Bool) : model.denote (value bit flag) emptyValues = ULift.up (bit,flag) := by
  classical
  change make (.up (if flag then 1 else 0)) (.up (singletonPayload () bit)) (.up flag) = .up (bit,flag)
  simp [make,represented_ne_invalid,readBoolean,singletonPayload]

theorem all_four_outputs_distinguished (firstBit firstFlag secondBit secondFlag : Bool) :
    model.denote (value firstBit firstFlag) emptyValues = model.denote (value secondBit secondFlag) emptyValues ↔
      firstBit = secondBit ∧ firstFlag = secondFlag := by
  rw [source_output,source_output]
  change (ULift.up (firstBit,firstFlag) : ULift.{1} (Bool × Bool)) =
    ULift.up (secondBit,secondFlag) ↔ _
  simp only [ULift.up.injEq,Prod.mk.injEq]

def assumptions (bit flag : Bool) : List (ClosedFormula Const) :=
  [SelectionProofs.principle selectPayload,SelectionProofs.principle selectFlag,fieldInjective constructor domain,
    admitted domain (first flag) (second bit) (third flag)]

theorem assumptions_realizable (bit flag : Bool) : Soundness.SatisfiesHyps model emptyValues (assumptions bit flag) := by
  intro formula present
  simp only [assumptions,List.mem_cons,List.not_mem_nil,or_false] at present
  rcases present with rfl | rfl | rfl | rfl
  · exact payload_choice_holds
  · exact flag_choice_holds
  · exact guarded_injectivity_holds
  · exact source_admitted bit flag

def payloadRecovered (bit flag : Bool) : ProofSyntax Const (assumptions bit flag)
    (.eq (.app (secondProjection selectPayload constructor domain) (value bit flag)) (second bit)) :=
  second_at selectPayload constructor domain (first flag) (second bit) (third flag)
    (.hyp (Δ := assumptions bit flag) ⟨0,by change 0 < 4; decide⟩)
    (.hyp (Δ := assumptions bit flag) ⟨2,by change 2 < 4; decide⟩)
    (.hyp (Δ := assumptions bit flag) ⟨3,by change 3 < 4; decide⟩)
def flagRecovered (bit flag : Bool) : ProofSyntax Const (assumptions bit flag)
    (.eq (.app (thirdProjection selectFlag constructor domain) (value bit flag)) (third flag)) :=
  third_at selectFlag constructor domain (first flag) (second bit) (third flag)
    (.hyp (Δ := assumptions bit flag) ⟨1,by change 1 < 4; decide⟩)
    (.hyp (Δ := assumptions bit flag) ⟨2,by change 2 < 4; decide⟩)
    (.hyp (Δ := assumptions bit flag) ⟨3,by change 3 < 4; decide⟩)

theorem sound {formula : ClosedFormula Const} {bit flag : Bool}
    (proof : ProofSyntax Const (assumptions bit flag) formula) : (model.denote formula emptyValues).down :=
  Soundness.extDerivation_sound proof.erase (model.functionsRespectEqv_of_fullDomains (HenkinModel.fullDomains_standard _ _))
    (fun _ => trivial) (assumptions_realizable bit flag)

theorem both_fields_recovered (bit flag : Bool) :
    (model.denote (.eq (.app (secondProjection selectPayload constructor domain) (value bit flag)) (second bit)) emptyValues).down ∧
    (model.denote (.eq (.app (thirdProjection selectFlag constructor domain) (value bit flag)) (third flag)) emptyValues).down :=
  ⟨sound (payloadRecovered bit flag),sound (flagRecovered bit flag)⟩

def invalidTerm : ClosedTerm Const B := .const (.payload invalid)
def unguardedBody := ConstructorProjections.secondBody constructor (value false false)

theorem unguarded_invalid_witness :
    (model.denote (instantiate invalidTerm unguardedBody) emptyValues).down := by
  refine ⟨ULift.up 0,trivial,ULift.up true,trivial,?_⟩
  change make (.up 0) (.up invalid) (.up true) = make (.up 0) (.up (singletonPayload () false)) (.up false)
  simp [make,represented_ne_invalid,readBoolean,singletonPayload]

theorem guarded_invalid_witness_refused :
    ¬ (model.denote (instantiate invalidTerm (secondBody constructor domain (value false false))) emptyValues).down := by
  rintro ⟨_,_,_,_,accepted,_⟩
  exact ContinuationPayloadBoundary.Controls.invalid_not_represented accepted.1

theorem unguarded_projection_chooses_invalid :
    model.denote (.app (ConstructorProjections.secondProjection selectPayload constructor) (value false false)) emptyValues =
      ULift.up invalid := by
  classical
  change biasedSelection _ = ULift.up invalid
  unfold biasedSelection
  apply if_pos
  refine ⟨ULift.up 0,trivial,ULift.up true,trivial,?_⟩
  change make (.up 0) (.up invalid) (.up true) = make (.up 0) (.up (singletonPayload () false)) (.up false)
  simp [make,represented_ne_invalid,readBoolean,singletonPayload]

theorem unguarded_flag_projection_chooses_true :
    model.denote (.app (ConstructorProjections.thirdProjection selectFlag constructor) (value false false)) emptyValues =
      ULift.up true := by
  classical
  change biasedFlagSelection _ = ULift.up true
  unfold biasedFlagSelection
  apply if_pos
  refine ⟨ULift.up 0,trivial,ULift.up invalid,trivial,?_⟩
  change make (.up 0) (.up invalid) (.up true) = make (.up 0) (.up (singletonPayload () false)) (.up false)
  simp [make,represented_ne_invalid,readBoolean,singletonPayload]

theorem unguarded_projection_wrong :
    ¬ (model.denote (.eq (.app (ConstructorProjections.secondProjection selectPayload constructor) (value false false))
      (second false)) emptyValues).down := by
  intro claimed
  change model.denote (.app (ConstructorProjections.secondProjection selectPayload constructor) (value false false)) emptyValues =
    ULift.up (singletonPayload () false) at claimed
  rw [unguarded_projection_chooses_invalid] at claimed
  exact ContinuationPayloadBoundary.Controls.raw_collision_distinct (congrArg ULift.down claimed)

theorem dropped_witness_guard_has_no_proof : ¬ Nonempty (ProofSyntax Const (assumptions false false)
    (.eq (.app (ConstructorProjections.secondProjection selectPayload constructor) (value false false)) (second false))) := by
  rintro ⟨claimed⟩
  exact unguarded_projection_wrong (sound claimed)

theorem dropped_flag_witness_guard_has_no_proof : ¬ Nonempty (ProofSyntax Const (assumptions false false)
    (.eq (.app (ConstructorProjections.thirdProjection selectFlag constructor) (value false false)) (third false))) := by
  rintro ⟨claimed⟩
  have holds := sound claimed
  change model.denote (.app (ConstructorProjections.thirdProjection selectFlag constructor) (value false false)) emptyValues =
    ULift.up false at holds
  rw [unguarded_flag_projection_chooses_true] at holds
  exact Bool.noConfusion (congrArg ULift.down holds)

theorem unguarded_injectivity_invalid : ¬ model.models (ConstructorProjections.fieldInjective constructor) := by
  intro rawInjectivity
  let premises : List (ClosedFormula Const) :=
    [SelectionProofs.principle selectPayload,ConstructorProjections.fieldInjective constructor]
  have computation : ProofSyntax Const premises (.eq
      (.app (ConstructorProjections.secondProjection selectPayload constructor) (value false false)) (second false)) :=
    ConstructorProjections.second_at selectPayload constructor (first false) (second false) (third false) (.hyp 0) (.hyp 1)
  apply unguarded_projection_wrong
  apply Soundness.extDerivation_sound computation.erase
    (model.functionsRespectEqv_of_fullDomains (HenkinModel.fullDomains_standard _ _)) (fun _ => trivial)
  intro formula present
  simp only [premises,List.mem_cons,List.not_mem_nil,or_false] at present
  rcases present with rfl | rfl
  · exact payload_choice_holds
  · exact rawInjectivity

theorem guarded_profile_is_strict : model.models (fieldInjective constructor domain) ∧
    ¬ model.models (ConstructorProjections.fieldInjective constructor) :=
  ⟨guarded_injectivity_holds,unguarded_injectivity_invalid⟩

#print axioms both_fields_recovered
#print axioms dropped_witness_guard_has_no_proof
end Mettapedia.Logic.HOL.GuardedConstructorProjections.Controls
