import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveElaborationComponents
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveElaborationProjection

/-!
# Exact produced-code checkpoints

A proved success observation retains the original producer's own code through
`Option.get`. Its source equation identifies that exact code; no alternative
typing witness is substituted. The term acceptance equation still requires
the existing independent replay. Success of production alone does not assert
typing or publication.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.FormationSensitiveElaboration

variable {Head : Type} {RootCode : Nat → Type} (R : Rules Head) [DecidableEq Head]

def producedInference (choices : Choices Head RootCode) {n : Nat} (fuel : Nat)
    (ambient : Ctx Head n) (term : Tm Head n)
    (produced : (synth R choices fuel ambient term).isSome = true) :
    Inferred Head RootCode n :=
  (synth R choices fuel ambient term).get produced

theorem producedInference_origin (choices : Choices Head RootCode) {n : Nat} (fuel : Nat)
    (ambient : Ctx Head n) (term : Tm Head n)
    (produced : (synth R choices fuel ambient term).isSome = true) :
    synth R choices fuel ambient term =
      some (producedInference R choices fuel ambient term produced) :=
  Option.eq_some_of_isSome produced

theorem synth_present_of_typeProjection (choices : Choices Head RootCode) {n : Nat} (fuel : Nat)
    (ambient : Ctx Head n) (term type : Tm Head n)
    (projected : typeProjection R choices fuel ambient term = some type) :
    (synth R choices fuel ambient term).isSome = true := by
  have present := congrArg Option.isSome ((synth_type R choices fuel ambient term).trans projected)
  simpa only [Option.isSome_map, Option.isSome_some] using present

theorem producedInference_type (choices : Choices Head RootCode) {n : Nat} (fuel : Nat)
    (ambient : Ctx Head n) (term type : Tm Head n)
    (produced : (synth R choices fuel ambient term).isSome = true)
    (projected : typeProjection R choices fuel ambient term = some type) :
    (producedInference R choices fuel ambient term produced).type = type := by
  have observed := (synth_type R choices fuel ambient term).trans projected
  rw [producedInference_origin R choices fuel ambient term produced] at observed
  exact Option.some.inj observed

def producedTermCode (choices : Choices Head RootCode) {n : Nat} (fuel : Nat)
    (ambient : Ctx Head n) (term type : Tm Head n)
    (produced : (check R choices fuel ambient term type).isSome = true) :
    Code Head RootCode n :=
  (check R choices fuel ambient term type).get produced

theorem producedTermCode_origin (choices : Choices Head RootCode) {n : Nat} (fuel : Nat)
    (ambient : Ctx Head n) (term type : Tm Head n)
    (produced : (check R choices fuel ambient term type).isSome = true) :
    check R choices fuel ambient term type =
      some (producedTermCode R choices fuel ambient term type produced) :=
  Option.eq_some_of_isSome produced

theorem zero_fuel_not_produced (choices : Choices Head RootCode) {n : Nat}
    (ambient : Ctx Head n) (term type : Tm Head n) :
    (check R choices 0 ambient term type).isSome = false := rfl

variable [DecidableRel R.headTyping] [DecidablePred R.isUniverse]
    [∀ u v w, Decidable (R.join u v w)] [DecidableRel R.cumulative]
    [DecidableRel R.headEq]

theorem termReplayAccepted_eq_produced_code
    (decoder : StructuralConversionCode.RootDecoder R.computation)
    (choices : Choices Head decoder.Code) {n : Nat} (fuel : Nat)
    (ambient : Ctx Head n) (term type : Tm Head n)
    (produced : (check R choices fuel ambient term type).isSome = true) :
    termReplayAccepted R decoder choices fuel ambient term type =
      StructuralTypingReplay.check R
        (fun code left right => code.check R.headEq decoder.decode left right)
        ambient term type (producedTermCode R choices fuel ambient term type produced) := by
  unfold termReplayAccepted
  rw [producedTermCode_origin R choices fuel ambient term type produced]

#print axioms producedTermCode_origin
#print axioms termReplayAccepted_eq_produced_code
#print axioms producedInference_origin
#print axioms producedInference_type
#print axioms synth_present_of_typeProjection
#print axioms zero_fuel_not_produced

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.FormationSensitiveElaboration
