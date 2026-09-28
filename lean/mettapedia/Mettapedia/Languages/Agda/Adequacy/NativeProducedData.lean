import Mettapedia.Languages.Agda.Adequacy.NativeProductionSoundness
import Mettapedia.Languages.Agda.Native.ProofCodec
import Mettapedia.OSLF.Syntax.FiniteRuleProofData

/-! Exact replay and independent source soundness of produced binary proof data.
This mathematical interface starts at wire data and excludes JSON transport. -/

set_option autoImplicit false
namespace Mettapedia.Languages.Agda.Native.Production.Wire

open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.Languages.Agda
open Structural.Statics

abbrev NativeTree := Structural.AdministrativeStatics.Derivation

def encodeData {j : Structural.AdministrativeStatics.Judgment} (tree : NativeTree j) : Data :=
  Mettapedia.OSLF.Binding.FiniteRuleLabelledProofWire.dataWireCodec.put (Mettapedia.Languages.Agda.Native.Codec.encode tree)

def replay (j : Structural.AdministrativeStatics.Judgment) (data : Data) : Option (NativeTree j) := do
  let wire ← Mettapedia.OSLF.Binding.FiniteRuleLabelledProofWire.dataWireCodec.get data
  Mettapedia.Languages.Agda.Native.Codec.decodeAt j wire

theorem replay_encode {j : Structural.AdministrativeStatics.Judgment} (tree : NativeTree j) :
    replay j (encodeData tree) = some tree := by
  simp only [replay, encodeData, Codec.get_put, bind, Option.bind_some]
  exact Mettapedia.Languages.Agda.Native.Codec.decodeAt_encode tree

/-- Successful replay preserves the submitted binary data exactly, as well as
the complete native tree. The concrete Data-label codec has no aliases. -/
theorem replay_exact {j : Structural.AdministrativeStatics.Judgment} {data : Data}
    {tree : NativeTree j} (accepted : replay j data = some tree) : encodeData tree = data := by
  cases decoded : Mettapedia.OSLF.Binding.FiniteRuleLabelledProofWire.dataWireCodec.get data with
  | none => simp only [replay, decoded] at accepted; cases accepted
  | some wire =>
      have checked : Mettapedia.Languages.Agda.Native.Codec.decodeAt j wire = some tree := by
        simpa only [replay, decoded, bind, Option.bind_some] using accepted
      rw [encodeData, Mettapedia.Languages.Agda.Native.Codec.decodeAt_exact checked]
      exact Mettapedia.OSLF.Binding.FiniteRuleLabelledProofWire.put_of_dataWire_get decoded

theorem replay_iff {j : Structural.AdministrativeStatics.Judgment} {data : Data}
    {tree : NativeTree j} : replay j data = some tree ↔ encodeData tree = data := by
  constructor
  · exact replay_exact
  · intro encoded
    rw [← encoded]
    exact replay_encode tree

def produce (fuel : Nat) (j : Structural.AdministrativeStatics.Judgment) : Option Data :=
  match run fuel j with
  | .established tree => some (encodeData tree)
  | _ => none

/-- Replay reconstructs the exact history chosen by the producer at this
budget. No claim equates histories selected at different budgets. -/
theorem produced_replays (fuel : Nat) (j : Structural.AdministrativeStatics.Judgment) (data : Data)
    (produced : produce fuel j = some data) :
    ∃ tree : NativeTree j, run fuel j = .established tree ∧ replay j data = some tree := by
  cases result : run fuel j with
  | established tree =>
      simp only [produce, result, Option.some.injEq] at produced
      subst data
      exact ⟨tree, rfl, replay_encode tree⟩
  | refuted impossible => simp only [produce, result] at produced; cases produced
  | incomplete => simp only [produce, result] at produced; cases produced

/-- All accepted proof data, regardless of its producer, carries an
independently specified source typing derivation of the observed raw input. -/
theorem replay_typing_sound {n : Nat} (Γ : RawContext n) (t : RawTm n) (A : RawTy n)
    (data : Data) (accepted : (replay (.core (typed Γ t A)) data).isSome = true) :
    Nonempty (StaticAdequacy.Reflection.ReflectedTyping Γ t A) := by
  rcases Option.isSome_iff_exists.mp accepted with ⟨tree, _⟩
  exact ⟨StaticAdequacy.AdministrativeReflection.reflectTyping tree⟩

#print axioms produced_replays
#print axioms replay_typing_sound

end Mettapedia.Languages.Agda.Native.Production.Wire
