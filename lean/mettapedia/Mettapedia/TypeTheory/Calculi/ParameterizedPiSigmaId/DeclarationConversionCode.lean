import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.DeclarationSignature
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralConversionCode

/-!
# Conversion evidence for declaration extensions

An extension reuses the base and declared-root decoders. Its delta code keeps
only the selected name: the body is read from the actual signature, so a stale
or forged body cannot be supplied as evidence. The existing structural checker
then handles arbitrary open conversion, including unfolding below binders.

Decoder exactness is independent of typing, dependency ordering and termination.
Those are separate obligations for admitting and executing a library.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace DeclarationConversionCode

open Declaration StructuralConversionCode

variable {Head : Type} {n : Nat} {BaseCode DeclaredCode : Nat → Type}

inductive RootCode (BaseCode DeclaredCode : Nat → Type) (n : Nat) where
  | inherited (code : BaseCode n)
  | delta (name : DeclName)
  | declared (code : DeclaredCode n)

def decode (signature : Signature Head)
    (baseDecode : {n : Nat} → BaseCode n → Option (Tm Head n × Tm Head n))
    (declaredDecode : {n : Nat} → DeclaredCode n → Option (Tm Head n × Tm Head n)) :
    RootCode BaseCode DeclaredCode n → Option (Tm Head n × Tm Head n)
  | .inherited code => baseDecode code
  | .delta name => (signature.valueOf? name).map fun value => (.const name, liftClosed value)
  | .declared code => declaredDecode code

variable {base : Rules Head} {signature : Signature Head}
    (baseDecoder : RootDecoder base.computation)
    (declaredDecoder : RootDecoder signature.computation)

theorem decode_sound (code : RootCode baseDecoder.Code declaredDecoder.Code n)
    {left right : Tm Head n}
    (decoded : decode signature baseDecoder.decode declaredDecoder.decode code = some (left, right)) :
    (extendRules base signature).computation.step left right := by
  cases code with
  | inherited code => exact .inherited (baseDecoder.sound code decoded)
  | declared code => exact .declared (declaredDecoder.sound code decoded)
  | delta name =>
      cases lookup : signature.valueOf? name with
      | none => simp [decode, lookup] at decoded
      | some body =>
          simp only [decode, lookup, Option.map_some, Option.some.injEq, Prod.mk.injEq] at decoded
          obtain ⟨rfl, rfl⟩ := decoded
          exact .delta lookup

theorem decode_complete {left right : Tm Head n}
    (root : (extendRules base signature).computation.step left right) :
    ∃ code : RootCode baseDecoder.Code declaredDecoder.Code n,
      decode signature baseDecoder.decode declaredDecoder.decode code = some (left, right) := by
  cases root with
  | inherited root =>
      obtain ⟨code, decoded⟩ := baseDecoder.complete root
      exact ⟨.inherited code, decoded⟩
  | declared root =>
      obtain ⟨code, decoded⟩ := declaredDecoder.complete root
      exact ⟨.declared code, decoded⟩
  | @delta name body lookup =>
      exact ⟨.delta name, by simp [decode, lookup]⟩

def rootDecoder : RootDecoder (extendRules base signature).computation where
  Code := RootCode baseDecoder.Code declaredDecoder.Code
  decode := decode signature baseDecoder.decode declaredDecoder.decode
  sound := decode_sound baseDecoder declaredDecoder
  complete := decode_complete baseDecoder declaredDecoder

/-- A finite constant inventory has no extra authored root equations. Its
decoder still includes every inherited root and every selected definition. -/
def ofList (base : Rules Head) (baseDecoder : RootDecoder base.computation)
    (entries : List (DeclName × Entry Head)) :
    RootDecoder (extendRules base (Signature.ofList entries)).computation :=
  rootDecoder baseDecoder
    (RootDecoder.ofEmpty _ (Signature.computation_ofList entries))

#print axioms decode_sound
#print axioms decode_complete
#print axioms rootDecoder
#print axioms ofList

end DeclarationConversionCode
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
