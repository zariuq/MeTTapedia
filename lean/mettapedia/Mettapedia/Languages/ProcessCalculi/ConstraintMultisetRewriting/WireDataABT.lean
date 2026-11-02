import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceSchemaActivation
import Mettapedia.OSLF.Syntax.BindingWireData

/-! # Injective common-ABT storage of existing finite wire data -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.WireDataABT

open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open InferenceSchemaActivation (Tm action)

def natural : Nat → Tm
  | 0 => .node (.inr "wire.zero") .nil
  | n + 1 => .node (.inr "wire.succ") (.cons 0 (natural n) .nil)

def encode : Data → Tm
  | .atom n => .node (.inr "wire.atom") (.cons 0 (natural n) .nil)
  | .pair first second => .node (.inr "wire.pair") (.cons 0 (encode first) (.cons 0 (encode second) .nil))

theorem natural_injective : Function.Injective natural := by
  intro first
  induction first with
  | zero => intro second same; cases second <;> simp_all [natural]
  | succ first ih =>
      intro second same
      cases second with
      | zero => simp [natural] at same
      | succ second =>
          have equal : natural first = natural second := by simpa [natural] using same
          exact congrArg Nat.succ (ih equal)

theorem encode_injective : Function.Injective encode := by
  intro first
  induction first with
  | atom n =>
      intro second same
      cases second with
      | atom m =>
          exact congrArg Data.atom (natural_injective (by simpa [encode] using same))
      | pair first second => simp [encode] at same
  | pair first second firstIH secondIH =>
      intro other same
      cases other with
      | atom n => simp [encode] at same
      | pair otherFirst otherSecond =>
          have both : encode first = encode otherFirst ∧ encode second = encode otherSecond := by
            simpa [encode] using same
          rw [firstIH both.1, secondIH both.2]

theorem natural_supported (n : Nat) : Term.supportedAt 0 (natural n) = true := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [natural, Term.supportedAt, Term.Fields.supportedAt] using ih

theorem encode_supported (value : Data) : Term.supportedAt 0 (encode value) = true := by
  induction value with
  | atom n => simpa [encode, Term.supportedAt, Term.Fields.supportedAt] using natural_supported n
  | pair first second firstIH secondIH =>
      simp [encode, Term.supportedAt, Term.Fields.supportedAt, firstIH, secondIH]

theorem encode_fixed (value : Data) (assignment : ABTProtectedParameters.Assignment InferenceSchemaActivation.Head 0) :
    action.apply assignment (encode value) = encode value :=
  ABTProtectedParameters.supported_term_fixed 0 assignment _ (encode_supported value)

theorem codec_injective {α : Type} (codec : Codec α) : Function.Injective (fun value => encode (codec.put value)) :=
  encode_injective.comp codec.put_injective

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.WireDataABT
