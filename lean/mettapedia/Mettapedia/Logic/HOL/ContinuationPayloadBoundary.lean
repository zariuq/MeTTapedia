import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.Set.Image

/-!
# Full continuation payloads and their represented values

A full continuation space that accepts predicates over a carrier contains an
injective image of that carrier's powerset. It therefore cannot itself embed
into the carrier. In particular, a constructor returning the same carrier
cannot be injective in every raw continuation payload at fixed other inputs.

Represented singleton payloads have a different boundary: their image is
equivalent to the original carrier. This distinguishes full function-space
injectivity from injectivity restricted to an admitted payload image. The
result is about full function spaces, not arbitrary Henkin domains, and does
not construct a recursive datatype or its constructor interpretation.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.ContinuationPayloadBoundary
universe u v w
variable {Number : Type u} {Element : Type v} {Truth : Type w}

abbrev Payload (Number : Type u) (Element : Type v) (Truth : Type w) :=
  (Number → Element → Number → Truth) → Truth

noncomputable def subsetPayload (zero : Number) (yes no : Truth) (subset : Set Element) :
    Payload Number Element Truth := by
  classical
  exact fun test => if ∃ point, point ∈ subset ∧ test zero point zero = yes then yes else no

noncomputable def probe (yes no : Truth) (point : Element) : Number → Element → Number → Truth := by
  classical
  exact fun _ candidate _ => if candidate = point then yes else no

theorem subsetPayload_probe (zero : Number) (yes no : Truth) (different : yes ≠ no)
    (subset : Set Element) (point : Element) :
    subsetPayload zero yes no subset (probe yes no point) = yes ↔ point ∈ subset := by
  classical
  have witness : (∃ candidate, candidate ∈ subset ∧ probe (Number := Number) yes no point zero candidate zero = yes) ↔
      point ∈ subset := by
    constructor
    · rintro ⟨candidate,member,selected⟩
      by_cases same : candidate = point
      · simpa only [same] using member
      · simp [probe,same,Ne.symm different] at selected
    · intro member
      exact ⟨point,member,by simp [probe]⟩
  by_cases member : point ∈ subset
  · simp [subsetPayload,witness.mpr member,member]
  · have absent := mt witness.mp member
    simp [subsetPayload,absent,member,Ne.symm different]

theorem subsetPayload_injective (zero : Number) (yes no : Truth) (different : yes ≠ no) :
    Function.Injective (subsetPayload (Element := Element) zero yes no) := by
  intro first second same
  apply Set.ext
  intro point
  rw [← subsetPayload_probe zero yes no different first point,
    ← subsetPayload_probe zero yes no different second point,same]

theorem no_full_payload_embedding (zero : Number) (yes no : Truth) (different : yes ≠ no)
    (encode : Payload Number Element Truth → Element) : ¬ Function.Injective encode := by
  intro injective
  exact Function.cantor_injective (encode ∘ subsetPayload zero yes no)
    (injective.comp (subsetPayload_injective zero yes no different))

theorem no_same_carrier_payload_injectivity (zero : Number) (bottom : Element)
    (yes no : Truth) (different : yes ≠ no)
    (construct : Number → Payload Number Element Truth → (Number → Element) → Element) :
    ¬ Function.Injective (fun payload => construct zero payload (fun _ => bottom)) :=
  no_full_payload_embedding zero yes no different _

def singletonPayload (zero : Number) (point : Element) : Payload Number Element Truth :=
  fun test => test zero point zero

theorem singletonPayload_injective (zero : Number) (yes no : Truth) (different : yes ≠ no) :
    Function.Injective (singletonPayload (Truth := Truth) (Element := Element) zero) := by
  classical
  intro first second same
  by_contra unequal
  have selected := congrFun same (probe yes no first)
  have impossible : yes = no := by
    simpa [singletonPayload,probe,Ne.symm unequal] using selected
  exact different impossible

noncomputable def representedPayloadEquiv (zero : Number) (yes no : Truth) (different : yes ≠ no) :
    Element ≃ Set.range (singletonPayload (Element := Element) (Truth := Truth) zero) where
  toFun point := ⟨singletonPayload zero point,point,rfl⟩
  invFun payload := Classical.choose payload.property
  left_inv point := singletonPayload_injective zero yes no different (Classical.choose_spec (show
    singletonPayload (Truth := Truth) zero point ∈ Set.range (singletonPayload zero) from ⟨point,rfl⟩))
  right_inv payload := Subtype.ext (Classical.choose_spec payload.property)

theorem raw_boolean_payload_refuses (encode : Payload Unit Bool Bool → Bool) : ¬ Function.Injective encode :=
  no_full_payload_embedding () true false (by decide) encode

theorem represented_boolean_values_separate :
    singletonPayload (Truth := Bool) () false ≠ singletonPayload () true := by
  intro same
  exact Bool.false_ne_true (singletonPayload_injective () true false (by decide) same)

#print axioms no_same_carrier_payload_injectivity
#print axioms representedPayloadEquiv
#print axioms raw_boolean_payload_refuses
end Mettapedia.Logic.HOL.ContinuationPayloadBoundary
