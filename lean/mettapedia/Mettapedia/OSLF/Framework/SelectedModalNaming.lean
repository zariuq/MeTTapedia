import Mettapedia.OSLF.Framework.DisplayedOccurrenceLanguage
import Mettapedia.OSLF.Framework.CarrierUniverseSignature

/-!
# Stable names for selected contextual modalities

Generated modal constructors are indexed by authored occurrence slots.  This
module owns only the reversible private namespace and the slot-to-occurrence
lookup; it is shared by the unary calibration skeleton and the contextual
native-type generator.
-/

namespace Mettapedia.OSLF.Framework

namespace SelectedModalNaming

/-- Stable internal name of the modal constructor at one occurrence slot. -/
def label (slot : Nat) : String :=
  String.ofList ('$' :: 'm' :: ':' :: List.replicate slot 's')

theorem label_injective : Function.Injective label := by
  intro first second equality
  have lengths := congrArg String.length equality
  simp [label] at lengths
  omega

/-- Occurrence-modal names and carrier-universe names occupy disjoint private
namespaces.  This is the reusable collision theorem needed when the two
generated families are composed into one flat language. -/
theorem label_ne_carrierUniverseLabel (slot : Nat)
    (code : CarrierUniverseSignature.Code) (carrier : String) :
    label slot ≠ CarrierUniverseSignature.label code carrier := by
  intro equality
  have lists := congrArg String.toList equality
  cases code <;>
    simp [label, CarrierUniverseSignature.label,
      CarrierUniverseSignature.Code.tag] at lists

/-- Decode exactly the private modal namespace. -/
def slot? (constructorName : String) : Option Nat :=
  match constructorName.toList with
  | '$' :: 'm' :: ':' :: suffix =>
      if suffix = List.replicate suffix.length 's'
      then some suffix.length
      else none
  | _ => none

@[simp]
theorem slot?_label (slot : Nat) : slot? (label slot) = some slot := by
  simp [slot?, label]

/-- Successful decoding is a left inverse, so a foreign constructor cannot
be identified with a selected modal slot. -/
theorem label_of_slot?_eq_some {constructorName : String} {slot : Nat}
    (decoded : slot? constructorName = some slot) :
    label slot = constructorName := by
  unfold slot? at decoded
  split at decoded
  next suffix equation =>
    split at decoded
    next canonical =>
      cases decoded
      rw [← (String.ofList_toList (s := constructorName)), equation]
      unfold label
      rw [canonical]
      simp only [List.length_replicate]
    next notCanonical => simp at decoded
  all_goals simp at decoded

/-- A valid generated slot points back to exactly one requested source
occurrence. -/
def site (request : DisplayedOccurrenceLanguage)
    (slot : Fin request.selectedSites.length) :
    DisplayedRewriteSite request.definition.language :=
  request.selectedSites[slot]

#print axioms label_injective
#print axioms label_ne_carrierUniverseLabel
#print axioms label_of_slot?_eq_some
#print axioms site

end SelectedModalNaming

end Mettapedia.OSLF.Framework
