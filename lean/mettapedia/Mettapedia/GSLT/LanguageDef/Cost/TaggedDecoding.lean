import Mettapedia.GSLT.LanguageDef.CostFunctor

/-! Exact reserved-prefix decoding shared by static Cost fibres. -/

namespace Mettapedia.GSLT.LanguageDef

/-- Remove one exact reserved string prefix. -/
def decodeTaggedPayload (tag name : String) : Option String :=
  (dropListPrefix? tag.toList name.toList).map String.ofList

@[simp]
theorem decodeTaggedPayload_append (tag payload : String) :
    decodeTaggedPayload tag (tag ++ payload) = some payload := by
  simp [decodeTaggedPayload, String.toList_append]

/-- Successful prefix decoding reconstructs the original string exactly. -/
theorem decodeTaggedPayload_eq_some_iff (tag name payload : String) :
    decodeTaggedPayload tag name = some payload ↔
      name = tag ++ payload := by
  constructor
  · intro decoded
    unfold decodeTaggedPayload at decoded
    cases decodedPrefix : dropListPrefix? tag.toList name.toList with
    | none => simp [decodedPrefix] at decoded
    | some suffix =>
        simp only [decodedPrefix, Option.map_some, Option.some.injEq] at decoded
        have reconstructed : tag ++ String.ofList suffix = name := by
          apply String.toList_inj.mp
          simpa [String.toList_append] using
            append_eq_of_dropListPrefix?_eq_some decodedPrefix
        simpa [decoded] using reconstructed.symm
  · rintro rfl
    exact decodeTaggedPayload_append _ _

end Mettapedia.GSLT.LanguageDef
