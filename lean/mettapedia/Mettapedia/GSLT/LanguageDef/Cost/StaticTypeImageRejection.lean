import Mettapedia.GSLT.LanguageDef.Cost.StaticTypeImage

/-! Reserved apparatus and wrapped sorts are outside the uniform base fibre. -/

namespace Mettapedia.GSLT.LanguageDef.CostStaticTypeImage

@[simp] theorem decodeBaseSort_wrapped :
    decodeBaseSort costWrappedSortName = none := by
  cases decoded : decodeBaseSort costWrappedSortName with
  | none => rfl
  | some sourceName =>
    have encoded : costWrappedSortName = costBaseSortTag ++ sourceName :=
      (decodeTaggedPayload_eq_some_iff costBaseSortTag costWrappedSortName sourceName).mp decoded
    exact False.elim (costBaseSortName_ne_wrapped sourceName encoded.symm)

@[simp] theorem decodeBaseSort_apparatus (kind : String) :
    decodeBaseSort (costApparatusSortName kind) = none := by
  cases decoded : decodeBaseSort (costApparatusSortName kind) with
  | none => rfl
  | some sourceName =>
    have encoded : costApparatusSortName kind = costBaseSortTag ++ sourceName :=
      (decodeTaggedPayload_eq_some_iff costBaseSortTag (costApparatusSortName kind) sourceName).mp decoded
    exact False.elim (costBaseSortName_ne_apparatus sourceName kind encoded.symm)

end Mettapedia.GSLT.LanguageDef.CostStaticTypeImage
