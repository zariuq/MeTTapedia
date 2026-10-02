import Mettapedia.GSLT.LanguageDef.NativeOpsCHeader

/-!
# Compositional native declaration checks

Individual declaration certificates compose into the same complete header
condition. No declaration, include, alias or ordering check is omitted.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps.NativeC

theorem option_mapM_cons_certified {α β : Type} (f : α → Option β)
    (first : α) (rest : List α) (head : β) (tail : List β)
    (headChecked : f first = some head) (tailChecked : rest.mapM f = some tail) :
    (first :: rest).mapM f = some (head :: tail) := by
  simp only [List.mapM_cons, headChecked, tailChecked]
  rfl

theorem declared_layouts_of_parts (representation : Representation)
    (arrays records externals functions : List HeaderItem)
    (arrayChecked : representation.arrayAliases.mapM (fun (element, name) => do
      let type ← sourceType? representation element
      some (HeaderItem.array name [⟨{type with pointers := type.pointers + 1}, "data".toList⟩,
        ⟨⟨"uint64_t".toList, 0⟩, "length".toList⟩])) = some arrays)
    (recordChecked : representation.interface.records.mapM (fun record => do
      let fields ← sourceFields? representation record.fields
      some (HeaderItem.record (recordName representation.moduleName record.name) fields)) = some records)
    (externalChecked : representation.interface.externals.mapM (fun declaration =>
      sourcePrototype? representation declaration.header declaration.cSymbol.toList false) = some externals)
    (functionChecked : representation.interface.functions.mapM (fun header =>
      sourcePrototype? representation header
        (functionSymbol representation.moduleName header.name).toList true) = some functions) :
    declaredLayouts? representation = some
      ((representation.interface.records.map fun record =>
        HeaderItem.forward (recordName representation.moduleName record.name)
          (recordName representation.moduleName record.name)) ++ arrays ++ records ++ externals ++ functions) := by
  unfold declaredLayouts?
  rw [arrayChecked, recordChecked, externalChecked, functionChecked]
  rfl

theorem header_agrees_of_full_checks (representation : Representation) (header : CHeader)
    (aliasTypes : ((representation.arrayAliases.map Prod.fst).eraseDups.length ==
      representation.arrayAliases.length) = true)
    (aliasNames : ((representation.arrayAliases.map Prod.snd).eraseDups.length ==
      representation.arrayAliases.length) = true)
    (byteSeparate : (!representation.arrayAliases.any (fun entry => entry.1 == .byte)) = true)
    (layouts : declaredLayouts? representation = some (declarations header))
    (includesAllowed : (includes header).all (fun name =>
      (permittedIncludes representation).contains name) = true)
    (includesPresent : (permittedIncludes representation).all (fun name =>
      (includes header).contains name) = true) : headerAgrees representation header = true := by
  simp only [headerAgrees, aliasTypes, aliasNames, byteSeparate, layouts,
    beq_self_eq_true, Bool.true_and, includesAllowed, includesPresent]

end Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
