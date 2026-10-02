import Mettapedia.GSLT.LanguageDef.NativeOpsCLayoutComposition
import Mettapedia.GSLT.LanguageDef.NativeOpsNames

/-!
# Shared finite native declaration facts

Character-level identifier and type certificates compose through the original
declaration reader. These laws avoid repeatedly rebuilding closed UTF-8
strings while preserving every parameter, field, pointer level and symbol.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps.NativeC

theorem record_name_of_characters (moduleName name moduleEncoded nameEncoded : String)
    (characters : Name)
    (moduleIdentifier : cIdentifier moduleName = moduleEncoded)
    (nameIdentifier : cIdentifier name = nameEncoded)
    (joined : "CettaGslt_".toList ++ moduleEncoded.toList ++ "_".toList ++
      nameEncoded.toList ++ "V1".toList = characters) :
    recordName moduleName name = characters := by
  simp only [recordName, moduleIdentifier, nameIdentifier, String.toList_append]
  exact joined

theorem parameter_name_of_characters (name encoded : String) (characters : Name)
    (identifierChecked : cIdentifier name = encoded)
    (joined : "local_".toList ++ encoded.toList = characters) :
    ("local_" ++ cIdentifier name).toList = characters := by
  simp only [identifierChecked, String.toList_append]
  exact joined

theorem source_record_type_of_facts (representation : Representation) (name : String)
    (characters : Name)
    (allocated : (lookupRecord representation.interface name).isSome = true)
    (named : recordName representation.moduleName name = characters) :
    sourceType? representation (.named name) = some ⟨characters, 0⟩ := by
  simp only [sourceType?, allocated, if_true, named]

theorem source_reference_type_of_fact (representation : Representation) (element : NativeType)
    (type : CType) (checked : sourceType? representation element = some type) :
    sourceType? representation (.ref element) =
      some { type with pointers := type.pointers + 1 } := by
  rw [sourceType?, checked]
  rfl

theorem source_field_of_facts (representation : Representation) (field : Parameter)
    (type : CType) (characters : Name)
    (typeChecked : sourceType? representation field.type = some type)
    (nameChecked : (cIdentifier field.name).toList = characters) :
    (do let actual ← sourceType? representation field.type
        some (CParameter.mk actual (cIdentifier field.name).toList)) =
      some ⟨type, characters⟩ := by
  rw [typeChecked]
  change some (CParameter.mk type (cIdentifier field.name).toList) = _
  exact congrArg (fun name => some (CParameter.mk type name)) nameChecked

theorem source_parameter_of_facts (representation : Representation) (parameter : Parameter)
    (type : CType) (characters : Name)
    (typeChecked : sourceType? representation parameter.type = some type)
    (nameChecked : ("local_" ++ cIdentifier parameter.name).toList = characters) :
    (do let actual ← sourceType? representation parameter.type
        some (CParameter.mk actual ("local_" ++ cIdentifier parameter.name).toList)) =
      some ⟨type, characters⟩ := by
  rw [typeChecked]
  change some (CParameter.mk type ("local_" ++ cIdentifier parameter.name).toList) = _
  exact congrArg (fun name => some (CParameter.mk type name)) nameChecked

theorem source_fields_cons_of_facts (representation : Representation) (first : Parameter)
    (rest : List Parameter) (head : CParameter) (tail : List CParameter)
    (headChecked : (do
      let type ← sourceType? representation first.type
      some (CParameter.mk type (cIdentifier first.name).toList)) = some head)
    (tailChecked : sourceFields? representation rest = some tail) :
    sourceFields? representation (first :: rest) = some (head :: tail) := by
  unfold sourceFields? at tailChecked ⊢
  exact option_mapM_cons_certified _ _ _ _ _ headChecked tailChecked

theorem source_parameters_cons_of_facts (representation : Representation) (first : Parameter)
    (rest : List Parameter) (head : CParameter) (tail : List CParameter)
    (headChecked : (do
      let type ← sourceType? representation first.type
      some (CParameter.mk type ("local_" ++ cIdentifier first.name).toList)) = some head)
    (tailChecked : sourceParameters? representation rest = some tail) :
    sourceParameters? representation (first :: rest) = some (head :: tail) := by
  unfold sourceParameters? at tailChecked ⊢
  exact option_mapM_cons_certified _ _ _ _ _ headChecked tailChecked

theorem source_prototype_of_facts (representation : Representation) (header : Header)
    (symbol : Name) (internal : Bool) (result : CType) (parameters : List CParameter)
    (resultChecked : sourceType? representation header.result = some result)
    (parametersChecked : sourceParameters? representation header.parameters = some parameters) :
    sourcePrototype? representation header symbol internal =
      some (.prototype result symbol (if internal then
        ⟨⟨"CettaGsltNativeOpsContextV1".toList, 1⟩, "ctx".toList⟩ :: parameters else parameters)) := by
  unfold sourcePrototype?
  rw [resultChecked, parametersChecked]
  rfl

end Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
