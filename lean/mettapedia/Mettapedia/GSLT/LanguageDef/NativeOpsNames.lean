import Mettapedia.GSLT.LanguageDef.NativeOpsSource

/-! Character certificates for the operational compiler's emitted identifiers. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps

theorem cIdentifier_of_characters (source encoded : String)
    (characters : cIdentifierCharacters source.toList = encoded.toList)
    (notKeyword : cKeywords.contains encoded = false) :
    cIdentifier source = encoded := by
  simp only [cIdentifier, characters, String.ofList_toList, notKeyword,
    Bool.false_eq_true, if_false]

theorem cIdentifier_of_keyword_characters (source encoded : String)
    (characters : cIdentifierCharacters source.toList = encoded.toList)
    (keyword : cKeywords.contains encoded = true) :
    cIdentifier source = "gslt_keyword_" ++ encoded := by
  simp only [cIdentifier, characters, String.ofList_toList, keyword, if_true]

theorem functionSymbol_of_characters (moduleName functionName moduleEncoded functionEncoded result : String)
    (moduleIdentifier : cIdentifier moduleName = moduleEncoded)
    (functionIdentifier : cIdentifier functionName = functionEncoded)
    (characters : "cetta_gslt_".toList ++ moduleEncoded.toList ++ "_".toList ++
      functionEncoded.toList ++ "_v1".toList = result.toList) :
    functionSymbol moduleName functionName = result := by
  simp only [functionSymbol, moduleIdentifier, functionIdentifier]
  apply String.toList_injective
  simpa only [String.toList_append] using characters

end Mettapedia.GSLT.LanguageDef.NativeOps
