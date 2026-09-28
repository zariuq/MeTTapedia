import Mettapedia.GSLT.LanguageDef.MapLanguageDef

/-!
# A validated image of an authored presentation

Mapping every declaration produces a raw presentation. Once that concrete
image passes validation, the per-declaration membership laws assemble into
the canonical structural morphism from the source. The validation premise is
necessary: noninjective symbol actions can collapse distinct declarations.
-/

namespace Mettapedia.GSLT.LanguageDef

/-- Package a checked image without presuming every symbol action preserves
the language validator. -/
def validatedImage (source : ValidatedLanguageDef)
    (symbols : LanguageDefSymbolMap)
    (valid : (mapLanguageDef symbols source.language).validate = []) :
    ValidatedLanguageDef :=
  ⟨mapLanguageDef symbols source.language, valid⟩

/-- The canonical structural map into an actually validated image. It carries
the same symbol action on sorts, constructors, equations, and rewrites. -/
def structuralMapToValidatedImage (source : ValidatedLanguageDef)
    (symbols : LanguageDefSymbolMap)
    (valid : (mapLanguageDef symbols source.language).validate = []) :
    StructuralMorphism source (validatedImage source symbols valid) where
  symbols := symbols
  mapsTypes _ membership :=
    mem_types_mapLanguageDef symbols membership
  mapsTerms _ membership :=
    mem_terms_mapLanguageDef symbols membership
  mapsEquations _ membership :=
    mem_equations_mapLanguageDef symbols membership
  mapsRewrites _ membership :=
    mem_rewrites_mapLanguageDef symbols membership

@[simp]
theorem structuralMapToValidatedImage_symbols
    (source : ValidatedLanguageDef) (symbols : LanguageDefSymbolMap)
    (valid : (mapLanguageDef symbols source.language).validate = []) :
    (structuralMapToValidatedImage source symbols valid).symbols = symbols := rfl

end Mettapedia.GSLT.LanguageDef
