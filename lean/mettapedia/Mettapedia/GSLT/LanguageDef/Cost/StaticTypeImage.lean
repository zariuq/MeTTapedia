import Mettapedia.GSLT.LanguageDef.Cost.TaggedDecoding
import Mettapedia.GSLT.LanguageDef.CostStaticTyping

/-!
# Exact static type images over an authored interactive theory

Decoding depends only on the interacting sort and static colour. No continued
object, selected normalizer, or retained-tree closure is required.
-/

namespace Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax StructuralMorphism
namespace CostStaticTypeImage

/-- Decode a sort name in the uniform base fiber. -/
def decodeBaseSort (name : String) : Option String :=
  decodeTaggedPayload costBaseSortTag name

@[simp]
theorem decodeBaseSort_encode (name : String) :
    decodeBaseSort (costBaseSortName name) = some name := by
  exact decodeTaggedPayload_append _ _

/-- Decode the type action of one static Cost copy.  In the wrapped copy the
distinguished interacting sort is represented by the single wrapped carrier;
every other base sort remains in the tagged base fiber. -/
def decode (theory : IGSLT)
    (color : CostStaticColor) : TypeExpr → Option TypeExpr
  | .base sort =>
      match color with
      | .base => (decodeBaseSort sort).map TypeExpr.base
      | .wrapped =>
          if sort = costWrappedSortName then
            some (.base theory.presentation.interactingSort.1.name)
          else do
            let sourceSort ← decodeBaseSort sort
            if sourceSort =
                theory.presentation.interactingSort.1.name then
              none
            else
              some (.base sourceSort)
  | .arrow domain codomain => do
      let sourceDomain ← decode theory color domain
      let sourceCodomain ← decode theory color codomain
      pure (.arrow sourceDomain sourceCodomain)
  | .multiBinder body => do
      let sourceBody ← decode theory color body
      pure (.multiBinder sourceBody)
  | .collection collectionType element => do
      let sourceElement ← decode theory color element
      pure (.collection collectionType sourceElement)

/-- Decoding is a computable left inverse of either exact static type action.
The wrapped interacting sort is separated from every tagged base sort by the
reserved namespace theorem of the generated signature. -/
@[simp]
theorem decode_mapTypeExpr (theory : IGSLT)
    (color : CostStaticColor) (type : TypeExpr) :
    decode theory color
        (mapTypeExpr (color.symbolsOf theory) type) = some type := by
  induction type with
  | base sort =>
      cases color with
      | base =>
          change decode theory .base
              (mapTypeExpr costBaseStaticSymbols (.base sort)) = _
          rw [mapTypeExpr_costBaseStaticSymbols]
          simp [decode, costBaseTypeExpr,
            decodeBaseSort_encode]
      | wrapped =>
          change decode theory .wrapped
              (mapTypeExpr (costWrappedStaticSymbols theory)
                (.base sort)) = _
          rw [mapTypeExpr_costWrappedStaticSymbols]
          by_cases interacting :
              sort = theory.presentation.interactingSort.1.name
          · subst sort
            simp [decode, costWrappedTypeExpr]
          · simp [decode, costWrappedTypeExpr,
              interacting, costBaseSortName_ne_wrapped,
              decodeBaseSort_encode]
  | arrow domain codomain domainHypothesis codomainHypothesis =>
      simp [decode, mapTypeExpr,
        domainHypothesis, codomainHypothesis]
  | multiBinder body inductionHypothesis =>
      simp [decode, mapTypeExpr, inductionHypothesis]
  | collection collectionType element inductionHypothesis =>
      simp [decode, mapTypeExpr, inductionHypothesis]

/-- A successfully decoded static type lies in the exact image of the
selected Cost fiber.  In the wrapped fiber the base-tagged interacting sort
is deliberately rejected: its only image is the distinguished wrapped sort.
Together with `decode_mapTypeExpr`, this makes decoding a
partial equivalence rather than a merely one-sided parser. -/
theorem mapTypeExpr_decode (theory : IGSLT)
    (color : CostStaticColor) {target sourceType : TypeExpr}
    (decoded : decode theory color target =
      some sourceType) :
    mapTypeExpr (color.symbolsOf theory) sourceType = target := by
  induction target generalizing sourceType with
  | base sort =>
      cases color with
      | base =>
          cases decodedSort : decodeBaseSort sort with
          | none =>
              simp [decode, decodedSort] at decoded
          | some sourceSort =>
              simp [decode, decodedSort] at decoded
              subst sourceType
              have sortEquality : sort = costBaseSortName sourceSort :=
                (decodeTaggedPayload_eq_some_iff
                  costBaseSortTag sort sourceSort).mp decodedSort
              subst sort
              simp [CostStaticColor.symbolsOf, costBaseStaticSymbols,
                costBaseLanguageDefSymbolMap, mapTypeExpr]
      | wrapped =>
          by_cases wrapped : sort = costWrappedSortName
          · subst sort
            simp [decode] at decoded
            subst sourceType
            simp [CostStaticColor.symbolsOf, costWrappedStaticSymbols,
              mapTypeExpr]
          · cases decodedSort : decodeBaseSort sort with
            | none =>
                simp [decode, wrapped, decodedSort] at decoded
            | some sourceSort =>
                by_cases interacting : sourceSort =
                    theory.presentation.interactingSort.1.name
                · simp [decode, wrapped, decodedSort,
                    interacting] at decoded
                · simp [decode, wrapped, decodedSort,
                    interacting] at decoded
                  subst sourceType
                  have sortEquality : sort = costBaseSortName sourceSort :=
                    (decodeTaggedPayload_eq_some_iff
                      costBaseSortTag sort sourceSort).mp decodedSort
                  subst sort
                  simp [CostStaticColor.symbolsOf, costWrappedStaticSymbols,
                    mapTypeExpr, interacting]
  | arrow domain codomain domainHypothesis codomainHypothesis =>
      cases decodedDomain : decode theory color domain with
      | none =>
          simp [decode, decodedDomain] at decoded
      | some sourceDomain =>
          cases decodedCodomain :
              decode theory color codomain with
          | none =>
              simp [decode, decodedDomain,
                decodedCodomain] at decoded
          | some sourceCodomain =>
              simp [decode, decodedDomain,
                decodedCodomain] at decoded
              subst sourceType
              simp [mapTypeExpr,
                domainHypothesis decodedDomain,
                codomainHypothesis decodedCodomain]
  | multiBinder body inductionHypothesis =>
      cases decodedBody : decode theory color body with
      | none =>
          simp [decode, decodedBody] at decoded
      | some sourceBody =>
          simp [decode, decodedBody] at decoded
          subst sourceType
          simp [mapTypeExpr, inductionHypothesis decodedBody]
  | collection collectionType element inductionHypothesis =>
      cases decodedElement : decode theory color element with
      | none =>
          simp [decode, decodedElement] at decoded
      | some sourceElement =>
          simp [decode, decodedElement] at decoded
          subst sourceType
          simp [mapTypeExpr, inductionHypothesis decodedElement]

/-- Each static type action is injective. -/
theorem embed_injective (theory : IGSLT)
    (color : CostStaticColor) :
    Function.Injective (mapTypeExpr (color.symbolsOf theory)) := by
  intro left right equality
  have decoded := congrArg (decode theory color) equality
  simpa using decoded

/-- Successful decoding is exactly membership with this preimage, including
arrows, multi-binders and collection types. -/
theorem decode_eq_some_iff (theory : IGSLT) (color : CostStaticColor)
    (target sourceType : TypeExpr) :
    decode theory color target = some sourceType ↔
      mapTypeExpr (color.symbolsOf theory) sourceType = target := by
  constructor
  · exact mapTypeExpr_decode theory color
  · rintro rfl
    exact decode_mapTypeExpr theory color sourceType

/-- Rejection means no source type embeds into this target type. -/
theorem decode_eq_none_iff (theory : IGSLT) (color : CostStaticColor)
    (target : TypeExpr) :
    decode theory color target = none ↔
      ¬ ∃ sourceType, mapTypeExpr (color.symbolsOf theory) sourceType = target := by
  constructor
  · intro rejected ⟨sourceType, mapped⟩
    have accepted := (decode_eq_some_iff theory color target sourceType).2 mapped
    simp [rejected] at accepted
  · intro absent
    cases decoded : decode theory color target with
    | none => rfl
    | some sourceType => exact False.elim (absent ⟨sourceType,
        mapTypeExpr_decode theory color decoded⟩)

@[simp] theorem decode_signature (theory : IGSLT) (color : CostStaticColor) :
    decode theory color (.base costSignatureSortName) = none := by
  cases color <;> rfl

@[simp] theorem decode_key (theory : IGSLT) (color : CostStaticColor) :
    decode theory color (.base costKeySortName) = none := by
  cases color <;> rfl

/-- In the wrapped colour the base-tagged interacting sort is foreign. It
cannot be mistaken for the distinguished wrapped carrier. -/
@[simp] theorem decode_wrapped_base_interacting (theory : IGSLT) :
    decode theory .wrapped
      (.base (costBaseSortName theory.presentation.interactingSort.1.name)) = none := by
  simp [decode, costBaseSortName_ne_wrapped]

end CostStaticTypeImage
end Mettapedia.GSLT.LanguageDef
