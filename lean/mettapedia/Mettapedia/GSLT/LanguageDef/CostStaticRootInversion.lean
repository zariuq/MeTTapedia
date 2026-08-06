import Mettapedia.GSLT.LanguageDef.CostHereditaryAlignment

/-!
# Static-root inversion for proof-relevant Cost trees

The raw constructor shape alone does not determine a Cost region.  Once the
tree is indexed by its checked result fibre, however, two useful inversions
are exact:

* a collection at a base result type cannot be the structural homogeneous
  collection constructor, so it is rooted at a static node;
* an application decoded at a static declaration role cannot be one of the
  interaction-principal or apparatus frames.

These statements expose the colour already retained by the tree.  They do
not rerun the executable planner or promote its enumeration order to
semantic data.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL.Syntax
open WellSorted

/-- Executable observation of whether the retained tree constructor is a
static region.  This inspects proof-relevant tree data, not compact syntax or
planner search order. -/
def CostRegionTree.rootIsStatic
    {source : CIGSLT} {targetFree : FreeTypeContext}
    {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr} :
    CostRegionTree source targetFree available outer pattern type → Bool
  | .static _ _ => true
  | _ => false

/-- A retained static root always inhabits a base result fibre.  This is an
index fact of `CostRegionTree.static`, independent of compact pattern shape
or planner search order. -/
theorem CostRegionTree.type_eq_base_of_rootIsStatic
    {source : CIGSLT} {targetFree : FreeTypeContext}
    {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (tree : CostRegionTree source targetFree available outer pattern type)
    (static : tree.rootIsStatic = true) :
    ∃ category, type = .base category := by
  cases tree with
  | bvar lookup => simp [CostRegionTree.rootIsStatic] at static
  | fvar lookup => simp [CostRegionTree.rootIsStatic] at static
  | static node children => exact ⟨_, rfl⟩
  | neutralApplicationOrdinary membership notBare constructor materializes
      neutral ordinary children =>
      simp [CostRegionTree.rootIsStatic] at static
  | neutralApplicationQuote membership notBare constructor materializes
      neutral quoted children =>
      simp [CostRegionTree.rootIsStatic] at static
  | lambda body => simp [CostRegionTree.rootIsStatic] at static
  | multiLambda body => simp [CostRegionTree.rootIsStatic] at static
  | subst body replacement => simp [CostRegionTree.rootIsStatic] at static
  | collection children => simp [CostRegionTree.rootIsStatic] at static

/-- A retained static root exposes one of the two syntax shapes certified by
its planner: an application or a collection.  The theorem is phrased on the
tree so clients need not dependently eliminate a hidden static node. -/
theorem CostRegionTree.pattern_shape_of_rootIsStatic
    {source : CIGSLT} {targetFree : FreeTypeContext}
    {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (tree : CostRegionTree source targetFree available outer pattern type)
    (static : tree.rootIsStatic = true) :
    (∃ wireName arguments, pattern = .apply wireName arguments) ∨
      ∃ collectionType elements rest,
        pattern = .collection collectionType elements rest := by
  cases tree with
  | bvar lookup => simp [CostRegionTree.rootIsStatic] at static
  | fvar lookup => simp [CostRegionTree.rootIsStatic] at static
  | static node children =>
      exact node.plan.pattern_shape_of_isStaticRoot node.rootStatic
  | neutralApplicationOrdinary membership notBare constructor materializes
      neutral ordinary children =>
      simp [CostRegionTree.rootIsStatic] at static
  | neutralApplicationQuote membership notBare constructor materializes
      neutral quoted children =>
      simp [CostRegionTree.rootIsStatic] at static
  | lambda body => simp [CostRegionTree.rootIsStatic] at static
  | multiLambda body => simp [CostRegionTree.rootIsStatic] at static
  | subst body replacement => simp [CostRegionTree.rootIsStatic] at static
  | collection children => simp [CostRegionTree.rootIsStatic] at static

/-- A free-variable tree cannot hide a static region root. -/
theorem CostRegionTree.rootIsStatic_eq_false_of_fvar
    {source : CIGSLT} {targetFree : FreeTypeContext}
    {available outer : List TypeExpr} {name : String} {type : TypeExpr}
    (tree : CostRegionTree source targetFree available outer (.fvar name)
      type) :
    tree.rootIsStatic = false := by
  apply Bool.eq_false_of_not_eq_true
  intro static
  rcases tree.pattern_shape_of_rootIsStatic static with
    ⟨wireName, arguments, impossible⟩ | ⟨collectionType, elements, rest,
      impossible⟩ <;> cases impossible

/-- A collection-typed tree is structural: static regions always return a
base sort, even when their compact root happens to be a collection. -/
theorem CostRegionTree.rootIsStatic_eq_false_of_collection_type
    {source : CIGSLT} {targetFree : FreeTypeContext}
    {available outer : List TypeExpr} {pattern : Pattern}
    {collectionType : CollType} {elementType : TypeExpr}
    (tree : CostRegionTree source targetFree available outer pattern
      (.collection collectionType elementType)) :
    tree.rootIsStatic = false := by
  apply Bool.eq_false_of_not_eq_true
  intro static
  obtain ⟨category, impossible⟩ := tree.type_eq_base_of_rootIsStatic static
  cases impossible

/-- A static-root colour certificate is reflected by the executable root
observation, including all three index-only reindexing constructors. -/
theorem CostRegionTree.StaticRootColor.rootIsStatic
    {source : CIGSLT} {targetFree : FreeTypeContext}
    {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    {tree : CostRegionTree source targetFree available outer pattern type}
    {color : CostStaticColor}
    (root : CostRegionTree.StaticRootColor source targetFree tree color) :
    tree.rootIsStatic = true := by
  induction root with
  | static node children => rfl
  | reindexPattern patternEq tree root inductionHypothesis =>
      cases patternEq
      exact inductionHypothesis
  | reindexAvailable availableEq tree root inductionHypothesis =>
      cases availableEq
      exact inductionHypothesis
  | reindexType typeEq tree root inductionHypothesis =>
      cases typeEq
      exact inductionHypothesis

/-- A tree observed as structural cannot carry any static-root colour
certificate. -/
theorem CostRegionTree.not_nonempty_staticRootColor_of_rootIsStatic_false
    {source : CIGSLT} {targetFree : FreeTypeContext}
    {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (tree : CostRegionTree source targetFree available outer pattern type)
    (structural : tree.rootIsStatic = false) :
    ¬ Nonempty (Σ color,
      CostRegionTree.StaticRootColor source targetFree tree color) := by
  rintro ⟨⟨color, root⟩⟩
  rw [root.rootIsStatic] at structural
  contradiction

/-- A base-typed collection tree is necessarily a proof-relevant static
root.  The structural collection constructor has a collection result type,
so it cannot inhabit this fibre. -/
theorem CostRegionTree.nonempty_staticRootColor_of_base_collection_of_eq
    {source : CIGSLT} {targetFree : FreeTypeContext}
    {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (tree : CostRegionTree source targetFree available outer pattern type)
    {collectionType : CollType} {elements : List Pattern}
    {rest : Option String} {category : String}
    (patternEq : pattern = .collection collectionType elements rest)
    (typeEq : type = .base category) :
    Nonempty (Σ color,
      CostRegionTree.StaticRootColor source targetFree tree color) := by
  cases tree with
  | bvar lookup => cases patternEq
  | fvar lookup => cases patternEq
  | static node children =>
      exact ⟨⟨_, .static node children⟩⟩
  | neutralApplicationOrdinary membership notBare constructor materializes
      neutral ordinary children => cases patternEq
  | neutralApplicationQuote membership notBare constructor materializes
      neutral quoted children => cases patternEq
  | lambda bodyTree => cases patternEq
  | multiLambda bodyTree => cases patternEq
  | subst bodyTree replacementTree => cases patternEq
  | collection children => cases typeEq

/-- Fixed-index specialization of
`nonempty_staticRootColor_of_base_collection_of_eq`. -/
theorem CostRegionTree.nonempty_staticRootColor_of_base_collection
    {source : CIGSLT} {targetFree : FreeTypeContext}
    {available outer : List TypeExpr} {collectionType : CollType}
    {elements : List Pattern} {rest : Option String} {category : String}
    (tree : CostRegionTree source targetFree available outer
      (.collection collectionType elements rest) (.base category)) :
    Nonempty (Σ color,
      CostRegionTree.StaticRootColor source targetFree tree color) :=
  tree.nonempty_staticRootColor_of_base_collection_of_eq rfl rfl

/-- An application tree whose intrinsic declaration has one static role is
rooted at that exact colour.  Constructor decoding rules out a neutral frame;
the remaining static case recovers the colour from the node's own plan. -/
theorem CostRegionTree.nonempty_staticRootColor_of_static_application_of_eq
    {source : CIGSLT} {targetFree : FreeTypeContext}
    {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (tree : CostRegionTree source targetFree available outer pattern type)
    {wireName : String} {arguments : List Pattern} {category : String}
    (patternEq : pattern = .apply wireName arguments)
    (_typeEq : type = .base category)
    (color : CostStaticColor)
    (constructor : source.DeclaredCostConstructor)
    (decoded : source.decodeDeclaredCostConstructor wireName = some constructor)
    (role : source.declaredCostConstructorRole constructor = .static color) :
    Nonempty (CostRegionTree.StaticRootColor source targetFree tree color) := by
  cases tree with
  | bvar lookup => cases patternEq
  | fvar lookup => cases patternEq
  | static node children =>
      rename_i nodeColor
      obtain ⟨nodeConstructor, nodeDecoded, nodeRole⟩ :=
        node.plan.application_dispatch_of_isStaticRoot node.rootStatic patternEq
      have constructorEq : nodeConstructor = constructor :=
        Option.some.inj (nodeDecoded.symm.trans decoded)
      subst nodeConstructor
      have colorEq : nodeColor = color :=
        CIGSLT.GeneratedCostConstructorRole.static.inj
          (nodeRole.symm.trans role)
      subst color
      exact ⟨.static node children⟩
  | neutralApplicationOrdinary membership notBare neutralConstructor
      materializes neutral ordinary children =>
      injection patternEq with wireEq argumentsEq
      have neutralDecoded : source.decodeDeclaredCostConstructor wireName =
          some neutralConstructor := by
        rw [← wireEq, ← materializes,
          source.materializeDeclaredCostConstructor_label]
        exact source.decodeDeclaredCostConstructor_render neutralConstructor
      have constructorEq : neutralConstructor = constructor :=
        Option.some.inj (neutralDecoded.symm.trans decoded)
      subst neutralConstructor
      rcases neutral with neutralRole | ⟨kind, neutralRole⟩ <;>
        rw [neutralRole] at role <;> contradiction
  | neutralApplicationQuote membership notBare neutralConstructor materializes
      neutral quoted children =>
      injection patternEq with wireEq argumentsEq
      have neutralDecoded : source.decodeDeclaredCostConstructor wireName =
          some neutralConstructor := by
        rw [← wireEq, ← materializes,
          source.materializeDeclaredCostConstructor_label]
        exact source.decodeDeclaredCostConstructor_render neutralConstructor
      have constructorEq : neutralConstructor = constructor :=
        Option.some.inj (neutralDecoded.symm.trans decoded)
      subst neutralConstructor
      rcases neutral with neutralRole | ⟨kind, neutralRole⟩ <;>
        rw [neutralRole] at role <;> contradiction
  | lambda bodyTree => cases patternEq
  | multiLambda bodyTree => cases patternEq
  | subst bodyTree replacementTree => cases patternEq
  | collection children => cases patternEq

/-- Fixed-index specialization of
`nonempty_staticRootColor_of_static_application_of_eq`. -/
theorem CostRegionTree.nonempty_staticRootColor_of_static_application
    {source : CIGSLT} {targetFree : FreeTypeContext}
    {available outer : List TypeExpr} {wireName : String}
    {arguments : List Pattern} {category : String}
    (tree : CostRegionTree source targetFree available outer
      (.apply wireName arguments) (.base category))
    (color : CostStaticColor)
    (constructor : source.DeclaredCostConstructor)
    (decoded : source.decodeDeclaredCostConstructor wireName = some constructor)
    (role : source.declaredCostConstructorRole constructor = .static color) :
    Nonempty (CostRegionTree.StaticRootColor source targetFree tree color) :=
  tree.nonempty_staticRootColor_of_static_application_of_eq rfl rfl color
    constructor decoded role

/-- Successful declaration-aware static decoding exposes the exact intrinsic
constructor and its selected static role. -/
theorem exists_declaredCostConstructor_of_static_decode
    (source : CIGSLT) (color : CostStaticColor) (wireName sourceName : String)
    (decoded : decodeDeclaredCostStaticConstructor source color wireName =
      some sourceName) :
    ∃ constructor : source.DeclaredCostConstructor,
      source.decodeDeclaredCostConstructor wireName = some constructor ∧
        source.declaredCostConstructorRole constructor = .static color := by
  unfold decodeDeclaredCostStaticConstructor at decoded
  cases constructorEq : source.decodeDeclaredCostConstructor wireName with
  | none => simp [constructorEq] at decoded
  | some constructor =>
      simp only [constructorEq] at decoded
      split at decoded
      next role => exact ⟨constructor, rfl, role⟩
      next role => simp at decoded

/-- A wrapped source label decodes in either generated static colour.  This
label-level form avoids choosing a second rule table: membership in
`wrappedLabels` already retains an authored constructor witness. -/
theorem decodeDeclaredCostStaticConstructor_symbols_of_wrappedLabel
    (source : CIGSLT) (color : CostStaticColor) (label : String)
    (wrapped : label ∈ source.continuationRetyping.wrappedLabels) :
    decodeDeclaredCostStaticConstructor source color
      ((color.symbols source).constructor label) = some label := by
  rcases List.mem_map.mp wrapped with ⟨constructor, membership, labelEq⟩
  rw [← labelEq]
  exact decodeDeclaredCostStaticConstructor_symbols_of_wrapped source color
    constructor.1 constructor.2
      (List.mem_map.mpr ⟨constructor, membership, rfl⟩)

end Mettapedia.GSLT.LanguageDef
