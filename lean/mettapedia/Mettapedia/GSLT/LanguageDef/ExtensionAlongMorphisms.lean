import Mathlib.Algebra.Group.End
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.SingleObj
import Mettapedia.GSLT.LanguageDef.ExtensionGluing
import Mettapedia.GSLT.LanguageDef.SourcePreservingCalculusCoproduct
import Mettapedia.GSLT.LanguageDef.StructuralCoproduct
import Mettapedia.GSLT.LanguageDef.ModuleAlgebra.RawDeclarationLayers
import Mettapedia.GSLT.LanguageDef.WellSorted
import Mettapedia.GSLT.LanguageDef.InferenceNewJudgmentConservativity
import Mettapedia.GSLT.LanguageDef.StructuralPatternScope

/-!
# Extension layers along morphisms of their cores

An `ExtensionLayer` is indexed by a set of cores: `reindex` follows plain
functions between index types, and a layer `Hom` never changes its core.
Neither moves declarations along a map of theories, so a union or an
interpretation of cores drops their extensions.  This module supplies the
missing action and the union it permits.

* `LayerTransport` is a covariant, functorial action of core morphisms on the
  declarations of a layer.  Its declaration functor has a category of
  elements, the total category of decorated cores (`LayerTransport.Total`),
  with the projection to cores and a lift of every core morphism.
* `CompositionalTransport` is a transport of a compositional layer that is a
  homomorphism of the payload partial monoid.  Products of transportable
  layers are transportable.
* Raw module rows are admitted against their own law-free schema and mention
  no core symbol.  Their transport is the identity, so a union of raw-layered
  cores along any pair of core morphisms is the ordered origin join of the
  rows (`rawTransport`).
* Proof calculi do mention core symbols: rule schemas contain core
  constructors inside judgment arguments.  Their transport renames those
  constructors and fixes the calculus' own judgment and rule namespaces
  (`calculusTransport`).  Admission moves along a typing morphism exactly when
  no constructor of the target carries a judgment head (`admitted_reindex_iff`).
* **Namespaces.**  Since a core morphism never renames judgment heads or rule
  identifiers, two layers that declare the same head have no union over any
  core.  A `NamespaceMap` renames both; it commutes with core transport
  (`layerSymbols_eq_rename_comp`, `layerSymbols_eq_comp_rename`), and calculi
  move along pairs of a core morphism and a renaming (`layerTransport`).
  Admission moves along such a pair exactly when the renaming is legal for the
  target core (`admitted_layer_iff`): it keeps heads apart and identifiers
  apart, keeps them nonempty, avoids the reserved heads and the target's
  constructor labels.  Two renamed decorated cores have a union exactly when
  the renamed calculi are compatible (`union_layer_admitted_iff`); the
  identity renaming gives `union_admitted_iff`.
* Gluing two compatible admitted calculi is their least upper bound in the
  refinement order of the fibre (`glue_least`).  Two decorated cores mapped
  into one core have a union exactly when their calculi are compatible
  (`union_admitted_iff`).  Over a structural coproduct the union receives both
  decorated cores by morphisms of complete calculus languages lying over the
  coproduct injections (`coproductUnionLeft`, `coproductUnionRight`).
  Restricted to the judgments of either side, the union is that side's
  calculus transported along its injection (`coproductUnion_restrict_left`,
  `coproductUnion_restrict_right`); it resolves each side's judgments as that
  side does, and checks a proof of a judgment of either side exactly as the
  transported side alone checks it (`coproductUnion_conservative_left`,
  `coproductUnion_conservative_right`).
  Along identity morphisms the union is the equal-core gluing itself
  (`equalCore_union_iff`).
* The admitted part of the category of elements of the layer transport embeds
  faithfully into the existing category of validated calculus languages over
  the same cores (`toCalculusLanguageDef`); a renaming over an identity core
  morphism becomes a vertical structural map.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ExtensionAlongMorphisms

open CategoryTheory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.Extension
open Mettapedia.GSLT.LanguageDef.ExtensionComposition
open Mettapedia.GSLT.LanguageDef.InferenceExtension
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.ExtensionGluing
open Mettapedia.GSLT.LanguageDef.SourcePreservingCalculusCoproduct

universe uBase uCore vCore uFiber uFiber'

/-! ## Transport along core morphisms -/

/-- A covariant, functorial action of core morphisms on the declarations of a
layer.  Unlike `ExtensionLayer.reindex`, which follows a function between
index types, a transport follows the morphisms of a category of cores. -/
structure LayerTransport {Core : Type uCore} [Category.{vCore} Core]
    (family : ExtensionLayer.{uCore, uFiber} Core) where
  /-- Move a declaration along a core morphism. -/
  map : ∀ {source target : Core}, (source ⟶ target) →
    family.Fiber source → family.Fiber target
  map_id : ∀ (core : Core) (declaration : family.Fiber core),
    map (𝟙 core) declaration = declaration
  map_comp : ∀ {first second third : Core} (earlier : first ⟶ second)
      (later : second ⟶ third) (declaration : family.Fiber first),
    map (earlier ≫ later) declaration = map later (map earlier declaration)

namespace LayerTransport

variable {Core : Type uCore} [Category.{vCore} Core]
  {family : ExtensionLayer.{uCore, uFiber} Core}

/-- The declarations of a transportable layer form a functor on cores. -/
def functor (transport : LayerTransport family) : Core ⥤ Type uFiber where
  obj core := family.Fiber core
  map morphism := TypeCat.ofHom (transport.map morphism)
  map_id core := by
    apply ConcreteCategory.hom_ext
    intro declaration
    exact transport.map_id core declaration
  map_comp earlier later := by
    apply ConcreteCategory.hom_ext
    intro declaration
    exact transport.map_comp earlier later declaration

@[simp] theorem functor_obj (transport : LayerTransport family) (core : Core) :
    transport.functor.obj core = family.Fiber core :=
  rfl

@[simp] theorem functor_map_apply (transport : LayerTransport family)
    {source target : Core} (morphism : source ⟶ target)
    (declaration : family.Fiber source) :
    transport.functor.map morphism declaration = transport.map morphism declaration :=
  rfl

/-- **Decorated cores.**  The total category is the category of elements of
the declaration functor, the Grothendieck construction of a functor into
types: an object is a core with one declaration over it, and a morphism is a
core morphism that transports the first declaration to the second. -/
abbrev Total (transport : LayerTransport family) : Type (max uCore uFiber) :=
  transport.functor.Elements

/-- Forget the declaration and keep the core. -/
def projection (transport : LayerTransport family) : transport.Total ⥤ Core :=
  CategoryOfElements.π transport.functor

/-- The lift of a core morphism at a declaration of its source. -/
def lift (transport : LayerTransport family) {source target : Core}
    (morphism : source ⟶ target) (declaration : family.Fiber source) :
    transport.functor.elementsMk source declaration ⟶
      transport.functor.elementsMk target (transport.map morphism declaration) :=
  ⟨morphism, rfl⟩

@[simp] theorem projection_map_lift (transport : LayerTransport family)
    {source target : Core} (morphism : source ⟶ target)
    (declaration : family.Fiber source) :
    transport.projection.map (transport.lift morphism declaration) = morphism :=
  rfl

/-- Every morphism of decorated cores is a lift: its target declaration is the
transport of its source declaration.  The projection is a discrete
opfibration. -/
theorem target_eq_map (transport : LayerTransport family)
    {source target : transport.Total} (morphism : source ⟶ target) :
    target.2 = transport.map morphism.val source.2 :=
  morphism.property.symm

end LayerTransport

/-! ## Compositional layers -/

/-- Reindex a compositional layer along a map of cores.  This is the
compositional companion of `ExtensionLayer.reindex`: the authored language
and payload over a core are those over its image. -/
def _root_.Mettapedia.GSLT.LanguageDef.ExtensionComposition.CompositionalLayer.reindex
    {Base : Type uBase} {Core : Type uCore} (image : Core → Base)
    (declarations : CompositionalLayer.{uBase, uFiber} Base) :
    CompositionalLayer.{uCore, uFiber} Core where
  Fiber := fun core => declarations.Fiber (image core)
  system := fun core => declarations.system (image core)

/-- A transport of a compositional layer that is also a homomorphism of the
payload partial monoid forced by authored concatenation. -/
structure CompositionalTransport {Core : Type uCore} [Category.{vCore} Core]
    (declarations : CompositionalLayer.{uCore, uFiber} Core) extends
    LayerTransport declarations.toCoGSLTLayer.toExtensionLayer where
  map_empty : ∀ {source target : Core} (morphism : source ⟶ target),
    map morphism (declarations.system source).emptyPayload =
      (declarations.system target).emptyPayload
  map_merge : ∀ {source target : Core} (morphism : source ⟶ target)
      (first second : declarations.Fiber source),
    (declarations.system target).merge (map morphism first) (map morphism second) =
      ((declarations.system source).merge first second).map (map morphism)

namespace CompositionalTransport

variable {Core : Type uCore} [Category.{vCore} Core]

/-- **Transportable layers are closed under product.**  The product transport
acts componentwise; its partial-monoid law is derived from the components'. -/
def product {left : CompositionalLayer.{uCore, uFiber} Core}
    {right : CompositionalLayer.{uCore, uFiber'} Core}
    (leftTransport : CompositionalTransport left)
    (rightTransport : CompositionalTransport right) :
    CompositionalTransport (left.product right) where
  map morphism := fun (declarations : left.Fiber _ × right.Fiber _) =>
    (leftTransport.map morphism declarations.1,
      rightTransport.map morphism declarations.2)
  map_id core := fun (declarations : left.Fiber core × right.Fiber core) =>
    Prod.ext (leftTransport.map_id core declarations.1)
      (rightTransport.map_id core declarations.2)
  map_comp earlier later := fun (declarations : left.Fiber _ × right.Fiber _) =>
    Prod.ext (leftTransport.map_comp earlier later declarations.1)
      (rightTransport.map_comp earlier later declarations.2)
  map_empty morphism :=
    Prod.ext (leftTransport.map_empty morphism) (rightTransport.map_empty morphism)
  map_merge morphism first second := by
    change ((left.system _).merge (leftTransport.map morphism first.1)
          (leftTransport.map morphism second.1)).bind
        (fun mergedLeft =>
          ((right.system _).merge (rightTransport.map morphism first.2)
              (rightTransport.map morphism second.2)).bind
            fun mergedRight => some (mergedLeft, mergedRight)) =
      (((left.system _).merge first.1 second.1).bind
        (fun mergedLeft =>
          ((right.system _).merge first.2 second.2).bind
            fun mergedRight => some (mergedLeft, mergedRight))).map
        (fun declarations =>
          (leftTransport.map morphism declarations.1,
            rightTransport.map morphism declarations.2))
    rw [leftTransport.map_merge, rightTransport.map_merge]
    cases (left.system _).merge first.1 second.1 <;>
      cases (right.system _).merge first.2 second.2 <;> rfl

end CompositionalTransport

/-! ## Raw module rows

A raw row is admitted against its own law-free schema: its category is a sort
of that schema and its fields are terms of that schema.  It mentions no symbol
of the core it decorates.  A core morphism therefore has nothing to rename,
and the transport of raw rows is the identity.  Consequently a union of
raw-layered cores along any pair of core morphisms into one core carries the
ordered origin join `RawDeclarationLayers.join?` of the rows; equal cores are
not needed for raw rows. -/

/-- Raw module rows over validated cores move along every structural morphism
unchanged. -/
def rawTransport :
    CompositionalTransport
      (ModuleAlgebra.RawDeclarationLayers.declarationLayer.reindex
        ValidatedLanguageDef.language) where
  map _ rows := rows
  map_id _ _ := rfl
  map_comp _ _ _ := rfl
  map_empty _ := rfl
  map_merge _ _ _ := rfl

/-! ## Proof calculi -/

/-- The calculus-language action of a core symbol map: constructors move as
the core map says, while the calculus' own judgment and rule namespaces stay
fixed.  A core morphism knows nothing about those namespaces. -/
def coreSymbols (symbols : LanguageDefSymbolMap) : CalculusLanguageSymbols where
  toLanguageDefSymbolMap := symbols
  judgment := _root_.id
  rule := _root_.id

@[simp] theorem coreSymbols_id :
    coreSymbols LanguageDefSymbolMap.id = CalculusLanguageSymbols.id :=
  rfl

@[simp] theorem coreSymbols_comp (first second : LanguageDefSymbolMap) :
    coreSymbols (first.comp second) = (coreSymbols first).comp (coreSymbols second) :=
  rfl

/-- A renaming of a calculus' own namespaces: its judgment heads and its rule
identifiers. -/
@[ext]
structure NamespaceMap where
  /-- Renaming of judgment heads. -/
  judgment : String → String
  /-- Renaming of rule identifiers. -/
  rule : String → String

/-- Renamings compose as functions: `later * earlier` renames by `earlier`
first. -/
instance : Monoid NamespaceMap where
  mul later earlier := ⟨later.judgment ∘ earlier.judgment, later.rule ∘ earlier.rule⟩
  one := ⟨_root_.id, _root_.id⟩
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl

@[simp] theorem NamespaceMap.one_judgment : (1 : NamespaceMap).judgment = _root_.id :=
  rfl

@[simp] theorem NamespaceMap.one_rule : (1 : NamespaceMap).rule = _root_.id :=
  rfl

@[simp] theorem NamespaceMap.mul_judgment (later earlier : NamespaceMap) :
    (later * earlier).judgment = later.judgment ∘ earlier.judgment :=
  rfl

@[simp] theorem NamespaceMap.mul_rule (later earlier : NamespaceMap) :
    (later * earlier).rule = later.rule ∘ earlier.rule :=
  rfl

/-- The calculus-language action of a core symbol map together with a renaming
of the calculus' own namespaces. -/
def layerSymbols (symbols : LanguageDefSymbolMap) (names : NamespaceMap) :
    CalculusLanguageSymbols where
  toLanguageDefSymbolMap := symbols
  judgment := names.judgment
  rule := names.rule

/-- A renaming of the namespaces alone, over an unchanged core. -/
abbrev namespaceSymbols (names : NamespaceMap) : CalculusLanguageSymbols :=
  layerSymbols LanguageDefSymbolMap.id names

@[simp] theorem layerSymbols_toLanguageDefSymbolMap (symbols : LanguageDefSymbolMap)
    (names : NamespaceMap) : (layerSymbols symbols names).toLanguageDefSymbolMap = symbols :=
  rfl

@[simp] theorem layerSymbols_judgment (symbols : LanguageDefSymbolMap) (names : NamespaceMap) :
    (layerSymbols symbols names).judgment = names.judgment :=
  rfl

@[simp] theorem layerSymbols_rule (symbols : LanguageDefSymbolMap) (names : NamespaceMap) :
    (layerSymbols symbols names).rule = names.rule :=
  rfl

/-- Without a renaming, the layer action is the core action. -/
@[simp] theorem layerSymbols_one (symbols : LanguageDefSymbolMap) :
    layerSymbols symbols 1 = coreSymbols symbols :=
  rfl

@[simp] theorem namespaceSymbols_one : namespaceSymbols 1 = CalculusLanguageSymbols.id :=
  rfl

/-- Layer actions compose: core maps in order, renamings as functions. -/
theorem layerSymbols_comp (first second : LanguageDefSymbolMap)
    (firstNames secondNames : NamespaceMap) :
    (layerSymbols first firstNames).comp (layerSymbols second secondNames) =
      layerSymbols (first.comp second) (secondNames * firstNames) :=
  rfl

/-- **Renaming commutes with core transport.**  The two act on disjoint
namespaces: a layer action is a renaming followed by a core action, and also a
core action followed by a renaming. -/
theorem layerSymbols_eq_rename_comp (symbols : LanguageDefSymbolMap) (names : NamespaceMap) :
    layerSymbols symbols names = (namespaceSymbols names).comp (coreSymbols symbols) := by
  ext name <;> rfl

theorem layerSymbols_eq_comp_rename (symbols : LanguageDefSymbolMap) (names : NamespaceMap) :
    layerSymbols symbols names = (coreSymbols symbols).comp (namespaceSymbols names) := by
  ext name <;> rfl

private theorem list_map_eq_self {α : Type*} (function : α → α) (elements : List α)
    (fixed : ∀ element ∈ elements, function element = element) :
    elements.map function = elements := by
  calc
    elements.map function = elements.map _root_.id := List.map_congr_left fixed
    _ = elements := List.map_id elements

/-- Reindexing a proof calculus along the identity action is the identity. -/
@[simp] theorem reindexProofCalculus_id (calculus : ProofCalculus) :
    reindexProofCalculus CalculusLanguageSymbols.id calculus = calculus := by
  cases calculus with
  | mk judgments rules conversion =>
      simp only [reindexProofCalculus]
      congr 1
      · exact list_map_eq_self _ _ fun judgment _ => mapJudgmentDecl_id judgment
      · exact list_map_eq_self _ _ fun rule _ => mapRuleSchema_id rule
      · cases conversion <;> simp

/-- Reindexing along a composite action is reindexing in two stages. -/
theorem reindexProofCalculus_comp (first second : CalculusLanguageSymbols)
    (calculus : ProofCalculus) :
    reindexProofCalculus (first.comp second) calculus =
      reindexProofCalculus second (reindexProofCalculus first calculus) := by
  cases calculus with
  | mk judgments rules conversion =>
      simp only [reindexProofCalculus, List.map_map, Option.map_map, ProofCalculus.mk.injEq]
      refine ⟨?_, ?_, ?_⟩
      · exact List.map_congr_left fun judgment _ =>
          mapJudgmentDecl_comp first second judgment
      · exact List.map_congr_left fun rule _ => mapRuleSchema_comp first second rule
      · cases conversion <;> simp [mapConversionDecl_comp]

/-- Reindexing is a homomorphism of the authored partial append: it keeps
the presence of a conversion root, so both sides fail together. -/
theorem append?_reindexProofCalculus (symbols : CalculusLanguageSymbols)
    (first second : ProofCalculus) :
    (reindexProofCalculus symbols first).append? (reindexProofCalculus symbols second) =
      (first.append? second).map (reindexProofCalculus symbols) := by
  cases first with
  | mk firstJudgments firstRules firstConversion =>
    cases second with
    | mk secondJudgments secondRules secondConversion =>
      cases firstConversion <;> cases secondConversion <;>
        simp [ProofCalculus.append?, reindexProofCalculus]

/-- **Proof calculi move along core morphisms.**  A structural morphism of
validated cores renames the core constructors inside every judgment argument
of every rule and fixes judgment heads, rule identifiers and the conversion
root. -/
def calculusTransport :
    CompositionalTransport (calculusLayer.reindex ValidatedLanguageDef.language) where
  map morphism := reindexProofCalculus (coreSymbols morphism.symbols)
  map_id _ calculus := reindexProofCalculus_id calculus
  map_comp earlier later calculus :=
    reindexProofCalculus_comp (coreSymbols earlier.symbols) (coreSymbols later.symbols)
      calculus
  map_empty _ := rfl
  map_merge morphism first second :=
    append?_reindexProofCalculus (coreSymbols morphism.symbols) first second

/-- **Proof calculi move along core morphisms and namespace renamings
together.**  A morphism of the base pairs a structural morphism of validated
cores with a renaming of the calculus' own judgment heads and rule
identifiers; the monoid of renamings is a category with one object. -/
def layerTransport :
    CompositionalTransport
      (calculusLayer.reindex fun base : ValidatedLanguageDef × SingleObj NamespaceMap =>
        base.1.language) where
  map morphism := reindexProofCalculus (layerSymbols morphism.1.symbols morphism.2)
  map_id _ calculus := reindexProofCalculus_id calculus
  map_comp earlier later calculus :=
    reindexProofCalculus_comp (layerSymbols earlier.1.symbols earlier.2)
      (layerSymbols later.1.symbols later.2) calculus
  map_empty _ := rfl
  map_merge morphism first second :=
    append?_reindexProofCalculus (layerSymbols morphism.1.symbols morphism.2) first second

/-- Along the identity renaming, layer transport is core transport. -/
theorem layerTransport_map_core {source target : ValidatedLanguageDef} (morphism : source ⟶ target)
    (calculus : ProofCalculus) :
    layerTransport.map (source := (source, SingleObj.star NamespaceMap))
        (target := (target, SingleObj.star NamespaceMap)) (morphism, 𝟙 _) calculus =
      calculusTransport.map morphism calculus :=
  rfl

/-! ### What core transport leaves fixed -/

section Fixed

variable (symbols : LanguageDefSymbolMap)

@[simp] theorem mapJudgmentDecl_coreSymbols (judgment : JudgmentDecl) :
    mapJudgmentDecl (coreSymbols symbols) judgment = judgment := by
  cases judgment
  rfl

@[simp] theorem mapConversionDecl_coreSymbols (conversion : ConversionDecl) :
    mapConversionDecl (coreSymbols symbols) conversion = conversion := by
  cases conversion
  rfl

@[simp] theorem mapRuleSchema_coreSymbols_id (rule : RuleSchema) :
    (mapRuleSchema (coreSymbols symbols) rule).id = rule.id :=
  rfl

@[simp] theorem reindex_coreSymbols_judgments (calculus : ProofCalculus) :
    (reindexProofCalculus (coreSymbols symbols) calculus).judgments =
      calculus.judgments :=
  list_map_eq_self _ _ fun judgment _ => mapJudgmentDecl_coreSymbols symbols judgment

@[simp] theorem reindex_coreSymbols_conversion (calculus : ProofCalculus) :
    (reindexProofCalculus (coreSymbols symbols) calculus).conversion =
      calculus.conversion := by
  cases calculus with
  | mk judgments rules conversion =>
      cases conversion <;> simp [reindexProofCalculus]

@[simp] theorem reindex_coreSymbols_rules (calculus : ProofCalculus) :
    (reindexProofCalculus (coreSymbols symbols) calculus).rules =
      calculus.rules.map (mapRuleSchema (coreSymbols symbols)) :=
  rfl

@[simp] theorem reindex_coreSymbols_ruleIds (calculus : ProofCalculus) :
    (reindexProofCalculus (coreSymbols symbols) calculus).rules.map RuleSchema.id =
      calculus.rules.map RuleSchema.id := by
  simp [List.map_map, Function.comp_def]

end Fixed

/-! ### Pattern invariants of constructor renaming -/

section PatternInvariants

variable (symbols : LanguageDefSymbolMap)

theorem metavariableOccurrences_mapPattern (pattern : Pattern) :
    ∀ depth, patternMetavariableOccurrencesAt depth (mapPattern symbols pattern) =
      patternMetavariableOccurrencesAt depth pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro depth; simp [mapPattern, patternMetavariableOccurrencesAt]
  | hfvar name => intro depth; simp [mapPattern, patternMetavariableOccurrencesAt]
  | happly constructor arguments inductionHypothesis =>
      intro depth
      simp only [mapPattern, mapPatternList_eq_map, patternMetavariableOccurrencesAt]
      induction arguments with
      | nil => rfl
      | cons argument arguments tailHypothesis =>
          simp only [List.map_cons, patternsMetavariableOccurrencesAt]
          rw [inductionHypothesis argument (by simp) depth,
            tailHypothesis (fun item member => inductionHypothesis item (by simp [member]))]
  | hlambda binder body inductionHypothesis =>
      intro depth
      simp only [mapPattern, patternMetavariableOccurrencesAt]
      exact inductionHypothesis (depth + 1)
  | hmultiLambda arity binders body inductionHypothesis =>
      intro depth
      simp only [mapPattern, patternMetavariableOccurrencesAt]
      exact inductionHypothesis (depth + arity)
  | hsubst body replacement bodyHypothesis replacementHypothesis =>
      intro depth
      simp only [mapPattern, patternMetavariableOccurrencesAt]
      rw [bodyHypothesis (depth + 1), replacementHypothesis depth]
  | hcollection collectionType elements rest inductionHypothesis =>
      intro depth
      simp only [mapPattern, mapPatternList_eq_map, patternMetavariableOccurrencesAt]
      induction elements with
      | nil => rfl
      | cons element elements tailHypothesis =>
          simp only [List.map_cons, patternsMetavariableOccurrencesAt]
          rw [inductionHypothesis element (by simp) depth,
            tailHypothesis (fun item member => inductionHypothesis item (by simp [member]))]

theorem noCollectionRest_mapPattern (pattern : Pattern) :
    patternHasNoCollectionRest (mapPattern symbols pattern) =
      patternHasNoCollectionRest pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => simp [mapPattern, patternHasNoCollectionRest]
  | hfvar name => simp [mapPattern, patternHasNoCollectionRest]
  | happly constructor arguments inductionHypothesis =>
      simp only [mapPattern, mapPatternList_eq_map, patternHasNoCollectionRest]
      induction arguments with
      | nil => rfl
      | cons argument arguments tailHypothesis =>
          simp only [List.map_cons, patternsHaveNoCollectionRest]
          rw [inductionHypothesis argument (by simp),
            tailHypothesis (fun item member => inductionHypothesis item (by simp [member]))]
  | hlambda binder body inductionHypothesis =>
      simp only [mapPattern, patternHasNoCollectionRest]
      exact inductionHypothesis
  | hmultiLambda arity binders body inductionHypothesis =>
      simp only [mapPattern, patternHasNoCollectionRest]
      exact inductionHypothesis
  | hsubst body replacement bodyHypothesis replacementHypothesis =>
      simp only [mapPattern, patternHasNoCollectionRest]
      rw [bodyHypothesis, replacementHypothesis]
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [mapPattern, mapPatternList_eq_map, patternHasNoCollectionRest]
      congr 1
      induction elements with
      | nil => rfl
      | cons element elements tailHypothesis =>
          simp only [List.map_cons, patternsHaveNoCollectionRest]
          rw [inductionHypothesis element (by simp),
            tailHypothesis (fun item member => inductionHypothesis item (by simp [member]))]

/-! The same invariants for judgment patterns.  None of them reads the outer
head, so they hold for every calculus-language action, renamings of judgment
heads included. -/

theorem metavariableOccurrences_mapJudgmentPattern (calculusSymbols : CalculusLanguageSymbols)
    (pattern : Pattern) (depth : Nat) :
    patternMetavariableOccurrencesAt depth (mapJudgmentPattern calculusSymbols pattern) =
      patternMetavariableOccurrencesAt depth pattern := by
  cases pattern with
  | apply head arguments =>
      have inner := metavariableOccurrences_mapPattern calculusSymbols.toLanguageDefSymbolMap
        (.apply head arguments) depth
      simpa [mapJudgmentPattern, mapPattern, mapPatternList_eq_map,
        patternMetavariableOccurrencesAt] using inner
  | bvar index =>
      exact metavariableOccurrences_mapPattern calculusSymbols.toLanguageDefSymbolMap _ depth
  | fvar name =>
      exact metavariableOccurrences_mapPattern calculusSymbols.toLanguageDefSymbolMap _ depth
  | lambda binder body =>
      exact metavariableOccurrences_mapPattern calculusSymbols.toLanguageDefSymbolMap _ depth
  | multiLambda arity binders body =>
      exact metavariableOccurrences_mapPattern calculusSymbols.toLanguageDefSymbolMap _ depth
  | subst body replacement =>
      exact metavariableOccurrences_mapPattern calculusSymbols.toLanguageDefSymbolMap _ depth
  | collection collectionType elements rest =>
      exact metavariableOccurrences_mapPattern calculusSymbols.toLanguageDefSymbolMap _ depth

theorem metavariableOccurrences_mapJudgmentPatterns (calculusSymbols : CalculusLanguageSymbols)
    (patterns : List Pattern) (depth : Nat) :
    patternsMetavariableOccurrencesAt depth (patterns.map (mapJudgmentPattern calculusSymbols)) =
      patternsMetavariableOccurrencesAt depth patterns := by
  induction patterns with
  | nil => rfl
  | cons pattern patterns inductionHypothesis =>
      simp only [List.map_cons, patternsMetavariableOccurrencesAt]
      rw [metavariableOccurrences_mapJudgmentPattern, inductionHypothesis]

theorem isWellScoped_mapJudgmentPattern (calculusSymbols : CalculusLanguageSymbols)
    (pattern : Pattern) :
    (mapJudgmentPattern calculusSymbols pattern).isWellScoped = pattern.isWellScoped := by
  cases pattern with
  | apply head arguments =>
      have inner := isWellScopedAt_mapPattern calculusSymbols.toLanguageDefSymbolMap
        (.apply head arguments) 0
      simpa [mapJudgmentPattern, mapPattern, mapPatternList_eq_map,
        Pattern.isWellScoped, Pattern.isWellScopedAt] using inner
  | bvar index => exact isWellScopedAt_mapPattern calculusSymbols.toLanguageDefSymbolMap _ 0
  | fvar name => exact isWellScopedAt_mapPattern calculusSymbols.toLanguageDefSymbolMap _ 0
  | lambda binder body =>
      exact isWellScopedAt_mapPattern calculusSymbols.toLanguageDefSymbolMap _ 0
  | multiLambda arity binders body =>
      exact isWellScopedAt_mapPattern calculusSymbols.toLanguageDefSymbolMap _ 0
  | subst body replacement =>
      exact isWellScopedAt_mapPattern calculusSymbols.toLanguageDefSymbolMap _ 0
  | collection collectionType elements rest =>
      exact isWellScopedAt_mapPattern calculusSymbols.toLanguageDefSymbolMap _ 0

theorem noCollectionRest_mapJudgmentPattern (calculusSymbols : CalculusLanguageSymbols)
    (pattern : Pattern) :
    patternHasNoCollectionRest (mapJudgmentPattern calculusSymbols pattern) =
      patternHasNoCollectionRest pattern := by
  cases pattern with
  | apply head arguments =>
      have inner := noCollectionRest_mapPattern calculusSymbols.toLanguageDefSymbolMap
        (.apply head arguments)
      simpa [mapJudgmentPattern, mapPattern, mapPatternList_eq_map,
        patternHasNoCollectionRest] using inner
  | bvar index => exact noCollectionRest_mapPattern calculusSymbols.toLanguageDefSymbolMap _
  | fvar name => exact noCollectionRest_mapPattern calculusSymbols.toLanguageDefSymbolMap _
  | lambda binder body =>
      exact noCollectionRest_mapPattern calculusSymbols.toLanguageDefSymbolMap _
  | multiLambda arity binders body =>
      exact noCollectionRest_mapPattern calculusSymbols.toLanguageDefSymbolMap _
  | subst body replacement =>
      exact noCollectionRest_mapPattern calculusSymbols.toLanguageDefSymbolMap _
  | collection collectionType elements rest =>
      exact noCollectionRest_mapPattern calculusSymbols.toLanguageDefSymbolMap _

theorem canonicalBinderMetadata_mapJudgmentPattern (calculusSymbols : CalculusLanguageSymbols)
    (pattern : Pattern) :
    (mapJudgmentPattern calculusSymbols pattern).hasCanonicalBinderMetadata =
      pattern.hasCanonicalBinderMetadata := by
  cases pattern with
  | apply head arguments =>
      have inner := WellSorted.hasCanonicalBinderMetadata_mapPattern
        calculusSymbols.toLanguageDefSymbolMap (.apply head arguments)
      simpa [mapJudgmentPattern, mapPattern, mapPatternList_eq_map,
        Pattern.hasCanonicalBinderMetadata] using inner
  | bvar index =>
      exact WellSorted.hasCanonicalBinderMetadata_mapPattern
        calculusSymbols.toLanguageDefSymbolMap _
  | fvar name =>
      exact WellSorted.hasCanonicalBinderMetadata_mapPattern
        calculusSymbols.toLanguageDefSymbolMap _
  | lambda binder body =>
      exact WellSorted.hasCanonicalBinderMetadata_mapPattern
        calculusSymbols.toLanguageDefSymbolMap _
  | multiLambda arity binders body =>
      exact WellSorted.hasCanonicalBinderMetadata_mapPattern
        calculusSymbols.toLanguageDefSymbolMap _
  | subst body replacement =>
      exact WellSorted.hasCanonicalBinderMetadata_mapPattern
        calculusSymbols.toLanguageDefSymbolMap _
  | collection collectionType elements rest =>
      exact WellSorted.hasCanonicalBinderMetadata_mapPattern
        calculusSymbols.toLanguageDefSymbolMap _

theorem patterns_mapRuleSchema (calculusSymbols : CalculusLanguageSymbols) (rule : RuleSchema) :
    RuleSchema.patterns (mapRuleSchema calculusSymbols rule) =
      (RuleSchema.patterns rule).map (mapJudgmentPattern calculusSymbols) := by
  simp [RuleSchema.patterns, mapRuleSchema]

/-- A calculus-language action keeps every local admission condition of a rule
schema that keeps its identifier nonempty.  The identifier is the only local
datum a renaming touches. -/
theorem isLocallyValid_mapRuleSchema (calculusSymbols : CalculusLanguageSymbols)
    (rule : RuleSchema)
    (keepsNonempty : (calculusSymbols.rule rule.id.value != "") = (rule.id.value != "")) :
    RuleSchema.isLocallyValid (mapRuleSchema calculusSymbols rule) =
      RuleSchema.isLocallyValid rule := by
  have occurrences : RuleSchema.occurrences (mapRuleSchema calculusSymbols rule) =
      RuleSchema.occurrences rule := by
    unfold RuleSchema.occurrences
    rw [patterns_mapRuleSchema, metavariableOccurrences_mapJudgmentPatterns]
  have identifier :
      (mapRuleSchema calculusSymbols rule).id.value = calculusSymbols.rule rule.id.value :=
    rfl
  unfold RuleSchema.isLocallyValid
  simp only [occurrences, patterns_mapRuleSchema, List.all_map, Function.comp_def,
    isWellScoped_mapJudgmentPattern, noCollectionRest_mapJudgmentPattern,
    canonicalBinderMetadata_mapJudgmentPattern]
  rw [identifier, keepsNonempty]
  rfl

/-- A locally valid rule schema has a nonempty identifier. -/
theorem id_nonempty_of_isLocallyValid {rule : RuleSchema}
    (valid : RuleSchema.isLocallyValid rule = true) : rule.id.value ≠ "" := by
  unfold RuleSchema.isLocallyValid at valid
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at valid
  exact valid.1.1.1.1.1.1.1

end PatternInvariants

/-! ### Constructor arities along typing morphisms -/

/-- In a list with duplicate-free labels, filtering at the label of a member
selects exactly that member. -/
theorem filter_label_eq_singleton {terms : List GrammarRule}
    (nodup : (terms.map (·.label)).Nodup) {rule : GrammarRule}
    (member : rule ∈ terms) {label : String} (labelled : rule.label = label) :
    terms.filter (fun declaration => declaration.label == label) = [rule] := by
  induction terms with
  | nil => cases member
  | cons head tail inductionHypothesis =>
      rw [List.map_cons, List.nodup_cons] at nodup
      rcases List.mem_cons.mp member with equal | inTail
      · subst equal
        have tailEmpty : tail.filter (fun declaration => declaration.label == label) = [] := by
          rw [List.filter_eq_nil_iff]
          intro declaration declarationMember matching
          have sameLabel : declaration.label = label := by simpa using matching
          exact nodup.1 (labelled ▸ sameLabel ▸ List.mem_map_of_mem declarationMember)
        simp [labelled, tailEmpty]
      · have headDifferent : head.label ≠ label := by
          intro sameLabel
          exact nodup.1 (sameLabel ▸ labelled ▸ List.mem_map_of_mem inTail)
        simp [headDifferent, inductionHypothesis nodup.2 inTail]

/-- A typing morphism carries a declared constructor arity to a declared
constructor arity of the target. -/
theorem languageHasConstructorArity_map {source target : ValidatedLanguageDef}
    (morphism : TypingMorphism source target) {head : String} {arity : Nat}
    (found : languageHasConstructorArity source.language head arity = true) :
    languageHasConstructorArity target.language (morphism.symbols.constructor head) arity =
      true := by
  unfold languageHasConstructorArity at found ⊢
  split at found
  · rename_i declaration filtered
    have selected : declaration ∈ source.language.terms.filter
        (fun candidate => candidate.label == head) := by
      rw [filtered]
      exact List.mem_singleton_self declaration
    obtain ⟨member, labelMatches⟩ := List.mem_filter.mp selected
    have label : declaration.label = head := by simpa using labelMatches
    obtain ⟨targetRule, targetMember, targetLabel, _, targetParams⟩ :=
      morphism.mapsTerms declaration member
    have unique := filter_label_eq_singleton
      (LanguageDef.constructorLabels_nodup_of_validate_eq_nil target.language target.valid)
      targetMember (label := morphism.symbols.constructor head) (by rw [targetLabel, label])
    rw [unique]
    simpa [targetParams] using found
  · simp at found

theorem fixedConstructorListsValid_eq_all (language : LanguageDef) (patterns : List Pattern) :
    fixedConstructorListsValid language patterns =
      patterns.all (fixedConstructorsValid language) := by
  induction patterns with
  | nil => simp [fixedConstructorListsValid]
  | cons pattern patterns inductionHypothesis =>
      simp [fixedConstructorListsValid, inductionHypothesis]

/-- Every fixed constructor occurrence of a schema fragment stays declared,
at its authored arity, after renaming along a typing morphism. -/
theorem fixedConstructorsValid_map {source target : ValidatedLanguageDef}
    (morphism : TypingMorphism source target) (pattern : Pattern)
    (valid : fixedConstructorsValid source.language pattern = true) :
    fixedConstructorsValid target.language (mapPattern morphism.symbols pattern) = true := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => simp [mapPattern, fixedConstructorsValid]
  | hfvar name => simp [mapPattern, fixedConstructorsValid]
  | happly constructor arguments inductionHypothesis =>
      simp only [fixedConstructorsValid, Bool.and_eq_true,
        fixedConstructorListsValid_eq_all, List.all_eq_true] at valid
      simp only [mapPattern, mapPatternList_eq_map, fixedConstructorsValid,
        Bool.and_eq_true, fixedConstructorListsValid_eq_all, List.all_eq_true,
        List.length_map, List.mem_map]
      refine ⟨languageHasConstructorArity_map morphism valid.1, ?_⟩
      rintro mapped ⟨argument, member, rfl⟩
      exact inductionHypothesis argument member (valid.2 argument member)
  | hlambda binder body inductionHypothesis =>
      simp only [fixedConstructorsValid] at valid
      simpa [mapPattern, fixedConstructorsValid] using inductionHypothesis valid
  | hmultiLambda arity binders body inductionHypothesis =>
      simp only [fixedConstructorsValid] at valid
      simpa [mapPattern, fixedConstructorsValid] using inductionHypothesis valid
  | hsubst body replacement bodyHypothesis replacementHypothesis =>
      simp only [fixedConstructorsValid, Bool.and_eq_true] at valid
      simp only [mapPattern, fixedConstructorsValid, Bool.and_eq_true]
      exact ⟨bodyHypothesis valid.1, replacementHypothesis valid.2⟩
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [fixedConstructorsValid, fixedConstructorListsValid_eq_all,
        List.all_eq_true] at valid
      simp only [mapPattern, mapPatternList_eq_map, fixedConstructorsValid,
        fixedConstructorListsValid_eq_all, List.all_eq_true, List.mem_map]
      rintro mapped ⟨element, member, rfl⟩
      exact inductionHypothesis element member (valid element member)

/-! ### Admission along core morphisms and renamings -/

/-- No constructor of a core carries a judgment head of a calculus. -/
def HeadsFresh (language : LanguageDef) (calculus : ProofCalculus) : Prop :=
  ∀ judgment ∈ calculus.judgments, ∀ declaration ∈ language.terms,
    declaration.label ≠ judgment.head

/-- **Legal renamings.**  A renaming keeps an admitted calculus admitted over a
core when it keeps judgment heads apart and rule identifiers apart, keeps rule
identifiers nonempty, and sends every judgment head to a nonempty, unreserved
head that no constructor of the core carries. -/
structure NamesValid (language : LanguageDef) (names : NamespaceMap)
    (calculus : ProofCalculus) : Prop where
  headsApart : ∀ first ∈ calculus.judgments.map JudgmentDecl.head,
    ∀ second ∈ calculus.judgments.map JudgmentDecl.head,
      names.judgment first = names.judgment second → first = second
  idsApart : ∀ first ∈ calculus.rules.map RuleSchema.id,
    ∀ second ∈ calculus.rules.map RuleSchema.id,
      names.rule first.value = names.rule second.value → first = second
  idsNonempty : ∀ id ∈ calculus.rules.map RuleSchema.id, names.rule id.value ≠ ""
  headsLegal : ∀ head ∈ calculus.judgments.map JudgmentDecl.head,
    names.judgment head ≠ "" ∧
      names.judgment head ∉ [Pattern.zipHead, Pattern.mapHead, Pattern.evalHead]
  fresh : HeadsFresh language (reindexProofCalculus (namespaceSymbols names) calculus)

/-- Judgment lookup reads only the judgment rows. -/
theorem lookupJudgment?_extend (first second : LanguageDef) (calculus : ProofCalculus)
    (head : String) (arity : Nat) :
    (CalculusLanguageDef.extend first calculus).lookupJudgment? head arity =
      (CalculusLanguageDef.extend second calculus).lookupJudgment? head arity :=
  rfl

/-- Core transport keeps every judgment lookup. -/
theorem lookupJudgment?_reindex (first second : LanguageDef) (symbols : LanguageDefSymbolMap)
    (calculus : ProofCalculus) (head : String) (arity : Nat) :
    (CalculusLanguageDef.extend first
        (reindexProofCalculus (coreSymbols symbols) calculus)).lookupJudgment? head arity =
      (CalculusLanguageDef.extend second calculus).lookupJudgment? head arity := by
  unfold CalculusLanguageDef.lookupJudgment?
  simp only [CalculusLanguageDef.extend_judgments, reindex_coreSymbols_judgments]

/-- A renaming that keeps judgment heads apart resolves the renamed head of
every declared judgment exactly when the original head resolves. -/
theorem lookupJudgment?_layer_isSome (first second : LanguageDef)
    (symbols : LanguageDefSymbolMap) (names : NamespaceMap) (calculus : ProofCalculus)
    (apart : ∀ first ∈ calculus.judgments.map JudgmentDecl.head,
      ∀ second ∈ calculus.judgments.map JudgmentDecl.head,
        names.judgment first = names.judgment second → first = second)
    {head : String} (declared : head ∈ calculus.judgments.map JudgmentDecl.head)
    (arity : Nat) :
    ((CalculusLanguageDef.extend first
        (reindexProofCalculus (layerSymbols symbols names) calculus)).lookupJudgment?
          (names.judgment head) arity).isSome =
      ((CalculusLanguageDef.extend second calculus).lookupJudgment? head arity).isSome := by
  have sameFilter :
      ((calculus.judgments.map (mapJudgmentDecl (layerSymbols symbols names))).filter
          fun declaration =>
            declaration.head == names.judgment head && declaration.arity == arity) =
        (calculus.judgments.filter fun declaration =>
          declaration.head == head && declaration.arity == arity).map
            (mapJudgmentDecl (layerSymbols symbols names)) := by
    rw [List.filter_map]
    congr 1
    apply List.filter_congr
    intro declaration member
    have sameHead :
        (names.judgment declaration.head == names.judgment head) = (declaration.head == head) := by
      by_cases equal : declaration.head = head
      · simp [equal]
      · have renamedApart : names.judgment declaration.head ≠ names.judgment head :=
          fun renamedEqual =>
            equal (apart _ (List.mem_map_of_mem member) _ declared renamedEqual)
        simp [equal, renamedApart]
    simp [mapJudgmentDecl, sameHead]
  unfold CalculusLanguageDef.lookupJudgment?
  simp only [CalculusLanguageDef.extend_judgments, reindexProofCalculus]
  rw [sameFilter]
  generalize (calculus.judgments.filter fun declaration =>
      declaration.head == head && declaration.arity == arity) = found
  rcases found with _ | ⟨first, _ | ⟨second, rest⟩⟩ <;> rfl

section Admission

variable {source target : ValidatedLanguageDef} (morphism : TypingMorphism source target)
  {calculus : ProofCalculus}

private theorem judgmentSchemaValid_layer (names : NamespaceMap)
    (apart : ∀ first ∈ calculus.judgments.map JudgmentDecl.head,
      ∀ second ∈ calculus.judgments.map JudgmentDecl.head,
        names.judgment first = names.judgment second → first = second)
    {pattern : Pattern}
    (valid : (CalculusLanguageDef.extend source.language calculus).judgmentSchemaValid
      pattern = true) :
    (CalculusLanguageDef.extend target.language
        (reindexProofCalculus (layerSymbols morphism.symbols names) calculus)).judgmentSchemaValid
      (mapJudgmentPattern (layerSymbols morphism.symbols names) pattern) = true := by
  cases pattern with
  | apply head arguments =>
      simp only [CalculusLanguageDef.judgmentSchemaValid, Bool.and_eq_true] at valid
      simp only [mapJudgmentPattern, layerSymbols_judgment, layerSymbols_toLanguageDefSymbolMap,
        CalculusLanguageDef.judgmentSchemaValid, Bool.and_eq_true, List.length_map]
      refine ⟨?_, ?_⟩
      · rw [lookupJudgment?_layer_isSome target.language source.language morphism.symbols names
          calculus apart (mem_judgmentHeads_of_lookup valid.1)]
        exact valid.1
      · simp only [fixedConstructorListsValid_eq_all, List.all_eq_true, List.mem_map] at valid ⊢
        rintro mapped ⟨argument, member, rfl⟩
        exact fixedConstructorsValid_map morphism argument (valid.2 argument member)
  | bvar index => simp [CalculusLanguageDef.judgmentSchemaValid] at valid
  | fvar name => simp [CalculusLanguageDef.judgmentSchemaValid] at valid
  | lambda binder body => simp [CalculusLanguageDef.judgmentSchemaValid] at valid
  | multiLambda arity binders body =>
      simp [CalculusLanguageDef.judgmentSchemaValid] at valid
  | subst body replacement => simp [CalculusLanguageDef.judgmentSchemaValid] at valid
  | collection collectionType elements rest =>
      simp [CalculusLanguageDef.judgmentSchemaValid] at valid

private theorem isValidIn_layer (names : NamespaceMap)
    (apart : ∀ first ∈ calculus.judgments.map JudgmentDecl.head,
      ∀ second ∈ calculus.judgments.map JudgmentDecl.head,
        names.judgment first = names.judgment second → first = second)
    {rule : RuleSchema}
    (keepsNonempty : (names.rule rule.id.value != "") = (rule.id.value != ""))
    (valid : RuleSchema.isValidIn (CalculusLanguageDef.extend source.language calculus)
      rule = true) :
    RuleSchema.isValidIn
        (CalculusLanguageDef.extend target.language
          (reindexProofCalculus (layerSymbols morphism.symbols names) calculus))
        (mapRuleSchema (layerSymbols morphism.symbols names) rule) = true := by
  simp only [RuleSchema.isValidIn, Bool.and_eq_true, List.all_eq_true] at valid ⊢
  refine ⟨?_, ?_, ?_⟩
  · rw [isLocallyValid_mapRuleSchema _ _ keepsNonempty]
    exact valid.1
  · intro mapped member
    rw [patterns_mapRuleSchema, List.mem_map] at member
    obtain ⟨pattern, patternMember, rfl⟩ := member
    exact judgmentSchemaValid_layer morphism names apart (valid.2.1 pattern patternMember)
  · exact valid.2.2

/-- **Admission moves along a core morphism and a renaming exactly when the
renaming is legal for the target core.**  Renaming the core constructors inside
judgment arguments and renaming the calculus' own namespaces keep every local,
signature, rule and conversion condition of an admitted calculus; the
obligations are the ones a renaming can break. -/
theorem admitted_layer_iff (names : NamespaceMap)
    (admitted : (CalculusLanguageDef.extend source.language calculus).isValid = true) :
    (CalculusLanguageDef.extend target.language
        (reindexProofCalculus (layerSymbols morphism.symbols names) calculus)).isValid = true ↔
      NamesValid target.language names calculus := by
  have renamedHeads :
      (reindexProofCalculus (layerSymbols morphism.symbols names) calculus).judgments.map
          JudgmentDecl.head =
        (calculus.judgments.map JudgmentDecl.head).map names.judgment := by
    show List.map JudgmentDecl.head
        (calculus.judgments.map (mapJudgmentDecl (layerSymbols morphism.symbols names))) = _
    rw [List.map_map, List.map_map]
    rfl
  have renamedIds :
      (reindexProofCalculus (layerSymbols morphism.symbols names) calculus).rules.map
          RuleSchema.id =
        (calculus.rules.map RuleSchema.id).map fun id => ⟨names.rule id.value⟩ := by
    show List.map RuleSchema.id
        (calculus.rules.map (mapRuleSchema (layerSymbols morphism.symbols names))) = _
    rw [List.map_map, List.map_map]
    rfl
  simp only [CalculusLanguageDef.isValid, CalculusLanguageDef.hasValidLocalRules,
    CalculusLanguageDef.judgmentSignatureValid, Bool.and_eq_true, List.all_eq_true,
    CalculusLanguageDef.judgmentHeads, CalculusLanguageDef.ruleIds,
    CalculusLanguageDef.conversionDeclarationValid] at admitted ⊢
  obtain ⟨⟨⟨⟨⟨_, sourceLocal⟩, sourceIds⟩, ⟨⟨sourceNonempty, sourceUnique⟩, sourceHeads⟩⟩,
    sourceRules⟩, sourceConversion⟩ := admitted
  simp only [CalculusLanguageDef.extend_judgments, CalculusLanguageDef.extend_rules,
    CalculusLanguageDef.extend_conversion, CalculusLanguageDef.extend_toLanguageDef] at *
  constructor
  · rintro ⟨⟨⟨⟨⟨_, targetLocal⟩, targetIds⟩, ⟨⟨targetNonempty, targetUnique⟩, targetHeads⟩⟩,
      _⟩, _⟩
    rw [eraseDups_length_iff_nodup, renamedIds] at targetIds
    rw [eraseDups_length_iff_nodup, renamedHeads] at targetUnique
    rw [renamedHeads] at targetHeads
    refine ⟨fun first firstMember second secondMember same =>
        List.inj_on_of_nodup_map targetUnique firstMember secondMember same,
      fun first firstMember second secondMember same =>
        List.inj_on_of_nodup_map targetIds firstMember secondMember (by rw [same]),
      fun id idMember => ?_, fun head headMember => ⟨?_, ?_⟩, ?_⟩
    · obtain ⟨rule, ruleMember, rfl⟩ := List.mem_map.mp idMember
      exact id_nonempty_of_isLocallyValid (targetLocal _ (List.mem_map_of_mem ruleMember))
    · obtain ⟨judgment, judgmentMember, rfl⟩ := List.mem_map.mp headMember
      have nonempty := targetNonempty _
        (List.mem_map_of_mem (f := mapJudgmentDecl (layerSymbols morphism.symbols names))
          judgmentMember)
      simpa [mapJudgmentDecl] using nonempty
    · simpa using (targetHeads _ (List.mem_map_of_mem headMember)).2
    · intro judgment judgmentMember declaration declarationMember sameHead
      obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp judgmentMember
      have avoided := (targetHeads _
        (List.mem_map_of_mem (List.mem_map_of_mem (f := JudgmentDecl.head) originalMember))).1
      simp only [Bool.not_eq_true', List.any_eq_false, beq_iff_eq] at avoided
      exact avoided declaration declarationMember sameHead
  · intro valid
    have keeps : ∀ rule ∈ calculus.rules,
        (names.rule rule.id.value != "") = (rule.id.value != "") := by
      intro rule ruleMember
      have renamed := valid.idsNonempty rule.id (List.mem_map_of_mem ruleMember)
      have original := id_nonempty_of_isLocallyValid (sourceLocal rule ruleMember)
      exact (bne_iff_ne.mpr renamed).trans (bne_iff_ne.mpr original).symm
    rw [eraseDups_length_iff_nodup] at sourceIds sourceUnique
    refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ⟨⟨?_, ?_⟩, ?_⟩⟩, ?_⟩, ?_⟩
    · simp [target.valid]
    · intro mapped member
      obtain ⟨rule, ruleMember, rfl⟩ := List.mem_map.mp member
      rw [isLocallyValid_mapRuleSchema _ _ (keeps rule ruleMember)]
      exact sourceLocal rule ruleMember
    · rw [eraseDups_length_iff_nodup, renamedIds]
      exact sourceIds.map_on fun first firstMember second secondMember same =>
        valid.idsApart first firstMember second secondMember (RuleId.mk.inj same)
    · intro mapped member
      obtain ⟨judgment, judgmentMember, rfl⟩ := List.mem_map.mp member
      simpa [mapJudgmentDecl] using
        (valid.headsLegal _ (List.mem_map_of_mem judgmentMember)).1
    · rw [eraseDups_length_iff_nodup, renamedHeads]
      exact sourceUnique.map_on valid.headsApart
    · intro head headMember
      rw [renamedHeads] at headMember
      obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp headMember
      refine ⟨?_, ?_⟩
      · have noLabel : (target.language.terms.any fun declaration =>
            declaration.label == names.judgment original) = false := by
          rw [List.any_eq_false]
          intro declaration declarationMember matching
          obtain ⟨judgment, judgmentMember, rfl⟩ := List.mem_map.mp originalMember
          exact valid.fresh _ (List.mem_map_of_mem judgmentMember) declaration
            declarationMember (beq_iff_eq.mp matching)
        simp [noLabel]
      · simpa using (valid.headsLegal original originalMember).2
    · intro mapped member
      obtain ⟨rule, ruleMember, rfl⟩ := List.mem_map.mp member
      exact isValidIn_layer morphism names valid.headsApart (keeps rule ruleMember)
        (sourceRules rule ruleMember)
    · cases conversionEquation : calculus.conversion with
      | none => simp [reindexProofCalculus, conversionEquation]
      | some declaration =>
          rw [conversionEquation] at sourceConversion
          simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at sourceConversion
          have declared := mem_judgmentHeads_of_lookup sourceConversion.2
          have renamedConversion :
              (reindexProofCalculus (layerSymbols morphism.symbols names) calculus).conversion =
                some (mapConversionDecl (layerSymbols morphism.symbols names) declaration) := by
            simp [reindexProofCalculus, conversionEquation]
          rw [renamedConversion]
          simp only [mapConversionDecl, layerSymbols_judgment, Bool.and_eq_true, bne_iff_ne,
            ne_eq]
          refine ⟨⟨(valid.headsLegal _ declared).1, sourceConversion.1.2⟩, ?_⟩
          rw [lookupJudgment?_layer_isSome target.language source.language morphism.symbols
            names calculus valid.headsApart declared]
          exact sourceConversion.2

/-- A calculus admitted over a core has heads fresh for that same core. -/
theorem headsFresh_of_admitted {language : LanguageDef}
    (admitted : (CalculusLanguageDef.extend language calculus).isValid = true) :
    HeadsFresh language calculus := by
  simp only [CalculusLanguageDef.isValid, CalculusLanguageDef.judgmentSignatureValid,
    Bool.and_eq_true, List.all_eq_true, CalculusLanguageDef.judgmentHeads] at admitted
  intro judgment judgmentMember declaration declarationMember sameHead
  have avoided := admitted.1.1.2.2 judgment.head (List.mem_map_of_mem judgmentMember)
  simp only [CalculusLanguageDef.extend_toLanguageDef, Bool.not_eq_true',
    List.any_eq_false, beq_iff_eq] at avoided
  exact avoided.1 declaration declarationMember sameHead

/-- An admitted calculus has nonempty, unreserved judgment heads and nonempty
rule identifiers. -/
theorem names_legal_of_admitted {language : LanguageDef}
    (admitted : (CalculusLanguageDef.extend language calculus).isValid = true) :
    (∀ head ∈ calculus.judgments.map JudgmentDecl.head,
        head ≠ "" ∧ head ∉ [Pattern.zipHead, Pattern.mapHead, Pattern.evalHead]) ∧
      ∀ id ∈ calculus.rules.map RuleSchema.id, id.value ≠ "" := by
  simp only [CalculusLanguageDef.isValid, CalculusLanguageDef.hasValidLocalRules,
    CalculusLanguageDef.judgmentSignatureValid, Bool.and_eq_true, List.all_eq_true,
    CalculusLanguageDef.judgmentHeads] at admitted
  obtain ⟨⟨⟨⟨⟨_, locallyValid⟩, _⟩, ⟨⟨nonempty, _⟩, heads⟩⟩, _⟩, _⟩ := admitted
  refine ⟨fun head headMember => ⟨?_, ?_⟩, fun id idMember => ?_⟩
  · obtain ⟨judgment, judgmentMember, rfl⟩ := List.mem_map.mp headMember
    simpa using nonempty judgment judgmentMember
  · simpa using (heads head headMember).2
  · obtain ⟨rule, ruleMember, rfl⟩ := List.mem_map.mp idMember
    exact id_nonempty_of_isLocallyValid (locallyValid rule ruleMember)

/-- Without a renaming, legality is freshness of the original heads. -/
theorem namesValid_one_iff {language language' : LanguageDef}
    (admitted : (CalculusLanguageDef.extend language' calculus).isValid = true) :
    NamesValid language 1 calculus ↔ HeadsFresh language calculus := by
  have unchanged : reindexProofCalculus (namespaceSymbols 1) calculus = calculus := by
    rw [namespaceSymbols_one, reindexProofCalculus_id]
  constructor
  · intro valid
    have fresh := valid.fresh
    rwa [unchanged] at fresh
  · intro fresh
    obtain ⟨legal, idsNonempty⟩ := names_legal_of_admitted admitted
    refine ⟨fun _ _ _ _ same => same, fun first _ second _ same => ?_,
      fun id idMember => idsNonempty id idMember, fun head headMember => legal head headMember,
      ?_⟩
    · exact congrArg RuleId.mk same
    · rw [unchanged]
      exact fresh

/-- **Admission moves along typing morphisms exactly when the judgment heads
stay fresh.**  The identity-renaming case of `admitted_layer_iff`. -/
theorem admitted_reindex_iff
    (admitted : (CalculusLanguageDef.extend source.language calculus).isValid = true) :
    (CalculusLanguageDef.extend target.language
        (reindexProofCalculus (coreSymbols morphism.symbols) calculus)).isValid = true ↔
      HeadsFresh target.language calculus := by
  rw [← layerSymbols_one, admitted_layer_iff morphism 1 admitted, namesValid_one_iff admitted]

/-- **Renaming over one core.**  A renaming keeps a calculus admitted over its
own core exactly when it is legal for that core: the identity-morphism case of
`admitted_layer_iff`. -/
theorem admitted_rename_iff {core : ValidatedLanguageDef} (names : NamespaceMap)
    (admitted : (CalculusLanguageDef.extend core.language calculus).isValid = true) :
    (CalculusLanguageDef.extend core.language
        (reindexProofCalculus (namespaceSymbols names) calculus)).isValid = true ↔
      NamesValid core.language names calculus :=
  admitted_layer_iff (TypingMorphism.id core) names admitted

end Admission

/-! ## Gluing is the join of the fibre -/

section FibreJoin

open ValidatedInferenceExtension

variable {language : LanguageDef}

private theorem find?_append_left (first second : List RuleSchema) {id : RuleId}
    {rule : RuleSchema}
    (found : first.find? (fun candidate => decide (candidate.id = id)) = some rule) :
    (first ++ second).find? (fun candidate => decide (candidate.id = id)) = some rule := by
  rw [List.find?_append, found]
  rfl

private theorem find?_eq_none_of_id_absent {rules : List RuleSchema} {id : RuleId}
    (absent : id ∉ rules.map RuleSchema.id) :
    rules.find? (fun candidate => decide (candidate.id = id)) = none := by
  rw [List.find?_eq_none]
  intro candidate member matching
  exact absent (List.mem_map.mpr ⟨candidate, member, of_decide_eq_true matching⟩)

private theorem id_of_find? {rules : List RuleSchema} {id : RuleId} {rule : RuleSchema}
    (found : rules.find? (fun candidate => decide (candidate.id = id)) = some rule) :
    rule ∈ rules ∧ rule.id = id := by
  have member := List.mem_of_find?_eq_some found
  have matching := List.find?_some found
  exact ⟨member, of_decide_eq_true matching⟩

/-- The glued calculus refines its first component. -/
theorem glue_refines_left (first second : AdmittedCalculus language)
    (compatible : Compatible first.1 second.1) :
    Refines first (glue first second compatible) where
  judgments := fun _ member => List.mem_append_left _ member
  rules := fun id rule found => find?_append_left first.1.rules second.1.rules found
  conversion := fun declaration declared => by
    change (second.1.conversion <|> first.1.conversion) = some declaration
    cases compatible.conversion with
    | inl firstNone => rw [firstNone] at declared; cases declared
    | inr secondNone => rw [secondNone, declared]; rfl

/-- The glued calculus refines its second component. -/
theorem glue_refines_right (first second : AdmittedCalculus language)
    (compatible : Compatible first.1 second.1) :
    Refines second (glue first second compatible) where
  judgments := fun _ member => List.mem_append_right _ member
  rules := fun id rule found => by
    obtain ⟨member, ruleId⟩ := id_of_find? found
    have absent : id ∉ first.1.rules.map RuleSchema.id := by
      intro present
      exact compatible.ruleIds id present (ruleId ▸ List.mem_map_of_mem member)
    change (first.1.rules ++ second.1.rules).find?
      (fun candidate => decide (candidate.id = id)) = some rule
    rw [List.find?_append, find?_eq_none_of_id_absent absent]
    exact found
  conversion := fun declaration declared => by
    change (second.1.conversion <|> first.1.conversion) = some declaration
    rw [declared]
    rfl

/-- **Gluing is the least upper bound in the refinement order of one fibre.**
Every admitted calculus refining both components refines their glue. -/
theorem glue_least (first second : AdmittedCalculus language)
    (compatible : Compatible first.1 second.1) {upper : AdmittedCalculus language}
    (fromFirst : Refines first upper) (fromSecond : Refines second upper) :
    Refines (glue first second compatible) upper where
  judgments := fun declaration member => by
    rcases List.mem_append.mp member with inFirst | inSecond
    · exact fromFirst.judgments declaration inFirst
    · exact fromSecond.judgments declaration inSecond
  rules := fun id rule found => by
    change (first.1.rules ++ second.1.rules).find?
      (fun candidate => decide (candidate.id = id)) = some rule at found
    rw [List.find?_append] at found
    cases inFirst : first.1.rules.find? (fun candidate => decide (candidate.id = id)) with
    | some firstRule =>
        rw [inFirst] at found
        have same : firstRule = rule := Option.some.inj found
        rw [← same]
        exact fromFirst.rules id firstRule inFirst
    | none =>
        rw [inFirst] at found
        exact fromSecond.rules id rule found
  conversion := fun declaration declared => by
    change (second.1.conversion <|> first.1.conversion) = some declaration at declared
    cases inSecond : second.1.conversion with
    | some secondDeclaration =>
        rw [inSecond] at declared
        have same : secondDeclaration = declaration := Option.some.inj declared
        rw [← same]
        exact fromSecond.conversion secondDeclaration inSecond
    | none =>
        rw [inSecond] at declared
        exact fromFirst.conversion declaration declared

end FibreJoin

/-! ## Unions of decorated cores -/

/-- Core transport neither creates nor removes a compatibility obstruction:
only the renamings of judgment heads and rule identifiers matter. -/
theorem compatible_layer_iff (firstSymbols secondSymbols : LanguageDefSymbolMap)
    (firstNames secondNames : NamespaceMap) (first second : ProofCalculus) :
    Compatible (reindexProofCalculus (layerSymbols firstSymbols firstNames) first)
        (reindexProofCalculus (layerSymbols secondSymbols secondNames) second) ↔
      Compatible (reindexProofCalculus (namespaceSymbols firstNames) first)
        (reindexProofCalculus (namespaceSymbols secondNames) second) := by
  constructor
  · intro compatible
    refine ⟨?_, ?_, ?_⟩
    · simpa [reindexProofCalculus, mapJudgmentDecl] using compatible.judgmentHeads
    · simpa [reindexProofCalculus, mapRuleSchema] using compatible.ruleIds
    · simpa [reindexProofCalculus] using compatible.conversion
  · intro compatible
    refine ⟨?_, ?_, ?_⟩
    · simpa [reindexProofCalculus, mapJudgmentDecl] using compatible.judgmentHeads
    · simpa [reindexProofCalculus, mapRuleSchema] using compatible.ruleIds
    · simpa [reindexProofCalculus] using compatible.conversion

/-- Core transport alone leaves compatibility as it is: the identity-renaming
case of `compatible_layer_iff`. -/
theorem compatible_reindex_iff (firstSymbols secondSymbols : LanguageDefSymbolMap)
    (first second : ProofCalculus) :
    Compatible (reindexProofCalculus (coreSymbols firstSymbols) first)
        (reindexProofCalculus (coreSymbols secondSymbols) second) ↔
      Compatible first second := by
  have criterion := compatible_layer_iff firstSymbols secondSymbols 1 1 first second
  simpa only [layerSymbols_one, coreSymbols_id, reindexProofCalculus_id] using criterion

/-- Compatibility is symmetric. -/
theorem compatible_symm {first second : ProofCalculus} (compatible : Compatible first second) :
    Compatible second first where
  judgmentHeads head member present := compatible.judgmentHeads head present member
  ruleIds id member present := compatible.ruleIds id present member
  conversion := compatible.conversion.symm

/-- The calculus of a union: both transported calculi, the first before the
second. -/
def unionCalculus (firstSymbols secondSymbols : LanguageDefSymbolMap)
    (first second : ProofCalculus) : ProofCalculus :=
  mergeOf (reindexProofCalculus (coreSymbols firstSymbols) first)
    (reindexProofCalculus (coreSymbols secondSymbols) second)

/-- Along identity core maps the union calculus is the equal-core merge. -/
@[simp] theorem unionCalculus_id (first second : ProofCalculus) :
    unionCalculus LanguageDefSymbolMap.id LanguageDefSymbolMap.id first second =
      mergeOf first second := by
  simp [unionCalculus]

/-- When at most one side roots a conversion, the authored append is the
merge. -/
theorem append?_eq_mergeOf {first second : ProofCalculus}
    (conversion : first.conversion = none ∨ second.conversion = none) :
    first.append? second = some (mergeOf first second) := by
  cases conversion with
  | inl firstNone =>
      cases secondConversion : second.conversion <;>
        simp [ProofCalculus.append?, mergeOf, firstNone, secondConversion]
  | inr secondNone =>
      cases firstConversion : first.conversion <;>
        simp [ProofCalculus.append?, mergeOf, firstConversion, secondNone]

/-- **An admitted merge has disjoint names.**  Duplicate-freedom of the merged
judgment heads and rule identifiers splits into disjointness of the two
sides.  With at most one conversion root this is exactly `Compatible`. -/
theorem compatible_of_mergeOf_admitted {language : LanguageDef}
    {first second : ProofCalculus}
    (conversion : first.conversion = none ∨ second.conversion = none)
    (admitted : (CalculusLanguageDef.extend language (mergeOf first second)).isValid =
      true) :
    Compatible first second := by
  simp only [CalculusLanguageDef.isValid, CalculusLanguageDef.hasValidLocalRules,
    CalculusLanguageDef.judgmentSignatureValid, Bool.and_eq_true,
    CalculusLanguageDef.judgmentHeads, CalculusLanguageDef.ruleIds] at admitted
  obtain ⟨⟨⟨⟨_, idsUnique⟩, ⟨⟨_, headsUnique⟩, _⟩⟩, _⟩, _⟩ := admitted
  rw [eraseDups_length_iff_nodup] at idsUnique headsUnique
  simp only [CalculusLanguageDef.extend_judgments, CalculusLanguageDef.extend_rules,
    mergeOf_judgments, mergeOf_rules, List.map_append, List.nodup_append] at idsUnique headsUnique
  refine ⟨?_, ?_, conversion⟩
  · intro head member present
    exact headsUnique.2.2 head member head present rfl
  · intro id member present
    exact idsUnique.2.2 id member id present rfl

section Union

variable {left right core : ValidatedLanguageDef}
  (leftMap : TypingMorphism left core) (rightMap : TypingMorphism right core)
  {leftCalculus rightCalculus : ProofCalculus}

/-- **The union of two decorated cores, each renamed, exists exactly when the
renamed calculi are compatible.**  Each calculus is admitted over its own core,
and each renaming is legal for the common core.  The authored merge of the two
transported calculi succeeds with an admitted result if and only if the renamed
calculi have disjoint judgment heads, disjoint rule identifiers and at most one
conversion root.  Renaming is what lets two layers that declare the same head
be united. -/
theorem union_layer_admitted_iff (leftNames rightNames : NamespaceMap)
    (leftAdmitted :
      (CalculusLanguageDef.extend left.language leftCalculus).isValid = true)
    (rightAdmitted :
      (CalculusLanguageDef.extend right.language rightCalculus).isValid = true)
    (leftLegal : NamesValid core.language leftNames leftCalculus)
    (rightLegal : NamesValid core.language rightNames rightCalculus) :
    (∃ merged,
        proofCalculusMonoid.op
            (reindexProofCalculus (layerSymbols leftMap.symbols leftNames) leftCalculus)
            (reindexProofCalculus (layerSymbols rightMap.symbols rightNames) rightCalculus) =
          some merged ∧
        (CalculusLanguageDef.extend core.language merged).isValid = true) ↔
      Compatible (reindexProofCalculus (namespaceSymbols leftNames) leftCalculus)
        (reindexProofCalculus (namespaceSymbols rightNames) rightCalculus) := by
  constructor
  · rintro ⟨merged, mergedByAuthoring, mergedAdmitted⟩
    have conversionRoot :
        (reindexProofCalculus (layerSymbols leftMap.symbols leftNames) leftCalculus).conversion =
            none ∨
          (reindexProofCalculus (layerSymbols rightMap.symbols rightNames)
            rightCalculus).conversion = none := by
      cases leftConversion :
          (reindexProofCalculus (layerSymbols leftMap.symbols leftNames) leftCalculus).conversion
        with
      | none => exact Or.inl rfl
      | some leftDeclaration =>
          cases rightConversion :
              (reindexProofCalculus (layerSymbols rightMap.symbols rightNames)
                rightCalculus).conversion with
          | none => exact Or.inr rfl
          | some rightDeclaration =>
              change ProofCalculus.append? _ _ = some merged at mergedByAuthoring
              simp [ProofCalculus.append?, leftConversion, rightConversion] at mergedByAuthoring
    change ProofCalculus.append? _ _ = some merged at mergedByAuthoring
    rw [append?_eq_mergeOf conversionRoot] at mergedByAuthoring
    obtain rfl := Option.some.inj mergedByAuthoring
    exact (compatible_layer_iff _ _ _ _ _ _).mp
      (compatible_of_mergeOf_admitted conversionRoot mergedAdmitted)
  · intro compatible
    obtain ⟨mergedByAuthoring, mergedAdmitted⟩ := gluing_of_compatible core.language
      (reindexProofCalculus (layerSymbols leftMap.symbols leftNames) leftCalculus)
      (reindexProofCalculus (layerSymbols rightMap.symbols rightNames) rightCalculus)
      ((admitted_layer_iff leftMap leftNames leftAdmitted).mpr leftLegal)
      ((admitted_layer_iff rightMap rightNames rightAdmitted).mpr rightLegal)
      ((compatible_layer_iff _ _ _ _ _ _).mpr compatible)
    exact ⟨_, mergedByAuthoring, mergedAdmitted⟩

/-- **The union of two decorated cores exists exactly when their calculi are
compatible.**  Both calculi are admitted over their own cores and their
judgment heads stay fresh in the common core.  This is the identity-renaming
case of `union_layer_admitted_iff`: the authored merge of the two transported
calculi succeeds with an admitted result if and only if the two calculi have
disjoint judgment heads, disjoint rule identifiers and at most one conversion
root. -/
theorem union_admitted_iff
    (leftAdmitted :
      (CalculusLanguageDef.extend left.language leftCalculus).isValid = true)
    (rightAdmitted :
      (CalculusLanguageDef.extend right.language rightCalculus).isValid = true)
    (leftFresh : HeadsFresh core.language leftCalculus)
    (rightFresh : HeadsFresh core.language rightCalculus) :
    (∃ merged,
        proofCalculusMonoid.op
            (reindexProofCalculus (coreSymbols leftMap.symbols) leftCalculus)
            (reindexProofCalculus (coreSymbols rightMap.symbols) rightCalculus) =
          some merged ∧
        (CalculusLanguageDef.extend core.language merged).isValid = true) ↔
      Compatible leftCalculus rightCalculus := by
  have criterion := union_layer_admitted_iff leftMap rightMap 1 1 leftAdmitted rightAdmitted
    ((namesValid_one_iff leftAdmitted).mpr leftFresh)
    ((namesValid_one_iff rightAdmitted).mpr rightFresh)
  simpa only [layerSymbols_one, coreSymbols_id, reindexProofCalculus_id] using criterion

end Union

/-- **Equal cores are the identity case.**  Along identity morphisms the
transport is the identity and freshness is implied by admission, so the union
criterion is exactly the equal-core gluing law: two calculi admitted over one
core glue to an admitted calculus if and only if they are compatible. -/
theorem equalCore_union_iff (core : ValidatedLanguageDef)
    {first second : ProofCalculus}
    (firstAdmitted : (CalculusLanguageDef.extend core.language first).isValid = true)
    (secondAdmitted : (CalculusLanguageDef.extend core.language second).isValid = true) :
    (∃ merged, proofCalculusMonoid.op first second = some merged ∧
        (CalculusLanguageDef.extend core.language merged).isValid = true) ↔
      Compatible first second := by
  have criterion := union_admitted_iff (TypingMorphism.id core) (TypingMorphism.id core)
    firstAdmitted secondAdmitted (headsFresh_of_admitted firstAdmitted)
    (headsFresh_of_admitted secondAdmitted)
  simpa [TypingMorphism.id] using criterion

/-! ### Unions over structural coproducts -/

section Coproduct

variable {name : String} {leftSymbols rightSymbols : LanguageDefSymbolMap}
  {left right : ValidatedLanguageDef}

/-- The conditions under which two decorated cores have a union over a
structural coproduct of their cores: both calculi are admitted over their own
cores, their judgment heads stay fresh in the coproduct, and they are
compatible. -/
structure UnionConditions
    (coproduct : StructuralCoproduct.Compatibility name leftSymbols rightSymbols left right)
    (leftCalculus rightCalculus : ProofCalculus) : Prop where
  leftAdmitted : (CalculusLanguageDef.extend left.language leftCalculus).isValid = true
  rightAdmitted : (CalculusLanguageDef.extend right.language rightCalculus).isValid = true
  leftFresh : HeadsFresh coproduct.combinedLanguage.language leftCalculus
  rightFresh : HeadsFresh coproduct.combinedLanguage.language rightCalculus
  compatible : Compatible leftCalculus rightCalculus

variable {coproduct : StructuralCoproduct.Compatibility name leftSymbols rightSymbols left right}
  {leftCalculus rightCalculus : ProofCalculus}

/-- The union calculus over a structural coproduct is admitted. -/
theorem coproductUnion_valid (conditions : UnionConditions coproduct leftCalculus rightCalculus) :
    (CalculusLanguageDef.extend coproduct.combinedLanguage.language
        (unionCalculus leftSymbols rightSymbols leftCalculus rightCalculus)).isValid =
      true :=
  (gluing_of_compatible coproduct.combinedLanguage.language
    (reindexProofCalculus (coreSymbols leftSymbols) leftCalculus)
    (reindexProofCalculus (coreSymbols rightSymbols) rightCalculus)
    ((admitted_reindex_iff coproduct.leftInclusion.toTyping conditions.leftAdmitted).mpr
      conditions.leftFresh)
    ((admitted_reindex_iff coproduct.rightInclusion.toTyping conditions.rightAdmitted).mpr
      conditions.rightFresh)
    ((compatible_reindex_iff _ _ _ _).mpr conditions.compatible)).2

/-- The decorated union over a structural coproduct, as one validated flat
calculus language. -/
def coproductUnion (conditions : UnionConditions coproduct leftCalculus rightCalculus) :
    ValidatedCalculusLanguageDef :=
  ⟨CalculusLanguageDef.extend coproduct.combinedLanguage.language
      (unionCalculus leftSymbols rightSymbols leftCalculus rightCalculus),
    coproductUnion_valid conditions⟩

/-- The left decorated core includes into the union, over the left coproduct
injection.  Its rules arrive renamed in the left block of the union; its
judgments and any conversion root arrive unchanged. -/
def coproductUnionLeft (conditions : UnionConditions coproduct leftCalculus rightCalculus) :
    CalculusStructuralMorphism ⟨_, conditions.leftAdmitted⟩ (coproductUnion conditions) where
  symbols := coreSymbols leftSymbols
  mapsTypes := coproduct.leftInclusion.mapsTypes
  mapsTerms := coproduct.leftInclusion.mapsTerms
  mapsEquations := coproduct.leftInclusion.mapsEquations
  mapsRewrites := coproduct.leftInclusion.mapsRewrites
  mapsJudgments judgment member := by
    rw [mapJudgmentDecl_coreSymbols]
    apply List.mem_append_left
    rw [reindex_coreSymbols_judgments]
    exact member
  mapsRules rule member := List.mem_append_left _ (List.mem_map_of_mem member)
  mapsConversion declaration declared := by
    change ((reindexProofCalculus (coreSymbols rightSymbols) rightCalculus).conversion <|>
        (reindexProofCalculus (coreSymbols leftSymbols) leftCalculus).conversion) =
      some (mapConversionDecl (coreSymbols leftSymbols) declaration)
    change leftCalculus.conversion = some declaration at declared
    rw [reindex_coreSymbols_conversion, reindex_coreSymbols_conversion,
      mapConversionDecl_coreSymbols]
    cases conditions.compatible.conversion with
    | inl leftNone => rw [leftNone] at declared; cases declared
    | inr rightNone => rw [rightNone, declared]; rfl

/-- The right decorated core includes into the union, over the right
coproduct injection. -/
def coproductUnionRight (conditions : UnionConditions coproduct leftCalculus rightCalculus) :
    CalculusStructuralMorphism ⟨_, conditions.rightAdmitted⟩ (coproductUnion conditions) where
  symbols := coreSymbols rightSymbols
  mapsTypes := coproduct.rightInclusion.mapsTypes
  mapsTerms := coproduct.rightInclusion.mapsTerms
  mapsEquations := coproduct.rightInclusion.mapsEquations
  mapsRewrites := coproduct.rightInclusion.mapsRewrites
  mapsJudgments judgment member := by
    rw [mapJudgmentDecl_coreSymbols]
    apply List.mem_append_right
    rw [reindex_coreSymbols_judgments]
    exact member
  mapsRules rule member := List.mem_append_right _ (List.mem_map_of_mem member)
  mapsConversion declaration declared := by
    change ((reindexProofCalculus (coreSymbols rightSymbols) rightCalculus).conversion <|>
        (reindexProofCalculus (coreSymbols leftSymbols) leftCalculus).conversion) =
      some (mapConversionDecl (coreSymbols rightSymbols) declaration)
    change rightCalculus.conversion = some declaration at declared
    rw [reindex_coreSymbols_conversion, reindex_coreSymbols_conversion,
      mapConversionDecl_coreSymbols, declared]
    rfl

/-- The left inclusion lies over the left coproduct injection. -/
theorem coproductUnionLeft_over
    (conditions : UnionConditions coproduct leftCalculus rightCalculus) :
    (coproductUnionLeft conditions).toLanguageDefMorphism = coproduct.leftInclusion :=
  StructuralMorphism.ext rfl

/-- The right inclusion lies over the right coproduct injection. -/
theorem coproductUnionRight_over
    (conditions : UnionConditions coproduct leftCalculus rightCalculus) :
    (coproductUnionRight conditions).toLanguageDefMorphism = coproduct.rightInclusion :=
  StructuralMorphism.ext rfl

/-- Every judgment the left calculus declares is resolved in the union exactly
as in the left decorated core. -/
theorem coproductUnion_lookupJudgment_left
    (conditions : UnionConditions coproduct leftCalculus rightCalculus)
    {head : String} (arity : Nat)
    (declared : head ∈ leftCalculus.judgments.map JudgmentDecl.head) :
    (coproductUnion conditions).1.lookupJudgment? head arity =
      (CalculusLanguageDef.extend left.language leftCalculus).lookupJudgment? head arity := by
  have absent : head ∉
      (reindexProofCalculus (coreSymbols rightSymbols) rightCalculus).judgments.map
        JudgmentDecl.head := by
    rw [reindex_coreSymbols_judgments]
    exact conditions.compatible.judgmentHeads head declared
  change (CalculusLanguageDef.extend coproduct.combinedLanguage.language
      (mergeOf _ _)).lookupJudgment? head arity = _
  rw [lookupJudgment_merge_left _ _ _ absent, lookupJudgment?_reindex]

/-- Every judgment the right calculus declares is resolved in the union exactly
as in the right decorated core. -/
theorem coproductUnion_lookupJudgment_right
    (conditions : UnionConditions coproduct leftCalculus rightCalculus)
    {head : String} (arity : Nat)
    (declared : head ∈ rightCalculus.judgments.map JudgmentDecl.head) :
    (coproductUnion conditions).1.lookupJudgment? head arity =
      (CalculusLanguageDef.extend right.language rightCalculus).lookupJudgment? head
        arity := by
  have absent : head ∉
      (reindexProofCalculus (coreSymbols leftSymbols) leftCalculus).judgments.map
        JudgmentDecl.head := by
    rw [reindex_coreSymbols_judgments]
    intro present
    exact conditions.compatible.judgmentHeads head present declared
  change (CalculusLanguageDef.extend coproduct.combinedLanguage.language
      (mergeOf _ _)).lookupJudgment? head arity = _
  rw [lookupJudgment_merge_right _ _ _ absent, lookupJudgment?_reindex]

end Coproduct

/-! ### What the decorated union preserves of each side -/

section Derivations

open CalculusLanguageExtension
open InferenceNewJudgmentConservativity

/-- Every rule of an admitted calculus concludes a judgment that the calculus
declares. -/
theorem conclusion_head_declared {language : LanguageDef} {calculus : ProofCalculus}
    (admitted : (CalculusLanguageDef.extend language calculus).isValid = true)
    {rule : RuleSchema} (member : rule ∈ calculus.rules) :
    ∃ head arguments, rule.conclusion = .apply head arguments ∧
      head ∈ calculus.judgments.map JudgmentDecl.head := by
  have valid := rule_isValidIn_of_mem ⟨_, admitted⟩ member
  simp only [RuleSchema.isValidIn, Bool.and_eq_true, List.all_eq_true] at valid
  have concluded := valid.2.1 rule.conclusion (by simp [RuleSchema.patterns])
  cases conclusionEquation : rule.conclusion with
  | apply head arguments =>
      rw [conclusionEquation] at concluded
      simp only [CalculusLanguageDef.judgmentSchemaValid, Bool.and_eq_true] at concluded
      exact ⟨head, arguments, rfl, mem_judgmentHeads_of_lookup concluded.1⟩
  | bvar index =>
      rw [conclusionEquation] at concluded
      simp [CalculusLanguageDef.judgmentSchemaValid] at concluded
  | fvar variableName =>
      rw [conclusionEquation] at concluded
      simp [CalculusLanguageDef.judgmentSchemaValid] at concluded
  | lambda binder body =>
      rw [conclusionEquation] at concluded
      simp [CalculusLanguageDef.judgmentSchemaValid] at concluded
  | multiLambda arity binders body =>
      rw [conclusionEquation] at concluded
      simp [CalculusLanguageDef.judgmentSchemaValid] at concluded
  | subst body replacement =>
      rw [conclusionEquation] at concluded
      simp [CalculusLanguageDef.judgmentSchemaValid] at concluded
  | collection collectionType elements rest =>
      rw [conclusionEquation] at concluded
      simp [CalculusLanguageDef.judgmentSchemaValid] at concluded

/-- Dropping a conversion root keeps admission. -/
theorem admitted_without_conversion {language : LanguageDef} {calculus : ProofCalculus}
    (admitted : (CalculusLanguageDef.extend language calculus).isValid = true) :
    (CalculusLanguageDef.extend language { calculus with conversion := none }).isValid =
      true := by
  simp only [CalculusLanguageDef.isValid, Bool.and_eq_true] at admitted ⊢
  exact ⟨admitted.1, by simp [CalculusLanguageDef.conversionDeclarationValid]⟩

/-- With disjoint rule identifiers, rule lookup does not depend on the order
of the two blocks. -/
private theorem find?_append_comm {first second : List RuleSchema}
    (disjoint : ∀ id ∈ first.map RuleSchema.id, id ∉ second.map RuleSchema.id) (id : RuleId) :
    (first ++ second).find? (fun rule => decide (rule.id = id)) =
      (second ++ first).find? (fun rule => decide (rule.id = id)) := by
  rw [List.find?_append, List.find?_append]
  cases inFirst : first.find? (fun rule => decide (rule.id = id)) with
  | none => simp
  | some found =>
      obtain ⟨member, matching⟩ := id_of_find? inFirst
      have absent : second.find? (fun rule => decide (rule.id = id)) = none := by
        rw [List.find?_eq_none]
        intro other otherMember otherMatching
        exact disjoint id (matching ▸ List.mem_map_of_mem member)
          (of_decide_eq_true otherMatching ▸ List.mem_map_of_mem otherMember)
      simp [absent]

variable {name : String} {leftSymbols rightSymbols : LanguageDefSymbolMap}
  {left right : ValidatedLanguageDef}
  {coproduct : StructuralCoproduct.Compatibility name leftSymbols rightSymbols left right}
  {leftCalculus rightCalculus : ProofCalculus}

/-- The transported left calculus over the coproduct, admitted on its own. -/
def coproductLeftPart (conditions : UnionConditions coproduct leftCalculus rightCalculus) :
    ValidatedCalculusLanguageDef :=
  ⟨CalculusLanguageDef.extend coproduct.combinedLanguage.language
      (reindexProofCalculus (coreSymbols leftSymbols) leftCalculus),
    (admitted_reindex_iff coproduct.leftInclusion.toTyping conditions.leftAdmitted).mpr
      conditions.leftFresh⟩

/-- The transported right calculus over the coproduct, admitted on its own. -/
def coproductRightPart (conditions : UnionConditions coproduct leftCalculus rightCalculus) :
    ValidatedCalculusLanguageDef :=
  ⟨CalculusLanguageDef.extend coproduct.combinedLanguage.language
      (reindexProofCalculus (coreSymbols rightSymbols) rightCalculus),
    (admitted_reindex_iff coproduct.rightInclusion.toTyping conditions.rightAdmitted).mpr
      conditions.rightFresh⟩

/-- The rows that one side adds to the other inside the union: its judgments
and its renamed rules, as a new-judgment extension. -/
private def increment (added : ProofCalculus) : CalculusLanguageExtension where
  newJudgments := added.judgments
  newRules := added.rules

private theorem increment_disjoint {base added : ProofCalculus} {language : LanguageDef}
    (compatible : Compatible base added) :
    (increment added).disjointFrom (CalculusLanguageDef.extend language base) = true := by
  simp only [CalculusLanguageExtension.disjointFrom, increment, List.all_nil, Bool.true_and,
    Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true', List.any_eq_false, beq_iff_eq,
    CalculusLanguageDef.extend_judgments, CalculusLanguageDef.extend_rules]
  refine ⟨fun judgment member existing existingMember sameHead => ?_,
    fun rule member existing existingMember sameId => ?_⟩
  · exact compatible.judgmentHeads existing.head (List.mem_map_of_mem existingMember)
      (sameHead ▸ List.mem_map_of_mem member)
  · exact compatible.ruleIds existing.id (List.mem_map_of_mem existingMember)
      (sameId ▸ List.mem_map_of_mem member)

private theorem increment_newJudgmentsOnly {language addedLanguage : LanguageDef}
    {base added : ProofCalculus} (compatible : Compatible base added)
    (addedAdmitted : (CalculusLanguageDef.extend addedLanguage added).isValid = true) :
    (increment added).policyHolds (CalculusLanguageDef.extend language base)
      .newJudgmentsOnly = true := by
  simp only [CalculusLanguageExtension.policyHolds, increment, List.all_eq_true]
  intro rule member
  obtain ⟨head, arguments, concluded, declared⟩ :=
    conclusion_head_declared addedAdmitted member
  rw [concluded]
  simp only [CalculusLanguageDef.extend_judgments, Bool.not_eq_true', List.any_eq_false,
    beq_iff_eq]
  intro judgment judgmentMember sameHead
  exact compatible.judgmentHeads head (sameHead ▸ List.mem_map_of_mem judgmentMember) declared

/-- The union presented as the transported left calculus extended by the right
rows, with the right conversion root set aside; rule lookup is unchanged by
setting it aside. -/
private def rightIncrement (conditions : UnionConditions coproduct leftCalculus rightCalculus) :
    ValidatedCalculusLanguageExtension (coproductLeftPart conditions) where
  extension := increment (reindexProofCalculus (coreSymbols rightSymbols) rightCalculus)
  policy := .newJudgmentsOnly
  disjoint := increment_disjoint ((compatible_reindex_iff _ _ _ _).mpr conditions.compatible)
  policyHolds := increment_newJudgmentsOnly
    ((compatible_reindex_iff _ _ _ _).mpr conditions.compatible)
    ((admitted_reindex_iff coproduct.rightInclusion.toTyping conditions.rightAdmitted).mpr
      conditions.rightFresh)
  valid := by
    have glued := (gluing_of_compatible coproduct.combinedLanguage.language
      (reindexProofCalculus (coreSymbols leftSymbols) leftCalculus)
      { reindexProofCalculus (coreSymbols rightSymbols) rightCalculus with conversion := none }
      (coproductLeftPart conditions).2
      (admitted_without_conversion (coproductRightPart conditions).2)
      ⟨by simpa using conditions.compatible.judgmentHeads,
        by simpa using conditions.compatible.ruleIds, Or.inr rfl⟩).2
    have same : (increment (reindexProofCalculus (coreSymbols rightSymbols)
        rightCalculus)).apply (coproductLeftPart conditions).1 =
      CalculusLanguageDef.extend coproduct.combinedLanguage.language
        (mergeOf (reindexProofCalculus (coreSymbols leftSymbols) leftCalculus)
          { reindexProofCalculus (coreSymbols rightSymbols) rightCalculus with
            conversion := none }) := by
      apply CalculusLanguageDef.ext <;>
        simp [CalculusLanguageExtension.apply, increment, coproductLeftPart, mergeOf]
    rw [same]
    exact glued

/-- The union presented as the transported right calculus extended by the left
rows. -/
private def leftIncrement (conditions : UnionConditions coproduct leftCalculus rightCalculus) :
    ValidatedCalculusLanguageExtension (coproductRightPart conditions) where
  extension := increment (reindexProofCalculus (coreSymbols leftSymbols) leftCalculus)
  policy := .newJudgmentsOnly
  disjoint := increment_disjoint
    ((compatible_reindex_iff _ _ _ _).mpr (compatible_symm conditions.compatible))
  policyHolds := increment_newJudgmentsOnly
    ((compatible_reindex_iff _ _ _ _).mpr (compatible_symm conditions.compatible))
    ((admitted_reindex_iff coproduct.leftInclusion.toTyping conditions.leftAdmitted).mpr
      conditions.leftFresh)
  valid := by
    have glued := (gluing_of_compatible coproduct.combinedLanguage.language
      (reindexProofCalculus (coreSymbols rightSymbols) rightCalculus)
      { reindexProofCalculus (coreSymbols leftSymbols) leftCalculus with conversion := none }
      (coproductRightPart conditions).2
      (admitted_without_conversion (coproductLeftPart conditions).2)
      ⟨by simpa using (compatible_symm conditions.compatible).judgmentHeads,
        by simpa using (compatible_symm conditions.compatible).ruleIds, Or.inr rfl⟩).2
    have same : (increment (reindexProofCalculus (coreSymbols leftSymbols)
        leftCalculus)).apply (coproductRightPart conditions).1 =
      CalculusLanguageDef.extend coproduct.combinedLanguage.language
        (mergeOf (reindexProofCalculus (coreSymbols rightSymbols) rightCalculus)
          { reindexProofCalculus (coreSymbols leftSymbols) leftCalculus with
            conversion := none }) := by
      apply CalculusLanguageDef.ext <;>
        simp [CalculusLanguageExtension.apply, increment, coproductRightPart, mergeOf]
    rw [same]
    exact glued

/-- **Derivations of left judgments are conserved by the union.**  On every
goal shaped by a judgment of the left calculus, the union accepts a raw proof
exactly when the transported left calculus alone accepts it.  The right rows
add no derivation of a left judgment. -/
theorem coproductUnion_conservative_left
    (conditions : UnionConditions coproduct leftCalculus rightCalculus) {goal : Pattern}
    (shape : (coproductLeftPart conditions).1.hasJudgmentShape goal = true)
    (proof : RawProof) :
    checkRaw (coproductUnion conditions) goal proof = true ↔
      checkRaw (coproductLeftPart conditions) goal proof = true := by
  have sameLookups : ∀ id,
      (coproductUnion conditions).1.lookupRule? id =
        (rightIncrement conditions).target.1.lookupRule? id := fun _ => rfl
  rw [← ValidatedCalculusLanguageExtension.checkRaw_iff_base_of_newJudgmentsOnly
    (rightIncrement conditions) rfl shape proof]
  constructor
  · exact checkRaw_true_of_ruleLookupRefines
      (fun id rule found => (sameLookups id) ▸ found)
  · exact checkRaw_true_of_ruleLookupRefines
      (fun id rule found => (sameLookups id).symm ▸ found)

/-- **Derivations of right judgments are conserved by the union.** -/
theorem coproductUnion_conservative_right
    (conditions : UnionConditions coproduct leftCalculus rightCalculus) {goal : Pattern}
    (shape : (coproductRightPart conditions).1.hasJudgmentShape goal = true)
    (proof : RawProof) :
    checkRaw (coproductUnion conditions) goal proof = true ↔
      checkRaw (coproductRightPart conditions) goal proof = true := by
  have disjointIds : ∀ id ∈
      (reindexProofCalculus (coreSymbols leftSymbols) leftCalculus).rules.map RuleSchema.id,
      id ∉ (reindexProofCalculus (coreSymbols rightSymbols) rightCalculus).rules.map
        RuleSchema.id := by
    simpa using conditions.compatible.ruleIds
  have sameLookups : ∀ id,
      (coproductUnion conditions).1.lookupRule? id =
        (leftIncrement conditions).target.1.lookupRule? id :=
    fun id => find?_append_comm disjointIds id
  rw [← ValidatedCalculusLanguageExtension.checkRaw_iff_base_of_newJudgmentsOnly
    (leftIncrement conditions) rfl shape proof]
  constructor
  · exact checkRaw_true_of_ruleLookupRefines
      (fun id rule found => (sameLookups id) ▸ found)
  · exact checkRaw_true_of_ruleLookupRefines
      (fun id rule found => (sameLookups id).symm ▸ found)

end Derivations

/-! ### Restriction of the union to each side -/

section Restriction

/-- The judgment head a rule concludes. -/
def conclusionHead (rule : RuleSchema) : Option String :=
  match rule.conclusion with
  | .apply head _ => some head
  | _ => none

/-- **Restriction to a judgment namespace**: the judgments with the given
heads, the rules concluding one of them, and a conversion root among them. -/
def restrictToHeads (heads : List String) (calculus : ProofCalculus) : ProofCalculus where
  judgments := calculus.judgments.filter fun judgment => decide (judgment.head ∈ heads)
  rules := calculus.rules.filter fun rule =>
    (conclusionHead rule).any fun head => decide (head ∈ heads)
  conversion := calculus.conversion.filter fun declaration =>
    decide (declaration.judgmentHead ∈ heads)

/-- Core transport keeps the judgment a rule concludes. -/
theorem conclusionHead_mapRuleSchema (symbols : LanguageDefSymbolMap) (rule : RuleSchema) :
    conclusionHead (mapRuleSchema (coreSymbols symbols) rule) = conclusionHead rule := by
  simp only [conclusionHead, mapRuleSchema]
  cases rule.conclusion <;> rfl

/-- An admitted calculus roots its conversion at a judgment it declares. -/
theorem conversion_head_declared {language : LanguageDef} {calculus : ProofCalculus}
    (admitted : (CalculusLanguageDef.extend language calculus).isValid = true)
    {declaration : ConversionDecl} (declared : calculus.conversion = some declaration) :
    declaration.judgmentHead ∈ calculus.judgments.map JudgmentDecl.head := by
  simp only [CalculusLanguageDef.isValid, Bool.and_eq_true] at admitted
  have rooted : (CalculusLanguageDef.extend language calculus).conversion = some declaration :=
    declared
  have valid := admitted.2
  simp only [CalculusLanguageDef.conversionDeclarationValid, rooted, Bool.and_eq_true] at valid
  exact mem_judgmentHeads_of_lookup valid.2

/-- Restricted to the heads of one admitted calculus, a merge keeps exactly
that calculus' rows when the other calculus declares none of those heads. -/
private theorem restrict_rows {language language' : LanguageDef} {kept dropped : ProofCalculus}
    (keptAdmitted : (CalculusLanguageDef.extend language kept).isValid = true)
    (droppedAdmitted : (CalculusLanguageDef.extend language' dropped).isValid = true)
    (apart : ∀ head ∈ dropped.judgments.map JudgmentDecl.head,
      head ∉ kept.judgments.map JudgmentDecl.head)
    (keptSymbols droppedSymbols : LanguageDefSymbolMap) :
    (dropped.judgments.filter fun judgment =>
        decide (judgment.head ∈ kept.judgments.map JudgmentDecl.head)) = [] ∧
      (kept.judgments.filter fun judgment =>
        decide (judgment.head ∈ kept.judgments.map JudgmentDecl.head)) = kept.judgments ∧
      ((dropped.rules.map (mapRuleSchema (coreSymbols droppedSymbols))).filter fun rule =>
        (conclusionHead rule).any fun head =>
          decide (head ∈ kept.judgments.map JudgmentDecl.head)) = [] ∧
      ((kept.rules.map (mapRuleSchema (coreSymbols keptSymbols))).filter fun rule =>
        (conclusionHead rule).any fun head =>
          decide (head ∈ kept.judgments.map JudgmentDecl.head)) =
        kept.rules.map (mapRuleSchema (coreSymbols keptSymbols)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [List.filter_eq_nil_iff]
    intro judgment member
    simpa using apart _ (List.mem_map_of_mem member)
  · rw [List.filter_eq_self]
    intro judgment member
    simpa using List.mem_map_of_mem (f := JudgmentDecl.head) member
  · rw [List.filter_eq_nil_iff]
    intro mapped member
    obtain ⟨rule, ruleMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨head, arguments, concluded, declared⟩ :=
      conclusion_head_declared droppedAdmitted ruleMember
    rw [conclusionHead_mapRuleSchema, conclusionHead, concluded]
    simpa using apart head declared
  · rw [List.filter_eq_self]
    intro mapped member
    obtain ⟨rule, ruleMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨head, arguments, concluded, declared⟩ :=
      conclusion_head_declared keptAdmitted ruleMember
    rw [conclusionHead_mapRuleSchema, conclusionHead, concluded]
    simpa using declared

variable {name : String} {leftSymbols rightSymbols : LanguageDefSymbolMap}
  {left right : ValidatedLanguageDef}
  {coproduct : StructuralCoproduct.Compatibility name leftSymbols rightSymbols left right}
  {leftCalculus rightCalculus : ProofCalculus}

/-- **Restricted to the left judgments, the union is the left calculus
transported along the left injection**: its judgments, the rows concluding
them and its conversion root. -/
theorem coproductUnion_restrict_left
    (conditions : UnionConditions coproduct leftCalculus rightCalculus) :
    restrictToHeads (leftCalculus.judgments.map JudgmentDecl.head)
        (unionCalculus leftSymbols rightSymbols leftCalculus rightCalculus) =
      reindexProofCalculus (coreSymbols leftSymbols) leftCalculus := by
  have apart : ∀ head ∈ rightCalculus.judgments.map JudgmentDecl.head,
      head ∉ leftCalculus.judgments.map JudgmentDecl.head :=
    fun head present member => conditions.compatible.judgmentHeads head member present
  obtain ⟨droppedJudgments, keptJudgments, droppedRules, keptRules⟩ :=
    restrict_rows conditions.leftAdmitted conditions.rightAdmitted apart leftSymbols rightSymbols
  have conversion :
      ((rightCalculus.conversion <|> leftCalculus.conversion).filter fun declaration =>
          decide (declaration.judgmentHead ∈ leftCalculus.judgments.map JudgmentDecl.head)) =
        leftCalculus.conversion := by
    cases conditions.compatible.conversion with
    | inl leftNone =>
        rw [leftNone]
        cases rightConversion : rightCalculus.conversion with
        | none => rfl
        | some declaration =>
            have absent := apart _
              (conversion_head_declared conditions.rightAdmitted rightConversion)
            simp [Option.filter, absent]
    | inr rightNone =>
        rw [rightNone]
        cases leftConversion : leftCalculus.conversion with
        | none => rfl
        | some declaration =>
            have present := conversion_head_declared conditions.leftAdmitted leftConversion
            simp [Option.filter, present]
  have eta : ∀ calculus : ProofCalculus,
      calculus = ⟨calculus.judgments, calculus.rules, calculus.conversion⟩ := fun _ => rfl
  have mergeConversion : ∀ first second : ProofCalculus,
      (mergeOf first second).conversion = (second.conversion <|> first.conversion) :=
    fun _ _ => rfl
  rw [eta (reindexProofCalculus (coreSymbols leftSymbols) leftCalculus)]
  change ProofCalculus.mk _ _ _ = _
  simp only [unionCalculus, mergeOf_judgments, mergeOf_rules, mergeConversion,
    reindex_coreSymbols_judgments, reindex_coreSymbols_rules, reindex_coreSymbols_conversion,
    List.filter_append, droppedJudgments, keptJudgments, droppedRules, keptRules,
    List.append_nil, conversion]

/-- **Restricted to the right judgments, the union is the right calculus
transported along the right injection.** -/
theorem coproductUnion_restrict_right
    (conditions : UnionConditions coproduct leftCalculus rightCalculus) :
    restrictToHeads (rightCalculus.judgments.map JudgmentDecl.head)
        (unionCalculus leftSymbols rightSymbols leftCalculus rightCalculus) =
      reindexProofCalculus (coreSymbols rightSymbols) rightCalculus := by
  have apart : ∀ head ∈ leftCalculus.judgments.map JudgmentDecl.head,
      head ∉ rightCalculus.judgments.map JudgmentDecl.head :=
    fun head member present => conditions.compatible.judgmentHeads head member present
  obtain ⟨droppedJudgments, keptJudgments, droppedRules, keptRules⟩ :=
    restrict_rows conditions.rightAdmitted conditions.leftAdmitted apart rightSymbols leftSymbols
  have conversion :
      ((rightCalculus.conversion <|> leftCalculus.conversion).filter fun declaration =>
          decide (declaration.judgmentHead ∈ rightCalculus.judgments.map JudgmentDecl.head)) =
        rightCalculus.conversion := by
    cases rightConversion : rightCalculus.conversion with
    | some declaration =>
        have present := conversion_head_declared conditions.rightAdmitted rightConversion
        simp [Option.filter, present]
    | none =>
        cases leftConversion : leftCalculus.conversion with
        | none => rfl
        | some declaration =>
            have absent := apart _
              (conversion_head_declared conditions.leftAdmitted leftConversion)
            simp [Option.filter, absent]
  have eta : ∀ calculus : ProofCalculus,
      calculus = ⟨calculus.judgments, calculus.rules, calculus.conversion⟩ := fun _ => rfl
  have mergeConversion : ∀ first second : ProofCalculus,
      (mergeOf first second).conversion = (second.conversion <|> first.conversion) :=
    fun _ _ => rfl
  rw [eta (reindexProofCalculus (coreSymbols rightSymbols) rightCalculus)]
  change ProofCalculus.mk _ _ _ = _
  simp only [unionCalculus, mergeOf_judgments, mergeOf_rules, mergeConversion,
    reindex_coreSymbols_judgments, reindex_coreSymbols_rules, reindex_coreSymbols_conversion,
    List.filter_append, droppedJudgments, keptJudgments, droppedRules, keptRules,
    List.nil_append, conversion]

end Restriction

/-! ## The category of elements inside the calculus-language category -/

/-- Forget the inference rows of a validated calculus language: the projection
of decorated cores to their cores in the existing category of complete calculus
languages. -/
def calculusCoreProjection : ValidatedCalculusLanguageDef ⥤ ValidatedLanguageDef where
  obj definition := definition.toValidatedLanguageDef
  map morphism := morphism.toLanguageDefMorphism
  map_id definition := CalculusStructuralMorphism.toLanguageDefMorphism_id definition
  map_comp earlier later := CalculusStructuralMorphism.toLanguageDefMorphism_comp earlier later

/-- Decorated cores whose calculus is admitted over the core.  Their morphisms
pair a core morphism with a renaming of the calculus' namespaces. -/
def AdmittedDecoration : ObjectProperty layerTransport.toLayerTransport.Total :=
  fun decorated =>
    (CalculusLanguageDef.extend decorated.1.1.language decorated.2).isValid = true

/-- Rows of a calculus are carried into any calculus equal to its transport. -/
theorem rows_of_reindex_eq {symbols : CalculusLanguageSymbols} {source target : ProofCalculus}
    (transported : reindexProofCalculus symbols source = target) :
    (∀ judgment ∈ source.judgments, mapJudgmentDecl symbols judgment ∈ target.judgments) ∧
      (∀ rule ∈ source.rules, mapRuleSchema symbols rule ∈ target.rules) ∧
      (∀ declaration, source.conversion = some declaration →
        target.conversion = some (mapConversionDecl symbols declaration)) := by
  subst transported
  refine ⟨fun judgment member => List.mem_map_of_mem member,
    fun rule member => List.mem_map_of_mem member, fun declaration declared => ?_⟩
  simp [reindexProofCalculus, declared]

/-- A morphism of decorated cores transports the source calculus onto the target
calculus, along its core morphism and its renaming. -/
theorem decorated_hom_reindex {source target : layerTransport.toLayerTransport.Total}
    (morphism : source ⟶ target) :
    reindexProofCalculus (layerSymbols morphism.val.1.symbols morphism.val.2) source.2 =
      target.2 :=
  morphism.property

/-- **Decorated cores sit inside the category of complete calculus languages.**
The category of elements of the layer transport, restricted to admitted
decorations, maps into the existing category of validated calculus languages:
a morphism becomes the structural map whose constructor action is the core
morphism and whose judgment and rule actions are the renaming.  A renaming
over an identity core morphism is a vertical structural map. -/
def toCalculusLanguageDef : AdmittedDecoration.FullSubcategory ⥤ ValidatedCalculusLanguageDef where
  obj decorated :=
    ⟨CalculusLanguageDef.extend decorated.obj.1.1.language decorated.obj.2, decorated.property⟩
  map morphism :=
    { symbols := layerSymbols morphism.hom.val.1.symbols morphism.hom.val.2
      mapsTypes := morphism.hom.val.1.mapsTypes
      mapsTerms := morphism.hom.val.1.mapsTerms
      mapsEquations := morphism.hom.val.1.mapsEquations
      mapsRewrites := morphism.hom.val.1.mapsRewrites
      mapsJudgments := fun judgment member =>
        (rows_of_reindex_eq (decorated_hom_reindex morphism.hom)).1 judgment member
      mapsRules := fun rule member =>
        (rows_of_reindex_eq (decorated_hom_reindex morphism.hom)).2.1 rule member
      mapsConversion := fun declaration declared =>
        (rows_of_reindex_eq (decorated_hom_reindex morphism.hom)).2.2 declaration declared }
  map_id _ := CalculusStructuralMorphism.ext rfl
  map_comp _ _ := CalculusStructuralMorphism.ext rfl

/-- The comparison lies over the cores. -/
theorem toCalculusLanguageDef_over {source target : AdmittedDecoration.FullSubcategory}
    (morphism : source ⟶ target) :
    calculusCoreProjection.map (toCalculusLanguageDef.map morphism) = morphism.hom.val.1 :=
  StructuralMorphism.ext rfl

/-- The comparison is faithful: a morphism of decorated cores, core morphism and
renaming together, is determined by the structural map of calculus languages it
induces. -/
instance : toCalculusLanguageDef.Faithful where
  map_injective {source target} {first second} equal := by
    have symbols := congrArg CalculusStructuralMorphism.symbols equal
    have coreEqual : first.hom.val.1.symbols = second.hom.val.1.symbols :=
      congrArg CalculusLanguageSymbols.toLanguageDefSymbolMap symbols
    have namesEqual : first.hom.val.2 = second.hom.val.2 :=
      NamespaceMap.ext (congrArg CalculusLanguageSymbols.judgment symbols)
        (congrArg CalculusLanguageSymbols.rule symbols)
    apply ObjectProperty.hom_ext
    apply CategoryOfElements.ext
    exact Prod.ext (StructuralMorphism.ext coreEqual) namesEqual

#print axioms LayerTransport.target_eq_map
#print axioms CompositionalTransport.product
#print axioms calculusTransport
#print axioms admitted_reindex_iff
#print axioms glue_least
#print axioms union_admitted_iff
#print axioms equalCore_union_iff
#print axioms coproductUnionLeft_over
#print axioms coproductUnion_lookupJudgment_left
#print axioms toCalculusLanguageDef_over
#print axioms coproductUnion_conservative_left
#print axioms coproductUnion_conservative_right
#print axioms coproductUnion_restrict_left
#print axioms coproductUnion_restrict_right
#print axioms layerTransport
#print axioms layerSymbols_eq_rename_comp
#print axioms admitted_layer_iff
#print axioms admitted_rename_iff
#print axioms compatible_layer_iff
#print axioms union_layer_admitted_iff

end Mettapedia.GSLT.LanguageDef.ExtensionAlongMorphisms
