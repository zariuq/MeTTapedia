import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Data.List.Nodup
import Mettapedia.OSLF.MeTTaIL.Syntax
import Mettapedia.OSLF.MeTTaIL.DerivedContexts

/-!
# Structural maps of validated language definitions

This module keeps `LanguageDef` as the sole source object.
Objects pair that exact value with its existing validation result.  Morphisms
are structural maps of the five-field operational theory: they map sort and
constructor symbols, preserve binder and collection shape, and carry declared
equations and rewrite schemas into declarations of the target.

These maps are deliberately distinct from behavioral `GSLT.Morphism`s and
from operational simulations between languages.  Parsing notation, backend
options, and proof-calculus declarations are not silently identified with the
operational theory.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts

/-- A language definition together with the result of its existing
validation gate.  The declaration data is retained verbatim. -/
structure ValidatedLanguageDef where
  language : LanguageDef
  valid : language.validate = []

namespace ValidatedLanguageDef

instance : Coe ValidatedLanguageDef LanguageDef := ⟨ValidatedLanguageDef.language⟩

end ValidatedLanguageDef

/-- Renaming data for the symbol namespaces occurring in the operational
theory of a `LanguageDef`. -/
@[ext]
structure LanguageDefSymbolMap where
  sort : String → String
  constructor : String → String
  relation : String → String
  equation : String → String
  rewrite : String → String

namespace LanguageDefSymbolMap

/-- Identity symbol map. -/
def id : LanguageDefSymbolMap where
  sort := _root_.id
  constructor := _root_.id
  relation := _root_.id
  equation := _root_.id
  rewrite := _root_.id

/-- Apply `first` and then `second`. -/
def comp (first second : LanguageDefSymbolMap) : LanguageDefSymbolMap where
  sort := second.sort ∘ first.sort
  constructor := second.constructor ∘ first.constructor
  relation := second.relation ∘ first.relation
  equation := second.equation ∘ first.equation
  rewrite := second.rewrite ∘ first.rewrite

end LanguageDefSymbolMap

/-! ## Structural action on declaration data -/

/-- Map every base sort while retaining arrow, binder, and collection shape. -/
def mapTypeExpr (symbols : LanguageDefSymbolMap) : TypeExpr → TypeExpr
  | .base sort => .base (symbols.sort sort)
  | .arrow domain codomain =>
      .arrow (mapTypeExpr symbols domain) (mapTypeExpr symbols codomain)
  | .multiBinder body => .multiBinder (mapTypeExpr symbols body)
  | .collection collectionType element =>
      .collection collectionType (mapTypeExpr symbols element)

/-- Map a declared carrier sort. -/
def mapTypeDecl (symbols : LanguageDefSymbolMap) (declaration : TypeDecl) : TypeDecl :=
  { declaration with name := symbols.sort declaration.name }

/-- Map the types of a constructor parameter without changing whether it is a
plain argument, a single binder, or a multiple binder. -/
def mapTermParam (symbols : LanguageDefSymbolMap) : TermParam → TermParam
  | .simple name type => .simple name (mapTypeExpr symbols type)
  | .abstractionNamed binder body type =>
      .abstractionNamed binder body (mapTypeExpr symbols type)
  | .multiAbstractionNamed binders body type =>
      .multiAbstractionNamed binders body (mapTypeExpr symbols type)

/-- Map a constructor declaration.  Declared notation and evaluation policy
are retained; the algebraic label, result sort, and parameter sorts are mapped. -/
def mapGrammarRule (symbols : LanguageDefSymbolMap)
    (rule : GrammarRule) : GrammarRule :=
  { rule with
    label := symbols.constructor rule.label
    category := symbols.sort rule.category
    params := rule.params.map (mapTermParam symbols) }

/- Structural action on the shared locally nameless term carrier.  Binder
metadata, de Bruijn indices, collection kind, order, multiplicity, and rest
variables are preserved.  The list companion keeps this traversal genuinely
structural, so its constructor equations remain definitionally available to
dependent consumers. -/
mutual
  def mapPattern (symbols : LanguageDefSymbolMap) : Pattern → Pattern
    | .bvar index => .bvar index
    | .fvar name => .fvar name
    | .apply constructor arguments =>
        .apply (symbols.constructor constructor)
          (mapPatternList symbols arguments)
    | .lambda binder body => .lambda binder (mapPattern symbols body)
    | .multiLambda arity binders body =>
        .multiLambda arity binders (mapPattern symbols body)
    | .subst body replacement =>
        .subst (mapPattern symbols body) (mapPattern symbols replacement)
    | .collection collectionType elements rest =>
        .collection collectionType (mapPatternList symbols elements) rest

  def mapPatternList (symbols : LanguageDefSymbolMap) : List Pattern →
      List Pattern
    | [] => []
    | pattern :: patterns =>
        mapPattern symbols pattern :: mapPatternList symbols patterns
end

/-- The structurally recursive list companion agrees with ordinary mapping. -/
@[simp]
theorem mapPatternList_eq_map (symbols : LanguageDefSymbolMap)
    (patterns : List Pattern) :
    mapPatternList symbols patterns = patterns.map (mapPattern symbols) := by
  induction patterns with
  | nil => rfl
  | cons pattern patterns inductionHypothesis =>
      simp [mapPatternList, inductionHypothesis]

/-- Map a declared premise.  Metavariable names remain local to the schema;
only term constructors and declared relation symbols are translated. -/
def mapPremise (symbols : LanguageDefSymbolMap) : Premise → Premise
  | .freshness condition =>
      .freshness { condition with term := mapPattern symbols condition.term }
  | .congruence left right =>
      .congruence (mapPattern symbols left) (mapPattern symbols right)
  | .relationQuery relation arguments =>
      .relationQuery (symbols.relation relation)
        (arguments.map (mapPattern symbols))
  | .forAll collection parameter body =>
      .forAll collection parameter (mapPremise symbols body)

/-- Map the sort annotations of a rule or equation metavariable context. -/
def mapTypeContext (symbols : LanguageDefSymbolMap)
    (context : List (String × TypeExpr)) : List (String × TypeExpr) :=
  context.map fun entry => (entry.1, mapTypeExpr symbols entry.2)

/-- Map a declared bidirectional equation. -/
def mapEquation (symbols : LanguageDefSymbolMap) (equation : Equation) : Equation :=
  { name := symbols.equation equation.name
    typeContext := mapTypeContext symbols equation.typeContext
    premises := equation.premises.map (mapPremise symbols)
    left := mapPattern symbols equation.left
    right := mapPattern symbols equation.right }

/-- Map a declared directional rewrite schema. -/
def mapRewriteRule (symbols : LanguageDefSymbolMap)
    (rewrite : RewriteRule) : RewriteRule :=
  { name := symbols.rewrite rewrite.name
    typeContext := mapTypeContext symbols rewrite.typeContext
    premises := rewrite.premises.map (mapPremise symbols)
    left := mapPattern symbols rewrite.left
    right := mapPattern symbols rewrite.right }

/-! ## Identity and composition laws for the induced action -/

private theorem list_map_eq_self_of_mem {α : Type*} (function : α → α)
    (elements : List α) (fixed : ∀ element ∈ elements, function element = element) :
    elements.map function = elements := by
  calc
    elements.map function = elements.map _root_.id :=
      List.map_congr_left fixed
    _ = elements := List.map_id elements

private theorem list_map_comp_of_mem {α β γ : Type*}
    (first : α → β) (second : β → γ) (composite : α → γ)
    (elements : List α)
    (agrees : ∀ element ∈ elements,
      composite element = second (first element)) :
    elements.map composite = (elements.map first).map second := by
  rw [List.map_map]
  exact List.map_congr_left agrees

@[simp] theorem mapTypeExpr_id (type : TypeExpr) :
    mapTypeExpr LanguageDefSymbolMap.id type = type := by
  induction type <;> simp_all [mapTypeExpr, LanguageDefSymbolMap.id]

@[simp] theorem mapTypeExpr_comp (first second : LanguageDefSymbolMap)
    (type : TypeExpr) :
    mapTypeExpr (first.comp second) type =
      mapTypeExpr second (mapTypeExpr first type) := by
  induction type <;> simp_all [mapTypeExpr, LanguageDefSymbolMap.comp]

@[simp] theorem mapTypeDecl_id (declaration : TypeDecl) :
    mapTypeDecl LanguageDefSymbolMap.id declaration = declaration := by
  cases declaration
  rfl

@[simp] theorem mapTypeDecl_comp (first second : LanguageDefSymbolMap)
    (declaration : TypeDecl) :
    mapTypeDecl (first.comp second) declaration =
      mapTypeDecl second (mapTypeDecl first declaration) := by
  cases declaration
  rfl

@[simp] theorem mapTermParam_id (parameter : TermParam) :
    mapTermParam LanguageDefSymbolMap.id parameter = parameter := by
  cases parameter <;> simp [mapTermParam]

@[simp] theorem mapTermParam_comp (first second : LanguageDefSymbolMap)
    (parameter : TermParam) :
    mapTermParam (first.comp second) parameter =
      mapTermParam second (mapTermParam first parameter) := by
  cases parameter <;> simp [mapTermParam]

@[simp] theorem mapGrammarRule_id (rule : GrammarRule) :
    mapGrammarRule LanguageDefSymbolMap.id rule = rule := by
  cases rule
  simp only [mapGrammarRule, LanguageDefSymbolMap.id, id_eq]
  congr 1
  exact list_map_eq_self_of_mem _ _ fun parameter _ => mapTermParam_id parameter

@[simp] theorem mapGrammarRule_comp (first second : LanguageDefSymbolMap)
    (rule : GrammarRule) :
    mapGrammarRule (first.comp second) rule =
      mapGrammarRule second (mapGrammarRule first rule) := by
  cases rule
  simp only [mapGrammarRule, LanguageDefSymbolMap.comp, Function.comp_apply]
  congr 1
  exact list_map_comp_of_mem _ _ _ _ fun parameter _ =>
    mapTermParam_comp first second parameter

@[simp] theorem mapPattern_id (pattern : Pattern) :
    mapPattern LanguageDefSymbolMap.id pattern = pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => simp [mapPattern]
  | hfvar name => simp [mapPattern]
  | happly constructor arguments inductionHypothesis =>
      simp only [mapPattern, mapPatternList_eq_map,
        LanguageDefSymbolMap.id, id_eq]
      congr 1
      exact list_map_eq_self_of_mem _ _ inductionHypothesis
  | hlambda binder body inductionHypothesis =>
      simp only [mapPattern]
      rw [inductionHypothesis]
  | hmultiLambda arity binders body inductionHypothesis =>
      simp only [mapPattern]
      rw [inductionHypothesis]
  | hsubst body replacement bodyHypothesis replacementHypothesis =>
      simp only [mapPattern]
      rw [bodyHypothesis, replacementHypothesis]
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [mapPattern, mapPatternList_eq_map]
      congr 1
      exact list_map_eq_self_of_mem _ _ inductionHypothesis

@[simp] theorem mapPattern_comp (first second : LanguageDefSymbolMap)
    (pattern : Pattern) :
    mapPattern (first.comp second) pattern =
      mapPattern second (mapPattern first pattern) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => simp [mapPattern]
  | hfvar name => simp [mapPattern]
  | happly constructor arguments inductionHypothesis =>
      simp only [mapPattern, mapPatternList_eq_map,
        LanguageDefSymbolMap.comp, Function.comp_apply]
      congr 1
      exact list_map_comp_of_mem _ _ _ _ inductionHypothesis
  | hlambda binder body inductionHypothesis =>
      simp only [mapPattern]
      rw [inductionHypothesis]
  | hmultiLambda arity binders body inductionHypothesis =>
      simp only [mapPattern]
      rw [inductionHypothesis]
  | hsubst body replacement bodyHypothesis replacementHypothesis =>
      simp only [mapPattern]
      rw [bodyHypothesis, replacementHypothesis]
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [mapPattern, mapPatternList_eq_map]
      congr 1
      exact list_map_comp_of_mem _ _ _ _ inductionHypothesis

namespace CIGSLT

/-- Structural action on the derivative of the shared pattern carrier. -/
def mapOneHoleContext (symbols : LanguageDefSymbolMap) :
    OneHoleContext → OneHoleContext
  | .hole => .hole
  | .apply constructor before inner after =>
      .apply (symbols.constructor constructor)
        (before.map (mapPattern symbols))
        (mapOneHoleContext symbols inner)
        (after.map (mapPattern symbols))
  | .lambda binder inner =>
      .lambda binder (mapOneHoleContext symbols inner)
  | .multiLambda arity binders inner =>
      .multiLambda arity binders (mapOneHoleContext symbols inner)
  | .substBody inner replacement =>
      .substBody (mapOneHoleContext symbols inner)
        (mapPattern symbols replacement)
  | .substReplacement body inner =>
      .substReplacement (mapPattern symbols body)
        (mapOneHoleContext symbols inner)
  | .collection collectionType before inner after rest =>
      .collection collectionType
        (before.map (mapPattern symbols))
        (mapOneHoleContext symbols inner)
        (after.map (mapPattern symbols)) rest

@[simp]
theorem mapOneHoleContext_fill (symbols : LanguageDefSymbolMap)
    (context : OneHoleContext) (pattern : Pattern) :
    (mapOneHoleContext symbols context).fill (mapPattern symbols pattern) =
      mapPattern symbols (context.fill pattern) := by
  induction context <;>
    simp_all [mapOneHoleContext, OneHoleContext.fill, mapPattern,
      List.map_append]

@[simp]
theorem mapPatternList_id (patterns : List Pattern) :
    patterns.map (mapPattern LanguageDefSymbolMap.id) = patterns := by
  calc
    patterns.map (mapPattern LanguageDefSymbolMap.id) =
        patterns.map _root_.id :=
      List.map_congr_left fun pattern _ => mapPattern_id pattern
    _ = patterns := List.map_id patterns

theorem mapPatternList_comp (first second : LanguageDefSymbolMap)
    (patterns : List Pattern) :
    patterns.map (mapPattern (first.comp second)) =
      (patterns.map (mapPattern first)).map (mapPattern second) := by
  rw [List.map_map]
  exact List.map_congr_left fun pattern _ => mapPattern_comp first second pattern

@[simp]
theorem mapOneHoleContext_id (context : OneHoleContext) :
    mapOneHoleContext LanguageDefSymbolMap.id context = context := by
  induction context with
  | hole => rfl
  | apply constructor before inner after ih =>
      simp only [mapOneHoleContext, mapPatternList_id, ih]
      rfl
  | lambda binder inner ih => simp [mapOneHoleContext, ih]
  | multiLambda arity binders inner ih => simp [mapOneHoleContext, ih]
  | substBody inner replacement ih =>
      simp [mapOneHoleContext, ih]
  | substReplacement body inner ih =>
      simp [mapOneHoleContext, ih]
  | collection collectionType before inner after rest ih =>
      simp [mapOneHoleContext, ih]

theorem mapOneHoleContext_comp (first second : LanguageDefSymbolMap)
    (context : OneHoleContext) :
    mapOneHoleContext (first.comp second) context =
      mapOneHoleContext second (mapOneHoleContext first context) := by
  induction context with
  | hole => rfl
  | apply constructor before inner after ih =>
      simp only [mapOneHoleContext, mapPatternList_comp, ih]
      rfl
  | lambda binder inner ih => simp [mapOneHoleContext, ih]
  | multiLambda arity binders inner ih => simp [mapOneHoleContext, ih]
  | substBody inner replacement ih =>
      simp [mapOneHoleContext, ih, mapPattern_comp]
  | substReplacement body inner ih =>
      simp [mapOneHoleContext, ih, mapPattern_comp]
  | collection collectionType before inner after rest ih =>
      simp [mapOneHoleContext, ih, mapPatternList_comp]

/-- Structural translation preserves composition of one-hole contexts. -/
@[simp]
theorem mapOneHoleContext_contextComp (symbols : LanguageDefSymbolMap)
    (outer inner : OneHoleContext) :
    mapOneHoleContext symbols (outer.comp inner) =
      (mapOneHoleContext symbols outer).comp
        (mapOneHoleContext symbols inner) := by
  induction outer <;>
    simp_all [mapOneHoleContext, OneHoleContext.comp]

end CIGSLT

@[simp] theorem mapPremise_id (premise : Premise) :
    mapPremise LanguageDefSymbolMap.id premise = premise := by
  induction premise with
  | freshness condition =>
      cases condition
      simp only [mapPremise]
      rw [mapPattern_id]
  | congruence left right =>
      simp only [mapPremise]
      rw [mapPattern_id, mapPattern_id]
  | relationQuery relation arguments =>
      simp only [mapPremise]
      congr 1
      exact list_map_eq_self_of_mem _ _ fun pattern _ => mapPattern_id pattern
  | forAll collection parameter body inductionHypothesis =>
      simp only [mapPremise]
      rw [inductionHypothesis]

@[simp] theorem mapPremise_comp (first second : LanguageDefSymbolMap)
    (premise : Premise) :
    mapPremise (first.comp second) premise =
      mapPremise second (mapPremise first premise) := by
  induction premise with
  | freshness condition =>
      cases condition
      simp only [mapPremise]
      rw [mapPattern_comp]
  | congruence left right =>
      simp only [mapPremise]
      rw [mapPattern_comp, mapPattern_comp]
  | relationQuery relation arguments =>
      simp only [mapPremise]
      congr 1
      exact list_map_comp_of_mem _ _ _ _ fun pattern _ =>
        mapPattern_comp first second pattern
  | forAll collection parameter body inductionHypothesis =>
      simp only [mapPremise]
      rw [inductionHypothesis]

@[simp] theorem mapTypeContext_id (context : List (String × TypeExpr)) :
    mapTypeContext LanguageDefSymbolMap.id context = context := by
  apply list_map_eq_self_of_mem
  intro entry membership
  rcases entry with ⟨name, type⟩
  simp only [mapTypeExpr_id]

@[simp] theorem mapTypeContext_comp (first second : LanguageDefSymbolMap)
    (context : List (String × TypeExpr)) :
    mapTypeContext (first.comp second) context =
      mapTypeContext second (mapTypeContext first context) := by
  apply list_map_comp_of_mem
  intro entry membership
  rcases entry with ⟨name, type⟩
  simp only [mapTypeExpr_comp]

@[simp] theorem mapEquation_id (equation : Equation) :
    mapEquation LanguageDefSymbolMap.id equation = equation := by
  cases equation
  simp only [mapEquation]
  rw [mapTypeContext_id]
  rw [list_map_eq_self_of_mem _ _ fun premise _ => mapPremise_id premise]
  rw [mapPattern_id, mapPattern_id]
  rfl

@[simp] theorem mapEquation_comp (first second : LanguageDefSymbolMap)
    (equation : Equation) :
    mapEquation (first.comp second) equation =
      mapEquation second (mapEquation first equation) := by
  cases equation
  simp only [mapEquation]
  rw [mapTypeContext_comp]
  rw [list_map_comp_of_mem _ _ _ _ fun premise _ =>
    mapPremise_comp first second premise]
  rw [mapPattern_comp, mapPattern_comp]
  rfl

@[simp] theorem mapRewriteRule_id (rewrite : RewriteRule) :
    mapRewriteRule LanguageDefSymbolMap.id rewrite = rewrite := by
  cases rewrite
  simp only [mapRewriteRule]
  rw [mapTypeContext_id]
  rw [list_map_eq_self_of_mem _ _ fun premise _ => mapPremise_id premise]
  rw [mapPattern_id, mapPattern_id]
  rfl

@[simp] theorem mapRewriteRule_comp (first second : LanguageDefSymbolMap)
    (rewrite : RewriteRule) :
    mapRewriteRule (first.comp second) rewrite =
      mapRewriteRule second (mapRewriteRule first rewrite) := by
  cases rewrite
  simp only [mapRewriteRule]
  rw [mapTypeContext_comp]
  rw [list_map_comp_of_mem _ _ _ _ fun premise _ =>
    mapPremise_comp first second premise]
  rw [mapPattern_comp, mapPattern_comp]
  rfl

/-! ## Signature and structural morphisms -/

/-- The weakest map needed by the declaration-derived typing judgment.
Constructor profiles are preserved, while parser notation and host evaluator
metadata may change or disappear.  Equations and rewrites are deliberately
outside this interface. -/
structure TypingMorphism (source target : ValidatedLanguageDef) where
  symbols : LanguageDefSymbolMap
  mapsTypes : ∀ declaration, List.Mem declaration source.language.types →
    List.Mem (mapTypeDecl symbols declaration) target.language.types
  mapsTerms : ∀ rule, List.Mem rule source.language.terms →
    ∃ targetRule, List.Mem targetRule target.language.terms ∧
      targetRule.label = symbols.constructor rule.label ∧
      targetRule.category = symbols.sort rule.category ∧
      targetRule.params = rule.params.map (mapTermParam symbols)

namespace TypingMorphism

/-- Typing maps are proof-irrelevantly determined by their symbol action and
therefore carry no hidden operational choice. -/
@[ext]
theorem ext {source target : ValidatedLanguageDef}
    {first second : TypingMorphism source target}
    (symbols : first.symbols = second.symbols) : first = second := by
  cases first
  cases second
  cases symbols
  rfl

/-- Identity on the typed profile of a validated language. -/
def id (language : ValidatedLanguageDef) : TypingMorphism language language where
  symbols := LanguageDefSymbolMap.id
  mapsTypes declaration membership := by
    rw [mapTypeDecl_id]
    exact membership
  mapsTerms rule membership := by
    refine ⟨rule, membership, ?_, ?_, ?_⟩
    · rfl
    · rfl
    · have parameters :=
        congrArg GrammarRule.params (mapGrammarRule_id rule)
      exact parameters.symm

/-- Composition of typed-profile maps. -/
def comp {first second third : ValidatedLanguageDef}
    (left : TypingMorphism first second)
    (right : TypingMorphism second third) :
    TypingMorphism first third where
  symbols := left.symbols.comp right.symbols
  mapsTypes declaration membership := by
    rw [mapTypeDecl_comp]
    exact right.mapsTypes _ (left.mapsTypes declaration membership)
  mapsTerms rule membership := by
    obtain ⟨middleRule, middleMembership, middleLabel, middleCategory,
      middleParameters⟩ := left.mapsTerms rule membership
    obtain ⟨targetRule, targetMembership, targetLabel, targetCategory,
      targetParameters⟩ := right.mapsTerms middleRule middleMembership
    refine ⟨targetRule, targetMembership, ?_, ?_, ?_⟩
    · rw [targetLabel, middleLabel]
      rfl
    · rw [targetCategory, middleCategory]
      rfl
    · rw [targetParameters, middleParameters, List.map_map]
      exact List.map_congr_left fun parameter _ =>
        (mapTermParam_comp left.symbols right.symbols parameter).symm

end TypingMorphism

/-- A map of the full typed signature underlying a validated language.
It preserves complete declared sort and constructor declarations, including
concrete-syntax metadata, but says nothing about equations or rewrites. -/
structure SignatureMorphism (source target : ValidatedLanguageDef) where
  symbols : LanguageDefSymbolMap
  mapsTypes : ∀ declaration, List.Mem declaration source.language.types →
    List.Mem (mapTypeDecl symbols declaration) target.language.types
  mapsTerms : ∀ rule, List.Mem rule source.language.terms →
    List.Mem (mapGrammarRule symbols rule) target.language.terms

namespace SignatureMorphism

/-- Forget full constructor-declaration equality while retaining the exact
profile action used by the typing judgment. -/
def toTyping {source target : ValidatedLanguageDef}
    (morphism : SignatureMorphism source target) :
    TypingMorphism source target where
  symbols := morphism.symbols
  mapsTypes := morphism.mapsTypes
  mapsTerms rule membership := by
    refine ⟨mapGrammarRule morphism.symbols rule,
      morphism.mapsTerms rule membership, ?_, ?_, ?_⟩ <;>
      rfl

/-- Signature maps are proof-irrelevantly determined by their symbol action. -/
@[ext]
theorem ext {source target : ValidatedLanguageDef}
    {first second : SignatureMorphism source target}
    (symbols : first.symbols = second.symbols) : first = second := by
  cases first
  cases second
  cases symbols
  rfl

/-- Identity on a validated typed signature. -/
def id (language : ValidatedLanguageDef) :
    SignatureMorphism language language where
  symbols := LanguageDefSymbolMap.id
  mapsTypes declaration membership := by
    rw [mapTypeDecl_id]
    exact membership
  mapsTerms rule membership := by
    rw [mapGrammarRule_id]
    exact membership

/-- Composition of typed-signature maps. -/
def comp {first second third : ValidatedLanguageDef}
    (left : SignatureMorphism first second)
    (right : SignatureMorphism second third) :
    SignatureMorphism first third where
  symbols := left.symbols.comp right.symbols
  mapsTypes declaration membership := by
    rw [mapTypeDecl_comp]
    exact right.mapsTypes _ (left.mapsTypes declaration membership)
  mapsTerms rule membership := by
    rw [mapGrammarRule_comp]
    exact right.mapsTerms _ (left.mapsTerms rule membership)

end SignatureMorphism

/-- A structural map between exact validated language definitions.  Each
source declaration is carried to a declaration of the target; the
target may contain additional declarations. -/
structure StructuralMorphism (source target : ValidatedLanguageDef) where
  symbols : LanguageDefSymbolMap
  mapsTypes : ∀ declaration, List.Mem declaration source.language.types →
    List.Mem (mapTypeDecl symbols declaration) target.language.types
  mapsTerms : ∀ rule, List.Mem rule source.language.terms →
    List.Mem (mapGrammarRule symbols rule) target.language.terms
  mapsEquations : ∀ equation, List.Mem equation source.language.equations →
    List.Mem (mapEquation symbols equation) target.language.equations
  mapsRewrites : ∀ rewrite, List.Mem rewrite source.language.rewrites →
    List.Mem (mapRewriteRule symbols rewrite) target.language.rewrites

namespace StructuralMorphism

/-- Forget equation and rewrite preservation while retaining
the exact typed-signature action of a structural `LanguageDef` map. -/
def toSignature {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target) :
    SignatureMorphism source target where
  symbols := morphism.symbols
  mapsTypes := morphism.mapsTypes
  mapsTerms := morphism.mapsTerms

/-- Forget directly to the weakest typed-profile action. -/
def toTyping {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target) :
    TypingMorphism source target :=
  morphism.toSignature.toTyping

/-! ### Action on declared symbols -/

/-- A carrier sort selected from the exact declaration list. -/
abbrev DeclaredSort (language : ValidatedLanguageDef) :=
  { declaration : TypeDecl // List.Mem declaration language.language.types }

/-- A constructor selected from the exact declaration list. -/
abbrev DeclaredConstructor (language : ValidatedLanguageDef) :=
  { declaration : GrammarRule // List.Mem declaration language.language.terms }

/-- An equation selected from the exact declaration list. -/
abbrev DeclaredEquation (language : ValidatedLanguageDef) :=
  { declaration : Equation // List.Mem declaration language.language.equations }

/-- A rewrite selected from the exact declaration list. -/
abbrev DeclaredRewrite (language : ValidatedLanguageDef) :=
  { declaration : RewriteRule // List.Mem declaration language.language.rewrites }

/-- Validation makes the name projection from declared carrier sorts
injective, so a typed generated namespace may retain declaration identity
without relying on raw strings. -/
theorem declaredSortName_injective (language : ValidatedLanguageDef) :
    Function.Injective
      (fun sort : DeclaredSort language => sort.1.name) := by
  intro left right equality
  apply Subtype.ext
  exact List.inj_on_of_nodup_map
    (LanguageDef.typeNames_nodup_of_validate_eq_nil
      language.language language.valid)
    left.2 right.2 equality

/-- Structural maps carry declared carrier sorts to declared carrier sorts. -/
def mapSort {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (sort : DeclaredSort source) : DeclaredSort target :=
  ⟨mapTypeDecl morphism.symbols sort.1,
    morphism.mapsTypes sort.1 sort.2⟩

/-- Structural maps carry declared constructors to declared constructors. -/
def mapConstructor {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (constructor : DeclaredConstructor source) : DeclaredConstructor target :=
  ⟨mapGrammarRule morphism.symbols constructor.1,
    morphism.mapsTerms constructor.1 constructor.2⟩

/-- Structural maps carry declared equations to declared equations. -/
def mapEquation {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (equation : DeclaredEquation source) : DeclaredEquation target :=
  ⟨Mettapedia.GSLT.LanguageDef.mapEquation morphism.symbols equation.1,
    morphism.mapsEquations equation.1 equation.2⟩

/-- Structural maps carry declared rewrites to declared rewrites. -/
def mapRewrite {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (rewrite : DeclaredRewrite source) : DeclaredRewrite target :=
  ⟨mapRewriteRule morphism.symbols rewrite.1,
    morphism.mapsRewrites rewrite.1 rewrite.2⟩

/-- Equality of structural morphisms is determined by their symbol action;
all declaration-preservation fields are proofs. -/
@[ext]
theorem ext {source target : ValidatedLanguageDef}
    {first second : StructuralMorphism source target}
    (symbols : first.symbols = second.symbols) : first = second := by
  cases first
  cases second
  cases symbols
  rfl

/-- Identity structural morphism. -/
def id (language : ValidatedLanguageDef) : StructuralMorphism language language where
  symbols := LanguageDefSymbolMap.id
  mapsTypes declaration membership := by
    rw [mapTypeDecl_id]
    exact membership
  mapsTerms rule membership := by
    rw [mapGrammarRule_id]
    exact membership
  mapsEquations equation membership := by
    rw [mapEquation_id]
    exact membership
  mapsRewrites rewrite membership := by
    rw [mapRewriteRule_id]
    exact membership

/-- Composition of structural maps. -/
def comp {first second third : ValidatedLanguageDef}
    (left : StructuralMorphism first second)
    (right : StructuralMorphism second third) :
    StructuralMorphism first third where
  symbols := left.symbols.comp right.symbols
  mapsTypes declaration membership := by
    rw [mapTypeDecl_comp]
    exact right.mapsTypes _ (left.mapsTypes declaration membership)
  mapsTerms rule membership := by
    rw [mapGrammarRule_comp]
    exact right.mapsTerms _ (left.mapsTerms rule membership)
  mapsEquations equation membership := by
    rw [mapEquation_comp]
    exact right.mapsEquations _ (left.mapsEquations equation membership)
  mapsRewrites rewrite membership := by
    rw [mapRewriteRule_comp]
    exact right.mapsRewrites _ (left.mapsRewrites rewrite membership)

@[simp] theorem mapSort_id (language : ValidatedLanguageDef)
    (sort : DeclaredSort language) :
    (id language).mapSort sort = sort := by
  apply Subtype.ext
  exact mapTypeDecl_id sort.1

@[simp] theorem mapSort_comp {first second third : ValidatedLanguageDef}
    (left : StructuralMorphism first second)
    (right : StructuralMorphism second third)
    (sort : DeclaredSort first) :
    (comp left right).mapSort sort = right.mapSort (left.mapSort sort) := by
  apply Subtype.ext
  exact mapTypeDecl_comp left.symbols right.symbols sort.1

@[simp] theorem mapConstructor_id (language : ValidatedLanguageDef)
    (constructor : DeclaredConstructor language) :
    (id language).mapConstructor constructor = constructor := by
  apply Subtype.ext
  exact mapGrammarRule_id constructor.1

@[simp] theorem mapConstructor_comp
    {first second third : ValidatedLanguageDef}
    (left : StructuralMorphism first second)
    (right : StructuralMorphism second third)
    (constructor : DeclaredConstructor first) :
    (comp left right).mapConstructor constructor =
      right.mapConstructor (left.mapConstructor constructor) := by
  apply Subtype.ext
  exact mapGrammarRule_comp left.symbols right.symbols constructor.1

@[simp] theorem mapEquation_id (language : ValidatedLanguageDef)
    (equation : DeclaredEquation language) :
    (id language).mapEquation equation = equation := by
  apply Subtype.ext
  exact Mettapedia.GSLT.LanguageDef.mapEquation_id equation.1

@[simp] theorem mapEquation_comp {first second third : ValidatedLanguageDef}
    (left : StructuralMorphism first second)
    (right : StructuralMorphism second third)
    (equation : DeclaredEquation first) :
    (comp left right).mapEquation equation =
      right.mapEquation (left.mapEquation equation) := by
  apply Subtype.ext
  exact Mettapedia.GSLT.LanguageDef.mapEquation_comp
    left.symbols right.symbols equation.1

@[simp] theorem mapRewrite_id (language : ValidatedLanguageDef)
    (rewrite : DeclaredRewrite language) :
    (id language).mapRewrite rewrite = rewrite := by
  apply Subtype.ext
  exact mapRewriteRule_id rewrite.1

@[simp] theorem mapRewrite_comp {first second third : ValidatedLanguageDef}
    (left : StructuralMorphism first second)
    (right : StructuralMorphism second third)
    (rewrite : DeclaredRewrite first) :
    (comp left right).mapRewrite rewrite =
      right.mapRewrite (left.mapRewrite rewrite) := by
  apply Subtype.ext
  exact mapRewriteRule_comp left.symbols right.symbols rewrite.1

end StructuralMorphism

/-- Exact validated language definitions and their structural operational-
theory maps form a Mathlib category. -/
instance : CategoryTheory.Category ValidatedLanguageDef where
  Hom := StructuralMorphism
  id := StructuralMorphism.id
  comp := StructuralMorphism.comp
  id_comp morphism := by
    apply StructuralMorphism.ext
    rfl
  comp_id morphism := by
    apply StructuralMorphism.ext
    rfl
  assoc first second third := by
    apply StructuralMorphism.ext
    rfl

/-! ## Positive and negative controls -/

/-- Every validated language has a structural identity map. -/
theorem structural_identity_exists (language : ValidatedLanguageDef) :
    Nonempty (StructuralMorphism language language) :=
  ⟨StructuralMorphism.id language⟩

/-- A language with at least one constructor cannot structurally map into a
language with no constructors.  This rules out the degenerate constant-map
masquerade at the declaration boundary. -/
theorem no_structural_morphism_to_empty_terms
    (source target : ValidatedLanguageDef)
    (sourceHasTerm : source.language.terms ≠ [])
    (targetHasNoTerms : target.language.terms = []) :
    ¬ Nonempty (StructuralMorphism source target) := by
  rintro ⟨morphism⟩
  obtain ⟨rule, membership⟩ :=
    List.exists_mem_of_ne_nil source.language.terms sourceHasTerm
  have mapped := morphism.mapsTerms rule membership
  rw [targetHasNoTerms] at mapped
  cases mapped

end Mettapedia.GSLT.LanguageDef
