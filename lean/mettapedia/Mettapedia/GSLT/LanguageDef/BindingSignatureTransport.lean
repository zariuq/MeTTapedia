import Mettapedia.GSLT.LanguageDef.BindingSignature
import Mettapedia.OSLF.Syntax.SignatureMorphism

/-!
# Structural transport of the derived binding signature

The operator action comes from the structural language map's actual constructor
membership proof. Parameter scopes and their multiplicities are transported
from the authored declaration; no target signature is specified separately.
-/

namespace Mettapedia.GSLT.LanguageDef.BindingSyntax

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Binding
open Mettapedia.GSLT.LanguageDef.WellSorted

set_option autoImplicit false

def ParameterScope.castBinders {parameter : TermParam} {first second : List TypeExpr}
    {bodyType : TypeExpr} (same : first = second)
    (scope : ParameterScope parameter first bodyType) :
    ParameterScope parameter second bodyType := same ▸ scope

@[simp] theorem ParameterScope.wrap_castBinders
    {parameter : TermParam} {first second : List TypeExpr} {bodyType : TypeExpr}
    (same : first = second) (scope : ParameterScope parameter first bodyType) (body : Pattern) :
    (scope.castBinders same).wrap body = scope.wrap body := by
  cases same
  rfl

def ParameterScope.map (symbols : LanguageDefSymbolMap)
    {parameter : TermParam} {binders : List TypeExpr} {bodyType : TypeExpr}
    (scope : ParameterScope parameter binders bodyType) :
    ParameterScope (mapTermParam symbols parameter)
      (binders.map (mapTypeExpr symbols)) (mapTypeExpr symbols bodyType) := by
  cases scope with
  | simple name type => exact .simple name _
  | abstraction binder name domain codomain => exact .abstraction binder name _ _
  | abstractionBase binder name sort => exact .abstractionBase binder name _
  | multiAbstraction binders name domain codomain count =>
      exact (ParameterScope.multiAbstraction binders name
          (mapTypeExpr symbols domain) (mapTypeExpr symbols bodyType) count).castBinders
            (by simp only [List.map_replicate])
  | multiAbstractionBase binders name sort count =>
      exact (ParameterScope.multiAbstractionBase binders name
        (symbols.sort sort) count).castBinders
          (by simp only [List.map_replicate, mapTypeExpr])

def ParameterScopes.map (symbols : LanguageDefSymbolMap) :
    {parameters : List TermParam} → {arity : List (List TypeExpr × TypeExpr)} →
    ParameterScopes parameters arity →
    ParameterScopes (parameters.map (mapTermParam symbols))
      (mapArities (mapTypeExpr symbols) arity)
  | _, _, .nil => .nil
  | _, _, .cons scope scopes => .cons (scope.map symbols) (scopes.map symbols)

theorem ParameterScope.wrap_map (symbols : LanguageDefSymbolMap)
    {parameter : TermParam} {binders : List TypeExpr} {bodyType : TypeExpr}
    (scope : ParameterScope parameter binders bodyType) (body : Pattern) :
    (scope.map symbols).wrap (mapPattern symbols body) =
      mapPattern symbols (scope.wrap body) := by
  cases scope <;> simp only [ParameterScope.map] <;> try rfl
  all_goals
    erw [ParameterScope.wrap_castBinders]
    rfl

/-- Map every derived operator using the source language's constructor action. -/
def mapOperator {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target) :
    {type : TypeExpr} → Operator source.language type →
      Operator target.language (mapTypeExpr morphism.symbols type)
  | _, .constructor rule member ordinary parameters =>
      .constructor (mapGrammarRule morphism.symbols rule)
        (morphism.mapsTerms rule member)
        (fun bare => ordinary
          ((usesBareCollection_mapGrammarRule_iff morphism.symbols rule).mp bare))
        (parameters.map morphism.symbols)
  | _, .collectionConstructor rule member name kind element shape count =>
      .collectionConstructor (mapGrammarRule morphism.symbols rule)
        (morphism.mapsTerms rule member) name kind (mapTypeExpr morphism.symbols element)
        (by simp only [mapGrammarRule, shape, List.map_cons, List.map_nil,
          mapTermParam, mapTypeExpr]) count
  | _, .lambda domain codomain =>
      .lambda (mapTypeExpr morphism.symbols domain) (mapTypeExpr morphism.symbols codomain)
  | _, .multiLambda domain codomain count =>
      .multiLambda (mapTypeExpr morphism.symbols domain)
        (mapTypeExpr morphism.symbols codomain) count
  | _, .subst domain codomain =>
      .subst (mapTypeExpr morphism.symbols domain) (mapTypeExpr morphism.symbols codomain)
  | _, .collection kind element count =>
      .collection kind (mapTypeExpr morphism.symbols element) count

theorem mapOperator_arity {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target) {type : TypeExpr}
    (operator : Operator source.language type) :
    (signatureOf target.language).arity (mapOperator morphism operator) =
      mapArities (mapTypeExpr morphism.symbols)
        ((signatureOf source.language).arity operator) := by
  cases operator <;>
    simp [mapOperator, signatureOf, mapArities, mapArity, List.map_replicate]

/-- A structural language map induces its binding signature morphism. -/
def signatureMorphism {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target) :
    SigMor (signatureOf source.language) (signatureOf target.language) where
  sortMap := mapTypeExpr morphism.symbols
  opMap := mapOperator morphism
  carriesArity := mapOperator_arity morphism

theorem ParameterScope.wrap_map_identity
    {parameter : TermParam} {binders : List TypeExpr} {bodyType : TypeExpr}
    (scope : ParameterScope parameter binders bodyType) (body : Pattern) :
    (scope.map LanguageDefSymbolMap.id).wrap body = scope.wrap body := by
  simpa only [mapPattern_id] using scope.wrap_map LanguageDefSymbolMap.id body

theorem ParameterScope.wrap_map_composition
    (first second : LanguageDefSymbolMap)
    {parameter : TermParam} {binders : List TypeExpr} {bodyType : TypeExpr}
    (scope : ParameterScope parameter binders bodyType) (body : Pattern) :
    ((scope.map first).map second).wrap (mapPattern second (mapPattern first body)) =
      (scope.map (first.comp second)).wrap (mapPattern (first.comp second) body) := by
  rw [ParameterScope.wrap_map, ParameterScope.wrap_map, ParameterScope.wrap_map,
    mapPattern_comp]

/-- Transport preserves the number and order of recursive argument slots. -/
theorem mapOperator_argument_count {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target) {type : TypeExpr}
    (operator : Operator source.language type) :
    ((signatureOf target.language).arity (mapOperator morphism operator)).length =
      ((signatureOf source.language).arity operator).length := by
  rw [mapOperator_arity]
  exact List.length_map _

/-- The same mapped intrinsic term erases to a term typed by the target
language's original judgment, at the mapped source context and type. -/
theorem mapped_erase_typed {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target) {bound : List TypeExpr}
    {type : TypeExpr} (term : Term (signatureOf source.language) bound type) :
    HasType target.language FreeTypeContext.empty
      (bound.map (mapTypeExpr morphism.symbols))
      (erase ((signatureMorphism morphism).onTerm term))
      (mapTypeExpr morphism.symbols type) :=
  erase_typed ((signatureMorphism morphism).onTerm term)

theorem mapped_erase_wellScoped {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target) {bound : List TypeExpr}
    {type : TypeExpr} (term : Term (signatureOf source.language) bound type) :
    (erase ((signatureMorphism morphism).onTerm term)).isWellScopedAt bound.length = true := by
  simpa only [List.length_map] using
    erase_wellScoped ((signatureMorphism morphism).onTerm term)

/-- Restore parameter wrappers on an erased ordered argument list. Mismatched
lists have no representation; intrinsic arguments always match. -/
private def wrapArguments : {parameters : List TermParam} →
    {arity : List (List TypeExpr × TypeExpr)} →
    ParameterScopes parameters arity → List Pattern → Option (List Pattern)
  | _, _, .nil, [] => some []
  | _, _, .cons scope scopes, head :: tail =>
      (wrapArguments scopes tail).map (scope.wrap head :: ·)
  | _, _, _, _ => none

private theorem wrapArguments_erase {language : LanguageDef} :
    ∀ {parameters : List TermParam} {arity : List (List TypeExpr × TypeExpr)}
      {bound : List TypeExpr} (scopes : ParameterScopes parameters arity)
      (arguments : Args (signatureOf language) arity bound),
      wrapArguments scopes (eraseArguments arguments) =
        some (eraseConstructorArguments scopes arguments)
  | _, _, _, .nil, .nil => rfl
  | _, _, _, .cons scope scopes, .cons head tail => by
      simp only [wrapArguments, eraseArguments, eraseConstructorArguments,
        wrapArguments_erase scopes tail, Option.map_some]

private theorem wrapArguments_map (symbols : LanguageDefSymbolMap) :
    ∀ {parameters : List TermParam} {arity : List (List TypeExpr × TypeExpr)}
      (scopes : ParameterScopes parameters arity) (arguments : List Pattern),
      wrapArguments (scopes.map symbols) (mapPatternList symbols arguments) =
        (wrapArguments scopes arguments).map (mapPatternList symbols)
  | _, _, .nil, [] => rfl
  | _, _, .nil, _ :: _ => rfl
  | _, _, .cons _ _, [] => rfl
  | _, _, .cons scope scopes, head :: tail => by
      change (wrapArguments (scopes.map symbols) (mapPatternList symbols tail)).map
        ((scope.map symbols).wrap (mapPattern symbols head) :: ·) =
        ((wrapArguments scopes tail).map (scope.wrap head :: ·)).map (mapPatternList symbols)
      erw [wrapArguments_map symbols scopes tail]
      simp only [Option.map_map]
      congr 1
      funext values
      change (scope.map symbols).wrap (mapPattern symbols head) ::
        mapPatternList symbols values = _
      rw [ParameterScope.wrap_map]
      rfl

private def representOperator {language : LanguageDef} :
    {type : TypeExpr} → Operator language type → List Pattern → Option Pattern
  | _, .constructor rule _ _ scopes, arguments =>
      (wrapArguments scopes arguments).map (.apply rule.label)
  | _, .collectionConstructor _ _ _ kind _ _ _, arguments =>
      some (.collection kind arguments none)
  | _, .lambda _ _, [body] => some (.lambda none body)
  | _, .multiLambda _ _ count, [body] => some (.multiLambda count [] body)
  | _, .subst _ _, [body, replacement] => some (.subst body replacement)
  | _, .collection kind _ _, arguments => some (.collection kind arguments none)
  | _, _, _ => none

private theorem representOperator_erase {language : LanguageDef} {bound : List TypeExpr}
    {type : TypeExpr} (operator : Operator language type)
    (arguments : Args (signatureOf language) ((signatureOf language).arity operator) bound) :
    representOperator operator (eraseArguments arguments) = some (erase (.op operator arguments)) := by
  cases operator with
  | constructor rule member ordinary scopes =>
      simp only [representOperator, wrapArguments_erase, Option.map_some, erase]
  | collectionConstructor => rfl
  | lambda => exact match arguments with | .cons body .nil => rfl
  | multiLambda => exact match arguments with | .cons body .nil => rfl
  | subst =>
      exact match arguments with | .cons body (.cons replacement .nil) => rfl
  | collection => rfl

private theorem representOperator_map {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target) {type : TypeExpr}
    (operator : Operator source.language type) (arguments : List Pattern) :
    representOperator (mapOperator morphism operator) (mapPatternList morphism.symbols arguments) =
      (representOperator operator arguments).map (mapPattern morphism.symbols) := by
  cases operator with
  | constructor rule member ordinary scopes =>
      change (wrapArguments (scopes.map morphism.symbols)
        (mapPatternList morphism.symbols arguments)).map
          (Pattern.apply (morphism.symbols.constructor rule.label)) = _
      erw [wrapArguments_map]
      simp only [representOperator, Option.map_map]
      rfl
  | collectionConstructor => rfl
  | lambda =>
      cases arguments with
      | nil => rfl
      | cons body tail => cases tail with | nil => rfl | cons _ _ => rfl
  | multiLambda =>
      cases arguments with
      | nil => rfl
      | cons body tail => cases tail with | nil => rfl | cons _ _ => rfl
  | subst =>
      cases arguments with
      | nil => rfl
      | cons body tail =>
          cases tail with
          | nil => rfl
          | cons replacement tail => cases tail with | nil => rfl | cons _ _ => rfl
  | collection => rfl

private theorem eraseArguments_cast {language : LanguageDef}
    {first second : List (List TypeExpr × TypeExpr)} {bound : List TypeExpr}
    (same : first = second) (arguments : Args (signatureOf language) first bound) :
    eraseArguments (castArgsArity same arguments) = eraseArguments arguments := by
  cases same
  rfl

private theorem index_liftVarMap (f : TypeExpr → TypeExpr)
    {first second : List TypeExpr} (positions : VarMap f first second)
    (compatible : ∀ type (position : Var first type),
      variableIndex (positions type position) = variableIndex position) :
    ∀ (binders : List TypeExpr) type (position : Var (binders ++ first) type),
      variableIndex (liftVarMap f positions binders type position) = variableIndex position
  | [], _, position => compatible _ position
  | _ :: binders, _, .zero => rfl
  | _ :: binders, _, .succ position =>
      congrArg (· + 1) (index_liftVarMap f positions compatible binders _ position)

mutual
theorem erase_mapTerm {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target) :
    ∀ {first second : List TypeExpr}
      (positions : VarMap (mapTypeExpr morphism.symbols) first second)
      (_ : ∀ type (position : Var first type),
        variableIndex (positions type position) = variableIndex position)
      {type : TypeExpr} (term : Term (signatureOf source.language) first type),
      erase (mapTerm (signatureMorphism morphism) positions term) =
        mapPattern morphism.symbols (erase term)
  | _, _, positions, compatible, _, .var position => by
      change Pattern.bvar (variableIndex (positions _ position)) =
        Pattern.bvar (variableIndex position)
      rw [compatible]
  | _, _, positions, compatible, _, .op operator arguments => by
      apply Option.some.inj
      change some (erase (Term.op (mapOperator morphism operator)
        (castArgsArity ((signatureMorphism morphism).carriesArity operator).symm
          (mapArgs (signatureMorphism morphism) positions arguments)))) = _
      erw [← representOperator_erase, eraseArguments_cast,
        erase_mapArgs morphism positions compatible, representOperator_map,
        representOperator_erase]
      rfl

theorem erase_mapArgs {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target) :
    ∀ {first second : List TypeExpr}
      (positions : VarMap (mapTypeExpr morphism.symbols) first second)
      (_ : ∀ type (position : Var first type),
        variableIndex (positions type position) = variableIndex position)
      {arity : List (List TypeExpr × TypeExpr)}
      (arguments : Args (signatureOf source.language) arity first),
      eraseArguments (mapArgs (signatureMorphism morphism) positions arguments) =
        mapPatternList morphism.symbols (eraseArguments arguments)
  | _, _, _, _, _, .nil => rfl
  | _, _, positions, compatible, _, .cons (bs := binders) head tail => by
      change erase (mapTerm (signatureMorphism morphism)
        (liftVarMap (mapTypeExpr morphism.symbols) positions binders) head) ::
        eraseArguments (mapArgs (signatureMorphism morphism) positions tail) = _
      rw [erase_mapTerm morphism _ (index_liftVarMap _ positions compatible binders) head,
        erase_mapArgs morphism positions compatible tail]
      rfl
end

private theorem index_mapVar (f : TypeExpr → TypeExpr) :
    ∀ {bound : List TypeExpr} type (position : Var bound type),
      variableIndex (mapVar f type position) = variableIndex position
  | _, _, .zero => rfl
  | _, _, .succ position => congrArg (· + 1) (index_mapVar f _ position)

/-- The actual intrinsic signature action commutes with erasure to the existing
structural LanguageDef action, including all binder wrappers and argument order. -/
theorem erase_onTerm {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target) {bound : List TypeExpr}
    {type : TypeExpr} (term : Term (signatureOf source.language) bound type) :
    erase ((signatureMorphism morphism).onTerm term) =
      mapPattern morphism.symbols (erase term) :=
  erase_mapTerm morphism _ (index_mapVar _) term

theorem erase_onTerm_identity (language : ValidatedLanguageDef)
    {bound : List TypeExpr} {type : TypeExpr}
    (term : Term (signatureOf language.language) bound type) :
    erase ((signatureMorphism (StructuralMorphism.id language)).onTerm term) = erase term := by
  rw [erase_onTerm]
  exact mapPattern_id _

theorem erase_onTerm_composition {first second third : ValidatedLanguageDef}
    (left : StructuralMorphism first second) (right : StructuralMorphism second third)
    {bound : List TypeExpr} {type : TypeExpr}
    (term : Term (signatureOf first.language) bound type) :
    erase ((signatureMorphism (left.comp right)).onTerm term) =
      erase ((signatureMorphism right).onTerm ((signatureMorphism left).onTerm term)) := by
  rw [erase_onTerm, erase_onTerm, erase_onTerm]
  exact mapPattern_comp _ _ _

private theorem scope_heq {p q : TermParam} {bs cs : List TypeExpr} {s t : TypeExpr}
    (first : ParameterScope p bs s) (second : ParameterScope q cs t)
    (parameters : p = q) (binders : bs = cs) : HEq first second := by
  cases first <;> cases second <;> cases parameters <;> try rfl
  all_goals
    have counts := congrArg List.length binders
    simp only [List.length_replicate] at counts
    cases counts
    rfl

private theorem scopes_unique {parameters : List TermParam}
    {arity : List (List TypeExpr × TypeExpr)}
    (first second : ParameterScopes parameters arity) : first = second := by
  induction first with
  | nil => cases second; rfl
  | cons scope scopes ih =>
      cases second with
      | cons other others =>
          cases eq_of_heq (scope_heq scope other rfl rfl)
          cases ih others
          rfl

private theorem constructor_heq {language : LanguageDef} {first second : GrammarRule}
    {a b : List (List TypeExpr × TypeExpr)}
    (firstMember : first ∈ language.terms) (secondMember : second ∈ language.terms)
    (firstOrdinary : ¬ UsesBareCollection first) (secondOrdinary : ¬ UsesBareCollection second)
    (firstScopes : ParameterScopes first.params a) (secondScopes : ParameterScopes second.params b)
    (rules : first = second) (arities : a = b) :
    HEq (Operator.constructor first firstMember firstOrdinary firstScopes)
      (Operator.constructor second secondMember secondOrdinary secondScopes) := by
  cases rules
  cases arities
  cases scopes_unique firstScopes secondScopes
  rfl

private theorem collectionConstructor_heq {language : LanguageDef} {first second : GrammarRule}
    (firstMember : first ∈ language.terms) (secondMember : second ∈ language.terms)
    (name : String) (kind : CollType) (element other : TypeExpr)
    (firstShape : first.params = [.simple name (.collection kind element)])
    (secondShape : second.params = [.simple name (.collection kind other)]) (count : Nat)
    (rules : first = second) (elements : element = other) :
    HEq (Operator.collectionConstructor first firstMember name kind element firstShape count)
      (Operator.collectionConstructor second secondMember name kind other secondShape count) := by
  cases rules
  cases elements
  rfl

theorem mapOperator_identity (language : ValidatedLanguageDef) {type : TypeExpr}
    (operator : Operator language.language type) :
    HEq (mapOperator (StructuralMorphism.id language) operator) operator := by
  cases operator with
  | constructor rule member ordinary scopes =>
      apply constructor_heq
      · exact mapGrammarRule_id rule
      · have types : mapTypeExpr LanguageDefSymbolMap.id = id := funext mapTypeExpr_id
        rw [show (StructuralMorphism.id language).symbols = LanguageDefSymbolMap.id from rfl,
          types]
        exact mapArities_id _
  | collectionConstructor rule member name kind element shape count =>
      apply collectionConstructor_heq
      · exact mapGrammarRule_id rule
      · exact mapTypeExpr_id element
  | lambda domain codomain =>
      change HEq (Operator.lambda (language := language.language)
        (mapTypeExpr LanguageDefSymbolMap.id domain) (mapTypeExpr LanguageDefSymbolMap.id codomain)) _
      rw [mapTypeExpr_id, mapTypeExpr_id]
  | multiLambda domain codomain count =>
      change HEq (Operator.multiLambda (language := language.language)
        (mapTypeExpr LanguageDefSymbolMap.id domain) (mapTypeExpr LanguageDefSymbolMap.id codomain) count) _
      rw [mapTypeExpr_id, mapTypeExpr_id]
  | subst domain codomain =>
      change HEq (Operator.subst (language := language.language)
        (mapTypeExpr LanguageDefSymbolMap.id domain) (mapTypeExpr LanguageDefSymbolMap.id type)) _
      rw [mapTypeExpr_id, mapTypeExpr_id]
  | collection kind element count =>
      change HEq (Operator.collection (language := language.language) kind
        (mapTypeExpr LanguageDefSymbolMap.id element) count) _
      rw [mapTypeExpr_id]

theorem mapOperator_composition {first second third : ValidatedLanguageDef}
    (left : StructuralMorphism first second) (right : StructuralMorphism second third)
    {type : TypeExpr} (operator : Operator first.language type) :
    HEq (mapOperator (left.comp right) operator)
      (mapOperator right (mapOperator left operator)) := by
  cases operator with
  | constructor rule member ordinary scopes =>
      apply constructor_heq
      · exact mapGrammarRule_comp left.symbols right.symbols rule
      · rw [mapArities_comp]
        have types : mapTypeExpr (left.symbols.comp right.symbols) =
            fun t => mapTypeExpr right.symbols (mapTypeExpr left.symbols t) :=
          funext (mapTypeExpr_comp left.symbols right.symbols)
        exact congrArg (fun f => mapArities f _) types
  | collectionConstructor rule member name kind element shape count =>
      apply collectionConstructor_heq
      · exact mapGrammarRule_comp left.symbols right.symbols rule
      · exact mapTypeExpr_comp left.symbols right.symbols element
  | lambda domain codomain =>
      change HEq (Operator.lambda (language := third.language)
        (mapTypeExpr (left.symbols.comp right.symbols) domain)
        (mapTypeExpr (left.symbols.comp right.symbols) codomain)) _
      rw [mapTypeExpr_comp, mapTypeExpr_comp]
      rfl
  | multiLambda domain codomain count =>
      change HEq (Operator.multiLambda (language := third.language)
        (mapTypeExpr (left.symbols.comp right.symbols) domain)
        (mapTypeExpr (left.symbols.comp right.symbols) codomain) count) _
      rw [mapTypeExpr_comp, mapTypeExpr_comp]
      rfl
  | subst domain codomain =>
      change HEq (Operator.subst (language := third.language)
        (mapTypeExpr (left.symbols.comp right.symbols) domain)
        (mapTypeExpr (left.symbols.comp right.symbols) type)) _
      rw [mapTypeExpr_comp, mapTypeExpr_comp]
      rfl
  | collection kind element count =>
      change HEq (Operator.collection (language := third.language) kind
        (mapTypeExpr (left.symbols.comp right.symbols) element) count) _
      rw [mapTypeExpr_comp]
      rfl

private theorem sigMor_eq {S T : Signature} (F G : SigMor S T)
    (sorts : F.sortMap = G.sortMap)
    (operators : ∀ s (o : S.Op s), HEq (F.opMap o) (G.opMap o)) : F = G := by
  cases F with
  | mk fs fo fa =>
      cases G with
      | mk gs go ga =>
          dsimp only at sorts operators
          cases sorts
          have same : @fo = @go := by
            funext s o
            exact eq_of_heq (operators s o)
          cases same
          rfl

theorem signatureMorphism_identity (language : ValidatedLanguageDef) :
    signatureMorphism (StructuralMorphism.id language) =
      SigMor.ident (signatureOf language.language) := by
  apply sigMor_eq
  · exact funext mapTypeExpr_id
  · intro s operator
    exact mapOperator_identity language operator

theorem signatureMorphism_composition {first second third : ValidatedLanguageDef}
    (left : StructuralMorphism first second) (right : StructuralMorphism second third) :
    signatureMorphism (left.comp right) =
      (signatureMorphism left).comp (signatureMorphism right) := by
  apply sigMor_eq
  · exact funext (mapTypeExpr_comp left.symbols right.symbols)
  · intro s operator
    exact mapOperator_composition left right operator

#print axioms signatureMorphism
#print axioms ParameterScope.wrap_map
#print axioms mapOperator_arity
#print axioms mapped_erase_typed
#print axioms mapped_erase_wellScoped
#print axioms erase_onTerm
#print axioms signatureMorphism_identity
#print axioms signatureMorphism_composition

end Mettapedia.GSLT.LanguageDef.BindingSyntax
