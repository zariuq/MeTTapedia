import Mettapedia.GSLT.LanguageDef.WellSorted
import Mettapedia.OSLF.Syntax.BindingSignature

/-!
# Binding syntax derived from a language definition

Constructor operators retain their membership in the authored `LanguageDef`.
Binding arities are determined by its existing parameter typing convention:
an abstraction binds its domain, while a multiple abstraction ranges over the
finite repetitions of its domain. No second constructor inventory is authored.

The structural lambda, substitution, and collection forms are precisely the
representation forms of `WellSorted.HasType`. Collection operators here have
no schema rest; declared metavariables and their sequence substitutions belong
to the separate metavariable extension, not to object operator names.

Erasure is proved against the existing typing judgment. This module does not
yet derive conditional rule instantiation or its executable matcher.
-/

namespace Mettapedia.GSLT.LanguageDef.BindingSyntax

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Binding
open Mettapedia.GSLT.LanguageDef.WellSorted

set_option autoImplicit false

/-- The binding argument specified by one authored parameter. The constructors
follow `parameterType?`, including its established same-sort shorthand. -/
inductive ParameterScope : TermParam → List TypeExpr → TypeExpr → Type where
  | simple (name : String) (type : TypeExpr) :
      ParameterScope (.simple name type) [] type
  | abstraction (binder : Option String) (name : String)
      (domain codomain : TypeExpr) :
      ParameterScope (.abstractionNamed binder name (.arrow domain codomain))
        [domain] codomain
  | abstractionBase (binder : Option String) (name sort : String) :
      ParameterScope (.abstractionNamed binder name (.base sort))
        [.base sort] (.base sort)
  | multiAbstraction (binders : List String) (name : String)
      (domain codomain : TypeExpr) (count : Nat) :
      ParameterScope
        (.multiAbstractionNamed binders name (.arrow (.multiBinder domain) codomain))
        (List.replicate count domain) codomain
  | multiAbstractionBase (binders : List String) (name sort : String) (count : Nat) :
      ParameterScope (.multiAbstractionNamed binders name (.base sort))
        (List.replicate count (.base sort)) (.base sort)

/-- Parameter order and every binding prefix come from the authored list. -/
inductive ParameterScopes : List TermParam → List (List TypeExpr × TypeExpr) → Type where
  | nil : ParameterScopes [] []
  | cons {parameter : TermParam} {parameters : List TermParam}
      {binders : List TypeExpr} {bodyType : TypeExpr}
      {arity : List (List TypeExpr × TypeExpr)} :
      ParameterScope parameter binders bodyType → ParameterScopes parameters arity →
      ParameterScopes (parameter :: parameters) ((binders, bodyType) :: arity)

/-- Reinsert the representation binder removed by an intrinsic binding arity. -/
def ParameterScope.wrap {parameter : TermParam} {binders : List TypeExpr}
    {bodyType : TypeExpr} (scope : ParameterScope parameter binders bodyType)
    (body : Pattern) : Pattern :=
  match scope with
  | .simple _ _ => body
  | .abstraction _ _ _ _ => .lambda none body
  | .abstractionBase _ _ _ => .lambda none body
  | .multiAbstraction _ _ _ _ count => .multiLambda count [] body
  | .multiAbstractionBase _ _ _ count => .multiLambda count [] body

theorem ParameterScope.wrap_typed
    {language : LanguageDef} {free : FreeTypeContext} {bound : List TypeExpr}
    {parameter : TermParam} {binders : List TypeExpr} {bodyType : TypeExpr}
    (scope : ParameterScope parameter binders bodyType) {body : Pattern}
    (typed : HasType language free (binders ++ bound) body bodyType) :
    ∃ expected, MatchesParameterRepresentation parameter (scope.wrap body) ∧
      parameterType? parameter = some expected ∧
      HasType language free bound (scope.wrap body) expected := by
  cases scope with
  | simple name type => exact ⟨_, trivial, rfl, typed⟩
  | abstraction binder name domain codomain =>
      exact ⟨_, trivial, rfl, HasType.lambda typed⟩
  | abstractionBase binder name sort =>
      exact ⟨.arrow (.base sort) (.base sort), trivial, rfl, HasType.lambda typed⟩
  | multiAbstraction binders name domain codomain count =>
      exact ⟨_, trivial, rfl,
        HasType.multiLambda typed⟩
  | multiAbstractionBase binders name sort count =>
      exact ⟨.arrow (.multiBinder (.base sort)) (.base sort), trivial, rfl,
        HasType.multiLambda typed⟩

/-- Object operators derived from constructor membership and the existing
structural representation forms. Binding counts index the multiple-binder
family; they do not restrict the general parameter declaration. -/
inductive Operator (language : LanguageDef) : TypeExpr → Type where
  | constructor (rule : GrammarRule) (member : rule ∈ language.terms)
      (ordinary : ¬ UsesBareCollection rule)
      {arity : List (List TypeExpr × TypeExpr)}
      (parameters : ParameterScopes rule.params arity) :
      Operator language (.base rule.category)
  | collectionConstructor (rule : GrammarRule) (member : rule ∈ language.terms)
      (parameterName : String) (kind : CollType) (elementType : TypeExpr)
      (shape : rule.params = [.simple parameterName (.collection kind elementType)])
      (count : Nat) : Operator language (.base rule.category)
  | lambda (domain codomain : TypeExpr) : Operator language (.arrow domain codomain)
  | multiLambda (domain codomain : TypeExpr) (count : Nat) :
      Operator language (.arrow (.multiBinder domain) codomain)
  | subst (domain codomain : TypeExpr) : Operator language codomain
  | collection (kind : CollType) (elementType : TypeExpr) (count : Nat) :
      Operator language (.collection kind elementType)

/-- The intrinsic signature of the authored constructor declarations and their
typed representation forms. Sorts are the existing `TypeExpr` carrier. -/
abbrev signatureOf (language : LanguageDef) : Signature where
  Srt := TypeExpr
  Op := Operator language
  arity := fun {_} operator => match operator with
    | .constructor _ _ _ (arity := arity) _ => arity
    | .collectionConstructor _ _ _ _ elementType _ count =>
        List.replicate count ([], elementType)
    | .lambda domain codomain => [([domain], codomain)]
    | .multiLambda domain codomain count => [(List.replicate count domain, codomain)]
    | .subst domain codomain => [([domain], codomain), ([], domain)]
    | .collection _ elementType count => List.replicate count ([], elementType)

/-- A variable's index ignores its sort, while retaining its context position. -/
def variableIndex {SortType : Type} : {bound : List SortType} → {sort : SortType} →
    Var bound sort → Nat
  | _, _, .zero => 0
  | _, _, .succ position => variableIndex position + 1

theorem variableIndex_lookup {SortType : Type} :
    ∀ {bound : List SortType} {sort : SortType} (position : Var bound sort),
      bound[variableIndex position]? = some sort
  | _, _, .zero => rfl
  | _, _, .succ position => variableIndex_lookup position

mutual
def erase {language : LanguageDef} : {bound : List TypeExpr} → {type : TypeExpr} →
    Term (signatureOf language) bound type → Pattern
  | _, _, .var position => .bvar (variableIndex position)
  | _, _, .op operator arguments =>
      match operator with
      | .constructor rule _ _ parameters =>
          .apply rule.label (eraseConstructorArguments parameters arguments)
      | .collectionConstructor _ _ _ kind _ _ _ =>
          .collection kind (eraseArguments arguments) none
      | .lambda _ _ =>
          match arguments with
          | .cons body .nil => .lambda none (erase body)
      | .multiLambda _ _ count =>
          match arguments with
          | .cons body .nil => .multiLambda count [] (erase body)
      | .subst _ _ =>
          match arguments with
          | .cons body (.cons replacement .nil) => .subst (erase body) (erase replacement)
      | .collection kind _ _ => .collection kind (eraseArguments arguments) none

def eraseArguments {language : LanguageDef} :
    {arity : List (List TypeExpr × TypeExpr)} → {bound : List TypeExpr} →
    Args (signatureOf language) arity bound → List Pattern
  | _, _, .nil => []
  | _, _, .cons head tail => erase head :: eraseArguments tail

def eraseConstructorArguments {language : LanguageDef} :
    {parameters : List TermParam} → {arity : List (List TypeExpr × TypeExpr)} →
    {bound : List TypeExpr} → ParameterScopes parameters arity →
    Args (signatureOf language) arity bound → List Pattern
  | _, _, _, .nil, .nil => []
  | _, _, _, .cons scope scopes, .cons head tail =>
      scope.wrap (erase head) :: eraseConstructorArguments scopes tail
end

theorem elements_typed_of_replicate
    {language : LanguageDef} {free : FreeTypeContext} {bound : List TypeExpr}
    {elementType : TypeExpr} : ∀ {count : Nat} {elements : List Pattern},
      List.Forall₂
        (fun (slot : List TypeExpr × TypeExpr) element =>
          HasType language free (slot.1 ++ bound) element slot.2)
        (List.replicate count ([], elementType)) elements →
      ElementsHaveType language free bound elements elementType
  | 0, _, .nil => .nil _ _
  | _ + 1, _, .cons head tail =>
      .cons head (elements_typed_of_replicate tail)

mutual
/-- Every erased intrinsic term satisfies the original language's typing
judgment in the same ordered context. -/
theorem erase_typed {language : LanguageDef} :
    ∀ {bound : List TypeExpr} {type : TypeExpr}
      (term : Term (signatureOf language) bound type),
      HasType language FreeTypeContext.empty bound (erase term) type
  | _, _, .var position => .bvar (variableIndex_lookup position)
  | _, _, .op (.constructor _ member ordinary parameters) arguments =>
      .constructor member ordinary (eraseConstructorArguments_typed parameters arguments)
  | _, _, .op (.collectionConstructor _ member _ _ _ shape _) arguments =>
      .collectionConstructor member shape
        (elements_typed_of_replicate (eraseArguments_typed arguments))
  | _, _, .op (.lambda _ _) arguments =>
      match arguments with
      | .cons body .nil => .lambda (erase_typed body)
  | _, _, .op (.multiLambda _ _ _) arguments =>
      match arguments with
      | .cons body .nil => .multiLambda (erase_typed body)
  | _, _, .op (.subst _ _) arguments =>
      match arguments with
      | .cons body (.cons replacement .nil) =>
          .subst (erase_typed body) (erase_typed replacement)
  | _, _, .op (.collection _ _ _) arguments =>
      .collection (elements_typed_of_replicate (eraseArguments_typed arguments))

theorem eraseArguments_typed {language : LanguageDef} :
    ∀ {arity : List (List TypeExpr × TypeExpr)} {bound : List TypeExpr}
      (arguments : Args (signatureOf language) arity bound),
      List.Forall₂
        (fun slot argument =>
          HasType language FreeTypeContext.empty (slot.1 ++ bound) argument slot.2)
        arity (eraseArguments arguments)
  | _, _, .nil => .nil
  | _, _, .cons head tail => .cons (erase_typed head) (eraseArguments_typed tail)

theorem eraseConstructorArguments_typed {language : LanguageDef} :
    ∀ {parameters : List TermParam} {arity : List (List TypeExpr × TypeExpr)}
      {bound : List TypeExpr} (scopes : ParameterScopes parameters arity)
      (arguments : Args (signatureOf language) arity bound),
      ArgumentsHaveTypes language FreeTypeContext.empty bound
        (eraseConstructorArguments scopes arguments) parameters
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons scope scopes, .cons head tail => by
      obtain ⟨expected, representation, expectedType, typed⟩ :=
        scope.wrap_typed (erase_typed head)
      exact .cons representation expectedType typed
        (eraseConstructorArguments_typed scopes tail)
end

theorem erase_wellScoped {language : LanguageDef} {bound : List TypeExpr}
    {type : TypeExpr} (term : Term (signatureOf language) bound type) :
    (erase term).isWellScopedAt bound.length = true :=
  (erase_typed term).isWellScopedAt

end Mettapedia.GSLT.LanguageDef.BindingSyntax
