import Mettapedia.Languages.Agda.Structural.StaticSyntax

/-!
# Finite-universe Pi statics as ordered structural rule data

The rules act on the binder-aware signature, using the generic substitution
action for beta instantiation. Each constructor stores exactly its local rule
parameters; recursive evidence is generated from the ordered premise list by
the shared indexed-polynomial construction.

The finite Set, Pi, variable and application rules follow Cockx's Agda Core
(`Syntax.agda`: `sortType`, `piSort`; `Typing.agda`: `TyType`, `TyPi`,
`TyLam`, `TyAppE`, `TyArg`). Typed conversion, beta and function extensionality
follow the corresponding relevant Pi rules in `logrel-mltt/Definition/Typed.agda`.
Here its single universe is replaced by the finite, noncumulative hierarchy.
Lambda, beta and eta retain explicit domain/codomain formation premises.

The presentation does not import the independent specification. Its comparison
with that specification, structural admissibility, and algorithmic realization
are separate obligations. Neither conversion nor substitution is an untyped
rewrite rule in this static presentation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.Statics

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists

/-- Local nonrecursive parameters of the eighteen static rule constructors. -/
inductive RuleShape : Judgment → Type where
  | empty : RuleShape (context (.nil : RawContext 0))
  | extend {n : Nat} (Γ : RawContext n) (A : RawTy n) :
      RuleShape (context (Γ.snoc A))
  | formation {n : Nat} (Γ : RawContext n) (k : Nat) (a : RawTm n) :
      RuleShape (formed Γ (TypeParameter.mk k a).code)
  | sort {n : Nat} (Γ : RawContext n) (k : Nat) :
      RuleShape (typed Γ (universeTerm k) (universeType n (k + 1)).code)
  | variable {n : Nat} (Γ : RawContext n) (v : Var (scope n) .term) :
      RuleShape (typed Γ (.var v) (ContextGeometry.lookup Γ v))
  | pi {n : Nat} (Γ : RawContext n) (A : TypeParameter n) (B : TypeBody n) :
      RuleShape (typed Γ (B.pi A) (universeType n (max A.level B.level)).code)
  | lambda {n : Nat} (Γ : RawContext n) (A : TypeParameter n)
      (B : TypeBody n) (body : TermBody n) :
      RuleShape (typed Γ body.lambda (piType A B).code)
  | application {n : Nat} (Γ : RawContext n) (A : TypeParameter n)
      (B : TypeBody n) (f a : RawTm n) :
      RuleShape (typed Γ (app f a) (B.instantiate a).code)
  | conversion {n : Nat} (Γ : RawContext n) (t : RawTm n) (A B : RawTy n) :
      RuleShape (typed Γ t B)
  | typeEquality {n : Nat} (Γ : RawContext n) (k : Nat) (a b : RawTm n) :
      RuleShape (typeEqual Γ (TypeParameter.mk k a).code (TypeParameter.mk k b).code)
  | reflexivity {n : Nat} (Γ : RawContext n) (t : RawTm n) (A : RawTy n) :
      RuleShape (termEqual Γ t t A)
  | symmetry {n : Nat} (Γ : RawContext n) (t u : RawTm n) (A : RawTy n) :
      RuleShape (termEqual Γ u t A)
  | transitivity {n : Nat} (Γ : RawContext n) (t u v : RawTm n) (A : RawTy n) :
      RuleShape (termEqual Γ t v A)
  | equalityConversion {n : Nat} (Γ : RawContext n) (t u : RawTm n) (A B : RawTy n) :
      RuleShape (termEqual Γ t u B)
  | piCongruence {n : Nat} (Γ : RawContext n) (A A' : TypeParameter n)
      (B B' : TypeBody n) :
      RuleShape (termEqual Γ (B.pi A) (B'.pi A')
        (universeType n (max A.level B.level)).code)
  | applicationCongruence {n : Nat} (Γ : RawContext n) (A : TypeParameter n)
      (B : TypeBody n) (f g a b : RawTm n) :
      RuleShape (termEqual Γ (app f a) (app g b) (B.instantiate a).code)
  | beta {n : Nat} (Γ : RawContext n) (A : TypeParameter n)
      (B : TypeBody n) (body : TermBody n) (a : RawTm n) :
      RuleShape (termEqual Γ (app body.lambda a) (body.instantiate a) (B.instantiate a).code)
  | eta {n : Nat} (Γ : RawContext n) (A : TypeParameter n)
      (B : TypeBody n) (f g : RawTm n) :
      RuleShape (termEqual Γ f g (piType A B).code)

/-- Recursive children are in source order, with their complete contexts and boundaries. -/
def premises : {j : Judgment} → RuleShape j → List Judgment
  | _, .empty => []
  | _, .extend Γ A => [context Γ, formed Γ A]
  | _, .formation Γ k a => [typed Γ a (universeType _ k).code]
  | _, .sort Γ _ => [context Γ]
  | _, .variable Γ _ => [context Γ]
  | _, .pi Γ A B => [formed Γ A.code, formed (Γ.snoc A.code) B.open.code]
  | _, .lambda Γ A B body => [formed Γ A.code, formed (Γ.snoc A.code) B.open.code,
      typed (Γ.snoc A.code) body.open B.open.code]
  | _, .application Γ A B f a => [typed Γ f (piType A B).code, typed Γ a A.code]
  | _, .conversion Γ t A B => [typed Γ t A, typeEqual Γ A B]
  | _, .typeEquality Γ k a b => [termEqual Γ a b (universeType _ k).code]
  | _, .reflexivity Γ t A => [typed Γ t A]
  | _, .symmetry Γ t u A => [termEqual Γ t u A]
  | _, .transitivity Γ t u v A => [termEqual Γ t u A, termEqual Γ u v A]
  | _, .equalityConversion Γ t u A B => [termEqual Γ t u A, typeEqual Γ A B]
  | _, .piCongruence Γ A A' B B' => [formed Γ A.code, typeEqual Γ A.code A'.code,
      typeEqual (Γ.snoc A.code) B.open.code B'.open.code]
  | _, .applicationCongruence Γ A B f g a b =>
      [termEqual Γ f g (piType A B).code, termEqual Γ a b A.code]
  | _, .beta Γ A B body a => [formed Γ A.code, formed (Γ.snoc A.code) B.open.code,
      typed (Γ.snoc A.code) body.open B.open.code, typed Γ a A.code]
  | _, @RuleShape.eta n Γ A B f g => [formed Γ A.code, formed (Γ.snoc A.code) B.open.code,
      typed Γ f (piType A B).code, typed Γ g (piType A B).code,
      termEqual (Γ.snoc A.code)
        (app (bind (Telescope.projection (S := sig) .term n) f) (.var .zero))
        (app (bind (Telescope.projection (S := sig) .term n) g) (.var .zero)) B.open.code]

/-- The generic finite-rule compiler generates the proof family from this data. -/
def presentation : FinitePresentation Unit (fun _ => Judgment) where
  Shape _ j := RuleShape j
  premises _ _ shape := premises shape

abbrev Derivation (j : Judgment) := presentation.Derivation () j

/-- Every derivation satisfies every predicate closed under these actual rules. -/
theorem least (P : Judgment → Prop)
    (closed : presentation.RuleClosed (fun _ j => P j))
    (j : Judgment) (d : Derivation j) : P j :=
  presentation.derivation_least (fun _ j => P j) closed () j d

end Mettapedia.Languages.Agda.Structural.Statics
