import Mettapedia.Languages.Agda.Structural.StaticRules
import Mettapedia.OSLF.Syntax.FiniteRulePremiseEvidence

/-!
# Constructing complete static rule trees

Each function selects its authored rule constructor and supplies every ordered
child. The proof family remains the generic indexed-polynomial fixed point;
there is no second inductive typing relation or separate checking algorithm.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.Statics

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists

private abbrev emptyChildren := noEvidence Derivation
private abbrev child := @consEvidence _ Derivation

namespace Derivation

def empty : Derivation (context (.nil : RawContext 0)) :=
  .roll .empty emptyChildren

def extend {n : Nat} {Γ : RawContext n} {A : RawTy n}
    (prior : Derivation (context Γ)) (type : Derivation (formed Γ A)) :
    Derivation (context (Γ.snoc A)) :=
  .roll (.extend Γ A) (child prior (child type emptyChildren))

def formation {n : Nat} {Γ : RawContext n} {k : Nat} {a : RawTm n}
    (typed : Derivation (typed Γ a (universeType n k).code)) :
    Derivation (formed Γ (TypeParameter.mk k a).code) :=
  .roll (.formation Γ k a) (child typed emptyChildren)

def sort {n : Nat} {Γ : RawContext n} (k : Nat) (formed : Derivation (context Γ)) :
    Derivation (typed Γ (universeTerm k) (universeType n (k + 1)).code) :=
  .roll (.sort Γ k) (child formed emptyChildren)

def variableTerm {n : Nat} {Γ : RawContext n} (v : Var (scope n) .term)
    (formed : Derivation (context Γ)) :
    Derivation (typed Γ (.var v) (ContextGeometry.lookup Γ v)) :=
  .roll (.variable Γ v) (child formed emptyChildren)

def pi {n : Nat} {Γ : RawContext n} {A : TypeParameter n} {B : TypeBody n}
    (domain : Derivation (formed Γ A.code))
    (codomain : Derivation (formed (Γ.snoc A.code) B.open.code)) :
    Derivation (typed Γ (B.pi A) (universeType n (max A.level B.level)).code) :=
  .roll (.pi Γ A B) (child domain (child codomain emptyChildren))

def lambda {n : Nat} {Γ : RawContext n} {A : TypeParameter n} {B : TypeBody n} {body : TermBody n}
    (domain : Derivation (formed Γ A.code))
    (codomain : Derivation (formed (Γ.snoc A.code) B.open.code))
    (typedBody : Derivation (typed (Γ.snoc A.code) body.open B.open.code)) :
    Derivation (typed Γ body.lambda (piType A B).code) :=
  .roll (.lambda Γ A B body) (child domain (child codomain (child typedBody emptyChildren)))

def application {n : Nat} {Γ : RawContext n} {A : TypeParameter n} {B : TypeBody n} {f a : RawTm n}
    (function : Derivation (typed Γ f (piType A B).code))
    (argument : Derivation (typed Γ a A.code)) :
    Derivation (typed Γ (app f a) (B.instantiate a).code) :=
  .roll (.application Γ A B f a) (child function (child argument emptyChildren))

def conversion {n : Nat} {Γ : RawContext n} {t : RawTm n} {A B : RawTy n}
    (term : Derivation (typed Γ t A)) (types : Derivation (typeEqual Γ A B)) :
    Derivation (typed Γ t B) :=
  .roll (.conversion Γ t A B) (child term (child types emptyChildren))

def typeEquality {n : Nat} {Γ : RawContext n} {k : Nat} {a b : RawTm n}
    (terms : Derivation (termEqual Γ a b (universeType n k).code)) :
    Derivation (typeEqual Γ (TypeParameter.mk k a).code (TypeParameter.mk k b).code) :=
  .roll (.typeEquality Γ k a b) (child terms emptyChildren)

def reflexivity {n : Nat} {Γ : RawContext n} {t : RawTm n} {A : RawTy n}
    (term : Derivation (typed Γ t A)) : Derivation (termEqual Γ t t A) :=
  .roll (.reflexivity Γ t A) (child term emptyChildren)

def symmetry {n : Nat} {Γ : RawContext n} {t u : RawTm n} {A : RawTy n}
    (equal : Derivation (termEqual Γ t u A)) : Derivation (termEqual Γ u t A) :=
  .roll (.symmetry Γ t u A) (child equal emptyChildren)

def transitivity {n : Nat} {Γ : RawContext n} {t u v : RawTm n} {A : RawTy n}
    (first : Derivation (termEqual Γ t u A)) (second : Derivation (termEqual Γ u v A)) :
    Derivation (termEqual Γ t v A) :=
  .roll (.transitivity Γ t u v A) (child first (child second emptyChildren))

def equalityConversion {n : Nat} {Γ : RawContext n} {t u : RawTm n} {A B : RawTy n}
    (terms : Derivation (termEqual Γ t u A)) (types : Derivation (typeEqual Γ A B)) :
    Derivation (termEqual Γ t u B) :=
  .roll (.equalityConversion Γ t u A B) (child terms (child types emptyChildren))

def piCongruence {n : Nat} {Γ : RawContext n} {A A' : TypeParameter n} {B B' : TypeBody n}
    (domain : Derivation (formed Γ A.code)) (domains : Derivation (typeEqual Γ A.code A'.code))
    (codomains : Derivation (typeEqual (Γ.snoc A.code) B.open.code B'.open.code)) :
    Derivation (termEqual Γ (B.pi A) (B'.pi A') (universeType n (max A.level B.level)).code) :=
  .roll (.piCongruence Γ A A' B B') (child domain (child domains (child codomains emptyChildren)))

def applicationCongruence {n : Nat} {Γ : RawContext n} {A : TypeParameter n}
    {B : TypeBody n} {f g a b : RawTm n}
    (functions : Derivation (termEqual Γ f g (piType A B).code))
    (arguments : Derivation (termEqual Γ a b A.code)) :
    Derivation (termEqual Γ (app f a) (app g b) (B.instantiate a).code) :=
  .roll (.applicationCongruence Γ A B f g a b) (child functions (child arguments emptyChildren))

def beta {n : Nat} {Γ : RawContext n} {A : TypeParameter n}
    {B : TypeBody n} {body : TermBody n} {a : RawTm n}
    (domain : Derivation (formed Γ A.code)) (codomain : Derivation (formed (Γ.snoc A.code) B.open.code))
    (typedBody : Derivation (typed (Γ.snoc A.code) body.open B.open.code))
    (argument : Derivation (typed Γ a A.code)) :
    Derivation (termEqual Γ (app body.lambda a) (body.instantiate a) (B.instantiate a).code) :=
  .roll (.beta Γ A B body a) (child domain (child codomain (child typedBody (child argument emptyChildren))))

def eta {n : Nat} {Γ : RawContext n} {A : TypeParameter n} {B : TypeBody n} {f g : RawTm n}
    (domain : Derivation (formed Γ A.code)) (codomain : Derivation (formed (Γ.snoc A.code) B.open.code))
    (first : Derivation (typed Γ f (piType A B).code))
    (second : Derivation (typed Γ g (piType A B).code))
    (bodies : Derivation (termEqual (Γ.snoc A.code)
      (app (bind (Telescope.projection (S := sig) .term n) f) (.var .zero))
      (app (bind (Telescope.projection (S := sig) .term n) g) (.var .zero)) B.open.code)) :
    Derivation (termEqual Γ f g (piType A B).code) :=
  .roll (.eta Γ A B f g) (child domain (child codomain (child first (child second (child bodies emptyChildren)))))

end Derivation

end Mettapedia.Languages.Agda.Structural.Statics
