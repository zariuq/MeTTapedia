import Mettapedia.Languages.Agda.Structural.SpineRenaming

/-!
# Recursive static rules for administrative equality

The existing twenty-four rule families enter through their actual rule data.
Every premise, including a prior core premise, recursively uses the enlarged
presentation. Nine conditional spine-equality families and three typed term
families retain all ordered premise positions and intermediate type codes.

Spine equality acts on an actual typed equality of heads. In particular its
cons rule requires argument equality and equality of the tails at the left
instantiated codomain; it does not assert unconditional action endpoints.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.AdministrativeStatics

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists
open Mettapedia.OSLF.Binding.IndexedRulePolynomialMorphisms
open Mettapedia.TypeTheory
open Statics (RawTm RawTy RawContext TypeParameter TypeBody)

inductive Judgment where
  | core (judgment : Statics.Judgment)
  | spineAction {n : Nat} (context : RawContext n) (input : RawTy n)
      (spine : Spine (scope n)) (output : RawTy n)
  | spineEquality {n : Nat} (context : RawContext n) (input : RawTy n)
      (first second : Spine (scope n)) (output : RawTy n)

def mapPrior : SpineStatics.CombinedJudgment → Judgment
  | .core j => .core j
  | .spineAction Γ A es B => .spineAction Γ A es B

inductive RuleShape : Judgment → Type where
  | prior {j : SpineStatics.CombinedJudgment} (shape : SpineStatics.RuleShape j) : RuleShape (mapPrior j)
  | spineRefl {n : Nat} (Γ : RawContext n) (A : RawTy n) (es : Spine (scope n)) (B : RawTy n) :
      RuleShape (.spineEquality Γ A es es B)
  | spineSymm {n : Nat} (Γ : RawContext n) (A : RawTy n) (es fs : Spine (scope n)) (B : RawTy n) :
      RuleShape (.spineEquality Γ A fs es B)
  | spineTrans {n : Nat} (Γ : RawContext n) (A : RawTy n) (es fs gs : Spine (scope n)) (B : RawTy n) :
      RuleShape (.spineEquality Γ A es gs B)
  | spineCons {n : Nat} (Γ : RawContext n) (A : TypeParameter n) (B : TypeBody n)
      (u v : RawTm n) (es fs : Spine (scope n)) (C : RawTy n) :
      RuleShape (.spineEquality Γ (Statics.piType A B).code
        (cons (apply u) es) (cons (apply v) fs) C)
  | spineAppend {n : Nat} (Γ : RawContext n) (A : RawTy n) (es fs : Spine (scope n))
      (B : RawTy n) (gs hs : Spine (scope n)) (C : RawTy n) :
      RuleShape (.spineEquality Γ A (append es gs) (append fs hs) C)
  | spineInputConversion {n : Nat} (Γ : RawContext n) (A' A : RawTy n)
      (es fs : Spine (scope n)) (B : RawTy n) : RuleShape (.spineEquality Γ A' es fs B)
  | spineOutputConversion {n : Nat} (Γ : RawContext n) (A : RawTy n)
      (es fs : Spine (scope n)) (B B' : RawTy n) : RuleShape (.spineEquality Γ A es fs B')
  | appendEmpty {n : Nat} (Γ : RawContext n) (A : RawTy n) (es : Spine (scope n)) (B : RawTy n) :
      RuleShape (.spineEquality Γ A (append nil es) es B)
  | appendCons {n : Nat} (Γ : RawContext n) (A : RawTy n) (u : RawTm n)
      (es fs : Spine (scope n)) (B : RawTy n) :
      RuleShape (.spineEquality Γ A (append (cons (apply u) es) fs) (cons (apply u) (append es fs)) B)
  | eliminationCongruence {n : Nat} (Γ : RawContext n) (f g : RawTm n) (A : RawTy n)
      (es fs : Spine (scope n)) (B : RawTy n) :
      RuleShape (.core (Statics.termEqual Γ (eliminate f es) (eliminate g fs) B))
  | emptyElimination {n : Nat} (Γ : RawContext n) (f : RawTm n) (A : RawTy n) :
      RuleShape (.core (Statics.termEqual Γ (eliminate f nil) f A))
  | nestedElimination {n : Nat} (Γ : RawContext n) (f : RawTm n) (A : RawTy n)
      (es : Spine (scope n)) (B : RawTy n) (fs : Spine (scope n)) (C : RawTy n) :
      RuleShape (.core (Statics.termEqual Γ (eliminate (eliminate f es) fs) (eliminate f (append es fs)) C))

def premises : {j : Judgment} → RuleShape j → List Judgment
  | _, .prior shape => (SpineStatics.premises shape).map mapPrior
  | _, .spineRefl Γ A es B => [.spineAction Γ A es B]
  | _, .spineSymm Γ A es fs B => [.spineEquality Γ A es fs B]
  | _, .spineTrans Γ A es fs gs B => [.spineEquality Γ A es fs B, .spineEquality Γ A fs gs B]
  | _, .spineCons Γ A B u v es fs C =>
      [.core (Statics.termEqual Γ u v A.code), .spineEquality Γ (B.instantiate u).code es fs C]
  | _, .spineAppend Γ A es fs B gs hs C => [.spineEquality Γ A es fs B, .spineEquality Γ B gs hs C]
  | _, .spineInputConversion Γ A' A es fs B => [.core (Statics.typeEqual Γ A' A), .spineEquality Γ A es fs B]
  | _, .spineOutputConversion Γ A es fs B B' => [.spineEquality Γ A es fs B, .core (Statics.typeEqual Γ B B')]
  | _, .appendEmpty Γ A es B => [.spineAction Γ A (append nil es) B]
  | _, .appendCons Γ A u es fs B => [.spineAction Γ A (append (cons (apply u) es) fs) B]
  | _, .eliminationCongruence Γ f g A es fs B =>
      [.core (Statics.termEqual Γ f g A), .spineEquality Γ A es fs B]
  | _, .emptyElimination Γ f A => [.core (Statics.typed Γ f A)]
  | _, .nestedElimination Γ f A es B fs C =>
      [.core (Statics.typed Γ f A), .spineAction Γ A es B, .spineAction Γ B fs C]

def presentation : FinitePresentation Unit (fun _ => Judgment) where
  Shape _ j := RuleShape j
  premises _ _ shape := premises shape

abbrev Derivation (j : Judgment) := presentation.Derivation () j
abbrev CoreDerivation (j : Statics.Judgment) := Derivation (.core j)
abbrev Action {n : Nat} (Γ : RawContext n) (A : RawTy n) (es : Spine (scope n)) (B : RawTy n) :=
  Derivation (.spineAction Γ A es B)
abbrev SpineEq {n : Nat} (Γ : RawContext n) (A : RawTy n) (es fs : Spine (scope n)) (B : RawTy n) :=
  Derivation (.spineEquality Γ A es fs B)

def priorHom : Hom SpineStatics.presentation.polynomial presentation.polynomial (fun _ j => mapPrior j) where
  onShape _ _ shape := .prior shape
  onPosition _ _ shape := finCongr (List.length_map (f := mapPrior) (as := SpineStatics.premises shape))
  onNext := by
    intro _ j shape position
    exact List.getElem_map mapPrior (l := SpineStatics.premises shape) (i := position.val) (h := position.isLt)

def canonicalHom := SpineStatics.canonicalHom.comp priorHom

noncomputable def includePrior {j : SpineStatics.CombinedJudgment} (tree : SpineStatics.Derivation j) :
    Derivation (mapPrior j) := priorHom.mapFix () j tree

noncomputable def includeCanonical {j : Statics.Judgment} (tree : Statics.Derivation j) : CoreDerivation j :=
  canonicalHom.mapFix () j tree

/-- The prior premise list is read at exactly its original addresses. -/
def priorPremiseEvidence {D : Judgment → Type} : {js : List SpineStatics.CombinedJudgment} →
    Evidence D (js.map mapPrior) → Evidence (fun j => D (mapPrior j)) js
  | [], _ => noEvidence _
  | _ :: _, children => consEvidence _ (children ⟨0, Nat.zero_lt_succ _⟩)
      (priorPremiseEvidence (fun position => children position.succ))

def liftPriorEvidence {D : Judgment → Type} : {js : List SpineStatics.CombinedJudgment} →
    Evidence (fun j => D (mapPrior j)) js → Evidence D (js.map mapPrior)
  | [], _ => noEvidence _
  | _ :: _, children => consEvidence _ (children 0) (liftPriorEvidence (fun position => children position.succ))

noncomputable def priorAlgebra {D : Judgment → Type}
    (algebra : IndexedPolynomial.Algebra presentation.polynomial (fun _ j => D j)) :
    IndexedPolynomial.Algebra SpineStatics.presentation.polynomial (fun _ j => D (mapPrior j)) :=
  IndexedRuleAlgebraPullback.pullback priorHom algebra

noncomputable def canonicalAlgebra {D : Judgment → Type}
    (algebra : IndexedPolynomial.Algebra presentation.polynomial (fun _ j => D j)) :
    IndexedPolynomial.Algebra Statics.presentation.polynomial (fun _ j => D (.core j)) :=
  SpineStatics.canonicalAlgebra (priorAlgebra algebra)

noncomputable def algebra : IndexedPolynomial.Algebra presentation.polynomial (fun _ j => Derivation j) :=
  IndexedPolynomial.Algebra.initial presentation.polynomial

noncomputable def coreAlgebra : IndexedPolynomial.Algebra Statics.presentation.polynomial (fun _ j => CoreDerivation j) :=
  canonicalAlgebra algebra

namespace Derivation

abbrev fire {j : Judgment} (shape : RuleShape j) (children : Evidence Derivation (premises shape)) : Derivation j :=
  .roll shape children

def prior {j : SpineStatics.CombinedJudgment} (shape : SpineStatics.RuleShape j)
    (children : Evidence (fun j => Derivation (mapPrior j)) (SpineStatics.premises shape)) : Derivation (mapPrior j) :=
  fire (.prior shape) (liftPriorEvidence children)

noncomputable def core {j : Statics.Judgment} (shape : Statics.RuleShape j)
    (children : Evidence CoreDerivation (Statics.premises shape)) : CoreDerivation j :=
  coreAlgebra.act () j ⟨shape, children⟩

private abbrev stop := noEvidence Derivation
private abbrev child := @consEvidence _ Derivation

def nil {n : Nat} (Γ : RawContext n) (A : RawTy n) : Action Γ A Structural.nil A :=
  fire (.prior (.nil Γ A)) stop

def cons {n : Nat} {Γ : RawContext n} {A : TypeParameter n} {B : TypeBody n}
    {u : RawTm n} {es : Spine (scope n)} {C : RawTy n}
    (argument : CoreDerivation (Statics.typed Γ u A.code)) (tail : Action Γ (B.instantiate u).code es C) :
    Action Γ (Statics.piType A B).code (Structural.cons (apply u) es) C :=
  fire (.prior (.cons Γ A B u es C)) (child argument (child tail stop))

def append {n : Nat} {Γ : RawContext n} {A B C : RawTy n} {es fs : Spine (scope n)}
    (first : Action Γ A es B) (second : Action Γ B fs C) : Action Γ A (Structural.append es fs) C :=
  fire (.prior (.append Γ A es B fs C)) (child first (child second stop))

def inputConversion {n : Nat} {Γ : RawContext n} {A' A B : RawTy n} {es : Spine (scope n)}
    (equal : CoreDerivation (Statics.typeEqual Γ A' A)) (action : Action Γ A es B) : Action Γ A' es B :=
  fire (.prior (.inputConversion Γ A' A es B)) (child equal (child action stop))

def outputConversion {n : Nat} {Γ : RawContext n} {A B B' : RawTy n} {es : Spine (scope n)}
    (action : Action Γ A es B) (equal : CoreDerivation (Statics.typeEqual Γ B B')) : Action Γ A es B' :=
  fire (.prior (.outputConversion Γ A es B B')) (child action (child equal stop))

def elimination {n : Nat} {Γ : RawContext n} {f : RawTm n} {A B : RawTy n} {es : Spine (scope n)}
    (head : CoreDerivation (Statics.typed Γ f A)) (action : Action Γ A es B) :
    CoreDerivation (Statics.typed Γ (eliminate f es) B) :=
  fire (.prior (.elimination Γ f A es B)) (child head (child action stop))

def spineRefl {n : Nat} {Γ : RawContext n} {A B : RawTy n} {es : Spine (scope n)}
    (action : Action Γ A es B) : SpineEq Γ A es es B := fire (.spineRefl Γ A es B) (child action stop)

def spineSymm {n : Nat} {Γ : RawContext n} {A B : RawTy n} {es fs : Spine (scope n)}
    (equal : SpineEq Γ A es fs B) : SpineEq Γ A fs es B := fire (.spineSymm Γ A es fs B) (child equal stop)

def spineTrans {n : Nat} {Γ : RawContext n} {A B : RawTy n} {es fs gs : Spine (scope n)}
    (first : SpineEq Γ A es fs B) (second : SpineEq Γ A fs gs B) : SpineEq Γ A es gs B :=
  fire (.spineTrans Γ A es fs gs B) (child first (child second stop))

def spineCons {n : Nat} {Γ : RawContext n} {A : TypeParameter n} {B : TypeBody n}
    {u v : RawTm n} {es fs : Spine (scope n)} {C : RawTy n}
    (arguments : CoreDerivation (Statics.termEqual Γ u v A.code)) (tails : SpineEq Γ (B.instantiate u).code es fs C) :
    SpineEq Γ (Statics.piType A B).code (Structural.cons (apply u) es) (Structural.cons (apply v) fs) C :=
  fire (.spineCons Γ A B u v es fs C) (child arguments (child tails stop))

def spineAppend {n : Nat} {Γ : RawContext n} {A B C : RawTy n} {es fs gs hs : Spine (scope n)}
    (first : SpineEq Γ A es fs B) (second : SpineEq Γ B gs hs C) :
    SpineEq Γ A (Structural.append es gs) (Structural.append fs hs) C :=
  fire (.spineAppend Γ A es fs B gs hs C) (child first (child second stop))

def spineInputConversion {n : Nat} {Γ : RawContext n} {A' A B : RawTy n} {es fs : Spine (scope n)}
    (equal : CoreDerivation (Statics.typeEqual Γ A' A)) (spines : SpineEq Γ A es fs B) : SpineEq Γ A' es fs B :=
  fire (.spineInputConversion Γ A' A es fs B) (child equal (child spines stop))

def spineOutputConversion {n : Nat} {Γ : RawContext n} {A B B' : RawTy n} {es fs : Spine (scope n)}
    (spines : SpineEq Γ A es fs B) (equal : CoreDerivation (Statics.typeEqual Γ B B')) : SpineEq Γ A es fs B' :=
  fire (.spineOutputConversion Γ A es fs B B') (child spines (child equal stop))

def appendEmpty {n : Nat} {Γ : RawContext n} {A B : RawTy n} {es : Spine (scope n)}
    (action : Action Γ A (Structural.append Structural.nil es) B) :
    SpineEq Γ A (Structural.append Structural.nil es) es B := fire (.appendEmpty Γ A es B) (child action stop)

def appendCons {n : Nat} {Γ : RawContext n} {A B : RawTy n} {u : RawTm n} {es fs : Spine (scope n)}
    (action : Action Γ A (Structural.append (Structural.cons (apply u) es) fs) B) :
    SpineEq Γ A (Structural.append (Structural.cons (apply u) es) fs) (Structural.cons (apply u) (Structural.append es fs)) B :=
  fire (.appendCons Γ A u es fs B) (child action stop)

def eliminationCongruence {n : Nat} {Γ : RawContext n} {f g : RawTm n} {A B : RawTy n} {es fs : Spine (scope n)}
    (heads : CoreDerivation (Statics.termEqual Γ f g A)) (spines : SpineEq Γ A es fs B) :
    CoreDerivation (Statics.termEqual Γ (eliminate f es) (eliminate g fs) B) :=
  fire (.eliminationCongruence Γ f g A es fs B) (child heads (child spines stop))

def emptyElimination {n : Nat} {Γ : RawContext n} {f : RawTm n} {A : RawTy n}
    (head : CoreDerivation (Statics.typed Γ f A)) : CoreDerivation (Statics.termEqual Γ (eliminate f Structural.nil) f A) :=
  fire (.emptyElimination Γ f A) (child head stop)

def nestedElimination {n : Nat} {Γ : RawContext n} {f : RawTm n} {A B C : RawTy n} {es fs : Spine (scope n)}
    (head : CoreDerivation (Statics.typed Γ f A)) (first : Action Γ A es B) (second : Action Γ B fs C) :
    CoreDerivation (Statics.termEqual Γ (eliminate (eliminate f es) fs) (eliminate f (Structural.append es fs)) C) :=
  fire (.nestedElimination Γ f A es B fs C) (child head (child first (child second stop)))

end Derivation

end Mettapedia.Languages.Agda.Structural.AdministrativeStatics
