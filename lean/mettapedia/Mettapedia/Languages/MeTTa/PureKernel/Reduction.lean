import Mathlib.Logic.Relation
import Mettapedia.Languages.MeTTa.PureKernel.Substitution

namespace Mettapedia.Languages.MeTTa.PureKernel.Reduction

open Mettapedia.Languages.MeTTa.PureKernel.Syntax
open Mettapedia.Languages.MeTTa.PureKernel.Substitution

/-- One-step β-reduction with congruence for the Pure kernel syntax. -/
inductive Red : PureTm n → PureTm n → Prop where
  | betaPi (body : PureTm (n + 1)) (a : PureTm n) :
      Red (.app (.lam body) a) (inst0 a body)
  | betaSigmaFst (a b : PureTm n) :
      Red (.fst (.pair a b)) a
  | betaSigmaSnd (a b : PureTm n) :
      Red (.snd (.pair a b)) b
  | congPiDom {A A' : PureTm n} {B : PureTm (n + 1)} :
      Red A A' → Red (.pi A B) (.pi A' B)
  | congPiCod {A : PureTm n} {B B' : PureTm (n + 1)} :
      Red B B' → Red (.pi A B) (.pi A B')
  | congSigmaDom {A A' : PureTm n} {B : PureTm (n + 1)} :
      Red A A' → Red (.sigma A B) (.sigma A' B)
  | congSigmaCod {A : PureTm n} {B B' : PureTm (n + 1)} :
      Red B B' → Red (.sigma A B) (.sigma A B')
  | congIdTy {A A' a b : PureTm n} :
      Red A A' → Red (.id A a b) (.id A' a b)
  | congIdLeft {A a a' b : PureTm n} :
      Red a a' → Red (.id A a b) (.id A a' b)
  | congIdRight {A a b b' : PureTm n} :
      Red b b' → Red (.id A a b) (.id A a b')
  | congLam {b b' : PureTm (n + 1)} :
      Red b b' → Red (.lam b) (.lam b')
  | congAppFun {f f' a : PureTm n} :
      Red f f' → Red (.app f a) (.app f' a)
  | congAppArg {f a a' : PureTm n} :
      Red a a' → Red (.app f a) (.app f a')
  | congPairFst {a a' b : PureTm n} :
      Red a a' → Red (.pair a b) (.pair a' b)
  | congPairSnd {a b b' : PureTm n} :
      Red b b' → Red (.pair a b) (.pair a b')
  | congFst {p p' : PureTm n} :
      Red p p' → Red (.fst p) (.fst p')
  | congSnd {p p' : PureTm n} :
      Red p p' → Red (.snd p) (.snd p')
  | congRefl {a a' : PureTm n} :
      Red a a' → Red (.refl a) (.refl a')

abbrev RedStar (t u : PureTm n) : Prop := Relation.ReflTransGen Red t u

namespace RedStar

theorem refl (t : PureTm n) : RedStar t t :=
  Relation.ReflTransGen.refl

theorem tail {t u v : PureTm n} (h₁ : RedStar t u) (h₂ : Red u v) : RedStar t v :=
  Relation.ReflTransGen.tail h₁ h₂

theorem trans {t u v : PureTm n} (h₁ : RedStar t u) (h₂ : RedStar u v) : RedStar t v :=
  Relation.ReflTransGen.trans h₁ h₂

theorem map {F : PureTm n → PureTm n}
    (hF : ∀ {x y}, Red x y → Red (F x) (F y))
    {t u : PureTm n} (h : RedStar t u) : RedStar (F t) (F u) := by
  induction h with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hxy hyz ih =>
      exact Relation.ReflTransGen.tail ih (hF hyz)

theorem congPiDom {A A' : PureTm n} {B : PureTm (n + 1)}
    (h : RedStar A A') : RedStar (.pi A B) (.pi A' B) :=
  map (F := fun t => .pi t B) (fun hstep => .congPiDom hstep) h

theorem congPiCod {A : PureTm n} {B B' : PureTm (n + 1)}
    (h : RedStar B B') : RedStar (.pi A B) (.pi A B') := by
  induction h with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hxy hyz ih =>
      exact .tail ih (.congPiCod hyz)

theorem congSigmaDom {A A' : PureTm n} {B : PureTm (n + 1)}
    (h : RedStar A A') : RedStar (.sigma A B) (.sigma A' B) :=
  map (F := fun t => .sigma t B) (fun hstep => .congSigmaDom hstep) h

theorem congSigmaCod {A : PureTm n} {B B' : PureTm (n + 1)}
    (h : RedStar B B') : RedStar (.sigma A B) (.sigma A B') := by
  induction h with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hxy hyz ih =>
      exact .tail ih (.congSigmaCod hyz)

theorem congLam {b b' : PureTm (n + 1)} (h : RedStar b b') : RedStar (.lam b) (.lam b') := by
  induction h with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hxy hyz ih =>
      exact .tail ih (.congLam hyz)

theorem congAppFun {f f' a : PureTm n} (h : RedStar f f') : RedStar (.app f a) (.app f' a) :=
  map (F := fun t => .app t a) (fun hstep => .congAppFun hstep) h

theorem congAppArg {f a a' : PureTm n} (h : RedStar a a') : RedStar (.app f a) (.app f a') :=
  map (F := fun t => .app f t) (fun hstep => .congAppArg hstep) h

theorem congPairFst {a a' b : PureTm n} (h : RedStar a a') :
    RedStar (.pair a b) (.pair a' b) :=
  map (F := fun t => .pair t b) (fun hstep => .congPairFst hstep) h

theorem congPairSnd {a b b' : PureTm n} (h : RedStar b b') :
    RedStar (.pair a b) (.pair a b') :=
  map (F := fun t => .pair a t) (fun hstep => .congPairSnd hstep) h

theorem congFst {p p' : PureTm n} (h : RedStar p p') : RedStar (.fst p) (.fst p') :=
  map (F := fun t => .fst t) (fun hstep => .congFst hstep) h

theorem congSnd {p p' : PureTm n} (h : RedStar p p') : RedStar (.snd p) (.snd p') :=
  map (F := fun t => .snd t) (fun hstep => .congSnd hstep) h

theorem congRefl {a a' : PureTm n} (h : RedStar a a') : RedStar (.refl a) (.refl a') :=
  map (F := fun t => .refl t) (fun hstep => .congRefl hstep) h

end RedStar

theorem red_to_redStar {t u : PureTm n} (h : Red t u) : RedStar t u :=
  Relation.ReflTransGen.tail Relation.ReflTransGen.refl h

end Mettapedia.Languages.MeTTa.PureKernel.Reduction
