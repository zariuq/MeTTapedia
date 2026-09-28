import Mettapedia.Languages.Agda.StaticMetatheory.Regularity

/-!
Weak-head syntax and typed contractions for the frozen finite-Set/Pi source.
The raw relation contracts beta and evaluates application heads. The typed
relation follows the explicit beta/app-subst/conv clauses in the pinned
logrel-mltt Definition.Typed. It maps to raw steps and source equalities.
There is no converse map from a raw step plus arbitrary source typing.
No total evaluator, normalization, Pi injectivity, or preservation of all raw
steps is assumed or asserted.
-/

namespace Mettapedia.Languages.Agda.SourceMetatheory.WeakHead
open Mettapedia.Languages.Agda.StaticSpecification
open Mettapedia.Languages.Agda.StaticMetatheory

inductive Step {n : Nat} : Term n → Term n → Type
  | beta (body : Abs n) (argument : Term n) :
      Step ((Term.lam body).app argument) (body.instantiate argument)
  | head {f g a : Term n} : Step f g → Step (f.app a) (g.app a)

inductive Neutral {n : Nat} : Term n → Type
  | var (i : Fin n) : Neutral (.var i)
  | app {f a : Term n} : Neutral f → Neutral (f.app a)

inductive Whnf {n : Nat} : Term n → Type
  | neutral {t : Term n} : Neutral t → Whnf t
  | lam (body : Abs n) : Whnf (.lam body)
  | pi (A : Ty n) (B : TyAbs n) : Whnf (.pi A B)
  | sort (k : Nat) : Whnf (.sort k)

theorem Neutral.not_lambda {t : Term n} (d : Neutral t) (body : Abs n) :
    t ≠ .lam body := by
  cases d <;> intro h <;> cases h

theorem Neutral.no_step {t u : Term n} (neutral : Neutral t) (step : Step t u) : False := by
  induction neutral generalizing u with
  | var => cases step
  | app head ih =>
      cases step with
      | beta => exact head.not_lambda _ rfl
      | head next => exact ih next

theorem Whnf.no_step {t u : Term n} (normal : Whnf t) (step : Step t u) : False := by
  cases normal with
  | neutral head => exact head.no_step step
  | lam => cases step
  | pi => cases step
  | sort => cases step

theorem Step.deterministic {t u v : Term n} (first : Step t u) (second : Step t v) : u = v := by
  induction first generalizing v with
  | beta body argument =>
      cases second with
      | beta => rfl
      | head step => cases step
  | @head f g a first ih =>
      cases second with
      | beta => cases first
      | head second => exact congrArg (fun term : Term n => term.app a) (ih second)

inductive Red {n : Nat} : Term n → Term n → Type
  | refl (t : Term n) : Red t t
  | step {t u v : Term n} : Step t u → Red u v → Red t v

def Red.trans {t u v : Term n} (first : Red t u) (second : Red u v) : Red t v :=
  match first with
  | .refl _ => second
  | .step next rest => .step next (rest.trans second)

theorem Red.from_normal {t u : Term n} (normal : Whnf t) (path : Red t u) : t = u := by
  cases path with
  | refl => rfl
  | step step => exact False.elim (normal.no_step step)

theorem Red.normal_unique {t u v : Term n} (first : Red t u) (second : Red t v)
    (leftNormal : Whnf u) (rightNormal : Whnf v) : u = v := by
  induction first generalizing v with
  | refl => exact second.from_normal leftNormal
  | step first rest ih =>
      cases second with
      | refl => exact False.elim (rightNormal.no_step first)
      | step second more =>
          have same := first.deterministic second
          cases same
          exact ih more leftNormal rightNormal

theorem Red.pi_fixed {A : Ty n} {B : TyAbs n} {t : Term n}
    (path : Red (.pi A B) t) : t = .pi A B := (path.from_normal (.pi A B)).symm

theorem Red.sort_fixed {k : Nat} {t : Term n}
    (path : Red (.sort k) t) : t = .sort k := (path.from_normal (.sort k)).symm

/-- A common weak-head reduct of two written Pis identifies their raw parts.
General source type equality does not yet supply such a common reduct. -/
theorem Red.common_pi_parts {A A' : Ty n} {B B' : TyAbs n} {t : Term n}
    (left : Red (.pi A B) t) (right : Red (.pi A' B') t) : A = A' ∧ B = B' :=
  Term.pi.inj (left.pi_fixed.symm.trans right.pi_fixed)

inductive TypedStep {n : Nat} (Γ : RawContext n) : Term n → Term n → Ty n → Type
  | beta {A : Ty n} {B : TyAbs n} {body : Abs n} {a : Term n} :
      FormTy Γ A → FormTy (Γ.snoc A) B.open → Typing (Γ.snoc A) body.open B.open →
      Typing Γ a A → TypedStep Γ ((Term.lam body).app a) (body.instantiate a) (B.instantiate a)
  | head {A : Ty n} {B : TyAbs n} {f g a : Term n} :
      TypedStep Γ f g (Ty.pi A B) → Typing Γ a A →
      TypedStep Γ (f.app a) (g.app a) (B.instantiate a)
  | conv {A B : Ty n} {t u : Term n} :
      TypedStep Γ t u A → TypeEq Γ A B → TypedStep Γ t u B

def TypedStep.raw {Γ : RawContext n} {t u : Term n} {A : Ty n}
    (d : TypedStep Γ t u A) : Step t u :=
  match d with
  | .beta _ _ _ _ => .beta _ _
  | .head step _ => .head step.raw
  | .conv step _ => step.raw

def TypedStep.equal {Γ : RawContext n} {t u : Term n} {A : Ty n}
    (d : TypedStep Γ t u A) : TermEq Γ t u A :=
  match d with
  | .beta domain codomain body argument => .beta domain codomain body argument
  | .head step argument => .appCong step.equal (.refl argument)
  | .conv step eq => .conv step.equal eq

def TypedStep.endpoints {Γ : RawContext n} {t u : Term n} {A : Ty n}
    (d : TypedStep Γ t u A) : TermEndpoints Γ t u A := termEndpoints d.equal

inductive TypedRed {n : Nat} (Γ : RawContext n) : Term n → Term n → Ty n → Type
  | refl {t : Term n} {A : Ty n} : Typing Γ t A → TypedRed Γ t t A
  | step {t u v : Term n} {A : Ty n} :
      TypedStep Γ t u A → TypedRed Γ u v A → TypedRed Γ t v A

def TypedRed.raw {Γ : RawContext n} {t u : Term n} {A : Ty n}
    (d : TypedRed Γ t u A) : Red t u :=
  match d with
  | .refl _ => .refl _
  | .step first rest => .step first.raw rest.raw

def TypedRed.equal {Γ : RawContext n} {t u : Term n} {A : Ty n}
    (d : TypedRed Γ t u A) : TermEq Γ t u A :=
  match d with
  | .refl typed => .refl typed
  | .step first rest => .trans first.equal rest.equal

def TypedRed.endpoints {Γ : RawContext n} {t u : Term n} {A : Ty n}
    (d : TypedRed Γ t u A) : TermEndpoints Γ t u A := termEndpoints d.equal

end Mettapedia.Languages.Agda.SourceMetatheory.WeakHead
