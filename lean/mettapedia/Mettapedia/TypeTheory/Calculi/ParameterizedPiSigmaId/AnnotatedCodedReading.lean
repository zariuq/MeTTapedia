import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.Syntax
import Mettapedia.Logic.HOL.Syntax.Closed
import Mettapedia.Logic.HOL.Syntax.ConstMap

/-!
# A uniform coded reading of the annotated grammar

Every source value, including a type code or a function, has one object
carrier. Source application uses an explicit operation on codes; source
abstraction retains its domain and passes a HOL function to the code builder.
The operation signature carries syntax only. Its laws and a universe/theory
interpretation are additional obligations.
-/

set_option autoImplicit false
namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedCodedReading
open Mettapedia.Logic
open Presentation TypedEquality.Annotated
universe u v
variable {Head : Type} {Base : Type u} {Const : HOL.Ty Base → Type v}

structure Operations (Head : Type) (Const : HOL.Ty Base → Type v) (object : HOL.Ty Base) where
  head : Head → HOL.ClosedTerm Const object
  constant : DeclName → HOL.ClosedTerm Const object
  product : HOL.ClosedTerm Const (.arr object (.arr (.arr object object) object))
  sum : HOL.ClosedTerm Const (.arr object (.arr (.arr object object) object))
  abstraction : HOL.ClosedTerm Const (.arr object (.arr (.arr object object) object))
  application : HOL.ClosedTerm Const (.arr object (.arr object object))
  pair : HOL.ClosedTerm Const (.arr object (.arr object object))
  first : HOL.ClosedTerm Const (.arr object object)
  second : HOL.ClosedTerm Const (.arr object object)
  truth : HOL.ClosedTerm Const (.arr .prop object)
  empty : HOL.ClosedTerm Const object

variable {object : HOL.Ty Base} (ops : Operations Head Const object)

def lift {n : Nat} {Γ : HOL.Ctx Base} (bound : Fin n → HOL.Term Const Γ object) :
    Fin (n+1) → HOL.Term Const (object :: Γ) object :=
  Fin.cases (.var .vz) (fun i => HOL.weaken (bound i))

def readAt : {n : Nat} → {Γ : HOL.Ctx Base} →
    (Fin n → HOL.Term Const Γ object) → CTm Head n → HOL.Term Const Γ object
  | _, _, bound, .var i => bound i
  | _, Γ, _, .head h => HOL.weakenCtx Γ (ops.head h)
  | _, Γ, _, .const c => HOL.weakenCtx Γ (ops.constant c)
  | _, Γ, bound, .pi A B => .app (.app (HOL.weakenCtx Γ ops.product) (readAt bound A))
      (.lam (readAt (lift bound) B))
  | _, Γ, bound, .sigma A B => .app (.app (HOL.weakenCtx Γ ops.sum) (readAt bound A))
      (.lam (readAt (lift bound) B))
  | _, Γ, bound, .lam A body => .app (.app (HOL.weakenCtx Γ ops.abstraction) (readAt bound A))
      (.lam (readAt (lift bound) body))
  | _, Γ, bound, .app f a => .app (.app (HOL.weakenCtx Γ ops.application) (readAt bound f)) (readAt bound a)
  | _, Γ, bound, .pair a b => .app (.app (HOL.weakenCtx Γ ops.pair) (readAt bound a)) (readAt bound b)
  | _, Γ, bound, .fst p => .app (HOL.weakenCtx Γ ops.first) (readAt bound p)
  | _, Γ, bound, .snd p => .app (HOL.weakenCtx Γ ops.second) (readAt bound p)
  | _, Γ, bound, .id _ a b => .app (HOL.weakenCtx Γ ops.truth) (.eq (readAt bound a) (readAt bound b))
  | _, Γ, _, .refl _ => HOL.weakenCtx Γ ops.empty

theorem readAt_rename {n m : Nat} {Γ : HOL.Ctx Base} (rho : Ren n m)
    (source : CTm Head n) (bound : Fin m → HOL.Term Const Γ object) :
    readAt ops bound (source.rename rho) = readAt ops (fun i => bound (rho i)) source := by
  induction source generalizing m Γ with
  | var i => rfl
  | head h => rfl
  | const c => rfl
  | pi A B ihA ihB | sigma A B ihA ihB | lam A B ihA ihB =>
    simp only [CTm.rename,readAt,ihA,ihB]
    congr 2
    apply congrArg (fun values => readAt ops values B)
    funext i
    refine Fin.cases ?_ (fun _ => ?_) i <;> rfl
  | app f a ihf iha | pair f a ihf iha => simp only [CTm.rename,readAt,ihf,iha]
  | fst p ih | snd p ih => simp only [CTm.rename,readAt,ih]
  | id A a b _ iha ihb => simp only [CTm.rename,readAt,iha,ihb]
  | refl _ _ => rfl

theorem readAt_targetSubst {n : Nat} {Γ Ξ : HOL.Ctx Base} (theta : HOL.Subst Const Γ Ξ)
    (source : CTm Head n) (bound : Fin n → HOL.Term Const Γ object) :
    HOL.subst theta (readAt ops bound source) =
      readAt ops (fun i => HOL.subst theta (bound i)) source := by
  induction source generalizing Γ Ξ with
  | var i => rfl
  | head h | const h => simp only [readAt,HOL.subst_weakenCtx]
  | pi A B ihA ihB | sigma A B ihA ihB | lam A B ihA ihB =>
    simp only [readAt,HOL.subst,HOL.subst_weakenCtx,ihA,ihB]
    congr 2
    apply congrArg (fun values => readAt ops values B)
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact HOL.subst_weaken theta (bound j)
  | app f a ihf iha | pair f a ihf iha => simp only [readAt,HOL.subst,HOL.subst_weakenCtx,ihf,iha]
  | fst p ih | snd p ih => simp only [readAt,HOL.subst,HOL.subst_weakenCtx,ih]
  | id A a b _ iha ihb => simp only [readAt,HOL.subst,HOL.subst_weakenCtx,iha,ihb]
  | refl _ _ => simp only [readAt,HOL.subst_weakenCtx]

theorem readAt_weaken {n : Nat} {Γ : HOL.Ctx Base} (added : HOL.Ty Base) (source : CTm Head n)
    (bound : Fin n → HOL.Term Const Γ object) :
    HOL.weaken (σ := added) (readAt ops bound source) = readAt ops (fun i => HOL.weaken (σ := added) (bound i)) source := by
  simpa only [HOL.subst_ofRename,HOL.weaken] using
    readAt_targetSubst ops (HOL.Subst.ofRename (HOL.Rename.weaken (σ := added))) source bound

theorem readAt_liftSub {n m : Nat} {Γ : HOL.Ctx Base} (sigma : CSub Head n m)
    (bound : Fin m → HOL.Term Const Γ object) :
    (fun i => readAt ops (lift bound) (CTm.liftSub sigma i)) =
      lift (fun i => readAt ops bound (sigma i)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · change readAt ops (lift bound) ((sigma j).rename wk) = HOL.weaken (readAt ops bound (sigma j))
    rw [readAt_rename,readAt_weaken]
    rfl

theorem readAt_subst {n m : Nat} {Γ : HOL.Ctx Base} (sigma : CSub Head n m)
    (source : CTm Head n) (bound : Fin m → HOL.Term Const Γ object) :
    readAt ops bound (source.subst sigma) = readAt ops (fun i => readAt ops bound (sigma i)) source := by
  induction source generalizing m Γ with
  | var i => rfl
  | head h | const h => rfl
  | pi A B ihA ihB | sigma A B ihA ihB | lam A B ihA ihB =>
    simp only [CTm.subst,readAt,ihA,ihB,readAt_liftSub]
  | app f a ihf iha | pair f a ihf iha => simp only [CTm.subst,readAt,ihf,iha]
  | fst p ih | snd p ih => simp only [CTm.subst,readAt,ih]
  | id A a b _ iha ihb => simp only [CTm.subst,readAt,iha,ihb]
  | refl _ _ => rfl

#print axioms readAt_subst
#print axioms readAt_targetSubst
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedCodedReading
