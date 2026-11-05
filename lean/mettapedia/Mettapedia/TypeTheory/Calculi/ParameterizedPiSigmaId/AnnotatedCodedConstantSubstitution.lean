import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedCodedReading
import Mettapedia.Logic.HOL.Syntax.ConstantSubstitutionComposition

/-!
# Closed definitions commute with the uniform coded reader

Replacing each operation's constants by closed terms gives the same result
as replacing them after reading a source term. The theorem covers binders,
source instantiation and arbitrary target contexts.
-/

set_option autoImplicit false
namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedCodedReading
open Mettapedia.Logic
open Presentation TypedEquality.Annotated
universe u v w
variable {Head : Type} {Base : Type u} {Const : HOL.Ty Base → Type v} {Target : HOL.Ty Base → Type w}
variable {object : HOL.Ty Base}

def Operations.mapDefinitions (operations : Operations Head Const object)
    (images : ∀ {type}, Const type → HOL.ClosedTerm Target type) : Operations Head Target object where
  head name := HOL.substConst images (operations.head name)
  constant name := HOL.substConst images (operations.constant name)
  product := HOL.substConst images operations.product
  sum := HOL.substConst images operations.sum
  abstraction := HOL.substConst images operations.abstraction
  application := HOL.substConst images operations.application
  pair := HOL.substConst images operations.pair
  first := HOL.substConst images operations.first
  second := HOL.substConst images operations.second
  truth := HOL.substConst images operations.truth
  empty := HOL.substConst images operations.empty

variable (operations : Operations Head Const object)

theorem substConst_lift (images : ∀ {type}, Const type → HOL.ClosedTerm Target type)
    {n : Nat} {Γ : HOL.Ctx Base} (bound : Fin n → HOL.Term Const Γ object) :
    (fun index => HOL.substConst images (lift bound index)) =
      lift (fun index => HOL.substConst images (bound index)) := by
  funext index
  refine Fin.cases ?_ (fun next => ?_) index
  · rfl
  · exact HOL.substConst_weaken images (bound next)

theorem readAt_substConst (images : ∀ {type}, Const type → HOL.ClosedTerm Target type)
    {n : Nat} {Γ : HOL.Ctx Base} (source : CTm Head n) (bound : Fin n → HOL.Term Const Γ object) :
    HOL.substConst images (readAt operations bound source) =
      readAt (operations.mapDefinitions images) (fun index => HOL.substConst images (bound index)) source := by
  induction source generalizing Γ with
  | var index => rfl
  | head name | const name => simp only [readAt,Operations.mapDefinitions,HOL.substConst_weakenCtx]
  | pi domain body domainIH bodyIH | sigma domain body domainIH bodyIH | lam domain body domainIH bodyIH =>
    simp only [readAt,Operations.mapDefinitions,HOL.substConst,HOL.substConst_weakenCtx,domainIH,bodyIH,substConst_lift]
  | app function argument functionIH argumentIH | pair function argument functionIH argumentIH =>
    simp only [readAt,Operations.mapDefinitions,HOL.substConst,HOL.substConst_weakenCtx,functionIH,argumentIH]
  | fst point previous | snd point previous =>
    simp only [readAt,Operations.mapDefinitions,HOL.substConst,HOL.substConst_weakenCtx,previous]
  | id type left right _ leftIH rightIH =>
    simp only [readAt,Operations.mapDefinitions,HOL.substConst,HOL.substConst_weakenCtx,leftIH,rightIH]
  | refl point _ => simp only [readAt,Operations.mapDefinitions,HOL.substConst_weakenCtx]

theorem readAt_inst0 {n : Nat} {Γ : HOL.Ctx Base} (value : CTm Head n) (body : CTm Head (n+1))
    (bound : Fin n → HOL.Term Const Γ object) :
    readAt operations bound (CTm.inst0 value body) =
      HOL.instantiate (readAt operations bound value) (readAt operations (lift bound) body) := by
  rw [CTm.inst0,readAt_subst,HOL.instantiate,readAt_targetSubst]
  apply congrArg (fun values => readAt operations values body)
  funext index
  refine Fin.cases ?_ (fun next => ?_) index
  · rfl
  · exact (HOL.instantiate_weaken (readAt operations bound value) (bound next)).symm

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedCodedReading
