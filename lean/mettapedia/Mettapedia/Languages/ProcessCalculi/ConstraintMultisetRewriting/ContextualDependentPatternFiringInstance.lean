import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentGeneralPatternRigidRefutation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentDynamicFragment

/-!
# Instances of terms with Miller occurrences

Let `t` be a normal term whose flexible variables occur only as heads of Miller spines (distinct rigid
variables as arguments, never projected). Substitute normal terms for the flexible variables and variables
for the rigid ones. The instance need not be normal: a flexible spine `F ȳ` becomes `(σ F) ȳ'`, a redex
when `σ F` is an abstraction. It **reduces to a normal term** all the same (`miller_instance`):

* a normal term applied to variables reduces to a normal term, since each β-step substitutes a variable,
  which is a renaming (`apps_instance`);
* every other node keeps its constructor, so no redex appears above a flexible spine: a Miller spine is
  read maximally, hence never the function of an application, and it is never projected.

The **rigid support** of `t` is the set of its variables outside the arguments of its flexible spines
(`rigidSupport`). Every rigid variable of the rigid support survives in the normal instance. This is the
fact behind Miller's and Abel–Pientka's failure rule for a rigid out-of-scope local: unlike
`ContextualDependentGeneralPattern.refuted_rigid`, it allows flexible spines anywhere in the right side.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentPatternFiring

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open ContextualDependentDynamicFragment
open ContextualDependentGeneralPattern (liftFlexible Admissible Admissible.lift)

section Shapes

variable {Head : Type}

/-- **The rigid support**: the variables of a term outside the arguments of its flexible spines. -/
def rigidSupport : {n : Nat} → (Fin n → Bool) → Tm Head n → Finset (Fin n)
  | _, _, .var index => {index}
  | _, _, .const _ => ∅
  | _, _, .head _ => ∅
  | _, flexible, .pi domain body =>
      rigidSupport flexible domain ∪ outerSupport (rigidSupport (liftFlexible flexible) body)
  | _, flexible, .sigma domain body =>
      rigidSupport flexible domain ∪ outerSupport (rigidSupport (liftFlexible flexible) body)
  | _, flexible, .id carrier left right =>
      rigidSupport flexible carrier ∪ rigidSupport flexible left ∪ rigidSupport flexible right
  | _, flexible, .lam body => outerSupport (rigidSupport (liftFlexible flexible) body)
  | _, flexible, .app function argument =>
      if flexHead flexible (spineHead function) then ∅
      else rigidSupport flexible function ∪ rigidSupport flexible argument
  | _, flexible, .pair left right => rigidSupport flexible left ∪ rigidSupport flexible right
  | _, flexible, .fst value => rigidSupport flexible value
  | _, flexible, .snd value => rigidSupport flexible value
  | _, flexible, .refl value => rigidSupport flexible value

/-- Substituting a variable for the newest variable is a renaming. -/
theorem inst0_var {n : Nat} (image : Fin n) (body : Tm Head (n + 1)) :
    inst0 (.var image) body = rename (Fin.cases image fun index => index) body := by
  unfold inst0
  rw [← subst_renSub]
  congr 1
  funext index
  refine Fin.cases rfl (fun _ => rfl) index

end Shapes

section Reduction

variable {Head : Type} {R : Rules Head}

theorem reduces_pi {n : Nat} {A A' : Tm Head n} {B B' : Tm Head (n + 1)} (domain : Reduces R A A')
    (codomain : Reduces R B B') : Reduces R (.pi A B) (.pi A' B') :=
  (domain.lift (fun A => Tm.pi A B) fun _ _ step => StepCore.congPiDom step).trans
    (codomain.lift (fun B => Tm.pi A' B) fun _ _ step => StepCore.congPiCod step)

theorem reduces_sigma {n : Nat} {A A' : Tm Head n} {B B' : Tm Head (n + 1)} (domain : Reduces R A A')
    (codomain : Reduces R B B') : Reduces R (.sigma A B) (.sigma A' B') :=
  (domain.lift (fun A => Tm.sigma A B) fun _ _ step => StepCore.congSigmaDom step).trans
    (codomain.lift (fun B => Tm.sigma A' B) fun _ _ step => StepCore.congSigmaCod step)

theorem reduces_id {n : Nat} {A A' a a' b b' : Tm Head n} (carrier : Reduces R A A') (left : Reduces R a a')
    (right : Reduces R b b') : Reduces R (.id A a b) (.id A' a' b') :=
  ((carrier.lift (fun A => Tm.id A a b) fun _ _ step => StepCore.congIdTy step).trans
    (left.lift (fun a => Tm.id A' a b) fun _ _ step => StepCore.congIdLeft step)).trans
    (right.lift (fun b => Tm.id A' a' b) fun _ _ step => StepCore.congIdRight step)

theorem reduces_lam {n : Nat} {body body' : Tm Head (n + 1)} (inner : Reduces R body body') :
    Reduces R (.lam body) (.lam body') :=
  inner.lift Tm.lam fun _ _ step => StepCore.congLam step

theorem reduces_app {n : Nat} {f f' a a' : Tm Head n} (function : Reduces R f f') (argument : Reduces R a a') :
    Reduces R (.app f a) (.app f' a') :=
  (function.lift (fun f => Tm.app f a) fun _ _ step => StepCore.congAppFun step).trans
    (argument.lift (fun a => Tm.app f' a) fun _ _ step => StepCore.congAppArg step)

theorem reduces_pair {n : Nat} {a a' b b' : Tm Head n} (left : Reduces R a a') (right : Reduces R b b') :
    Reduces R (.pair a b) (.pair a' b') :=
  (left.lift (fun a => Tm.pair a b) fun _ _ step => StepCore.congPairFst step).trans
    (right.lift (fun b => Tm.pair a' b) fun _ _ step => StepCore.congPairSnd step)

theorem reduces_fst {n : Nat} {p p' : Tm Head n} (inner : Reduces R p p') : Reduces R (.fst p) (.fst p') :=
  inner.lift Tm.fst fun _ _ step => StepCore.congFst step

theorem reduces_snd {n : Nat} {p p' : Tm Head n} (inner : Reduces R p p') : Reduces R (.snd p) (.snd p') :=
  inner.lift Tm.snd fun _ _ step => StepCore.congSnd step

theorem reduces_refl {n : Nat} {a a' : Tm Head n} (inner : Reduces R a a') : Reduces R (.refl a) (.refl a') :=
  inner.lift Tm.refl fun _ _ step => StepCore.congRefl step

end Reduction

section Instances

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable (rigid : ∀ name, S.roles name = .rigid)

local notation "Normal" => ContextualDependentNormalChecking.Normal (S := S)

/-! ## Normal terms by their constructors -/

include rigid in
theorem normal_const {n : Nat} (name : DeclName) : Normal (.const name : Tm Head n) := by
  intro target step
  cases step with
  | root rootStep => exact ContextualDependentNormalObservations.no_root rigid rootStep

include rigid in
theorem normal_head {n : Nat} (value : Head) : Normal (.head value : Tm Head n) := by
  intro target step
  cases step with
  | root rootStep => exact ContextualDependentNormalObservations.no_root rigid rootStep
  | head same => exact (same : False).elim

include rigid in
theorem normal_pi {n : Nat} {A : Tm Head n} {B : Tm Head (n + 1)} (domain : Normal A) (codomain : Normal B) :
    Normal (.pi A B) := by
  intro target step
  cases step with
  | root rootStep => exact ContextualDependentNormalObservations.no_root rigid rootStep
  | congPiDom inner => exact domain _ inner
  | congPiCod inner => exact codomain _ inner

include rigid in
theorem normal_sigma {n : Nat} {A : Tm Head n} {B : Tm Head (n + 1)} (domain : Normal A) (codomain : Normal B) :
    Normal (.sigma A B) := by
  intro target step
  cases step with
  | root rootStep => exact ContextualDependentNormalObservations.no_root rigid rootStep
  | congSigmaDom inner => exact domain _ inner
  | congSigmaCod inner => exact codomain _ inner

include rigid in
theorem normal_id {n : Nat} {A a b : Tm Head n} (carrier : Normal A) (left : Normal a) (right : Normal b) :
    Normal (.id A a b) := by
  intro target step
  cases step with
  | root rootStep => exact ContextualDependentNormalObservations.no_root rigid rootStep
  | congIdTy inner => exact carrier _ inner
  | congIdLeft inner => exact left _ inner
  | congIdRight inner => exact right _ inner

include rigid in
theorem normal_lam {n : Nat} {body : Tm Head (n + 1)} (inner : Normal body) : Normal (.lam body) := by
  intro target step
  cases step with
  | root rootStep => exact ContextualDependentNormalObservations.no_root rigid rootStep
  | congLam step => exact inner _ step

include rigid in
theorem normal_pair {n : Nat} {a b : Tm Head n} (left : Normal a) (right : Normal b) : Normal (.pair a b) := by
  intro target step
  cases step with
  | root rootStep => exact ContextualDependentNormalObservations.no_root rigid rootStep
  | congPairFst inner => exact left _ inner
  | congPairSnd inner => exact right _ inner

include rigid in
theorem normal_refl {n : Nat} {a : Tm Head n} (inner : Normal a) : Normal (.refl a) := by
  intro target step
  cases step with
  | root rootStep => exact ContextualDependentNormalObservations.no_root rigid rootStep
  | congRefl step => exact inner _ step

/-! ## A normal term applied to variables -/

include rigid in
/-- **A normal term applied to variables reduces to a normal term.** -/
theorem applied_normalizes {m : Nat} (function : Tm Head m) (normal : Normal function) :
    ∀ arguments : List (Fin m), ∃ result, Reduces S.R (appsVar function arguments) result ∧ Normal result
  | [] => ⟨function, .refl, normal⟩
  | argument :: rest => by
      obtain ⟨inner, reduced, innerNormal⟩ := applied_normalizes function normal rest
      have toApp : Reduces S.R (appsVar function (argument :: rest)) (.app inner (.var argument)) :=
        reduces_app reduced .refl
      by_cases isLambda : ∃ body, inner = .lam body
      · obtain ⟨body, rfl⟩ := isLambda
        refine ⟨inst0 (.var argument) body, toApp.tail (StepCore.betaPi body (.var argument)), ?_⟩
        rw [inst0_var]
        exact ContextualDependentNormalObservations.normal_rename rigid _
          (ContextualDependentNormalObservations.normal_lam innerNormal)
      · refine ⟨.app inner (.var argument), toApp, ?_⟩
        exact ContextualDependentNormalObservations.normal_app rigid innerNormal
          (ContextualDependentNormalObservations.normal_var rigid argument)
          (fun body same => isLambda ⟨body, same⟩)

/-- Substituting into a variable spine whose arguments go to variables. -/
theorem subst_apps {n m : Nat} (σ : Sub Head n m) (head : Fin n) :
    ∀ arguments : List (Fin n), (∀ argument ∈ arguments, ∃ image, σ argument = .var image) →
      ∃ images : List (Fin m), subst σ (appsVar (.var head) arguments) = appsVar (σ head) images
  | [], _ => ⟨[], rfl⟩
  | argument :: rest, onVariables => by
      obtain ⟨images, same⟩ := subst_apps σ head rest
        fun other member => onVariables other (List.mem_cons_of_mem _ member)
      obtain ⟨image, mapped⟩ := onVariables argument List.mem_cons_self
      refine ⟨image :: images, ?_⟩
      simp only [appsVar, subst]
      rw [same, mapped]

/-! ## Miller instances -/

include rigid in
/-- **A Miller instance reduces to a normal term**, keeping the constructor of every node that is not a
flexible spine, and every rigid variable of the rigid support. -/
theorem miller_instance {n : Nat} (t : Tm Head n) :
    ∀ {m : Nat} (flexible : Fin n → Bool) (σ : Sub Head n m),
      Normal t → miller flexible t = true → Admissible S flexible σ →
      ∃ result : Tm Head m, Reduces S.R (subst σ t) result ∧ Normal result ∧
        (flexHead flexible (spineHead t) = false → isLam result = isLam t ∧ isPair result = isPair t) ∧
        ∀ index image, index ∈ rigidSupport flexible t → σ index = .var image → image ∈ result.support := by
  induction t with
  | var index =>
      intro m flexible σ _ _ admissible
      refine ⟨σ index, .refl, ?_, fun rigidHead => ?_, fun other image member mapped => ?_⟩
      · cases mode : flexible index with
        | true => exact (admissible index).1 mode
        | false =>
            obtain ⟨image, mapped⟩ := (admissible index).2 mode
            rw [mapped]
            exact ContextualDependentNormalObservations.normal_var rigid image
      · obtain ⟨image, mapped⟩ := (admissible index).2 rigidHead
        rw [mapped]
        exact ⟨rfl, rfl⟩
      · have same : other = index := by simpa [rigidSupport] using member
        subst same
        rw [mapped]
        simp [Tm.support]
  | const name =>
      intro m flexible σ _ _ _
      exact ⟨.const name, .refl, normal_const rigid name, fun _ => ⟨rfl, rfl⟩,
        fun _ _ member => by simp [rigidSupport] at member⟩
  | head value =>
      intro m flexible σ _ _ _
      exact ⟨.head value, .refl, normal_head rigid value, fun _ => ⟨rfl, rfl⟩,
        fun _ _ member => by simp [rigidSupport] at member⟩
  | pi domain body ihDomain ihBody =>
      intro m flexible σ normal holds admissible
      simp only [miller, Bool.and_eq_true] at holds
      obtain ⟨domain', reducedDomain, normalDomain, _, keepsDomain⟩ :=
        ihDomain flexible σ (fun _ next => normal _ (.congPiDom next)) holds.1 admissible
      obtain ⟨body', reducedBody, normalBody, _, keepsBody⟩ :=
        ihBody (liftFlexible flexible) (liftSub σ) (fun _ next => normal _ (.congPiCod next)) holds.2
          (admissible.lift rigid)
      refine ⟨.pi domain' body', reduces_pi reducedDomain reducedBody, normal_pi rigid normalDomain normalBody,
        fun _ => ⟨rfl, rfl⟩, fun index image member mapped => ?_⟩
      simp only [rigidSupport, Finset.mem_union, mem_outerSupport] at member
      simp only [Tm.support, Finset.mem_union, mem_outerSupport]
      rcases member with member | member
      · exact .inl (keepsDomain index image member mapped)
      · exact .inr (keepsBody index.succ image.succ member (by simp [liftSub_succ, mapped]; rfl))
  | sigma domain body ihDomain ihBody =>
      intro m flexible σ normal holds admissible
      simp only [miller, Bool.and_eq_true] at holds
      obtain ⟨domain', reducedDomain, normalDomain, _, keepsDomain⟩ :=
        ihDomain flexible σ (fun _ next => normal _ (.congSigmaDom next)) holds.1 admissible
      obtain ⟨body', reducedBody, normalBody, _, keepsBody⟩ :=
        ihBody (liftFlexible flexible) (liftSub σ) (fun _ next => normal _ (.congSigmaCod next)) holds.2
          (admissible.lift rigid)
      refine ⟨.sigma domain' body', reduces_sigma reducedDomain reducedBody,
        normal_sigma rigid normalDomain normalBody, fun _ => ⟨rfl, rfl⟩, fun index image member mapped => ?_⟩
      simp only [rigidSupport, Finset.mem_union, mem_outerSupport] at member
      simp only [Tm.support, Finset.mem_union, mem_outerSupport]
      rcases member with member | member
      · exact .inl (keepsDomain index image member mapped)
      · exact .inr (keepsBody index.succ image.succ member (by simp [liftSub_succ, mapped]; rfl))
  | id carrier left right ihCarrier ihLeft ihRight =>
      intro m flexible σ normal holds admissible
      simp only [miller, Bool.and_eq_true] at holds
      obtain ⟨⟨carrierHolds, leftHolds⟩, rightHolds⟩ := holds
      obtain ⟨carrier', reducedCarrier, normalCarrier, _, keepsCarrier⟩ :=
        ihCarrier flexible σ (fun _ next => normal _ (.congIdTy next)) carrierHolds admissible
      obtain ⟨left', reducedLeft, normalLeft, _, keepsLeft⟩ :=
        ihLeft flexible σ (fun _ next => normal _ (.congIdLeft next)) leftHolds admissible
      obtain ⟨right', reducedRight, normalRight, _, keepsRight⟩ :=
        ihRight flexible σ (fun _ next => normal _ (.congIdRight next)) rightHolds admissible
      refine ⟨.id carrier' left' right', reduces_id reducedCarrier reducedLeft reducedRight,
        normal_id rigid normalCarrier normalLeft normalRight, fun _ => ⟨rfl, rfl⟩,
        fun index image member mapped => ?_⟩
      simp only [rigidSupport, Finset.mem_union] at member
      simp only [Tm.support, Finset.mem_union]
      rcases member with (member | member) | member
      · exact .inl (.inl (keepsCarrier index image member mapped))
      · exact .inl (.inr (keepsLeft index image member mapped))
      · exact .inr (keepsRight index image member mapped)
  | lam body ih =>
      intro m flexible σ normal holds admissible
      simp only [miller] at holds
      obtain ⟨body', reduced, normalBody, _, keeps⟩ :=
        ih (liftFlexible flexible) (liftSub σ) (fun _ next => normal _ (.congLam next)) holds (admissible.lift rigid)
      refine ⟨.lam body', reduces_lam reduced, normal_lam rigid normalBody, fun _ => ⟨rfl, rfl⟩,
        fun index image member mapped => ?_⟩
      simp only [rigidSupport, mem_outerSupport] at member
      simp only [Tm.support, mem_outerSupport]
      exact keeps index.succ image.succ member (by simp [liftSub_succ, mapped]; rfl)
  | app function argument ihFunction ihArgument =>
      intro m flexible σ normal holds admissible
      by_cases flexibleSpine : flexHead flexible (spineHead function) = true
      · simp only [miller, flexibleSpine, if_true] at holds
        cases read : readSpine (Tm.app function argument) with
        | none => simp [millerSpine, read] at holds
        | some found =>
            obtain ⟨head, arguments⟩ := found
            simp only [millerSpine, read, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_eq_eq_not,
              Bool.not_true, decide_eq_true_eq] at holds
            obtain ⟨⟨flexibleHead, rigidArguments⟩, _⟩ := holds
            have shape := readSpine_spec read
            obtain ⟨images, substituted⟩ := subst_apps σ head arguments fun other member =>
              (admissible other).2 (rigidArguments other member)
            obtain ⟨result, reduced, normalResult⟩ :=
              applied_normalizes rigid (σ head) ((admissible head).1 flexibleHead) images
            refine ⟨result, ?_, normalResult, fun rigidHead => ?_, fun index image member _ => ?_⟩
            · rw [shape, substituted]
              exact reduced
            · change flexHead flexible (spineHead function) = false at rigidHead
              rw [flexibleSpine] at rigidHead
              cases rigidHead
            · simp [rigidSupport, flexibleSpine] at member
      · have rigidSpine : flexHead flexible (spineHead function) = false := by
          cases computed : flexHead flexible (spineHead function)
          · rfl
          · exact absurd computed flexibleSpine
        simp only [miller, rigidSpine, Bool.false_eq_true, if_false, Bool.and_eq_true] at holds
        have functionNormal : Normal function := fun _ next => normal _ (.congAppFun next)
        obtain ⟨function', reducedFunction, normalFunction, shapeFunction, keepsFunction⟩ :=
          ihFunction flexible σ functionNormal holds.1 admissible
        obtain ⟨argument', reducedArgument, normalArgument, _, keepsArgument⟩ :=
          ihArgument flexible σ (fun _ next => normal _ (.congAppArg next)) holds.2 admissible
        have notLambda : ∀ body, function' ≠ .lam body := by
          intro body same
          have lambda := (shapeFunction rigidSpine).1
          rw [same] at lambda
          cases function with
          | lam inner => exact normal _ (.betaPi inner argument)
          | _ => cases lambda
        refine ⟨.app function' argument', reduces_app reducedFunction reducedArgument,
          ContextualDependentNormalObservations.normal_app rigid normalFunction normalArgument notLambda,
          fun _ => ⟨rfl, rfl⟩, fun index image member mapped => ?_⟩
        simp only [rigidSupport, rigidSpine, Bool.false_eq_true, if_false, Finset.mem_union] at member
        simp only [Tm.support, Finset.mem_union]
        rcases member with member | member
        · exact .inl (keepsFunction index image member mapped)
        · exact .inr (keepsArgument index image member mapped)
  | pair left right ihLeft ihRight =>
      intro m flexible σ normal holds admissible
      simp only [miller, Bool.and_eq_true] at holds
      obtain ⟨left', reducedLeft, normalLeft, _, keepsLeft⟩ :=
        ihLeft flexible σ (fun _ next => normal _ (.congPairFst next)) holds.1 admissible
      obtain ⟨right', reducedRight, normalRight, _, keepsRight⟩ :=
        ihRight flexible σ (fun _ next => normal _ (.congPairSnd next)) holds.2 admissible
      refine ⟨.pair left' right', reduces_pair reducedLeft reducedRight, normal_pair rigid normalLeft normalRight,
        fun _ => ⟨rfl, rfl⟩, fun index image member mapped => ?_⟩
      simp only [rigidSupport, Finset.mem_union] at member
      simp only [Tm.support, Finset.mem_union]
      rcases member with member | member
      · exact .inl (keepsLeft index image member mapped)
      · exact .inr (keepsRight index image member mapped)
  | fst value ih =>
      intro m flexible σ normal holds admissible
      simp only [miller, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at holds
      obtain ⟨rigidValue, valueHolds⟩ := holds
      obtain ⟨value', reduced, normalValue, shapeValue, keeps⟩ :=
        ih flexible σ (fun _ next => normal _ (.congFst next)) valueHolds admissible
      have notPair : ∀ first second, value' ≠ .pair first second := by
        intro first second same
        have paired := (shapeValue rigidValue).2
        rw [same] at paired
        cases value with
        | pair a b => exact normal _ (.betaSigmaFst a b)
        | _ => cases paired
      refine ⟨.fst value', reduces_fst reduced,
        ContextualDependentNormalObservations.normal_fst rigid normalValue notPair, fun _ => ⟨rfl, rfl⟩,
        fun index image member mapped => ?_⟩
      simp only [rigidSupport] at member
      exact keeps index image member mapped
  | snd value ih =>
      intro m flexible σ normal holds admissible
      simp only [miller, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at holds
      obtain ⟨rigidValue, valueHolds⟩ := holds
      obtain ⟨value', reduced, normalValue, shapeValue, keeps⟩ :=
        ih flexible σ (fun _ next => normal _ (.congSnd next)) valueHolds admissible
      have notPair : ∀ first second, value' ≠ .pair first second := by
        intro first second same
        have paired := (shapeValue rigidValue).2
        rw [same] at paired
        cases value with
        | pair a b => exact normal _ (.betaSigmaSnd a b)
        | _ => cases paired
      refine ⟨.snd value', reduces_snd reduced,
        ContextualDependentNormalObservations.normal_snd rigid normalValue notPair, fun _ => ⟨rfl, rfl⟩,
        fun index image member mapped => ?_⟩
      simp only [rigidSupport] at member
      exact keeps index image member mapped
  | refl value ih =>
      intro m flexible σ normal holds admissible
      simp only [miller] at holds
      obtain ⟨value', reduced, normalValue, _, keeps⟩ :=
        ih flexible σ (fun _ next => normal _ (.congRefl next)) holds admissible
      refine ⟨.refl value', reduces_refl reduced, normal_refl rigid normalValue, fun _ => ⟨rfl, rfl⟩,
        fun index image member mapped => ?_⟩
      simp only [rigidSupport] at member
      exact keeps index image member mapped

end Instances

end ContextualDependentPatternFiring
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
