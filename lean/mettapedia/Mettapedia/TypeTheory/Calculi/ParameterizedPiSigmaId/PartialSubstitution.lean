import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedSubstitution
import Mettapedia.Data.Option.Constructor
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Fin

/-!
# Finite term support and checked partial substitution

The executable support inventory represents the already defined free-variable
set. A partial environment may omit unused slots. Substitution rejects a used
missing slot rather than supplying an arbitrary native term. Lifting a partial
environment still creates the bound variable and weakens each older value.

The exactness theorem compares this checked traversal to ordinary simultaneous
substitution; it applies under every native binder.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation

variable {Head : Type} {n m : Nat}

/-- Older coordinates used beneath one binder. -/
def outerSupport {n : Nat} (slots : Finset (Fin (n + 1))) : Finset (Fin n) :=
  Finset.univ.filter fun index => index.succ ∈ slots

@[simp] theorem mem_outerSupport {slots : Finset (Fin (n + 1))} {index : Fin n} :
    index ∈ outerSupport slots ↔ index.succ ∈ slots := by
  simp [outerSupport]

/-- A computable inventory of the existing syntactic free-variable set. -/
def Tm.support : {n : Nat} → Tm Head n → Finset (Fin n)
  | _, .var index => {index}
  | _, .const _ | _, .head _ => ∅
  | _, .pi domain body | _, .sigma domain body =>
      domain.support ∪ outerSupport body.support
  | _, .id carrier left right => carrier.support ∪ left.support ∪ right.support
  | _, .lam body => outerSupport body.support
  | _, .app left right | _, .pair left right => left.support ∪ right.support
  | _, .fst value | _, .snd value | _, .refl value => value.support

@[simp] theorem Tm.mem_support (term : Tm Head n) (index : Fin n) :
    index ∈ term.support ↔ index ∈ term.freeVariables := by
  induction term with
  | var candidate => simp [support, freeVariables]
  | const name => simp [support, freeVariables]
  | head value => simp [support, freeVariables]
  | pi domain body ihDomain ihBody => simp [support, freeVariables, ihDomain, ihBody]
  | sigma domain body ihDomain ihBody => simp [support, freeVariables, ihDomain, ihBody]
  | id carrier left right ihCarrier ihLeft ihRight =>
      simp [support, freeVariables, ihCarrier, ihLeft, ihRight, or_assoc]
  | lam body ihBody => simp [support, freeVariables, ihBody]
  | app left right ihLeft ihRight => simp [support, freeVariables, ihLeft, ihRight]
  | pair left right ihLeft ihRight => simp [support, freeVariables, ihLeft, ihRight]
  | fst value ihValue => exact ihValue index
  | snd value ihValue => exact ihValue index
  | refl value ihValue => exact ihValue index

abbrev PartialSub (Head : Type) (n m : Nat) := Fin n → Option (Tm Head m)

def liftPartialSub (environment : PartialSub Head n m) : PartialSub Head (n + 1) (m + 1) :=
  Fin.cases (some (.var 0)) fun index => (environment index).map (rename wk)

/-- Checked, capture-avoiding substitution. Missing used entries are explicit. -/
def substPartial {n m : Nat} (environment : PartialSub Head n m) :
    Tm Head n → Option (Tm Head m)
  | .var index => environment index
  | .const name => some (.const name)
  | .head value => some (.head value)
  | .pi domain body => do
      let domain ← substPartial environment domain
      let body ← substPartial (liftPartialSub environment) body
      pure (.pi domain body)
  | .sigma domain body => do
      let domain ← substPartial environment domain
      let body ← substPartial (liftPartialSub environment) body
      pure (.sigma domain body)
  | .id carrier left right => do
      let carrier ← substPartial environment carrier
      let left ← substPartial environment left
      let right ← substPartial environment right
      pure (.id carrier left right)
  | .lam body => (substPartial (liftPartialSub environment) body).map Tm.lam
  | .app left right => do
      let left ← substPartial environment left
      let right ← substPartial environment right
      pure (.app left right)
  | .pair left right => do
      let left ← substPartial environment left
      let right ← substPartial environment right
      pure (.pair left right)
  | .fst value => (substPartial environment value).map Tm.fst
  | .snd value => (substPartial environment value).map Tm.snd
  | .refl value => (substPartial environment value).map Tm.refl

theorem liftPartialSub_agrees {slots : Finset (Fin (n + 1))}
    {partialEnv : PartialSub Head n m} {environment : Sub Head n m}
    (agree : ∀ index, index ∈ outerSupport slots →
      partialEnv index = some (environment index)) :
    ∀ index, index ∈ slots →
      liftPartialSub partialEnv index = some (liftSub environment index) := by
  intro index
  refine Fin.cases ?_ ?_ index
  · intro _
    rfl
  · intro prior present
    simp only [liftPartialSub, Fin.cases_succ, liftSub]
    rw [agree prior (mem_outerSupport.mpr present)]
    rfl

/-- Agreement on the computed support suffices; omitted slots outside that
support cannot affect the result. -/
theorem substPartial_eq (term : Tm Head n) {partialEnv : PartialSub Head n m}
    {environment : Sub Head n m}
    (agree : ∀ index, index ∈ term.support → partialEnv index = some (environment index)) :
    substPartial partialEnv term = some (subst environment term) := by
  induction term generalizing m with
  | var index => exact agree index (by simp [Tm.support])
  | const name => rfl
  | head value => rfl
  | pi domain body ihDomain ihBody =>
      rw [substPartial, ihDomain (fun i hi => agree i (Finset.mem_union_left _ hi)),
        ihBody (liftPartialSub_agrees (fun i hi => agree i (Finset.mem_union_right _ hi)))]
      rfl
  | sigma domain body ihDomain ihBody =>
      rw [substPartial, ihDomain (fun i hi => agree i (Finset.mem_union_left _ hi)),
        ihBody (liftPartialSub_agrees (fun i hi => agree i (Finset.mem_union_right _ hi)))]
      rfl
  | id carrier left right ihCarrier ihLeft ihRight =>
      rw [substPartial,
        ihCarrier (fun i hi => agree i (Finset.mem_union_left _ (Finset.mem_union_left _ hi))),
        ihLeft (fun i hi => agree i (Finset.mem_union_left _ (Finset.mem_union_right _ hi))),
        ihRight (fun i hi => agree i (Finset.mem_union_right _ hi))]
      rfl
  | lam body ihBody =>
      rw [substPartial, ihBody (liftPartialSub_agrees agree)]
      rfl
  | app left right ihLeft ihRight =>
      rw [substPartial, ihLeft (fun i hi => agree i (Finset.mem_union_left _ hi)),
        ihRight (fun i hi => agree i (Finset.mem_union_right _ hi))]
      rfl
  | pair left right ihLeft ihRight =>
      rw [substPartial, ihLeft (fun i hi => agree i (Finset.mem_union_left _ hi)),
        ihRight (fun i hi => agree i (Finset.mem_union_right _ hi))]
      rfl
  | fst value ihValue => rw [substPartial, ihValue agree]; rfl
  | snd value ihValue => rw [substPartial, ihValue agree]; rfl
  | refl value ihValue => rw [substPartial, ihValue agree]; rfl

theorem liftPartialSub_defined (slots : Finset (Fin (n + 1)))
    (environment : PartialSub Head n m) :
    (∀ index, index ∈ slots → (liftPartialSub environment index).isSome = true) ↔
      ∀ index, index ∈ outerSupport slots → (environment index).isSome = true := by
  constructor
  · intro all index present
    simpa [liftPartialSub] using all index.succ (mem_outerSupport.mp present)
  · intro all index
    refine Fin.cases ?_ ?_ index
    · intro _
      rfl
    · intro prior present
      simpa [liftPartialSub] using all prior (mem_outerSupport.mpr present)

/-- Exact admission for checked raw syntax reconstruction, including variables
below binders. No used missing capture can be silently replaced. -/
theorem substPartial_defined (term : Tm Head n) (environment : PartialSub Head n m) :
    (substPartial environment term).isSome = true ↔
      ∀ index, index ∈ term.support → (environment index).isSome = true := by
  induction term generalizing m with
  | var index => simp [substPartial, Tm.support]
  | const name => simp [substPartial, Tm.support]
  | head value => simp [substPartial, Tm.support]
  | pi domain body ihDomain ihBody =>
      simp only [substPartial, Option.assemble_two_isSome, Bool.and_eq_true,
        ihDomain, ihBody, liftPartialSub_defined, Tm.support,
        Finset.mem_union, or_imp, forall_and]
  | sigma domain body ihDomain ihBody =>
      simp only [substPartial, Option.assemble_two_isSome, Bool.and_eq_true,
        ihDomain, ihBody, liftPartialSub_defined, Tm.support,
        Finset.mem_union, or_imp, forall_and]
  | id carrier left right ihCarrier ihLeft ihRight =>
      simp only [substPartial, Option.assemble_three_isSome, Bool.and_eq_true,
        ihCarrier, ihLeft, ihRight, Tm.support, Finset.mem_union, or_imp, forall_and]
  | lam body ihBody =>
      simpa only [substPartial, Option.isSome_map, Tm.support] using
        (ihBody (liftPartialSub environment)).trans (liftPartialSub_defined _ _)
  | app left right ihLeft ihRight =>
      simp only [substPartial, Option.assemble_two_isSome, Bool.and_eq_true,
        ihLeft, ihRight, Tm.support, Finset.mem_union, or_imp, forall_and]
  | pair left right ihLeft ihRight =>
      simp only [substPartial, Option.assemble_two_isSome, Bool.and_eq_true,
        ihLeft, ihRight, Tm.support, Finset.mem_union, or_imp, forall_and]
  | fst value ihValue => simpa only [substPartial, Option.isSome_map, Tm.support] using ihValue environment
  | snd value ihValue => simpa only [substPartial, Option.isSome_map, Tm.support] using ihValue environment
  | refl value ihValue => simpa only [substPartial, Option.isSome_map, Tm.support] using ihValue environment

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
