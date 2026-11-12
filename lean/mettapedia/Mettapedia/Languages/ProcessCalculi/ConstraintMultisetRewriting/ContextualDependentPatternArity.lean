import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentElimReads
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPatternFiringInstance

/-!
# The arity of an unknown is read from its type

The dynamic pattern fragment asks every unknown to be applied to as many arguments as its **declared** type has
leading Π binders (`metaArity`, `arities`). The permuted Miller class has no such condition. It is not needed: on a
typed side the count is forced.

**The derived arity** (`tower_pattern_arity`). A head with a normal principal type `T`, applied to **variables**,
typed at a type that is not a function type up to equality, has exactly `piCount T` arguments. The proof follows the
spine from the head: a normal type below a Π type is a Π type (`tower_normal_pi_of_le`), instantiating its codomain
at a variable is a renaming, which keeps both normality and the Π count; at the end of the spine a Π type cannot be
below a type that is not one. For an unknown the arity is the Π count of the normal form of its declared type
(`tower_unknown_arity`); no arity is declared and none is read from the store.

**The hypothesis "applied to variables" is needed** (`ArityControls.applied_twice`, `ArityControls.arity_one`). Over
`A : U0, a : A, F : Π (X : U0). X` the spine `F (A → A) a` is typed at `A`, which is not a function type, and has two
arguments, while the type of `F` has one Π binder: an argument that is a type can turn the codomain into a function
type. In a Miller pattern the arguments are bound locals, so the count is the Π count.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentEtaDepth

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist ContextualDependentDynamicFragment
open ContextualDependentSpinesMany
open ContextualDependentIntersectionGeneral.DeadControls ContextualDependentPatternFiring.Controls
open ContextualDependentAcceptance4
open ContextualDependentExecutableJoin (Star Normal)
open ContextualDependentPatternFiring (inst0_var)

/-- **The arity is forced by typing**: a head with a normal principal type, applied to variables and typed at a
type that is not a function type up to equality, has as many arguments as its type has leading Π binders. -/
theorem tower_pattern_arity {n : Nat} {Γ : Ctx (LevelTower.Head Nat) n} (formed : CtxFormed setting.R Γ) :
    ∀ (arguments : List (Fin n)) {head type result : Tower.Tm n},
      TypedEquality.Typed setting.R Γ head type →
      (∀ U, TypedEquality.Typed setting.R Γ head U → TypeLe setting.R Γ type U) → Normal setting.R type →
      TypedEquality.Typed setting.R Γ (appSpine head (arguments.map Tm.var)) result →
      (∀ domain codomain, ¬ TypeEq setting.R Γ result (.pi domain codomain)) →
      arguments.length = piCount type
  | [], head, type, result, typedHead, principal, _, typed, notPi => by
      have facts : FormFacts setting.R setting.roles := TowerModel.facts
      have le : TypeLe setting.R Γ type result := principal _ typed
      cases type with
      | pi domain codomain =>
          have isResult := Typed.isType typed formed
          obtain ⟨_, _, same, _, _⟩ := Below.pi_source facts (TypeLe.toBelow le isResult) formed
            (IsType.refl (Typed.isType typedHead formed))
          exact absurd same (notPi _ _)
      | _ => rfl
  | argument :: rest, head, type, result, typedHead, principal, normal, typed, notPi => by
      have facts : FormFacts setting.R setting.roles := TowerModel.facts
      have empty : setting.R.computation = RootComputation.empty := rfl
      obtain ⟨U, prefixTyped⟩ := appSpine_prefix_typed (t := .app head (.var argument)) (rest.map Tm.var) typed
      obtain ⟨A, B, tf, ta, _⟩ := Typed.generation prefixTyped
      obtain ⟨DL, EL, rfl⟩ := tower_normal_pi_of_le formed normal (Typed.isType typedHead formed)
        (Typed.isType tf formed) (principal _ tf)
      obtain ⟨domains, _⟩ := TypeLe.pi_parts facts (principal _ tf) (Typed.isType tf formed) formed
      have ta' : TypedEquality.Typed setting.R Γ (.var argument) DL := Typed.convType ta domains.symm
      have principal' : ∀ U, TypedEquality.Typed setting.R Γ (.app head (.var argument)) U →
          TypeLe setting.R Γ (inst0 (.var argument) EL) U := by
        intro U typedU
        obtain ⟨A', B', tf'', ta'', le'⟩ := Typed.generation typedU
        obtain ⟨doms, codoms⟩ := TypeLe.pi_parts facts (principal _ tf'') (Typed.isType tf'' formed) formed
        have instantiated : Below setting.R Γ (inst0 (.var argument) EL) (inst0 (.var argument) B') :=
          Derivable.substitutes codoms (SubstMor.single (Typed.convType ta'' doms.symm))
        exact .sub instantiated le'
      have normal' : Normal setting.R (inst0 (.var argument) EL) := by
        rw [inst0_var]
        exact (ContextualDependentNormalizing.normal_rename_iff empty _ _).mpr ((normal_pi_iff empty).mp normal).2
      have below := tower_pattern_arity formed rest (Derivable.appElim typedHead ta') principal' normal' typed notPi
      rw [inst0_var, ContextualDependentDynamicFragment.piCount_rename] at below
      simp only [List.length_cons, piCount, below]

/-- **The arity of an unknown is the Π count of the normal form of its declared type**: a variable applied to
variables and typed at a type that is not a function type up to equality has as many arguments as the normal form of
its declared type has leading Π binders. -/
theorem tower_unknown_arity {n : Nat} {Γ : Ctx (LevelTower.Head Nat) n} (formed : CtxFormed setting.R Γ)
    {h : Fin n} {normalType result : Tower.Tm n} (arguments : List (Fin n))
    (same : TypeEq setting.R Γ (Ctx.lookup Γ h) normalType) (normal : Normal setting.R normalType)
    (typed : TypedEquality.Typed setting.R Γ (appSpine (.var h) (arguments.map Tm.var)) result)
    (notPi : ∀ domain codomain, ¬ TypeEq setting.R Γ result (.pi domain codomain)) :
    arguments.length = piCount normalType :=
  tower_pattern_arity formed arguments (Typed.convType (.var h) same)
    (fun U typedU => by
      obtain ⟨u, hu, e⟩ := TypeEq.symm same
      exact .conv e hu (Typed.generation typedU))
    normal typed notPi

end ContextualDependentEtaDepth
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
