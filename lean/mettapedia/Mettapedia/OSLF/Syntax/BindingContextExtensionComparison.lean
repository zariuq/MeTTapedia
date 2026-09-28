import Mettapedia.OSLF.Syntax.BindingOperationPresheaf
import Mettapedia.OSLF.Syntax.IntrinsicScopedConditionalSubstitution

/-!
# Categorical binder extension agrees with authored substitution

The product-context map that keeps binder variables fixed and substitutes
ambient variables is exactly the binding algebra's environment lift. This
comparison holds for arbitrary ordered multisorted binder contexts and makes
the closed presheaf interpretation of authored operations computationally
compatible with their source substitution laws.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.MultiBinderPresheaf

open _root_.CategoryTheory
open Mettapedia.GSLT.LanguageDef.MultiSortedClone
open Mettapedia.OSLF.Binding.BindingSubstitutionAlgebra
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPresheaf
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalSubstitution

universe u
variable {S : Signature}

def environmentArrow (A : BindingCloneAlgebra.Algebra.{u} S)
    {Γ Δ : Ctx S} (σ : Environment S A.substitution.Carrier Γ Δ) :
    ContextObject.ofList A.substitution.toClone Δ ⟶
      ContextObject.ofList A.substitution.toClone Γ :=
  fun i => σ _ (varOfIdx Γ i)

/-- The clone's positional weakening is the typed substitution algebra's
weakening for any semantic value. -/
theorem weakenOperation_eq (A : BindingCloneAlgebra.Algebra.{u} S)
    {Γ : Ctx S} {fresh result : S.Srt}
    (term : A.substitution.Carrier Γ result) :
    weakenOperation A.substitution.toClone (input := fresh) term =
      A.substitution.weaken term := by
  change A.substitution.substitute
      (fromPositions Γ (fun i =>
        A.substitution.injectVar (varOfIdx (fresh :: Γ) i.succ))) term =
    A.substitution.substitute
      (fun _ v => A.substitution.injectVar (.succ v)) term
  congr 1
  funext sort v
  exact fromPositions_ofEnvironment
    (fun _ w => A.substitution.injectVar (.succ w)) v

/-- The right product projection weakens precisely the ambient variable
past the whole ordered binder context. -/
theorem rightProjection_as_var (A : BindingCloneAlgebra.Algebra.{u} S) :
    ∀ (scope Γ : Ctx S) (i : Fin Γ.length),
      rightProjectionEnvironment A.substitution.toClone scope Γ i =
        A.substitution.injectVar
          (weakenVar scope (varOfIdx Γ i))
  | [], _, _ => rfl
  | fresh :: scope, Γ, i => by
      change weakenOperation A.substitution.toClone (input := fresh)
          (rightProjectionEnvironment A.substitution.toClone scope Γ i) =
        A.substitution.injectVar
          (.succ (weakenVar scope (varOfIdx Γ i)))
      have hweaken := weakenOperation_eq A (fresh := fresh)
        (rightProjectionEnvironment A.substitution.toClone scope Γ i)
      rw [hweaken]
      have ih := rightProjection_as_var A scope Γ i
      rw [ih]
      exact A.substitution.substitute_var _ _

/-- The left product projection is precisely injection of a binder-local
variable into the combined context. -/
theorem leftProjection_as_var (A : BindingCloneAlgebra.Algebra.{u} S) :
    ∀ (scope Γ : Ctx S) (i : Fin scope.length),
      leftProjectionEnvironment A.substitution.toClone scope Γ i =
        A.substitution.injectVar
          (injPrefix (Γ := Γ) scope (varOfIdx scope i))
  | [], _, i => Fin.elim0 i
  | fresh :: scope, Γ, i => by
      refine Fin.cases ?_ (fun later => ?_) i
      · rfl
      · change weakenOperation A.substitution.toClone (input := fresh)
            (leftProjectionEnvironment A.substitution.toClone scope Γ later) =
          A.substitution.injectVar
            (.succ (injPrefix scope (varOfIdx scope later)))
        have hweaken := weakenOperation_eq A (fresh := fresh)
          (leftProjectionEnvironment A.substitution.toClone scope Γ later)
        rw [hweaken]
        have ih := leftProjection_as_var A scope Γ later
        rw [ih]
        exact A.substitution.substitute_var _ _

/-- Lifting preserves every locally bound variable as that same projection. -/
theorem liftEnvironment_injPrefix (A : BindingCloneAlgebra.Algebra.{u} S)
    {Γ Δ : Ctx S} (σ : Environment S A.substitution.Carrier Γ Δ) :
    ∀ (scope : Ctx S) {s : S.Srt} (v : Var scope s),
      A.substitution.liftEnvironment σ scope s
        (injPrefix (Γ := Γ) scope v) =
      A.substitution.injectVar (injPrefix (Γ := Δ) scope v)
  | [], _, v => nomatch v
  | _ :: _, _, .zero => rfl
  | fresh :: scope, s, .succ v => by
      change A.substitution.weaken (fresh := fresh)
          (A.substitution.liftEnvironment σ scope s
            (injPrefix (Γ := Γ) scope v)) =
        A.substitution.injectVar (.succ (injPrefix scope v))
      rw [liftEnvironment_injPrefix A σ scope v]
      exact A.substitution.substitute_var _ _

/-- Product-context extension is exactly the original capture-avoiding
environment lift, for every ordered list of binders. -/
theorem extendScope_environment (A : BindingCloneAlgebra.Algebra.{u} S)
    (scope : Ctx S) {Γ Δ : Ctx S}
    (σ : Environment S A.substitution.Carrier Γ Δ) :
    extendScope A scope (environmentArrow A σ) =
      environmentArrow A (A.substitution.liftEnvironment σ scope) := by
  let C := A.substitution.toClone
  let X := ContextObject.ofList C scope
  let Y := ContextObject.ofList C Δ
  let Z := ContextObject.ofList C Γ
  let lifted := environmentArrow A (A.substitution.liftEnvironment σ scope)
  symm
  change lifted = pair C (fstProjection C X Y)
    (sndProjection C X Y ≫ environmentArrow A σ)
  apply categorical_pair_unique C
    (fstProjection C X Y)
    (sndProjection C X Y ≫ environmentArrow A σ)
  all_goals dsimp only [X, Y, Z, C, lifted]
  · funext i
    change Fin scope.length at i
    change C.substitute
        (leftProjectionEnvironment C scope Γ i)
        (environmentArrow A (A.substitution.liftEnvironment σ scope)) =
      leftProjectionEnvironment C scope Δ i
    rw [leftProjection_as_var A scope Γ i,
      leftProjection_as_var A scope Δ i]
    change A.substitution.substitute
        (fromPositions (scope ++ Γ)
          (environmentArrow A (A.substitution.liftEnvironment σ scope)))
        (A.substitution.injectVar (injPrefix scope (varOfIdx scope i))) = _
    rw [A.substitution.substitute_var]
    exact (fromPositions_ofEnvironment
      (A.substitution.liftEnvironment σ scope)
      (injPrefix scope (varOfIdx scope i))).trans
        (liftEnvironment_injPrefix A σ scope (varOfIdx scope i))
  · funext i
    change Fin Γ.length at i
    change C.substitute
        (rightProjectionEnvironment C scope Γ i)
        (environmentArrow A (A.substitution.liftEnvironment σ scope)) =
      C.substitute (environmentArrow A σ i)
        (rightProjectionEnvironment C scope Δ)
    rw [rightProjection_as_var A scope Γ i]
    change A.substitution.substitute
        (fromPositions (scope ++ Γ)
          (environmentArrow A (A.substitution.liftEnvironment σ scope)))
        (A.substitution.injectVar
          (weakenVar scope (varOfIdx Γ i))) = _
    rw [A.substitution.substitute_var]
    have hRead := fromPositions_ofEnvironment
      (A.substitution.liftEnvironment σ scope)
      (weakenVar scope (varOfIdx Γ i))
    have hRest :
        A.substitution.liftEnvironment σ scope _
          (weakenVar scope (varOfIdx Γ i)) =
        C.substitute (environmentArrow A σ i)
          (rightProjectionEnvironment C scope Δ) := by
      rw [liftEnvironment_weakenVar A.substitution σ scope (varOfIdx Γ i)]
      have hProj : rightProjectionEnvironment A.substitution.toClone scope Δ =
        (fun j => A.substitution.injectVar
          (weakenVar scope (varOfIdx Δ j))) := by
        funext j
        exact rightProjection_as_var A scope Δ j
      rw [hProj]
      change A.substitution.substitute
          (fun _ v => A.substitution.injectVar (weakenVar scope v))
          (σ _ (varOfIdx Γ i)) =
        A.substitution.substitute
          (fromPositions Δ (fun j => A.substitution.injectVar
            (weakenVar scope (varOfIdx Δ j))))
          (σ _ (varOfIdx Γ i))
      congr 1
      funext sort var
      exact (fromPositions_ofEnvironment
        (fun _ v => A.substitution.injectVar (weakenVar scope v)) var).symm
    exact hRead.trans hRest

/-- Reindexing a contextual body by the categorical binder extension is
exactly the authored substitution lifted beneath its binder list. -/
theorem scopedBodies_substitute (A : BindingCloneAlgebra.Algebra.{u} S)
    (scope : Ctx S) {Γ Δ : Ctx S}
    (σ : Environment S A.substitution.Carrier Γ Δ)
    (result : S.Srt)
    (body : A.substitution.Carrier (scope ++ Γ) result) :
    ((scopedBodies A scope result).map
      (Quiver.Hom.op (environmentArrow A σ))) body =
      A.substitution.substitute
        (A.substitution.liftEnvironment σ scope) body := by
  change A.substitution.toClone.substitute body
      (extendScope A scope (environmentArrow A σ)) = _
  rw [extendScope_environment]
  change A.substitution.substitute
      (fromPositions (scope ++ Γ)
        (environmentArrow A (A.substitution.liftEnvironment σ scope)))
      body = _
  congr 1
  funext sort var
  exact fromPositions_ofEnvironment
    (A.substitution.liftEnvironment σ scope) var

/-- Reading the categorical context extension back as an environment gives
exactly the authored binder-preserving environment lift. -/
theorem fromPositions_extendScope (A : BindingCloneAlgebra.Algebra.{u} S)
    (scope : Ctx S) {Γ Δ : Ctx S}
    (f : ContextObject.ofList A.substitution.toClone Δ ⟶
      ContextObject.ofList A.substitution.toClone Γ) :
    fromPositions (scope ++ Γ) (extendScope A scope f) =
      A.substitution.liftEnvironment (fromPositions Γ f) scope := by
  have recovered :
      environmentArrow A (fromPositions Γ f) = f := by
    funext index
    exact fromPositions_varOfIdx Γ f index
  have h1 : fromPositions (scope ++ Γ) (extendScope A scope f) =
      fromPositions (scope ++ Γ)
        (extendScope A scope
          (environmentArrow A (fromPositions Γ f))) := by
    rw [recovered]
    rfl
  have h2 : fromPositions (scope ++ Γ)
        (extendScope A scope
          (environmentArrow A (fromPositions Γ f))) =
      fromPositions (scope ++ Γ)
        (environmentArrow A
          (A.substitution.liftEnvironment (fromPositions Γ f) scope)) := by
    rw [extendScope_environment]
    rfl
  have h3 : fromPositions (scope ++ Γ)
        (environmentArrow A
          (A.substitution.liftEnvironment (fromPositions Γ f) scope)) =
      A.substitution.liftEnvironment (fromPositions Γ f) scope := by
    funext sort var
    exact fromPositions_ofEnvironment
      (A.substitution.liftEnvironment (fromPositions Γ f) scope) var
  exact h1.trans (h2.trans h3)

#print axioms extendScope_environment
#print axioms scopedBodies_substitute
#print axioms fromPositions_extendScope

end Mettapedia.OSLF.Binding.MultiBinderPresheaf
