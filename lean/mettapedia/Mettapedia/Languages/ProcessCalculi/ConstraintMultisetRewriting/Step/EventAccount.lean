import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EventCategory
import Mathlib.CategoryTheory.SingleObj

/-! # Monoid accounts are interpretations of the free event category

The existing ordered run account is the unique categorical extension of its
event grades. The opposite monoid compensates for Mathlib's convention that
composition in a one-object category multiplies in reverse order. No
commutativity assumption is introduced.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

open CategoryTheory

universe uO uT uH uOcc uS uF uM uN

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF}

namespace Step

variable (P : Step X O State Firing) {M : Type uM} [Monoid M]
  (grade : (s : State) → Firing s → M)

def accountGenerators : EffectCore.EventObject P.effectCore P.eventAdmission ⥤q SingleObj Mᵐᵒᵖ where
  obj _ := SingleObj.star _
  map {s _} event := MulOpposite.op (grade s event.firing)

def accountFunctor : EffectCore.RunCategory P.effectCore P.eventAdmission ⥤ SingleObj Mᵐᵒᵖ :=
  P.effectCore.interpret P.eventAdmission (P.accountGenerators grade)

theorem account_interpretation_exists_unique :
    ∃! interpretation : EffectCore.RunCategory P.effectCore P.eventAdmission ⥤ SingleObj Mᵐᵒᵖ,
      Paths.of (EffectCore.EventObject P.effectCore P.eventAdmission) ⋙q interpretation.toPrefunctor =
        P.accountGenerators grade :=
  P.effectCore.interpretation_exists_unique P.eventAdmission (P.accountGenerators grade)

def pathAccount {s t : EffectCore.EventObject P.effectCore P.eventAdmission}
    (path : Quiver.Path s t) : M :=
  MulOpposite.unop ((P.accountFunctor grade).map path)

theorem pathAccount_nil (s : EffectCore.EventObject P.effectCore P.eventAdmission) :
    P.pathAccount grade (Quiver.Path.nil (a := s)) = 1 := rfl

theorem pathAccount_cons {s t u : EffectCore.EventObject P.effectCore P.eventAdmission}
    (path : Quiver.Path s t) (event : P.effectCore.Event P.eventAdmission t u) :
    P.pathAccount grade (path.cons event) = P.pathAccount grade path * grade t event.firing := rfl

theorem pathAccount_comp {s t u : EffectCore.EventObject P.effectCore P.eventAdmission}
    (first : Quiver.Path s t) (second : Quiver.Path t u) :
    P.pathAccount grade (first.comp second) = P.pathAccount grade first * P.pathAccount grade second := by
  induction second with
  | nil => simp [pathAccount_nil]
  | cons rest event earlier =>
      rw [Quiver.Path.comp_cons, pathAccount_cons, earlier, pathAccount_cons, mul_assoc]

/-- The existing recursively computed account is recovered without changing
the order of the actual firings. -/
theorem Run.account_eq_pathAccount : ∀ {s : State} (run : P.Run s),
    run.account grade = P.pathAccount grade (run.eventPath P)
  | _, .nil _ => rfl
  | _, .cons firing admitted rest => by
      rw [Run.account, Run.eventPath, pathAccount_comp, pathAccount_cons, pathAccount_nil,
        one_mul, ← Run.account_eq_pathAccount]
      rfl

theorem endpoint_account {s t : State} (run : {run : P.Run s // run.last = t}) :
    P.pathAccount grade (P.endpointPath run) = run.val.account grade := by
  rcases run with ⟨run, ends⟩
  cases ends
  exact (Run.account_eq_pathAccount P grade run).symm

/-- Mapping grades by a monoid homomorphism commutes with interpreting runs. -/
theorem pathAccount_regrade {N : Type uN} [Monoid N] (map : M →* N)
    {s t : EffectCore.EventObject P.effectCore P.eventAdmission} (path : Quiver.Path s t) :
    P.pathAccount (fun state firing => map (grade state firing)) path = map (P.pathAccount grade path) := by
  induction path with
  | nil => exact map.map_one.symm
  | cons rest event earlier =>
      rw [pathAccount_cons, pathAccount_cons, earlier, map.map_mul]

#print axioms account_interpretation_exists_unique
#print axioms Run.account_eq_pathAccount
#print axioms pathAccount_regrade

end Step

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
