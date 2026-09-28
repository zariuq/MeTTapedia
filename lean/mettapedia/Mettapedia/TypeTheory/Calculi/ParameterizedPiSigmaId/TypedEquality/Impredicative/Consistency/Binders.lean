import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Consistency.TruthLaws

/-!
# Reading abstractions under substitutions

A code built from quantifiers is read by opening its abstractions one at a time:
at a generic carrier the body is read at a fresh generic, and at a data carrier
it is read at every term related to itself, in every world reached by a
morphism. When the code is a term under a substitution, the opened body is again
a term under a substitution:

* at a generic carrier, under the lifted substitution;
* at a data carrier, under the substitution renamed into the new world and
  extended by the representative.

So the meaning of a code with nested quantifiers is computed from the meanings
of the terms its substitution assigns to the free variables.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Consistency

open Normalization

variable {Head : Type}

/-! ## Opening a binder -/

/-- Opening the newest binder at the newest variable, after weakening below it,
is the identity. -/
theorem inst0_var_zero_rename_liftRen_wk {n : Nat} (t : Tm Head (n + 1)) :
    inst0 (.var 0) (Presentation.rename (liftRen wk) t) = t := by
  unfold inst0
  rw [subst_rename]
  refine (subst_ext (fun i => ?_) t).trans (subst_ids t)
  exact Fin.cases rfl (fun _ => rfl) i

/-- Opening a renamed body under a lifted substitution at a term is the
substitution renamed and extended by that term. -/
theorem inst0_rename_liftRen_subst_liftSub {n m k : Nat} (σ : Sub Head n m) (ρ : Ren m k)
    (s : Tm Head k) (body : Tm Head (n + 1)) :
    inst0 s (Presentation.rename (liftRen ρ) (subst (liftSub σ) body)) =
      subst (consSub s fun i => Presentation.rename ρ (σ i)) body := by
  unfold inst0
  rw [rename_subst, subst_comp]
  refine subst_ext (fun i => ?_) body
  refine Fin.cases rfl (fun j => ?_) i
  show subst (subst0 s) (Presentation.rename (liftRen ρ) (Presentation.rename wk (σ j))) =
    Presentation.rename ρ (σ j)
  rw [rename_liftRen_wk]
  exact inst0_rename_wk s _

/-! ## Reading abstractions -/

variable {S : Reading Head}

/-- An abstraction under a substitution, read at a function on a data carrier:
its body under the substitution renamed and extended by each representative. -/
theorem Read.lam_data {n m : Nat} {ξ : World S m} {σ : Sub Head n m}
    {body : Tm Head (n + 1)} {A : Carrier .data} {B : Carrier .gen} {φ : A.V S → B.V S}
    (read : ∀ {k : Nat} {ξ' : World S k} {ρ : Ren m k}, Morph ξ ξ' ρ →
      ∀ {s : Tm Head k} (related : DataEq S.toDataSetting A s s),
        Read S ξ' (subst (consSub s fun i => Presentation.rename ρ (σ i)) body) B
          (φ (dataValue S.toDataSetting A s related))) :
    Read S ξ (subst σ (.lam body)) (.arr A B) φ :=
  .dataArg fun {_ _ _} morph {_} related => Read.expand (.single (WhStep.beta _ _)) (by
    rw [inst0_rename_liftRen_subst_liftSub]
    exact read morph related)

/-- An abstraction under a substitution, read at a function on a generic
carrier: its body under the lifted substitution, at a fresh generic of each
meaning. -/
theorem Read.lam_gen {n m : Nat} {ξ : World S m} {σ : Sub Head n m}
    {body : Tm Head (n + 1)} {A B : Carrier .gen} {φ : A.V S → B.V S}
    (read : ∀ v : A.V S, Read S (ξ.snoc ⟨A, v⟩) (subst (liftSub σ) body) B (φ v)) :
    Read S ξ (subst σ (.lam body)) (.arr A B) φ :=
  .genericArg fun v => Read.expand (.single (WhStep.beta _ _)) (by
    rw [inst0_var_zero_rename_liftRen_wk]
    exact read v)

end Consistency
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
