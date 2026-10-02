import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedProgramPartialMeaning

/-!
# Composition of retained-binder ordinary substitution

Filling an ambient environment beneath local binders and then supplying the
binder arguments is the same as supplying their ordered joined environment.
The proof uses the existing semantic clone laws, independently of syntax.
-/

set_option autoImplicit false
noncomputable section
namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedPresheaf
open BindingSubstitutionAlgebra
universe u
variable {S : Signature} (A : BindingCloneAlgebra.Algebra.{u} S)

/-- Weakening respects the ordinary context index transport. -/
theorem weaken_contextCast {Γ Δ : Ctx S} (same : Γ = Δ)
    {s fresh : S.Srt} (x : A.substitution.Carrier Γ s) :
    (congrArg (List.cons fresh) same) ▸ A.substitution.weaken x =
      A.substitution.weaken (same ▸ x) := by
  cases same
  rfl

/-- Transport leaves a new leading projection unchanged. -/
theorem injectZero_contextCast {Γ Δ : Ctx S} (same : Γ = Δ) (fresh : S.Srt) :
    (congrArg (List.cons fresh) same) ▸
      A.substitution.injectVar (Var.zero : Var (fresh :: Γ) fresh) =
    A.substitution.injectVar (Var.zero : Var (fresh :: Δ) fresh) := by
  cases same
  rfl

/-- The retained binder's newest variable remains its projection. -/
theorem liftClosedEnvironment_zero {Γ : Ctx S}
    (environment : Environment S A.substitution.Carrier Γ [])
    (bs : Ctx S) (fresh : S.Srt) :
    liftClosedEnvironment A environment (fresh :: bs) fresh Var.zero =
      A.substitution.injectVar Var.zero := by
  change (congrArg (List.cons fresh) (List.append_nil bs)) ▸
    A.substitution.injectVar (Var.zero : Var (fresh :: (bs ++ [])) fresh) = _
  exact injectZero_contextCast A (List.append_nil bs) fresh

/-- Older retained-binder values are weakened across the newest binder. -/
theorem liftClosedEnvironment_succ {Γ : Ctx S}
    (environment : Environment S A.substitution.Carrier Γ [])
    (bs : Ctx S) {fresh s : S.Srt} (v : Var (bs ++ Γ) s) :
    liftClosedEnvironment A environment (fresh :: bs) s (Var.succ v) =
      A.substitution.weaken (fresh := fresh) (liftClosedEnvironment A environment bs s v) :=
  weaken_contextCast A (List.append_nil bs) _

/-- A substitution through one weakening discards its newest coordinate. -/
theorem substitute_weaken {Γ Δ : Ctx S} {s fresh : S.Srt}
    (environment : Environment S A.substitution.Carrier (fresh :: Γ) Δ)
    (x : A.substitution.Carrier Γ s) :
    A.substitution.substitute environment (A.substitution.weaken x) =
      A.substitution.substitute (fun r v => environment r (.succ v)) x := by
  unfold Algebra.weaken
  rw [A.substitution.substitute_comp]
  congr 1
  funext r v
  exact A.substitution.substitute_var environment (.succ v)

/-- All endo-environments of the empty context are the clone identity. -/
theorem substitute_empty (environment : Environment S A.substitution.Carrier [] [])
    {s : S.Srt} (x : A.substitution.Carrier [] s) :
    A.substitution.substitute environment x = x := by
  have same : environment = fun _ v => A.substitution.injectVar v := by
    funext r v
    exact nomatch v
  rw [same]
  exact A.substitution.substitute_identity x

/-- Supplying retained-binder arguments to the lifted ambient environment
recovers their single ordered join. -/
theorem substitute_liftClosedEnvironment {Γ : Ctx S}
    (environment : Environment S A.substitution.Carrier Γ []) :
    ∀ (bs : Ctx S) (arguments : Environment S A.substitution.Carrier bs []),
      (fun r v => A.substitution.substitute arguments
        (liftClosedEnvironment A environment bs r v)) =
      SemanticContextualMetavariables.joinEnvironment arguments environment
  | [], arguments => by
      funext r v
      exact substitute_empty A arguments (environment r v)
  | fresh :: bs, arguments => by
      funext r v
      cases v with
      | zero =>
          rw [liftClosedEnvironment_zero, A.substitution.substitute_var]
          rfl
      | succ old =>
          rw [liftClosedEnvironment_succ, substitute_weaken]
          exact congrFun (congrFun (substitute_liftClosedEnvironment environment bs
            (fun r v => arguments r (.succ v))) r) old

/-- The common binder composition law for every binding-clone model. -/
theorem partialSubstitute_then_apply {Γ : Ctx S} (bs : Ctx S)
    (environment : Environment S A.substitution.Carrier Γ [])
    (arguments : Environment S A.substitution.Carrier bs [])
    {s : S.Srt} (body : A.substitution.Carrier (bs ++ Γ) s) :
    A.substitution.substitute arguments (partialSubstitute A bs environment body) =
      A.substitution.substitute
        (SemanticContextualMetavariables.joinEnvironment arguments environment) body := by
  unfold partialSubstitute
  rw [A.substitution.substitute_comp, substitute_liftClosedEnvironment]

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedPresheaf
end
