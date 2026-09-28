import Mettapedia.OSLF.Syntax.IntrinsicScopedConditionalPolynomial

/-!
# Contextual substitution acts on scoped conditional rule occurrences

A substitution of the ambient context acts on one occurrence of an intrinsic
scoped conditional rule: every contextual metavariable value is substituted
beneath its own declared dependencies, and the closing environment is
post-composed. The conclusion of the substituted occurrence is the
substituted conclusion. Each premise child of the substituted occurrence is
the original child substituted beneath exactly that premise's binders.

Both facts rest on two laws of the schema interpretation: substituting an
interpreted schema substitutes its ambient and ordinary environments, and an
environment on the ambient block of the valuation can be moved into the
valuation itself.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicScopedConditionalSubstitution

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.BindingSubstitutionAlgebra
open Mettapedia.OSLF.Binding.FreeBindingTerms
open Mettapedia.OSLF.Binding.BindingEquationalModels
open Mettapedia.OSLF.Binding.SemanticContextualMetavariables
open Mettapedia.OSLF.Binding.SemanticScopedPremiseInterpretation
open Mettapedia.OSLF.Binding.BinderLocalPremise
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment)
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPolynomial

universe u

variable {S : Signature} {M : List (MetaArity S)}

/-! ## Environment laws of a substitution algebra -/

section EnvironmentLaws

variable (A : BindingSubstitutionAlgebra.Algebra.{u} S)

/-- Lifting the identity environment beneath binders is the identity. -/
theorem liftEnvironment_injectVar {Γ : Ctx S} :
    ∀ (binders : Ctx S),
      A.liftEnvironment (fun _ v => A.injectVar v : Environment S A.Carrier Γ Γ)
          binders =
        (fun _ v => A.injectVar v :
          Environment S A.Carrier (binders ++ Γ) (binders ++ Γ))
  | [] => rfl
  | fresh :: binders => by
      funext s x
      cases x with
      | zero => rfl
      | succ old =>
          change A.weaken (fresh := fresh)
              (A.liftEnvironment (fun _ v => A.injectVar v) binders s old) =
            A.injectVar (Var.succ old)
          rw [liftEnvironment_injectVar binders]
          exact A.substitute_var _ old

/-- A lifted environment sends a weakened variable to the weakened value. -/
theorem liftEnvironment_weakenVar {Γ Δ : Ctx S}
    (σ : Environment S A.Carrier Γ Δ) :
    ∀ (binders : Ctx S) {s : S.Srt} (x : Var Γ s),
      A.liftEnvironment σ binders s (weakenVar binders x) =
        A.substitute (fun _ v => A.injectVar (weakenVar binders v)) (σ s x)
  | [], _, x => (A.substitute_identity (σ _ x)).symm
  | fresh :: binders, s, x => by
      change A.weaken (fresh := fresh)
          (A.liftEnvironment σ binders s (weakenVar binders x)) =
        A.substitute (fun _ v => A.injectVar (weakenVar (fresh :: binders) v))
          (σ s x)
      rw [liftEnvironment_weakenVar σ binders x]
      unfold BindingSubstitutionAlgebra.Algebra.weaken
      rw [A.substitute_comp]
      congr 1
      funext t v
      exact A.substitute_var _ (weakenVar binders v)

/-- Substitution along a lifted environment composes lifted environments. -/
theorem substitute_liftEnvironment {Γ Δ Θ : Ctx S}
    (σ : Environment S A.Carrier Δ Θ) (env : Environment S A.Carrier Γ Δ) :
    ∀ (binders : Ctx S) {s : S.Srt} (x : Var (binders ++ Γ) s),
      A.substitute (A.liftEnvironment σ binders)
          (A.liftEnvironment env binders s x) =
        A.liftEnvironment (fun t v => A.substitute σ (env t v)) binders s x
  | [], _, _ => rfl
  | _ :: _, _, .zero => A.substitute_var _ _
  | fresh :: binders, s, .succ old => by
      change A.substitute (A.liftEnvironment σ (fresh :: binders))
          (A.substitute (fun _ v => A.injectVar (Var.succ v))
            (A.liftEnvironment env binders s old)) =
        A.substitute (fun _ v => A.injectVar (Var.succ v))
          (A.liftEnvironment (fun t v => A.substitute σ (env t v)) binders s old)
      rw [← substitute_liftEnvironment σ env binders old, A.substitute_comp,
        A.substitute_comp]
      congr 1
      funext t v
      exact A.substitute_var _ (Var.succ v)

/-- Substitution distributes over a joined dependency/ambient environment. -/
theorem substitute_joinEnvironment {Γ Δ Θ : Ctx S}
    (ρ : Environment S A.Carrier Δ Θ) :
    ∀ (dependencies : Ctx S)
      (arguments : Environment S A.Carrier dependencies Δ)
      (ambient : Environment S A.Carrier Γ Δ) {s : S.Srt}
      (x : Var (dependencies ++ Γ) s),
      A.substitute ρ (joinEnvironment arguments ambient s x) =
        joinEnvironment (fun t v => A.substitute ρ (arguments t v))
          (fun t v => A.substitute ρ (ambient t v)) s x
  | [], _, _, _, _ => rfl
  | _ :: _, _, _, _, .zero => rfl
  | _ :: dependencies, arguments, ambient, _, .succ old =>
      substitute_joinEnvironment ρ dependencies
        (fun t v => arguments t (.succ v)) ambient old

/-- A joined environment evaluated on a lifted ambient environment moves the
ambient environment into the join. -/
theorem substitute_join_liftEnvironment {Γ Δ Θ : Ctx S}
    (ρ : Environment S A.Carrier Δ Θ)
    (ambient : Environment S A.Carrier Γ Δ) :
    ∀ (dependencies : Ctx S)
      (arguments : Environment S A.Carrier dependencies Θ)
      {s : S.Srt} (x : Var (dependencies ++ Γ) s),
      A.substitute (joinEnvironment arguments ρ)
          (A.liftEnvironment ambient dependencies s x) =
        joinEnvironment arguments
          (fun t v => A.substitute ρ (ambient t v)) s x
  | [], _, _, _ => rfl
  | _ :: _, _, _, .zero => A.substitute_var _ _
  | _ :: dependencies, arguments, s, .succ old => by
      change A.substitute (joinEnvironment arguments ρ)
          (A.substitute (fun _ v => A.injectVar (Var.succ v))
            (A.liftEnvironment ambient dependencies s old)) =
        joinEnvironment (fun t v => arguments t (.succ v))
          (fun t v => A.substitute ρ (ambient t v)) s old
      rw [A.substitute_comp,
        ← substitute_join_liftEnvironment ρ ambient dependencies
          (fun t v => arguments t (.succ v)) old]
      congr 1
      funext t v
      exact A.substitute_var _ (Var.succ v)

end EnvironmentLaws

/-! ## Laws of contextual metavariable application -/

/-- Substituting an applied metavariable body substitutes both supplied
environments. -/
theorem substitute_apply (A : BindingCloneAlgebra.Algebra.{u} S)
    {dependencies Γ Δ Θ : Ctx S} {sort : S.Srt}
    (body : A.substitution.Carrier (dependencies ++ Γ) sort)
    (arguments : Environment S A.substitution.Carrier dependencies Δ)
    (ambient : Environment S A.substitution.Carrier Γ Δ)
    (σ : Environment S A.substitution.Carrier Δ Θ) :
    A.substitution.substitute σ (apply A body arguments ambient) =
      apply A body (fun t v => A.substitution.substitute σ (arguments t v))
        (fun t v => A.substitution.substitute σ (ambient t v)) := by
  unfold apply
  rw [A.substitution.substitute_comp]
  congr 1
  funext t v
  exact substitute_joinEnvironment A.substitution σ dependencies
    arguments ambient v

/-- An environment applied after the ambient block can instead be applied to
the metavariable body beneath its dependencies. -/
theorem apply_postAmbient (A : BindingCloneAlgebra.Algebra.{u} S)
    {dependencies Γ Δ Θ : Ctx S} {sort : S.Srt}
    (body : A.substitution.Carrier (dependencies ++ Γ) sort)
    (arguments : Environment S A.substitution.Carrier dependencies Θ)
    (ρ : Environment S A.substitution.Carrier Δ Θ)
    (ambient : Environment S A.substitution.Carrier Γ Δ) :
    apply A body arguments
        (fun t v => A.substitution.substitute ρ (ambient t v)) =
      apply A
        (A.substitution.substitute
          (A.substitution.liftEnvironment ambient dependencies) body)
        arguments ρ := by
  unfold apply
  rw [A.substitution.substitute_comp]
  congr 1
  funext t v
  exact (substitute_join_liftEnvironment A.substitution ρ ambient
    dependencies arguments v).symm

/-! ## Substitution laws of the schema interpretation -/

/-- Substitute the ambient block of every contextual metavariable value. -/
def substValuation (A : BindingCloneAlgebra.Algebra.{u} S) {Γ Δ : Ctx S}
    (σ : Environment S A.substitution.Carrier Γ Δ)
    (body : Valuation (M := M) A Γ) : Valuation (M := M) A Δ :=
  fun k => A.substitution.substitute
    (A.substitution.liftEnvironment σ (M.get k).1) (body k)

/-- Substitution beneath binders commutes with weakening the ambient
environment past those binders. -/
theorem substitute_weakenEnvironment (A : BindingCloneAlgebra.Algebra.{u} S)
    (binders : Ctx S) {Γ Δ Θ : Ctx S}
    (σ : Environment S A.substitution.Carrier Δ Θ)
    (ambient : Environment S A.substitution.Carrier Γ Δ) :
    (fun t v => A.substitution.substitute
      (A.substitution.liftEnvironment σ binders)
      (weakenEnvironment A binders ambient t v)) =
      weakenEnvironment A binders
        (fun t v => A.substitution.substitute σ (ambient t v)) := by
  funext t v
  unfold weakenEnvironment
  rw [A.substitution.substitute_comp, A.substitution.substitute_comp]
  congr 1
  funext r w
  rw [A.substitution.substitute_var]
  exact liftEnvironment_weakenVar A.substitution σ binders w

/-- Weakening a post-composed environment post-composes the weakened one. -/
theorem weakenEnvironment_postAmbient (A : BindingCloneAlgebra.Algebra.{u} S)
    (binders : Ctx S) {Γ Δ Θ : Ctx S}
    (ρ : Environment S A.substitution.Carrier Δ Θ)
    (ambient : Environment S A.substitution.Carrier Γ Δ) :
    weakenEnvironment A binders
        (fun t v => A.substitution.substitute ρ (ambient t v)) =
      (fun t v => A.substitution.substitute
        (weakenEnvironment A binders ρ) (ambient t v)) := by
  funext t v
  unfold weakenEnvironment
  rw [A.substitution.substitute_comp]

mutual

/-- Substituting an interpreted schema substitutes its ambient and ordinary
environments. -/
theorem substitute_interpretSchema (A : BindingCloneAlgebra.Algebra.{u} S)
    {Γ Ξ Δ Θ : Ctx S}
    (σ : Environment S A.substitution.Carrier Δ Θ)
    (body : Valuation (M := M) A Γ)
    (ambient : Environment S A.substitution.Carrier Γ Δ)
    (ordinary : Environment S A.substitution.Carrier Ξ Δ) :
    ∀ {sort : S.Srt} (term : Term (withMetas S M) Ξ sort),
      A.substitution.substitute σ (interpretSchema A body ambient ordinary term) =
        interpretSchema A body
          (fun t v => A.substitution.substitute σ (ambient t v))
          (fun t v => A.substitution.substitute σ (ordinary t v)) term
  | _, .var _ => rfl
  | _, .op (Sum.inl op) args => by
      change A.substitution.substitute σ
          (A.operation op (interpretArgs A body ambient ordinary args)) =
        A.operation op (interpretArgs A body
          (fun t v => A.substitution.substitute σ (ambient t v))
          (fun t v => A.substitution.substitute σ (ordinary t v)) args)
      rw [A.operation_substitute]
      exact congrArg (A.operation op)
        (substituteArgs_interpretArgs A σ body ambient ordinary args)
  | _, .op (Sum.inr (.mk k)) args => by
      change A.substitution.substitute σ
          (apply A (body k)
            (argsEnvironment A (interpretArgs A body ambient ordinary args))
            ambient) =
        apply A (body k)
          (argsEnvironment A (interpretArgs A body
            (fun t v => A.substitution.substitute σ (ambient t v))
            (fun t v => A.substitution.substitute σ (ordinary t v)) args))
          (fun t v => A.substitution.substitute σ (ambient t v))
      rw [substitute_apply,
        ← substituteArgs_interpretArgs A σ body ambient ordinary args]
      congr 1
      funext t v
      exact (argsEnvironment_substituteArgs A σ _ t v).symm
termination_by _ term => 2 * termSize term
decreasing_by
  all_goals simp only [termSize]
  all_goals omega

/-- The argument-vector form, with each argument substituted beneath its own
binders. -/
theorem substituteArgs_interpretArgs (A : BindingCloneAlgebra.Algebra.{u} S)
    {Γ Ξ Δ Θ : Ctx S}
    (σ : Environment S A.substitution.Carrier Δ Θ)
    (body : Valuation (M := M) A Γ)
    (ambient : Environment S A.substitution.Carrier Γ Δ)
    (ordinary : Environment S A.substitution.Carrier Ξ Δ) :
    ∀ {arity : List (List S.Srt × S.Srt)}
      (args : Args (withMetas S M) arity Ξ),
      A.substitution.substituteArgs σ
          (interpretArgs A body ambient ordinary args) =
        interpretArgs A body
          (fun t v => A.substitution.substitute σ (ambient t v))
          (fun t v => A.substitution.substitute σ (ordinary t v)) args
  | _, .nil => rfl
  | _, .cons (bs := binders) head tail => by
      change FamilyArgs.cons
          (A.substitution.substitute (A.substitution.liftEnvironment σ binders)
            (interpretSchema A body (weakenEnvironment A binders ambient)
              (A.substitution.liftEnvironment ordinary binders) head))
          (A.substitution.substituteArgs σ
            (interpretArgs A body ambient ordinary tail)) =
        FamilyArgs.cons
          (interpretSchema A body
            (weakenEnvironment A binders
              (fun t v => A.substitution.substitute σ (ambient t v)))
            (A.substitution.liftEnvironment
              (fun t v => A.substitution.substitute σ (ordinary t v)) binders)
            head)
          (interpretArgs A body
            (fun t v => A.substitution.substitute σ (ambient t v))
            (fun t v => A.substitution.substitute σ (ordinary t v)) tail)
      have ordinaryEq :
          (fun t v => A.substitution.substitute
            (A.substitution.liftEnvironment σ binders)
            (A.substitution.liftEnvironment ordinary binders t v)) =
          A.substitution.liftEnvironment
            (fun t v => A.substitution.substitute σ (ordinary t v)) binders := by
        funext t v
        exact substitute_liftEnvironment A.substitution σ ordinary binders v
      rw [substitute_interpretSchema A (A.substitution.liftEnvironment σ binders)
          body (weakenEnvironment A binders ambient)
          (A.substitution.liftEnvironment ordinary binders) head,
        substitute_weakenEnvironment A binders σ ambient, ordinaryEq,
        substituteArgs_interpretArgs A σ body ambient ordinary tail]
termination_by _ args => 2 * argsSize args + 1
decreasing_by
  all_goals simp only [argsSize]
  all_goals first | omega | have := termSize_pos head; omega

end

mutual

/-- An environment post-composed onto the ambient block may instead be
applied inside every metavariable value. -/
theorem interpretSchema_postAmbient (A : BindingCloneAlgebra.Algebra.{u} S)
    {Γ Ξ Δ Θ : Ctx S}
    (ρ : Environment S A.substitution.Carrier Δ Θ)
    (ambient : Environment S A.substitution.Carrier Γ Δ)
    (body : Valuation (M := M) A Γ)
    (ordinary : Environment S A.substitution.Carrier Ξ Θ) :
    ∀ {sort : S.Srt} (term : Term (withMetas S M) Ξ sort),
      interpretSchema A body
          (fun t v => A.substitution.substitute ρ (ambient t v)) ordinary term =
        interpretSchema A (substValuation A ambient body) ρ ordinary term
  | _, .var _ => rfl
  | _, .op (Sum.inl op) args => by
      change A.operation op (interpretArgs A body
          (fun t v => A.substitution.substitute ρ (ambient t v)) ordinary args) =
        A.operation op (interpretArgs A (substValuation A ambient body) ρ
          ordinary args)
      rw [interpretArgs_postAmbient A ρ ambient body ordinary args]
  | _, .op (Sum.inr (.mk k)) args => by
      change apply A (body k)
          (argsEnvironment A (interpretArgs A body
            (fun t v => A.substitution.substitute ρ (ambient t v)) ordinary args))
          (fun t v => A.substitution.substitute ρ (ambient t v)) =
        apply A (substValuation A ambient body k)
          (argsEnvironment A (interpretArgs A (substValuation A ambient body) ρ
            ordinary args)) ρ
      rw [interpretArgs_postAmbient A ρ ambient body ordinary args]
      exact apply_postAmbient A (body k) _ ρ ambient
termination_by _ term => 2 * termSize term
decreasing_by
  all_goals simp only [termSize]
  all_goals omega

/-- The argument-vector form of moving the ambient environment. -/
theorem interpretArgs_postAmbient (A : BindingCloneAlgebra.Algebra.{u} S)
    {Γ Ξ Δ Θ : Ctx S}
    (ρ : Environment S A.substitution.Carrier Δ Θ)
    (ambient : Environment S A.substitution.Carrier Γ Δ)
    (body : Valuation (M := M) A Γ)
    (ordinary : Environment S A.substitution.Carrier Ξ Θ) :
    ∀ {arity : List (List S.Srt × S.Srt)}
      (args : Args (withMetas S M) arity Ξ),
      interpretArgs A body
          (fun t v => A.substitution.substitute ρ (ambient t v)) ordinary args =
        interpretArgs A (substValuation A ambient body) ρ ordinary args
  | _, .nil => rfl
  | _, .cons (bs := binders) head tail => by
      change FamilyArgs.cons
          (interpretSchema A body
            (weakenEnvironment A binders
              (fun t v => A.substitution.substitute ρ (ambient t v)))
            (A.substitution.liftEnvironment ordinary binders) head)
          (interpretArgs A body
            (fun t v => A.substitution.substitute ρ (ambient t v)) ordinary tail) =
        FamilyArgs.cons
          (interpretSchema A (substValuation A ambient body)
            (weakenEnvironment A binders ρ)
            (A.substitution.liftEnvironment ordinary binders) head)
          (interpretArgs A (substValuation A ambient body) ρ ordinary tail)
      rw [weakenEnvironment_postAmbient A binders ρ ambient,
        interpretSchema_postAmbient A (weakenEnvironment A binders ρ) ambient
          body (A.substitution.liftEnvironment ordinary binders) head,
        interpretArgs_postAmbient A ρ ambient body ordinary tail]
termination_by _ args => 2 * argsSize args + 1
decreasing_by
  all_goals simp only [argsSize]
  all_goals first | omega | have := termSize_pos head; omega

end

/-! ## Substituted rule occurrences and their judgments -/

variable (R : List (Rule S M))

/-- Substitute both endpoints of a judgment along an environment out of its
context. -/
def substJudgment {A : BindingCloneAlgebra.Algebra.{u} S} (j : Judgment A)
    {Δ : Ctx S} (σ : Environment S A.substitution.Carrier j.1 Δ) :
    Judgment A :=
  ⟨Δ, j.2.1, A.substitution.substitute σ j.2.2.1,
    A.substitution.substitute σ j.2.2.2⟩

/-- A substitution of the ambient context acts on one rule occurrence. -/
def Instance.subst {A : BindingCloneAlgebra.Algebra.{u} S}
    (occurrence : Instance R A) {Δ : Ctx S}
    (σ : Environment S A.substitution.Carrier occurrence.ambient Δ) :
    Instance R A where
  index := occurrence.index
  ambient := Δ
  valuation := substValuation A σ occurrence.valuation
  close := fun t v => A.substitution.substitute σ (occurrence.close t v)

/-- One endpoint of the conclusion: substitution commutes with the
interpretation at the identity ambient environment. -/
theorem substitute_interpretSchema_identity
    (A : BindingCloneAlgebra.Algebra.{u} S) {Γ Ξ Δ : Ctx S}
    (σ : Environment S A.substitution.Carrier Γ Δ)
    (body : Valuation (M := M) A Γ)
    (ordinary : Environment S A.substitution.Carrier Ξ Γ)
    {sort : S.Srt} (term : Term (withMetas S M) Ξ sort) :
    A.substitution.substitute σ
        (interpretSchema A body (fun _ v => A.substitution.injectVar v)
          ordinary term) =
      interpretSchema A (substValuation A σ body)
        (fun _ v => A.substitution.injectVar v)
        (fun t v => A.substitution.substitute σ (ordinary t v)) term := by
  rw [substitute_interpretSchema]
  have ambientEq :
      (fun t v => A.substitution.substitute σ
        (A.substitution.injectVar v : A.substitution.Carrier Γ t)) =
      (fun t v => A.substitution.substitute
        (fun _ w => A.substitution.injectVar w) (σ t v)) := by
    funext t v
    rw [A.substitution.substitute_var, A.substitution.substitute_identity]
  rw [ambientEq]
  exact interpretSchema_postAmbient A (fun _ w => A.substitution.injectVar w)
    σ body _ term

/-- The substituted occurrence concludes the substituted judgment. -/
theorem conclusionJudgment_subst {A : BindingCloneAlgebra.Algebra.{u} S}
    (occurrence : Instance R A) {Δ : Ctx S}
    (σ : Environment S A.substitution.Carrier occurrence.ambient Δ) :
    conclusionJudgment R A (Instance.subst R occurrence σ) =
      substJudgment (conclusionJudgment R A occurrence) σ := by
  obtain ⟨index, ambient, valuation, close⟩ := occurrence
  change (⟨Δ, (R.get index).conclusion.sort,
      interpretSchema A (substValuation A σ valuation)
        (fun _ v => A.substitution.injectVar v)
        (fun t v => A.substitution.substitute σ (close t v))
        (R.get index).conclusion.lhs,
      interpretSchema A (substValuation A σ valuation)
        (fun _ v => A.substitution.injectVar v)
        (fun t v => A.substitution.substitute σ (close t v))
        (R.get index).conclusion.rhs⟩ : Judgment A) =
    ⟨Δ, (R.get index).conclusion.sort,
      A.substitution.substitute σ
        (interpretSchema A valuation (fun _ v => A.substitution.injectVar v)
          close (R.get index).conclusion.lhs),
      A.substitution.substitute σ
        (interpretSchema A valuation (fun _ v => A.substitution.injectVar v)
          close (R.get index).conclusion.rhs)⟩
  rw [substitute_interpretSchema_identity, substitute_interpretSchema_identity]

/-- One endpoint of a premise child: substitution beneath the premise's
binders commutes with its interpretation. -/
theorem substitute_interpretSchema_premise
    (A : BindingCloneAlgebra.Algebra.{u} S) {Γ Ξ Δ : Ctx S}
    (σ : Environment S A.substitution.Carrier Γ Δ)
    (body : Valuation (M := M) A Γ)
    (close : Environment S A.substitution.Carrier Ξ Γ)
    (binders : Ctx S)
    {sort : S.Srt} (term : Term (withMetas S M) (binders ++ Ξ) sort) :
    A.substitution.substitute (A.substitution.liftEnvironment σ binders)
        (interpretSchema A body
          (weakenEnvironment A binders (fun _ v => A.substitution.injectVar v))
          (A.substitution.liftEnvironment close binders) term) =
      interpretSchema A (substValuation A σ body)
        (weakenEnvironment A binders (fun _ v => A.substitution.injectVar v))
        (A.substitution.liftEnvironment
          (fun t v => A.substitution.substitute σ (close t v)) binders) term := by
  rw [substitute_interpretSchema]
  have ordinaryEq :
      (fun t v => A.substitution.substitute
        (A.substitution.liftEnvironment σ binders)
        (A.substitution.liftEnvironment close binders t v)) =
      A.substitution.liftEnvironment
        (fun t v => A.substitution.substitute σ (close t v)) binders := by
    funext t v
    exact substitute_liftEnvironment A.substitution σ close binders v
  have ambientEq :
      (fun t v => A.substitution.substitute
        (A.substitution.liftEnvironment σ binders)
        (weakenEnvironment A binders
          (fun _ w => A.substitution.injectVar w : Environment S
            A.substitution.Carrier Γ Γ) t v)) =
      (fun t v => A.substitution.substitute
        (weakenEnvironment A binders
          (fun _ w => A.substitution.injectVar w : Environment S
            A.substitution.Carrier Δ Δ)) (σ t v)) := by
    rw [substitute_weakenEnvironment A binders σ]
    funext t v
    unfold weakenEnvironment
    beta_reduce
    rw [A.substitution.substitute_var]
    congr 1
    funext r w
    exact (A.substitution.substitute_var
      (fun _ x => A.substitution.injectVar (weakenVar binders x)) w).symm
  rw [ordinaryEq, ambientEq]
  exact interpretSchema_postAmbient A
    (weakenEnvironment A binders (fun _ w => A.substitution.injectVar w))
    σ body _ term

/-- Each child of the substituted occurrence is the original child
substituted beneath exactly that premise's binders. -/
theorem childJudgment_subst {A : BindingCloneAlgebra.Algebra.{u} S}
    (occurrence : Instance R A) {Δ : Ctx S}
    (σ : Environment S A.substitution.Carrier occurrence.ambient Δ)
    (position : Fin (R.get occurrence.index).premises.length) :
    childJudgment R A (Instance.subst R occurrence σ) position =
      substJudgment (childJudgment R A occurrence position)
        (A.substitution.liftEnvironment σ
          ((R.get occurrence.index).premises.get position).binders) := by
  obtain ⟨index, ambient, valuation, close⟩ := occurrence
  change (⟨((R.get index).premises.get position).binders ++ Δ,
      ((R.get index).premises.get position).sort,
      interpretSchema A (substValuation A σ valuation)
        (weakenEnvironment A ((R.get index).premises.get position).binders
          (fun _ v => A.substitution.injectVar v))
        (A.substitution.liftEnvironment
          (fun t v => A.substitution.substitute σ (close t v))
          ((R.get index).premises.get position).binders)
        ((R.get index).premises.get position).source,
      interpretSchema A (substValuation A σ valuation)
        (weakenEnvironment A ((R.get index).premises.get position).binders
          (fun _ v => A.substitution.injectVar v))
        (A.substitution.liftEnvironment
          (fun t v => A.substitution.substitute σ (close t v))
          ((R.get index).premises.get position).binders)
        ((R.get index).premises.get position).target⟩ : Judgment A) =
    ⟨((R.get index).premises.get position).binders ++ Δ,
      ((R.get index).premises.get position).sort,
      A.substitution.substitute
        (A.substitution.liftEnvironment σ
          ((R.get index).premises.get position).binders)
        (interpretSchema A valuation
          (weakenEnvironment A ((R.get index).premises.get position).binders
            (fun _ v => A.substitution.injectVar v))
          (A.substitution.liftEnvironment close
            ((R.get index).premises.get position).binders)
          ((R.get index).premises.get position).source),
      A.substitution.substitute
        (A.substitution.liftEnvironment σ
          ((R.get index).premises.get position).binders)
        (interpretSchema A valuation
          (weakenEnvironment A ((R.get index).premises.get position).binders
            (fun _ v => A.substitution.injectVar v))
          (A.substitution.liftEnvironment close
            ((R.get index).premises.get position).binders)
          ((R.get index).premises.get position).target)⟩
  rw [substitute_interpretSchema_premise, substitute_interpretSchema_premise]


/-! ## Identity and composition of the occurrence action -/

theorem substJudgment_identity {A : BindingCloneAlgebra.Algebra.{u} S}
    (j : Judgment A) :
    substJudgment j (fun _ v => A.substitution.injectVar v) = j := by
  obtain ⟨Γ, sort, source, target⟩ := j
  change (⟨Γ, sort,
      A.substitution.substitute (fun _ v => A.substitution.injectVar v) source,
      A.substitution.substitute (fun _ v => A.substitution.injectVar v) target⟩ :
        Judgment A) = ⟨Γ, sort, source, target⟩
  rw [A.substitution.substitute_identity, A.substitution.substitute_identity]

theorem substJudgment_comp {A : BindingCloneAlgebra.Algebra.{u} S}
    (j : Judgment A) {Δ Θ : Ctx S}
    (σ : Environment S A.substitution.Carrier j.1 Δ)
    (τ : Environment S A.substitution.Carrier Δ Θ) :
    substJudgment (substJudgment j σ) τ =
      substJudgment j (fun t v => A.substitution.substitute τ (σ t v)) := by
  obtain ⟨Γ, sort, source, target⟩ := j
  change (⟨Θ, sort,
      A.substitution.substitute τ (A.substitution.substitute σ source),
      A.substitution.substitute τ (A.substitution.substitute σ target)⟩ :
        Judgment A) =
    ⟨Θ, sort,
      A.substitution.substitute
        (fun t v => A.substitution.substitute τ (σ t v)) source,
      A.substitution.substitute
        (fun t v => A.substitution.substitute τ (σ t v)) target⟩
  rw [A.substitution.substitute_comp, A.substitution.substitute_comp]

/-- The identity substitution fixes every rule occurrence. -/
theorem Instance.subst_identity {A : BindingCloneAlgebra.Algebra.{u} S}
    (occurrence : Instance R A) :
    Instance.subst R occurrence (fun _ v => A.substitution.injectVar v) =
      occurrence := by
  obtain ⟨index, ambient, valuation, close⟩ := occurrence
  have valuationEq :
      substValuation A (fun _ v => A.substitution.injectVar v) valuation =
        valuation := by
    funext k
    change A.substitution.substitute
        (A.substitution.liftEnvironment (fun _ v => A.substitution.injectVar v)
          (M.get k).1) (valuation k) = valuation k
    rw [liftEnvironment_injectVar A.substitution (M.get k).1]
    exact A.substitution.substitute_identity (valuation k)
  have closeEq :
      (fun t v => A.substitution.substitute
        (fun _ w => A.substitution.injectVar w) (close t v)) = close := by
    funext t v
    exact A.substitution.substitute_identity (close t v)
  change (⟨index, ambient,
      substValuation A (fun _ v => A.substitution.injectVar v) valuation,
      fun t v => A.substitution.substitute
        (fun _ w => A.substitution.injectVar w) (close t v)⟩ : Instance R A) =
    ⟨index, ambient, valuation, close⟩
  rw [valuationEq, closeEq]

/-- Substituting twice is substituting once along the composite. -/
theorem Instance.subst_comp {A : BindingCloneAlgebra.Algebra.{u} S}
    (occurrence : Instance R A) {Δ Θ : Ctx S}
    (σ : Environment S A.substitution.Carrier occurrence.ambient Δ)
    (τ : Environment S A.substitution.Carrier Δ Θ) :
    Instance.subst R (Instance.subst R occurrence σ) τ =
      Instance.subst R occurrence
        (fun t v => A.substitution.substitute τ (σ t v)) := by
  obtain ⟨index, ambient, valuation, close⟩ := occurrence
  have valuationEq :
      substValuation A τ (substValuation A σ valuation) =
        substValuation A (fun t v => A.substitution.substitute τ (σ t v))
          valuation := by
    funext k
    change A.substitution.substitute
        (A.substitution.liftEnvironment τ (M.get k).1)
        (A.substitution.substitute
          (A.substitution.liftEnvironment σ (M.get k).1) (valuation k)) =
      A.substitution.substitute
        (A.substitution.liftEnvironment
          (fun t v => A.substitution.substitute τ (σ t v)) (M.get k).1)
        (valuation k)
    rw [A.substitution.substitute_comp]
    congr 1
    funext t v
    exact substitute_liftEnvironment A.substitution τ σ (M.get k).1 v
  have closeEq :
      (fun t v => A.substitution.substitute τ
        (A.substitution.substitute σ (close t v))) =
      (fun t v => A.substitution.substitute
        (fun r w => A.substitution.substitute τ (σ r w)) (close t v)) := by
    funext t v
    exact A.substitution.substitute_comp σ τ (close t v)
  change (⟨index, Θ, substValuation A τ (substValuation A σ valuation),
      fun t v => A.substitution.substitute τ
        (A.substitution.substitute σ (close t v))⟩ : Instance R A) =
    ⟨index, Θ,
      substValuation A (fun t v => A.substitution.substitute τ (σ t v))
        valuation,
      fun t v => A.substitution.substitute
        (fun r w => A.substitution.substitute τ (σ r w)) (close t v)⟩
  rw [valuationEq, closeEq]

/-! ## Substitution acts on firing trees -/

/-- The free firing trees of the intrinsic conditional rules over a clone. -/
abbrev Tree (A : BindingCloneAlgebra.Algebra.{u} S) (j : Judgment A) :=
  Mettapedia.TypeTheory.IndexedPolynomial.Fix (rules R A) () j

/-- Transport an environment out of a judgment's context along an equality
of judgments. -/
def castEnv {A : BindingCloneAlgebra.Algebra.{u} S} {j₁ j₂ : Judgment A}
    (e : j₁ = j₂) {Δ : Ctx S}
    (σ : Environment S A.substitution.Carrier j₂.1 Δ) :
    Environment S A.substitution.Carrier j₁.1 Δ :=
  e ▸ σ

theorem castEnv_heq {A : BindingCloneAlgebra.Algebra.{u} S}
    {j₁ j₂ : Judgment A} (e : j₁ = j₂) {Δ : Ctx S}
    (σ : Environment S A.substitution.Carrier j₂.1 Δ) :
    HEq (castEnv e σ) σ := by
  subst e
  rfl

theorem substJudgment_castEnv {A : BindingCloneAlgebra.Algebra.{u} S}
    {j₁ j₂ : Judgment A} (e : j₁ = j₂) {Δ : Ctx S}
    (σ : Environment S A.substitution.Carrier j₂.1 Δ) :
    substJudgment j₁ (castEnv e σ) = substJudgment j₂ σ := by
  subst e
  rfl

/-- Contextual substitution of a complete firing tree. The result is
indexed by the substituted endpoints, so source and target commute with the
action by construction. Every rule occurrence is substituted, every premise
child is substituted beneath its own binders, and premise positions are kept. -/
noncomputable def substTree (A : BindingCloneAlgebra.Algebra.{u} S) :
    ∀ (j : Judgment A), Tree R A j →
      ∀ {Δ : Ctx S} (σ : Environment S A.substitution.Carrier j.1 Δ)
        (target : Judgment A), substJudgment j σ = target → Tree R A target :=
  Mettapedia.TypeTheory.IndexedPolynomial.Fix.eliminate (rules R A)
    (fun _ j _ => ∀ {Δ : Ctx S}
      (σ : Environment S A.substitution.Carrier j.1 Δ)
      (target : Judgment A), substJudgment j σ = target → Tree R A target)
    (fun _ _ shape _children results {_} σ target h =>
      Mettapedia.TypeTheory.IndexedPolynomial.Fix.roll
        (⟨Instance.subst R shape.1 (castEnv shape.2 σ),
          (conclusionJudgment_subst R shape.1 (castEnv shape.2 σ)).trans
            ((substJudgment_castEnv shape.2 σ).trans h)⟩ :
          Shape R A target)
        (fun position => results position
          (A.substitution.liftEnvironment (castEnv shape.2 σ)
            ((R.get shape.1.index).premises.get position).binders)
          (childJudgment R A (Instance.subst R shape.1 (castEnv shape.2 σ))
            position)
          (childJudgment_subst R shape.1 (castEnv shape.2 σ) position).symm))
    ()

/-- The action on one constructor layer. -/
theorem substTree_roll (A : BindingCloneAlgebra.Algebra.{u} S)
    {j : Judgment A} (shape : Shape R A j)
    (children : ∀ position : Fin (R.get shape.1.index).premises.length,
      Tree R A (childJudgment R A shape.1 position))
    {Δ : Ctx S} (σ : Environment S A.substitution.Carrier j.1 Δ)
    (target : Judgment A) (h : substJudgment j σ = target) :
    substTree R A j (Mettapedia.TypeTheory.IndexedPolynomial.Fix.roll shape children)
        σ target h =
      Mettapedia.TypeTheory.IndexedPolynomial.Fix.roll
        (⟨Instance.subst R shape.1 (castEnv shape.2 σ),
          (conclusionJudgment_subst R shape.1 (castEnv shape.2 σ)).trans
            ((substJudgment_castEnv shape.2 σ).trans h)⟩ :
          Shape R A target)
        (fun (position : Fin (R.get shape.1.index).premises.length) =>
          substTree R A _ (children position)
          (A.substitution.liftEnvironment (castEnv shape.2 σ)
            ((R.get shape.1.index).premises.get position).binders)
          (childJudgment R A (Instance.subst R shape.1 (castEnv shape.2 σ))
            position)
          (childJudgment_subst R shape.1 (castEnv shape.2 σ) position).symm) :=
  rfl

/-- Equal occurrences with heterogeneously equal children build equal
constructor layers. -/
theorem roll_congr_instance {A : BindingCloneAlgebra.Algebra.{u} S}
    {target : Judgment A} {first second : Instance R A}
    (same : first = second)
    (firstConclusion : conclusionJudgment R A first = target)
    (secondConclusion : conclusionJudgment R A second = target)
    (firstChildren : ∀ position : Fin (R.get first.index).premises.length,
      Tree R A (childJudgment R A first position))
    (secondChildren : ∀ position : Fin (R.get second.index).premises.length,
      Tree R A (childJudgment R A second position))
    (children : ∀ firstPosition secondPosition,
      HEq firstPosition secondPosition →
        HEq (firstChildren firstPosition) (secondChildren secondPosition)) :
    (Mettapedia.TypeTheory.IndexedPolynomial.Fix.roll
        (⟨first, firstConclusion⟩ : Shape R A target) firstChildren :
      Tree R A target) =
      Mettapedia.TypeTheory.IndexedPolynomial.Fix.roll
        (⟨second, secondConclusion⟩ : Shape R A target) secondChildren := by
  subst same
  have childrenEq : firstChildren = secondChildren :=
    funext fun position => eq_of_heq (children position position HEq.rfl)
  subst childrenEq
  rfl

theorem childJudgment_congr {A : BindingCloneAlgebra.Algebra.{u} S}
    {first second : Instance R A} (same : first = second)
    (firstPosition : Fin (R.get first.index).premises.length)
    (secondPosition : Fin (R.get second.index).premises.length)
    (samePosition : HEq firstPosition secondPosition) :
    childJudgment R A first firstPosition =
      childJudgment R A second secondPosition := by
  subst same
  cases samePosition
  rfl

theorem substTree_congr (A : BindingCloneAlgebra.Algebra.{u} S)
    {j : Judgment A} (tree : Tree R A j) {Δ : Ctx S}
    {σ₁ σ₂ : Environment S A.substitution.Carrier j.1 Δ} (sameEnv : σ₁ = σ₂)
    {target₁ target₂ : Judgment A} (sameTarget : target₁ = target₂)
    (h₁ : substJudgment j σ₁ = target₁) (h₂ : substJudgment j σ₂ = target₂) :
    HEq (substTree R A j tree σ₁ target₁ h₁)
      (substTree R A j tree σ₂ target₂ h₂) := by
  subst sameEnv
  subst sameTarget
  rfl

theorem substTree_heq (A : BindingCloneAlgebra.Algebra.{u} S)
    {j₁ j₂ : Judgment A} (sameJudgment : j₁ = j₂)
    {tree₁ : Tree R A j₁} {tree₂ : Tree R A j₂} (sameTree : HEq tree₁ tree₂)
    {Δ : Ctx S} {σ₁ : Environment S A.substitution.Carrier j₁.1 Δ}
    {σ₂ : Environment S A.substitution.Carrier j₂.1 Δ} (sameEnv : HEq σ₁ σ₂)
    {target₁ target₂ : Judgment A} (sameTarget : target₁ = target₂)
    (h₁ : substJudgment j₁ σ₁ = target₁) (h₂ : substJudgment j₂ σ₂ = target₂) :
    HEq (substTree R A j₁ tree₁ σ₁ target₁ h₁)
      (substTree R A j₂ tree₂ σ₂ target₂ h₂) := by
  subst sameJudgment
  cases sameTree
  cases sameEnv
  subst sameTarget
  rfl

/-- The identity substitution fixes every firing tree. -/
theorem substTree_identity (A : BindingCloneAlgebra.Algebra.{u} S)
    (j : Judgment A) (tree : Tree R A j) :
    ∀ (h : substJudgment j (fun _ v => A.substitution.injectVar v) = j),
      substTree R A j tree (fun _ v => A.substitution.injectVar v) j h =
        tree := by
  refine Mettapedia.TypeTheory.IndexedPolynomial.Fix.eliminate (rules R A)
    (fun _ j tree => ∀ (h : substJudgment j
        (fun _ v => A.substitution.injectVar v) = j),
      substTree R A j tree (fun _ v => A.substitution.injectVar v) j h = tree)
    ?_ () j tree
  intro base j shape children ih
  cases base
  obtain ⟨occurrence, hconc⟩ := shape
  subst hconc
  intro h
  refine roll_congr_instance R (Instance.subst_identity R occurrence) _ _ _ _ ?_
  intro position otherPosition samePosition
  cases samePosition
  have envEq :
      A.substitution.liftEnvironment
          (fun _ v => A.substitution.injectVar v :
            Environment S A.substitution.Carrier occurrence.ambient
              occurrence.ambient)
          ((R.get occurrence.index).premises.get position).binders =
        (fun _ v => A.substitution.injectVar v) :=
    liftEnvironment_injectVar A.substitution _
  have targetEq :
      childJudgment R A
          (Instance.subst R occurrence (fun _ v => A.substitution.injectVar v))
          position =
        childJudgment R A occurrence position :=
    (childJudgment_subst R occurrence _ position).trans
      ((congrArg (substJudgment (childJudgment R A occurrence position))
        (liftEnvironment_injectVar A.substitution _)).trans
        (substJudgment_identity _))
  exact (substTree_congr R A (children position) envEq targetEq _
    (substJudgment_identity _)).trans
    (heq_of_eq (ih position (substJudgment_identity _)))

/-- Substituting twice is substituting once along the composite. -/
theorem substTree_comp (A : BindingCloneAlgebra.Algebra.{u} S)
    (j : Judgment A) (tree : Tree R A j) :
    ∀ {Δ Θ : Ctx S} (σ : Environment S A.substitution.Carrier j.1 Δ)
      (τ : Environment S A.substitution.Carrier Δ Θ) (target : Judgment A)
      (hSecond : substJudgment (substJudgment j σ) τ = target)
      (hDirect : substJudgment j
        (fun t v => A.substitution.substitute τ (σ t v)) = target),
      substTree R A (substJudgment j σ)
          (substTree R A j tree σ (substJudgment j σ) rfl) τ target hSecond =
        substTree R A j tree
          (fun t v => A.substitution.substitute τ (σ t v)) target hDirect := by
  refine Mettapedia.TypeTheory.IndexedPolynomial.Fix.eliminate (rules R A)
    (fun _ j tree => ∀ {Δ Θ : Ctx S}
      (σ : Environment S A.substitution.Carrier j.1 Δ)
      (τ : Environment S A.substitution.Carrier Δ Θ) (target : Judgment A)
      (hSecond : substJudgment (substJudgment j σ) τ = target)
      (hDirect : substJudgment j
        (fun t v => A.substitution.substitute τ (σ t v)) = target),
      substTree R A (substJudgment j σ)
          (substTree R A j tree σ (substJudgment j σ) rfl) τ target hSecond =
        substTree R A j tree
          (fun t v => A.substitution.substitute τ (σ t v)) target hDirect)
    ?_ () j tree
  intro base j shape children ih
  cases base
  obtain ⟨occurrence, hconc⟩ := shape
  subst hconc
  intro Δ Θ σ τ target hSecond hDirect
  have envEq : ∀ (pf : conclusionJudgment R A (Instance.subst R occurrence σ) =
      substJudgment (conclusionJudgment R A occurrence) σ),
      castEnv pf τ = τ :=
    fun pf => eq_of_heq (castEnv_heq pf τ)
  have instanceEq : ∀ (pf : conclusionJudgment R A (Instance.subst R occurrence σ) =
      substJudgment (conclusionJudgment R A occurrence) σ),
      Instance.subst R (Instance.subst R occurrence σ) (castEnv pf τ) =
        Instance.subst R occurrence
          (fun t v => A.substitution.substitute τ (σ t v)) := by
    intro pf
    rw [envEq pf]
    exact Instance.subst_comp R occurrence σ τ
  refine roll_congr_instance R (instanceEq _) _ _ _ _ ?_
  intro position otherPosition samePosition
  cases samePosition
  have firstChild :
      childJudgment R A (Instance.subst R occurrence σ) position =
        substJudgment (childJudgment R A occurrence position)
          (A.substitution.liftEnvironment σ
            ((R.get occurrence.index).premises.get position).binders) :=
    childJudgment_subst R occurrence σ position
  have liftComp :
      (fun t v => A.substitution.substitute
        (A.substitution.liftEnvironment τ
          ((R.get occurrence.index).premises.get position).binders)
        (A.substitution.liftEnvironment σ
          ((R.get occurrence.index).premises.get position).binders t v)) =
        A.substitution.liftEnvironment
          (fun t v => A.substitution.substitute τ (σ t v))
          ((R.get occurrence.index).premises.get position).binders := by
    funext t v
    exact substitute_liftEnvironment A.substitution τ σ _ v
  have directChild :
      substJudgment
          (substJudgment (childJudgment R A occurrence position)
            (A.substitution.liftEnvironment σ
              ((R.get occurrence.index).premises.get position).binders))
          (A.substitution.liftEnvironment τ
            ((R.get occurrence.index).premises.get position).binders) =
        childJudgment R A
          (Instance.subst R occurrence
            (fun t v => A.substitution.substitute τ (σ t v))) position :=
    (substJudgment_comp _ _ _).trans
      ((congrArg (substJudgment (childJudgment R A occurrence position))
        liftComp).trans (childJudgment_subst R occurrence _ position).symm)
  have directOnce :
      substJudgment (childJudgment R A occurrence position)
          (fun t v => A.substitution.substitute
            (A.substitution.liftEnvironment τ
              ((R.get occurrence.index).premises.get position).binders)
            (A.substitution.liftEnvironment σ
              ((R.get occurrence.index).premises.get position).binders t v)) =
        childJudgment R A
          (Instance.subst R occurrence
            (fun t v => A.substitution.substitute τ (σ t v))) position :=
    (congrArg (substJudgment (childJudgment R A occurrence position))
      liftComp).trans (childJudgment_subst R occurrence _ position).symm
  refine HEq.trans (substTree_heq R A firstChild
      (substTree_congr R A (children position) rfl firstChild _ rfl)
      (heq_of_eq (congrArg
        (fun env => A.substitution.liftEnvironment env
          ((R.get occurrence.index).premises.get position).binders)
        (envEq _)))
      (childJudgment_congr R (instanceEq _) position position HEq.rfl)
      _ directChild) ?_
  refine HEq.trans (heq_of_eq (ih position
    (A.substitution.liftEnvironment σ
      ((R.get occurrence.index).premises.get position).binders)
    (A.substitution.liftEnvironment τ
      ((R.get occurrence.index).premises.get position).binders)
    _ directChild directOnce)) ?_
  exact substTree_congr R A (children position) liftComp rfl _ _

#print axioms substitute_interpretSchema
#print axioms interpretSchema_postAmbient
#print axioms conclusionJudgment_subst
#print axioms childJudgment_subst
#print axioms Instance.subst_identity
#print axioms Instance.subst_comp
#print axioms substTree
#print axioms substTree_identity
#print axioms substTree_comp

end Mettapedia.OSLF.Binding.IntrinsicScopedConditionalSubstitution
