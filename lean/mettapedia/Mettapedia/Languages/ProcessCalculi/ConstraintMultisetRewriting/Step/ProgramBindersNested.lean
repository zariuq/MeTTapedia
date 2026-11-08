import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramBindersContexts
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramBindersControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LambdaExecution

/-!
# Calls under binders: the λ contexts

Every position of a λ-term, under binders too, is a context of the λ grammar.
- **β in contexts:** with the β equation `(= ((λx. $B x) $A) $B[$A])`, rewriting in λ contexts is
  exactly `LambdaContextualRung.Step` (`lambda_rewrites_iff`). So the binder-bearing core, the
  retained λ execution of `LambdaExecution`, and the four-rule source agree on runs
  (`lambda_three_way`).
- **Calls under binders:** `(= (k $y) $y)` as a schema. Under `λx`, its hole lists `x`, which is in
  scope at the call, so `λx. (k x)` rewrites to `λx. x` (`under_binder_call`).
- **Two orders:** in `(λx. (k x)) a`, the call under the binder and the β redex both fire. Both
  orders reach `a`, on the step too (`both_orders_reach_a`).
- **Scope against capture:** under `λx`, the hole of `(= (k (λz. $N)) $N)` may take `x` but not the
  pattern's own bound `z` (`outer_binder_available`, `inner_binder_refused`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramBinders.Nested

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open LambdaContextualRung (sig Srt Op Context appT lamT)
open LambdaComparison (app lam app_inj lam_inj)
open ContextualPatternFragment (Pattern)
open Controls (Consts fC gC weaken_ne_bound lamT_inj appT_inj)

/-! ## The λ grammar -/

mutual
theorem encode_eq_include {W : Type} (declaration : W → MetaArity sig) :
    ∀ {Γ : Ctx sig} {sort : Srt} (term : Term sig Γ sort),
      LambdaComparison.encode declaration term = Rigid.includeTerm declaration term
  | _, _, .var _ => rfl
  | _, _, .op operator arguments =>
      congrArg (Term.op (S := signature sig declaration) (Sum.inl operator))
        (encodeArgs_eq_includeArgs declaration arguments)

theorem encodeArgs_eq_includeArgs {W : Type} (declaration : W → MetaArity sig) :
    ∀ {arities : List (MetaArity sig)} {Γ : Ctx sig} (arguments : Args sig arities Γ),
      LambdaComparison.encodeArgs declaration arguments = Rigid.includeArgs declaration arguments
  | _, _, .nil => rfl
  | _, _, .cons head tail => by
      change Args.cons (LambdaComparison.encode declaration head) (LambdaComparison.encodeArgs declaration tail) =
        Args.cons (Rigid.includeTerm declaration head) (Rigid.includeArgs declaration tail)
      rw [encode_eq_include declaration head, encodeArgs_eq_includeArgs declaration tail]
end

/-- Decidable equality of λ contexts. -/
def contextDecEq : {Γ Δ : Ctx sig} → (first second : Context Γ Δ) → Decidable (first = second)
  | _, _, .hole, .hole => isTrue rfl
  | _, _, .appLeft inner argument, .appLeft inner' argument' =>
      match contextDecEq inner inner', decEq argument argument' with
      | isTrue same, isTrue same' => isTrue (by rw [same, same'])
      | isFalse differ, _ => isFalse fun same => differ (Context.appLeft.inj same).1
      | _, isFalse differ => isFalse fun same => differ (Context.appLeft.inj same).2
  | _, _, .appRight function inner, .appRight function' inner' =>
      match decEq function function', contextDecEq inner inner' with
      | isTrue same, isTrue same' => isTrue (by rw [same, same'])
      | isFalse differ, _ => isFalse fun same => differ (Context.appRight.inj same).1
      | _, isFalse differ => isFalse fun same => differ (Context.appRight.inj same).2
  | _, _, .underLam inner, .underLam inner' =>
      match contextDecEq inner inner' with
      | isTrue same => isTrue (by rw [same])
      | isFalse differ => isFalse fun same => differ (Context.underLam.inj same)
  | _, _, .hole, .appLeft _ _ => isFalse nofun
  | _, _, .hole, .appRight _ _ => isFalse nofun
  | _, _, .hole, .underLam _ => isFalse nofun
  | _, _, .appLeft _ _, .hole => isFalse nofun
  | _, _, .appLeft _ _, .appRight _ _ => isFalse nofun
  | _, _, .appLeft _ _, .underLam _ => isFalse nofun
  | _, _, .appRight _ _, .hole => isFalse nofun
  | _, _, .appRight _ _, .appLeft _ _ => isFalse nofun
  | _, _, .appRight _ _, .underLam _ => isFalse nofun
  | _, _, .underLam _, .hole => isFalse nofun
  | _, _, .underLam _, .appLeft _ _ => isFalse nofun
  | _, _, .underLam _, .appRight _ _ => isFalse nofun

instance (Γ Δ : Ctx sig) : DecidableEq (Context Γ Δ) := contextDecEq

/-- The outer context weakened into the hole's context: one shift per binder passed. -/
def weakening : {Γ Δ : Ctx sig} → Context Γ Δ → Ren sig Γ Δ
  | _, _, .hole => fun _ position => position
  | _, _, .appLeft inner _ => weakening inner
  | _, _, .appRight _ inner => weakening inner
  | _, _, .underLam inner => fun sort position => weakening inner sort (.succ position)

/-- Every position of a λ-term, under binders too. -/
def grammar : ContextGrammar sig .term where
  Context := Context
  contextEq := fun _ _ => contextDecEq
  weakening := weakening
  plugSource := fun context term => context.plug term
  plug := fun declaration _ _ context term => LambdaComparison.plug declaration context term
  plug_include := fun declaration _ _ context term => by
    rw [← encode_eq_include, ← encode_eq_include]
    exact LambdaComparison.plug_encode declaration context term
  instantiate_plug := fun change _ _ context term => LambdaComparison.instantiate_plug change context term
  plug_injective := fun _ _ _ context => LambdaComparison.plug_injective context
  plug_pattern := fun context term patterned => LambdaComparison.plug_pattern context term patterned
  plug_recovers := fun {_} {declaration} _ _ context value term same => by
    rw [← encode_eq_include] at same
    obtain ⟨inner, isPlug, read⟩ := LambdaComparison.plug_recovers context value term same
    exact ⟨inner, isPlug, read.trans (encode_eq_include declaration inner)⟩

theorem include_app_recovers {W : Type} {declaration : W → MetaArity sig} {Γ : Ctx sig} :
    ∀ (term : Term sig Γ .term) (function argument : Term (signature sig declaration) Γ .term),
      app declaration function argument = Rigid.includeTerm declaration term →
      ∃ (f a : Term sig Γ .term), term = appT f a ∧
        function = Rigid.includeTerm declaration f ∧ argument = Rigid.includeTerm declaration a
  | .var _, _, _, same => by cases same
  | .op .app (.cons f (.cons a .nil)), _, _, same => ⟨f, a, rfl, app_inj same⟩
  | .op .lam _, _, _, same => by cases (Term.op.inj same).1

theorem include_lam_recovers {W : Type} {declaration : W → MetaArity sig} {Γ : Ctx sig} :
    ∀ (term : Term sig Γ .term) (body : Term (signature sig declaration) (.term :: Γ) .term),
      lam declaration body = Rigid.includeTerm declaration term →
      ∃ b : Term sig (.term :: Γ) .term, term = lamT b ∧ body = Rigid.includeTerm declaration b
  | .var _, _, same => by cases same
  | .op .app _, _, same => by cases (Term.op.inj same).1
  | .op .lam (.cons body .nil), _, same => ⟨body, rfl, lam_inj same⟩

/-! ## β in every context -/

def betaArity (Δ : Ctx sig) : Bool → MetaArity sig
  | false => (.term :: Δ, .term)
  | true => (Δ, .term)

/-- `(= ((λx. $B x) $A) $B[$A])`. -/
def betaEquation (Δ : Ctx sig) : Equation sig Δ .term :=
  ⟨Bool, inferInstance, betaArity Δ,
    app _ (lam _ (generator (betaArity Δ) false)) (generator (betaArity Δ) true),
    inst (generator (betaArity Δ) false) (generator (betaArity Δ) true)⟩

theorem instantiate_beta_lhs {Δ : Ctx sig} {W : Type} {target : W → MetaArity sig}
    (change : Assignment (betaArity Δ) target) :
    instantiate change (betaEquation Δ).lhs = app target (lam target (change false)) (change true) :=
  congrArg₂ (fun body argument => app target (lam target body) argument)
    (instantiate_generator change false) (instantiate_generator change true)

theorem instantiate_beta_rhs {Δ : Ctx sig} {W : Type} {target : W → MetaArity sig}
    (change : Assignment (betaArity Δ) target) :
    instantiate change (betaEquation Δ).rhs = inst (change false) (change true) :=
  (LambdaComparison.instantiate_inst change _ _).trans
    (congrArg₂ inst (instantiate_generator change false) (instantiate_generator change true))

theorem beta_answers {Δ : Ctx sig} (call answer : Term sig Δ .term) :
    Answers (betaEquation Δ) call answer ↔
      ∃ body argument, call = appT (lamT body) argument ∧ answer = inst body argument := by
  constructor
  · rintro ⟨θ, matched, answered⟩
    have opened := (instantiate_beta_lhs _).symm.trans matched
    obtain ⟨function, argument, rfl, functionRead, argumentRead⟩ := include_app_recovers call _ _ opened
    obtain ⟨body, rfl, bodyRead⟩ := include_lam_recovers function _ functionRead
    have bodySame : θ false = body := Rigid.include_injective _ _ _ bodyRead
    have argumentSame : θ true = argument := Rigid.include_injective _ _ _ argumentRead
    refine ⟨body, argument, rfl, ?_⟩
    have result := (Rigid.include_inst (ground sig) (θ false) (θ true)).trans
      ((instantiate_beta_rhs _).symm.trans answered)
    exact (Rigid.include_injective _ _ _ result).symm.trans (congrArg₂ inst bodySame argumentSame)
  · rintro ⟨body, argument, rfl, rfl⟩
    refine ⟨fun | false => body | true => argument, (instantiate_beta_lhs _).trans rfl, ?_⟩
    exact (instantiate_beta_rhs _).trans (Rigid.include_inst (ground sig) body argument).symm

theorem beta_lhs_pattern (Δ : Ctx sig) : Pattern sig (betaEquation Δ).arity (betaEquation Δ).lhs :=
  .rigid (S := sig) Op.app _ (.cons _ _ (.rigid (S := sig) Op.lam _
    (.cons _ _ (ContextualPatternFragment.generator_pattern _) .nil))
    (.cons _ _ (ContextualPatternFragment.generator_pattern _) .nil))

def betaSchema (Γ : Ctx sig) : Schema grammar Γ Unit := fun {Δ} _ _ => betaEquation Δ

/-- **β in λ contexts is the four-rule λ step.** -/
theorem lambda_rewrites_iff {Γ : Ctx sig} (call answer : Term sig Γ .term) :
    CRewrites grammar (betaSchema Γ) call answer ↔ LambdaContextualRung.Step Γ call answer := by
  rw [LambdaContextualRung.step_iff_context_beta]
  constructor
  · rintro ⟨Δ, context, _, inner, result, rfl, rfl, answered⟩
    obtain ⟨body, argument, rfl, rfl⟩ := (beta_answers inner result).mp answered
    exact ⟨Δ, context, body, argument, rfl, rfl⟩
  · rintro ⟨Δ, context, body, argument, rfl, rfl⟩
    exact ⟨Δ, context, (), _, _, rfl, rfl, (beta_answers _ _).mpr ⟨body, argument, rfl, rfl⟩⟩

/-- **The three-way join.** The four-rule λ source, the retained λ execution of `LambdaExecution`,
and the binder-bearing equation core with the β equation agree on runs. -/
theorem lambda_three_way {Γ : Ctx sig} (call answer : Term sig Γ .term) :
    (Relation.ReflTransGen (LambdaContextualRung.Step Γ) call answer ↔
      ∃ after, Relation.ReflTransGen LambdaExecution.Transition (LambdaExecution.initial call) after ∧
        LambdaExecution.Represents after answer) ∧
    (Relation.ReflTransGen (LambdaContextualRung.Step Γ) call answer ↔
      ∃ after, Relation.ReflTransGen (Transition (contextProgram grammar (betaSchema Γ))) (initial call) after ∧
        Reads (contextProgram grammar (betaSchema Γ)) after answer) := by
  have same : LambdaContextualRung.Step Γ = CRewrites grammar (betaSchema Γ) := by
    funext first second
    exact propext (lambda_rewrites_iff first second).symm
  refine ⟨LambdaExecution.finite_execution_iff call answer, ?_⟩
  rw [same]
  exact context_execution_iff (betaSchema Γ) call answer

/-! ## A call under a binder -/

/-- `(= (k $y) $y)` at any weakening: `k` is the constant at position `0`, and the hole lists every
variable in scope at the call. -/
def callEquation {Δ : Ctx sig} (ρ : Ren sig Consts Δ) : Equation sig Δ .term :=
  ⟨Unit, inferInstance, fun _ => (Δ, .term), app _ (.var (ρ _ .zero)) (generator _ ()), generator _ ()⟩

theorem call_answers {Δ : Ctx sig} (ρ : Ren sig Consts Δ) (call answer : Term sig Δ .term) :
    Answers (callEquation ρ) call answer ↔ call = appT (.var (ρ _ .zero)) answer := by
  constructor
  · rintro ⟨θ, matched, answered⟩
    have opened : app _ (.var (ρ _ .zero)) (Rigid.includeTerm (ground sig) (θ ())) =
        Rigid.includeTerm (ground sig) call :=
      (congrArg (app _ (.var (ρ _ .zero))) (instantiate_generator _ ())).symm.trans matched
    have read : Rigid.includeTerm (ground sig) (θ ()) = Rigid.includeTerm (ground sig) answer :=
      (instantiate_generator _ ()).symm.trans answered
    obtain ⟨head, argument, rfl, headRead, argumentRead⟩ := include_app_recovers call _ _ opened
    have headSame : Term.var (ρ _ .zero) = head := Rigid.include_injective (ground sig) (.var (ρ _ .zero)) head headRead
    have argumentSame : argument = answer :=
      Rigid.include_injective _ _ _ (argumentRead.symm.trans read)
    rw [← headSame, argumentSame]
  · rintro rfl
    exact ⟨fun _ => answer, (congrArg (app _ (.var (ρ _ .zero))) (instantiate_generator _ ())).trans rfl,
      instantiate_generator _ ()⟩

/-- β and the call equation, as one program. -/
def nestedSchema : Schema grammar Consts Bool :=
  fun {Δ} context rule => cond rule (betaEquation Δ) (callEquation (weakening context))

/-- `λx. (k x)` rewrites to `λx. x`: the hole takes `x`, which is in scope at the call. -/
theorem under_binder_call :
    CRewrites grammar nestedSchema (lamT (appT (.var (.succ .zero)) (.var .zero)) : Term sig Consts .term)
      (lamT (.var .zero)) :=
  ⟨_, .underLam .hole, false, _, _, rfl, rfl, (call_answers _ _ _).mpr rfl⟩

/-- `(λx. (k x)) a`. -/
def nestedProgram : Term sig Consts .term := appT (lamT (appT (.var (.succ .zero)) (.var .zero))) gC

/-- β first gives `k a`. -/
theorem beta_first : CRewrites grammar nestedSchema nestedProgram (appT fC gC) :=
  ⟨_, .hole, true, _, _, rfl, rfl, (beta_answers _ _).mpr ⟨_, _, rfl, rfl⟩⟩

/-- The call under the binder first gives `(λx. x) a`. -/
theorem call_first : CRewrites grammar nestedSchema nestedProgram (appT (lamT (.var .zero)) gC) :=
  ⟨_, .appLeft (.underLam .hole) gC, false, _, _, rfl, rfl, (call_answers _ _ _).mpr rfl⟩

theorem first_rewrites_differ : appT fC gC ≠ (appT (lamT (.var .zero)) gC : Term sig Consts .term) := by
  intro same
  cases same

/-- Both orders reach `a`, and the step reaches it. -/
theorem both_orders_reach_a :
    Relation.ReflTransGen (CRewrites grammar nestedSchema) (appT fC gC) gC ∧
      Relation.ReflTransGen (CRewrites grammar nestedSchema) (appT (lamT (.var .zero)) gC) gC ∧
      Relation.ReflTransGen (CRewrites grammar nestedSchema) nestedProgram gC ∧
      ∃ after, Relation.ReflTransGen (Transition (contextProgram grammar nestedSchema)) (initial nestedProgram) after ∧
        Reads (contextProgram grammar nestedSchema) after gC := by
  have callRoot : CRewrites grammar nestedSchema (appT fC gC) gC :=
    ⟨_, .hole, false, _, _, rfl, rfl, (call_answers _ _ _).mpr rfl⟩
  have betaRoot : CRewrites grammar nestedSchema (appT (lamT (.var .zero)) gC) gC :=
    ⟨_, .hole, true, _, _, rfl, rfl, (beta_answers _ _).mpr ⟨_, _, rfl, rfl⟩⟩
  have whole : Relation.ReflTransGen (CRewrites grammar nestedSchema) nestedProgram gC :=
    (Relation.ReflTransGen.single beta_first).tail callRoot
  exact ⟨.single callRoot, .single betaRoot, whole, (context_execution_iff nestedSchema _ _).mp whole⟩

/-! ## Scope against capture under a binder -/

/-- `(= (k (λz. $N)) $N)`: the hole lists the variables in scope at the call, not the pattern's `z`. -/
def scopeEquation {Δ : Ctx sig} (ρ : Ren sig Consts Δ) : Equation sig Δ .term :=
  ⟨Unit, inferInstance, fun _ => (Δ, .term),
    app _ (.var (ρ _ .zero)) (lam _ (weaken (generator (fun _ : Unit => ((Δ, .term) : MetaArity sig)) ()))),
    generator _ ()⟩

theorem instantiate_scope_lhs {Δ : Ctx sig} (ρ : Ren sig Consts Δ) {W : Type} {target : W → MetaArity sig}
    (change : Assignment (scopeEquation ρ).arity target) :
    instantiate change (scopeEquation ρ).lhs = app target (.var (ρ _ .zero)) (lam target (weaken (change ()))) := by
  change app target (.var (ρ _ .zero)) (lam target (instantiate change (weaken (generator _ ())))) = _
  rw [weaken, ContextualFamily.instantiate_rename, instantiate_generator]
  rfl

/-- Under `λx`, the hole takes `x`: `λx. (k (λz. x))` answers `λx. x`. -/
theorem outer_binder_available :
    Answers (scopeEquation (Δ := .term :: Consts) (weakening (.underLam .hole)))
      (appT (.var (.succ .zero)) (lamT (.var (.succ .zero)))) (.var .zero) := by
  refine ⟨fun _ => .var .zero, ?_, instantiate_generator _ ()⟩
  rw [Matches, instantiate_scope_lhs]
  rfl

/-- Under `λx`, the hole cannot capture the pattern's own `z`: `λx. (k (λz. z))` is refused. -/
theorem inner_binder_refused (answer : Term sig (.term :: Consts) .term) :
    ¬ Answers (scopeEquation (Δ := .term :: Consts) (weakening (.underLam .hole)))
      (appT (.var (.succ .zero)) (lamT (.var .zero))) answer := by
  rintro ⟨θ, matched, _⟩
  rw [Matches, instantiate_scope_lhs] at matched
  exact weaken_ne_bound _ (lam_inj (app_inj matched).2)

#print axioms encode_eq_include
#print axioms beta_answers
#print axioms beta_lhs_pattern
#print axioms lambda_rewrites_iff
#print axioms lambda_three_way
#print axioms call_answers
#print axioms under_binder_call
#print axioms beta_first
#print axioms call_first
#print axioms first_rewrites_differ
#print axioms both_orders_reach_a
#print axioms outer_binder_available
#print axioms inner_binder_refused

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramBinders.Nested
