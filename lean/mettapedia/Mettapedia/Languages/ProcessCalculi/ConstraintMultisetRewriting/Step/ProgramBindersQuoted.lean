import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramBindersContexts
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.QuotedLambdaExecution

/-!
# The join with the quoted-λ account

The two computational roots of `QuotedLambda` are pattern equations of the binder-bearing core.
- **β:** `(= ((λx. $B x) $A) $B[$A])`. The hole under `λ` lists the bound variable, the argument's
  hole does not; the right-hand side substitutes the argument for it.
- **Activation:** `(= (activate (quote $C)) $C)`.

Each is a family over the hole's context, and the active contexts of `QuotedLambda` (never inside
a quotation) are a context grammar.

**Theorems.**
- `quoted_rewrites_iff`: rewriting by the two equations in active contexts is exactly the step
  relation `QuotedLambda.Step`.
- `quoted_execution_iff`: runs of `QuotedLambda.Step` are exactly the readings of the runs of the
  equation core on the contextual step.
- `executes_iff_rewrites`: the contextual transform execution of `QuotedLambdaExecution` and one
  rewrite of the equation core agree.
- `quoted_principal_first`: the first firing on a call computes a principal answer.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramBinders.Quoted

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open QuotedLambda (sig Op Context Redex)
open LambdaContextualRung (Srt)
open QuotedLambdaExecution (app lam quote activate Kind)
open ContextualPatternFragment (Pattern)

scoped instance : DecidableEq sig.Srt := inferInstanceAs (DecidableEq Srt)
scoped instance (sort : sig.Srt) : DecidableEq (sig.Op sort) := inferInstanceAs (DecidableEq (Op sort))

/-- The identity `λx. x` is a closed term of the only sort. -/
instance : ClosedTerms sig := ⟨fun | .term => QuotedLambda.lam (.var .zero)⟩

/-- Decidable equality of active contexts. -/
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
  | _, _, .underActivate inner, .underActivate inner' =>
      match contextDecEq inner inner' with
      | isTrue same => isTrue (by rw [same])
      | isFalse differ => isFalse fun same => differ (Context.underActivate.inj same)
  | _, _, .hole, .appLeft _ _ => isFalse nofun
  | _, _, .hole, .appRight _ _ => isFalse nofun
  | _, _, .hole, .underLam _ => isFalse nofun
  | _, _, .hole, .underActivate _ => isFalse nofun
  | _, _, .appLeft _ _, .hole => isFalse nofun
  | _, _, .appLeft _ _, .appRight _ _ => isFalse nofun
  | _, _, .appLeft _ _, .underLam _ => isFalse nofun
  | _, _, .appLeft _ _, .underActivate _ => isFalse nofun
  | _, _, .appRight _ _, .hole => isFalse nofun
  | _, _, .appRight _ _, .appLeft _ _ => isFalse nofun
  | _, _, .appRight _ _, .underLam _ => isFalse nofun
  | _, _, .appRight _ _, .underActivate _ => isFalse nofun
  | _, _, .underLam _, .hole => isFalse nofun
  | _, _, .underLam _, .appLeft _ _ => isFalse nofun
  | _, _, .underLam _, .appRight _ _ => isFalse nofun
  | _, _, .underLam _, .underActivate _ => isFalse nofun
  | _, _, .underActivate _, .hole => isFalse nofun
  | _, _, .underActivate _, .appLeft _ _ => isFalse nofun
  | _, _, .underActivate _, .appRight _ _ => isFalse nofun
  | _, _, .underActivate _, .underLam _ => isFalse nofun

instance (Γ Δ : Ctx sig) : DecidableEq (Context Γ Δ) := contextDecEq

/-- The outer context weakened into the hole's context: one shift per binder passed. -/
def weakening : {Γ Δ : Ctx sig} → Context Γ Δ → Ren sig Γ Δ
  | _, _, .hole => fun _ position => position
  | _, _, .appLeft inner _ => weakening inner
  | _, _, .appRight _ inner => weakening inner
  | _, _, .underLam inner => fun sort position => weakening inner sort (.succ position)
  | _, _, .underActivate inner => weakening inner

/-- The active contexts of the quoted-λ account: never inside a quotation. -/
def grammar : ContextGrammar sig .term where
  Context := Context
  contextEq := fun _ _ => contextDecEq
  weakening := weakening
  plugSource := fun context term => context.plug term
  plug := fun declaration _ _ context term => QuotedLambdaExecution.plug declaration context term
  plug_include := fun declaration _ _ context term => QuotedLambdaExecution.plug_encode declaration context term
  instantiate_plug := fun change _ _ context term => QuotedLambdaExecution.instantiate_plug change context term
  plug_injective := fun _ _ _ context => QuotedLambdaExecution.plug_injective context
  plug_pattern := fun context term patterned => QuotedLambdaExecution.plug_pattern context term patterned
  plug_recovers := fun context value term same => QuotedLambdaExecution.plug_recovers context value term same

/-! ## The two root equations -/

/-- The hole under `λ` lists the bound variable; the argument's hole does not. -/
def betaArity (Δ : Ctx sig) : Bool → MetaArity sig
  | false => (.term :: Δ, .term)
  | true => (Δ, .term)

/-- `(= ((λx. $B x) $A) $B[$A])`. -/
def betaEquation (Δ : Ctx sig) : Equation sig Δ .term :=
  ⟨Bool, inferInstance, betaArity Δ,
    app _ (lam _ (generator (betaArity Δ) false)) (generator (betaArity Δ) true),
    inst (generator (betaArity Δ) false) (generator (betaArity Δ) true)⟩

/-- `(= (activate (quote $C)) $C)`. -/
def activationEquation (Δ : Ctx sig) : Equation sig Δ .term :=
  ⟨Unit, inferInstance, fun _ => (Δ, .term), activate _ (quote _ (generator _ ())), generator _ ()⟩

def family : (Δ : Ctx sig) → Kind → Equation sig Δ .term
  | Δ, .beta => betaEquation Δ
  | Δ, .activation => activationEquation Δ

/-- The two equations mention no constant, so the schema ignores the weakening. -/
def schema (Γ : Ctx sig) : Schema grammar Γ Kind := fun {Δ} _ kind => family Δ kind

theorem instantiate_beta_lhs {Δ : Ctx sig} {W : Type} {target : W → MetaArity sig}
    (change : Assignment (betaArity Δ) target) :
    instantiate change (betaEquation Δ).lhs = app target (lam target (change false)) (change true) :=
  congrArg₂ (fun body argument => app target (lam target body) argument)
    (instantiate_generator change false) (instantiate_generator change true)

theorem instantiate_beta_rhs {Δ : Ctx sig} {W : Type} {target : W → MetaArity sig}
    (change : Assignment (betaArity Δ) target) :
    instantiate change (betaEquation Δ).rhs = inst (change false) (change true) :=
  (QuotedLambdaExecution.instantiate_inst change _ _).trans
    (congrArg₂ inst (instantiate_generator change false) (instantiate_generator change true))

theorem beta_answers {Δ : Ctx sig} (call answer : Term sig Δ .term) :
    Answers (betaEquation Δ) call answer ↔
      ∃ body argument, call = QuotedLambda.app (QuotedLambda.lam body) argument ∧ answer = inst body argument := by
  constructor
  · rintro ⟨θ, matched, answered⟩
    have opened := (instantiate_beta_lhs _).symm.trans matched
    obtain ⟨function, argument, rfl, functionRead, argumentRead⟩ :=
      QuotedLambdaExecution.encode_app_recovers call _ _ opened
    obtain ⟨body, rfl, bodyRead⟩ := QuotedLambdaExecution.encode_lam_recovers function _ functionRead
    have bodySame : θ false = body := Rigid.include_injective _ _ _ bodyRead
    have argumentSame : θ true = argument := Rigid.include_injective _ _ _ argumentRead
    refine ⟨body, argument, rfl, ?_⟩
    have result := (Rigid.include_inst (ground sig) (θ false) (θ true)).trans
      ((instantiate_beta_rhs _).symm.trans answered)
    exact ((Rigid.include_injective _ _ _ result).symm.trans (congrArg₂ inst bodySame argumentSame))
  · rintro ⟨body, argument, rfl, rfl⟩
    refine ⟨fun | false => body | true => argument, (instantiate_beta_lhs _).trans rfl, ?_⟩
    exact (instantiate_beta_rhs _).trans (Rigid.include_inst (ground sig) body argument).symm

theorem activation_answers {Δ : Ctx sig} (call answer : Term sig Δ .term) :
    Answers (activationEquation Δ) call answer ↔ call = QuotedLambda.activate (QuotedLambda.quote answer) := by
  constructor
  · rintro ⟨θ, matched, answered⟩
    have opened : activate _ (quote _ (Rigid.includeTerm (ground sig) (θ ()))) = Rigid.includeTerm (ground sig) call :=
      (congrArg (fun code => activate _ (quote _ code)) (instantiate_generator _ ())).symm.trans matched
    have read : Rigid.includeTerm (ground sig) (θ ()) = Rigid.includeTerm (ground sig) answer :=
      (instantiate_generator _ ()).symm.trans answered
    obtain ⟨name, rfl, nameRead⟩ := QuotedLambdaExecution.encode_activate_recovers call _ opened
    obtain ⟨code, rfl, codeRead⟩ := QuotedLambdaExecution.encode_quote_recovers name _ nameRead
    have same : code = answer := Rigid.include_injective _ _ _ (codeRead.symm.trans read)
    rw [same]
  · rintro rfl
    refine ⟨fun _ => answer, ?_, instantiate_generator _ ()⟩
    exact (congrArg (fun code => activate _ (quote _ code)) (instantiate_generator _ ())).trans rfl

/-- The root rewrites of the two equations are exactly the root redexes. -/
theorem family_answers {Δ : Ctx sig} (call answer : Term sig Δ .term) :
    (∃ kind, Answers (family Δ kind) call answer) ↔
      ∃ redex : Redex Δ, call = redex.source ∧ answer = redex.target := by
  constructor
  · rintro ⟨kind, answered⟩
    cases kind with
    | beta =>
        obtain ⟨body, argument, rfl, rfl⟩ := (beta_answers call answer).mp answered
        exact ⟨.beta body argument, rfl, rfl⟩
    | activation =>
        obtain rfl := (activation_answers call answer).mp answered
        exact ⟨.activation answer, rfl, rfl⟩
  · rintro ⟨redex, rfl, rfl⟩
    cases redex with
    | beta body argument => exact ⟨.beta, (beta_answers _ _).mpr ⟨body, argument, rfl, rfl⟩⟩
    | activation code => exact ⟨.activation, (activation_answers _ _).mpr rfl⟩

/-- **Rewriting in active contexts is the quoted-λ step.** -/
theorem quoted_rewrites_iff {Γ : Ctx sig} (call answer : Term sig Γ .term) :
    CRewrites grammar (schema Γ) call answer ↔ QuotedLambda.Step Γ call answer := by
  rw [QuotedLambda.step_iff_context_redex]
  constructor
  · rintro ⟨Δ, context, kind, inner, result, rfl, rfl, answered⟩
    obtain ⟨redex, rfl, rfl⟩ := (family_answers inner result).mp ⟨kind, answered⟩
    exact ⟨Δ, context, redex, rfl, rfl⟩
  · rintro ⟨Δ, context, redex, rfl, rfl⟩
    obtain ⟨kind, answered⟩ := (family_answers redex.source redex.target).mpr ⟨redex, rfl, rfl⟩
    exact ⟨Δ, context, kind, _, _, rfl, rfl, answered⟩

/-- **The join on the step.** Runs of the quoted-λ step are exactly the readings of runs of the
binder-bearing equation core on the contextual step. -/
theorem quoted_execution_iff {Γ : Ctx sig} (call answer : Term sig Γ .term) :
    Relation.ReflTransGen (QuotedLambda.Step Γ) call answer ↔
      ∃ after, Relation.ReflTransGen (Transition (contextProgram grammar (schema Γ))) (initial call) after ∧
        Reads (contextProgram grammar (schema Γ)) after answer := by
  have same : QuotedLambda.Step Γ = CRewrites grammar (schema Γ) := by
    funext first second
    exact propext (quoted_rewrites_iff first second).symm
  rw [same]
  exact context_execution_iff (schema Γ) call answer

/-- The transform execution of `QuotedLambdaExecution` and one rewrite of the equation core agree. -/
theorem executes_iff_rewrites {Γ : Ctx sig} (call answer : Term sig Γ .term) :
    QuotedLambdaExecution.Executes call answer ↔ Rewrites (contextProgram grammar (schema Γ)) call answer :=
  (QuotedLambdaExecution.source_step_iff_executes call answer).symm.trans
    ((quoted_rewrites_iff call answer).symm.trans (context_rewrites_iff (schema Γ) call answer).symm)

theorem family_lhs_pattern (Δ : Ctx sig) (kind : Kind) :
    Pattern sig (family Δ kind).arity (family Δ kind).lhs := by
  cases kind with
  | beta =>
      exact .rigid (S := sig) Op.app _ (.cons _ _ (.rigid (S := sig) Op.lam _
        (.cons _ _ (ContextualPatternFragment.generator_pattern _) .nil))
        (.cons _ _ (ContextualPatternFragment.generator_pattern _) .nil))
  | activation =>
      exact .rigid (S := sig) Op.activate _ (.cons _ _ (.rigid (S := sig) Op.quote _
        (.cons _ _ (ContextualPatternFragment.generator_pattern _) .nil)) .nil)

/-- **The first firing is principal.** At the initial state of any call, an admitted firing of
either equation in any active context has a completed worklist run whose answer is principal. -/
theorem quoted_principal_first {Γ : Ctx sig} (call : Term sig Γ .term)
    (key : Σ Δ : Ctx sig, grammar.Context Γ Δ × Kind)
    (valid : Admitted (contextProgram grammar (schema Γ)) (initial call) key) :
    ∃ (fuel : Nat) (update : ContextualFrameUpdate.Update (firingProblem (initial call) key)),
      (letI := (destination (contextProgram grammar (schema Γ)) (initial call) key valid).1.equality;
        ContextualFrameWorklist.run fuel (active (contextProgram grammar (schema Γ)) (initial (program :=
          contextProgram grammar (schema Γ)) call).1.declarations) (firingProblem (initial call) key)) =
          .residual update ∧
        update.remaining = [] := by
  obtain ⟨fuel, update, computed, empty, _⟩ := principal_firing (initial call) key valid (initial_pattern call)
    (atContext_pattern key.2.1 (family key.1 key.2.2) (family_lhs_pattern key.1 key.2.2))
  exact ⟨fuel, update, computed, empty⟩

/-! ## Controls -/

open QuotedLambda.Controls (quotedArgumentProgram identity)

/-- Named code passed by β and then explicitly activated, on the step. -/
theorem passing_then_activating_on_step :
    ∃ after, Relation.ReflTransGen (Transition (contextProgram grammar (schema []))) (initial quotedArgumentProgram) after ∧
      Reads (contextProgram grammar (schema [])) after identity :=
  (quoted_execution_iff _ _).mp QuotedLambda.Controls.passing_named_code_then_explicitly_activating

/-- A quotation is inert: no firing of either equation is admitted at its initial state. -/
theorem quotation_has_no_firing {Γ : Ctx sig} (code : Term sig Γ .term)
    (key : Σ Δ : Ctx sig, Context Γ Δ × Kind) :
    ¬ Admitted (contextProgram grammar (schema Γ)) (initial (QuotedLambda.quote code)) key := by
  intro valid
  obtain ⟨θ, matched⟩ := (valid_iff _ _ (initial_determines _) key).mp valid
  obtain ⟨result, read⟩ := holeFree (instantiate ((contextProgram grammar (schema Γ) key).assign θ (ground sig))
    (contextProgram grammar (schema Γ) key).rhs)
  have rewriting : Rewrites (contextProgram grammar (schema Γ)) (QuotedLambda.quote code) result :=
    ⟨key, θ, matched, read⟩
  exact QuotedLambda.quote_is_inert code result ((quoted_rewrites_iff _ _).mp
    ((context_rewrites_iff (schema Γ) _ _).mp rewriting))

#print axioms beta_answers
#print axioms activation_answers
#print axioms family_answers
#print axioms quoted_rewrites_iff
#print axioms quoted_execution_iff
#print axioms executes_iff_rewrites
#print axioms family_lhs_pattern
#print axioms quoted_principal_first
#print axioms passing_then_activating_on_step
#print axioms quotation_has_no_firing

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramBinders.Quoted
