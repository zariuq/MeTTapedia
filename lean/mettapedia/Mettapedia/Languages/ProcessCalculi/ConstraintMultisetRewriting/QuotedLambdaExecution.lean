import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualTransportedActivation
import Mettapedia.OSLF.Syntax.QuotedLambda
import Mettapedia.OSLF.Syntax.ContextualRigidReflection

/-!
# Quotation, lexical captures and activation through contextual transforms

The independent source is `QuotedLambda`: ordinary lambda constructors,
inert lexical quotation and explicit activation. Both computational roots
are ordinary contextual transform schemas. The active-context grammar
excludes quotation bodies; patterns may still inspect their rigid syntax.
No source evaluator is called by a rule or supplied as an admission premise.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.QuotedLambdaExecution

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open QuotedLambda (sig Op Context Redex)
open LambdaContextualRung (Srt)

variable {V W : Type} (declaration : V → MetaArity sig)

abbrev encode {Γ : Ctx sig} {sort : Srt} (term : Term sig Γ sort) :
    Term (signature sig declaration) Γ sort := Rigid.includeTerm declaration term

def app {Γ : Ctx sig} (function argument : Term (signature sig declaration) Γ .term) :=
  Term.op (S := signature sig declaration) (.inl .app) (.cons function (.cons argument .nil))
def lam {Γ : Ctx sig} (body : Term (signature sig declaration) (.term :: Γ) .term) :=
  Term.op (S := signature sig declaration) (.inl .lam) (.cons body .nil)
def quote {Γ : Ctx sig} (code : Term (signature sig declaration) Γ .term) :=
  Term.op (S := signature sig declaration) (.inl .quote) (.cons code .nil)
def activate {Γ : Ctx sig} (name : Term (signature sig declaration) Γ .term) :=
  Term.op (S := signature sig declaration) (.inl .activate) (.cons name .nil)

variable {declaration} {next : W → MetaArity sig}

theorem app_inj {Γ : Ctx sig} {first second third fourth : Term (signature sig declaration) Γ .term}
    (same : app declaration first second = app declaration third fourth) : first = third ∧ second = fourth := by
  have fields := Args.cons.inj (eq_of_heq (Term.op.inj same).2)
  exact ⟨fields.1, (Args.cons.inj fields.2).1⟩
theorem lam_inj {Γ : Ctx sig} {first second : Term (signature sig declaration) (.term :: Γ) .term}
    (same : lam declaration first = lam declaration second) : first = second :=
  (Args.cons.inj (eq_of_heq (Term.op.inj same).2)).1
theorem quote_inj {Γ : Ctx sig} {first second : Term (signature sig declaration) Γ .term}
    (same : quote declaration first = quote declaration second) : first = second :=
  (Args.cons.inj (eq_of_heq (Term.op.inj same).2)).1
theorem activate_inj {Γ : Ctx sig} {first second : Term (signature sig declaration) Γ .term}
    (same : activate declaration first = activate declaration second) : first = second :=
  (Args.cons.inj (eq_of_heq (Term.op.inj same).2)).1

def plug (declaration : V → MetaArity sig) : {Γ Δ : Ctx sig} → Context Γ Δ →
    Term (signature sig declaration) Δ .term → Term (signature sig declaration) Γ .term
  | _, _, .hole, term => term
  | _, _, .appLeft inner argument, term => app declaration (plug declaration inner term) (encode declaration argument)
  | _, _, .appRight function inner, term => app declaration (encode declaration function) (plug declaration inner term)
  | _, _, .underLam inner, term => lam declaration (plug declaration inner term)
  | _, _, .underActivate inner, term => activate declaration (plug declaration inner term)

theorem plug_encode (declaration : V → MetaArity sig) {Γ Δ : Ctx sig} (context : Context Γ Δ)
    (term : Term sig Δ .term) : plug declaration context (encode declaration term) = encode declaration (context.plug term) := by
  induction context with
  | hole => rfl
  | appLeft inner argument ih => exact congrArg (fun value => app declaration value (encode declaration argument)) (ih term)
  | appRight function inner ih => exact congrArg (app declaration (encode declaration function)) (ih term)
  | underLam inner ih => exact congrArg (lam declaration) (ih term)
  | underActivate inner ih => exact congrArg (activate declaration) (ih term)

theorem instantiate_plug (change : Assignment declaration next) {Γ Δ : Ctx sig} (context : Context Γ Δ)
    (term : Term (signature sig declaration) Δ .term) :
    instantiate change (plug declaration context term) = plug next context (instantiate change term) := by
  induction context with
  | hole => rfl
  | appLeft inner argument ih =>
      change app next (instantiate change (plug declaration inner term))
        (instantiate change (encode declaration argument)) = _
      rw [ih, Rigid.instantiate_include]
      rfl
  | appRight function inner ih =>
      change app next (instantiate change (encode declaration function))
        (instantiate change (plug declaration inner term)) = _
      rw [ih, Rigid.instantiate_include]
      rfl
  | underLam inner ih => exact congrArg (lam next) (ih term)
  | underActivate inner ih => exact congrArg (activate next) (ih term)

theorem instantiate_inst (change : Assignment declaration next) {Γ : Ctx sig}
    (body : Term (signature sig declaration) (.term :: Γ) .term)
    (argument : Term (signature sig declaration) Γ .term) :
    instantiate change (inst body argument) = inst (instantiate change body) (instantiate change argument) := by
  simp only [Mettapedia.OSLF.Binding.inst, Mettapedia.OSLF.Binding.ContextualFamily.instantiate_bind]
  congr 1
  funext sort position
  cases position <;> rfl

theorem plug_injective {Γ Δ : Ctx sig} (context : Context Γ Δ) : Function.Injective (plug declaration context) := by
  induction context with
  | hole => exact Function.injective_id
  | appLeft inner argument ih => exact fun _ _ same => ih (app_inj same).1
  | appRight function inner ih => exact fun _ _ same => ih (app_inj same).2
  | underLam inner ih => exact fun _ _ same => ih (lam_inj same)
  | underActivate inner ih => exact fun _ _ same => ih (activate_inj same)

theorem plug_pattern {Γ Δ : Ctx sig} (context : Context Γ Δ)
    (term : Term (signature sig declaration) Δ .term) (patterned : ContextualPatternFragment.Pattern sig declaration term) :
    ContextualPatternFragment.Pattern sig declaration (plug declaration context term) := by
  induction context with
  | hole => exact patterned
  | appLeft inner argument ih =>
      exact .rigid (S := sig) Op.app _ (.cons _ _ (ih term patterned)
        (.cons _ _ (ContextualPatternFragment.rigid_inclusion_pattern declaration argument) .nil))
  | appRight function inner ih =>
      exact .rigid (S := sig) Op.app _ (.cons _ _ (ContextualPatternFragment.rigid_inclusion_pattern declaration function)
        (.cons _ _ (ih term patterned) .nil))
  | underLam inner ih => exact .rigid (S := sig) Op.lam _ (.cons _ _ (ih term patterned) .nil)
  | underActivate inner ih => exact .rigid (S := sig) Op.activate _ (.cons _ _ (ih term patterned) .nil)

inductive Kind where
  | beta | activation
  deriving DecidableEq

def kind {Γ : Ctx sig} : Redex Γ → Kind
  | .beta _ _ => .beta
  | .activation _ => .activation

/-- The activation schema uses the ambient-context declaration (true).
The other declaration is unused by that rule; it imposes no closure condition. -/
def locals (context : Ctx sig) : Bool → MetaArity sig
  | false => (.term :: context, .term)
  | true => (context, .term)
def captures : Empty → MetaArity sig := fun impossible => nomatch impossible
abbrev raw (context : Ctx sig) := ContextualActivatedStep.source (locals context) captures
abbrev active (context : Ctx sig) := ContextualActivatedStep.target (locals context) captures

def rootInput (Δ : Ctx sig) : Kind → Term (signature sig (raw Δ)) Δ .term
  | .beta => app (raw Δ) (lam (raw Δ) (generator (raw Δ) (.inl false))) (generator (raw Δ) (.inl true))
  | .activation => activate (raw Δ) (quote (raw Δ) (generator (raw Δ) (.inl true)))
def rootOutput (Δ : Ctx sig) : Kind → Term (signature sig (raw Δ)) Δ .term
  | .beta => inst (generator (raw Δ) (.inl false)) (generator (raw Δ) (.inl true))
  | .activation => generator (raw Δ) (.inl true)

def lhs {Γ Δ : Ctx sig} (selected : Kind) (context : Context Γ Δ) := plug (raw Δ) context (rootInput Δ selected)
def rhs {Γ Δ : Ctx sig} (selected : Kind) (context : Context Γ Δ) := plug (raw Δ) context (rootOutput Δ selected)
def rule {Γ Δ : Ctx sig} (selected : Kind) (context : Context Γ Δ) : RuleInstance (Term (signature sig (raw Δ)) Γ .term) :=
  ⟨[lhs selected context], [], [], [], [rhs selected context]⟩

def selection : Selection Nat := ⟨[0], [], [1]⟩
def occupied : Finset Nat := ∅
def rows (Δ : Ctx sig) {Γ : Ctx sig} (input : Term sig Γ .term) (_ : Nat) :
    ContextualStoredRows.Row (locals Δ) captures Γ .term := .shared (encode captures input)
def before (Γ : Ctx sig) : Configuration (Term (signature sig captures) Γ .term) Nat := ⟨[], {0}⟩
def openTerm {Γ Δ : Ctx sig} (term : Term (signature sig (raw Δ)) Γ .term) :=
  ContextualFreshening.termAt (locals Δ) captures
    (ContextualActivationScopes.scopeAt occupied (ContextualActivationScopes.rulePort selection)) term
def outputs {Γ Δ : Ctx sig} (selected : Kind) (context : Context Γ Δ) (_ : Nat) := openTerm (rhs selected context)
def problem {Γ Δ : Ctx sig} (selected : Kind) (context : Context Γ Δ) (input : Term sig Γ .term) :=
  ContextualActivatedStep.problem (locals Δ) captures occupied selection (rule selected context) (rows Δ input) (before Γ)

theorem problem_eq {Γ Δ : Ctx sig} (selected : Kind) (context : Context Γ Δ) (input : Term sig Γ .term) :
    problem selected context input = [(openTerm (lhs selected context), encode (active Δ) input)] := by
  change [(openTerm (lhs selected context),
    instantiate (ContextualFreshening.assignment (locals Δ) captures _)
      (instantiate (ContextualSelectionViews.capturedSource (locals Δ) captures) (encode captures input)))] = _
  rw [Rigid.instantiate_include, Rigid.instantiate_include]

def model {Δ : Ctx sig} (redex : Redex Δ) : Assignment (active Δ) captures
  | .inl ⟨_, false⟩ => match redex with
    | .beta body _ => encode captures body
    | .activation code => encode captures (weaken code)
  | .inl ⟨_, true⟩ => match redex with
    | .beta _ argument => encode captures argument
    | .activation code => encode captures code
  | .inr impossible => nomatch impossible

theorem opened_lhs {Γ Δ : Ctx sig} (selected : Kind) (context : Context Γ Δ) :
    openTerm (lhs selected context) = plug (active Δ) context
      (match selected with
      | .beta => app (active Δ) (lam (active Δ) (generator (active Δ) (.inl ⟨1, false⟩)))
          (generator (active Δ) (.inl ⟨1, true⟩))
      | .activation => activate (active Δ) (quote (active Δ) (generator (active Δ) (.inl ⟨1, true⟩)))) := by
  unfold openTerm lhs ContextualFreshening.termAt
  rw [instantiate_plug]
  cases selected <;> simp only [rootInput, app, lam, activate, quote, instantiate, instantiateArgs, instantiate_generator] <;> rfl

theorem opened_rhs {Γ Δ : Ctx sig} (selected : Kind) (context : Context Γ Δ) :
    openTerm (rhs selected context) = plug (active Δ) context
      (match selected with
      | .beta => inst (generator (active Δ) (.inl ⟨1, false⟩)) (generator (active Δ) (.inl ⟨1, true⟩))
      | .activation => generator (active Δ) (.inl ⟨1, true⟩)) := by
  unfold openTerm rhs ContextualFreshening.termAt
  rw [instantiate_plug]
  cases selected
  · simp only [rootOutput, instantiate_inst, instantiate_generator]; rfl
  · simp only [rootOutput, instantiate_generator]; rfl

theorem input_model {Γ Δ : Ctx sig} (context : Context Γ Δ) (redex : Redex Δ) :
    ContextualFrameUnifier.Models (model redex) (problem (kind redex) context (context.plug redex.source)) := by
  intro equation member
  rw [problem_eq] at member
  have only := List.mem_singleton.mp member
  subst equation
  simp only [opened_lhs, instantiate_plug, Rigid.instantiate_include]
  cases redex with
  | beta body argument =>
      simp only [kind, app, lam, instantiate, instantiateArgs, instantiate_generator, model]
      exact plug_encode captures context (QuotedLambda.app (QuotedLambda.lam body) argument)
  | activation code =>
      simp only [kind, activate, quote, instantiate, instantiateArgs, instantiate_generator, model]
      exact plug_encode captures context (QuotedLambda.activate (QuotedLambda.quote code))

theorem input_pattern {Γ Δ : Ctx sig} (selected : Kind) (context : Context Γ Δ) (input : Term sig Γ .term) :
    ContextualPatternFragment.ProblemPattern (ContextualResidual.observeProblem (problem selected context input)) := by
  rw [problem_eq]
  intro equation member
  have only := List.mem_singleton.mp member
  subst equation
  constructor
  · change ContextualPatternFragment.Pattern sig (active Δ) (openTerm (lhs selected context))
    rw [opened_lhs]
    apply plug_pattern
    cases selected with
    | beta =>
        exact .rigid (S := sig) Op.app _
          (.cons _ _ (.rigid (S := sig) Op.lam _ (.cons _ _
            (ContextualPatternFragment.generator_pattern _) .nil))
            (.cons _ _ (ContextualPatternFragment.generator_pattern _) .nil))
    | activation =>
        exact .rigid (S := sig) Op.activate _ (.cons _ _
          (.rigid (S := sig) Op.quote _ (.cons _ _ (ContextualPatternFragment.generator_pattern _) .nil)) .nil)
  · exact ContextualPatternFragment.rigid_inclusion_pattern _ input

theorem admitted {Γ Δ : Ctx sig} (selected : Kind) (context : Context Γ Δ) (input : Term sig Γ .term) :
    ContextualGuardedStep.Requirements (locals Δ) captures occupied selection
      (rule selected context) (rows Δ input) (before Γ) (outputs selected context) := by
  refine ⟨by decide, by decide, rfl, rfl, rfl, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · change ({0} : Finset Nat) ⊆ {0}; exact Finset.Subset.refl _
    · change (∅ : Finset Nat) ⊆ {0}; exact Finset.empty_subset _
    · change Disjoint ({0} : Finset Nat) ∅; exact Finset.disjoint_empty_right _
    · change Disjoint ({1} : Finset Nat) {0}; decide
    · intro check member; cases member
  · intro check member; cases member

local instance : DecidableEq sig.Srt := inferInstanceAs (DecidableEq Srt)
local instance (sort : sig.Srt) : DecidableEq (sig.Op sort) := inferInstanceAs (DecidableEq (Op sort))

/-- Arbitrary mixed source terms, including quotations containing captures,
give actual completed runs in the established pattern fragment. -/
theorem completed_run {Γ Δ : Ctx sig} (context : Context Γ Δ) (redex : Redex Δ) :
    ∃ fuel update, ContextualTransportedActivation.FromRun (locals Δ) captures fuel occupied selection
      (rule (kind redex) context) (rows Δ (context.plug redex.source)) (before Γ) (outputs (kind redex) context) update := by
  apply (ContextualTransportedActivation.semantic_admission_iff_completed_run
    (locals Δ) captures (input_pattern _ context _)).mp
  exact ⟨admitted _ context _, ContextualFrameUnifier.solvable_of_model (input_model context redex)⟩

theorem output_for_every_solution {Γ Δ : Ctx sig} (context : Context Γ Δ) (redex : Redex Δ)
    {Future : Type} {future : Future → MetaArity sig} (candidate : Assignment (active Δ) future)
    (solved : ContextualFrameUnifier.Models candidate (problem (kind redex) context (context.plug redex.source))) :
    instantiate candidate (outputs (kind redex) context 1) = encode future (context.plug redex.target) := by
  have matched := solved _ (by rw [problem_eq]; exact List.mem_singleton_self _)
  change instantiate candidate (openTerm (lhs (kind redex) context)) =
    instantiate candidate (encode (active Δ) _) at matched
  rw [opened_lhs, instantiate_plug, Rigid.instantiate_include] at matched
  have root := plug_injective context (matched.trans (plug_encode future context redex.source).symm)
  cases redex with
  | beta body argument =>
      change app future (lam future (instantiate candidate (generator (active Δ) (.inl ⟨1, false⟩))))
        (instantiate candidate (generator (active Δ) (.inl ⟨1, true⟩))) =
          app future (lam future (encode future body)) (encode future argument) at root
      have both := app_inj root
      have body_eq := lam_inj both.1
      change instantiate candidate (openTerm (rhs .beta context)) = _
      rw [opened_rhs, instantiate_plug, instantiate_inst, body_eq, both.2, ← Rigid.include_inst, plug_encode]
      rfl
  | activation code =>
      change activate future (quote future (instantiate candidate (generator (active Δ) (.inl ⟨1, true⟩)))) =
        activate future (quote future (encode future code)) at root
      have code_eq := quote_inj (activate_inj root)
      change instantiate candidate (openTerm (rhs .activation context)) = _
      rw [opened_rhs, instantiate_plug, code_eq, plug_encode]
      rfl

theorem encode_app_recovers {Γ : Ctx sig} :
    ∀ (term : Term sig Γ .term) (function argument : Term (signature sig declaration) Γ .term),
      app declaration function argument = encode declaration term →
      ∃ (f a : Term sig Γ .term), term = QuotedLambda.app f a ∧
        function = encode declaration f ∧ argument = encode declaration a
  | .var _, _, _, same => by cases same
  | .op .app (.cons f (.cons a .nil)), _, _, same => ⟨f, a, rfl, app_inj same⟩
  | .op .lam _, _, _, same => by cases (Term.op.inj same).1
  | .op .quote _, _, _, same => by cases (Term.op.inj same).1
  | .op .activate _, _, _, same => by cases (Term.op.inj same).1

theorem encode_lam_recovers {Γ : Ctx sig} :
    ∀ (term : Term sig Γ .term) (body : Term (signature sig declaration) (.term :: Γ) .term),
      lam declaration body = encode declaration term →
      ∃ b : Term sig (.term :: Γ) .term, term = QuotedLambda.lam b ∧ body = encode declaration b
  | .var _, _, same => by cases same
  | .op .app _, _, same => by cases (Term.op.inj same).1
  | .op .lam (.cons body .nil), _, same => ⟨body, rfl, lam_inj same⟩
  | .op .quote _, _, same => by cases (Term.op.inj same).1
  | .op .activate _, _, same => by cases (Term.op.inj same).1

theorem encode_quote_recovers {Γ : Ctx sig} :
    ∀ (term : Term sig Γ .term) (code : Term (signature sig declaration) Γ .term),
      quote declaration code = encode declaration term →
      ∃ body : Term sig Γ .term, term = QuotedLambda.quote body ∧ code = encode declaration body
  | .var _, _, same => by cases same
  | .op .app _, _, same => by cases (Term.op.inj same).1
  | .op .lam _, _, same => by cases (Term.op.inj same).1
  | .op .quote (.cons body .nil), _, same => ⟨body, rfl, quote_inj same⟩
  | .op .activate _, _, same => by cases (Term.op.inj same).1

theorem encode_activate_recovers {Γ : Ctx sig} :
    ∀ (term : Term sig Γ .term) (name : Term (signature sig declaration) Γ .term),
      activate declaration name = encode declaration term →
      ∃ body : Term sig Γ .term, term = QuotedLambda.activate body ∧ name = encode declaration body
  | .var _, _, same => by cases same
  | .op .app _, _, same => by cases (Term.op.inj same).1
  | .op .lam _, _, same => by cases (Term.op.inj same).1
  | .op .quote _, _, same => by cases (Term.op.inj same).1
  | .op .activate (.cons body .nil), _, same => ⟨body, rfl, activate_inj same⟩

theorem plug_recovers {Γ Δ : Ctx sig} (context : Context Γ Δ)
    (value : Term (signature sig declaration) Δ .term) (term : Term sig Γ .term)
    (same : plug declaration context value = encode declaration term) :
    ∃ inner : Term sig Δ .term, term = context.plug inner ∧ value = encode declaration inner := by
  induction context with
  | hole => exact ⟨term, rfl, same⟩
  | appLeft context argument ih =>
      obtain ⟨f, a, rfl, first, second⟩ := encode_app_recovers term _ _ same
      have argument_eq := Rigid.include_injective declaration argument a second
      obtain ⟨inner, rfl, recovered⟩ := ih value f first
      exact ⟨inner, congrArg (QuotedLambda.app (context.plug inner)) argument_eq.symm, recovered⟩
  | appRight function context ih =>
      obtain ⟨f, a, rfl, first, second⟩ := encode_app_recovers term _ _ same
      have function_eq := Rigid.include_injective declaration function f first
      obtain ⟨inner, rfl, recovered⟩ := ih value a second
      exact ⟨inner, congrArg (fun head => QuotedLambda.app head (context.plug inner)) function_eq.symm, recovered⟩
  | underLam context ih =>
      obtain ⟨b, rfl, matched⟩ := encode_lam_recovers term _ same
      obtain ⟨inner, source_eq, decoded⟩ := ih value b matched
      exact ⟨inner, congrArg QuotedLambda.lam source_eq, decoded⟩
  | underActivate context ih =>
      obtain ⟨b, rfl, matched⟩ := encode_activate_recovers term _ same
      obtain ⟨inner, source_eq, decoded⟩ := ih value b matched
      exact ⟨inner, congrArg QuotedLambda.activate source_eq, decoded⟩

theorem model_recovers_source {Γ Δ : Ctx sig} (selected : Kind) (context : Context Γ Δ) (input : Term sig Γ .term)
    {Future : Type} {future : Future → MetaArity sig} (candidate : Assignment (active Δ) future)
    (solved : ContextualFrameUnifier.Models candidate (problem selected context input)) :
    ∃ redex : Redex Δ, kind redex = selected ∧ input = context.plug redex.source := by
  have matched := solved _ (by rw [problem_eq]; exact List.mem_singleton_self _)
  change instantiate candidate (openTerm (lhs selected context)) = instantiate candidate (encode (active Δ) input) at matched
  rw [opened_lhs, instantiate_plug, Rigid.instantiate_include] at matched
  obtain ⟨inner, input_eq, root_eq⟩ := plug_recovers context _ input matched
  cases selected with
  | beta =>
      obtain ⟨function, argument, shape, function_eq, _⟩ := encode_app_recovers inner _ _ root_eq
      obtain ⟨body, head, _⟩ := encode_lam_recovers function _ function_eq
      exact ⟨.beta body argument, rfl, by rw [input_eq, shape, head]; rfl⟩
  | activation =>
      obtain ⟨name, shape, name_eq⟩ := encode_activate_recovers inner _ root_eq
      obtain ⟨code, body, _⟩ := encode_quote_recovers name _ name_eq
      exact ⟨.activation code, rfl, by rw [input_eq, shape, body]; rfl⟩

def Executes {Γ : Ctx sig} (input output : Term sig Γ .term) : Prop :=
  ∃ (selected : Kind) (Δ : Ctx sig) (context : Context Γ Δ) (fuel : Nat)
    (update : ContextualFrameUpdate.Update (ContextualResidual.observeProblem (problem selected context input))),
    ContextualTransportedActivation.FromRun (locals Δ) captures fuel occupied selection
      (rule selected context) (rows Δ input) (before Γ) (outputs selected context) update ∧
      instantiate update.answer (outputs selected context 1) = encode update.declaration output

/-- Actual completed pattern-worklist firings preserve and reflect every
mixed source reduction at the declared active contexts. -/
theorem source_step_iff_executes {Γ : Ctx sig} (input output : Term sig Γ .term) :
    QuotedLambda.Step Γ input output ↔ Executes input output := by
  constructor
  · intro step
    obtain ⟨Δ, context, redex, rfl, rfl⟩ := QuotedLambda.step_iff_context_redex.mp step
    obtain ⟨fuel, update, returned⟩ := completed_run context redex
    refine ⟨kind redex, Δ, context, fuel, update, returned, ?_⟩
    exact output_for_every_solution context redex update.answer
      ((ContextualResidual.models_observeProblem _ _).mp (update.completed returned.empty))
  · rintro ⟨selected, Δ, context, fuel, update, returned, observed⟩
    have solved := (ContextualResidual.models_observeProblem _ _).mp (update.completed returned.empty)
    obtain ⟨redex, rfl, rfl⟩ := model_recovers_source selected context input update.answer solved
    have result := output_for_every_solution context redex update.answer solved
    have same := Rigid.include_injective update.declaration output (context.plug redex.target) (observed.symm.trans result)
    rw [same]
    exact context.congr_step redex.step

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.QuotedLambdaExecution
