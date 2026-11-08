import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualTransportedActivation
import Mettapedia.OSLF.Syntax.LambdaContextualRung

/-!
# Intrinsic lambda application through contextual transforms

The source is the independent four-rule, context-indexed lambda reduction
relation. Its terms embed as rigid constructors in the existing contextual
term family. The beta schema has two private declarations: its body depends
on the bound argument and the ambient variables; its argument depends only
on the ambient variables. Its output is contextual application of the first
declaration to the second, not a call to a source evaluator.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LambdaComparison

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open LambdaContextualRung (sig Srt Op appT lamT)

variable {V W : Type} (declaration : V → MetaArity sig)

def app {Γ : Ctx sig} (function argument : Term (signature sig declaration) Γ .term) :
    Term (signature sig declaration) Γ .term :=
  .op (.inl .app) (.cons function (.cons argument .nil))

def lam {Γ : Ctx sig} (body : Term (signature sig declaration) (.term :: Γ) .term) :
    Term (signature sig declaration) Γ .term :=
  .op (.inl .lam) (.cons body .nil)

/- Only rigid source constructors are inserted; object variables retain
their original intrinsic binding positions. -/
mutual
def encode : {Γ : Ctx sig} → {sort : Srt} → Term sig Γ sort → Term (signature sig declaration) Γ sort
  | _, _, .var position => .var position
  | _, _, .op operator arguments => .op (.inl operator) (encodeArgs arguments)

def encodeArgs : {Γ : Ctx sig} → {arities : List (MetaArity sig)} →
    Args sig arities Γ → Args (signature sig declaration) arities Γ
  | _, _, .nil => .nil
  | _, _, .cons head tail => .cons (encode head) (encodeArgs tail)
end

theorem encode_rename {Γ Δ : Ctx sig} (rho : Ren sig Γ Δ) :
    ∀ term : Term sig Γ .term,
      encode declaration (rename rho term) = rename (S := signature sig declaration) rho (encode declaration term)
  | .var _ => rfl
  | .op .app (.cons function (.cons argument .nil)) => by
      simp only [Mettapedia.OSLF.Binding.rename, renameArgs, liftRen, encode, encodeArgs,
        encode_rename rho function, encode_rename rho argument]
  | .op .lam (.cons body .nil) => by
      change lam declaration (encode declaration (rename (liftRen rho [.term]) body)) =
        lam declaration (rename (S := signature sig declaration) (liftRen rho [.term]) (encode declaration body))
      rw [encode_rename (liftRen rho [.term]) body]
termination_by term => termSize term
decreasing_by all_goals (simp only [Mettapedia.OSLF.Binding.termSize, Mettapedia.OSLF.Binding.argsSize]; omega)

theorem encode_bind {Γ Δ : Ctx sig} (sigma : Sub sig Γ Δ)
    (tau : Sub (signature sig declaration) Γ Δ)
    (compatible : ∀ sort position, tau sort position = encode declaration (sigma sort position)) :
    ∀ term : Term sig Γ .term,
      encode declaration (bind sigma term) = bind tau (encode declaration term)
  | .var position => by simpa only [Mettapedia.OSLF.Binding.bind, encode] using (compatible _ position).symm
  | .op .app (.cons function (.cons argument .nil)) => by
      change app declaration (encode declaration (bind sigma function))
          (encode declaration (bind sigma argument)) =
        app declaration (bind tau (encode declaration function)) (bind tau (encode declaration argument))
      rw [encode_bind sigma tau compatible function,
        encode_bind sigma tau compatible argument]
  | .op .lam (.cons body .nil) => by
      change lam declaration (encode declaration (bind (liftSub sigma [.term]) body)) =
        lam declaration (bind (liftSub tau [.term]) (encode declaration body))
      congr 1
      apply encode_bind (liftSub sigma [.term]) (liftSub tau [.term]) _ body
      intro sort position
      cases position with
      | zero => rfl
      | succ position =>
          cases sort
          simp only [liftSub, weaken, compatible, encode_rename]
termination_by term => termSize term
decreasing_by all_goals (simp only [Mettapedia.OSLF.Binding.termSize, Mettapedia.OSLF.Binding.argsSize]; omega)

theorem encode_inst {Γ : Ctx sig} (body : Term sig (.term :: Γ) .term)
    (argument : Term sig Γ .term) :
    encode declaration (inst body argument) =
      inst (encode declaration body) (encode declaration argument) := by
  apply encode_bind declaration (extend argument) (extend (encode declaration argument)) _ body
  intro sort position
  cases position <;> simp only [extend, encode]

variable {declaration} {next : W → MetaArity sig}

theorem instantiate_encode (change : Assignment declaration next) :
    ∀ {Γ : Ctx sig} (term : Term sig Γ .term),
      instantiate change (encode declaration term) = encode next term
  | _, .var _ => rfl
  | _, .op .app (.cons function (.cons argument .nil)) => by
      change app next (instantiate change (encode declaration function))
          (instantiate change (encode declaration argument)) = _
      rw [instantiate_encode change function, instantiate_encode change argument]
      rfl
  | _, .op .lam (.cons body .nil) => by
      change lam next (instantiate change (encode declaration body)) = _
      rw [instantiate_encode change body]
      rfl
termination_by _ term => termSize term
decreasing_by all_goals (simp only [Mettapedia.OSLF.Binding.termSize, Mettapedia.OSLF.Binding.argsSize]; omega)

theorem encode_pattern : ∀ {Γ : Ctx sig} (term : Term sig Γ .term),
    ContextualPatternFragment.Pattern sig declaration (encode declaration term)
  | _, .var position => .object position
  | _, .op .app (.cons function (.cons argument .nil)) =>
      .rigid (S := sig) Op.app _ (.cons _ _ (encode_pattern function) (.cons _ _ (encode_pattern argument) .nil))
  | _, .op .lam (.cons body .nil) => .rigid (S := sig) Op.lam _ (.cons _ _ (encode_pattern body) .nil)
termination_by _ term => termSize term
decreasing_by all_goals (simp only [Mettapedia.OSLF.Binding.termSize, Mettapedia.OSLF.Binding.argsSize]; omega)

theorem instantiate_inst (change : Assignment declaration next) {Γ : Ctx sig}
    (body : Term (signature sig declaration) (.term :: Γ) .term)
    (argument : Term (signature sig declaration) Γ .term) :
    instantiate change (inst body argument) = inst (instantiate change body) (instantiate change argument) := by
  simp only [Mettapedia.OSLF.Binding.inst, Mettapedia.OSLF.Binding.ContextualFamily.instantiate_bind]
  congr 1
  funext sort position
  cases position <;> rfl

open LambdaContextualRung (Context)

theorem app_inj {Γ : Ctx sig} {first second third fourth : Term (signature sig declaration) Γ .term}
    (same : app declaration first second = app declaration third fourth) :
    first = third ∧ second = fourth := by
  have fields := Args.cons.inj (eq_of_heq (Term.op.inj same).2)
  exact ⟨fields.1, (Args.cons.inj fields.2).1⟩

theorem lam_inj {Γ : Ctx sig} {first second : Term (signature sig declaration) (.term :: Γ) .term}
    (same : lam declaration first = lam declaration second) : first = second := by
  exact (Args.cons.inj (eq_of_heq (Term.op.inj same).2)).1

def plug (declaration : V → MetaArity sig) : {Γ Δ : Ctx sig} → Context Γ Δ →
    Term (signature sig declaration) Δ .term → Term (signature sig declaration) Γ .term
  | _, _, .hole, term => term
  | _, _, .appLeft inner argument, term => app declaration (plug declaration inner term) (encode declaration argument)
  | _, _, .appRight function inner, term => app declaration (encode declaration function) (plug declaration inner term)
  | _, _, .underLam inner, term => lam declaration (plug declaration inner term)

theorem plug_encode (declaration : V → MetaArity sig) {Γ Δ : Ctx sig} (context : Context Γ Δ)
    (term : Term sig Δ .term) : plug declaration context (encode declaration term) =
      encode declaration (context.plug term) := by
  induction context with
  | hole => rfl
  | appLeft inner argument ih => exact congrArg (fun value => app declaration value (encode declaration argument)) (ih term)
  | appRight function inner ih => exact congrArg (app declaration (encode declaration function)) (ih term)
  | underLam inner ih => exact congrArg (lam declaration) (ih term)

theorem instantiate_plug (change : Assignment declaration next) {Γ Δ : Ctx sig} (context : Context Γ Δ)
    (term : Term (signature sig declaration) Δ .term) :
    instantiate change (plug declaration context term) = plug next context (instantiate change term) := by
  induction context with
  | hole => rfl
  | appLeft inner argument ih =>
      change app next (instantiate change (plug declaration inner term))
        (instantiate change (encode declaration argument)) = _
      rw [ih, instantiate_encode]
      rfl
  | appRight function inner ih =>
      change app next (instantiate change (encode declaration function))
        (instantiate change (plug declaration inner term)) = _
      rw [ih, instantiate_encode]
      rfl
  | underLam inner ih => exact congrArg (lam next) (ih term)

theorem plug_injective {Γ Δ : Ctx sig} (context : Context Γ Δ) :
    Function.Injective (plug declaration context) := by
  induction context with
  | hole => exact Function.injective_id
  | appLeft inner argument ih => exact fun _ _ same => ih (app_inj same).1
  | appRight function inner ih => exact fun _ _ same => ih (app_inj same).2
  | underLam inner ih => exact fun _ _ same => ih (lam_inj same)

theorem plug_pattern {Γ Δ : Ctx sig} (context : Context Γ Δ)
    (term : Term (signature sig declaration) Δ .term)
    (patterned : ContextualPatternFragment.Pattern sig declaration term) :
    ContextualPatternFragment.Pattern sig declaration (plug declaration context term) := by
  induction context with
  | hole => exact patterned
  | appLeft inner argument ih =>
      exact .rigid (S := sig) Op.app _ (.cons _ _ (ih term patterned) (.cons _ _ (encode_pattern argument) .nil))
  | appRight function inner ih =>
      exact .rigid (S := sig) Op.app _ (.cons _ _ (encode_pattern function) (.cons _ _ (ih term patterned) .nil))
  | underLam inner ih => exact .rigid (S := sig) Op.lam _ (.cons _ _ (ih term patterned) .nil)

def locals (context : Ctx sig) : Bool → MetaArity sig
  | false => (.term :: context, .term)
  | true => (context, .term)

def captures : Empty → MetaArity sig := fun impossible => nomatch impossible
abbrev raw (context : Ctx sig) := ContextualActivatedStep.source (locals context) captures
abbrev active (context : Ctx sig) := ContextualActivatedStep.target (locals context) captures

def lhs {Γ Δ : Ctx sig} (context : Context Γ Δ) : Term (signature sig (raw Δ)) Γ .term :=
  plug (raw Δ) context (app (raw Δ) (lam (raw Δ) (generator (raw Δ) (.inl false)))
    (generator (raw Δ) (.inl true)))

def rhs {Γ Δ : Ctx sig} (context : Context Γ Δ) : Term (signature sig (raw Δ)) Γ .term :=
  plug (raw Δ) context (inst (generator (raw Δ) (.inl false)) (generator (raw Δ) (.inl true)))

/-- One schema per source evaluation context; neither the body nor the
argument nor its computed reduct is baked into this rule. -/
def rule {Γ Δ : Ctx sig} (context : Context Γ Δ) : RuleInstance (Term (signature sig (raw Δ)) Γ .term) :=
  ⟨[lhs context], [], [], [], [rhs context]⟩

def selection : Selection Nat := ⟨[0], [], [1]⟩
def occupied : Finset Nat := ∅

def rows (Δ : Ctx sig) {Γ : Ctx sig} (input : Term sig Γ .term) (_ : Nat) :
    ContextualStoredRows.Row (locals Δ) captures Γ .term := .shared (encode captures input)

def before (Γ : Ctx sig) : Configuration (Term (signature sig captures) Γ .term) Nat := ⟨[], {0}⟩

def openTerm {Γ Δ : Ctx sig} (term : Term (signature sig (raw Δ)) Γ .term) :=
  ContextualFreshening.termAt (locals Δ) captures
    (ContextualActivationScopes.scopeAt occupied (ContextualActivationScopes.rulePort selection)) term

def outputs {Γ Δ : Ctx sig} (context : Context Γ Δ) (_ : Nat) : Term (signature sig (active Δ)) Γ .term :=
  openTerm (rhs context)

def problem {Γ Δ : Ctx sig} (context : Context Γ Δ) (input : Term sig Γ .term) :=
  ContextualActivatedStep.problem (locals Δ) captures occupied selection (rule context) (rows Δ input) (before Γ)

theorem problem_eq {Γ Δ : Ctx sig} (context : Context Γ Δ) (input : Term sig Γ .term) :
    problem context input = [(openTerm (lhs context), encode (active Δ) input)] := by
  change [(openTerm (lhs context),
    instantiate (ContextualFreshening.assignment (locals Δ) captures _)
      (instantiate (ContextualSelectionViews.capturedSource (locals Δ) captures) (encode captures input)))] = _
  rw [instantiate_encode, instantiate_encode]

def model {Δ : Ctx sig} (body : Term sig (.term :: Δ) .term) (argument : Term sig Δ .term) :
    Assignment (active Δ) captures
  | .inl ⟨_, false⟩ => encode captures body
  | .inl ⟨_, true⟩ => encode captures argument
  | .inr impossible => nomatch impossible

theorem opened_lhs {Γ Δ : Ctx sig} (context : Context Γ Δ) :
    openTerm (lhs context) = plug (active Δ) context
      (app (active Δ) (lam (active Δ) (generator (active Δ) (.inl ⟨1, false⟩)))
        (generator (active Δ) (.inl ⟨1, true⟩))) := by
  unfold openTerm lhs ContextualFreshening.termAt
  rw [instantiate_plug]
  simp only [app, lam, instantiate, instantiateArgs, instantiate_generator]
  rfl

theorem opened_rhs {Γ Δ : Ctx sig} (context : Context Γ Δ) :
    openTerm (rhs context) = plug (active Δ) context
      (inst (generator (active Δ) (.inl ⟨1, false⟩)) (generator (active Δ) (.inl ⟨1, true⟩))) := by
  unfold openTerm rhs ContextualFreshening.termAt
  rw [instantiate_plug, instantiate_inst, instantiate_generator, instantiate_generator]
  rfl

theorem input_model {Γ Δ : Ctx sig} (context : Context Γ Δ)
    (body : Term sig (.term :: Δ) .term) (argument : Term sig Δ .term) :
    ContextualFrameUnifier.Models (model body argument)
      (problem context (context.plug (appT (lamT body) argument))) := by
  intro equation member
  rw [problem_eq] at member
  have only := List.mem_singleton.mp member
  subst equation
  simp only [opened_lhs, instantiate_plug, app, lam, instantiate, instantiateArgs,
    instantiate_generator, model, instantiate_encode]
  exact plug_encode captures context (appT (lamT body) argument)

theorem input_pattern {Γ Δ : Ctx sig} (context : Context Γ Δ) (input : Term sig Γ .term) :
    ContextualPatternFragment.ProblemPattern (ContextualResidual.observeProblem (problem context input)) := by
  rw [problem_eq]
  intro equation member
  have only := List.mem_singleton.mp member
  subst equation
  constructor
  · change ContextualPatternFragment.Pattern sig (active Δ) (openTerm (lhs context))
    rw [opened_lhs]
    apply plug_pattern
    exact .rigid (S := sig) Op.app _
      (.cons _ _ (.rigid (S := sig) Op.lam _ (.cons _ _
        (ContextualPatternFragment.generator_pattern _) .nil))
        (.cons _ _ (ContextualPatternFragment.generator_pattern _) .nil))
  · exact encode_pattern input

theorem admitted {Γ Δ : Ctx sig} (context : Context Γ Δ) (input : Term sig Γ .term) :
    ContextualGuardedStep.Requirements (locals Δ) captures occupied selection
      (rule context) (rows Δ input) (before Γ) (outputs context) := by
  refine ⟨by decide, by decide, rfl, rfl, rfl, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · change ({0} : Finset Nat) ⊆ {0}; exact Finset.Subset.refl _
    · change (∅ : Finset Nat) ⊆ {0}; exact Finset.empty_subset _
    · change Disjoint ({0} : Finset Nat) ∅; exact Finset.disjoint_empty_right _
    · change Disjoint ({1} : Finset Nat) {0}; decide
    intro check member
    cases member
  · intro check member
    cases member

local instance : DecidableEq sig.Srt := inferInstanceAs (DecidableEq Srt)
local instance (sort : sig.Srt) : DecidableEq (sig.Op sort) := by
  cases sort
  intro first second
  cases first <;> cases second
  · exact isTrue rfl
  · exact isFalse (by intro same; cases same)
  · exact isFalse (by intro same; cases same)
  · exact isTrue rfl

/-- Every source beta contraction, at any one-hole context and with arbitrary
body and argument, constructs a completed run of the existing worklist. -/
theorem completed_run {Γ Δ : Ctx sig} (context : Context Γ Δ)
    (body : Term sig (.term :: Δ) .term) (argument : Term sig Δ .term) :
    ∃ fuel update, ContextualTransportedActivation.FromRun (locals Δ) captures fuel occupied selection
      (rule context) (rows Δ (context.plug (appT (lamT body) argument))) (before Γ) (outputs context) update := by
  apply (ContextualTransportedActivation.semantic_admission_iff_completed_run
    (locals Δ) captures (input_pattern context _)).mp
  exact ⟨admitted context _, ContextualFrameUnifier.solvable_of_model (input_model context body argument)⟩

theorem output_for_every_solution {Γ Δ : Ctx sig} (context : Context Γ Δ)
    (body : Term sig (.term :: Δ) .term) (argument : Term sig Δ .term)
    {Future : Type} {future : Future → MetaArity sig} (candidate : Assignment (active Δ) future)
    (solved : ContextualFrameUnifier.Models candidate
      (problem context (context.plug (appT (lamT body) argument)))) :
    instantiate candidate (outputs context 1) = encode future (context.plug (inst body argument)) := by
  have matched := solved _ (by rw [problem_eq]; exact List.mem_singleton_self _)
  change instantiate candidate (openTerm (lhs context)) = instantiate candidate (encode (active Δ) _) at matched
  rw [opened_lhs, instantiate_plug, instantiate_encode, ← plug_encode] at matched
  have root := plug_injective context matched
  change app future (lam future (instantiate candidate (generator (active Δ) (.inl ⟨1, false⟩))))
    (instantiate candidate (generator (active Δ) (.inl ⟨1, true⟩))) =
      app future (lam future (encode future body)) (encode future argument) at root
  have both := app_inj root
  have body_eq := lam_inj both.1
  change instantiate candidate (openTerm (rhs context)) = _
  rw [opened_rhs, instantiate_plug, instantiate_inst, body_eq, both.2, ← encode_inst, plug_encode]

theorem encode_injective {Γ : Ctx sig} :
    ∀ (first second : Term sig Γ .term), encode declaration first = encode declaration second → first = second
  | .var first, .var second, same => by
      have positions := Term.var.inj (S := signature sig declaration) same
      exact congrArg (Term.var (S := sig)) positions
  | .var _, .op _ _, same => by cases same
  | .op _ _, .var _, same => by cases same
  | .op .app (.cons f (.cons a .nil)), .op .app (.cons g (.cons b .nil)), same => by
      have both := app_inj same
      exact congrArg₂ appT (encode_injective f g both.1) (encode_injective a b both.2)
  | .op .lam (.cons b .nil), .op .lam (.cons c .nil), same =>
      congrArg lamT (encode_injective b c (lam_inj same))
  | .op .app _, .op .lam _, same => by cases (Term.op.inj same).1
  | .op .lam _, .op .app _, same => by cases (Term.op.inj same).1
termination_by first _ _ => termSize first
decreasing_by all_goals (simp only [Mettapedia.OSLF.Binding.termSize, Mettapedia.OSLF.Binding.argsSize]; omega)

theorem encode_app_recovers {Γ : Ctx sig} :
    ∀ (term : Term sig Γ .term) (function argument : Term (signature sig declaration) Γ .term),
    app declaration function argument = encode declaration term →
    ∃ (sourceFunction sourceArgument : Term sig Γ .term),
      term = appT sourceFunction sourceArgument ∧
      function = encode declaration sourceFunction ∧ argument = encode declaration sourceArgument
  | .var _, _, _, same => by cases same
  | .op .app (.cons function (.cons argument .nil)), _, _, same =>
      ⟨function, argument, rfl, app_inj same⟩
  | .op .lam _, _, _, same => by cases (Term.op.inj same).1

theorem encode_lam_recovers {Γ : Ctx sig} :
    ∀ (term : Term sig Γ .term) (body : Term (signature sig declaration) (.term :: Γ) .term),
    lam declaration body = encode declaration term →
    ∃ sourceBody : Term sig (.term :: Γ) .term,
      term = lamT sourceBody ∧ body = encode declaration sourceBody
  | .var _, _, same => by cases same
  | .op .app _, _, same => by cases (Term.op.inj same).1
  | .op .lam (.cons body .nil), _, same => ⟨body, rfl, lam_inj same⟩

/-- A matched surrounding program really contains the selected subterm.
The context grammar cannot hide a non-source value in an erased hole. -/
theorem plug_recovers {Γ Δ : Ctx sig} (context : Context Γ Δ)
    (value : Term (signature sig declaration) Δ .term) (term : Term sig Γ .term)
    (same : plug declaration context value = encode declaration term) :
    ∃ inner : Term sig Δ .term, term = context.plug inner ∧ value = encode declaration inner := by
  induction context with
  | hole => exact ⟨term, rfl, same⟩
  | appLeft context argument ih =>
      obtain ⟨f, a, rfl, first, second⟩ := encode_app_recovers term _ _ same
      have argument_eq := encode_injective argument a second
      obtain ⟨inner, rfl, recovered⟩ := ih value f first
      exact ⟨inner, congrArg (appT (context.plug inner)) argument_eq.symm, recovered⟩
  | appRight function context ih =>
      obtain ⟨f, a, rfl, first, second⟩ := encode_app_recovers term _ _ same
      have function_eq := encode_injective function f first
      obtain ⟨inner, rfl, recovered⟩ := ih value a second
      exact ⟨inner, congrArg (fun head => appT head (context.plug inner)) function_eq.symm, recovered⟩
  | underLam context ih =>
      obtain ⟨b, rfl, matched⟩ := encode_lam_recovers term _ same
      obtain ⟨inner, source_eq, decoded⟩ := ih value b matched
      exact ⟨inner, congrArg lamT source_eq, decoded⟩

/-- A model of an actual prepared input equation recovers an ordinary
source beta redex. No unifier can reinterpret a variable or lambda as an
application merely to enable this rule. -/
theorem model_recovers_source {Γ Δ : Ctx sig} (context : Context Γ Δ) (input : Term sig Γ .term)
    {Future : Type} {future : Future → MetaArity sig} (candidate : Assignment (active Δ) future)
    (solved : ContextualFrameUnifier.Models candidate (problem context input)) :
    ∃ (body : Term sig (.term :: Δ) .term) (argument : Term sig Δ .term),
      input = context.plug (appT (lamT body) argument) := by
  have matched := solved _ (by rw [problem_eq]; exact List.mem_singleton_self _)
  change instantiate candidate (openTerm (lhs context)) = instantiate candidate (encode (active Δ) input) at matched
  rw [opened_lhs, instantiate_plug, instantiate_encode] at matched
  obtain ⟨inner, input_eq, root_eq⟩ := plug_recovers context _ input matched
  obtain ⟨function, argument, root_eq, function_eq, _⟩ := encode_app_recovers inner _ _ root_eq
  obtain ⟨body, function_eq, _⟩ := encode_lam_recovers function _ function_eq
  exact ⟨body, argument, by rw [input_eq, root_eq, function_eq]⟩

/-- Observation of a selected completed transform through its actual returned
solution. This is a client comparison, not another core transition rule. -/
def Executes {Γ : Ctx sig} (input output : Term sig Γ .term) : Prop :=
  ∃ (Δ : Ctx sig) (context : Context Γ Δ) (fuel : Nat)
    (update : ContextualFrameUpdate.Update (ContextualResidual.observeProblem (problem context input))),
    ContextualTransportedActivation.FromRun (locals Δ) captures fuel occupied selection
      (rule context) (rows Δ input) (before Γ) (outputs context) update ∧
      instantiate update.answer (outputs context 1) = encode update.declaration output

/-- Both directions use the independent four-rule source. Forward execution
obtains an actual terminating pattern-worklist run. Reverse execution uses
its model to recover the source redex and its observed result. -/
theorem source_step_iff_executes {Γ : Ctx sig} (input output : Term sig Γ .term) :
    LambdaContextualRung.Step Γ input output ↔ Executes input output := by
  constructor
  · intro step
    obtain ⟨Δ, context, body, argument, rfl, rfl⟩ := LambdaContextualRung.step_iff_context_beta.mp step
    obtain ⟨fuel, update, returned⟩ := completed_run context body argument
    refine ⟨Δ, context, fuel, update, returned, ?_⟩
    exact output_for_every_solution context body argument update.answer
      ((ContextualResidual.models_observeProblem _ _).mp (update.completed returned.empty))
  · rintro ⟨Δ, context, fuel, update, returned, observed⟩
    have solved := (ContextualResidual.models_observeProblem _ _).mp (update.completed returned.empty)
    obtain ⟨body, argument, rfl⟩ := model_recovers_source context input update.answer solved
    have exact_output := output_for_every_solution context body argument update.answer solved
    have same := encode_injective output (context.plug (inst body argument)) (observed.symm.trans exact_output)
    rw [same]
    exact context.congr_step (.beta body argument)

/-- The returned solution reads the actual emitted shared value as the source
reduct. Fresh original/helper identities remain in the stored value; this
theorem interprets them rather than silently rewriting the whole world. -/
theorem emitted_value_in_actual_frame {Γ Δ : Ctx sig} (context : Context Γ Δ)
    (body : Term sig (.term :: Δ) .term) (argument : Term sig Δ .term)
    {fuel : Nat}
    {update : ContextualFrameUpdate.Update
      (ContextualResidual.observeProblem (problem context (context.plug (appT (lamT body) argument))))}
    (returned : ContextualTransportedActivation.FromRun (locals Δ) captures fuel occupied selection
      (rule context) (rows Δ (context.plug (appT (lamT body) argument))) (before Γ) (outputs context) update) :
    instantiate (ContextualComputedFreshFrame.answer update)
      (instantiate (ContextualComputedFreshFrame.includeSource update) (outputs context 1)) =
      encode (ContextualComputedFreshFrame.active (active Δ) update.declaration)
        (context.plug (inst body argument)) := by
  rw [ContextualComputedFreshFrame.answer_on_source_term,
    output_for_every_solution context body argument update.answer
      ((ContextualResidual.models_observeProblem _ _).mp (update.completed returned.empty)), instantiate_encode]

theorem actual_result_publishes_shared_value {Γ Δ : Ctx sig} (context : Context Γ Δ)
    (input : Term sig Γ .term)
    (update : ContextualFrameUpdate.Update (ContextualResidual.observeProblem (problem context input))) :
    ContextualTransportedActivation.resultRows (locals Δ) captures
      (ContextualComputedFreshFrame.includeSource update) selection (outputs context) (rows Δ input) 1 =
      .shared (instantiate (ContextualComputedFreshFrame.includeSource update) (outputs context 1)) :=
  ContextualTransportedActivation.produced_row_is_shared (locals Δ) captures _ selection _ _ (by decide)

theorem actual_result_consumes_and_publishes {Γ Δ : Ctx sig} (context : Context Γ Δ)
    (input : Term sig Γ .term)
    (update : ContextualFrameUpdate.Update (ContextualResidual.observeProblem (problem context input))) :
    (ContextualTransportedActivation.result (locals Δ) captures
      (ContextualComputedFreshFrame.includeSource update) occupied selection (rule context)
        (rows Δ input) (before Γ)).present = {1} := by
  change (({0} : Finset Nat) \ {0}) ∪ {1} = {1}
  simp

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LambdaComparison
