import Mettapedia.OSLF.Syntax.LambdaContextualRung

/-!
# Lambda terms with lexical quotation and explicit activation

This independent source profile conservatively adds two constructors to the
existing intrinsic lambda syntax. Quotation retains lexical variables and
substitution acts on those captures. Reduction has no congruence rule under
quotation: code becomes executable through the explicit activation rule.
Beta reduction remains the unrestricted contextual relation of the original
lambda profile; this is not a call-by-need strategy or an effects semantics.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.Binding.QuotedLambda

open LambdaContextualRung (Srt)

inductive Op : Srt → Type where
  | app : Op .term
  | lam : Op .term
  | quote : Op .term
  | activate : Op .term
  deriving DecidableEq

def sig : Signature where
  Srt := Srt
  Op := Op
  arity := fun {_} operator => match operator with
    | .app => [([], .term), ([], .term)]
    | .lam => [([.term], .term)]
    | .quote | .activate => [([], .term)]

def app {Γ : Ctx sig} (function argument : Term sig Γ .term) : Term sig Γ .term :=
  .op .app (.cons function (.cons argument .nil))
def lam {Γ : Ctx sig} (body : Term sig (.term :: Γ) .term) : Term sig Γ .term :=
  .op .lam (.cons body .nil)
def quote {Γ : Ctx sig} (code : Term sig Γ .term) : Term sig Γ .term :=
  .op .quote (.cons code .nil)
def activate {Γ : Ctx sig} (name : Term sig Γ .term) : Term sig Γ .term :=
  .op .activate (.cons name .nil)

@[simp] theorem bind_app {Γ Δ : Ctx sig} (assignment : Sub sig Γ Δ)
    (function argument : Term sig Γ .term) :
    bind assignment (app function argument) = app (bind assignment function) (bind assignment argument) := rfl
@[simp] theorem bind_lam {Γ Δ : Ctx sig} (assignment : Sub sig Γ Δ)
    (body : Term sig (.term :: Γ) .term) :
    bind assignment (lam body) = lam (bind (liftSub assignment [.term]) body) := rfl
@[simp] theorem bind_quote {Γ Δ : Ctx sig} (assignment : Sub sig Γ Δ)
    (code : Term sig Γ .term) : bind assignment (quote code) = quote (bind assignment code) := rfl
@[simp] theorem bind_activate {Γ Δ : Ctx sig} (assignment : Sub sig Γ Δ)
    (name : Term sig Γ .term) : bind assignment (activate name) = activate (bind assignment name) := rfl

/-- A quoted body may contain reducible terms, including further activation,
without making any of those terms an active reduction position. -/
inductive Step : (Γ : Ctx sig) → Term sig Γ .term → Term sig Γ .term → Prop where
  | beta {Γ : Ctx sig} (body : Term sig (.term :: Γ) .term) (argument : Term sig Γ .term) :
      Step Γ (app (lam body) argument) (inst body argument)
  | activateQuote {Γ : Ctx sig} (code : Term sig Γ .term) :
      Step Γ (activate (quote code)) code
  | appLeft {Γ : Ctx sig} {source target : Term sig Γ .term} (argument : Term sig Γ .term) :
      Step Γ source target → Step Γ (app source argument) (app target argument)
  | appRight {Γ : Ctx sig} {source target : Term sig Γ .term} (function : Term sig Γ .term) :
      Step Γ source target → Step Γ (app function source) (app function target)
  | underLam {Γ : Ctx sig} {source target : Term sig (.term :: Γ) .term} :
      Step (.term :: Γ) source target → Step Γ (lam source) (lam target)
  | underActivate {Γ : Ctx sig} {source target : Term sig Γ .term} :
      Step Γ source target → Step Γ (activate source) (activate target)

theorem substitute {Γ Δ : Ctx sig} (assignment : Sub sig Γ Δ) :
    ∀ {source target : Term sig Γ .term}, Step Γ source target →
      Step Δ (bind assignment source) (bind assignment target)
  | _, _, .beta body argument => by
      have commuting : bind assignment (inst body argument) =
          inst (bind (liftSub assignment [.term]) body) (bind assignment argument) :=
        ContextualLinearSubstitution.bind_inst assignment body argument
      rw [bind_app, bind_lam, commuting]
      exact .beta _ _
  | _, _, .activateQuote code => by
      rw [bind_activate, bind_quote]
      exact .activateQuote _
  | _, _, .appLeft argument step => by
      simpa only [bind_app] using Step.appLeft (bind assignment argument) (substitute assignment step)
  | _, _, .appRight function step => by
      simpa only [bind_app] using Step.appRight (bind assignment function) (substitute assignment step)
  | _, _, .underLam step => by
      rw [bind_lam, bind_lam]
      exact .underLam (substitute (liftSub assignment [.term]) step)
  | _, _, .underActivate step => by
      rw [bind_activate, bind_activate]
      exact .underActivate (substitute assignment step)

theorem quote_is_inert {Γ : Ctx sig} (code target : Term sig Γ .term) :
    ¬ Step Γ (quote code) target := by intro step; cases step

theorem variable_is_inert {Γ : Ctx sig} (position : Var Γ .term) (target : Term sig Γ .term) :
    ¬ Step Γ (.var position) target := by intro step; cases step

inductive Context : Ctx sig → Ctx sig → Type where
  | hole {Γ : Ctx sig} : Context Γ Γ
  | appLeft {Γ Δ : Ctx sig} : Context Γ Δ → Term sig Γ .term → Context Γ Δ
  | appRight {Γ Δ : Ctx sig} : Term sig Γ .term → Context Γ Δ → Context Γ Δ
  | underLam {Γ Δ : Ctx sig} : Context (.term :: Γ) Δ → Context Γ Δ
  | underActivate {Γ Δ : Ctx sig} : Context Γ Δ → Context Γ Δ

def Context.plug : {Γ Δ : Ctx sig} → Context Γ Δ → Term sig Δ .term → Term sig Γ .term
  | _, _, .hole, value => value
  | _, _, .appLeft inner argument, value => app (inner.plug value) argument
  | _, _, .appRight function inner, value => app function (inner.plug value)
  | _, _, .underLam inner, value => lam (inner.plug value)
  | _, _, .underActivate inner, value => activate (inner.plug value)

theorem Context.congr_step {Γ Δ : Ctx sig} (context : Context Γ Δ)
    {source target : Term sig Δ .term} (step : Step Δ source target) :
    Step Γ (context.plug source) (context.plug target) := by
  induction context with
  | hole => exact step
  | appLeft inner argument ih => exact .appLeft argument (ih step)
  | appRight function inner ih => exact .appRight function (ih step)
  | underLam inner ih => exact .underLam (ih step)
  | underActivate inner ih => exact .underActivate (ih step)

/-- The two computational roots. Context closure is specified separately,
so quotation cannot acquire an implicit reduction rule. -/
inductive Redex (Γ : Ctx sig) where
  | beta (body : Term sig (.term :: Γ) .term) (argument : Term sig Γ .term)
  | activation (code : Term sig Γ .term)

def Redex.source {Γ : Ctx sig} : Redex Γ → Term sig Γ .term
  | .beta body argument => app (lam body) argument
  | .activation code => activate (quote code)
def Redex.target {Γ : Ctx sig} : Redex Γ → Term sig Γ .term
  | .beta body argument => inst body argument
  | .activation code => code

theorem Redex.step {Γ : Ctx sig} (redex : Redex Γ) : Step Γ redex.source redex.target := by
  cases redex with
  | beta body argument => exact .beta body argument
  | activation code => exact .activateQuote code

theorem step_iff_context_redex {Γ : Ctx sig} {source target : Term sig Γ .term} :
    Step Γ source target ↔ ∃ (Δ : Ctx sig) (context : Context Γ Δ) (redex : Redex Δ),
      source = context.plug redex.source ∧ target = context.plug redex.target := by
  constructor
  · intro step
    induction step with
    | beta body argument => exact ⟨_, .hole, .beta body argument, rfl, rfl⟩
    | activateQuote code => exact ⟨_, .hole, .activation code, rfl, rfl⟩
    | appLeft argument step ih =>
        obtain ⟨Δ, context, redex, rfl, rfl⟩ := ih
        exact ⟨Δ, .appLeft context argument, redex, rfl, rfl⟩
    | appRight function step ih =>
        obtain ⟨Δ, context, redex, rfl, rfl⟩ := ih
        exact ⟨Δ, .appRight function context, redex, rfl, rfl⟩
    | underLam step ih =>
        obtain ⟨Δ, context, redex, rfl, rfl⟩ := ih
        exact ⟨Δ, .underLam context, redex, rfl, rfl⟩
    | underActivate step ih =>
        obtain ⟨Δ, context, redex, rfl, rfl⟩ := ih
        exact ⟨Δ, .underActivate context, redex, rfl, rfl⟩
  · rintro ⟨Δ, context, redex, rfl, rfl⟩
    exact context.congr_step redex.step

mutual
def includeLambda : {Γ : Ctx LambdaContextualRung.sig} → {sort : Srt} →
    Term LambdaContextualRung.sig Γ sort → Term sig Γ sort
  | _, _, .var position => .var position
  | _, _, .op .app arguments => .op .app (includeLambdaArgs arguments)
  | _, _, .op .lam arguments => .op .lam (includeLambdaArgs arguments)
def includeLambdaArgs : {Γ : Ctx sig} → {arities : List (List Srt × Srt)} →
    Args LambdaContextualRung.sig arities Γ → Args sig arities Γ
  | _, _, .nil => .nil
  | _, _, .cons head tail => .cons (includeLambda head) (includeLambdaArgs tail)
end

mutual
theorem includeLambda_rename {Γ Δ : Ctx sig} (rho : Ren sig Γ Δ) :
    ∀ {sort : Srt} (term : Term LambdaContextualRung.sig Γ sort),
      includeLambda (rename rho term) = rename (S := sig) rho (includeLambda term)
  | _, .var _ => rfl
  | _, .op .app arguments => congrArg (Term.op (S := sig) Op.app) (includeLambdaArgs_rename rho arguments)
  | _, .op .lam arguments => congrArg (Term.op (S := sig) Op.lam) (includeLambdaArgs_rename rho arguments)
theorem includeLambdaArgs_rename {Γ Δ : Ctx sig} (rho : Ren sig Γ Δ) :
    ∀ {arities : List (List Srt × Srt)} (arguments : Args LambdaContextualRung.sig arities Γ),
      includeLambdaArgs (renameArgs rho arguments) = renameArgs (S := sig) rho (includeLambdaArgs arguments)
  | _, .nil => rfl
  | _, .cons (bs := binders) head tail =>
      congrArg₂ Args.cons (includeLambda_rename (liftRen rho binders) head)
        (includeLambdaArgs_rename rho tail)
end

theorem includeLambda_liftSub {Γ Δ : Ctx sig} (assignment : Sub LambdaContextualRung.sig Γ Δ) :
    ∀ (binders : Ctx sig) (sort : Srt) (position : Var (binders ++ Γ) sort),
      includeLambda (liftSub assignment binders sort position) =
        liftSub (fun sort position => includeLambda (assignment sort position)) binders sort position
  | [], _, _ => rfl
  | _ :: _, _, .zero => rfl
  | _ :: binders, sort, .succ position => by
      simp only [liftSub, weaken, includeLambda_rename, includeLambda_liftSub assignment binders sort position]
      rfl

mutual
theorem includeLambda_bind {Γ Δ : Ctx sig} (assignment : Sub LambdaContextualRung.sig Γ Δ) :
    ∀ {sort : Srt} (term : Term LambdaContextualRung.sig Γ sort),
      includeLambda (bind assignment term) =
        bind (fun sort position => includeLambda (assignment sort position)) (includeLambda term)
  | _, .var _ => rfl
  | _, .op .app arguments => congrArg (Term.op (S := sig) Op.app) (includeLambdaArgs_bind assignment arguments)
  | _, .op .lam arguments => congrArg (Term.op (S := sig) Op.lam) (includeLambdaArgs_bind assignment arguments)
theorem includeLambdaArgs_bind {Γ Δ : Ctx sig} (assignment : Sub LambdaContextualRung.sig Γ Δ) :
    ∀ {arities : List (List Srt × Srt)} (arguments : Args LambdaContextualRung.sig arities Γ),
      includeLambdaArgs (bindArgs assignment arguments) =
        bindArgs (fun sort position => includeLambda (assignment sort position)) (includeLambdaArgs arguments)
  | _, .nil => rfl
  | _, .cons (bs := binders) head tail => by
      have lifted : (fun sort position => includeLambda (liftSub assignment binders sort position)) =
          liftSub (fun sort position => includeLambda (assignment sort position)) binders := by
        funext sort position
        exact includeLambda_liftSub assignment binders sort position
      exact congrArg₂ Args.cons
        ((includeLambda_bind (liftSub assignment binders) head).trans
          (congrArg (fun environment : Sub sig (List.append (α := Srt) binders Γ) (List.append (α := Srt) binders Δ) =>
            bind environment (includeLambda head)) lifted))
        (includeLambdaArgs_bind assignment tail)
end

theorem includeLambda_inst {Γ : Ctx sig} (body : Term LambdaContextualRung.sig (.term :: Γ) .term)
    (argument : Term LambdaContextualRung.sig Γ .term) :
    includeLambda (inst body argument) = inst (includeLambda body) (includeLambda argument) := by
  unfold inst
  rw [includeLambda_bind]
  congr 1
  funext sort position
  cases position <;> rfl

theorem lambda_step_preserved {Γ : Ctx sig} {source target : Term LambdaContextualRung.sig Γ .term}
    (step : LambdaContextualRung.Step Γ source target) :
    Step Γ (includeLambda source) (includeLambda target) := by
  induction step with
  | beta body argument =>
      rw [includeLambda_inst]
      exact .beta (includeLambda body) (includeLambda argument)
  | appCongL argument step ih => exact .appLeft (includeLambda argument) ih
  | appCongR function step ih => exact .appRight (includeLambda function) ih
  | lamCong step ih => exact .underLam ih

theorem app_injective {Γ : Ctx sig} {first second third fourth : Term sig Γ .term}
    (same : app first second = app third fourth) : first = third ∧ second = fourth := by
  have arguments := Args.cons.inj (eq_of_heq (Term.op.inj same).2)
  exact ⟨arguments.1, (Args.cons.inj arguments.2).1⟩

theorem lam_injective {Γ : Ctx sig} {first second : Term sig (.term :: Γ) .term}
    (same : lam first = lam second) : first = second :=
  (Args.cons.inj (eq_of_heq (Term.op.inj same).2)).1

theorem includeLambda_app_recovers {Γ : Ctx sig} :
    ∀ (term : Term LambdaContextualRung.sig Γ .term) (function argument : Term sig Γ .term),
      app function argument = includeLambda term →
        ∃ (f a : Term LambdaContextualRung.sig Γ .term),
          term = LambdaContextualRung.appT f a ∧ function = includeLambda f ∧ argument = includeLambda a
  | .var _, _, _, same => by cases same
  | .op .app (.cons function (.cons argument .nil)), _, _, same => ⟨function, argument, rfl, app_injective same⟩
  | .op .lam _, _, _, same => by cases (Term.op.inj same).1

theorem includeLambda_lam_recovers {Γ : Ctx sig} :
    ∀ (term : Term LambdaContextualRung.sig Γ .term) (body : Term sig (.term :: Γ) .term),
      lam body = includeLambda term →
        ∃ b : Term LambdaContextualRung.sig (.term :: Γ) .term,
          term = LambdaContextualRung.lamT b ∧ body = includeLambda b
  | .var _, _, same => by cases same
  | .op .app _, _, same => by cases (Term.op.inj same).1
  | .op .lam (.cons body .nil), _, same => ⟨body, rfl, lam_injective same⟩

theorem activation_is_not_pure {Γ : Ctx sig} :
    ∀ (term : Term LambdaContextualRung.sig Γ .term) (name : Term sig Γ .term),
      activate name ≠ includeLambda term
  | .var _, _, same => by cases same
  | .op .app _, _, same => by cases (Term.op.inj same).1
  | .op .lam _, _, same => by cases (Term.op.inj same).1

/-- An execution starting in the original lambda sublanguage cannot invent
quotation or activation, nor reach a reduct missing from the original source. -/
theorem lambda_step_reflected {Γ : Ctx sig} (original : Term LambdaContextualRung.sig Γ .term)
    {target : Term sig Γ .term} (step : Step Γ (includeLambda original) target) :
    ∃ result, LambdaContextualRung.Step Γ original result ∧ target = includeLambda result := by
  generalize sourceEq : includeLambda original = source at step
  induction step with
  | beta body argument =>
      obtain ⟨function, input, rfl, head, rfl⟩ := includeLambda_app_recovers original _ _ sourceEq.symm
      obtain ⟨body, rfl, rfl⟩ := includeLambda_lam_recovers function _ head
      exact ⟨inst body input, .beta body input, (includeLambda_inst body input).symm⟩
  | activateQuote code => exact False.elim (activation_is_not_pure original _ sourceEq.symm)
  | appLeft argument step ih =>
      obtain ⟨function, input, rfl, head, rfl⟩ := includeLambda_app_recovers original _ _ sourceEq.symm
      obtain ⟨result, sourceStep, rfl⟩ := ih function head.symm
      exact ⟨LambdaContextualRung.appT result input, .appCongL input sourceStep, rfl⟩
  | appRight function step ih =>
      obtain ⟨head, input, rfl, rfl, tail⟩ := includeLambda_app_recovers original _ _ sourceEq.symm
      obtain ⟨result, sourceStep, rfl⟩ := ih input tail.symm
      exact ⟨LambdaContextualRung.appT head result, .appCongR head sourceStep, rfl⟩
  | underLam step ih =>
      obtain ⟨body, rfl, inside⟩ := includeLambda_lam_recovers original _ sourceEq.symm
      obtain ⟨result, sourceStep, rfl⟩ := ih body inside.symm
      exact ⟨LambdaContextualRung.lamT result, .lamCong sourceStep, rfl⟩
  | underActivate step ih => exact False.elim (activation_is_not_pure original _ sourceEq.symm)

theorem includeLambda_injective {Γ : Ctx sig} :
    ∀ (first second : Term LambdaContextualRung.sig Γ .term),
      includeLambda first = includeLambda second → first = second
  | .var first, .var second, same => congrArg (Term.var (S := LambdaContextualRung.sig))
      (Term.var.inj (S := sig) same)
  | .var _, .op operator _, same => by cases operator <;> cases same
  | .op operator _, .var _, same => by cases operator <;> cases same
  | .op .app (.cons f (.cons a .nil)), .op .app (.cons g (.cons b .nil)), same =>
      congrArg₂ LambdaContextualRung.appT (includeLambda_injective f g (app_injective same).1)
        (includeLambda_injective a b (app_injective same).2)
  | .op .lam (.cons b .nil), .op .lam (.cons c .nil), same =>
      congrArg LambdaContextualRung.lamT (includeLambda_injective b c (lam_injective same))
  | .op .app _, .op .lam _, same => by cases (Term.op.inj same).1
  | .op .lam _, .op .app _, same => by cases (Term.op.inj same).1
termination_by first _ _ => termSize first
decreasing_by all_goals (simp only [termSize, argsSize]; omega)

theorem lambda_path_reflected {Γ : Ctx sig} (original : Term LambdaContextualRung.sig Γ .term)
    {target : Term sig Γ .term} (path : Relation.ReflTransGen (Step Γ) (includeLambda original) target) :
    ∃ result, Relation.ReflTransGen (LambdaContextualRung.Step Γ) original result ∧ target = includeLambda result := by
  induction path with
  | refl => exact ⟨original, .refl, rfl⟩
  | tail prior step ih =>
      obtain ⟨middle, priorPath, rfl⟩ := ih
      obtain ⟨result, sourceStep, rfl⟩ := lambda_step_reflected middle step
      exact ⟨result, priorPath.tail sourceStep, rfl⟩

theorem pure_lambda_paths_iff {Γ : Ctx sig} (source target : Term LambdaContextualRung.sig Γ .term) :
    Relation.ReflTransGen (LambdaContextualRung.Step Γ) source target ↔
      Relation.ReflTransGen (Step Γ) (includeLambda source) (includeLambda target) := by
  constructor
  · intro path
    induction path with
    | refl => exact .refl
    | tail prior step ih => exact ih.tail (lambda_step_preserved step)
  · intro path
    obtain ⟨actual, sourcePath, same⟩ := lambda_path_reflected source path
    exact includeLambda_injective target actual same ▸ sourcePath

theorem quote_has_only_its_reflexive_path {Γ : Ctx sig} (code target : Term sig Γ .term) :
    Relation.ReflTransGen (Step Γ) (quote code) target ↔ target = quote code := by
  constructor
  · intro path
    induction path with
    | refl => rfl
    | tail prior step ih => exact False.elim (quote_is_inert code _ (ih ▸ step))
  · rintro rfl; exact .refl

namespace Controls

def identity : Term sig [] .term := lam (.var .zero)
def quotedArgumentProgram : Term sig [] .term :=
  app (lam (activate (.var .zero))) (quote identity)

theorem passing_named_code_then_explicitly_activating :
    Relation.ReflTransGen (Step []) quotedArgumentProgram identity := by
  have beta : Step [] quotedArgumentProgram (activate (quote identity)) := .beta _ _
  exact (Relation.ReflTransGen.single beta).tail (.activateQuote identity)

def capturedProgram : Term sig [.term] .term :=
  activate (app (lam (quote (lam (.var (.succ .zero))))) (.var .zero))
def capturedResult : Term sig [.term] .term := lam (.var (.succ .zero))

theorem activation_retains_a_capture_beneath_an_inner_lambda :
    Relation.ReflTransGen (Step [.term]) capturedProgram capturedResult := by
  have beta : Step [.term] capturedProgram (activate (quote capturedResult)) := .underActivate (.beta _ _)
  exact (Relation.ReflTransGen.single beta).tail (.activateQuote capturedResult)

theorem the_result_did_not_capture_the_inner_binder : capturedResult ≠ lam (.var .zero) := by
  intro same
  cases Term.var.inj (lam_injective same)

def selfApply : Term sig [] .term := lam (app (.var .zero) (.var .zero))
def looping : Term sig [] .term := app selfApply selfApply

theorem the_unquoted_body_can_reduce_forever_one_step_at_a_time : Step [] looping looping := .beta _ _
theorem its_quotation_has_no_execution (target : Term sig [] .term) : ¬ Step [] (quote looping) target :=
  quote_is_inert looping target
theorem one_activation_opens_exactly_one_quotation :
    Step [] (activate (quote (quote looping))) (quote looping) := .activateQuote _

end Controls

end Mettapedia.OSLF.Binding.QuotedLambda
