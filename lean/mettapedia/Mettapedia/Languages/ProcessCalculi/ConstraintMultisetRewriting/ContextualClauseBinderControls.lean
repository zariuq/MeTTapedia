import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClausePublication
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SchematicReachInformation

/-!
# A queried lambda body computes through its declared argument spine

The stored value is lambda z. pair(z,2). One query captures its body at a
unary contextual variable; the authored body applies it to 1 and 2. This
uses intrinsic capture-avoiding substitution in the ordinary clause compiler.
No evaluator callback supplies the answers.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClausePublication.BinderControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries ContextualClauseFrames ContextualClauseProblem ContextualClauseAdmission
open ContextualWorldScopeLedger ContextualScopeSupport

inductive DataOperator where
  | symbol : Nat → DataOperator
  | pair
  | lam
  deriving DecidableEq

abbrev dataSignature : Signature where
  Srt := Unit
  Op _ := DataOperator
  arity
    | .symbol _ => []
    | .pair => [([], ()), ([], ())]
    | .lam => [([()], ())]

abbrev base := SchematicReach.base dataSignature () Nat
local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) := by
  change DecidableEq (DataOperator ⊕ Operator (SchematicReach.spaceDeclaration dataSignature () (Name := Nat)) sort)
  infer_instance

abbrev locals (impossible : Empty) : MetaArity base := nomatch impossible
abbrev captures (impossible : Empty) : MetaArity base := nomatch impossible
def queries (key : Bool) : MetaArity base := if key then ([], ()) else ([()], ())
abbrev actor := queryFamily queries captures
abbrev origin := family queries locals captures

def symbol {V : Type} {decl : V → MetaArity base} {Γ : Ctx base} (number : Nat) : Term (signature base decl) Γ () :=
  .op (.inl (.inl (.symbol number))) .nil
def pair {V : Type} {decl : V → MetaArity base} {Γ : Ctx base}
    (first second : Term (signature base decl) Γ ()) : Term (signature base decl) Γ () :=
  .op (.inl (.inl .pair)) (.cons first (.cons second .nil))
def lam {V : Type} {decl : V → MetaArity base} {Γ : Ctx base}
    (body : Term (signature base decl) (() :: Γ) ()) : Term (signature base decl) Γ () :=
  .op (.inl (.inl .lam)) (.cons body .nil)
def located {V : Type} {decl : V → MetaArity base} (space : Nat) (value : SchematicReach.Closed decl) :=
  SchematicReach.place (SchematicReach.name space) value
def function {V : Type} (decl : V → MetaArity base) : SchematicReach.Closed decl :=
  lam (pair (.var .zero) (symbol 2))
def callBody (number : Nat) : SchematicReach.Closed actor :=
  .op (.inr (.mk (.inl false))) (.cons (symbol number) .nil)
def sourceCall (number : Nat) : SchematicReach.Closed origin :=
  .op (.inr (.mk (.inl false))) (.cons (symbol number) .nil)

def rows (_ : Nat) : ContextualStoredRows.Row locals captures [] () := .shared (located 1 (function captures))
def initial : Configuration (SchematicReach.Closed captures) Nat := ⟨[], {0}⟩
def scopes (impossible : Empty) : Finset Nat := nomatch impossible
def inventory : Inventory locals captures (O := Nat) [] () := ⟨initial, rows, [], []⟩
def before : ContextualExecution.Endpoint locals Nat [] () where
  Names := Empty
  equality := inferInstance
  declarations := captures
  scopes := scopes
  occupied := ∅
  inventory := inventory
  covered := (coveredWorld_iff locals captures scopes ∅ inventory).mpr (by decide +kernel)

def code : RuleInstance (SchematicReach.Closed actor) :=
  ⟨[], [located 1 (lam (generator actor (.inl false)))], [], [],
    [located 9 (pair (callBody 1) (callBody 2))]⟩
def plan : ContextualPublication.Plan (SchematicReach.Closed actor) := ⟨code, [true], rfl⟩
def selected : Selection Nat := ⟨[], [0], [1]⟩
def sourceProblem := problem queries locals captures selected code rows initial

theorem source_problem_explicit : sourceProblem =
    [(located 1 (lam (generator origin (.inl false))), located 1 (function origin))] := by
  with_unfolding_all rfl

def model {V : Type} (decl : V → MetaArity base) : Assignment origin decl
  | .inl false => pair (.var .zero) (symbol 2)
  | .inl true => symbol 0
  | .inr (.inl ⟨_, impossible⟩) => nomatch impossible
  | .inr (.inr impossible) => nomatch impossible

theorem source_model {V : Type} (decl : V → MetaArity base) : ContextualFrameUnifier.Models (model decl) sourceProblem := by
  rw [source_problem_explicit]
  intro equation member
  obtain rfl := List.mem_singleton.mp member
  with_unfolding_all rfl

theorem source_admitted : Admitted queries locals captures selected code rows initial := by
  refine ⟨by decide +kernel, by decide +kernel, rfl, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    ⟨Empty, captures, model captures, source_model captures⟩, ?_⟩
  intro check member
  cases member

theorem covered : RuleCovered (privateScopes scopes) ∅ code := by
  apply (ruleRoots_covered_iff (privateScopes scopes) ∅ code).mp
  decide +kernel
theorem patterned : ContextualPatternFragment.ProblemPattern (ContextualResidual.observeProblem sourceProblem) := by
  apply (ContextualPatternFragment.checkProblem_iff _).mp
  decide +kernel

theorem actual_compiled_lambda_body : Nonempty (Compiled queries locals (before := before) plan selected) :=
  realize queries locals (before := before) plan selected covered source_admitted patterned

private theorem instantiate_symbol {V Next : Type} {decl : V → MetaArity base} {next : Next → MetaArity base}
    (assignment : Assignment decl next) {Γ : Ctx base} (number : Nat) :
    instantiate assignment (symbol (Γ := Γ) number) = symbol number := rfl
private theorem instantiate_pair {V Next : Type} {decl : V → MetaArity base} {next : Next → MetaArity base}
    (assignment : Assignment decl next) {Γ : Ctx base} (first second : Term (signature base decl) Γ ()) :
    instantiate assignment (pair first second) = pair (instantiate assignment first) (instantiate assignment second) := rfl
private theorem instantiate_lam {V Next : Type} {decl : V → MetaArity base} {next : Next → MetaArity base}
    (assignment : Assignment decl next) {Γ : Ctx base} (body : Term (signature base decl) (() :: Γ) ()) :
    instantiate assignment (lam body) = lam (instantiate assignment body) := rfl
private theorem instantiate_located {V Next : Type} {decl : V → MetaArity base} {next : Next → MetaArity base}
    (assignment : Assignment decl next) (space : Nat) (value : SchematicReach.Closed decl) :
    instantiate assignment (located space value) = located space (instantiate assignment value) := rfl
private theorem lam_injective {V : Type} {decl : V → MetaArity base}
    {first second : Term (signature base decl) [()] ()} (same : lam first = lam second) : first = second := by
  exact (Args.cons.inj (eq_of_heq (Term.op.inj same).2)).1

theorem source_body_applies_its_argument {V : Type} (decl : V → MetaArity base)
    (candidate : Assignment origin decl) (solved : ContextualFrameUnifier.Models candidate sourceProblem) (number : Nat) :
    instantiate candidate (sourceCall number) = pair (symbol number) (symbol 2) := by
  have equation := solved _ (by rw [source_problem_explicit]; exact List.mem_singleton_self _)
  have bodyEq : candidate (.inl false) = pair (.var .zero) (symbol 2) := by
    apply lam_injective
    change instantiate candidate (located 1 (lam (generator origin (.inl false)))) =
      instantiate candidate (located 1 (function origin)) at equation
    rw [instantiate_located, instantiate_located] at equation
    have heads := (SchematicReach.place_injective equation).2
    change instantiate candidate (lam (generator origin (.inl false))) = instantiate candidate (function origin) at heads
    have opened : instantiate candidate (lam (generator origin (.inl false))) = lam (candidate (.inl false)) :=
      (instantiate_lam candidate (generator origin (.inl false))).trans
        (congrArg (lam (decl := decl) (Γ := [])) (instantiate_generator candidate (.inl false)))
    exact opened.symm.trans (heads.trans (show instantiate candidate (function origin) = function decl from rfl))
  change bind (argsToSub (.cons (symbol number) .nil)) (candidate (.inl false)) = _
  rw [bodyEq]
  rfl

theorem actual_lambda_body_result (compiled : Compiled queries locals (before := before) plan selected) :
    compiled.firing.target.inventory.rows 1 =
      ContextualPublication.ordinary (bank queries locals) compiled.firing.update.declaration
        (located 9 (pair (pair (symbol 1) (symbol 2)) (pair (symbol 2) (symbol 2)))) := by
  have made : 1 ∈ compiled.firing.selection.made := by rw [compiled.selected]; decide +kernel
  have reuse : compiled.firing.reusable 1 = true := by
    have intents := compiled.intents
    change [compiled.firing.reusable 1] = [true] at intents
    exact (List.cons.inj intents).1
  rw [compiled.firing.ordinary_row made reuse]
  apply congrArg (ContextualPublication.ordinary (bank queries locals) compiled.firing.update.declaration)
  have sourceSolved : ContextualFrameUnifier.Models
      (Assignment.compose compiled.firing.update.answer (frame queries locals captures ∅).assignment) sourceProblem :=
    compiled.solved_source_model
  have first := source_body_applies_its_argument compiled.firing.update.declaration _ sourceSolved 1
  have second := source_body_applies_its_argument compiled.firing.update.declaration _ sourceSolved 2
  have output := output_at_port queries locals captures ∅ selected code rows (by decide +kernel) rfl ⟨0, by decide +kernel⟩
  have view : queryView queries locals captures (code.produce.get ⟨0, by decide +kernel⟩) =
      located 9 (pair (sourceCall 1) (sourceCall 2)) := by with_unfolding_all rfl
  rw [compiled.values]
  change instantiate compiled.firing.update.answer (outputs queries locals captures ∅ selected code rows 1) = _
  have value : outputs queries locals captures ∅ selected code rows 1 =
      instantiate (frame queries locals captures ∅).assignment (located 9 (pair (sourceCall 1) (sourceCall 2))) :=
    output.trans (congrArg (instantiate (frame queries locals captures ∅).assignment) view)
  rw [value]
  apply (Assignment.instantiate_compose compiled.firing.update.answer (frame queries locals captures ∅).assignment _).symm.trans
  have location := instantiate_located (Assignment.compose compiled.firing.update.answer (frame queries locals captures ∅).assignment)
    9 (pair (sourceCall 1) (sourceCall 2))
  exact location.trans (congrArg (located (decl := compiled.firing.update.declaration) 9)
    ((instantiate_pair (Assignment.compose compiled.firing.update.answer (frame queries locals captures ∅).assignment)
      (sourceCall 1) (sourceCall 2)).trans (congrArg₂ pair first second)))

def closedBody : Term (signature base actor) [()] () := .op (.inr (.mk (.inl true))) .nil
def missingDependencyCode : RuleInstance (SchematicReach.Closed actor) :=
  { code with read := [located 1 (lam closedBody)] }
def missingDependencyPlan : ContextualPublication.Plan (SchematicReach.Closed actor) :=
  ⟨missingDependencyCode, [true], rfl⟩
def missingDependencyProblem := problem queries locals captures selected missingDependencyCode rows initial
def isRefuted {V : Type} {decl : V → MetaArity base} {job : ContextualResidual.Problem decl} :
    ContextualFrameWorklist.Result job → Bool
  | .refuted _ => true
  | .residual _ => false

def emptyRen : Ren base [] [()] := fun _ impossible => nomatch impossible
def sourceClosedBody : Term (signature base origin) [()] () := .op (.inr (.mk (.inl true))) .nil

theorem missing_problem_explicit : missingDependencyProblem =
    [(located 1 (lam sourceClosedBody), located 1 (function origin))] := by with_unfolding_all rfl

private theorem a_closed_term_cannot_read_the_outer_argument {V : Type} (decl : V → MetaArity base)
    (closed : Term (signature base decl) [] ()) :
    rename (S := signature base decl) emptyRen closed ≠ pair (.var .zero) (symbol 2) := by
  intro same
  cases closed with
  | var impossible => cases impossible
  | op operator arguments =>
      have head := (Term.op.inj same).1
      cases head
      cases arguments with
      | cons first rest =>
          have argument := (Args.cons.inj (eq_of_heq (Term.op.inj same).2)).1
          exact ContextualEquationRefutation.variable_outside_image
            (T := signature base decl) emptyRen .zero (by intro formal; cases formal) first argument

/-- The negative result quantifies over every future declaration family.
A body hole with no argument spine cannot capture the bound variable. -/
theorem missing_dependency_has_no_source_model {V : Type} (decl : V → MetaArity base)
    (candidate : Assignment origin decl) : ¬ ContextualFrameUnifier.Models candidate missingDependencyProblem := by
  intro solved
  have equation := solved _ (by rw [missing_problem_explicit]; exact List.mem_singleton_self _)
  change instantiate candidate (located 1 (lam sourceClosedBody)) = instantiate candidate (located 1 (function origin)) at equation
  rw [instantiate_located, instantiate_located] at equation
  have bodies := (SchematicReach.place_injective equation).2
  have bodyEq : instantiate candidate sourceClosedBody = pair (.var .zero) (symbol 2) := by
    apply lam_injective
    exact (instantiate_lam candidate sourceClosedBody).symm.trans
      (bodies.trans (show instantiate candidate (function origin) = function decl from rfl))
  have bodyIsClosed : sourceClosedBody = rename (S := signature base origin) emptyRen (generator origin (.inl true)) :=
    VariableSpines.application_eq_rename_generator (S := base) (declaration := origin)
      (Sum.inl true) .nil emptyRen (by intro sort index; cases index)
  have actual : instantiate candidate sourceClosedBody = rename (S := signature base decl) emptyRen (candidate (.inl true)) :=
    (congrArg (instantiate candidate) bodyIsClosed).trans
      ((ContextualFamily.instantiate_rename candidate emptyRen (generator origin (.inl true))).trans
        (congrArg (rename (S := signature base decl) emptyRen) (instantiate_generator candidate (.inl true))))
  exact a_closed_term_cannot_read_the_outer_argument decl (candidate (.inl true)) (actual.symm.trans bodyEq)

theorem the_actual_driver_refutes_the_missing_dependency :
    ∃ fuel, isRefuted (ContextualFrameWorklist.run fuel origin (ContextualResidual.observeProblem missingDependencyProblem)) = true := by
  have structural : ContextualPatternFragment.ProblemPattern (ContextualResidual.observeProblem missingDependencyProblem) :=
    (ContextualPatternFragment.checkProblem_iff _).mp (by decide +kernel)
  obtain ⟨fuel, finished⟩ := ContextualPatternTermination.finishes
    (ContextualResidual.observeProblem missingDependencyProblem) structural
  refine ⟨fuel, ?_⟩
  generalize computed : ContextualFrameWorklist.run fuel origin (ContextualResidual.observeProblem missingDependencyProblem) = result at finished ⊢
  cases finished with
  | refuted impossible => rfl
  | solved update empty =>
      exact False.elim (missing_dependency_has_no_source_model update.declaration update.answer
        ((ContextualResidual.models_observeProblem _ _).mp (update.completed empty)))

theorem an_undeclared_argument_dependency_cannot_compile :
    ¬ Nonempty (Compiled queries locals (before := before) missingDependencyPlan selected) := by
  rintro ⟨compiled⟩
  obtain ⟨Future, future, candidate, model⟩ := compiled.source_admitted.solvable
  exact missing_dependency_has_no_source_model future candidate model

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClausePublication.BinderControls
