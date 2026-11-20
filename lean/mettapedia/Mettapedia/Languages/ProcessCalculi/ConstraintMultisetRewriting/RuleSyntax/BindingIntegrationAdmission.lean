import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PrincipalStep
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualUnifierProfiles
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFreshAnswer
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Contextual

/-!
# Certified contextual solver steps retain the residual admission problem

A principal answer for one selected equation does not have to solve all the
other equations in a firing. The remaining equations are transported to an
actual residual store. Admission before and after that solver step agrees
when its retained interface contains both sides of every remaining equation,
every check argument and every observed occurrence label. Resource identities
and the original output-shape tests remain explicit.

The binding and distinct-variable-spine applications below consume the
existing executable solver's actual success result. The flexible-pair
application consumes its existing scope pullback and fresh-helper answer.
No general higher-order solver or failure-as-inconsistency principle is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.BindingIntegration

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

namespace Admission

universe uT uS uO
variable {T : Type uT} {Sub : Type uS} {O : Type uO}

section Residual

variable (A : SubstitutionAction T Sub)
  {solvedPart problem : EquationStore T} {answer : Sub} {observed : List T}

/-- Factor a model of the entire firing, retaining the unsolved equations.
Only the selected part has been solved by the principal answer. -/
theorem residual_model
    (principal : A.PrincipalOn solvedPart answer observed)
    (included : ∀ equation ∈ solvedPart, equation ∈ problem)
    (equations : ∀ equation ∈ problem, equation.1 ∈ observed ∧ equation.2 ∈ observed)
    {candidate : Sub} (model : A.Models candidate problem) :
    ∃ residual, A.Models residual (A.applyStore answer problem) ∧
      ∀ term ∈ observed,
        A.E (A.apply candidate term) (A.apply (A.compose residual answer) term) := by
  obtain ⟨residual, through⟩ := principal.factors candidate
    (fun equation member => model equation (included equation member))
  refine ⟨residual, (A.models_applyStore residual answer problem).mpr ?_, through⟩
  intro equation member
  exact A.equivalence.trans (A.equivalence.symm (through equation.1 (equations equation member).1))
    (A.equivalence.trans (model equation member) (through equation.2 (equations equation member).2))

theorem residual_consistent_iff
    (principal : A.PrincipalOn solvedPart answer observed)
    (included : ∀ equation ∈ solvedPart, equation ∈ problem)
    (equations : ∀ equation ∈ problem, equation.1 ∈ observed ∧ equation.2 ∈ observed) :
    A.Consistent problem ↔ A.Consistent (A.applyStore answer problem) := by
  constructor
  · rintro ⟨candidate, model⟩
    obtain ⟨residual, models, _⟩ := residual_model A principal included equations model
    exact ⟨residual, models⟩
  · rintro ⟨residual, models⟩
    exact ⟨A.compose residual answer, (A.models_applyStore residual answer problem).mp models⟩

theorem residual_check_iff
    (principal : A.PrincipalOn solvedPart answer observed)
    (included : ∀ equation ∈ solvedPart, equation ∈ problem)
    (equations : ∀ equation ∈ problem, equation.1 ∈ observed ∧ equation.2 ∈ observed)
    (label : O → T) (world : Finset O) (check : Check T)
    (arguments : ∀ term ∈ check.terms, term ∈ observed)
    (values : ∀ occurrence ∈ world, label occurrence ∈ observed) :
    A.Entails problem (fun candidate => check.Holds A candidate label world) ↔
      A.Entails (A.applyStore answer problem)
        (fun residual => (check.map (A.apply answer)).Holds A residual
          (fun occurrence => A.apply answer (label occurrence)) world) := by
  constructor
  · intro original residual models
    exact (SubstitutionStability.check_map A residual answer label world check).mpr
      (original (A.compose residual answer) ((A.models_applyStore residual answer problem).mp models))
  · intro transported candidate model
    obtain ⟨residual, residualModels, through⟩ := residual_model A principal included equations model
    have holds := (SubstitutionStability.check_map A residual answer label world check).mp
      (transported residual residualModels)
    exact (Check.holds_congr A candidate (A.compose residual answer) label world check
      (fun term member => through term (arguments term member))
      (fun occurrence member => through (label occurrence) (values occurrence member))).mpr holds

end Residual

section Occurrences

/-- The retained interface is computed from the actual firing: equations,
check arguments and the entire pre-firing observation world. -/
noncomputable def retained (label : O → T) (rule : RuleInstance T) (selection : Selection O)
    (before : Configuration T O) : List T :=
  (selection.problem label rule before).flatMap (fun equation => [equation.1, equation.2]) ++
    rule.checks.flatMap Check.terms ++ before.present.toList.map label

theorem retained_equations (label : O → T) (rule : RuleInstance T) (selection : Selection O)
    (before : Configuration T O) (equation : Equation T)
    (member : equation ∈ selection.problem label rule before) :
    equation.1 ∈ retained label rule selection before ∧ equation.2 ∈ retained label rule selection before := by
  constructor
  · exact List.mem_append_left _ (List.mem_append_left _
      (List.mem_flatMap.mpr ⟨equation, member, by simp⟩))
  · exact List.mem_append_left _ (List.mem_append_left _
      (List.mem_flatMap.mpr ⟨equation, member, by simp⟩))

theorem retained_arguments (label : O → T) (rule : RuleInstance T) (selection : Selection O)
    (before : Configuration T O) (check : Check T) (member : check ∈ rule.checks)
    (term : T) (argument : term ∈ check.terms) : term ∈ retained label rule selection before :=
  List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨check, member, argument⟩))

theorem retained_values (label : O → T) (rule : RuleInstance T) (selection : Selection O)
    (before : Configuration T O) (occurrence : O) (member : occurrence ∈ before.present) :
    label occurrence ∈ retained label rule selection before :=
  List.mem_append_right _ (List.mem_map.mpr ⟨occurrence, Finset.mem_toList.mpr member, rfl⟩)

variable [DecidableEq O]

/-- A certified solver step preserves and reflects actual admission while
the rest of the firing's knowledge remains an explicit residual problem. -/
theorem valid_iff_of_principal_prefix (A : SubstitutionAction T Sub) (label : O → T)
    {rule : RuleInstance T} {selection : Selection O} {before : Configuration T O}
    {solvedPart : EquationStore T} {answer : Sub}
    (principal : A.PrincipalOn solvedPart answer (retained label rule selection before))
    (included : ∀ equation ∈ solvedPart, equation ∈ selection.problem label rule before)
    (shape : (ShapeTest.ofSelection rule selection).Holds label)
    (enabled : Enabled label before.present selection.commit) :
    selection.Valid A label rule before ↔
      selection.Valid A (fun occurrence => A.apply answer (label occurrence))
        (rule.map (A.apply answer)) (SubstitutionStability.configuration A answer before) := by
  have consistency := residual_consistent_iff A principal included
    (retained_equations label rule selection before)
  constructor
  · intro valid
    exact SubstitutionStability.valid_map A answer label valid (consistency.mp valid.consistent)
  · intro valid
    refine ⟨shape.1, shape.2.1, shape.2.2.1, shape.2.2.2.1, shape.2.2.2.2,
      enabled, consistency.mpr ?_, ?_⟩
    · simpa only [SubstitutionStability.problem_map] using valid.consistent
    · intro check member
      apply (residual_check_iff A principal included (retained_equations label rule selection before)
        label before.present check (retained_arguments label rule selection before check member)
        (retained_values label rule selection before)).mpr
      intro residual models
      have checks := valid.checks (check.map (A.apply answer))
        (List.mem_map.mpr ⟨check, member, rfl⟩) residual
      rw [SubstitutionStability.problem_map] at checks
      exact checks models

theorem step_of_residual_valid (A : SubstitutionAction T Sub) (label : O → T)
    {rule : RuleInstance T} {selection : Selection O} {before : Configuration T O}
    {solvedPart : EquationStore T} {answer : Sub}
    (principal : A.PrincipalOn solvedPart answer (retained label rule selection before))
    (included : ∀ equation ∈ solvedPart, equation ∈ selection.problem label rule before)
    (shape : (ShapeTest.ofSelection rule selection).Holds label)
    (enabled : Enabled label before.present selection.commit)
    (valid : selection.Valid A (fun occurrence => A.apply answer (label occurrence))
      (rule.map (A.apply answer)) (SubstitutionStability.configuration A answer before)) :
    Step A label rule before (selection.result label rule before) :=
  ⟨selection, (valid_iff_of_principal_prefix A label principal included shape enabled).mpr valid, rfl⟩

end Occurrences

section Contextual

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

variable {S : Signature} {V : Type} [DecidableEq V]
  {declaration : V → MetaArity S} {O : Type} [DecidableEq O]

/-- Executable binding success supplies the principal-prefix certificate.
Other equations, including unresolved metavariables, are not dropped. -/
theorem binding_admission_iff (identity : V)
    (body : Term (signature S declaration) (declaration identity).1 (declaration identity).2)
    {answer : Assignment declaration declaration}
    (solved : ContextualBinding.solve? identity body = some answer)
    (label : O → Term (signature S declaration) (declaration identity).1 (declaration identity).2)
    (rule : RuleInstance (Term (signature S declaration) (declaration identity).1 (declaration identity).2))
    (selection : Selection O)
    (before : Configuration (Term (signature S declaration) (declaration identity).1 (declaration identity).2) O)
    (selected : (generator declaration identity, body) ∈ selection.problem label rule before)
    (shape : (ShapeTest.ofSelection rule selection).Holds label)
    (enabled : Enabled label before.present selection.commit) :
    selection.Valid (ContextualFamilies.action declaration (declaration identity).1 (declaration identity).2)
      label rule before ↔
    selection.Valid (ContextualFamilies.action declaration (declaration identity).1 (declaration identity).2)
      (fun occurrence => instantiate answer (label occurrence)) (rule.map (instantiate answer))
      (SubstitutionStability.configuration
        (ContextualFamilies.action declaration (declaration identity).1 (declaration identity).2) answer before) := by
  apply valid_iff_of_principal_prefix _ label
    (SubstitutionAction.Principal.on _ (ContextualBinding.solve_principal solved)
      (retained label rule selection before))
  · intro equation member
    exact (List.mem_singleton.mp member) ▸ selected
  · exact shape
  · exact enabled

/-- The recoverable distinct-variable-spine case has the same actual
admission theorem; the strengthener is not supplied for arbitrary spines. -/
theorem spine_admission_iff (identity : V) {context : Ctx S}
    (rho : Ren S (declaration identity).1 context)
    (inverse : Strengthener (S := signature S declaration) rho)
    (target : Term (signature S declaration) context (declaration identity).2)
    {answer : Assignment declaration declaration}
    (solved : ContextualPatternBinding.solve? identity rho inverse target = some answer)
    (label : O → Term (signature S declaration) context (declaration identity).2)
    (rule : RuleInstance (Term (signature S declaration) context (declaration identity).2))
    (selection : Selection O)
    (before : Configuration (Term (signature S declaration) context (declaration identity).2) O)
    (selected : (rename (S := signature S declaration) rho (generator declaration identity), target) ∈
      selection.problem label rule before)
    (shape : (ShapeTest.ofSelection rule selection).Holds label)
    (enabled : Enabled label before.present selection.commit) :
    selection.Valid (ContextualFamilies.action declaration context (declaration identity).2) label rule before ↔
      selection.Valid (ContextualFamilies.action declaration context (declaration identity).2)
        (fun occurrence => instantiate answer (label occurrence)) (rule.map (instantiate answer))
        (SubstitutionStability.configuration
          (ContextualFamilies.action declaration context (declaration identity).2) answer before) := by
  apply valid_iff_of_principal_prefix _ label
    (SubstitutionAction.Principal.on _
      (ContextualPatternBinding.solve_principal identity rho inverse target solved)
      (retained label rule selection before))
  · intro equation member
    exact (List.mem_singleton.mp member) ▸ selected
  · exact shape
  · exact enabled

end Contextual

section FreshHelper

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualFreshAnswer

variable {S : Signature} {Other : Type} {L R context : Ctx S}
  {left : Ren S L context} {right : Ren S R context}
  {O : Type} [DecidableEq O]

/-- The distinct-hole solver introduces its own fresh helper. Only old-frame
observations may be factored through it; the helper's independent value is
not assumed to have existed in the source. -/
theorem flexible_pair_admission_iff (pullback : ScopePullback left right)
    (result : S.Srt) (others : Other → MetaArity S)
    (observed : List (Term (signature S (oldDeclarations L R result others)) context result))
    (label : O → Term (signature S (activeDeclarations L R pullback.context result others)) context result)
    (rule : RuleInstance
      (Term (signature S (activeDeclarations L R pullback.context result others)) context result))
    (selection : Selection O)
    (before : Configuration
      (Term (signature S (activeDeclarations L R pullback.context result others)) context result) O)
    (selected : ∀ equation ∈ problem (left := left) (right := right) pullback.context result others,
      equation ∈ selection.problem label rule before)
    (covered : ∀ term ∈ retained label rule selection before,
      term ∈ observed.map (instantiate (includeOld pullback.context result others)))
    (shape : (ShapeTest.ofSelection rule selection).Holds label)
    (enabled : Enabled label before.present selection.commit) :
    selection.Valid (ContextualFamilies.action (activeDeclarations L R pullback.context result others) context result)
      label rule before ↔
      selection.Valid
        (ContextualFamilies.action (activeDeclarations L R pullback.context result others) context result)
        (fun occurrence => instantiate (answer pullback result others) (label occurrence))
        (rule.map (instantiate (answer pullback result others)))
        (SubstitutionStability.configuration
          (ContextualFamilies.action (activeDeclarations L R pullback.context result others) context result)
          (answer pullback result others) before) := by
  apply valid_iff_of_principal_prefix _ label
    (SubstitutionAction.PrincipalOn.restrict _ (principal_on pullback result others observed) covered)
  · exact selected
  · exact shape
  · exact enabled

end FreshHelper

namespace Frames

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

variable {S : Signature} {V W : Type}
  {source : V → MetaArity S} {target : W → MetaArity S}
  {context : Ctx S} {sort : S.Srt}

/-- Pack the real contextual equations into the heterogeneous observation
carrier used by rule firings, schematic rows and worlds. -/
def observedProblem (problem : EquationStore (Term (signature S source) context sort)) :
    EquationStore (Observation S source) :=
  problem.map fun equation => (observe equation.1, observe equation.2)

theorem observed_models_iff {Future : Type} {future : Future → MetaArity S}
    (candidate : Assignment source future)
    (problem : EquationStore (Term (signature S source) context sort)) :
    (Interface.Frames.contextual S).Models (a := ⟨V, source⟩) (b := ⟨Future, future⟩)
      candidate (observedProblem problem) ↔ ContextualFrameUnifier.Models candidate problem := by
  constructor
  · intro model equation member
    exact observe_injective (model _ (List.mem_map.mpr ⟨equation, member, rfl⟩))
  · intro model equation member
    obtain ⟨original, inside, rfl⟩ := List.mem_map.mp member
    exact congrArg observe (model original inside)

/-- A certified solver case factors every contextual observation, including
terms at indices other than the particular equation's context and sort. -/
theorem observed_principal
    {problem : EquationStore (Term (signature S source) context sort)}
    {answer : Assignment source target}
    (principal : ContextualFrameUnifier.Principal problem answer) :
    (Interface.Frames.contextual S).Principal (a := ⟨V, source⟩) (m := ⟨W, target⟩)
      (observedProblem problem) answer := by
  refine ⟨(observed_models_iff answer problem).mpr principal.sound, ?_⟩
  intro future candidate model
  obtain ⟨residual, components⟩ := principal.factors future.arity candidate
    ((observed_models_iff candidate problem).mp model)
  refine ⟨residual, ?_⟩
  intro observation
  change instantiateObservation candidate observation =
    instantiateObservation (Assignment.compose residual answer) observation
  rw [← instantiateObservation_comp]
  exact factor_observation candidate answer residual components observation

/-- The actual information store may contain further equations at arbitrary
context/sort indices. They survive as residual knowledge in the solver's
target frame; the complete caller substitution is retained. -/
theorem observed_residual_models_iff
    {problem : EquationStore (Term (signature S source) context sort)}
    {answer : Assignment source target}
    (principal : ContextualFrameUnifier.Principal problem answer)
    (information : EquationStore (Observation S source))
    (included : ∀ equation ∈ observedProblem problem, equation ∈ information)
    {Future : Type} {future : Future → MetaArity S} (candidate : Assignment source future) :
    (Interface.Frames.contextual S).Models (a := ⟨V, source⟩) (b := ⟨Future, future⟩)
      candidate information ↔
      ∃ residual : Assignment target future,
        (Interface.Frames.contextual S).Models (a := ⟨W, target⟩) (b := ⟨Future, future⟩)
          residual ((Interface.Frames.contextual S).applyStore (a := ⟨V, source⟩) (b := ⟨W, target⟩) answer information) ∧
        candidate = Assignment.compose residual answer := by
  constructor
  · intro model
    obtain ⟨residual, components⟩ := principal.factors future candidate
      ((observed_models_iff candidate problem).mp (fun equation member => model equation (included equation member)))
    have same : candidate = Assignment.compose residual answer := funext components
    refine ⟨residual, ?_, same⟩
    apply (Interface.Frames.models_applyStore (X := Interface.Frames.contextual S)
      (a := ⟨V, source⟩) (b := ⟨W, target⟩) (c := ⟨Future, future⟩) answer residual information).mpr
    change (Interface.Frames.contextual S).Models (a := ⟨V, source⟩) (b := ⟨Future, future⟩)
      (Assignment.compose residual answer) information
    rwa [← same]
  · rintro ⟨residual, model, rfl⟩
    exact (Interface.Frames.models_applyStore (X := Interface.Frames.contextual S)
      (a := ⟨V, source⟩) (b := ⟨W, target⟩) (c := ⟨Future, future⟩) answer residual information).mp model

theorem observed_residual_solvable_iff
    {problem : EquationStore (Term (signature S source) context sort)}
    {answer : Assignment source target}
    (principal : ContextualFrameUnifier.Principal problem answer)
    (information : EquationStore (Observation S source))
    (included : ∀ equation ∈ observedProblem problem, equation ∈ information) :
    (Interface.Frames.contextual S).Solvable (a := ⟨V, source⟩) information ↔
      (Interface.Frames.contextual S).Solvable (a := ⟨W, target⟩)
        ((Interface.Frames.contextual S).applyStore (a := ⟨V, source⟩) (b := ⟨W, target⟩) answer information) := by
  constructor
  · rintro ⟨future, candidate, model⟩
    obtain ⟨residual, residualModel, _⟩ :=
      (observed_residual_models_iff principal information included candidate).mp model
    exact ⟨future, residual, residualModel⟩
  · exact Interface.Frames.solvable_of_applyStore (X := Interface.Frames.contextual S)
      (a := ⟨V, source⟩) (b := ⟨W, target⟩) answer

section Firings

variable {O : Type} [DecidableEq O]
  {E : Extensions (fun F G : Interface.Frames.Frame S => Assignment F.arity G.arity)}
  {P : Program (Contextual.Terms S)} (state : State (Contextual.Terms S) O)
  (firing : Firing O E P state.frame)
  {Result : Type} {result : Result → MetaArity S}
  {context : Ctx S} {sort : S.Srt}

/-- A solver certificate is applied to the actual information of the
opened firing. Universal checks and collect observations are still asked at
every residual solution, with no closed-term or one-frame assumption. -/
theorem firing_admission_iff
    (problem : EquationStore (Term (signature S (E.target firing.ext).arity) context sort))
    (answer : Assignment (E.target firing.ext).arity result)
    (principal : ContextualFrameUnifier.Principal problem answer)
    (included : ∀ equation ∈ observedProblem problem,
      equation ∈ firing.information (Interface.Frames.contextual S) state) :
    firing.Admits (Interface.Frames.contextual S) state ↔
      firing.Shapes (Interface.Frames.contextual S) state ∧
      Enabled (fun _ : O => ()) state.present (firing.selection.commit (T := Unit)) ∧
      (Interface.Frames.contextual S).Solvable (a := ⟨Result, result⟩)
        ((Interface.Frames.contextual S).applyStore
          (a := E.target firing.ext) (b := ⟨Result, result⟩) answer
          (firing.information (Interface.Frames.contextual S) state)) ∧
      ∀ (future : Interface.Frames.Frame S) (residual : Assignment result future.arity),
        (Interface.Frames.contextual S).Models
          (a := ⟨Result, result⟩) (b := future) residual
          ((Interface.Frames.contextual S).applyStore
          (a := E.target firing.ext) (b := ⟨Result, result⟩) answer
            (firing.information (Interface.Frames.contextual S) state)) →
        firing.Holds (Interface.Frames.contextual S) state (Assignment.compose residual answer) := by
  have solvability := observed_residual_solvable_iff principal
    (firing.information (Interface.Frames.contextual S) state) included
  constructor
  · rintro ⟨shape, enabled, solvable, checks⟩
    refine ⟨shape, enabled, solvability.mp solvable, ?_⟩
    intro future residual model
    exact checks future (Assignment.compose residual answer)
      ((Interface.Frames.models_applyStore (X := Interface.Frames.contextual S)
        (a := E.target firing.ext) (b := ⟨Result, result⟩) (c := future) answer residual _).mp model)
  · rintro ⟨shape, enabled, solvable, checks⟩
    refine ⟨shape, enabled, solvability.mpr solvable, ?_⟩
    intro future candidate model
    obtain ⟨residual, residualModel, same⟩ :=
      (observed_residual_models_iff principal
        (firing.information (Interface.Frames.contextual S) state) included candidate).mp model
    rw [same]
    exact checks future residual residualModel

end Firings

end Frames

namespace Controls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

inductive Op : Unit → Type where
  | constant : Op ()
  | pair : Op ()
  | binder : Op ()

def base : Signature where
  Srt := Unit
  Op := Op
  arity operator := match operator with
    | .constant => []
    | .pair => [([], ()), ([], ())]
    | .binder => [([()], ())]

def declaration (name : Nat) : MetaArity base :=
  if name = 0 then ([()], ()) else ([], ())

abbrev context : Ctx base := [()]
abbrev Ty := Term (signature base declaration) context ()
abbrev A := ContextualFamilies.action declaration context ()

def hole : Ty := generator declaration 0
def pending : Ty := .op (.inr (.mk 1)) .nil
def constant : Ty := .op (.inl .constant) .nil

/-- The nested binder uses its own variable and the outer object variable;
the second metavariable remains a separate declaration in its body. -/
def body : Ty := .op (.inl .binder) (.cons
  (.op (.inl .pair) (.cons (.var .zero) (.cons
    (.op (.inl .pair) (.cons (.var (.succ .zero))
      (.cons (.op (.inr (.mk 1)) .nil) .nil))) .nil))) .nil)

def answer := ContextualBinding.answer 0 body

theorem binding_solver_succeeds : ContextualBinding.solve? 0 body = some answer := by
  change (if (0 : Nat) ∈ support body then none else some answer) = some answer
  simp [body, support, supportArgs]

def label : Nat → Ty
  | 0 => body
  | _ => hole

def rule : RuleInstance Ty := ⟨[], [hole], [], [.count body 1], [hole]⟩
def selection : Selection Nat := ⟨[], [0], [1]⟩
def initial : Configuration Ty Nat := ⟨[(pending, constant)], {0}⟩

theorem selected_binding_is_in_problem : (hole, body) ∈ selection.problem label rule initial := by
  change (hole, body) ∈ [(pending, constant), (hole, body)]
  simp

theorem initial_shape : (ShapeTest.ofSelection rule selection).Holds label := by
  exact ⟨by decide, by decide, rfl, rfl, rfl⟩

theorem initial_enabled : Enabled label initial.present selection.commit := by decide

/-- The selected binding has an exact admission transport even though its
answer deliberately does not solve the other equation in the store. -/
theorem nested_binding_admission_iff :
    selection.Valid A label rule initial ↔
      selection.Valid A (fun occurrence => instantiate answer (label occurrence))
        (rule.map (instantiate answer)) (SubstitutionStability.configuration A answer initial) :=
  binding_admission_iff 0 body binding_solver_succeeds label rule selection initial
    selected_binding_is_in_problem initial_shape initial_enabled

theorem pending_declaration_is_not_bound : instantiate answer pending = pending := rfl

theorem binding_answer_does_not_solve_the_remaining_equation :
    ¬ A.Models answer initial.equations := by
  intro model
  have impossible := model (pending, constant) (by simp [initial])
  change pending = constant at impossible
  have heads := (Term.op.inj impossible).1
  cases heads

theorem residual_equation_is_retained :
    (SubstitutionStability.configuration A answer initial).equations = [(pending, constant)] := rfl

def residual : Assignment declaration declaration :=
  ContextualBinding.answer 1 (.op (.inl .constant) .nil)

/-- The residual witness solves the pending equation. The first answer
therefore need not be a model of the whole firing by itself. -/
theorem actual_residual_selection_is_valid :
    selection.Valid A (fun occurrence => instantiate answer (label occurrence))
      (rule.map (instantiate answer)) (SubstitutionStability.configuration A answer initial) := by
  refine ⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨residual, ?_⟩, ?_⟩
  · change A.Models residual [(pending, constant), (body, body)]
    intro equation member
    rcases List.mem_cons.mp member with same | member
    · subst equation
      rfl
    · have same := List.mem_singleton.mp member
      subst equation
      rfl
  · intro check member candidate _
    change check ∈ [.count body 1] at member
    have same := List.mem_singleton.mp member
    subst check
    classical
    change (Check.matches A candidate (fun occurrence => instantiate answer (label occurrence)) {0} body).card = 1
    have region : Check.matches A candidate
        (fun occurrence => instantiate answer (label occurrence)) {0} body = {0} := by
      apply Finset.filter_eq_self.mpr
      intro occurrence member
      have same : occurrence = 0 := Finset.mem_singleton.mp member
      subst occurrence
      rfl
    rw [region]
    rfl

theorem nested_binding_fires : Step A label rule initial (selection.result label rule initial) :=
  ⟨selection, nested_binding_admission_iff.mpr actual_residual_selection_is_valid, rfl⟩

theorem nested_binding_keeps_the_read_occurrence :
    0 ∈ (selection.result label rule initial).present := by decide

theorem nested_binding_output_is_observed_under_the_answer : instantiate answer (label 1) = body := rfl

theorem nested_binding_keeps_the_actual_equations :
    (selection.result label rule initial).equations = [(pending, constant), (hole, body)] := rfl

end Controls

end Admission

#print axioms Admission.residual_model
#print axioms Admission.valid_iff_of_principal_prefix
#print axioms Admission.binding_admission_iff
#print axioms Admission.spine_admission_iff
#print axioms Admission.flexible_pair_admission_iff
#print axioms Admission.Frames.observed_principal
#print axioms Admission.Frames.observed_residual_models_iff
#print axioms Admission.Frames.firing_admission_iff
#print axioms Admission.Controls.nested_binding_admission_iff
#print axioms Admission.Controls.binding_answer_does_not_solve_the_remaining_equation
#print axioms Admission.Controls.nested_binding_fires

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.BindingIntegration
