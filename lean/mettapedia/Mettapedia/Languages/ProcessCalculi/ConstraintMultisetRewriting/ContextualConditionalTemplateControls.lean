import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateExecution
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExtensionAmalgamation

/-!
# Mixed conditional publication with a dormant incompatible schema

The actor establishes X=0. It publishes a template pair(X,pair(Y,Y))
whose condition is X=0, another template conditioned by X=1, a shared
output, and an ordinary output. The incompatible schema stays latent;
its existence does not prevent the other outputs from being published.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualTemplateSource ContextualConditionalRows

inductive Operation where
  | literal : Nat → Operation
  | pair : Operation
  deriving DecidableEq

abbrev base : Signature where
  Srt := Unit
  Op _ := Operation
  arity
    | .literal _ => []
    | .pair => [([], ()), ([], ())]

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) := inferInstanceAs (DecidableEq Operation)

abbrev locals (impossible : Empty) : MetaArity base := nomatch impossible
abbrev inners (_ : Unit) : MetaArity base := ([], ())
abbrev captures (_ : Unit) : MetaArity base := ([], ())
abbrev bank := Expanded locals inners
abbrev actor := Actor locals captures
abbrev blueprint := Blueprint locals inners captures
abbrev active := Active locals inners captures

def literal {V : Type} {declaration : V → MetaArity base} {Γ : Ctx base} (number : Nat) :
    Term (signature base declaration) Γ () := .op (.inl (.literal number)) .nil

def pair {V : Type} {declaration : V → MetaArity base} {Γ : Ctx base}
    (left right : Term (signature base declaration) Γ ()) : Term (signature base declaration) Γ () :=
  .op (.inl .pair) (.cons left (.cons right .nil))

def actorX : Term (signature base actor) [] () := generator actor (.inr ())
def capturedX : Term (signature base blueprint) [] () := generator blueprint (.inr (.inr ()))
def privateY : Term (signature base blueprint) [] () := generator blueprint (.inl ())
def body : Term (signature base blueprint) [] () := pair capturedX (pair privateY privateY)
def conditions (number : Nat) : ContextualResidual.Problem blueprint :=
  [(observe capturedX, observe (literal (Γ := []) number))]

def code : ContextualTemplateSource.Rule locals inners captures [] () :=
  ⟨[], [], [(actorX, literal 0)], [], [.schema body, .schema body, .live actorX, .ordinary actorX]⟩

def sourceRule : ContextualConditionalTemplateSource.Rule locals inners captures [] () where
  code := code
  conditions := Fin.cases (conditions 0)
    (Fin.cases (conditions 1) (Fin.cases PUnit.unit (Fin.cases PUnit.unit (fun impossible => Fin.elim0 impossible))))

abbrev before : ContextualConditionalExecution.State bank Nat [] () :=
  ⟨Unit, inferInstance, captures, ∅, [], ∅, fun _ => ofStored bank captures (.live (literal 0))⟩

def chosen : Selection Nat := ⟨[], [], [10, 11, 12, 13]⟩
def rawRule := code.lower locals inners captures
def produced := (ContextualActivatedStep.prepared bank captures ∅ chosen rawRule (fun occurrence => (before.rows occurrence).value)).rule.produce
def outputs (occurrence : Nat) : Term (signature base active) [] () :=
  (ContextualTemplateSource.assign chosen.made produced occurrence).getD (literal 0)
def information := ContextualConditionalExecution.information bank captures ∅ chosen rawRule before.rows before.equations
def activeX : Term (signature base active) [] () := generator active (.inr ())

theorem information_explicit : information = [(observe activeX, observe (literal (Γ := []) 0))] := by
  with_unfolding_all rfl

def sourceModel {V : Type} (declaration : V → MetaArity base) : Assignment active declaration
  | .inl ⟨_, .inl impossible⟩ => nomatch impossible
  | .inl ⟨_, .inr (_, ())⟩ => literal 0
  | .inr () => literal 0

theorem source_model {V : Type} (declaration : V → MetaArity base) :
    ContextualResidual.Models (sourceModel declaration) information := by
  rw [information_explicit]
  intro equation member
  have same := List.mem_singleton.mp member
  subst equation
  rfl

theorem admitted : ContextualConditionalExecution.Admitted bank before rawRule chosen outputs := by
  refine ⟨by decide +kernel, by decide +kernel, rfl, rfl, ?_,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    ⟨Unit, captures, sourceModel captures, source_model captures⟩, ?_⟩
  · exact ContextualTemplateSource.assign_map chosen.made produced (fun _ => literal 0)
      (by decide +kernel) rfl
  · intro check member
    cases member

theorem an_actual_mixed_firing_exists (fuel : Nat) :
    ∃ firing : ContextualConditionalTemplateExecution.Firing locals inners before,
      firing.sourceRule = sourceRule ∧ firing.selection = chosen ∧ firing.execution.outputs = outputs ∧
        firing.execution.fuel = fuel ∧ firing.target.present = {10, 11, 12, 13} ∧
        ContextualConditionalExecution.Solvable firing.target.equations := by
  obtain ⟨firing, authored, selected, values, budget⟩ :=
    ContextualConditionalTemplateExecution.realize locals inners before sourceRule chosen outputs admitted fuel
  refine ⟨firing, authored, selected, values, budget, ?_, firing.target_solvable⟩
  rw [firing.physical_result, selected]
  decide +kernel

def reading {V : Type} (declaration : V → MetaArity base) (number : Nat) : Assignment actor declaration
  | .inl impossible => nomatch impossible
  | .inr () => literal number

def pattern {V : Type} {declaration : V → MetaArity base} (first second captured : Nat) :
    Term (signature base declaration) [] () := pair (literal captured) (pair (literal first) (literal second))

theorem source_has_private_instance {V : Type} (declaration : V → MetaArity base) (number : Nat) :
    Matches inners actor (reading declaration 0) (pattern number number 0) ⟨.schema body, conditions 0⟩ := by
  refine ⟨ContextualGuardMatching.Extension.identity declaration, (fun _ => literal number), ?_, rfl⟩
  intro equation member
  have only := List.mem_singleton.mp member
  subst equation
  rfl

theorem incompatible_source_row_has_no_instance {V : Type} (declaration : V → MetaArity base)
    (value : Term (signature base declaration) [] ()) :
    ¬ Matches inners actor (reading declaration 0) value ⟨.schema body, conditions 1⟩ := by
  rintro ⟨extension, _images, models, _same⟩
  have equation := models (observe capturedX, observe (literal (Γ := []) 1)) (List.mem_singleton_self _)
  change observe (literal (declaration := extension.declarations) (Γ := []) 0) = observe (literal 1) at equation
  have values := observe_injective equation
  have impossible : (0 : Nat) = 1 := Operation.literal.inj (Sum.inl.inj (Term.op.inj values).1)
  omega

private theorem pair_injective {V : Type} {declaration : V → MetaArity base}
    {first second third fourth : Term (signature base declaration) [] ()}
    (same : pair first second = pair third fourth) : first = third ∧ second = fourth := by
  have fields := Args.cons.inj (eq_of_heq (Term.op.inj same).2)
  exact ⟨fields.1, (Args.cons.inj fields.2).1⟩

theorem instantiate_body {V : Type} (declaration : V → MetaArity base) (images : Assignment blueprint declaration) :
    instantiate images body = pair (images (.inr (.inr ()))) (pair (images (.inl ())) (images (.inl ()))) := by
  change pair (instantiate images (generator blueprint (.inr (.inr ()))))
    (pair (instantiate images (generator blueprint (.inl ()))) (instantiate images (generator blueprint (.inl ())))) = _
  erw [instantiate_generator, instantiate_generator]

theorem one_use_cannot_split_private_alias {V : Type} (declaration : V → MetaArity base)
    (first second : Nat) (apart : first ≠ second) :
    ¬ Matches inners actor (reading declaration 0) (pattern first second 0) ⟨.schema body, conditions 0⟩ := by
  rintro ⟨extension, images, _conditions, same⟩
  change instantiate _ body = _ at same
  rw [instantiate_body] at same
  change pair (literal (declaration := extension.declarations) 0) (pair (images ()) (images ())) =
    pair (literal 0) (pair (literal first) (literal second)) at same
  have fields := pair_injective (pair_injective same).2
  have clash := fields.1.symm.trans fields.2
  exact apart (Operation.literal.inj (Sum.inl.inj (Term.op.inj clash).1))

theorem shared_capture_cannot_become_a_private_choice {V : Type} (declaration : V → MetaArity base)
    (number : Nat) :
    ¬ Matches inners actor (reading declaration 0) (pattern number number 1) ⟨.schema body, conditions 0⟩ := by
  rintro ⟨extension, images, _conditions, same⟩
  change instantiate _ body = _ at same
  rw [instantiate_body] at same
  change pair (literal (declaration := extension.declarations) 0) (pair (images ()) (images ())) =
    pair (literal 1) (pair (literal number) (literal number)) at same
  have impossible : (0 : Nat) = 1 := Operation.literal.inj (Sum.inl.inj (Term.op.inj (pair_injective same).1).1)
  omega

theorem dropping_the_row_condition_invents_an_answer {V : Type} (declaration : V → MetaArity base) :
    Matches inners actor (reading declaration 0) (pattern 0 0 0) ⟨.schema body, []⟩ ∧
      ¬ Matches inners actor (reading declaration 0) (pattern 0 0 0) ⟨.schema body, conditions 1⟩ := by
  constructor
  · exact ⟨ContextualGuardMatching.Extension.identity declaration, (fun _ => literal 0),
      (by intro equation member; cases member), rfl⟩
  · exact incompatible_source_row_has_no_instance declaration _

section Actual

variable (firing : ContextualConditionalTemplateExecution.Firing locals inners before)
    (authored : firing.sourceRule = sourceRule) (selected : firing.selection = chosen)

include authored selected

theorem first_descriptor : firing.descriptor 10 = some (0, ⟨.schema body, conditions 0⟩) := by
  change firing.sourceRule.outputsFor firing.selection.made 10 = _
  rw [authored, selected]
  rfl

theorem second_descriptor : firing.descriptor 11 = some (1, ⟨.schema body, conditions 1⟩) := by
  change firing.sourceRule.outputsFor firing.selection.made 11 = _
  rw [authored, selected]
  rfl

theorem captured_actor_is_zero {V : Type} (declaration : V → MetaArity base)
    (candidate : Assignment firing.target.declarations declaration)
    (model : ContextualResidual.Models candidate firing.target.equations) :
    Assignment.compose candidate (ContextualTemplatePublication.captureValues locals inners captures firing.update firing.scope) =
      reading declaration 0 := by
  have inherited := (ContextualResidual.models_mapProblem _ _ _).mp model
  have sameInformation : ContextualConditionalExecution.information bank captures ∅ firing.selection firing.execution.rule
      before.rows before.equations = information := by
    rw [firing.compiled, authored, selected]
    rfl
  have equation := inherited (observe activeX, observe (literal (Γ := []) 0)) (by
    erw [sameInformation, information_explicit]
    exact List.mem_singleton_self _)
  change observe (instantiate (Assignment.compose candidate (ContextualComputedFreshFrame.includeSource firing.update)) activeX) =
    observe (literal (declaration := declaration) (Γ := []) 0) at equation
  have value := observe_injective equation
  funext name
  cases name with
  | inl impossible => exact nomatch impossible
  | inr name =>
      cases name
      change instantiate candidate
        (instantiate (ContextualComputedFreshFrame.includeSource firing.update)
          (actorAt locals inners captures firing.scope (.inr ()))) = literal 0
      rw [actorAt_shared]
      exact (Assignment.instantiate_compose candidate (ContextualComputedFreshFrame.includeSource firing.update) activeX).symm.trans value

theorem good_template_has_independent_private_instances {V : Type} (declaration : V → MetaArity base)
    (candidate : Assignment firing.target.declarations declaration)
    (model : ContextualResidual.Models candidate firing.target.equations) (number : Nat) :
    Matches (ContextualPublication.privateFamily bank firing.update.declaration) firing.target.declarations candidate
      (pattern number number 0) (firing.target.rows 10) := by
  apply (firing.schema_matches_source 10 0 body (conditions 0) (first_descriptor firing authored selected)
    declaration candidate _).mpr
  rw [captured_actor_is_zero firing authored selected declaration candidate model]
  exact source_has_private_instance declaration number

theorem bad_template_stays_latent_and_unmatched {V : Type} (declaration : V → MetaArity base)
    (candidate : Assignment firing.target.declarations declaration)
    (model : ContextualResidual.Models candidate firing.target.equations)
    (value : Term (signature base declaration) [] ()) :
    ¬ Matches (ContextualPublication.privateFamily bank firing.update.declaration) firing.target.declarations candidate
      value (firing.target.rows 11) := by
  intro matched
  have source := (firing.schema_matches_source 11 1 body (conditions 1) (second_descriptor firing authored selected)
    declaration candidate value).mp matched
  rw [captured_actor_is_zero firing authored selected declaration candidate model] at source
  exact incompatible_source_row_has_no_instance declaration value source

theorem a_private_alias_remains_one_within_each_use {V : Type} (declaration : V → MetaArity base)
    (candidate : Assignment firing.target.declarations declaration)
    (model : ContextualResidual.Models candidate firing.target.equations) (first second : Nat) (apart : first ≠ second) :
    ¬ Matches (ContextualPublication.privateFamily bank firing.update.declaration) firing.target.declarations candidate
      (pattern first second 0) (firing.target.rows 10) := by
  intro matched
  have source := (firing.schema_matches_source 10 0 body (conditions 0) (first_descriptor firing authored selected)
    declaration candidate _).mp matched
  rw [captured_actor_is_zero firing authored selected declaration candidate model] at source
  exact one_use_cannot_split_private_alias declaration first second apart source

theorem published_capture_cannot_be_rechosen {V : Type} (declaration : V → MetaArity base)
    (candidate : Assignment firing.target.declarations declaration)
    (model : ContextualResidual.Models candidate firing.target.equations) (number : Nat) :
    ¬ Matches (ContextualPublication.privateFamily bank firing.update.declaration) firing.target.declarations candidate
      (pattern number number 1) (firing.target.rows 10) := by
  intro matched
  have source := (firing.schema_matches_source 10 0 body (conditions 0) (first_descriptor firing authored selected)
    declaration candidate _).mp matched
  rw [captured_actor_is_zero firing authored selected declaration candidate model] at source
  exact shared_capture_cannot_become_a_private_choice declaration number source

end Actual

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateControls
