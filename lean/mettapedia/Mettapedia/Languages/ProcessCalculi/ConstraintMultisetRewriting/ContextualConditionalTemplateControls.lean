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
  ⟨[], [], [(actorX, literal 0)], [], [.schema body, .schema body, .shared actorX, .ordinary actorX]⟩

def sourceRule : ContextualConditionalTemplateSource.Rule locals inners captures [] () where
  code := code
  conditions := Fin.cases (conditions 0)
    (Fin.cases (conditions 1) (Fin.cases PUnit.unit (Fin.cases PUnit.unit (fun impossible => Fin.elim0 impossible))))

abbrev before : ContextualConditionalExecution.State bank Nat [] () :=
  ⟨Unit, inferInstance, captures, ∅, [], ∅, fun _ => ofStored bank captures (.shared (literal 0))⟩

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
    ∃ firing : ContextualConditionalTemplateExecution.CompiledTemplate locals inners before,
      firing.sourceRule = sourceRule ∧ firing.selection = chosen ∧ firing.publication.firing.outputs = outputs ∧
        firing.publication.firing.fuel = fuel ∧ firing.target.present = {10, 11, 12, 13} ∧
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

variable (firing : ContextualConditionalTemplateExecution.CompiledTemplate locals inners before)
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
  have sameInformation : ContextualConditionalExecution.information bank captures ∅ firing.selection firing.publication.firing.rule
      before.rows before.equations = information := by
    have lowered := congrArg
      (fun rule : ContextualConditionalTemplateSource.Rule locals inners captures [] () =>
        rule.code.lower locals inners captures) authored
    have pinned : firing.publication.firing.rule = sourceRule.code.lower locals inners captures :=
      firing.publication.authored.trans lowered
    rw [pinned, selected]
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

namespace ReuseContracts

/-- An actual nonempty computation witnesses the observer distinction:
changing an off-output flag preserves all returned rows and the produced-port
contract, but violates the original exact-function contract. -/
theorem actual_port_contract_forgets_off_output_flags (fuel : Nat) :
    ∃ firing : ContextualConditionalExecution.Firing bank before,
      firing.fuel = fuel ∧
        ∃ published : ContextualConditionalExecution.Published bank before firing.rule firing.selection firing.outputs
          (.made (firing.selection.made.map firing.reusable)),
          HEq published.firing.target.rows firing.target.rows ∧
            ¬ (ContextualConditionalExecution.ReuseIntent.all firing.reusable).Holds
              firing.selection.made published.firing.reusable := by
  obtain ⟨compiled, _authored, selected, _values, budget, _present, _solvable⟩ := an_actual_mixed_firing_exists fuel
  let firing := compiled.publication.firing
  let reuse : Nat → Bool := fun occurrence => if occurrence = 0 then !firing.reusable occurrence else firing.reusable occurrence
  have outside : 0 ∉ firing.selection.made := by
    change 0 ∉ compiled.selection.made
    rw [selected]
    decide +kernel
  have same : ∀ occurrence ∈ firing.selection.made, reuse occurrence = firing.reusable occurrence := by
    intro occurrence made
    have different : occurrence ≠ 0 := by
      intro equal
      exact outside (equal ▸ made)
    exact if_neg different
  let published : ContextualConditionalExecution.Published bank before firing.rule firing.selection firing.outputs
      (.made (firing.selection.made.map firing.reusable)) :=
    ⟨firing.withReuse reuse, rfl, rfl, rfl, List.map_congr_left same⟩
  refine ⟨firing, budget, published, heq_of_eq (firing.withReuse_rows reuse same), ?_⟩
  intro exactFlags
  have atZero := congrFun exactFlags 0
  change (if (0 : Nat) = 0 then !firing.reusable 0 else firing.reusable 0) = firing.reusable 0 at atZero
  rw [if_pos rfl] at atZero
  cases value : firing.reusable 0 <;> simp [value] at atZero

end ReuseContracts

namespace PublicationBoundary

variable (compiled : ContextualConditionalTemplateExecution.CompiledTemplate locals inners before)
    (authored : compiled.sourceRule = sourceRule) (selected : compiled.selection = chosen)

include authored selected in
/-- The raw solver-backed target stores this schema-shaped output as a shared
value. Its row has an instance at every model, whereas the declared
conditional publication retains the incompatible local condition. -/
theorem raw_target_and_publication_disagree {V : Type} (declaration : V → MetaArity base)
    (candidate : Assignment compiled.target.declarations declaration)
    (model : ContextualResidual.Models candidate compiled.target.equations) :
    ∃ value : Term (signature base declaration) [] (),
      Matches (ContextualPublication.privateFamily bank compiled.update.declaration)
        compiled.target.declarations candidate value (compiled.publication.firing.target.rows 11) ∧
      ¬ Matches (ContextualPublication.privateFamily bank compiled.update.declaration)
        compiled.target.declarations candidate value (compiled.target.rows 11) := by
  have made : 11 ∈ compiled.publication.firing.selection.made := by
    change 11 ∈ compiled.selection.made
    rw [selected]
    decide +kernel
  have isShared : compiled.publication.firing.reusable 11 = false := by
    rw [compiled.reuse_intent]
    change compiled.sourceRule.ordinaryFlags compiled.selection.made 11 = false
    rw [authored, selected]
    rfl
  refine ⟨instantiate candidate
    (instantiate (ContextualComputedFreshFrame.includeSource compiled.update)
      (compiled.publication.firing.outputs 11)), ?_, ?_⟩
  · rw [compiled.publication.firing.shared_row 11 made isShared]
    erw [ofStored_matches_iff, ContextualGuardMatching.shared_matches_iff]
  · exact bad_template_stays_latent_and_unmatched compiled authored selected declaration candidate model _

/-- This is an actual finite-budget execution with a model, not an
uninhabited interface or a hypothetical row overlay. -/
theorem an_actual_publication_differs_from_its_raw_target (fuel : Nat) :
    ∃ compiled : ContextualConditionalTemplateExecution.CompiledTemplate locals inners before,
      compiled.publication.firing.fuel = fuel ∧
      compiled.target.rows ≠ compiled.publication.firing.target.rows := by
  obtain ⟨compiled, authored, selected, _outputs, budget, _present, consistent⟩ := an_actual_mixed_firing_exists fuel
  refine ⟨compiled, budget, ?_⟩
  intro same
  obtain ⟨V, declaration, candidate, model⟩ := consistent
  obtain ⟨value, raw, rejected⟩ := raw_target_and_publication_disagree compiled authored selected declaration candidate model
  exact rejected (same.symm ▸ raw)

def swappedRule : ContextualConditionalTemplateSource.Rule locals inners captures [] () where
  code := code
  conditions := Fin.cases (conditions 1)
    (Fin.cases (conditions 0) (Fin.cases PUnit.unit (Fin.cases PUnit.unit (fun impossible => Fin.elim0 impossible))))

/-- Changing only the saved row conditions leaves all raw execution data,
including the actual worklist return, unchanged. -/
def swapConditions (compiled : ContextualConditionalTemplateExecution.CompiledTemplate locals inners before)
    (authored : compiled.sourceRule = sourceRule) :
    ContextualConditionalTemplateExecution.CompiledTemplate locals inners before := by
  have lowered : compiled.publication.firing.rule = sourceRule.code.lower locals inners captures :=
    compiled.publication.authored.trans
      (congrArg (fun rule : ContextualConditionalTemplateSource.Rule locals inners captures [] () =>
        rule.code.lower locals inners captures) authored)
  have flags : compiled.publication.firing.reusable = sourceRule.ordinaryFlags compiled.1.selection.made :=
    compiled.publication.intents.trans
      (congrArg (fun rule : ContextualConditionalTemplateSource.Rule locals inners captures [] () =>
        rule.ordinaryFlags compiled.1.selection.made) authored)
  exact ⟨⟨swappedRule, compiled.1.selection, compiled.1.outputs⟩,
    ⟨compiled.publication.firing, lowered, compiled.publication.selected, compiled.publication.values, flags⟩⟩

include authored selected in
theorem swapped_first_row_has_no_instance {V : Type} (declaration : V → MetaArity base)
    (candidate : Assignment compiled.target.declarations declaration)
    (model : ContextualResidual.Models candidate compiled.target.equations)
    (value : Term (signature base declaration) [] ()) :
    ¬ Matches (ContextualPublication.privateFamily bank compiled.update.declaration)
      compiled.target.declarations candidate value ((swapConditions compiled authored).target.rows 10) := by
  have descriptor : (swapConditions compiled authored).descriptor 10 =
      some (0, ⟨.schema body, conditions 1⟩) := by
    change swappedRule.outputsFor compiled.selection.made 10 = _
    rw [selected]
    rfl
  intro matched
  have source := ((swapConditions compiled authored).schema_matches_source 10 0 body (conditions 1)
    descriptor declaration candidate value).mp matched
  change Matches inners actor
    (Assignment.compose candidate (ContextualTemplatePublication.captureValues locals inners captures compiled.update compiled.scope))
    value ⟨.schema body, conditions 1⟩ at source
  rw [captured_actor_is_zero compiled authored selected declaration candidate model] at source
  exact incompatible_source_row_has_no_instance declaration value source

theorem same_raw_execution_has_different_conditional_publications (fuel : Nat) :
    ∃ first second : ContextualConditionalTemplateExecution.CompiledTemplate locals inners before,
      first.publication.firing = second.publication.firing ∧ first.publication.firing.fuel = fuel ∧
        ¬ HEq first.target.rows second.target.rows := by
  obtain ⟨first, authored, selected, _outputs, budget, _present, consistent⟩ := an_actual_mixed_firing_exists fuel
  refine ⟨first, swapConditions first authored, rfl, budget, ?_⟩
  intro same
  obtain ⟨V, declaration, candidate, model⟩ := consistent
  have positive := good_template_has_independent_private_instances first authored selected declaration candidate model 0
  have negative := swapped_first_row_has_no_instance first authored selected declaration candidate model (pattern 0 0 0)
  have rows := eq_of_heq same
  exact negative (rows ▸ positive)

/-- Answer existence is a semantic observation, retaining the row's local
conditions and quantifying over actual models of the resulting information. -/
def HasFirstAnswer (compiled : ContextualConditionalTemplateExecution.CompiledTemplate locals inners before) : Prop :=
  ∃ (V : Type) (declaration : V → MetaArity base),
    ∃ candidate : Assignment compiled.target.declarations declaration,
      ContextualResidual.Models candidate compiled.target.equations ∧
        ∃ value : Term (signature base declaration) [] (),
          Matches (ContextualPublication.privateFamily bank compiled.update.declaration)
            compiled.target.declarations candidate value (compiled.target.rows 10)

/-- No observation of the raw firing alone recovers conditional answer
existence for every authored publication, even at a fixed finite budget. -/
theorem answerability_does_not_factor_through_raw_execution (fuel : Nat) :
    ¬ ∃ observeRaw : ContextualConditionalExecution.Firing bank before → Prop,
      ∀ compiled : ContextualConditionalTemplateExecution.CompiledTemplate locals inners before,
        compiled.publication.firing.fuel = fuel →
          (observeRaw compiled.publication.firing ↔ HasFirstAnswer compiled) := by
  rintro ⟨observeRaw, exactReadout⟩
  obtain ⟨first, authored, selected, _outputs, budget, _present, consistent⟩ := an_actual_mixed_firing_exists fuel
  have positive : HasFirstAnswer first := by
    obtain ⟨V, declaration, candidate, model⟩ := consistent
    exact ⟨V, declaration, candidate, model, pattern 0 0 0,
      good_template_has_independent_private_instances first authored selected declaration candidate model 0⟩
  have raw := (exactReadout first budget).mpr positive
  have swapped := (exactReadout (swapConditions first authored) budget).mp raw
  obtain ⟨V, declaration, candidate, model, value, matched⟩ := swapped
  exact swapped_first_row_has_no_instance first authored selected declaration candidate model value matched

end PublicationBoundary

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateControls
