import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualTemplateExecution
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SchematicReachControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPublicationControls

/-!
# A constructed template keeps one shared capture and freshens its holes

The producer reads a shared value from a named space, constructs a reusable
template with a repeated private variable and an explicit actor capture, and
publishes shared and ordinary values in the same event. The actual solver run
and final inventory are used throughout. These are full-owner source controls;
no proof kernel or host evaluator performs the construction.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualTemplatePublication.Controls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Logic.LP (ScopedVar)
open ContextualTemplateSource ContextualWorldScopeLedger ContextualScopeSupport
open SchematicReach.Controls (spaceSignature DataOperator symbol pair)

abbrev base := spaceSignature
local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) := by
  change DecidableEq (DataOperator ⊕ Operator (SchematicReach.spaceDeclaration
    SchematicReach.Controls.dataSignature () (Name := Nat)) sort)
  infer_instance

abbrev locals (_ : Nat) : MetaArity base := ([], ())
abbrev inners (_ : Nat) : MetaArity base := ([], ())
abbrev captures (_ : Nat) : MetaArity base := ([], ())
abbrev bank := Expanded locals inners
abbrev active := Active locals inners captures
abbrev actor := Actor locals captures
abbrev blueprint := Blueprint locals inners captures

def actorVariable (index : Nat) : SchematicReach.Closed actor := generator actor (.inl index)
def privateVariable : SchematicReach.Closed blueprint := generator blueprint (.inl 0)
def capturedVariable : SchematicReach.Closed blueprint := generator blueprint (.inr (.inl 0))
def body : SchematicReach.Closed blueprint :=
  SchematicReach.place (SchematicReach.name 9) (pair privateVariable (pair privateVariable capturedVariable))

def sourceRule : ContextualTemplateSource.Rule locals inners captures [] () :=
  ⟨[], [SchematicReach.place (SchematicReach.name 1) (actorVariable 0)], [], [],
    [.schema body, .shared (SchematicReach.place (SchematicReach.name 9) (actorVariable 0)),
      .ordinary (SchematicReach.place (SchematicReach.name 9) (pair (actorVariable 0) (actorVariable 1)))]⟩
def rule := sourceRule.lower locals inners captures
def selected : Selection Nat := ⟨[], [7], [90, 91, 92]⟩
def rows (occurrence : Nat) : ContextualStoredRows.Row bank captures [] () :=
  if occurrence = 7 then .shared (SchematicReach.place (SchematicReach.name 1) (generator captures 0))
  else .shared (SchematicReach.place (SchematicReach.name 2) (generator captures 9))
def initial : Configuration (SchematicReach.Closed captures) Nat := ⟨[], {7, 11}⟩
def scopes (_ : Nat) : Finset Nat := ∅
def inventory : Inventory bank captures (O := Nat) [] () := ⟨initial, rows, [], []⟩
def start : ContextualExecution.Endpoint bank Nat [] () where
  Names := Nat
  equality := inferInstance
  declarations := captures
  scopes := scopes
  occupied := ∅
  inventory := inventory
  covered := (coveredWorld_iff bank captures scopes ∅ inventory).mpr (by decide +kernel)

def outputs (occurrence : Nat) : SchematicReach.Closed active :=
  if occurrence = 90 then (Production.schema body).atScope locals inners captures 1 0
  else if occurrence = 91 then (Production.shared (SchematicReach.place (SchematicReach.name 9)
    (actorVariable 0))).atScope locals inners captures 1 1
  else (Production.ordinary (SchematicReach.place (SchematicReach.name 9)
    (pair (actorVariable 0) (actorVariable 1)))).atScope locals inners captures 1 2

def problem := ContextualActivatedStep.problem bank captures ∅ selected rule rows initial
def observed := ContextualResidual.observeProblem problem

theorem problem_explicit : problem =
    [(SchematicReach.place (SchematicReach.name 1) (generator active (.inl (ScopedVar.at 1 (.inl 0)))),
      SchematicReach.place (SchematicReach.name 1) (generator active (.inr 0)))] := by
  with_unfolding_all rfl

def sourceModel {Next : Type} (next : Next → MetaArity base) (caller : Assignment captures next) : Assignment active next
  | .inl ⟨_, .inl _⟩ => caller 0
  | .inl ⟨_, .inr _⟩ => caller 0
  | .inr identity => caller identity

theorem source_model {Next : Type} (next : Next → MetaArity base) (caller : Assignment captures next) :
    ContextualResidual.Models (sourceModel next caller) observed := by
  apply (ContextualResidual.models_observeProblem _ _).mpr
  rw [problem_explicit]
  intro equation member
  obtain rfl := List.mem_singleton.mp member
  change instantiate (sourceModel next caller)
      (SchematicReach.place (SchematicReach.name 1) (generator active (.inl (ScopedVar.at 1 (.inl 0))))) =
    instantiate (sourceModel next caller)
      (SchematicReach.place (SchematicReach.name 1) (generator active (.inr 0)))
  simp only [SchematicReach.instantiate_place, SchematicReach.instantiate_name]
  exact congrArg (SchematicReach.place (SchematicReach.name 1))
    ((instantiate_generator (sourceModel next caller) (.inl (ScopedVar.at 1 (.inl 0)))).trans
      (instantiate_generator (sourceModel next caller) (.inr 0)).symm)

def localResult := ContextualFrameWorklist.runWithRefuter
  (fun declaration problem => ContextualEquationRefutation.choose (S := base) (source := declaration) problem)
  2 active observed
def updateOption {V : Type} {declaration : V → MetaArity base} {job : ContextualResidual.Problem declaration} :
    ContextualFrameWorklist.Result job → Option (ContextualFrameUpdate.Update job)
  | .residual update => some update
  | .refuted _ => none
theorem computed_update_present : (updateOption localResult).isSome = true := by decide +kernel
def update := (updateOption localResult).get computed_update_present

theorem actual_run : ContextualFrameWorklist.run 2 active observed = .residual update := by
  rw [ContextualFrameWorklist.run_eq_local_on_model 2 observed captures (sourceModel captures (generator captures))
    (source_model captures (generator captures))]
  exact ContextualPublication.Controls.extracted_return localResult computed_update_present

theorem finished : update.remaining = [] := by decide +kernel
theorem covered_rule : RuleCovered (privateScopes scopes) ∅ rule := by
  apply (ruleRoots_covered_iff (privateScopes scopes) ∅ rule).mp
  decide +kernel
theorem admission : ContextualGuardedStep.Requirements bank captures ∅ selected rule rows initial outputs := by
  refine ⟨by decide, by decide, rfl, rfl, ?_, by decide, ?_⟩
  · with_unfolding_all rfl
  · intro check member
    cases member

def rawTarget := ContextualExecution.computedTarget bank start rule selected outputs covered_rule admission update
def execution : ContextualExecution.Firing bank start rawTarget :=
  ⟨rule, covered_rule, selected, outputs, 2, update, admission, actual_run, finished, rfl⟩
def firing : ContextualTemplatePublication.Firing locals inners start := ⟨sourceRule, rawTarget, execution, rfl⟩

theorem source_template_is_the_first_output : firing.descriptor 90 = some (0, .schema body) := rfl
theorem the_three_outputs_commit_together : firing.target.inventory.configuration.present = {7, 11, 90, 91, 92} := by
  decide +kernel

def future (_ : Nat) : MetaArity base := ([], ())
def constantAt (arity : MetaArity base) (value : Nat) :
    Term (signature base future) arity.1 arity.2 := by
  rcases arity with ⟨context, sort⟩
  cases sort
  exact .op (.inl (.inl (DataOperator.symbol value))) .nil

def observe (value helper : Nat) : Assignment firing.target.declarations future := fun identity =>
  constantAt (firing.target.declarations identity) (match identity with | .inl _ => value | .inr _ => helper)

def actorReading (value : Nat) : Assignment actor future
  | .inl _ => symbol value
  | .inr _ => symbol value

theorem capture_is_the_original_reference (value helper : Nat) :
    Assignment.compose (observe value helper) (captureValues locals inners captures update 1) =
      actorReading value := by
  funext identity
  cases identity with
  | inl identity =>
      change instantiate (observe value helper) (captureValues locals inners captures update 1 (.inl identity)) = _
      erw [capture_local, instantiate_generator]
      rfl
  | inr identity =>
      change instantiate (observe value helper) (captureValues locals inners captures update 1 (.inr identity)) = _
      erw [capture_shared, instantiate_generator]
      rfl

def pattern (privateValue capturedValue : Nat) : SchematicReach.Closed future :=
  SchematicReach.place (SchematicReach.name 9)
    (pair (symbol privateValue) (pair (symbol privateValue) (symbol capturedValue)))

theorem later_private_read (privateValue capturedValue helper : Nat) :
    ContextualGuardMatching.Matches (ContextualPublication.privateFamily bank update.declaration)
      (observe capturedValue helper) (pattern privateValue capturedValue) (firing.target.inventory.rows 90) := by
  apply (firing.schema_matches_source 90 0 body source_template_is_the_first_output future _ _).mpr
  erw [capture_is_the_original_reference]
  refine ⟨ContextualGuardMatching.Extension.identity future, (fun _ => symbol privateValue), ?_⟩
  with_unfolding_all rfl

theorem two_private_reads_keep_the_capture :
    ContextualGuardMatching.Matches (ContextualPublication.privateFamily bank update.declaration)
        (observe 42 999) (pattern 20 42) (firing.target.inventory.rows 90) ∧
      ContextualGuardMatching.Matches (ContextualPublication.privateFamily bank update.declaration)
        (observe 42 999) (pattern 30 42) (firing.target.inventory.rows 90) :=
  ⟨later_private_read 20 42 999, later_private_read 30 42 999⟩

theorem source_pullback (value helper : Nat) :
    Assignment.compose (observe value helper) (ContextualComputedFreshFrame.includeSource update) =
      sourceModel future (fun _ => symbol value) := by
  funext identity
  cases identity with
  | inl identity =>
      rcases identity with ⟨scope, name⟩
      cases name with
      | inl name =>
          change instantiate (observe value helper) (ContextualComputedFreshFrame.includeSource update
            (.inl (ScopedVar.at scope (.inl name)))) = _
          erw [ContextualFreshFrameScopeLedger.includeSource_image, instantiate_generator]
          rfl
      | inr name =>
          change instantiate (observe value helper) (ContextualComputedFreshFrame.includeSource update
            (.inl (ScopedVar.at scope (.inr name)))) = _
          erw [ContextualFreshFrameScopeLedger.includeSource_image, instantiate_generator]
          rfl
  | inr name =>
      change instantiate (observe value helper) (ContextualComputedFreshFrame.includeSource update (.inr name)) = _
      erw [ContextualFreshFrameScopeLedger.includeSource_image, instantiate_generator]
      rfl

theorem observation_models_the_actual_world (value helper : Nat) :
    ContextualFrameUnifier.Models (observe value helper) firing.target.inventory.configuration.equations := by
  rw [firing.native_equations]
  change ContextualFrameUnifier.Models (observe value helper)
    (ContextualFrameUnifier.mapProblem (ContextualComputedFreshFrame.includeSource update) problem)
  apply (ContextualFrameUnifier.models_mapProblem _ _ _).mpr
  rw [source_pullback]
  exact (ContextualResidual.models_observeProblem _ _).mp (source_model future (fun _ => symbol value))

def firstOfPair {V : Type} {declaration : V → MetaArity base} :
    SchematicReach.Closed declaration → Option (SchematicReach.Closed declaration)
  | .op (.inl (.inl .pair)) (.cons first (.cons _ .nil)) => some first
  | _ => none

def secondOfPair {V : Type} {declaration : V → MetaArity base} :
    SchematicReach.Closed declaration → Option (SchematicReach.Closed declaration)
  | .op (.inl (.inl .pair)) (.cons _ (.cons second .nil)) => some second
  | _ => none

theorem body_instance {V : Type} {next : V → MetaArity base} (assignment : Assignment blueprint next) :
    instantiate assignment body = SchematicReach.place (SchematicReach.name 9)
      (pair (assignment (.inl 0)) (pair (assignment (.inl 0)) (assignment (.inr (.inl 0))))) := by
  change SchematicReach.place (SchematicReach.name 9)
      (pair (instantiate assignment privateVariable)
        (pair (instantiate assignment privateVariable) (instantiate assignment capturedVariable))) = _
  have privateEq := instantiate_generator assignment (.inl 0)
  have capturedEq := instantiate_generator assignment (.inr (.inl 0))
  exact (congrArg (fun value => SchematicReach.place (SchematicReach.name 9)
    (pair value (pair value (instantiate assignment capturedVariable)))) privateEq).trans
      (congrArg (fun value => SchematicReach.place (SchematicReach.name 9)
        (pair (assignment (.inl 0)) (pair (assignment (.inl 0)) value))) capturedEq)

def mixedPattern (first second captured : Nat) : SchematicReach.Closed future :=
  SchematicReach.place (SchematicReach.name 9) (pair (symbol first) (pair (symbol second) (symbol captured)))

theorem one_use_cannot_split_the_private_alias (first second captured helper : Nat) (apart : first ≠ second) :
    ¬ ContextualGuardMatching.Matches (ContextualPublication.privateFamily bank update.declaration)
      (observe captured helper) (mixedPattern first second captured) (firing.target.inventory.rows 90) := by
  intro matched
  have original := (firing.schema_matches_source 90 0 body source_template_is_the_first_output future _ _).mp matched
  erw [capture_is_the_original_reference] at original
  obtain ⟨extension, images, same⟩ := original
  have full := (body_instance (ContextualGuardMatching.instanceAssignment inners images extension.assignment
    (actorReading captured))).symm.trans same
  change SchematicReach.place (SchematicReach.name 9) (pair (images 0) (pair (images 0) (symbol captured))) =
    SchematicReach.place (SchematicReach.name 9) (pair (symbol first) (pair (symbol second) (symbol captured))) at full
  have values := (SchematicReach.place_injective (S := SchematicReach.Controls.dataSignature)
    (point := ()) (Name := Nat) full).2
  have one := Option.some.inj (congrArg firstOfPair values)
  have two := Option.some.inj (congrArg firstOfPair (Option.some.inj (congrArg secondOfPair values)))
  exact apart (SchematicReach.Controls.symbol_injective (one.symm.trans two))

theorem a_capture_cannot_be_replaced_by_a_helper (privateValue : Nat) :
    ¬ ContextualGuardMatching.Matches (ContextualPublication.privateFamily bank update.declaration)
      (observe 42 999) (pattern privateValue 999) (firing.target.inventory.rows 90) := by
  intro matched
  have original := (firing.schema_matches_source 90 0 body source_template_is_the_first_output future _ _).mp matched
  erw [capture_is_the_original_reference] at original
  obtain ⟨extension, images, same⟩ := original
  have full := (body_instance (ContextualGuardMatching.instanceAssignment inners images extension.assignment
    (actorReading 42))).symm.trans same
  change SchematicReach.place (SchematicReach.name 9) (pair (images 0) (pair (images 0) (symbol 42))) =
    SchematicReach.place (SchematicReach.name 9)
      (pair (symbol privateValue) (pair (symbol privateValue) (symbol 999))) at full
  have values := (SchematicReach.place_injective (S := SchematicReach.Controls.dataSignature)
    (point := ()) (Name := Nat) full).2
  have captured := Option.some.inj (congrArg secondOfPair (Option.some.inj (congrArg secondOfPair values)))
  have impossible := SchematicReach.Controls.symbol_injective captured
  omega

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualTemplatePublication.Controls
