import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualInteractionFactors
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExecutionPaths
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualComputedFrameAsks

/-!
# Guard-retaining data certificates for heterogeneous contextual schedules

A prepared event has port and scope formation, an independently evaluated
resource operator, and a checked solver return. It does not contain an
Admission, Firing or Path proof and need not satisfy its guards. Its complete
target inventory is computed with every original guard root retained.

A certificate is a finite sequence of such data across the actual contextual
endpoint families. Compilation retains each question's own equation prefix,
per-use row views and physical world. Satisfying that compiled question list
constructs the existing source path with its exact terminal endpoint.
This is a conditional execution certificate, not arbitrary rule installation
or an anti-unification algorithm.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSchedulePromotion

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualFrameUpdate ContextualWorldScopeLedger ContextualFreshFrameScopeLedger
open ContextualExecution ContextualInteractionFactors

variable {S : Signature} {Local O : Type} (locals : Local → MetaArity S)
  {Γ : Ctx S} {sort : S.Srt}

/-- A question is data in its original declaration frame and original row
world; the final state of a later schedule is not substituted here. -/
structure Question (context : Ctx S) (sort : S.Srt) : Type 1 where
  Names : Type
  declarations : Names → MetaArity S
  equations : EquationStore (Term (signature S declarations) context sort)
  rows : O → ContextualStoredRows.Row locals declarations context sort
  world : Finset O
  check : Check (Term (signature S declarations) context sort)

def Question.Holds (question : Question locals (O := O) Γ sort) : Prop :=
  ContextualGuardSemantics.Ask locals question.equations question.rows question.world question.check

def Checked (questions : List (Question locals (O := O) Γ sort)) : Prop :=
  ∀ question ∈ questions, question.Holds locals

theorem checked_append_iff (first second : List (Question locals (O := O) Γ sort)) :
    Checked locals (first ++ second) ↔ Checked locals first ∧ Checked locals second :=
  List.forall_mem_append

variable [DecidableEq O] [DecidableEq Local]
  [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

structure Prepared (before : Endpoint locals O Γ sort) : Type 1 where
  rule : RuleInstance (Term (signature S (ContextualActivatedStep.source locals before.declarations)) Γ sort)
  ruleCovered : RuleCovered (ContextualScopeSupport.privateScopes before.scopes) before.occupied rule
  selection : Selection O
  outputs : O → Term (signature S (ContextualActivatedStep.target locals before.declarations)) Γ sort
  formation : Formation locals before.declarations before.occupied selection rule before.inventory.rows outputs
  resources : Resources selection before.inventory.configuration.present
  fuel : Nat
  update : Update (ContextualResidual.observeProblem
    (ContextualActivatedStep.problem locals before.declarations before.occupied selection rule
      before.inventory.rows before.inventory.configuration))
  computed : letI := before.equality
    ContextualFrameWorklist.run fuel (ContextualActivatedStep.target locals before.declarations)
      (ContextualResidual.observeProblem
        (ContextualActivatedStep.problem locals before.declarations before.occupied selection rule
          before.inventory.rows before.inventory.configuration)) = .residual update
  finished : update.remaining = []

namespace Prepared

variable {locals} {before : Endpoint locals O Γ sort}

def target (prepared : Prepared locals before) : Endpoint locals O Γ sort where
  Names := (Mettapedia.Logic.LP.ScopedVar Local ⊕ before.Names) ⊕ (prepared.update.Variables ⊕ Empty)
  equality := by
    letI := before.equality
    letI := prepared.update.equality
    infer_instance
  declarations := ContextualComputedFreshFrame.active
    (ContextualActivatedStep.target locals before.declarations) prepared.update.declaration
  scopes := frameScopes (ContextualScopeSupport.activeScopes before.scopes)
    (helperScope (ContextualActivationScopes.after before.occupied prepared.selection))
  occupied := helperLedger (ContextualActivationScopes.after before.occupied prepared.selection)
  inventory := mapInventory locals (ContextualActivatedStep.target locals before.declarations)
    (ContextualComputedFreshFrame.includeSource prepared.update)
    (afterInventory locals before.declarations before.occupied prepared.selection prepared.rule
      before.inventory prepared.outputs)
  covered := inventory_includeSource_covered locals prepared.update _ _
    (afterInventory_covered locals before.declarations before.scopes before.occupied prepared.selection
      prepared.rule before.inventory prepared.outputs before.covered prepared.ruleCovered
      ((resources_iff prepared.outputs prepared.selection before.inventory.configuration.present).mp
        prepared.resources).2.2 prepared.formation.outputs)

def question (prepared : Prepared locals before)
    (check : Check (Term (signature S (ContextualActivatedStep.target locals before.declarations)) Γ sort)) :
    Question locals (O := O) Γ sort where
  Names := Mettapedia.Logic.LP.ScopedVar Local ⊕ before.Names
  declarations := ContextualActivatedStep.target locals before.declarations
  equations := ContextualActivatedStep.problem locals before.declarations before.occupied prepared.selection
    prepared.rule before.inventory.rows before.inventory.configuration
  rows := ContextualGuardedStep.guardRows locals before.declarations before.inventory.rows
  world := before.inventory.configuration.present
  check := check

def questions (prepared : Prepared locals before) : List (Question locals (O := O) Γ sort) :=
  ((ContextualActivatedStep.prepared locals before.declarations before.occupied prepared.selection
    prepared.rule before.inventory.rows).rule.checks).map prepared.question

/-- Every original check is retained, including repeated checks and checks
whose free variables do not occur in the produced terms. -/
theorem questions_length (prepared : Prepared locals before) :
    prepared.questions.length = prepared.rule.checks.length := by
  simp only [questions, List.length_map, ContextualActivatedStep.prepared,
    ContextualSelectionViews.prepare, ContextualFreshening.ruleAt, RuleInstance.map]

theorem admission (prepared : Prepared locals before) (accepted : Checked locals prepared.questions) :
    ContextualGuardedStep.Requirements locals before.declarations before.occupied
      prepared.selection prepared.rule before.inventory.rows before.inventory.configuration prepared.outputs := by
  obtain ⟨taken, made, enabled⟩ :=
    (resources_iff prepared.outputs prepared.selection before.inventory.configuration.present).mp prepared.resources
  refine ⟨taken, made, prepared.formation.take_length, prepared.formation.read_length,
    prepared.formation.outputs, enabled, ?_⟩
  intro check member
  exact accepted (prepared.question check) (List.mem_map.mpr ⟨check, member, rfl⟩)

theorem target_eq_computed (prepared : Prepared locals before)
    (accepted : Checked locals prepared.questions) :
    prepared.target = computedTarget locals before prepared.rule prepared.selection prepared.outputs
      prepared.ruleCovered (prepared.admission accepted) prepared.update := rfl

def firing (prepared : Prepared locals before) (accepted : Checked locals prepared.questions) :
    Firing locals before prepared.target where
  rule := prepared.rule
  ruleCovered := prepared.ruleCovered
  selection := prepared.selection
  outputs := prepared.outputs
  fuel := prepared.fuel
  update := prepared.update
  admitted := prepared.admission accepted
  computed := prepared.computed
  empty := prepared.finished
  destination := prepared.target_eq_computed accepted

theorem actual_return (prepared : Prepared locals before) (accepted : Checked locals prepared.questions) :
    letI := before.equality
    ContextualTransportedActivation.FromRun locals before.declarations prepared.fuel before.occupied
      prepared.selection prepared.rule before.inventory.rows before.inventory.configuration prepared.outputs
      prepared.update := (prepared.firing accepted).returned

/-- The actual target's extra solver declarations neither add nor erase
answers to an all-future query written in the post-activation interface.
This compares the full stored rows, not just selected output terms. -/
theorem target_ask_iff (prepared : Prepared locals before)
    (check : Check (Term (signature S (ContextualActivatedStep.target locals before.declarations)) Γ sort)) :
    ContextualGuardSemantics.Ask locals prepared.target.inventory.configuration.equations
      prepared.target.inventory.rows prepared.target.inventory.configuration.present
      (check.map (instantiate (ContextualComputedFreshFrame.includeSource prepared.update))) ↔
    ContextualGuardSemantics.Ask locals
      (ContextualActivatedStep.problem locals before.declarations before.occupied prepared.selection
        prepared.rule before.inventory.rows before.inventory.configuration)
      (ContextualActivatedStep.resultRows locals before.declarations prepared.selection prepared.outputs before.inventory.rows)
      (ContextualActivatedStep.result locals before.declarations before.occupied prepared.selection
        prepared.rule before.inventory.rows before.inventory.configuration).present check :=
  ContextualComputedFreshFrame.ask_include_computed_frame_iff locals prepared.update _ _ _ check

theorem target_solvable_iff (prepared : Prepared locals before) :
    ContextualFrameUnifier.Solvable prepared.target.inventory.configuration.equations ↔
      ContextualFrameUnifier.Solvable
        (ContextualActivatedStep.problem locals before.declarations before.occupied prepared.selection
          prepared.rule before.inventory.rows before.inventory.configuration) :=
  ContextualComputedFreshFrame.exists_model_in_computed_frame_iff prepared.update _

/-- Successful realization records each original question at the original
cut; the target observation law does not replace that earlier question. -/
theorem firing_retains_original_questions (prepared : Prepared locals before)
    (accepted : Checked locals prepared.questions) :
    ContextualGuardedStep.Valid locals before.declarations before.occupied
      prepared.selection prepared.rule before.inventory.rows before.inventory.configuration prepared.outputs :=
  (prepared.firing accepted).semantic_admission

end Prepared

/-- A finite data schedule with genuinely changing declaration families.
No constructor contains a source Admission, Firing or Path proof. -/
inductive Certificate : Endpoint locals O Γ sort → Endpoint locals O Γ sort → Type 1
  | nil (before) : Certificate before before
  | snoc {before middle} (past : Certificate before middle) (next : Prepared locals middle) :
      Certificate before next.target

namespace Certificate

variable {locals} {source middle target : Endpoint locals O Γ sort}

def questions {source : Endpoint locals O Γ sort} : {target : Endpoint locals O Γ sort} →
    Certificate locals source target → List (Question locals (O := O) Γ sort)
  | _, .nil _ => []
  | _, .snoc past next => past.questions ++ next.questions

def selections {source : Endpoint locals O Γ sort} : {target : Endpoint locals O Γ sort} →
    Certificate locals source target → List (Selection O)
  | _, .nil _ => []
  | _, .snoc past next => past.selections ++ [next.selection]

def fuels {source : Endpoint locals O Γ sort} : {target : Endpoint locals O Γ sort} →
    Certificate locals source target → List Nat
  | _, .nil _ => []
  | _, .snoc past next => past.fuels ++ [next.fuel]

def append (first : Certificate locals source middle) : {target : Endpoint locals O Γ sort} →
    Certificate locals middle target → Certificate locals source target
  | _, .nil _ => first
  | _, .snoc past next => .snoc (append first past) next

theorem questions_append (first : Certificate locals source middle)
    (second : Certificate locals middle target) :
    (first.append second).questions = first.questions ++ second.questions := by
  induction second with
  | nil => simp [append, questions]
  | snoc past next earlier => simp [append, questions, earlier, List.append_assoc]

theorem checked_append (first : Certificate locals source middle)
    (second : Certificate locals middle target) :
    Checked locals (first.append second).questions ↔
      Checked locals first.questions ∧ Checked locals second.questions := by
  rw [questions_append, checked_append_iff]

def realize {source : Endpoint locals O Γ sort} : {target : Endpoint locals O Γ sort} →
    (certificate : Certificate locals source target) →
      Checked locals certificate.questions → Quiver.Path source target
  | _, .nil _, _accepted => .nil
  | _, .snoc past next, accepted =>
      let split := (checked_append_iff locals past.questions next.questions).mp accepted
      (realize past split.1).cons (next.firing split.2)

theorem realize_selections (certificate : Certificate locals source target)
    (accepted : Checked locals certificate.questions) :
    ContextualExecution.selections (certificate.realize accepted) = certificate.selections := by
  induction certificate with
  | nil => rfl
  | snoc past next earlier =>
      simp only [realize, ContextualExecution.selections, selections, Prepared.firing]
      rw [earlier]

theorem realize_fuels (certificate : Certificate locals source target)
    (accepted : Checked locals certificate.questions) :
    ContextualExecution.fuels (certificate.realize accepted) = certificate.fuels := by
  induction certificate with
  | nil => rfl
  | snoc past next earlier =>
      simp only [realize, ContextualExecution.fuels, fuels, Prepared.firing]
      rw [earlier]

theorem realize_append (first : Certificate locals source middle)
    (second : Certificate locals middle target)
    (firstAccepted : Checked locals first.questions) (secondAccepted : Checked locals second.questions) :
    (first.append second).realize ((checked_append first second).mpr ⟨firstAccepted, secondAccepted⟩) =
      (first.realize firstAccepted).comp (second.realize secondAccepted) := by
  induction second with
  | nil => rfl
  | snoc past next earlier =>
      simp only [append, realize, Quiver.Path.comp]
      rw [earlier]

end Certificate

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSchedulePromotion
