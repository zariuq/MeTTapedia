import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SchematicReachAdmission
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SchematicReachFrame
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PropagationHistory

/-!
# Atomic results of the joined schematic-space admission

The occurrence result, row metadata and propagation record are committed
together. Retained schemas transport captures and retain their private
templates. Produced values use the existing shared-output rule-instance
profile; a source construct that stores a reusable template must supply the
ordinary schema storage entry rather than silently convert it to a shared
reference. Source-level publication classification is not inferred here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SchematicReach

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

variable {S : Signature} {point : S.Srt} {Name Local Shared O Installation : Type}
    [DecidableEq Name] [DecidableEq O]
    (locals : Local → MetaArity (base S point Name))
    (captures : Shared → MetaArity (base S point Name))

def result (occupied : Finset Nat) (selection : Selection O)
    (addresses : O → Closed captures) (rows : O → ContextualStoredRows.Row locals captures [] point)
    (before : Configuration (Closed captures) O)
    (rule : NamedSpaces.LocatedRule (ActiveTerm locals captures)) :
    Configuration (ActiveTerm locals captures) O :=
  ⟨eventProblem locals captures occupied selection addresses rows before rule,
    fire before.present (selection.commit (T := ActiveTerm locals captures))⟩

def resultAddresses (selection : Selection O) (addresses : O → Closed captures)
    (produced : O → ActiveTerm locals captures × ActiveTerm locals captures) : O → ActiveTerm locals captures :=
  fun occurrence => if occurrence ∈ selection.made then (produced occurrence).1
    else instantiate (ContextualSelectionViews.capturedTarget locals captures) (addresses occurrence)

def resultPayloads (selection : Selection O) (rows : O → ContextualStoredRows.Row locals captures [] point)
    (produced : O → ActiveTerm locals captures × ActiveTerm locals captures) :
    O → ContextualStoredRows.Row locals (Active locals captures) [] point :=
  fun occurrence => if occurrence ∈ selection.made then .shared (produced occurrence).2
    else (rows occurrence).map locals (ContextualSelectionViews.capturedTarget locals captures)

def Step (installation : Installation) (standing : Bool) (occupied : Finset Nat) (selection : Selection O)
    (known : Set (ActiveTerm locals captures)) (written : Set Name)
    (addresses : O → Closed captures) (rows : O → ContextualStoredRows.Row locals captures [] point)
    (before : Configuration (Closed captures) O)
    (rule : NamedSpaces.LocatedRule (ActiveTerm locals captures))
    (produced : O → ActiveTerm locals captures × ActiveTerm locals captures)
    (history : List (PropagationHistory.Key Installation O))
    (after : Configuration (ActiveTerm locals captures) O)
    (afterAddresses : O → ActiveTerm locals captures)
    (afterRows : O → ContextualStoredRows.Row locals (Active locals captures) [] point)
    (afterOccupied : Finset Nat) (afterHistory : List (PropagationHistory.Key Installation O)) : Prop :=
  Admits locals captures occupied selection known written addresses rows before rule
      (fun occurrence => place (produced occurrence).1 (produced occurrence).2) ∧
    PropagationHistory.Fresh ⟨installation,standing,selection⟩ history ∧
    after = result locals captures occupied selection addresses rows before rule ∧
    afterAddresses = resultAddresses locals captures selection addresses produced ∧
    afterRows = resultPayloads locals captures selection rows produced ∧
    afterOccupied = ContextualActivationScopes.after occupied selection ∧
    afterHistory = PropagationHistory.record ⟨installation,standing,selection⟩ history

variable {locals captures} {occupied : Finset Nat} {selection : Selection O}
    {known : Set (ActiveTerm locals captures)} {written : Set Name}
    {addresses : O → Closed captures} {rows : O → ContextualStoredRows.Row locals captures [] point}
    {before : Configuration (Closed captures) O}
    {rule : NamedSpaces.LocatedRule (ActiveTerm locals captures)} {outputs : O → ActiveTerm locals captures}

theorem Admits.old_consistent
    (admitted : Admits locals captures occupied selection known written addresses rows before rule outputs) :
    ContextualFrameUnifier.Solvable (ContextualActivatedStep.frame locals captures before).equations := by
  obtain ⟨Future,future,candidate,model⟩ := admitted.consistent
  exact ContextualFrameUnifier.solvable_of_model
    ((ContextualFrameUnifier.models_append candidate _ _).mp model).1

theorem Admits.unreached_not_selected
    (admitted : Admits locals captures occupied selection known written addresses rows before rule outputs)
    {occurrence : O} {n : Name}
    (atName : ResolvesTo (ContextualActivatedStep.frame locals captures before).equations
      (instantiate (ContextualSelectionViews.capturedTarget locals captures) (addresses occurrence)) n)
    (unreached : ¬ Reached locals captures occupied selection known addresses rows before n) :
    occurrence ∉ selection.taken ++ selection.read := by
  intro selected
  obtain ⟨m,reached,atOther⟩ := admitted.selected occurrence selected
  exact unreached ((atOther.unique admitted.old_consistent atName) ▸ reached)

theorem Admits.unreached_survives
    (admitted : Admits locals captures occupied selection known written addresses rows before rule outputs)
    {occurrence : O} (present : occurrence ∈ before.present) {n : Name}
    (atName : ResolvesTo (ContextualActivatedStep.frame locals captures before).equations
      (instantiate (ContextualSelectionViews.capturedTarget locals captures) (addresses occurrence)) n)
    (unreached : ¬ Reached locals captures occupied selection known addresses rows before n) :
    occurrence ∈ (result locals captures occupied selection addresses rows before rule).present := by
  apply mem_fire.mpr
  refine Or.inl ⟨present,?_⟩
  intro taken
  exact admitted.unreached_not_selected atName unreached
    (List.mem_append_left _ (by simpa [Selection.commit] using taken))

omit [DecidableEq Name] in
theorem retained_schema (produced : O → ActiveTerm locals captures × ActiveTerm locals captures)
    {occurrence : O} (notMade : occurrence ∉ selection.made)
    (atom : Term (signature (base S point Name) locals) [] point)
    (stored : rows occurrence = ContextualStoredRows.store locals captures atom) :
    resultPayloads locals captures selection rows produced occurrence =
      ContextualStoredRows.store locals (Active locals captures) atom := by
  simp only [resultPayloads,notMade,ite_false,stored,ContextualStoredRows.map_store]

/-- An unselected protected view has the same equality consequences before
and after this actual event. Protection is computed from equation support. -/
theorem Admits.meaning_frame
    (admitted : Admits locals captures occupied selection known written addresses rows before rule outputs)
    (first second : ActiveTerm locals captures)
    (untouched : ∀ identity ∈ support first ++ support second,
      ¬ Frame.Variables (ContextualActivatedStep.frame locals captures before).equations
        (eventEquations locals captures occupied selection addresses rows rule) identity) :
    Frame.Entails (result locals captures occupied selection addresses rows before rule).equations first second ↔
      Frame.Entails (ContextualActivatedStep.frame locals captures before).equations first second :=
  Frame.entails_iff admitted.consistent first second untouched

theorem Admits.physical_and_meaning_frame
    (admitted : Admits locals captures occupied selection known written addresses rows before rule outputs)
    {occurrence : O} (present : occurrence ∈ before.present) {n : Name}
    (atName : ResolvesTo (ContextualActivatedStep.frame locals captures before).equations
      (instantiate (ContextualSelectionViews.capturedTarget locals captures) (addresses occurrence)) n)
    (unreached : ¬ Reached locals captures occupied selection known addresses rows before n)
    (first second : ActiveTerm locals captures)
    (untouched : ∀ identity ∈ support first ++ support second,
      ¬ Frame.Variables (ContextualActivatedStep.frame locals captures before).equations
        (eventEquations locals captures occupied selection addresses rows rule) identity) :
    occurrence ∈ (result locals captures occupied selection addresses rows before rule).present ∧
      (Frame.Entails (result locals captures occupied selection addresses rows before rule).equations first second ↔
        Frame.Entails (ContextualActivatedStep.frame locals captures before).equations first second) :=
  ⟨admitted.unreached_survives present atName unreached,admitted.meaning_frame first second untouched⟩

theorem Admits.commit_with_history
    (produced : O → ActiveTerm locals captures × ActiveTerm locals captures)
    (admitted : Admits locals captures occupied selection known written addresses rows before rule
      (fun occurrence => place (produced occurrence).1 (produced occurrence).2))
    (installation : Installation) (standing : Bool) (history : List (PropagationHistory.Key Installation O))
    (fresh : PropagationHistory.Fresh ⟨installation,standing,selection⟩ history) :
    Step locals captures installation standing occupied selection known written addresses rows before rule
      produced history
      (result locals captures occupied selection addresses rows before rule)
      (resultAddresses locals captures selection addresses produced)
      (resultPayloads locals captures selection rows produced)
      (ContextualActivationScopes.after occupied selection)
      (PropagationHistory.record ⟨installation,standing,selection⟩ history) :=
  ⟨admitted,fresh,rfl,rfl,rfl,rfl,rfl⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SchematicReach
