import Mettapedia.Languages.MeTTa.PeTTa.UnifyingCollectionCopies
import Mettapedia.Languages.MeTTa.PeTTa.UnifyingConstraintReadout
import Mettapedia.Languages.MeTTa.PeTTa.StreamingBindingReachability
import Mettapedia.Languages.MeTTa.PeTTa.StreamingScopeReachability

/-!
# Source solver observations through actual streaming collection return

Each bank row retains its independently solved source equations. The proved
MGU bridge and both actual copying algorithms give one joint observation.
At collection closure, maintained invariants earn binding validity and caller
freshness. Relating whole producer runs to these bank rows remains separate.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Streaming.CollectionReadout

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Languages.ProcessCalculi.MORK
open EagerDFS
open UnifyingConstraintPresentation

abbrev SourceRows := List (Destination.Equations × Destination.Environment)

/-- Independent source equations and actual solver results, paired with the
bank's own substitutions. No readout equality is supplied in this relation. -/
def Models (rows : SourceRows) (answers : List Unifying.Answer) : Prop :=
  List.Forall₂ (fun row answer => OutputPlan.ConstraintAdmission.Represents row.1 answer.bindings ∧
    Destination.resolve row.1 = some row.2) rows answers

def sourceValues (rows : SourceRows) (answers : List Unifying.Answer) : List Atom :=
  List.zipWith (fun row answer => Destination.read row.2 answer.value) rows answers

theorem bank_variants {rows : SourceRows} {answers : List Unifying.Answer}
    (models : Models rows answers)
    (valid : ∀ answer ∈ answers, Unifying.Idempotent answer.bindings) :
    List.Forall₂ AtomRenaming.Variant (sourceValues rows answers)
      (answers.map fun answer => Unifying.resolve answer.bindings answer.value) := by
  induction models with
  | nil => exact .nil
  | @cons row answer rows answers head tail ih =>
      exact .cons
        (source_runtime_readout_variant row.1 answer.bindings row.2 head.1
          (valid answer List.mem_cons_self) head.2 answer.value)
        (ih (fun answer present => valid answer (List.mem_cons_of_mem _ present)))

/-- This is a copy/readout boundary, conditional on corresponding banks. The
producer must still earn Models; it is not a whole-evaluator simulation. -/
theorem copied_bank_joint (protectedNames : Finset String) (use : Nat)
    {rows : SourceRows} {answers : List Unifying.Answer}
    (models : Models rows answers)
    (valid : ∀ answer ∈ answers, Unifying.Idempotent answer.bindings)
    (allocated : ∀ name ∈ protectedNames, Mettapedia.ScopedString.Before use name) :
    VariantReadout.joint
        ((Collection.copyAnswers protectedNames ((sourceValues rows answers).map fun value => (value,[]))).map Prod.fst) =
      VariantReadout.joint (Unifying.copies use answers) := by
  have corresponding : List.Forall₂ AtomRenaming.Variant
      (((sourceValues rows answers).map fun value => (value,([] : List Atom))).map Prod.fst)
      ((answers.map fun answer => (Unifying.resolve answer.bindings answer.value,([] : List Atom))).map Prod.fst) := by
    rw [List.map_map,List.map_map]
    change List.Forall₂ AtomRenaming.Variant ((sourceValues rows answers).map id)
      (answers.map fun answer => Unifying.resolve answer.bindings answer.value)
    rw [List.map_id]
    exact bank_variants models valid
  have compared := CollectionCopyReadout.copied_joint_observations protectedNames protectedNames _ _ _ _
    corresponding (Collection.copyAnswers_valid _ _)
    (Unifying.CollectionCopies.copies_valid protectedNames use answers allocated)
  rw [List.map_map] at compared
  change VariantReadout.joint
      ((Collection.copyAnswers protectedNames ((sourceValues rows answers).map fun value => (value,[]))).map Prod.fst) =
    VariantReadout.joint ((Unifying.copies use answers).map id) at compared
  rw [List.map_id] at compared
  exact compared

def callerNames (bindings : Subst) : Finset String := (bindings.map Prod.fst).toFinset

theorem caller_names_allocated (use : Nat) (bindings : Subst)
    (supported : Unifying.SupportedBindings (Mettapedia.ScopedString.Before use) bindings) :
    ∀ name ∈ callerNames bindings, Mettapedia.ScopedString.Before use name := by
  intro name present
  obtain ⟨binding,inBindings,same⟩ := List.mem_map.mp (List.mem_toFinset.mp present)
  rw [← same]
  exact (supported binding inBindings).1

/-- The actual closing step keeps the reached world and exact caller. Its
original bindings cannot alter the copied aggregate. Idempotence and caller
freshness are obtained from the maintained frontier, not assumed afresh. -/
theorem actual_collection_return (registry : SpaceSemantics.Program) (state : State)
    (key : Nat) (bindings : Subst) (caller : List Frame) (answers : List Unifying.Answer)
    (older : List Job) (rows : SourceRows)
    (agenda : state.agenda = .collect key bindings caller answers :: older)
    (refined : BindingInvariant.stateRefines [] state) (wellScoped : ScopeInvariant.WellScoped state)
    (models : Models rows answers) :
    ∃ reached,
      step registry state = some reached ∧
      reached.world.state = state.world.state ∧
      reached.world.uses = state.world.uses + answers.length ∧
      reached.agenda = .execute ⟨.returned
        [⟨.expression (Unifying.copies state.world.uses answers),bindings⟩],caller⟩ :: older ∧
      Unifying.resolve bindings (.expression (Unifying.copies state.world.uses answers)) =
        .expression (Unifying.copies state.world.uses answers) ∧
      VariantReadout.joint
          ((Collection.copyAnswers (callerNames bindings) ((sourceValues rows answers).map fun value => (value,[]))).map Prod.fst) =
        VariantReadout.joint (Unifying.copies state.world.uses answers) := by
  have bank := (BindingInvariant.head_and_tail refined agenda).1.2.2
  have saved := (ScopeInvariant.head_and_tail wellScoped agenda).1.1
  let reached : State :=
    {state with
      world := {state.world with uses := state.world.uses + answers.length}
      agenda := .execute ⟨.returned
        [⟨.expression (Unifying.copies state.world.uses answers),bindings⟩],caller⟩ :: older}
  refine ⟨reached,by simp only [step,agenda,reached],rfl,rfl,rfl,?_,?_⟩
  · exact Unifying.CollectionCopies.caller_cannot_capture_collection _ _ _ saved
  · apply copied_bank_joint _ _ models _ (caller_names_allocated _ _ saved)
    intro answer present
    exact (bank answer present).1

theorem copies_apart_from_retained_cells (state : State) (answers : List Unifying.Answer)
    (wellScoped : ScopeInvariant.WellScoped state) :
    ∀ name old, state.world.state.cells name = some old →
      ∀ copied ∈ Unifying.copies state.world.uses answers, AtomRenaming.Apart old copied := by
  intro name old stored
  exact Unifying.CollectionCopies.copies_apart_from_old _ _ old (wellScoped.1.1 name old stored)

end Mettapedia.Languages.MeTTa.PeTTa.Streaming.CollectionReadout
