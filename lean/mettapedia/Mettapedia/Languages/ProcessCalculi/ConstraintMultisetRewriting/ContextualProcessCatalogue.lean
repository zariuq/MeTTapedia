import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualProcessTransport
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSchedulePromotionTransport

/-!
# A common-frame catalogue retaining every contextual event's original cut

Each catalogue item retains the physical selection, the prepared rule and
its per-use take/read views, and the original joint equation prefix and
pre-event row world. Pure helper/capture inclusion moves these data into the
terminal declaration family. The catalogue can be enumerated in a different
order for checking: its guard conjunction is unchanged. This does not by
itself permit reordering the original source execution.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualProcessCatalogue

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualExecution ContextualSchedulePromotion ContextualGuardMatching

variable {S : Signature} {Local O V W : Type} (locals : Local → MetaArity S)
  {declarations : V → MetaArity S} {later : W → MetaArity S} {Γ : Ctx S} {sort : S.Srt}

structure Event (declarations : V → MetaArity S) (context : Ctx S) (sort : S.Srt) where
  selection : Selection O
  rule : RuleInstance (Term (signature S declarations) context sort)
  takenViews : List (Term (signature S declarations) context sort)
  readViews : List (Term (signature S declarations) context sort)
  problem : EquationStore (Term (signature S declarations) context sort)
  guardRows : O → ContextualStoredRows.Row locals declarations context sort
  guardWorld : Finset O

namespace Event

variable {locals}

def map (change : Assignment declarations later) (event : Event locals (O := O) declarations Γ sort) :
    Event locals (O := O) later Γ sort where
  selection := event.selection
  rule := event.rule.map (instantiate change)
  takenViews := event.takenViews.map (instantiate change)
  readViews := event.readViews.map (instantiate change)
  problem := ContextualFrameUnifier.mapProblem change event.problem
  guardRows occurrence := (event.guardRows occurrence).map locals change
  guardWorld := event.guardWorld

def Holds (event : Event locals (O := O) declarations Γ sort) : Prop :=
  ∀ check ∈ event.rule.checks,
    ContextualGuardSemantics.Ask locals event.problem event.guardRows event.guardWorld check

theorem map_extension_iff (event : Event locals (O := O) declarations Γ sort)
    (extension : Extension declarations) :
    (event.map extension.assignment).Holds ↔ event.Holds := by
  change (∀ check ∈ event.rule.checks.map (Check.map (instantiate extension.assignment)), _) ↔ _
  simp only [List.forall_mem_map]
  apply forall_congr'
  intro check
  apply forall_congr'
  intro _member
  exact ContextualGuardSemantics.Ask.extension_iff locals extension event.problem event.guardRows
    event.guardWorld check

end Event

def Checked (events : List (Event locals (O := O) declarations Γ sort)) : Prop :=
  ∀ event ∈ events, event.Holds

theorem checked_append_iff (first second : List (Event locals (O := O) declarations Γ sort)) :
    Checked locals (first ++ second) ↔ Checked locals first ∧ Checked locals second :=
  List.forall_mem_append

theorem checked_map_extension_iff (events : List (Event locals (O := O) declarations Γ sort))
    (extension : Extension declarations) :
    Checked locals (events.map (Event.map extension.assignment)) ↔ Checked locals events := by
  simp only [Checked, List.forall_mem_map, Event.map_extension_iff]

theorem checked_perm_iff {events reordered : List (Event locals (O := O) declarations Γ sort)}
    (perm : events.Perm reordered) : Checked locals events ↔ Checked locals reordered := by
  constructor
  · intro checked event member
    exact checked event (perm.symm.subset member)
  · intro checked event member
    exact checked event (perm.subset member)

variable {locals} [DecidableEq O] [DecidableEq Local]
  [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

def originalEvent {before : Endpoint locals O Γ sort} (prepared : Prepared locals before) :
    Event locals (O := O) (ContextualActivatedStep.target locals before.declarations) Γ sort := {
    selection := prepared.selection
    rule := (ContextualActivatedStep.prepared locals before.declarations before.occupied
      prepared.selection prepared.rule before.inventory.rows).rule
    takenViews := List.ofFn (ContextualActivatedStep.prepared locals before.declarations before.occupied
      prepared.selection prepared.rule before.inventory.rows).taken
    readViews := List.ofFn (ContextualActivatedStep.prepared locals before.declarations before.occupied
      prepared.selection prepared.rule before.inventory.rows).read
    problem := ContextualActivatedStep.problem locals before.declarations before.occupied
      prepared.selection prepared.rule before.inventory.rows before.inventory.configuration
    guardRows := ContextualGuardedStep.guardRows locals before.declarations before.inventory.rows
    guardWorld := before.inventory.configuration.present }

def preparedEvent {before : Endpoint locals O Γ sort} (prepared : Prepared locals before) :
    Event locals (O := O) prepared.target.declarations Γ sort :=
  Event.map (ContextualComputedFreshFrame.includeSource prepared.update) (originalEvent prepared)

theorem preparedEvent_checked_iff {before : Endpoint locals O Γ sort} (prepared : Prepared locals before) :
    (preparedEvent prepared).Holds ↔ ContextualSchedulePromotion.Checked locals prepared.questions := by
  have reflected := Event.map_extension_iff (originalEvent prepared)
    (ContextualComputedFreshFrame.declarationExtension prepared.update)
  rw [ContextualComputedFreshFrame.declarationExtension_assignment prepared.update] at reflected
  apply reflected.trans
  simp only [Event.Holds, originalEvent, ContextualSchedulePromotion.Checked,
    Prepared.questions, List.forall_mem_map]
  rfl

def events {source : Endpoint locals O Γ sort} : {target : Endpoint locals O Γ sort} →
    Certificate locals source target → List (Event locals (O := O) target.declarations Γ sort)
  | _, .nil _ => []
  | _, .snoc past next =>
      (events past).map (Event.map (later := next.target.declarations)
        (ContextualProcessTransport.captureExtension next).assignment) ++
        [preparedEvent next]

theorem events_checked_iff {source target : Endpoint locals O Γ sort}
    (certificate : Certificate locals source target) :
    Checked locals (events certificate) ↔ ContextualSchedulePromotion.Checked locals certificate.questions := by
  induction certificate with
  | nil => simp [events, Checked, Certificate.questions, ContextualSchedulePromotion.Checked]
  | snoc past next earlier =>
      rw [events, checked_append_iff]
      have moved := checked_map_extension_iff locals (events past)
        (ContextualProcessTransport.captureExtension next)
      have last : Checked locals [preparedEvent next] ↔ ContextualSchedulePromotion.Checked locals next.questions := by
        simpa only [Checked, List.forall_mem_singleton] using preparedEvent_checked_iff next
      exact (and_congr (moved.trans earlier) last).trans
        (ContextualSchedulePromotion.checked_append_iff locals _ _).symm

/-- Every checked common-frame enumeration reconstructs the same original
source endpoint. Reordering this catalogue checks the same original cuts. -/
theorem realize_permuted_catalogue {source target : Endpoint locals O Γ sort}
    (certificate : Certificate locals source target)
    (reordered : List (Event locals (O := O) target.declarations Γ sort))
    (perm : (events certificate).Perm reordered) (checked : Checked locals reordered) :
    Nonempty (Quiver.Path source target) :=
  ⟨certificate.realize ((events_checked_iff certificate).mp ((checked_perm_iff locals perm).mpr checked))⟩

theorem selections_preserved {source target : Endpoint locals O Γ sort}
    (certificate : Certificate locals source target) :
    (events certificate).map Event.selection = certificate.selections := by
  induction certificate with
  | nil => rfl
  | snoc past next earlier =>
      simp only [events, List.map_append, List.map_map, List.map_cons, List.map_nil]
      change (events past).map Event.selection ++ [next.selection] = past.selections ++ [next.selection]
      rw [earlier]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualProcessCatalogue
