import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SchemaPublicationAuthority
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProofUse

/-!
# Source-origin proof schedules retain compiled conditions and used hypotheses

A source firing contains a schema, inputs and an occurrence selection, never
an arbitrary concrete rule. Lowering computes every rule through activation.
The existing conditional schedule compiler retains resources, equations,
shapes and all transported checks. Its existing proof-use calculation retains
the actual initial protected occurrences used by the result.

The cut theorem changes only the logical assumptions. It neither drops the
compiled condition nor authorizes universal publication from one instance.
Kernel source membership and actual send formation also realize the compiled
certificate as a run of the existing schema-authority system.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SchemaSchedules

open Mettapedia.Languages.ProcessCalculi
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.TierZeroKernel (Derivable)

universe uT uS uR uX uO uN uI
variable {T : Type uT} {S : Type uS} {R : Type uR} {X : Type uX} {O : Type uO}
    {N : Type uN} {I : Type uI}

structure SourceFiring (R : Type uR) (X : Type uX) (O : Type uO) where
  schema : R
  inputs : X
  selection : Selection O

def lower (activate : R → X → Option (RuleInstance T)) (source : SourceFiring R X O) :
    Option (ConditionalSchedule.Firing T O) :=
  (activate source.schema source.inputs).map fun rule => (rule, source.selection)

def lowerAll (activate : R → X → Option (RuleInstance T)) (sources : List (SourceFiring R X O)) :
    Option (List (ConditionalSchedule.Firing T O)) := sources.mapM (lower activate)

theorem lower_origin (activate : R → X → Option (RuleInstance T)) (source : SourceFiring R X O)
    {firing : ConditionalSchedule.Firing T O} (computed : lower activate source = some firing) :
    ∃ rule, activate source.schema source.inputs = some rule ∧ firing = (rule, source.selection) := by
  obtain ⟨rule, origin, same⟩ := Option.map_eq_some_iff.mp computed
  exact ⟨rule, origin, same.symm⟩

private theorem collect_iff {A B : Type*} (function : A → Option B) (inputs : List A) (outputs : List B) :
    inputs.mapM function = some outputs ↔ List.Forall₂ (fun input output => function input = some output) inputs outputs := by
  induction inputs generalizing outputs with
  | nil => cases outputs <;> simp
  | cons input inputs earlier =>
      cases outputs with
      | nil =>
          cases head : function input <;> cases tail : inputs.mapM function <;>
            simp [List.mapM_cons, head, tail]
      | cons output outputs =>
          cases head : function input <;> cases tail : inputs.mapM function <;>
            simp [List.mapM_cons, head, tail, ← earlier]

theorem lowerAll_iff (activate : R → X → Option (RuleInstance T)) (sources : List (SourceFiring R X O))
    (schedule : List (ConditionalSchedule.Firing T O)) :
    lowerAll activate sources = some schedule ↔
      List.Forall₂ (fun source firing => lower activate source = some firing) sources schedule :=
  collect_iff _ _ _

theorem member_origin (activate : R → X → Option (RuleInstance T)) (installed : List R)
    {sources : List (SourceFiring R X O)} {schedule : List (ConditionalSchedule.Firing T O)}
    (computed : lowerAll activate sources = some schedule)
    (authorized : ∀ source ∈ sources, source.schema ∈ installed)
    {rule : RuleInstance T} (member : rule ∈ schedule.map Prod.fst) :
    ∃ schema ∈ installed, ∃ inputs, activate schema inputs = some rule := by
  obtain ⟨firing, present, same⟩ := List.mem_map.mp member
  obtain ⟨source, sourcePresent, lowered⟩ := GuardedMultisetRewriting.mem_of_forall₂
    ((lowerAll_iff activate sources schedule).mp computed) firing present
  obtain ⟨actual, origin, rfl⟩ := lower_origin activate source lowered
  change actual = rule at same
  subst rule
  exact ⟨source.schema, authorized source sourcePresent, source.inputs, origin⟩

section ProofUse

variable [DecidableEq O] (protectedOccurrence : O → Prop) [DecidablePred protectedOccurrence]

omit [DecidablePred protectedOccurrence] in
theorem final_consistent (action : SubstitutionAction T S) (label : O → T) :
    ∀ (schedule : List (ConditionalSchedule.Firing T O)) (before : Configuration T O),
      ConditionalSchedule.Executable action label before schedule →
        action.Consistent (ConditionalSchedule.follow label before schedule).equations
  | [], _, executable => executable
  | firing :: rest, before, executable =>
      final_consistent action label rest (firing.2.result label firing.1 before) executable.2

theorem infers_origin (action : SubstitutionAction T S) (label : O → T)
    (activate : R → X → Option (RuleInstance T)) (installed : List R)
    {sources : List (SourceFiring R X O)} {schedule : List (ConditionalSchedule.Firing T O)}
    (computed : lowerAll activate sources = some schedule)
    (authorized : ∀ source ∈ sources, source.schema ∈ installed)
    {premises : Multiset T} {conclusion : T}
    (inferred : Provenance.Infers action label protectedOccurrence (schedule.map Prod.fst) premises conclusion) :
    SchemaPublicationAuthority.Infers action label protectedOccurrence activate installed premises conclusion := by
  obtain ⟨rule, member, before, picked, assignment, valid, solved, hypotheses, output, made, isProtected, result⟩ := inferred
  obtain ⟨schema, installedSchema, inputs, origin⟩ := member_origin activate installed computed authorized member
  exact ⟨schema, installedSchema, inputs, rule, origin, rule, by simp, before, picked, assignment,
    valid, solved, hypotheses, output, made, isProtected, result⟩

theorem derivable_origin (action : SubstitutionAction T S) (label : O → T)
    (activate : R → X → Option (RuleInstance T)) (installed : List R)
    {sources : List (SourceFiring R X O)} {schedule : List (ConditionalSchedule.Firing T O)}
    (computed : lowerAll activate sources = some schedule)
    (authorized : ∀ source ∈ sources, source.schema ∈ installed)
    {initial : T → Prop} {conclusion : T}
    (derived : Derivable initial (Provenance.Infers action label protectedOccurrence (schedule.map Prod.fst)) conclusion) :
    Derivable initial (SchemaPublicationAuthority.Infers action label protectedOccurrence activate installed) conclusion := by
  induction derived with
  | initial hypothesis => exact .initial hypothesis
  | infer actual children earlier =>
      exact .infer (infers_origin protectedOccurrence action label activate installed computed authorized actual) earlier

theorem compiled_derivation (action : SubstitutionAction T S) (label : O → T)
    (activate : R → X → Option (RuleInstance T)) (installed : List R)
    (sources : List (SourceFiring R X O)) (schedule : List (ConditionalSchedule.Firing T O))
    (computed : lowerAll activate sources = some schedule)
    (authorized : ∀ source ∈ sources, source.schema ∈ installed)
    (before : Configuration T O)
    (enabled : (ConditionalSchedule.compile label schedule).Holds action label before)
    (assignment : S) (solved : action.Models assignment (ConditionalSchedule.follow label before schedule).equations)
    (output : O) (present : output ∈ (ConditionalSchedule.follow label before schedule).present)
    (isProtected : protectedOccurrence output) :
    Derivable (ProofUse.Hypotheses action assignment label
        (ProofUse.followOrigins protectedOccurrence ProofUse.initialOrigins schedule output))
      (SchemaPublicationAuthority.Infers action label protectedOccurrence activate installed)
      (action.apply assignment (label output)) := by
  have executable := (ConditionalSchedule.compile_holds_iff action label before schedule).mp enabled
  have admitted : ProofUse.Admitted protectedOccurrence (schedule.map Prod.fst) schedule := by
    intro firing member
    left
    exact List.mem_map.mpr ⟨firing, member, rfl⟩
  have correct := ProofUse.executable_preserves protectedOccurrence action label (schedule.map Prod.fst)
    before ProofUse.initialOrigins schedule executable admitted
    (ProofUse.initial_correct protectedOccurrence action label (schedule.map Prod.fst) before)
  exact derivable_origin protectedOccurrence action label activate installed computed authorized
    (correct assignment solved output present isProtected)

theorem compiled_cut (action : SubstitutionAction T S) (label : O → T)
    (activate : R → X → Option (RuleInstance T)) (installed : List R)
    (sources : List (SourceFiring R X O)) (schedule : List (ConditionalSchedule.Firing T O))
    (computed : lowerAll activate sources = some schedule)
    (authorized : ∀ source ∈ sources, source.schema ∈ installed)
    (before : Configuration T O)
    (enabled : (ConditionalSchedule.compile label schedule).Holds action label before)
    (assignment : S) (solved : action.Models assignment (ConditionalSchedule.follow label before schedule).equations)
    (output : O) (present : output ∈ (ConditionalSchedule.follow label before schedule).present)
    (isProtected : protectedOccurrence output) (replacement : T → Prop)
    (supply : ∀ source ∈ ProofUse.followOrigins protectedOccurrence ProofUse.initialOrigins schedule output,
      Derivable replacement (SchemaPublicationAuthority.Infers action label protectedOccurrence activate installed)
        (action.apply assignment (label source))) :
    Derivable replacement (SchemaPublicationAuthority.Infers action label protectedOccurrence activate installed)
      (action.apply assignment (label output)) := by
  apply (compiled_derivation protectedOccurrence action label activate installed sources schedule computed authorized
    before enabled assignment solved output present isProtected).cut
  intro judgment assumed
  obtain ⟨source, member, same⟩ := assumed
  rw [same]
  exact supply source member

end ProofUse

section System

variable [DecidableEq O] {location : O → N} {protectedOccurrence : O → Prop}

theorem executable_system_run (system : SchemaPublicationAuthority.System R N I O location protectedOccurrence)
    (activate : R → X → Option (RuleInstance T)) (action : SubstitutionAction T S) (label : O → T)
    {sources : List (SourceFiring R X O)} {schedule : List (ConditionalSchedule.Firing T O)}
    (computed : lowerAll activate sources = some schedule) :
    ∀ before : Configuration T O, ConditionalSchedule.Executable action label before schedule →
      (∀ source ∈ sources, source.schema ∈ (system.process system.kernel).schemas ∧
        PublicationAuthority.Formed (system.process system.kernel).rights location source.selection) →
      system.Run activate action label before (List.replicate schedule.length system.kernel)
        (ConditionalSchedule.follow label before schedule) := by
  have related := (lowerAll_iff activate sources schedule).mp computed
  clear computed
  induction related with
  | nil => intro before _ _; exact .nil before
  | @cons source firing sources schedule lowered rest earlier =>
      intro before executable authorized
      obtain ⟨rule, origin, rfl⟩ := lower_origin activate source lowered
      have allowed := authorized source (by simp)
      refine .cons ?_ (earlier _ executable.2 (fun next member => authorized next (List.mem_cons_of_mem _ member)))
      exact ⟨source.schema, allowed.1, source.inputs, rule, origin, source.selection, executable.1, allowed.2, rfl⟩

theorem compiled_system_run (system : SchemaPublicationAuthority.System R N I O location protectedOccurrence)
    (activate : R → X → Option (RuleInstance T)) (action : SubstitutionAction T S) (label : O → T)
    {sources : List (SourceFiring R X O)} {schedule : List (ConditionalSchedule.Firing T O)}
    (computed : lowerAll activate sources = some schedule) (before : Configuration T O)
    (enabled : (ConditionalSchedule.compile label schedule).Holds action label before)
    (authorized : ∀ source ∈ sources, source.schema ∈ (system.process system.kernel).schemas ∧
      PublicationAuthority.Formed (system.process system.kernel).rights location source.selection) :
    system.Run activate action label before (List.replicate schedule.length system.kernel)
      (ConditionalSchedule.follow label before schedule) :=
  executable_system_run system activate action label computed before
    ((ConditionalSchedule.compile_holds_iff action label before schedule).mp enabled) authorized

end System

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SchemaSchedules
