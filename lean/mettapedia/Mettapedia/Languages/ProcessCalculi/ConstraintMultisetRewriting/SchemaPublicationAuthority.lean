import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PublicationAuthority

/-!
# Installed schema origins and publication rights on ordinary firings

A process installs source schemas. Each firing supplies inputs and obtains
its rule instance through the actual activation function. Protected publication
therefore retains both installed-schema membership and computed activation
origin, rather than trusting an arbitrary supplied concrete instance.

Send rights act on immutable physical locations. The sole-writer policy
derives the publication boundary. This package does not establish guest logic
adequacy, premise routing, read/take/binding rights, schema promotion or native
enforcement; these remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SchemaPublicationAuthority

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.InteractionTypes (Rights)
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.TierZeroKernel (Derivable)

universe uT uS uO uN uI uR uX
variable {T : Type uT} {S : Type uS} {O : Type uO} {N : Type uN}
  {I : Type uI} {R : Type uR} {X : Type uX}

structure Process (R : Type uR) (N : Type uN) where
  rights : Rights N
  schemas : List R

namespace Process

variable [DecidableEq O]

def Step (process : Process R N) (activate : R → X → Option (RuleInstance T))
    (action : SubstitutionAction T S) (label : O → T) (location : O → N)
    (before after : Configuration T O) : Prop :=
  ∃ schema ∈ process.schemas, ∃ inputs rule, activate schema inputs = some rule ∧
    ∃ picked : Selection O, picked.Valid action label rule before ∧
      PublicationAuthority.Formed process.rights location picked ∧ after = picked.result label rule before

theorem step_is_ordinary {process : Process R N} {activate : R → X → Option (RuleInstance T)}
    {action : SubstitutionAction T S} {label : O → T} {location : O → N} {before after : Configuration T O}
    (stepped : process.Step activate action label location before after) :
    ∃ schema ∈ process.schemas, ∃ inputs rule, activate schema inputs = some rule ∧
      ConstraintMultisetRewriting.Step action label rule before after := by
  obtain ⟨schema, installed, inputs, rule, computed, picked, valid, _, destination⟩ := stepped
  exact ⟨schema, installed, inputs, rule, computed, picked, valid, destination⟩

end Process

/-- Logical inference keeps the installed source schema and the actual
successful activation, alongside the complete ordinary firing evidence. -/
def Infers [DecidableEq O] (action : SubstitutionAction T S) (label : O → T)
    (protectedOccurrence : O → Prop) [DecidablePred protectedOccurrence]
    (activate : R → X → Option (RuleInstance T)) (installed : List R)
    (hypotheses : Multiset T) (conclusion : T) : Prop :=
  ∃ schema ∈ installed, ∃ inputs rule, activate schema inputs = some rule ∧
    Provenance.Infers action label protectedOccurrence [rule] hypotheses conclusion

def AllDerivable [DecidableEq O] (action : SubstitutionAction T S) (label : O → T)
    (protectedOccurrence : O → Prop) [DecidablePred protectedOccurrence]
    (activate : R → X → Option (RuleInstance T)) (installed : List R)
    (initial : T → Prop) (state : Configuration T O) : Prop :=
  ∀ assignment, action.Models assignment state.equations →
    ∀ occurrence ∈ state.present, protectedOccurrence occurrence →
      Derivable initial (Infers action label protectedOccurrence activate installed)
        (action.apply assignment (label occurrence))

structure System (R : Type uR) (N : Type uN) (I : Type uI) (O : Type uO)
    (location : O → N) (protectedOccurrence : O → Prop) where
  process : I → Process R N
  kernel : I
  soleWriter : ∀ actor, actor ≠ kernel → ∀ occurrence, protectedOccurrence occurrence →
    (process actor).rights (location occurrence) .send = false

namespace System

variable [DecidableEq O] {location : O → N} {protectedOccurrence : O → Prop}
    (system : System R N I O location protectedOccurrence)

def Step (activate : R → X → Option (RuleInstance T)) (action : SubstitutionAction T S)
    (label : O → T) (actor : I) (before after : Configuration T O) : Prop :=
  (system.process actor).Step activate action label location before after

theorem nonwriter_creates_no_protected_occurrence
    (activate : R → X → Option (RuleInstance T)) (action : SubstitutionAction T S) (label : O → T)
    {actor : I} {before after : Configuration T O} (notKernel : actor ≠ system.kernel)
    (stepped : system.Step activate action label actor before after)
    {occurrence : O} (present : occurrence ∈ after.present) (isProtected : protectedOccurrence occurrence) :
    occurrence ∈ before.present := by
  obtain ⟨_, _, _, _, _, picked, _, formed, rfl⟩ := stepped
  rcases mem_fire.mp present with survived | produced
  · exact survived.1
  · have made : occurrence ∈ picked.made := by simpa [Selection.commit] using produced
    have permitted := formed occurrence made
    rw [system.soleWriter actor notKernel occurrence isProtected] at permitted
    cases permitted

theorem step_allDerivable [DecidablePred protectedOccurrence]
    (activate : R → X → Option (RuleInstance T)) (action : SubstitutionAction T S) (label : O → T)
    (initial : T → Prop) {actor : I} {before after : Configuration T O}
    (stepped : system.Step activate action label actor before after)
    (prior : AllDerivable action label protectedOccurrence activate (system.process system.kernel).schemas initial before) :
    AllDerivable action label protectedOccurrence activate (system.process system.kernel).schemas initial after := by
  obtain ⟨schema, installed, inputs, rule, computed, picked, valid, formed, rfl⟩ := stepped
  intro assignment solved occurrence present isProtected
  have oldModels := valid.refines assignment solved
  rcases mem_fire.mp present with survived | produced
  · exact prior assignment oldModels occurrence survived.1 isProtected
  · have made : occurrence ∈ picked.made := by simpa [Selection.commit] using produced
    by_cases kernelActor : actor = system.kernel
    · subst actor
      apply Derivable.infer (premises := labels (fun source => action.apply assignment (label source))
        (Provenance.premises picked protectedOccurrence))
      · refine ⟨schema, installed, inputs, rule, computed, rule, by simp, before, picked,
          assignment, valid, solved, rfl, occurrence, made, isProtected, rfl⟩
      · intro judgment member
        obtain ⟨source, selectedMember, rfl⟩ := Multiset.mem_map.mp member
        have selected : source ∈ Provenance.premises picked protectedOccurrence := by simpa using selectedMember
        obtain ⟨gathered, protectedSource⟩ := Finset.mem_filter.mp selected
        have sourcePresent : source ∈ before.present := by
          rcases Finset.mem_union.mp gathered with consumed | read
          · exact valid.occurrences.taken_subset consumed
          · exact valid.occurrences.kept_subset read
        exact prior assignment oldModels source sourcePresent protectedSource
    · have permitted := formed occurrence made
      rw [system.soleWriter actor kernelActor occurrence isProtected] at permitted
      cases permitted

inductive Run (activate : R → X → Option (RuleInstance T)) (action : SubstitutionAction T S)
    (label : O → T) : Configuration T O → List I → Configuration T O → Prop
  | nil (state : Configuration T O) : Run activate action label state [] state
  | cons {before middle after : Configuration T O} {actor : I} {schedule : List I} :
      system.Step activate action label actor before middle → Run activate action label middle schedule after →
        Run activate action label before (actor :: schedule) after

theorem run_allDerivable [DecidablePred protectedOccurrence]
    (activate : R → X → Option (RuleInstance T)) (action : SubstitutionAction T S) (label : O → T)
    (initial : T → Prop) {before after : Configuration T O} {schedule : List I}
    (run : system.Run activate action label before schedule after)
    (prior : AllDerivable action label protectedOccurrence activate (system.process system.kernel).schemas initial before) :
    AllDerivable action label protectedOccurrence activate (system.process system.kernel).schemas initial after := by
  induction run with
  | nil => exact prior
  | cons stepped rest earlier => exact earlier (system.step_allDerivable activate action label initial stepped prior)

end System

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SchemaPublicationAuthority
