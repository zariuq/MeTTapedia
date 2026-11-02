import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Provenance
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.InteractionTypes.Facets

/-!
# Publication rights imply the protected-space admission boundary

Locations belong to physical occurrences, independently of substitutions of
their values. Publication uses the existing `send` facet. A process selects
one of its installed rules and an ordinary valid occurrence firing, then must
hold the send rights for its actual fresh outputs.

The sole-writer policy derives the admission disjunction required by the
provenance theorem. It is not supplied as an assumption of each firing.
These are publication rights; take/read/observation rights, binding authority,
logical justification of installed rules and native enforcement remain
separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PublicationAuthority

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.InteractionTypes (Rights)

universe uT uS uO uN uI
variable {T : Type uT} {S : Type uS} {O : Type uO} {N : Type uN} {I : Type uI}

/-- The send-right component of formation, checked on the actual output
identities before publication. It asserts no logical theorem validity. -/
def Formed (rights : Rights N) (location : O → N) (selection : Selection O) : Prop :=
  ∀ occurrence ∈ selection.made, rights (location occurrence) .send = true

structure Process (T : Type uT) (N : Type uN) where
  rights : Rights N
  rules : List (RuleInstance T)

namespace Process

variable [DecidableEq O]

def Step (process : Process T N) (A : SubstitutionAction T S) (label : O → T)
    (location : O → N) (before after : Configuration T O) : Prop :=
  ∃ rule ∈ process.rules, ∃ selection : Selection O,
    selection.Valid A label rule before ∧ Formed process.rights location selection ∧
      after = selection.result label rule before

theorem step_is_ordinary {process : Process T N} {A : SubstitutionAction T S}
    {label : O → T} {location : O → N} {before after : Configuration T O}
    (step : process.Step A label location before after) :
    ∃ rule ∈ process.rules, ConstraintMultisetRewriting.Step A label rule before after := by
  obtain ⟨rule, installed, selection, valid, _, rfl⟩ := step
  exact ⟨rule, installed, selection, valid, rfl⟩

end Process

/-- Publication protection concerns occurrence location, so unifying equal
values in different spaces does not grant a send capability. -/
structure System (T : Type uT) (N : Type uN) (I : Type uI) (O : Type uO)
    (location : O → N) (protectedOccurrence : O → Prop) where
  process : I → Process T N
  kernel : I
  soleWriter : ∀ actor, actor ≠ kernel → ∀ occurrence, protectedOccurrence occurrence →
    (process actor).rights (location occurrence) .send = false

namespace System

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

variable [DecidableEq O] {location : O → N} {protectedOccurrence : O → Prop}
  (system : System T N I O location protectedOccurrence)

def Step (A : SubstitutionAction T S) (label : O → T) (actor : I)
    (before after : Configuration T O) : Prop :=
  (system.process actor).Step A label location before after

theorem step_has_publication_boundary (A : SubstitutionAction T S) (label : O → T)
    {actor : I} {before after : Configuration T O}
    (step : system.Step A label actor before after) :
    Provenance.SystemStep A label protectedOccurrence (system.process system.kernel).rules before after := by
  obtain ⟨rule, installed, selection, valid, formed, rfl⟩ := step
  refine ⟨rule, selection, valid, ?_, rfl⟩
  by_cases kernelActor : actor = system.kernel
  · subst actor
    exact Or.inl installed
  · right
    intro occurrence made protectedHere
    have permitted := formed occurrence made
    rw [system.soleWriter actor kernelActor occurrence protectedHere] at permitted
    cases permitted

theorem nonwriter_creates_no_protected_occurrence (A : SubstitutionAction T S) (label : O → T)
    {actor : I} {before after : Configuration T O}
    (notKernel : actor ≠ system.kernel) (step : system.Step A label actor before after)
    {occurrence : O} (present : occurrence ∈ after.present) (isProtected : protectedOccurrence occurrence) :
    occurrence ∈ before.present := by
  obtain ⟨rule, _, selection, _, formed, rfl⟩ := step
  rcases mem_fire.mp present with survived | produced
  · exact survived.1
  · have made : occurrence ∈ selection.made := by simpa [Selection.commit] using produced
    have permitted := formed occurrence made
    rw [system.soleWriter actor notKernel occurrence isProtected] at permitted
    cases permitted

inductive Run (A : SubstitutionAction T S) (label : O → T) :
    Configuration T O → List I → Configuration T O → Prop
  | nil (state : Configuration T O) : Run A label state [] state
  | cons {before middle after : Configuration T O} {actor : I} {schedule : List I} :
      system.Step A label actor before middle → Run A label middle schedule after →
        Run A label before (actor :: schedule) after

theorem step_allDerivable [DecidablePred protectedOccurrence]
    (A : SubstitutionAction T S) (label : O → T) (initial : T → Prop)
    {actor : I} {before after : Configuration T O}
    (step : system.Step A label actor before after)
    (prior : Provenance.AllDerivable A label protectedOccurrence
      (system.process system.kernel).rules initial before) :
    Provenance.AllDerivable A label protectedOccurrence
      (system.process system.kernel).rules initial after :=
  Provenance.step_preserves A label protectedOccurrence _ initial
    (system.step_has_publication_boundary A label step) prior

/-- A certificate schedules ordinary firings. Protection follows from send
rights and installed membership, without a second proof interpreter. -/
theorem run_allDerivable [DecidablePred protectedOccurrence]
    (A : SubstitutionAction T S) (label : O → T) (initial : T → Prop)
    {before after : Configuration T O} {schedule : List I}
    (run : system.Run A label before schedule after)
    (prior : Provenance.AllDerivable A label protectedOccurrence
      (system.process system.kernel).rules initial before) :
    Provenance.AllDerivable A label protectedOccurrence
      (system.process system.kernel).rules initial after := by
  induction run with
  | nil => exact prior
  | cons step _ ih => exact ih (system.step_allDerivable A label initial step prior)

end System

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PublicationAuthority
