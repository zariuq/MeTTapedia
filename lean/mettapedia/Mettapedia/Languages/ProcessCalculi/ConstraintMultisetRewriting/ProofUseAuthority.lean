import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProofUse
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PublicationAuthority

/-!
# Publication capabilities discharge proof-use admission

A scheduled firing names an installed rule of its actor and has send rights
for the selected output identities. The sole-writer policy then supplies the
admission condition of hypothesis-use inference and cut. No per-step logical
admission disjunction is trusted from a schedule's author.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProofUseAuthority

open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.TierZeroKernel (Derivable)

universe uT uS uO uN uI
variable {T : Type uT} {S : Type uS} {O : Type uO} {N : Type uN} {I : Type uI}
  [DecidableEq O] {location : O → N} {protectedOccurrence : O → Prop}
  [DecidablePred protectedOccurrence]

omit [DecidableEq O] [DecidablePred protectedOccurrence] in
theorem admitted_of_rights (system : PublicationAuthority.System T N I O location protectedOccurrence)
    (schedule : List (ConditionalSchedule.Firing T O))
    (authorized : ∀ firing ∈ schedule, ∃ actor,
      firing.1 ∈ (system.process actor).rules ∧
        PublicationAuthority.Formed (system.process actor).rights location firing.2) :
    ProofUse.Admitted protectedOccurrence (system.process system.kernel).rules schedule := by
  intro firing member
  obtain ⟨actor, installed, formed⟩ := authorized firing member
  by_cases isKernel : actor = system.kernel
  · subst actor
    exact Or.inl installed
  · right
    intro occurrence made isProtected
    have permitted := formed occurrence made
    rw [system.soleWriter actor isKernel occurrence isProtected] at permitted
    cases permitted

theorem compiled_cut (system : PublicationAuthority.System T N I O location protectedOccurrence)
    (A : SubstitutionAction T S) (label : O → T)
    (before : Configuration T O) (schedule : List (ConditionalSchedule.Firing T O))
    (enabled : (ConditionalSchedule.compile label schedule).Holds A label before)
    (authorized : ∀ firing ∈ schedule, ∃ actor,
      firing.1 ∈ (system.process actor).rules ∧
        PublicationAuthority.Formed (system.process actor).rights location firing.2)
    (assignment : S) (solved : A.Models assignment (ConditionalSchedule.follow label before schedule).equations)
    (occurrence : O) (present : occurrence ∈ (ConditionalSchedule.follow label before schedule).present)
    (isProtected : protectedOccurrence occurrence) (replacement : T → Prop)
    (supply : ∀ source ∈ ProofUse.followOrigins protectedOccurrence ProofUse.initialOrigins schedule occurrence,
      Derivable replacement (Provenance.Infers A label protectedOccurrence (system.process system.kernel).rules)
        (A.apply assignment (label source))) :
    Derivable replacement (Provenance.Infers A label protectedOccurrence (system.process system.kernel).rules)
      (A.apply assignment (label occurrence)) :=
  ProofUse.compiled_cut protectedOccurrence A label _ before schedule enabled
    (admitted_of_rights system schedule authorized) assignment solved occurrence present isProtected replacement supply

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProofUseAuthority
