import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.OccurrenceStep
import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.TierZeroKernel

/-!
# Theorem-space provenance under shared constraint refinement

An existing protected occurrence must have a derivation in every solution of
the current equations. Refinement preserves that obligation for survivors.
New protected occurrences require an installed rule instance, whose premises
are precisely the protected take/read occurrences actually selected.

The derivation closure is the existing guarded-rewriting closure. There is
no proof-object evaluator. This establishes provenance from installed rules,
not adequacy of those rules for any particular guest logic. Resource and
binding authority must separately justify the publication boundary supplied
to the system-step relation below.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Provenance

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.TierZeroKernel (Derivable)

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

def premises (selection : Selection O) (protectedOccurrence : O → Prop)
    [DecidablePred protectedOccurrence] : Finset O :=
  (selection.taken.toFinset ∪ selection.read.toFinset).filter protectedOccurrence

/-- A declarative inference extracted from the same selected occurrences and
equation solution as the operational step. All checks remain in `Valid`. -/
def Infers (A : SubstitutionAction T S) (label : O → T)
    (protectedOccurrence : O → Prop) [DecidablePred protectedOccurrence]
    (installed : List (RuleInstance T)) (hypotheses : Multiset T) (conclusion : T) : Prop :=
  ∃ rule ∈ installed, ∃ before : Configuration T O, ∃ selection : Selection O, ∃ σ : S,
    selection.Valid A label rule before ∧ A.Models σ (selection.problem label rule before) ∧
      hypotheses = labels (fun o => A.apply σ (label o)) (premises selection protectedOccurrence) ∧
      ∃ o ∈ selection.made, protectedOccurrence o ∧ conclusion = A.apply σ (label o)

def AllDerivable (A : SubstitutionAction T S) (label : O → T)
    (protectedOccurrence : O → Prop) [DecidablePred protectedOccurrence]
    (installed : List (RuleInstance T)) (initial : T → Prop) (state : Configuration T O) : Prop :=
  ∀ σ, A.Models σ state.equations → ∀ o ∈ state.present, protectedOccurrence o →
    Derivable initial (Infers A label protectedOccurrence installed) (A.apply σ (label o))

theorem valid_preserves (A : SubstitutionAction T S) (label : O → T)
    (protectedOccurrence : O → Prop) [DecidablePred protectedOccurrence]
    (installed : List (RuleInstance T)) (initial : T → Prop)
    {rule : RuleInstance T} {before : Configuration T O} {selection : Selection O}
    (valid : selection.Valid A label rule before)
    (admission : rule ∈ installed ∨ ∀ o ∈ selection.made, ¬ protectedOccurrence o)
    (prior : AllDerivable A label protectedOccurrence installed initial before) :
    AllDerivable A label protectedOccurrence installed initial
      (selection.result label rule before) := by
  intro σ solved o member isProtected
  have oldModels : A.Models σ before.equations := valid.refines σ solved
  have partition : (o ∈ before.present ∧ o ∉ (selection.commit (T := T)).taken) ∨
      o ∈ (selection.commit (T := T)).made := mem_fire.mp member
  rcases partition with survived | produced
  · exact prior σ oldModels o survived.1 isProtected
  · have outputMember : o ∈ selection.made := by simpa [Selection.commit] using produced
    rcases admission with admitted | noPublish
    · apply Derivable.infer (premises :=
        labels (fun o => A.apply σ (label o)) (premises selection protectedOccurrence))
      · exact ⟨rule, admitted, before, selection, σ, valid, solved, rfl,
          o, outputMember, isProtected, rfl⟩
      · intro judgment inPremises
        obtain ⟨source, sourceMember, rfl⟩ := Multiset.mem_map.mp inPremises
        have selected : source ∈ premises selection protectedOccurrence := by simpa using sourceMember
        obtain ⟨gathered, protectedSource⟩ := Finset.mem_filter.mp selected
        have present : source ∈ before.present := by
          rcases Finset.mem_union.mp gathered with consumed | read
          · exact valid.occurrences.taken_subset consumed
          · exact valid.occurrences.kept_subset read
        exact prior σ oldModels source present protectedSource
    · exact False.elim (noPublish o outputMember isProtected)

/-- System steps either use an installed rule or publish no protected
occurrence. This boundary is an explicit premise, not a claimed theorem about
an unmodeled native authority mechanism. -/
def SystemStep (A : SubstitutionAction T S) (label : O → T)
    (protectedOccurrence : O → Prop) (installed : List (RuleInstance T))
    (before after : Configuration T O) : Prop :=
  ∃ rule : RuleInstance T, ∃ selection : Selection O,
    selection.Valid A label rule before ∧
      (rule ∈ installed ∨ ∀ o ∈ selection.made, ¬ protectedOccurrence o) ∧
      after = selection.result label rule before

theorem step_preserves (A : SubstitutionAction T S) (label : O → T)
    (protectedOccurrence : O → Prop) [DecidablePred protectedOccurrence]
    (installed : List (RuleInstance T)) (initial : T → Prop)
    {before after : Configuration T O}
    (step : SystemStep A label protectedOccurrence installed before after)
    (prior : AllDerivable A label protectedOccurrence installed initial before) :
    AllDerivable A label protectedOccurrence installed initial after := by
  obtain ⟨rule, selection, valid, admitted, rfl⟩ := step
  exact valid_preserves A label protectedOccurrence installed initial valid admitted prior

theorem run_preserves (A : SubstitutionAction T S) (label : O → T)
    (protectedOccurrence : O → Prop) [DecidablePred protectedOccurrence]
    (installed : List (RuleInstance T)) (initial : T → Prop)
    {before after : Configuration T O}
    (run : Relation.ReflTransGen (SystemStep A label protectedOccurrence installed) before after)
    (prior : AllDerivable A label protectedOccurrence installed initial before) :
    AllDerivable A label protectedOccurrence installed initial after := by
  induction run with
  | refl => exact prior
  | tail _ step ih => exact step_preserves A label protectedOccurrence installed initial step ih

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Provenance
