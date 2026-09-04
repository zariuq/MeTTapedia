import Mettapedia.GSLT.LanguageDef.GSLTILEvidenceWorlds
import Mettapedia.TypeTheory.EffectfulFamilyObserverFactorization
import Mettapedia.TypeTheory.WitnessRetainingDependentSequencing

/-!
# Dependent continuations over elaboration worlds

An elaboration world retains both a visible internal command and the exact
evidence which produced it.  A continuation may depend on either coordinate.
Forgetting evidence is therefore sound for dependent continuations only when
their fibres descend, up to equivalence, along the visible-outcome observer.

History thinness makes the complete world equivalent to the subtype of
realized visible outcomes.  Consequently every dependent continuation then
descends to realized outcomes.  Without history thinness, outcome-only
continuations still descend, but history-sensitive continuations need not.
The obstruction persists through answer effects whenever the effect retains
the relevant fibre distinction.

This is an observer-relative compatibility theorem.  It does not select an
elaboration policy, identify proof histories with visible terms, or choose a
particular object-language type theory.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.ElaborationWorldDependentContinuation

open Mettapedia.GSLT.Dynamics.AnswerEffects
open Mettapedia.GSLT.LanguageDef.GSLTIL.EvidenceWorlds
open Mettapedia.GSLT.LanguageDef.GSLTIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.TypeTheory.DependentFamilyObserverFactorization
open Mettapedia.TypeTheory.EffectfulFamilyObserverFactorization
open Mettapedia.TypeTheory.WitnessRetainingDependentSequencing

universe u uSource uTarget uFibre

variable {program : Program}
variable (worldSystem :
  Mettapedia.GSLT.LanguageDef.GSLTIL.EvidenceWorlds.Profile program)
variable (command : worldSystem.Command)

/-! ## Visible and realized outcomes -/

/-- Forget the evidence coordinate of one complete elaboration world. -/
def visibleOutcome (world : worldSystem.World command) : Pattern :=
  world.1

/-- A visible command together with mere evidence that it is realized by the
given surface command.  This forgets which evidence realizes it. -/
abbrev RealizedOutcome : Type :=
  { internal : Pattern // Nonempty (worldSystem.Evidence command internal) }

/-- Project a complete elaboration world to its realized visible outcome. -/
def realizedOutcome (world : worldSystem.World command) :
    RealizedOutcome (worldSystem := worldSystem) (command := command) :=
  ⟨world.1, ⟨world.2⟩⟩

/-- When fixed-outcome evidence fibres are thin, a complete world contains
exactly the same information as its realized visible outcome. -/
noncomputable def realizedOutcomeEquiv
    (thin : worldSystem.HistoryThin) :
    worldSystem.World command ≃
      RealizedOutcome (worldSystem := worldSystem) (command := command) where
  toFun := realizedOutcome (worldSystem := worldSystem) (command := command)
  invFun := fun outcome => ⟨outcome.1, Classical.choice outcome.2⟩
  left_inv := by
    rintro ⟨internal, evidence⟩
    change
      (Sigma.mk internal
          (Classical.choice
            (show Nonempty (worldSystem.Evidence command internal) from
              ⟨evidence⟩)) : worldSystem.World command) =
        Sigma.mk internal evidence
    exact Sigma.ext rfl
      (heq_of_eq ((thin command internal).allEq _ _))
  right_inv := by
    intro outcome
    apply Subtype.ext
    rfl

/-! ## Continuation-family descent -/

/-- Transport any dependent family through an equivalence used as its
observer. -/
noncomputable def factorThroughEquivalence
    {Source : Type uSource} {Target : Type uTarget}
    (observer : Source ≃ Target)
    (family : Source → Type uFibre) :
    FamilyFactorization observer family where
  targetFamily := fun target => family (observer.symm target)
  identify := fun source =>
    Equiv.cast (congrArg family (observer.symm_apply_apply source).symm)

/-- History thinness is sufficient for every continuation family to descend
to realized visible outcomes. -/
noncomputable def everyContinuationFactors_of_historyThin
    (thin : worldSystem.HistoryThin)
    (continuation : worldSystem.World command → Type u) :
    FamilyFactorization
      (realizedOutcome (worldSystem := worldSystem) (command := command))
      continuation :=
  factorThroughEquivalence
    (realizedOutcomeEquiv (worldSystem := worldSystem)
      (command := command) thin) continuation

/-- A continuation which was already indexed only by the visible outcome
always descends, independently of history multiplicity. -/
def outcomeOnlyContinuation (result : Pattern → Type u) :
    worldSystem.World command → Type u :=
  fun world => result
    (visibleOutcome (worldSystem := worldSystem) (command := command) world)

/-- The exact factorization for an outcome-only continuation. -/
def outcomeOnlyFactors (result : Pattern → Type u) :
    FamilyFactorization
      (visibleOutcome (worldSystem := worldSystem) (command := command))
      (outcomeOnlyContinuation (worldSystem := worldSystem)
        (command := command) result) :=
  FamilyFactorization.pullback
    (visibleOutcome (worldSystem := worldSystem) (command := command)) result

/-- Outcome-compatible continuation fibres remain compatible after applying
any answer effect pointwise. -/
def outcomeOnlyFactorsThroughAnswerEffect
    (result : Pattern → Type u) (effect : AnswerEffect.{u}) :
    FamilyFactorization
      (visibleOutcome (worldSystem := worldSystem) (command := command))
      (fun world => effect.Carrier
        (outcomeOnlyContinuation (worldSystem := worldSystem)
          (command := command) result world)) :=
  FamilyFactorization.throughAnswerEffect
    (outcomeOnlyFactors (worldSystem := worldSystem)
      (command := command) result) effect

/-! ## Proof-relevant dependent choice -/

/-- Sequence an answer collection of complete worlds with a continuation
whose result type may depend on the selected world.  The sigma result retains
that world rather than silently contracting it to its visible outcome. -/
def chooseWorldDependent (effect : AnswerEffect)
    (continuation : worldSystem.World command → Type)
    (worlds : effect.Carrier (worldSystem.World command))
    (next : (world : worldSystem.World command) →
      effect.Carrier (continuation world)) :
    effect.Carrier (Sigma continuation) :=
  bindSigma effect worlds next

/-- Dependent world choice is natural under every operation-preserving
answer-effect morphism.  This preserves the sigma witness while allowing an
explicit downstream map to forget order or multiplicity. -/
theorem morphism_map_chooseWorldDependent
    {first second : AnswerEffect}
    (morphism : AnswerEffect.Morphism first second)
    (continuation : worldSystem.World command → Type)
    (worlds : first.Carrier (worldSystem.World command))
    (next : (world : worldSystem.World command) →
      first.Carrier (continuation world)) :
    morphism.map
        (chooseWorldDependent worldSystem command first continuation worlds next) =
      chooseWorldDependent worldSystem command second continuation
        (morphism.map worlds) (fun world => morphism.map (next world)) :=
  morphism_map_bindSigma morphism worlds next

/-! ## Positive and negative controls -/

namespace Canary

open Mettapedia.GSLT.LanguageDef.GSLTIL.EvidenceWorlds.Canary

abbrev duplicateSystem := duplicateHistoryProfile

/-- The two worlds have one visible internal command but retain different
derivation histories. -/
def firstWorld : duplicateSystem.World () :=
  ⟨_, DuplicateHistory.first⟩

def secondWorld : duplicateSystem.World () :=
  ⟨_, DuplicateHistory.second⟩

theorem worlds_have_same_visible_outcome :
    visibleOutcome (worldSystem := duplicateSystem) (command := ()) firstWorld =
      visibleOutcome (worldSystem := duplicateSystem) (command := ())
        secondWorld :=
  rfl

/-- A decidable tag used only to witness that the two retained histories are
not equal. -/
def historyTag : duplicateSystem.World () → Bool
  | ⟨_, DuplicateHistory.first⟩ => false
  | ⟨_, DuplicateHistory.second⟩ => true

theorem firstWorld_ne_secondWorld : firstWorld ≠ secondWorld := by
  intro equalWorlds
  have equalTags := congrArg historyTag equalWorlds
  simp [historyTag, firstWorld, secondWorld] at equalTags

/-- A deliberately history-sensitive continuation: the first derivation
continues into a singleton fibre and the second into a Boolean fibre. -/
def historySensitiveContinuation : duplicateSystem.World () → Type
  | ⟨_, DuplicateHistory.first⟩ => PUnit
  | ⟨_, DuplicateHistory.second⟩ => Bool

/-- Forgetting history cannot carry the history-sensitive continuation
family, because the two identified worlds have non-equivalent fibres. -/
theorem historySensitiveContinuation_does_not_factor :
    ¬ Nonempty
      (FamilyFactorization
        (visibleOutcome (worldSystem := duplicateSystem) (command := ()))
        historySensitiveContinuation) := by
  apply FamilyFactorization.not_nonempty_of_nonEquivalent_fibres
    (left := firstWorld) (right := secondWorld)
    worlds_have_same_visible_outcome
  simpa [historySensitiveContinuation, firstWorld, secondWorld] using
    Mettapedia.TypeTheory.DependentFamilyObserverFactorization.Canary.unit_not_equiv_bool

/-- Finite-support answer collection retains the cardinality distinction
between the two continuation fibres. -/
theorem finset_punit_not_equiv_finset_bool :
    ¬ Nonempty (Finset PUnit ≃ Finset Bool) := by
  rintro ⟨equivalence⟩
  have equalCardinality := Fintype.card_congr equivalence
  simp at equalCardinality

/-- Applying a support-set answer effect does not repair the invalid history
erasure: its resulting fibres are still non-equivalent. -/
theorem supportHistorySensitive_does_not_factor :
    ¬ Nonempty
      (FamilyFactorization
        (visibleOutcome (worldSystem := duplicateSystem) (command := ()))
        (fun world => supportEffect.Carrier
          (historySensitiveContinuation world))) := by
  apply FamilyFactorization.not_nonempty_of_nonEquivalent_fibres
    (left := firstWorld) (right := secondWorld)
    worlds_have_same_visible_outcome
  simpa [historySensitiveContinuation, firstWorld, secondWorld,
    supportEffect] using finset_punit_not_equiv_finset_bool

/-- A constant continuation family descends to visible outcomes. -/
def constantUnitFactorization :
    FamilyFactorization
      (visibleOutcome (worldSystem := duplicateSystem) (command := ()))
      (fun _world : duplicateSystem.World () => PUnit) :=
  outcomeOnlyFactors (worldSystem := duplicateSystem)
    (command := ()) (fun _ => PUnit)

/-- Even though the constant family descends, its induced total-space
observer still identifies values carrying the two distinct histories. -/
theorem factorization_does_not_make_total_observer_faithful :
    ¬ Function.Injective constantUnitFactorization.totalObservation := by
  intro injective
  let firstValue : Sigma (fun _world : duplicateSystem.World () => PUnit) :=
    ⟨firstWorld, PUnit.unit⟩
  let secondValue : Sigma (fun _world : duplicateSystem.World () => PUnit) :=
    ⟨secondWorld, PUnit.unit⟩
  have sameObservation :
      constantUnitFactorization.totalObservation firstValue =
        constantUnitFactorization.totalObservation secondValue := by
    rfl
  have sameValue := injective sameObservation
  exact firstWorld_ne_secondWorld (congrArg Sigma.fst sameValue)

/-- Paired boundary: visible-outcome dependency is stable through ordered
choice, while derivation-sensitive dependency is rejected both before and
after a support-retaining answer effect. -/
theorem dependent_continuation_observer_boundary :
    Nonempty
        (FamilyFactorization
          (visibleOutcome (worldSystem := duplicateSystem) (command := ()))
          (outcomeOnlyContinuation (worldSystem := duplicateSystem)
            (command := ()) (fun _ => Bool))) ∧
      Nonempty
        (FamilyFactorization
          (visibleOutcome (worldSystem := duplicateSystem) (command := ()))
          (fun world => listEffect.Carrier
            (outcomeOnlyContinuation (worldSystem := duplicateSystem)
              (command := ()) (fun _ => Bool) world))) ∧
      ¬ Nonempty
        (FamilyFactorization
          (visibleOutcome (worldSystem := duplicateSystem) (command := ()))
          historySensitiveContinuation) ∧
      ¬ Nonempty
        (FamilyFactorization
          (visibleOutcome (worldSystem := duplicateSystem) (command := ()))
          (fun world => supportEffect.Carrier
            (historySensitiveContinuation world))) :=
  ⟨⟨outcomeOnlyFactors (worldSystem := duplicateSystem)
      (command := ()) (fun _ => Bool)⟩,
    ⟨outcomeOnlyFactorsThroughAnswerEffect (worldSystem := duplicateSystem)
      (command := ()) (fun _ => Bool) listEffect⟩,
    historySensitiveContinuation_does_not_factor,
    supportHistorySensitive_does_not_factor⟩

end Canary

#print axioms realizedOutcomeEquiv
#print axioms factorThroughEquivalence
#print axioms everyContinuationFactors_of_historyThin
#print axioms outcomeOnlyFactors
#print axioms outcomeOnlyFactorsThroughAnswerEffect
#print axioms morphism_map_chooseWorldDependent
#print axioms Canary.historySensitiveContinuation_does_not_factor
#print axioms Canary.supportHistorySensitive_does_not_factor
#print axioms Canary.factorization_does_not_make_total_observer_faithful
#print axioms Canary.dependent_continuation_observer_boundary

end Mettapedia.GSLT.Dynamics.ElaborationWorldDependentContinuation
