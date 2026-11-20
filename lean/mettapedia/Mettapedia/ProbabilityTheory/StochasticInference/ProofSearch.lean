import Mettapedia.ProbabilityTheory.StochasticInference.ProbLogic
import Mettapedia.ProbabilityTheory.StochasticInference.Readouts

/-!
# Certified bounds from partial proof search

Rule selection may depend on any policy. In a positive Horn program it
can only remove completed proofs. Each selected proof retains its full
lineage, including shared premises, in the lower event. An upper event
can be checked by Boolean implication.
-/

set_option autoImplicit false

namespace Mettapedia.ProbabilityTheory.StochasticInference.ProbLogic

open Mettapedia.Logic.BDDCore
open StatePredicates (Diagram)

variable {n atoms : Nat}

def Implies (source target : Diagram n) : Prop :=
  ∀ x, source.val.eval x = true → target.val.eval x = true

def entails (source target : Diagram n) : Bool :=
  StatePredicates.equivalent (StatePredicates.conj source (StatePredicates.neg target))
    (StatePredicates.falsity n)

theorem entails_iff (source target : Diagram n) :
    entails source target = true ↔ Implies source target := by
  rw [entails, StatePredicates.equivalent_iff]
  simp only [Implies, StatePredicates.conj, StatePredicates.neg, StatePredicates.falsity,
    BDD.eval_zero, apply_eval, bddNot_eval]
  constructor
  · intro valid x appears
    simpa [appears] using valid x
  · intro included x
    by_cases appears : source.val.eval x = true
    · simp [included x appears]
    · simp [Bool.eq_false_iff.mpr appears]

structure DiagramBounds (target : Diagram n) where
  lower : Diagram n
  upper : Diagram n
  lower_sound : Implies lower target
  upper_sound : Implies target upper

def DiagramBounds.checked (target lower upper : Diagram n) : Option (DiagramBounds target) :=
  if lo : entails lower target = true then
    if hi : entails target upper = true then
      some ⟨lower, upper, (entails_iff _ _).mp lo, (entails_iff _ _).mp hi⟩
    else none
  else none

def DiagramBounds.asEvents {target : Diagram n} (bounds : DiagramBounds target) :
    EventBounds (binaryPositive n) (event target) where
  lower := event bounds.lower
  upper := event bounds.upper
  lower_sound := fun x proof => by
    rw [event_holds] at proof ⊢
    exact bounds.lower_sound (bits x) proof
  upper_sound := fun x proof => by
    rw [event_holds] at proof ⊢
    exact bounds.upper_sound (bits x) proof

theorem productMass_mono (p : Fin n → UnitProbability) (lower upper : Diagram n)
    (included : Implies lower upper) : productMass p lower ≤ productMass p upper := by
  have nonneg := RationalWMC.nonneg (fun i => (p i).val)
    (fun i => ⟨(p i).nonneg, (p i).le_one⟩) upper.val
  have positiveUpper : (0 : ℝ) ≤ (productMass p upper : ℝ) := Rat.cast_nonneg.mpr nonneg
  suffices h : ENNReal.ofReal (productMass p lower : ℝ) ≤ ENNReal.ofReal (productMass p upper : ℝ) by
    exact_mod_cast (ENNReal.ofReal_le_ofReal_iff positiveUpper).mp h
  rw [productMass_exact, productMass_exact]
  apply Finset.sum_le_sum
  intro x _
  by_cases appears : lower.val.eval x = true <;> simp [appears, included x]

def DiagramBounds.productInterval? {target : Diagram n} (bounds : DiagramBounds target)
    (p : Fin n → UnitProbability) (evidence : Diagram n) : Option (ℚ × ℚ) :=
  let low := productMasses p evidence bounds.lower
  let high := productMasses p evidence bounds.upper
  some (·, ·) <*> low.posterior? <*> high.posterior?

theorem DiagramBounds.productInterval_sound {target : Diagram n} (bounds : DiagramBounds target)
    (p : Fin n → UnitProbability) (evidence : Diagram n) (low high value : ℚ)
    (interval : bounds.productInterval? p evidence = some (low, high))
    (answer : (productMasses p evidence target).posterior? = some value) :
    low ≤ value ∧ value ≤ high := by
  open Mettapedia.ProbabilityTheory.BayesianNetworks.ScopedFactorReadout in
    by_cases positive : 0 < productMass p evidence
    · simp [productInterval?, productMasses, Masses.posterior?, positive] at interval answer
      obtain ⟨lo, hi⟩ := interval
      rw [← lo, ← hi, ← answer]
      have withEvidence {source dest : Diagram n} (included : Implies source dest) :
          Implies (StatePredicates.conj evidence source) (StatePredicates.conj evidence dest) := by
        intro x found
        simp only [StatePredicates.conj, apply_eval, Bool.and_eq_true] at found ⊢
        exact ⟨found.1, included x found.2⟩
      constructor
      · exact div_le_div_of_nonneg_right (productMass_mono p _ _
          (withEvidence bounds.lower_sound)) positive.le
      · exact div_le_div_of_nonneg_right (productMass_mono p _ _
          (withEvidence bounds.upper_sound)) positive.le
    · simp [productMasses, Masses.posterior?, positive] at answer

open Mettapedia.Logic.LP in
private theorem restricted_derivation {P Q : PropProgram (Fin atoms)} {facts : Finset (Fin atoms)}
    {q : Fin atoms} (includes : P ⊆ Q) (proof : Derivable P facts q) : Derivable Q facts q := by
  induction proof with
  | fact h => exact .fact h
  | rule present _ ih => exact .rule (includes present) ih

/-- Retain a sound lower event even when the rule selector or round budget
excludes some proofs. Full search can provide a sharper upper event. -/
def budgetedHorn (rules : List (HornClosure.Clause atoms)) (initial : HornClosure.Table n atoms)
    (query : Fin atoms) (keep : HornClosure.Clause atoms → Bool) (rounds : Nat) :
    DiagramBounds ((HornClosure.compile rules initial).get query) where
  lower := (HornClosure.iterate (rules.filter keep) initial rounds).get query
  upper := StatePredicates.truth n
  lower_sound := by
    intro world arrives
    apply (HornClosure.mem_facts _ _ _).mp
    rw [HornClosure.compiled_facts, Mettapedia.Logic.LP.saturate_iff_derivable]
    apply restricted_derivation (P := HornClosure.logical (rules.filter keep))
    · intro rule member
      simp only [HornClosure.logical, List.mem_toFinset, List.mem_map, List.mem_filter] at member ⊢
      obtain ⟨source, ⟨inRules, _⟩, rfl⟩ := member
      exact ⟨source, inRules, rfl⟩
    · apply Mettapedia.Logic.LP.iterate_sound _ _ rounds
      rw [← HornClosure.iterate_facts]
      exact (HornClosure.mem_facts _ _ _).mpr arrives
  upper_sound := fun _ _ => rfl

end Mettapedia.ProbabilityTheory.StochasticInference.ProbLogic
