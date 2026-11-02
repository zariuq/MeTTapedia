import Mettapedia.Languages.VibeITP.Presentation.ProofWitness
import Mettapedia.Languages.VibeITP.Spec.DerivationV2

/-!
# Finite supplied proofs for simultaneous instantiation

Existing static certificates remain explicit leaves. New modus-ponens and
simultaneous-instantiation nodes may consume arbitrary new proofs. The checker
retains ordered children and all replacements, including shadowed entries.
Soundness concerns the exact supplied witness; coverage is existential under
the existing hosted-theory contract. Native execution observations are outside
this static certificate language.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation.SimultaneousProofs

open ComputationalProofs

inductive Witness where
  | base (original : ProofWitness)
  | modusPonens (implication premise : Witness)
  | instantiateMany (replacements : List (Spec.SymId × Spec.Term)) (child : Witness)
  deriving Repr

namespace Witness

def result (theory : Spec.Theory) : Witness → Option Spec.Term
  | .base original => original.result theory
  | .modusPonens implication premise => do
      let implicationStatement ← result theory implication
      let premiseStatement ← result theory premise
      modusPonensResult implicationStatement premiseStatement
  | .instantiateMany replacements child => do
      let statement ← result theory child
      if replacements.all (fun pair => Spec.WellFormed theory.sig pair.2) then
        Spec.SimultaneousInstantiation.statement theory.sig replacements statement
      else none

inductive Checks (theory : Spec.Theory) : Witness → Spec.Term → Prop where
  | base {original : ProofWitness} {statement : Spec.Term} :
      original.Checks theory statement → Checks theory (.base original) statement
  | modusPonens {implication premise : Witness} {antecedent conclusion : Spec.Term} :
      Checks theory implication (.impl antecedent conclusion) →
      Checks theory premise antecedent →
      Checks theory (.modusPonens implication premise) conclusion
  | instantiateMany {replacements : List (Spec.SymId × Spec.Term)}
      {child : Witness} {statement conclusion : Spec.Term} :
      Checks theory child statement →
      (∀ pair ∈ replacements, Spec.WellFormed theory.sig pair.2 = true) →
      Spec.SimultaneousInstantiation.statement theory.sig replacements statement = some conclusion →
      Checks theory (.instantiateMany replacements child) conclusion

theorem Checks.eval {theory : Spec.Theory} {witness : Witness} {statement : Spec.Term}
    (checked : Checks theory witness statement) : result theory witness = some statement := by
  induction checked with
  | base original => exact original.eval
  | modusPonens _ _ implication premise =>
      simp [result, implication, premise, modusPonensResult, Spec.Term.impl]
  | instantiateMany _ formed instantiated child =>
      have allFormed := List.all_eq_true.mpr formed
      simp [result, child, allFormed, instantiated]

theorem result_sound {theory : Spec.Theory} {witness : Witness} {statement : Spec.Term}
    (accepted : result theory witness = some statement) : Checks theory witness statement := by
  induction witness generalizing statement with
  | base original => exact .base (ProofWitness.result_sound accepted)
  | modusPonens implication premise implicationIH premiseIH =>
      cases left : result theory implication with
      | none => simp [result, left] at accepted
      | some implicationStatement =>
          cases right : result theory premise with
          | none => simp [result, right] at accepted
          | some premiseStatement =>
              have operation : modusPonensResult implicationStatement premiseStatement = some statement := by
                simpa [result, left, right] using accepted
              have matched := (modusPonensResult_eq_some_iff _ _ _).mp operation
              have checked := implicationIH left
              rw [matched] at checked
              exact .modusPonens checked (premiseIH right)
  | instantiateMany replacements child childIH =>
      cases computed : result theory child with
      | none => simp [result, computed] at accepted
      | some childStatement =>
          cases formed : replacements.all (fun pair => Spec.WellFormed theory.sig pair.2) with
          | false => simp [result, computed, formed] at accepted
          | true =>
              exact .instantiateMany (childIH computed) (List.all_eq_true.mp formed)
                (by simpa [result, computed, formed] using accepted)

theorem result_eq_some_iff (theory : Spec.Theory) (witness : Witness) (statement : Spec.Term) :
    result theory witness = some statement ↔ Checks theory witness statement :=
  ⟨result_sound, Checks.eval⟩

theorem result_none_iff (theory : Spec.Theory) (witness : Witness) :
    result theory witness = none ↔ ¬ ∃ statement, Checks theory witness statement := by
  constructor
  · intro refused ⟨statement, checked⟩
    have success := checked.eval
    rw [refused] at success
    contradiction
  · intro impossible
    cases computed : result theory witness with
    | none => rfl
    | some statement => exact False.elim (impossible ⟨statement, result_sound computed⟩)

theorem Checks.derives {theory : Spec.Theory} {witness : Witness} {statement : Spec.Term}
    (checked : Checks theory witness statement) : Spec.DerivesV2 theory statement := by
  induction checked with
  | base original => exact Spec.static_derives_v2 original.derives
  | modusPonens _ _ implication premise => exact .modusPonens implication premise
  | instantiateMany _ formed instantiated child => exact .instantiateMany child formed instantiated

theorem Checks.deterministic {theory : Spec.Theory} {witness : Witness} {first second : Spec.Term}
    (left : Checks theory witness first) (right : Checks theory witness second) : first = second :=
  Option.some.inj (left.eval.symm.trans right.eval)

def check (theory : Spec.Theory) (witness : Witness) (claimed : Spec.Term) : Bool :=
  decide (result theory witness = some claimed)

theorem check_iff (theory : Spec.Theory) (witness : Witness) (claimed : Spec.Term) :
    check theory witness claimed = true ↔ Checks theory witness claimed := by
  simp only [check, decide_eq_true_eq, result_eq_some_iff]

theorem check_sound {theory : Spec.Theory} {witness : Witness} {claimed : Spec.Term}
    (accepted : check theory witness claimed = true) : Spec.DerivesV2 theory claimed :=
  ((check_iff _ _ _).mp accepted).derives

/-- The old proof remains the same supplied certificate; no proof search or
replacement theorem is used when embedding it. -/
theorem base_result (theory : Spec.Theory) (original : ProofWitness) :
    result theory (.base original) = original.result theory := rfl

theorem base_check (theory : Spec.Theory) (original : ProofWitness) (claimed : Spec.Term) :
    check theory (.base original) claimed = original.check theory claimed := rfl

end Witness

theorem certificate_exists {theory : Spec.Theory} {allocated : Nat} (hosted : Hosted theory allocated)
    {statement : Spec.Term} (derived : Spec.DerivesV2 theory statement) :
    ∃ witness, Witness.Checks theory witness statement := by
  generalize empty : ([] : List Spec.ExecutionObservation) = observations at derived
  induction derived with
  | base original =>
      subst observations
      obtain ⟨originalWitness, checked⟩ := ComputationalProofs.certificate_exists hosted
        (Spec.execution_free_derives_static original)
      exact ⟨.base originalWitness, .base checked⟩
  | modusPonens _ _ implicationIH premiseIH =>
      obtain ⟨implication, checkedImplication⟩ := implicationIH
      obtain ⟨premise, checkedPremise⟩ := premiseIH
      exact ⟨.modusPonens implication premise, .modusPonens checkedImplication checkedPremise⟩
  | instantiateMany _ formed instantiated childIH =>
      obtain ⟨child, checkedChild⟩ := childIH
      exact ⟨.instantiateMany _ child, .instantiateMany checkedChild formed instantiated⟩
  | jit _ member _ _ => simp at member

theorem derives_iff_checked {theory : Spec.Theory} {allocated : Nat} (hosted : Hosted theory allocated)
    (statement : Spec.Term) :
    Spec.DerivesV2 theory statement ↔ ∃ witness, Witness.check theory witness statement = true := by
  constructor
  · intro derived
    obtain ⟨witness, checked⟩ := certificate_exists hosted derived
    exact ⟨witness, (Witness.check_iff _ _ _).mpr checked⟩
  · rintro ⟨witness, checked⟩
    exact Witness.check_sound checked

#print axioms Witness.check_sound
#print axioms certificate_exists

end Mettapedia.Languages.VibeITP.Presentation.SimultaneousProofs
