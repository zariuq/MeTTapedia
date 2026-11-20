import Mettapedia.ProbabilityTheory.StochasticInference.Binary

/-!
# Executable interventions on ordered binary mechanisms

Each variable has one conditional table and all parents precede the
variable. An intervention replaces that variable's table by a point
mass. Evidence can be supplied to the resulting model as usual.
-/

set_option autoImplicit false

namespace Mettapedia.ProbabilityTheory.StochasticInference.Interventions

open Mettapedia.ProbabilityTheory.BayesianNetworks.ExecutableFactorTable (Config)

variable {n : Nat}

structure Mechanism (child : Fin n) where
  parents : List (Fin n)
  distinct : parents.Nodup
  earlier : ∀ parent ∈ parents, parent < child
  probability : LocalConfig (BinaryDomains n) parents → UnitProbability

private theorem child_absent {child : Fin n} (mechanism : Mechanism child) :
    child ∉ mechanism.parents := fun member => (lt_irrefl _ (mechanism.earlier child member))

def Mechanism.factor {child : Fin n} (mechanism : Mechanism child) : Potential (BinaryDomains n) :=
  Potential.onScope (binaryPositive n) (child :: mechanism.parents)
    (List.nodup_cons.mpr ⟨child_absent mechanism, mechanism.distinct⟩)
    (fun values =>
      (mechanism.probability (fun i member => values i (List.mem_cons_of_mem _ member))).atOutcome
        (decide ((values child List.mem_cons_self).val = 1)))
    (fun _ => UnitProbability.atOutcome_nonneg _ _)

theorem Mechanism.factor_value {child : Fin n} (mechanism : Mechanism child)
    (x : Config (BinaryDomains n)) :
    mechanism.factor.table.value _ (binaryPositive n) x =
      (mechanism.probability (fun i _ => x i)).atOutcome (bits x child) :=
  tableOnScope_value _ _ _ _ _

def Mechanism.after {child : Fin n} (mechanism : Mechanism child) (setting : Option Bool) :
    Potential (BinaryDomains n) :=
  setting.elim mechanism.factor (fun b => (binaryEvent child b).asPotential)

theorem Mechanism.after_value {child : Fin n} (mechanism : Mechanism child) (setting : Option Bool)
    (x : Config (BinaryDomains n)) :
    (mechanism.after setting).table.value _ (binaryPositive n) x =
      match setting with
      | none => (mechanism.probability (fun i _ => x i)).atOutcome (bits x child)
      | some chosen => if bits x child = chosen then 1 else 0 := by
  cases setting with
  | none => exact mechanism.factor_value x
  | some chosen =>
    change (binaryEvent child chosen).value (binaryPositive n) x = _
    unfold Event.value binaryEvent Event.equalTo Event.onScope
    rw [tableOnScope_value]
    simp only [bits, bitValue]
    have values : (x child).val = 0 ∨ (x child).val = 1 := by
      have bound : (x child).val < 2 := (x child).isLt
      omega
    rcases values with zero | one
    · cases chosen <;> simp [Fin.ext_iff, zero]
    · cases chosen <;> simp [Fin.ext_iff, one]

def model (mechanisms : ∀ child, Mechanism (n := n) child) (setting : Fin n → Option Bool)
    (Id : Type*) : State Id (BinaryDomains n) :=
  .initial ((List.finRange n).map fun child => (mechanisms child).after (setting child))

theorem model_truncated (mechanisms : ∀ child, Mechanism (n := n) child)
    (setting : Fin n → Option Bool) (Id : Type*) (x : Config (BinaryDomains n)) :
    (model mechanisms setting Id).unnormalized (binaryPositive n) x =
      ((List.finRange n).map fun child =>
        match setting child with
        | none => ((mechanisms child).probability (fun i _ => x i)).atOutcome (bits x child)
        | some chosen => if bits x child = chosen then 1 else 0).prod := by
  simp [model, State.initial, State.unnormalized, State.tables, State.factors, EvidenceLedger.active,
    EvidenceLedger.empty, worldWeight, List.map_map, Function.comp_def, Mechanism.after_value]

end Mettapedia.ProbabilityTheory.StochasticInference.Interventions
