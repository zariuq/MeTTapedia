import Mettapedia.Logic.FundedHMLMaximalObservations

/-!
# Earned finite codes for actual funded modal observations

A complete paid readout reveals its Boolean and exact instruction price.
An exhausted unfinished readout reveals neither, and has spent its whole
purse. These codes are independent of the executor. The comparison below
earns their equality kernel from actual public answers and spending.

The finite carrier is a code space, not a claim that every code is realised
by every supplied transition presentation or test. Observations execute
the supplied emitted program before their class is proved.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ModalMuCalculus.StackInspection.BudgetObservation

open Inspection Funded

universe u v

abbrev Code (budget : Nat) := Option (Bool × Fin (budget + 1))

def classify (budget : Nat) (row : Bool × Nat) : Code budget :=
  if affordable : row.2 ≤ budget then some (row.1, ⟨row.2, by omega⟩) else none

def meaning (budget : Nat) : Code budget → Option Bool × Nat
  | none => (none, budget)
  | some (answer, price) => (some answer, price.val)

theorem meaning_injective (budget : Nat) : Function.Injective (meaning budget) := by
  intro first second same
  cases first with
  | none =>
      cases second with
      | none => rfl
      | some pair =>
          have answer := congrArg Prod.fst same
          cases answer
  | some before =>
      cases second with
      | none =>
          have answer := congrArg Prod.fst same
          cases answer
      | some after =>
          have answer := Option.some.inj (congrArg Prod.fst same)
          have price := Fin.ext (congrArg Prod.snd same)
          exact congrArg some (Prod.ext answer price)

theorem meaning_classifies (budget : Nat) (row : Bool × Nat) :
    meaning budget (classify budget row) =
      (if row.2 ≤ budget then some row.1 else none, min budget row.2) := by
  by_cases affordable : row.2 ≤ budget
  · simp only [classify, dif_pos affordable, meaning, if_pos affordable,
      Nat.min_eq_right affordable]
  · simp only [classify, dif_neg affordable, meaning, if_neg affordable,
      Nat.min_eq_left (by omega : budget ≤ row.2)]

def restrict {small large : Nat} (_included : small ≤ large) : Code large → Code small
  | none => none
  | some (answer, price) =>
      if affordable : price.val ≤ small then some (answer, ⟨price.val, by omega⟩) else none

theorem restrict_classifies {small large : Nat} (included : small ≤ large) (row : Bool × Nat) :
    restrict included (classify large row) = classify small row := by
  by_cases affordable : row.2 ≤ small
  · have larger : row.2 ≤ large := affordable.trans included
    simp only [classify, dif_pos larger, restrict, dif_pos affordable]
  · by_cases larger : row.2 ≤ large
    · simp only [classify, dif_pos larger, restrict, dif_neg affordable]
    · simp only [classify, dif_neg larger, restrict, dif_neg affordable]

theorem restrict_identity (budget : Nat) (code : Code budget) :
    restrict (le_refl budget) code = code := by
  cases code with
  | none => rfl
  | some pair =>
      have affordable : pair.2.val ≤ budget := by omega
      simp only [restrict, dif_pos affordable]

theorem restrict_composition {small middle large : Nat}
    (first : small ≤ middle) (second : middle ≤ large) (code : Code large) :
    restrict first (restrict second code) = restrict (first.trans second) code := by
  cases code with
  | none => rfl
  | some pair =>
      by_cases affordable : pair.2.val ≤ small
      · have intermediary : pair.2.val ≤ middle := affordable.trans first
        simp only [restrict, dif_pos intermediary, dif_pos affordable]
      · by_cases intermediary : pair.2.val ≤ middle
        · simp only [restrict, dif_pos intermediary, dif_neg affordable]
        · simp only [restrict, dif_neg intermediary, dif_neg affordable]

structure Question (Action : Type v) (n : Nat) where
  formula : Formula Action n
  admitted : formula.isHML = true

variable {State : Type u} {Action : Type v} {n : Nat}

/-- Execute the actual compiled program; classification is not used in
this definition of the observation. -/
def observation (presentation : SuccessorPresentation State Action)
    (environment : BooleanEnv State n) (budget : Nat) (question : Question Action n)
    (state : State) : Option Bool × Nat :=
  let actual := attempt presentation question.formula question.admitted environment state [] budget
  (publicAnswer actual.endpoint, actual.endpoint.spent)

def row (presentation : SuccessorPresentation State Action)
    (environment : BooleanEnv State n) (question : Question Action n) (state : State) : Bool × Nat :=
  inspect presentation question.formula question.admitted environment state

theorem observation_classified (presentation : SuccessorPresentation State Action)
    (environment : BooleanEnv State n) (budget : Nat) (question : Question Action n)
    (state : State) :
    observation presentation environment budget question state =
      meaning budget (classify budget (row presentation environment question state)) := by
  rw [meaning_classifies]
  exact Prod.ext
    (attempt_answer presentation question.formula question.admitted environment state [] budget)
    (attempt_spent presentation question.formula question.admitted environment state [] budget)

theorem observation_equality_iff (presentation : SuccessorPresentation State Action)
    (environment : BooleanEnv State n) (budget : Nat) (question : Question Action n)
    (first second : State) :
    observation presentation environment budget question first =
      observation presentation environment budget question second ↔
    classify budget (row presentation environment question first) =
      classify budget (row presentation environment question second) := by
  rw [observation_classified, observation_classified]
  exact (meaning_injective budget).eq_iff

theorem maximal_prefix_observation (presentation : SuccessorPresentation State Action)
    (environment : BooleanEnv State n) (budget : Nat) (question : Question Action n)
    (state : State) (stack : List Bool)
    (receipt : Prefix presentation question.formula question.admitted environment state stack budget)
    (maximal : Maximal environment receipt.endpoint) :
    (publicAnswer receipt.endpoint, receipt.endpoint.spent) =
      observation presentation environment budget question state := by
  rw [observation_classified, meaning_classifies]
  exact Prod.ext
    (receipt.maximal_answer presentation question.formula question.admitted environment state stack budget maximal)
    (receipt.maximal_spent presentation question.formula question.admitted environment state stack budget maximal)

end Mettapedia.Logic.ModalMuCalculus.StackInspection.BudgetObservation
