import Mettapedia.Languages.OCaml.MachineCorrectness

/-! A successful completed-observation check produces an evaluation proof.
Pending and malformed runs cannot pass; fault observations remain distinct
from ordinary returned values.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.OCaml

deriving instance ReflBEq, LawfulBEq for Literal
deriving instance ReflBEq, LawfulBEq for FunctionRef
deriving instance ReflBEq, LawfulBEq for Fault

mutual
  def valueEqual : Value → Value → Bool
    | .literal first, .literal second => decide (first = second)
    | .tuple first, .tuple second => valuesEqual first second
    | .cons first tail, .cons second rest => valueEqual first second && valueEqual tail rest
    | .variant firstType firstTag first, .variant secondType secondTag second =>
        decide (firstType = secondType) && decide (firstTag = secondTag) && valuesEqual first second
    | .closure firstFunction first, .closure secondFunction second =>
        decide (firstFunction = secondFunction) && valuesEqual first second
    | _, _ => false

  def valuesEqual : List Value → List Value → Bool
    | [], [] => true
    | first :: rest, second :: tail => valueEqual first second && valuesEqual rest tail
    | _, _ => false
end

theorem valueEqual_iff (first : Value) : ∀ second, valueEqual first second = true ↔ first = second := by
  refine Value.rec
    (motive_1 := fun first => ∀ second, valueEqual first second = true ↔ first = second)
    (motive_2 := fun first => ∀ second, valuesEqual first second = true ↔ first = second)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ first
  · intro literal second
    cases second <;> simp [valueEqual]
  · intro fields ih second
    cases second <;> simp_all [valueEqual]
  · intro head tail headIH tailIH second
    cases second <;> simp_all [valueEqual]
  · intro typeId constructor fields ih second
    cases second <;> simp_all [valueEqual, and_assoc]
  · intro function captured ih second
    cases second <;> simp_all [valueEqual]
  · intro second
    cases second <;> simp [valuesEqual]
  · intro head tail headIH tailIH second
    cases second <;> simp_all [valuesEqual]

def resultEqual (first second : Result) : Bool := match first, second with
  | .ok first, .ok second => valueEqual first second
  | .error first, .error second => decide (first = second)
  | _, _ => false

theorem resultEqual_iff (first second : Result) : resultEqual first second = true ↔ first = second := by
  cases first <;> cases second <;> simp [resultEqual, valueEqual_iff]

def observes (program : Program) (budget : Nat) (expected : Result) : Bool :=
  match run program budget (begin program) with
  | .complete actual => resultEqual actual expected
  | .pending _ | .invalid _ => false

theorem observes_iff (program : Program) (budget : Nat) (expected : Result) :
    observes program budget expected = true ↔ run program budget (begin program) = .complete expected := by
  unfold observes
  cases outcome : run program budget (begin program) with
  | complete actual => simp only [resultEqual_iff, RunResult.complete.injEq]
  | pending state => simp
  | invalid error => simp

theorem observes_sound {program : Program} {budget : Nat} {expected : Result}
    (accepted : observes program budget expected = true) : Evaluates program [] program.entry expected :=
  run_sound ((observes_iff program budget expected).mp accepted)

structure ObservationWitness (program : Program) (expected : Result) : Type where
  evaluated : Evaluates program [] program.entry expected

def checkedObservation (program : Program) (budget : Nat) (expected : Result) :
    Option (ObservationWitness program expected) :=
  if accepted : observes program budget expected = true then some ⟨observes_sound accepted⟩ else none

theorem checkedObservation_iff (program : Program) (budget : Nat) (expected : Result) :
    (checkedObservation program budget expected).isSome = true ↔
      run program budget (begin program) = .complete expected := by
  unfold checkedObservation
  split
  · rename_i accepted
    exact ⟨fun _ => (observes_iff program budget expected).mp accepted, fun _ => rfl⟩
  · rename_i refused
    constructor
    · intro impossible
      cases impossible
    · intro completed
      exact (refused ((observes_iff program budget expected).mpr completed)).elim

#print axioms observes_sound
#print axioms checkedObservation_iff

end Mettapedia.Languages.OCaml
