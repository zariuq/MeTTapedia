import Mettapedia.Machines.InformationFlow.FloatingLabel

/-!
# Static flow checking and erasure of monitor checks

The target evaluator is defined independently and has no current label and no
write/output flow checks. A syntax-directed security judgment proves that it
agrees with the monitored evaluator. Read effects are conservatively joined
across sequential and conditional commands. This is a finite first-order
fragment, not a static analysis of arbitrary reflective MeTTa code.

The theorem removes checks, not physical timing channels. Output destinations
remain in the mathematical trace so the same observers can be compared.
-/

namespace Mettapedia.Machines.InformationFlow.FloatingLabel

universe u

structure RawState (Label : Type u) where
  register : List Nat
  store : Nat → List Nat
  trace : List (Label × List Nat)

def erase {Label : Type u} (s : State Label) : RawState Label :=
  ⟨s.register, s.store, s.trace⟩

def uncheckedStep {Label : Type u} : Primitive Label → RawState Label → RawState Label
  | .literal value, s => { s with register := value }
  | .query space predicate, s => { s with register := (s.store space).filter predicate }
  | .count, s => { s with register := [s.register.length] }
  | .write space, s => { s with store := Function.update s.store space s.register }
  | .emit destination, s => { s with trace := s.trace ++ [(destination, s.register)] }

def uncheckedRun {Label : Type u} : Command Label → RawState Label → RawState Label
  | .skip, s => s
  | .primitive operation, s => uncheckedStep operation s
  | .seq first second, s => uncheckedRun second (uncheckedRun first s)
  | .ifEmpty yes no, s =>
      if s.register.isEmpty then uncheckedRun yes s else uncheckedRun no s

variable {Label : Type u} [SemilatticeSup Label] [OrderBot Label] [DecidableLE Label]

def primitiveReadLabel (spaceLabel : Nat → Label) : Primitive Label → Label
  | .query space _ => spaceLabel space
  | _ => ⊥

def readLabel (spaceLabel : Nat → Label) : Command Label → Label
  | .skip => ⊥
  | .primitive operation => primitiveReadLabel spaceLabel operation
  | .seq first second => readLabel spaceLabel first ⊔ readLabel spaceLabel second
  | .ifEmpty yes no => readLabel spaceLabel yes ⊔ readLabel spaceLabel no

inductive Admissible (spaceLabel : Nat → Label) (bound : Label) : Primitive Label → Prop
  | literal (value) : Admissible spaceLabel bound (.literal value)
  | query (space predicate) : Admissible spaceLabel bound (.query space predicate)
  | count : Admissible spaceLabel bound .count
  | write (space) (flows : bound ≤ spaceLabel space) : Admissible spaceLabel bound (.write space)
  | emit (destination) (flows : bound ≤ destination) : Admissible spaceLabel bound (.emit destination)

inductive WellTyped (spaceLabel : Nat → Label) : Label → Command Label → Prop
  | skip (bound) : WellTyped spaceLabel bound .skip
  | primitive (bound operation) (allowed : Admissible spaceLabel bound operation) :
      WellTyped spaceLabel bound (.primitive operation)
  | seq (bound first second)
      (firstTyped : WellTyped spaceLabel bound first)
      (secondTyped : WellTyped spaceLabel (bound ⊔ readLabel spaceLabel first) second) :
      WellTyped spaceLabel bound (.seq first second)
  | ifEmpty (bound yes no)
      (yesTyped : WellTyped spaceLabel bound yes)
      (noTyped : WellTyped spaceLabel bound no) :
      WellTyped spaceLabel bound (.ifEmpty yes no)

theorem step_current_eq (spaceLabel : Nat → Label) (operation : Primitive Label)
    (s : State Label) :
    (step spaceLabel operation s).current = s.current ⊔ primitiveReadLabel spaceLabel operation := by
  cases operation <;> simp [step, primitiveReadLabel]
  all_goals split <;> simp

theorem run_current_bound (spaceLabel : Nat → Label) (command : Command Label)
    (s : State Label) :
    (run spaceLabel command s).current ≤ s.current ⊔ readLabel spaceLabel command := by
  induction command generalizing s with
  | skip => simp [run, readLabel]
  | primitive operation => exact le_of_eq (step_current_eq _ _ _)
  | seq first second ihFirst ihSecond =>
      exact (ihSecond _).trans (by
        simpa only [readLabel, sup_assoc] using
          sup_le_sup_right (ihFirst s) (readLabel spaceLabel second))
  | ifEmpty yes no ihYes ihNo =>
      simp only [run]
      split
      · exact (ihYes s).trans (sup_le_sup_left le_sup_left _)
      · exact (ihNo s).trans (sup_le_sup_left le_sup_right _)

omit [OrderBot Label] in
theorem step_check_erasure {spaceLabel : Nat → Label} {operation : Primitive Label}
    {bound : Label} (allowed : Admissible spaceLabel bound operation)
    (s : State Label) (within : s.current ≤ bound) :
    erase (step spaceLabel operation s) = uncheckedStep operation (erase s) := by
  cases allowed with
  | literal => rfl
  | query => rfl
  | count => rfl
  | write space flows => simp [step, uncheckedStep, erase, within.trans flows]
  | emit destination flows => simp [step, uncheckedStep, erase, within.trans flows]

/-- Removing dynamic flow checks preserves the register, every space, and the
full destination-tagged output trace for statically checked commands. -/
theorem run_check_erasure {spaceLabel : Nat → Label} {command : Command Label}
    {bound : Label} (typed : WellTyped spaceLabel bound command)
    (s : State Label) (within : s.current ≤ bound) :
    erase (run spaceLabel command s) = uncheckedRun command (erase s) := by
  induction typed generalizing s with
  | skip => rfl
  | primitive bound operation allowed => exact step_check_erasure allowed s within
  | seq bound first second firstTyped secondTyped ihFirst ihSecond =>
      have nextBound : (run spaceLabel first s).current ≤ bound ⊔ readLabel spaceLabel first :=
        (run_current_bound _ _ _).trans (sup_le_sup_right within _)
      simp only [run, uncheckedRun]
      rw [ihSecond _ nextBound, ihFirst s within]
  | ifEmpty bound yes no yesTyped noTyped ihYes ihNo =>
      by_cases hEmpty : s.register.isEmpty = true
      · simpa [run, uncheckedRun, erase, hEmpty] using ihYes s within
      · simpa [run, uncheckedRun, erase, hEmpty] using ihNo s within

omit [DecidableLE Label] in
theorem readLabel_bottom (command : Command Label) :
    readLabel (fun _ => (⊥ : Label)) command = ⊥ := by
  induction command with
  | skip => rfl
  | primitive operation => cases operation <;> rfl
  | seq first second ihFirst ihSecond => simp [readLabel, ihFirst, ihSecond]
  | ifEmpty yes no ihYes ihNo => simp [readLabel, ihYes, ihNo]

omit [DecidableLE Label] in
theorem all_public_wellTyped (command : Command Label) :
    WellTyped (fun _ => (⊥ : Label)) ⊥ command := by
  induction command with
  | skip => exact .skip _
  | primitive operation =>
      apply WellTyped.primitive
      cases operation with
      | literal value => exact .literal _
      | query space predicate => exact .query _ _
      | count => exact .count
      | write space => exact .write _ le_rfl
      | emit destination => exact .emit _ bot_le
  | seq first second ihFirst ihSecond =>
      exact .seq _ _ _ ihFirst (by simpa [readLabel_bottom] using ihSecond)
  | ifEmpty yes no ihYes ihNo => exact .ifEmpty _ _ _ ihYes ihNo

/-- The all-public instance agrees with the independently defined unmonitored
semantics on all finite commands, including mutation and conditional execution. -/
theorem all_public_conservativity (command : Command Label) (s : State Label)
    (atBottom : s.current = ⊥) :
    erase (run (fun _ => (⊥ : Label)) command s) = uncheckedRun command (erase s) :=
  run_check_erasure (all_public_wellTyped command) s (by simp [atBottom])

end Mettapedia.Machines.InformationFlow.FloatingLabel
