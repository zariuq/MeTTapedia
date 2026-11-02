import Mettapedia.Machines.AddressedOccurrencePaths
import Mettapedia.Machines.BranchLocalNeed.LocalStepPaths

/-!
# Need branch addresses separate actual successor occurrences

Only suspended-producer selection branches; its occurrence position is
appended to the world path. Silent local transitions and other protocol steps
preserve or extend that path. Distinct branches therefore cannot later share
one completed address.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.BranchLocalNeed.NeedAddressedPaths

open NeedReference

variable {O L R U V F N E : Type}

theorem branch_index_path
    (machine : Machine O L R U V F N E) (base : World O U V F N E)
    (cell : CellId) (record : CellRecord O V F) (owner : EvaluatorId) (stack : List (Frame R))
    (alternatives : List (U × L)) (start index : Nat) (next : Machine O L R U V F N E)
    (selected : (branchAlternatives machine base cell record owner stack start alternatives)[index]? = some next) :
    next.world.path = base.path ++ [start + index] := by
  induction alternatives generalizing start index with
  | nil => simp [branchAlternatives] at selected
  | cons head tail ih =>
      cases index with
      | zero =>
          simp only [branchAlternatives, List.getElem?_cons_zero, Option.some.injEq] at selected
          subst next
          simp [finished, recorded, World.record, World.setKnownCache, World.fork]
      | succ index =>
          simp only [branchAlternatives, List.getElem?_cons_succ] at selected
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (start + 1) index selected

theorem reference_shape (spec : Spec O L R U V F N E) (machine : Machine O L R U V F N E) :
    (step spec machine).length ≤ 1 ∨
      ∀ (index : Nat) (next : Machine O L R U V F N E), (step spec machine)[index]? = some next →
        next.world.path = machine.world.path ++ [index] := by
  let single : Spec O L R U V F N E := { spec with alternatives := fun _ => [] }
  have small := step_length_le single 1 (Nat.le_refl _) (by intro origin; exact Nat.zero_le _) machine
  cases control : machine.control with
  | run state stack =>
      exact Or.inl (by simpa only [step, control, single] using small)
  | returned result stack =>
      exact Or.inl (by simpa only [step, control, single] using small)
  | halted result => exact Or.inl (by simp [step, control])
  | force cell stack =>
      cases found : machine.world.heap.lookup cell with
      | none => exact Or.inl (by simp [step, control, found])
      | some record =>
          cases cache : record.cache with
          | value value => exact Or.inl (by simp [step, control, found, cache])
          | stableFault fault => exact Or.inl (by simp [step, control, found, cache])
          | evaluating owner => exact Or.inl (by simp [step, control, found, cache])
          | suspended =>
              cases rules : spec.alternatives record.origin with
              | nil => exact Or.inl (by simp [step, control, found, cache, rules])
              | cons head tail =>
                  right
                  intro index next selected
                  simp only [step, control, found, cache, rules] at selected
                  simpa using branch_index_path machine _ cell record machine.world.nextEvaluator stack
                    (head :: tail) 0 index next selected

theorem local_shape (extension : NeedLocalSteps.Extension O L R U V F N E)
    (machine : Machine O L R U V F N E) :
    (NeedLocalSteps.step extension machine).length ≤ 1 ∨
      ∀ (index : Nat) (next : Machine O L R U V F N E),
        (NeedLocalSteps.step extension machine)[index]? = some next →
          next.world.path = machine.world.path ++ [index] := by
  cases control : machine.control with
  | run state stack =>
      cases localStep : extension.localStep state with
      | some next => exact Or.inl (by simp [NeedLocalSteps.step, control, localStep])
      | none => simpa only [NeedLocalSteps.step, control, localStep] using reference_shape extension.reference machine
  | force cell stack => simpa only [NeedLocalSteps.step, control] using reference_shape extension.reference machine
  | returned result stack => simpa only [NeedLocalSteps.step, control] using reference_shape extension.reference machine
  | halted result => simpa only [NeedLocalSteps.step, control] using reference_shape extension.reference machine

theorem local_grows (extension : NeedLocalSteps.Extension O L R U V F N E)
    (before next : Machine O L R U V F N E) (selected : next ∈ NeedLocalSteps.step extension before) :
    before.world.path <+: next.world.path := by
  have referenceCase (selected : next ∈ step extension.reference before) : before.world.path <+: next.world.path := by
    obtain ⟨suffix, equation⟩ := NeedCacheLaws.step_path_extends extension.reference before next selected
    exact ⟨suffix, equation.symm⟩
  cases control : before.control with
  | run state stack =>
      cases localStep : extension.localStep state with
      | none => exact referenceCase (by simpa only [NeedLocalSteps.step, control, localStep] using selected)
      | some successor =>
          simp only [NeedLocalSteps.step, control, localStep, List.mem_singleton] at selected
          subst next
          exact ⟨[], List.append_nil _⟩
  | force cell stack => exact referenceCase (by simpa only [NeedLocalSteps.step, control] using selected)
  | returned result stack => exact referenceCase (by simpa only [NeedLocalSteps.step, control] using selected)
  | halted result => exact referenceCase (by simpa only [NeedLocalSteps.step, control] using selected)

theorem common_extension_index (prefix common : List Nat) (i j : Nat)
    (left : prefix ++ [i] <+: common) (right : prefix ++ [j] <+: common) : i = j := by
  obtain ⟨suffix, left⟩ := left
  obtain ⟨tail, right⟩ := right
  have same : prefix ++ (i :: suffix) = prefix ++ (j :: tail) := by
    simpa only [List.append_assoc, List.singleton_append] using left.trans right.symm
  exact (List.cons.inj (List.append_left_cancel same)).1

theorem laws (extension : NeedLocalSteps.Extension O L R U V F N E)
    (initial : Machine O L R U V F N E) :
    AddressedOccurrencePaths.Laws (NeedLocalSteps.pathMachine extension initial) (fun state => state.world.path) where
  grows before next index selected := local_grows extension before next (List.mem_of_getElem? selected)
  separated before left right i j common leftAt rightAt leftPrefix rightPrefix := by
    rcases local_shape extension before with small | branching
    · obtain ⟨leftBound, _⟩ := List.getElem?_eq_some_iff.mp leftAt
      obtain ⟨rightBound, _⟩ := List.getElem?_eq_some_iff.mp rightAt
      change i < (NeedLocalSteps.step extension before).length at leftBound
      change j < (NeedLocalSteps.step extension before).length at rightBound
      omega
    · rw [branching i left leftAt] at leftPrefix
      rw [branching j right rightAt] at rightPrefix
      exact common_extension_index before.world.path common i j leftPrefix rightPrefix

end Mettapedia.Machines.BranchLocalNeed.NeedAddressedPaths
