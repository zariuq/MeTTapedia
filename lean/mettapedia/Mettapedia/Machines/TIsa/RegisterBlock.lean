import Mettapedia.Machines.TIsa.Continuation
import Mettapedia.Machines.TIsa.RegisterProfile
import Mathlib.Data.List.Nodup

/-!
# Ordered RegisterCode blocks compiled to continuation resources

Source instructions retain RegisterCode's executor. The target is a finite
list of ordinary guarded transform recipes; execution is the existing GSLT
rewrite relation. No additional program interpreter is introduced.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.RegisterBlock

open Cells CellEffects RegisterProfile Control

def state (activation : Nat) (point : Word) (values : Nat → Word) : Location Nat → Word
  | .inl name => if name = activation then point else 0
  | .inr register => values register

def edge (activation point : Nat) (write : Write) : Edge Nat :=
  ⟨activation, BitVec.ofNat 64 point, BitVec.ofNat 64 (point + 1), write.recipe⟩

def lower (activation : Nat) : Nat → List Write → List (Edge Nat)
  | _, [] => []
  | point, write :: later => edge activation point write :: lower activation (point + 1) later

theorem lower_length (activation point : Nat) (writes : List Write) :
    (lower activation point writes).length = writes.length := by
  induction writes generalizing point with
  | nil => rfl
  | cons write later ih => simp [lower, ih]

theorem lower_member (activation point : Nat) (writes : List Write) (entry : Edge Nat)
    (member : entry ∈ lower activation point writes) :
    entry.activation = activation ∧ ∃ offset < writes.length,
      entry.point = BitVec.ofNat 64 (point + offset) := by
  induction writes generalizing point with
  | nil => cases member
  | cons write later ih =>
      simp only [lower, List.mem_cons] at member
      rcases member with rfl | member
      · exact ⟨rfl, 0, by simp, by simp [edge]⟩
      · obtain ⟨owned, offset, bound, same⟩ := ih (point + 1) member
        exact ⟨owned, offset + 1, by simp; omega,
          by rw [same]; congr 1; omega⟩

theorem word_index_injective (left right : Nat) (leftBound : left < 2 ^ 64) (rightBound : right < 2 ^ 64)
    (same : BitVec.ofNat 64 left = BitVec.ofNat 64 right) : left = right := by
  have equal := congrArg BitVec.toNat same
  simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt leftBound, Nat.mod_eq_of_lt rightBound] using equal

theorem lower_unique (activation point : Nat) (writes : List Write)
    (bounded : point + writes.length < 2 ^ 64) :
    ((lower activation point writes).map Edge.point).Nodup := by
  induction writes generalizing point with
  | nil => simp [lower]
  | cons write later ih =>
      simp only [lower, List.map_cons, List.nodup_cons]
      refine ⟨?_, ih (point + 1) (by simp only [List.length_cons] at bounded; omega)⟩
      intro member
      obtain ⟨entry, inTail, same⟩ := List.mem_map.mp member
      obtain ⟨_, offset, within, pointEqual⟩ := lower_member activation (point + 1) later entry inTail
      have equal : point + 1 + offset = point := word_index_injective _ _
        (by simp only [List.length_cons] at bounded; omega)
        (by simp only [List.length_cons] at bounded; omega)
        (pointEqual.symm.trans same)
      omega

theorem lower_terminal_absent (activation point : Nat) (writes : List Write)
    (bounded : point + writes.length < 2 ^ 64) :
    BitVec.ofNat 64 (point + writes.length) ∉ (lower activation point writes).map Edge.point := by
  intro member
  obtain ⟨entry, source, same⟩ := List.mem_map.mp member
  obtain ⟨_, offset, within, pointEqual⟩ := lower_member activation point writes entry source
  have equal := word_index_injective (point + offset) (point + writes.length)
    (by omega) bounded (pointEqual.symm.trans same)
  omega

theorem edge_guard (activation point : Nat) (write : Write) (before : Nat → Word) (result : Word)
    (computed : write.operation.evaluate (write.arguments.map (operandValue before)) = some result) :
    (edge activation point write).recipe.guard
      ((edge activation point write).recipe.inputs.map (state activation (BitVec.ofNat 64 point) before))
      ((edge activation point write).recipe.outputs.map
        (state activation (BitVec.ofNat 64 (point + 1)) (Function.update before write.destination result))) = true := by
  apply (Edge.guard_iff _ _ _).mpr
  refine ⟨by simp [edge, state], by simp [edge, state], ?_⟩
  change write.recipe.guard (write.recipe.inputs.map before)
    (write.recipe.outputs.map (Function.update before write.destination result)) = true
  apply (write.guard_iff _ _).mpr
  simpa using computed

theorem edge_finish (activation point : Nat) (write : Write) (before : Nat → Word) (result : Word) :
    (edge activation point write).finish (state activation (BitVec.ofNat 64 point) before)
      (state activation (BitVec.ofNat 64 (point + 1)) (Function.update before write.destination result)) =
      state activation (BitVec.ofNat 64 (point + 1)) (Function.update before write.destination result) := by
  funext location
  cases location with
  | inl name => by_cases same : name = activation <;> simp [Edge.finish, edge, state, same]
  | inr register =>
      change overwrite write.recipe.writes before (Function.update before write.destination result) register = _
      rw [write.overwrite_eq]
      simp [state]

theorem edge_finish_any (activation point : Nat) (write : Write) (before : Nat → Word)
    (after : Location Nat → Word) :
    (edge activation point write).finish (state activation (BitVec.ofNat 64 point) before) after =
      state activation (BitVec.ofNat 64 (point + 1))
        (Function.update before write.destination (after (.inr write.destination))) := by
  funext location
  cases location with
  | inl name => by_cases same : name = activation <;> simp [Edge.finish, edge, state, same]
  | inr register =>
      change overwrite write.recipe.writes before (fun key => after (.inr key)) register = _
      rw [write.overwrite_eq]
      rfl

theorem unique_point (whole : List (Edge Nat)) (unique : (whole.map Edge.point).Nodup)
    (left right : Edge Nat) (leftMember : left ∈ whole) (rightMember : right ∈ whole)
    (same : left.point = right.point) : left = right := by
  obtain ⟨leftIndex, rfl⟩ := List.mem_iff_get.mp leftMember
  obtain ⟨rightIndex, rfl⟩ := List.mem_iff_get.mp rightMember
  have equal : (whole.map Edge.point)[leftIndex.val]'(by simp) =
      (whole.map Edge.point)[rightIndex.val]'(by simp) := by simpa using same
  have indices : leftIndex = rightIndex := Fin.ext (unique.getElem_inj_iff.mp equal)
  cases indices
  rfl

/-- No other source row or arithmetic answer can be invented at this point. -/
theorem head_step_iff (activation point : Nat) (write : Write) (whole : List (Edge Nat))
    (keys : Finset (Location Nat)) (before : Nat → Word) (result : Multiset (Cell (Location Nat)))
    (member : edge activation point write ∈ whole)
    (unique : (whole.map Edge.point).Nodup)
    (owned : ∀ entry ∈ whole, entry.activation = activation)
    (inScope : (edge activation point write).recipe.support ⊆ keys) :
    (edgeProgram whole).theory.rewrites (encode keys (state activation (BitVec.ofNat 64 point) before)) result ↔
      ∃ value : Word,
        write.operation.evaluate (write.arguments.map (operandValue before)) = some value ∧
        result = encode keys (state activation (BitVec.ofNat 64 (point + 1))
          (Function.update before write.destination value)) := by
  rw [edgeProgram_rewrite_iff]
  constructor
  · rintro ⟨entry, entryMember, after, _, current, _, guarded, endpoint⟩
    have pointEqual : entry.point = (edge activation point write).point := by
      simpa [state, edge, owned entry entryMember] using current.symm
    have equal := unique_point whole unique entry (edge activation point write) entryMember member pointEqual
    subst entry
    have computed : write.operation.evaluate (write.arguments.map (operandValue before)) =
        some (after (.inr write.destination)) := (write.guard_iff before (fun key => after (.inr key))).mp guarded
    exact ⟨after (.inr write.destination), computed,
      by rw [endpoint, edge_finish_any]⟩
  · rintro ⟨value, computed, rfl⟩
    let after := state activation (BitVec.ofNat 64 (point + 1)) (Function.update before write.destination value)
    have guarded := (Edge.guard_iff _ _ _).mp (edge_guard activation point write before value computed)
    exact ⟨edge activation point write, member, after, inScope,
      guarded.1, guarded.2.1, guarded.2.2, congrArg (encode keys)
        (edge_finish activation point write before value).symm⟩

/-- Every successful scalar block is realized by its actual finite target program. -/
theorem run_realized (activation point : Nat) (writes : List Write) (whole : List (Edge Nat))
    (keys : Finset (Location Nat)) (before after : Nat → Word)
    (contained : ∀ entry ∈ lower activation point writes, entry ∈ whole)
    (inScope : ∀ entry ∈ whole, entry.recipe.support ⊆ keys)
    (run : runWrites writes before = some after) :
    Relation.ReflTransGen (edgeProgram whole).theory.rewrites
      (encode keys (state activation (BitVec.ofNat 64 point) before))
      (encode keys (state activation (BitVec.ofNat 64 (point + writes.length)) after)) := by
  induction writes generalizing point before with
  | nil =>
      have same : before = after := Option.some.inj run
      subst after
      exact .refl
  | cons write later ih =>
      simp only [runWrites, Option.bind_eq_bind, Option.bind_eq_some_iff] at run
      obtain ⟨result, computed, rest⟩ := run
      have member : edge activation point write ∈ whole := contained _ (by simp [lower])
      have first : (edgeProgram whole).theory.rewrites
          (encode keys (state activation (BitVec.ofNat 64 point) before))
          (encode keys (state activation (BitVec.ofNat 64 (point + 1))
            (Function.update before write.destination result))) := by
        apply (edgeProgram_rewrite_iff whole keys _ _).mpr
        refine ⟨edge activation point write, member,
          state activation (BitVec.ofNat 64 (point + 1)) (Function.update before write.destination result),
          inScope _ member, ?_⟩
        have guarded := (Edge.guard_iff _ _ _).mp (edge_guard activation point write before result computed)
        exact ⟨guarded.1, guarded.2.1, guarded.2.2,
          congrArg (encode keys) (edge_finish activation point write before result).symm⟩
      have remaining := ih (point + 1) (Function.update before write.destination result)
        (fun entry member => contained entry (by simp [lower, member])) rest
      have endPoint : point + 1 + later.length = point + (write :: later).length := by simp; omega
      rw [endPoint] at remaining
      exact Relation.ReflTransGen.head first remaining

theorem state_point_injective (activation : Nat) (keys : Finset (Location Nat))
    (present : .inl activation ∈ keys) (left right : Word) (before after : Nat → Word)
    (same : encode keys (state activation left before) = encode keys (state activation right after)) :
    left = right := by
  have equal := ((encode_le_iff keys keys _ _).mp (le_of_eq same)).2 (.inl activation) present
  simpa [state] using equal

/-- The terminal control token cannot take another edge of this program. -/
theorem terminal_stuck (activation : Nat) (terminal : Word) (whole : List (Edge Nat))
    (keys : Finset (Location Nat)) (before : Nat → Word)
    (owned : ∀ entry ∈ whole, entry.activation = activation)
    (absent : terminal ∉ whole.map Edge.point) :
    ∀ result, ¬(edgeProgram whole).theory.rewrites (encode keys (state activation terminal before)) result := by
  intro result step
  obtain ⟨entry, member, after, _, current, _, _, _⟩ :=
    (edgeProgram_rewrite_iff whole keys _ _).mp step
  have equal : entry.point = terminal := by simpa [state, owned entry member] using current.symm
  exact absent (List.mem_map.mpr ⟨entry, member, equal⟩)

/-- Every path reaching the block's exit is an execution of its source writes. -/
theorem run_reflected (activation point : Nat) (writes : List Write) (whole : List (Edge Nat))
    (keys : Finset (Location Nat)) (before observed : Nat → Word)
    (controlPresent : .inl activation ∈ keys)
    (contained : ∀ entry ∈ lower activation point writes, entry ∈ whole)
    (unique : (whole.map Edge.point).Nodup)
    (owned : ∀ entry ∈ whole, entry.activation = activation)
    (inScope : ∀ entry ∈ whole, entry.recipe.support ⊆ keys)
    (bounded : point + writes.length < 2 ^ 64)
    (terminalAbsent : BitVec.ofNat 64 (point + writes.length) ∉ whole.map Edge.point)
    (path : Relation.ReflTransGen (edgeProgram whole).theory.rewrites
      (encode keys (state activation (BitVec.ofNat 64 point) before))
      (encode keys (state activation (BitVec.ofNat 64 (point + writes.length)) observed))) :
    ∃ after, runWrites writes before = some after ∧
      encode keys (state activation (BitVec.ofNat 64 (point + writes.length)) observed) =
        encode keys (state activation (BitVec.ofNat 64 (point + writes.length)) after) := by
  induction writes generalizing point before with
  | nil =>
      rcases path.cases_head with equal | ⟨next, first, _⟩
      · exact ⟨before, rfl, equal.symm⟩
      · exact False.elim (terminal_stuck activation (BitVec.ofNat 64 point) whole keys before owned terminalAbsent next first)
  | cons write later ih =>
      rcases path.cases_head with equal | ⟨next, first, rest⟩
      · have same := state_point_injective activation keys controlPresent _ _ before observed equal
        have indexSame := word_index_injective point (point + (write :: later).length)
          (by simp only [List.length_cons] at bounded; omega) bounded same
        simp only [List.length_cons] at indexSame
        omega
      · have member : edge activation point write ∈ whole := contained _ (by simp [lower])
        obtain ⟨value, computed, rfl⟩ := (head_step_iff activation point write whole keys before next
          member unique owned (inScope _ member)).mp first
        have endPoint : point + 1 + later.length = point + (write :: later).length := by simp; omega
        have childPath : Relation.ReflTransGen (edgeProgram whole).theory.rewrites
            (encode keys (state activation (BitVec.ofNat 64 (point + 1))
              (Function.update before write.destination value)))
            (encode keys (state activation (BitVec.ofNat 64 (point + 1 + later.length)) observed)) := by
          simpa only [endPoint] using rest
        obtain ⟨after, ran, endpoint⟩ := ih (point + 1) (Function.update before write.destination value)
          (fun entry member => contained entry (by simp [lower, member]))
          (by omega) (by simpa only [endPoint] using terminalAbsent) childPath
        refine ⟨after, ?_, ?_⟩
        · simpa [runWrites, computed] using ran
        · simpa only [endPoint] using endpoint

/-- Two-sided source/transform execution for the complete admitted scalar block. -/
theorem completion_iff (activation point : Nat) (writes : List Write) (keys : Finset (Location Nat))
    (before observed : Nat → Word) (controlPresent : .inl activation ∈ keys)
    (inScope : ∀ entry ∈ lower activation point writes, entry.recipe.support ⊆ keys)
    (bounded : point + writes.length < 2 ^ 64) :
    Relation.ReflTransGen (edgeProgram (lower activation point writes)).theory.rewrites
      (encode keys (state activation (BitVec.ofNat 64 point) before))
      (encode keys (state activation (BitVec.ofNat 64 (point + writes.length)) observed)) ↔
      ∃ after, runWrites writes before = some after ∧
        encode keys (state activation (BitVec.ofNat 64 (point + writes.length)) observed) =
          encode keys (state activation (BitVec.ofNat 64 (point + writes.length)) after) := by
  constructor
  · exact run_reflected activation point writes _ keys before observed controlPresent
      (fun _ member => member) (lower_unique activation point writes bounded)
      (fun entry member => (lower_member activation point writes entry member).1) inScope bounded
      (lower_terminal_absent activation point writes bounded)
  · rintro ⟨after, ran, endpoint⟩
    rw [endpoint]
    exact run_realized activation point writes _ keys before after (fun _ member => member) inScope ran

theorem initialized_injective : Function.Injective initialized := by
  intro before after same
  funext register
  exact Option.some.inj (congrFun same register)

/-- The entry/exit theorem directly names the original RegisterCode executor. -/
theorem source_completion_iff (instructions : List (RegisterCode.Instr Word Scalar Nat Nat))
    (writes : List Write) (accepted : lowerWrites? instructions = some writes)
    (activation point : Nat) (keys : Finset (Location Nat)) (before observed : Nat → Word)
    (controlPresent : .inl activation ∈ keys)
    (inScope : ∀ entry ∈ lower activation point writes, entry.recipe.support ⊆ keys)
    (bounded : point + writes.length < 2 ^ 64) :
    Relation.ReflTransGen (edgeProgram (lower activation point writes)).theory.rewrites
      (encode keys (state activation (BitVec.ofNat 64 point) before))
      (encode keys (state activation (BitVec.ofNat 64 (point + writes.length)) observed)) ↔
      ∃ after, RegisterCode.exec semantics (fun _ _ => none) instructions (initialized before) =
        some (RegisterCode.Outcome.next (initialized after)) ∧
        encode keys (state activation (BitVec.ofNat 64 (point + writes.length)) observed) =
          encode keys (state activation (BitVec.ofNat 64 (point + writes.length)) after) := by
  rw [completion_iff activation point writes keys before observed controlPresent inScope bounded,
    lowerWrites?_source instructions writes accepted before]
  constructor
  · rintro ⟨after, ran, endpoint⟩
    exact ⟨after, by rw [ran]; rfl, endpoint⟩
  · rintro ⟨after, ran, endpoint⟩
    obtain ⟨values, computed, equal⟩ := Option.map_eq_some_iff.mp ran
    have same : values = after := initialized_injective (RegisterCode.Outcome.next.inj equal)
    exact ⟨after, by simpa only [same] using computed, endpoint⟩

namespace Controls

private def write : Write := ⟨0, .binary .add, [.reg 0, .reg 0]⟩
private def keys : Finset (Location Nat) := {.inl 0, .inr 0}
private def before : Nat → Word := fun _ => 7
private def answer (value : Word) : Nat → Word := Function.update before 0 value

private theorem inputs_in_scope : ∀ entry ∈ lower 0 0 [write], entry.recipe.support ⊆ keys := by
  intro entry member
  simp only [lower, List.mem_cons, List.not_mem_nil, or_false] at member
  subst entry
  decide

example : Relation.ReflTransGen (edgeProgram (lower 0 0 [write])).theory.rewrites
    (encode keys (state 0 0 before)) (encode keys (state 0 1 (answer 14))) := by
  apply (completion_iff 0 0 [write] keys before (answer 14) (by decide) inputs_in_scope (by decide)).mpr
  exact ⟨answer 14, rfl, rfl⟩

example : ¬Relation.ReflTransGen (edgeProgram (lower 0 0 [write])).theory.rewrites
    (encode keys (state 0 0 before)) (encode keys (state 0 1 (answer 15))) := by
  intro path
  obtain ⟨after, ran, endpoint⟩ :=
    (completion_iff 0 0 [write] keys before (answer 15) (by decide) inputs_in_scope (by decide)).mp path
  have same : answer 14 = after := Option.some.inj ran
  subst after
  have agree := ((encode_le_iff keys keys _ _).mp (le_of_eq endpoint)).2 (.inr 0) (by decide)
  change (15 : Word) = 14 at agree
  exact (by decide : (15 : Word) ≠ 14) agree

end Controls

end Mettapedia.Machines.TIsa.RegisterBlock
