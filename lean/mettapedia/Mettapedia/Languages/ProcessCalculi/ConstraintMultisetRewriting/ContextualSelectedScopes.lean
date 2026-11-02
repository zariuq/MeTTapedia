import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFreshFrameScopeLedger

/-!
# Exact scope allocation for selected ports and their solver helper frame

Each event reserves one scope per rule/take/read port, then one helper scope.
Different event port counts change the intermediate scope numbers. Two full
reservations nevertheless allocate exactly the same final ledger in either
order; no equality of the two port counts is required.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSelectedScopes

open ContextualActivationScopes ContextualFreshFrameScopeLedger

def reserve (occupied : Finset Nat) (count : Nat) := occupied ∪ Finset.Ico (start occupied) (start occupied + count)
def advance (occupied : Finset Nat) (count : Nat) := helperLedger (reserve occupied count)

theorem next_start (occupied : Finset Nat) (count : Nat) (positive : 0 < count) :
    start (reserve occupied count) = start occupied + count := by
  have upper : (reserve occupied count).sup id ≤ start occupied + count - 1 := by
    apply Finset.sup_le
    intro name member
    rcases Finset.mem_union.mp member with old | fresh
    · have earlier := occupied_lt_start occupied old
      dsimp only [id]
      omega
    · have bounds := Finset.mem_Ico.mp fresh
      dsimp only [id]
      omega
  have last : start occupied + count - 1 ∈ reserve occupied count := by
    apply Finset.mem_union_right
    apply Finset.mem_Ico.mpr
    constructor <;> omega
  have lower : start occupied + count - 1 ≤ (reserve occupied count).sup id := Finset.le_sup (f := id) last
  unfold start
  change (reserve occupied count).sup id + 1 = occupied.sup id + 1 + count
  dsimp only [start] at upper lower
  omega

theorem advance_eq_interval (occupied : Finset Nat) (count : Nat) (positive : 0 < count) :
    advance occupied count = occupied ∪ Finset.Ico (start occupied) (start occupied + count + 1) := by
  unfold advance helperLedger helperScope
  rw [next_start occupied count positive]
  ext name
  by_cases old : name ∈ occupied <;> simp [reserve, old, Finset.mem_Ico]
  omega

theorem advance_start (occupied : Finset Nat) (count : Nat) (positive : 0 < count) :
    start (advance occupied count) = start occupied + count + 1 := by
  rw [advance_eq_interval occupied count positive]
  exact next_start occupied (count + 1) (by omega)

theorem two_advances (occupied : Finset Nat) (first second : Nat)
    (firstPositive : 0 < first) (secondPositive : 0 < second) :
    advance (advance occupied first) second =
      occupied ∪ Finset.Ico (start occupied) (start occupied + first + 1 + second + 1) := by
  rw [advance_eq_interval _ second secondPositive, advance_start occupied first firstPositive,
    advance_eq_interval occupied first firstPositive]
  ext name
  by_cases old : name ∈ occupied <;> simp [old, Finset.mem_Ico]
  omega

theorem advance_comm (occupied : Finset Nat) (first second : Nat)
    (firstPositive : 0 < first) (secondPositive : 0 < second) :
    advance (advance occupied first) second = advance (advance occupied second) first := by
  rw [two_advances occupied first second firstPositive secondPositive,
    two_advances occupied second first secondPositive firstPositive]
  congr 2
  omega

theorem old_scopes_survive (occupied : Finset Nat) (count : Nat) : occupied ⊆ advance occupied count :=
  Finset.Subset.trans Finset.subset_union_left (ContextualFreshFrameScopeLedger.old_scopes_retained _)

theorem rule_scope_in_final (occupied : Finset Nat) (first second : Nat)
    (firstPositive : 0 < first) (secondPositive : 0 < second) :
    start occupied ∈ advance (advance occupied first) second ∧
      start (advance occupied first) ∈ advance (advance occupied first) second ∧
      start (advance occupied second) ∈ advance (advance occupied first) second := by
  rw [two_advances occupied first second firstPositive secondPositive,
    advance_start occupied first firstPositive, advance_start occupied second secondPositive]
  refine ⟨Finset.mem_union_right _ ?_, Finset.mem_union_right _ ?_, Finset.mem_union_right _ ?_⟩ <;>
    apply Finset.mem_Ico.mpr <;> constructor <;> omega

theorem helper_scope_in_final (occupied : Finset Nat) (first second : Nat)
    (firstPositive : 0 < first) (secondPositive : 0 < second) :
    helperScope (reserve occupied first) ∈ advance (advance occupied first) second ∧
      helperScope (reserve occupied second) ∈ advance (advance occupied first) second := by
  change start (reserve occupied first) ∈ _ ∧ start (reserve occupied second) ∈ _
  rw [next_start occupied first firstPositive, next_start occupied second secondPositive,
    two_advances occupied first second firstPositive secondPositive]
  constructor <;> apply Finset.mem_union_right <;> apply Finset.mem_Ico.mpr <;> constructor <;> omega

theorem last_helper_scope (occupied : Finset Nat) (first second : Nat)
    (firstPositive : 0 < first) (secondPositive : 0 < second) :
    helperScope (reserve (advance occupied first) second) = start occupied + first + 1 + second := by
  change start (reserve (advance occupied first) second) = _
  rw [next_start _ second secondPositive, advance_start occupied first firstPositive]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSelectedScopes
