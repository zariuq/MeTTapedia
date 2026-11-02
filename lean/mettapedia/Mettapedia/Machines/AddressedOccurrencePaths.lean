import Mettapedia.Machines.OccurrenceMachine

/-!
# Terminal occurrence paths distinguished by persistent branch addresses

The hypotheses are local: addresses grow through one transition, and distinct
successor positions have no common future address. Completed traces reaching
one address are therefore identical, without an assumed whole-run law.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.AddressedOccurrencePaths

variable {Term State Answer Address : Type}

structure Laws (machine : OccurrenceMachineCore Term State Answer) (address : State → List Address) : Prop where
  grows : ∀ (before next : State) (index : Nat), (machine.next before)[index]? = some next → address before <+: address next
  separated : ∀ (before left right : State) (i j : Nat) (common : List Address),
    (machine.next before)[i]? = some left → (machine.next before)[j]? = some right →
    address left <+: common → address right <+: common → i = j

theorem follow_prefix (machine : OccurrenceMachineCore Term State Answer) (address : State → List Address)
    (laws : Laws machine address) (trace : List Nat) {before final : State}
    (followed : machine.follow before trace = some final) : address before <+: address final := by
  induction trace generalizing before with
  | nil =>
      simp only [OccurrenceMachineCore.follow, Option.some.injEq] at followed
      subst final
      exact ⟨[], List.append_nil _⟩
  | cons index trace ih =>
      change ((machine.next before)[index]? >>= fun next => machine.follow next trace) = some final at followed
      cases selected : (machine.next before)[index]? with
      | none => simp [selected] at followed
      | some next =>
          simp only [selected] at followed
          exact (laws.grows before next index selected).trans (ih followed)

/-- Branch address and termination determine the full occurrence trace. No
equality of final answer values is assumed. -/
theorem terminal_traces_unique (machine : OccurrenceMachineCore Term State Answer)
    (address : State → List Address) (laws : Laws machine address)
    (first second : List Nat) {before left right : State} {a b : Answer}
    (leftRun : machine.follow before first = some left)
    (rightRun : machine.follow before second = some right)
    (leftDone : machine.answer left = some a) (rightDone : machine.answer right = some b)
    (sameAddress : address left = address right) : first = second := by
  induction first generalizing second before with
  | nil =>
      simp only [OccurrenceMachineCore.follow, Option.some.injEq] at leftRun
      subst left
      cases second with
      | nil => rfl
      | cons index tail =>
          simp [OccurrenceMachineCore.follow, machine.answer_final _ _ leftDone] at rightRun
  | cons i tail ih =>
      change ((machine.next before)[i]? >>= fun next => machine.follow next tail) = some left at leftRun
      cases selectedLeft : (machine.next before)[i]? with
      | none => simp [selectedLeft] at leftRun
      | some nextLeft =>
          simp only [selectedLeft] at leftRun
          cases second with
          | nil =>
              simp only [OccurrenceMachineCore.follow, Option.some.injEq] at rightRun
              subst right
              simp [machine.answer_final _ _ rightDone] at selectedLeft
          | cons j rest =>
              change ((machine.next before)[j]? >>= fun next => machine.follow next rest) = some right at rightRun
              cases selectedRight : (machine.next before)[j]? with
              | none => simp [selectedRight] at rightRun
              | some nextRight =>
                  simp only [selectedRight] at rightRun
                  have leftPrefix := follow_prefix machine address laws tail leftRun
                  have rightPrefix := follow_prefix machine address laws rest rightRun
                  rw [← sameAddress] at rightPrefix
                  have same := laws.separated before nextLeft nextRight i j (address left)
                    selectedLeft selectedRight leftPrefix rightPrefix
                  subst j
                  have equal : nextLeft = nextRight := Option.some.inj (selectedLeft.symm.trans selectedRight)
                  subst nextRight
                  exact congrArg (List.cons i) (ih rest leftRun rightRun)

end Mettapedia.Machines.AddressedOccurrencePaths
