import Mathlib.Tactic

/-!
# Growth checks with open engine needs

The growth gate runs each registered check and requires it to stay within
its bounds. Some bounds belong to the engine and are not met yet (the
Anthropic encoder is quadratic in the message count). Such a check is held
as an open engine need: a strict expected failure. The gate requires it to
break its bounds, like the gate's own mutants.

Invariants proved here, for any measurements:

* the gate passes only if every registered check holds and every open need
  still breaks its bounds;
* once an engine meets a need, the gate fails until the check is promoted
  to the registered list, and after the promotion it passes again;
* a need cannot be promoted while the engine still breaks it.

The counterexample is a report-only list of needs: a need the engine has
met stays listed as open, unpromoted, and the gate still passes, so the
engine can later regress unseen.
-/

set_option autoImplicit false

namespace Mettapedia.Protocols.Agents.GrowthEngineNeeds

variable {C : Type}

/-- The gate's verdict: registered checks hold; open needs break. -/
def gate (holds : C → Bool) (registered needs : List C) : Bool :=
  registered.all holds && needs.all (fun c => !holds c)

theorem gate_passes_iff (holds : C → Bool) (registered needs : List C) :
    gate holds registered needs = true ↔
      (∀ c ∈ registered, holds c = true) ∧ ∀ c ∈ needs, holds c = false := by
  simp [gate, List.all_eq_true]

/-- A need the engine meets fails the gate. -/
theorem met_need_fails (holds : C → Bool) (registered needs : List C) (c : C)
    (hc : c ∈ needs) (met : holds c = true) : gate holds registered needs = false := by
  cases h : gate holds registered needs
  · rfl
  · exact absurd ((gate_passes_iff holds registered needs).1 h |>.2 c hc) (by simp [met])

/-- Promoting a met need restores the gate. -/
theorem promotion_restores (holds : C → Bool) (registered needs : List C) (c : C)
    (pass : gate holds registered (c :: needs) = false) (rest : gate holds registered needs = true)
    (met : holds c = true) : gate holds (c :: registered) needs = true := by
  have := (gate_passes_iff holds registered needs).1 rest
  rw [gate_passes_iff]
  refine ⟨?_, this.2⟩
  intro d hd
  rcases List.mem_cons.1 hd with rfl | hd
  · exact met
  · exact this.1 d hd

/-- A need the engine still breaks cannot be promoted. -/
theorem unmet_promotion_fails (holds : C → Bool) (registered needs : List C) (c : C)
    (unmet : holds c = false) : gate holds (c :: registered) needs = false := by
  simp [gate, unmet]

/-- The rejected design: needs are only reported. -/
def reportOnly (holds : C → Bool) (registered _needs : List C) : Bool := registered.all holds

/-- A met need stays listed as open and the report-only gate passes. -/
theorem report_only_hides_a_met_need :
    reportOnly (fun _ : Unit => true) [] [()] = true ∧ gate (fun _ : Unit => true) [] [()] = false := by
  decide

end Mettapedia.Protocols.Agents.GrowthEngineNeeds
