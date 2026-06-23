import Mettapedia.ProbabilityTheory.BayesianNetworks.BayesianNetwork

namespace Mettapedia.ProbabilityTheory.BayesianNetworks

open MeasureTheory

variable {V : Type*}

namespace BayesianNetwork

variable (bn : BayesianNetwork V)

def eventEq (v : V) (val : bn.stateSpace v) : Set bn.JointSpace :=
  { ω | ω v = val }

def eventOfConstraints (cs : List (Σ v : V, bn.stateSpace v)) : Set bn.JointSpace :=
  { ω | ∀ c ∈ cs, ω c.1 = c.2 }

@[simp]
theorem eventOfConstraints_nil :
    eventOfConstraints (bn := bn) [] = Set.univ := by
  ext ω
  simp [eventOfConstraints]

@[simp]
theorem eventOfConstraints_cons (c : Σ v : V, bn.stateSpace v)
    (cs : List (Σ v : V, bn.stateSpace v)) :
    eventOfConstraints (bn := bn) (c :: cs) =
      eventEq (bn := bn) c.1 c.2 ∩ eventOfConstraints (bn := bn) cs := by
  ext ω
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · exact h c (by simp)
    · intro c' hc'
      exact h c' (by simp [hc'])
  · rintro ⟨h1, h2⟩ c' hc'
    rcases List.mem_cons.mp hc' with h | h
    · subst h
      exact h1
    · exact h2 c' h

theorem measurable_eventEq
    [∀ v, MeasurableSingletonClass (bn.stateSpace v)]
    (v : V) (val : bn.stateSpace v) :
    MeasurableSet (eventEq (bn := bn) v val) := by
  classical
  have hmeas : Measurable (fun ω : bn.JointSpace => ω v) := by
    fun_prop
  have hsingleton : MeasurableSet ({val} : Set (bn.stateSpace v)) := by
    simp
  change MeasurableSet ((fun ω : bn.JointSpace => ω v) ⁻¹' ({val} : Set (bn.stateSpace v)))
  exact hsingleton.preimage hmeas

theorem measurable_eventOfConstraints
    [∀ v, MeasurableSingletonClass (bn.stateSpace v)]
    (cs : List (Σ v : V, bn.stateSpace v)) :
    MeasurableSet (eventOfConstraints (bn := bn) cs) := by
  induction cs with
  | nil =>
      simp
  | cons c cs ih =>
      simp [eventOfConstraints_cons, measurable_eventEq, ih]

/-- For BNs where stateSpace v is Bool, `eventEq v false = (eventEq v true)ᶜ`. -/
theorem eventEq_false_eq_compl_true_of_bool
    {bn : BayesianNetwork V} (v : V)
    (valTrue valFalse : bn.stateSpace v)
    (h_ne : valTrue ≠ valFalse)
    (h_exhaust : ∀ x : bn.stateSpace v, x = valTrue ∨ x = valFalse) :
    eventEq (bn := bn) v valFalse = (eventEq (bn := bn) v valTrue)ᶜ := by
  ext ω; simp only [eventEq, Set.mem_setOf_eq, Set.mem_compl_iff]
  constructor
  · intro hf ht; exact h_ne (ht ▸ hf ▸ rfl)
  · intro hnt; rcases h_exhaust (ω v) with h | h
    · exact absurd h hnt
    · exact h

end BayesianNetwork

end Mettapedia.ProbabilityTheory.BayesianNetworks
