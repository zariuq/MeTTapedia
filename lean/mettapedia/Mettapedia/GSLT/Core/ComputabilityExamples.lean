import Mettapedia.GSLT.Core.StepFree
import Mathlib.Computability.Halting

/-!
# Computability boundaries for static and operational GSLTs

Two tagged terms for each program code suffice. Identify the tags exactly
when the code does not halt. This gives a step-free, effectively coded
carrier whose equations do not even have a recursive enumeration. If the
same condition licenses a directed rewrite between the tags, even positive
reachability is not recursively enumerable.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ComputabilityExamples

open Nat.Partrec (Code)

variable {α : Type*}

/-- Distinct tags for one object can be identified by an arbitrary predicate. -/
def pairedEquations (identify : α → Prop) : Setoid (α × Bool) where
  r x y := x.1 = y.1 ∧ (x.2 = y.2 ∨ identify x.1)
  iseqv :=
    ⟨fun _ => ⟨rfl, Or.inl rfl⟩,
      fun ⟨eq, tag⟩ => ⟨eq.symm, tag.elim (fun h => Or.inl h.symm) (fun h => Or.inr (eq ▸ h))⟩,
      fun ⟨eq, tag⟩ ⟨eq', tag'⟩ => ⟨eq.trans eq',
        tag.elim
          (fun h => tag'.elim (fun h' => Or.inl (h.trans h')) (fun h' => Or.inr (eq.symm ▸ h')))
          Or.inr⟩⟩

def doesNotHalt (code : Code) : Prop := ¬ (code.eval 0).Dom

abbrev staticTheory : GSLT := GSLT.equationOnly (Code × Bool) (pairedEquations doesNotHalt)

theorem code_equiv_iff (code : Code) :
    staticTheory.Equiv (code, false) (code, true) ↔ doesNotHalt code := by
  change (_ ∧ (_ ∨ doesNotHalt code)) ↔ _
  simp

theorem static_has_no_rewrites (first last : staticTheory.Term) :
    ¬ staticTheory.Step first last := GSLT.equationOnly_not_step _ _ _ _

private def probes (code : Code) : (Code × Bool) × (Code × Bool) :=
  ((code, false), (code, true))

private theorem probes_computable : Computable probes :=
  (Computable.id.pair (Computable.const false)).pair (Computable.id.pair (Computable.const true))

/-- A computable enumeration of these equations would enumerate nonhalting. -/
theorem static_equivalence_not_enumerable :
    ¬ REPred (fun pair : (Code × Bool) × (Code × Bool) => staticTheory.Equiv pair.1 pair.2) := by
  intro listed
  have reduced : REPred fun code => staticTheory.Equiv (probes code).1 (probes code).2 :=
    Partrec.comp listed probes_computable
  exact ComputablePred.halting_problem_not_re 0 (reduced.of_eq code_equiv_iff)

/-- The same obstruction transfers along any computable encoding that
preserves and reflects the equations. -/
theorem no_faithful_effective_equations {Target : Type*} [Primcodable Target]
    (encode : (Code × Bool) → Target) (effective : Computable encode)
    (equal : Target → Target → Prop) (listed : REPred fun p : Target × Target => equal p.1 p.2)
    (faithful : ∀ x y, equal (encode x) (encode y) ↔ staticTheory.Equiv x y) : False := by
  apply static_equivalence_not_enumerable
  have reduced : REPred fun p : (Code × Bool) × (Code × Bool) => equal (encode p.1) (encode p.2) :=
    Partrec.comp listed ((effective.comp Computable.fst).pair (effective.comp Computable.snd))
  exact reduced.of_eq fun pair => faithful pair.1 pair.2

/-- A rule can be specified over mathematical evidence of nonhalting. -/
abbrev operationalTheory : GSLT where
  Term := Code × Bool
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites x y := x.1 = y.1 ∧ x.2 = false ∧ y.2 = true ∧ doesNotHalt x.1
  rewrites_resp_left := fun eq step => by cases eq; exact ⟨_, step, rfl⟩
  rewrites_resp_right := fun step eq => by cases eq; exact step

private theorem first_step_or_eq (theory : GSLT) {s t : theory.Term} (path : theory.MultiStep s t) :
    s = t ∨ ∃ next, theory.Step s next := by
  cases path with
  | refl => exact Or.inl rfl
  | step first _ => exact Or.inr ⟨_, first⟩

theorem code_reaches_iff (code : Code) :
    operationalTheory.MultiStep (code, false) (code, true) ↔ doesNotHalt code := by
  constructor
  · intro path
    rcases first_step_or_eq operationalTheory path with eq | ⟨_, first⟩
    · simp at eq
    · exact first.2.2.2
  · intro proof
    exact GSLT.MultiStep.step (u := (code, true)) ⟨rfl, rfl, rfl, proof⟩ (.refl _)

theorem operational_reachability_not_enumerable :
    ¬ REPred (fun pair : (Code × Bool) × (Code × Bool) => operationalTheory.MultiStep pair.1 pair.2) := by
  intro listed
  have reduced : REPred fun code => operationalTheory.MultiStep (probes code).1 (probes code).2 :=
    Partrec.comp listed probes_computable
  exact ComputablePred.halting_problem_not_re 0 (reduced.of_eq code_reaches_iff)

/-! ## Decidable edges with no total finite frontier -/

/-- Checking that evaluation first succeeds at this fuel is a bounded test. -/
def firstFuel (code : Code) (before : ℕ) : Prop :=
  (code.evaln (before + 1) 0).isSome ∧ !(code.evaln before 0).isSome

private theorem fuel_test_primrec (fuel : Code × ℕ → ℕ) (effective : Primrec fuel) :
    Primrec (fun (p : Code × ℕ) => (p.1.evaln (fuel p) 0).isSome) :=
  Primrec.option_isSome.comp (Code.primrec_evaln.comp ((effective.pair Primrec.fst).pair (Primrec.const 0)))

theorem firstFuel_computable : ComputablePred (fun p : Code × ℕ => firstFuel p.1 p.2) := by
  apply ComputablePred.computable_iff.mpr
  refine ⟨fun p => (p.1.evaln (p.2 + 1) 0).isSome && !(p.1.evaln p.2 0).isSome, ?_, ?_⟩
  · exact (Primrec.and.comp (fuel_test_primrec _ (Primrec.succ.comp Primrec.snd))
      (Primrec.not.comp (fuel_test_primrec _ Primrec.snd))).to_comp
  · funext p
    exact propext (by simp [firstFuel])

theorem halts_iff_firstFuel (code : Code) :
    (code.eval 0).Dom ↔ ∃ before, firstFuel code before := by
  constructor
  · intro halts
    obtain ⟨value, returned⟩ := Part.dom_iff_mem.mp halts
    obtain ⟨later, seen⟩ := Code.evaln_complete.mp returned
    have someFuel : ∃ n, (code.evaln n 0).isSome = true :=
      ⟨later, Option.isSome_iff_exists.mpr ⟨value, seen⟩⟩
    have minSeen := Nat.find_spec someFuel
    have positive : Nat.find someFuel ≠ 0 := by
      intro zero
      simp [zero, Code.evaln] at minSeen
    obtain ⟨before, next⟩ := Nat.exists_eq_succ_of_ne_zero positive
    refine ⟨before, ?_, ?_⟩
    · rwa [next] at minSeen
    · have earlier : before < Nat.find someFuel := by rw [next]; exact Nat.lt_succ_self _
      have absent := Nat.find_min someFuel earlier
      simpa using Bool.eq_false_of_not_eq_true absent
  · rintro ⟨before, found, _⟩
    obtain ⟨value, seen⟩ := Option.isSome_iff_exists.mp found
    exact Part.dom_iff_mem.mpr ⟨value, Code.evaln_sound seen⟩

theorem firstFuel_unique (code : Code) {first second : ℕ}
    (found : firstFuel code first) (found' : firstFuel code second) : first = second := by
  have order {i j : ℕ} (a : firstFuel code i) (b : firstFuel code j) : i ≤ j := by
    by_contra! earlier
    obtain ⟨value, seen⟩ := Option.isSome_iff_exists.mp b.1
    have still := Option.isSome_iff_exists.mpr ⟨value, Code.evaln_mono earlier seen⟩
    have absent : !(code.evaln i 0).isSome := a.2
    simp [still] at absent
  exact le_antisymm (order found found') (order found' found)

/-- Deciding a candidate edge does not supply a complete finite list of
successors, even when the list would have at most one member. -/
theorem no_computable_frontier (frontier : Code → List ℕ) (effective : Computable frontier)
    (agrees : ∀ c before, before ∈ frontier c ↔ firstFuel c before) : False := by
  have empty : ComputablePred (fun c => (frontier c).length = 0) :=
    (Primrec.eq.decide.to_comp.comp (Computable.list_length.comp effective) (Computable.const 0)).computablePred
  apply ComputablePred.halting_problem 0
  refine empty.not.of_eq fun code => ?_
  rw [halts_iff_firstFuel]
  simp only [← agrees code, List.length_eq_zero_iff]
  cases frontier code <;> simp

#print axioms static_equivalence_not_enumerable
#print axioms no_faithful_effective_equations
#print axioms operational_reachability_not_enumerable
#print axioms firstFuel_computable
#print axioms no_computable_frontier

end Mettapedia.GSLT.ComputabilityExamples
