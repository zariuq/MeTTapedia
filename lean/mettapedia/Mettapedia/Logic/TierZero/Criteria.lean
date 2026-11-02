import Mettapedia.Logic.TierZero.Kernel
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Basis
import Mettapedia.Enactive.Finite
import Mettapedia.Algebra.QuantaleWeakness

/-!
# Naturalness criteria for the tier-0 kernel, measured on its own steps

Four kernel forms are compared. Each is a set of step shapes over spaces.

* **dataflow** (`kernel/tier0.metta`): every node fires when the theorems it cites exist; a
  citation keeps the theorem; acceptance reads the claim's pending nodes in full (their absence).
* **sequential** (`kernel/tier0_seq.metta`): a cursor walks the nodes in order; a citation keeps the
  theorem; acceptance is the cursor at the end, with no full read.
* **rho** (COMM only): every read takes; a citation takes the theorem and makes it again.
* **rewrite** (the earlier `=`-rewrite kernel, `MettaKernel/kernel/lcf_core.metta`): theorems are
  values computed by functions; there is no space and no step.

## Criteria and what is proved here

1. **Parts of a step used** (`formParts`, the "minimal operators" criterion): dataflow uses take,
   keep, make and full read; sequential take, keep, make; rho take and make
   (`card_parts_rho_lt_sequential`, `card_parts_sequential_lt_dataflow`). Counting parts is a
   description length: it is the simplicity-maxing instance of Goertzel's constraint-cost
   quantale, and it ranks rho simplest.
2. **What each part buys**, from the separation theorems of `OccurrenceCommits.Basis`:
   * two nodes citing one theorem by keeping it are independent steps (`citeKeep_independent`),
     while citing by take-and-make makes them clash (`citeTake_clash`); and no step without keep
     encodes a keeping citation once the same theorem can be proved twice (`citeKeep_needs_keep`);
   * the dataflow acceptance, a full read of the pending nodes, is encoded by no positive step
     (`acceptQuery_needs_fullRead`); the sequential acceptance is positive (`acceptCursor_positive`),
     paid for by fixing the order.
3. **Bennett weakness** (`Enactive.Finite`): a schedule constraint "node i before node j" is a fact;
   a kernel form's statement is the set of constraints it imposes on the order of steps. On the
   three-node proof (two leaves, one root citing both) the dataflow statement is the two citation
   constraints and the sequential one adds "leaf 0 before leaf 1"; the dataflow statement is
   strictly weaker (`bennett_dataflow_weaker`).
4. **Goertzel's quantale weakness** in its counting instance (pairs of schedules the verdict does
   not distinguish, `QuantaleWeakness.pairDistinctionWeakness`) ranks the same way
   (`goertzel_counting_dataflow_weaker`): four indistinguishable pairs against one.

So the razors disagree: counting parts picks rho's COMM, weakness picks the dataflow kernel, and the
sequential kernel lies between. The tie is broken only by further requirements: independence of
citations and read-only theorem readers need keep (item 2), a schedule-free check needs the full
read, and the LCF requirement needs rights (`TierZero.Rights`), which every form must add.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Criteria

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

/-! ## Step shapes of the kernel forms -/

/-- The four parts of a step. -/
inductive Part where
  | take | keep | make | fullRead
  deriving DecidableEq, Repr

/-- Labels of the occurrences in the examples: a theorem, a pending node, a conclusion, a verdict,
and the cursor at the end of a walk. -/
inductive Lab where
  | thm (j : ℕ)
  | pending (n : ℕ)
  | concl (n : ℕ)
  | accepted
  | cursorEnd
  deriving DecidableEq, Repr

/-- Occurrence `0` and `5` carry the same theorem (it was proved twice); `20` and `21` are that
theorem made again; `1`, `2` and every occurrence from `100` on are pending nodes. -/
def lab : ℕ → Lab
  | 0 => .thm 7
  | 5 => .thm 7
  | 20 => .thm 7
  | 21 => .thm 7
  | 10 => .concl 1
  | 11 => .concl 2
  | 30 => .accepted
  | 40 => .cursorEnd
  | n => .pending n

/-- The parts a step uses. -/
def parts (c : Commit ℕ Lab) : Finset Part :=
  (if c.taken.Nonempty then {Part.take} else ∅) ∪ (if c.kept.Nonempty then {Part.keep} else ∅) ∪
    (if c.made.Nonempty then {Part.make} else ∅) ∪ (if c.queries ≠ [] then {Part.fullRead} else ∅)

/-- The parts a kernel form uses. -/
def formParts (steps : List (Commit ℕ Lab)) : Finset Part :=
  steps.foldr (fun c acc => parts c ∪ acc) ∅

def isPending : Lab → Bool
  | .pending _ => true
  | _ => false

/-- Discharge of node `i`'s premise by keeping the theorem `0`. -/
def citeKeep (i : ℕ) : Commit ℕ Lab := ⟨{i}, {0}, {9 + i}, []⟩

/-- Discharge by taking the theorem and making it again (the rho form). -/
def citeTake (i : ℕ) : Commit ℕ Lab := ⟨{i, 0}, ∅, {9 + i, 19 + i}, []⟩

/-- A node closing: its obligation is taken and its theorem made. -/
def closeStep : Commit ℕ Lab := ⟨{1}, ∅, {10}, []⟩

/-- Dataflow acceptance: keep the root theorem, read the pending nodes in full (none), make the
verdict. -/
def acceptQuery : Commit ℕ Lab := ⟨∅, {0}, {30}, [⟨isPending, ∅⟩]⟩

/-- Sequential acceptance: take the cursor at the end, keep the root theorem, make the verdict. -/
def acceptCursor : Commit ℕ Lab := ⟨{40}, {0}, {30}, []⟩

/-- Rho acceptance: take the cursor at the end and the root theorem, make both the verdict and the
theorem again. -/
def acceptRho : Commit ℕ Lab := ⟨{40, 0}, ∅, {30, 20}, []⟩

def dataflowSteps : List (Commit ℕ Lab) := [citeKeep 1, closeStep, acceptQuery]
def sequentialSteps : List (Commit ℕ Lab) := [citeKeep 1, closeStep, acceptCursor]
def rhoSteps : List (Commit ℕ Lab) := [citeTake 1, closeStep, acceptRho]

theorem parts_dataflow : formParts dataflowSteps = {Part.take, Part.keep, Part.make, Part.fullRead} := by
  decide

theorem parts_sequential : formParts sequentialSteps = {Part.take, Part.keep, Part.make} := by
  decide

theorem parts_rho : formParts rhoSteps = {Part.take, Part.make} := by
  decide

/-- **Counting parts ranks rho simplest.** -/
theorem card_parts_rho_lt_sequential : (formParts rhoSteps).card < (formParts sequentialSteps).card := by
  decide

theorem card_parts_sequential_lt_dataflow :
    (formParts sequentialSteps).card < (formParts dataflowSteps).card := by
  decide

/-! ## What keep and the full read buy -/

/-- Two nodes citing one theorem by keeping it are independent: they commute. -/
theorem citeKeep_independent : Independent lab (citeKeep 1) (citeKeep 2) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro (h | h) <;> exact h (by decide)
  · rintro (h | ⟨read, mem, -⟩)
    · exact h (by decide)
    · simp [citeKeep] at mem
  · rintro (h | ⟨read, mem, -⟩)
    · exact h (by decide)
    · simp [citeKeep] at mem

/-- Two nodes citing one theorem by taking it clash: at most one of them goes first. -/
theorem citeTake_clash : Clash (citeTake 1) (citeTake 2) :=
  Or.inl (by decide)

theorem citeKeep_enabled : Enabled lab {0, 1} (citeKeep 1) where
  taken_subset := by decide
  kept_subset := by decide
  apart := by decide
  fresh := by decide
  queries_hold := by simp [citeKeep]

/-- **Keep is needed**: once a theorem can be proved twice (occurrence `5` carries the label of
`0`), no step without keep encodes a keeping citation. -/
theorem citeKeep_needs_keep (e : Commit ℕ Lab) (keepFree : e.kept = ∅) : ¬ Encodes lab (citeKeep 1) e :=
  not_encodes_keep (o := 0) (o' := 5) rfl citeKeep_enabled (by decide) (by decide) (by decide) rfl
    keepFree

theorem acceptQuery_enabled : Enabled lab {0} acceptQuery where
  taken_subset := by decide
  kept_subset := by decide
  apart := by decide
  fresh := by decide
  queries_hold := by
    intro read mem
    simp only [acceptQuery, List.mem_singleton] at mem
    subst mem
    unfold PredicateQuery.Holds regionOf
    decide

theorem pending_unbounded (F : Finset ℕ) : ∃ o ∉ F, isPending (lab o) = true := by
  refine ⟨F.sup id + 100, ?_, ?_⟩
  · intro mem
    have h : F.sup id + 100 ≤ F.sup id := Finset.le_sup (f := id) mem
    omega
  · have big : 41 ≤ F.sup id + 100 := by omega
    unfold lab
    split <;> first | omega | rfl

/-- **The full read is needed** for the dataflow acceptance: no positive step encodes it. -/
theorem acceptQuery_needs_fullRead (e : Commit ℕ Lab) (positive : e.Positive) :
    ¬ Encodes lab acceptQuery e :=
  not_encodes_predicateQuery acceptQuery_enabled (List.mem_singleton_self _) pending_unbounded positive

/-- The sequential acceptance needs none: it is positive. -/
theorem acceptCursor_positive : acceptCursor.Positive := rfl

/-! ## Bennett weakness of the schedule constraints -/

/-- A world is an order of the three steps of the proof: `σ i` is the time of node `i`. -/
abbrev World := Equiv.Perm (Fin 3)

/-- The fact "node `i` is checked before node `j`". -/
def before (i j : Fin 3) : Finset World := Finset.univ.filter fun σ => σ i < σ j

/-- The vocabulary: every ordering constraint between two different nodes. -/
def vocabulary : Finset (Finset World) :=
  {before 0 1, before 1 0, before 0 2, before 2 0, before 1 2, before 2 1}

def layer : Mettapedia.Enactive.Finite.Layer World := ⟨vocabulary⟩

/-- Dataflow: only the citations order the steps (the root cites both leaves). -/
def dataflowFacts : Finset (Finset World) := {before 0 2, before 1 2}

/-- Sequential: the proof's order, leaf 0, leaf 1, root. -/
def sequentialFacts : Finset (Finset World) := {before 0 1, before 0 2, before 1 2}

theorem realizes_identity (facts : Finset (Finset World)) (h : facts ⊆ sequentialFacts) :
    Mettapedia.Enactive.Finite.Realizable facts := by
  refine ⟨Equiv.refl _, fun fact mem => ?_⟩
  have := h mem
  simp only [sequentialFacts, Finset.mem_insert, Finset.mem_singleton] at this
  rcases this with rfl | rfl | rfl <;> simp [before]

theorem dataflow_statement : dataflowFacts ∈ layer.statements := by
  rw [Mettapedia.Enactive.Finite.Layer.mem_statements]
  refine ⟨?_, realizes_identity _ ?_⟩
  · intro x hx
    simp only [dataflowFacts, Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [layer, vocabulary, Finset.mem_insert, Finset.mem_singleton]
    rcases hx with rfl | rfl <;> simp
  · intro x hx
    simp only [dataflowFacts, Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [sequentialFacts, Finset.mem_insert, Finset.mem_singleton]
    rcases hx with rfl | rfl <;> simp

theorem sequential_statement : sequentialFacts ∈ layer.statements := by
  rw [Mettapedia.Enactive.Finite.Layer.mem_statements]
  refine ⟨?_, realizes_identity _ subset_rfl⟩
  intro x hx
  simp only [sequentialFacts, Finset.mem_insert, Finset.mem_singleton] at hx
  simp only [layer, vocabulary, Finset.mem_insert, Finset.mem_singleton]
  rcases hx with rfl | rfl | rfl <;> simp

/-- The swapped order of the leaves satisfies the dataflow constraints, not the sequential ones. -/
def swapLeaves : World := Equiv.swap 0 1

theorem before01_ne_before02 : before 0 1 ≠ before 0 2 := by
  intro h
  have : swapLeaves ∈ before 0 2 := by simp [before, swapLeaves, Equiv.swap_apply_of_ne_of_ne]
  rw [← h] at this
  simp [before, swapLeaves] at this

theorem before01_ne_before12 : before 0 1 ≠ before 1 2 := by
  intro h
  have : swapLeaves ∈ before 1 2 := by simp [before, swapLeaves, Equiv.swap_apply_of_ne_of_ne]
  rw [← h] at this
  simp [before, swapLeaves] at this

theorem dataflow_ssubset_sequential : dataflowFacts ⊂ sequentialFacts := by
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨before 0 1, by simp [sequentialFacts], ?_⟩
    simp [dataflowFacts, before01_ne_before02, before01_ne_before12]
  · intro x hx
    simp only [dataflowFacts, Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [sequentialFacts, Finset.mem_insert, Finset.mem_singleton]
    rcases hx with rfl | rfl <;> simp

/-- **Bennett**: the dataflow kernel's constraints on the order of steps are strictly weaker. -/
theorem bennett_dataflow_weaker :
    layer.weakness ⟨sequentialFacts, sequential_statement⟩ <
      layer.weakness ⟨dataflowFacts, dataflow_statement⟩ :=
  layer.weakness_strictAnti (show (⟨dataflowFacts, dataflow_statement⟩ : layer.Statement) <
    ⟨sequentialFacts, sequential_statement⟩ from dataflow_ssubset_sequential)

/-! ## Goertzel's quantale weakness, counting instance -/

/-- The orders each kernel admits. -/
def admitted (facts : Finset (Finset World)) : Finset World :=
  Finset.univ.filter fun σ => ∀ fact ∈ facts, σ ∈ fact

theorem admitted_dataflow_card : (admitted dataflowFacts).card = 2 := by
  decide

theorem admitted_sequential_card : (admitted sequentialFacts).card = 1 := by
  decide

/-- **Goertzel, counting quantale**: the verdict does not distinguish any two admitted orders (the
kernel's verdict is a function of the proof), so the undistinguished pairs are all pairs of
admitted orders; the dataflow kernel leaves four, the sequential kernel one. -/
theorem goertzel_counting_dataflow_weaker :
    Mettapedia.Algebra.QuantaleWeakness.pairDistinctionWeakness
        (Mettapedia.Algebra.QuantaleWeakness.inducedPairEvent (admitted sequentialFacts)) <
      Mettapedia.Algebra.QuantaleWeakness.pairDistinctionWeakness
        (Mettapedia.Algebra.QuantaleWeakness.inducedPairEvent (admitted dataflowFacts)) := by
  rw [Mettapedia.Algebra.QuantaleWeakness.pairDistinctionWeakness_inducedPairEvent,
    Mettapedia.Algebra.QuantaleWeakness.pairDistinctionWeakness_inducedPairEvent]
  unfold Mettapedia.Algebra.QuantaleWeakness.bennettWeakness
  rw [admitted_dataflow_card, admitted_sequential_card]
  decide

end Mettapedia.Logic.TierZero.Criteria
