import Mettapedia.TypeTheory.MaterialSets.Hypersets.PresentedLabels
import Mettapedia.TypeTheory.MaterialSets.Hypersets.Streams

/-!
# Bisimilarity of explicitly presented labelled values

The exact membership equation of a presented labelled graph identifies its
material equality with readout-labelled bisimilarity. Related pairs supply a
common labelled graph; uniqueness on its explicit pair encoding proves the
reverse implication without choosing matches as functions.

Concrete graph providers encode arbitrary natural-number results and two
distinct fault tags. Their finite singleton chains have distinct material
readings. Outcome transitions distinguish those readings, while one-node and
two-node cycles agree exactly at the stated behavioural observation.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets

universe u

namespace HSet.PresentedLabels

section Bisimilarity

variable {α α' β β' : Type u} {r : α → β → α → Prop} {s : α' → β' → α' → Prop}
  {ℓ : β → HSet.{u}} {ℓ' : β' → HSet.{u}}

/-- Equality of material values supplies a matching relation on all states. -/
theorem labelledBisimilar_of_decorate_eq (p : PresentedLabels ℓ) (q : PresentedLabels ℓ')
    {a : α} {a' : α'} (h : p.decorate r a = q.decorate s a') :
    LabelledBisimilar r s ℓ ℓ' a a' := by
  refine ⟨fun c c' => p.decorate r c = q.decorate s c', ?_, h⟩
  intro c c' hcc'
  constructor
  · intro b d hrd
    have hmem : kpair (ℓ b) (p.decorate r d) ∈ q.decorate s c' := by
      rw [← hcc']
      exact p.mem_decorate.mpr ⟨b, d, hrd, rfl⟩
    obtain ⟨b', d', hsd, he⟩ := q.mem_decorate.mp hmem
    obtain ⟨hl, hd⟩ := kpair_inj.mp he
    exact ⟨b', d', hsd, hl, hd⟩
  · intro b' d' hsd
    have hmem : kpair (ℓ' b') (q.decorate s d') ∈ p.decorate r c := by
      rw [hcc']
      exact q.mem_decorate.mpr ⟨b', d', hsd, rfl⟩
    obtain ⟨b, d, hrd, he⟩ := p.mem_decorate.mp hmem
    obtain ⟨hl, hd⟩ := kpair_inj.mp he
    exact ⟨b, d, hrd, hl.symm, hd.symm⟩

/-- Both readings of related pairs solve the same labelled graph, using the
first system's supplied label presentations. -/
theorem decorate_eq_of_labelledBisimilar (p : PresentedLabels ℓ) (q : PresentedLabels ℓ')
    {a : α} {a' : α'} (h : LabelledBisimilar r s ℓ ℓ' a a') :
    p.decorate r a = q.decorate s a' := by
  obtain ⟨R, hR, haa'⟩ := h
  have left : IsLabelledDecoration (pairRel r s ℓ ℓ' R) ℓ
      (fun pair => p.decorate r pair.1.1) := by
    intro pair y
    show y ∈ p.decorate r pair.1.1 ↔ _
    rw [p.mem_decorate]
    constructor
    · rintro ⟨b, c, hrc, rfl⟩
      obtain ⟨b', c', hsc, hl, hc⟩ := (hR pair.2).1 b c hrc
      exact ⟨b, ⟨(c, c'), hc⟩, ⟨hrc, b', hsc, hl⟩, rfl⟩
    · rintro ⟨b, pair', ⟨hrq, _⟩, rfl⟩
      exact ⟨b, pair'.1.1, hrq, rfl⟩
  have right : IsLabelledDecoration (pairRel r s ℓ ℓ' R) ℓ
      (fun pair => q.decorate s pair.1.2) := by
    intro pair y
    show y ∈ q.decorate s pair.1.2 ↔ _
    rw [q.mem_decorate]
    constructor
    · rintro ⟨b', c', hsc, rfl⟩
      obtain ⟨b, c, hrc, hl, hc⟩ := (hR pair.2).2 b' c' hsc
      exact ⟨b, ⟨(c, c'), hc⟩, ⟨hrc, b', hsc, hl⟩, by rw [hl]⟩
    · rintro ⟨b, pair', ⟨_, b', hsq, hl⟩, rfl⟩
      exact ⟨b', pair'.1.2, hsq, by rw [hl]⟩
  exact congrFun ((p.unique left).trans (p.unique right).symm) ⟨(a, a'), haa'⟩

/-- Material equality is exactly readout-labelled bisimilarity, with no
finiteness hypothesis and no selection of label graphs or transition matches. -/
theorem decorate_eq_iff_labelledBisimilar (p : PresentedLabels ℓ) (q : PresentedLabels ℓ')
    {a : α} {a' : α'} :
    p.decorate r a = q.decorate s a' ↔ LabelledBisimilar r s ℓ ℓ' a a' :=
  ⟨p.labelledBisimilar_of_decorate_eq q, p.decorate_eq_of_labelledBisimilar q⟩

end Bisimilarity

section Cycles

variable {β : Type u} {ℓ : β → HSet.{u}}

/-- A one-node cycle emits the declared label at every transition. -/
def loopRel (b : β) (_source : PUnit.{u + 1}) (label : β) (_target : PUnit.{u + 1}) : Prop :=
  label = b

/-- A two-node cycle emits one label while alternating its two states. -/
def twoCycleRel (b : β) (source : ULift.{u} Bool) (label : β) (target : ULift.{u} Bool) : Prop :=
  label = b ∧ target.down = !source.down

/-- Different cycle lengths have the same material behaviour when they emit
the same reading. The relation actually matches every cyclic transition. -/
theorem loop_eq_twoCycle (p : PresentedLabels ℓ) (b : β) :
    p.decorate (loopRel b) PUnit.unit = p.decorate (twoCycleRel b) ⟨false⟩ := by
  apply (p.decorate_eq_iff_labelledBisimilar p).mpr
  refine ⟨fun (_ : PUnit.{u + 1}) (_ : ULift.{u} Bool) => True, ?_, trivial⟩
  intro source target _
  constructor
  · intro label next step
    exact ⟨label, ⟨!target.down⟩, ⟨step, rfl⟩, rfl, trivial⟩
  · intro label next step
    exact ⟨label, PUnit.unit, step.1, rfl, trivial⟩

/-- The emitted reading, rather than the cycle's authored label name, decides
equality of the repeating behaviours. -/
theorem loop_eq_iff_reading_eq (p : PresentedLabels ℓ) (b c : β) :
    p.decorate (loopRel b) PUnit.unit = p.decorate (loopRel c) PUnit.unit ↔ ℓ b = ℓ c := by
  constructor
  · intro equal
    obtain ⟨R, hR, related⟩ := (p.decorate_eq_iff_labelledBisimilar p).mp equal
    obtain ⟨label, next, step, readings, _⟩ := (hR related).1 b PUnit.unit rfl
    exact step ▸ readings
  · intro readings
    apply (p.decorate_eq_iff_labelledBisimilar p).mpr
    refine ⟨fun (_ _ : PUnit.{u + 1}) => True, ?_, trivial⟩
    intro source target _
    constructor
    · intro label next step
      exact ⟨c, PUnit.unit, rfl, step ▸ readings, trivial⟩
    · intro label next step
      exact ⟨b, PUnit.unit, rfl, step ▸ readings, trivial⟩

/-- A repeating value contains a genuine membership cycle through its
Kuratowski pair and its unordered-pair member. -/
theorem loop_not_wf (p : PresentedLabels ℓ) (b : β) :
    ¬ (p.decorate (loopRel b) PUnit.unit).WF := by
  apply HSet.not_wf_of_cycle
    (y := kpair (ℓ b) (p.decorate (loopRel b) PUnit.unit))
    (z := {ℓ b, p.decorate (loopRel b) PUnit.unit})
  · exact p.mem_decorate.mpr ⟨b, PUnit.unit, rfl, rfl⟩
  · exact mem_kpair.mpr (Or.inr rfl)
  · exact mem_pair.mpr (Or.inr rfl)

end Cycles

end HSet.PresentedLabels

namespace OutcomeLabels

open HSet

/-- Two observable faults remain distinct from each other and every result. -/
inductive Fault : Type u where
  | divisionByZero
  | unboundSymbol
  deriving DecidableEq

/-- Declared results and faults carried by outcome observations. -/
inductive Outcome : Type u where
  | result (value : Nat)
  | fault (kind : Fault.{u})
  deriving DecidableEq

/-- Disjoint finite-chain indices for the fault and result constructors. -/
def code : Outcome.{u} → Nat
  | .result n => n + 2
  | .fault .divisionByZero => 0
  | .fault .unboundSymbol => 1

theorem code_injective : Function.Injective code.{u} := by
  intro first second equal
  cases first with
  | result n =>
    cases second with
    | result m =>
      exact congrArg Outcome.result (Nat.add_right_cancel equal)
    | fault kind =>
      cases kind <;> simp only [code] at equal <;> omega
  | fault firstKind =>
    cases second with
    | result m =>
      cases firstKind <;> simp only [code] at equal <;> omega
    | fault secondKind =>
      cases firstKind <;> cases secondKind <;> simp_all [code]

/-- The material value of a finite singleton chain. -/
def chainValue : Nat → HSet.{u}
  | 0 => ∅
  | n + 1 => {chainValue n}

private theorem chainValue_succ_ne_empty (n : Nat) : chainValue.{u} (n + 1) ≠ ∅ := by
  intro equal
  exact notMem_empty (chainValue n) (equal ▸ mem_singleton_self (chainValue n))

theorem chainValue_injective : Function.Injective chainValue.{u} := by
  intro n
  induction n with
  | zero =>
    intro m equal
    cases m with
    | zero => rfl
    | succ m => exact (chainValue_succ_ne_empty m equal.symm).elim
  | succ n ih =>
    intro m equal
    cases m with
    | zero => exact (chainValue_succ_ne_empty n equal).elim
    | succ m => exact congrArg Nat.succ (ih (singleton_inj.mp equal))

/-- The finite chain is built recursively from the empty graph and a single
authored child, without selecting a representative of its material value. -/
def chainGraph : Nat → AccessiblePointedGraph.{u}
  | 0 => AccessiblePointedGraph.empty
  | n + 1 => AccessiblePointedGraph.sup (fun _ : PUnit.{u + 1} => chainGraph n)

theorem mk_chainGraph (n : Nat) : HSet.mk (chainGraph.{u} n) = chainValue n := by
  induction n with
  | zero => exact mk_empty
  | succ n ih =>
    change HSet.range (fun _ : PUnit.{u + 1} => chainGraph n) = {chainValue n}
    ext y
    rw [mem_range, mem_singleton]
    constructor
    · rintro ⟨_, rfl⟩
      exact ih
    · intro equal
      exact ⟨PUnit.unit, ih.trans equal.symm⟩

/-- A different authored graph duplicates the root's child at every nonzero
index, while retaining the same material reading. -/
def duplicateGraph : Nat → AccessiblePointedGraph.{u}
  | 0 => AccessiblePointedGraph.empty
  | n + 1 => AccessiblePointedGraph.sup (fun _ : ULift.{u} Bool => chainGraph n)

theorem mk_duplicateGraph (n : Nat) : HSet.mk (duplicateGraph.{u} n) = chainValue n := by
  cases n with
  | zero => exact mk_empty
  | succ n =>
    change HSet.range (fun _ : ULift.{u} Bool => chainGraph n) = {chainValue n}
    ext y
    rw [mem_range, mem_singleton]
    constructor
    · rintro ⟨_, rfl⟩
      exact mk_chainGraph n
    · intro equal
      exact ⟨⟨false⟩, (mk_chainGraph n).trans equal.symm⟩

def reading (outcome : Outcome.{u}) : HSet.{u} := chainValue (code outcome)

theorem reading_injective : Function.Injective reading.{u} :=
  fun _ _ equal => code_injective (chainValue_injective equal)

/-- Concrete small graph providers for every declared natural result and fault. -/
def presented : PresentedLabels reading.{u} where
  graph outcome := chainGraph (code outcome)
  mk_graph outcome := mk_chainGraph (code outcome)

/-- A concrete alternative provider contains duplicate authored children. -/
def duplicated : PresentedLabels reading.{u} where
  graph outcome := duplicateGraph (code outcome)
  mk_graph outcome := mk_duplicateGraph (code outcome)

theorem outcome_presentation_independent {α : Type u}
    (r : α → Outcome.{u} → α → Prop) : presented.decorate r = duplicated.decorate r :=
  presented.presentation_independent duplicated r

/-- An outcome observation exposes one result or fault before reaching its
childless endpoint. -/
inductive TerminalState : Type u where
  | exposes
  | done
  deriving DecidableEq

def terminalRel (outcome : Outcome.{u})
    (source : TerminalState.{u}) (label : Outcome.{u}) (target : TerminalState.{u}) : Prop :=
  source = .exposes ∧ label = outcome ∧ target = .done

theorem decorate_done (outcome : Outcome.{u}) :
    presented.decorate (terminalRel outcome) TerminalState.done = ∅ := by
  apply eq_empty_iff.mpr
  intro y member
  obtain ⟨label, target, step, _⟩ := presented.mem_decorate.mp member
  exact TerminalState.noConfusion step.1

def terminalValue (outcome : Outcome.{u}) : HSet.{u} :=
  presented.decorate (terminalRel outcome) TerminalState.exposes

/-- The outcome readout retains the whole declared tag paired with the actual
childless successor. -/
theorem terminalValue_spec (outcome : Outcome.{u}) :
    terminalValue outcome = {kpair (reading outcome) ∅} := by
  ext y
  rw [terminalValue, presented.mem_decorate, mem_singleton]
  constructor
  · rintro ⟨label, target, ⟨_, rfl, rfl⟩, equal⟩
    rwa [decorate_done] at equal
  · intro equal
    refine ⟨outcome, TerminalState.done, ⟨rfl, rfl, rfl⟩, ?_⟩
    rwa [decorate_done]

theorem terminalValue_injective : Function.Injective terminalValue.{u} := by
  intro first second equal
  rw [terminalValue_spec, terminalValue_spec] at equal
  exact reading_injective (kpair_inj.mp (singleton_inj.mp equal)).1

/-- Different natural results remain distinguishable in their material readout. -/
theorem result_values_ne {n m : Nat} (different : n ≠ m) :
    terminalValue (Outcome.result n : Outcome.{u}) ≠ terminalValue (Outcome.result m) := by
  intro equal
  exact different (Outcome.result.inj (terminalValue_injective equal))

/-- A fault cannot be confused with a successful result. -/
theorem result_fault_values_ne (n : Nat) (fault : Fault.{u}) :
    terminalValue (Outcome.result n) ≠ terminalValue (Outcome.fault fault) := by
  intro equal
  exact Outcome.noConfusion (terminalValue_injective equal)

theorem fault_values_ne :
    terminalValue (Outcome.fault Fault.divisionByZero : Outcome.{u}) ≠
      terminalValue (Outcome.fault Fault.unboundSymbol) := by
  intro equal
  exact Fault.noConfusion (Outcome.fault.inj (terminalValue_injective equal))

/-- Cyclic presentations remain equivalent at the declared observation. -/
theorem outcome_cycle_eq (outcome : Outcome.{u}) :
    presented.decorate (PresentedLabels.loopRel outcome) PUnit.unit =
      presented.decorate (PresentedLabels.twoCycleRel outcome) ⟨false⟩ :=
  presented.loop_eq_twoCycle outcome

/-- Cycles with different outcome readings remain distinct. -/
theorem outcome_cycles_ne {first second : Outcome.{u}} (different : first ≠ second) :
    presented.decorate (PresentedLabels.loopRel first) PUnit.unit ≠
      presented.decorate (PresentedLabels.loopRel second) PUnit.unit := by
  intro equal
  exact different (reading_injective ((presented.loop_eq_iff_reading_eq first second).mp equal))

end OutcomeLabels

end Mettapedia.TypeTheory.MaterialSets.Hypersets
