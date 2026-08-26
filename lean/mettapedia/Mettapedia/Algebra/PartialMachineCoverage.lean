import Mathlib.Tactic

/-!
# Partial machine coverage over an ordered-successor coalgebra

A language's operational semantics is a coalgebra: a state is carried to its
successors.  Reading the successor structure as a *powerset* coalgebra keeps
branching, and coalgebraic equivalence there is strong bisimulation; reading it
through the monad's Kleisli category instead gives traces, and the two readings
must not be collapsed.  Here successors are carried by `List`, which keeps both
order and multiplicity, so the observable is the ordered answer bag rather than
a set of reachable answers.

An abstract machine is a second coalgebra with a decoding back to language
states.  This file separates two very different notions of "the machine covers
this program":

* **Closure.** The admitted states form a sub-coalgebra: successors of admitted
  states are admitted.  A machine whose instruction set is closed under the
  fragment needs no escape at all.
* **Partial coverage.** The admitted states are an arbitrary subobject, and at
  the boundary the machine decodes its state and hands control back to the
  reference semantics.

The main theorem is that **closure is not required for correctness**: soundness
at admitted states alone already makes hybrid execution agree with the reference
everywhere.  Demanding closure is therefore strictly stronger than soundness
needs, and a machine that demands it before executing anything can only ever
report full coverage or none — which is the formal reason an all-or-nothing
admission test produces a two-valued coverage map, independent of how general
its underlying operations are.

The cost side then makes coverage a spectrum: hybrid cost decreases
monotonically as more states are admitted, so partial admission is worth having
even when closure is unreachable.

The abstraction is not about compilation in particular.  The same shape governs
any local structure that must earn a global permission.  A collector safe-point
predicate of the form "collect only at the outermost frame" is a whole-program
condition and admits exactly one collection per run; replacing it with a local
per-frame licence — each suspended frame independently declaring its complete
moving roots, and the chain checked compositionally — is the same passage from a
two-valued condition to a spectrum, and yields many bounded collections instead
of one unbounded one.  Instruction admission and collection safe points are two
instances of one theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.PartialMachineCoverage

universe u v

/-- Reference operational semantics: each state carries its successors in
order, so multiplicity and ordering are part of the observable. -/
structure Coalg (X : Type u) where
  step : X → List X

/-- A machine over its own carrier, with a decoding back to language states.
`step y = none` means the machine has no instruction for this state; it is a
*residual*, not an error. -/
structure Machine (X : Type u) (Y : Type v) where
  step : Y → Option (List Y)
  decode : Y → X

namespace Machine

variable {X : Type u} {Y : Type v}

/-- The machine admits a state when it has an instruction for it. -/
def Admits (m : Machine X Y) (y : Y) : Prop := (m.step y).isSome

/-- Soundness **only where admitted**: whenever the machine does step, decoding
its successors reproduces the reference successors, in order. -/
def SoundOnAdmitted (c : Coalg X) (m : Machine X Y) : Prop :=
  ∀ y ys, m.step y = some ys → (ys.map m.decode) = c.step (m.decode y)

/-- Hybrid execution: the machine where it has an instruction, the reference
semantics on the decoded state where it does not. -/
def hybridStep (c : Coalg X) (m : Machine X Y) (y : Y) : List X :=
  match m.step y with
  | some ys => ys.map m.decode
  | none => c.step (m.decode y)

/-! ## Closure is not required -/

/-- **Main theorem.**  Soundness at admitted states alone makes hybrid execution
agree with the reference semantics at *every* state, admitted or not.  No
closure condition on the admitted set is needed, and the ordered successor list
— hence multiplicity and order — is reproduced exactly. -/
theorem hybridStep_eq_reference
    (c : Coalg X) (m : Machine X Y) (sound : SoundOnAdmitted c m) (y : Y) :
    m.hybridStep c y = c.step (m.decode y) := by
  unfold hybridStep
  cases h : m.step y with
  | none => simp
  | some ys => simpa [h] using sound y ys h

/-- The admitted set forms a sub-coalgebra — the "closed instruction set" case,
where the machine never needs to hand control back. -/
def Closed (m : Machine X Y) : Prop :=
  ∀ y ys, m.step y = some ys → ∀ y' ∈ ys, m.Admits y'

/-- Closure is sufficient but, by `hybridStep_eq_reference`, never necessary:
a sound machine is correct whether or not it is closed. -/
theorem correct_without_closure
    (c : Coalg X) (m : Machine X Y) (sound : SoundOnAdmitted c m) :
    (∀ y, m.hybridStep c y = c.step (m.decode y)) ∧
      ¬ (Closed m → ∀ y, m.hybridStep c y = c.step (m.decode y)) → False := by
  rintro ⟨-, hneg⟩
  exact hneg (fun _ y => hybridStep_eq_reference c m sound y)

/-! ## Why an all-or-nothing admission test yields a two-valued coverage map -/

/-- A *whole-program* admission test refuses to execute unless every state it
could reach is admitted.  Formally it only ever accepts a closed admitted set. -/
def WholeProgramAdmission (m : Machine X Y) : Prop :=
  Closed m ∨ ∀ y, ¬ m.Admits y

/-- **Under whole-program admission no transition may cross the boundary.**
Either every successor of an admitted state is admitted, or nothing is admitted
at all.  The intermediate case — some states executed by the machine, others
handed back — is excluded by construction, so coverage is two-valued however
general the machine's operations happen to be. -/
theorem wholeProgram_excludes_boundary
    (m : Machine X Y) (h : WholeProgramAdmission m)
    (y : Y) (ys : List Y) (hstep : m.step y = some ys)
    (y' : Y) (hmem : y' ∈ ys) :
    m.Admits y' := by
  rcases h with hclosed | hnone
  · exact hclosed y ys hstep y' hmem
  · exact absurd hstep (by
      have hy := hnone y
      unfold Admits at hy
      intro hc
      rw [hc] at hy
      simp at hy)

/-! ## The observable is ordered, and collapsing it changes the language -/

/-- Forgetting order and multiplicity: the trace-style reading. -/
def observedSet (l : List X) : Set X := {x | x ∈ l}

/-- **Guard.**  Two successor structures can agree as sets while differing as
ordered bags, so an optimization justified by set-equality is not justified for
this semantics.  Order alone already separates them; duplication separates them
again. -/
theorem ordered_observable_is_finer :
    ∃ l₁ l₂ : List Bool,
      observedSet l₁ = observedSet l₂ ∧ l₁ ≠ l₂ := by
  refine ⟨[true, false], [false, true], ?_, by simp⟩
  ext b; cases b <;> simp [observedSet]

/-- Multiplicity is likewise invisible to the set reading. -/
theorem multiplicity_invisible_to_set :
    ∃ l₁ l₂ : List Bool,
      observedSet l₁ = observedSet l₂ ∧ l₁.length ≠ l₂.length := by
  refine ⟨[true], [true, true], ?_, by simp⟩
  ext b; cases b <;> simp [observedSet]

/-! ## Coverage as a spectrum -/

/-- A cost model over a finite state census: admitted states cost
`machineCost`, residual states cost `referenceCost`. -/
structure CostModel where
  machineCost : ℕ
  referenceCost : ℕ
  machine_cheaper : machineCost ≤ referenceCost

/-- Total cost of a census of `total` states of which `admitted` are executed
by the machine. -/
def hybridCost (k : CostModel) (total admitted : ℕ) : ℕ :=
  admitted * k.machineCost + (total - admitted) * k.referenceCost

/-- **Spectrum theorem.**  Admitting one more state never increases cost, so
partial coverage is worth having at every level and there is no threshold below
which admitting states is pointless. -/
theorem hybridCost_antitone
    (k : CostModel) (total admitted : ℕ) (h : admitted < total) :
    hybridCost k total (admitted + 1) ≤ hybridCost k total admitted := by
  unfold hybridCost
  have hsub : total - admitted = (total - (admitted + 1)) + 1 := by omega
  rw [hsub, Nat.succ_mul, Nat.add_mul, Nat.one_mul]
  have hcheap := k.machine_cheaper
  omega

/-- At full coverage the reference cost disappears entirely; at zero coverage
the machine contributes nothing.  These are the two endpoints an all-or-nothing
admission test restricts execution to. -/
theorem hybridCost_endpoints (k : CostModel) (total : ℕ) :
    hybridCost k total 0 = total * k.referenceCost ∧
      hybridCost k total total = total * k.machineCost := by
  constructor <;> simp [hybridCost]

end Machine

end Mettapedia.Algebra.PartialMachineCoverage
