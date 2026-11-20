import Mettapedia.Machines.PortfolioReach.Program
import Mathlib.Data.List.GetD

/-!
# Raise-freedom by entry typing

A slot is a relation's parameter or its answer. A taint is a set of slots that may hold a
non-integer. Under a taint each value of an activation has a kind, integer or unknown
(`kindOf`): a parameter by its slot, a primitive's value is an integer, a call's value by the
callee's answer slot, a read's value by `rowKind` of its space, a literal by itself.

The invariant (`Invariant`) is a taint that is

* closed (`TaintClosed`): a call passes an integer wherever the callee's parameter is untainted, an
  equation answers an integer wherever its relation's answer is untainted, and the take's own
  call passes its arguments so; and
* checked (`checked`): every primitive reads integers (`%` also a nonzero literal divisor;
  `/` never), every order compares integers, and no goal writes.

Results:

* `invariant_quiet`: under the invariant no effect and no raise is reachable from the take, so
  no bound prunes one, and the portfolio's law (`admitted_portfolio`) is the law it had before
  arithmetic and reads were admitted.
* `admits_iff`: `admits`, which iterates the taint operator from the empty taint and checks under
  its least fixed point, decides the invariant.
* `lfp_stable`: the iteration is stable after as many rounds as there are slots
  (`universe_card_le`); each round is one pass over the program.

Controls: a division (`Controls.division_rejected`, `Controls.division_raises`), a comparison of a
symbol, a parameter one call site passes a symbol to, an operand read from a space row, a raise
that pruning skips (`Controls.skipped_raise`), and the measured arithmetic loop, admitted and
answered (`Controls.arithmetic_loop`).
-/

set_option autoImplicit false

namespace Mettapedia.Machines.PortfolioReach

open Mettapedia.Machines.BoundedSearchPortfolio (Origin BatchMeaning)

/-! ## Slots, kinds and taints -/

inductive Slot where
  | param (relation index : Nat)
  | result (relation : Nat)
  deriving DecidableEq, Repr

/-- The slots that may hold a non-integer. -/
abbrev Taint := Finset Slot

/-- `true` when the operand is known to hold an integer. -/
def kindOf (kinds : List Bool) : Operand → Bool
  | .var index => kinds.getD index false
  | .lit value => value.isInt

/-- The kinds a goal pushes. -/
def pushes (taint : Taint) (rowKind : Nat → Bool) : Goal → List Bool
  | .prim .. => [true]
  | .test .. => []
  | .call relation _ => [decide (Slot.result relation ∉ taint)]
  | .read space => [rowKind space]
  | .write .. => []

def nonzeroLiteral : Operand → Bool
  | .lit (.int value) => decide (value ≠ 0)
  | _ => false

/-- A goal that cannot raise or write, given the kinds before it. -/
def safe (kinds : List Bool) : Goal → Bool
  | .prim .add left right | .prim .sub left right | .prim .mul left right
  | .prim .min left right | .prim .max left right => kindOf kinds left && kindOf kinds right
  | .prim .mod left right => kindOf kinds left && nonzeroLiteral right
  | .prim .div _ _ => false
  | .test .eq _ _ => true
  | .test _ left right => kindOf kinds left && kindOf kinds right
  | .call .. => true
  | .read _ => true
  | .write .. => false

/-- The parameters a call passes a possibly non-integer value to. -/
def callTaints (kinds : List Bool) : Goal → List Slot
  | .call relation arguments =>
      (List.range arguments.length).filterMap fun index =>
        if kindOf kinds (arguments.getD index (.lit (.sym 0))) then none
        else some (.param relation index)
  | _ => []

/-- The slots the rest of an equation of `own` taints. -/
def taints (taint : Taint) (rowKind : Nat → Bool) (own : Nat) :
    List Bool → List Goal → Operand → List Slot
  | kinds, [], result => if kindOf kinds result then [] else [.result own]
  | kinds, goal :: goals, result =>
      callTaints kinds goal ++ taints taint rowKind own (kinds ++ pushes taint rowKind goal) goals result

/-- Every goal of the rest of an equation is safe. -/
def checks (taint : Taint) (rowKind : Nat → Bool) : List Bool → List Goal → Bool
  | _, [] => true
  | kinds, goal :: goals =>
      safe kinds goal && checks taint rowKind (kinds ++ pushes taint rowKind goal) goals

def paramKinds (taint : Taint) (relation arity : Nat) : List Bool :=
  (List.range arity).map fun index => decide (Slot.param relation index ∉ taint)

/-- Every equation, with its relation and the relation's arity. -/
def allEquations (program : Program) : List (Nat × Nat × Equation) :=
  (List.range program.length).flatMap fun index =>
    match program[index]? with
    | some relation => relation.equations.map fun equation => (index, relation.arity, equation)
    | none => []

/-- The taint operator. -/
def taintStep (program : Program) (rowKind : Nat → Bool) (taint : Taint) : Taint :=
  ((allEquations program).flatMap fun entry =>
    taints taint rowKind entry.1 (paramKinds taint entry.1 entry.2.1) entry.2.2.goals
      entry.2.2.result).toFinset

def TaintClosed (program : Program) (rowKind : Nat → Bool) (taint : Taint) : Prop :=
  taintStep program rowKind taint ⊆ taint

def checked (program : Program) (rowKind : Nat → Bool) (taint : Taint) : Bool :=
  (allEquations program).all fun entry =>
    checks taint rowKind (paramKinds taint entry.1 entry.2.1) entry.2.2.goals

/-- The take's own call, as one more relation after the program. -/
def rootRelation (entry : Nat) (arguments : List Val) : Relation :=
  ⟨0, [⟨[.call entry (arguments.map .lit)], .var 0⟩]⟩

def withRoot (program : Program) (entry : Nat) (arguments : List Val) : Program :=
  program ++ [rootRelation entry arguments]

/-- **The invariant**: a closed taint under which every goal is safe. -/
def Invariant (program : Program) (rowKind : Nat → Bool) (entry : Nat) (arguments : List Val) :
    Prop :=
  ∃ taint, TaintClosed (withRoot program entry arguments) rowKind taint ∧
    checked (withRoot program entry arguments) rowKind taint = true

/-! ## The fixed-point computation -/

def callSlots : Goal → List Slot
  | .call relation arguments => (List.range arguments.length).map (.param relation)
  | _ => []

/-- Every slot an equation of `own` could taint. -/
def slotsOf (own : Nat) : List Goal → List Slot
  | [] => [.result own]
  | goal :: goals => callSlots goal ++ slotsOf own goals

def slotUniverse (program : Program) : Finset Slot :=
  ((allEquations program).flatMap fun entry => slotsOf entry.1 entry.2.2.goals).toFinset

/-- The least closed taint, by iteration from the empty one. -/
def lfp (program : Program) (rowKind : Nat → Bool) : Taint :=
  (taintStep program rowKind)^[(slotUniverse program).card] ∅

/-- **The decision**: check under the least closed taint. -/
def admits (program : Program) (rowKind : Nat → Bool) (entry : Nat) (arguments : List Val) : Bool :=
  checked (withRoot program entry arguments) rowKind (lfp (withRoot program entry arguments) rowKind)

/-- `low` knows no more integers than `high`. -/
def KindsLe (low high : List Bool) : Prop :=
  low.length = high.length ∧ ∀ index, low.getD index false = true → high.getD index false = true

theorem KindsLe.refl (kinds : List Bool) : KindsLe kinds kinds := ⟨rfl, fun _ known => known⟩

theorem KindsLe.append {a b c d : List Bool} (first : KindsLe a b) (second : KindsLe c d) :
    KindsLe (a ++ c) (b ++ d) := by
  refine ⟨by simp [first.1, second.1], fun index known => ?_⟩
  by_cases inside : index < a.length
  · rw [List.getD_append _ _ _ _ inside] at known
    rw [List.getD_append _ _ _ _ (by rw [← first.1]; exact inside)]
    exact first.2 index known
  · have outside : a.length ≤ index := Nat.le_of_not_lt inside
    rw [List.getD_append_right _ _ _ _ outside] at known
    rw [List.getD_append_right _ _ _ _ (by rw [← first.1]; exact outside), ← first.1]
    exact second.2 _ known

theorem kindOf_mono {low high : List Bool} (le : KindsLe low high) {operand : Operand}
    (known : kindOf low operand = true) : kindOf high operand = true := by
  cases operand with
  | var index => exact le.2 index known
  | lit value => exact known

theorem pushes_mono {taint taint' : Taint} (sub : taint ⊆ taint') (rowKind : Nat → Bool)
    (goal : Goal) : KindsLe (pushes taint' rowKind goal) (pushes taint rowKind goal) := by
  cases goal with
  | call relation arguments =>
      refine ⟨rfl, fun index known => ?_⟩
      cases index with
      | zero =>
          simp only [pushes, List.getD_cons_zero, decide_eq_true_eq] at known ⊢
          exact fun inside => known (sub inside)
      | succ index => simp [pushes] at known
  | prim => exact KindsLe.refl _
  | test => exact KindsLe.refl _
  | read => exact KindsLe.refl _
  | write => exact KindsLe.refl _

theorem paramKinds_length (taint : Taint) (relation arity : Nat) :
    (paramKinds taint relation arity).length = arity := by
  simp [paramKinds]

theorem paramKinds_getD (taint : Taint) (relation arity index : Nat) :
    (paramKinds taint relation arity).getD index false =
      decide (index < arity ∧ Slot.param relation index ∉ taint) := by
  by_cases inside : index < arity
  · simp [paramKinds, List.getD_eq_getElem?_getD, inside]
  · rw [List.getD_eq_default _ _ (by rw [paramKinds_length]; exact Nat.le_of_not_lt inside)]
    simp [inside]

theorem paramKinds_mono {taint taint' : Taint} (sub : taint ⊆ taint') (relation arity : Nat) :
    KindsLe (paramKinds taint' relation arity) (paramKinds taint relation arity) := by
  refine ⟨by simp [paramKinds_length], fun index known => ?_⟩
  rw [paramKinds_getD] at known ⊢
  simp only [decide_eq_true_eq] at known ⊢
  exact ⟨known.1, fun inside => known.2 (sub inside)⟩

theorem callTaints_mono {low high : List Bool} (le : KindsLe low high) {goal : Goal}
    {slot : Slot} (member : slot ∈ callTaints high goal) : slot ∈ callTaints low goal := by
  cases goal with
  | call relation arguments =>
      simp only [callTaints, List.mem_filterMap, List.mem_range] at member ⊢
      obtain ⟨index, inside, picked⟩ := member
      refine ⟨index, inside, ?_⟩
      have unknown : kindOf high (arguments.getD index (.lit (.sym 0))) = false := by
        cases known : kindOf high (arguments.getD index (.lit (.sym 0))) with
        | false => rfl
        | true => rw [known] at picked; simp at picked
      have lowUnknown : kindOf low (arguments.getD index (.lit (.sym 0))) = false := by
        cases lowKnown : kindOf low (arguments.getD index (.lit (.sym 0))) with
        | false => rfl
        | true =>
            have raised := kindOf_mono le lowKnown
            rw [unknown] at raised
            cases raised
      rw [unknown] at picked
      rw [lowUnknown]
      exact picked
  | prim => simp [callTaints] at member
  | test => simp [callTaints] at member
  | read => simp [callTaints] at member
  | write => simp [callTaints] at member

theorem taints_mono {taint taint' : Taint} (sub : taint ⊆ taint') (rowKind : Nat → Bool)
    (own : Nat) : ∀ (goals : List Goal) (low high : List Bool) (result : Operand),
      KindsLe low high → ∀ slot ∈ taints taint rowKind own high goals result,
        slot ∈ taints taint' rowKind own low goals result
  | [], low, high, result, le, slot, member => by
      simp only [taints] at member ⊢
      cases known : kindOf high result with
      | true => rw [known] at member; simp at member
      | false =>
          cases lowKnown : kindOf low result with
          | true =>
              have raised := kindOf_mono le lowKnown
              rw [known] at raised
              cases raised
          | false =>
              rw [known] at member
              exact member
  | goal :: goals, low, high, result, le, slot, member => by
      simp only [taints, List.mem_append] at member ⊢
      rcases member with here | later
      · exact Or.inl (callTaints_mono le here)
      · exact Or.inr (taints_mono sub rowKind own goals _ _ result
          (le.append (pushes_mono sub rowKind goal)) slot later)

theorem taints_slots (taint : Taint) (rowKind : Nat → Bool) (own : Nat) :
    ∀ (goals : List Goal) (kinds : List Bool) (result : Operand),
      ∀ slot ∈ taints taint rowKind own kinds goals result, slot ∈ slotsOf own goals
  | [], kinds, result, slot, member => by
      simp only [taints, slotsOf] at member ⊢
      split at member <;> simp_all
  | goal :: goals, kinds, result, slot, member => by
      simp only [taints, slotsOf, List.mem_append] at member ⊢
      rcases member with here | later
      · left
        cases goal with
        | call relation arguments =>
            simp only [callTaints, List.mem_filterMap, List.mem_range] at here
            obtain ⟨index, inside, picked⟩ := here
            simp only [callSlots, List.mem_map, List.mem_range]
            refine ⟨index, inside, ?_⟩
            split at picked <;> simp_all
        | prim => simp [callTaints] at here
        | test => simp [callTaints] at here
        | read => simp [callTaints] at here
        | write => simp [callTaints] at here
      · exact Or.inr (taints_slots taint rowKind own goals _ result slot later)

theorem taintStep_mono (program : Program) (rowKind : Nat → Bool) {taint taint' : Taint}
    (sub : taint ⊆ taint') : taintStep program rowKind taint ⊆ taintStep program rowKind taint' := by
  intro slot member
  simp only [taintStep, List.mem_toFinset, List.mem_flatMap] at member ⊢
  obtain ⟨entry, listed, tainted⟩ := member
  exact ⟨entry, listed, taints_mono sub rowKind entry.1 entry.2.2.goals _ _ entry.2.2.result
    (paramKinds_mono sub entry.1 entry.2.1) slot tainted⟩

theorem taintStep_universe (program : Program) (rowKind : Nat → Bool) (taint : Taint) :
    taintStep program rowKind taint ⊆ slotUniverse program := by
  intro slot member
  simp only [taintStep, slotUniverse, List.mem_toFinset, List.mem_flatMap] at member ⊢
  obtain ⟨entry, listed, tainted⟩ := member
  exact ⟨entry, listed, taints_slots taint rowKind entry.1 entry.2.2.goals _ entry.2.2.result
    slot tainted⟩

section Iteration

variable {α : Type*}

theorem iterate_chain (F : Finset α → Finset α) (mono : ∀ X Y, X ⊆ Y → F X ⊆ F Y) :
    ∀ k, F^[k] ∅ ⊆ F^[k + 1] ∅
  | 0 => Finset.empty_subset _
  | k + 1 => by
      have grown := mono _ _ (iterate_chain F mono k)
      rwa [← Function.iterate_succ_apply' F k, ← Function.iterate_succ_apply' F (k + 1)] at grown

theorem iterate_card (F : Finset α → Finset α) (mono : ∀ X Y, X ⊆ Y → F X ⊆ F Y) :
    ∀ k, (∀ j < k, F^[j] ∅ ≠ F^[j + 1] ∅) → k ≤ (F^[k] ∅).card
  | 0, _ => Nat.zero_le _
  | k + 1, moving => by
      have earlier := iterate_card F mono k fun j small => moving j (by omega)
      have grows : (F^[k] ∅).card < (F^[k + 1] ∅).card := by
        by_contra notLess
        exact moving k (by omega)
          (Finset.eq_of_subset_of_card_le (iterate_chain F mono k) (by omega))
      omega

/-- A monotone operator bounded by `U` is stable after `U.card` rounds from the empty set. -/
theorem iterate_stable (F : Finset α → Finset α) (mono : ∀ X Y, X ⊆ Y → F X ⊆ F Y)
    (U : Finset α) (bounded : ∀ X, F X ⊆ U) : F (F^[U.card] ∅) = F^[U.card] ∅ := by
  have frozen : ∀ j, F^[j] ∅ = F^[j + 1] ∅ → ∀ m, j ≤ m → F^[m] ∅ = F^[m + 1] ∅ := by
    intro j same m le
    induction le with
    | refl => exact same
    | step _ ih =>
        rw [Function.iterate_succ_apply' F, Function.iterate_succ_apply' F (_ + 1), ← ih]
  by_contra moved
  have moving : ∀ j < U.card + 1, F^[j] ∅ ≠ F^[j + 1] ∅ := by
    intro j small same
    apply moved
    have stays := frozen j same U.card (by omega)
    rw [Function.iterate_succ_apply'] at stays
    exact stays.symm
  have big := iterate_card F mono (U.card + 1) moving
  have small : (F^[U.card + 1] ∅).card ≤ U.card := by
    rw [Function.iterate_succ_apply']
    exact Finset.card_le_card (bounded _)
  omega

/-- Every closed set contains every iterate from the empty set. -/
theorem iterate_least (F : Finset α → Finset α) (mono : ∀ X Y, X ⊆ Y → F X ⊆ F Y)
    (Y : Finset α) (closed : F Y ⊆ Y) : ∀ k, F^[k] ∅ ⊆ Y
  | 0 => Finset.empty_subset _
  | k + 1 => by
      rw [Function.iterate_succ_apply']
      exact (mono _ _ (iterate_least F mono Y closed k)).trans closed

end Iteration

/-- **Cost of the decision.** The iteration is stable after `(slotUniverse program).card` rounds, one
pass over the program each, and the check is one pass more. -/
theorem lfp_stable (program : Program) (rowKind : Nat → Bool) :
    taintStep program rowKind (lfp program rowKind) = lfp program rowKind :=
  iterate_stable _ (fun _ _ sub => taintStep_mono program rowKind sub) _
    (taintStep_universe program rowKind)

/-- The slots are at most one per call-argument position and one per equation. -/
theorem universe_card_le (program : Program) :
    (slotUniverse program).card ≤
      ((allEquations program).flatMap fun entry => slotsOf entry.1 entry.2.2.goals).length :=
  List.toFinset_card_le _

theorem lfp_closed (program : Program) (rowKind : Nat → Bool) :
    TaintClosed program rowKind (lfp program rowKind) := by
  unfold TaintClosed
  rw [lfp_stable]

theorem lfp_least (program : Program) (rowKind : Nat → Bool) {taint : Taint}
    (closed : TaintClosed program rowKind taint) : lfp program rowKind ⊆ taint :=
  iterate_least _ (fun _ _ sub => taintStep_mono program rowKind sub) taint closed _

theorem safe_mono {low high : List Bool} (le : KindsLe low high) {goal : Goal}
    (isSafe : safe low goal = true) : safe high goal = true := by
  cases goal with
  | prim op left right =>
      cases op <;> simp only [safe, Bool.and_eq_true] at isSafe ⊢
      all_goals first
        | exact ⟨kindOf_mono le isSafe.1, kindOf_mono le isSafe.2⟩
        | exact ⟨kindOf_mono le isSafe.1, isSafe.2⟩
        | exact isSafe
  | test op left right =>
      cases op <;> simp only [safe, Bool.and_eq_true] at isSafe ⊢
      all_goals exact ⟨kindOf_mono le isSafe.1, kindOf_mono le isSafe.2⟩
  | call => rfl
  | read => rfl
  | write => exact isSafe

theorem checks_mono {taint taint' : Taint} (sub : taint ⊆ taint') (rowKind : Nat → Bool) :
    ∀ (goals : List Goal) (low high : List Bool), KindsLe low high →
      checks taint' rowKind low goals = true → checks taint rowKind high goals = true
  | [], _, _, _, _ => rfl
  | goal :: goals, low, high, le, passes => by
      simp only [checks, Bool.and_eq_true] at passes ⊢
      exact ⟨safe_mono le passes.1, checks_mono sub rowKind goals _ _
        (le.append (pushes_mono sub rowKind goal)) passes.2⟩

/-- **The computation decides the invariant.** -/
theorem admits_iff (program : Program) (rowKind : Nat → Bool) (entry : Nat)
    (arguments : List Val) :
    admits program rowKind entry arguments = true ↔ Invariant program rowKind entry arguments := by
  constructor
  · intro admitted
    exact ⟨_, lfp_closed _ rowKind, admitted⟩
  · rintro ⟨taint, closed, passes⟩
    have least := lfp_least _ rowKind closed
    simp only [admits, checked, List.all_eq_true] at passes ⊢
    intro entry listed
    exact checks_mono least rowKind _ _ _ (paramKinds_mono least entry.1 entry.2.1)
      (passes entry listed)

/-! ## Soundness: a typed stack never raises or writes -/

/-- The values of an activation have the kinds they are given. -/
def Agree (env : List Val) (kinds : List Bool) : Prop :=
  env.length = kinds.length ∧
    ∀ index, kinds.getD index false = true → (env.getD index (.sym 0)).isInt = true

theorem Agree.append {env : List Val} {kinds : List Bool} (agree : Agree env kinds)
    {value : Val} {kind : Bool} (fits : kind = true → value.isInt = true) :
    Agree (env ++ [value]) (kinds ++ [kind]) := by
  refine ⟨by simp [agree.1], fun index known => ?_⟩
  by_cases inside : index < kinds.length
  · rw [List.getD_append _ _ _ _ inside] at known
    rw [List.getD_append _ _ _ _ (by rw [agree.1]; exact inside)]
    exact agree.2 index known
  · have outside : kinds.length ≤ index := Nat.le_of_not_lt inside
    rw [List.getD_append_right _ _ _ _ outside] at known
    rw [List.getD_append_right _ _ _ _ (by rw [agree.1]; exact outside), agree.1]
    cases offset : index - kinds.length with
    | zero =>
        rw [offset] at known
        simpa using fits (by simpa using known)
    | succ more =>
        rw [offset] at known
        simp at known

theorem Agree.eval {env : List Val} {kinds : List Bool} (agree : Agree env kinds)
    {operand : Operand} (known : kindOf kinds operand = true) :
    (operand.eval env).isInt = true := by
  cases operand with
  | var index => exact agree.2 index known
  | lit value => exact known

theorem safe_prim {kinds : List Bool} {env : List Val} (agree : Agree env kinds) {op : Prim}
    {left right : Operand} (isSafe : safe kinds (.prim op left right) = true) :
    ∃ c, runPrim op (left.eval env) (right.eval env) = .ok (.int c) := by
  cases op
  case div => simp [safe] at isSafe
  case mod =>
    simp only [safe, Bool.and_eq_true] at isSafe
    obtain ⟨leftKnown, divisor⟩ := isSafe
    obtain ⟨a, ha⟩ := (Val.isInt_iff _).mp (agree.eval leftKnown)
    cases right with
    | var index => simp [nonzeroLiteral] at divisor
    | lit value =>
        cases value with
        | sym name => simp [nonzeroLiteral] at divisor
        | int n =>
            have nonzero : n ≠ 0 := by simpa [nonzeroLiteral] using divisor
            exact ⟨_, by rw [ha]; exact mod_int a nonzero⟩
  all_goals
    simp only [safe, Bool.and_eq_true] at isSafe
    obtain ⟨a, ha⟩ := (Val.isInt_iff _).mp (agree.eval isSafe.1)
    obtain ⟨b, hb⟩ := (Val.isInt_iff _).mp (agree.eval isSafe.2)
    rw [ha, hb]
    exact total_int rfl a b

theorem safe_test {kinds : List Bool} {env : List Val} (agree : Agree env kinds) {op : Cmp}
    {left right : Operand} (isSafe : safe kinds (.test op left right) = true) :
    ∃ truth, runCmp op (left.eval env) (right.eval env) = .ok truth := by
  cases op
  case eq => exact ⟨_, eq_total _ _⟩
  all_goals
    simp only [safe, Bool.and_eq_true] at isSafe
    obtain ⟨a, ha⟩ := (Val.isInt_iff _).mp (agree.eval isSafe.1)
    obtain ⟨b, hb⟩ := (Val.isInt_iff _).mp (agree.eval isSafe.2)
    rw [ha, hb]
    exact cmp_int _ a b

/-- A frame of relation `own`: its values have kinds under which its remaining goals are safe
and taint nothing outside the taint. -/
def FrameOK (taint : Taint) (rowKind : Nat → Bool) (frame : Frame) (own : Nat) : Prop :=
  ∃ kinds, Agree frame.env kinds ∧ checks taint rowKind kinds frame.goals = true ∧
    ∀ slot ∈ taints taint rowKind own kinds frame.goals frame.result, slot ∈ taint

/-- A stack whose every frame is typed, each waiting caller for a value of its callee's kind. -/
inductive StackOK (taint : Taint) (rowKind : Nat → Bool) : List Frame → Prop
  | root {frame : Frame} {own : Nat} : FrameOK taint rowKind frame own →
      StackOK taint rowKind [frame]
  | call {frame caller : Frame} {below : List Frame} {own : Nat} :
      FrameOK taint rowKind frame own →
      (∀ value : Val, (Slot.result own ∉ taint → value.isInt = true) →
        StackOK taint rowKind ({ caller with env := caller.env ++ [value] } :: below)) →
      StackOK taint rowKind (frame :: caller :: below)

theorem StackOK.top {taint : Taint} {rowKind : Nat → Bool} {frame : Frame}
    {rest : List Frame} (ok : StackOK taint rowKind (frame :: rest)) :
    ∃ own, FrameOK taint rowKind frame own ∧
      ∀ frame', FrameOK taint rowKind frame' own → StackOK taint rowKind (frame' :: rest) := by
  cases ok with
  | root framed => exact ⟨_, framed, fun _ framed' => .root framed'⟩
  | call framed continues => exact ⟨_, framed, fun _ framed' => .call framed' continues⟩

/-- Every equation of the program is typed under the taint. -/
def Typed (program : Program) (rowKind : Nat → Bool) (taint : Taint) : Prop :=
  ∀ relation callee equation, program[relation]? = some callee → equation ∈ callee.equations →
    checks taint rowKind (paramKinds taint relation callee.arity) equation.goals = true ∧
      ∀ slot ∈ taints taint rowKind relation (paramKinds taint relation callee.arity)
        equation.goals equation.result, slot ∈ taint

/-- The rows of a space read as integers are integers. -/
def RowsInt (rowKind : Nat → Bool) (store : Store) : Prop :=
  ∀ space, rowKind space = true → ∀ row ∈ store space, row.isInt = true

theorem Move.eq_branch {S : Type*} {A : Type*} {E : Type*} {move : Move S A E}
    (quiet : move.quiet = true) {children : List S} (stepped : move.step = .branch children) :
    move = .branch children := by
  cases move <;> simp_all [Move.quiet, Move.step]

/-- **Preservation.** A typed stack steps quietly to typed stacks. -/
theorem preserve {program : Program} {rowKind : Nat → Bool} {store : Store} {taint : Taint}
    (typed : Typed program rowKind taint) (rows : RowsInt rowKind store) {state : List Frame}
    (ok : StackOK taint rowKind state) :
    (stepFrames program store state).quiet = true ∧
      ∀ children, stepFrames program store state = .branch children →
        ∀ child ∈ children, StackOK taint rowKind child := by
  rcases state with _ | ⟨⟨env, goals, result⟩, rest⟩
  · cases ok
  obtain ⟨own, ⟨kinds, agree, passes, closed⟩, replace⟩ := ok.top
  cases goals with
  | nil =>
      cases rest with
      | nil => exact ⟨rfl, fun children stepped => by simp [stepFrames] at stepped⟩
      | cons caller below =>
          cases ok with
          | call framed continues =>
              obtain ⟨kinds', agree', _, closed'⟩ := framed
              refine ⟨rfl, fun children stepped child member => ?_⟩
              simp only [stepFrames, Move.branch.injEq] at stepped
              subst stepped
              simp only [List.mem_singleton] at member
              subst member
              apply continues
              intro clean
              apply agree'.eval
              by_contra unknown
              apply clean
              apply closed'
              simp [taints, unknown]
  | cons goal goals =>
      simp only [checks, Bool.and_eq_true] at passes
      obtain ⟨isSafe, passesRest⟩ := passes
      have closedRest : ∀ slot ∈ taints taint rowKind own (kinds ++ pushes taint rowKind goal)
          goals result, slot ∈ taint := fun slot member =>
        closed slot (by simp only [taints, List.mem_append]; exact Or.inr member)
      have closedCall : ∀ slot ∈ callTaints kinds goal, slot ∈ taint := fun slot member =>
        closed slot (by simp only [taints, List.mem_append]; exact Or.inl member)
      have next : ∀ (value : Val) (kind : Bool), pushes taint rowKind goal = [kind] →
          (kind = true → value.isInt = true) →
          StackOK taint rowKind (⟨env ++ [value], goals, result⟩ :: rest) := by
        intro value kind pushed fits
        apply replace
        refine ⟨kinds ++ [kind], agree.append fits, ?_, ?_⟩
        · rw [← pushed]; exact passesRest
        · rw [← pushed]; exact closedRest
      cases goal with
      | prim op left right =>
          obtain ⟨c, ran⟩ := safe_prim agree isSafe
          refine ⟨by simp [stepFrames, ran, Move.quiet], fun children stepped child member => ?_⟩
          simp only [stepFrames, ran, Move.branch.injEq] at stepped
          subst stepped
          simp only [List.mem_singleton] at member
          subst member
          exact next _ true rfl (fun _ => rfl)
      | test op left right =>
          obtain ⟨truth, ran⟩ := safe_test agree isSafe
          cases truth with
          | true =>
              refine ⟨by simp [stepFrames, ran, Move.quiet],
                fun children stepped child member => ?_⟩
              simp only [stepFrames, ran, Move.branch.injEq] at stepped
              subst stepped
              simp only [List.mem_singleton] at member
              subst member
              apply replace
              exact ⟨kinds, agree, by simpa [pushes] using passesRest,
                by simpa [pushes] using closedRest⟩
          | false =>
              refine ⟨by simp [stepFrames, ran, Move.quiet],
                fun children stepped child member => ?_⟩
              simp only [stepFrames, ran, Move.branch.injEq] at stepped
              subst stepped
              simp at member
      | call relation arguments =>
          cases found : program[relation]? with
          | none =>
              refine ⟨by simp [stepFrames, found, Move.quiet],
                fun children stepped child member => ?_⟩
              simp only [stepFrames, found, Move.branch.injEq] at stepped
              subst stepped
              simp at member
          | some callee =>
              by_cases arity : arguments.length = callee.arity
              · refine ⟨by simp [stepFrames, found, arity, Move.quiet],
                  fun children stepped child member => ?_⟩
                simp only [stepFrames, found, arity, if_true, Move.branch.injEq] at stepped
                subst stepped
                obtain ⟨equation, listed, rfl⟩ := List.mem_map.mp member
                obtain ⟨calleeChecks, calleeClosed⟩ := typed relation callee equation found listed
                refine StackOK.call (own := relation)
                  ⟨paramKinds taint relation callee.arity, ?_, calleeChecks, calleeClosed⟩ ?_
                · refine ⟨by simp [arity, paramKinds_length], fun index known => ?_⟩
                  rw [paramKinds_getD] at known
                  simp only [decide_eq_true_eq] at known
                  obtain ⟨inside, clean⟩ := known
                  have argumentKnown :
                      kindOf kinds (arguments.getD index (.lit (.sym 0))) = true := by
                    by_contra unknown
                    apply clean
                    apply closedCall
                    simp only [callTaints, List.mem_filterMap, List.mem_range]
                    exact ⟨index, by omega, by rw [if_neg unknown]⟩
                  have shifted : (arguments.map (Operand.eval env)).getD index (.sym 0) =
                      (arguments.getD index (.lit (.sym 0))).eval env :=
                    List.getD_map arguments (Operand.lit (.sym 0)) (Operand.eval env)
                  rw [shifted]
                  exact agree.eval argumentKnown
                · intro value fits
                  exact next value _ rfl (fun clean => fits (by simpa using clean))
              · refine ⟨by simp [stepFrames, found, arity, Move.quiet],
                  fun children stepped child member => ?_⟩
                simp only [stepFrames, found, arity, if_false, Move.branch.injEq] at stepped
                subst stepped
                simp at member
      | read space =>
          refine ⟨by simp [stepFrames, Move.quiet], fun children stepped child member => ?_⟩
          simp only [stepFrames, Move.branch.injEq] at stepped
          subst stepped
          obtain ⟨row, present, rfl⟩ := List.mem_map.mp member
          exact next row (rowKind space) rfl (fun known => rows space known row present)
      | write space row => simp [safe] at isSafe

/-- A typed stack is quiet: no effect and no raise is reachable from it. -/
theorem stack_quiet {program : Program} {rowKind : Nat → Bool} {store : Store} {taint : Taint}
    (typed : Typed program rowKind taint) (rows : RowsInt rowKind store) {start : List Frame}
    (ok : StackOK taint rowKind start) : Quiet (system program) store start := by
  have reach : ∀ state target, Reachable ((system program).space store) state target →
      StackOK taint rowKind state → StackOK taint rowKind target := by
    intro state target reached
    induction reached with
    | here => exact id
    | step expands member _ ih =>
        intro okState
        obtain ⟨quiet, children⟩ := preserve typed rows okState
        exact ih (children _ (Move.eq_branch quiet expands) _ member)
  intro state reached
  exact (preserve typed rows (reach _ _ reached ok)).1

theorem mem_allEquations {program : Program} {relation : Nat} {callee : Relation}
    {equation : Equation} (found : program[relation]? = some callee)
    (member : equation ∈ callee.equations) :
    (relation, callee.arity, equation) ∈ allEquations program := by
  obtain ⟨inside, _⟩ := List.getElem?_eq_some_iff.mp found
  simp only [allEquations, List.mem_flatMap, List.mem_range]
  refine ⟨relation, inside, ?_⟩
  rw [found]
  exact List.mem_map.mpr ⟨equation, member, rfl⟩

/-- **Raise-freedom.** Under the invariant, with read spaces typed by their rows, no effect and no
raise is reachable from the take: no bound prunes one. -/
theorem invariant_quiet {program : Program} {rowKind : Nat → Bool} {entry : Nat}
    {arguments : List Val} {store : Store} (invariant : Invariant program rowKind entry arguments)
    (rows : RowsInt rowKind store) : Quiet (system program) store (root entry arguments) := by
  obtain ⟨taint, closed, passes⟩ := invariant
  have typedAll : ∀ relation callee equation,
      (withRoot program entry arguments)[relation]? = some callee →
      equation ∈ callee.equations →
      checks taint rowKind (paramKinds taint relation callee.arity) equation.goals = true ∧
        ∀ slot ∈ taints taint rowKind relation (paramKinds taint relation callee.arity)
          equation.goals equation.result, slot ∈ taint := by
    intro relation callee equation found listed
    have member := mem_allEquations found listed
    refine ⟨?_, fun slot tainted => closed ?_⟩
    · simp only [checked, List.all_eq_true] at passes
      exact passes _ member
    · simp only [taintStep, List.mem_toFinset, List.mem_flatMap]
      exact ⟨_, member, tainted⟩
  have typed : Typed program rowKind taint := by
    intro relation callee equation found listed
    apply typedAll relation callee equation _ listed
    obtain ⟨inside, _⟩ := List.getElem?_eq_some_iff.mp found
    rw [withRoot, List.getElem?_append_left inside]
    exact found
  have rootFound : (withRoot program entry arguments)[program.length]? =
      some (rootRelation entry arguments) := by
    simp [withRoot]
  obtain ⟨rootChecks, rootClosed⟩ :=
    typedAll program.length _ _ rootFound (List.mem_singleton_self _)
  exact stack_quiet typed rows
    (.root (own := program.length) ⟨[], ⟨rfl, fun _ known => by simp at known⟩, rootChecks,
      rootClosed⟩)

theorem admits_quiet {program : Program} {rowKind : Nat → Bool} {entry : Nat}
    {arguments : List Val} {store : Store} (admitted : admits program rowKind entry arguments = true)
    (rows : RowsInt rowKind store) : Quiet (system program) store (root entry arguments) :=
  invariant_quiet ((admits_iff program rowKind entry arguments).mp admitted) rows

/-- **The widened fragment keeps the portfolio's law.** An admitted take leaves the world as it
was under every sequence of slices, and a published batch is a batch of the search read at the
entry store. -/
theorem admitted_portfolio {program : Program} {rowKind : Nat → Bool} {entry : Nat}
    {arguments : List Val} {store : Store} (admitted : admits program rowKind entry arguments = true)
    (rows : RowsInt rowKind store) (demand : Nat) (slices : List (Origin × Nat))
    (log : List Event) :
    (portfolio (system program) (root entry arguments) demand slices store log).world =
        ⟨store, log, none⟩ ∧
      ∀ answers, batch (portfolio (system program) (root entry arguments) demand slices store log) =
          some answers →
        BatchMeaning ((system program).space store) (root entry arguments) demand answers :=
  (portfolio_quiet _ (admits_quiet admitted rows) demand slices log).2

/-- And it publishes whenever some bound settles the demand. -/
theorem admitted_publishes {program : Program} {rowKind : Nat → Bool} {entry : Nat}
    {arguments : List Val} {store : Store} (admitted : admits program rowKind entry arguments = true)
    (rows : RowsInt rowKind store) (demand target : Nat)
    (decides : Decides ((system program).space store) (root entry arguments) demand target)
    (log : List Event) :
    ∃ count answers,
      batch (portfolio (system program) (root entry arguments) demand
          (rounds (doubling 1) count) store log) = some answers ∧
        BatchMeaning ((system program).space store) (root entry arguments) demand answers ∧
        (portfolio (system program) (root entry arguments) demand (rounds (doubling 1) count)
          store log).world = ⟨store, log, none⟩ :=
  portfolio_publishes _ (admits_quiet admitted rows) demand target decides log

namespace Controls

def noRows : Nat → Bool := fun _ => false

def emptyStore : Store := fun _ => []

/-- `(= (f $n) (/ 10 $n))`, taken on `0`. -/
def division : Program := [⟨1, [⟨[.prim .div (.lit (.int 10)) (.var 0)], .var 1⟩]⟩]

/-- **Division.** Every value is an integer (the least taint is empty), and `/` is still
refused: an integer divisor can be zero. -/
theorem division_rejected :
    lfp (withRoot division 0 [.int 0]) noRows = ∅ ∧ admits division noRows 0 [.int 0] = false := by
  decide

theorem division_raises : ¬ Quiet (system division) emptyStore (root 0 [.int 0]) :=
  not_quiet (state := [⟨[.int 0], [.prim .div (.lit (.int 10)) (.var 0)], .var 1⟩,
    ⟨[], [], .var 0⟩]) rfl (by decide) rfl

/-- `(= (f $n) (< $n 1))`. -/
def comparison : Program := [⟨1, [⟨[.test .lt (.var 0) (.lit (.int 1))], .var 0⟩]⟩]

/-- **Comparison of a symbol.** Taken on a symbol it is refused, on an integer admitted. -/
theorem comparison_of_symbol :
    admits comparison noRows 0 [.sym 0] = false ∧ admits comparison noRows 0 [.int 3] = true := by
  decide

theorem comparison_raises : ¬ Quiet (system comparison) emptyStore (root 0 [.sym 0]) :=
  not_quiet (state := [⟨[.sym 0], [.test .lt (.var 0) (.lit (.int 1))], .var 0⟩,
    ⟨[], [], .var 0⟩]) rfl (by decide) rfl

/-- `(= (g) (h 3))`, `(= (g) (h a))` and `(= (h $x) (+ $x 1))`. -/
def symbolArgument : Program :=
  [⟨0, [⟨[.call 1 [.lit (.int 3)]], .var 0⟩, ⟨[.call 1 [.lit (.sym 0)]], .var 0⟩]⟩,
    ⟨1, [⟨[.prim .add (.var 0) (.lit (.int 1))], .var 1⟩]⟩]

/-- The same program without the call site that passes the symbol. -/
def integerArgument : Program :=
  [⟨0, [⟨[.call 1 [.lit (.int 3)]], .var 0⟩]⟩,
    ⟨1, [⟨[.prim .add (.var 0) (.lit (.int 1))], .var 1⟩]⟩]

/-- **A parameter one call site passes a symbol to.** The parameter is tainted and the program
refused; without that call site it is admitted. -/
theorem symbol_argument :
    Slot.param 1 0 ∈ lfp (withRoot symbolArgument 0 []) noRows ∧
      admits symbolArgument noRows 0 [] = false ∧ admits integerArgument noRows 0 [] = true := by
  decide

theorem symbol_argument_raises : ¬ Quiet (system symbolArgument) emptyStore (root 0 []) := by
  intro quiet
  have reach : Reachable ((system symbolArgument).space emptyStore) (root 0 [])
      [⟨[.sym 0], [.prim .add (.var 0) (.lit (.int 1))], .var 1⟩, ⟨[], [], .var 0⟩,
        ⟨[], [], .var 0⟩] :=
    .step (child := [⟨[], [.call 1 [.lit (.sym 0)]], .var 0⟩, ⟨[], [], .var 0⟩]) rfl (by decide)
      (.step rfl (by decide) (.here _))
  exact absurd (quiet _ reach) (by decide)

/-- `(= (r) (+ <a row of space 0> 1))`. -/
def rowOperand : Program := [⟨0, [⟨[.read 0, .prim .add (.var 0) (.lit (.int 1))], .var 1⟩]⟩]

def symbolRows : Store := fun _ => [.sym 2]

def integerRows : Store := fun _ => [.int 4, .int 5]

/-- **An operand read from a space row.** Refused when the space's rows are not known to be
integers, admitted when they are. -/
theorem row_operand :
    admits rowOperand noRows 0 [] = false ∧ admits rowOperand (fun _ => true) 0 [] = true := by
  decide

theorem row_operand_raises : ¬ Quiet (system rowOperand) symbolRows (root 0 []) := by
  intro quiet
  have reach : Reachable ((system rowOperand).space symbolRows) (root 0 [])
      [⟨[.sym 2], [.prim .add (.var 0) (.lit (.int 1))], .var 1⟩, ⟨[], [], .var 0⟩] :=
    .step (child := [⟨[], [.read 0, .prim .add (.var 0) (.lit (.int 1))], .var 1⟩,
      ⟨[], [], .var 0⟩]) rfl (by decide) (.step rfl (by decide) (.here _))
  exact absurd (quiet _ reach) (by decide)

theorem row_operand_quiet : Quiet (system rowOperand) integerRows (root 0 []) :=
  admits_quiet (rowKind := fun _ => true) (by decide) (by
    intro space _ row member
    simp only [integerRows, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> rfl)

/-- A chain of `length` calls, at relations `1` to `length`, ending in `(/ 1 0)`. -/
def chain (length : Nat) : List Relation :=
  (List.range length).map (fun index => ⟨0, [⟨[.call (index + 2) []], .var 0⟩]⟩) ++
    [⟨0, [⟨[.prim .div (.lit (.int 1)) (.lit (.int 0))], .var 0⟩]⟩]

/-- `(= (s) (deep))` and `(= (s) 6)`, where `(deep)` divides by zero after twenty calls. -/
def skipped : Program := ⟨0, [⟨[.call 1 []], .var 0⟩, ⟨[], .lit (.int 6)⟩]⟩ :: chain 20

/-- **A raise that pruning skips.** The plain cursor raises. Under doubling quanta deepening
publishes `6` before the walk reaches the division, and nothing is raised. -/
theorem skipped_raise :
    (plain (system skipped) (root 0 []) 1 40 emptyStore []).2.1.raised =
        some (.fault .zeroDivisor) ∧
      batch (portfolio (system skipped) (root 0 []) 1 (rounds (doubling 1) 4) emptyStore []) =
        some [.int 6] ∧
      (portfolio (system skipped) (root 0 []) 1 (rounds (doubling 1) 4) emptyStore []).world.raised =
        none ∧
      admits skipped noRows 0 [] = false := by
  decide

/-- `(= (loop2 $n) (loop2 (+ $n 1)))` and `(= (gen2) (superpose ((loop2 0) a b c)))`. -/
def arithmeticLoop : Program :=
  [⟨1, [⟨[.prim .add (.var 0) (.lit (.int 1)), .call 0 [.var 1]], .var 2⟩]⟩,
    ⟨0, [⟨[.call 0 [.lit (.int 0)]], .var 0⟩, ⟨[], .lit (.sym 1)⟩, ⟨[], .lit (.sym 2)⟩,
      ⟨[], .lit (.sym 3)⟩]⟩]

/-- **The measured arithmetic loop.** CeTTa hangs on `!(once (gen2))`, since arithmetic ends its
portfolio. Under entry typing the program is admitted; the plain cursor has no answer after sixty
expansions; the portfolio answers `a` with nothing performed. -/
theorem arithmetic_loop :
    admits arithmeticLoop noRows 1 [] = true ∧
      (plain (system arithmeticLoop) (root 1 []) 1 60 emptyStore []).2.2.reversed = [] ∧
      batch (portfolio (system arithmeticLoop) (root 1 []) 1 (rounds (doubling 1) 4) emptyStore
        []) = some [.sym 1] ∧
      (portfolio (system arithmeticLoop) (root 1 []) 1 (rounds (doubling 1) 4) emptyStore
        []).world.log = [] := by
  decide

end Controls

#print axioms admits_iff
#print axioms lfp_stable
#print axioms invariant_quiet
#print axioms admits_quiet
#print axioms admitted_portfolio
#print axioms admitted_publishes
#print axioms Controls.division_rejected
#print axioms Controls.division_raises
#print axioms Controls.comparison_of_symbol
#print axioms Controls.comparison_raises
#print axioms Controls.symbol_argument
#print axioms Controls.symbol_argument_raises
#print axioms Controls.row_operand
#print axioms Controls.row_operand_raises
#print axioms Controls.row_operand_quiet
#print axioms Controls.skipped_raise
#print axioms Controls.arithmetic_loop

end Mettapedia.Machines.PortfolioReach
