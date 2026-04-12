/-
# WAM Unification Algorithm

The WAM uses a UNION/FIND-based unification algorithm that:
1. Uses the heap for term representation
2. Uses REF chains for variable substitutions
3. Uses a PDL stack for work items
4. Implements deref for chain following
5. Implements bind for linking variables

## Algorithm Overview

unify(a1, a2):
  push a1, a2 onto PDL
  while PDL not empty and not failed:
    d1 = deref(pop())
    d2 = deref(pop())
    if d1 ≠ d2:
      if either is REF: bind them
      else: if same functor, push subterms; else fail

## References

- Aït-Kaci (1991) §2.3: The unify operation (Figure 2.7)
- Martelli & Montanari (1982): Efficient unification algorithm
-/

import Mettapedia.AutoBooks.ClaudeProcWam.WAM.Machine

namespace Mettapedia.AutoBooks.ClaudeProcWam.WAM

/-! ## Unification State

We separate the unification state from the full machine state
for cleaner specification and proof.
-/

/-- Unification state: heap + PDL + failure flag -/
structure UnifyState where
  heap : Heap
  pdl : PDL
  trail : Trail
  hb : HeapAddr  -- Heap backtrack point for trailing
  fail : Bool
  deriving Repr

/-- Initialize unification state from machine state -/
def UnifyState.fromMachine (m : MachineState) (a1 a2 : HeapAddr) : UnifyState := {
  heap := m.heap
  pdl := [a1, a2]
  trail := m.trail
  hb := m.hb
  fail := false
}

/-- Apply unification result to machine state -/
def UnifyState.toMachine (us : UnifyState) (m : MachineState) : MachineState :=
  { m with
    heap := us.heap
    trail := us.trail
    tr := us.trail.entries.size
    fail := us.fail
    status := if us.fail then .failed else m.status }

/-! ## Core Unification Operations -/

/-- Bind address a1 to a2, trailing if necessary -/
def UnifyState.bind (us : UnifyState) (a1 a2 : HeapAddr) : UnifyState :=
  -- Prefer binding higher to lower (younger to older)
  let (src, tgt) := if a1 > a2 then (a1, a2) else (a2, a1)
  let heap' := us.heap.bind src tgt
  -- Trail if src < hb (older than choice point)
  let trail' := if src < us.hb then us.trail.push src else us.trail
  { us with heap := heap', trail := trail' }

/-- Helper: step with two cells -/
def UnifyState.stepCells (us : UnifyState) (d1 d2 : HeapAddr)
    (c1 c2 : HeapCell) (rest : PDL) : UnifyState :=
  match c1, c2 with
  -- At least one is a REF: bind them
  | .ref _, _ => { us.bind d1 d2 with pdl := rest }
  | _, .ref _ => { us.bind d1 d2 with pdl := rest }
  -- Both are STR: check functors and push subterms
  | .str v1, .str v2 =>
    match us.heap.get? v1, us.heap.get? v2 with
    | some (.functor f1), some (.functor f2) =>
      if f1 == f2 then
        -- Same functor: push subterm pairs
        let pairs := (List.range f1.arity).map (fun i => [v1 + 1 + i, v2 + 1 + i]) |>.flatten
        { us with pdl := pairs ++ rest }
      else
        { us with fail := true, pdl := rest }
    | _, _ => { us with fail := true, pdl := rest }
  -- Both are CON: check equality
  | .con f1, .con f2 =>
    if f1 == f2 then { us with pdl := rest }
    else { us with fail := true, pdl := rest }
  -- Both are LIS: push head and tail pairs
  | .lis h1, .lis h2 =>
    let pairs := [h1, h2, h1 + 1, h2 + 1]
    { us with pdl := pairs ++ rest }
  -- Otherwise: fail
  | _, _ => { us with fail := true, pdl := rest }

/-- Single unification step -/
def UnifyState.step (us : UnifyState) : UnifyState :=
  if us.fail then us
  else match us.pdl with
  | [] => us  -- Done
  | [_] => { us with fail := true }  -- Odd number on stack
  | a1 :: a2 :: rest =>
    let d1 := us.heap.deref a1
    let d2 := us.heap.deref a2
    if d1 == d2 then
      -- Same address, already unified
      { us with pdl := rest }
    else
      -- Get cells at dereferenced addresses
      match us.heap.get? d1, us.heap.get? d2 with
      | some c1, some c2 => us.stepCells d1 d2 c1 c2 rest
      | _, _ => { us with fail := true, pdl := rest }

/-- Run unification to completion with fuel -/
def UnifyState.run (us : UnifyState) (fuel : Nat) : UnifyState :=
  match fuel with
  | 0 => us  -- Out of fuel
  | fuel' + 1 =>
    if us.fail || us.pdl.isEmpty then us
    else (us.step).run fuel'

/-- Unify two addresses -/
def UnifyState.unify (us : UnifyState) (a1 a2 : HeapAddr) : UnifyState :=
  let us' := { us with pdl := [a1, a2] }
  us'.run (us'.heap.cells.size * 2 + 10)  -- Generous fuel

/-! ## Machine-Level Unification -/

/-- Unify two heap addresses in machine context -/
def MachineState.unify (m : MachineState) (a1 a2 : HeapAddr) : MachineState :=
  let us := UnifyState.fromMachine m a1 a2
  let us' := us.run (m.heap.cells.size * 2 + 10)
  us'.toMachine m

/-- Unify X register with heap address -/
def MachineState.unifyRegHeap (m : MachineState) (r : XReg) (addr : HeapAddr) : MachineState :=
  match m.getXReg r with
  | some (.ref a) => m.unify a addr
  | some (.str a) => m.unify a addr
  | _ => m.setFail

/-! ## Unification Properties

We state key properties that a correct unification should satisfy.
-/

/-- Two addresses represent equal terms in the heap (Boolean version).
    This is structural equality after dereferencing.
    - REF chains are followed (via deref)
    - CON cells compare constant values
    - STR cells compare functor and all subterms recursively
    - LIS cells compare head and tail

    Note: This is defined with fuel to ensure termination.
    In a well-formed acyclic heap, sufficient fuel always exists. -/
def Heap.termEqAux (h : Heap) (a1 a2 : HeapAddr) (fuel : Nat) : Bool :=
  let d1 := h.deref a1
  let d2 := h.deref a2
  if d1 == d2 then true  -- Same address after deref
  else match fuel with
  | 0 => false  -- Out of fuel
  | fuel' + 1 =>
    match h.get? d1, h.get? d2 with
    | some (.con f1), some (.con f2) => f1 == f2
    | some (.str v1), some (.str v2) =>
      match h.get? v1, h.get? v2 with
      | some (.functor f1), some (.functor f2) =>
        f1 == f2 &&
        (List.range f1.arity).all fun i =>
          h.termEqAux (v1 + 1 + i) (v2 + 1 + i) fuel'
      | _, _ => false
    | some (.lis v1), some (.lis v2) =>
      h.termEqAux v1 v2 fuel' && h.termEqAux (v1 + 1) (v2 + 1) fuel'
    | _, _ => false

/-- Propositional term equality with generous fuel -/
def Heap.termEq (h : Heap) (a1 a2 : HeapAddr) : Prop :=
  h.termEqAux a1 a2 (h.cells.size * 2)

/-- If derefs are equal (same address), termEqAux is true -/
theorem Heap.termEqAux_of_deref_beq (h : Heap) (a1 a2 : HeapAddr) (fuel : Nat)
    (heq : h.deref a1 == h.deref a2) :
    h.termEqAux a1 a2 fuel = true := by
  unfold termEqAux
  simp only [heq, ite_true]

/-- If derefs are equal (propositionally), termEq holds -/
theorem Heap.termEq_of_deref_eq (h : Heap) (a1 a2 : HeapAddr)
    (heq : h.deref a1 = h.deref a2) :
    h.termEq a1 a2 := by
  unfold termEq
  have hbeq : h.deref a1 == h.deref a2 := by simp only [beq_iff_eq, heq]
  exact termEqAux_of_deref_beq h a1 a2 (h.cells.size * 2) hbeq

/-- If both derefs point to CON with same constant, termEqAux is true -/
theorem Heap.termEqAux_of_con (h : Heap) (a1 a2 : HeapAddr) (fuel : Nat) (f : Functor)
    (hneq : ¬(h.deref a1 == h.deref a2))
    (hc1 : h.get? (h.deref a1) = some (.con f))
    (hc2 : h.get? (h.deref a2) = some (.con f)) :
    h.termEqAux a1 a2 (fuel + 1) = true := by
  unfold termEqAux
  simp only [Bool.not_eq_true] at hneq
  simp only [hneq, hc1, hc2, beq_self_eq_true]
  rfl

/-- If both derefs point to STR cells with matching 0-ary functors, termEqAux is true -/
theorem Heap.termEqAux_of_str_functor0 (h : Heap) (a1 a2 : HeapAddr) (fuel : Nat)
    (f : Functor) (v1 v2 : HeapAddr)
    (hneq : (h.deref a1 == h.deref a2) = false)
    (hs1 : h.get? (h.deref a1) = some (.str v1))
    (hs2 : h.get? (h.deref a2) = some (.str v2))
    (hf1 : h.get? v1 = some (.functor f))
    (hf2 : h.get? v2 = some (.functor f))
    (harity : f.arity = 0) :
    h.termEqAux a1 a2 (fuel + 1) = true := by
  unfold termEqAux
  simp only [hneq, hs1, hs2, hf1, hf2, beq_self_eq_true, Bool.true_and]
  -- Goal: (if false = true then true else ...) = true
  -- Since false ≠ true, this reduces to the else branch
  simp only [Bool.false_eq_true, ↓reduceIte]
  -- Need to show: (List.range f.arity).all ... = true
  simp only [harity, List.range_zero, List.all_nil]

/-- If both derefs point to STR cells with matching functors and all subterms have termEqAux,
    then the STR pair has termEqAux. This is the compositional property of termEq. -/
theorem Heap.termEqAux_of_str_subterms (h : Heap) (a1 a2 : HeapAddr) (fuel : Nat)
    (f : Functor) (v1 v2 : HeapAddr)
    (hneq : (h.deref a1 == h.deref a2) = false)
    (hs1 : h.get? (h.deref a1) = some (.str v1))
    (hs2 : h.get? (h.deref a2) = some (.str v2))
    (hf1 : h.get? v1 = some (.functor f))
    (hf2 : h.get? v2 = some (.functor f))
    (hsubterms : ∀ i, i < f.arity → h.termEqAux (v1 + 1 + i) (v2 + 1 + i) fuel = true) :
    h.termEqAux a1 a2 (fuel + 1) = true := by
  unfold termEqAux
  simp only [hneq, hs1, hs2, hf1, hf2, beq_self_eq_true, Bool.true_and]
  simp only [Bool.false_eq_true, ↓reduceIte]
  -- Need to show: (List.range f.arity).all ... = true
  simp only [List.all_eq_true, List.mem_range]
  intro i hi
  exact hsubterms i hi

/-- An address is well-formed if all cell references are valid.
    For STR cells, we require the functor and all subterms to be valid. -/
def Heap.wellFormed (h : Heap) : Prop :=
  ∀ i : Nat, i < h.cells.size →
    match h.cells[i]? with
    | some (.ref a) => a < h.cells.size
    | some (.str a) =>
      -- STR must point to valid functor with valid subterms
      a < h.cells.size ∧
      match h.cells[a]? with
      | some (.functor f) => a + f.arity < h.cells.size
      | _ => True  -- Not a functor - invalid but not our concern here
    | some (.lis a) => a + 1 < h.cells.size
    | _ => True

/-- Helper: STR cells point to functors with valid subterms -/
def Heap.strWellFormed (h : Heap) (i a : Nat) (hlt : i < h.cells.size)
    (hstr : h.cells[i]? = some (.str a)) (hwf : h.wellFormed) :
    a < h.cells.size ∧ ∀ f, h.cells[a]? = some (.functor f) → a + f.arity < h.cells.size := by
  have := hwf i hlt
  simp only [hstr] at this
  exact ⟨this.1, fun f hf => by simp only [hf] at this; exact this.2⟩

/-- An address is terminal: derefAux returns immediately -/
def Heap.isTerminal (h : Heap) (addr : HeapAddr) : Bool :=
  match h.get? addr with
  | none => true
  | some (.ref a) => a == addr
  | some _ => true

/-- REF chains always descend: non-self REF cells point to strictly lower addresses.
    This is the key WAM invariant that ensures chain acyclicity. -/
def Heap.chainsDescend (h : Heap) : Prop :=
  ∀ i : Nat, i < h.cells.size →
    match h.cells[i]? with
    | some (.ref a) => a = i ∨ a < i  -- Self-ref or strictly lower
    | _ => True

/-- In a descending heap, derefAux reaches a terminal within addr steps.
    Since addresses decrease at each step, we can't take more than addr non-terminal steps.
    This is proven by strong induction on addr. -/
theorem Heap.derefAux_terminates (h : Heap) (addr : HeapAddr) (fuel : Nat)
    (hlt : addr < h.cells.size) (hdesc : h.chainsDescend) (hwf : h.wellFormed)
    (hfuel : fuel ≥ addr) :
    h.isTerminal (h.derefAux addr fuel) = true := by
  -- Strong induction on addr
  induction addr using Nat.strong_induction_on generalizing fuel with
  | _ addr ih =>
    cases hfuel_eq : fuel with
    | zero =>
      -- fuel = 0, so derefAux addr 0 = addr
      simp only [derefAux]
      -- Since fuel = 0 ≥ addr, we have addr = 0
      have haddr0 : addr = 0 := by omega
      subst haddr0
      simp only [isTerminal]
      cases hcell : h.get? 0 with
      | none => rfl
      | some c =>
        cases c with
        | ref a =>
          -- By chainsDescend at 0, a = 0 ∨ a < 0. Since a < 0 is impossible, a = 0
          have hdesc0 := hdesc 0 hlt
          unfold get? at hcell
          simp only [hcell] at hdesc0
          cases hdesc0 with
          | inl h_eq => subst h_eq; simp only [beq_self_eq_true]
          | inr h_lt => exact absurd h_lt (Nat.not_lt_zero a)
        | str _ => rfl
        | con _ => rfl
        | functor _ => rfl
        | lis _ => rfl
    | succ fuel' =>
      simp only [derefAux]
      cases hcell : h.get? addr with
      | none =>
        simp only [isTerminal, hcell]
      | some c =>
        cases c with
        | ref a =>
          unfold get? at hcell
          by_cases heq : a == addr
          · -- Self-ref: terminal
            simp only [heq, if_true, isTerminal, get?, hcell]
          · -- Not self-ref: a < addr by chainsDescend
            have hbeq_false : (a == addr) = false := by
              cases h_eq : (a == addr) with
              | true => exact absurd trivial (by simp only [h_eq] at heq; exact heq)
              | false => rfl
            simp only [hbeq_false]
            have hne : a ≠ addr := by
              intro h_eq
              simp only [h_eq, beq_self_eq_true] at hbeq_false
              exact Bool.false_ne_true hbeq_false.symm
            have hdesc_at := hdesc addr hlt
            simp only [hcell] at hdesc_at
            cases hdesc_at with
            | inl h_eq => exact absurd h_eq hne
            | inr h_a_lt =>
              -- a < addr, so fuel' ≥ a (since fuel' + 1 ≥ addr > a)
              have ha_lt : a < h.cells.size := by
                unfold wellFormed at hwf
                have := hwf addr hlt
                simp only [hcell] at this
                exact this
              have hfuel' : fuel' ≥ a := by
                have h1 : fuel' + 1 ≥ addr := by rw [← hfuel_eq]; exact hfuel
                have h2 : a < addr := h_a_lt
                have h3 : a + 1 ≤ addr := Nat.succ_le_of_lt h2
                have h4 : fuel' + 1 ≥ a + 1 := Nat.le_trans h3 h1
                exact Nat.le_of_succ_le_succ h4
              exact ih a h_a_lt fuel' ha_lt hfuel'
        | str _ => simp only [isTerminal, hcell]
        | con _ => simp only [isTerminal, hcell]
        | functor _ => simp only [isTerminal, hcell]
        | lis _ => simp only [isTerminal, hcell]

/-- Address a is reachable from addr in k steps if derefAux from addr reaches a -/
def Heap.reachable (h : Heap) (addr a : HeapAddr) : Prop :=
  ∃ k, h.derefAux addr k = a ∧ k > 0

/-- Self-referential addresses are not reachable from different addresses
    (in acyclic heaps). This is the key property for bind correctness. -/
def Heap.notReachableFrom (h : Heap) (src tgt : HeapAddr) : Prop :=
  ∀ k, h.derefAux tgt k ≠ src

/-- In a descending heap, derefAux never increases the address.
    This follows from chainsDescend: REF chains only go down. -/
theorem Heap.derefAux_le (h : Heap) (addr : HeapAddr) (fuel : Nat)
    (hlt : addr < h.cells.size) (hdesc : h.chainsDescend) :
    h.derefAux addr fuel ≤ addr := by
  induction fuel generalizing addr with
  | zero => simp only [derefAux]; exact Nat.le_refl addr
  | succ n ih =>
    simp only [derefAux]
    cases hcell : h.get? addr with
    | none => exact Nat.le_refl addr
    | some c =>
      cases c with
      | ref a =>
        by_cases heq : a == addr
        · -- Self-ref: stays at addr
          simp only [heq, ↓reduceIte]; exact Nat.le_refl addr
        · -- Non-self REF: a < addr by chainsDescend, then recurse
          simp only [heq, Bool.false_eq_true, ↓reduceIte]
          have hdesc_at := hdesc addr hlt
          unfold get? at hcell
          simp only [hcell] at hdesc_at
          have ha_lt : a < addr := by
            cases hdesc_at with
            | inl h_eq =>
              simp only [beq_iff_eq] at heq
              exact absurd h_eq heq
            | inr h_lt => exact h_lt
          have ha_valid : a < h.cells.size := Nat.lt_trans ha_lt hlt
          have h_ih := ih a ha_valid
          exact Nat.le_trans h_ih (Nat.le_of_lt ha_lt)
      | str _ | con _ | functor _ | lis _ => exact Nat.le_refl addr

/-- Higher addresses are not reachable from lower ones in descending heaps.
    Key lemma for bind correctness. -/
theorem Heap.notReachableFrom_of_gt (h : Heap) (src tgt : HeapAddr)
    (htgt : tgt < h.cells.size) (hgt : src > tgt) (hdesc : h.chainsDescend) :
    h.notReachableFrom src tgt := by
  intro k
  have hle : h.derefAux tgt k ≤ tgt := derefAux_le h tgt k htgt hdesc
  -- hgt : src > tgt, i.e., tgt < src
  -- hle : derefAux tgt k ≤ tgt
  -- Want: derefAux tgt k ≠ src
  -- Since derefAux tgt k ≤ tgt < src, we have derefAux tgt k < src
  have hlt : h.derefAux tgt k < src := Nat.lt_of_le_of_lt hle hgt
  exact Nat.ne_of_lt hlt

/-- Terminal addresses are fixed points of derefAux -/
theorem Heap.derefAux_terminal (h : Heap) (addr : HeapAddr) (fuel : Nat)
    (hterm : h.isTerminal addr = true) :
    h.derefAux addr (fuel + 1) = addr := by
  simp only [derefAux]
  unfold isTerminal at hterm
  cases hg : h.get? addr with
  | none => rfl
  | some c =>
    cases c with
    | ref a =>
      simp only [hg] at hterm
      have heq : a = addr := by simpa using hterm
      simp only [heq, beq_self_eq_true, ite_true]
    | str _ | con _ | functor _ | lis _ => rfl

/-- get? returns some for valid addresses -/
theorem Heap.get?_some_of_lt (h : Heap) (addr : HeapAddr) (hlt : addr < h.cells.size) :
    ∃ c, h.get? addr = some c := by
  unfold get?
  exact ⟨h.cells[addr], Array.getElem?_eq_some_iff.mpr ⟨hlt, rfl⟩⟩

/-- derefAux preserves validity: if we start valid, we stay valid -/
theorem Heap.derefAux_lt (h : Heap) (addr : HeapAddr) (fuel : Nat)
    (hlt : addr < h.cells.size) (hwf : h.wellFormed) :
    h.derefAux addr fuel < h.cells.size := by
  induction fuel generalizing addr with
  | zero => simp only [derefAux]; exact hlt
  | succ n ih =>
    simp only [derefAux]
    -- Since addr is valid, get? returns some
    have ⟨c, hc⟩ := h.get?_some_of_lt addr hlt
    rw [hc]
    cases c with
    | ref a =>
      by_cases heq : a == addr
      · simp only [heq, ite_true]; exact hlt
      · simp only [heq]
        -- By wellFormed, a < h.cells.size
        have ha : a < h.cells.size := by
          unfold wellFormed at hwf
          have := hwf addr hlt
          unfold get? at hc
          rw [hc] at this
          exact this
        exact ih a ha
    | str _ => exact hlt
    | con _ => exact hlt
    | functor _ => exact hlt
    | lis _ => exact hlt

/-- Deref terminates on well-formed heaps -/
theorem Heap.deref_terminates (h : Heap) (addr : HeapAddr)
    (hlt : addr < h.cells.size) (hwf : h.wellFormed) :
    h.deref addr < h.cells.size := by
  unfold deref
  exact derefAux_lt h addr h.cells.size hlt hwf

/-- If derefAux returns a terminal, one more step still returns the same -/
theorem Heap.derefAux_stable_step (h : Heap) (addr : HeapAddr) (k : Nat)
    (hterm : h.isTerminal (h.derefAux addr k) = true) :
    h.derefAux addr k = h.derefAux addr (k + 1) := by
  induction k generalizing addr with
  | zero =>
    -- derefAux addr 0 = addr, and if addr is terminal, derefAux addr 1 = addr
    simp only [derefAux]
    exact (derefAux_terminal h addr 0 hterm).symm
  | succ k' ih =>
    -- derefAux addr (k'+1) depends on what's at addr
    simp only [derefAux] at hterm ⊢
    cases hcell : h.get? addr with
    | none => rfl
    | some c =>
      cases c with
      | ref a =>
        simp only [hcell] at hterm
        by_cases heq : a == addr
        · -- Self-ref: terminal
          simp only [heq, ite_true]
        · -- Not self-ref: recurse
          simp only [heq] at hterm ⊢
          exact ih a hterm
      | str _ => rfl
      | con _ => rfl
      | functor _ => rfl
      | lis _ => rfl

/-- Once derefAux reaches a terminal, additional fuel doesn't change the result.
    This is the key stability lemma for chain analysis. -/
theorem Heap.derefAux_stable (h : Heap) (addr : HeapAddr) (k m : Nat)
    (hterm : h.isTerminal (h.derefAux addr k) = true) :
    h.derefAux addr k = h.derefAux addr (k + m) := by
  induction m with
  | zero => simp
  | succ m' ih =>
    have hsucc : k + m'.succ = (k + m') + 1 := by omega
    rw [hsucc, ← derefAux_stable_step h addr (k + m')]
    · exact ih
    · rw [← ih]; exact hterm

/-- If chains descend and fuel ≥ addr, then derefAux addr fuel = derefAux addr (fuel + m) for any m.
    This follows directly from derefAux_terminates and derefAux_stable. -/
theorem Heap.derefAux_converges (h : Heap) (addr : HeapAddr) (fuel : Nat)
    (hlt : addr < h.cells.size) (hwf : h.wellFormed) (hdesc : h.chainsDescend)
    (hfuel : fuel ≥ addr) :
    h.derefAux addr fuel = h.derefAux addr (fuel + 1) := by
  have hterm : h.isTerminal (h.derefAux addr fuel) = true :=
    derefAux_terminates h addr fuel hlt hdesc hwf hfuel
  exact derefAux_stable h addr fuel 1 hterm

/-- Deref is idempotent on acyclic heaps.

    This requires showing that deref returns a terminal address,
    which in turn requires acyclicity of REF chains. The current
    wellFormed predicate doesn't capture acyclicity explicitly.

    In practice, WAM maintains acyclicity by always binding younger
    (higher address) variables to older (lower address) ones. -/
theorem Heap.deref_idempotent (h : Heap) (addr : HeapAddr)
    (hterm : h.isTerminal (h.deref addr) = true) :
    h.deref (h.deref addr) = h.deref addr := by
  unfold deref at *
  cases hfuel : h.cells.size with
  | zero => simp only [derefAux]
  | succ n =>
    rw [hfuel] at hterm
    exact derefAux_terminal h (h.derefAux addr (n + 1)) n hterm

/-- Setting preserves heap size -/
theorem Heap.set_size (h : Heap) (addr : HeapAddr) (cell : HeapCell) :
    (h.set addr cell).cells.size = h.cells.size := by
  unfold set
  split
  · simp only [Array.size_set]
  · rfl

/-- Binding preserves heap size -/
theorem Heap.bind_size (h : Heap) (src tgt : HeapAddr) :
    (h.bind src tgt).cells.size = h.cells.size := by
  unfold bind
  exact set_size h src (.ref tgt)

/-- Setting preserves heap top -/
theorem Heap.set_top (h : Heap) (addr : HeapAddr) (cell : HeapCell) :
    (h.set addr cell).top = h.top := by
  unfold top
  exact set_size h addr cell

/-- Binding preserves heap top -/
theorem Heap.bind_top (h : Heap) (src tgt : HeapAddr) :
    (h.bind src tgt).top = h.top := by
  unfold top
  exact bind_size h src tgt

/-- Push increases heap size by 1 -/
theorem Heap.push_size (h : Heap) (c : HeapCell) :
    (h.push c).cells.size = h.cells.size + 1 := by
  unfold push
  simp only [Array.size_push]

/-- Push updates top by 1 -/
theorem Heap.push_top (h : Heap) (c : HeapCell) :
    (h.push c).top = h.top + 1 := by
  unfold top
  exact push_size h c

/-- After push, cells[i]? at old addresses is unchanged -/
theorem Heap.cells_push_lt (h : Heap) (c : HeapCell) (addr : HeapAddr)
    (hlt : addr < h.cells.size) :
    (h.push c).cells[addr]? = h.cells[addr]? := by
  unfold push
  simp only [Array.getElem?_push]
  have hne : addr ≠ h.cells.size := Nat.ne_of_lt hlt
  simp only [hne, ↓reduceIte]

/-- After push, cells[i]? at new address returns the pushed cell -/
theorem Heap.cells_push_eq (h : Heap) (c : HeapCell) :
    (h.push c).cells[h.cells.size]? = some c := by
  unfold push
  simp only [Array.getElem?_push]
  simp only [↓reduceIte]

/-- Push of self-referential REF preserves well-formedness.
    This is the common case for creating unbound variables. -/
theorem Heap.push_selfref_preserves_wf (h : Heap) (hwf : h.wellFormed) :
    (h.push (.ref h.cells.size)).wellFormed := by
  unfold wellFormed at *
  intro i hi
  simp only [push_size] at hi
  by_cases heq : i = h.cells.size
  · -- New cell at h.cells.size: self-ref is valid in new size
    subst heq
    rw [cells_push_eq]
    simp only [push_size]
    omega
  · -- Old cell: check unchanged
    have hlt : i < h.cells.size := by omega
    rw [cells_push_lt h (.ref h.cells.size) i hlt]
    have horig := hwf i hlt
    cases hcell : h.cells[i]? with
    | none => trivial
    | some cell =>
      simp only [hcell] at horig
      cases cell with
      | ref a =>
        -- horig simplifies to: a < h.cells.size
        simp only at horig
        simp only [push_size]
        exact Nat.lt_add_right 1 horig
      | str a =>
        -- horig : a < size ∧ (functor → bound)
        simp only at horig
        have ha_lt : a < h.cells.size := horig.1
        constructor
        · simp only [push_size]
          exact Nat.lt_add_right 1 ha_lt
        · -- Inner match on functor
          cases hf : h.cells[a]? with
          | none =>
            rw [cells_push_lt h (.ref h.cells.size) a ha_lt]
            simp only [hf]
          | some fc =>
            simp only [hf] at horig
            cases fc with
            | functor f =>
              simp only at horig
              rw [cells_push_lt h (.ref h.cells.size) a ha_lt]
              simp only [hf, push_size]
              exact Nat.lt_add_right 1 horig.2
            | _ =>
              rw [cells_push_lt h (.ref h.cells.size) a ha_lt]
              simp only [hf]
      | con _ => trivial
      | functor _ => trivial
      | lis a =>
        simp only at horig
        simp only [push_size]
        exact Nat.lt_add_right 1 horig

/-- Push of CON cell preserves well-formedness -/
theorem Heap.push_con_preserves_wf (h : Heap) (hwf : h.wellFormed) (f : Functor) :
    (h.push (.con f)).wellFormed := by
  unfold wellFormed at *
  intro i hi
  simp only [push_size] at hi
  by_cases heq : i = h.cells.size
  · -- New cell at h.cells.size: CON is always valid
    subst heq
    rw [cells_push_eq]
    trivial
  · -- Old cell: check unchanged
    have hlt : i < h.cells.size := by omega
    rw [cells_push_lt h (.con f) i hlt]
    have horig := hwf i hlt
    cases hcell : h.cells[i]? with
    | none => trivial
    | some cell =>
      simp only [hcell] at horig
      cases cell with
      | ref a =>
        simp only at horig
        simp only [push_size]
        exact Nat.lt_add_right 1 horig
      | str a =>
        simp only at horig
        have ha_lt : a < h.cells.size := horig.1
        constructor
        · simp only [push_size]
          exact Nat.lt_add_right 1 ha_lt
        · cases hf : h.cells[a]? with
          | none =>
            rw [cells_push_lt h (.con f) a ha_lt]
            simp only [hf]
          | some fc =>
            simp only [hf] at horig
            cases fc with
            | functor f' =>
              simp only at horig
              rw [cells_push_lt h (.con f) a ha_lt]
              simp only [hf, push_size]
              exact Nat.lt_add_right 1 horig.2
            | _ =>
              rw [cells_push_lt h (.con f) a ha_lt]
              simp only [hf]
      | con _ => trivial
      | functor _ => trivial
      | lis a =>
        simp only at horig
        simp only [push_size]
        exact Nat.lt_add_right 1 horig

/-- Push STR+functor pair preserves well-formedness (for 0-arity functors).
    Note: For arity > 0, subterms must be added before wellFormed holds.
    The WAM model allows transient invalid states during query construction.
    Used for put_structure: push .str (size+1) then .functor f

    Design limitation: The current wellFormed predicate requires all STR cells
    to point to functors with valid subterms. But put_structure creates a STR
    cell before subterms are added, violating this temporarily. A more refined
    invariant would distinguish "construction phase" from "execution phase". -/
theorem Heap.push_structure_preserves_wf (h : Heap) (f : Functor)
    (hwf : h.wellFormed) (harity : f.arity = 0) :
    ((h.push (.str (h.cells.size + 1))).push (.functor f)).wellFormed := by
  -- Final size: h.cells.size + 2
  set h1 := h.push (.str (h.cells.size + 1)) with hh1
  set h2 := h1.push (.functor f) with hh2
  have h1_size : h1.cells.size = h.cells.size + 1 := push_size h _
  have h2_size : h2.cells.size = h.cells.size + 2 := by
    simp only [hh2, push_size, h1_size]
  -- Cell lookups in h2
  have h2_old : ∀ i, i < h.cells.size → h2.cells[i]? = h.cells[i]? := by
    intro i hlt
    have hi1 : i < h1.cells.size := by omega
    simp only [hh2, hh1]
    rw [cells_push_lt h1 (.functor f) i hi1]
    exact cells_push_lt h (.str (h.cells.size + 1)) i hlt
  have h2_str : h2.cells[h.cells.size]? = some (.str (h.cells.size + 1)) := by
    simp only [hh2, hh1, push, Array.getElem?_push, Array.size_push]
    simp only [show h.cells.size ≠ h.cells.size + 1 by omega, ↓reduceIte]
  have h2_functor : h2.cells[h.cells.size + 1]? = some (.functor f) := by
    simp only [hh2, hh1, push, Array.getElem?_push, Array.size_push, ↓reduceIte]
  -- Now prove wellFormed
  unfold wellFormed
  intro i hi
  simp only [h2_size] at hi
  -- Three cases: old cell, STR cell, functor cell
  by_cases hi_old : i < h.cells.size
  · -- Old cell: use original wellFormed
    rw [h2_old i hi_old]
    have horig := hwf i hi_old
    cases hcell : h.cells[i]? with
    | none => trivial
    | some cell =>
      simp only [hcell] at horig
      cases cell with
      | ref a =>
        simp only at horig
        calc a < h.cells.size := horig
          _ < h.cells.size + 2 := by omega
          _ = h2.cells.size := h2_size.symm
      | str a =>
        simp only at horig
        have ha_lt : a < h.cells.size := horig.1
        constructor
        · calc a < h.cells.size := ha_lt
            _ < h.cells.size + 2 := by omega
            _ = h2.cells.size := h2_size.symm
        · cases hf : h.cells[a]? with
          | none =>
            rw [h2_old a ha_lt]
            simp only [hf]
          | some fc =>
            simp only [hf] at horig
            cases fc with
            | functor f' =>
              simp only at horig
              rw [h2_old a ha_lt]
              simp only [hf]
              calc a + f'.arity < h.cells.size := horig.2
                _ < h.cells.size + 2 := by omega
                _ = h2.cells.size := h2_size.symm
            | _ =>
              rw [h2_old a ha_lt]
              simp only [hf]
      | con _ => trivial
      | functor _ => trivial
      | lis a =>
        simp only at horig
        calc a + 1 < h.cells.size := horig
          _ < h.cells.size + 2 := by omega
          _ = h2.cells.size := h2_size.symm
  · -- New cells
    by_cases hi_str : i = h.cells.size
    · -- STR cell at h.cells.size
      subst hi_str
      simp only [h2_str]
      constructor
      · calc h.cells.size + 1 < h.cells.size + 2 := by omega
          _ = h2.cells.size := h2_size.symm
      · -- Functor check: h2.cells[h.cells.size + 1]? = some (.functor f)
        simp only [h2_functor, harity]
        calc h.cells.size + 1 + 0 < h.cells.size + 2 := by omega
          _ = h2.cells.size := h2_size.symm
    · -- Functor cell at h.cells.size + 1
      have hi_functor : i = h.cells.size + 1 := by omega
      subst hi_functor
      simp only [h2_functor]

/-- Setting a REF cell preserves well-formedness if the target is valid.
    This is the main case needed for unification (binding). -/
theorem Heap.set_ref_preserves_wf (h : Heap) (addr tgt : HeapAddr)
    (hwf : h.wellFormed) (htgt : tgt < h.cells.size) :
    (h.set addr (.ref tgt)).wellFormed := by
  unfold set
  split
  · -- addr < h.cells.size case
    rename_i hlt
    unfold wellFormed at *
    intro i hi
    simp only [Array.size_set] at hi
    by_cases heq : i = addr
    · -- Setting at i = addr: new REF cell
      subst heq
      simp only [Array.getElem?_set, ↓reduceIte, Array.size_set]
      exact htgt
    · -- Not at addr: need to show original cell is still valid
      have hne : addr ≠ i := fun h => heq h.symm
      simp only [Array.getElem?_set, hne, ↓reduceIte, Array.size_set]
      have horig := hwf i hi
      -- For STR cells, we need to handle the inner match
      cases hcell : h.cells[i]? with
      | none => trivial
      | some c =>
        simp only [hcell] at horig
        cases c with
        | ref a => exact horig
        | str a =>
          constructor
          · exact horig.1
          · -- Inner match on cells[a]
            by_cases ha : addr = a
            · -- Setting at the functor address - but we're setting a REF, not a functor
              subst ha
              simp only [↓reduceIte]
            · simp only [ha, ↓reduceIte]
              exact horig.2
        | con _ => trivial
        | functor _ => trivial
        | lis a => exact horig
  · -- addr >= h.cells.size, heap unchanged
    exact hwf

/-- Binding preserves well-formedness if target is valid -/
theorem Heap.bind_preserves_wf (h : Heap) (src tgt : HeapAddr)
    (hwf : h.wellFormed) (htgt : tgt < h.cells.size) :
    (h.bind src tgt).wellFormed := by
  unfold bind
  exact set_ref_preserves_wf h src tgt hwf htgt

/-- Binding higher to lower preserves chainsDescend.
    The WAM invariant: we always bind higher addresses to lower ones. -/
theorem Heap.bind_preserves_chainsDescend (h : Heap) (src tgt : HeapAddr)
    (hdesc : h.chainsDescend) (hsrc : src < h.cells.size) (hle : tgt ≤ src) :
    (h.bind src tgt).chainsDescend := by
  unfold bind chainsDescend at *
  intro i hi
  rw [set_size] at hi
  by_cases heq : i = src
  · -- At src: new cell is ref tgt, and tgt ≤ src
    subst heq
    -- get? src on (h.set src (ref tgt)) = some (ref tgt)
    simp only [set, hsrc, ↓reduceDIte, Array.getElem?_set, ↓reduceIte]
    cases Nat.eq_or_lt_of_le hle with
    | inl h_eq => left; exact h_eq
    | inr h_lt => right; exact h_lt
  · -- Not at src: unchanged
    simp only [set, hsrc, ↓reduceDIte]
    have hne : src ≠ i := fun h => heq h.symm
    rw [Array.getElem?_set]
    simp only [hne, ↓reduceIte]
    exact hdesc i hi

/-- Setting a CON cell preserves well-formedness.
    CON cells have no reference constraints, so this is simpler than REF. -/
theorem Heap.set_con_preserves_wf (h : Heap) (addr : HeapAddr)
    (hwf : h.wellFormed) (c : Functor) :
    (h.set addr (.con c)).wellFormed := by
  unfold set
  split
  · -- addr < h.cells.size case
    rename_i hlt
    unfold wellFormed at *
    intro i hi
    simp only [Array.size_set] at hi
    by_cases heq : i = addr
    · -- Setting at i = addr: new CON cell (no constraints)
      subst heq
      simp only [Array.getElem?_set, ↓reduceIte]
    · -- Not at addr: need to show original cell is still valid
      have hne : addr ≠ i := fun h => heq h.symm
      simp only [Array.getElem?_set, hne, ↓reduceIte, Array.size_set]
      have horig := hwf i hi
      cases hcell : h.cells[i]? with
      | none => trivial
      | some cell =>
        simp only [hcell] at horig
        cases cell with
        | ref a => exact horig
        | str a =>
          constructor
          · exact horig.1
          · -- Inner match on cells[a]
            by_cases ha : addr = a
            · -- Setting a functor address to CON - True case in match
              subst ha
              simp only [↓reduceIte]
            · simp only [ha, ↓reduceIte]
              exact horig.2
        | con _ => trivial
        | functor _ => trivial
        | lis a => exact horig
  · -- addr >= h.cells.size, heap unchanged
    exact hwf

/-- UnifyState.bind preserves heap well-formedness if both addresses are valid -/
theorem UnifyState.bind_preserves_wf (us : UnifyState) (a1 a2 : HeapAddr)
    (hwf : us.heap.wellFormed) (ha1 : a1 < us.heap.cells.size) (ha2 : a2 < us.heap.cells.size) :
    (us.bind a1 a2).heap.wellFormed := by
  unfold bind
  simp only
  -- Bind the higher to lower
  split
  · -- a1 > a2, so we bind a1 to a2
    exact Heap.bind_preserves_wf us.heap a1 a2 hwf ha2
  · -- a1 <= a2, so we bind a2 to a1
    exact Heap.bind_preserves_wf us.heap a2 a1 hwf ha1

/-- All addresses in PDL are valid -/
def UnifyState.pdlValid (us : UnifyState) : Prop :=
  ∀ a ∈ us.pdl, a < us.heap.cells.size

/-- The heap of stepCells is either unchanged or from bind -/
theorem UnifyState.stepCells_heap (us : UnifyState) (d1 d2 : HeapAddr)
    (c1 c2 : HeapCell) (rest : PDL) :
    (us.stepCells d1 d2 c1 c2 rest).heap = us.heap ∨
    (us.stepCells d1 d2 c1 c2 rest).heap = (us.bind d1 d2).heap := by
  simp only [stepCells]
  cases c1 <;> cases c2 <;> simp only [true_or, or_true]
  -- str.str case: inner match on functors
  · rename_i v1 v2
    split
    · -- some functor, some functor
      split <;> (left; rfl)
    all_goals (left; rfl)
  -- con.con case
  · rename_i f1 f2
    split <;> (left; rfl)

/-- Helper: range map produces addresses in range -/
theorem List.range_map_subterm_bound (v : Nat) (n : Nat) (hv : v + n < sz) :
    ∀ a ∈ (List.range n).map (fun i => v + 1 + i), a < sz := by
  intro a ha
  simp only [List.mem_map, List.mem_range] at ha
  obtain ⟨i, hi, rfl⟩ := ha
  omega

/-- PDL validity for rest plus range-generated addresses -/
theorem pdl_valid_pairs_rest (rest : PDL) (v1 v2 n : Nat) (sz : Nat)
    (hrest : ∀ a ∈ rest, a < sz)
    (hv1 : v1 + n < sz) (hv2 : v2 + n < sz) :
    ∀ a ∈ ((List.range n).map (fun i => [v1 + 1 + i, v2 + 1 + i])).flatten ++ rest, a < sz := by
  intro a ha
  simp only [List.mem_append, List.mem_flatten, List.mem_map, List.mem_range] at ha
  cases ha with
  | inl h =>
    obtain ⟨pair, ⟨i, hi, hpair⟩, ha_in_pair⟩ := h
    subst hpair
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha_in_pair
    cases ha_in_pair with
    | inl h => omega
    | inr h => omega
  | inr h => exact hrest a h

/-- LIS PDL validity -/
theorem pdl_valid_lis_rest (rest : PDL) (h1 h2 : Nat) (sz : Nat)
    (hrest : ∀ a ∈ rest, a < sz)
    (hh1 : h1 + 1 < sz) (hh2 : h2 + 1 < sz) :
    ∀ a ∈ [h1, h2, h1 + 1, h2 + 1] ++ rest, a < sz := by
  intro a ha
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
  -- ha : a = h1 ∨ a = h2 ∨ a = h1 + 1 ∨ a = h2 + 1 ∨ a ∈ rest
  by_cases h : a = h1 <;> [omega; skip]
  by_cases h' : a = h2 <;> [omega; skip]
  by_cases h'' : a = h1 + 1 <;> [omega; skip]
  by_cases h''' : a = h2 + 1 <;> [omega; skip]
  -- Must be in rest
  have : a ∈ rest := by
    simp only [h, h', h'', h''', or_self, false_or] at ha
    exact ha
  exact hrest a this

/-- Step preserves PDL validity -/
theorem UnifyState.step_preserves_pdlValid (us : UnifyState)
    (hwf : us.heap.wellFormed) (hpdl : us.pdlValid) :
    (us.step).pdlValid := by
  unfold step pdlValid
  by_cases hfail : us.fail
  · simp only [hfail, ↓reduceIte]
    exact hpdl
  · simp only [hfail, Bool.false_eq_true, ↓reduceIte]
    match hpdl_match : us.pdl with
    | [] => intro a ha; exact hpdl a ha
    | [x] =>
      -- After step with singleton, pdl stays [x] but fail is set
      simp only
      intro a ha
      simp only [List.mem_singleton] at ha
      subst ha
      exact hpdl a (by rw [hpdl_match]; simp)
    | a1 :: a2 :: rest =>
      have ha1 : a1 < us.heap.cells.size := hpdl a1 (by rw [hpdl_match]; simp)
      have ha2 : a2 < us.heap.cells.size := hpdl a2 (by rw [hpdl_match]; simp)
      have hrest : ∀ a ∈ rest, a < us.heap.cells.size := by
        intro a ha
        exact hpdl a (by rw [hpdl_match]; simp [ha])
      have hd1 : us.heap.deref a1 < us.heap.cells.size := Heap.deref_terminates us.heap a1 ha1 hwf
      have hd2 : us.heap.deref a2 < us.heap.cells.size := Heap.deref_terminates us.heap a2 ha2 hwf
      by_cases heq : us.heap.deref a1 == us.heap.deref a2
      · simp only [heq, ↓reduceIte]
        exact hrest
      · simp only [heq, Bool.false_eq_true, ↓reduceIte]
        cases hg1 : us.heap.get? (us.heap.deref a1) with
        | none =>
          -- PDL becomes rest, heap unchanged
          simp only
          intro a ha
          exact hrest a ha
        | some c1 =>
          cases hg2 : us.heap.get? (us.heap.deref a2) with
          | none =>
            -- PDL becomes rest, heap unchanged
            simp only
            intro a ha
            exact hrest a ha
          | some c2 =>
            simp only
            -- Now analyze stepCells
            unfold stepCells
            cases c1 with
            | ref _ =>
              -- PDL is rest, heap may change but size preserved
              simp only [bind]
              intro a ha
              simp only [Heap.bind_size]
              exact hrest a ha
            | str v1 =>
              cases c2 with
              | ref _ =>
                simp only [bind]
                intro a ha
                simp only [Heap.bind_size]
                exact hrest a ha
              | str v2 =>
                simp only
                split
                · -- Both functors
                  rename_i f1 f2 hf1 hf2
                  split
                  · -- Same functor
                    intro a ha
                    have hwf1 := hwf (us.heap.deref a1) hd1
                    have hwf2 := hwf (us.heap.deref a2) hd2
                    unfold Heap.get? at hg1 hg2 hf1 hf2
                    simp only [hg1] at hwf1
                    simp only [hg2] at hwf2
                    have hv1_arity : v1 + f1.arity < us.heap.cells.size := by
                      simp only [hf1] at hwf1; exact hwf1.2
                    have hv2_arity : v2 + f2.arity < us.heap.cells.size := by
                      simp only [hf2] at hwf2; exact hwf2.2
                    rename_i hfeq
                    have hfeq' : f1 = f2 := by simpa using hfeq
                    subst hfeq'
                    exact pdl_valid_pairs_rest rest v1 v2 f1.arity us.heap.cells.size hrest hv1_arity hv2_arity a ha
                  · -- Different functor
                    intro a ha; exact hrest a ha
                -- Fallback case: not both functors
                all_goals (intro a ha; exact hrest a ha)
              | con _ => intro a ha; exact hrest a ha
              | functor _ => intro a ha; exact hrest a ha
              | lis _ => intro a ha; exact hrest a ha
            | con _ =>
              cases c2 with
              | ref _ =>
                simp only [bind]
                intro a ha
                simp only [Heap.bind_size]
                exact hrest a ha
              | str _ => intro a ha; exact hrest a ha
              | con f2 =>
                simp only
                split <;> (intro a ha; exact hrest a ha)
              | functor _ => intro a ha; exact hrest a ha
              | lis _ => intro a ha; exact hrest a ha
            | functor _ =>
              cases c2 with
              | ref _ =>
                simp only [bind]
                intro a ha
                simp only [Heap.bind_size]
                exact hrest a ha
              | _ => intro a ha; exact hrest a ha
            | lis h1 =>
              cases c2 with
              | ref _ =>
                simp only [bind]
                intro a ha
                simp only [Heap.bind_size]
                exact hrest a ha
              | str _ => intro a ha; exact hrest a ha
              | con _ => intro a ha; exact hrest a ha
              | functor _ => intro a ha; exact hrest a ha
              | lis h2 =>
                intro a ha
                have hwf1 := hwf (us.heap.deref a1) hd1
                have hwf2 := hwf (us.heap.deref a2) hd2
                unfold Heap.get? at hg1 hg2
                simp only [hg1] at hwf1
                simp only [hg2] at hwf2
                exact pdl_valid_lis_rest rest h1 h2 us.heap.cells.size hrest hwf1 hwf2 a ha

/-- Step preserves heap well-formedness when PDL contains valid addresses -/
theorem UnifyState.step_preserves_wf (us : UnifyState)
    (hwf : us.heap.wellFormed) (hpdl : us.pdlValid) :
    (us.step).heap.wellFormed := by
  unfold step
  by_cases hfail : us.fail
  · simp only [hfail, ↓reduceIte]; exact hwf
  · simp only [hfail, Bool.false_eq_true, ↓reduceIte]
    match hpdl_match : us.pdl with
    | [] => exact hwf
    | [_] => exact hwf
    | a1 :: a2 :: rest =>
      have ha1 : a1 < us.heap.cells.size := hpdl a1 (by rw [hpdl_match]; simp)
      have ha2 : a2 < us.heap.cells.size := hpdl a2 (by rw [hpdl_match]; simp)
      have hd1 : us.heap.deref a1 < us.heap.cells.size := Heap.deref_terminates us.heap a1 ha1 hwf
      have hd2 : us.heap.deref a2 < us.heap.cells.size := Heap.deref_terminates us.heap a2 ha2 hwf
      by_cases heq : us.heap.deref a1 == us.heap.deref a2
      · simp only [heq, ↓reduceIte]; exact hwf
      · simp only [heq, Bool.false_eq_true, ↓reduceIte]
        cases hg1 : us.heap.get? (us.heap.deref a1) with
        | none => exact hwf
        | some c1 =>
          cases hg2 : us.heap.get? (us.heap.deref a2) with
          | none => exact hwf
          | some c2 =>
            -- stepCells either keeps heap or uses bind
            cases stepCells_heap us (us.heap.deref a1) (us.heap.deref a2) c1 c2 rest with
            | inl h => rw [h]; exact hwf
            | inr h => rw [h]; exact bind_preserves_wf us _ _ hwf hd1 hd2

/-- Run preserves both well-formedness and PDL validity -/
theorem UnifyState.run_preserves (us : UnifyState) (fuel : Nat)
    (hwf : us.heap.wellFormed) (hpdl : us.pdlValid) :
    (us.run fuel).heap.wellFormed ∧ (us.run fuel).pdlValid := by
  induction fuel generalizing us with
  | zero => exact ⟨hwf, hpdl⟩
  | succ n ih =>
    unfold run
    by_cases hfail : us.fail
    · simp only [hfail]; exact ⟨hwf, hpdl⟩
    · simp only [hfail]
      by_cases hempty : us.pdl.isEmpty
      · simp only [hempty]; exact ⟨hwf, hpdl⟩
      · simp only [hempty]
        exact ih us.step (step_preserves_wf us hwf hpdl) (step_preserves_pdlValid us hwf hpdl)

/-- Run preserves heap well-formedness -/
theorem UnifyState.run_preserves_wf (us : UnifyState) (fuel : Nat)
    (hwf : us.heap.wellFormed) (hpdl : us.pdlValid) :
    (us.run fuel).heap.wellFormed :=
  (run_preserves us fuel hwf hpdl).1

/-- Unification preserves heap well-formedness -/
theorem UnifyState.unify_preserves_wf (us : UnifyState) (a1 a2 : HeapAddr)
    (hwf : us.heap.wellFormed) (ha1 : a1 < us.heap.cells.size) (ha2 : a2 < us.heap.cells.size) :
    (us.unify a1 a2).heap.wellFormed := by
  unfold unify
  have hpdl : ({ us with pdl := [a1, a2] } : UnifyState).pdlValid := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact ha1
    · exact ha2
  exact run_preserves_wf { us with pdl := [a1, a2] } _ hwf hpdl

/-- Bind preserves heap top in UnifyState -/
theorem UnifyState.bind_preserves_heap_top (us : UnifyState) (a1 a2 : HeapAddr) :
    (us.bind a1 a2).heap.top = us.heap.top := by
  unfold bind
  simp only
  split <;> exact Heap.bind_top us.heap _ _

/-- stepCells preserves heap size (only uses bind) -/
theorem UnifyState.stepCells_preserves_heap_size (us : UnifyState) (d1 d2 : HeapAddr)
    (c1 c2 : HeapCell) (rest : PDL) :
    (us.stepCells d1 d2 c1 c2 rest).heap.cells.size = us.heap.cells.size := by
  cases stepCells_heap us d1 d2 c1 c2 rest with
  | inl h => rw [h]
  | inr h =>
    rw [h]
    unfold bind
    simp only
    split <;> exact Heap.bind_size us.heap _ _

/-- step preserves heap size -/
theorem UnifyState.step_preserves_heap_size (us : UnifyState) :
    us.step.heap.cells.size = us.heap.cells.size := by
  unfold step
  split
  · rfl  -- fail case
  · match hpdl : us.pdl with
    | [] => rfl
    | [_] => rfl
    | a1 :: a2 :: rest =>
      simp only
      split
      · rfl  -- deref equal case
      · -- stepCells case
        cases hg1 : us.heap.get? (us.heap.deref a1) with
        | none => rfl
        | some c1 =>
          cases hg2 : us.heap.get? (us.heap.deref a2) with
          | none => rfl
          | some c2 => exact stepCells_preserves_heap_size us _ _ c1 c2 rest

/-- run preserves heap size -/
theorem UnifyState.run_preserves_heap_size (us : UnifyState) (fuel : Nat) :
    (us.run fuel).heap.cells.size = us.heap.cells.size := by
  induction fuel generalizing us with
  | zero => rfl
  | succ n ih =>
    unfold run
    split
    · rfl  -- fail or empty PDL case
    · rw [ih us.step, step_preserves_heap_size]

/-- Helper: after set, get? at src returns the new cell -/
theorem Heap.get?_set_self (h : Heap) (addr : HeapAddr) (cell : HeapCell)
    (hlt : addr < h.cells.size) :
    (h.set addr cell).get? addr = some cell := by
  unfold set get?
  simp only [hlt, ↓reduceDIte]
  rw [Array.getElem?_set]
  simp only [↓reduceIte]

/-- Helper: after set, get? at other addresses is unchanged -/
theorem Heap.get?_set_ne (h : Heap) (addr i : HeapAddr) (cell : HeapCell)
    (hne : i ≠ addr) :
    (h.set addr cell).get? i = h.get? i := by
  unfold set get?
  split
  · rw [Array.getElem?_set]
    have : addr ≠ i := fun h => hne h.symm
    simp only [this, ↓reduceIte]
  · rfl

/-- derefAux with more fuel returns the same result if we've reached a terminal -/
theorem Heap.derefAux_fuel_mono (h : Heap) (addr : HeapAddr) (fuel1 fuel2 : Nat)
    (hle : fuel1 ≤ fuel2) (hterm : h.isTerminal (h.derefAux addr fuel1) = true) :
    h.derefAux addr fuel2 = h.derefAux addr fuel1 := by
  induction fuel1 generalizing addr fuel2 with
  | zero =>
    simp only [derefAux] at hterm ⊢
    unfold isTerminal at hterm
    cases hg : h.get? addr with
    | none =>
      cases fuel2 with
      | zero => rfl
      | succ n => simp only [derefAux, hg]
    | some c =>
      cases c with
      | ref a =>
        simp only [hg] at hterm
        have heq : a = addr := by simpa using hterm
        cases fuel2 with
        | zero => rfl
        | succ n => simp only [derefAux, hg, heq, beq_self_eq_true, ↓reduceIte]
      | str _ | con _ | functor _ | lis _ =>
        cases fuel2 with
        | zero => rfl
        | succ n => simp only [derefAux, hg]
  | succ n ih =>
    cases fuel2 with
    | zero => omega
    | succ m =>
      simp only [derefAux]
      cases hg : h.get? addr with
      | none => rfl
      | some c =>
        cases c with
        | ref a =>
          by_cases heq : a == addr
          · simp only [heq, ↓reduceIte]
          · simp only [heq, Bool.false_eq_true, ↓reduceIte]
            apply ih
            · omega
            · simp only [derefAux, hg, heq, Bool.false_eq_true, ↓reduceIte] at hterm
              exact hterm
        | _ => rfl

/-- After binding src to tgt, derefAux from src follows the REF to tgt -/
theorem Heap.derefAux_bind_src (h : Heap) (src tgt : HeapAddr) (fuel : Nat)
    (hsrc : src < h.cells.size) (_htgt : tgt < h.cells.size) (hne : src ≠ tgt) :
    (h.bind src tgt).derefAux src (fuel + 1) = (h.bind src tgt).derefAux tgt fuel := by
  unfold bind
  simp only [derefAux]
  have hget : (h.set src (.ref tgt)).get? src = some (.ref tgt) := get?_set_self h src (.ref tgt) hsrc
  rw [hget]
  have hne' : tgt ≠ src := fun h => hne h.symm
  have hbeq : (tgt == src) = false := beq_eq_false_iff_ne.mpr hne'
  simp only [hbeq, Bool.false_eq_true, ↓reduceIte]

/-- Binding src to tgt doesn't affect derefAux from any address start ≠ src,
    as long as src is not reachable from start.
    Helper for chain analysis - proves deref equality after bind. -/
theorem Heap.derefAux_bind_ne (h : Heap) (src tgt start : HeapAddr) (fuel : Nat)
    (hne_start : start ≠ src) (hnotreach : h.notReachableFrom src start) :
    (h.bind src tgt).derefAux start fuel = h.derefAux start fuel := by
  -- Induct on fuel
  match fuel with
  | 0 => simp only [derefAux]
  | fuel' + 1 =>
    simp only [derefAux]
    -- Get cell at start in bound vs original heap (unchanged since start ≠ src)
    have hget_eq : (h.bind src tgt).get? start = h.get? start := by
      unfold bind
      exact get?_set_ne h src start (.ref tgt) hne_start
    rw [hget_eq]
    match hcell : h.get? start with
    | none => rfl
    | some (.ref next) =>
      if heq : next == start then
        simp only [heq, ite_true]
      else
        simp only [heq]
        -- Need: next ≠ src and src not reachable from next
        have hne_next : next ≠ src := by
          intro h_eq
          subst h_eq  -- replaces src with next in context
          have hbeq : (next == start) = false := beq_eq_false_iff_ne.mpr (Ne.symm hne_start)
          have hreach1 : h.derefAux start 1 = next := by
            simp only [derefAux, hcell, hbeq, Bool.false_eq_true, ite_false]
          exact hnotreach 1 hreach1
        have hnotreach_next : h.notReachableFrom src next := by
          intro k hk
          have hbeq : (next == start) = false := beq_eq_false_iff_ne.mpr (fun h_eq => heq (beq_self_eq_true next ▸ h_eq ▸ rfl))
          have hreach : h.derefAux start (k + 1) = src := by
            simp only [derefAux, hcell, hbeq, Bool.false_eq_true, ite_false, hk]
          exact hnotreach (k + 1) hreach
        exact derefAux_bind_ne h src tgt next fuel' hne_next hnotreach_next
    | some (.str _) => rfl
    | some (.con _) => rfl
    | some (.functor _) => rfl
    | some (.lis _) => rfl
termination_by fuel

/-- Binding src to tgt doesn't affect derefAux from tgt (if src not reachable from tgt) -/
theorem Heap.derefAux_bind_tgt (h : Heap) (src tgt : HeapAddr) (fuel : Nat)
    (_hsrc : src < h.cells.size) (hne : src ≠ tgt)
    (hnotreach : h.notReachableFrom src tgt) :
    (h.bind src tgt).derefAux tgt fuel = h.derefAux tgt fuel :=
  derefAux_bind_ne h src tgt tgt fuel (Ne.symm hne) hnotreach

/-- After binding src to tgt, deref of src equals deref of tgt.
    This is the key lemma for unification correctness.
    Requires that src is not reachable from tgt (otherwise binding creates a cycle).
    Also requires wellFormed heap with descending chains (WAM invariant). -/
theorem Heap.bind_deref_eq (h : Heap) (src tgt : HeapAddr)
    (hsrc : src < h.cells.size) (htgt : tgt < h.cells.size)
    (hne : src ≠ tgt) (hnotreach : h.notReachableFrom src tgt)
    (hwf : h.wellFormed) (hdesc : h.chainsDescend) :
    (h.bind src tgt).deref src = (h.bind src tgt).deref tgt := by
  unfold deref
  have hsize : (h.bind src tgt).cells.size = h.cells.size := bind_size h src tgt
  cases hsz : h.cells.size with
  | zero =>
    simp_all
  | succ n =>
    rw [hsize, hsz]
    -- derefAux src (n+1) = derefAux tgt n by derefAux_bind_src
    rw [derefAux_bind_src h src tgt n (by omega) (by omega) hne]
    -- derefAux tgt n = derefAux tgt (n+1) when tgt's chain is unaffected by bind
    -- Use derefAux_bind_ne to show bound heap equals original from tgt
    have hbind_eq := derefAux_bind_ne h src tgt tgt n (Ne.symm hne) hnotreach
    rw [hbind_eq]
    -- Now need: h.derefAux tgt n = (h.bind src tgt).derefAux tgt (n+1)
    -- The RHS is the same as h.derefAux tgt (n+1) by derefAux_bind_ne
    have hbind_eq' := derefAux_bind_ne h src tgt tgt (n+1) (Ne.symm hne) hnotreach
    rw [hbind_eq']
    -- Now just need h.derefAux tgt n = h.derefAux tgt (n+1)
    -- Use derefAux_converges: if chainsDescend and n ≥ tgt, then derefAux tgt n = derefAux tgt (n+1)
    have htgt_n : tgt < n + 1 := by rw [← hsz]; exact htgt
    have hn_ge_tgt : n ≥ tgt := Nat.lt_succ_iff.mp htgt_n
    exact derefAux_converges h tgt n htgt hwf hdesc hn_ge_tgt

/-- UnifyState bind establishes deref equality.
    Requires that higher address is not reachable from lower (WAM invariant).
    Also requires wellFormed heap with descending chains. -/
theorem UnifyState.bind_deref_eq (us : UnifyState) (a1 a2 : HeapAddr)
    (ha1 : a1 < us.heap.cells.size) (ha2 : a2 < us.heap.cells.size)
    (hne : a1 ≠ a2)
    (hnotreach : if a1 > a2 then us.heap.notReachableFrom a1 a2
                 else us.heap.notReachableFrom a2 a1)
    (hwf : us.heap.wellFormed) (hdesc : us.heap.chainsDescend) :
    (us.bind a1 a2).heap.deref a1 = (us.bind a1 a2).heap.deref a2 := by
  unfold bind
  simp only
  split_ifs with hgt
  · -- a1 > a2: bind a1 to a2, tgt = a2
    simp only [hgt, ↓reduceIte] at hnotreach
    exact Heap.bind_deref_eq us.heap a1 a2 ha1 ha2 (Nat.ne_of_gt hgt) hnotreach hwf hdesc
  · -- a1 <= a2: bind a2 to a1, tgt = a1
    push_neg at hgt
    have hlt : a1 < a2 := Nat.lt_of_le_of_ne hgt hne
    simp only [Nat.not_lt.mpr (Nat.le_of_lt hlt), ↓reduceIte] at hnotreach
    have h := Heap.bind_deref_eq us.heap a2 a1 ha2 ha1 (Ne.symm hne) hnotreach hwf hdesc
    exact h.symm

/-- If deref a = d and d is terminal with a REF cell, then that REF is self-referential.
    This follows from the definition of deref: a REF cell that's not self-referential
    would cause deref to continue following the chain. -/
theorem Heap.deref_ref_is_selfref (h : Heap) (a d : HeapAddr) (r : HeapAddr)
    (ha_deref : h.deref a = d)
    (hd_lt : d < h.cells.size)
    (hwf : h.wellFormed)
    (hdesc : h.chainsDescend)
    (hcell : h.get? d = some (.ref r)) :
    r = d := by
  -- If r ≠ d, then d is not terminal, contradicting that deref stops at d
  by_contra hne
  have hne' : (r == d) = false := beq_eq_false_iff_ne.mpr hne
  -- d is terminal (deref returns terminals on well-formed descending heaps)
  have hterm : h.isTerminal d = true := by
    -- Since deref a = d, derefAux a (h.cells.size) = d
    -- And derefAux terminates at a terminal when given enough fuel
    rw [← ha_deref]
    unfold deref
    by_cases ha_valid : a < h.cells.size
    · exact derefAux_terminates h a h.cells.size ha_valid hdesc hwf (Nat.le_of_lt ha_valid)
    · -- a ≥ size: derefAux returns a immediately
      push_neg at ha_valid
      -- Show isTerminal a = true when a ≥ size
      -- When a ≥ size, get? a = none (no valid cell)
      -- First, show derefAux a size = a
      have hderef_a : h.derefAux a h.cells.size = a := by
        unfold derefAux
        cases h.cells.size with
        | zero => rfl
        | succ n =>
          unfold get?
          have ha_none : h.cells[a]? = none := by
            rw [Array.getElem?_eq_none_iff]
            exact ha_valid
          simp only [ha_none]
      rw [hderef_a]
      unfold isTerminal get?
      have ha_none : h.cells[a]? = none := by
        rw [Array.getElem?_eq_none_iff]
        exact ha_valid
      simp only [ha_none]
  -- But isTerminal d = (r == d) since cell at d is ref r
  simp only [isTerminal, hcell, hne'] at hterm
  exact Bool.false_ne_true hterm

/-- Helper: if deref a = d where d is terminal and a ≠ d, then a has a REF cell to some a' < a -/
theorem Heap.deref_chain_step (h : Heap) (a d : HeapAddr)
    (ha_deref : h.deref a = d)
    (ha_ne : a ≠ d)
    (ha_lt : a < h.cells.size)
    (hwf : h.wellFormed)
    (hdesc : h.chainsDescend) :
    ∃ a', h.get? a = some (.ref a') ∧ a' < a ∧ h.deref a' = d := by
  unfold deref at ha_deref
  -- Since a ≠ d and deref a = d, there must be at least one step
  cases hsz : h.cells.size with
  | zero =>
    -- a < 0 is impossible
    simp only [hsz] at ha_lt
    exact absurd ha_lt (Nat.not_lt_zero a)
  | succ n =>
    have ha_lt_n : a < n + 1 := by rw [← hsz]; exact ha_lt
    have ha_lt_orig : a < h.cells.size := ha_lt
    rw [hsz] at ha_deref
    simp only [derefAux] at ha_deref
    cases hcell : h.get? a with
    | none =>
      -- If no cell, derefAux returns a, so d = a. Contradiction.
      simp only [hcell] at ha_deref
      exact False.elim (ha_ne ha_deref)
    | some c =>
      simp only [hcell] at ha_deref
      cases c with
      | ref a' =>
        by_cases heq : a' == a
        · -- Self-ref: derefAux returns a, so d = a. Contradiction.
          simp only [heq, ite_true] at ha_deref
          exact False.elim (ha_ne ha_deref)
        · -- Not self-ref: follows to a'
          simp only [heq] at ha_deref
          -- a' < a by chainsDescend
          have hdesc_a := hdesc a ha_lt_orig
          have hcell' : h.cells[a]? = some (.ref a') := by
            unfold get? at hcell
            exact hcell
          simp only [hcell'] at hdesc_a
          have ha'_lt_a : a' < a := by
            cases hdesc_a with
            | inl h_eq =>
              -- a' = a contradicts heq
              have heq_true : (a' == a) = true := by rw [h_eq]; exact beq_self_eq_true a
              exact absurd heq_true heq
            | inr h_lt => exact h_lt
          -- h.deref a' = d
          have ha'_valid : a' < h.cells.size := by
            unfold wellFormed at hwf
            have := hwf a ha_lt_orig
            simp only [hcell'] at this
            exact this
          -- derefAux a' n converges to d
          have hn_ge : n ≥ a' := by
            have ha_le : a ≤ n := Nat.lt_succ_iff.mp ha_lt_n
            have : a' < n + 1 := Nat.lt_of_lt_of_le ha'_lt_a (Nat.le_succ_of_le ha_le)
            exact Nat.lt_succ_iff.mp this
          have ha'_lt_size : a' < h.cells.size := ha'_valid
          rw [hsz] at ha'_lt_size
          have hconv := derefAux_converges h a' n ha'_valid hwf hdesc hn_ge
          refine ⟨a', rfl, ha'_lt_a, ?_⟩
          unfold deref
          rw [hsz, ← hconv]
          -- Simplify ha_deref which has if false = true
          have ha_deref' : h.derefAux a' n = d := by
            simp only [Bool.false_eq_true, ↓reduceIte] at ha_deref
            exact ha_deref
          exact ha_deref'
      | str _ =>
        -- STR is terminal, so derefAux returns a = d. Contradiction.
        simp only at ha_deref
        exact False.elim (ha_ne ha_deref)
      | con _ =>
        simp only at ha_deref
        exact False.elim (ha_ne ha_deref)
      | lis _ =>
        simp only at ha_deref
        exact False.elim (ha_ne ha_deref)
      | functor _ =>
        simp only at ha_deref
        exact False.elim (ha_ne ha_deref)

/-- If h.deref a = d and d is a self-referential REF, then after binding d to tgt,
    the deref of a on the new heap equals the deref of tgt on the new heap.
    Uses strong induction on a. Requires tgt ≤ d (binding higher to lower). -/
theorem Heap.deref_through_selfref_bind (h : Heap) (a d tgt : HeapAddr)
    (ha_deref : h.deref a = d)
    (hd_selfref : h.get? d = some (.ref d))
    (hd_lt : d < h.cells.size)
    (htgt_lt : tgt < h.cells.size)
    (hne : d ≠ tgt)
    (hle : tgt ≤ d)  -- WAM invariant: bind higher to lower
    (hwf : h.wellFormed)
    (hdesc : h.chainsDescend)
    (hnotreach : h.notReachableFrom d tgt) :
    (h.bind d tgt).deref a = (h.bind d tgt).deref tgt := by
  -- Use bind_deref_eq to show (h.bind d tgt).deref d = (h.bind d tgt).deref tgt
  have hderefs_eq := bind_deref_eq h d tgt hd_lt htgt_lt hne hnotreach hwf hdesc
  -- Suffices to show (h.bind d tgt).deref a = (h.bind d tgt).deref d
  suffices h_chain : (h.bind d tgt).deref a = (h.bind d tgt).deref d by
    rw [h_chain, hderefs_eq]
  -- Strong induction on a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    -- Case 1: a = d
    by_cases ha_eq : a = d
    · subst ha_eq; rfl
    · -- Case 2: a ≠ d, use chain step
      -- Need a < h.cells.size for chain_step
      by_cases ha_valid : a < h.cells.size
      · -- Get the chain step: a has ref a' with a' < a and deref a' = d
        have ⟨a', hcell_a, ha'_lt, ha'_deref⟩ := deref_chain_step h a d ha_deref ha_eq ha_valid hwf hdesc
        -- After bind, cell at a is unchanged (since a ≠ d)
        have hcell_bind : (h.bind d tgt).get? a = some (.ref a') := by
          unfold bind
          have ha_ne_d : a ≠ d := ha_eq
          exact get?_set_ne h d a (.ref tgt) ha_ne_d ▸ hcell_a
        -- IH: (h.bind d tgt).deref a' = (h.bind d tgt).deref d
        have ha'_valid : a' < h.cells.size := Nat.lt_trans ha'_lt ha_valid
        have hih := ih a' ha'_lt ha'_deref
        -- Now show (h.bind d tgt).deref a follows ref to a', then equals deref a'
        -- We'll work with (h.bind d tgt).derefAux directly
        have hsize : (h.bind d tgt).cells.size = h.cells.size := bind_size h d tgt
        -- Unfold deref and rewrite sizes
        unfold deref
        rw [hsize]
        -- Goal is now: (h.bind d tgt).derefAux a h.cells.size = (h.bind d tgt).derefAux d h.cells.size
        -- Now work with h.cells.size
        cases hsz : h.cells.size with
        | zero => simp_all
        | succ n =>
          -- Rewrite hih using hsize
          have hih' : (h.bind d tgt).derefAux a' (n + 1) = (h.bind d tgt).derefAux d (n + 1) := by
            have := ih a' ha'_lt ha'_deref
            unfold deref at this
            rw [hsize, hsz] at this
            exact this
          rw [hsz] at ha_valid ha'_valid
          simp only [derefAux, hcell_bind]
          -- a' ≠ a since a' < a
          have ha'_ne_a : (a' == a) = false := by
            have : a' ≠ a := Nat.ne_of_lt ha'_lt
            exact beq_eq_false_iff_ne.mpr this
          simp only [ha'_ne_a, Bool.false_eq_true, ite_false]
          -- LHS is now: (h.bind d tgt).derefAux a' n
          -- RHS has a match on (h.bind d tgt).get? d
          -- Simplify RHS: after bind d tgt, cell at d is ref tgt (not self-ref anymore)
          have hcell_d_bind : (h.bind d tgt).get? d = some (.ref tgt) := by
            unfold bind
            exact get?_set_self h d (.ref tgt) hd_lt
          simp only [hcell_d_bind]
          -- Now RHS is: if (tgt == d) then d else (h.bind d tgt).derefAux tgt n
          have htgt_ne_d : (tgt == d) = false := by
            have : tgt ≠ d := Ne.symm hne
            exact beq_eq_false_iff_ne.mpr this
          simp only [htgt_ne_d]
          -- Goal: (h.bind d tgt).derefAux a' n = (h.bind d tgt).derefAux tgt n
          -- We have hih' : (h.bind d tgt).derefAux a' (n+1) = (h.bind d tgt).derefAux d (n+1)
          -- But after bind, derefAux d (n+1) = derefAux tgt n
          -- Use derefAux_bind_src
          have hd_step := derefAux_bind_src h d tgt n hd_lt htgt_lt hne
          -- hd_step : (h.bind d tgt).derefAux d (n+1) = (h.bind d tgt).derefAux tgt n
          -- Also need: (h.bind d tgt).derefAux a' n = (h.bind d tgt).derefAux a' (n+1)
          have hn_ge : n ≥ a' := Nat.lt_succ_iff.mp ha'_valid
          have ha'_lt_orig : a' < h.cells.size := by rw [hsz]; exact ha'_valid
          have hbind_wf := bind_preserves_wf h d tgt hwf htgt_lt
          have hbind_desc := bind_preserves_chainsDescend h d tgt hdesc hd_lt hle
          have ha'_lt_bind : a' < (h.bind d tgt).cells.size := by rw [hsize]; exact ha'_lt_orig
          have hconv := derefAux_converges (h.bind d tgt) a' n ha'_lt_bind hbind_wf hbind_desc hn_ge
          rw [hconv, hih', hd_step]
          simp only [Bool.false_eq_true, ite_false]
      · -- a ≥ size: deref a = a, but deref a = d with d < size. Contradiction.
        push_neg at ha_valid
        unfold deref at ha_deref
        cases hsz : h.cells.size with
        | zero =>
          simp only [hsz] at hd_lt
          exact absurd hd_lt (Nat.not_lt_zero d)
        | succ n =>
          rw [hsz] at ha_deref hd_lt ha_valid
          simp only [derefAux] at ha_deref
          cases hcell : h.get? a with
          | none =>
            simp only [hcell] at ha_deref
            -- ha_deref : a = d, but a ≥ n+1 > d. Contradiction.
            have : d < a := Nat.lt_of_lt_of_le hd_lt ha_valid
            exact absurd ha_deref.symm (Nat.ne_of_lt this)
          | some c =>
            -- get? a = some c means a < size, contradiction
            -- But ha_valid says a ≥ n+1 = size, so get? a = none
            -- The some c case is impossible
            unfold get? at hcell
            have ha_none : h.cells[a]? = none := Array.getElem?_eq_none_iff.mpr (by rw [hsz]; exact ha_valid)
            simp only [ha_none] at hcell
            cases hcell

/-- If deref a = d on old heap, and we bind d to tgt where tgt is self-ref terminal,
    then deref a = tgt on new heap.
    Unlike deref_through_selfref_bind, this doesn't require d to be self-ref. -/
theorem Heap.deref_through_bind_to_selfref (h : Heap) (a d tgt : HeapAddr)
    (ha_deref : h.deref a = d)
    (hd_lt : d < h.cells.size)
    (htgt_lt : tgt < h.cells.size)
    (htgt_selfref : h.get? tgt = some (.ref tgt))
    (hne : d ≠ tgt)
    (hle : tgt ≤ d)  -- WAM invariant: bind higher to lower
    (hwf : h.wellFormed)
    (hdesc : h.chainsDescend)
    (hnotreach : h.notReachableFrom d tgt) :
    (h.bind d tgt).deref a = tgt := by
  -- After bind d tgt, cell at d becomes ref tgt
  -- a's chain on new heap: a → ... → d → tgt → tgt (self-loop terminal)
  -- So deref a = tgt on new heap
  have hcell_d_bind : (h.bind d tgt).get? d = some (.ref tgt) := by
    unfold bind
    exact get?_set_self h d (.ref tgt) hd_lt
  have hsize : (h.bind d tgt).cells.size = h.cells.size := bind_size h d tgt
  -- tgt's cell unchanged (since tgt ≠ d)
  have hcell_tgt_bind : (h.bind d tgt).get? tgt = h.get? tgt := by
    unfold bind
    exact get?_set_ne h d tgt (.ref tgt) (Ne.symm hne)
  -- deref tgt = tgt on new heap (still self-ref terminal)
  have hderef_tgt_new : (h.bind d tgt).deref tgt = tgt := by
    unfold deref
    rw [hsize]
    cases hsz : h.cells.size with
    | zero => simp_all
    | succ n =>
      simp only [derefAux, hcell_tgt_bind, htgt_selfref, beq_self_eq_true, ↓reduceIte]
  -- Now show deref a = tgt on new heap by strong induction
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    by_cases ha_eq : a = d
    · -- a = d: deref d follows ref to tgt
      rw [ha_eq]
      unfold deref
      rw [hsize]
      cases hsz : h.cells.size with
      | zero => simp_all
      | succ n =>
        simp only [derefAux, hcell_d_bind]
        have htgt_ne_d : (tgt == d) = false := beq_eq_false_iff_ne.mpr (Ne.symm hne)
        simp only [htgt_ne_d, Bool.false_eq_true, ite_false]
        -- Now need derefAux tgt n = tgt
        -- tgt is self-ref, so this is immediate
        have htgt_lt' : tgt < n + 1 := by rw [← hsz]; exact htgt_lt
        have hn_ge : n ≥ tgt := Nat.lt_succ_iff.mp htgt_lt'
        have hbind_wf := bind_preserves_wf h d tgt hwf htgt_lt
        have hbind_desc := bind_preserves_chainsDescend h d tgt hdesc hd_lt hle
        have htgt_lt_bind : tgt < (h.bind d tgt).cells.size := by rw [hsize]; exact htgt_lt
        have hconv := derefAux_converges (h.bind d tgt) tgt n htgt_lt_bind hbind_wf hbind_desc hn_ge
        rw [hconv]
        simp only [derefAux, hcell_tgt_bind, htgt_selfref, beq_self_eq_true, ↓reduceIte]
    · -- a ≠ d: first need to check if a < size
      by_cases ha_valid : a < h.cells.size
      · -- Get the chain step from old heap
        by_cases ha_eq_tgt : a = tgt
        · -- a = tgt: just return tgt
          subst ha_eq_tgt
          exact hderef_tgt_new
        · -- a ≠ d and a ≠ tgt: cell at a unchanged
          have hcell_a_bind : (h.bind d tgt).get? a = h.get? a := by
            unfold bind
            exact get?_set_ne h d a (.ref tgt) ha_eq
          unfold deref
          rw [hsize]
          cases hsz : h.cells.size with
          | zero => simp_all
          | succ n =>
            cases hcell_a : h.get? a with
            | none =>
              -- a has no cell, so deref a = a on old heap. But deref a = d. So a = d. Contradiction.
              unfold deref at ha_deref
              rw [hsz] at ha_deref
              simp only [derefAux, hcell_a] at ha_deref
              exact absurd ha_deref ha_eq
            | some ca =>
              simp only [derefAux, hcell_a_bind, hcell_a]
              cases ca with
              | ref next =>
                by_cases heq_self : next == a
                · -- Self-ref at a: deref a = a on old heap. But deref a = d. So a = d. Contradiction.
                  simp only [heq_self, ↓reduceIte]
                  unfold deref at ha_deref
                  rw [hsz] at ha_deref
                  simp only [derefAux, hcell_a, heq_self, ↓reduceIte] at ha_deref
                  exact absurd ha_deref ha_eq
                · -- Non-self-ref: follows chain
                  simp only [heq_self, Bool.false_eq_true, ↓reduceIte]
                  -- next < a by chainsDescend
                  have hdesc_a := hdesc a ha_valid
                  unfold get? at hcell_a
                  simp only [hcell_a] at hdesc_a
                  have hnext_lt_a : next < a := by
                    cases hdesc_a with
                    | inl h_eq =>
                      have heq_true : (next == a) = true := by rw [h_eq]; exact beq_self_eq_true a
                      exact absurd heq_true heq_self
                    | inr h_lt => exact h_lt
                  -- deref next = d on old heap
                  have hnext_valid : next < h.cells.size := Nat.lt_trans hnext_lt_a ha_valid
                  have hnext_valid' : next < n + 1 := by rw [← hsz]; exact hnext_valid
                  have hn_ge : n ≥ next := Nat.lt_succ_iff.mp hnext_valid'
                  -- Convert hcell_a to get? form
                  have hcell_a_get : h.get? a = some (.ref next) := by
                    unfold get?
                    simp only [hcell_a]
                  have hnext_deref : h.deref next = d := by
                    unfold deref at ha_deref ⊢
                    rw [hsz] at ha_deref
                    simp only [derefAux, hcell_a_get] at ha_deref
                    have hne_self : (next == a) = false := beq_eq_false_iff_ne.mpr (Nat.ne_of_lt hnext_lt_a)
                    simp only [hne_self, Bool.false_eq_true, ite_false] at ha_deref
                    rw [hsz]
                    have hconv := derefAux_converges h next n hnext_valid hwf hdesc hn_ge
                    rw [← hconv, ha_deref]
                  -- IH: deref next = tgt on new heap
                  have hih := ih next hnext_lt_a hnext_deref
                  -- Result: derefAux next n = tgt on new heap
                  unfold deref at hih
                  rw [hsize, hsz] at hih
                  have hbind_wf := bind_preserves_wf h d tgt hwf htgt_lt
                  have hbind_desc := bind_preserves_chainsDescend h d tgt hdesc hd_lt hle
                  have hnext_lt_bind : next < (h.bind d tgt).cells.size := by rw [hsize]; exact hnext_valid
                  have hconv := derefAux_converges (h.bind d tgt) next n hnext_lt_bind hbind_wf hbind_desc hn_ge
                  rw [hconv, hih]
              | str _ | con _ | lis _ | functor _ =>
                -- Terminal cell at a: deref a = a on old heap. But deref a = d. So a = d. Contradiction.
                unfold deref at ha_deref
                rw [hsz] at ha_deref
                simp only [derefAux, hcell_a] at ha_deref
                exact absurd ha_deref ha_eq
      · -- a ≥ size: invalid address
        push_neg at ha_valid
        unfold deref at ha_deref
        cases hsz : h.cells.size with
        | zero => simp_all
        | succ n =>
          rw [hsz] at ha_deref hd_lt ha_valid
          simp only [derefAux] at ha_deref
          cases hcell : h.get? a with
          | none =>
            simp only [hcell] at ha_deref
            have : d < a := Nat.lt_of_lt_of_le hd_lt ha_valid
            exact absurd ha_deref.symm (Nat.ne_of_lt this)
          | some c =>
            unfold get? at hcell
            have ha_none : h.cells[a]? = none := Array.getElem?_eq_none_iff.mpr (by rw [hsz]; exact ha_valid)
            simp only [ha_none] at hcell
            cases hcell

/-- If d is terminal and deref a ≠ d, then d is not reachable from a.
    This is the contrapositive of: if d reachable from a, then deref a = d. -/
theorem Heap.notReachableFrom_of_terminal_ne (h : Heap) (d a : HeapAddr)
    (hterm : h.isTerminal d = true) (ha_deref : h.deref a ≠ d)
    (ha_lt : a < h.cells.size) (hwf : h.wellFormed) (hdesc : h.chainsDescend) :
    h.notReachableFrom d a := by
  intro k hk
  -- If derefAux a k = d, then since d is terminal, deref a = d
  -- But we have deref a ≠ d, contradiction
  -- Key: derefAux stays at terminal addresses
  have : h.deref a = d := by
    unfold deref
    cases hsz : h.cells.size with
    | zero => simp_all
    | succ n =>
      -- Need to show: derefAux a (n+1) = d given derefAux a k = d and d is terminal
      -- Since d is terminal, for any fuel f, derefAux d f = d
      -- The chain: derefAux a (n+1) either reaches d before n+1 steps, or doesn't hit d at all
      -- If derefAux a k = d for some k ≤ n+1, then all subsequent steps also return d
      by_cases hk_le : k ≤ n
      · -- k ≤ n: derefAux a k = d, and we need derefAux a (n+1) = d
        -- Use fuel monotonicity: derefAux increases fuel preserves terminal result
        have hterm_k : h.isTerminal (h.derefAux a k) = true := by rw [hk]; exact hterm
        exact (derefAux_fuel_mono h a k (n + 1) (Nat.le_succ_of_le hk_le) hterm_k).symm ▸ hk
      · -- k > n: but derefAux a k with k > size should give same result as derefAux a size
        -- Since chains descend and we have wellFormed, the chain terminates in ≤ a steps
        push_neg at hk_le
        -- If k > n ≥ a (since a < n+1 = size), then derefAux a k should equal derefAux a a
        have ha_lt' : a < n + 1 := hsz ▸ ha_lt
        have ha_le_n : a ≤ n := Nat.lt_succ_iff.mp ha_lt'
        have hconv := derefAux_converges h a n ha_lt hwf hdesc ha_le_n
        -- But hk says derefAux a k = d. If k > n and derefAux converges at n, then derefAux a k = derefAux a n = derefAux a (n+1)
        have hterm_n : h.isTerminal (h.derefAux a n) = true :=
          derefAux_terminates h a n ha_lt hdesc hwf ha_le_n
        have hk_n := derefAux_fuel_mono h a n k (Nat.le_of_lt hk_le) hterm_n
        rw [hk_n] at hk
        rw [← hconv, hk]
  exact ha_deref this

/-- After step with PDL = [a1, a2], if PDL becomes empty and no fail,
    then the terms are structurally equal.

    Key cases where PDL becomes empty after step:
    1. deref a1 = deref a2: Already equal, termEq trivial
    2. One is REF: After bind, derefs equal → termEq (needs bind_deref_eq infrastructure)
    3. Both CON with same value: termEq by constant comparison
    4. Both STR/LIS: Subterms pushed, PDL not empty (contradiction)

    Note: Requires wellFormed heap and chainsDescend for bind_deref_eq. -/
theorem UnifyState.step_pair_termEq (us : UnifyState) (a1 a2 : HeapAddr)
    (hpdl : us.pdl = [a1, a2])
    (hnotfail : ¬us.fail)
    (hstep_ok : ¬us.step.fail)
    (hempty_step : us.step.pdl.isEmpty)
    (hvalid1 : a1 < us.heap.cells.size)
    (hvalid2 : a2 < us.heap.cells.size)
    (hwf : us.heap.wellFormed)
    (hdesc : us.heap.chainsDescend) :
    us.step.heap.termEq a1 a2 := by
  -- Unfold step and analyze cases
  unfold step at hstep_ok hempty_step ⊢
  simp only [hnotfail, Bool.false_eq_true, ↓reduceIte, hpdl] at hstep_ok hempty_step ⊢
  -- Let d1 = deref a1, d2 = deref a2
  set d1 := us.heap.deref a1 with hd1_def
  set d2 := us.heap.deref a2 with hd2_def
  -- Case on whether derefs are equal
  by_cases heq_deref : d1 == d2
  · -- Case 1: derefs equal, heap unchanged
    simp only [heq_deref, ↓reduceIte]
    have heq' : us.heap.deref a1 = us.heap.deref a2 := by
      simp only [beq_iff_eq] at heq_deref; exact heq_deref
    exact Heap.termEq_of_deref_eq us.heap a1 a2 heq'
  · -- Case 2: derefs different, need to look at cells
    simp only [heq_deref, Bool.false_eq_true, ↓reduceIte] at hstep_ok hempty_step ⊢
    have hd1_lt : d1 < us.heap.cells.size := Heap.deref_terminates us.heap a1 hvalid1 hwf
    have hd2_lt : d2 < us.heap.cells.size := Heap.deref_terminates us.heap a2 hvalid2 hwf
    cases hg1 : us.heap.get? d1 with
    | none =>
      -- Invalid cell at d1 → step fails (contradiction)
      simp only [hg1] at hstep_ok
      exact absurd trivial hstep_ok
    | some c1 =>
      cases hg2 : us.heap.get? d2 with
      | none =>
        -- Invalid cell at d2 → step fails (contradiction)
        simp only [hg1, hg2] at hstep_ok
        exact absurd trivial hstep_ok
      | some c2 =>
        -- Both cells valid, analyze stepCells
        simp only [hg1, hg2] at hstep_ok hempty_step ⊢
        -- stepCells cases
        unfold stepCells at hstep_ok hempty_step ⊢
        cases c1 with
        | ref r =>
          -- REF case: bind makes derefs equal
          simp only at hempty_step hstep_ok ⊢
          -- After bind, use termEq_of_deref_eq
          have hne : d1 ≠ d2 := by simp only [beq_iff_eq, ne_eq] at heq_deref ⊢; exact heq_deref
          -- d1 is terminal with ref r cell, so r = d1 (self-referential)
          have hr_eq : r = d1 := Heap.deref_ref_is_selfref us.heap a1 d1 r hd1_def.symm hd1_lt hwf hdesc hg1
          -- d1 is self-referential (r = d1)
          have hd1_selfref : us.heap.get? d1 = some (.ref d1) := by subst hr_eq; exact hg1
          -- Get hd2_lt before establishing notReachableFrom
          have hd2_lt : d2 < us.heap.cells.size := Heap.deref_terminates us.heap a2 hvalid2 hwf
          -- Establish notReachableFrom based on bind direction
          have hnotreach : if d1 > d2 then us.heap.notReachableFrom d1 d2
                          else us.heap.notReachableFrom d2 d1 := by
            split_ifs with hgt
            · exact Heap.notReachableFrom_of_gt us.heap d1 d2 hd2_lt hgt hdesc
            · push_neg at hgt
              have hlt : d1 < d2 := Nat.lt_of_le_of_ne hgt hne
              exact Heap.notReachableFrom_of_gt us.heap d2 d1 hd1_lt hlt hdesc
          -- Split on bind direction
          unfold bind
          split_ifs with hgt
          · -- Case d1 > d2: bind d1 to d2
            simp only
            -- Use deref_through_selfref_bind: after binding d1 to d2,
            -- deref a1 on new heap = deref d2 on new heap
            have hle : d2 ≤ d1 := Nat.le_of_lt hgt
            have hnotreach' : us.heap.notReachableFrom d1 d2 := by simp only [hgt, ↓reduceIte] at hnotreach; exact hnotreach
            have hderef_a1 := Heap.deref_through_selfref_bind us.heap a1 d1 d2
              hd1_def.symm hd1_selfref hd1_lt hd2_lt hne hle hwf hdesc hnotreach'
            -- Now show deref a2 on new heap = deref d2 on new heap
            -- Key: d1 is not reachable from a2 (if it were, deref a2 would = d1 ≠ d2)
            have hterm_d1 : us.heap.isTerminal d1 = true := by
              unfold Heap.isTerminal; simp only [hd1_selfref, beq_self_eq_true]
            have ha2_deref_ne : us.heap.deref a2 ≠ d1 := by
              rw [← hd2_def]; exact Ne.symm hne
            have hnotreach_a2 : us.heap.notReachableFrom d1 a2 :=
              Heap.notReachableFrom_of_terminal_ne us.heap d1 a2 hterm_d1 ha2_deref_ne hvalid2 hwf hdesc
            -- a2 ≠ d1 (if a2 = d1, then deref a2 = deref d1 = d1 ≠ d2)
            have ha2_ne_d1 : a2 ≠ d1 := by
              intro h_eq
              have hderef_d1 : us.heap.deref d1 = d1 := by
                unfold Heap.deref
                cases hsz : us.heap.cells.size with
                | zero =>
                  simp only [hsz] at hd1_lt
                  exact absurd hd1_lt (Nat.not_lt_zero d1)
                | succ n =>
                  simp only [Heap.derefAux, hd1_selfref, beq_self_eq_true, ↓reduceIte]
              rw [h_eq] at hd2_def
              exact hne (hderef_d1.symm.trans hd2_def.symm)
            -- deref a2 on new heap equals deref a2 on old heap (since d1 not in chain)
            have hderef_a2_eq := Heap.derefAux_bind_ne us.heap d1 d2 a2 us.heap.cells.size
              ha2_ne_d1 hnotreach_a2
            -- Similarly, d2's deref is unchanged since d2 ≠ d1
            have hd2_ne_d1 : d2 ≠ d1 := Ne.symm hne
            have hnotreach_d2 : us.heap.notReachableFrom d1 d2 := hnotreach'
            have hderef_d2_eq := Heap.derefAux_bind_ne us.heap d1 d2 d2 us.heap.cells.size
              hd2_ne_d1 hnotreach_d2
            -- On old heap, deref a2 = d2 and deref d2 = d2 (terminal)
            -- So on new heap, deref a2 = d2 and deref d2 = d2
            have hd2_term : us.heap.isTerminal d2 = true :=
              Heap.derefAux_terminates us.heap a2 us.heap.cells.size hvalid2 hdesc hwf (Nat.le_of_lt hvalid2)
            -- deref d2 = d2 on old heap
            have hderef_d2_old : us.heap.deref d2 = d2 := by
              unfold Heap.deref
              cases hsz : us.heap.cells.size with
              | zero => simp_all
              | succ n =>
                have hd2_lt' : d2 < n + 1 := hsz ▸ hd2_lt
                have hn_ge : n ≥ d2 := Nat.lt_succ_iff.mp hd2_lt'
                -- For terminal d2, derefAux d2 k = d2 for all k
                simp only [Heap.derefAux, hg2]
                cases c2 with
                | ref r2 =>
                  -- d2 is terminal with ref r2 means r2 = d2
                  have hr2_eq : r2 = d2 := Heap.deref_ref_is_selfref us.heap a2 d2 r2 hd2_def.symm hd2_lt hwf hdesc hg2
                  simp only [hr2_eq, beq_self_eq_true, ↓reduceIte]
                | str _ | con _ | lis _ | functor _ =>
                  rfl
            -- Now derive the result
            unfold Heap.deref at hderef_a1
            have hsize : (us.heap.bind d1 d2).cells.size = us.heap.cells.size := Heap.bind_size us.heap d1 d2
            rw [hsize] at hderef_a1
            -- hderef_a1 : derefAux a1 size = derefAux d2 size on bound heap
            -- hderef_a2_eq : derefAux a2 size on bound = derefAux a2 size on old
            -- hderef_d2_eq : derefAux d2 size on bound = derefAux d2 size on old
            -- old deref a2 = d2, old deref d2 = d2
            -- So new deref a2 = new deref d2 = d2... wait no
            -- new deref d2 = old deref d2 = d2 (from hderef_d2_eq and hderef_d2_old)
            -- new deref a2 = old deref a2 = d2 (from hderef_a2_eq and hd2_def)
            -- new deref a1 = new deref d2 = d2 (from hderef_a1 and above)
            -- So new deref a1 = d2 = new deref a2
            have hderef_a2_new : (us.heap.bind d1 d2).deref a2 = d2 := by
              unfold Heap.deref
              rw [hsize, hderef_a2_eq]
              -- Now show: us.heap.derefAux a2 us.heap.cells.size = d2
              -- This is us.heap.deref a2 = d2, i.e., hd2_def.symm
              unfold Heap.deref at hd2_def
              exact hd2_def.symm
            have hderef_d2_new : (us.heap.bind d1 d2).deref d2 = d2 := by
              unfold Heap.deref
              rw [hsize, hderef_d2_eq]
              -- old deref d2 = d2
              unfold Heap.deref at hderef_d2_old
              exact hderef_d2_old
            have hderef_a1_new : (us.heap.bind d1 d2).deref a1 = d2 := by
              unfold Heap.deref
              rw [hsize]
              calc (us.heap.bind d1 d2).derefAux a1 us.heap.cells.size
                  = (us.heap.bind d1 d2).derefAux d2 us.heap.cells.size := hderef_a1
                _ = d2 := by unfold Heap.deref at hderef_d2_new; rw [hsize] at hderef_d2_new; exact hderef_d2_new
            have hderefs_final : (us.heap.bind d1 d2).deref a1 = (us.heap.bind d1 d2).deref a2 := by
              rw [hderef_a1_new, hderef_a2_new]
            exact Heap.termEq_of_deref_eq (us.heap.bind d1 d2) a1 a2 hderefs_final
          · -- Case d1 ≤ d2 (with d1 ≠ d2, so d1 < d2): bind d2 to d1
            simp only
            push_neg at hgt
            have hlt : d1 < d2 := Nat.lt_of_le_of_ne hgt hne
            have hle : d1 ≤ d2 := Nat.le_of_lt hlt
            -- On old heap: deref a1 = d1, deref a2 = d2
            -- After bind d2 to d1: cell at d2 becomes ref d1
            -- d1's chain unchanged (d2 not in d1's chain since d2 > d1 and chains descend)
            -- a2's chain: ends at d2, now d2 → d1, so deref a2 = deref d1 = d1
            -- a1's chain: unchanged since d2 not in it, so deref a1 = d1
            -- So both derefs = d1
            -- First show d2 not in a1's chain
            have hnotreach' : us.heap.notReachableFrom d2 d1 := by
              simp only [Nat.not_lt.mpr hle, ↓reduceIte] at hnotreach; exact hnotreach
            have hterm_d2 : us.heap.isTerminal d2 = true :=
              Heap.derefAux_terminates us.heap a2 us.heap.cells.size hvalid2 hdesc hwf (Nat.le_of_lt hvalid2)
            have ha1_deref_ne : us.heap.deref a1 ≠ d2 := by
              rw [← hd1_def]; exact hne
            have hnotreach_a1 : us.heap.notReachableFrom d2 a1 :=
              Heap.notReachableFrom_of_terminal_ne us.heap d2 a1 hterm_d2 ha1_deref_ne hvalid1 hwf hdesc
            have ha1_ne_d2 : a1 ≠ d2 := by
              intro h_eq
              have hderef_d2 : us.heap.deref d2 = d2 := by
                unfold Heap.deref
                cases hsz : us.heap.cells.size with
                | zero =>
                  simp only [hsz] at hd2_lt
                  exact absurd hd2_lt (Nat.not_lt_zero d2)
                | succ n =>
                  simp only [Heap.derefAux, hg2]
                  cases c2 with
                  | ref r2 =>
                    have hr2_eq : r2 = d2 := Heap.deref_ref_is_selfref us.heap a2 d2 r2 hd2_def.symm hd2_lt hwf hdesc hg2
                    simp only [hr2_eq, beq_self_eq_true, ↓reduceIte]
                  | str _ | con _ | lis _ | functor _ => rfl
              rw [h_eq] at hd1_def
              exact hne (hd1_def.trans hderef_d2)
            -- deref a1 unchanged after bind d2 d1
            have hderef_a1_eq := Heap.derefAux_bind_ne us.heap d2 d1 a1 us.heap.cells.size
              ha1_ne_d2 hnotreach_a1
            -- deref d1 unchanged (d1 ≠ d2)
            have hnotreach_d1 : us.heap.notReachableFrom d2 d1 := hnotreach'
            have hderef_d1_eq := Heap.derefAux_bind_ne us.heap d2 d1 d1 us.heap.cells.size
              hne hnotreach_d1
            -- d1 is terminal, deref d1 = d1 on old heap
            have hderef_d1_old : us.heap.deref d1 = d1 := by
              unfold Heap.deref
              cases hsz : us.heap.cells.size with
              | zero => simp_all
              | succ n =>
                simp only [Heap.derefAux, hd1_selfref, beq_self_eq_true, ↓reduceIte]
            have hsize : (us.heap.bind d2 d1).cells.size = us.heap.cells.size := Heap.bind_size us.heap d2 d1
            have hderef_a1_new : (us.heap.bind d2 d1).deref a1 = d1 := by
              unfold Heap.deref
              rw [hsize, hderef_a1_eq]
              -- Now show: us.heap.derefAux a1 us.heap.cells.size = d1
              -- This is us.heap.deref a1 = d1, i.e., hd1_def.symm
              unfold Heap.deref at hd1_def
              exact hd1_def.symm
            have hderef_d1_new : (us.heap.bind d2 d1).deref d1 = d1 := by
              unfold Heap.deref
              rw [hsize, hderef_d1_eq]
              unfold Heap.deref at hderef_d1_old
              exact hderef_d1_old
            -- For a2: use deref_through_selfref_bind (need d2 to be self-ref)
            -- Actually d2 might not be self-ref (could be STR/CON/etc)
            -- But we can still show deref a2 = d1 on new heap
            -- After bind, cell at d2 = ref d1, so deref d2 = deref d1 = d1
            have hcell_d2_bind : (us.heap.bind d2 d1).get? d2 = some (.ref d1) := by
              unfold Heap.bind
              exact Heap.get?_set_self us.heap d2 (.ref d1) hd2_lt
            -- deref d2 on new heap = d1
            have hderef_d2_new : (us.heap.bind d2 d1).deref d2 = d1 := by
              unfold Heap.deref
              rw [hsize]
              cases hsz : us.heap.cells.size with
              | zero => simp_all
              | succ n =>
                simp only [Heap.derefAux, hcell_d2_bind]
                have hd1_ne_d2 : (d1 == d2) = false := beq_eq_false_iff_ne.mpr hne
                simp only [hd1_ne_d2, Bool.false_eq_true, ↓reduceIte]
                -- Now need: derefAux d1 n on new heap = d1
                -- d1 ≠ d2, so d1's cell unchanged
                have hcell_d1_bind : (us.heap.bind d2 d1).get? d1 = us.heap.get? d1 := by
                  unfold Heap.bind
                  exact Heap.get?_set_ne us.heap d2 d1 (.ref d1) hne
                have hd1_lt_orig : d1 < us.heap.cells.size := Heap.deref_terminates us.heap a1 hvalid1 hwf
                have hd1_lt' : d1 < n + 1 := hsz ▸ hd1_lt_orig
                have hn_ge : n ≥ d1 := Nat.lt_succ_iff.mp hd1_lt'
                have hbind_wf := Heap.bind_preserves_wf us.heap d2 d1 hwf hd1_lt_orig
                have hbind_desc := Heap.bind_preserves_chainsDescend us.heap d2 d1 hdesc hd2_lt hle
                have hd1_lt_bind : d1 < (us.heap.bind d2 d1).cells.size := by rw [hsize]; exact hd1_lt_orig
                have hconv := Heap.derefAux_converges (us.heap.bind d2 d1) d1 n hd1_lt_bind hbind_wf hbind_desc hn_ge
                rw [hconv]
                simp only [Heap.derefAux, hcell_d1_bind, hd1_selfref, beq_self_eq_true, ↓reduceIte]
            -- Now show deref a2 = d1 on new heap
            -- a2's chain leads to d2, then d2 → d1
            -- Use deref_through_bind_to_selfref: binding d2 to d1 where d1 is self-ref
            have hd1_lt : d1 < us.heap.cells.size := Heap.deref_terminates us.heap a1 hvalid1 hwf
            have hderef_a2_new : (us.heap.bind d2 d1).deref a2 = d1 :=
              Heap.deref_through_bind_to_selfref us.heap a2 d2 d1
                hd2_def.symm hd2_lt hd1_lt hd1_selfref (Ne.symm hne) hle hwf hdesc hnotreach'
            have hderefs_final : (us.heap.bind d2 d1).deref a1 = (us.heap.bind d2 d1).deref a2 := by
              rw [hderef_a1_new, hderef_a2_new]
            exact Heap.termEq_of_deref_eq (us.heap.bind d2 d1) a1 a2 hderefs_final
        | str v1 =>
          cases c2 with
          | ref r2 =>
            -- Symmetric REF case: c2 = ref, so d2 is self-ref REF
            simp only at hempty_step hstep_ok ⊢
            have hne : d1 ≠ d2 := by simp only [beq_iff_eq, ne_eq] at heq_deref ⊢; exact heq_deref
            -- d2 is self-ref (since c2 = ref r2 and d2 is terminal)
            have hr2_eq : r2 = d2 := Heap.deref_ref_is_selfref us.heap a2 d2 r2 hd2_def.symm hd2_lt hwf hdesc hg2
            have hd2_selfref : us.heap.get? d2 = some (.ref d2) := by subst hr2_eq; exact hg2
            have hterm_d2 : us.heap.isTerminal d2 = true := by
              unfold Heap.isTerminal; simp only [hd2_selfref, beq_self_eq_true]
            have hd1_lt : d1 < us.heap.cells.size := Heap.deref_terminates us.heap a1 hvalid1 hwf
            -- Split on bind direction
            have hnotreach : if d1 > d2 then us.heap.notReachableFrom d1 d2
                            else us.heap.notReachableFrom d2 d1 := by
              split_ifs with hgt
              · exact Heap.notReachableFrom_of_gt us.heap d1 d2 hd2_lt hgt hdesc
              · push_neg at hgt
                have hlt : d1 < d2 := Nat.lt_of_le_of_ne hgt hne
                exact Heap.notReachableFrom_of_gt us.heap d2 d1 hd1_lt hlt hdesc
            unfold bind
            split_ifs with hgt
            · -- d1 > d2: bind d1 to d2 (d2 is self-ref target)
              simp only
              have hle : d2 ≤ d1 := Nat.le_of_lt hgt
              have hnotreach' : us.heap.notReachableFrom d1 d2 := by simp only [hgt, ↓reduceIte] at hnotreach; exact hnotreach
              have hterm_d1 : us.heap.isTerminal d1 = true := by
                unfold Heap.isTerminal; simp only [hg1]
              -- d1 not reachable from a2 since deref a2 = d2 ≠ d1
              have ha2_deref_ne : us.heap.deref a2 ≠ d1 := by rw [← hd2_def]; exact Ne.symm hne
              have hnotreach_a2 : us.heap.notReachableFrom d1 a2 :=
                Heap.notReachableFrom_of_terminal_ne us.heap d1 a2 hterm_d1 ha2_deref_ne hvalid2 hwf hdesc
              -- Use deref_through_bind_to_selfref: bind d1 to d2 (d2 self-ref)
              have hderef_a1 := Heap.deref_through_bind_to_selfref us.heap a1 d1 d2
                hd1_def.symm hd1_lt hd2_lt hd2_selfref (Nat.ne_of_gt hgt) hle hwf hdesc hnotreach'
              -- deref a2 unchanged since d1 not in chain
              have ha2_ne_d1 : a2 ≠ d1 := by
                intro h_eq
                have hderef_d1 : us.heap.deref d1 = d1 := by
                  unfold Heap.deref
                  cases hsz : us.heap.cells.size with
                  | zero => simp only [hsz] at hd1_lt; exact absurd hd1_lt (Nat.not_lt_zero d1)
                  | succ n => simp only [Heap.derefAux, hg1]
                rw [h_eq] at hd2_def
                exact hne (hderef_d1.symm.trans hd2_def.symm)
              have hderef_a2_eq := Heap.derefAux_bind_ne us.heap d1 d2 a2 us.heap.cells.size
                ha2_ne_d1 hnotreach_a2
              -- d2's deref unchanged
              have hnotreach_d2 : us.heap.notReachableFrom d1 d2 := hnotreach'
              have hderef_d2_eq := Heap.derefAux_bind_ne us.heap d1 d2 d2 us.heap.cells.size
                (Ne.symm hne) hnotreach_d2
              have hderef_d2_old : us.heap.deref d2 = d2 := by
                unfold Heap.deref
                cases hsz : us.heap.cells.size with
                | zero => simp_all
                | succ n => simp only [Heap.derefAux, hd2_selfref, beq_self_eq_true, ↓reduceIte]
              have hsize : (us.heap.bind d1 d2).cells.size = us.heap.cells.size := Heap.bind_size us.heap d1 d2
              have hderef_a2_new : (us.heap.bind d1 d2).deref a2 = d2 := by
                unfold Heap.deref
                rw [hsize, hderef_a2_eq]
                unfold Heap.deref at hd2_def
                exact hd2_def.symm
              -- deref a1 = d2 on new heap (from deref_through_bind_to_selfref)
              have hderefs_final : (us.heap.bind d1 d2).deref a1 = (us.heap.bind d1 d2).deref a2 := by
                rw [hderef_a1, hderef_a2_new]
              exact Heap.termEq_of_deref_eq (us.heap.bind d1 d2) a1 a2 hderefs_final
            · -- d1 ≤ d2 (so d1 < d2): bind d2 to d1
              simp only
              push_neg at hgt
              have hlt : d1 < d2 := Nat.lt_of_le_of_ne hgt hne
              have hle : d1 ≤ d2 := Nat.le_of_lt hlt
              have hnotreach' : us.heap.notReachableFrom d2 d1 := by
                simp only [Nat.not_lt.mpr hle, ↓reduceIte] at hnotreach; exact hnotreach
              -- Use deref_through_selfref_bind: bind d2 (self-ref) to d1
              have hderef_a2 := Heap.deref_through_selfref_bind us.heap a2 d2 d1
                hd2_def.symm hd2_selfref hd2_lt hd1_lt (Ne.symm hne) hle hwf hdesc hnotreach'
              -- deref a1 unchanged since d2 not in chain
              have hterm_d1 : us.heap.isTerminal d1 = true := by
                unfold Heap.isTerminal; simp only [hg1]
              have ha1_deref_ne : us.heap.deref a1 ≠ d2 := by rw [← hd1_def]; exact hne
              have hnotreach_a1 : us.heap.notReachableFrom d2 a1 :=
                Heap.notReachableFrom_of_terminal_ne us.heap d2 a1 hterm_d2 ha1_deref_ne hvalid1 hwf hdesc
              have ha1_ne_d2 : a1 ≠ d2 := by
                intro h_eq
                have hderef_d2 : us.heap.deref d2 = d2 := by
                  unfold Heap.deref
                  cases hsz : us.heap.cells.size with
                  | zero => simp only [hsz] at hd2_lt; exact absurd hd2_lt (Nat.not_lt_zero d2)
                  | succ n => simp only [Heap.derefAux, hd2_selfref, beq_self_eq_true, ↓reduceIte]
                rw [h_eq] at hd1_def
                exact hne (hd1_def.trans hderef_d2)
              have hderef_a1_eq := Heap.derefAux_bind_ne us.heap d2 d1 a1 us.heap.cells.size
                ha1_ne_d2 hnotreach_a1
              -- d1's deref unchanged
              have hnotreach_d1 : us.heap.notReachableFrom d2 d1 := hnotreach'
              have hderef_d1_eq := Heap.derefAux_bind_ne us.heap d2 d1 d1 us.heap.cells.size
                hne hnotreach_d1
              have hderef_d1_old : us.heap.deref d1 = d1 := by
                unfold Heap.deref
                cases hsz : us.heap.cells.size with
                | zero => simp_all
                | succ n => simp only [Heap.derefAux, hg1]
              have hsize : (us.heap.bind d2 d1).cells.size = us.heap.cells.size := Heap.bind_size us.heap d2 d1
              have hderef_a1_new : (us.heap.bind d2 d1).deref a1 = d1 := by
                unfold Heap.deref
                rw [hsize, hderef_a1_eq]
                unfold Heap.deref at hd1_def
                exact hd1_def.symm
              -- deref d1 = d1 on new heap (d1's cell unchanged)
              have hderef_d1_new : (us.heap.bind d2 d1).deref d1 = d1 := by
                unfold Heap.deref
                rw [hsize, hderef_d1_eq]
                unfold Heap.deref at hderef_d1_old
                exact hderef_d1_old
              -- deref a2 = d1 on new heap
              -- hderef_a2 : deref a2 = deref d1 on new heap
              -- hderef_d1_new : deref d1 = d1 on new heap
              have hderef_a2_new : (us.heap.bind d2 d1).deref a2 = d1 := by
                rw [hderef_a2, hderef_d1_new]
              have hderefs_final : (us.heap.bind d2 d1).deref a1 = (us.heap.bind d2 d1).deref a2 := by
                rw [hderef_a1_new, hderef_a2_new]
              exact Heap.termEq_of_deref_eq (us.heap.bind d2 d1) a1 a2 hderefs_final
          | str v2 =>
            -- STR.STR: check functors
            cases hf1 : us.heap.get? v1 with
            | none =>
              simp only [hf1] at hstep_ok; exact absurd trivial hstep_ok
            | some fc1 =>
              cases hf2 : us.heap.get? v2 with
              | none =>
                simp only [hf1, hf2] at hstep_ok; exact absurd trivial hstep_ok
              | some fc2 =>
                simp only [hf1, hf2] at hstep_ok hempty_step ⊢
                cases fc1 with
                | functor f1 =>
                  cases fc2 with
                  | functor f2 =>
                    simp only at hstep_ok hempty_step ⊢
                    by_cases hfeq : f1 == f2
                    · -- Same functor: arity=0 needed for empty PDL
                      simp only [hfeq, ↓reduceIte] at hempty_step ⊢
                      -- Extract arity = 0 from hempty_step (empty PDL)
                      simp only [List.append_nil, List.isEmpty_iff] at hempty_step
                      have harity0 : f1.arity = 0 := by
                        by_contra hne
                        have hpos : f1.arity > 0 := Nat.pos_of_ne_zero hne
                        simp only [List.flatten_eq_nil_iff, List.mem_map, forall_exists_index,
                          and_imp, forall_apply_eq_imp_iff₂] at hempty_step
                        have hmem : 0 ∈ List.range f1.arity := List.mem_range.mpr hpos
                        have := hempty_step 0 hmem
                        simp at this
                      -- f1 = f2 from hfeq
                      have hfeq' : f1 = f2 := beq_iff_eq.mp hfeq
                      -- Apply termEqAux_of_str_functor0
                      have hneq_deref : (us.heap.deref a1 == us.heap.deref a2) = false := by
                        simp only [hd1_def, hd2_def] at heq_deref ⊢
                        exact Bool.eq_false_iff.mpr heq_deref
                      have hs1 : us.heap.get? (us.heap.deref a1) = some (.str v1) := by
                        simp only [← hd1_def, hg1]
                      have hs2 : us.heap.get? (us.heap.deref a2) = some (.str v2) := by
                        simp only [← hd2_def, hg2]
                      have hf2' : us.heap.get? v2 = some (.functor f1) := hfeq' ▸ hf2
                      unfold Heap.termEq
                      have hpos : us.heap.cells.size > 0 := Nat.lt_of_le_of_lt (Nat.zero_le d1) hd1_lt
                      have hfuel : us.heap.cells.size * 2 > 0 := Nat.mul_pos hpos (by omega)
                      match hfuel_match : us.heap.cells.size * 2 with
                      | 0 => exact absurd hfuel_match (Nat.ne_of_gt hfuel)
                      | fuel + 1 =>
                        exact Heap.termEqAux_of_str_functor0 us.heap a1 a2 fuel f1 v1 v2
                          hneq_deref hs1 hs2 hf1 hf2' harity0
                    · -- Different functors: step fails
                      simp only [hfeq, Bool.false_eq_true, ↓reduceIte] at hstep_ok
                      exact absurd trivial hstep_ok
                  | _ => simp only at hstep_ok; exact absurd trivial hstep_ok
                | _ => simp only at hstep_ok; exact absurd trivial hstep_ok
          | con _ => simp only at hstep_ok; exact absurd trivial hstep_ok
          | lis _ => simp only at hstep_ok; exact absurd trivial hstep_ok
          | functor _ => simp only at hstep_ok; exact absurd trivial hstep_ok
        | con f1 =>
          cases c2 with
          | ref r2 =>
            -- Symmetric REF case: c1 = con, c2 = ref (d2 is self-ref)
            simp only at hempty_step hstep_ok ⊢
            have hne : d1 ≠ d2 := by simp only [beq_iff_eq, ne_eq] at heq_deref ⊢; exact heq_deref
            have hr2_eq : r2 = d2 := Heap.deref_ref_is_selfref us.heap a2 d2 r2 hd2_def.symm hd2_lt hwf hdesc hg2
            have hd2_selfref : us.heap.get? d2 = some (.ref d2) := by subst hr2_eq; exact hg2
            have hterm_d2 : us.heap.isTerminal d2 = true := by
              unfold Heap.isTerminal; simp only [hd2_selfref, beq_self_eq_true]
            have hd1_lt : d1 < us.heap.cells.size := Heap.deref_terminates us.heap a1 hvalid1 hwf
            have hterm_d1 : us.heap.isTerminal d1 = true := by unfold Heap.isTerminal; simp only [hg1]
            have hnotreach : if d1 > d2 then us.heap.notReachableFrom d1 d2
                            else us.heap.notReachableFrom d2 d1 := by
              split_ifs with hgt
              · exact Heap.notReachableFrom_of_gt us.heap d1 d2 hd2_lt hgt hdesc
              · push_neg at hgt
                have hlt : d1 < d2 := Nat.lt_of_le_of_ne hgt hne
                exact Heap.notReachableFrom_of_gt us.heap d2 d1 hd1_lt hlt hdesc
            unfold bind
            split_ifs with hgt
            · -- d1 > d2: bind d1 to d2
              simp only
              have hle : d2 ≤ d1 := Nat.le_of_lt hgt
              have hnotreach' : us.heap.notReachableFrom d1 d2 := by simp only [hgt, ↓reduceIte] at hnotreach; exact hnotreach
              have ha2_deref_ne : us.heap.deref a2 ≠ d1 := by rw [← hd2_def]; exact Ne.symm hne
              have hnotreach_a2 : us.heap.notReachableFrom d1 a2 :=
                Heap.notReachableFrom_of_terminal_ne us.heap d1 a2 hterm_d1 ha2_deref_ne hvalid2 hwf hdesc
              have hderef_a1 := Heap.deref_through_bind_to_selfref us.heap a1 d1 d2
                hd1_def.symm hd1_lt hd2_lt hd2_selfref (Nat.ne_of_gt hgt) hle hwf hdesc hnotreach'
              have ha2_ne_d1 : a2 ≠ d1 := by
                intro h_eq
                have hderef_d1 : us.heap.deref d1 = d1 := by
                  unfold Heap.deref
                  cases hsz : us.heap.cells.size with
                  | zero => simp only [hsz] at hd1_lt; exact absurd hd1_lt (Nat.not_lt_zero d1)
                  | succ n => simp only [Heap.derefAux, hg1]
                rw [h_eq] at hd2_def
                exact hne (hderef_d1.symm.trans hd2_def.symm)
              have hderef_a2_eq := Heap.derefAux_bind_ne us.heap d1 d2 a2 us.heap.cells.size ha2_ne_d1 hnotreach_a2
              have hderef_d2_eq := Heap.derefAux_bind_ne us.heap d1 d2 d2 us.heap.cells.size (Ne.symm hne) hnotreach'
              have hderef_d2_old : us.heap.deref d2 = d2 := by
                unfold Heap.deref
                cases hsz : us.heap.cells.size with
                | zero => simp_all
                | succ n => simp only [Heap.derefAux, hd2_selfref, beq_self_eq_true, ↓reduceIte]
              have hsize : (us.heap.bind d1 d2).cells.size = us.heap.cells.size := Heap.bind_size us.heap d1 d2
              have hderef_a2_new : (us.heap.bind d1 d2).deref a2 = d2 := by
                unfold Heap.deref; rw [hsize, hderef_a2_eq]; unfold Heap.deref at hd2_def; exact hd2_def.symm
              have hderefs_final : (us.heap.bind d1 d2).deref a1 = (us.heap.bind d1 d2).deref a2 := by
                rw [hderef_a1, hderef_a2_new]
              exact Heap.termEq_of_deref_eq (us.heap.bind d1 d2) a1 a2 hderefs_final
            · -- d1 ≤ d2 (d1 < d2): bind d2 to d1
              simp only
              push_neg at hgt
              have hlt : d1 < d2 := Nat.lt_of_le_of_ne hgt hne
              have hle : d1 ≤ d2 := Nat.le_of_lt hlt
              have hnotreach' : us.heap.notReachableFrom d2 d1 := by
                simp only [Nat.not_lt.mpr hle, ↓reduceIte] at hnotreach; exact hnotreach
              have hderef_a2 := Heap.deref_through_selfref_bind us.heap a2 d2 d1
                hd2_def.symm hd2_selfref hd2_lt hd1_lt (Ne.symm hne) hle hwf hdesc hnotreach'
              have ha1_deref_ne : us.heap.deref a1 ≠ d2 := by rw [← hd1_def]; exact hne
              have hnotreach_a1 : us.heap.notReachableFrom d2 a1 :=
                Heap.notReachableFrom_of_terminal_ne us.heap d2 a1 hterm_d2 ha1_deref_ne hvalid1 hwf hdesc
              have ha1_ne_d2 : a1 ≠ d2 := by
                intro h_eq
                have hderef_d2 : us.heap.deref d2 = d2 := by
                  unfold Heap.deref
                  cases hsz : us.heap.cells.size with
                  | zero => simp only [hsz] at hd2_lt; exact absurd hd2_lt (Nat.not_lt_zero d2)
                  | succ n => simp only [Heap.derefAux, hd2_selfref, beq_self_eq_true, ↓reduceIte]
                rw [h_eq] at hd1_def
                exact hne (hd1_def.trans hderef_d2)
              have hderef_a1_eq := Heap.derefAux_bind_ne us.heap d2 d1 a1 us.heap.cells.size ha1_ne_d2 hnotreach_a1
              have hderef_d1_eq := Heap.derefAux_bind_ne us.heap d2 d1 d1 us.heap.cells.size hne hnotreach'
              have hderef_d1_old : us.heap.deref d1 = d1 := by
                unfold Heap.deref
                cases hsz : us.heap.cells.size with
                | zero => simp_all
                | succ n => simp only [Heap.derefAux, hg1]
              have hsize : (us.heap.bind d2 d1).cells.size = us.heap.cells.size := Heap.bind_size us.heap d2 d1
              have hderef_a1_new : (us.heap.bind d2 d1).deref a1 = d1 := by
                unfold Heap.deref; rw [hsize, hderef_a1_eq]; unfold Heap.deref at hd1_def; exact hd1_def.symm
              have hderef_d1_new : (us.heap.bind d2 d1).deref d1 = d1 := by
                unfold Heap.deref; rw [hsize, hderef_d1_eq]; unfold Heap.deref at hderef_d1_old; exact hderef_d1_old
              have hderef_a2_new : (us.heap.bind d2 d1).deref a2 = d1 := by rw [hderef_a2, hderef_d1_new]
              have hderefs_final : (us.heap.bind d2 d1).deref a1 = (us.heap.bind d2 d1).deref a2 := by
                rw [hderef_a1_new, hderef_a2_new]
              exact Heap.termEq_of_deref_eq (us.heap.bind d2 d1) a1 a2 hderefs_final
          | str _ => simp only at hstep_ok; exact absurd trivial hstep_ok
          | con f2 =>
            -- CON.CON: check equality
            simp only at hstep_ok hempty_step ⊢
            by_cases hceq : f1 == f2
            · -- Same constant: heap unchanged, termEq via termEqAux_of_con
              simp only [hceq, ↓reduceIte]
              have hf_eq : f1 = f2 := by simp only [beq_iff_eq] at hceq; exact hceq
              subst hf_eq
              unfold Heap.termEq
              -- Need to show termEqAux returns true for CON.CON same constant
              have h := Heap.termEqAux_of_con us.heap a1 a2 (us.heap.cells.size * 2 - 1) f1
                heq_deref hg1 hg2
              -- h : termEqAux ... (size*2 - 1 + 1) = true
              -- Goal: termEqAux ... (size * 2) = true
              -- These are equal when size ≥ 1 (which it is since we have valid cells)
              have hpos : us.heap.cells.size ≥ 1 := by
                have := Nat.lt_of_lt_of_le hd1_lt (Nat.le_refl _)
                omega
              have heq_fuel : us.heap.cells.size * 2 - 1 + 1 = us.heap.cells.size * 2 := by omega
              rw [heq_fuel] at h
              exact h
            · -- Different constants: step fails
              simp only [hceq, Bool.false_eq_true, ↓reduceIte] at hstep_ok
              exact absurd trivial hstep_ok
          | lis _ => simp only at hstep_ok; exact absurd trivial hstep_ok
          | functor _ => simp only at hstep_ok; exact absurd trivial hstep_ok
        | lis h1 =>
          cases c2 with
          | ref r2 =>
            -- Symmetric REF case: c1 = lis, c2 = ref (d2 is self-ref)
            simp only at hempty_step hstep_ok ⊢
            have hne : d1 ≠ d2 := by simp only [beq_iff_eq, ne_eq] at heq_deref ⊢; exact heq_deref
            have hr2_eq : r2 = d2 := Heap.deref_ref_is_selfref us.heap a2 d2 r2 hd2_def.symm hd2_lt hwf hdesc hg2
            have hd2_selfref : us.heap.get? d2 = some (.ref d2) := by subst hr2_eq; exact hg2
            have hterm_d2 : us.heap.isTerminal d2 = true := by
              unfold Heap.isTerminal; simp only [hd2_selfref, beq_self_eq_true]
            have hd1_lt : d1 < us.heap.cells.size := Heap.deref_terminates us.heap a1 hvalid1 hwf
            have hterm_d1 : us.heap.isTerminal d1 = true := by unfold Heap.isTerminal; simp only [hg1]
            have hnotreach : if d1 > d2 then us.heap.notReachableFrom d1 d2
                            else us.heap.notReachableFrom d2 d1 := by
              split_ifs with hgt
              · exact Heap.notReachableFrom_of_gt us.heap d1 d2 hd2_lt hgt hdesc
              · push_neg at hgt
                have hlt : d1 < d2 := Nat.lt_of_le_of_ne hgt hne
                exact Heap.notReachableFrom_of_gt us.heap d2 d1 hd1_lt hlt hdesc
            unfold bind
            split_ifs with hgt
            · -- d1 > d2: bind d1 to d2
              simp only
              have hle : d2 ≤ d1 := Nat.le_of_lt hgt
              have hnotreach' : us.heap.notReachableFrom d1 d2 := by simp only [hgt, ↓reduceIte] at hnotreach; exact hnotreach
              have ha2_deref_ne : us.heap.deref a2 ≠ d1 := by rw [← hd2_def]; exact Ne.symm hne
              have hnotreach_a2 : us.heap.notReachableFrom d1 a2 :=
                Heap.notReachableFrom_of_terminal_ne us.heap d1 a2 hterm_d1 ha2_deref_ne hvalid2 hwf hdesc
              have hderef_a1 := Heap.deref_through_bind_to_selfref us.heap a1 d1 d2
                hd1_def.symm hd1_lt hd2_lt hd2_selfref (Nat.ne_of_gt hgt) hle hwf hdesc hnotreach'
              have ha2_ne_d1 : a2 ≠ d1 := by
                intro h_eq
                have hderef_d1 : us.heap.deref d1 = d1 := by
                  unfold Heap.deref
                  cases hsz : us.heap.cells.size with
                  | zero => simp only [hsz] at hd1_lt; exact absurd hd1_lt (Nat.not_lt_zero d1)
                  | succ n => simp only [Heap.derefAux, hg1]
                rw [h_eq] at hd2_def
                exact hne (hderef_d1.symm.trans hd2_def.symm)
              have hderef_a2_eq := Heap.derefAux_bind_ne us.heap d1 d2 a2 us.heap.cells.size ha2_ne_d1 hnotreach_a2
              have hsize : (us.heap.bind d1 d2).cells.size = us.heap.cells.size := Heap.bind_size us.heap d1 d2
              have hderef_a2_new : (us.heap.bind d1 d2).deref a2 = d2 := by
                unfold Heap.deref; rw [hsize, hderef_a2_eq]; unfold Heap.deref at hd2_def; exact hd2_def.symm
              have hderefs_final : (us.heap.bind d1 d2).deref a1 = (us.heap.bind d1 d2).deref a2 := by
                rw [hderef_a1, hderef_a2_new]
              exact Heap.termEq_of_deref_eq (us.heap.bind d1 d2) a1 a2 hderefs_final
            · -- d1 ≤ d2 (d1 < d2): bind d2 to d1
              simp only
              push_neg at hgt
              have hlt : d1 < d2 := Nat.lt_of_le_of_ne hgt hne
              have hle : d1 ≤ d2 := Nat.le_of_lt hlt
              have hnotreach' : us.heap.notReachableFrom d2 d1 := by
                simp only [Nat.not_lt.mpr hle, ↓reduceIte] at hnotreach; exact hnotreach
              have hderef_a2 := Heap.deref_through_selfref_bind us.heap a2 d2 d1
                hd2_def.symm hd2_selfref hd2_lt hd1_lt (Ne.symm hne) hle hwf hdesc hnotreach'
              have ha1_deref_ne : us.heap.deref a1 ≠ d2 := by rw [← hd1_def]; exact hne
              have hnotreach_a1 : us.heap.notReachableFrom d2 a1 :=
                Heap.notReachableFrom_of_terminal_ne us.heap d2 a1 hterm_d2 ha1_deref_ne hvalid1 hwf hdesc
              have ha1_ne_d2 : a1 ≠ d2 := by
                intro h_eq
                have hderef_d2 : us.heap.deref d2 = d2 := by
                  unfold Heap.deref
                  cases hsz : us.heap.cells.size with
                  | zero => simp only [hsz] at hd2_lt; exact absurd hd2_lt (Nat.not_lt_zero d2)
                  | succ n => simp only [Heap.derefAux, hd2_selfref, beq_self_eq_true, ↓reduceIte]
                rw [h_eq] at hd1_def
                exact hne (hd1_def.trans hderef_d2)
              have hderef_a1_eq := Heap.derefAux_bind_ne us.heap d2 d1 a1 us.heap.cells.size ha1_ne_d2 hnotreach_a1
              have hderef_d1_eq := Heap.derefAux_bind_ne us.heap d2 d1 d1 us.heap.cells.size hne hnotreach'
              have hderef_d1_old : us.heap.deref d1 = d1 := by
                unfold Heap.deref
                cases hsz : us.heap.cells.size with
                | zero => simp_all
                | succ n => simp only [Heap.derefAux, hg1]
              have hsize : (us.heap.bind d2 d1).cells.size = us.heap.cells.size := Heap.bind_size us.heap d2 d1
              have hderef_a1_new : (us.heap.bind d2 d1).deref a1 = d1 := by
                unfold Heap.deref; rw [hsize, hderef_a1_eq]; unfold Heap.deref at hd1_def; exact hd1_def.symm
              have hderef_d1_new : (us.heap.bind d2 d1).deref d1 = d1 := by
                unfold Heap.deref; rw [hsize, hderef_d1_eq]; unfold Heap.deref at hderef_d1_old; exact hderef_d1_old
              have hderef_a2_new : (us.heap.bind d2 d1).deref a2 = d1 := by rw [hderef_a2, hderef_d1_new]
              have hderefs_final : (us.heap.bind d2 d1).deref a1 = (us.heap.bind d2 d1).deref a2 := by
                rw [hderef_a1_new, hderef_a2_new]
              exact Heap.termEq_of_deref_eq (us.heap.bind d2 d1) a1 a2 hderefs_final
          | str _ => simp only at hstep_ok; exact absurd trivial hstep_ok
          | con _ => simp only at hstep_ok; exact absurd trivial hstep_ok
          | lis h2 =>
            -- LIS.LIS: push pairs, PDL not empty (contradiction)
            -- stepCells returns {pdl := [h1, h2, h1+1, h2+1] ++ []}
            simp only [List.append_nil] at hempty_step
            -- hempty_step : [h1, h2, h1+1, h2+1].isEmpty = true
            -- This is obviously false
            simp only [List.isEmpty_iff] at hempty_step
            -- hempty_step : [h1, h2, h1+1, h2+1] = []
            -- Contradiction: cons list can't equal nil
            cases hempty_step
          | functor _ => simp only at hstep_ok; exact absurd trivial hstep_ok
        | functor f1 =>
          cases c2 with
          | ref r2 =>
            -- Symmetric REF case: c1 = functor, c2 = ref (d2 is self-ref)
            simp only at hempty_step hstep_ok ⊢
            have hne : d1 ≠ d2 := by simp only [beq_iff_eq, ne_eq] at heq_deref ⊢; exact heq_deref
            have hr2_eq : r2 = d2 := Heap.deref_ref_is_selfref us.heap a2 d2 r2 hd2_def.symm hd2_lt hwf hdesc hg2
            have hd2_selfref : us.heap.get? d2 = some (.ref d2) := by subst hr2_eq; exact hg2
            have hterm_d2 : us.heap.isTerminal d2 = true := by
              unfold Heap.isTerminal; simp only [hd2_selfref, beq_self_eq_true]
            have hd1_lt : d1 < us.heap.cells.size := Heap.deref_terminates us.heap a1 hvalid1 hwf
            have hterm_d1 : us.heap.isTerminal d1 = true := by unfold Heap.isTerminal; simp only [hg1]
            have hnotreach : if d1 > d2 then us.heap.notReachableFrom d1 d2
                            else us.heap.notReachableFrom d2 d1 := by
              split_ifs with hgt
              · exact Heap.notReachableFrom_of_gt us.heap d1 d2 hd2_lt hgt hdesc
              · push_neg at hgt
                have hlt : d1 < d2 := Nat.lt_of_le_of_ne hgt hne
                exact Heap.notReachableFrom_of_gt us.heap d2 d1 hd1_lt hlt hdesc
            unfold bind
            split_ifs with hgt
            · -- d1 > d2: bind d1 to d2
              simp only
              have hle : d2 ≤ d1 := Nat.le_of_lt hgt
              have hnotreach' : us.heap.notReachableFrom d1 d2 := by simp only [hgt, ↓reduceIte] at hnotreach; exact hnotreach
              have ha2_deref_ne : us.heap.deref a2 ≠ d1 := by rw [← hd2_def]; exact Ne.symm hne
              have hnotreach_a2 : us.heap.notReachableFrom d1 a2 :=
                Heap.notReachableFrom_of_terminal_ne us.heap d1 a2 hterm_d1 ha2_deref_ne hvalid2 hwf hdesc
              have hderef_a1 := Heap.deref_through_bind_to_selfref us.heap a1 d1 d2
                hd1_def.symm hd1_lt hd2_lt hd2_selfref (Nat.ne_of_gt hgt) hle hwf hdesc hnotreach'
              have ha2_ne_d1 : a2 ≠ d1 := by
                intro h_eq
                have hderef_d1 : us.heap.deref d1 = d1 := by
                  unfold Heap.deref
                  cases hsz : us.heap.cells.size with
                  | zero => simp only [hsz] at hd1_lt; exact absurd hd1_lt (Nat.not_lt_zero d1)
                  | succ n => simp only [Heap.derefAux, hg1]
                rw [h_eq] at hd2_def
                exact hne (hderef_d1.symm.trans hd2_def.symm)
              have hderef_a2_eq := Heap.derefAux_bind_ne us.heap d1 d2 a2 us.heap.cells.size ha2_ne_d1 hnotreach_a2
              have hsize : (us.heap.bind d1 d2).cells.size = us.heap.cells.size := Heap.bind_size us.heap d1 d2
              have hderef_a2_new : (us.heap.bind d1 d2).deref a2 = d2 := by
                unfold Heap.deref; rw [hsize, hderef_a2_eq]; unfold Heap.deref at hd2_def; exact hd2_def.symm
              have hderefs_final : (us.heap.bind d1 d2).deref a1 = (us.heap.bind d1 d2).deref a2 := by
                rw [hderef_a1, hderef_a2_new]
              exact Heap.termEq_of_deref_eq (us.heap.bind d1 d2) a1 a2 hderefs_final
            · -- d1 ≤ d2 (d1 < d2): bind d2 to d1
              simp only
              push_neg at hgt
              have hlt : d1 < d2 := Nat.lt_of_le_of_ne hgt hne
              have hle : d1 ≤ d2 := Nat.le_of_lt hlt
              have hnotreach' : us.heap.notReachableFrom d2 d1 := by
                simp only [Nat.not_lt.mpr hle, ↓reduceIte] at hnotreach; exact hnotreach
              have hderef_a2 := Heap.deref_through_selfref_bind us.heap a2 d2 d1
                hd2_def.symm hd2_selfref hd2_lt hd1_lt (Ne.symm hne) hle hwf hdesc hnotreach'
              have ha1_deref_ne : us.heap.deref a1 ≠ d2 := by rw [← hd1_def]; exact hne
              have hnotreach_a1 : us.heap.notReachableFrom d2 a1 :=
                Heap.notReachableFrom_of_terminal_ne us.heap d2 a1 hterm_d2 ha1_deref_ne hvalid1 hwf hdesc
              have ha1_ne_d2 : a1 ≠ d2 := by
                intro h_eq
                have hderef_d2 : us.heap.deref d2 = d2 := by
                  unfold Heap.deref
                  cases hsz : us.heap.cells.size with
                  | zero => simp only [hsz] at hd2_lt; exact absurd hd2_lt (Nat.not_lt_zero d2)
                  | succ n => simp only [Heap.derefAux, hd2_selfref, beq_self_eq_true, ↓reduceIte]
                rw [h_eq] at hd1_def
                exact hne (hd1_def.trans hderef_d2)
              have hderef_a1_eq := Heap.derefAux_bind_ne us.heap d2 d1 a1 us.heap.cells.size ha1_ne_d2 hnotreach_a1
              have hderef_d1_eq := Heap.derefAux_bind_ne us.heap d2 d1 d1 us.heap.cells.size hne hnotreach'
              have hderef_d1_old : us.heap.deref d1 = d1 := by
                unfold Heap.deref
                cases hsz : us.heap.cells.size with
                | zero => simp_all
                | succ n => simp only [Heap.derefAux, hg1]
              have hsize : (us.heap.bind d2 d1).cells.size = us.heap.cells.size := Heap.bind_size us.heap d2 d1
              have hderef_a1_new : (us.heap.bind d2 d1).deref a1 = d1 := by
                unfold Heap.deref; rw [hsize, hderef_a1_eq]; unfold Heap.deref at hd1_def; exact hd1_def.symm
              have hderef_d1_new : (us.heap.bind d2 d1).deref d1 = d1 := by
                unfold Heap.deref; rw [hsize, hderef_d1_eq]; unfold Heap.deref at hderef_d1_old; exact hderef_d1_old
              have hderef_a2_new : (us.heap.bind d2 d1).deref a2 = d1 := by rw [hderef_a2, hderef_d1_new]
              have hderefs_final : (us.heap.bind d2 d1).deref a1 = (us.heap.bind d2 d1).deref a2 := by
                rw [hderef_a1_new, hderef_a2_new]
              exact Heap.termEq_of_deref_eq (us.heap.bind d2 d1) a1 a2 hderefs_final
          | _ => simp only at hstep_ok; exact absurd trivial hstep_ok

/-- All pairs in a list satisfy termEq on a heap -/
def Heap.allPairsTermEq (h : Heap) : List HeapAddr → Prop
  | [] => True
  | [_] => True  -- Odd element ignored (shouldn't happen in well-formed PDL)
  | a1 :: a2 :: rest => h.termEq a1 a2 ∧ h.allPairsTermEq rest

/-- Generalized: if run succeeds, first pair has termEq.
    This handles the case where PDL may contain multiple pairs by
    focusing on the first pair, which is what we need for compositionality.

    The key insight: successful run means all pairs were processed without failure,
    which means either they had equal derefs, got bound together, or structurally matched. -/
theorem UnifyState.run_first_pair_termEq (us : UnifyState) (a1 a2 : HeapAddr) (rest : List HeapAddr)
    (fuel : Nat)
    (hpdl : us.pdl = a1 :: a2 :: rest)
    (hnotfail : ¬us.fail)
    (hvalid1 : a1 < us.heap.cells.size)
    (hvalid2 : a2 < us.heap.cells.size)
    (hwf : us.heap.wellFormed)
    (hdesc : us.heap.chainsDescend)
    (hsucc : (us.run fuel).pdl.isEmpty ∧ ¬(us.run fuel).fail) :
    (us.run fuel).heap.termEq a1 a2 := by
  -- This is the general version; we prove it by reducing to the single-pair case
  -- when rest = [], or by structural argument when rest is non-empty.
  -- For now, we note this requires well-founded induction on term structure.
  sorry

/-- Helper: for successful termination, initial PDL pair terms are equal.

    The proof requires showing:
    1. First step either establishes term equality (bind/identical/same-const case)
       or decomposes into subterms (structure case)
    2. Subsequent unification of subterms implies equality of original terms
    This is a complex induction on term structure. -/
theorem UnifyState.run_initial_termEq (us : UnifyState) (a1 a2 : HeapAddr) (fuel : Nat)
    (hpdl : us.pdl = [a1, a2])
    (hnotfail : ¬us.fail)
    (hvalid1 : a1 < us.heap.cells.size)
    (hvalid2 : a2 < us.heap.cells.size)
    (hwf : us.heap.wellFormed)
    (hdesc : us.heap.chainsDescend)
    (hsucc : (us.run fuel).pdl.isEmpty ∧ ¬(us.run fuel).fail) :
    (us.run fuel).heap.termEq a1 a2 := by
  induction fuel generalizing us with
  | zero =>
    -- Base case: fuel = 0, run 0 = us
    simp only [run] at hsucc
    -- hsucc says us.pdl.isEmpty, but hpdl says us.pdl = [a1, a2]
    simp only [hpdl, List.isEmpty_cons] at hsucc
    -- hsucc.1 is false = true, derive contradiction
    cases hsucc.1
  | succ n ih =>
    -- Inductive case: run (n+1)
    -- First, show us.run (n+1) = (us.step).run n under our hypotheses
    have hrun_unfold : us.run (n + 1) = (us.step).run n := by
      simp only [run, hnotfail, Bool.false_eq_true, hpdl, List.isEmpty_cons, Bool.or_self, ↓reduceIte]
    rw [hrun_unfold] at hsucc
    simp only [run, hnotfail, Bool.false_eq_true, hpdl, List.isEmpty_cons, Bool.or_self, ↓reduceIte]
    -- Now: (us.step).run n terminates successfully
    -- hsucc : (us.step.run n).pdl.isEmpty ∧ ¬(us.step.run n).fail
    -- Need to show: ((us.step).run n).heap.termEq a1 a2
    by_cases hstep_empty : us.step.pdl.isEmpty
    · -- Step produces empty PDL: use step_pair_termEq
      by_cases hstep_fail : us.step.fail
      · -- step failed, then run n returns us.step
        have hrun_eq : (us.step).run n = us.step := by
          induction n with
          | zero => simp only [run]
          | succ m _ => simp only [run, hstep_fail, Bool.true_or, ↓reduceIte]
        simp only [hrun_eq] at hsucc
        exact absurd hstep_fail hsucc.2
      · -- step succeeded with empty pdl, then run n returns us.step
        have hrun_eq : (us.step).run n = us.step := by
          induction n with
          | zero => simp only [run]
          | succ m _ => simp only [run, hstep_fail, hstep_empty, Bool.or_true, ↓reduceIte]
        simp only [hrun_eq]
        -- Apply step_pair_termEq
        exact step_pair_termEq us a1 a2 hpdl hnotfail hstep_fail hstep_empty hvalid1 hvalid2 hwf hdesc
    · -- Step produces non-empty PDL: STR.STR arity>0 or LIS.LIS case
      -- Proof approach:
      -- 1. step doesn't modify heap (only pushes subterm pairs to PDL)
      -- 2. deref a1, a2 still reach the original STR/LIS cells
      -- 3. After run processes subterm pairs, each has termEq
      -- 4. Use termEqAux_of_str_subterms: subterms termEq → parent termEq
      --
      -- Key lemma needed: run_all_subterms_termEq
      -- If pdl = [(v1+1,v2+1), ..., (v1+n,v2+n)] and run succeeds,
      -- then all pairs have termEq on final heap.
      --
      -- This requires well-founded induction on term depth, where
      -- step strictly decreases total depth by replacing one pair
      -- with smaller subterm pairs.
      sorry

/-- When run terminates normally (not failed, PDL empty), properties hold.
    This is the form we actually use for soundness. -/
theorem UnifyState.run_terminates_complete (_us : UnifyState) (_fuel : Nat)
    (_hnotfail : ¬(_us.run _fuel).fail)
    (_hempty : (_us.run _fuel).pdl.isEmpty) :
    True := trivial  -- Placeholder for now; the important property is run_initial_termEq

/-- Successful unification makes terms structurally equal.
    After unify(a1, a2), if not fail and PDL processed, then termEq a1 a2.

    Note: This theorem assumes the fuel provided is sufficient for termination.
    The proof that heap.size * 2 + 10 is sufficient would require a termination
    measure (sum of term sizes on PDL decreases). -/
theorem UnifyState.unify_sound (us : UnifyState) (a1 a2 : HeapAddr)
    (hnotfail_init : ¬us.fail)
    (hvalid1 : a1 < us.heap.cells.size)
    (hvalid2 : a2 < us.heap.cells.size)
    (hwf : us.heap.wellFormed)
    (hdesc : us.heap.chainsDescend)
    (hnotfail : ¬(us.unify a1 a2).fail)
    (hterminated : (us.unify a1 a2).pdl.isEmpty) :
    (us.unify a1 a2).heap.termEq a1 a2 := by
  -- us.unify a1 a2 = ({ us with pdl := [a1, a2] }).run (fuel)
  unfold unify
  have hpdl : ({ us with pdl := [a1, a2] } : UnifyState).pdl = [a1, a2] := rfl
  apply run_initial_termEq { us with pdl := [a1, a2] } a1 a2 _ hpdl hnotfail_init hvalid1 hvalid2 hwf hdesc
  unfold unify at hnotfail hterminated
  exact ⟨hterminated, hnotfail⟩

end Mettapedia.AutoBooks.ClaudeProcWam.WAM
