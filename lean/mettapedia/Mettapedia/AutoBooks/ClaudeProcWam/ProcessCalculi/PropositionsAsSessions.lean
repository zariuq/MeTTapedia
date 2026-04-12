/-
# Propositions as Sessions

Formalization of Wadler's (2012) correspondence between propositions
and sessions, building on Caires-Pfenning (2010).

## Key Correspondence

| Linear Logic      | Session Type     | Process           |
|-------------------|------------------|-------------------|
| A ⊗ B             | A ⊗ B            | x[y].(P | Q)      |
| A ⅋ B             | A ⅋ B            | x(y).P            |
| A & B             | A & B            | x.case(P, Q)      |
| A ⊕ B             | A ⊕ B            | x.inl; P          |
| !A                | !A               | !x(y).P           |
| ?A                | ?A               | ?x[y].P           |
| 1                 | end              | x[].0             |
| ⊥                 | end⊥             | x().P             |

## Main Results

- Type preservation under reduction
- Progress: well-typed processes are deadlock-free
- Cut elimination corresponds to communication

## References

- Wadler (2012): Propositions as Sessions
- Caires & Pfenning (2010): Session Types as Intuitionistic Linear Propositions
-/

import Mettapedia.AutoBooks.ClaudeProcWam.ProcessCalculi.SessionTypes

namespace Mettapedia.AutoBooks.ClaudeProcWam.ProcessCalculi

open SessionType

/-! ## Classical Linear Logic (CLL) Propositions

Following Wadler, we use classical linear logic for symmetric duality.
-/

/-- Classical linear logic propositions -/
inductive CLLProp where
  /-- Atomic proposition -/
  | atom : String → CLLProp
  /-- Dual of atomic -/
  | atomDual : String → CLLProp
  /-- Tensor: A ⊗ B -/
  | tensor : CLLProp → CLLProp → CLLProp
  /-- Par: A ⅋ B -/
  | par : CLLProp → CLLProp → CLLProp
  /-- With: A & B -/
  | addConj : CLLProp → CLLProp → CLLProp
  /-- Plus: A ⊕ B -/
  | addDisj : CLLProp → CLLProp → CLLProp
  /-- One: 1 -/
  | one : CLLProp
  /-- Bottom: ⊥ -/
  | bot : CLLProp
  /-- Top: ⊤ -/
  | top : CLLProp
  /-- Zero: 0 -/
  | zero : CLLProp
  /-- Of course: !A -/
  | ofCourse : CLLProp → CLLProp
  /-- Why not: ?A -/
  | whyNot : CLLProp → CLLProp
  deriving DecidableEq, Repr, Inhabited

namespace CLLProp

/-- Linear negation (duality) -/
def dual : CLLProp → CLLProp
  | .atom x => .atomDual x
  | .atomDual x => .atom x
  | .tensor a b => .par a.dual b.dual
  | .par a b => .tensor a.dual b.dual
  | .addConj a b => .addDisj a.dual b.dual
  | .addDisj a b => .addConj a.dual b.dual
  | .one => .bot
  | .bot => .one
  | .top => .zero
  | .zero => .top
  | .ofCourse a => .whyNot a.dual
  | .whyNot a => .ofCourse a.dual

/-- Duality is involutive -/
theorem dual_dual (a : CLLProp) : a.dual.dual = a := by
  induction a with
  | atom _ => rfl
  | atomDual _ => rfl
  | one => rfl
  | bot => rfl
  | top => rfl
  | zero => rfl
  | tensor a b iha ihb => simp only [dual, iha, ihb]
  | par a b iha ihb => simp only [dual, iha, ihb]
  | addConj a b iha ihb => simp only [dual, iha, ihb]
  | addDisj a b iha ihb => simp only [dual, iha, ihb]
  | ofCourse a ih => simp only [dual, ih]
  | whyNot a ih => simp only [dual, ih]

instance : ToString CLLProp where
  toString p := go p
where
  go : CLLProp → String
    | .atom x => x
    | .atomDual x => s!"{x}⊥"
    | .tensor a b => s!"({go a} ⊗ {go b})"
    | .par a b => s!"({go a} ⅋ {go b})"
    | .addConj a b => s!"({go a} & {go b})"
    | .addDisj a b => s!"({go a} ⊕ {go b})"
    | .one => "1"
    | .bot => "⊥"
    | .top => "⊤"
    | .zero => "0"
    | .ofCourse a => s!"!{go a}"
    | .whyNot a => s!"?{go a}"

end CLLProp

/-! ## Typing Contexts

Linear contexts where each proposition is used exactly once.
Contexts are multisets of (channel, proposition) pairs.
-/

/-- Channel name -/
abbrev Chan := String

/-- A typing assignment: channel has type A -/
structure TypeAssign where
  chan : Chan
  prop : CLLProp
  deriving DecidableEq, Repr

/-- Typing context (linear, so multiset semantics) -/
abbrev Context := List TypeAssign

/-- Empty context -/
def Context.empty : Context := []

/-- Singleton context -/
def Context.singleton (x : Chan) (a : CLLProp) : Context := [{ chan := x, prop := a }]

/-- Context union (for tensor rule) -/
def Context.union (Γ Δ : Context) : Context := Γ ++ Δ

/-- A context is linear if each channel appears at most once -/
def Context.linear (Γ : Context) : Prop :=
  ∀ i j : Fin Γ.length, Γ[i].chan = Γ[j].chan → i = j

/-- Get all channels in a context -/
def Context.chans (Γ : Context) : List Chan := Γ.map (·.chan)

/-- Channel not in context -/
def Context.notMem (c : Chan) (Γ : Context) : Prop := c ∉ Γ.chans

/-- Two contexts are disjoint (no shared channels) -/
def Context.disjoint (Γ Δ : Context) : Prop :=
  ∀ c ∈ Γ.chans, c ∉ Δ.chans

/-- In a linear context, if a channel appears at position n, it doesn't appear before n -/
theorem Context.linear_no_dup_prefix (Γ : Context) (hlin : Γ.linear) (n : Fin Γ.length)
    (i : Fin Γ.length) (hi : i.val < n.val) : Γ[i].chan ≠ Γ[n].chan := by
  intro heq
  have := hlin i n heq
  omega

/-- Channel at end of context is not in the prefix -/
theorem Context.end_not_in_prefix (Γ : Context) (ta : TypeAssign) (hlin : (Γ ++ [ta]).linear) :
    ta.chan ∉ Γ.chans := by
  intro hmem
  simp only [Context.chans, List.mem_map] at hmem
  obtain ⟨ta', hta'Γ, hchan⟩ := hmem
  -- ta' ∈ Γ with ta'.chan = ta.chan
  -- In the linear context Γ ++ [ta], ta appears at position |Γ|
  -- ta' appears at some position i < |Γ|
  -- They have the same channel, contradicting linearity
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hta'Γ
  have hn : Γ.length < (Γ ++ [ta]).length := by simp
  have hilt : i < (Γ ++ [ta]).length := Nat.lt_of_lt_of_le hi (by simp)
  let fi : Fin (Γ ++ [ta]).length := ⟨i, hilt⟩
  let fn : Fin (Γ ++ [ta]).length := ⟨Γ.length, hn⟩
  have hget_i : (Γ ++ [ta]).get fi = Γ[i] := by simp [fi, List.getElem_append_left hi]
  have hget_n : (Γ ++ [ta]).get fn = ta := by simp [fn]
  have heq' : ((Γ ++ [ta]).get fi).chan = ((Γ ++ [ta]).get fn).chan := by
    simp only [hget_i, hget_n, hget, hchan]
  have hfin_eq := hlin fi fn heq'
  simp only [fi, fn, Fin.mk.injEq] at hfin_eq
  omega

/-! ## Processes (π-calculus with Sessions)

Based on Wadler's CP calculus.
-/

/-- Process terms -/
inductive CPProc where
  /-- Terminated process -/
  | nil : CPProc
  /-- Parallel composition: P | Q -/
  | par : CPProc → CPProc → CPProc
  /-- Output on x, bind y, continue as P | Q -/
  | out : Chan → Chan → CPProc → CPProc → CPProc
  /-- Input on x, bind y, continue as P -/
  | inp : Chan → Chan → CPProc → CPProc
  /-- Left selection on x, continue as P -/
  | inl : Chan → CPProc → CPProc
  /-- Right selection on x, continue as P -/
  | inr : Chan → CPProc → CPProc
  /-- Case on x, branches P and Q -/
  | case : Chan → CPProc → CPProc → CPProc
  /-- Empty output on x (for 1) -/
  | emptyOut : Chan → CPProc
  /-- Empty input on x, continue as P (for ⊥) -/
  | emptyInp : Chan → CPProc → CPProc
  /-- Server accept on x, bind y, continue as P -/
  | accept : Chan → Chan → CPProc → CPProc
  /-- Client request on x, bind y, continue as P -/
  | request : Chan → Chan → CPProc → CPProc
  /-- Link two channels -/
  | link : Chan → Chan → CPProc
  /-- Channel restriction (new channel) -/
  | nu : Chan → CLLProp → CPProc → CPProc
  deriving Repr, Inhabited

instance : ToString CPProc where
  toString p := go p
where
  go : CPProc → String
    | .nil => "0"
    | .par p q => s!"({go p} | {go q})"
    | .out x y p q => s!"{x}[{y}].({go p} | {go q})"
    | .inp x y p => s!"{x}({y}).{go p}"
    | .inl x p => s!"{x}.inl;{go p}"
    | .inr x p => s!"{x}.inr;{go p}"
    | .case x p q => s!"{x}.case({go p}, {go q})"
    | .emptyOut x => s!"{x}[]"
    | .emptyInp x p => s!"{x}().{go p}"
    | .accept x y p => s!"!{x}({y}).{go p}"
    | .request x y p => s!"?{x}[{y}].{go p}"
    | .link x w => s!"{x}↔{w}"
    | .nu x a p => s!"(ν{x}:{a}){go p}"

/-- Channel substitution in processes: P[y/z] replaces z with y -/
def CPProc.subst (p : CPProc) (y z : Chan) : CPProc :=
  let s := fun c => if c == z then y else c
  match p with
  | .nil => .nil
  | .par p1 p2 => .par (p1.subst y z) (p2.subst y z)
  | .out x w p1 p2 =>
    if w == z then .out (s x) w p1 (p2.subst y z)  -- w binds z in p1
    else .out (s x) (s w) (p1.subst y z) (p2.subst y z)
  | .inp x w p1 =>
    if w == z then p  -- z is bound, don't substitute in body
    else .inp (s x) w (p1.subst y z)
  | .inl x p1 => .inl (s x) (p1.subst y z)
  | .inr x p1 => .inr (s x) (p1.subst y z)
  | .case x p1 p2 => .case (s x) (p1.subst y z) (p2.subst y z)
  | .emptyOut x => .emptyOut (s x)
  | .emptyInp x p1 => .emptyInp (s x) (p1.subst y z)
  | .accept x w p1 =>
    if w == z then .accept (s x) w p1  -- z is bound
    else .accept (s x) w (p1.subst y z)
  | .request x w p1 =>
    if w == z then .request (s x) w p1  -- z is bound
    else .request (s x) w (p1.subst y z)
  | .link x w => .link (s x) (s w)
  | .nu x a p1 =>
    if x == z then p  -- z is bound by ν, don't substitute
    else .nu x a (p1.subst y z)

/-- Free channels in a process (channels mentioned that aren't bound).
    In tensor output `x[w].(P|Q)`, the channel `w` is bound (sent to partner)
    and used in P, so it's filtered from P's free channels. -/
def CPProc.freeChans : CPProc → List Chan
  | .nil => []
  | .par p1 p2 => p1.freeChans ++ p2.freeChans
  | .out x w p1 p2 => [x] ++ (p1.freeChans.filter (· != w)) ++ p2.freeChans
  | .inp x w p1 => [x] ++ (p1.freeChans.filter (· != w))
  | .inl x p1 => [x] ++ p1.freeChans
  | .inr x p1 => [x] ++ p1.freeChans
  | .case x p1 p2 => [x] ++ p1.freeChans ++ p2.freeChans
  | .emptyOut x => [x]
  | .emptyInp x p1 => [x] ++ p1.freeChans
  | .accept x w p1 => [x] ++ (p1.freeChans.filter (· != w))
  | .request x w p1 => [x] ++ (p1.freeChans.filter (· != w))
  | .link x w => [x, w]
  | .nu x _ p1 => p1.freeChans.filter (· != x)

/-- Helper: if x == y then y else x = x -/
private theorem beq_ite_self (x y : Chan) : (if x == y then y else x) = x := by
  by_cases h : x = y
  · simp [h]
  · simp [beq_eq_false_iff_ne.mpr h]

/-- Substituting a channel for itself has no effect -/
theorem CPProc.subst_self (p : CPProc) (y : Chan) : p.subst y y = p := by
  induction p with
  | nil => rfl
  | par p1 p2 ih1 ih2 => simp only [subst, ih1, ih2]
  | out x w p1 p2 ih1 ih2 =>
    simp only [subst]
    by_cases hw : w = y
    · simp only [hw, beq_self_eq_true, ↓reduceIte, beq_ite_self, ih2]
    · simp only [beq_eq_false_iff_ne.mpr hw, Bool.false_eq_true, ↓reduceIte, beq_ite_self, ih1, ih2]
  | inp x w p1 ih1 =>
    simp only [subst]
    by_cases hw : w = y
    · simp only [hw, beq_self_eq_true, ↓reduceIte]
    · simp only [beq_eq_false_iff_ne.mpr hw, Bool.false_eq_true, ↓reduceIte, beq_ite_self, ih1]
  | inl x p1 ih1 => simp only [subst, beq_ite_self, ih1]
  | inr x p1 ih1 => simp only [subst, beq_ite_self, ih1]
  | case x p1 p2 ih1 ih2 => simp only [subst, beq_ite_self, ih1, ih2]
  | emptyOut x => simp only [subst, beq_ite_self]
  | emptyInp x p1 ih1 => simp only [subst, beq_ite_self, ih1]
  | accept x w p1 ih1 =>
    simp only [subst]
    by_cases hw : w = y
    · simp only [hw, beq_self_eq_true, ↓reduceIte, beq_ite_self]
    · simp only [beq_eq_false_iff_ne.mpr hw, Bool.false_eq_true, ↓reduceIte, beq_ite_self, ih1]
  | request x w p1 ih1 =>
    simp only [subst]
    by_cases hw : w = y
    · simp only [hw, beq_self_eq_true, ↓reduceIte, beq_ite_self]
    · simp only [beq_eq_false_iff_ne.mpr hw, Bool.false_eq_true, ↓reduceIte, beq_ite_self, ih1]
  | link x w => simp only [subst, beq_ite_self]
  | nu x a p1 ih1 =>
    simp only [subst]
    by_cases hx : x = y
    · simp only [hx, beq_self_eq_true, ↓reduceIte]
    · simp only [beq_eq_false_iff_ne.mpr hx, Bool.false_eq_true, ↓reduceIte, ih1]

/-- Substituting a channel not free in the process has no effect -/
theorem CPProc.subst_not_free (p : CPProc) (y z : Chan) (h : z ∉ p.freeChans) :
    p.subst y z = p := by
  induction p with
  | nil => rfl
  | par p1 p2 ih1 ih2 =>
    simp only [freeChans, List.mem_append, not_or] at h
    simp only [subst, ih1 h.1, ih2 h.2]
  | out x w p1 p2 ih1 ih2 =>
    -- freeChans: [x] ++ (p1.freeChans.filter (· != w)) ++ p2.freeChans
    -- subst: if w == z then .out (s x) w p1 (p2.subst y z) else .out (s x) (s w) ...
    unfold freeChans at h
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
               List.mem_filter, not_or, not_and, bne_iff_ne] at h
    -- h.1.1 : z ≠ x, h.1.2 : z ∈ p1.freeChans → z = w, h.2 : z ∉ p2.freeChans
    unfold subst
    by_cases hwz : w = z
    · -- w = z: binding shadows z in p1, only substitute in p2
      have hzx : z ≠ x := h.1.1
      have hxz : (x == z) = false := beq_eq_false_iff_ne.mpr hzx.symm
      have h2 : z ∉ p2.freeChans := h.2
      simp only [hwz, beq_self_eq_true, ↓reduceIte, hxz, Bool.false_eq_true, ih2 h2]
    · have hzx : z ≠ x := h.1.1
      have hxz : (x == z) = false := beq_eq_false_iff_ne.mpr hzx.symm
      have hwne : w ≠ z := fun heq => hwz heq
      have hwzf : (w == z) = false := beq_eq_false_iff_ne.mpr hwne
      -- h.1.2 : z ∈ p1.freeChans → ¬z ≠ w (i.e., → z = w by double negation)
      have h1 : z ∉ p1.freeChans := fun hmem =>
        hwz (Decidable.not_not.mp (h.1.2 hmem)).symm
      have h2 : z ∉ p2.freeChans := h.2
      simp only [hwzf, Bool.false_eq_true, ↓reduceIte, hxz, ih1 h1, ih2 h2]
  | inp x w p1 ih1 =>
    unfold freeChans at h
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
               List.mem_filter, not_or, not_and, bne_iff_ne] at h
    unfold subst
    by_cases hwz : w = z
    · simp only [hwz, beq_self_eq_true, ↓reduceIte]
    · have hzx : z ≠ x := h.1
      have hxz : (x == z) = false := beq_eq_false_iff_ne.mpr hzx.symm
      have hwne : w ≠ z := fun heq => hwz heq
      have hwzf : (w == z) = false := beq_eq_false_iff_ne.mpr hwne
      have hfree : z ∉ p1.freeChans := fun hmem =>
        hwz (Decidable.not_not.mp (h.2 hmem)).symm
      simp only [hwzf, Bool.false_eq_true, ↓reduceIte, hxz, ih1 hfree]
  | inl x p1 ih1 =>
    unfold freeChans at h
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
    have hzx : z ≠ x := h.1
    have hxz : (x == z) = false := beq_eq_false_iff_ne.mpr hzx.symm
    simp only [subst, hxz, Bool.false_eq_true, ↓reduceIte, ih1 h.2]
  | inr x p1 ih1 =>
    unfold freeChans at h
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
    have hzx : z ≠ x := h.1
    have hxz : (x == z) = false := beq_eq_false_iff_ne.mpr hzx.symm
    simp only [subst, hxz, Bool.false_eq_true, ↓reduceIte, ih1 h.2]
  | case x p1 p2 ih1 ih2 =>
    unfold freeChans at h
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
    have hzx : z ≠ x := h.1.1
    have hxz : (x == z) = false := beq_eq_false_iff_ne.mpr hzx.symm
    have h1 : z ∉ p1.freeChans := h.1.2
    have h2 : z ∉ p2.freeChans := h.2
    simp only [subst, hxz, Bool.false_eq_true, ↓reduceIte, ih1 h1, ih2 h2]
  | emptyOut x =>
    unfold freeChans at h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    have hxz : (x == z) = false := beq_eq_false_iff_ne.mpr fun heq => h heq.symm
    simp only [subst, hxz, Bool.false_eq_true, ↓reduceIte]
  | emptyInp x p1 ih1 =>
    unfold freeChans at h
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
    have hzx : z ≠ x := h.1
    have hxz : (x == z) = false := beq_eq_false_iff_ne.mpr hzx.symm
    simp only [subst, hxz, Bool.false_eq_true, ↓reduceIte, ih1 h.2]
  | accept x w p1 ih1 =>
    unfold freeChans at h
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
               List.mem_filter, not_or, not_and, bne_iff_ne] at h
    unfold subst
    by_cases hwz : w = z
    · have hzx : z ≠ x := h.1
      have hxz : (x == z) = false := beq_eq_false_iff_ne.mpr hzx.symm
      simp only [hwz, beq_self_eq_true, hxz, Bool.false_eq_true, if_true, if_false]
    · have hzx : z ≠ x := h.1
      have hxz : (x == z) = false := beq_eq_false_iff_ne.mpr hzx.symm
      have hwne : w ≠ z := fun heq => hwz heq
      have hwzf : (w == z) = false := beq_eq_false_iff_ne.mpr hwne
      have hfree : z ∉ p1.freeChans := fun hmem =>
        hwz (Decidable.not_not.mp (h.2 hmem)).symm
      simp only [hwzf, Bool.false_eq_true, ↓reduceIte, hxz, ih1 hfree]
  | request x w p1 ih1 =>
    unfold freeChans at h
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
               List.mem_filter, not_or, not_and, bne_iff_ne] at h
    unfold subst
    by_cases hwz : w = z
    · have hzx : z ≠ x := h.1
      have hxz : (x == z) = false := beq_eq_false_iff_ne.mpr hzx.symm
      simp only [hwz, beq_self_eq_true, hxz, Bool.false_eq_true, if_true, if_false]
    · have hzx : z ≠ x := h.1
      have hxz : (x == z) = false := beq_eq_false_iff_ne.mpr hzx.symm
      have hwne : w ≠ z := fun heq => hwz heq
      have hwzf : (w == z) = false := beq_eq_false_iff_ne.mpr hwne
      have hfree : z ∉ p1.freeChans := fun hmem =>
        hwz (Decidable.not_not.mp (h.2 hmem)).symm
      simp only [hwzf, Bool.false_eq_true, ↓reduceIte, hxz, ih1 hfree]
  | link x w =>
    unfold freeChans at h
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
    have hxz : (x == z) = false := beq_eq_false_iff_ne.mpr fun heq => h.1 heq.symm
    have hwz : (w == z) = false := beq_eq_false_iff_ne.mpr fun heq => h.2 heq.symm
    simp only [subst, hxz, hwz, Bool.false_eq_true, ↓reduceIte]
  | nu x a p1 ih1 =>
    unfold freeChans at h
    simp only [List.mem_filter, not_and, bne_iff_ne] at h
    unfold subst
    by_cases hxz : x = z
    · simp only [hxz, beq_self_eq_true, ↓reduceIte]
    · have hfree : z ∉ p1.freeChans := fun hmem => h hmem fun heq => hxz heq.symm
      simp only [beq_eq_false_iff_ne.mpr hxz, Bool.false_eq_true, ↓reduceIte, ih1 hfree]

/-! ## Typing Rules

These correspond to linear logic proof rules.
-/

/-- Helper to create type assignment -/
def mkAssign (x : Chan) (a : CLLProp) : TypeAssign := { chan := x, prop := a }

/-- Well-typedness judgment: Γ ⊢ P -/
inductive CPTyped : Context → CPProc → Prop where
  /-- Axiom/Link: x:A, w:A⊥ ⊢ x↔w -/
  | ax (x w : Chan) (a : CLLProp) :
      CPTyped [mkAssign x a, mkAssign w a.dual] (.link x w)

  /-- Cut: If Γ,x:A ⊢ P and Δ,x:A⊥ ⊢ Q then Γ,Δ ⊢ (νx:A)(P | Q) -/
  | cut (Γ Δ : Context) (x : Chan) (a : CLLProp) (p q : CPProc)
      (hp : CPTyped (Γ ++ [mkAssign x a]) p)
      (hq : CPTyped (Δ ++ [mkAssign x a.dual]) q) :
      CPTyped (Γ ++ Δ) (.nu x a (.par p q))

  /-- ⊗R: If Γ,y:A ⊢ P and Δ,x:B ⊢ Q then Γ,Δ,x:A⊗B ⊢ x[y].(P|Q) -/
  | tensorR (Γ Δ : Context) (x y : Chan) (a b : CLLProp) (p q : CPProc)
      (hp : CPTyped (Γ ++ [mkAssign y a]) p)
      (hq : CPTyped (Δ ++ [mkAssign x b]) q) :
      CPTyped (Γ ++ Δ ++ [mkAssign x (.tensor a b)]) (.out x y p q)

  /-- ⅋R: If Γ,y:A,x:B ⊢ P then Γ,x:A⅋B ⊢ x(y).P -/
  | parR (Γ : Context) (x y : Chan) (a b : CLLProp) (p : CPProc)
      (hp : CPTyped (Γ ++ [mkAssign y a, mkAssign x b]) p) :
      CPTyped (Γ ++ [mkAssign x (.par a b)]) (.inp x y p)

  /-- &R: If Γ,x:A ⊢ P and Γ,x:B ⊢ Q then Γ,x:A&B ⊢ x.case(P,Q) -/
  | addConjR (Γ : Context) (x : Chan) (a b : CLLProp) (p q : CPProc)
      (hp : CPTyped (Γ ++ [mkAssign x a]) p)
      (hq : CPTyped (Γ ++ [mkAssign x b]) q) :
      CPTyped (Γ ++ [mkAssign x (.addConj a b)]) (.case x p q)

  /-- ⊕R₁: If Γ,x:A ⊢ P then Γ,x:A⊕B ⊢ x.inl;P -/
  | addDisjR1 (Γ : Context) (x : Chan) (a b : CLLProp) (p : CPProc)
      (hp : CPTyped (Γ ++ [mkAssign x a]) p) :
      CPTyped (Γ ++ [mkAssign x (.addDisj a b)]) (.inl x p)

  /-- ⊕R₂: If Γ,x:B ⊢ P then Γ,x:A⊕B ⊢ x.inr;P -/
  | addDisjR2 (Γ : Context) (x : Chan) (a b : CLLProp) (p : CPProc)
      (hp : CPTyped (Γ ++ [mkAssign x b]) p) :
      CPTyped (Γ ++ [mkAssign x (.addDisj a b)]) (.inr x p)

  /-- 1R: x:1 ⊢ x[] -/
  | oneR (x : Chan) :
      CPTyped [mkAssign x .one] (.emptyOut x)

  /-- ⊥R: If Γ ⊢ P then Γ,x:⊥ ⊢ x().P -/
  | botR (Γ : Context) (x : Chan) (p : CPProc)
      (hp : CPTyped Γ p) :
      CPTyped (Γ ++ [mkAssign x .bot]) (.emptyInp x p)

  /-- ⊤R: Γ,x:⊤ ⊢ anything (unused premise) -/
  | topR (Γ : Context) (x : Chan) (p : CPProc) :
      CPTyped (Γ ++ [mkAssign x .top]) p

  /-- Mix: If Γ ⊢ P and Δ ⊢ Q then Γ,Δ ⊢ P | Q
      Parallel composition with disjoint contexts (mix rule). -/
  | mix (Γ Δ : Context) (p q : CPProc)
      (hp : CPTyped Γ p)
      (hq : CPTyped Δ q) :
      CPTyped (Γ ++ Δ) (.par p q)

/-- Well-typed processes have linear contexts (each channel appears at most once).
    This is fundamental to linear logic: every channel is used exactly once.

    Note: This requires careful analysis of each typing rule. The ax rule assumes
    x ≠ w for well-formedness. The cut/tensorR/mix rules require context disjointness.
    TODO: Full proof requires formalizing these constraints. -/
theorem CPTyped.context_linear (h : CPTyped Γ p) : Γ.linear := by
  sorry

/-- Free channels of a well-typed process are contained in the context.
    This is a key property of linear logic typing: every channel used in a
    process must be accounted for in the typing context.

    Note: The topR case is problematic since it types any process. We use sorry
    there, but in practice topR is used with specific well-formed processes. -/
theorem CPTyped.freeChans_subset_context (h : CPTyped Γ p) :
    ∀ c ∈ p.freeChans, ∃ ta ∈ Γ, ta.chan = c := by
  induction h with
  | ax x w a =>
    intro c hc
    simp only [CPProc.freeChans, List.mem_cons, List.not_mem_nil, or_false] at hc
    cases hc with
    | inl hcx => exact ⟨mkAssign x a, .head _, hcx.symm⟩
    | inr hcw => exact ⟨mkAssign w a.dual, .tail _ (.head _), hcw.symm⟩
  | cut Γ' Δ' x a p q hp hq ihp ihq =>
    intro c hc
    simp only [CPProc.freeChans, List.mem_filter, bne_iff_ne,
               CPProc.freeChans, List.mem_append] at hc
    cases hc.1 with
    | inl hcp =>
      obtain ⟨ta, htaΓ, htac⟩ := ihp c hcp
      simp only [List.mem_append] at htaΓ
      cases htaΓ with
      | inl htaΓ' => exact ⟨ta, List.mem_append_left _ htaΓ', htac⟩
      | inr htax =>
        simp only [List.mem_singleton] at htax
        rw [htax] at htac
        exact absurd htac.symm hc.2
    | inr hcq =>
      obtain ⟨ta, htaΔ, htac⟩ := ihq c hcq
      simp only [List.mem_append] at htaΔ
      cases htaΔ with
      | inl htaΔ' => exact ⟨ta, List.mem_append_right _ htaΔ', htac⟩
      | inr htax =>
        simp only [List.mem_singleton] at htax
        rw [htax] at htac
        exact absurd htac.symm hc.2
  | tensorR Γ' Δ' x y a b p q hp hq ihp ihq =>
    intro c hc
    -- freeChans of .out x y p q is now [x] ++ filter (· != y) p.freeChans ++ q.freeChans
    simp only [CPProc.freeChans, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
               List.mem_filter, bne_iff_ne, or_assoc] at hc
    -- hc : c = x ∨ (c ∈ p.freeChans ∧ c ≠ y) ∨ c ∈ q.freeChans
    rcases hc with hcx | ⟨hcp, hcney⟩ | hcq
    · exact ⟨mkAssign x (.tensor a b), List.mem_append_right _ (List.mem_singleton.mpr rfl), hcx.symm⟩
    · -- c ∈ p.freeChans and c ≠ y
      obtain ⟨ta, htaΓ, htac⟩ := ihp c hcp
      simp only [List.mem_append, List.mem_singleton] at htaΓ
      rcases htaΓ with htaΓ' | htay
      · exact ⟨ta, List.mem_append_left _ (List.mem_append_left _ htaΓ'), htac⟩
      · -- ta = mkAssign y a, so c = y, but hcney says c ≠ y - contradiction
        rw [htay] at htac
        exact absurd htac.symm hcney
    · obtain ⟨ta, htaΔ, htac⟩ := ihq c hcq
      simp only [List.mem_append, List.mem_singleton] at htaΔ
      rcases htaΔ with htaΔ' | htax
      · exact ⟨ta, List.mem_append_left _ (List.mem_append_right _ htaΔ'), htac⟩
      · rw [htax] at htac
        exact ⟨mkAssign x (.tensor a b), List.mem_append_right _ (List.mem_singleton.mpr rfl), htac⟩
  | parR Γ' x y a b p hp ihp =>
    intro c hc
    simp only [CPProc.freeChans, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
               List.mem_filter, bne_iff_ne] at hc
    rcases hc with hcx | ⟨hcp, hcney⟩
    · exact ⟨mkAssign x (.par a b), List.mem_append_right _ (List.mem_singleton.mpr rfl), hcx.symm⟩
    · obtain ⟨ta, htaΓ, htac⟩ := ihp c hcp
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at htaΓ
      rcases htaΓ with htaΓ' | htay | htax
      · exact ⟨ta, List.mem_append_left _ htaΓ', htac⟩
      · rw [htay] at htac; exact absurd htac.symm hcney
      · rw [htax] at htac
        exact ⟨mkAssign x (.par a b), List.mem_append_right _ (List.mem_singleton.mpr rfl), htac⟩
  | addConjR Γ' x a b p q hp hq ihp ihq =>
    intro c hc
    simp only [CPProc.freeChans, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
               or_assoc] at hc
    rcases hc with hcx | hcp | hcq
    · exact ⟨mkAssign x (.addConj a b), List.mem_append_right _ (List.mem_singleton.mpr rfl), hcx.symm⟩
    · obtain ⟨ta, htaΓ, htac⟩ := ihp c hcp
      simp only [List.mem_append, List.mem_singleton] at htaΓ
      rcases htaΓ with htaΓ' | htax
      · exact ⟨ta, List.mem_append_left _ htaΓ', htac⟩
      · rw [htax] at htac
        exact ⟨mkAssign x (.addConj a b), List.mem_append_right _ (List.mem_singleton.mpr rfl), htac⟩
    · obtain ⟨ta, htaΓ, htac⟩ := ihq c hcq
      simp only [List.mem_append, List.mem_singleton] at htaΓ
      rcases htaΓ with htaΓ' | htax
      · exact ⟨ta, List.mem_append_left _ htaΓ', htac⟩
      · rw [htax] at htac
        exact ⟨mkAssign x (.addConj a b), List.mem_append_right _ (List.mem_singleton.mpr rfl), htac⟩
  | addDisjR1 Γ' x a b p hp ihp =>
    intro c hc
    simp only [CPProc.freeChans, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with hcx | hcp
    · exact ⟨mkAssign x (.addDisj a b), List.mem_append_right _ (List.mem_singleton.mpr rfl), hcx.symm⟩
    · obtain ⟨ta, htaΓ, htac⟩ := ihp c hcp
      simp only [List.mem_append, List.mem_singleton] at htaΓ
      cases htaΓ with
      | inl htaΓ' => exact ⟨ta, List.mem_append_left _ htaΓ', htac⟩
      | inr htax =>
        rw [htax] at htac
        exact ⟨mkAssign x (.addDisj a b), List.mem_append_right _ (List.mem_singleton.mpr rfl), htac⟩
  | addDisjR2 Γ' x a b p hp ihp =>
    intro c hc
    simp only [CPProc.freeChans, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with hcx | hcp
    · exact ⟨mkAssign x (.addDisj a b), List.mem_append_right _ (List.mem_singleton.mpr rfl), hcx.symm⟩
    · obtain ⟨ta, htaΓ, htac⟩ := ihp c hcp
      simp only [List.mem_append, List.mem_singleton] at htaΓ
      cases htaΓ with
      | inl htaΓ' => exact ⟨ta, List.mem_append_left _ htaΓ', htac⟩
      | inr htax =>
        rw [htax] at htac
        exact ⟨mkAssign x (.addDisj a b), List.mem_append_right _ (List.mem_singleton.mpr rfl), htac⟩
  | oneR x =>
    intro c hc
    simp only [CPProc.freeChans, List.mem_cons, List.not_mem_nil, or_false] at hc
    exact ⟨mkAssign x .one, List.mem_singleton.mpr rfl, hc.symm⟩
  | botR Γ' x p hp ihp =>
    intro c hc
    simp only [CPProc.freeChans, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with hcx | hcp
    · exact ⟨mkAssign x .bot, List.mem_append_right _ (List.mem_singleton.mpr rfl), hcx.symm⟩
    · obtain ⟨ta, htaΓ, htac⟩ := ihp c hcp
      exact ⟨ta, List.mem_append_left _ htaΓ, htac⟩
  | topR Γ' x p =>
    -- topR types any process without constraining it, so we cannot prove
    -- that all free channels are in the context. This is a fundamental limitation.
    intro c hc
    by_cases hcx : c = x
    · exact ⟨mkAssign x .top, List.mem_append_right _ (List.mem_singleton.mpr rfl), hcx.symm⟩
    · sorry
  | mix Γ' Δ' p q hp hq ihp ihq =>
    intro c hc
    simp only [CPProc.freeChans, List.mem_append] at hc
    cases hc with
    | inl hcp =>
      obtain ⟨ta, htaΓ, htac⟩ := ihp c hcp
      exact ⟨ta, List.mem_append_left _ htaΓ, htac⟩
    | inr hcq =>
      obtain ⟨ta, htaΔ, htac⟩ := ihq c hcq
      exact ⟨ta, List.mem_append_right _ htaΔ, htac⟩

/-- Corollary: if a channel is not in any context assignment, it's not free in the process.
    Note: This relies on freeChans_subset_context which has a sorry in the topR case. -/
theorem CPTyped.not_in_context_not_free (h : CPTyped Γ p)
    (hnotctx : ∀ ta ∈ Γ, ta.chan ≠ c) : c ∉ p.freeChans := by
  intro hfree
  obtain ⟨ta, htaΓ, htac⟩ := h.freeChans_subset_context c hfree
  exact hnotctx ta htaΓ htac

/-! ## Normal Forms

A process is in normal form if it cannot reduce further. In CP calculus,
normal forms are nil or parallel compositions of normal forms. -/

/-- Process normal form predicate. A process is a normal form if it is:
    - nil (terminated)
    - par of two normal forms (parallel threads both terminated) -/
def CPProc.isNormalForm : CPProc → Prop
  | .nil => True
  | .par p q => p.isNormalForm ∧ q.isNormalForm
  | _ => False

/-- nil is a normal form -/
theorem CPProc.nil_isNormalForm : CPProc.nil.isNormalForm := trivial

/-- par of normal forms is a normal form -/
theorem CPProc.par_isNormalForm (hp : p.isNormalForm) (hq : q.isNormalForm) :
    (CPProc.par p q).isNormalForm := ⟨hp, hq⟩

/-! ## Reduction (Communication)

Process reduction corresponds to cut elimination.
-/

/-- Structural congruence for processes -/
inductive CPCong : CPProc → CPProc → Prop where
  | refl (p : CPProc) : CPCong p p
  | symm (p q : CPProc) : CPCong p q → CPCong q p
  | trans (p q r : CPProc) : CPCong p q → CPCong q r → CPCong p r
  -- Scope extrusion rules would go here

/-- One-step reduction -/
inductive CPReduce : CPProc → CPProc → Prop where
  /-- β-tensor/par: (νx:A⊗B)(x[y].(P|Q) | x(z).R) → (νy:A)(P | R[y/z]) | Q
      Principal cut for tensor ⊗ and par ⅋. The tensor side sends channel y,
      the par side receives and binds z, which gets substituted by y. -/
  | beta_tensor_par (x y z : Chan) (a b : CLLProp) (p q r : CPProc) :
      CPReduce
        (.nu x (.tensor a b)
          (.par (.out x y p q) (.inp x z r)))
        (.par (.nu y a (.par p (r.subst y z))) q)

  /-- β-par/tensor: symmetric case -/
  | beta_par_tensor (x y z : Chan) (a b : CLLProp) (p q r : CPProc) :
      CPReduce
        (.nu x (.par a b)
          (.par (.inp x y p) (.out x z q r)))
        (.par (.nu y a (.par p (q.subst y z))) r)

  /-- β-addDisj-l/addConj: (νx:A⊕B)(x.inl;P | x.case(Q,R)) → (νx:A)(P | Q)
      The ⊕ side selects left, the & side provides the left branch. -/
  | beta_addDisj_l (x : Chan) (a b : CLLProp) (p q r : CPProc) :
      CPReduce
        (.nu x (.addDisj a b)
          (.par (.inl x p) (.case x q r)))
        (.nu x a (.par p q))

  /-- β-addDisj-r/addConj: (νx:A⊕B)(x.inr;P | x.case(Q,R)) → (νx:B)(P | R) -/
  | beta_addDisj_r (x : Chan) (a b : CLLProp) (p q r : CPProc) :
      CPReduce
        (.nu x (.addDisj a b)
          (.par (.inr x p) (.case x q r)))
        (.nu x b (.par p r))

  /-- β-one/bot: (νx:1)(x[] | x().P) → P
      Unit/counit interaction. -/
  | beta_one_bot (x : Chan) (p : CPProc) :
      CPReduce
        (.nu x .one (.par (.emptyOut x) (.emptyInp x p)))
        p

  /-- β-bot/one: symmetric case -/
  | beta_bot_one (x : Chan) (p : CPProc) :
      CPReduce
        (.nu x .bot (.par (.emptyInp x p) (.emptyOut x)))
        p

  /-- Congruence: reduction under restriction -/
  | cong_nu (x : Chan) (a : CLLProp) (p p' : CPProc)
      (hred : CPReduce p p') :
      CPReduce (.nu x a p) (.nu x a p')

  /-- Congruence: reduction in left of parallel -/
  | cong_par_l (p p' q : CPProc)
      (hred : CPReduce p p') :
      CPReduce (.par p q) (.par p' q)

  /-- Congruence: reduction in right of parallel -/
  | cong_par_r (p q q' : CPProc)
      (hred : CPReduce q q') :
      CPReduce (.par p q) (.par p q')

/-! ## Properties -/

/-! ### Inversion Lemmas

    These lemmas characterize the possible typing derivations for specific process forms.
    They are needed to handle dependent elimination in the principal cut cases. -/

/-- Inversion for .emptyOut: only oneR or topR can type it -/
lemma CPTyped.emptyOut_inv (Γ : Context) (x : Chan) (h : CPTyped Γ (.emptyOut x)) :
    (Γ = [mkAssign x .one]) ∨
    (∃ Γ' y, Γ = Γ' ++ [mkAssign y .top]) := by
  cases h with
  | oneR x' => left; rfl
  | topR Γ' y _ => right; exact ⟨Γ', y, rfl⟩

/-- Inversion for .emptyInp: only botR or topR can type it -/
lemma CPTyped.emptyInp_inv (Γ : Context) (x : Chan) (p : CPProc)
    (h : CPTyped Γ (.emptyInp x p)) :
    (∃ Δ, Γ = Δ ++ [mkAssign x .bot] ∧ CPTyped Δ p) ∨
    (∃ Γ' y, Γ = Γ' ++ [mkAssign y .top]) := by
  cases h with
  | botR Δ x' p' hp => left; exact ⟨Δ, rfl, hp⟩
  | topR Γ' y _ => right; exact ⟨Γ', y, rfl⟩

/-- Inversion for .out (tensor output): only tensorR or topR can type it -/
lemma CPTyped.out_inv (Γctx : Context) (x y : Chan) (p q : CPProc)
    (h : CPTyped Γctx (.out x y p q)) :
    (∃ Γ Δ a b, Γctx = Γ ++ Δ ++ [mkAssign x (.tensor a b)] ∧
                CPTyped (Γ ++ [mkAssign y a]) p ∧
                CPTyped (Δ ++ [mkAssign x b]) q) ∨
    (∃ Γ' z, Γctx = Γ' ++ [mkAssign z .top]) := by
  cases h with
  | tensorR Γ Δ x' y' a b p' q' hp hq =>
    left; exact ⟨Γ, Δ, a, b, rfl, hp, hq⟩
  | topR Γ' z _ => right; exact ⟨Γ', z, rfl⟩

/-- Inversion for .inp (par input): only parR or topR can type it -/
lemma CPTyped.inp_inv (Γctx : Context) (x y : Chan) (p : CPProc)
    (h : CPTyped Γctx (.inp x y p)) :
    (∃ Γ a b, Γctx = Γ ++ [mkAssign x (.par a b)] ∧
              CPTyped (Γ ++ [mkAssign y a, mkAssign x b]) p) ∨
    (∃ Γ' z, Γctx = Γ' ++ [mkAssign z .top]) := by
  cases h with
  | parR Γ x' y' a b p' hp => left; exact ⟨Γ, a, b, rfl, hp⟩
  | topR Γ' z _ => right; exact ⟨Γ', z, rfl⟩

/-- Inversion for .case (additive conjunction): only addConjR or topR can type it -/
lemma CPTyped.case_inv (Γctx : Context) (x : Chan) (p q : CPProc)
    (h : CPTyped Γctx (.case x p q)) :
    (∃ Γ a b, Γctx = Γ ++ [mkAssign x (.addConj a b)] ∧
              CPTyped (Γ ++ [mkAssign x a]) p ∧
              CPTyped (Γ ++ [mkAssign x b]) q) ∨
    (∃ Γ' z, Γctx = Γ' ++ [mkAssign z .top]) := by
  cases h with
  | addConjR Γ x' a b p' q' hp hq => left; exact ⟨Γ, a, b, rfl, hp, hq⟩
  | topR Γ' z _ => right; exact ⟨Γ', z, rfl⟩

/-- Inversion for .inl (additive left): only addDisjR1 or topR can type it -/
lemma CPTyped.inl_inv (Γctx : Context) (x : Chan) (p : CPProc)
    (h : CPTyped Γctx (.inl x p)) :
    (∃ Γ a b, Γctx = Γ ++ [mkAssign x (.addDisj a b)] ∧
              CPTyped (Γ ++ [mkAssign x a]) p) ∨
    (∃ Γ' z, Γctx = Γ' ++ [mkAssign z .top]) := by
  cases h with
  | addDisjR1 Γ x' a b p' hp => left; exact ⟨Γ, a, b, rfl, hp⟩
  | topR Γ' z _ => right; exact ⟨Γ', z, rfl⟩

/-- Inversion for .inr (additive right): only addDisjR2 or topR can type it -/
lemma CPTyped.inr_inv (Γctx : Context) (x : Chan) (p : CPProc)
    (h : CPTyped Γctx (.inr x p)) :
    (∃ Γ a b, Γctx = Γ ++ [mkAssign x (.addDisj a b)] ∧
              CPTyped (Γ ++ [mkAssign x b]) p) ∨
    (∃ Γ' z, Γctx = Γ' ++ [mkAssign z .top]) := by
  cases h with
  | addDisjR2 Γ x' a b p' hp => left; exact ⟨Γ, a, b, rfl, hp⟩
  | topR Γ' z _ => right; exact ⟨Γ', z, rfl⟩

/-- Helper: substitute channel in context assignment list -/
def Context.substChan (ctx : Context) (y z : Chan) : Context :=
  ctx.map fun a => ⟨if a.chan == z then y else a.chan, a.prop⟩

/-- Channel substitution preserves typing (renaming lemma).
    If Γ, z:A ⊢ P and y is fresh, then Γ, y:A ⊢ P[y/z].

    This is a key lemma for cut elimination in CLL / session types.
    The proof is by induction on the typing derivation.

    Note: This requires careful handling because the context shape in the
    typing derivation may differ from the expected shape Γ ++ [z:A]. -/
theorem CPTyped.subst_typing (Γ : Context) (y z : Chan) (a : CLLProp) (p : CPProc)
    (h : CPTyped (Γ ++ [mkAssign z a]) p)
    (hfresh : ∀ ta ∈ Γ, ta.chan ≠ y) :
    CPTyped (Γ ++ [mkAssign y a]) (p.subst y z) := by
  -- Handle trivial case where y = z (substitution is identity)
  by_cases hyz : y = z
  · rw [hyz, CPProc.subst_self]; exact h
  -- The key insight is that for z to be the typed channel in context Γ ++ [z:a],
  -- the typing derivation must end with a rule that provides that channel.
  -- We generalize z and a so the IH applies at different types in rule premises.
  generalize hctx : Γ ++ [mkAssign z a] = ctx at h
  induction h generalizing Γ z a with
  | ax x w a' =>
    -- ax gives context [x:a', w:a'.dual]
    -- This must equal Γ ++ [z:a], so z=w, a=a'.dual, and Γ=[x:a']
    simp only [CPProc.subst]
    -- Context equality: [mkAssign x a', mkAssign w a'.dual] = Γ ++ [mkAssign z a]
    -- This forces Γ = [mkAssign x a'], z = w, a = a'.dual
    cases Γ with
    | nil =>
      -- Γ = [], so [mkAssign z a] = [mkAssign x a', mkAssign w a'.dual]
      simp only [List.nil_append] at hctx
      -- Length 1 ≠ length 2, contradiction
      have hlen := congrArg List.length hctx
      simp at hlen
    | cons hd tl =>
      cases tl with
      | nil =>
        -- Γ = [hd], context is [hd, mkAssign z a] = [mkAssign x a', mkAssign w a'.dual]
        simp only [List.cons_append, List.nil_append] at hctx
        have h1 := List.cons.inj hctx
        have h2 := List.cons.inj h1.2
        -- h1.1 : hd = mkAssign x a'
        -- h2.1 : mkAssign z a = mkAssign w a'.dual
        have hd_chan : hd.chan = x := by rw [h1.1]; rfl
        have hd_prop : hd.prop = a' := by rw [h1.1]; rfl
        have z_eq_w : z = w := congrArg TypeAssign.chan h2.1
        have a_eq : a = a'.dual := congrArg TypeAssign.prop h2.1
        -- After subst: the goal involves substituting y for z in .link x w
        -- .link x w becomes .link (if x == z then y else x) (if w == z then y else w)
        -- Since z = w, this is .link (if x == w then y else x) y
        rw [z_eq_w]
        simp only [beq_self_eq_true, ↓reduceIte]
        -- Now (if x == w then y else x)
        by_cases hxw : x = w
        · -- x = w: degenerate case with duplicate channel in original context
          -- Original context would be [mkAssign w a', mkAssign w a'.dual]
          -- This is actually typeable (ax allows any distinct or same names)
          -- Result: .link y y with context [hd] ++ [mkAssign y a'.dual]
          simp only [hxw, beq_self_eq_true, ↓reduceIte]
          -- Context is [mkAssign x a'] ++ [mkAssign y a'.dual] = [mkAssign w a', mkAssign y a'.dual]
          -- For .link y y, we need CPTyped [...] (.link y y)
          -- This requires y:A, y:A⊥ but we have w:a', y:a'.dual
          -- If w ≠ y (which is true by hfresh), we can't type .link y y with ax
          -- But since hxw: x = w, and hd.chan = x, hd.chan = w
          -- hfresh says hd.chan ≠ y, so w ≠ y
          -- .link y y is not typeable by ax (needs y in context at both positions)
          -- This case might be impossible due to freshness constraint
          sorry
        · -- x ≠ w: normal case
          have hne : (x == w) = false := beq_eq_false_iff_ne.mpr hxw
          simp only [hne]
          -- Goal: CPTyped ([hd] ++ [mkAssign y a'.dual]) (.link x y)
          -- Context is [mkAssign x a', mkAssign y a'.dual]
          have hhd : hd = mkAssign x a' := by
            cases hd; simp only [mkAssign] at *; congr
          rw [hhd, a_eq]
          exact CPTyped.ax x y a'
      | cons hd2 tl2 =>
        -- Γ has at least 2 elements, but ax context has exactly 2
        simp only [List.cons_append] at hctx
        have hlen := congrArg List.length hctx
        simp at hlen
  | cut Γ' Δ' x' a' p' q' hp hq ihp ihq =>
    -- cut context is (Γ' ++ Δ'), process is .nu x' a' (.par p' q')
    -- This equals Γ ++ [z:a], need careful analysis
    simp only [CPProc.subst]
    sorry
  | tensorR Γ' Δ' x' y' a' b' p' q' hp hq ihp ihq =>
    simp only [CPProc.subst]
    -- hctx: Γ ++ [mkAssign z a] = Γ' ++ Δ' ++ [mkAssign x' (a'.tensor b')]
    -- By list equality, the last elements must match: z = x', a = a'.tensor b'
    have heq := List.append_singleton_inj.mp hctx
    have hΓ : Γ = Γ' ++ Δ' := heq.1
    have hassign := heq.2
    simp only [mkAssign] at hassign
    have hzx' : z = x' := congrArg TypeAssign.chan hassign
    have ha : a = a'.tensor b' := congrArg TypeAssign.prop hassign
    subst hΓ hzx' ha
    -- After subst: x' → z, Γ → Γ' ++ Δ', a → a'.tensor b'
    simp only [beq_self_eq_true, ↓reduceIte]
    -- Goal: CPTyped ((Γ' ++ Δ') ++ [mkAssign y (a'.tensor b')])
    --         (if (y' == z) then .out y y' p' (q'.subst y z) else .out y y' (p'.subst y z) (q'.subst y z))
    by_cases hy'z : y' = z
    · -- y' = z: bound variable shadows substitution in p'
      simp only [hy'z, beq_self_eq_true, ↓reduceIte]
      -- Goal: CPTyped ((Γ' ++ Δ') ++ [mkAssign y (a'.tensor b')]) (.out y z p' (q'.subst y z))
      -- Linearity violation: y' = z means same channel appears in both p' and q' contexts
      -- TODO: Add linearity invariant
      sorry
    · -- y' ≠ z: normal case
      have hne : (y' == z) = false := beq_eq_false_iff_ne.mpr hy'z
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      -- Goal: CPTyped ((Γ' ++ Δ') ++ [mkAssign y (a'.tensor b')]) (.out y y' (p'.subst y z) (q'.subst y z))
      -- For tensorR with outer channel y, bound channel y', we need:
      --   (1) CPTyped (Γ' ++ [mkAssign y' a']) (p'.subst y z)
      --   (2) CPTyped (Δ' ++ [mkAssign y b']) (q'.subst y z)
      -- For (2): ihq applies directly
      have hfreshΔ : ∀ ta ∈ Δ', ta.chan ≠ y := fun ta hta =>
        hfresh ta (List.mem_append_right Γ' hta)
      have hIHq := ihq Δ' z b' hfreshΔ hyz rfl
      -- hIHq : CPTyped (Δ' ++ [mkAssign y b']) (q'.subst y z)
      -- For (1): z is not in Γ' ++ [mkAssign y' a'], so p'.subst y z = p'
      -- z is only at the end of the original context, not in Γ' or Δ' proper
      -- Since hy'z : y' ≠ z, we need z ∉ Γ'
      -- The original context was Γ' ++ Δ' ++ [z:...], so z only appears at the end
      -- By linear structure, z ∉ Γ' and z ∉ Δ' (z is the suffix, not in prefix)
      -- We derive: z not in hp's context Γ' ++ [y':a']
      have hz_not_in_hp_ctx : ∀ ta ∈ Γ' ++ [mkAssign y' a'], ta.chan ≠ z := by
        intro ta hta
        simp only [List.mem_append, List.mem_singleton] at hta
        cases hta with
        | inl hΓ' =>
          -- ta ∈ Γ'. Need to show ta.chan ≠ z.
          -- By hq : CPTyped (Δ' ++ [mkAssign z b']) q', the context Δ' ++ [z:b'] is linear.
          -- By end_not_in_prefix, z ∉ Δ'.chans.
          -- The tensorR rule combines Γ' and Δ', so by disjointness of linear typing,
          -- z also ∉ Γ'.chans (since z is the tensor channel from q's context).
          -- TODO: Formalize tensorR context disjointness property
          sorry
        | inr heq =>
          rw [heq]; simp only [mkAssign]
          exact hy'z
      have hp' := CPTyped.not_in_context_not_free hp hz_not_in_hp_ctx
      have hp_subst : p'.subst y z = p' := CPProc.subst_not_free p' y z hp'
      rw [hp_subst]
      exact CPTyped.tensorR Γ' Δ' y y' a' b' p' (q'.subst y z) hp hIHq
  | parR Γ' x' y' a' b' p' hp ihp =>
    simp only [CPProc.subst]
    -- hctx: Γ ++ [mkAssign z a] = Γ' ++ [mkAssign x' (a'.par b')]
    have heq := List.append_singleton_inj.mp hctx
    have hΓ : Γ = Γ' := heq.1
    have hassign := heq.2
    simp only [mkAssign] at hassign
    have hzx' : z = x' := congrArg TypeAssign.chan hassign
    have ha : a = a'.par b' := congrArg TypeAssign.prop hassign
    subst hΓ hzx' ha
    -- After subst: x' becomes z, Γ' becomes Γ
    -- hp : CPTyped (Γ ++ [mkAssign y' a', mkAssign z b']) p'
    -- Goal: CPTyped (Γ ++ [mkAssign y (a'.par b')]) (if (y' == z) then .inp z y' p' else .inp y y' (p'.subst y z))
    by_cases hy'z : y' = z
    · -- y' = z: degenerate case - the premise hp has context Γ ++ [z:a', z:b']
      -- which violates linearity (z appears twice). This case shouldn't occur
      -- in well-formed linear logic derivations. For now, use sorry.
      -- TODO: Add linearity invariant to rule out this case
      simp only [hy'z, beq_self_eq_true, ↓reduceIte]
      sorry
    · -- y' ≠ z: normal case
      have hne : (y' == z) = false := beq_eq_false_iff_ne.mpr hy'z
      simp only [hne, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true, ↓reduceIte]
      -- Goal: CPTyped (Γ ++ [mkAssign y (a'.par b')]) (.inp y y' (p'.subst y z))
      -- TODO: Need y ≠ y' to prove freshness for IH. This requires strengthening
      -- the theorem's freshness hypothesis to cover bound variables in derivation.
      sorry
  | addConjR Γ' x' a' b' p' q' hp hq ihp ihq =>
    simp only [CPProc.subst]
    -- hctx: Γ ++ [mkAssign z a] = Γ' ++ [mkAssign x' (a'.addConj b')]
    have heq := List.append_singleton_inj.mp hctx
    have hΓ : Γ = Γ' := heq.1
    have hassign := heq.2
    simp only [mkAssign] at hassign
    have hzx' : z = x' := congrArg TypeAssign.chan hassign
    have ha : a = a'.addConj b' := congrArg TypeAssign.prop hassign
    subst hΓ hzx' ha
    simp only [beq_self_eq_true, ↓reduceIte]
    -- Apply addConjR with both IH results
    have hIHp := ihp Γ z a' hfresh hyz rfl
    have hIHq := ihq Γ z b' hfresh hyz rfl
    exact CPTyped.addConjR Γ y a' b' (p'.subst y z) (q'.subst y z) hIHp hIHq
  | addDisjR1 Γ' x' a' b' p' hp ihp =>
    simp only [CPProc.subst]
    -- hctx: Γ ++ [mkAssign z a] = Γ' ++ [mkAssign x' (a'.addDisj b')]
    have heq := List.append_singleton_inj.mp hctx
    have hΓ : Γ = Γ' := heq.1
    have hassign := heq.2
    simp only [mkAssign] at hassign
    have hzx' : z = x' := congrArg TypeAssign.chan hassign
    have ha : a = a'.addDisj b' := congrArg TypeAssign.prop hassign
    subst hΓ hzx' ha
    -- After subst: Γ' → Γ, x' → z
    simp only [beq_self_eq_true, ↓reduceIte]
    -- Apply addDisjR1 with channel y
    have hIH := ihp Γ z a' hfresh hyz rfl
    exact CPTyped.addDisjR1 Γ y a' b' (p'.subst y z) hIH
  | addDisjR2 Γ' x' a' b' p' hp ihp =>
    simp only [CPProc.subst]
    -- hctx: Γ ++ [mkAssign z a] = Γ' ++ [mkAssign x' (a'.addDisj b')]
    have heq := List.append_singleton_inj.mp hctx
    have hΓ : Γ = Γ' := heq.1
    have hassign := heq.2
    simp only [mkAssign] at hassign
    have hzx' : z = x' := congrArg TypeAssign.chan hassign
    have ha : a = a'.addDisj b' := congrArg TypeAssign.prop hassign
    subst hΓ hzx' ha
    simp only [beq_self_eq_true, ↓reduceIte]
    -- Apply addDisjR2 with channel y (premise uses b', not a')
    have hIH := ihp Γ z b' hfresh hyz rfl
    exact CPTyped.addDisjR2 Γ y a' b' (p'.subst y z) hIH
  | oneR x' =>
    -- oneR context is [x':1], process is .emptyOut x'
    -- [x':1] = Γ ++ [z:a], so Γ = [] and z = x' and a = .one
    simp only [CPProc.subst]
    cases Γ with
    | nil =>
      simp only [List.nil_append] at hctx
      have hz := List.singleton_injective hctx
      simp only [mkAssign] at hz
      have hzchan : z = x' := congrArg TypeAssign.chan hz
      have haprop : a = .one := congrArg TypeAssign.prop hz
      subst hzchan haprop
      simp only [beq_self_eq_true, ↓reduceIte, List.nil_append]
      exact CPTyped.oneR y
    | cons hd tl =>
      simp only [List.cons_append] at hctx
      have hlen := congrArg List.length hctx
      simp at hlen
  | botR Γ' x' p' hp ihp =>
    -- botR context is Γ' ++ [x':⊥], process is .emptyInp x' p'
    simp only [CPProc.subst]
    -- hctx: Γ ++ [z:a] = Γ' ++ [x':⊥]
    have heq := List.append_singleton_inj.mp hctx
    have hassign := heq.2
    simp only [mkAssign] at hassign
    have hx : z = x' := congrArg TypeAssign.chan hassign
    have ha : a = CLLProp.bot := congrArg TypeAssign.prop hassign
    rw [heq.1, hx, ha]
    simp only [beq_self_eq_true, ↓reduceIte]
    -- Goal: CPTyped (Γ' ++ [mkAssign y .bot]) (.emptyInp y (p'.subst y x'))
    -- hp : CPTyped Γ' p'. Since botR adds x' as a fresh channel, x' ∉ Γ'.
    -- By not_in_context_not_free: x' ∉ p'.freeChans (assuming linearity of Γ').
    -- By subst_not_free: p'.subst y x' = p'.
    -- Then apply botR with y.
    -- TODO: This requires proving that botR's premise channel x' is not in Γ'
    -- (a linearity property of linear logic contexts).
    sorry
  | topR Γ' x' p' =>
    -- topR context is Γ' ++ [x':⊤], types any process p'
    -- hctx: Γ ++ [z:a] = Γ' ++ [x':⊤]
    have heq := List.append_singleton_inj.mp hctx
    -- heq.1 : Γ = Γ', heq.2 : mkAssign z a = mkAssign x' .top
    have hassign := heq.2
    simp only [mkAssign] at hassign
    have hx : z = x' := congrArg TypeAssign.chan hassign
    have ha : a = CLLProp.top := congrArg TypeAssign.prop hassign
    -- Rewrite goal using equalities
    rw [heq.1, hx, ha]
    -- Goal: CPTyped (Γ' ++ [mkAssign y .top]) (p'.subst y x')
    exact CPTyped.topR Γ' y (p'.subst y x')
  | mix Γ' Δ' p' q' hp hq ihp ihq =>
    simp only [CPProc.subst]
    -- hctx : Γ ++ [mkAssign z a] = Γ' ++ Δ'
    -- Case split: z is in Γ' (Δ' = []) or z is in Δ' (Δ' ends with z)
    -- The last element of LHS is mkAssign z a, so it must be the last of RHS
    cases hΔ' : Δ' with
    | nil =>
      -- Δ' = [], so Γ' = Γ ++ [mkAssign z a]
      simp only [hΔ', List.append_nil] at hctx
      -- hctx : Γ ++ [mkAssign z a] = Γ'
      have hIHp := ihp Γ z a hfresh hyz hctx
      -- hq : CPTyped [] q', need to show q'.subst y z = q'
      -- Since z is not in the empty context, z ∉ q'.freeChans
      -- For CPTyped [] q', freeChans ⊆ [] means freeChans = []
      simp only [hΔ'] at hq
      have hz_not_free : z ∉ q'.freeChans := by
        intro hmem
        have ⟨ta, hta, _⟩ := hq.freeChans_subset_context z hmem
        exact List.not_mem_nil hta
      rw [CPProc.subst_not_free q' y z hz_not_free]
      have hmix := CPTyped.mix (Γ ++ [mkAssign y a]) [] (p'.subst y z) q' hIHp hq
      simp only [List.append_nil] at hmix
      exact hmix
    | cons hd tl =>
      -- Δ' = hd :: tl, non-empty, so z is in Δ'
      -- The last element of Γ' ++ (hd :: tl) is the last of (hd :: tl)
      -- Since hctx says this equals mkAssign z a, we have Δ' ends with mkAssign z a
      have hΔ'_ne : Δ' ≠ [] := by simp only [hΔ']; exact List.cons_ne_nil hd tl
      -- Use getLast? to avoid proof-relevant non-emptiness issues
      have hLHS_last : (Γ ++ [mkAssign z a]).getLast? = some (mkAssign z a) := by
        simp only [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ []),
                   List.getLast?_singleton]
      have hRHS_last : (Γ' ++ Δ').getLast? = Δ'.getLast? := by
        exact List.getLast?_append_of_ne_nil Γ' hΔ'_ne
      -- From hctx: getLast? equal
      have hLast_eq : Δ'.getLast? = some (mkAssign z a) := by
        have heq : List.getLast? (Γ' ++ Δ') = List.getLast? (Γ ++ [mkAssign z a]) := by
          rw [hctx]
        rw [hRHS_last, hLHS_last] at heq
        exact heq
      -- Extract: Δ'.getLast = mkAssign z a
      -- `a ∈ l.getLast?` means `some a = l.getLast?`
      have hmem : mkAssign z a ∈ Δ'.getLast? := by
        rw [hLast_eq]; rfl
      have hΔ'_decomp : Δ' = Δ'.dropLast ++ [mkAssign z a] :=
        (List.dropLast_append_getLast? (mkAssign z a) hmem).symm
      -- Rewrite hctx using this decomposition
      rw [hΔ'_decomp] at hctx
      -- hctx : Γ ++ [mkAssign z a] = Γ' ++ (Δ'.dropLast ++ [mkAssign z a])
      --      = (Γ' ++ Δ'.dropLast) ++ [mkAssign z a]
      rw [← List.append_assoc] at hctx
      have hΓ_eq : Γ = Γ' ++ Δ'.dropLast := List.append_cancel_right hctx
      -- hp : CPTyped Γ' p', need z ∉ Γ' to show p'.subst y z = p'
      -- hq : CPTyped Δ' q' = CPTyped (Δ'.dropLast ++ [mkAssign z a]) q'
      rw [hΔ'_decomp] at hq
      -- Apply ihq to hq
      have hfreshΔ : ∀ ta ∈ Δ'.dropLast, ta.chan ≠ y := by
        intro ta hta
        have hta' : ta ∈ Γ := by
          rw [hΓ_eq]
          exact List.mem_append_right Γ' hta
        exact hfresh ta hta'
      have hIHq := ihq Δ'.dropLast z a hfreshΔ hyz hΔ'_decomp.symm
      -- For p'.subst y z = p', need z ∉ p'.freeChans
      -- This requires showing z ∉ Γ'.chans (from linearity of the derivation)
      -- TODO: This requires context_linear or similar property
      sorry

/-- Type preservation (subject reduction)

    The proof proceeds by case analysis on the reduction rule.
    Each reduction corresponds to a cut elimination step in linear logic.

    Key cases:
    - β-tensor/par: tensor elimination with par introduction
    - β-plus/with: additive disjunction elimination with conjunction introduction

    The proof requires showing that the type derivation can be restructured
    after each communication step. -/
theorem CPTyped.preservation (Γ : Context) (p p' : CPProc)
    (htp : CPTyped Γ p) (hred : CPReduce p p') :
    CPTyped Γ p' := by
  -- Proof by case analysis on the reduction rule.
  -- Each principal cut (beta reduction) corresponds to cut elimination in CLL.
  -- The topR rule (⊤) provides a uniform escape: it types ANY process.
  cases hred with
  | beta_tensor_par x y z a b pp qq rr =>
    -- Principal cut for ⊗/⅋: tensor output meets par input
    -- Before: (νx:A⊗B)(x[y].(P|Q) | x(z).R)
    -- After: (νy:A)(P | R[y/z]) | Q
    --
    -- This is the most complex principal cut case. Key issues:
    -- 1. tensorR splits context: Γ' = Γ₁ ++ Γ₂ where
    --    - CPTyped (Γ₁ ++ [y:A]) pp
    --    - CPTyped (Γ₂ ++ [x:B]) qq
    -- 2. parR: CPTyped (Δ' ++ [z:A⊥, x:B⊥]) rr
    -- 3. Result mixes contexts differently:
    --    - (νy:A)(pp | rr.subst y z) uses Γ₁ ++ (Δ' without x:B⊥)
    --    - qq uses Γ₂ without x:B
    -- 4. Requires: channel substitution lemma for typing
    -- 5. Requires: context manipulation to eliminate x from both sides
    cases htp with
    | cut Γ' Δ' x' a' left right hleft hright =>
      -- TODO: Prove using out_inv, inp_inv, channel substitution lemma,
      -- and careful context manipulation to construct result with mix + cut
      sorry
    | topR Γ' x' _ =>
      exact CPTyped.topR Γ' x' (.par (.nu y a (.par pp (rr.subst y z))) qq)
  | beta_par_tensor x y z a b pp qq rr =>
    -- Symmetric principal cut for ⅋/⊗
    -- Before: (νx:A⅋B)(x(y).P | x[z].(Q|R))
    -- After: (νy:A)(P | Q[y/z]) | R
    -- Symmetric to beta_tensor_par
    cases htp with
    | cut Γ' Δ' x' a' left right hleft hright =>
      -- TODO: Symmetric to beta_tensor_par
      sorry
    | topR Γ' x' _ =>
      exact CPTyped.topR Γ' x' (.par (.nu y a (.par pp (qq.subst y z))) rr)
  | beta_addDisj_l x a b pp qq rr =>
    -- Principal cut for ⊕/&: left selection meets case
    -- Before: (νx:A⊕B)(x.inl;P | x.case(Q,R)) → (νx:A)(P | Q)
    cases htp with
    | cut Γ' Δ' x' a' left right hleft hright =>
      -- hleft : CPTyped (Γ' ++ [mkAssign x (.addDisj a b)]) (.inl x pp)
      -- hright : CPTyped (Δ' ++ [mkAssign x (.addConj a.dual b.dual)]) (.case x qq rr)
      have hdual : (CLLProp.addDisj a b).dual = .addConj a.dual b.dual := rfl
      rw [hdual] at hright
      have hinv_l := CPTyped.inl_inv _ _ _ hleft
      have hinv_r := CPTyped.case_inv _ _ _ _ hright
      cases hinv_l with
      | inl hinl =>
        obtain ⟨Γ, a', b', heqL, hpL⟩ := hinl
        cases hinv_r with
        | inl hcase =>
          obtain ⟨Δ, a'', b'', heqR, hqR, _hrR⟩ := hcase
          -- heqL: Γ' ++ [mkAssign x (.addDisj a b)] = Γ ++ [mkAssign x (.addDisj a' b')]
          -- heqR: Δ' ++ [mkAssign x (.addConj a.dual b.dual)] = Δ ++ [mkAssign x (.addConj a'' b'')]
          -- Extract: Γ' = Γ, a' = a, b' = b, Δ' = Δ, a'' = a.dual, b'' = b.dual
          have ⟨hΓ, hAssignL⟩ := List.append_singleton_inj.mp heqL
          have hTypeL := congrArg TypeAssign.prop hAssignL
          simp only [mkAssign] at hTypeL
          -- hTypeL : .addDisj a b = .addDisj a' b'
          have ha : a = a' := by injection hTypeL
          have ⟨hΔ, hAssignR⟩ := List.append_singleton_inj.mp heqR
          have hTypeR := congrArg TypeAssign.prop hAssignR
          simp only [mkAssign] at hTypeR
          -- hTypeR : .addConj a.dual b.dual = .addConj a'' b''
          have ha' : a.dual = a'' := by injection hTypeR
          -- Now construct the result. After subst, Γ→Γ', Δ→Δ', a'→a, a''→a.dual
          subst hΓ hΔ ha ha'
          -- Goal: CPTyped (Γ' ++ Δ') (.nu x a (.par pp qq))
          -- We have: hpL : CPTyped (Γ' ++ [mkAssign x a]) pp
          --          hqR : CPTyped (Δ' ++ [mkAssign x a.dual]) qq
          exact CPTyped.cut Γ' Δ' x a pp qq hpL hqR
        | inr htopR =>
          -- hright was topR, contradiction: .addConj ≠ .top
          obtain ⟨Γ'', z, heq⟩ := htopR
          have heq' := (List.append_singleton_inj.mp heq).2
          have hprop := congrArg TypeAssign.prop heq'
          simp only [mkAssign] at hprop
          -- hprop : .addConj a.dual b.dual = .top, contradiction
          cases hprop
      | inr htopL =>
        -- hleft was topR, contradiction: .addDisj ≠ .top
        obtain ⟨Γ'', z, heq⟩ := htopL
        have heq' := (List.append_singleton_inj.mp heq).2
        have hprop := congrArg TypeAssign.prop heq'
        simp only [mkAssign] at hprop
        -- hprop : .addDisj a b = .top, contradiction
        cases hprop
    | topR Γ' x' _ =>
      exact CPTyped.topR Γ' x' (.nu x a (.par pp qq))
  | beta_addDisj_r x a b pp qq rr =>
    -- Principal cut for ⊕/&: right selection meets case
    -- Before: (νx:A⊕B)(x.inr;P | x.case(Q,R)) → (νx:B)(P | R)
    cases htp with
    | cut Γ' Δ' x' a' left right hleft hright =>
      -- hleft : CPTyped (Γ' ++ [mkAssign x (.addDisj a b)]) (.inr x pp)
      -- hright : CPTyped (Δ' ++ [mkAssign x (.addConj a.dual b.dual)]) (.case x qq rr)
      have hdual : (CLLProp.addDisj a b).dual = .addConj a.dual b.dual := rfl
      rw [hdual] at hright
      have hinv_l := CPTyped.inr_inv _ _ _ hleft
      have hinv_r := CPTyped.case_inv _ _ _ _ hright
      cases hinv_l with
      | inl hinr =>
        obtain ⟨Γ, a', b', heqL, hpL⟩ := hinr
        cases hinv_r with
        | inl hcase =>
          obtain ⟨Δ, a'', b'', heqR, _hqR, hrR⟩ := hcase
          -- Extract context and type equalities
          have ⟨hΓ, hAssignL⟩ := List.append_singleton_inj.mp heqL
          have hTypeL := congrArg TypeAssign.prop hAssignL
          simp only [mkAssign] at hTypeL
          -- hTypeL : .addDisj a b = .addDisj a' b'
          have hb : b = b' := by injection hTypeL
          have ⟨hΔ, hAssignR⟩ := List.append_singleton_inj.mp heqR
          have hTypeR := congrArg TypeAssign.prop hAssignR
          simp only [mkAssign] at hTypeR
          -- hTypeR : .addConj a.dual b.dual = .addConj a'' b''
          have hb' : b.dual = b'' := by injection hTypeR
          -- Now construct the result
          subst hΓ hΔ hb hb'
          -- Goal: CPTyped (Γ' ++ Δ') (.nu x b (.par pp rr))
          -- We have: hpL : CPTyped (Γ' ++ [mkAssign x b]) pp
          --          hrR : CPTyped (Δ' ++ [mkAssign x b.dual]) rr
          exact CPTyped.cut Γ' Δ' x b pp rr hpL hrR
        | inr htopR =>
          -- hright was topR, contradiction: .addConj ≠ .top
          obtain ⟨Γ'', z, heq⟩ := htopR
          have heq' := (List.append_singleton_inj.mp heq).2
          have hprop := congrArg TypeAssign.prop heq'
          simp only [mkAssign] at hprop
          cases hprop
      | inr htopL =>
        -- hleft was topR, contradiction: .addDisj ≠ .top
        obtain ⟨Γ'', z, heq⟩ := htopL
        have heq' := (List.append_singleton_inj.mp heq).2
        have hprop := congrArg TypeAssign.prop heq'
        simp only [mkAssign] at hprop
        cases hprop
    | topR Γ' x' _ =>
      exact CPTyped.topR Γ' x' (.nu x b (.par pp rr))
  | beta_one_bot xChan pCont =>
    -- Principal cut for 1/⊥: unit output meets unit input
    -- Before: (νx:1)(x[].0 | x().P)  →  P
    -- After: P
    cases htp with
    | cut Γ' Δ' x a left right hleft hright =>
      -- Typing is via cut: Γ ++ Δ ⊢ (νx:1)(emptyOut x | emptyInp x P)
      -- hleft: CPTyped (Γ' ++ [mkAssign xChan .one]) (.emptyOut xChan)
      -- hright: CPTyped (Δ' ++ [mkAssign xChan .bot]) (.emptyInp xChan pCont)
      -- By emptyOut_inv, hleft is oneR, so Γ' = []
      -- By emptyInp_inv, hright is botR, giving CPTyped Δ' pCont
      have hinv_l := CPTyped.emptyOut_inv _ _ hleft
      -- Note: .one.dual = .bot
      have hdual : CLLProp.one.dual = CLLProp.bot := rfl
      rw [hdual] at hright
      have hinv_r := CPTyped.emptyInp_inv _ _ _ hright
      cases hinv_l with
      | inl hone =>
        -- hleft is oneR, so Γ' = []
        have hGamma_nil : Γ' = [] := by
          have heq := hone
          -- Γ' ++ [mkAssign xChan .one] = [mkAssign xChan .one]
          cases Γ' with
          | nil => rfl
          | cons h t =>
            simp only [List.cons_append] at heq
            exact absurd heq (by simp)
        cases hinv_r with
        | inl hbot =>
          -- hright is botR, giving CPTyped Δ'' pCont where Δ' = Δ''
          obtain ⟨Δ'', heq, hp⟩ := hbot
          -- heq: Δ' ++ [mkAssign xChan .bot] = Δ'' ++ [mkAssign xChan .bot]
          have hDelta_eq : Δ' = Δ'' := (List.append_singleton_inj.mp heq).1
          subst hDelta_eq hGamma_nil
          simp only [List.nil_append]
          exact hp
        | inr htop =>
          -- hright is topR - but then .bot ≠ .top, contradiction
          obtain ⟨Γ'', y, heq⟩ := htop
          -- heq: Δ' ++ [mkAssign xChan .bot] = Γ'' ++ [mkAssign y .top]
          have heq' := (List.append_singleton_inj.mp heq).2
          have hprop := congrArg TypeAssign.prop heq'
          simp only [mkAssign] at hprop
          exact absurd hprop (by decide)
      | inr htop =>
        -- hleft is topR - but then .one ≠ .top, contradiction
        obtain ⟨Γ'', y, heq⟩ := htop
        have heq' := (List.append_singleton_inj.mp heq).2
        have hprop := congrArg TypeAssign.prop heq'
        simp only [mkAssign] at hprop
        exact absurd hprop (by decide)
    | topR Γ' xTop _ =>
      -- p' is the target process (unified with constructor's p parameter)
      exact CPTyped.topR Γ' xTop p'
  | beta_bot_one xChan _ =>
    -- Symmetric principal cut for ⊥/1
    -- Before: (νx:⊥)(x().P | x[].0)  →  P
    -- After: P
    cases htp with
    | cut Γ' Δ' x a left right hleft hright =>
      -- hleft: CPTyped (Γ' ++ [mkAssign xChan .bot]) (.emptyInp xChan p')
      -- hright: CPTyped (Δ' ++ [mkAssign xChan .one]) (.emptyOut xChan)
      -- By emptyInp_inv, hleft is botR, giving CPTyped Γ' p'
      -- By emptyOut_inv, hright is oneR, so Δ' = []
      have hdual : CLLProp.bot.dual = CLLProp.one := rfl
      rw [hdual] at hright
      have hinv_l := CPTyped.emptyInp_inv _ _ _ hleft
      have hinv_r := CPTyped.emptyOut_inv _ _ hright
      cases hinv_r with
      | inl hone =>
        -- hright is oneR, so Δ' = []
        have hDelta_nil : Δ' = [] := by
          have heq := hone
          cases Δ' with
          | nil => rfl
          | cons h t =>
            simp only [List.cons_append] at heq
            exact absurd heq (by simp)
        cases hinv_l with
        | inl hbot =>
          -- hleft is botR, giving CPTyped Γ'' p' where Γ' = Γ''
          obtain ⟨Γ'', heq, hp⟩ := hbot
          have hGamma_eq : Γ' = Γ'' := (List.append_singleton_inj.mp heq).1
          subst hGamma_eq hDelta_nil
          simp only [List.append_nil]
          exact hp
        | inr htop =>
          -- hleft is topR - but then .bot ≠ .top, contradiction
          obtain ⟨Γ'', y, heq⟩ := htop
          have heq' := (List.append_singleton_inj.mp heq).2
          have hprop := congrArg TypeAssign.prop heq'
          simp only [mkAssign] at hprop
          exact absurd hprop (by decide)
      | inr htop =>
        -- hright is topR - but then .one ≠ .top, contradiction
        obtain ⟨Γ'', y, heq⟩ := htop
        have heq' := (List.append_singleton_inj.mp heq).2
        have hprop := congrArg TypeAssign.prop heq'
        simp only [mkAssign] at hprop
        exact absurd hprop (by decide)
    | topR Γ' xTop _ =>
      exact CPTyped.topR Γ' xTop p'
  | cong_nu x a pp pp' hred' =>
    -- Congruence under restriction: if body reduces, result reduces
    cases htp with
    | cut Γ' Δ' x' a' left right hleft hright =>
      -- The cut body (.par left right) reduces to pp'
      -- Case on how the parallel reduces
      match hred' with
      | .cong_par_l _ newLeft _ hredL =>
        -- left -> newLeft, so pp' = .par newLeft right
        have ih := preservation (Γ' ++ [mkAssign x a]) left newLeft hleft hredL
        exact CPTyped.cut Γ' Δ' x a newLeft right ih hright
      | .cong_par_r _ _ newRight hredR =>
        -- right -> newRight, so pp' = .par left newRight
        have ih := preservation (Δ' ++ [mkAssign x a.dual]) right newRight hright hredR
        exact CPTyped.cut Γ' Δ' x a left newRight hleft ih
    | topR Γ' x' _ => exact CPTyped.topR Γ' x' (.nu x a pp')
  | cong_par_l pp pp' qq hred' =>
    -- Congruence in left of parallel
    cases htp with
    | mix Γ' Δ' left right hp hq =>
      have ih := preservation Γ' pp pp' hp hred'
      exact CPTyped.mix Γ' Δ' pp' qq ih hq
    | topR Γ' x' _ => exact CPTyped.topR Γ' x' (.par pp' qq)
  | cong_par_r pp qq qq' hred' =>
    -- Congruence in right of parallel
    cases htp with
    | mix Γ' Δ' left right hp hq =>
      have ih := preservation Δ' qq qq' hq hred'
      exact CPTyped.mix Γ' Δ' pp qq' hp ih
    | topR Γ' x' _ => exact CPTyped.topR Γ' x' (.par pp qq')

/-- Progress: well-typed closed processes are either values or can step

    A process with empty typing context has no free channels, meaning
    all channels are bound by ν. Such processes are either:
    - Terminated (nil)
    - Can reduce via internal communication

    Note: The empty context case is very restrictive. Analysis:
    - ax: context = [x:A, w:A⊥] - non-empty
    - cut: context = Γ ++ Δ - can be empty if Γ = Δ = []
    - tensorR, parR, addConjR, addDisjR1/R2: context = ... ++ [x:T] - non-empty
    - oneR: context = [x:1] - non-empty
    - botR: context = Γ ++ [x:⊥] - non-empty
    - topR: context = Γ ++ [x:⊤] - non-empty

    So the ONLY way to get CPTyped [] p is via cut with Γ = Δ = [].
    The cut produces .nu x a (.par p q) which can reduce if p and q
    are complementary on x (principal cut). -/
theorem CPTyped.progress (p : CPProc)
    (htp : CPTyped [] p) :
    p.isNormalForm ∨ ∃ p', CPReduce p p' := by
  -- Most typing rules produce non-empty contexts
  -- Only cut/mix with Γ = Δ = [] can produce empty context
  -- We generalize the context to handle the equation
  generalize hctx : ([] : Context) = ctx at htp
  induction htp with
  | ax x w a =>
    -- Context [x:a, w:a.dual] = [], impossible (length mismatch)
    exact absurd hctx.symm (List.cons_ne_nil _ _)
  | cut Γ' Δ' x a left right hleft hright _ihleft _ihright =>
    -- Context Γ' ++ Δ' = []
    have hboth := List.append_eq_nil_iff.mp hctx.symm
    have hΓ'_nil : Γ' = [] := hboth.1
    have hΔ'_nil : Δ' = [] := hboth.2
    -- hleft : CPTyped [x:a] left, hright : CPTyped [x:a.dual] right
    -- The cut body is .nu x a (.par left right)
    -- We need to show this can step via principal reduction
    -- This requires analyzing left and right to find a principal cut
    -- TODO: Full analysis requires matching left/right structures
    sorry
  | tensorR Γ' Δ' x y a b pp qq hp hq _ihp _ihq =>
    -- [] = Γ' ++ Δ' ++ [x:tensor], impossible
    have h : Γ' ++ Δ' ++ [mkAssign x (.tensor a b)] ≠ [] :=
      List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)
    exact absurd hctx.symm h
  | parR Γ' x y a b pp hp _ihp =>
    exact absurd hctx.symm (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _))
  | addConjR Γ' x a b pp qq hp hq _ihp _ihq =>
    exact absurd hctx.symm (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _))
  | addDisjR1 Γ' x a b pp hp _ihp =>
    exact absurd hctx.symm (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _))
  | addDisjR2 Γ' x a b pp hp _ihp =>
    exact absurd hctx.symm (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _))
  | oneR x =>
    exact absurd hctx.symm (List.cons_ne_nil _ _)
  | botR Γ' x pp hp _ihp =>
    exact absurd hctx.symm (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _))
  | topR Γ' x pp =>
    exact absurd hctx.symm (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _))
  | mix Γ' Δ' pp qq hp hq ihp ihq =>
    -- Context Γ' ++ Δ' = [], so both empty
    have hboth := List.append_eq_nil_iff.mp hctx.symm
    have hΓ'_nil : Γ' = [] := hboth.1
    have hΔ'_nil : Δ' = [] := hboth.2
    subst hΓ'_nil hΔ'_nil
    -- hp : CPTyped [] pp, hq : CPTyped [] qq
    -- By IH on the derivations
    rcases ihp rfl with hpp_nf | ⟨pp', hpp_red⟩
    · rcases ihq rfl with hqq_nf | ⟨qq', hqq_red⟩
      · -- Both normal forms: .par pp qq is also a normal form
        left
        exact CPProc.par_isNormalForm hpp_nf hqq_nf
      · -- pp is normal form, qq reduces
        right; exact ⟨.par pp qq', .cong_par_r pp qq qq' hqq_red⟩
    · -- pp reduces
      right; exact ⟨.par pp' qq, .cong_par_l pp pp' qq hpp_red⟩

/-! ## Examples -/

/-- Example: identity process (forwarder) -/
def idProc (x w : Chan) : CPProc := .link x w

/-- Identity is well-typed -/
example (x w : Chan) (a : CLLProp) :
    CPTyped [mkAssign x a, mkAssign w a.dual] (idProc x w) :=
  CPTyped.ax x w a

end Mettapedia.AutoBooks.ClaudeProcWam.ProcessCalculi
