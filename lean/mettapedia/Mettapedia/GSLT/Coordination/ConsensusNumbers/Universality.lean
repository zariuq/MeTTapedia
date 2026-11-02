import Mettapedia.GSLT.Coordination.ConsensusNumbers.Universal
import Mettapedia.GSLT.Coordination.ConsensusNumbers.StepSpace

/-!
# Universality from consensus objects, and from steps

The universal construction (`Universal`) runs over any base object that offers a `Board`: a
consensus slot for each place of the log and announcements for each process. Two bases offer one.

## Consensus objects and registers

A **consensus object** (`consensusObject`, Herlihy's): the first value proposed stays, and every
proposal answers it. Example: proposals `3` then `5` both answer `3`.

* `consensusBase n Op`: one consensus object per place of the log, beside one register per process
  holding its latest announcement (the operation and its tag).
* **Herlihy's universality theorem** (`consensus_universal`): from consensus objects and registers,
  every object given by a sequential specification, started at any state, has a wait-free,
  linearizable implementation for any number `n` of processes.

## A space with steps

A space's atoms can hold the log and the announcements: the atom `slot k e` says place `k` holds
`e`, the atom `ann i t op` says process `i` announced `op` with tag `t` (`Code`, written into atoms by
an injective `enc`).

* A claim of place `k` is one step: make `slot k e`, provided no `slot k` atom is present. Taking
  nothing, it fires exactly when the place is undecided.
* An announcement is one step that only makes its atom; reading and learning are `match` queries.
* **Steps are universal** (`steps_universal`): over a space whose atoms can encode the target's
  operations, every object has a wait-free, linearizable implementation by steps, for any number of
  processes. Even steps that take nothing suffice (`noTakeSteps_universal`): an absence-guarded
  addition is enough.

## Controls

* `Controls.consensus_first_stays`: the second proposal to a consensus object answers the first
  (positive).
* `Controls.consensus_not_register`: a consensus object is not a register: a second write does not
  overwrite (negative).
* `Controls.claim_blocked`: a claim of a decided place does not fire (positive), a claim of an
  undecided place does (`Controls.claim_fires`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Coordination.ConsensusNumbers

/-- **A consensus object**: the first value proposed stays, and every proposal answers it. -/
def consensusObject (V : Type) : DetObject where
  State := Option V
  Op := V
  Res := V
  apply s v := match s with
    | none => (some v, v)
    | some w => (some w, w)

namespace Universal

/-! ## Consensus objects and registers -/

section Consensus

variable {n : ℕ} {Op : Type}

/-- An operation on the consensus objects and registers: a proposal to the consensus object of
place `k`, or an operation on the registers. -/
inductive BaseOp (n : ℕ) (Op : Type) where
  | propose (k : ℕ) (e : Entry n Op)
  | reg (o : RegOp (Fin n) (Option (Op × ℕ)))

/-- An answer: what a consensus object decided, or a register's answer. -/
inductive BaseRes (n : ℕ) (Op : Type) where
  | decided (e : Entry n Op)
  | reg (r : Option (Option (Op × ℕ)))

/-- **One consensus object per place of the log, beside one register per process** for its latest
announcement. Each operation acts on its own component exactly as that object does: a proposal by
`consensusObject`, a register operation by `registers`. -/
def consensusBase (n : ℕ) (Op : Type) : DetObject where
  State := (ℕ → Option (Entry n Op)) × (Fin n → Option (Op × ℕ))
  Op := BaseOp n Op
  Res := BaseRes n Op
  apply s op := match op with
    | .propose k e =>
        (((Function.update s.1 k ((consensusObject (Entry n Op)).apply (s.1 k) e).1, s.2) :
            (ℕ → Option (Entry n Op)) × (Fin n → Option (Op × ℕ))),
          BaseRes.decided ((consensusObject (Entry n Op)).apply (s.1 k) e).2)
    | .reg o =>
        (((s.1, ((registers (Fin n) (Option (Op × ℕ))).apply s.2 o).1) :
            (ℕ → Option (Entry n Op)) × (Fin n → Option (Op × ℕ))),
          BaseRes.reg ((registers (Fin n) (Option (Op × ℕ))).apply s.2 o).2)

/-- The announcement with tag `t` in a register holding `(op, t')`. -/
def annOf : Option (Op × ℕ) → ℕ → Option Op
  | some (op, t'), t => if t' = t then some op else none
  | none, _ => none

theorem consensus_apply_fst (s : Option (Entry n Op)) (e : Entry n Op) :
    ((consensusObject (Entry n Op)).apply s e).1 = some (s.getD e) := by
  cases s <;> rfl

/-- **The board of consensus objects and registers.** -/
def consensusBoard (n : ℕ) (Op : Type) : Board (consensusBase n Op) n Op where
  slot s k := s.1 k
  ann s i t := annOf (s.2 i) t
  init := (fun _ => none, fun _ => none)
  claim k e := .propose k e
  learn k e := .propose k e
  learned _ r e := match r with
    | .decided w => w
    | .reg _ => e
  write i t op := .reg (.write i (some (op, t)))
  read i _ := .reg (.read i)
  readOut _ t r := match r with
    | .reg (some v) => annOf v t
    | _ => none
  init_slot _ := rfl
  init_ann _ _ := rfl
  claim_slot s k e := by
    show Function.update s.1 k ((consensusObject (Entry n Op)).apply (s.1 k) e).1 = _
    rw [consensus_apply_fst]
  claim_ann s k e := rfl
  learn_slot s k e w h := by
    show Function.update s.1 k ((consensusObject (Entry n Op)).apply (s.1 k) e).1 = s.1
    rw [consensus_apply_fst, h, Option.getD_some, ← h, Function.update_eq_self]
  learn_ann s k e w _ := rfl
  learn_out s k e w h := by
    show ((consensusObject (Entry n Op)).apply (s.1 k) e).2 = w
    rw [h]; rfl
  write_slot s i t op := rfl
  write_self s i t op _ := by
    show annOf (Function.update s.2 i (some (op, t)) i) t = some op
    simp [annOf]
  write_above s i t op _ t' lt := by
    show annOf (Function.update s.2 i (some (op, t)) i) t' = none
    simp [annOf]; omega
  write_other s i t op j ne := by
    funext t'
    show annOf (Function.update s.2 i (some (op, t)) j) t' = annOf (s.2 j) t'
    rw [Function.update_of_ne ne]
  read_slot s i t := rfl
  read_ann s i t := rfl
  read_out s i t := rfl

/-- **Herlihy's universality theorem.** From consensus objects and registers, every object given by
a sequential specification, started at any state, has a wait-free, linearizable implementation for
any number of processes. -/
theorem consensus_universal (Y : DetObject) (s₀ : Y.State) (n : ℕ) :
    Implements (consensusBase n Y.Op).toObject Y s₀ n :=
  ⟨universal (consensusBoard n Y.Op) s₀, universal_linearizable _ _, universal_waitFree _ _⟩

end Consensus

/-! ## A space with steps -/

section Steps

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Equivalence (Rule Avoids
  avoids_none)

/-- What an atom of the board says: place `k` holds `e`, or process `i` announced `op` with tag
`t`. -/
inductive Code (n : ℕ) (Op : Type) where
  | slot (k : ℕ) (e : Entry n Op)
  | ann (i : Fin n) (t : ℕ) (op : Op)
  deriving DecidableEq

variable {A : Type} [DecidableEq A] {n : ℕ} {Op : Type} (enc : Code n Op → A)

open Classical in
/-- Is the atom one of place `k`? -/
noncomputable def isSlotAt (k : ℕ) (a : A) : Bool := decide (∃ e, enc (.slot k e) = a)

open Classical in
/-- Is the atom an announcement of process `i` with tag `t`? -/
noncomputable def isAnnAt (i : Fin n) (t : ℕ) (a : A) : Bool := decide (∃ op, enc (.ann i t op) = a)

open Classical in
/-- The entry of place `k` found among the atoms `m`, if any. -/
noncomputable def slotIn (k : ℕ) (m : Multiset A) : Option (Entry n Op) :=
  if h : ∃ e, enc (.slot k e) ∈ m then some h.choose else none

open Classical in
/-- The announcement of process `i` with tag `t` found among the atoms `m`, if any. -/
noncomputable def annIn (i : Fin n) (t : ℕ) (m : Multiset A) : Option Op :=
  if h : ∃ op, enc (.ann i t op) ∈ m then some h.choose else none

/-- The step that decides place `k` for `e`: make its atom, provided no atom of place `k` is
present. -/
noncomputable def claimRule (k : ℕ) (e : Entry n Op) : Rule A :=
  ⟨0, 0, {enc (.slot k e)}, isSlotAt enc k⟩

/-- The step that announces: make the announcement's atom. -/
def writeRule (i : Fin n) (t : ℕ) (op : Op) : Rule A := ⟨0, 0, {enc (.ann i t op)}, fun _ => false⟩

variable {enc}

omit [DecidableEq A] in
theorem filter_add_singleton_false {p : A → Bool} {M : Multiset A} {x : A} (h : p x = false) :
    (M + {x}).filter (fun b => p b = true) = M.filter (fun b => p b = true) := by
  simp [Multiset.filter_add, Multiset.filter_singleton, h]

omit [DecidableEq A] in
theorem slotIn_filter_add_other {k k' : ℕ} {e : Entry n Op} (ne : k' ≠ k) (M : Multiset A)
    (inj : Function.Injective enc) :
    slotIn enc k' ((M + {enc (.slot k e)}).filter fun b => isSlotAt enc k' b = true) =
      slotIn enc k' (M.filter fun b => isSlotAt enc k' b = true) := by
  rw [filter_add_singleton_false]
  simp only [isSlotAt, decide_eq_false_iff_not, not_exists]
  intro e' h
  have := inj h
  simp only [Code.slot.injEq] at this
  exact ne this.1

omit [DecidableEq A] in
theorem mem_filter_slot {k : ℕ} {e : Entry n Op} {M : Multiset A} :
    enc (.slot k e) ∈ M.filter (fun b => isSlotAt enc k b = true) ↔ enc (.slot k e) ∈ M := by
  rw [Multiset.mem_filter]
  exact and_iff_left (by simp only [isSlotAt, decide_eq_true_eq]; exact ⟨e, rfl⟩)

omit [DecidableEq A] in
theorem mem_filter_ann {i : Fin n} {t : ℕ} {op : Op} {M : Multiset A} :
    enc (.ann i t op) ∈ M.filter (fun b => isAnnAt enc i t b = true) ↔ enc (.ann i t op) ∈ M := by
  rw [Multiset.mem_filter]
  exact and_iff_left (by simp only [isAnnAt, decide_eq_true_eq]; exact ⟨op, rfl⟩)

omit [DecidableEq A] in
theorem slotIn_singleton (inj : Function.Injective enc) (k : ℕ) (e : Entry n Op) :
    slotIn enc k ({enc (.slot k e)} : Multiset A) = some e := by
  have ex : ∃ e', enc (.slot k e') ∈ ({enc (.slot k e)} : Multiset A) := ⟨e, by simp⟩
  unfold slotIn
  rw [dif_pos ex]
  have spec := inj (Multiset.mem_singleton.mp ex.choose_spec)
  rw [Code.slot.injEq] at spec
  rw [spec.2]

omit [DecidableEq A] in
theorem annIn_singleton (inj : Function.Injective enc) (i : Fin n) (t : ℕ) (op : Op) :
    annIn enc i t ({enc (.ann i t op)} : Multiset A) = some op := by
  have ex : ∃ op', enc (.ann i t op') ∈ ({enc (.ann i t op)} : Multiset A) := ⟨op, by simp⟩
  unfold annIn
  rw [dif_pos ex]
  have spec := inj (Multiset.mem_singleton.mp ex.choose_spec)
  rw [Code.ann.injEq] at spec
  rw [spec.2.2]

theorem claimRule_enabled_iff (k : ℕ) (e : Entry n Op) (M : Multiset A) :
    (claimRule enc k e).Enabled M ↔ ¬ ∃ e', enc (.slot k e') ∈ M := by
  simp only [Rule.Enabled, claimRule, Rule.redex, add_zero, zero_le, true_and, tsub_zero, Avoids,
    isSlotAt, decide_eq_false_iff_not, not_exists]
  constructor
  · intro h e' mem; exact h _ mem e' rfl
  · intro h x mem e' hx; subst hx; exact h e' mem

omit [DecidableEq A] in
theorem slotIn_eq_none_iff (k : ℕ) (M : Multiset A) :
    slotIn enc k (M.filter fun b => isSlotAt enc k b = true) = none ↔
      ¬ ∃ e', enc (.slot k e') ∈ M := by
  unfold slotIn
  split_ifs with h
  · simp only [false_iff, not_not]
    obtain ⟨e', mem⟩ := h
    exact ⟨e', mem_filter_slot.mp mem⟩
  · simp only [true_iff]
    rintro ⟨e', mem⟩
    exact h ⟨e', mem_filter_slot.mpr mem⟩

theorem step_apply_pos {allowed : Rule A → Prop} {ρ : Rule A} (ok : allowed ρ) {M : Multiset A}
    (en : ρ.Enabled M) : (ruleSpace A allowed).apply M (.step ρ ok) = (ρ.result M, .fired true) :=
  if_pos en

theorem step_apply_neg {allowed : Rule A → Prop} {ρ : Rule A} (ok : allowed ρ) {M : Multiset A}
    (en : ¬ ρ.Enabled M) : (ruleSpace A allowed).apply M (.step ρ ok) = (M, .fired false) :=
  if_neg en

theorem claimRule_result (k : ℕ) (e : Entry n Op) (M : Multiset A) :
    (claimRule enc k e).result M = M + {enc (.slot k e)} := by
  simp [Rule.result, claimRule]

theorem writeRule_enabled (i : Fin n) (t : ℕ) (op : Op) (M : Multiset A) :
    (writeRule enc i t op).Enabled M :=
  ⟨by simp [writeRule, Rule.redex], by simpa [writeRule, Rule.redex] using avoids_none M⟩

theorem writeRule_result (i : Fin n) (t : ℕ) (op : Op) (M : Multiset A) :
    (writeRule enc i t op).result M = M + {enc (.ann i t op)} := by
  simp [Rule.result, writeRule]

omit [DecidableEq A] in
theorem isSlotAt_slot (k : ℕ) (e : Entry n Op) : isSlotAt enc k (enc (.slot k e)) = true := by
  simp only [isSlotAt, decide_eq_true_eq]; exact ⟨e, rfl⟩

omit [DecidableEq A] in
theorem isAnnAt_ann (i : Fin n) (t : ℕ) (op : Op) : isAnnAt enc i t (enc (.ann i t op)) = true := by
  simp only [isAnnAt, decide_eq_true_eq]; exact ⟨op, rfl⟩

omit [DecidableEq A] in
theorem isAnnAt_slot (inj : Function.Injective enc) (i : Fin n) (t k : ℕ) (e : Entry n Op) :
    isAnnAt enc i t (enc (.slot k e)) = false := by
  simp only [isAnnAt, decide_eq_false_iff_not, not_exists]
  intro op h; cases inj h

omit [DecidableEq A] in
theorem isSlotAt_ann (inj : Function.Injective enc) (k : ℕ) (i : Fin n) (t : ℕ) (op : Op) :
    isSlotAt enc k (enc (.ann i t op)) = false := by
  simp only [isSlotAt, decide_eq_false_iff_not, not_exists]
  intro e h; cases inj h

omit [DecidableEq A] in
theorem filter_slot_eq_zero {k : ℕ} {M : Multiset A} (none' : ¬ ∃ e', enc (.slot k e') ∈ M) :
    M.filter (fun b => isSlotAt enc k b = true) = 0 :=
  Multiset.filter_eq_nil.mpr fun a mem ha => none' (by
    simp only [isSlotAt, decide_eq_true_eq] at ha
    obtain ⟨e', rfl⟩ := ha
    exact ⟨e', mem⟩)

omit [DecidableEq A] in
theorem filter_ann_eq_zero {i : Fin n} {t : ℕ} {M : Multiset A}
    (none' : ¬ ∃ op', enc (.ann i t op') ∈ M) :
    M.filter (fun b => isAnnAt enc i t b = true) = 0 :=
  Multiset.filter_eq_nil.mpr fun a mem ha => none' (by
    simp only [isAnnAt, decide_eq_true_eq] at ha
    obtain ⟨op', rfl⟩ := ha
    exact ⟨op', mem⟩)

theorem claim_slot_view (inj : Function.Injective enc) {allowed : Rule A → Prop} (k : ℕ)
    (e : Entry n Op) (ok : allowed (claimRule enc k e)) (M : Multiset A) :
    (fun k' => slotIn enc k' (((ruleSpace A allowed).apply M (.step (claimRule enc k e) ok)).1.filter
      (fun b => isSlotAt enc k' b = true))) =
    Function.update (fun k' => slotIn enc k' (M.filter (fun b => isSlotAt enc k' b = true))) k
      (some ((slotIn enc k (M.filter (fun b => isSlotAt enc k b = true))).getD e)) := by
  funext k'
  by_cases en : (claimRule enc k e).Enabled M
  · have none' := (claimRule_enabled_iff k e M).mp en
    rw [step_apply_pos ok en, claimRule_result]
    by_cases hk : k' = k
    · subst hk
      rw [Function.update_self, (slotIn_eq_none_iff k' M).mpr none', Option.getD_none,
        Multiset.filter_add, filter_slot_eq_zero none', zero_add, Multiset.filter_singleton,
        if_pos (isSlotAt_slot k' e)]
      exact slotIn_singleton inj k' e
    · rw [Function.update_of_ne hk]
      exact slotIn_filter_add_other hk M inj
  · rw [step_apply_neg ok en]
    by_cases hk : k' = k
    · subst hk
      have some' : ∃ e', enc (.slot k' e') ∈ M := by
        by_contra h; exact en ((claimRule_enabled_iff k' e M).mpr h)
      cases hs : slotIn enc k' (M.filter fun b => isSlotAt enc k' b = true) with
      | none => exact absurd some' ((slotIn_eq_none_iff k' M).mp hs)
      | some w => rw [Function.update_self, Option.getD_some]
    · rw [Function.update_of_ne hk]

theorem claim_ann_view (inj : Function.Injective enc) {allowed : Rule A → Prop} (k : ℕ)
    (e : Entry n Op) (ok : allowed (claimRule enc k e)) (M : Multiset A) :
    (fun i t => annIn enc i t (((ruleSpace A allowed).apply M (.step (claimRule enc k e) ok)).1.filter
      (fun b => isAnnAt enc i t b = true))) =
    (fun i t => annIn enc i t (M.filter (fun b => isAnnAt enc i t b = true))) := by
  funext i t
  by_cases en : (claimRule enc k e).Enabled M
  · rw [step_apply_pos ok en, claimRule_result, filter_add_singleton_false (isAnnAt_slot inj i t k e)]
  · rw [step_apply_neg ok en]

variable (enc) in
/-- **The board of a space with steps**, for any handle that may fire the claim and announcement
steps. -/
noncomputable def spaceBoard (inj : Function.Injective enc) (allowed : Rule A → Prop)
    (hc : ∀ k e, allowed (claimRule enc k e)) (hw : ∀ i t op, allowed (writeRule enc i t op)) :
    Board (ruleSpace A allowed) n Op where
  slot M k := slotIn enc k (M.filter fun b => isSlotAt enc k b = true)
  ann M i t := annIn enc i t (M.filter fun b => isAnnAt enc i t b = true)
  init := 0
  claim k e := .step (claimRule enc k e) (hc k e)
  learn k _ := .query (isSlotAt enc k)
  learned k r e := match r with
    | .matches m => (slotIn enc k m).getD e
    | _ => e
  write i t op := .step (writeRule enc i t op) (hw i t op)
  read i t := .query (isAnnAt enc i t)
  readOut i t r := match r with
    | .matches m => annIn enc i t m
    | _ => none
  init_slot k := by simp [slotIn]
  init_ann i t := by simp [annIn]
  claim_slot M k e := claim_slot_view inj k e (hc k e) M
  claim_ann M k e := claim_ann_view inj k e (hc k e) M
  learn_slot M k e w _ := rfl
  learn_ann M k e w _ := rfl
  learn_out M k e w h := by
    show (slotIn enc k (M.filter fun b => isSlotAt enc k b = true)).getD e = w
    rw [h]; rfl
  write_slot M i t op := by
    funext k
    show slotIn enc k (((ruleSpace A allowed).apply M (.step (writeRule enc i t op) (hw i t op))).1.filter
      (fun b => isSlotAt enc k b = true)) = _
    rw [step_apply_pos _ (writeRule_enabled i t op M), writeRule_result,
      filter_add_singleton_false (isSlotAt_ann inj k i t op)]
  write_self M i t op pre := by
    show annIn enc i t (((ruleSpace A allowed).apply M (.step (writeRule enc i t op) (hw i t op))).1.filter
      (fun b => isAnnAt enc i t b = true)) = some op
    have absent : ¬ ∃ op', enc (.ann i t op') ∈ M := by
      rintro ⟨op', mem⟩
      have := pre t le_rfl
      unfold annIn at this
      rw [dif_pos ⟨op', mem_filter_ann.mpr mem⟩] at this
      cases this
    rw [step_apply_pos _ (writeRule_enabled i t op M), writeRule_result, Multiset.filter_add,
      filter_ann_eq_zero absent, zero_add, Multiset.filter_singleton, if_pos (isAnnAt_ann i t op)]
    exact annIn_singleton inj i t op
  write_above M i t op pre t' lt := by
    show annIn enc i t' (((ruleSpace A allowed).apply M (.step (writeRule enc i t op) (hw i t op))).1.filter
      (fun b => isAnnAt enc i t' b = true)) = none
    rw [step_apply_pos _ (writeRule_enabled i t op M), writeRule_result, filter_add_singleton_false]
    · exact pre t' (by omega)
    · simp only [isAnnAt, decide_eq_false_iff_not, not_exists]
      intro op' h
      have := inj h
      simp only [Code.ann.injEq] at this
      omega
  write_other M i t op j ne := by
    funext t'
    show annIn enc j t' (((ruleSpace A allowed).apply M (.step (writeRule enc i t op) (hw i t op))).1.filter
      (fun b => isAnnAt enc j t' b = true)) = _
    rw [step_apply_pos _ (writeRule_enabled i t op M), writeRule_result, filter_add_singleton_false]
    simp only [isAnnAt, decide_eq_false_iff_not, not_exists]
    intro op' h
    have := inj h
    simp only [Code.ann.injEq] at this
    exact ne this.1
  read_slot M i t := rfl
  read_ann M i t := rfl
  read_out M i t := rfl

/-- **Steps are universal**: over a space whose atoms can encode the log and the announcements of
the target's operations, every object has a wait-free, linearizable implementation by steps and
`match` queries, for any number of processes. -/
theorem steps_universal (Y : DetObject) (s₀ : Y.State) (enc : Code n Y.Op → A)
    (inj : Function.Injective enc) : Implements (stepSpace A).toObject Y s₀ n :=
  ⟨universal (spaceBoard enc inj (fun _ => True) (fun _ _ => trivial) (fun _ _ _ => trivial)) s₀,
    universal_linearizable _ _, universal_waitFree _ _⟩

/-- **Steps that take nothing are already universal**: an addition guarded by absence, an
addition, and `match`. -/
theorem noTakeSteps_universal (Y : DetObject) (s₀ : Y.State) (enc : Code n Y.Op → A)
    (inj : Function.Injective enc) : Implements (noTakeSpace A).toObject Y s₀ n :=
  ⟨universal (spaceBoard enc inj (fun ρ => ρ.take = 0) (fun _ _ => rfl) (fun _ _ _ => rfl)) s₀,
    universal_linearizable _ _, universal_waitFree _ _⟩

end Steps

end Universal

/-! ## Controls -/

namespace Controls

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Equivalence (Rule)

/-- **Positive control**: the second proposal to a consensus object answers the first. -/
theorem consensus_first_stays :
    (consensusObject ℕ).apply ((consensusObject ℕ).apply none (3 : ℕ)).1 (5 : ℕ) =
      ((some 3 : Option ℕ), (3 : ℕ)) := rfl

/-- **Negative control**: a consensus object is not a register: after proposals `3` and `5` it holds
`3`, where a register written `3` then `5` holds `5`. -/
theorem consensus_not_register :
    ((consensusObject ℕ).apply ((consensusObject ℕ).apply none (3 : ℕ)).1 (5 : ℕ)).1 ≠
      (some 5 : Option ℕ) := by
  show (some 3 : Option ℕ) ≠ some 5
  decide

/-- The coding of the controls: a code becomes its own atom. -/
abbrev selfCode : Universal.Code 1 ℕ → Universal.Code 1 ℕ := id

/-- **Positive control**: a claim of an undecided place fires. -/
theorem claim_fires :
    (Universal.claimRule selfCode 0 (0, 7)).Enabled (0 : Multiset (Universal.Code 1 ℕ)) :=
  (Universal.claimRule_enabled_iff 0 (0, 7) 0).mpr (by simp)

/-- **Negative control**: a claim of a decided place does not fire. -/
theorem claim_blocked :
    ¬ (Universal.claimRule selfCode 0 (0, 7)).Enabled ({.slot 0 (0, 3)} : Multiset (Universal.Code 1 ℕ)) := by
  rw [Universal.claimRule_enabled_iff]
  simp

end Controls

end Mettapedia.GSLT.Coordination.ConsensusNumbers
