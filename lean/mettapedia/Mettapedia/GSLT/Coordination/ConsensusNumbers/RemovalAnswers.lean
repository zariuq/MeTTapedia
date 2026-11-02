import Mettapedia.GSLT.Coordination.ConsensusNumbers.StepSpace

/-!
# What a removal answers does not matter beyond two processes

MeTTa's implementations differ in what `remove-atom` answers. Hyperon Experimental removes one
occurrence equal to its argument and answers the unit atom; PeTTa removes every stored atom that
unifies with its argument (pattern variables allowed) and answers `true`. A proposed answer is the
number of atoms removed: `0` or `1` for removing one occurrence, any number for removing every match.

This file shows that the answer, however informative, never lets the separate operations
(`add-atom`, `match`, and removals) give consensus to three processes, and that any answer which says
whether something was removed gives it to two.

## A bystander that cannot tell whether an operation happened

Two processes are about to apply `a` and `b` at the state `s`. `StateBlind T s a b` says that a
third process, which sees only the state, learns nothing that separates the possible outcomes:

* `a` changes nothing, or `b` changes nothing;
* both orders end in the same state;
* `b` after `a` ends where `b` alone ends: `b` **erased** what `a` did. Example: `add 1` and then
  "remove every `1`" end where "remove every `1`" alone ends, although the removal answers `2` in the
  first case and `1` in the second.

The last case is Herlihy's argument for read-modify-write operations that overwrite each other: at a
critical configuration, compare "`a` then `b`" with "`b` alone"; the states agree and a third process
has not moved, so it decides the same from both, which cannot be. The `Valence` file covers the other
cases, and needs the answers to agree when one operation overwrites another; here only the state
matters (`not_solvable_of_stateBlind`).

## The theorems

* **Whatever the operations answer, a space with separate operations gives no consensus to three
  processes** (`spaceWith_not_solvable_three`): every pair of operations is state-blind
  (`spaceWith_stateBlind`). Removing every match at once is one atomic operation on many atoms, but
  as a change of state it commutes with every other removal, and with an addition it either commutes
  or erases it. This holds with any number of spaces and registers used together
  (`spacesWith_registers_not_solvable_three`).
* **More informative answers never hurt** (`Solves.transfer`, `Solvable.of_answers`): if the answers
  of one object can be computed from those of another with the same states and operations, a
  protocol over the first runs over the second.
* **Counting removal** (`countSpace`: remove one occurrence and answer `0` or `1`; remove every atom
  satisfying a pattern and answer how many; add; match) **has consensus number exactly two**
  (`countSpace_hasConsensusNumber_two`), as the reported removal of `Spaces` does.
* **Removing one occurrence, alone**: a space with only `add-atom`, `match` and a removal of one
  occurrence answering `0` or `1` (`oneRemovalSpace`, Hyperon Experimental's operations with a
  counting answer) has consensus number exactly two (`oneRemovalSpace_hasConsensusNumber_two`).
* **Removing every match, alone**: a space with only `add-atom`, `match` and remove-every-match
  answering the count (`patternSpace`, PeTTa's operations with counting answers) **also has consensus
  number exactly two** (`patternSpace_hasConsensusNumber_two`). The two processes remove every copy
  of a single `token`; at most one copy is ever present, so this is the test-and-set race of `Spaces`
  (`tas_runs_on_patternSpace`).

## Controls

* `Controls.erase_not_bystander`: "add `1`, then remove every `1`" against "remove every `1`" from
  `{1}`: the condition of `Valence` fails (the two orders end in different states and the counts
  differ), the new condition holds. So the extension is needed.
* `Controls.claims_not_stateBlind`: two absence-guarded claims of different values at the empty
  space (steps) are not state-blind, as they must not be: steps have an infinite consensus number.
* `Controls.twoWrites_not_stateBlind`: writing two registers at once in overlapping pairs is not
  state-blind. Atomicity on many cells is not what makes removal harmless; it is that removals
  commute.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Coordination.ConsensusNumbers

/-! ## State-blind pairs -/

/-- A process seeing only the state cannot separate the outcomes of `a` and `b`: one of them changes
nothing, or the two orders end in the same state, or the second erases the first. -/
def StateBlind (T : DetObject) (s : T.State) (a b : T.Op) : Prop :=
  (T.apply s a).1 = s ∨ (T.apply s b).1 = s ∨
    (T.apply (T.apply s a).1 b).1 = (T.apply (T.apply s b).1 a).1 ∨
    (T.apply (T.apply s a).1 b).1 = (T.apply s b).1 ∨
    (T.apply (T.apply s b).1 a).1 = (T.apply s a).1

theorem StateBlind.symm {T : DetObject} {s : T.State} {a b : T.Op} (h : StateBlind T s a b) :
    StateBlind T s b a := by
  rcases h with h | h | h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inl h.symm))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))

namespace Protocol

variable {T : DetObject} {n : ℕ} {P : Protocol T.toObject n Bool}

/-- **No erased step at a critical pair.** If `b` after `a` ends in the state `b` alone ends in, a
third process cannot tell the two configurations apart. -/
theorem Solves.no_erased (S : P.Solves) {x : Fin n → Bool} {C : P.Config}
    (reach : P.Reach x C) {p q r : Fin n} {a b : T.Op} (ne : p ≠ q) (rp : r ≠ p) (rq : r ≠ q)
    (ha : P.action p (C.loc p) = .invoke a) (hb : P.action q (C.loc q) = .invoke b)
    {v w : Bool} (hvw : v ≠ w) (hp : ¬ P.Decides (P.go C p) w) (hq : ¬ P.Decides (P.go C q) v)
    (erased : (T.apply (T.apply C.obj a).1 b).1 = (T.apply C.obj b).1) : False := by
  obtain ⟨pqObj, -, -, pqRest⟩ := go_go_of_invoke ne ha hb
  have qObj : (P.go C q).obj = (T.apply C.obj b).1 := by rw [go_of_invoke hb]
  have qLoc : (P.go C q).loc r = C.loc r := go_loc_of_ne rq
  refine S.no_split ((reach.go p).go q) (E := P.go C q) ?_ ?_ hvw (not_decides_go hp) hq (r := r)
  · rw [pqObj, qObj, erased]
  · rw [pqRest r rp rq, qLoc]

end Protocol

open Protocol

/-- **No three-process consensus from an object whose pairs of operations are state-blind.** -/
theorem not_solvable_of_stateBlind {T : DetObject} {n : ℕ} (three : 3 ≤ n)
    (blind : ∀ s a b, StateBlind T s a b) : ¬ Solvable T.toObject n Bool := by
  rintro ⟨P, S⟩
  obtain ⟨x, biv⟩ := S.initial_bivalent (by omega)
  obtain ⟨C, reach, bivC, crit⟩ := S.exists_critical biv
  obtain ⟨p, q, a, b, ne, ha, hb, hp, hq⟩ := S.critical_pair reach bivC crit
  obtain ⟨r, rp, rq⟩ := exists_third three p q
  rcases blind C.obj a b with h | h | h | h | h
  · exact S.no_hidden_order reach ne ha hb (v := false) (w := true) (by decide) hp hq (.noChange h)
  · exact S.no_hidden_order reach (Ne.symm ne) hb ha (v := true) (w := false) (by decide) hq hp
      (.noChange h)
  · exact S.no_bystander_order reach ne rp rq ha hb (v := false) (w := true) (by decide) hp hq h
  · exact S.no_erased reach ne rp rq ha hb (v := false) (w := true) (by decide) hp hq h
  · exact S.no_erased reach (Ne.symm ne) rq rp hb ha (v := true) (w := false) (by decide) hq hp h

/-- **Consensus number two** for an object whose pairs are state-blind and which gives two processes
consensus. -/
theorem hasConsensusNumber_two_of_stateBlind {T : DetObject} (s : T.State)
    (blind : ∀ s a b, StateBlind T s a b) (two : Solvable T.toObject 2 Bool) :
    HasConsensusNumber T.toObject 2 := by
  intro n
  constructor
  · intro solvable
    by_contra big
    exact not_solvable_of_stateBlind (by
      have : ¬ n ≤ 2 := fun h => big (by exact_mod_cast h)
      omega) blind solvable
  · intro small
    have small : n ≤ 2 := by exact_mod_cast small
    rcases Nat.lt_or_ge n 2 with lt | ge
    · exact solvable_of_le_one _ s (by omega) Bool
    · obtain rfl : n = 2 := by omega
      exact two

/-! ### Many objects together -/

theorem pi_stateBlind {K : Type} [DecidableEq K] {T : K → DetObject}
    (blind : ∀ k s a b, StateBlind (T k) s a b) : ∀ s a b, StateBlind (DetObject.pi T) s a b := by
  rintro s ⟨k, a⟩ ⟨l, b⟩
  by_cases same : k = l
  · subst same
    rcases blind k (s k) a b with h | h | h | h | h
    · exact Or.inl (by rw [pi_apply, h, Function.update_eq_self])
    · exact Or.inr (Or.inl (by rw [pi_apply, h, Function.update_eq_self]))
    · exact Or.inr (Or.inr (Or.inl (by
        simp only [Function.update_self, Function.update_idem, h])))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by
        simp only [Function.update_self, Function.update_idem, h]))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (by
        simp only [Function.update_self, Function.update_idem, h]))))
  · refine Or.inr (Or.inr (Or.inl ?_))
    simp only [Function.update_of_ne (Ne.symm same), Function.update_of_ne same]
    exact Function.update_comm same _ _ _

/-- Registers are state-blind: a read changes nothing, a second write to a register erases the
first, writes to different registers commute. -/
theorem registers_stateBlind {ι V : Type} [DecidableEq ι] :
    ∀ s a b, StateBlind (registers ι V) s a b := by
  rintro s (i | ⟨i, v⟩) b
  · exact Or.inl rfl
  · cases b with
    | read j => exact Or.inr (Or.inl rfl)
    | write j w =>
        by_cases same : i = j
        · subst same
          exact Or.inr (Or.inr (Or.inr (Or.inl (by simp [Function.update_idem]))))
        · exact Or.inr (Or.inr (Or.inl (by simp [Function.update_comm same])))

/-! ## Spaces, whatever their operations answer -/

variable {A : Type} [DecidableEq A]

variable (A) in
/-- A space with MeTTa's separate operations (`add`, remove one occurrence, remove every atom
satisfying a pattern, `match`), whatever each operation answers. -/
abbrev spaceWith {R : Type} (reply : Multiset A → SpaceOp A → R) : DetObject where
  State := Multiset A
  Op := SpaceOp A
  Res := R
  apply M op := (spaceNext M op, reply M op)

section AnyReply

variable {R : Type} (reply : Multiset A → SpaceOp A → R)

theorem spaceWith_add_remove (M : Multiset A) (x y : A) :
    StateBlind (spaceWith A reply) M (.add x) (.remove y) := by
  by_cases h : y ∈ M ∨ x ≠ y
  · exact Or.inr (Or.inr (Or.inl (add_remove_comm h)))
  · have absent : y ∉ M := fun mem => h (Or.inl mem)
    exact Or.inr (Or.inl (remove_absent absent))

theorem spaceWith_add_removeWhere (M : Multiset A) (x : A) (p : A → Bool) :
    StateBlind (spaceWith A reply) M (.add x) (.removeWhere p) := by
  by_cases miss : M.filter (fun b => p b = true) = 0
  · exact Or.inr (Or.inl (removeWhere_miss miss))
  · by_cases px : p x = true
    · exact Or.inr (Or.inr (Or.inr (Or.inl (add_removeWhere_hit px))))
    · exact Or.inr (Or.inr (Or.inl (add_removeWhere_comm (by simpa using px))))

/-- **Every pair of separate operations is state-blind, whatever the operations answer.** -/
theorem spaceWith_stateBlind : ∀ M a b, StateBlind (spaceWith A reply) M a b := by
  intro M a b
  cases a with
  | query p => exact Or.inl rfl
  | add x =>
      cases b with
      | query q => exact Or.inr (Or.inl rfl)
      | add y => exact Or.inr (Or.inr (Or.inl (Multiset.cons_swap y x M)))
      | remove y => exact spaceWith_add_remove reply M x y
      | removeWhere q => exact spaceWith_add_removeWhere reply M x q
  | remove x =>
      cases b with
      | query q => exact Or.inr (Or.inl rfl)
      | add y => exact (spaceWith_add_remove reply M y x).symm
      | remove y => exact Or.inr (Or.inr (Or.inl (Multiset.erase_comm M x y)))
      | removeWhere q => exact Or.inr (Or.inr (Or.inl (remove_removeWhere_comm M x q)))
  | removeWhere p =>
      cases b with
      | query q => exact Or.inr (Or.inl rfl)
      | add y => exact (spaceWith_add_removeWhere reply M y p).symm
      | remove y => exact Or.inr (Or.inr (Or.inl (remove_removeWhere_comm M y p).symm))
      | removeWhere q => exact Or.inr (Or.inr (Or.inl (removeWhere_comm M p q)))

/-- **Whatever its operations answer, a space with separate operations gives no consensus to
three processes.** -/
theorem spaceWith_not_solvable_three {n : ℕ} (three : 3 ≤ n) :
    ¬ Solvable (spaceWith A reply).toObject n Bool :=
  not_solvable_of_stateBlind three (spaceWith_stateBlind reply)

variable (K ι V : Type) [DecidableEq K] [DecidableEq ι]

variable (A) in
/-- Spaces named by `K`, answering by `reply`, beside the registers named by `ι`. -/
abbrev spacesWithAndRegisters : DetObject :=
  DetObject.pi fun k : Option K => match k with
    | none => registers ι V
    | some _ => spaceWith A reply

/-- **No three-process consensus from any number of such spaces and registers.** -/
theorem spacesWith_registers_not_solvable_three {n : ℕ} (three : 3 ≤ n) :
    ¬ Solvable (spacesWithAndRegisters A reply K ι V).toObject n Bool := by
  refine not_solvable_of_stateBlind three (pi_stateBlind ?_)
  rintro (_ | _) s a b
  · exact registers_stateBlind s a b
  · exact spaceWith_stateBlind reply s a b

end AnyReply

/-! ## More informative answers never hurt -/

section Transfer

variable {T T' : DetObject} {n : ℕ} {V : Type}

/-- An action with its operation translated by `φ`. -/
def Action.mapOp {Op Op' V : Type} (φ : Op → Op') : Action Op V → Action Op' V
  | .decide v => .decide v
  | .invoke a => .invoke (φ a)

/-- The next local state of a translated protocol: the answer is turned back by `h` first. -/
def translateNext (P : Protocol T.toObject n V) (h : T.Op → T'.Res → T.Res) (i : Fin n)
    (l : P.Local) (r : T'.Res) : P.Local :=
  match P.action i l with
  | .decide _ => l
  | .invoke a => P.next i l (h a r)

/-- Run a protocol over `T` on `T'`: each operation `a` becomes `φ a`, the state `s` is read as
`ψ s`, and each answer is turned back by `h a`. -/
def Protocol.translate (P : Protocol T.toObject n V) (ψ : T.State → T'.State) (φ : T.Op → T'.Op)
    (h : T.Op → T'.Res → T.Res) : Protocol T'.toObject n V where
  Local := P.Local
  start := P.start
  init := ψ P.init
  action i l := (P.action i l).mapOp φ
  next := translateNext P h

variable {P : Protocol T.toObject n V} {ψ : T.State → T'.State} {φ : T.Op → T'.Op}
  {h : T.Op → T'.Res → T.Res}

theorem translateNext_of_invoke {i : Fin n} {l : P.Local} {a : T.Op}
    (hP : P.action i l = .invoke a) (r : T'.Res) : translateNext P h i l r = P.next i l (h a r) := by
  unfold translateNext; rw [hP]

/-- A configuration over `T`, read over `T'`. -/
def Protocol.image (C : P.Config) : (P.translate ψ φ h).Config := ⟨ψ C.obj, C.loc⟩

theorem translate_decision (C : P.Config) (i : Fin n) :
    (P.translate ψ φ h).decision (Protocol.image C) i = P.decision C i := by
  unfold Protocol.decision
  dsimp only [Protocol.image, Protocol.translate]
  cases P.action i (C.loc i) <;> rfl

/-- The translation agrees with `T` wherever the protocol can be. -/
def TranslationAgrees (P : Protocol T.toObject n V) (ψ : T.State → T'.State) (φ : T.Op → T'.Op)
    (h : T.Op → T'.Res → T.Res) : Prop :=
  ∀ x C, P.Reach x C → ∀ i a, P.action i (C.loc i) = .invoke a →
    (T'.apply (ψ C.obj) (φ a)).1 = ψ (T.apply C.obj a).1 ∧
      h a (T'.apply (ψ C.obj) (φ a)).2 = (T.apply C.obj a).2

theorem translate_go (agree : TranslationAgrees P ψ φ h) {x : Fin n → V} {C : P.Config}
    (reach : P.Reach x C) (i : Fin n) :
    (P.translate ψ φ h).go (Protocol.image C) i = Protocol.image (P.go C i) := by
  cases hP : P.action i (C.loc i) with
  | decide v =>
      have act : (P.translate ψ φ h).action i ((Protocol.image (ψ := ψ) (φ := φ) (h := h) C).loc i) =
          .decide v := by
        dsimp only [Protocol.image, Protocol.translate]; rw [hP]; rfl
      rw [Protocol.go_of_decide act, Protocol.go_of_decide hP]
  | invoke a =>
      have act : (P.translate ψ φ h).action i ((Protocol.image (ψ := ψ) (φ := φ) (h := h) C).loc i) =
          .invoke (φ a) := by
        dsimp only [Protocol.image, Protocol.translate]; rw [hP]; rfl
      obtain ⟨st, ans⟩ := agree x C reach i a hP
      rw [Protocol.go_of_invoke act, Protocol.go_of_invoke hP]
      apply Protocol.Config.ext
      · exact st
      · dsimp only [Protocol.image, Protocol.translate]
        rw [translateNext_of_invoke hP, ans]

theorem translate_run (agree : TranslationAgrees P ψ φ h) {x : Fin n → V} {C : P.Config}
    (reach : P.Reach x C) (σ : List (Fin n)) :
    (P.translate ψ φ h).run (Protocol.image C) σ = Protocol.image (P.run C σ) := by
  induction σ generalizing C with
  | nil => rfl
  | cons i σ ih =>
      simp only [Protocol.run]
      rw [translate_go agree reach i]
      exact ih (reach.go i)

theorem translate_initial (x : Fin n → V) :
    (P.translate ψ φ h).initial x = Protocol.image (P.initial x) := rfl

/-- **A protocol translated along operations that agree wherever it can be still solves
consensus.** -/
theorem Protocol.Solves.transfer (S : P.Solves) (agree : TranslationAgrees P ψ φ h) :
    (P.translate ψ φ h).Solves := by
  have reachImage : ∀ x C', (P.translate ψ φ h).Reach x C' →
      ∃ C, P.Reach x C ∧ C' = Protocol.image C := by
    intro x C' reach
    obtain ⟨σ, rfl⟩ := Protocol.reach_iff.mp reach
    refine ⟨P.run (P.initial x) σ, (Protocol.Reach.initial x).run σ, ?_⟩
    rw [translate_initial, translate_run agree (Protocol.Reach.initial x)]
  refine ⟨?_, ?_, ?_⟩
  · intro x C' reach i j v w hv hw
    obtain ⟨C, reachC, rfl⟩ := reachImage x C' reach
    rw [translate_decision] at hv hw
    exact S.agreement x C reachC i j v w hv hw
  · intro x C' reach i v hv
    obtain ⟨C, reachC, rfl⟩ := reachImage x C' reach
    rw [translate_decision] at hv
    exact S.validity x C reachC i v hv
  · intro x σ c start exec i often
    have same : ∀ m, c m = Protocol.image (P.runFrom (P.initial x) σ m) := by
      intro m
      induction m with
      | zero => rw [start]; rfl
      | succ m ih =>
          rw [Protocol.step_iff_go.mp (exec m), ih]
          show _ = Protocol.image (P.go (P.runFrom (P.initial x) σ m) (σ m))
          rw [translate_go agree (Protocol.Execution.reach (x := x) rfl
            (Protocol.execution_runFrom (P.initial x) σ) m)]
    obtain ⟨m, hm⟩ := S.waitFree x σ _ rfl (Protocol.execution_runFrom _ σ) i often
    exact ⟨m, by rw [same m, translate_decision]; exact hm⟩

/-- **More informative answers never hurt**: if `T'` has the states and operations of `T` and the
answers of `T` are computed from those of `T'`, everything solvable over `T` is solvable over
`T'`. -/
theorem Solvable.of_answers (ψ : T.State → T'.State) (φ : T.Op → T'.Op) (h : T.Op → T'.Res → T.Res)
    (agree : ∀ s a, (T'.apply (ψ s) (φ a)).1 = ψ (T.apply s a).1 ∧
      h a (T'.apply (ψ s) (φ a)).2 = (T.apply s a).2)
    (solvable : Solvable T.toObject n V) : Solvable T'.toObject n V := by
  obtain ⟨P, S⟩ := solvable
  exact ⟨_, S.transfer (ψ := ψ) (φ := φ) (h := h) fun _ C _ _ a _ => agree C.obj a⟩

end Transfer

/-! ## Counting removal -/

/-- Answers that count what was removed. -/
inductive CountReply (A : Type) where
  | ack
  | removedCount (k : ℕ)
  | matches (m : Multiset A)

/-- Removing one occurrence answers `0` or `1`; removing every atom satisfying a pattern answers
how many there were. -/
def countReply (M : Multiset A) : SpaceOp A → CountReply A
  | .add _ => .ack
  | .remove a => .removedCount (if a ∈ M then 1 else 0)
  | .removeWhere p => .removedCount (M.filter fun b => p b = true).card
  | .query p => .matches (M.filter fun b => p b = true)

variable (A) in
/-- A space whose removals answer how many atoms they removed. -/
abbrev countSpace : DetObject := spaceWith A countReply

/-- Read a counting answer as a reported removal: did it remove anything? -/
def CountReply.toReply : CountReply A → SpaceReply A
  | .ack => .ack
  | .removedCount k => .removed (decide (k ≠ 0))
  | .matches m => .matches m

theorem countReply_toReply (M : Multiset A) (op : SpaceOp A) :
    (countReply M op).toReply = spaceReply M op := by
  cases op with
  | add a => rfl
  | remove a =>
      by_cases h : a ∈ M <;> simp [countReply, spaceReply, CountReply.toReply, h]
  | removeWhere p =>
      simp [countReply, spaceReply, CountReply.toReply, Multiset.card_eq_zero]
  | query p => rfl

/-- **Two processes reach consensus over a counting space.** -/
theorem countSpace_solvable_two [Infinite A] : Solvable (countSpace A).toObject 2 Bool :=
  Solvable.of_answers (T := separateSpace A) id id (fun _ r => r.toReply)
    (fun M op => ⟨rfl, countReply_toReply M op⟩)
    (((separateSpace_hasConsensusNumber_two (A := A)) 2).mpr le_rfl)

/-- **A space whose removals answer how many atoms they removed has consensus number exactly
two.** -/
theorem countSpace_hasConsensusNumber_two [Infinite A] :
    HasConsensusNumber (countSpace A).toObject 2 :=
  hasConsensusNumber_two_of_stateBlind (T := countSpace A) 0 (spaceWith_stateBlind countReply)
    countSpace_solvable_two

/-! ## Removing every match, alone -/

/-- PeTTa's operations: add, remove every atom satisfying a pattern, match. -/
inductive PatternOp (A : Type) where
  | add (a : A)
  | removeAll (p : A → Bool)
  | query (p : A → Bool)

/-- The same operation among the separate operations. -/
def PatternOp.toSpaceOp : PatternOp A → SpaceOp A
  | .add a => .add a
  | .removeAll p => .removeWhere p
  | .query p => .query p

variable (A) in
/-- A space with `add-atom`, `match`, and a removal of every match that answers the count. -/
abbrev patternSpace : DetObject where
  State := Multiset A
  Op := PatternOp A
  Res := CountReply A
  apply M op := (spaceNext M op.toSpaceOp, countReply M op.toSpaceOp)

theorem patternSpace_stateBlind : ∀ M a b, StateBlind (patternSpace A) M a b :=
  fun M a b => spaceWith_stateBlind countReply M a.toSpaceOp b.toSpaceOp

/-- Removing one occurrence, read as removing every copy: the same where at most one copy is
present. -/
def removeAllCopies : SpaceOp A → PatternOp A
  | .add a => .add a
  | .remove a => .removeAll fun b => decide (b = a)
  | .removeWhere p => .removeAll p
  | .query p => .query p

theorem filter_ne_eq_erase {M : Multiset A} {a : A} (once : M.count a ≤ 1) :
    M.filter (fun b => decide (b = a) = false) = M.erase a := by
  ext c
  rw [Multiset.count_filter, count_erase']
  by_cases h : c = a
  · subst h; simp; omega
  · simp [h]

theorem removeAllCopies_agrees {M : Multiset A} (op : SpaceOp A)
    (once : ∀ a, op = .remove a → M.count a ≤ 1) :
    ((patternSpace A).apply M (removeAllCopies op)).1 = ((separateSpace A).apply M op).1 ∧
      ((patternSpace A).apply M (removeAllCopies op)).2.toReply = ((separateSpace A).apply M op).2 := by
  cases op with
  | add a => exact ⟨rfl, rfl⟩
  | remove a =>
      refine ⟨filter_ne_eq_erase (once a rfl), ?_⟩
      show CountReply.toReply (.removedCount (M.filter fun b => decide (b = a) = true).card) =
        SpaceReply.removed (decide (a ∈ M))
      have card : (M.filter fun b => decide (b = a) = true).card = M.count a := by
        rw [Multiset.count_eq_card_filter_eq]
        congr 1
        exact Multiset.filter_congr fun b _ => by simp [eq_comm]
      rw [card]
      by_cases h : a ∈ M
      · simp [CountReply.toReply, h, Multiset.count_ne_zero.mpr h]
      · simp [CountReply.toReply, h]
  | removeWhere p =>
      refine ⟨rfl, ?_⟩
      show CountReply.toReply (.removedCount (M.filter fun b => p b = true).card) =
        SpaceReply.removed (decide (M.filter (fun b => p b = true) ≠ 0))
      simp only [CountReply.toReply, ne_eq, Multiset.card_eq_zero]
  | query p => exact ⟨rfl, rfl⟩

section TasOnPattern

variable {V : Type} {token : A} {prop : Fin 2 → V → A}
  (prop_inj : ∀ i v j w, prop i v = prop j w → i = j ∧ v = w)
  (token_ne : ∀ i v, prop i v ≠ token)

include token_ne in
theorem board_count_token (x : Fin 2 → V) (p q : Phase) :
    (board token prop x p q).count token ≤ 1 := by
  unfold board
  have h0 : ({prop 0 (x 0)} : Multiset A).count token = 0 :=
    Multiset.count_eq_zero.mpr (by simpa using (token_ne 0 (x 0)).symm)
  have h1 : ({prop 1 (x 1)} : Multiset A).count token = 0 :=
    Multiset.count_eq_zero.mpr (by simpa using (token_ne 1 (x 1)).symm)
  simp only [Multiset.count_add]
  split_ifs <;> simp [h0, h1]

include prop_inj token_ne in
/-- **The test-and-set race runs on a space whose only removal removes every match.** The two
processes remove every copy of the one `token`; at most one copy is ever present. -/
theorem tas_runs_on_patternSpace :
    ((tasProtocol token prop).translate (T' := patternSpace A) id removeAllCopies
      (fun _ r => r.toReply)).Solves := by
  refine (tas_solves prop_inj token_ne).transfer ?_
  intro x C reach i a ha
  obtain ⟨p, q, -, h0, h1, hobj⟩ := tas_inv_of_reach prop_inj token_ne reach
  refine removeAllCopies_agrees a fun b hb => ?_
  subst hb
  have hb : b = token := by
    obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    all_goals
      first
        | (rw [h0] at ha) | (rw [h1] at ha)
      cases p <;> cases q <;> simp [locOf] at ha <;> exact ha.symm
  subst hb
  show (C.obj).count b ≤ 1
  rw [hobj]
  exact board_count_token token_ne x p q

end TasOnPattern

/-- **A space with `add-atom`, `match`, and a removal of every match answering the count has
consensus number exactly two.** -/
theorem patternSpace_hasConsensusNumber_two [Infinite A] :
    HasConsensusNumber (patternSpace A).toObject 2 := by
  let e : Option (Fin 2 × Bool) → A := fun o => Infinite.natEmbedding A (Encodable.encode o)
  have inj : Function.Injective e :=
    (Infinite.natEmbedding A).injective.comp Encodable.encode_injective
  refine hasConsensusNumber_two_of_stateBlind (T := patternSpace A) 0 patternSpace_stateBlind ?_
  refine ⟨_, tas_runs_on_patternSpace (token := e none) (prop := fun i v => e (some (i, v)))
    (fun i v j w h => ?_) (fun i v h => ?_)⟩
  · have := Option.some.inj (inj h)
    exact ⟨(Prod.ext_iff.mp this).1, (Prod.ext_iff.mp this).2⟩
  · exact absurd (inj h) (by simp)

/-! ## Removing one occurrence, alone -/

/-- Hyperon Experimental's operations: add, remove one occurrence, match. -/
inductive OneRemovalOp (A : Type) where
  | add (a : A)
  | remove (a : A)
  | query (p : A → Bool)

/-- The same operation among the separate operations. -/
def OneRemovalOp.toSpaceOp : OneRemovalOp A → SpaceOp A
  | .add a => .add a
  | .remove a => .remove a
  | .query p => .query p

variable (A) in
/-- A space with `add-atom`, `match`, and a removal of one occurrence answering `0` or `1`. -/
abbrev oneRemovalSpace : DetObject where
  State := Multiset A
  Op := OneRemovalOp A
  Res := CountReply A
  apply M op := (spaceNext M op.toSpaceOp, countReply M op.toSpaceOp)

theorem oneRemovalSpace_stateBlind : ∀ M a b, StateBlind (oneRemovalSpace A) M a b :=
  fun M a b => spaceWith_stateBlind countReply M a.toSpaceOp b.toSpaceOp

/-- The race's operations among Hyperon's; the race never removes by pattern, so the last case is
never used. -/
def keepOneRemoval : SpaceOp A → OneRemovalOp A
  | .add a => .add a
  | .remove a => .remove a
  | .removeWhere p => .query p
  | .query p => .query p

section TasOnOneRemoval

variable {V : Type} {token : A} {prop : Fin 2 → V → A}
  (prop_inj : ∀ i v j w, prop i v = prop j w → i = j ∧ v = w)
  (token_ne : ∀ i v, prop i v ≠ token)

include prop_inj token_ne in
/-- **The test-and-set race runs on a space whose removal answers `0` or `1`.** -/
theorem tas_runs_on_oneRemovalSpace :
    ((tasProtocol token prop).translate (T' := oneRemovalSpace A) id keepOneRemoval
      (fun _ r => r.toReply)).Solves := by
  refine (tas_solves prop_inj token_ne).transfer ?_
  intro x C reach i a ha
  obtain ⟨p, q, -, h0, h1, -⟩ := tas_inv_of_reach prop_inj token_ne reach
  cases a with
  | add b => exact ⟨rfl, rfl⟩
  | remove b => exact ⟨rfl, countReply_toReply C.obj (.remove b)⟩
  | query f => exact ⟨rfl, rfl⟩
  | removeWhere f =>
      exfalso
      obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
      all_goals
        first
          | (rw [h0] at ha) | (rw [h1] at ha)
        cases p <;> cases q <;> simp [locOf] at ha

end TasOnOneRemoval

/-- **A space with `add-atom`, `match`, and a removal of one occurrence answering `0` or `1` has
consensus number exactly two**: a count in `{0, 1}` says no more than a reported removal. -/
theorem oneRemovalSpace_hasConsensusNumber_two [Infinite A] :
    HasConsensusNumber (oneRemovalSpace A).toObject 2 := by
  let e : Option (Fin 2 × Bool) → A := fun o => Infinite.natEmbedding A (Encodable.encode o)
  have inj : Function.Injective e :=
    (Infinite.natEmbedding A).injective.comp Encodable.encode_injective
  refine hasConsensusNumber_two_of_stateBlind (T := oneRemovalSpace A) 0 oneRemovalSpace_stateBlind ?_
  refine ⟨_, tas_runs_on_oneRemovalSpace (token := e none) (prop := fun i v => e (some (i, v)))
    (fun i v j w h => ?_) (fun i v h => ?_)⟩
  · have := Option.some.inj (inj h)
    exact ⟨(Prod.ext_iff.mp this).1, (Prod.ext_iff.mp this).2⟩
  · exact absurd (inj h) (by simp)

/-! ## Controls -/

namespace Controls

/-- **Positive and negative control**: from `{1}`, "add `1`, then remove every `1`" and "remove every
`1`" end in the same state although the counts differ (`2` against `1`). The condition of `Valence`
fails for this pair; the state-blind one holds. -/
theorem erase_not_bystander :
    StateBlind (countSpace ℕ) {1} (.add 1) (.removeWhere fun b => decide (b = 1)) ∧
      ¬ BystanderCannotOrder (countSpace ℕ) {1} (.add 1) (.removeWhere fun b => decide (b = 1)) := by
  refine ⟨Or.inr (Or.inr (Or.inr (Or.inl (by simp [spaceNext])))), ?_⟩
  have one : ¬ OrderHidden (countSpace ℕ) {1} (.add 1) (.removeWhere fun b => decide (b = 1)) := by
    rintro (h | h | ⟨h, -⟩)
    · have := congrArg Multiset.card h; simp [spaceNext] at this
    · have := congrArg Prod.snd h; simp [spaceNext, countReply, Multiset.filter_singleton] at this
    · have := congrArg Multiset.card h; simp [spaceNext, Multiset.filter_singleton] at this
  have two : ¬ OrderHidden (countSpace ℕ) {1} (.removeWhere fun b => decide (b = 1)) (.add 1) := by
    rintro (h | h | ⟨h, -⟩)
    · have := congrArg Multiset.card h; simp [spaceNext, Multiset.filter_singleton] at this
    · have := congrArg (fun r => Multiset.card r.1) h; simp [spaceNext, Multiset.filter_singleton] at this
    · have := congrArg Multiset.card h; simp [spaceNext, Multiset.filter_singleton] at this
  rintro ((h | h) | h)
  · exact one h
  · exact two h
  · have := congrArg Multiset.card h; simp [spaceNext, Multiset.filter_singleton] at this

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Equivalence (Rule Avoids) in
/-- **Negative control**: two absence-guarded claims of different values at the empty space (steps
that make `1`, or `2`, provided neither is present) are not state-blind: the first to fire wins and
the state shows which. -/
theorem claims_not_stateBlind :
    ¬ StateBlind (noTakeSpace ℕ) 0
      (.step ⟨0, 0, {1}, fun a => decide (a = 1 ∨ a = 2)⟩ rfl)
      (.step ⟨0, 0, {2}, fun a => decide (a = 1 ∨ a = 2)⟩ rfl) := by
  rintro (h | h | h | h | h) <;> simp [Rule.Enabled, Rule.redex, Rule.result, Avoids] at h

/-- Three registers with one operation that writes two of them at once. -/
def twoWrites : DetObject where
  State := Fin 3 → ℕ
  Op := (Fin 3 × ℕ) × (Fin 3 × ℕ)
  Res := Unit
  apply s w := (Function.update (Function.update s w.1.1 w.1.2) w.2.1 w.2.2, ())

/-- **Negative control**: writing registers `0, 1` and registers `1, 2` at once, from all zeros, is
not state-blind: register `1` shows the order, register `0` or `2` shows whether the other write
happened. Writing many cells atomically is not harmless in general. -/
theorem twoWrites_not_stateBlind :
    ¬ StateBlind twoWrites (fun _ => 0) ((0, 1), (1, 1)) ((1, 2), (2, 2)) := by
  rintro (h | h | h | h | h)
  · have := congrFun h 0; revert this; decide
  · have := congrFun h 1; revert this; decide
  · have := congrFun h 1; revert this; decide
  · have := congrFun h 0; revert this; decide
  · have := congrFun h 2; revert this; decide

end Controls

end Mettapedia.GSLT.Coordination.ConsensusNumbers
