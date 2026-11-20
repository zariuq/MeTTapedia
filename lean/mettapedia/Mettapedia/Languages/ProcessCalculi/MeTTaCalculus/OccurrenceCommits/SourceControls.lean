import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.CommutativeMatching
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.SourceQuantifiers

/-!
# Controls for compiling sources to commits

Occurrences are pairs of a value and a serial number (`Occ`), labelled by their value: content
identity and occurrence identity are separate, and fresh occurrences of every label exist
(`supply`). `bagComm` declares the symbol `bag` commutative; `noComm` declares nothing, the
syntactic case. Every fact about rows below is computed by the kernel (`decide`).

## The separating cases

* **Read and take of one occurrence is refused** (`readTake_one_refused`): with one `tok`, the only
  row keeps and takes the same occurrence, the identification condition of double-pushout
  rewriting fails, and nothing fires. With two `tok`s exactly two rows are linear
  (`readTake_two_linear_rows`) and the transform fires (`readTake_two_fires`).
* **A vacuous `every` after a taking kernel** (`evalStep_vacuous`): an evaluation step takes a
  redex and, for every equation of its head, makes the right-hand side. With no equation the
  `every` has no row, and the commit takes the redex and makes nothing: the redex is lost.
  Reading one equation in the kernel first (`evalStepGuarded`) refuses the firing when there is
  none (`evalStepGuarded_refused`), and agrees with the unguarded step when there is one
  (`evalStep_with_equation`, `evalStepGuarded_with_equation`).

## Controls asked for

* **A static region that must widen modulo `E`** (`naivePrefixKeys_unsound_modulo_comm`): the
  pattern `bag(tok, $x)` has the naive prefix key `bag tok`; the label `bag(lock, tok)` is solved
  modulo commutativity and lies outside it. The consequence is concrete
  (`naive_apartness_wrong`): the naive keys declare a taker of `bag(tok, $x)` and a reader of
  `bag(lock, $y)` apart, and at a store holding `bag(lock, tok)` their commits are not
  independent. The widened keys do not declare them apart (`widened_not_apart`).
* **A non-linear pattern** (`diagonal_*`): `pr($x, $x)` matches `pr(a, a)` and not `pr(a, b)`; it
  matches `pr(bag(a, b), bag(b, a))` modulo commutativity and not syntactically. A repeated
  variable is equality modulo `E`.
* **A matcher that is sound and not complete** (`syntactic_sound_for_comm`,
  `syntactic_not_complete_for_comm`): the syntactic matcher used for the commutative theory.
  What breaks: a none query fires although the region is not empty modulo `E`
  (`incomplete_absence_fires`); an `every` misses a row and its completeness query, computed by
  the same matcher, does not see it either (`incomplete_every_misses_row`); `unique` fires with
  two occurrences in its region (`incomplete_unique_fires`). The complete matcher refuses the
  first and third and takes both rows in the second.
* **A matcher that is complete and not minimal double-counts** (`raw_not_minimal`,
  `raw_every_makes_twice`): `rawMatch` answers `bag($x, $y)` against `bag(a, a)` twice, so an
  `every` makes its template twice.
* **`every (take p)` modulo a non-unitary theory** (`everyTake_refused_modulo_comm`): an occurrence
  `bag(a, b)` has two rows for `bag($x, $y)`; both take it, and the `every` is refused, as the
  multiset `every` refuses rows that take one occurrence. Syntactically there is one row and it
  fires (`everyTake_fires_syntactic`). `all take` takes the region once in both cases
  (`allTake_fires_modulo_comm`).
* **Static independence, positive and negative** (`takeTok_readLock_apart`,
  `takeTok_readTok_not_apart`, `takeTok_readTok_dependent`).
* **The text checks for the cheapest mode** (`text_checks`, `readLock_takeTok_checks`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources.Controls

open Commutative

/-- Symbols of the controls. -/
inductive Sig where
  | tok | lock | bag | pr | redex | eqn | seen | out | a | b | nil
  deriving DecidableEq, Repr

/-- Occurrences: a value and a serial number. -/
abbrev Occ := Tm Sig × ℕ

/-- The label of an occurrence is its value. -/
def lbl : Occ → Tm Sig := Prod.fst

/-- `bag` commutes. -/
def bagComm : Sig → Bool
  | .bag => true
  | _ => false

/-- Nothing commutes: syntactic matching. -/
def noComm : Sig → Bool := fun _ => false

/-- The commutative layer. -/
abbrev Lc : TermLayer ℕ (Tm Sig) (Pat ℕ Sig) := termLayer bagComm
/-- The syntactic layer. -/
abbrev Ls : TermLayer ℕ (Tm Sig) (Pat ℕ Sig) := termLayer noComm
/-- The matcher modulo commutativity of `bag`. -/
abbrev mc : Matcher ℕ (Tm Sig) (Pat ℕ Sig) := cmatch bagComm
/-- The syntactic matcher. -/
abbrev ms : Matcher ℕ (Tm Sig) (Pat ℕ Sig) := cmatch noComm

/-- The empty substitution. -/
def empty : Subst ℕ (Tm Sig) := fun _ => none

/-- Fresh occurrences of every label exist. -/
theorem supply : ∀ (X : Finset Occ) (t : Tm Sig), ∃ o, o ∉ X ∧ lbl o = t := by
  intro X t
  obtain ⟨n, notIn⟩ := Infinite.exists_notMem_finset (X.image Prod.snd)
  refine ⟨(t, n), fun member => notIn (Finset.mem_image.mpr ⟨_, member, rfl⟩), rfl⟩

/-- A commit made nothing when its footprint makes nothing. -/
theorem made_eq_empty {S : Finset Occ} {fp : Footprint Occ (Tm Sig)} {c : Commit Occ (Tm Sig)}
    (commit : IsCommitOf lbl S fp c) (nothing : fp.makes = 0) : c.made = ∅ := by
  have := commit.made
  rw [nothing] at this
  unfold labels at this
  exact Finset.val_eq_zero.mp (Multiset.map_eq_zero.mp this)

/-- A linear row gives a fired commit. -/
theorem fires_of_row {L : TermLayer ℕ (Tm Sig) (Pat ℕ Sig)} {m : Matcher ℕ (Tm Sig) (Pat ℕ Sig)}
    {S : Finset Occ} {t : Transform ℕ (Tm Sig) (Pat ℕ Sig)}
    (row : ∃ x ∈ t.rows L m lbl S, (footprintOf x.2).Linear) :
    ∃ x ∈ t.rows L m lbl S, ∃ c, Fires L m lbl S t c ∧ IsCommitOf lbl S (footprintOf x.2) c := by
  obtain ⟨x, member, linear⟩ := row
  obtain ⟨c, commit⟩ := exists_isCommitOf (S := S) supply (footprintOf x.2)
  exact ⟨x, member, c, ⟨x, member, linear, commit⟩, commit⟩

/-- No linear row: nothing fires. -/
theorem not_fires_of_rows {L : TermLayer ℕ (Tm Sig) (Pat ℕ Sig)} {m : Matcher ℕ (Tm Sig) (Pat ℕ Sig)}
    {S : Finset Occ} {t : Transform ℕ (Tm Sig) (Pat ℕ Sig)}
    (none : ∀ x ∈ t.rows L m lbl S, ¬ (footprintOf x.2).Linear) (c : Commit Occ (Tm Sig)) :
    ¬ Fires L m lbl S t c := fun ⟨x, member, linear, _⟩ => none x member linear

/-- A computed refutation of "no element" gives an element. -/
theorem exists_of_not_forall {α : Type*} {s : Multiset α} {p : α → Prop}
    (h : ¬ ∀ x ∈ s, ¬ p x) : ∃ x ∈ s, p x := by
  by_contra none
  exact h fun x member holds => none ⟨x, member, holds⟩

/-- Naive prefix keys over the control terms. -/
abbrev naiveR : RegionKeys (Tm Sig) (Pat ℕ Sig) (Key Sig) := regionKeys naivePrefixKeys
/-- Prefix keys widened for `bagComm`. -/
abbrev widenedR : RegionKeys (Tm Sig) (Pat ℕ Sig) (Key Sig) := regionKeys (prefixKeys bagComm)
/-- Head keys. -/
abbrev headR : RegionKeys (Tm Sig) (Pat ℕ Sig) (Key Sig) := regionKeys headKeys

/-- Terms of the controls. -/
def k (s : Sig) : Tm Sig := .leaf s
/-- A unary node. -/
def un (f : Sig) (x : Tm Sig) : Tm Sig := .node f x (.leaf .nil)
/-- A binary node. -/
def bin (f : Sig) (x y : Tm Sig) : Tm Sig := .node f x y

/-- Two variable patterns have the same shape, but a held assignment to one
    variable makes their observations different unless the assignment is
    renamed with the pattern. -/
theorem captured_variable_requires_context_renaming :
    (ms (.var 0) (Function.update empty 0 (some (k .b))) (k .a)).length = 0 ∧
    (ms (.var 1) (Function.update empty 0 (some (k .b))) (k .a)).length = 1 ∧
    (ms (.var 1) (Function.update empty 1 (some (k .b))) (k .a)).length = 0 ∧
    (ms (.var 0) (Function.update empty 0 (some (k .b))) (k .b)).length = 1 ∧
    (ms (.var 1) (Function.update empty 1 (some (k .b))) (k .b)).length = 1 := by
  decide

/-! ## Read and take of one occurrence -/

/-- Read a `tok` and take a `tok`. -/
def readTake : Transform ℕ (Tm Sig) (Pat ℕ Sig) :=
  ⟨.cons (.read (.leaf .tok)) (.cons (.take (.leaf .tok)) .done), [.leaf .out]⟩

/-- One `tok`. -/
def oneTok : Finset Occ := {(k .tok, 0)}
/-- Two `tok`s. -/
def twoTok : Finset Occ := {(k .tok, 0), (k .tok, 1)}

theorem readTake_one_rows : ∀ x ∈ readTake.rows Ls ms lbl oneTok, ¬ (footprintOf x.2).Linear := by
  decide

/-- **Negative control: one occurrence is not both read and taken.** -/
theorem readTake_one_refused (c : Commit Occ (Tm Sig)) : ¬ Fires Ls ms lbl oneTok readTake c :=
  not_fires_of_rows readTake_one_rows c

/-- With two `tok`s, exactly two of the four rows are linear. -/
theorem readTake_two_linear_rows :
    (readTake.rows Ls ms lbl twoTok).card = 4 ∧
      ((readTake.rows Ls ms lbl twoTok).filter fun x => (footprintOf x.2).Linear).card = 2 := by
  decide

/-- Equal token labels leave two different legal occurrence footprints. A
    removal policy must say which it selects; their identities are observable. -/
theorem readTake_two_distinct_footprints :
    (∃ row ∈ readTake.rows Ls ms lbl twoTok,
      (footprintOf row.2).Linear ∧
      (footprintOf row.2).keeps = {(k .tok, 0)} ∧
      (footprintOf row.2).takes = {(k .tok, 1)}) ∧
    (∃ row ∈ readTake.rows Ls ms lbl twoTok,
      (footprintOf row.2).Linear ∧
      (footprintOf row.2).keeps = {(k .tok, 1)} ∧
      (footprintOf row.2).takes = {(k .tok, 0)}) := by
  constructor
  · apply exists_of_not_forall
    decide +kernel
  · apply exists_of_not_forall
    decide +kernel

/-- **Positive control: with two `tok`s the transform fires.** -/
theorem readTake_two_fires : ∃ c, Fires Ls ms lbl twoTok readTake c := by
  obtain ⟨-, -, c, fires, -⟩ := fires_of_row (L := Ls) (m := ms) (S := twoTok) (t := readTake)
    (exists_of_not_forall (by decide))
  exact ⟨c, fires⟩

/-! Replacing a taken value by an equal value does not keep the original
occurrence. A read and take still need different physical witnesses. -/

/-- Keep and take a token, then make a fresh token with the same label. -/
def readReplaceTok : Transform ℕ (Tm Sig) (Pat ℕ Sig) :=
  ⟨.cons (.read (.leaf .tok)) (.cons (.take (.leaf .tok)) .done), [.leaf .tok]⟩

/-- A same-labelled output does not make a single read/take witness linear. -/
theorem readReplaceTok_one_refused (c : Commit Occ (Tm Sig)) :
    ¬ Fires Ls ms lbl oneTok readReplaceTok c := by
  apply not_fires_of_rows (t := readReplaceTok) _ c
  decide

/-- A second physical token supplies the independent witness. -/
theorem readReplaceTok_two_fires : ∃ c, Fires Ls ms lbl twoTok readReplaceTok c := by
  obtain ⟨-, -, c, fires, -⟩ := fires_of_row (L := Ls) (m := ms) (S := twoTok)
    (t := readReplaceTok) (exists_of_not_forall (by decide))
  exact ⟨c, fires⟩

/-! ## A removal selected after a read

Once a removal has selected a physical occurrence, its consumption participates
in the same footprint as source takes. A conflicting candidate does not imply
that all read matches conflict: the next witness can keep a different item.
This models the selected removal, not the separate policy for a removal with
no matching occurrence. -/

/-- Keep one arbitrary occurrence and consume the occurrence labelled `a`. -/
def readAnyTakeA : Transform ℕ (Tm Sig) (Pat ℕ Sig) :=
  ⟨.cons (.read (.var 0)) (.cons (.take (.leaf .a)) .done), [.var 0]⟩

def aAndB : Finset Occ := {(k .a, 0), (k .b, 1)}

/-- Source rows for a variable already bound to `b`. -/
def heldBoundRows := Sources.rows Ls ms lbl aAndB [.var 0]
  (.cons (.read (.var 0)) .done) (Function.update empty 0 (some (k .b)))

/-- Source rows for another variable in that same held context. -/
def heldFreeRows := Sources.rows Ls ms lbl aAndB [.var 1]
  (.cons (.read (.var 1)) .done) (Function.update empty 0 (some (k .b)))

/-- The same store distinguishes an outer-bound source variable from an
    unbound one: the former has one kept row, the latter has two. -/
theorem held_context_changes_source_rows :
    heldBoundRows.card = 1 ∧ heldFreeRows.card = 2 ∧
    (∀ row ∈ heldBoundRows, (footprintOf row.2).keeps = {((k .b), 1)}) ∧
    (∃ row ∈ heldFreeRows, (footprintOf row.2).keeps = {((k .a), 0)}) := by
  have checks : heldBoundRows.card = 1 ∧ heldFreeRows.card = 2 ∧
      (∀ row ∈ heldBoundRows, (footprintOf row.2).keeps = {((k .b), 1)}) ∧
      ¬ (∀ row ∈ heldFreeRows, (footprintOf row.2).keeps ≠ {((k .a), 0)}) := by
    decide +kernel
  exact ⟨checks.1, checks.2.1, checks.2.2.1, exists_of_not_forall checks.2.2.2⟩

/-- Both read candidates exist, but only the one keeping `b` is linear. -/
theorem readAnyTakeA_candidate_filter :
    (readAnyTakeA.rows Ls ms lbl aAndB).card = 2 ∧
      ((readAnyTakeA.rows Ls ms lbl aAndB).filter fun x =>
        (footprintOf x.2).Linear).card = 1 ∧
      ∀ x ∈ readAnyTakeA.rows Ls ms lbl aAndB,
        (footprintOf x.2).Linear → x.1 0 = some (k .b) := by
  decide +kernel

/-- Both choices are present: keeping `a` conflicts and keeping `b` does not. -/
theorem readAnyTakeA_both_candidates :
    (∃ x ∈ readAnyTakeA.rows Ls ms lbl aAndB,
      x.1 0 = some (k .a) ∧ ¬ (footprintOf x.2).Linear) ∧
    (∃ x ∈ readAnyTakeA.rows Ls ms lbl aAndB,
      x.1 0 = some (k .b) ∧ (footprintOf x.2).Linear) := by
  exact ⟨exists_of_not_forall (by decide), exists_of_not_forall (by decide)⟩

/-- Rejecting the candidate that keeps `a` is not exhaustion: a complete
matcher still finds an independent firing that keeps `b`. -/
theorem readAnyTakeA_has_firing : ∃ c, Fires Ls ms lbl aAndB readAnyTakeA c := by
  obtain ⟨-, -, c, fires, -⟩ := fires_of_row (L := Ls) (m := ms)
    (S := aAndB) (t := readAnyTakeA) (exists_of_not_forall (by decide))
  exact ⟨c, fires⟩

/-! ## A vacuous `every` after a taking kernel -/

/-- Take a redex `redex(x)`; for every equation `eqn(x, y)`, make `y`. -/
def evalStep : Transform ℕ (Tm Sig) (Pat ℕ Sig) :=
  ⟨.cons (.take (.node .redex (.var 0) (.leaf .nil)))
    (.every (.cons (.read (.node .eqn (.var 0) (.var 1))) .done)), [.var 1]⟩

/-- The same step, reading one equation of the redex's head in the kernel first. -/
def evalStepGuarded : Transform ℕ (Tm Sig) (Pat ℕ Sig) :=
  ⟨.cons (.take (.node .redex (.var 0) (.leaf .nil)))
    (.cons (.read (.node .eqn (.var 0) (.var 2)))
      (.every (.cons (.read (.node .eqn (.var 0) (.var 1))) .done))), [.var 1]⟩

/-- A redex and no equation. -/
def redexAlone : Finset Occ := {(un .redex (k .a), 0)}
/-- A redex and one equation `a = b`. -/
def redexWithEquation : Finset Occ := {(un .redex (k .a), 0), (bin .eqn (k .a) (k .b), 1)}

theorem evalStep_vacuous_row :
    ∃ x ∈ evalStep.rows Lc mc lbl redexAlone, (footprintOf x.2).Linear ∧
      (footprintOf x.2).takes = {(un .redex (k .a), 0)} ∧ (footprintOf x.2).makes = 0 :=
  exists_of_not_forall (by decide)

/-- **The vacuous `every`**: with no equation, the step fires, takes the redex and makes nothing;
the store is left empty. -/
theorem evalStep_vacuous : ∃ c, Fires Lc mc lbl redexAlone evalStep c ∧ fire redexAlone c = ∅ := by
  obtain ⟨x, member, linear, takes, makes⟩ := evalStep_vacuous_row
  obtain ⟨c, commit⟩ := exists_isCommitOf (S := redexAlone) supply (footprintOf x.2)
  refine ⟨c, ⟨x, member, linear, commit⟩, ?_⟩
  rw [fire, made_eq_empty commit makes, commit.taken, takes]
  decide

/-- **The guarded step refuses** when there is no equation. -/
theorem evalStepGuarded_refused (c : Commit Occ (Tm Sig)) :
    ¬ Fires Lc mc lbl redexAlone evalStepGuarded c :=
  not_fires_of_rows (by decide) c

/-- With an equation, the unguarded step fires and makes the right-hand side. -/
theorem evalStep_with_equation :
    ∃ x ∈ evalStep.rows Lc mc lbl redexWithEquation, (footprintOf x.2).Linear ∧
      (footprintOf x.2).takes = {(un .redex (k .a), 0)} ∧ (footprintOf x.2).makes = {k .b} :=
  exists_of_not_forall (by decide)

/-- With an equation, the guarded step fires the same way. -/
theorem evalStepGuarded_with_equation :
    ∃ x ∈ evalStepGuarded.rows Lc mc lbl redexWithEquation, (footprintOf x.2).Linear ∧
      (footprintOf x.2).takes = {(un .redex (k .a), 0)} ∧ (footprintOf x.2).makes = {k .b} :=
  exists_of_not_forall (by decide)

/-! ## A static region that must widen modulo the theory -/

/-- `bag(tok, $x)`. -/
def pBagTok : Pat ℕ Sig := .node .bag (.leaf .tok) (.var 0)
/-- `bag(lock, tok)`, equal to `bag(tok, lock)` modulo commutativity. -/
def lockTok : Tm Sig := bin .bag (k .lock) (k .tok)

theorem solves_lockTok : Lc.Solves (Function.update empty 0 (some (k .lock))) pBagTok lockTok :=
  ⟨bin .bag (k .tok) (k .lock), rfl, (by decide : ceq bagComm (bin .bag (k .tok) (k .lock)) lockTok = true)⟩

/-- **The naive prefix keys are not sound modulo commutativity.** -/
theorem naivePrefixKeys_unsound_modulo_comm :
    ¬ naiveR.Sound Lc := by
  intro sound
  obtain ⟨key, member, covers⟩ := sound _ _ _ solves_lockTok
  simp only [regionKeys, naivePrefixKeys, pBagTok, Pat.head?, List.mem_singleton] at member
  subst member
  obtain ⟨l, r, same, head⟩ := covers
  simp only [lockTok, bin, k, Tm.node.injEq] at same
  obtain ⟨-, rfl, -⟩ := same
  cases head

/-- The widened keys cover it: they are the theory's closure of the naive region. -/
theorem widened_covers_lockTok :
    widenedR.CoveredBy (prefixKeys bagComm pBagTok) lockTok :=
  prefixKeys_sound bagComm _ _ _ solves_lockTok

/-- Take `bag(tok, $x)`. -/
def takeBagTok : Transform ℕ (Tm Sig) (Pat ℕ Sig) := ⟨.cons (.take pBagTok) .done, []⟩
/-- Read `bag(lock, $y)`. -/
def readBagLock : Transform ℕ (Tm Sig) (Pat ℕ Sig) :=
  ⟨.cons (.read (.node .bag (.leaf .lock) (.var 1))) .done, [.leaf .out]⟩

/-- A store with `bag(lock, tok)`. -/
def lockTokStore : Finset Occ := {(lockTok, 0)}

/-- **What the unsound keys get wrong.** The naive keys declare the two transforms apart, yet at a
store with `bag(lock, tok)` the taker's commit takes what the reader's commit keeps. -/
theorem naive_apartness_wrong :
    (takeBagTok.static naiveR).Apart naiveR (readBagLock.static naiveR) ∧
      ∃ c d, Fires Lc mc lbl lockTokStore takeBagTok c ∧ Fires Lc mc lbl lockTokStore readBagLock d ∧
        Disjoint c.made d.made ∧ ¬ Independent lbl c d := by
  refine ⟨by decide, ?_⟩
  obtain ⟨x, xMember, xLinear, xTakes⟩ : ∃ x ∈ takeBagTok.rows Lc mc lbl lockTokStore,
      (footprintOf x.2).Linear ∧ (footprintOf x.2).takes = {(lockTok, 0)} :=
    exists_of_not_forall (by decide)
  obtain ⟨y, yMember, yLinear, yKeeps⟩ : ∃ y ∈ readBagLock.rows Lc mc lbl lockTokStore,
      (footprintOf y.2).Linear ∧ (footprintOf y.2).keeps = {(lockTok, 0)} :=
    exists_of_not_forall (by decide)
  obtain ⟨c, commitC⟩ := exists_isCommitOf (S := lockTokStore) supply (footprintOf x.2)
  obtain ⟨M, apartM, labelsM⟩ :=
    exists_fresh_labels supply (footprintOf y.2).makes (lockTokStore ∪ c.made)
  let d : Commit Occ (Tm Sig) := ⟨(footprintOf y.2).takes.toFinset,
    (footprintOf y.2).keeps.toFinset, M, (footprintOf y.2).queries.toList⟩
  have commitD : IsCommitOf lbl lockTokStore (footprintOf y.2) d :=
    ⟨rfl, rfl, fun r => Multiset.mem_toList,
      Finset.disjoint_of_subset_right Finset.subset_union_left apartM, labelsM⟩
  refine ⟨c, d, ⟨x, xMember, xLinear, commitC⟩, ⟨y, yMember, yLinear, commitD⟩,
    (Finset.disjoint_of_subset_right Finset.subset_union_right apartM).symm, ?_⟩
  rintro ⟨-, notSpoil, -⟩
  apply notSpoil
  left
  rw [commitC.taken, commitD.kept, xTakes, yKeeps]
  decide

/-- **The widened keys do not declare them apart.** -/
theorem widened_not_apart :
    ¬ (takeBagTok.static widenedR).Apart widenedR (readBagLock.static widenedR) := by
  decide

/-! ## A non-linear pattern -/

/-- `pr($x, $x)`. -/
def pDiag : Pat ℕ Sig := .node .pr (.var 0) (.var 0)

theorem diagonal_matches_equal : (ms pDiag empty (bin .pr (k .a) (k .a))).length = 1 := by decide

theorem diagonal_refuses_different : (ms pDiag empty (bin .pr (k .a) (k .b))).length = 0 := by decide

/-- **A repeated variable is equality modulo the theory.** -/
theorem diagonal_modulo_comm :
    (mc pDiag empty (bin .pr (bin .bag (k .a) (k .b)) (bin .bag (k .b) (k .a)))).length = 1 := by
  decide

theorem diagonal_syntactic_refuses :
    (ms pDiag empty (bin .pr (bin .bag (k .a) (k .b)) (bin .bag (k .b) (k .a)))).length = 0 := by
  decide

/-! ## A sound matcher that is not complete -/

/-- A syntactic step is a step modulo commutativity. -/
theorem step_of_syntactic {σ τ : Subst ℕ (Tm Sig)} {p : Pat ℕ Sig} {t : Tm Sig}
    (step : Ls.Step σ p t τ) : Lc.Step σ p t τ := by
  obtain ⟨grows, only, u, inst, rel⟩ := step
  refine ⟨grows, only, u, inst, ?_⟩
  have same : u = t := ceq_noComm_iff.mp rel
  subst same
  exact ceq_refl u

/-- **The syntactic matcher is sound for the commutative theory.** -/
theorem syntactic_sound_for_comm : Matcher.Sound Lc ms := fun answer =>
  step_of_syntactic (cmatch_sound answer)

/-- `bag(a, b)`, without variables. -/
def pBagAB : Pat ℕ Sig := .node .bag (.leaf .a) (.leaf .b)
/-- `bag(b, a)`. -/
def bagBA : Tm Sig := bin .bag (k .b) (k .a)

/-- **The syntactic matcher is not complete for the commutative theory.** -/
theorem syntactic_not_complete_for_comm : ¬ Matcher.Complete Lc ms := by
  intro complete
  have step : Lc.Step empty pBagAB bagBA empty :=
    ⟨Extends.refl _, fun _ _ => rfl, bin .bag (k .a) (k .b), rfl,
      (by decide : ceq bagComm (bin .bag (k .a) (k .b)) bagBA = true)⟩
  obtain ⟨τ, answer, -⟩ := complete (SubstEquiv.refl Lc.equivalence _) step
  have : (ms pBagAB empty bagBA).length = 0 := by decide
  rw [List.length_eq_zero_iff] at this
  rw [this] at answer
  simp at answer

/-- Make `out` when no `bag(a, b)` is present. -/
def absentAB : Transform ℕ (Tm Sig) (Pat ℕ Sig) := ⟨.cons (.absent pBagAB) .done, [.leaf .out]⟩

/-- A store with `bag(b, a)`. -/
def storeBA : Finset Occ := {(bagBA, 0)}

/-- **What breaks: a none query fires although its region is not empty modulo the theory.** -/
theorem incomplete_absence_fires :
    (∃ c, Fires Lc ms lbl storeBA absentAB c) ∧ (∃ o ∈ storeBA, Lc.Covers empty pBagAB (lbl o)) ∧
      ∀ c, ¬ Fires Lc mc lbl storeBA absentAB c := by
  refine ⟨?_, ⟨(bagBA, 0), by decide, empty, Extends.refl _, fun _ _ => rfl,
    bin .bag (k .a) (k .b), rfl, (by decide : ceq bagComm (bin .bag (k .a) (k .b)) bagBA = true)⟩,
    fun c => not_fires_of_rows (by decide) c⟩
  obtain ⟨-, -, c, fires, -⟩ := fires_of_row (L := Lc) (m := ms) (S := storeBA) (t := absentAB)
    (exists_of_not_forall (by decide))
  exact ⟨c, fires⟩

/-- Take every `bag(a, $x)`. -/
def everyTakeBagA : Transform ℕ (Tm Sig) (Pat ℕ Sig) :=
  ⟨.every (.cons (.take (.node .bag (.leaf .a) (.var 0))) .done), []⟩

/-- A store with `bag(a, b)` and `bag(b, a)`. -/
def storeABBA : Finset Occ := {(bin .bag (k .a) (k .b), 0), (bagBA, 1)}

/-- **What breaks: an `every` misses a row**, and its completeness query, computed by the same
matcher, does not see it. The complete matcher takes both. -/
theorem incomplete_every_misses_row :
    (∀ x ∈ everyTakeBagA.rows Lc ms lbl storeABBA,
      (footprintOf x.2).takes = {(bin .bag (k .a) (k .b), 0)} ∧
        ∀ r ∈ (footprintOf x.2).queries, r.seen = {(bin .bag (k .a) (k .b), 0)}) ∧
      ∀ x ∈ everyTakeBagA.rows Lc mc lbl storeABBA,
        (footprintOf x.2).takes = {(bin .bag (k .a) (k .b), 0), (bagBA, 1)} := by
  decide

/-- Read the unique `bag(a, b)`. -/
def uniqueAB : Transform ℕ (Tm Sig) (Pat ℕ Sig) :=
  ⟨.cons (.unique .read pBagAB) .done, [.leaf .out]⟩

/-- A store with `bag(a, b)` and `bag(b, a)`, two occurrences of one value modulo the theory. -/
theorem incomplete_unique_fires :
    (∃ c, Fires Lc ms lbl storeABBA uniqueAB c) ∧ ∀ c, ¬ Fires Lc mc lbl storeABBA uniqueAB c := by
  refine ⟨?_, fun c => not_fires_of_rows (by decide) c⟩
  obtain ⟨-, -, c, fires, -⟩ := fires_of_row (L := Lc) (m := ms) (S := storeABBA) (t := uniqueAB)
    (exists_of_not_forall (by decide))
  exact ⟨c, fires⟩

/-! ## A matcher that is not minimal -/

/-- `rawMatch` modulo commutativity, every answer kept. -/
abbrev mraw : Matcher ℕ (Tm Sig) (Pat ℕ Sig) := rawMatch bagComm

/-- `bag($x, $y)`. -/
def pBagXY : Pat ℕ Sig := .node .bag (.var 0) (.var 1)

/-- **`rawMatch` is not minimal**: `bag($x, $y)` against `bag(a, a)` answers twice, the minimal
matcher once. -/
theorem raw_not_minimal :
    (mraw pBagXY empty (bin .bag (k .a) (k .a))).length = 2 ∧
      (mc pBagXY empty (bin .bag (k .a) (k .a))).length = 1 ∧ ¬ Matcher.Minimal Lc mraw := by
  refine ⟨by decide, by decide, fun minimal => ?_⟩
  have pairwise := minimal pBagXY empty (bin .bag (k .a) (k .a))
  have twice : mraw pBagXY empty (bin .bag (k .a) (k .a)) =
      [Function.update (Function.update empty 0 (some (k .a))) 1 (some (k .a)),
        Function.update (Function.update empty 0 (some (k .a))) 1 (some (k .a))] := rfl
  rw [twice] at pairwise
  simp only [List.pairwise_cons, List.mem_singleton, forall_eq, List.not_mem_nil,
    IsEmpty.forall_iff, implies_true, List.Pairwise.nil, and_true] at pairwise
  exact pairwise (SubstEquiv.refl Lc.equivalence _)

/-- For every `bag($x, $y)`, make `seen($x)`. -/
def everyReadBag : Transform ℕ (Tm Sig) (Pat ℕ Sig) :=
  ⟨.every (.cons (.read pBagXY) .done), [.node .seen (.var 0) (.leaf .nil)]⟩

/-- A store with `bag(a, a)`. -/
def storeAA : Finset Occ := {(bin .bag (k .a) (k .a), 0)}

/-- **A redundant matcher double-counts**: the `every` makes its template twice. -/
theorem raw_every_makes_twice :
    (∀ x ∈ everyReadBag.rows Lc mraw lbl storeAA, (footprintOf x.2).makes = {un .seen (k .a), un .seen (k .a)}) ∧
      ∀ x ∈ everyReadBag.rows Lc mc lbl storeAA, (footprintOf x.2).makes = {un .seen (k .a)} := by
  decide

/-! ## `every (take p)` modulo a non-unitary theory -/

/-- Take every `bag($x, $y)`. -/
def everyTakeBag : Transform ℕ (Tm Sig) (Pat ℕ Sig) := ⟨.every (.cons (.take pBagXY) .done), []⟩

/-- A store with `bag(a, b)`. -/
def storeAB : Finset Occ := {(bin .bag (k .a) (k .b), 0)}

/-- **Modulo commutativity the occurrence has two rows, both take it, and the `every` is
refused.** -/
theorem everyTake_refused_modulo_comm (c : Commit Occ (Tm Sig)) :
    ¬ Fires Lc mc lbl storeAB everyTakeBag c :=
  not_fires_of_rows (by decide) c

/-- **Syntactically there is one row, and it takes the occurrence.** -/
theorem everyTake_fires_syntactic :
    ∃ x ∈ everyTakeBag.rows Ls ms lbl storeAB, (footprintOf x.2).Linear ∧
      (footprintOf x.2).takes = {(bin .bag (k .a) (k .b), 0)} :=
  exists_of_not_forall (by decide)

/-- Take the whole region of `bag($x, $y)`; the fold here ignores the bag. -/
def allTakeBag : Transform ℕ (Tm Sig) (Pat ℕ Sig) :=
  ⟨.cons (.all .take pBagXY (.var 2) fun _ => k .nil) .done, []⟩

/-- **`all take` takes the region once, modulo the theory too**, and fires to the empty store, the
`removeAll` contract. -/
theorem allTake_fires_modulo_comm :
    ∃ c, Fires Lc mc lbl storeAB allTakeBag c ∧ fire storeAB c = ∅ := by
  obtain ⟨x, member, linear, takes, makes⟩ : ∃ x ∈ allTakeBag.rows Lc mc lbl storeAB,
      (footprintOf x.2).Linear ∧ (footprintOf x.2).takes = {(bin .bag (k .a) (k .b), 0)} ∧
        (footprintOf x.2).makes = 0 := exists_of_not_forall (by decide)
  obtain ⟨c, commit⟩ := exists_isCommitOf (S := storeAB) supply (footprintOf x.2)
  refine ⟨c, ⟨x, member, linear, commit⟩, ?_⟩
  rw [fire, made_eq_empty commit makes, commit.taken, takes]
  decide

/-! ## Static independence -/

/-- Take a `tok`. -/
def takeTok : Transform ℕ (Tm Sig) (Pat ℕ Sig) := ⟨.cons (.take (.leaf .tok)) .done, []⟩
/-- Read a `lock`, make `out`. -/
def readLock : Transform ℕ (Tm Sig) (Pat ℕ Sig) := ⟨.cons (.read (.leaf .lock)) .done, [.leaf .out]⟩
/-- Read a `tok`, make `out`. -/
def readTok : Transform ℕ (Tm Sig) (Pat ℕ Sig) := ⟨.cons (.read (.leaf .tok)) .done, [.leaf .out]⟩

/-- **Positive control**: by head keys, a taker of `tok` and a reader of `lock` are apart, so every
pair of commits they fire is independent. -/
theorem takeTok_readLock_apart :
    (takeTok.static headR).Apart headR (readLock.static headR) := by
  decide

theorem takeTok_readLock_independent {S S' : Finset Occ} {c d : Commit Occ (Tm Sig)}
    (fires : Fires Lc mc lbl S takeTok c) (fires' : Fires Lc mc lbl S' readLock d)
    (freshApart : Disjoint c.made d.made) : Independent lbl c d :=
  independent_of_staticApart cmatch_sound (headKeys_sound bagComm) takeTok_readLock_apart fires
    fires' freshApart

/-- **Negative control**: a taker and a reader of `tok` are not apart. -/
theorem takeTok_readTok_not_apart :
    ¬ (takeTok.static headR).Apart headR (readTok.static headR) := by
  decide

/-- And their commits at one `tok` are not independent: the taker takes what the reader keeps. -/
theorem takeTok_readTok_dependent :
    ∃ c d, Fires Lc mc lbl oneTok takeTok c ∧ Fires Lc mc lbl oneTok readTok d ∧
      ¬ Independent lbl c d := by
  obtain ⟨x, xMember, xLinear, xTakes⟩ : ∃ x ∈ takeTok.rows Lc mc lbl oneTok,
      (footprintOf x.2).Linear ∧ (footprintOf x.2).takes = {(k .tok, 0)} :=
    exists_of_not_forall (by decide)
  obtain ⟨y, yMember, yLinear, yKeeps⟩ : ∃ y ∈ readTok.rows Lc mc lbl oneTok,
      (footprintOf y.2).Linear ∧ (footprintOf y.2).keeps = {(k .tok, 0)} :=
    exists_of_not_forall (by decide)
  obtain ⟨c, commitC⟩ := exists_isCommitOf (S := oneTok) supply (footprintOf x.2)
  obtain ⟨d, commitD⟩ := exists_isCommitOf (S := oneTok) supply (footprintOf y.2)
  refine ⟨c, d, ⟨x, xMember, xLinear, commitC⟩, ⟨y, yMember, yLinear, commitD⟩, ?_⟩
  rintro ⟨-, notSpoil, -⟩
  apply notSpoil
  left
  rw [commitC.taken, commitD.kept, xTakes, yKeeps]
  decide

/-! ## The cheapest check, from the text -/

/-- **Positive and negative controls of the text checks**: a reader of `lock` has no complete
source and takes nothing; a none query has a complete source; a taker takes. -/
theorem text_checks :
    readLock.sources.queryFree = true ∧ readLock.sources.takeFree = true ∧
      readLock.sources.keepFree = false ∧ absentAB.sources.queryFree = false ∧
        takeTok.sources.takeFree = false ∧ takeTok.sources.keepFree = true ∧
          evalStep.sources.queryFree = false := by
  decide

/-- So every commit the reader of `lock` fires is monotone, and `claims` permits exactly what
`serializable` permits for it; every commit the taker of `tok` fires needs only `snapshot`. -/
theorem readLock_takeTok_checks {S S' : Finset Occ} {c d : Commit Occ (Tm Sig)}
    (fires : Fires Lc mc lbl S readLock c) (fires' : Fires Lc mc lbl S' takeTok d) (store : Finset Occ) :
    c.Monotone ∧ (Permits lbl Mode.claims store c ↔ Permits lbl Mode.serializable store c) ∧
      (Permits lbl Mode.snapshot store d ↔ Permits lbl Mode.serializable store d) :=
  ⟨monotone_of_noTakes_noQueries (by decide) (by decide) fires,
    permits_claims_iff_of_noQueries (by decide) fires store,
    permits_snapshot_iff_of_noKeeps_noQueries (by decide) (by decide) fires' store⟩

/-! ## Positive and negative controls of the matcher conditions -/

/-- **Completeness, positive**: the commutative matcher is complete for the bag theory.
(`syntactic_not_complete_for_comm` is the negative control.) -/
theorem mc_complete : Matcher.Complete Lc mc := cmatch_complete (comm := bagComm)

/-- **Minimality, positive**: the commutative matcher gives no two equivalent answers. -/
theorem mc_minimal : Matcher.Minimal Lc mc := cmatch_minimal (comm := bagComm)

/-- The syntactic matcher with every answer given twice. -/
def answersTwice : Matcher ℕ (Tm Sig) (Pat ℕ Sig) := fun p σ t => ms p σ t ++ ms p σ t

/-- **Minimality, negative**: the diagonal's one answer, given twice, is repeated. -/
theorem answersTwice_not_minimal : ¬ Matcher.Minimal Ls answersTwice := by
  intro minimal
  obtain ⟨τ, single⟩ := List.length_eq_one_iff.mp diagonal_matches_equal
  have pairwise := minimal pDiag empty (bin .pr (k .a) (k .a))
  simp only [answersTwice, single, List.singleton_append, List.pairwise_cons, List.mem_singleton,
    forall_eq] at pairwise
  exact pairwise.1 (SubstEquiv.refl Ls.equivalence τ)

/-- A matcher that accepts every value with the substitution it was given. -/
def acceptEverything : Matcher ℕ (Tm Sig) (Pat ℕ Sig) := fun _ σ _ => [σ]

/-- **Soundness, negative**: accepting `a` for the pattern `tok` is not a step, since `tok` and `a`
differ. (`syntactic_sound_for_comm` is the positive control.) -/
theorem acceptEverything_unsound : ¬ Matcher.Sound Ls acceptEverything := by
  intro sound
  have step := sound (p := .leaf .tok) (σ := empty) (t := k .a) (τ := empty)
    (by simp [acceptEverything])
  obtain ⟨u, inst, related⟩ := step.solves
  simp only [Ls, termLayer, Pat.inst, Option.some.injEq] at inst related
  subst inst
  revert related
  decide

/-- **Monotone regions, positive**: a sound and complete matcher never answers for more values
when more variables are bound. -/
theorem mc_regionMonotone : Matcher.RegionMonotone mc :=
  Matcher.regionMonotone_of_sound_complete (cmatch_sound (comm := bagComm))
    (cmatch_complete (comm := bagComm))

/-- A matcher that answers only once variable `0` is bound. -/
def needsZero : Matcher ℕ (Tm Sig) (Pat ℕ Sig) := fun _ σ _ => if (σ 0).isSome then [σ] else []

/-- **Monotone regions, negative**: binding variable `0` lets `needsZero` answer for a value it
refused before. -/
theorem needsZero_not_regionMonotone : ¬ Matcher.RegionMonotone needsZero := by
  intro monotone
  have := monotone (σ := empty) (τ := Function.update empty 0 (some (k .a))) (p := pDiag)
    (t := k .a) (fun v t bound => by simp [empty] at bound) (by simp [Matcher.region, needsZero])
  simp [Matcher.region, needsZero, empty] at this

/-- **Extends, positive**: binding variable `0` extends the empty substitution. -/
theorem empty_extended : Extends empty (Function.update empty 0 (some (k .a))) :=
  fun v t bound => by simp [empty] at bound

/-- **Extends, negative**: the empty substitution does not extend one that binds `0`. -/
theorem bound_not_extended_by_empty : ¬ Extends (Function.update empty 0 (some (k .a))) empty :=
  fun extends_ => by simpa [empty] using extends_ 0 (k .a) (by simp)

/-- `0` bound to `bag(a, b)`. -/
def bagAB0 : Subst ℕ (Tm Sig) := Function.update empty 0 (some (bin .bag (k .a) (k .b)))

/-- `0` bound to `bag(b, a)`. -/
def bagBA0 : Subst ℕ (Tm Sig) := Function.update empty 0 (some (bin .bag (k .b) (k .a)))

/-- **Equivalent substitutions, positive**: modulo the commutativity of `bag` the two bindings are
equivalent, though different. -/
theorem bagAB0_equiv_bagBA0 : SubstEquiv Lc.E bagAB0 bagBA0 := by
  intro v
  by_cases zero : v = 0
  · subst zero
    simp only [bagAB0, bagBA0, Function.update_self]
    exact Option.Rel.some (by simp only [Lc, termLayer]; decide)
  · simp only [bagAB0, bagBA0, Function.update_of_ne zero, empty]
    exact Option.Rel.none

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources.Controls
