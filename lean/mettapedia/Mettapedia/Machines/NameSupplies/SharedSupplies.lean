import Mettapedia.Machines.NameSupplies.Pools
import Mettapedia.Machines.NameSupplies.Shares
import Mathlib.Data.Finite.Prod

/-!
# Supplies of shares and clocks

In the style of interval tree clocks (Almeida, Baquero and Fonte 2008), a supply holds a share of
the unit interval and a clock (`ShareSupply`).  A fork hands each part a piece of the share at the
same clock; a join takes the union of the two shares at the later clock; a supply's next name is its
share with its clock, and drawing advances the clock (`shareDiscipline`).

* **Disjointness and exact names.**  A pool is *well shared* (`WellShared`) when its live shares are
  normal, nonempty and pairwise disjoint, every drawn name is below the clock of every live supply
  whose share overlaps the name's share, and no name was drawn twice.  Every operation keeps a pool
  well shared (`wellShared_step`, `wellShared_run`), so the discipline is exact from every
  well-shared pool (`shares_exact`): live supplies draw distinct names (`next_names_distinct`) and a
  live supply's next name was never drawn (`next_name_fresh`).
* **Any splitter.**  The fork may cut the share by any splitter (`Splitter`) whose pieces are normal,
  nonempty, inside the share and pairwise disjoint; the invariant and exactness hold for each
  (`wellShared_run_with`, `shares_exact_with`).  `Share.piece` is the linear splitter
  (`splitDiscipline_linear`); `BalancedPieces` and `SiblingPushes` give two more.
* **Balanced fork and join return the supply** (`join_pieces`): a supply forked in two whose two
  pieces join again is the supply it was.  A computation that forks and joins in balance keeps its
  shares bounded.
* **Unbalanced forking grows the shares.**  Forking the whole interval again and again, the `k`-th
  piece forked off has `2k + 3` nodes (`forkedOff_whole`, `forkedOff_whole_size`): the shares are
  exact, so by `exact_forking_unbounded` they had to grow.
* **Control: copying is bounded but not exact.**  Handing every part the whole supply keeps every
  share the whole interval (`copy_shares_whole`) and draws a name twice (`copy_not_exact`).
-/

set_option autoImplicit false

namespace Mettapedia.Machines.NameSupplies

/-- A supply of a share of the unit interval and a clock. -/
structure ShareSupply where
  share : Share
  clock : ℕ
  deriving DecidableEq, Repr

/-- A name drawn from a share supply: the share and the clock value. -/
abbrev ShareName := Share × ℕ

/-- **The share discipline.** -/
def shareDiscipline : Discipline ShareSupply ShareName where
  draw supply := ((supply.share, supply.clock), { supply with clock := supply.clock + 1 })
  piece supply parts i := ⟨supply.share.piece parts i, supply.clock⟩
  join first second := ⟨first.share.join second.share, max first.clock second.clock⟩

/-- The whole interval at clock zero. -/
def wholeSupply : ShareSupply := ⟨.all, 0⟩

/-- **A splitter**: a way to cut a share into `k` parts, each normal and nonempty when the share
is, each inside the share, and pairwise disjoint. -/
structure Splitter where
  /-- `piece share k i`: the part of `share` for part `i` of `k`. -/
  piece : Share → ℕ → ℕ → Share
  piece_normal : ∀ {share : Share}, share.Normal → share ≠ .none → ∀ k i,
    (piece share k i).Normal ∧ piece share k i ≠ .none
  piece_owns : ∀ {share : Share} {k i : ℕ} {point : ℕ → Bool},
    (piece share k i).Owns point → share.Owns point
  pieces_disjoint : ∀ (share : Share) {k i j : ℕ}, i < k → j < k → i ≠ j →
    ¬ (piece share k i).Overlap (piece share k j)

/-- The linear splitter of `Share.piece`: the first part takes the left half, the others share
the right half. -/
def linearSplitter : Splitter :=
  ⟨Share.piece, Share.piece_normal, Share.piece_owns, Share.pieces_disjoint⟩

/-- The share discipline with the pieces of a splitter. -/
def splitDiscipline (splitter : Splitter) : Discipline ShareSupply ShareName :=
  { shareDiscipline with piece := fun supply parts i => ⟨splitter.piece supply.share parts i, supply.clock⟩ }

theorem splitDiscipline_linear : splitDiscipline linearSplitter = shareDiscipline := rfl

/-- **A well-shared pool.** -/
structure WellShared (pool : Pool ShareSupply ShareName) : Prop where
  normal : ∀ s ∈ pool.live, s.share.Normal ∧ s.share ≠ .none
  disjoint : ∀ s t, {s, t} ≤ pool.live → ¬ s.share.Overlap t.share
  dominated : ∀ name ∈ pool.drawn, ∀ s ∈ pool.live, s.share.Overlap name.1 → name.2 < s.clock
  fresh : pool.drawn.Nodup

theorem wellShared_single (supply : ShareSupply) (normal : supply.share.Normal)
    (nonempty : supply.share ≠ .none) : WellShared ⟨{supply}, []⟩ where
  normal s member := by
    rw [Multiset.mem_singleton] at member
    subst member
    exact ⟨normal, nonempty⟩
  disjoint s t pair := by
    have := Multiset.card_le_card pair
    simp at this
  dominated name member := by simp at member
  fresh := List.nodup_nil

theorem wellShared_whole : WellShared ⟨{wholeSupply}, []⟩ :=
  wellShared_single _ trivial nofun

private theorem mem_of_mem_sub {live removed : Multiset ShareSupply} {s : ShareSupply}
    (member : s ∈ live - removed) : s ∈ live :=
  Multiset.mem_of_le (Multiset.sub_le_self _ _) member

private theorem mem_pieces (splitter : Splitter) {supply piece : ShareSupply} {parts : ℕ}
    (member : piece ∈ (splitDiscipline splitter).pieces supply parts) :
    ∃ i < parts, piece = ⟨splitter.piece supply.share parts i, supply.clock⟩ := by
  obtain ⟨i, below, rfl⟩ := List.mem_map.mp member
  exact ⟨i, List.mem_range.mp below, rfl⟩

private theorem pieces_pairwise (splitter : Splitter) (supply : ShareSupply) (parts : ℕ) :
    ((splitDiscipline splitter).pieces supply parts).Pairwise
      fun s t => ¬ s.share.Overlap t.share := by
  rw [List.pairwise_iff_getElem]
  intro i j iBelow jBelow before
  simp only [Discipline.pieces, List.length_map, List.length_range] at iBelow jBelow
  simp only [Discipline.pieces, List.getElem_map, List.getElem_range, splitDiscipline]
  exact splitter.pieces_disjoint _ iBelow jBelow (by omega)

private theorem wellShared_fork (splitter : Splitter) (pool : Pool ShareSupply ShareName)
    (shared : WellShared pool) (supply : ShareSupply) (parts : ℕ) (present : supply ∈ pool.live) :
    WellShared (pool.step (splitDiscipline splitter) (.fork supply parts)) := by
  obtain ⟨normal, nonempty⟩ := shared.normal supply present
  have rest : pool.live - {supply} = pool.live.erase supply := Multiset.sub_singleton _ _
  have overlapOfPiece : ∀ {i : ℕ} {other : Share},
      (splitter.piece supply.share parts i).Overlap other → supply.share.Overlap other :=
    fun ⟨point, inPiece, inOther⟩ => ⟨point, splitter.piece_owns inPiece, inOther⟩
  have crossing : ∀ p ∈ (splitDiscipline splitter).pieces supply parts,
      ∀ u ∈ pool.live - {supply}, ¬ p.share.Overlap u.share := by
    intro p member u other overlap
    obtain ⟨i, -, rfl⟩ := mem_pieces splitter member
    rw [rest] at other
    exact shared.disjoint _ _ (pair_of_mem_erase present other) (overlapOfPiece overlap)
  refine ⟨?_, ?_, ?_, by simpa [Pool.step, Operation.names] using shared.fresh⟩
  · intro s member
    rcases Multiset.mem_add.mp member with piece | other
    · obtain ⟨i, -, rfl⟩ := mem_pieces splitter (Multiset.mem_coe.mp piece)
      exact splitter.piece_normal normal nonempty _ _
    · exact shared.normal s (mem_of_mem_sub other)
  · intro s t pair
    rcases pair_le_add pair with bothPieces | bothOther | ⟨piece, other⟩ | ⟨piece, other⟩
    · exact pair_of_pairwise (fun h overlap => h overlap.symm)
        (pieces_pairwise splitter supply parts) bothPieces
    · exact shared.disjoint s t (bothOther.trans (Multiset.sub_le_self _ _))
    · exact crossing s (Multiset.mem_coe.mp piece) t other
    · exact fun overlap => crossing t (Multiset.mem_coe.mp piece) s other overlap.symm
  · intro name member s live overlap
    simp only [Pool.step, Operation.names, List.append_nil] at member
    rcases Multiset.mem_add.mp live with piece | other
    · obtain ⟨i, -, rfl⟩ := mem_pieces splitter (Multiset.mem_coe.mp piece)
      exact shared.dominated name member supply present (overlapOfPiece overlap)
    · exact shared.dominated name member s (mem_of_mem_sub other) overlap

private theorem wellShared_join (pool : Pool ShareSupply ShareName) (shared : WellShared pool)
    (first second : ShareSupply) (present : {first, second} ≤ pool.live) :
    WellShared (pool.step shareDiscipline (.join first second)) := by
  have firstLive : first ∈ pool.live := Multiset.mem_of_le present (by simp)
  have secondLive : second ∈ pool.live := Multiset.mem_of_le present (by simp)
  obtain ⟨firstNormal, firstNonempty⟩ := shared.normal first firstLive
  obtain ⟨secondNormal, -⟩ := shared.normal second secondLive
  have joined : ∀ u ∈ pool.live - {first, second},
      ¬ (first.share.join second.share).Overlap u.share := by
    intro u member overlap
    obtain ⟨firstPair, secondPair⟩ := pairs_of_mem_sub present member
    rcases (Share.overlap_join _ _ _).mp overlap with fromFirst | fromSecond
    · exact shared.disjoint _ _ firstPair fromFirst
    · exact shared.disjoint _ _ secondPair fromSecond
  have live : (pool.step shareDiscipline (.join first second)).live =
      ⟨first.share.join second.share, max first.clock second.clock⟩ ::ₘ
        (pool.live - {first, second}) := by
    simp [Pool.step, Operation.produced, Operation.consumed, shareDiscipline]
  refine ⟨?_, ?_, ?_, by simpa [Pool.step, Operation.names] using shared.fresh⟩
  · rw [live]
    intro s member
    rcases Multiset.mem_cons.mp member with rfl | other
    · exact ⟨Share.normal_join firstNormal secondNormal,
        Share.join_ne_none firstNormal firstNonempty⟩
    · exact shared.normal s (mem_of_mem_sub other)
  · rw [live]
    intro s t pair
    rcases pair_le_cons pair with other | ⟨rfl, inOther⟩ | ⟨rfl, inOther⟩
    · exact shared.disjoint s t (other.trans (Multiset.sub_le_self _ _))
    · exact joined t inOther
    · exact fun overlap => joined s inOther overlap.symm
  · rw [live]
    intro name member s isLive overlap
    simp only [Pool.step, Operation.names, List.append_nil] at member
    rcases Multiset.mem_cons.mp isLive with rfl | other
    · rcases (Share.overlap_join _ _ _).mp overlap with fromFirst | fromSecond
      · exact lt_max_of_lt_left (shared.dominated name member first firstLive fromFirst)
      · exact lt_max_of_lt_right (shared.dominated name member second secondLive fromSecond)
    · exact shared.dominated name member s (mem_of_mem_sub other) overlap

private theorem wellShared_release (pool : Pool ShareSupply ShareName) (shared : WellShared pool)
    (supply : ShareSupply) : WellShared (pool.step shareDiscipline (.release supply)) := by
  have live : (pool.step shareDiscipline (.release supply)).live = pool.live - {supply} := by
    simp [Pool.step, Operation.produced, Operation.consumed]
  refine ⟨?_, ?_, ?_, by simpa [Pool.step, Operation.names] using shared.fresh⟩
  · rw [live]; exact fun s member => shared.normal s (mem_of_mem_sub member)
  · rw [live]; exact fun s t pair => shared.disjoint s t (pair.trans (Multiset.sub_le_self _ _))
  · rw [live]
    intro name member s isLive
    simp only [Pool.step, Operation.names, List.append_nil] at member
    exact shared.dominated name member s (mem_of_mem_sub isLive)

private theorem wellShared_draw (pool : Pool ShareSupply ShareName) (shared : WellShared pool)
    (supply : ShareSupply) (present : supply ∈ pool.live) :
    WellShared (pool.step shareDiscipline (.draw supply)) := by
  obtain ⟨normal, nonempty⟩ := shared.normal supply present
  have rest : pool.live - {supply} = pool.live.erase supply := Multiset.sub_singleton _ _
  have others : ∀ u ∈ pool.live - {supply}, ¬ supply.share.Overlap u.share := by
    intro u other
    rw [rest] at other
    exact shared.disjoint _ _ (pair_of_mem_erase present other)
  have live : (pool.step shareDiscipline (.draw supply)).live =
      ⟨supply.share, supply.clock + 1⟩ ::ₘ (pool.live - {supply}) := by
    simp [Pool.step, Operation.produced, Operation.consumed, shareDiscipline]
  have drawn : (pool.step shareDiscipline (.draw supply)).drawn =
      pool.drawn ++ [(supply.share, supply.clock)] := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [live]
    intro s member
    rcases Multiset.mem_cons.mp member with rfl | other
    · exact ⟨normal, nonempty⟩
    · exact shared.normal s (mem_of_mem_sub other)
  · rw [live]
    intro s t pair
    rcases pair_le_cons pair with other | ⟨rfl, inOther⟩ | ⟨rfl, inOther⟩
    · exact shared.disjoint s t (other.trans (Multiset.sub_le_self _ _))
    · exact others t inOther
    · exact fun overlap => others s inOther overlap.symm
  · rw [live, drawn]
    intro name member s isLive overlap
    simp only [List.mem_append, List.mem_singleton] at member
    rcases Multiset.mem_cons.mp isLive with rfl | other
    · rcases member with old | rfl
      · exact Nat.lt_succ_of_lt (shared.dominated name old supply present overlap)
      · exact Nat.lt_succ_self _
    · rcases member with old | rfl
      · exact shared.dominated name old s (mem_of_mem_sub other) overlap
      · exact absurd overlap.symm (others s other)
  · rw [drawn]
    refine List.nodup_append.mpr ⟨shared.fresh, List.nodup_singleton _, ?_⟩
    intro name old other otherMember same
    rw [List.mem_singleton] at otherMember
    subst otherMember
    subst same
    exact Nat.lt_irrefl _
      (shared.dominated _ old supply present (Share.overlap_self normal nonempty))

/-- **Every operation keeps a pool well shared**, for the share discipline with any splitter. -/
theorem wellShared_step_with (splitter : Splitter) (pool : Pool ShareSupply ShareName)
    (shared : WellShared pool) (operation : Operation ShareSupply)
    (enabled : operation.Enabled pool.live) :
    WellShared (pool.step (splitDiscipline splitter) operation) := by
  cases operation with
  | fork supply parts =>
      exact wellShared_fork splitter pool shared supply parts (Multiset.singleton_le.mp enabled)
  | join first second => exact wellShared_join pool shared first second enabled
  | release supply => exact wellShared_release pool shared supply
  | draw supply => exact wellShared_draw pool shared supply (Multiset.singleton_le.mp enabled)

/-- **Every valid run keeps a pool well shared**, for the share discipline with any splitter. -/
theorem wellShared_run_with (splitter : Splitter) (pool : Pool ShareSupply ShareName)
    (shared : WellShared pool) (operations : List (Operation ShareSupply))
    (valid : Pool.Valid (splitDiscipline splitter) pool operations) :
    WellShared (pool.run (splitDiscipline splitter) operations) := by
  induction operations generalizing pool with
  | nil => exact shared
  | cons operation rest ih =>
      exact ih _ (wellShared_step_with splitter pool shared operation valid.1) valid.2

/-- **Exact names with any splitter**: from a well-shared pool, no valid run draws a name twice. -/
theorem shares_exact_with (splitter : Splitter) (pool : Pool ShareSupply ShareName)
    (shared : WellShared pool) : Exact (splitDiscipline splitter) pool :=
  fun operations valid => (wellShared_run_with splitter pool shared operations valid).fresh

/-- **Every operation keeps a pool well shared.** -/
theorem wellShared_step (pool : Pool ShareSupply ShareName) (shared : WellShared pool)
    (operation : Operation ShareSupply) (enabled : operation.Enabled pool.live) :
    WellShared (pool.step shareDiscipline operation) :=
  wellShared_step_with linearSplitter pool shared operation enabled

/-- **Every valid run keeps a pool well shared.** -/
theorem wellShared_run (pool : Pool ShareSupply ShareName) (shared : WellShared pool)
    (operations : List (Operation ShareSupply)) (valid : Pool.Valid shareDiscipline pool operations) :
    WellShared (pool.run shareDiscipline operations) :=
  wellShared_run_with linearSplitter pool shared operations valid

/-- **Exact names**: from a well-shared pool, no valid run draws a name twice. -/
theorem shares_exact (pool : Pool ShareSupply ShareName) (shared : WellShared pool) :
    Exact shareDiscipline pool :=
  shares_exact_with linearSplitter pool shared

/-- **Live supplies draw distinct names.** -/
theorem next_names_distinct {pool : Pool ShareSupply ShareName} (shared : WellShared pool)
    {s t : ShareSupply} (pair : {s, t} ≤ pool.live) :
    (shareDiscipline.draw s).1 ≠ (shareDiscipline.draw t).1 := by
  intro same
  have shares : s.share = t.share := congrArg Prod.fst same
  obtain ⟨normal, nonempty⟩ := shared.normal s (Multiset.mem_of_le pair (by simp))
  exact shared.disjoint s t pair (shares ▸ Share.overlap_self normal nonempty)

/-- **A live supply's next name was never drawn.** -/
theorem next_name_fresh {pool : Pool ShareSupply ShareName} (shared : WellShared pool)
    {s : ShareSupply} (live : s ∈ pool.live) : (shareDiscipline.draw s).1 ∉ pool.drawn := by
  intro old
  obtain ⟨normal, nonempty⟩ := shared.normal s live
  exact Nat.lt_irrefl _ (shared.dominated _ old s live (Share.overlap_self normal nonempty))

/-! ## Balanced and unbalanced forking -/

/-- **Balanced fork and join return the supply.** -/
theorem join_pieces {supply : ShareSupply} (normal : supply.share.Normal) :
    shareDiscipline.join (shareDiscipline.piece supply 2 0) (shareDiscipline.piece supply 2 1) =
      supply := by
  simp only [shareDiscipline, max_self]
  rw [show supply.share.piece 2 0 = (supply.share.split).1 from rfl,
    show supply.share.piece 2 1 = (supply.share.split).2 from rfl, Share.join_split normal]

/-- `k` left steps down from a share: `node (… (node share none) …) none`. -/
def leftward : ℕ → Share → Share
  | 0, share => share
  | k + 1, share => .node (leftward k share) .none

theorem leftward_ne_none (k : ℕ) {share : Share} (nonempty : share ≠ .none) :
    leftward k share ≠ .none := by
  cases k with
  | zero => exact nonempty
  | succ k => exact nofun

theorem leftward_size (k : ℕ) (share : Share) : (leftward k share).size = share.size + 2 * k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [leftward, Share.size, ih]; omega

private theorem split_leftward (k : ℕ) :
    (leftward k .all).split = (leftward (k + 1) .all, leftward k (.node .none .all)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have notNone := leftward_ne_none k (share := .all) nofun
      have step : (Share.node (leftward k .all) .none).split =
          (.node (leftward k .all).split.1 .none, .node (leftward k .all).split.2 .none) := by
        cases kStep : leftward k .all with
        | none => exact absurd kStep notNone
        | all => rfl
        | node l r => rfl
      rw [leftward, step, ih]
      rfl

/-- **The pieces forked off the whole interval.** -/
theorem forkedOff_whole (k : ℕ) :
    kept shareDiscipline wholeSupply k = ⟨leftward k .all, 0⟩ ∧
      forkedOff shareDiscipline wholeSupply k = ⟨leftward k (.node .none .all), 0⟩ := by
  induction k with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
      have keptNext : kept shareDiscipline wholeSupply (k + 1) = ⟨leftward (k + 1) .all, 0⟩ := by
        rw [kept, ih.1]
        simp only [shareDiscipline]
        rw [show (leftward k Share.all).piece 2 0 = ((leftward k Share.all).split).1 from rfl,
          split_leftward]
      refine ⟨keptNext, ?_⟩
      rw [forkedOff, keptNext]
      simp only [shareDiscipline]
      rw [show (leftward (k + 1) Share.all).piece 2 1 = ((leftward (k + 1) Share.all).split).2 from rfl,
        split_leftward]

/-- **The `k`-th piece forked off the whole interval has `2k + 3` nodes.** -/
theorem forkedOff_whole_size (k : ℕ) :
    (forkedOff shareDiscipline wholeSupply k).share.size = 2 * k + 3 := by
  rw [(forkedOff_whole k).2, leftward_size]
  simp [Share.size]
  omega

/-- The shares on the whole interval are exact, so `exact_forking_unbounded` applies. -/
theorem shares_forking_unbounded (bound : ℕ) :
    ∃ k, ∃ operations : List (Operation ShareSupply),
      operations <+: eagerForks shareDiscipline wholeSupply k ∧
      ∃ s ∈ ((Pool.mk {wholeSupply} [] : Pool ShareSupply ShareName).run shareDiscipline
        operations).live, bound < s.share.size := by
  refine ⟨bound + 1, _,
    List.prefix_append _ [Operation.release (forkedOff shareDiscipline wholeSupply bound)],
    _, eager_forkedOff_live shareDiscipline wholeSupply bound, ?_⟩
  rw [forkedOff_whole_size]
  omega

/-- The size of a supply: the nodes of its share and its clock. -/
def ShareSupply.size (supply : ShareSupply) : ℕ := supply.share.size + supply.clock

/-- **Supplies of bounded size are finitely many.** -/
theorem finite_supply_size_le (bound : ℕ) : {supply : ShareSupply | supply.size ≤ bound}.Finite := by
  refine ((Share.finite_size_le bound).prod (Set.finite_le_nat bound)).image
    (fun pair => (⟨pair.1, pair.2⟩ : ShareSupply)) |>.subset ?_
  intro supply small
  simp only [Set.mem_ofPred_eq, ShareSupply.size] at small
  exact ⟨(supply.share, supply.clock), ⟨show supply.share.size ≤ bound by omega,
    show supply.clock ≤ bound by omega⟩, rfl⟩

/-- **The abstract conflict, for shares**: the share discipline is exact from the whole supply, so
`exact_forking_unbounded` applies to it. -/
theorem share_supplies_unbounded :
    (∀ k (operations : List (Operation ShareSupply)),
      operations <+: eagerForks shareDiscipline wholeSupply k →
        ((Pool.mk {wholeSupply} [] : Pool ShareSupply ShareName).run shareDiscipline
          operations).live.card ≤ 2) ∧
    ∀ bound, ∃ k, ∃ operations : List (Operation ShareSupply),
      operations <+: eagerForks shareDiscipline wholeSupply k ∧
      ∃ s ∈ ((Pool.mk {wholeSupply} [] : Pool ShareSupply ShareName).run shareDiscipline
        operations).live, bound < s.size :=
  exact_forking_unbounded shareDiscipline wholeSupply (shares_exact _ wellShared_whole)
    ShareSupply.size finite_supply_size_le

/-! ## Control: copying is bounded but not exact -/

/-- Copying: every part of a fork receives the whole supply. -/
def copyDiscipline : Discipline ShareSupply ShareName :=
  { shareDiscipline with piece := fun supply _ _ => supply }

/-- **Copying keeps every share the whole interval**, along every valid run from the whole
supply. -/
theorem copy_shares_whole (operations : List (Operation ShareSupply))
    (valid : Pool.Valid copyDiscipline (Pool.mk {wholeSupply} [] : Pool ShareSupply ShareName)
      operations) :
    ∀ s ∈ ((Pool.mk {wholeSupply} [] : Pool ShareSupply ShareName).run copyDiscipline
      operations).live, s.share = .all := by
  suffices ∀ (pool : Pool ShareSupply ShareName), (∀ s ∈ pool.live, s.share = .all) →
      Pool.Valid copyDiscipline pool operations →
        ∀ s ∈ (pool.run copyDiscipline operations).live, s.share = .all from
    this _ (fun s member => by rw [Multiset.mem_singleton.mp member]; rfl) valid
  clear valid
  induction operations with
  | nil => exact fun pool whole _ => whole
  | cons operation rest ih =>
      intro pool whole valid
      apply ih _ _ valid.2
      intro s member
      rcases Multiset.mem_add.mp member with made | other
      · cases operation with
        | fork supply parts =>
            obtain ⟨i, -, rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp made)
            exact whole supply (Multiset.singleton_le.mp valid.1)
        | join first second =>
            rw [Operation.produced, Multiset.mem_singleton] at made
            subst made
            simp [copyDiscipline, shareDiscipline,
              whole first (Multiset.mem_of_le valid.1 (by simp [Operation.consumed]))]
        | release supply => simp [Operation.produced] at made
        | draw supply =>
            rw [Operation.produced, Multiset.mem_singleton] at made
            subst made
            exact whole supply (Multiset.singleton_le.mp valid.1)
      · exact whole s (Multiset.mem_of_le (Multiset.sub_le_self _ _) other)

/-- **Copying is not exact**: the two parts of a fork draw the same name. -/
theorem copy_not_exact :
    ¬ Exact copyDiscipline (Pool.mk {wholeSupply} [] : Pool ShareSupply ShareName) := by
  intro exact
  have valid : Pool.Valid copyDiscipline (Pool.mk {wholeSupply} [] : Pool ShareSupply ShareName)
      [.fork wholeSupply 2, .draw wholeSupply, .draw wholeSupply] := by
    refine ⟨by simp [Operation.Enabled, Operation.consumed], ?_, ?_, trivial⟩ <;>
      simp [Pool.step, Operation.Enabled, Operation.consumed, Operation.produced,
        Discipline.pieces, copyDiscipline, shareDiscipline, List.range_succ, wholeSupply]
  have := exact _ valid
  simp [Pool.step, Operation.names, copyDiscipline, shareDiscipline] at this

end Mettapedia.Machines.NameSupplies
