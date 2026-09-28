import Mettapedia.GSLT.LanguageDef.NativeControlOnce

/-!
# A delimited cut over tier frames and host choices

The open-equation cursor and the PeTTa machine hold alternatives in separate,
bottom-indexed arrays. A host answer can leave a borrowed answer choice with an
`open_base`: it resumes only the tier interval above that base. Host alternatives
lie between these segment markers. The owning answer choice lies below every
borrowed segment of its cursor.

This model decodes that layout by following the host stack from its newest entry
and draining the tier intervals named by its segment markers. It does not flatten
the two physical stacks by concatenation. Administrative tier frames have no
alternative observation. A delimiter records both array heights; successful
commitment removes both suffixes, without restoring the selected logical context
or the performed world. `cut_refines_once` proves the resulting step is exactly
the existing `NativeControlOnce` commit, and `cut_reflects_once` states its
no-invention direction.

Interval bounds alone do not establish faithful decoding. `WellFormed` also
requires one base-zero owner below all borrowers, with no cursor segment below
that owner. It proves complete frame-index coverage, host order, and occurrence
multiplicity. `faithful_cut_refines_once` combines this representation contract
with the cut step. This is a model of one open cursor and the host choices
interleaved with it, not all C cursor heaps.
Other host work is an opaque alternative. It does not verify C pointers, arena
reclamation, goal/obligation trails, effectful destructor or transaction cleanup,
exceptions, or the compiler recording the right delimiter. Preserving `world`
here describes administrative cancellation; any observable cleanup needs its
own specified transition. In particular `oem_settle` restores branch state after an
answer has been exported; a selected answer must already have independent valid
storage before those operations or cancellation. Keeping its mathematical value
here is not a proof that an `Atom *` remains live. Owning versus borrowed markers
are retained, but freeing the owning cursor requires a separate ownership proof.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeControlTwoStackCut

open Mettapedia.GSLT.LanguageDef.HostGoals.Scopes

/-- The owning host choice closes its cursor; borrowed segment choices do not. -/
inductive Ownership where
  | owning
  | borrowed
  deriving DecidableEq, Repr

/-- A segment drains its cursor's frames down to `base`. A delimiter is an
administrative host choice, such as `PETTA_CHOICE_ONCE`. -/
inductive HostFrame (Task : Type) where
  | alternative (task : Task)
  | segment (ownership : Ownership) (base : Nat)
  | delimiter
  deriving DecidableEq, Repr

/-- Both arrays use the C convention: oldest entries first. A `none` tier frame
is an administrative host/resume boundary, rather than an answer alternative. -/
structure Layout (Task : Type) where
  tier : List (Option Task)
  host : List (HostFrame Task)
  deriving DecidableEq, Repr

/-- The heights captured on entry to the specified logical delimiter. The type
alone cannot establish that capture or identify a stack lifetime: a concrete
implementation must pair these heights with its epoch or linear ownership token.
Later range/kind checks cannot reconstruct this entry-time authority. -/
structure Mark where
  tierHeight : Nat
  hostHeight : Nat
  deriving DecidableEq, Repr

variable {Task : Type}

/-- The alternatives in the half-open tier interval `[lower, upper)`, newest
first. No conversion to a set discards occurrence multiplicity. -/
def slice (tier : List (Option Task)) (lower upper : Nat) : List Task :=
  (((tier.take upper).drop lower).reverse).filterMap id

/-- Decode host entries in newest-first order. Segment markers, rather than a
second scheduler, determine where a native interval enters the frontier. -/
def decodeAt (tier : List (Option Task)) : Nat → List (HostFrame Task) → List Task
  | _, [] => []
  | upper, .alternative task :: rest => task :: decodeAt tier upper rest
  | upper, .segment _ base :: rest => slice tier base upper ++ decodeAt tier base rest
  | upper, .delimiter :: rest => decodeAt tier upper rest

/-- The tier boundary left after traversing a host segment. -/
def bottom : Nat → List (HostFrame Task) → Nat
  | upper, [] => upper
  | upper, .alternative _ :: rest => bottom upper rest
  | _, .segment _ base :: rest => bottom base rest
  | upper, .delimiter :: rest => bottom upper rest

theorem decodeAt_append (tier : List (Option Task)) (upper : Nat)
    (first second : List (HostFrame Task)) :
    decodeAt tier upper (first ++ second) =
      decodeAt tier upper first ++ decodeAt tier (bottom upper first) second := by
  induction first generalizing upper with
  | nil => rfl
  | cons frame entries ih =>
      cases frame with
      | alternative => simp only [List.cons_append, decodeAt, bottom, ih]
      | delimiter => exact ih upper
      | segment ownership base =>
          simp only [List.cons_append, decodeAt, bottom, ih, List.append_assoc]

def Layout.pending (layout : Layout Task) : List Task :=
  decodeAt layout.tier layout.tier.length layout.host.reverse

/-- The indexed physical operation being justified. No frame checkpoint is
restored: cut cancels alternatives instead of backtracking into one. -/
def truncate (mark : Mark) (layout : Layout Task) : Layout Task :=
  ⟨layout.tier.take mark.tierHeight, layout.host.take mark.hostHeight⟩

/-- Every marker of a new host suffix names an interval at or above `floor`.
The bound decreases monotonically as older markers are traversed. -/
inductive Above (floor : Nat) : Nat → List (HostFrame Task) → Prop where
  | nil {upper : Nat} : floor ≤ upper → Above floor upper []
  | alternative {upper : Nat} {task : Task} {rest : List (HostFrame Task)} :
      Above floor upper rest → Above floor upper (.alternative task :: rest)
  | segment {upper base : Nat} {ownership : Ownership} {rest : List (HostFrame Task)} :
      floor ≤ base → base ≤ upper → Above floor base rest →
        Above floor upper (.segment ownership base :: rest)
  | delimiter {upper : Nat} {rest : List (HostFrame Task)} :
      Above floor upper rest → Above floor upper (.delimiter :: rest)

/-- Below this cursor's owner, host choices contain no segments of this cursor.
They may contain arbitrary opaque work, including work owning other cursors. -/
inductive HostOnly : List (HostFrame Task) → Prop where
  | nil : HostOnly []
  | alternative {task : Task} {rest : List (HostFrame Task)} :
      HostOnly rest → HostOnly (.alternative task :: rest)
  | delimiter {rest : List (HostFrame Task)} :
      HostOnly rest → HostOnly (.delimiter :: rest)

/-- Exactly one owning marker is present, at base zero. Every borrowed marker
is above that owner. This condition is independent of interval monotonicity. -/
inductive OwnerChain : List (HostFrame Task) → Prop where
  | owner {rest : List (HostFrame Task)} :
      HostOnly rest → OwnerChain (.segment .owning 0 :: rest)
  | alternative {task : Task} {rest : List (HostFrame Task)} :
      OwnerChain rest → OwnerChain (.alternative task :: rest)
  | borrowed {base : Nat} {rest : List (HostFrame Task)} :
      OwnerChain rest → OwnerChain (.segment .borrowed base :: rest)
  | delimiter {rest : List (HostFrame Task)} :
      OwnerChain rest → OwnerChain (.delimiter :: rest)

/-- Faithfulness requires ownership and coverage as well as decreasing marker
indices. `Above` alone deliberately expresses only the interval bound. -/
structure WellFormed (layout : Layout Task) : Prop where
  bounded : Above 0 layout.tier.length layout.host.reverse
  owned : OwnerChain layout.host.reverse

theorem HostOnly.bottom {entries : List (HostFrame Task)} (clean : HostOnly entries)
    (upper : Nat) : bottom upper entries = upper := by
  induction clean with
  | nil => rfl
  | alternative clean ih => exact ih
  | delimiter clean ih => exact ih

theorem HostOnly.bounded {entries : List (HostFrame Task)} (clean : HostOnly entries) :
    Above 0 0 entries := by
  induction clean with
  | nil => exact .nil (Nat.le_refl 0)
  | alternative clean ih => exact .alternative ih
  | delimiter clean ih => exact .delimiter ih

theorem OwnerChain.drains {entries : List (HostFrame Task)} (owned : OwnerChain entries)
    (upper : Nat) : bottom upper entries = 0 := by
  induction owned generalizing upper with
  | owner clean => exact clean.bottom 0
  | alternative owned ih => exact ih upper
  | borrowed owned ih => exact ih _
  | delimiter owned ih => exact ih upper

theorem WellFormed.drains {layout : Layout Task} (wellFormed : WellFormed layout) :
    bottom layout.tier.length layout.host.reverse = 0 :=
  wellFormed.owned.drains _

theorem HostOnly.append {first second : List (HostFrame Task)}
    (left : HostOnly first) (right : HostOnly second) : HostOnly (first ++ second) := by
  induction left with
  | nil => exact right
  | alternative left ih => exact .alternative ih
  | delimiter left ih => exact .delimiter ih

theorem OwnerChain.append_hostOnly {first second : List (HostFrame Task)}
    (owned : OwnerChain first) (clean : HostOnly second) : OwnerChain (first ++ second) := by
  induction owned with
  | owner lower => exact .owner (lower.append clean)
  | alternative owned ih => exact .alternative ih
  | borrowed owned ih => exact .borrowed ih
  | delimiter owned ih => exact .delimiter ih

theorem Above.append {floor upper : Nat} {first second : List (HostFrame Task)}
    (left : Above floor upper first)
    (right : Above floor (bottom upper first) second) : Above floor upper (first ++ second) := by
  induction left with
  | nil => exact right
  | alternative left ih => exact .alternative (ih right)
  | segment low high left ih => exact .segment low high (ih right)
  | delimiter left ih => exact .delimiter (ih right)

/-- A whole-owner delimiter has a faithful combined layout when its inner
intervals are bounded and the outer host prefix refers to none of this cursor's
native frames. Coverage is derived from the owner, not assumed as an equation. -/
theorem owner_layout_wellFormed (tier : List (Option Task))
    (inside outside : List (HostFrame Task))
    (inner : Above 0 tier.length inside) (owned : OwnerChain inside)
    (outer : HostOnly outside) :
    WellFormed ⟨tier, outside.reverse ++ inside.reverse⟩ := by
  constructor
  · simp only [List.reverse_append, List.reverse_reverse]
    apply inner.append
    simpa only [owned.drains] using outer.bounded
  · simp only [List.reverse_append, List.reverse_reverse]
    exact owned.append_hostOnly outer

/-- Decode only the delimited suffix. Any final unassigned native interval
stops at the delimiter's tier height, not at the cursor's owner. -/
def pendingAbove (floor : Nat) (tier : List (Option Task)) :
    Nat → List (HostFrame Task) → List Task
  | upper, [] => slice tier floor upper
  | upper, .alternative task :: rest => task :: pendingAbove floor tier upper rest
  | upper, .segment _ base :: rest => slice tier base upper ++ pendingAbove floor tier base rest
  | upper, .delimiter :: rest => pendingAbove floor tier upper rest

/-- A physical slice splits at an intermediate height in stack order. -/
theorem slice_split (tier : List (Option Task)) {lower middle upper : Nat}
    (lower_le : lower ≤ middle) (middle_le : middle ≤ upper) :
    slice tier lower upper = slice tier middle upper ++ slice tier lower middle := by
  have split : (tier.take upper).drop lower =
      (tier.take middle).drop lower ++ (tier.take upper).drop middle := by
    rw [← List.take_append_drop (middle - lower) ((tier.take upper).drop lower)]
    simp only [List.take_drop, List.drop_drop]
    have h : lower + (middle - lower) = middle := Nat.add_sub_of_le lower_le
    rw [h, List.take_take, Nat.min_eq_left middle_le]
  simp only [slice, split, List.reverse_append, List.filterMap_append]

/-- Native projection of the interval walk. Its payload is independent of the
host task type, allowing physical frame indices themselves to be observed. -/
def nativeOnly {HostTask : Type} (tier : List (Option Task)) :
    Nat → List (HostFrame HostTask) → List Task
  | _, [] => []
  | upper, .alternative _ :: rest => nativeOnly tier upper rest
  | upper, .segment _ base :: rest => slice tier base upper ++ nativeOnly tier base rest
  | upper, .delimiter :: rest => nativeOnly tier upper rest

/-- Host alternatives in their physical newest-first order. -/
def hostOnly : List (HostFrame Task) → List Task
  | [] => []
  | .alternative task :: rest => task :: hostOnly rest
  | .segment _ _ :: rest => hostOnly rest
  | .delimiter :: rest => hostOnly rest

/-- Decreasing intervals partition a native prefix. The final unvisited prefix
is explicit, so missing owners cannot silently count as complete coverage. -/
theorem nativeOnly_partition {HostTask : Type} (tier : List (Option Task))
    {floor upper : Nat} {entries : List (HostFrame HostTask)}
    (bounded : Above floor upper entries) :
    nativeOnly tier upper entries ++ slice tier floor (bottom upper entries) =
      slice tier floor upper := by
  induction bounded with
  | nil => rfl
  | alternative bounded ih => exact ih
  | @segment upper base ownership rest floor_le base_le bounded ih =>
      simp only [nativeOnly, bottom, List.append_assoc]
      rw [ih, ← slice_split tier floor_le base_le]
  | delimiter bounded ih => exact ih

theorem nativeOnly_complete {HostTask : Type} (tier : List (Option Task))
    {upper : Nat} {entries : List (HostFrame HostTask)}
    (bounded : Above 0 upper entries) (drained : bottom upper entries = 0) :
    nativeOnly tier upper entries = slice tier 0 upper := by
  have partition := nativeOnly_partition tier bounded
  simpa [drained, slice] using partition

/-- Each physical native frame index is visited once, in descending order,
including administrative frames that carry no answer alternative. -/
theorem WellFormed.native_index_coverage {layout : Layout Task}
    (wellFormed : WellFormed layout) :
    nativeOnly ((List.range layout.tier.length).map some) layout.tier.length
      layout.host.reverse = (List.range layout.tier.length).reverse := by
  rw [nativeOnly_complete _ wellFormed.bounded wellFormed.drains]
  simp [slice, ← List.map_take]

/-- The decoder has exactly the native and host occurrences, including repeated
equal task values. Interval faithfulness is supplied separately below. -/
theorem decodeAt_perm (tier : List (Option Task)) (upper : Nat)
    (entries : List (HostFrame Task)) :
    (decodeAt tier upper entries).Perm
      (nativeOnly tier upper entries ++ hostOnly entries) := by
  induction entries generalizing upper with
  | nil => exact .refl []
  | cons frame entries ih =>
      cases frame with
      | alternative task =>
          exact (List.Perm.cons task (ih upper)).trans List.perm_middle.symm
      | segment ownership base =>
          simpa only [decodeAt, nativeOnly, hostOnly, List.append_assoc] using
            (ih base).append_left (slice tier base upper)
      | delimiter => exact ih upper

/-- Host residual choices retain their relative order through interval decoding. -/
theorem hostOnly_sublist (tier : List (Option Task)) (upper : Nat)
    (entries : List (HostFrame Task)) :
    (hostOnly entries).Sublist (decodeAt tier upper entries) := by
  induction entries generalizing upper with
  | nil => exact .refl []
  | cons frame entries ih =>
      cases frame with
      | alternative task => exact (ih upper).cons_cons task
      | segment ownership base =>
          exact (ih base).trans (List.sublist_append_right _ _)
      | delimiter => exact ih upper

/-- A well-formed physical layout preserves the multiplicity of every native
and host alternative; the separate index law prevents overlapping intervals
from explaining duplicate values by visiting one physical frame twice. -/
theorem WellFormed.pending_perm {layout : Layout Task} (wellFormed : WellFormed layout) :
    layout.pending.Perm (layout.tier.reverse.filterMap id ++ hostOnly layout.host.reverse) := by
  have permutation := decodeAt_perm layout.tier layout.tier.length layout.host.reverse
  rw [nativeOnly_complete _ wellFormed.bounded wellFormed.drains] at permutation
  simpa [Layout.pending, slice] using permutation

theorem WellFormed.host_order {layout : Layout Task} (_wellFormed : WellFormed layout) :
    (hostOnly layout.host.reverse).Sublist layout.pending :=
  hostOnly_sublist _ _ _

theorem WellFormed.pending_count [BEq Task] {layout : Layout Task}
    (wellFormed : WellFormed layout) (task : Task) :
    layout.pending.count task = (layout.tier.reverse.filterMap id).count task +
      (hostOnly layout.host.reverse).count task := by
  simpa only [List.count_append] using wellFormed.pending_perm.count_eq task

/-- A decoder confined below a retained height never observes removed tier
frames. The hypothesis constrains indices, not the desired decoder equality. -/
theorem decodeAt_take (tier : List (Option Task)) {floor upper : Nat}
    {entries : List (HostFrame Task)} (bounded : Above 0 upper entries)
    (fits : upper ≤ floor) :
    decodeAt (tier.take floor) upper entries = decodeAt tier upper entries := by
  induction bounded with
  | nil => rfl
  | alternative bounded ih => simp only [decodeAt, ih fits]
  | @segment upper base ownership rest base_nonneg base_le bounded ih =>
      simp only [decodeAt, slice, List.take_take, Nat.min_eq_left fits]
      rw [ih (Nat.le_trans base_le fits)]
  | delimiter bounded ih => exact ih fits

/-- Opaque host choices preserve their own order between native segments. -/
theorem decodeAt_alternatives (tier : List (Option Task)) (upper : Nat)
    (tasks : List Task) (entries : List (HostFrame Task)) :
    decodeAt tier upper (tasks.map HostFrame.alternative ++ entries) =
      tasks ++ decodeAt tier upper entries := by
  induction tasks with
  | nil => rfl
  | cons task tasks ih => simp only [List.map_cons, List.cons_append, decodeAt, ih]

/-- After a nonfinal host answer, the machine's borrowed choice makes exactly
the newly created native interval run before the host's residual choices.
`oldTier` includes the administrative host frame; the host residual itself is
kept in `hostResidual`. The lower cursor intervals are unchanged. -/
theorem borrowed_segment_insertion (oldTier newTier : List (Option Task))
    (oldHost : List (HostFrame Task)) (hostResidual : List Task)
    (bounded : Above 0 oldTier.length oldHost.reverse) :
    (⟨oldTier ++ newTier,
      oldHost ++ hostResidual.map HostFrame.alternative ++
        [.segment .borrowed oldTier.length]⟩ : Layout Task).pending =
      newTier.reverse.filterMap id ++ hostResidual.reverse ++
        (⟨oldTier, oldHost⟩ : Layout Task).pending := by
  simp only [Layout.pending, List.length_append, List.reverse_append,
    List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append,
    decodeAt, ← List.map_reverse]
  rw [decodeAt_alternatives]
  have low : decodeAt (oldTier ++ newTier) oldTier.length oldHost.reverse =
      decodeAt oldTier oldTier.length oldHost.reverse := by
    rw [← decodeAt_take (oldTier ++ newTier) bounded (Nat.le_refl oldTier.length)]
    simp
  rw [low]
  have high : slice (oldTier ++ newTier) oldTier.length
      (oldTier.length + newTier.length) = newTier.reverse.filterMap id := by
    simp only [slice, ← List.length_append, List.take_length, List.drop_left]
  rw [high, List.append_assoc]

/-- A suffix of interleaved host and native alternatives ends at the old active
segment, whose `base` is below the new delimiter. This is the two-stack
partition law; the outer alternatives can themselves contain host segments. -/
theorem decode_partition (tier : List (Option Task)) {floor upper base : Nat}
    {inside outside : List (HostFrame Task)} (ownership : Ownership)
    (inner : Above floor upper inside) (base_le : base ≤ floor)
    (outer : Above 0 base outside) :
    decodeAt tier upper (inside ++ (.segment ownership base :: outside)) =
      pendingAbove floor tier upper inside ++
        decodeAt (tier.take floor) floor (.segment ownership base :: outside) := by
  induction inner with
  | @nil upper floor_le =>
      simp only [List.nil_append, pendingAbove, decodeAt]
      rw [slice_split tier base_le floor_le]
      have slice_take : slice (tier.take floor) base floor = slice tier base floor := by
        simp [slice, List.take_take]
      rw [slice_take, decodeAt_take tier outer base_le]
      simp only [List.append_assoc]
  | alternative inner ih => simpa only [List.cons_append, decodeAt, pendingAbove, List.cons_append] using congrArg (List.cons _) ih
  | segment floor_le base_le' inner ih =>
      simp only [List.cons_append, decodeAt, pendingAbove]
      rw [ih, List.append_assoc]
      rfl
  | delimiter inner ih => simpa only [List.cons_append, decodeAt, pendingAbove] using ih

/-- Truncation by the recorded host index keeps exactly the previous physical
host prefix. Truncating the tier is separately observable through the decoder. -/
theorem truncate_prefix (tier : List (Option Task)) (hostPrefix hostSuffix : List (HostFrame Task))
    (floor : Nat) :
    truncate ⟨floor, hostPrefix.length⟩ ⟨tier, hostPrefix ++ hostSuffix⟩ =
      ⟨tier.take floor, hostPrefix⟩ := by
  simp [truncate]

/-- The exact occurrence list canceled by an indexed cut, followed by precisely
the alternatives retained by the two physical stack prefixes. This algebraic
partition alone does not establish coverage of the original physical arrays;
that additional fact is supplied by `WellFormed`. -/
theorem pending_partition (tier : List (Option Task)) (floor base : Nat)
    (inside outside : List (HostFrame Task)) (ownership : Ownership)
    (floor_fits : floor ≤ tier.length) (base_le : base ≤ floor)
    (inner : Above floor tier.length inside) (outer : Above 0 base outside) :
    let hostPrefix := (.segment ownership base :: outside).reverse
    let layout : Layout Task := ⟨tier, hostPrefix ++ inside.reverse⟩
    layout.pending = pendingAbove floor tier tier.length inside ++
      (truncate ⟨floor, hostPrefix.length⟩ layout).pending := by
  dsimp only
  rw [truncate_prefix]
  simp only [Layout.pending, List.reverse_append, List.reverse_reverse,
    List.length_take, Nat.min_eq_left floor_fits]
  exact decode_partition tier ownership inner base_le outer

/-- A host-level delimiter may instead enclose the whole cursor owner. Its new
host suffix drains the cursor to zero, while the outer host stack refers to no
frames of that cursor. In this case removing the owner is correctly scoped. -/
theorem owner_pending_partition (tier : List (Option Task))
    (inside outside : List (HostFrame Task))
    (inner : Above 0 tier.length inside) (owned : OwnerChain inside)
    (outer : HostOnly outside) :
    let layout : Layout Task := ⟨tier, outside.reverse ++ inside.reverse⟩
    layout.pending = decodeAt tier tier.length inside ++
      (truncate ⟨0, outside.length⟩ layout).pending ∧
      nativeOnly tier tier.length inside = tier.reverse.filterMap id := by
  dsimp only
  constructor
  · have lengths : outside.length = outside.reverse.length := by simp
    rw [lengths, truncate_prefix]
    simp only [Layout.pending, List.reverse_append, List.reverse_reverse,
      List.take_zero, List.length_nil]
    rw [decodeAt_append, owned.drains]
    have lower := decodeAt_take tier outer.bounded (Nat.le_refl 0)
    have lower' : decodeAt [] 0 outside = decodeAt tier 0 outside := by
      simpa only [List.take_zero] using lower
    rw [lower']
  · simpa [slice] using nativeOnly_complete tier inner (owned.drains tier.length)

/-- No occurrence is invented by cancellation, including with duplicate task
values. The stronger `pending_partition` also retains their exact order. -/
theorem retained_occurrence_was_pending (tier : List (Option Task)) (floor base : Nat)
    (inside outside : List (HostFrame Task)) (ownership : Ownership)
    (floor_fits : floor ≤ tier.length) (base_le : base ≤ floor)
    (inner : Above floor tier.length inside) (outer : Above 0 base outside)
    (task : Task) :
    let hostPrefix := (.segment ownership base :: outside).reverse
    let layout : Layout Task := ⟨tier, hostPrefix ++ inside.reverse⟩
    task ∈ (truncate ⟨floor, hostPrefix.length⟩ layout).pending → task ∈ layout.pending := by
  dsimp only
  rw [pending_partition tier floor base inside outside ownership floor_fits base_le inner outer]
  exact List.mem_append_right _

/-- Mathematical selected values and world effects are outside the canceled
alternative stacks. This is an obligation on the implementation's export and
root ownership, not an assertion about C pointer validity. -/
structure State (Task Selected World : Type) where
  choices : Layout Task
  selected : Selected
  world : World
  deriving DecidableEq, Repr

def commit {Selected World : Type} (mark : Mark) (state : State Task Selected World) :
    State Task Selected World :=
  { state with choices := truncate mark state.choices }

/-- A delimiter marker is tested by kind, without comparing task payloads. -/
def isDelimiter : HostFrame Task → Bool
  | .delimiter => true
  | _ => false

/-- The ordinary machine checks the saved once-choice index and kind. A native
delimiter additionally has a tier height to validate. These checks do not
establish the interval invariant or pointer ownership by themselves. Reusing a
stack slot for another delimiter of the same kind also passes them (ABA); a
lifetime epoch or nonreusable ownership token is a separate runtime obligation. -/
def checkedCommit {Selected World : Type} (mark : Mark)
    (state : State Task Selected World) : Option (State Task Selected World) :=
  if mark.tierHeight ≤ state.choices.tier.length ∧
      (state.choices.host[mark.hostHeight]?).any isDelimiter then
    some (commit mark state)
  else none

/-- A successful checked operation is precisely indexed cancellation; neither
an out-of-range index nor another choice kind can silently serve as a delimiter. -/
theorem checkedCommit_success_iff {Selected World : Type} (mark : Mark)
    (state result : State Task Selected World) :
    checkedCommit mark state = some result ↔
      mark.tierHeight ≤ state.choices.tier.length ∧
        (state.choices.host[mark.hostHeight]?).any isDelimiter = true ∧
        commit mark state = result := by
  simp only [checkedCommit]
  split <;> simp_all

@[simp] theorem commit_selected {Selected World : Type} (mark : Mark)
    (state : State Task Selected World) : (commit mark state).selected = state.selected := rfl

@[simp] theorem commit_world {Selected World : Type} (mark : Mark)
    (state : State Task Selected World) : (commit mark state).world = state.world := rfl

/-- Nested indexed cancellation cannot restore choices already canceled. -/
theorem truncate_nested (outer inner : Mark) (layout : Layout Task)
    (tier_le : outer.tierHeight ≤ inner.tierHeight)
    (host_le : outer.hostHeight ≤ inner.hostHeight) :
    truncate outer (truncate inner layout) = truncate outer layout := by
  simp [truncate, List.take_take, Nat.min_eq_left tier_le, Nat.min_eq_left host_le]

/-- Number of owning answer choices, whose C release path closes the cursor.
Borrowed markers do not contribute a close action. This count describes the
release protocol, not the safety of the allocator implementing it. -/
def ownerCount : List (HostFrame Task) → Nat
  | [] => 0
  | .segment .owning _ :: rest => 1 + ownerCount rest
  | _ :: rest => ownerCount rest

theorem ownerCount_append (first second : List (HostFrame Task)) :
    ownerCount (first ++ second) = ownerCount first + ownerCount second := by
  induction first with
  | nil => simp [ownerCount]
  | cons frame frames ih =>
      cases frame with
      | alternative => simp [ownerCount, ih]
      | delimiter => simp [ownerCount, ih]
      | segment ownership base => cases ownership <;> simp [ownerCount, ih, Nat.add_assoc]

theorem ownerCount_reverse (entries : List (HostFrame Task)) :
    ownerCount entries.reverse = ownerCount entries := by
  induction entries with
  | nil => rfl
  | cons frame entries ih =>
      rw [List.reverse_cons, ownerCount_append, ih]
      cases frame with
      | alternative => simp [ownerCount]
      | delimiter => simp [ownerCount]
      | segment ownership base => cases ownership <;> simp [ownerCount, Nat.add_comm]

theorem HostOnly.ownerCount_eq_zero {entries : List (HostFrame Task)}
    (clean : HostOnly entries) : ownerCount entries = 0 := by
  induction clean with
  | nil => rfl
  | alternative clean ih => exact ih
  | delimiter clean ih => exact ih

theorem OwnerChain.ownerCount_eq_one {entries : List (HostFrame Task)}
    (owned : OwnerChain entries) : ownerCount entries = 1 := by
  induction owned with
  | owner clean => simp [ownerCount, clean.ownerCount_eq_zero]
  | alternative owned ih => exact ih
  | borrowed owned ih => exact ih
  | delimiter owned ih => exact ih

theorem WellFormed.unique_owner {layout : Layout Task} (wellFormed : WellFormed layout) :
    ownerCount layout.host = 1 := by
  rw [← ownerCount_reverse]
  exact wellFormed.owned.ownerCount_eq_one

/-- The host truncation releases its removed suffix newest first, as
`petta_choice_pop` does. Only owning entries request closing the cursor. -/
def ownerReleases (mark : Mark) (layout : Layout Task) : Nat :=
  ownerCount (layout.host.drop mark.hostHeight).reverse

/-- If this cursor's sole owner is below the delimiter, removing its borrowed
segments cannot request closing that owner. The uniqueness premise prevents a
second owning marker from masquerading as a safe borrow. -/
theorem retained_owner_not_released (mark : Mark) (layout : Layout Task)
    (unique : ownerCount layout.host = 1)
    (retained : ownerCount (layout.host.take mark.hostHeight) = 1) :
    ownerReleases mark layout = 0 := by
  have partition := ownerCount_append (layout.host.take mark.hostHeight)
    (layout.host.drop mark.hostHeight)
  rw [List.take_append_drop, unique, retained] at partition
  simp only [ownerReleases, ownerCount_reverse]
  omega

section Once

variable {C K Call F A : Type}

abbrev OnceTask (C K F A : Type) :=
  CTask C (NativeControlOnce.Control K A) (NativeControlOnce.Frame F)

/-- The two physical indices implement the single logical `once` scope. The
selected context is the current witness's context; there is no rollback to the
entry context in this cut step. This is the decoder-level equation. Use
`faithful_cut_refines_once` for the contract that also rules out omitted or
multiply decoded physical frames. -/
theorem cut_refines_once (P : CProgram C K Call F A) (answer : C × A)
    (returns : List (NativeControlOnce.Frame F × Option Nat))
    (emitted : List (C × A)) (tier : List (Option (OnceTask C K F A)))
    (floor base : Nat) (inside outside : List (HostFrame (OnceTask C K F A)))
    (ownership : Ownership) (floor_fits : floor ≤ tier.length) (base_le : base ≤ floor)
    (inner : Above floor tier.length inside) (outer : Above 0 base outside) :
    let hostPrefix := (.segment ownership base :: outside).reverse
    let layout : Layout (OnceTask C K F A) := ⟨tier, hostPrefix ++ inside.reverse⟩
    let retained := (truncate ⟨floor, hostPrefix.length⟩ layout).pending
    cstep (NativeControlOnce.program P)
      ⟨⟨answer.1, .commit answer.2, returns, some retained.length⟩ :: layout.pending, emitted⟩ =
      ⟨⟨answer.1, .answer answer.2, returns, some retained.length⟩ :: retained, emitted⟩ := by
  dsimp only
  rw [pending_partition tier floor base inside outside ownership floor_fits base_le inner outer]
  exact NativeControlOnce.commit_step P answer _ _ returns emitted

/-- Reflection uses the same exact step: an implementation result cannot have
an additional answer, alternative, or changed selected binding at this boundary. -/
theorem cut_reflects_once (P : CProgram C K Call F A) (answer : C × A)
    (returns : List (NativeControlOnce.Frame F × Option Nat))
    (emitted : List (C × A)) (tier : List (Option (OnceTask C K F A)))
    (floor base : Nat) (inside outside : List (HostFrame (OnceTask C K F A)))
    (ownership : Ownership) (floor_fits : floor ≤ tier.length) (base_le : base ≤ floor)
    (inner : Above floor tier.length inside) (outer : Above 0 base outside)
    (result : CState C (NativeControlOnce.Control K A) (NativeControlOnce.Frame F) A) :
    let hostPrefix := (.segment ownership base :: outside).reverse
    let layout : Layout (OnceTask C K F A) := ⟨tier, hostPrefix ++ inside.reverse⟩
    let retained := (truncate ⟨floor, hostPrefix.length⟩ layout).pending
    cstep (NativeControlOnce.program P)
      ⟨⟨answer.1, .commit answer.2, returns, some retained.length⟩ :: layout.pending, emitted⟩ = result ↔
      ⟨⟨answer.1, .answer answer.2, returns, some retained.length⟩ :: retained, emitted⟩ = result := by
  dsimp only
  rw [cut_refines_once P answer returns emitted tier floor base inside outside ownership
    floor_fits base_le inner outer]

/-- The implementation-facing local-cut contract includes physical faithfulness.
The source layout covers every frame exactly once; the retained owner and
interval bounds establish the same invariant for the target layout. Thus the
step equality concerns the actual occurrence frontier, not an arbitrary decoder
that might have silently skipped or revisited a frame. Entry-time scope capture
and C storage validity are still separate obligations. -/
theorem faithful_cut_refines_once (P : CProgram C K Call F A) (answer : C × A)
    (returns : List (NativeControlOnce.Frame F × Option Nat))
    (emitted : List (C × A)) (tier : List (Option (OnceTask C K F A)))
    (floor base : Nat) (inside outside : List (HostFrame (OnceTask C K F A)))
    (ownership : Ownership) (floor_fits : floor ≤ tier.length) (base_le : base ≤ floor)
    (inner : Above floor tier.length inside) (outer : Above 0 base outside)
    (sourceWF : WellFormed
      ⟨tier, (.segment ownership base :: outside).reverse ++ inside.reverse⟩)
    (retainedOwned : OwnerChain (.segment ownership base :: outside)) :
    let hostPrefix := (.segment ownership base :: outside).reverse
    let layout : Layout (OnceTask C K F A) := ⟨tier, hostPrefix ++ inside.reverse⟩
    let target := truncate ⟨floor, hostPrefix.length⟩ layout
    WellFormed target ∧
      nativeOnly ((List.range layout.tier.length).map some) layout.tier.length
        layout.host.reverse = (List.range layout.tier.length).reverse ∧
      layout.pending.Perm (layout.tier.reverse.filterMap id ++ hostOnly layout.host.reverse) ∧
      cstep (NativeControlOnce.program P)
        ⟨⟨answer.1, .commit answer.2, returns, some target.pending.length⟩ :: layout.pending,
          emitted⟩ =
        ⟨⟨answer.1, .answer answer.2, returns, some target.pending.length⟩ :: target.pending,
          emitted⟩ := by
  dsimp only
  refine ⟨?_, sourceWF.native_index_coverage, sourceWF.pending_perm, ?_⟩
  · rw [truncate_prefix]
    constructor
    · simp only [List.reverse_reverse, List.length_take, Nat.min_eq_left floor_fits]
      exact .segment (Nat.zero_le base) base_le outer
    · simpa only [List.reverse_reverse] using retainedOwned
  · exact cut_refines_once P answer returns emitted tier floor base inside outside ownership
      floor_fits base_le inner outer

/-- The same source commit covers a host-level `once` that owns the entire open
cursor. Its owner can leave the host stack because no outer alternative names
that cursor's frames. Answer-storage validity remains a separate obligation. -/
theorem owner_cut_refines_once (P : CProgram C K Call F A) (answer : C × A)
    (returns : List (NativeControlOnce.Frame F × Option Nat))
    (emitted : List (C × A)) (tier : List (Option (OnceTask C K F A)))
    (inside outside : List (HostFrame (OnceTask C K F A)))
    (inner : Above 0 tier.length inside) (owned : OwnerChain inside)
    (outer : HostOnly outside) :
    let layout : Layout (OnceTask C K F A) := ⟨tier, outside.reverse ++ inside.reverse⟩
    let retained := (truncate ⟨0, outside.length⟩ layout).pending
    cstep (NativeControlOnce.program P)
      ⟨⟨answer.1, .commit answer.2, returns, some retained.length⟩ :: layout.pending, emitted⟩ =
      ⟨⟨answer.1, .answer answer.2, returns, some retained.length⟩ :: retained, emitted⟩ := by
  dsimp only
  rw [(owner_pending_partition tier inside outside inner owned outer).1]
  exact NativeControlOnce.commit_step P answer _ _ returns emitted

/-- Whole-owner cancellation combines faithful physical decoding with the
existing source commit. The target has no tier frames and only the outer host
work; it is a closed cursor layout rather than another live owning cursor. -/
theorem faithful_owner_cut_refines_once (P : CProgram C K Call F A) (answer : C × A)
    (returns : List (NativeControlOnce.Frame F × Option Nat))
    (emitted : List (C × A)) (tier : List (Option (OnceTask C K F A)))
    (inside outside : List (HostFrame (OnceTask C K F A)))
    (inner : Above 0 tier.length inside) (owned : OwnerChain inside)
    (outer : HostOnly outside) :
    let layout : Layout (OnceTask C K F A) := ⟨tier, outside.reverse ++ inside.reverse⟩
    let target := truncate ⟨0, outside.length⟩ layout
    WellFormed layout ∧
      nativeOnly ((List.range layout.tier.length).map some) layout.tier.length
        layout.host.reverse = (List.range layout.tier.length).reverse ∧
      layout.pending.Perm (layout.tier.reverse.filterMap id ++ hostOnly layout.host.reverse) ∧
      target.tier = [] ∧ HostOnly target.host.reverse ∧
      cstep (NativeControlOnce.program P)
        ⟨⟨answer.1, .commit answer.2, returns, some target.pending.length⟩ :: layout.pending,
          emitted⟩ =
        ⟨⟨answer.1, .answer answer.2, returns, some target.pending.length⟩ :: target.pending,
          emitted⟩ := by
  dsimp only
  have sourceWF := owner_layout_wellFormed tier inside outside inner owned outer
  refine ⟨sourceWF, sourceWF.native_index_coverage, sourceWF.pending_perm, rfl, ?_, ?_⟩
  · have lengths : outside.length = outside.reverse.length := by simp
    rw [lengths, truncate_prefix]
    simpa only [List.reverse_reverse] using outer
  · exact owner_cut_refines_once P answer returns emitted tier inside outside inner owned outer

end Once

namespace Controls

/-- A native alternative after a host answer, the host's residual, an earlier
native alternative, and an outer host alternative occupy different intervals. -/
def layout : Layout Nat :=
  ⟨[some 10, none, some 20, none, some 30],
    [.alternative 90, .segment .owning 0, .alternative 21, .segment .borrowed 2,
      .delimiter, .alternative 31, .segment .borrowed 4]⟩

def localMark : Mark := ⟨3, 4⟩

theorem interleaved_layout : layout.pending = [30, 31, 20, 21, 10, 90] := by decide

/-- Both the new native alternative and the new host residual disappear. The
borrowed segment and host residual outside the delimiter survive. -/
theorem cuts_host_and_tier :
    (truncate localMark layout).pending = [20, 21, 10, 90] := by decide

/-- Clearing only tier frames leaves the scoped host residual resumable. -/
theorem tier_only_is_too_narrow :
    (truncate ⟨3, layout.host.length⟩ layout).pending = [31, 20, 21, 10, 90] := by decide

/-- Clearing only host frames leaves the scoped tier alternative resumable. -/
theorem host_only_is_too_narrow :
    (truncate ⟨layout.tier.length, 4⟩ layout).pending = [30, 20, 21, 10, 90] := by decide

/-- Removing the owning choice also drops native and host alternatives outside
this delimiter. -/
theorem holder_cut_is_too_wide :
    (truncate ⟨0, 1⟩ layout).pending = [90] := by decide

theorem local_cut_keeps_cursor_owner :
    ownerCount layout.host = 1 ∧
      ownerCount (truncate localMark layout).host = 1 ∧
      ownerReleases localMark layout = 0 := by decide

/-- An enclosing cut that really removes the owning choice requests one close;
borrowed segments above it do not each request another close. -/
theorem enclosing_cut_closes_owner_once :
    ownerReleases ⟨0, 1⟩ layout = 1 := by decide

/-- The selected binding and already performed effects are retained as values;
this intentionally makes no pointer-lifetime claim. -/
theorem selected_binding_and_effects :
    let state : State Nat (Nat × Nat) (List Nat) := ⟨layout, (7, 42), [5, 6]⟩
    (commit localMark state).choices.pending = [20, 21, 10, 90] ∧
      (commit localMark state).selected = (7, 42) ∧
      (commit localMark state).world = [5, 6] := by decide

theorem checked_delimiter_succeeds :
    checkedCommit localMark (⟨layout, (7, 42), [5, 6]⟩ : State Nat (Nat × Nat) (List Nat)) =
      some ⟨truncate localMark layout, (7, 42), [5, 6]⟩ := by decide

theorem checked_wrong_kind_fails :
    checkedCommit ⟨3, 3⟩ (⟨layout, (7, 42), [5, 6]⟩ : State Nat (Nat × Nat) (List Nat)) =
      none := by decide

theorem checked_absent_index_fails :
    checkedCommit ⟨3, 7⟩ (⟨layout, (7, 42), [5, 6]⟩ : State Nat (Nat × Nat) (List Nat)) =
      none := by decide

/-- Equal values retain distinct occurrences when they lie outside the cut. -/
theorem duplicate_outer_occurrences :
    (truncate ⟨2, 1⟩ (⟨[some 7, some 7, some 7],
      [.segment .owning 0, .alternative 7, .segment .borrowed 2]⟩ : Layout Nat)).pending =
      [7, 7] := by decide

theorem layout_wellFormed : WellFormed layout := by
  constructor
  · change Above 0 5 [.segment .borrowed 4, .alternative 31, .delimiter,
      .segment .borrowed 2, .alternative 21, .segment .owning 0, .alternative 90]
    repeat' first | apply Above.segment | apply Above.alternative | apply Above.delimiter |
      apply Above.nil
    all_goals omega
  · exact .borrowed (.alternative (.delimiter
      (.borrowed (.alternative (.owner (.alternative .nil))))))

/-- A bounded empty marker list can silently omit a nonempty cursor. Complete
ownership rejects it, while the old interval-only predicate accepts it. -/
def missingOwner : Layout Nat := ⟨[some 7], []⟩

theorem missing_owner_is_not_faithful :
    Above 0 missingOwner.tier.length missingOwner.host.reverse ∧
      missingOwner.pending = [] ∧ ¬ WellFormed missingOwner := by
  refine ⟨.nil (by decide), rfl, ?_⟩
  intro malformed
  cases malformed.owned

/-- The marker at base one lies below a marker that already drained to zero.
The unguarded decoder consequently visits the same physical frame twice. -/
def overlapping : Layout Nat :=
  ⟨[some 7], [.segment .owning 0, .segment .borrowed 1, .segment .borrowed 0]⟩

theorem overlapping_intervals_duplicate :
    overlapping.pending = [7, 7] ∧ bottom overlapping.tier.length overlapping.host.reverse = 0 ∧
      OwnerChain overlapping.host.reverse ∧ ¬ WellFormed overlapping := by
  refine ⟨rfl, rfl, .borrowed (.borrowed (.owner .nil)), ?_⟩
  intro malformed
  have bounded := malformed.bounded
  cases bounded with
  | segment low high rest =>
      cases rest with
      | segment low high rest => omega

end Controls

end Mettapedia.GSLT.LanguageDef.NativeControlTwoStackCut
