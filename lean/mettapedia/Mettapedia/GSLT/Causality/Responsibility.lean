import Mettapedia.GSLT.Causality.ActualCausation

/-!
# Degree of responsibility and blame on footprinted traces

Halpern, *Actual Causality* (2016), Section 6.1, sets the degree of
responsibility of an occurrence to 0 when that occurrence belongs to no
actual cause, and otherwise to `1/k`, where `k` is the number of occurrences
in a smallest actual cause containing it. The cause is the modified clause
already formalized here: a contingency is pinned to the value it wrote on the
actual word.

Chockler and Halpern, "Responsibility and Blame: A Structural-Model Approach"
(2004), Definition 3.2, sets the degree to 0 when the setting is not a cause,
and otherwise to `1/(k+1)`, where `k` is the least number of variables in a
witness whose values differ from the actual context. A variable held at its
actual value does not count. On their better rock-throwing model Suzy's degree
is 1 and Billy's is 0; the naive model, which must change Billy's throw, gives
Suzy `1/2`. An 11–0 vote gives each voter `1/6`. A 6–5 vote gives each
majority voter 1 and each minority voter 0.

The modified clause and Definition 3.2 agree when every pin is an actual
write: the changes that make one occurrence critical are the other members of
a smallest cause, so `1/(k+1) = 1/|X|`. They differ when a witness may set an
occurrence off its actual write. The one-change trace below is that
difference. The idle occurrence has pinned degree 0. The unpinned witness
changes one cell that this occurrence does not write, so the 2004 denominator
is 2.

A positive degree is stored as that denominator. `0` means responsibility
zero. The numerator of a positive degree is 1.

Blame is the finite weighted sum of those ratios. The library's weighted
layers are a semiring on a rewrite kernel, or a real-valued distribution on
another carrier. Neither is a distribution over occurrence words, and the
real carrier brings `Classical.choice`. The sum below is the same arithmetic
on natural-number weights.
-/

set_option autoImplicit false

open Mettapedia.GSLT.Distinction.CausalGluing
open Mettapedia.GSLT.Distinction.CausalGluing.Occurrences
open Mettapedia.GSLT.Causality.ActualCausation

namespace Mettapedia.GSLT.Causality.Responsibility

/-! ## The pinned degree -/

/-- The occurrence lies in no actual cause. Its degree is 0. -/
def NoResponsibility {Id Cell Value Channel : Type}
    (O : Occurrences Id Cell Value Channel) (actual : List Id)
    (initial : Store Id Cell Value) (φ : Store Id Cell Value → Prop)
    (retained : List Id → List Id → Prop) (i : Id) : Prop :=
  ¬ ∃ X, i ∈ X ∧ ActualCause O actual initial φ retained X

/-- The degree is `1/k`. Some actual cause of length `k` contains `i`, and
no actual cause containing `i` is shorter. -/
def PositiveDegree {Id Cell Value Channel : Type}
    (O : Occurrences Id Cell Value Channel) (actual : List Id)
    (initial : Store Id Cell Value) (φ : Store Id Cell Value → Prop)
    (retained : List Id → List Id → Prop) (i : Id) (k : Nat) : Prop :=
  0 < k ∧
    (∃ X, i ∈ X ∧ ActualCause O actual initial φ retained X ∧ X.length = k) ∧
    (∀ X, i ∈ X → ActualCause O actual initial φ retained X → k ≤ X.length)

theorem length_ge_one {α : Type} {a : α} {X : List α} (h : a ∈ X) : 1 ≤ X.length :=
  Nat.succ_le_of_lt (List.length_pos_of_mem h)

theorem length_ge_two {α : Type} {a b : α} {X : List α}
    (hne : a ≠ b) (ha : a ∈ X) (hb : b ∈ X) : 2 ≤ X.length := by
  cases X with
  | nil => cases ha
  | cons _ xs =>
      cases ha with
      | head _ =>
          cases hb with
          | head _ => exact absurd rfl hne
          | tail _ hb' =>
              exact Nat.succ_le_succ (length_ge_one hb')
      | tail _ ha' =>
          cases hb with
          | head _ =>
              exact Nat.succ_le_succ (length_ge_one ha')
          | tail _ hb' =>
              exact Nat.succ_le_succ (length_ge_one hb')

/-- An occurrence absent from the word is in no cause. -/
theorem noResponsibility_of_absent {Id Cell Value Channel : Type}
    (O : Occurrences Id Cell Value Channel) (actual : List Id)
    (initial : Store Id Cell Value) (φ : Store Id Cell Value → Prop)
    (retained : List Id → List Id → Prop) {i : Id} (absent : i ∉ actual) :
    NoResponsibility O actual initial φ retained i := by
  intro ⟨X, mem, cause⟩
  exact absent (cause.1.2.1 i mem)

theorem positiveDegree_trace {Id Cell Value Channel : Type}
    (O : Occurrences Id Cell Value Channel) {w w' : List Id}
    (equivalent : TraceEquiv O.Independent w w') (initial : Store Id Cell Value)
    (φ : Store Id Cell Value → Prop) (retained : List Id → List Id → Prop)
    {i : Id} {k : Nat} (held : PositiveDegree O w initial φ retained i k) :
    PositiveDegree O w' initial φ retained i k := by
  rcases held with ⟨pos, ⟨X, mem, cause, len⟩, shorter⟩
  refine ⟨pos, ⟨X, mem, actualCause_of_trace O equivalent initial φ retained cause, len⟩, ?_⟩
  intro Y memY causeY
  exact shorter Y memY
    (actualCause_of_trace O (Relation.EqvGen.symm w w' equivalent) initial φ retained causeY)

theorem noResponsibility_trace {Id Cell Value Channel : Type}
    (O : Occurrences Id Cell Value Channel) {w w' : List Id}
    (equivalent : TraceEquiv O.Independent w w') (initial : Store Id Cell Value)
    (φ : Store Id Cell Value → Prop) (retained : List Id → List Id → Prop)
    {i : Id} (held : NoResponsibility O w initial φ retained i) :
    NoResponsibility O w' initial φ retained i := by
  intro ⟨X, mem, cause⟩
  exact held ⟨X, mem,
    actualCause_of_trace O (Relation.EqvGen.symm w w' equivalent) initial φ retained cause⟩

/-! ## A search over a finite candidate list -/

def subsets {α : Type} : List α → List (List α)
  | [] => [[]]
  | a :: rest =>
      let tail := subsets rest
      tail ++ tail.map (fun ys => a :: ys)

/-- Minimum length of a candidate that contains `i` and is marked as a cause.
`0` means the list contains no such candidate. -/
def searchDegree {α : Type} [DecidableEq α] (cands : List (List α))
    (cause : List α → Bool) (i : α) : Nat :=
  cands.foldl (fun best X =>
    if decide (i ∈ X) && cause X then
      if best = 0 then X.length else Nat.min best X.length
    else
      best) 0

/-! ## Late preemption: Suzy 1, Billy 0 -/

def preemptBreaksB (store : Store PreemptId PreemptCell Bool) : Bool :=
  (store .sh).1 || (store .bh).1

def retainedPreempt (X alt : List PreemptId) : Bool :=
  if alt == suzyAlt then decide (PreemptId.suzyThrow ∈ X) && decide (PreemptId.billyThrow ∉ X)
  else if alt == billyAlt then
    decide (PreemptId.billyThrow ∈ X) && decide (PreemptId.suzyThrow ∉ X)
  else if alt == bothAlt then
    decide (PreemptId.suzyThrow ∈ X) && decide (PreemptId.billyThrow ∈ X)
  else false

def ac2Preempt (X : List PreemptId) : Bool :=
  let outside := preemptActual.filter fun i => decide (i ∉ X)
  (subsets outside).any fun pinned =>
    [suzyAlt, billyAlt, bothAlt].any fun alt =>
      retainedPreempt X alt &&
        X.all (fun i => decide (i ∉ alt)) &&
        !preemptBreaksB
          (pinWrites preemptO (fun i => decide (i ∈ pinned)) preemptActual
            (preemptO.final alt preemptInitial))

def ac1Preempt (X : List PreemptId) : Bool :=
  !X.isEmpty && X.all (fun i => decide (i ∈ preemptActual)) &&
    preemptBreaksB (preemptO.final preemptActual preemptInitial)

def properSubB {α : Type} [DecidableEq α] (Y X : List α) : Bool :=
  Y.all (fun i => decide (i ∈ X)) && X.any (fun i => decide (i ∉ Y))

def ac3Preempt (X : List PreemptId) : Bool :=
  (subsets X).all fun Y => !properSubB Y X || !(ac1Preempt Y && ac2Preempt Y)

/-- The witness search for the preemption forks. -/
def preemptCause (X : List PreemptId) : Bool :=
  ac1Preempt X && ac2Preempt X && ac3Preempt X

theorem preemption_suzy_degree :
    PositiveDegree preemptO preemptActual preemptInitial preemptBreaks PreemptRetained
      .suzyThrow 1 :=
  ⟨Nat.succ_pos 0,
    ⟨[.suzyThrow], List.mem_cons_self, preemption_suzy_actualCause, rfl⟩,
    fun _ memX _ => length_ge_one memX⟩

theorem preemption_billy_degree :
    NoResponsibility preemptO preemptActual preemptInitial preemptBreaks PreemptRetained
      .billyThrow := by
  intro ⟨X, hb, cause⟩
  rcases cause.2.1 with ⟨keep, _, _, _, fork, _, falsifies⟩
  cases fork with
  | suzy _ noBilly => exact noBilly hb
  | billy _ _ => exact falsifies (Or.inl (preemption_billy_pin_sh keep))
  | both suzyIn _ =>
      exact cause.2.2 [.suzyThrow]
        ⟨singleton_members suzyIn, .billyThrow, hb,
          (by decide : PreemptId.billyThrow ∉ [PreemptId.suzyThrow])⟩
        ⟨preemption_suzy_ac1, preemption_suzy_ac2⟩

/-- Swapping Suzy's hit with Billy's throw leaves Suzy's degree at 1. -/
theorem preemption_responsibility_trace :
    PositiveDegree preemptO preemptSwapped preemptInitial preemptBreaks PreemptRetained
      .suzyThrow 1 :=
  positiveDegree_trace preemptO preemption_trace preemptInitial preemptBreaks PreemptRetained
    preemption_suzy_degree

theorem preemption_suzy_search :
    searchDegree (subsets preemptActual) preemptCause .suzyThrow = 1 := by
  decide

theorem preemption_billy_search :
    searchDegree (subsets preemptActual) preemptCause .billyThrow = 0 := by
  decide

/-! ## Symmetric overdetermination: 1/2 each -/

def overBreaksB (store : Store OverId OverCell Bool) : Bool :=
  (store .sh).1 || (store .bh).1

def retainedOver (X alt : List OverId) : Bool :=
  if alt == overSuzyAlt then decide (OverId.suzyHit ∈ X) && decide (OverId.billyHit ∉ X)
  else if alt == overBillyAlt then
    decide (OverId.billyHit ∈ X) && decide (OverId.suzyHit ∉ X)
  else if alt == overBothAlt then
    decide (OverId.suzyHit ∈ X) && decide (OverId.billyHit ∈ X)
  else false

def ac2Over (X : List OverId) : Bool :=
  let outside := overActual.filter fun i => decide (i ∉ X)
  (subsets outside).any fun pinned =>
    [overSuzyAlt, overBillyAlt, overBothAlt].any fun alt =>
      retainedOver X alt &&
        X.all (fun i => decide (i ∉ alt)) &&
        !overBreaksB
          (pinWrites overO (fun i => decide (i ∈ pinned)) overActual
            (overO.final alt overInitial))

def ac1Over (X : List OverId) : Bool :=
  !X.isEmpty && X.all (fun i => decide (i ∈ overActual)) &&
    overBreaksB (overO.final overActual overInitial)

def ac3Over (X : List OverId) : Bool :=
  (subsets X).all fun Y => !properSubB Y X || !(ac1Over Y && ac2Over Y)

def overCause (X : List OverId) : Bool :=
  ac1Over X && ac2Over X && ac3Over X

theorem over_cause_both (X : List OverId)
    (cause : ActualCause overO overActual overInitial overBreaks OverRetained X) :
    .suzyHit ∈ X ∧ .billyHit ∈ X := by
  rcases cause.2.1 with ⟨keep, _, _, _, fork, _, falsifies⟩
  cases fork with
  | onlySuzy _ _ => exact absurd (Or.inr (over_suzy_pin_bh keep)) falsifies
  | onlyBilly _ _ => exact absurd (Or.inl (over_billy_pin_sh keep)) falsifies
  | both hs hb => exact ⟨hs, hb⟩

theorem over_suzy_degree :
    PositiveDegree overO overActual overInitial overBreaks OverRetained .suzyHit 2 :=
  ⟨Nat.succ_pos 1,
    ⟨[.suzyHit, .billyHit], List.mem_cons_self, overdetermination_conjunction_actualCause, rfl⟩,
    fun X memX cause =>
      length_ge_two (by decide : OverId.suzyHit ≠ OverId.billyHit) memX
        (over_cause_both X cause).2⟩

theorem over_billy_degree :
    PositiveDegree overO overActual overInitial overBreaks OverRetained .billyHit 2 :=
  ⟨Nat.succ_pos 1,
    ⟨[.suzyHit, .billyHit], List.mem_cons_of_mem _ List.mem_cons_self,
      overdetermination_conjunction_actualCause, rfl⟩,
    fun X memX cause =>
      length_ge_two (by decide : OverId.billyHit ≠ OverId.suzyHit) memX
        (over_cause_both X cause).1⟩

theorem over_suzy_search :
    searchDegree (subsets overActual) overCause .suzyHit = 2 := by
  decide

theorem over_billy_search :
    searchDegree (subsets overActual) overCause .billyHit = 2 := by
  decide

/-! ## Where the two degrees differ -/

inductive GapId where
  | suzy | billy | suzyOff
  deriving DecidableEq

inductive GapCell where
  | bottle
  deriving DecidableEq

def gapWrite : GapId → GapCell → Option Bool
  | .suzy, .bottle => some true
  | .suzyOff, .bottle => some false
  | .billy, _ => none

def gapO : Occurrences GapId GapCell Bool Unit where
  footprint i := { reads := fun _ => false, writes := gapWrite i }
  channel := fun _ => none

def gapInitial : Store GapId GapCell Bool := fun _ => (false, none)

def gapActual : List GapId := [.suzy, .billy]

def gapBottle (store : Store GapId GapCell Bool) : Prop :=
  (store .bottle).1 = true

/-- Pinned forks. Dropping Billy keeps Suzy's actual write. -/
inductive GapRetained : List GapId → List GapId → Prop
  | onlySuzy {X : List GapId} : .suzy ∈ X → .billy ∉ X → GapRetained X [.billy]
  | onlyBilly {X : List GapId} : .billy ∈ X → .suzy ∉ X → GapRetained X [.suzy]
  | both {X : List GapId} : .suzy ∈ X → .billy ∈ X → GapRetained X []

/-- The unpinned fork sets Suzy off the value she wrote. -/
inductive GapUnpinned : List GapId → List GapId → Prop
  | suzy {X : List GapId} : .suzy ∈ X → .billy ∉ X → GapUnpinned X [.billy]
  | billy {X : List GapId} : .billy ∈ X → GapUnpinned X [.suzyOff]

theorem gap_actual_bottle : ((gapO.final gapActual gapInitial) .bottle).1 = true := rfl

theorem gap_billy_only_bottle : ((gapO.final [.billy] gapInitial) .bottle).1 = false := rfl

theorem gap_suzy_bottle : ((gapO.final [.suzy] gapInitial) .bottle).1 = true := rfl

theorem gap_off_bottle : ((gapO.final [.suzyOff] gapInitial) .bottle).1 = false := rfl

theorem gap_empty_bottle : ((gapO.final [] gapInitial) .bottle).1 = false := rfl

theorem gap_bottle_ok :
    ∀ i ∈ gapActual,
      (gapO.footprint i).writes .bottle = none ∨
        (gapO.footprint i).writes .bottle = some true := by
  intro i hi
  cases hi with
  | head _ => exact Or.inr rfl
  | tail _ hi =>
      cases hi with
      | head _ => exact Or.inl rfl
      | tail _ hi => cases hi

theorem gap_pin_suzy (keep : GapId → Bool) :
    ((pinWrites gapO keep gapActual (gapO.final [.suzy] gapInitial)) .bottle).1 = true :=
  pinWrites_keeps_payload gapO keep gapActual .bottle true (gapO.final [.suzy] gapInitial)
    gap_suzy_bottle gap_bottle_ok

theorem gap_suzy_ac1 :
    AC1 gapO gapActual gapInitial gapBottle [.suzy] :=
  ⟨⟨.suzy, List.mem_cons_self⟩,
    singleton_members (by decide : GapId.suzy ∈ gapActual), gap_actual_bottle⟩

theorem gap_suzy_ac2 :
    AC2 gapO gapActual gapInitial gapBottle GapRetained [.suzy] := by
  refine ⟨fun _ => false, [.billy], ?_, ?_, ?_, ?_, ?_⟩
  · intro _ hi; cases hi
  · intro _ hi; cases hi
  · exact GapRetained.onlySuzy List.mem_cons_self (by decide)
  · intro i hi
    cases hi with
    | head _ => decide
    | tail _ hi => cases hi
  · rw [pinWrites_const_false gapO gapActual (gapO.final [.billy] gapInitial)]
    exact not_true_of_false gap_billy_only_bottle

theorem gap_suzy_degree :
    PositiveDegree gapO gapActual gapInitial gapBottle GapRetained .suzy 1 :=
  ⟨Nat.succ_pos 0,
    ⟨[.suzy], List.mem_cons_self,
      ⟨gap_suzy_ac1, gap_suzy_ac2,
        ac3_singleton gapO gapActual gapInitial gapBottle GapRetained
          (fun i => mem_singleton (a := GapId.suzy) (i := i))⟩, rfl⟩,
    fun _ memX _ => length_ge_one memX⟩

theorem gap_suzy_unpinned :
    UnpinnedCause gapO gapActual gapInitial gapBottle GapUnpinned [.suzy] :=
  ⟨gap_suzy_ac1,
    ⟨[.billy], GapUnpinned.suzy List.mem_cons_self (by decide),
      singleton_absent (by decide : GapId.suzy ∉ [.billy]),
      not_true_of_false gap_billy_only_bottle⟩,
    unpinnedAc3_singleton gapO gapActual gapInitial gapBottle GapUnpinned
      (fun i => mem_singleton (a := GapId.suzy) (i := i))⟩

/-- Suzy's witness changes the bottle, and she is the occurrence who writes it.
Definition 3.2 does not count the candidate's own removal, so `k = 0` and the
denominator is 1, in agreement with the pinned degree. -/
theorem gap_suzy_change_count :
    (gapO.footprint .suzy).writes .bottle = some true ∧
      (gapO.footprint .billy).writes .bottle = none ∧
      ((gapO.final gapActual gapInitial) .bottle).1 = true ∧
      ((gapO.final [.billy] gapInitial) .bottle).1 = false ∧
      GapId.suzy ∈ [.suzy] :=
  ⟨rfl, rfl, gap_actual_bottle, gap_billy_only_bottle, List.mem_cons_self⟩

theorem gap_billy_degree :
    NoResponsibility gapO gapActual gapInitial gapBottle GapRetained .billy := by
  intro ⟨X, hb, cause⟩
  rcases cause.2.1 with ⟨keep, _, _, _, fork, _, falsifies⟩
  cases fork with
  | onlySuzy _ noBilly => exact noBilly hb
  | onlyBilly _ _ => exact falsifies (gap_pin_suzy keep)
  | both suzyIn _ =>
      exact cause.2.2 [.suzy]
        ⟨singleton_members suzyIn, .billy, hb, (by decide : GapId.billy ∉ [GapId.suzy])⟩
        ⟨gap_suzy_ac1, gap_suzy_ac2⟩

theorem gap_billy_unpinned :
    UnpinnedCause gapO gapActual gapInitial gapBottle GapUnpinned [.billy] :=
  ⟨⟨⟨.billy, List.mem_cons_self⟩,
      singleton_members (by decide : GapId.billy ∈ gapActual), gap_actual_bottle⟩,
    ⟨[.suzyOff], GapUnpinned.billy List.mem_cons_self,
      singleton_absent (by decide : GapId.billy ∉ [.suzyOff]),
      not_true_of_false gap_off_bottle⟩,
    unpinnedAc3_singleton gapO gapActual gapInitial gapBottle GapUnpinned
      (fun i => mem_singleton (a := GapId.billy) (i := i))⟩

/-- Billy is not a pinned cause, so Section 6.1 gives him 0. The unpinned
witness writes the bottle false where Suzy wrote it true. That is one change
outside the candidate, so Definition 3.2 gives him `1/2`. -/
theorem gap_billy_divergence :
    NoResponsibility gapO gapActual gapInitial gapBottle GapRetained .billy ∧
      UnpinnedCause gapO gapActual gapInitial gapBottle GapUnpinned [.billy] ∧
      (gapO.footprint .billy).writes .bottle = none ∧
      (gapO.footprint .suzy).writes .bottle = some true ∧
      (gapO.footprint .suzyOff).writes .bottle = some false ∧
      ((gapO.final gapActual gapInitial) .bottle).1 = true ∧
      ((gapO.final [.suzyOff] gapInitial) .bottle).1 = false ∧
      GapId.suzy ∉ [.billy] :=
  ⟨gap_billy_degree, gap_billy_unpinned, rfl, rfl, rfl, gap_actual_bottle, gap_off_bottle,
    by decide⟩

/-! ## Counting votes -/

inductive Side where
  | yes | no
  deriving DecidableEq

inductive VoteId where
  | cast (v : Fin 11) (s : Side)
  deriving DecidableEq

def voteWrite : VoteId → Fin 11 → Option Bool
  | .cast v .yes, c => if v = c then some true else none
  | .cast v .no, c => if v = c then some false else none

def voteO : Occurrences VoteId (Fin 11) Bool Unit where
  footprint i := { reads := fun _ => false, writes := voteWrite i }
  channel := fun _ => none

def voteInitial : Store VoteId (Fin 11) Bool := fun _ => (false, none)

def sideBit : Side → Bool
  | .yes => true
  | .no => false

def voter : VoteId → Fin 11
  | .cast v _ => v

def votersOf (X : List VoteId) : List (Fin 11) :=
  X.map voter

def wordOf (choice : Fin 11 → Side) : List VoteId :=
  (List.finRange 11).map fun i => .cast i (choice i)

/-- List membership as a `Bool`, using equality only.
The `Decidable` instance of `i ∈ xs` on `Fin` selects the linear-order
`LawfulBEq`, and that instance depends on `Classical.choice`. -/
def memB {α : Type} [DecidableEq α] (a : α) : List α → Bool
  | [] => false
  | b :: bs => decide (a = b) || memB a bs

theorem memB_of_mem {α : Type} [DecidableEq α] {a : α} {l : List α} (h : a ∈ l) :
    memB a l = true := by
  induction l with
  | nil => cases h
  | cons b bs ih =>
      cases h with
      | head _ =>
          rw [memB, decide_eq_true rfl]
          rfl
      | tail _ ht =>
          cases hb : decide (a = b)
          · rw [memB, hb, ih ht]
            rfl
          · rw [memB, hb]
            rfl

theorem memB_true {α : Type} [DecidableEq α] {a : α} {l : List α} (h : memB a l = true) :
    a ∈ l := by
  induction l with
  | nil =>
      rw [memB] at h
      cases h
  | cons b bs ih =>
      rw [memB] at h
      cases hb : decide (a = b)
      · rw [hb] at h
        exact List.mem_cons_of_mem b (ih h)
      · have : a = b := of_decide_eq_true hb
        rw [this]
        exact List.mem_cons_self

theorem memB_of_not {α : Type} [DecidableEq α] {a : α} {l : List α} (h : a ∉ l) :
    memB a l = false := by
  cases hb : memB a l
  · rfl
  · exact absurd (memB_true hb) h

def altChoice (base : Fin 11 → Side) (drop : List (Fin 11)) (i : Fin 11) : Side :=
  cond (memB i drop) .no (base i)

def altWord (base : Fin 11 → Side) (drop : List (Fin 11)) : List VoteId :=
  wordOf (altChoice base drop)

inductive VoteRetained (base : Fin 11 → Side) : List VoteId → List VoteId → Prop
  | flip {X : List VoteId} : VoteRetained base X (altWord base (votersOf X))

def cellBit (store : Store VoteId (Fin 11) Bool) (i : Fin 11) : Bool :=
  (store i).1

def yesCount (store : Store VoteId (Fin 11) Bool) : Nat :=
  (List.finRange 11).countP (cellBit store)

def majority (store : Store VoteId (Fin 11) Bool) : Prop :=
  6 ≤ yesCount store

def allYes : Fin 11 → Side := fun _ => .yes

def splitChoice : Fin 11 → Side :=
  fun i => if i.val < 6 then .yes else .no

theorem voteWrite_at (i : Fin 11) (s : Side) :
    voteWrite (.cast i s) i = some (sideBit s) := by
  cases s <;> simp [voteWrite, sideBit]

theorem voteWrite_other (i c : Fin 11) (s : Side) (h : i ≠ c) :
    voteWrite (.cast i s) c = none := by
  cases s <;> simp [voteWrite, h]

theorem foldl_const {α β : Type} (l : List α) (f : β → α → β) (init : β)
    (h : ∀ b a, f b a = b) : l.foldl f init = init := by
  induction l generalizing init with
  | nil => rfl
  | cons a l ih =>
      rw [List.foldl_cons, h, ih]

theorem foldl_congr {α β : Type} {l : List α} {f g : β → α → β} {init : β}
    (h : ∀ b a, f b a = g b a) : l.foldl f init = l.foldl g init := by
  induction l generalizing init with
  | nil => rfl
  | cons a l ih =>
      rw [List.foldl_cons, List.foldl_cons, h, ih]

theorem foldl_finRange_pick {n : Nat} (target : Fin n) (value : Bool) :
    (List.finRange n).foldl (fun acc i => if i = target then value else acc) false = value := by
  induction n with
  | zero => exact Fin.elim0 target
  | succ n ih =>
      rw [List.finRange_succ, List.foldl_cons]
      cases target using Fin.cases with
      | zero =>
          rw [if_pos rfl, List.foldl_map]
          exact foldl_const (List.finRange n)
            (fun acc j => if Fin.succ j = 0 then value else acc) value
            (fun _ j => if_neg (Fin.succ_ne_zero j))
      | succ t =>
          rw [if_neg (Fin.succ_ne_zero t).symm, List.foldl_map]
          have hfun : ∀ acc j,
              (if Fin.succ j = Fin.succ t then value else acc) =
                (if j = t then value else acc) := by
            intro acc j
            by_cases h : j = t
            · simp [h]
            · have hs : Fin.succ j ≠ Fin.succ t := by
                intro eq
                exact h (Fin.succ_inj.mp eq)
              simp [h, hs]
          rw [foldl_congr hfun]
          exact ih t

theorem final_cell_fold (word : List VoteId) (cell : Fin 11)
    (store : Store VoteId (Fin 11) Bool) :
    ((voteO.final word store) cell).1 =
      word.foldl (fun acc i =>
        match voteWrite i cell with
        | some b => b
        | none => acc) (store cell).1 := by
  induction word generalizing store with
  | nil => rfl
  | cons i word ih =>
      rw [List.foldl_cons]
      have step : ((voteO.apply i store) cell).1 =
          match voteWrite i cell with
          | some b => b
          | none => (store cell).1 := by
        have hw : (voteO.footprint i).writes cell = voteWrite i cell := by
          unfold voteO
          rfl
        rw [Occurrences.apply, hw]
        cases voteWrite i cell <;> rfl
      simp only [Occurrences.final]
      rw [ih (voteO.apply i store), step]

theorem foldl_vote (choice : Fin 11 → Side) (cell : Fin 11) :
    (List.finRange 11).foldl (fun acc i =>
        match voteWrite (.cast i (choice i)) cell with
        | some b => b
        | none => acc) false =
      sideBit (choice cell) := by
  have hfun : ∀ acc i,
      (match voteWrite (.cast i (choice i)) cell with
        | some b => b
        | none => acc) =
        (if i = cell then sideBit (choice cell) else acc) := by
    intro acc i
    by_cases h : i = cell
    · subst h
      simp [voteWrite_at i (choice i)]
    · simp [voteWrite_other i cell (choice i) h, h]
  rw [foldl_congr hfun]
  exact foldl_finRange_pick cell (sideBit (choice cell))

theorem word_cell (choice : Fin 11 → Side) (cell : Fin 11) :
    ((voteO.final (wordOf choice) voteInitial) cell).1 = sideBit (choice cell) := by
  rw [final_cell_fold, wordOf, List.foldl_map]
  exact foldl_vote choice cell

theorem countP_congr {α : Type} {l : List α} {p q : α → Bool}
    (h : ∀ a ∈ l, p a = q a) : l.countP p = l.countP q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      rw [List.countP_cons, List.countP_cons, h a List.mem_cons_self]
      exact congrArg (fun n => n + if q a then 1 else 0)
        (ih (fun b hb => h b (List.mem_cons_of_mem a hb)))

theorem countP_const_false {α : Type} (l : List α) : l.countP (fun _ => false) = 0 := by
  induction l with
  | nil => rfl
  | cons _ l ih =>
      rw [List.countP_cons_of_neg (by simp : ¬ (false : Bool))]
      exact ih

theorem not_bool_eq {b : Bool} (h : b = false) : ¬ b = true := by
  intro ht
  rw [h] at ht
  cases ht

theorem decide_ne_not {α : Type} [DecidableEq α] (a b : α) :
    decide (a ≠ b) = ! decide (a = b) := by
  by_cases h : a = b
  · rw [decide_eq_false (fun hn : a ≠ b => hn h), decide_eq_true h]
    rfl
  · rw [decide_eq_true h, decide_eq_false h]
    rfl

theorem bang_not (b : Bool) : (!b) = decide (¬ b = true) := by
  cases b <;> rfl

theorem bool_cover (m e : Bool) : m = ((m && e) || (m && !e)) := by
  cases m <;> cases e <;> rfl

theorem countP_mono {α : Type} {l : List α} {p q : α → Bool}
    (h : ∀ a ∈ l, p a = true → q a = true) : l.countP p ≤ l.countP q := by
  induction l with
  | nil => exact Nat.le_refl 0
  | cons a l ih =>
      have ih' := ih (fun b hb hp => h b (List.mem_cons_of_mem a hb) hp)
      cases hp : p a with
      | false =>
          rw [List.countP_cons_of_neg (not_bool_eq hp), List.countP_cons (p := q)]
          exact Nat.le_trans ih' (Nat.le_add_right _ _)
      | true =>
          have hq : q a = true := h a List.mem_cons_self hp
          rw [List.countP_cons_of_pos hp, List.countP_cons_of_pos hq]
          exact Nat.add_le_add_right ih' 1

theorem yesCount_mono {s t : Store VoteId (Fin 11) Bool}
    (h : ∀ i, (s i).1 = true → (t i).1 = true) : yesCount s ≤ yesCount t := by
  unfold yesCount cellBit
  exact countP_mono (fun i _ hp => h i hp)

theorem nodup_map_succ {n : Nat} {l : List (Fin n)} (h : l.Nodup) :
    (l.map Fin.succ).Nodup := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.map_cons]
      refine List.Pairwise.cons ?_ (ih (List.Pairwise.of_cons h))
      intro b hb
      rcases List.mem_map.1 hb with ⟨c, hc, rfl⟩
      intro eq
      exact (List.pairwise_cons.mp h).1 c hc (Fin.succ_inj.mp eq)

theorem nodup_finRange : ∀ n, (List.finRange n).Nodup
  | 0 => by simp [List.finRange_zero]
  | n + 1 => by
      rw [List.finRange_succ]
      refine List.Pairwise.cons ?_ (nodup_map_succ (nodup_finRange n))
      intro a ha
      rcases List.mem_map.1 ha with ⟨_, _, rfl⟩
      exact (Fin.succ_ne_zero _).symm

theorem countP_id_zero {α : Type} [DecidableEq α] {a : α} {l : List α} (h : a ∉ l) :
    l.countP (fun i => decide (i = a)) = 0 := by
  induction l with
  | nil => rfl
  | cons b l ih =>
      have hb : b ≠ a := by
        intro eq
        exact h (eq ▸ List.mem_cons_self)
      have hrest : a ∉ l := by
        intro hm
        exact h (List.mem_cons_of_mem b hm)
      rw [List.countP_cons_of_neg]
      · exact ih hrest
      · intro ht
        exact hb (of_decide_eq_true ht)

theorem countP_id_le_one {α : Type} [DecidableEq α] {a : α} {l : List α} (nd : l.Nodup) :
    l.countP (fun i => decide (i = a)) ≤ 1 := by
  induction l with
  | nil => simp
  | cons b l ih =>
      have ndl := List.Pairwise.of_cons nd
      have b_not : b ∉ l := by
        intro hb
        exact (List.pairwise_cons.mp nd).1 b hb rfl
      by_cases h : b = a
      · subst h
        rw [List.countP_cons, decide_eq_true rfl, countP_id_zero b_not]
        exact Nat.le_refl 1
      · rw [List.countP_cons_of_neg]
        · exact ih ndl
        · intro ht
          exact h (of_decide_eq_true ht)

theorem countP_id_ge_one {α : Type} [DecidableEq α] {a : α} {l : List α} (ha : a ∈ l) :
    1 ≤ l.countP (fun i => decide (i = a)) := by
  induction l with
  | nil => cases ha
  | cons b l ih =>
      cases ha with
      | head _ =>
          rw [List.countP_cons, decide_eq_true rfl]
          exact Nat.le_add_left 1 _
      | tail _ hmem =>
          by_cases hb : b = a
          · subst hb
            rw [List.countP_cons, decide_eq_true rfl]
            exact Nat.le_add_left 1 _
          · rw [List.countP_cons_of_neg]
            · exact ih hmem
            · intro ht
              exact hb (of_decide_eq_true ht)

theorem countP_id_one {α : Type} [DecidableEq α] {a : α} {l : List α} (nd : l.Nodup) (ha : a ∈ l) :
    l.countP (fun i => decide (i = a)) = 1 :=
  Nat.le_antisymm (countP_id_le_one nd) (countP_id_ge_one ha)

theorem memB_cons {α : Type} [DecidableEq α] (i y : α) (ys : List α) :
    memB i (y :: ys) = (decide (i = y) || memB i ys) :=
  rfl

theorem countP_or_le {α : Type} (p q : α → Bool) (l : List α) :
    l.countP (fun a => p a || q a) ≤ l.countP p + l.countP q := by
  induction l with
  | nil =>
      rw [List.countP_nil, List.countP_nil, List.countP_nil]
  | cons a l ih =>
      cases hp : p a <;> cases hq : q a
      · have hor : (p a || q a) = false := by rw [hp, hq]; rfl
        rw [List.countP_cons_of_neg (p := fun b => p b || q b) (not_bool_eq hor),
          List.countP_cons_of_neg (not_bool_eq hp),
          List.countP_cons_of_neg (not_bool_eq hq)]
        exact ih
      · have hor : (p a || q a) = true := by rw [hp, hq]; rfl
        rw [List.countP_cons_of_pos (p := fun b => p b || q b) hor,
          List.countP_cons_of_neg (not_bool_eq hp),
          List.countP_cons_of_pos hq]
        exact Nat.add_le_add_right ih 1
      · have hor : (p a || q a) = true := by rw [hp, hq]; rfl
        rw [List.countP_cons_of_pos (p := fun b => p b || q b) hor,
          List.countP_cons_of_pos hp,
          List.countP_cons_of_neg (not_bool_eq hq)]
        have hcomm : l.countP p + l.countP q + 1 = l.countP p + 1 + l.countP q := by
          rw [Nat.add_assoc, Nat.add_comm (l.countP q) 1, ← Nat.add_assoc]
        exact hcomm ▸ Nat.add_le_add_right ih 1
      · have hor : (p a || q a) = true := by rw [hp, hq]; rfl
        rw [List.countP_cons_of_pos (p := fun b => p b || q b) hor,
          List.countP_cons_of_pos hp,
          List.countP_cons_of_pos hq]
        have hgoal : l.countP p + l.countP q + 1 ≤
            (l.countP p + 1) + (l.countP q + 1) := by
          have hleft : l.countP p + l.countP q + 1 = l.countP p + (l.countP q + 1) :=
            Nat.add_assoc _ _ _
          have hright : (l.countP p + 1) + (l.countP q + 1) =
              l.countP p + (1 + (l.countP q + 1)) := Nat.add_assoc _ _ _
          rw [hleft, hright]
          apply Nat.add_le_add_left
          have hswap : l.countP q + 1 = 1 + l.countP q := Nat.add_comm _ _
          rw [hswap]
          apply Nat.add_le_add_left
          exact Nat.le_add_left _ 1
        exact Nat.le_trans (Nat.add_le_add_right ih 1) hgoal

theorem countP_memB_nil {α : Type} [DecidableEq α] (l : List α) :
    l.countP (fun i => memB i ([] : List α)) = 0 := by
  induction l with
  | nil => rfl
  | cons _ l ih =>
      rw [List.countP_cons_of_neg]
      · exact ih
      · rw [memB]
        exact not_bool_eq rfl

theorem countP_mem_le {α : Type} [DecidableEq α] (ys l : List α) (hl : l.Nodup) :
    l.countP (fun i => memB i ys) ≤ ys.length := by
  induction ys generalizing l with
  | nil =>
      rw [countP_memB_nil]
      exact Nat.zero_le _
  | cons y ys ih =>
      rw [countP_congr (l := l) (fun i _ => memB_cons i y ys)]
      apply Nat.le_trans
        (countP_or_le (fun i => decide (i = y)) (fun i => memB i ys) l)
      apply Nat.le_trans
        (Nat.add_le_add (countP_id_le_one (a := y) hl) (ih l hl))
      rw [List.length_cons, Nat.add_comm]

theorem countP_or_add {α : Type} (p q : α → Bool) (l : List α)
    (disj : ∀ a ∈ l, p a = true → q a = true → False) :
    l.countP (fun a => p a || q a) = l.countP p + l.countP q := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have disj' : ∀ b ∈ l, p b = true → q b = true → False :=
        fun b hb => disj b (List.mem_cons_of_mem a hb)
      cases hp : p a <;> cases hq : q a
      · have hor : (p a || q a) = false := by rw [hp, hq]; rfl
        rw [List.countP_cons_of_neg (p := fun b => p b || q b) (not_bool_eq hor),
          List.countP_cons_of_neg (not_bool_eq hp),
          List.countP_cons_of_neg (not_bool_eq hq), ih disj']
      · have hor : (p a || q a) = true := by rw [hp, hq]; rfl
        rw [List.countP_cons_of_pos (p := fun b => p b || q b) hor,
          List.countP_cons_of_neg (not_bool_eq hp),
          List.countP_cons_of_pos hq, ih disj', Nat.add_assoc]
      · have hor : (p a || q a) = true := by rw [hp, hq]; rfl
        rw [List.countP_cons_of_pos (p := fun b => p b || q b) hor,
          List.countP_cons_of_pos hp,
          List.countP_cons_of_neg (not_bool_eq hq), ih disj',
          Nat.add_assoc, Nat.add_comm (l.countP q) 1, ← Nat.add_assoc]
      · exact absurd hq (disj a List.mem_cons_self hp)

theorem countP_mem_eq {α : Type} [DecidableEq α] {l ys : List α}
    (hl : l.Nodup) (hys : ys.Nodup) (sub : ∀ y ∈ ys, y ∈ l) :
    l.countP (fun i => memB i ys) = ys.length := by
  induction ys with
  | nil =>
      rw [countP_memB_nil]
      rfl
  | cons y ys ih =>
      have y_not : y ∉ ys := by
        intro hy
        exact (List.pairwise_cons.mp hys).1 y hy rfl
      have y_in : y ∈ l := sub y List.mem_cons_self
      have ys_sub : ∀ z ∈ ys, z ∈ l := fun z hz => sub z (List.mem_cons_of_mem y hz)
      have disj : ∀ i ∈ l, decide (i = y) = true → memB i ys = true → False := by
        intro i _ hi hmem
        exact y_not ((of_decide_eq_true hi) ▸ memB_true hmem)
      rw [countP_congr (l := l) (fun i _ => memB_cons i y ys),
        countP_or_add _ _ l disj, countP_id_one hl y_in,
        ih (List.Pairwise.of_cons hys) ys_sub, Nat.add_comm, List.length_cons]

theorem countP_map {α β : Type} (f : α → β) (p : β → Bool) (l : List α) :
    (l.map f).countP p = l.countP (fun a => p (f a)) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      rw [List.map_cons, List.countP_cons, List.countP_cons, ih]

theorem countP_val_lt {n k : Nat} (hk : k ≤ n) :
    (List.finRange n).countP (fun i : Fin n => decide (i.val < k)) = k := by
  induction n generalizing k with
  | zero =>
      cases Nat.le_zero.mp hk
      rw [List.finRange_zero, List.countP_nil]
  | succ n ih =>
      cases k with
      | zero =>
          rw [countP_congr (q := fun _ => false) (fun i _ =>
            decide_eq_false (Nat.not_lt_zero i.val))]
          exact countP_const_false _
      | succ k =>
          rw [List.finRange_succ, List.countP_cons]
          have h0 : decide ((0 : Fin (n + 1)).val < Nat.succ k) = true :=
            decide_eq_true (Nat.zero_lt_succ k)
          rw [h0, countP_map]
          have hfun : ∀ a ∈ List.finRange n,
              decide ((Fin.succ a).val < k.succ) = decide (a.val < k) := by
            intro j _
            have hv : ((Fin.succ j) : Nat) = j + 1 := Fin.val_succ j
            by_cases hj : j.val < k
            · have hs : (Fin.succ j).val < k.succ := by
                rw [hv]
                exact Nat.succ_lt_succ hj
              rw [decide_eq_true hs, decide_eq_true hj]
            · have hs : ¬ (Fin.succ j).val < k.succ := by
                rw [hv]
                intro hlt
                exact hj (Nat.lt_of_succ_lt_succ hlt)
              rw [decide_eq_false hs, decide_eq_false hj]
          rw [countP_congr hfun, ih (Nat.le_of_succ_le_succ hk), if_pos rfl]

theorem yesCount_word (choice : Fin 11 → Side) :
    yesCount (voteO.final (wordOf choice) voteInitial) =
      (List.finRange 11).countP (fun i => sideBit (choice i)) := by
  unfold yesCount
  exact countP_congr (fun i _ => by simp [cellBit, word_cell choice i])

theorem allYes_count :
    yesCount (voteO.final (wordOf allYes) voteInitial) = 11 := by
  rw [yesCount_word]
  have hfun : ∀ i ∈ List.finRange 11, sideBit (allYes i) = true := fun _ _ => rfl
  rw [countP_congr hfun, List.countP_eq_length.mpr (fun _ _ => rfl), List.length_finRange]

theorem split_count :
    yesCount (voteO.final (wordOf splitChoice) voteInitial) = 6 := by
  rw [yesCount_word]
  have hfun : ∀ i ∈ List.finRange 11,
      sideBit (splitChoice i) = decide (i.val < 6) := by
    intro i _
    by_cases h : i.val < 6
    · simp [splitChoice, sideBit, h]
    · simp [splitChoice, sideBit, h]
  rw [countP_congr hfun]
  exact countP_val_lt (by decide : 6 ≤ 11)

theorem allYes_majority : majority (voteO.final (wordOf allYes) voteInitial) := by
  unfold majority
  rw [allYes_count]
  decide

theorem split_majority : majority (voteO.final (wordOf splitChoice) voteInitial) := by
  unfold majority
  rw [split_count]

theorem side_of_mem {choice : Fin 11 → Side} {i : Fin 11} {s : Side}
    (h : .cast i s ∈ wordOf choice) : choice i = s := by
  rcases List.mem_map.1 h with ⟨_, _, heq⟩
  cases heq
  rfl

theorem allYes_writes (cell : Fin 11) :
    ∀ i ∈ wordOf allYes,
      (voteO.footprint i).writes cell = none ∨
        (voteO.footprint i).writes cell = some true := by
  intro i hi
  rcases List.mem_map.1 hi with ⟨j, _, rfl⟩
  by_cases h : j = cell
  · rw [h]
    exact Or.inr (voteWrite_at cell .yes)
  · exact Or.inl (voteWrite_other j cell .yes h)

theorem outside_count (drop : List (Fin 11)) :
    (List.finRange 11).countP (fun i => ! memB i drop) =
      11 - (List.finRange 11).countP (fun i => memB i drop) := by
  have h := List.length_eq_countP_add_countP (fun i => memB i drop)
    (l := List.finRange 11)
  rw [List.length_finRange] at h
  have hbang : ∀ i ∈ List.finRange 11,
      decide (¬ memB i drop = true) = ! memB i drop :=
    fun i _ => (bang_not _).symm
  rw [countP_congr hbang] at h
  have sum : (List.finRange 11).countP (fun i => memB i drop) +
      (List.finRange 11).countP (fun i => ! memB i drop) = 11 := h.symm
  have back : (List.finRange 11).countP (fun i => ! memB i drop) =
      (List.finRange 11).countP (fun i => memB i drop) +
        (List.finRange 11).countP (fun i => ! memB i drop) -
      (List.finRange 11).countP (fun i => memB i drop) :=
    (Nat.add_sub_cancel_left _ _).symm
  rw [back, sum]

theorem few_outside (drop : List (Fin 11))
    (hfew : (List.finRange 11).countP (fun i => memB i drop) ≤ 5) :
    6 ≤ (List.finRange 11).countP (fun i => ! memB i drop) := by
  rw [outside_count]
  exact Nat.le_trans (by decide : 6 ≤ 11 - 5) (Nat.sub_le_sub_left hfew 11)

theorem allYes_alt_bit (drop : List (Fin 11)) (i : Fin 11) :
    sideBit (altChoice allYes drop i) = ! memB i drop := by
  unfold altChoice allYes sideBit
  cases memB i drop <;> rfl

theorem allYes_alt_count (drop : List (Fin 11)) :
    yesCount (voteO.final (altWord allYes drop) voteInitial) =
      (List.finRange 11).countP (fun i => ! memB i drop) := by
  rw [altWord, yesCount_word]
  exact countP_congr (fun i _ => allYes_alt_bit drop i)

theorem unanimous_few_not_ac2 (X : List VoteId)
    (hfew : (List.finRange 11).countP (fun i => memB i (votersOf X)) ≤ 5) :
    ¬ AC2 voteO (wordOf allYes) voteInitial majority (VoteRetained allYes) X := by
  intro held
  rcases held with ⟨keep, _, _, _, fork, _, falsifies⟩
  cases fork
  have base : 6 ≤ yesCount (voteO.final (altWord allYes (votersOf X)) voteInitial) := by
    rw [allYes_alt_count]
    exact few_outside (votersOf X) hfew
  have mono : yesCount (voteO.final (altWord allYes (votersOf X)) voteInitial) ≤
      yesCount (pinWrites voteO keep (wordOf allYes)
        (voteO.final (altWord allYes (votersOf X)) voteInitial)) := by
    refine yesCount_mono ?_
    intro cell htrue
    have kept := pinWrites_keeps_payload voteO keep (wordOf allYes) cell true
      (voteO.final (altWord allYes (votersOf X)) voteInitial) htrue (allYes_writes cell)
    exact kept
  exact falsifies (Nat.le_trans base mono)

theorem count_le_length_voters (X : List VoteId) :
    (List.finRange 11).countP (fun i => memB i (votersOf X)) ≤ X.length := by
  have h := countP_mem_le (votersOf X) (List.finRange 11) (nodup_finRange 11)
  rw [votersOf, List.length_map] at h
  exact h

theorem unanimous_short_not_cause (X : List VoteId) (h : X.length ≤ 5) :
    ¬ ActualCause voteO (wordOf allYes) voteInitial majority (VoteRetained allYes) X := by
  intro cause
  exact unanimous_few_not_ac2 X (Nat.le_trans (count_le_length_voters X) h) cause.2.1

theorem unanimous_cause_long (X : List VoteId)
    (cause : ActualCause voteO (wordOf allYes) voteInitial majority (VoteRetained allYes) X) :
    6 ≤ X.length := by
  by_contra short
  have hle : X.length ≤ 5 := Nat.lt_succ_iff.mp ((Nat.not_le).mp short)
  exact unanimous_short_not_cause X hle cause

def others (v : Fin 11) : List (Fin 11) :=
  ((List.finRange 11).filter fun i => decide (i ≠ v)).take 5

def pick (v : Fin 11) : List (Fin 11) :=
  v :: others v

theorem filter_ne_length (v : Fin 11) :
    ((List.finRange 11).filter fun i => decide (i ≠ v)).length = 10 := by
  rw [← List.countP_eq_length_filter]
  have one := countP_id_one (nodup_finRange 11) (List.mem_finRange v)
  have split := List.length_eq_countP_add_countP (fun i : Fin 11 => decide (i = v))
    (l := List.finRange 11)
  rw [List.length_finRange, one] at split
  have sum : 1 + (List.finRange 11).countP (fun i => ¬ decide (i = v)) = 11 := split.symm
  have hne : ∀ i ∈ List.finRange 11,
      decide (i ≠ v) = ! decide (i = v) := fun i _ => decide_ne_not i v
  have hbang : ∀ i ∈ List.finRange 11,
      (! decide (i = v)) = decide (¬ decide (i = v) = true) := fun i _ => bang_not _
  rw [countP_congr hne, countP_congr hbang]
  have back : (List.finRange 11).countP (fun i => ¬ decide (i = v)) =
      1 + (List.finRange 11).countP (fun i => ¬ decide (i = v)) - 1 :=
    (Nat.add_sub_cancel_left 1 _).symm
  rw [back, sum]

theorem others_length (v : Fin 11) : (others v).length = 5 := by
  unfold others
  exact List.length_take_of_le (by rw [filter_ne_length]; decide)

theorem pick_length (v : Fin 11) : (pick v).length = 6 := by
  rw [pick, List.length_cons, others_length]

theorem v_not_filtered (v : Fin 11) :
    v ∉ (List.finRange 11).filter fun i => decide (i ≠ v) := by
  intro h
  have ht := (List.mem_filter.mp h).2
  exact absurd rfl (of_decide_eq_true ht)

theorem v_not_others (v : Fin 11) : v ∉ others v := by
  intro h
  exact v_not_filtered v (List.mem_of_mem_take h)

theorem nodup_filter_ne (v : Fin 11) :
    ((List.finRange 11).filter fun i => decide (i ≠ v)).Nodup :=
  List.Pairwise.filter _ (nodup_finRange 11)

theorem pick_nodup (v : Fin 11) : (pick v).Nodup := by
  unfold pick
  refine List.Pairwise.cons ?_ (List.Pairwise.take (nodup_filter_ne v))
  intro a ha eq
  exact v_not_others v (eq.symm ▸ ha)

theorem pick_sub (v : Fin 11) : ∀ i ∈ pick v, i ∈ List.finRange 11 := by
  intro i hi
  exact List.mem_finRange i

theorem pick_count (v : Fin 11) :
    (List.finRange 11).countP (fun i => memB i (pick v)) = 6 := by
  rw [countP_mem_eq (nodup_finRange 11) (pick_nodup v) (pick_sub v), pick_length]

def causeVotes (v : Fin 11) : List VoteId :=
  (pick v).map fun i => .cast i .yes

theorem voters_cause (v : Fin 11) : votersOf (causeVotes v) = pick v := by
  unfold causeVotes votersOf
  induction pick v with
  | nil => rfl
  | cons a as ih =>
      rw [List.map_cons, List.map_cons (f := voter)]
      have ha : voter (VoteId.cast a .yes) = a := rfl
      rw [ha, ih]

theorem cause_length (v : Fin 11) : (causeVotes v).length = 6 := by
  rw [causeVotes, List.length_map, pick_length]

theorem cause_has (v : Fin 11) : .cast v .yes ∈ causeVotes v := by
  unfold causeVotes pick
  exact List.mem_map.2 ⟨v, List.mem_cons_self, rfl⟩

theorem cause_members (v : Fin 11) :
    ∀ i ∈ causeVotes v, i ∈ wordOf allYes := by
  intro occ hocc
  rcases List.mem_map.1 hocc with ⟨w, _, rfl⟩
  exact List.mem_map.2 ⟨w, List.mem_finRange w, rfl⟩

theorem yes_not_in_no_alt (drop : List (Fin 11)) {i : Fin 11} (hi : i ∈ drop) :
    .cast i .yes ∉ altWord allYes drop := by
  intro hm
  have hs := side_of_mem hm
  unfold altChoice at hs
  rw [memB_of_mem hi] at hs
  cases hs

theorem cause_drops (v : Fin 11) :
    ∀ i ∈ causeVotes v, i ∉ altWord allYes (pick v) := by
  intro occ hocc
  rcases List.mem_map.1 hocc with ⟨w, hw, rfl⟩
  exact yes_not_in_no_alt (pick v) hw

theorem cause_alt_count (v : Fin 11) :
    yesCount (voteO.final (altWord allYes (pick v)) voteInitial) = 5 := by
  rw [allYes_alt_count, outside_count, pick_count]

theorem cause_ac2 (v : Fin 11) :
    AC2 voteO (wordOf allYes) voteInitial majority (VoteRetained allYes) (causeVotes v) := by
  refine ⟨fun _ => false, altWord allYes (pick v), ?_, ?_, ?_, ?_, ?_⟩
  · intro _ hi; cases hi
  · intro _ hi; cases hi
  · have held : VoteRetained allYes (causeVotes v)
        (altWord allYes (votersOf (causeVotes v))) := VoteRetained.flip
    rw [voters_cause] at held
    exact held
  · exact cause_drops v
  · rw [pinWrites_const_false voteO (wordOf allYes)
        (voteO.final (altWord allYes (pick v)) voteInitial)]
    intro held
    have few := cause_alt_count v
    have : 6 ≤ 5 := by
      unfold majority at held
      rw [few] at held
      exact held
    exact Nat.not_succ_le_self 5 this

theorem missing_voter (v : Fin 11) {Y : List VoteId}
    (sub : ProperSubset Y (causeVotes v)) :
    ∃ w, w ∈ pick v ∧ ∀ i ∈ votersOf Y, i ∈ pick v ∧ i ≠ w := by
  rcases sub with ⟨into, missing, inX, notInY⟩
  rcases List.mem_map.1 inX with ⟨w, hw, rfl⟩
  refine ⟨w, hw, ?_⟩
  intro i hi
  rcases List.mem_map.1 hi with ⟨occ, hocc, heqv⟩
  have inCause := into occ hocc
  rcases List.mem_map.1 inCause with ⟨w', hw', rfl⟩
  cases heqv
  refine ⟨hw', ?_⟩
  intro eq
  exact notInY (eq ▸ hocc)

theorem boolAnd {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  cases a <;> cases b
  · cases h
  · cases h
  · cases h
  · exact ⟨rfl, rfl⟩

theorem count_without (v w : Fin 11) (hw : w ∈ pick v) (ys : List (Fin 11))
    (hys : ∀ i ∈ ys, i ∈ pick v ∧ i ≠ w) :
    (List.finRange 11).countP (fun i => memB i ys) ≤ 5 := by
  have hmono : (List.finRange 11).countP (fun i => memB i ys) ≤
      (List.finRange 11).countP (fun i => memB i (pick v) && decide (i ≠ w)) := by
    refine countP_mono ?_
    intro i _ hp
    rcases hys i (memB_true hp) with ⟨hin, hne⟩
    have hinb : memB i (pick v) = true := memB_of_mem hin
    have hneb : decide (i ≠ w) = true := decide_eq_true hne
    rw [hinb, hneb]
    rfl
  have hone : (List.finRange 11).countP
      (fun i => memB i (pick v) && decide (i = w)) = 1 := by
    have hfun : ∀ i ∈ List.finRange 11,
        (memB i (pick v) && decide (i = w)) = decide (i = w) := by
      intro i _
      cases h : decide (i = w)
      · cases memB i (pick v) <;> rfl
      · rw [memB_of_mem (by
          have : i = w := of_decide_eq_true h
          rw [this]
          exact hw)]
        rfl
    rw [countP_congr hfun]
    exact countP_id_one (nodup_finRange 11) (List.mem_finRange w)
  have hsum : (List.finRange 11).countP (fun i => memB i (pick v)) =
      (List.finRange 11).countP (fun i => memB i (pick v) && decide (i = w)) +
      (List.finRange 11).countP (fun i => memB i (pick v) && decide (i ≠ w)) := by
    have hfun : ∀ i ∈ List.finRange 11,
        memB i (pick v) =
          ((memB i (pick v) && decide (i = w)) ||
            (memB i (pick v) && decide (i ≠ w))) := by
      intro i _
      rw [decide_ne_not i w]
      exact bool_cover (memB i (pick v)) (decide (i = w))
    rw [countP_congr hfun]
    refine countP_or_add _ _ _ ?_
    intro i _ hp hq
    rcases boolAnd hp with ⟨_, heq⟩
    rcases boolAnd hq with ⟨_, hne⟩
    exact of_decide_eq_true hne (of_decide_eq_true heq)
  rw [pick_count v, hone] at hsum
  have hfive : (List.finRange 11).countP
      (fun i => memB i (pick v) && decide (i ≠ w)) = 5 := by
    have hsum' : 1 + (List.finRange 11).countP
        (fun i => memB i (pick v) && decide (i ≠ w)) = 6 := hsum.symm
    have hsub := congrArg (fun n => n - 1) hsum'
    rw [Nat.add_sub_cancel_left] at hsub
    exact hsub
  rw [hfive] at hmono
  exact hmono

theorem proper_few (v : Fin 11) {Y : List VoteId}
    (sub : ProperSubset Y (causeVotes v)) :
    (List.finRange 11).countP (fun i => memB i (votersOf Y)) ≤ 5 := by
  rcases missing_voter v sub with ⟨w, hw, hys⟩
  exact count_without v w hw (votersOf Y) hys

theorem cause_ac3 (v : Fin 11) :
    AC3 voteO (wordOf allYes) voteInitial majority (VoteRetained allYes) (causeVotes v) := by
  intro Y sub both
  exact unanimous_few_not_ac2 Y (proper_few v sub) both.2

theorem cause_ac1 (v : Fin 11) :
    AC1 voteO (wordOf allYes) voteInitial majority (causeVotes v) :=
  ⟨⟨.cast v .yes, cause_has v⟩, cause_members v, allYes_majority⟩

theorem unanimous_voter_cause (v : Fin 11) :
    ActualCause voteO (wordOf allYes) voteInitial majority (VoteRetained allYes)
      (causeVotes v) :=
  ⟨cause_ac1 v, cause_ac2 v, cause_ac3 v⟩

/-- Each voter in an 11–0 majority has degree `1/6`. -/
theorem unanimous_degree (v : Fin 11) :
    PositiveDegree voteO (wordOf allYes) voteInitial majority (VoteRetained allYes)
      (.cast v .yes) 6 :=
  ⟨Nat.succ_pos 5,
    ⟨causeVotes v, cause_has v, unanimous_voter_cause v, cause_length v⟩,
    fun X _ cause => unanimous_cause_long X cause⟩

/-! ## A 6–5 vote -/

theorem split_yes_writes (cell : Fin 11) (hcell : cell.val < 6) :
    ∀ i ∈ wordOf splitChoice,
      (voteO.footprint i).writes cell = none ∨
        (voteO.footprint i).writes cell = some true := by
  intro i hi
  rcases List.mem_map.1 hi with ⟨j, _, rfl⟩
  by_cases h : j = cell
  · rw [h]
    have hyes : splitChoice cell = .yes := by
      unfold splitChoice
      exact if_pos hcell
    rw [hyes]
    exact Or.inr (voteWrite_at cell .yes)
  · exact Or.inl (voteWrite_other j cell (splitChoice j) h)

theorem split_alt_bit (v : Fin 11) (i : Fin 11) :
    sideBit (altChoice splitChoice [v] i) =
      (decide (i ≠ v) && decide (i.val < 6)) := by
  cases h : decide (i = v)
  · have hne : i ≠ v := of_decide_eq_false h
    have hmem : memB i [v] = false := by
      rw [memB, h, memB]
      rfl
    have hleft : sideBit (altChoice splitChoice [v] i) = sideBit (splitChoice i) := by
      unfold altChoice
      rw [hmem]
      rfl
    have hsplit : sideBit (splitChoice i) = decide (i.val < 6) := by
      unfold splitChoice sideBit
      cases hlt : decide (i.val < 6)
      · rw [if_neg (of_decide_eq_false hlt)]
      · rw [if_pos (of_decide_eq_true hlt)]
    have hright : (decide (i ≠ v) && decide (i.val < 6)) = decide (i.val < 6) := by
      rw [decide_eq_true hne]
      rfl
    rw [hleft, hsplit, hright]
  · have heq : i = v := of_decide_eq_true h
    rw [heq]
    have hmem : memB v [v] = true := by
      rw [memB, decide_eq_true rfl]
      rfl
    have hleft : sideBit (altChoice splitChoice [v] v) = false := by
      unfold altChoice sideBit
      rw [hmem]
      rfl
    have hright : (decide (v ≠ v) && decide (v.val < 6)) = false := by
      rw [decide_eq_false (fun hn : v ≠ v => hn rfl)]
      rfl
    rw [hleft, hright]

theorem split_singleton_count (v : Fin 11) (hv : v.val < 6) :
    yesCount (voteO.final (altWord splitChoice [v]) voteInitial) = 5 := by
  rw [altWord, yesCount_word, countP_congr (fun i _ => split_alt_bit v i)]
  have hall := countP_val_lt (n := 11) (k := 6) (by decide)
  have hone : (List.finRange 11).countP (fun i => decide (i = v)) = 1 :=
    countP_id_one (nodup_finRange 11) (List.mem_finRange v)
  have hsplit : (List.finRange 11).countP (fun i => decide (i.val < 6)) =
      (List.finRange 11).countP (fun i => decide (i.val < 6) && decide (i = v)) +
      (List.finRange 11).countP (fun i => decide (i.val < 6) && ! decide (i = v)) := by
    rw [countP_congr (fun i _ => bool_cover (decide (i.val < 6)) (decide (i = v)))]
    refine countP_or_add _ _ _ ?_
    intro i _ hp hq
    rcases boolAnd hp with ⟨_, heq⟩
    rcases boolAnd hq with ⟨_, hne⟩
    rw [heq] at hne
    cases hne
  have heq_one : (List.finRange 11).countP
      (fun i => decide (i.val < 6) && decide (i = v)) = 1 := by
    have hfun : ∀ i ∈ List.finRange 11,
        (decide (i.val < 6) && decide (i = v)) = decide (i = v) := by
      intro i _
      cases h : decide (i = v)
      · cases decide (i.val < 6) <;> rfl
      · have hv' : i.val < 6 := by
          have : i = v := of_decide_eq_true h
          rw [this]
          exact hv
        rw [decide_eq_true hv']
        rfl
    rw [countP_congr hfun, hone]
  have hbridge : ∀ i ∈ List.finRange 11,
      (decide (i.val < 6) && ! decide (i = v)) =
        (decide (i.val < 6) && decide (i ≠ v)) := by
    intro i _
    exact congrArg (fun b => decide (i.val < 6) && b) (decide_ne_not i v).symm
  rw [countP_congr hbridge] at hsplit
  rw [hall, heq_one] at hsplit
  have hrest : (List.finRange 11).countP
      (fun i => decide (i.val < 6) && decide (i ≠ v)) = 5 := by
    have hsum' : 1 + (List.finRange 11).countP
        (fun i => decide (i.val < 6) && decide (i ≠ v)) = 6 := hsplit.symm
    have hsub := congrArg (fun n => n - 1) hsum'
    rw [Nat.add_sub_cancel_left] at hsub
    exact hsub
  rw [countP_congr (fun i _ => Bool.and_comm (decide (i ≠ v)) (decide (i.val < 6))), hrest]

theorem split_yes_ac2 (v : Fin 11) (hv : v.val < 6) :
    AC2 voteO (wordOf splitChoice) voteInitial majority (VoteRetained splitChoice)
      [.cast v .yes] := by
  refine ⟨fun _ => false, altWord splitChoice [v], ?_, ?_, ?_, ?_, ?_⟩
  · intro _ hi; cases hi
  · intro _ hi; cases hi
  · have hvoters : votersOf [VoteId.cast v .yes] = [v] := rfl
    have held : VoteRetained splitChoice [VoteId.cast v .yes]
        (altWord splitChoice (votersOf [VoteId.cast v .yes])) := VoteRetained.flip
    rw [hvoters] at held
    exact held
  · intro occ hocc
    cases hocc with
    | head _ =>
        intro hm
        have hs := side_of_mem hm
        unfold altChoice at hs
        have hm : memB v [v] = true := by
          rw [memB, decide_eq_true rfl]
          rfl
        rw [hm] at hs
        cases hs
    | tail _ h => cases h
  · rw [pinWrites_const_false voteO (wordOf splitChoice)
        (voteO.final (altWord splitChoice [v]) voteInitial)]
    intro held
    have few := split_singleton_count v hv
    have : 6 ≤ 5 := by
      unfold majority at held
      rw [few] at held
      exact held
    exact Nat.not_succ_le_self 5 this

theorem split_yes_ac1 (v : Fin 11) (hv : v.val < 6) :
    AC1 voteO (wordOf splitChoice) voteInitial majority [VoteId.cast v .yes] :=
  ⟨⟨VoteId.cast v .yes, List.mem_cons_self⟩,
    singleton_members (by
      have hyes : splitChoice v = .yes := by
        unfold splitChoice
        exact if_pos hv
      exact List.mem_map.2 ⟨v, List.mem_finRange v, by rw [hyes]⟩),
    split_majority⟩

/-- A majority voter in a 6–5 vote has degree 1. -/
theorem split_majority_degree (v : Fin 11) (hv : v.val < 6) :
    PositiveDegree voteO (wordOf splitChoice) voteInitial majority (VoteRetained splitChoice)
      (.cast v .yes) 1 :=
  ⟨Nat.succ_pos 0,
    ⟨[.cast v .yes], List.mem_cons_self,
      ⟨split_yes_ac1 v hv, split_yes_ac2 v hv,
        ac3_singleton voteO (wordOf splitChoice) voteInitial majority (VoteRetained splitChoice)
          (fun i => mem_singleton (a := VoteId.cast v .yes) (i := i))⟩, rfl⟩,
    fun _ memX _ => length_ge_one memX⟩

theorem no_yes_voter (X : List VoteId)
    (h : ∀ i ∈ votersOf X, ¬ i.val < 6) (cell : Fin 11) (hcell : cell.val < 6) :
    cell ∉ votersOf X := by
  intro hm
  exact h cell hm hcell

theorem minority_alt_keeps (X : List VoteId)
    (h : ∀ i ∈ votersOf X, ¬ i.val < 6) (cell : Fin 11) (hcell : cell.val < 6) :
    sideBit (altChoice splitChoice (votersOf X) cell) = true := by
  have hnot := no_yes_voter X h cell hcell
  unfold altChoice splitChoice sideBit
  rw [memB_of_not hnot, if_pos hcell]
  rfl

theorem minority_not_ac2 (X : List VoteId)
    (h : ∀ i ∈ votersOf X, ¬ i.val < 6) :
    ¬ AC2 voteO (wordOf splitChoice) voteInitial majority (VoteRetained splitChoice) X := by
  intro held
  rcases held with ⟨keep, _, _, _, fork, _, falsifies⟩
  cases fork
  have base : 6 ≤ yesCount (voteO.final (altWord splitChoice (votersOf X)) voteInitial) := by
    rw [altWord, yesCount_word]
    have hbit : ∀ i ∈ List.finRange 11,
        decide (i.val < 6) = true →
          sideBit (altChoice splitChoice (votersOf X) i) = true := by
      intro i _ ht
      exact minority_alt_keeps X h i (of_decide_eq_true ht)
    have hcount : (List.finRange 11).countP (fun i => decide (i.val < 6)) ≤
        (List.finRange 11).countP (fun i => sideBit (altChoice splitChoice (votersOf X) i)) :=
      countP_mono hbit
    rw [countP_val_lt (by decide : 6 ≤ 11)] at hcount
    exact hcount
  have mono : yesCount (voteO.final (altWord splitChoice (votersOf X)) voteInitial) ≤
      yesCount (pinWrites voteO keep (wordOf splitChoice)
        (voteO.final (altWord splitChoice (votersOf X)) voteInitial)) := by
    refine yesCount_mono ?_
    intro cell htrue
    by_cases hcell : cell.val < 6
    · exact pinWrites_keeps_payload voteO keep (wordOf splitChoice) cell true
        (voteO.final (altWord splitChoice (votersOf X)) voteInitial) htrue
        (split_yes_writes cell hcell)
    · have hfalse : ((voteO.final (altWord splitChoice (votersOf X)) voteInitial) cell).1
          = false := by
        rw [altWord, word_cell]
        unfold altChoice splitChoice sideBit
        cases memB cell (votersOf X)
        · rw [if_neg hcell]
          rfl
        · rfl
      exact absurd htrue (not_true_of_false hfalse)
  exact falsifies (Nat.le_trans base mono)

theorem voter_of_actual {occ : VoteId} (h : occ ∈ wordOf splitChoice) :
    occ = .cast (voter occ) (splitChoice (voter occ)) := by
  rcases List.mem_map.1 h with ⟨_, _, rfl⟩
  rfl

/-- The first majority `yes` voter in a candidate, if there is one. -/
def findYes : List VoteId → Option (Fin 11)
  | [] => none
  | .cast u .yes :: rest =>
      cond (decide (u.val < 6)) (some u) (findYes rest)
  | .cast _ .no :: rest => findYes rest

theorem findYes_no (w : Fin 11) (rest : List VoteId) :
    findYes (VoteId.cast w .no :: rest) = findYes rest :=
  rfl

theorem findYes_yes_low (w : Fin 11) (rest : List VoteId)
    (hlt : decide (w.val < 6) = true) :
    findYes (VoteId.cast w .yes :: rest) = some w := by
  rw [findYes, hlt]
  rfl

theorem findYes_yes_high (w : Fin 11) (rest : List VoteId)
    (hge : decide (w.val < 6) = false) :
    findYes (VoteId.cast w .yes :: rest) = findYes rest := by
  rw [findYes, hge]
  rfl

theorem findYes_some {X : List VoteId} {u : Fin 11}
    (h : findYes X = some u) : u.val < 6 ∧ VoteId.cast u .yes ∈ X := by
  induction X generalizing u with
  | nil =>
      rw [findYes] at h
      cases h
  | cons head rest ih =>
      cases head with
      | cast w s =>
          cases s with
          | no =>
              rw [findYes_no] at h
              rcases ih h with ⟨hu, hmem⟩
              exact ⟨hu, List.Mem.tail _ hmem⟩
          | yes =>
              cases hd : decide (w.val < 6)
              · rw [findYes_yes_high w rest hd] at h
                rcases ih h with ⟨hu, hmem⟩
                exact ⟨hu, List.Mem.tail _ hmem⟩
              · rw [findYes_yes_low w rest hd] at h
                cases h
                exact ⟨of_decide_eq_true hd, List.mem_cons_self⟩

theorem findYes_isSome {X : List VoteId} {u : Fin 11}
    (h : VoteId.cast u .yes ∈ X) (hu : u.val < 6) : ∃ w, findYes X = some w := by
  induction X with
  | nil => cases h
  | cons head rest ih =>
      cases h with
      | head _ =>
          refine ⟨u, ?_⟩
          rw [findYes, decide_eq_true hu]
          rfl
      | tail _ ht =>
          cases head with
          | cast w s =>
              cases s with
              | no =>
                  rcases ih ht with ⟨w', hw⟩
                  refine ⟨w', ?_⟩
                  rw [findYes]
                  exact hw
              | yes =>
                  cases hd : decide (w.val < 6)
                  · rcases ih ht with ⟨w', hw⟩
                    refine ⟨w', ?_⟩
                    rw [findYes, hd]
                    exact hw
                  · refine ⟨w, ?_⟩
                    rw [findYes, hd]
                    rfl

theorem split_minority_degree (v : Fin 11) (_hv : ¬ v.val < 6) :
    NoResponsibility voteO (wordOf splitChoice) voteInitial majority (VoteRetained splitChoice)
      (VoteId.cast v .no) := by
  intro ⟨X, hmem, cause⟩
  have occ : VoteId.cast v .no ∈ X := hmem
  cases hf : findYes X with
  | some u =>
      rcases findYes_some hf with ⟨hu, huX⟩
      have uneq : VoteId.cast u .yes ≠ VoteId.cast v .no := by
        intro eq
        cases eq
      exact cause.2.2 [VoteId.cast u .yes]
        ⟨singleton_members huX, VoteId.cast v .no, occ, by
          intro hm
          exact uneq (mem_singleton.mp hm).symm⟩
        ⟨split_yes_ac1 u hu, split_yes_ac2 u hu⟩
  | none =>
      have hno : ∀ i ∈ votersOf X, ¬ i.val < 6 := by
        intro i hi hlt
        rcases List.mem_map.1 hi with ⟨occ', hocc', rfl⟩
        have inA := cause.1.2.1 occ' hocc'
        have sh := voter_of_actual inA
        have side : splitChoice (voter occ') = .yes := by
          unfold splitChoice
          rw [if_pos hlt]
        have hmemYes : VoteId.cast (voter occ') .yes ∈ X := by
          rw [sh, side] at hocc'
          exact hocc'
        rcases findYes_isSome hmemYes hlt with ⟨w, hw⟩
        rw [hf] at hw
        cases hw
      exact minority_not_ac2 X hno cause.2.1

/-! ## Graded causation -/

/-- Normality of a witness, in the sense of Halpern and Hitchcock (2015).
The witness sets the voters in `drop` to `no`. A smaller sum of their indices
is more normal. A cause is ranked by this witness. -/
def witnessNormality (drop : List (Fin 11)) : Nat :=
  drop.foldl (fun acc i => acc + i.val) 0

def causeGrade (v : Fin 11) : Nat :=
  witnessNormality (pick v)

/-- Both voters have degree `1/6`. The witness for voter 0 is more normal. -/
theorem graded_same_degree_different_rank :
    PositiveDegree voteO (wordOf allYes) voteInitial majority (VoteRetained allYes)
      (VoteId.cast 0 .yes) 6 ∧
    PositiveDegree voteO (wordOf allYes) voteInitial majority (VoteRetained allYes)
      (VoteId.cast ⟨10, by decide⟩ .yes) 6 ∧
    causeGrade 0 < causeGrade ⟨10, by decide⟩ := by
  refine ⟨unanimous_degree 0, unanimous_degree ⟨10, by decide⟩, ?_⟩
  decide

/-! ## Blame -/

structure Ratio where
  num : Nat
  den : Nat
  deriving DecidableEq

def responsibilityRatio (k : Nat) : Ratio :=
  if k = 0 then ⟨0, 1⟩ else ⟨1, k⟩

def lcmAll : List Nat → Nat
  | [] => 1
  | d :: ds => Nat.lcm d (lcmAll ds)

/-- Weighted sum of responsibility ratios. A pair is a weight and a degree. -/
def expect (ws : List (Nat × Nat)) : Ratio :=
  let ratios := ws.map fun wk => (wk.1, responsibilityRatio wk.2)
  let common := lcmAll (ratios.map fun wr => wr.2.den)
  let num := ratios.foldl (fun acc wr => acc + wr.1 * wr.2.num * (common / wr.2.den)) 0
  let weight := ratios.foldl (fun acc wr => acc + wr.1) 0
  ⟨num, weight * common⟩

structure Situation where
  weight : Nat
  degree : Nat
  deriving DecidableEq

/-- What the agent knows: weighted situations, and which one occurred.
Blame reads only the situations. -/
structure Knowledge where
  worlds : List Situation
  actual : Nat

def blame (k : Knowledge) : Ratio :=
  expect (k.worlds.map fun s => (s.weight, s.degree))

theorem blame_ignores_actual (k₁ k₂ : Knowledge) (h : k₁.worlds = k₂.worlds) :
    blame k₁ = blame k₂ := by
  simp [blame, h]

/-- Weight 2 on the preemption word, where Suzy's degree is 1, and weight 1 on
the word where she is absent and Billy's hit breaks the bottle. -/
def uncertain : List Situation := [⟨2, 1⟩, ⟨1, 0⟩]

theorem uncertain_blame : blame ⟨uncertain, 0⟩ = ⟨2, 3⟩ := rfl

theorem blame_same_either_world :
    blame ⟨uncertain, 0⟩ = blame ⟨uncertain, 1⟩ :=
  blame_ignores_actual ⟨uncertain, 0⟩ ⟨uncertain, 1⟩ rfl

theorem suzy_absent_word : PreemptId.suzyThrow ∉ suzyAlt := by decide

theorem absent_breaks :
    preemptBreaks (preemptO.final suzyAlt preemptInitial) :=
  Or.inr suzyAlt_bh

theorem actual_breaks :
    preemptBreaks (preemptO.final preemptActual preemptInitial) :=
  Or.inl preempt_actual_sh

theorem absent_degree :
    NoResponsibility preemptO suzyAlt preemptInitial preemptBreaks PreemptRetained
      .suzyThrow :=
  noResponsibility_of_absent preemptO suzyAlt preemptInitial preemptBreaks PreemptRetained
    suzy_absent_word

/-- The bottle breaks in both situations. Suzy's responsibility is 1 in the
first and 0 in the second. Her blame is `2/3` either way. -/
theorem blame_differs_from_responsibility :
    preemptBreaks (preemptO.final preemptActual preemptInitial) ∧
      preemptBreaks (preemptO.final suzyAlt preemptInitial) ∧
      PositiveDegree preemptO preemptActual preemptInitial preemptBreaks PreemptRetained
        .suzyThrow 1 ∧
      NoResponsibility preemptO suzyAlt preemptInitial preemptBreaks PreemptRetained
        .suzyThrow ∧
      blame ⟨uncertain, 0⟩ = ⟨2, 3⟩ ∧
      blame ⟨uncertain, 0⟩ = blame ⟨uncertain, 1⟩ ∧
      blame ⟨uncertain, 0⟩ ≠ responsibilityRatio 1 ∧
      blame ⟨uncertain, 1⟩ ≠ responsibilityRatio 0 := by
  refine ⟨actual_breaks, absent_breaks, preemption_suzy_degree, absent_degree,
    uncertain_blame, blame_same_either_world, ?_, ?_⟩
  · decide
  · decide

end Mettapedia.GSLT.Causality.Responsibility
