import Mettapedia.Machines.SetOutputPublication
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Option
import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.List.Nodup

/-!
# Layered deterministic graphs and complete proof languages

The grouped worker propagates finite languages through reachable graph edges.
An independent flat worker enumerates every row occurrence. Their comparison
retains the whole state and the ordered unary proof word. Counts are justified
by a unique initial row and functional transitions for each label, not by
formula-transition injectivity. Producer occurrences and stored support remain
separate observations.

States may represent whole alpha-equivalence classes with cross-subtree
correlations. This file does not construct that quotient, prove a source
compiler correct, establish native ownership, or preserve an effect order by
arbitrary language enumeration. Such correspondence obligations remain outside
this finite graph model. No Prime or solver-draft dependency is imported.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ProofLanguageRegions

open Finset

variable {State Label : Type}

/-- A label has at most one successor from any state. Distinct source rules
with the same observation label require a richer model or separate admission. -/
structure System (State Label : Type) where
  initial : State
  labels : List Label
  next : State → Label → Option State

abbrev Word (Label : Type) := List Label
abbrev Row (State Label : Type) := State × Word Label

/-- Most recent label first: `[b,a]` denotes `b(a(I))`. -/
def extend (sys : System State Label) (row : Row State Label) : List (Row State Label) :=
  sys.labels.filterMap fun label =>
    (sys.next row.1 label).map fun child => (child, label :: row.2)

/-- Flat occurrence execution; it does not call the grouped worker. -/
def flat (sys : System State Label) : Nat → List (Row State Label)
  | 0 => [(sys.initial, [])]
  | n + 1 => (flat sys n).flatMap (extend sys)

inductive Path (sys : System State Label) : Nat → State → Word Label → Prop where
  | seed : Path sys 0 sys.initial []
  | step {n : Nat} {parent child : State} {word : Word Label} {label : Label} :
      Path sys n parent word → label ∈ sys.labels → sys.next parent label = some child →
      Path sys (n + 1) child (label :: word)

/-- Independent interpretation of the unary proof word. -/
def evaluate (sys : System State Label) : Word Label → Option State
  | [] => some sys.initial
  | label :: rest => (evaluate sys rest).bind fun parent => sys.next parent label

theorem Path.evaluate {sys : System State Label} {n : Nat} {state : State} {word : Word Label}
    (path : Path sys n state word) : evaluate sys word = some state := by
  induction path with
  | seed => rfl
  | @step n parent child word label path admitted next ih =>
      change (ProofLanguageRegions.evaluate sys word).bind (fun source => sys.next source label) = some child
      rw [ih]
      exact next

theorem Path.length {sys : System State Label} {n : Nat} {state : State} {word : Word Label}
    (path : Path sys n state word) : word.length = n := by
  induction path with
  | seed => rfl
  | step _ _ _ ih => simp [ih]

/-- Different paths carrying the same complete word cannot end in different
states. The transition on formula states need not be injective. -/
theorem path_unambiguous {sys : System State Label} {n m : Nat} {first second : State}
    {word : Word Label} (left : Path sys n first word) (right : Path sys m second word) :
    first = second := Option.some.inj (left.evaluate.symm.trans right.evaluate)

@[simp] theorem mem_extend (sys : System State Label) (parent child : State)
    (word output : Word Label) :
    (child, output) ∈ extend sys (parent, word) ↔
      ∃ label ∈ sys.labels, sys.next parent label = some child ∧ output = label :: word := by
  simp only [extend, List.mem_filterMap]
  constructor
  · rintro ⟨label, member, found⟩
    obtain ⟨target, next, same⟩ := Option.map_eq_some_iff.mp found
    exact ⟨label, member, next.trans (congrArg some (Prod.mk.inj same).1),
      (Prod.mk.inj same).2.symm⟩
  · rintro ⟨label, member, next, rfl⟩
    exact ⟨label, member, by simp [next]⟩

@[simp] theorem mem_flat (sys : System State Label) (n : Nat) (state : State) (word : Word Label) :
    (state, word) ∈ flat sys n ↔ Path sys n state word := by
  induction n generalizing state word with
  | zero => constructor
            · simp only [flat, List.mem_singleton, Prod.mk.injEq, and_imp]
              intro same empty
              subst state
              subst word
              exact .seed
            · intro path
              cases path
              simp [flat]
  | succ n ih =>
      simp only [flat, List.mem_flatMap]
      constructor
      · rintro ⟨⟨parent, old⟩, before, after⟩
        obtain ⟨label, member, next, rfl⟩ := (mem_extend sys parent state old word).mp after
        exact .step ((ih parent old).mp before) member next
      · intro path
        cases path with
        | @step _ parent _ old label before member next =>
            exact ⟨(parent, old), (ih parent old).mpr before,
              (mem_extend sys parent state old (label :: old)).mpr ⟨label, member, next, rfl⟩⟩

variable [DecidableEq State] [DecidableEq Label]

/-- Reachable graph layers are computed from successors, independently of
flat proof enumeration. Depth is an explicit layer even if states recur. -/
def reachable (sys : System State Label) : Nat → Finset State
  | 0 => {sys.initial}
  | n + 1 => (reachable sys n).biUnion fun parent =>
      sys.labels.toFinset.biUnion fun label => (sys.next parent label).toFinset

theorem Path.reachable {sys : System State Label} {n : Nat} {state : State} {word : Word Label}
    (path : Path sys n state word) : state ∈ reachable sys n := by
  induction path with
  | seed => simp [ProofLanguageRegions.reachable]
  | @step n parent child word label path member next ih =>
      simp only [ProofLanguageRegions.reachable, Finset.mem_biUnion]
      exact ⟨parent, ih, label, by simpa using member, by simp [next]⟩

/-- Incoming edges are indexed by source and label; destination is checked
from the actual transition function. -/
def incoming (sys : System State Label) (n : Nat) (target : State) : Finset (State × Label) :=
  ((reachable sys n) ×ˢ sys.labels.toFinset).filter fun edge => sys.next edge.1 edge.2 = some target

@[simp] theorem mem_incoming (sys : System State Label) (n : Nat) (target parent : State) (label : Label) :
    (parent, label) ∈ incoming sys n target ↔
      parent ∈ reachable sys n ∧ label ∈ sys.labels ∧ sys.next parent label = some target := by
  simp [incoming, and_assoc]

/-- The grouped language DP has no reference to flat rows or their support. -/
def language (sys : System State Label) : Nat → State → Finset (Word Label)
  | 0, state => if state = sys.initial then {[]} else ∅
  | n + 1, state => (incoming sys n state).biUnion fun edge =>
      (language sys n edge.1).image (List.cons edge.2)

@[simp] theorem mem_language (sys : System State Label) (n : Nat) (state : State) (word : Word Label) :
    word ∈ language sys n state ↔ Path sys n state word := by
  induction n generalizing state word with
  | zero =>
      constructor
      · intro member
        by_cases same : state = sys.initial
        · subst state
          have empty : word = [] := by simpa [language] using member
          subst word
          exact .seed
        · simp [language, same] at member
      · intro path
        cases path
        simp [language]
  | succ n ih =>
      simp only [language, Finset.mem_biUnion, Finset.mem_image]
      constructor
      · rintro ⟨⟨parent, label⟩, edge, old, member, rfl⟩
        obtain ⟨_, admitted, next⟩ := (mem_incoming sys n state parent label).mp edge
        exact .step ((ih parent old).mp member) admitted next
      · intro path
        cases path with
        | @step _ parent _ old label before member next =>
            exact ⟨(parent, label),
              (mem_incoming sys n state parent label).mpr ⟨before.reachable, member, next⟩,
              old, (ih parent old).mpr before, rfl⟩

/-- Complete row/proof equality, not merely equal final counts. -/
theorem complete_row_language (sys : System State Label) (n : Nat) (state : State) (word : Word Label) :
    (state, word) ∈ flat sys n ↔ word ∈ language sys n state := by
  rw [mem_flat, mem_language]

theorem reachable_iff_language (sys : System State Label) (n : Nat) (state : State) :
    state ∈ reachable sys n ↔ (language sys n state).Nonempty := by
  induction n generalizing state with
  | zero => by_cases same : state = sys.initial <;> simp [reachable, language, same]
  | succ n ih =>
      simp only [ProofLanguageRegions.reachable, Finset.mem_biUnion]
      constructor
      · rintro ⟨parent, before, label, admitted, child⟩
        have next : sys.next parent label = some state := by simpa using child
        obtain ⟨word, wordIn⟩ := (ih parent).mp before
        exact ⟨label :: word, (mem_language sys (n + 1) state _).mpr
          (.step ((mem_language sys n parent word).mp wordIn) (by simpa using admitted) next)⟩
      · rintro ⟨word, member⟩
        have path := (mem_language sys (n + 1) state word).mp member
        cases path with
        | @step _ parent _ old label before admitted next =>
            exact ⟨parent, before.reachable, label, by simpa using admitted, by simp [next]⟩

/-- Incoming word families are disjoint even when different formula states
merge. Their label and tail word recover the unique parent. -/
theorem incoming_disjoint (sys : System State Label) (n : Nat) (state : State) :
    (↑(incoming sys n state) : Set (State × Label)).PairwiseDisjoint
      (fun edge => (language sys n edge.1).image (List.cons edge.2)) := by
  intro first _ second _ different
  apply Finset.disjoint_left.mpr
  intro word left right
  obtain ⟨old, left, same⟩ := Finset.mem_image.mp left
  obtain ⟨other, right, equal⟩ := Finset.mem_image.mp right
  have pair := List.cons.inj (same.trans equal.symm)
  have parent := path_unambiguous ((mem_language sys n first.1 old).mp left)
    (pair.2.symm ▸ (mem_language sys n second.1 other).mp right)
  exact different (Prod.ext parent pair.1)

/-- Scalar graph DP: one addition per incoming graph edge, not per proof. -/
def count (sys : System State Label) : Nat → State → Nat
  | 0, state => if state = sys.initial then 1 else 0
  | n + 1, state => ∑ edge ∈ incoming sys n state, count sys n edge.1

theorem count_eq_language_card (sys : System State Label) (n : Nat) (state : State) :
    count sys n state = (language sys n state).card := by
  induction n generalizing state with
  | zero => by_cases same : state = sys.initial <;> simp [count, language, same]
  | succ n ih =>
      rw [count, language, Finset.card_biUnion (incoming_disjoint sys n state)]
      apply Finset.sum_congr rfl
      intro edge _
      rw [Finset.card_image_of_injective _ (fun _ _ same => (List.cons.inj same).2)]
      exact ih edge.1

omit [DecidableEq State] [DecidableEq Label] in
theorem word_unique_on_flat (sys : System State Label) (n : Nat)
    (first second : Row State Label) (left : first ∈ flat sys n) (right : second ∈ flat sys n)
    (same : first.2 = second.2) : first = second := by
  rcases first with ⟨first, word⟩
  rcases second with ⟨second, other⟩
  simp only at same
  subst other
  exact Prod.ext (path_unambiguous ((mem_flat sys n first word).mp left)
    ((mem_flat sys n second word).mp right)) rfl

omit [DecidableEq State] [DecidableEq Label] in
theorem extend_nodup (sys : System State Label) (distinct : sys.labels.Nodup)
    (row : Row State Label) : (extend sys row).Nodup := by
  apply distinct.filterMap
  intro first second output left right
  obtain ⟨child, _, left⟩ := Option.map_eq_some_iff.mp (Option.mem_def.mp left)
  obtain ⟨other, _, right⟩ := Option.map_eq_some_iff.mp (Option.mem_def.mp right)
  exact (List.cons.inj (Prod.mk.inj (left.trans right.symm)).2).1

omit [DecidableEq State] [DecidableEq Label] in
/-- A unique seed and unique labels make flat producer occurrences inject
into stored rows. No injectivity of `next` in its source is assumed. -/
theorem flat_nodup (sys : System State Label) (distinct : sys.labels.Nodup) (n : Nat) :
    (flat sys n).Nodup := by
  induction n with
  | zero => simp [flat]
  | succ n ih =>
      rw [flat, List.nodup_flatMap]
      refine ⟨fun row _ => extend_nodup sys distinct row, ?_⟩
      apply ih.imp_of_mem
      intro first second firstIn secondIn different output left right
      rcases first with ⟨first, word⟩
      rcases second with ⟨second, other⟩
      rcases output with ⟨target, newWord⟩
      obtain ⟨label, _, _, firstWord⟩ := (mem_extend sys first target word newWord).mp left
      obtain ⟨secondLabel, _, _, secondWord⟩ := (mem_extend sys second target other newWord).mp right
      have same := (List.cons.inj (firstWord.symm.trans secondWord)).2
      exact different (word_unique_on_flat sys n _ _ firstIn secondIn same)

/-- The occurrence list at one graph node, before any set publication. -/
def flatWords (sys : System State Label) (n : Nat) (state : State) : List (Word Label) :=
  ((flat sys n).filter fun row => row.1 == state).map Prod.snd

omit [DecidableEq Label] in
@[simp] theorem mem_flatWords (sys : System State Label) (n : Nat) (state : State) (word : Word Label) :
    word ∈ flatWords sys n state ↔ (state, word) ∈ flat sys n := by
  simp only [flatWords, List.mem_map, List.mem_filter, beq_iff_eq]
  constructor
  · rintro ⟨⟨parent, old⟩, ⟨before, same⟩, equal⟩
    simp only at same equal
    subst parent
    subst old
    exact before
  · intro member
    exact ⟨(state, word), ⟨member, rfl⟩, rfl⟩

omit [DecidableEq Label] in
theorem flatWords_nodup (sys : System State Label) (distinct : sys.labels.Nodup) (n : Nat) (state : State) :
    (flatWords sys n state).Nodup := by
  apply List.Nodup.map_on _ ((flat_nodup sys distinct n).filter _)
  intro first firstIn second secondIn same
  exact word_unique_on_flat sys n first second (List.mem_filter.mp firstIn).1
    (List.mem_filter.mp secondIn).1 same

theorem language_eq_flatWords_support (sys : System State Label) (n : Nat) (state : State) :
    language sys n state = (flatWords sys n state).toFinset := by
  ext word
  simp only [List.mem_toFinset, mem_flatWords, complete_row_language]

/-- Full row equality also preserves occurrence counts under precisely the
unique-label condition. Set cardinality alone does not provide this premise. -/
theorem count_eq_flat_occurrences (sys : System State Label) (distinct : sys.labels.Nodup)
    (n : Nat) (state : State) : count sys n state = (flatWords sys n state).length := by
  rw [count_eq_language_card, language_eq_flatWords_support,
    List.toFinset_card_of_nodup (flatWords_nodup sys distinct n state)]

def rows (sys : System State Label) (n : Nat) : Finset (Row State Label) :=
  (reachable sys n).biUnion fun state => (language sys n state).image fun word => (state, word)

@[simp] theorem mem_rows (sys : System State Label) (n : Nat) (state : State) (word : Word Label) :
    (state, word) ∈ rows sys n ↔ (state, word) ∈ flat sys n := by
  simp only [rows, Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨parent, _, old, member, same⟩
    have equal := Prod.mk.inj same
    rcases equal with ⟨rfl, rfl⟩
    exact (complete_row_language sys n parent old).mpr member
  · intro member
    exact ⟨state, ((mem_flat sys n state word).mp member).reachable, word,
      (complete_row_language sys n state word).mp member, rfl⟩

theorem rows_eq_flat_support (sys : System State Label) (n : Nat) :
    rows sys n = (flat sys n).toFinset := by
  ext row
  rcases row with ⟨state, word⟩
  simp

theorem rows_card_eq_counts (sys : System State Label) (n : Nat) :
    (rows sys n).card = ∑ state ∈ reachable sys n, count sys n state := by
  rw [rows, Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro state _
    rw [Finset.card_image_of_injective _ (fun _ _ same => (Prod.mk.inj same).2)]
    exact (count_eq_language_card sys n state).symm
  · intro first _ second _ different
    apply Finset.disjoint_left.mpr
    intro row left right
    obtain ⟨_, _, same⟩ := Finset.mem_image.mp left
    obtain ⟨_, _, equal⟩ := Finset.mem_image.mp right
    exact different (Prod.mk.inj (same.trans equal.symm)).1

theorem layer_count_eq_flat_length (sys : System State Label) (distinct : sys.labels.Nodup) (n : Nat) :
    (∑ state ∈ reachable sys n, count sys n state) = (flat sys n).length := by
  rw [← rows_card_eq_counts, rows_eq_flat_support,
    List.toFinset_card_of_nodup (flat_nodup sys distinct n)]

/-- All reachable rows are retained, including open dead ends, rather than
only the accepted terminal proofs. -/
def flatThrough (sys : System State Label) (bound : Nat) : List (Row State Label) :=
  (List.range (bound + 1)).flatMap (flat sys)

theorem complete_prefix_rows (sys : System State Label) (bound : Nat) (state : State) (word : Word Label) :
    (state, word) ∈ flatThrough sys bound ↔
      ∃ layer ≤ bound, word ∈ language sys layer state := by
  simp only [flatThrough, List.mem_flatMap, List.mem_range, complete_row_language]
  constructor
  · rintro ⟨layer, less, member⟩
    exact ⟨layer, Nat.lt_succ_iff.mp less, member⟩
  · rintro ⟨layer, le, member⟩
    exact ⟨layer, Nat.lt_succ_iff.mpr le, member⟩

omit [DecidableEq State] [DecidableEq Label] in
theorem flatThrough_nodup (sys : System State Label) (distinct : sys.labels.Nodup) (bound : Nat) :
    (flatThrough sys bound).Nodup := by
  rw [flatThrough, List.nodup_flatMap]
  refine ⟨fun n _ => flat_nodup sys distinct n, ?_⟩
  apply (show (List.range (bound + 1)).Nodup from List.nodup_range).imp
  intro first second different row left right
  rcases row with ⟨state, word⟩
  have firstLength := ((mem_flat sys first state word).mp left).length
  have secondLength := ((mem_flat sys second state word).mp right).length
  exact different (firstLength.symm.trans secondLength)

def totalCount (sys : System State Label) (bound : Nat) : Nat :=
  ((List.range (bound + 1)).map fun n => ∑ state ∈ reachable sys n, count sys n state).sum

theorem total_count_eq_all_occurrences (sys : System State Label) (distinct : sys.labels.Nodup)
    (bound : Nat) : totalCount sys bound = (flatThrough sys bound).length := by
  simp only [totalCount, flatThrough, List.length_flatMap, layer_count_eq_flat_length sys distinct]

theorem total_count_eq_stored_support (sys : System State Label) (distinct : sys.labels.Nodup)
    (bound : Nat) : totalCount sys bound = (flatThrough sys bound).toFinset.card := by
  rw [total_count_eq_all_occurrences sys distinct,
    List.toFinset_card_of_nodup (flatThrough_nodup sys distinct bound)]

/-- Explicit scalar addition program for one adjacency list. `visits` counts
one update per edge, with no traversal of that edge's proof language. This
models graph arithmetic, not native table access or bigint bit complexity. -/
def addIncoming (weight : State → Nat) : List (State × Label) → Nat → Nat × Nat
  | [], accumulated => (accumulated, 0)
  | edge :: rest, accumulated =>
      let later := addIncoming weight rest (accumulated + weight edge.1)
      (later.1, later.2 + 1)

omit [DecidableEq State] [DecidableEq Label] in
theorem addIncoming_exact (weight : State → Nat) (edges : List (State × Label)) (start : Nat) :
    addIncoming weight edges start =
      (start + (edges.map fun edge => weight edge.1).sum, edges.length) := by
  induction edges generalizing start with
  | nil => simp [addIncoming]
  | cons edge rest ih => simp [addIncoming, ih, Nat.add_assoc]

/-- Any duplicate-free physical enumeration of the actual incoming edge set
computes the graph DP value and performs exactly one addition per edge. -/
theorem graph_count_adjacency (sys : System State Label) (n : Nat) (state : State)
    (edges : List (State × Label)) (distinct : edges.Nodup)
    (exactEdges : edges.toFinset = incoming sys n state) :
    addIncoming (count sys n) edges 0 = (count sys (n + 1) state, edges.length) := by
  rw [addIncoming_exact]
  simp only [Nat.zero_add, count]
  congr 1
  rw [← exactEdges, List.sum_toFinset _ distinct]

/-- Publication keeps every producer occurrence as an observation, while
stored membership is idempotent. It does not infer the count from support. -/
theorem publication_support (store produced : List (Row State Label)) (row : Row State Label) :
    row ∈ SetOutputPublication.publish store produced ↔ row ∈ store ∨ row ∈ produced :=
  SetOutputPublication.mem_publish store produced row

namespace WholeBody

/-- A binary encoding of a complete formula/goal stack. Shared variable
numbers remain meaningful across the entire tree. -/
inductive Term where
  | var (name : Nat)
  | atom (symbol : Nat)
  | pair (left right : Term)
  deriving DecidableEq, Repr

def rename (change : Nat → Nat) : Term → Term
  | .var name => .var (change name)
  | .atom symbol => .atom symbol
  | .pair first second => .pair (rename change first) (rename change second)

def position (name : Nat) : List Nat → Nat
  | [] => 0
  | first :: rest => if name = first then 0 else position name rest + 1

def canonicalize : Term → List Nat → Term × List Nat
  | .var name, seen =>
      (.var (position name seen), if name ∈ seen then seen else seen ++ [name])
  | .atom symbol, seen => (.atom symbol, seen)
  | .pair first second, seen =>
      let left := canonicalize first seen
      let right := canonicalize second left.2
      (.pair left.1 right.1, right.2)

def key (term : Term) : Term := (canonicalize term []).1

theorem position_rename (change : Nat → Nat) (injective : Function.Injective change)
    (name : Nat) (seen : List Nat) :
    position (change name) (seen.map change) = position name seen := by
  induction seen with
  | nil => rfl
  | cons first rest ih => simp [position, injective.eq_iff, ih]

/-- One renaming context is threaded through both subtrees; arbitrary
injective renaming of the original variable names preserves the complete key. -/
theorem canonicalize_rename (change : Nat → Nat) (injective : Function.Injective change) :
    ∀ (term : Term) (seen : List Nat),
      canonicalize (rename change term) (seen.map change) =
        ((canonicalize term seen).1, (canonicalize term seen).2.map change)
  | .var name, seen => by
      simp only [rename, canonicalize, position_rename change injective]
      by_cases present : name ∈ seen
      · simp [List.mem_map_of_injective injective, present]
      · simp [List.mem_map_of_injective injective, present]
  | .atom symbol, seen => rfl
  | .pair first second, seen => by
      simp only [rename, canonicalize]
      rw [canonicalize_rename change injective first seen]
      cases left : canonicalize first seen with
      | mk firstKey names =>
          rw [canonicalize_rename change injective second names]

theorem key_rename (change : Nat → Nat) (injective : Function.Injective change) (term : Term) :
    key (rename change term) = key term := by
  simpa only [key, List.map_nil] using congrArg (fun value : Term × List Nat => value.1)
    (canonicalize_rename change injective term [])

structure Core where
  remaining : Nat
  hypotheses : Nat
  body : Term
  deriving DecidableEq, Repr

/-- Coordinates remain part of the key; body-only grouping cannot erase the
remaining-depth or hypothesis guards. -/
def Core.key (core : Core) : Core := {core with body := WholeBody.key core.body}

end WholeBody

/-- The full grouped row multiset equals the independent flat occurrence
multiset under unique labels, not just after projecting counts or support. -/
theorem complete_row_bag (sys : System State Label) (distinct : sys.labels.Nodup) (n : Nat) :
    (rows sys n).val = (flat sys n : Multiset (Row State Label)) := by
  apply Multiset.Nodup.toFinset_inj (rows sys n).nodup
    (by simpa using flat_nodup sys distinct n)
  simpa using rows_eq_flat_support sys n

theorem complete_proof_bag (sys : System State Label) (distinct : sys.labels.Nodup)
    (n : Nat) (state : State) :
    (language sys n state).val = (flatWords sys n state : Multiset (Word Label)) := by
  apply Multiset.Nodup.toFinset_inj (language sys n state).nodup
    (by simpa using flatWords_nodup sys distinct n state)
  simpa using language_eq_flatWords_support sys n state

/-- Explicit closed unary proof syntax. Formula variables and unification
cells are not constructors of this datatype. -/
inductive Proof (Label : Type) where
  | seed
  | prefix (label : Label) (old : Proof Label)
  deriving DecidableEq, Repr

def wordProof : Word Label → Proof Label
  | [] => .seed
  | label :: rest => .prefix label (wordProof rest)

omit [DecidableEq State] [DecidableEq Label] in
theorem wordProof_injective : Function.Injective (wordProof (Label := Label)) := by
  intro first
  induction first with
  | nil => intro second same; cases second <;> simp_all [wordProof]
  | cons head tail ih =>
      intro second same
      cases second with
      | nil => simp [wordProof] at same
      | cons other rest =>
          have equal := Proof.prefix.inj same
          exact congrArg₂ List.cons equal.1 (ih equal.2)

/-- A materialized table uses local indices for each reachable layer. Each
layer has its own width; it does not clear the full global state universe. -/
structure IndexedLayers (State Label : Type) where
  width : Nat → Nat
  node : (n : Nat) → Fin (width n) → State
  adjacency : (n : Nat) → Vector (List (Fin (width n) × Label)) (width (n + 1))

def IndexedLayers.edgeRows (layers : IndexedLayers State Label) (n : Nat)
    (target : Fin (layers.width (n + 1))) : List (State × Label) :=
  ((layers.adjacency n)[target.val]).map fun edge => (layers.node n edge.1, edge.2)

/-- These are certificates about actual node/edge records, not an assumed
answer or count. Source-to-record certification is a separate obligation. -/
def IndexedLayers.Valid (sys : System State Label) (layers : IndexedLayers State Label) : Prop :=
  (∀ n, Function.Injective (layers.node n)) ∧
  (∀ n state, state ∈ reachable sys n ↔ ∃ index, layers.node n index = state) ∧
  ∀ n target, (layers.edgeRows n target).Nodup ∧
    (layers.edgeRows n target).toFinset = incoming sys n (layers.node (n + 1) target)

theorem IndexedLayers.layer_names (sys : System State Label) (layers : IndexedLayers State Label)
    (valid : layers.Valid sys) (n : Nat) :
    Finset.univ.image (layers.node n) = reachable sys n := by
  ext state
  simpa using (valid.2.1 n state).symm

theorem IndexedLayers.width_eq_reachable (sys : System State Label) (layers : IndexedLayers State Label)
    (valid : layers.Valid sys) (n : Nat) : layers.width n = (reachable sys n).card := by
  rw [← layers.layer_names sys valid n,
    Finset.card_image_of_injective _ (valid.1 n)]
  simp

theorem IndexedLayers.adjacency_length (sys : System State Label) (layers : IndexedLayers State Label)
    (valid : layers.Valid sys) (n : Nat) (target : Fin (layers.width (n + 1))) :
    (layers.adjacency n)[target.val].length =
      (incoming sys n (layers.node (n + 1) target)).card := by
  rw [← (valid.2.2 n target).2,
    List.toFinset_card_of_nodup (valid.2.2 n target).1]
  simp [IndexedLayers.edgeRows]

/-- Counts for all children are computed eagerly into an array-backed vector.
The prior table is captured once; the word languages are never enumerated. -/
def countTableStep {before after : Nat} (old : Vector Nat before)
    (adjacency : Vector (List (Fin before × Label)) after) : Vector Nat after × Nat :=
  let computed := Vector.ofFn fun target : Fin after =>
    addIncoming (fun parent : Fin before => old[parent.val]) adjacency[target.val] 0
  (computed.map Prod.fst, (computed.toList.map Prod.snd).sum)

omit [DecidableEq Label] in
theorem countTableStep_visits {before after : Nat} (old : Vector Nat before)
    (adjacency : Vector (List (Fin before × Label)) after) :
    (countTableStep old adjacency).2 = (adjacency.toList.map List.length).sum := by
  simp only [countTableStep, Vector.toList_ofFn, List.map_ofFn, addIncoming_exact]
  congr 1
  apply List.ext_getElem
  · simp
  · intro index left right
    simp

theorem countTableStep_correct (sys : System State Label) (layers : IndexedLayers State Label)
    (valid : layers.Valid sys) (n : Nat) (old : Vector Nat (layers.width n))
    (previous : ∀ index : Fin (layers.width n), old[index.val] = count sys n (layers.node n index))
    (target : Fin (layers.width (n + 1))) :
    (countTableStep old (layers.adjacency n)).1[target.val] =
      count sys (n + 1) (layers.node (n + 1) target) := by
  have scan := graph_count_adjacency sys n (layers.node (n + 1) target)
    (layers.edgeRows n target) (valid.2.2 n target).1 (valid.2.2 n target).2
  have value := congrArg Prod.fst scan
  simpa [countTableStep, addIncoming_exact, IndexedLayers.edgeRows, List.map_map,
    Function.comp_def, previous] using value

/-- A genuine materialized DP, separate from the recursive count specification.
The previous layer is a stored vector, reused by every outgoing adjacency. -/
def countTables (sys : System State Label) (layers : IndexedLayers State Label) :
    (n : Nat) → Vector Nat (layers.width n)
  | 0 => Vector.ofFn fun index => if layers.node 0 index = sys.initial then 1 else 0
  | n + 1 => (countTableStep (countTables sys layers n) (layers.adjacency n)).1

theorem countTables_correct (sys : System State Label) (layers : IndexedLayers State Label)
    (valid : layers.Valid sys) (n : Nat) (index : Fin (layers.width n)) :
    (countTables sys layers n)[index.val] = count sys n (layers.node n index) := by
  induction n with
  | zero => simp [countTables, count]
  | succ n ih => exact countTableStep_correct sys layers valid n _ ih index

theorem countTables_full_language (sys : System State Label) (layers : IndexedLayers State Label)
    (valid : layers.Valid sys) (n : Nat) (index : Fin (layers.width n)) :
    (countTables sys layers n)[index.val] = (language sys n (layers.node n index)).card := by
  rw [countTables_correct sys layers valid, count_eq_language_card]

/-- This ledger records the actual adjacency additions and table entries
materialized. Integer bit costs, record construction and native access bounds
are not inferred from it. Under exact reachable layer records, the entries are
vertices and adjacency occurrences are edges. -/
def tableWork (layers : IndexedLayers State Label) : Nat → Nat × Nat
  | 0 => (layers.width 0, 0)
  | n + 1 =>
      let old := tableWork layers n
      (old.1 + layers.width (n + 1),
        old.2 + ((layers.adjacency n).toList.map List.length).sum)

namespace Controls

/-- Two labels grow distinct proof words while sharing the same next state. -/
def diamond : System Nat Bool := ⟨0, [false, true], fun state _ => some (state + 1)⟩

abbrev diamondLayers : IndexedLayers Nat Bool where
  width _ := 1
  node n _ := n
  adjacency _ := Vector.replicate 1 [(0, false), (0, true)]

theorem diamond_reachable (n : Nat) : reachable diamond n = {n} := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [reachable, ih]
      simp [diamond]

theorem diamond_layers_valid : diamondLayers.Valid diamond := by
  refine ⟨?_, ?_, ?_⟩
  · intro n first second _
    exact Subsingleton.elim _ _
  · intro n state
    simp [diamond_reachable, diamondLayers, eq_comm]
  · intro n target
    have only : target = 0 := Subsingleton.elim _ _
    subst target
    constructor
    · simp [IndexedLayers.edgeRows, diamondLayers]
    · rw [incoming, diamond_reachable]
      ext edge
      rcases edge with ⟨parent, label⟩
      cases label <;> simp [IndexedLayers.edgeRows, diamondLayers, diamond]

theorem diamond_materialized (n : Nat) :
    (countTables diamond diamondLayers n)[0] = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (countTableStep (countTables diamond diamondLayers n)
        (Vector.replicate 1 [(0, false), (0, true)])).1[0] = 2 ^ (n + 1)
      simpa [countTableStep, addIncoming, Nat.pow_succ, Nat.mul_two] using
        congrArg (fun value => value + value) ih

theorem diamond_materialized_work (n : Nat) : tableWork diamondLayers n = (n + 1, 2 * n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [tableWork, ih]
      simp [diamondLayers, Nat.mul_add, Nat.add_assoc]

theorem diamond_full_bag :
    flat diamond 2 = [(2, [false, false]), (2, [true, false]),
      (2, [false, true]), (2, [true, true])] := by decide +kernel

theorem diamond_count : count diamond 4 4 = 16 ∧ (reachable diamond 4).card = 1 ∧
    (language diamond 4 4).card = 16 ∧ totalCount diamond 4 = 31 := by decide +kernel

/-- Distinct parent states may merge. The proof tail still separates them. -/
def merge : System Nat Nat := ⟨0, [1, 2, 3], fun state label =>
  if state = 0 ∧ label = 1 then some 1
  else if state = 0 ∧ label = 2 then some 2
  else if (state = 1 ∨ state = 2) ∧ label = 3 then some 3 else none⟩

theorem formula_transition_need_not_be_injective :
    merge.next 1 3 = merge.next 2 3 ∧ count merge 2 3 = 2 ∧
      language merge 2 3 = {[3, 1], [3, 2]} := by decide +kernel

/-- The branch at state2 has no final successor but remains in storage. -/
def deadEnd : System Nat Nat := ⟨0, [1, 2], fun state label =>
  if state = 0 ∧ label = 1 then some 1
  else if state = 0 ∧ label = 2 then some 2
  else if state = 1 ∧ label = 1 then some 3 else none⟩

theorem unsuccessful_prefix_retained :
    (2, [2]) ∈ flatThrough deadEnd 2 ∧ language deadEnd 2 2 = ∅ ∧
      totalCount deadEnd 2 = 4 := by decide +kernel

def repeated : System Nat Nat := ⟨0, [1, 1], fun state label =>
  if state = 0 ∧ label = 1 then some 2 else none⟩

/-- Raw duplicate rule occurrences cannot be counted from the fact set. -/
theorem duplicate_label_control :
    (flat repeated 1).length = 2 ∧ (rows repeated 1).card = 1 ∧
      count repeated 1 2 = 1 ∧
      SetOutputPublication.publish [] (flat repeated 1) = [(2, [1])] := by decide +kernel

/-- An occurrence-bearing source can have two distinct MGUs with the same
label. Such a source is not admitted by the functional graph model. -/
def occurrenceExpand (instances : List (Nat × Nat)) (old : Word Nat) : List (Row Nat Nat) :=
  instances.map fun entry => (entry.2, entry.1 :: old)

theorem ambiguous_mgu_control :
    occurrenceExpand [(1, 2), (1, 3)] [] = [(2, [1]), (3, [1])] ∧
      ((occurrenceExpand [(1, 2), (1, 3)] []).map Prod.snd).toFinset.card = 1 ∧
      (occurrenceExpand [(1, 2), (1, 3)] []).toFinset.card = 2 := by decide +kernel

theorem ambiguous_mgu_not_functional (sys : System Nat Nat) :
    ¬ (Path sys 1 2 [1] ∧ Path sys 1 3 [1]) := by
  rintro ⟨first, second⟩
  have impossible : (2 : Nat) = 3 := path_unambiguous first second
  omega

/-- A noninjective annotation (length, or a commutative label bag) erases
proof distinctions even with a perfectly deterministic graph. -/
theorem noncommutative_word_control :
    ([1, 2] : Word Nat) ≠ [2, 1] ∧ wordProof [1, 2] ≠ wordProof [2, 1] ∧
      ([1, 2] : Word Nat).length = [2, 1].length ∧
      ([1, 2] : Word Nat).toFinset = [2, 1].toFinset := by decide +kernel

theorem noninjective_annotation_control :
    (language diamond 2 2).card = 4 ∧
      ((language diamond 2 2).image List.length).card = 1 := by decide +kernel

open WholeBody in
/-- Alpha renaming preserves one shared context, but repeated variables and
cross-subtree correlations cannot be canonicalized independently. -/
theorem whole_body_correlation_control :
    key (.pair (.var 7) (.var 7)) = key (.pair (.var 12) (.var 12)) ∧
    key (.pair (.var 7) (.var 7)) ≠ key (.pair (.var 7) (.var 8)) ∧
    key (.pair (.pair (.var 7) (.var 8)) (.pair (.var 7) (.var 8))) ≠
      key (.pair (.pair (.var 7) (.var 8)) (.pair (.var 8) (.var 7))) ∧
    (Term.pair (key (.var 7)) (key (.var 7))) =
      (Term.pair (key (.var 7)) (key (.var 8))) := by decide +kernel

open WholeBody in
theorem coordinates_not_body_only :
    (Core.key ⟨2, 1, .var 7⟩) ≠ Core.key ⟨1, 1, .var 7⟩ ∧
      (Core.key ⟨2, 1, .var 7⟩) ≠ Core.key ⟨2, 2, .var 7⟩ := by decide +kernel

end Controls

#print axioms complete_row_language
#print axioms complete_row_bag
#print axioms incoming_disjoint
#print axioms count_eq_language_card
#print axioms total_count_eq_stored_support
#print axioms graph_count_adjacency
#print axioms WholeBody.canonicalize_rename
#print axioms countTables_correct
#print axioms countTableStep_visits
#print axioms Controls.diamond_materialized
#print axioms Controls.duplicate_label_control
#print axioms Controls.ambiguous_mgu_not_functional

end Mettapedia.Machines.ProofLanguageRegions
