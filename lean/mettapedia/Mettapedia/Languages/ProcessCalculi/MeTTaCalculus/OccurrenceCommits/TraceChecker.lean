import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.SplitPhaseRuns

/-!
# A verified checker for the traces a scheduler prints

A scheduler that explores a concurrent program prints what it did as ground data: occurrence
identities, the labels of fresh occurrences, the regions of its predicate queries (as location
and pattern pairs), and one event per step. This module reads such data back into the semantics of
`SplitPhaseRuns` and decides, with Boolean functions over lists, whether it is a valid run.

## Syntax

* `Tm`: symbols, numbered pattern variables, expressions. A label `Lbl` is a location and an atom.
* A region is written as a list of (location, pattern) pairs. Its predicate `regionPred` holds of
  a label when some pair matches it, by one-way matching with consistent bindings (`matchTm`).
  An atom of the form `(facet x rights)` is opaque: a pattern matches it only by equality.
* `TCommit`: taken, kept, made (with labels) and predicate queries (a region and the identities
  seen).
* `TEvent`: the events of `Event`, with modes named `serializable`, `claims`, `snapshot`,
  `unchecked`.

`labelOf tbl` reads labels from a table; `TCommit.decode`, `TEvent.decode` and `CState.decode`
give the commits, events and states of `SplitPhaseRuns`.

## Theorems

* `enabledB_iff`, `permitsB_iff`, `fireL_toFinset`: the Boolean tests and the list firing compute
  `Enabled`, `Permits` and `fire`.
* **`checkRun_isSome_iff`**: the checker accepts a list of events exactly when, decoded, it is a
  valid run (`RunValid`); `checkRun_final`: the state it computes decodes to the run's final state.
* **`checkRun_fires_iff`**: for a trace of atomic firings, the checker accepts exactly when the
  decoded commits form an `Executable` sequence with identities never reused.
* **`checkTree_iff`**: a trace tree (each record names its parent node) is accepted exactly when
  the path to every node is a valid run.
* **`serializableB_iff`**: the history test computes `SerializableHistory`; with
  `serializableHistory_iff_acyclic` it is the precedence-cycle test on one-snapshot waves.
* **`rowsCheck_iff`**: the row test of a firing with `every` holds exactly when its rows take
  pairwise disjoint occurrences, each inside what the firing takes. A commit whose rows share a
  take can be enabled as one commit (`Controls.merged_rows_enabled`), so the row condition is
  stated on its own and checked beside `checkTree`.
* **`linearCheck_iff`**: the take test holds exactly when no commit lists an occurrence among its
  takes twice. Decoding a printed commit to sets merges a repeated take, so a commit whose kernel
  and one of its rows take one occurrence is a valid run and passes the row test when the kernel's
  takes are not listed as a row (`Controls.kernel_row_double_take`); the take test refuses it.
* `consistent_made_labels`: a table that passes `consistentB` gives every fresh occurrence the
  label the trace printed for it.

## Controls

Small traces decided by evaluation (`decide`): a taker-then-reader snapshot run is valid and its
history serializable; the same run validated in `serializable` mode is refused; write skew under
`snapshot` is a valid run whose history is not serializable; a double take is refused; an absence
read fails at a store holding an occurrence of its region; a facet is opaque to patterns; rows of
an `every` that share a take are refused, rows that take apart pass.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.TraceChecker

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

/-! ## Terms, labels, regions -/

/-- Symbols (numbers are symbols), numbered pattern variables, expressions. -/
inductive Tm where
  | sym (s : String)
  | var (k : ℕ)
  | expr (args : List Tm)

instance : Inhabited Tm := ⟨.sym ""⟩

mutual
/-- Equality of terms, decided. -/
def Tm.decEq : (a b : Tm) → Decidable (a = b)
  | .sym x, .sym y =>
      if h : x = y then isTrue (h ▸ rfl) else isFalse fun e => h (by injection e)
  | .var j, .var k =>
      if h : j = k then isTrue (h ▸ rfl) else isFalse fun e => h (by injection e)
  | .expr as, .expr bs =>
      match Tm.decEqList as bs with
      | isTrue h => isTrue (h ▸ rfl)
      | isFalse h => isFalse fun e => h (by injection e)
  | .sym _, .var _ => isFalse fun e => Tm.noConfusion e
  | .sym _, .expr _ => isFalse fun e => Tm.noConfusion e
  | .var _, .sym _ => isFalse fun e => Tm.noConfusion e
  | .var _, .expr _ => isFalse fun e => Tm.noConfusion e
  | .expr _, .sym _ => isFalse fun e => Tm.noConfusion e
  | .expr _, .var _ => isFalse fun e => Tm.noConfusion e
termination_by structural a => a
/-- Equality of term lists, decided. -/
def Tm.decEqList : (as bs : List Tm) → Decidable (as = bs)
  | [], [] => isTrue rfl
  | a :: as, b :: bs =>
      match Tm.decEq a b, Tm.decEqList as bs with
      | isTrue h, isTrue h' => isTrue (h ▸ h' ▸ rfl)
      | isFalse h, _ => isFalse fun e => h (List.cons.inj e).1
      | _, isFalse h' => isFalse fun e => h' (List.cons.inj e).2
  | [], _ :: _ => isFalse fun e => by cases e
  | _ :: _, [] => isFalse fun e => by cases e
termination_by structural as => as
end

instance : DecidableEq Tm := Tm.decEq

/-- A label: where an occurrence lives and which atom it carries. -/
structure Lbl where
  loc : Tm
  atom : Tm
  deriving DecidableEq, Inhabited

/-- An atom `(facet x rights)` is opaque to patterns. -/
def Tm.isFacet : Tm → Bool
  | .expr [.sym "facet", _, _] => true
  | _ => false

mutual
/-- One-way matching of a pattern against a term, extending bindings. -/
def matchTm : Tm → Tm → List (ℕ × Tm) → Option (List (ℕ × Tm))
  | .var k, a, s =>
      match s.lookup k with
      | some v => if v = a then some s else none
      | none => some ((k, a) :: s)
  | .sym x, a, s => if Tm.sym x = a then some s else none
  | .expr ps, .expr as, s =>
      if (Tm.expr as).isFacet then (if Tm.expr ps = Tm.expr as then some s else none)
      else matchList ps as s
  | .expr _, _, _ => none
termination_by structural p => p
/-- Matching of argument lists of equal length. -/
def matchList : List Tm → List Tm → List (ℕ × Tm) → Option (List (ℕ × Tm))
  | [], [], s => some s
  | p :: ps, a :: as, s =>
      match matchTm p a s with
      | some s' => matchList ps as s'
      | none => none
  | _, _, _ => none
termination_by structural ps => ps
end

/-- The predicate of a region written as (location, pattern) pairs. -/
def regionPred (spec : List (Tm × Tm)) (l : Lbl) : Bool :=
  spec.any fun x => (matchList [x.1, x.2] [l.loc, l.atom] []).isSome

mutual
/-- A term without pattern variables. -/
def Tm.ground : Tm → Bool
  | .sym _ => true
  | .var _ => false
  | .expr args => Tm.groundList args
termination_by structural t => t
/-- Terms without pattern variables. -/
def Tm.groundList : List Tm → Bool
  | [] => true
  | a :: as => a.ground && Tm.groundList as
termination_by structural ts => ts
end

mutual
/-- **A ground pattern matches exactly itself**, leaving the bindings as they were. -/
theorem matchTm_ground : ∀ (p t : Tm) (s : List (ℕ × Tm)), p.ground = true →
    matchTm p t s = if p = t then some s else none
  | .sym x, t, s, _ => by simp [matchTm]
  | .var _, _, _, h => by simp [Tm.ground] at h
  | .expr ps, .expr as, s, h => by
      simp only [Tm.ground] at h
      simp only [matchTm, matchList_ground ps as s h, Tm.expr.injEq]
      split <;> rfl
  | .expr _, .sym _, _, _ => by simp [matchTm]
  | .expr _, .var _, _, _ => by simp [matchTm]
termination_by structural p => p
/-- Ground argument lists match exactly themselves. -/
theorem matchList_ground : ∀ (ps as : List Tm) (s : List (ℕ × Tm)), Tm.groundList ps = true →
    matchList ps as s = if ps = as then some s else none
  | [], [], s, _ => by simp [matchList]
  | [], _ :: _, s, _ => by simp [matchList]
  | _ :: _, [], s, _ => by simp [matchList]
  | p :: ps, a :: as, s, h => by
      simp only [Tm.groundList, Bool.and_eq_true] at h
      simp only [matchList, matchTm_ground p a s h.1, List.cons.injEq]
      by_cases same : p = a
      · simp only [same, if_true, matchList_ground ps as s h.2, true_and]
      · simp [same]
termination_by structural ps => ps
end

/-- **A region of one ground location**: a pattern at a ground location matches exactly the labels
at that location whose atom it matches. -/
theorem regionPred_ground {loc : Tm} (ground : loc.ground = true) (pat : Tm) (l : Lbl) :
    regionPred [(loc, pat)] l = (decide (l.loc = loc) && (matchTm pat l.atom []).isSome) := by
  simp only [regionPred, List.any_cons, List.any_nil, Bool.or_false, matchList,
    matchTm_ground loc l.loc [] ground]
  by_cases same : loc = l.loc
  · subst same
    simp only [if_true, decide_true, Bool.true_and]
    cases matchTm pat l.atom [] with
    | none => rfl
    | some s' => simp
  · have : ¬ l.loc = loc := fun h => same h.symm
    simp [same, this]

/-! ## Commits, events, states -/

/-- A predicate query as printed: the region and the identities seen there. -/
structure TQuery where
  spec : List (Tm × Tm)
  seen : List ℕ
  deriving DecidableEq

/-- A commit as printed. For a firing with `every`, `rows` lists what each row takes, and a
scheduler may list what the kernel takes as a first row; it is empty otherwise. The interaction
kernel lists the rows only, so its own takes appear in `taken` alone. -/
structure TCommit where
  taken : List ℕ
  kept : List ℕ
  made : List (ℕ × Lbl)
  queries : List TQuery
  rows : List (List ℕ)
  deriving DecidableEq

/-- The validation modes, by name. -/
inductive TMode where
  | serializable
  | claims
  | snapshot
  | unchecked
  deriving DecidableEq, Repr

/-- An event as printed. -/
inductive TEvent where
  | fire (c : TCommit)
  | begin (t : ℕ) (mode : TMode) (c : TCommit)
  | commit (t : ℕ) (dropped : List ℕ)
  | abort (t : ℕ)
  | batch (cs : List TCommit)
  | observe (c : TCommit)
  | branch (b : ℕ) (c : TCommit)
  | tau
  deriving DecidableEq

/-- A checker state. -/
structure CState where
  store : List ℕ
  born : List ℕ
  active : List (ℕ × TMode × TCommit)
  branches : List (ℕ × List ℕ)

/-- The labels of a trace, read from a table. -/
def labelOf (tbl : List (ℕ × Lbl)) (o : ℕ) : Lbl := (tbl.lookup o).getD default

def TMode.toChecks : TMode → Finset Check
  | .serializable => Mode.serializable
  | .claims => Mode.claims
  | .snapshot => Mode.snapshot
  | .unchecked => Mode.unchecked

def TQuery.decode (r : TQuery) : PredicateQuery ℕ Lbl := ⟨regionPred r.spec, r.seen.toFinset⟩

def TCommit.madeIds (c : TCommit) : List ℕ := c.made.map Prod.fst

def TCommit.decode (c : TCommit) : Commit ℕ Lbl :=
  ⟨c.taken.toFinset, c.kept.toFinset, c.madeIds.toFinset, c.queries.map TQuery.decode⟩

def TCommit.dropMade (c : TCommit) (dropped : List ℕ) : TCommit :=
  { c with made := c.made.filter fun x => !dropped.contains x.1 }

def TEvent.decode : TEvent → Event ℕ Lbl
  | .fire c => .fire c.decode
  | .begin t m c => .begin t m.toChecks c.decode
  | .commit t dropped => .commit t dropped.toFinset
  | .abort t => .abort t
  | .batch cs => .batch (cs.map TCommit.decode)
  | .observe c => .observe c.decode
  | .branch b c => .branch b c.decode
  | .tau => .tau

def decodeActive (x : ℕ × TMode × TCommit) : ℕ × Finset Check × Commit ℕ Lbl :=
  (x.1, x.2.1.toChecks, x.2.2.decode)

def decodeBranch (x : ℕ × List ℕ) : ℕ × Finset ℕ := (x.1, x.2.toFinset)

def CState.decode (s : CState) : RunState ℕ Lbl :=
  ⟨s.store.toFinset, s.born.toFinset, s.active.map decodeActive, s.branches.map decodeBranch⟩

def CState.branchStore (s : CState) (b : ℕ) : List ℕ := (s.branches.lookup b).getD s.store

/-! ## Boolean tests -/

def subsetB (xs ys : List ℕ) : Bool := xs.all fun x => ys.contains x

def disjointB (xs ys : List ℕ) : Bool := xs.all fun x => !ys.contains x

def sameSetB (xs ys : List ℕ) : Bool := subsetB xs ys && subsetB ys xs

def holdsB (L : ℕ → Lbl) (store : List ℕ) (r : TQuery) : Bool :=
  sameSetB (store.filter fun o => regionPred r.spec (L o)) r.seen

def enabledB (L : ℕ → Lbl) (store : List ℕ) (c : TCommit) : Bool :=
  subsetB c.taken store && subsetB c.kept store && disjointB c.taken c.kept &&
    disjointB c.madeIds store && c.queries.all (holdsB L store)

def fireL (store : List ℕ) (c : TCommit) : List ℕ :=
  store.filter (fun o => !c.taken.contains o) ++ c.madeIds

def TMode.checksTakes : TMode → Bool
  | .unchecked => false
  | _ => true

def TMode.checksKeeps : TMode → Bool
  | .serializable => true
  | .claims => true
  | _ => false

def TMode.checksRegions : TMode → Bool
  | .serializable => true
  | _ => false

def permitsB (L : ℕ → Lbl) (m : TMode) (store : List ℕ) (c : TCommit) : Bool :=
  (!m.checksTakes || subsetB c.taken store) && (!m.checksKeeps || subsetB c.kept store) &&
    (!m.checksRegions || c.queries.all (holdsB L store)) && disjointB c.madeIds store

def pairwiseB {α : Type*} (f : α → α → Bool) : List α → Bool
  | [] => true
  | x :: xs => xs.all (f x) && pairwiseB f xs

def noClashB (e d : TCommit) : Bool := disjointB e.taken d.taken && disjointB e.madeIds d.madeIds

def executableB (L : ℕ → Lbl) : List ℕ → List TCommit → Bool
  | _, [] => true
  | store, c :: cs => enabledB L store c && executableB L (fireL store c) cs

def fireListL : List ℕ → List TCommit → List ℕ
  | store, [] => store
  | store, c :: cs => fireListL (fireL store c) cs

def eraseKeyL {β : Type} (t : ℕ) (l : List (ℕ × β)) : List (ℕ × β) := l.filter fun x => x.1 != t

/-- When an event may happen, decided. -/
def validB (L : ℕ → Lbl) (s : CState) : TEvent → Bool
  | .fire c => enabledB L s.store c && disjointB c.madeIds s.born
  | .begin t _ c => (s.active.lookup t).isNone && enabledB L s.store c && disjointB c.madeIds s.born
  | .commit t dropped =>
      match s.active.lookup t with
      | some (m, c) =>
          subsetB dropped c.madeIds &&
            dropped.all (fun o => (fireL s.store (c.dropMade dropped)).any fun o' => decide (L o' = L o)) &&
            permitsB L m s.store (c.dropMade dropped)
      | none => false
  | .abort t => (s.active.lookup t).isSome
  | .batch cs => cs.all (enabledB L s.store) && disjointB (cs.flatMap TCommit.madeIds) s.born &&
      pairwiseB noClashB cs && executableB L s.store cs
  | .observe c => enabledB L s.store c && c.taken.isEmpty && c.made.isEmpty
  | .branch b c => enabledB L (s.branchStore b) c && disjointB c.madeIds s.born
  | .tau => true

/-- What an event does, computed. -/
def nextC (s : CState) : TEvent → CState
  | .fire c => { s with store := fireL s.store c, born := s.born ++ c.madeIds }
  | .begin t m c => { s with active := (t, m, c) :: s.active, born := s.born ++ c.madeIds }
  | .commit t dropped =>
      match s.active.lookup t with
      | some (_, c) => { s with store := fireL s.store (c.dropMade dropped),
                                active := eraseKeyL t s.active }
      | none => s
  | .abort t => { s with active := eraseKeyL t s.active }
  | .batch cs => { s with store := fireListL s.store cs, born := s.born ++ cs.flatMap TCommit.madeIds }
  | .observe _ => s
  | .branch b c => { s with branches := (b, fireL (s.branchStore b) c) :: eraseKeyL b s.branches,
                            born := s.born ++ c.madeIds }
  | .tau => s

/-- The checker: the state a list of events reaches, or nothing if some event may not happen. -/
def checkRun (L : ℕ → Lbl) : CState → List TEvent → Option CState
  | s, [] => some s
  | s, e :: es => if validB L s e then checkRun L (nextC s e) es else none

/-! ## The tests compute the semantics -/

section Correctness

variable (L : ℕ → Lbl)

theorem subsetB_iff (xs ys : List ℕ) : subsetB xs ys = true ↔ xs.toFinset ⊆ ys.toFinset := by
  simp [subsetB, Finset.subset_iff]

theorem disjointB_iff (xs ys : List ℕ) : disjointB xs ys = true ↔ Disjoint xs.toFinset ys.toFinset := by
  simp [disjointB, Finset.disjoint_left]

theorem sameSetB_iff (xs ys : List ℕ) : sameSetB xs ys = true ↔ xs.toFinset = ys.toFinset := by
  rw [sameSetB, Bool.and_eq_true, subsetB_iff, subsetB_iff]
  exact ⟨fun ⟨a, b⟩ => Finset.Subset.antisymm a b, fun h => ⟨h ▸ le_rfl, h ▸ le_rfl⟩⟩

theorem holdsB_iff (store : List ℕ) (r : TQuery) :
    holdsB L store r = true ↔ r.decode.Holds L store.toFinset := by
  rw [holdsB, sameSetB_iff, PredicateQuery.Holds, regionOf, TQuery.decode, List.toFinset_filter]

theorem readsB_iff (store : List ℕ) (c : TCommit) :
    c.queries.all (holdsB L store) = true ↔ ∀ read ∈ c.decode.queries, read.Holds L store.toFinset := by
  simp only [List.all_eq_true, TCommit.decode, List.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, holdsB_iff]

theorem enabledB_iff (store : List ℕ) (c : TCommit) :
    enabledB L store c = true ↔ Enabled L store.toFinset c.decode := by
  simp only [enabledB, Bool.and_eq_true, subsetB_iff, disjointB_iff, readsB_iff]
  constructor
  · rintro ⟨⟨⟨⟨taken, kept⟩, apart⟩, fresh⟩, reads⟩
    exact ⟨taken, kept, apart, fresh, reads⟩
  · intro enabled
    exact ⟨⟨⟨⟨enabled.taken_subset, enabled.kept_subset⟩, enabled.apart⟩, enabled.fresh⟩,
      enabled.queries_hold⟩

theorem fireL_toFinset (store : List ℕ) (c : TCommit) :
    (fireL store c).toFinset = fire store.toFinset c.decode := by
  ext o
  simp [fireL, fire, TCommit.decode, TCommit.madeIds, Finset.mem_sdiff]

theorem fireListL_toFinset :
    ∀ (store : List ℕ) (cs : List TCommit),
      (fireListL store cs).toFinset = fireList store.toFinset (cs.map TCommit.decode) := by
  intro store cs
  induction cs generalizing store with
  | nil => rfl
  | cons c cs ih => simp only [fireListL, List.map_cons, fireList_cons, ih, fireL_toFinset]

theorem mem_toChecks_takes (m : TMode) : Check.takes ∈ m.toChecks ↔ m.checksTakes = true := by
  cases m <;> decide

theorem mem_toChecks_keeps (m : TMode) : Check.keeps ∈ m.toChecks ↔ m.checksKeeps = true := by
  cases m <;> decide

theorem mem_toChecks_regions (m : TMode) : Check.regions ∈ m.toChecks ↔ m.checksRegions = true := by
  cases m <;> decide

theorem permitsB_iff (m : TMode) (store : List ℕ) (c : TCommit) :
    permitsB L m store c = true ↔ Permits L m.toChecks store.toFinset c.decode := by
  simp only [permitsB, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', subsetB_iff,
    disjointB_iff, readsB_iff, Permits, mem_toChecks_takes, mem_toChecks_keeps,
    mem_toChecks_regions]
  constructor
  · rintro ⟨⟨⟨takes, keeps⟩, regions⟩, fresh⟩
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fresh⟩
    · rcases takes with no | yes
      · rw [h] at no; cases no
      · exact yes
    · rcases keeps with no | yes
      · rw [h] at no; cases no
      · exact yes
    · rcases regions with no | yes
      · rw [h] at no; cases no
      · exact yes
  · rintro ⟨takes, keeps, regions, fresh⟩
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, fresh⟩
    · cases h : m.checksTakes
      · exact Or.inl rfl
      · exact Or.inr (takes h)
    · cases h : m.checksKeeps
      · exact Or.inl rfl
      · exact Or.inr (keeps h)
    · cases h : m.checksRegions
      · exact Or.inl rfl
      · exact Or.inr (regions h)

theorem pairwiseB_iff {α : Type*} (f : α → α → Bool) :
    ∀ (l : List α), pairwiseB f l = true ↔ l.Pairwise fun x y => f x y = true := by
  intro l
  induction l with
  | nil => simp [pairwiseB]
  | cons x xs ih => simp [pairwiseB, ih, List.pairwise_cons, List.all_eq_true]

theorem noClashB_iff (e d : TCommit) : noClashB e d = true ↔ ¬ Clash e.decode d.decode := by
  simp only [noClashB, Bool.and_eq_true, disjointB_iff, Clash, not_or, not_not]
  rfl

theorem pairwise_noClash_iff (cs : List TCommit) :
    pairwiseB noClashB cs = true ↔
      (cs.map TCommit.decode).Pairwise fun e d => ¬ Clash e d := by
  rw [pairwiseB_iff, List.pairwise_map]
  simp only [noClashB_iff]

theorem executableB_iff :
    ∀ (store : List ℕ) (cs : List TCommit),
      executableB L store cs = true ↔ Executable L store.toFinset (cs.map TCommit.decode) := by
  intro store cs
  induction cs generalizing store with
  | nil => simp [executableB, Executable.nil]
  | cons c cs ih =>
      rw [executableB, Bool.and_eq_true, List.map_cons, executable_cons_iff, enabledB_iff, ih,
        fireL_toFinset]

theorem madeOf_decode : ∀ (cs : List TCommit),
    madeOf (cs.map TCommit.decode) = (cs.flatMap TCommit.madeIds).toFinset := by
  intro cs
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      simp only [List.map_cons, madeOf, ih, List.flatMap_cons, List.toFinset_append, TCommit.decode]

theorem lookup_map_decodeActive :
    ∀ (l : List (ℕ × TMode × TCommit)) (t : ℕ),
      (l.map decodeActive).lookup t = (l.lookup t).map fun x => (x.1.toChecks, x.2.decode) := by
  intro l t
  induction l with
  | nil => rfl
  | cons x xs ih =>
      obtain ⟨k, m, c⟩ := x
      by_cases same : t = k
      · subst same; simp [List.lookup, decodeActive]
      · have : (t == k) = false := by simpa using same
        simp [List.lookup, decodeActive, this, ih]

theorem lookup_map_decodeBranch :
    ∀ (l : List (ℕ × List ℕ)) (b : ℕ),
      (l.map decodeBranch).lookup b = (l.lookup b).map List.toFinset := by
  intro l b
  induction l with
  | nil => rfl
  | cons x xs ih =>
      obtain ⟨k, v⟩ := x
      by_cases same : b = k
      · subst same; simp [List.lookup, decodeBranch]
      · have : (b == k) = false := by simpa using same
        simp [List.lookup, decodeBranch, this, ih]

theorem branchStore_decode (s : CState) (b : ℕ) :
    (s.branchStore b).toFinset = s.decode.branchStore b := by
  simp only [CState.branchStore, RunState.branchStore, CState.decode, lookup_map_decodeBranch]
  cases s.branches.lookup b <;> rfl

theorem eraseKey_map {β γ : Type} (f : ℕ × β → ℕ × γ) (keep : ∀ x, (f x).1 = x.1) (t : ℕ)
    (l : List (ℕ × β)) : eraseKey t (l.map f) = (eraseKeyL t l).map f := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      simp only [eraseKey, eraseKeyL, List.map_cons, List.filter_cons, keep] at ih ⊢
      split <;> simp [ih]

theorem dropMade_decode (c : TCommit) (dropped : List ℕ) :
    (c.dropMade dropped).decode = c.decode.dropMade dropped.toFinset := by
  simp only [TCommit.decode, TCommit.dropMade, Commit.dropMade, TCommit.madeIds, Commit.mk.injEq,
    true_and, and_true]
  ext o
  simp [List.mem_filter]

theorem justifiedB_iff (store : List ℕ) (c : TCommit) (dropped : List ℕ) :
    (dropped.all fun o => (fireL store (c.dropMade dropped)).any fun o' => decide (L o' = L o)) = true ↔
      ∀ o ∈ dropped.toFinset, ∃ o' ∈ fire store.toFinset (c.decode.dropMade dropped.toFinset),
        L o' = L o := by
  simp only [List.all_eq_true, List.any_eq_true, decide_eq_true_eq, List.mem_toFinset]
  constructor
  · intro h o member
    obtain ⟨o', inFire, same⟩ := h o member
    refine ⟨o', ?_, same⟩
    rw [← dropMade_decode, ← fireL_toFinset]
    exact List.mem_toFinset.mpr inFire
  · intro h o member
    obtain ⟨o', inFire, same⟩ := h o member
    refine ⟨o', ?_, same⟩
    rw [← dropMade_decode, ← fireL_toFinset] at inFire
    exact List.mem_toFinset.mp inFire

/-- **The decided test is the semantic condition.** -/
theorem validB_iff (s : CState) (e : TEvent) : validB L s e = true ↔ Valid L s.decode e.decode := by
  cases e with
  | fire c =>
      simp only [validB, TEvent.decode, Valid, Bool.and_eq_true, enabledB_iff, disjointB_iff,
        CState.decode, TCommit.decode]
  | begin t m c =>
      simp only [validB, TEvent.decode, Valid, Bool.and_eq_true, enabledB_iff, disjointB_iff,
        Option.isNone_iff_eq_none, CState.decode, lookup_map_decodeActive, Option.map_eq_none_iff,
        TCommit.decode, and_assoc]
  | commit t dropped =>
      simp only [validB, TEvent.decode, Valid]
      rw [show s.decode.active.lookup t = (s.active.lookup t).map fun x => (x.1.toChecks, x.2.decode)
        from lookup_map_decodeActive _ _]
      cases found : s.active.lookup t with
      | none => simp
      | some x =>
          obtain ⟨m, c⟩ := x
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, Bool.and_eq_true,
            subsetB_iff, justifiedB_iff, permitsB_iff, dropMade_decode]
          constructor
          · rintro ⟨⟨sub, just⟩, permits⟩
            refine ⟨m.toChecks, c.decode, ⟨rfl, rfl⟩, ?_, just, permits⟩
            simpa [TCommit.decode] using sub
          · rintro ⟨mode, d, ⟨rfl, rfl⟩, sub, just, permits⟩
            exact ⟨⟨by simpa [TCommit.decode] using sub, just⟩, permits⟩
  | abort t =>
      simp only [validB, TEvent.decode, Valid, CState.decode, lookup_map_decodeActive]
      cases s.active.lookup t <;> simp
  | batch cs =>
      simp only [validB, TEvent.decode, Valid, Bool.and_eq_true, List.all_eq_true, enabledB_iff,
        disjointB_iff, pairwise_noClash_iff, executableB_iff, madeOf_decode, List.mem_map,
        forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, CState.decode, and_assoc]
  | observe c =>
      simp only [validB, TEvent.decode, Valid, Bool.and_eq_true, enabledB_iff, List.isEmpty_iff,
        TCommit.decode, CState.decode, TCommit.madeIds]
      constructor
      · rintro ⟨⟨enabled, taken⟩, made⟩
        exact ⟨enabled, by simp [taken], by simp [made]⟩
      · rintro ⟨enabled, taken, made⟩
        refine ⟨⟨enabled, ?_⟩, ?_⟩
        · simpa using taken
        · simpa using made
  | branch b c =>
      simp only [validB, TEvent.decode, Valid, Bool.and_eq_true, enabledB_iff, disjointB_iff,
        branchStore_decode]
      rfl
  | tau => simp [validB, TEvent.decode, Valid]

/-- **The computed step is the semantic step.** -/
theorem nextC_decode (s : CState) (e : TEvent) : (nextC s e).decode = next s.decode e.decode := by
  cases e with
  | fire c =>
      simp only [nextC, TEvent.decode, next, CState.decode, fireL_toFinset, List.toFinset_append,
        TCommit.decode]
  | begin t m c =>
      simp only [nextC, TEvent.decode, next, CState.decode, List.map_cons, List.toFinset_append,
        decodeActive, TCommit.decode]
  | commit t dropped =>
      simp only [nextC, TEvent.decode, next]
      rw [show s.decode.active.lookup t = (s.active.lookup t).map fun x => (x.1.toChecks, x.2.decode)
        from lookup_map_decodeActive _ _]
      cases s.active.lookup t with
      | none => rfl
      | some x =>
          obtain ⟨m, c⟩ := x
          simp only [Option.map_some, CState.decode, fireL_toFinset, dropMade_decode,
            eraseKey_map decodeActive (fun _ => rfl)]
  | abort t =>
      simp only [nextC, TEvent.decode, next, CState.decode, eraseKey_map decodeActive (fun _ => rfl)]
  | batch cs =>
      simp only [nextC, TEvent.decode, next, CState.decode, fireListL_toFinset, List.toFinset_append,
        madeOf_decode]
  | observe c => rfl
  | branch b c =>
      simp only [nextC, TEvent.decode, next, CState.decode, List.map_cons, List.toFinset_append,
        eraseKey_map decodeBranch (fun _ => rfl), decodeBranch, fireL_toFinset, branchStore_decode,
        TCommit.decode]
  | tau => rfl

/-- **The checker accepts exactly the valid runs.** -/
theorem checkRun_isSome_iff :
    ∀ (s : CState) (es : List TEvent),
      (checkRun L s es).isSome = true ↔ RunValid L s.decode (es.map TEvent.decode) := by
  intro s es
  induction es generalizing s with
  | nil => simp [checkRun, RunValid]
  | cons e es ih =>
      simp only [checkRun, List.map_cons, RunValid]
      rw [← validB_iff, ← nextC_decode, ← ih]
      cases validB L s e <;> simp

/-- **The checker computes the final state of the run.** -/
theorem checkRun_final :
    ∀ (s : CState) (es : List TEvent) (s' : CState), checkRun L s es = some s' →
      s'.decode = final s.decode (es.map TEvent.decode) := by
  intro s es
  induction es generalizing s with
  | nil => intro s' h; simp only [checkRun, Option.some.injEq] at h; subst h; rfl
  | cons e es ih =>
      intro s' h
      simp only [checkRun] at h
      split at h
      · rw [List.map_cons, final_cons, ← nextC_decode]; exact ih _ s' h
      · cases h

/-- **For atomic firings, the checker accepts exactly the executable sequences** whose fresh
identities are never reused. -/
theorem checkRun_fires_iff (s : CState) (cs : List TCommit) :
    (checkRun L s (cs.map TEvent.fire)).isSome = true ↔
      Executable L s.store.toFinset (cs.map TCommit.decode) ∧
        ∀ (pre : List (Commit ℕ Lbl)) (c : Commit ℕ Lbl) (post : List (Commit ℕ Lbl)),
          cs.map TCommit.decode = pre ++ c :: post → Disjoint c.made (s.born.toFinset ∪ madeOf pre) := by
  rw [checkRun_isSome_iff, List.map_map]
  have : (TEvent.decode ∘ TEvent.fire) = (Event.fire ∘ TCommit.decode) := rfl
  rw [this, ← List.map_map]
  exact runValid_fires_iff s.decode (cs.map TCommit.decode)

end Correctness

/-! ## Trace trees -/

/-- A record of a trace tree: node `k + 1` is reached from `parent` by `event`, where `k` is the
record's position; node `0` is the root. -/
structure TEdge where
  parent : ℕ
  event : TEvent

/-- The events on the path from the root to a node, when every parent comes earlier. -/
def pathTo (edges : List TEdge) : ℕ → Option (List TEvent)
  | 0 => some []
  | k + 1 =>
      match edges[k]? with
      | some e =>
          if _h : e.parent ≤ k then (pathTo edges e.parent).map (· ++ [e.event]) else none
      | none => none
termination_by k => k
decreasing_by omega

/-- One record processed: the state of its node from the state of its parent. -/
def treeStep (L : ℕ → Lbl) (states : Array (Option CState)) (e : TEdge) : Array (Option CState) :=
  states.push ((states[e.parent]?).join.bind fun s => checkRun L s [e.event])

/-- The states of the first `n` records' nodes, root first. -/
def treeStates (L : ℕ → Lbl) (root : CState) (edges : List TEdge) (n : ℕ) : Array (Option CState) :=
  (edges.take n).foldl (treeStep L) #[some root]

/-- **The tree checker**: every node's state was computed. -/
def checkTree (L : ℕ → Lbl) (root : CState) (edges : List TEdge) : Bool :=
  let states := treeStates L root edges edges.length
  (List.range (edges.length + 1)).all fun k => (states[k]?).join.isSome

theorem checkRun_append (L : ℕ → Lbl) :
    ∀ (s : CState) (xs ys : List TEvent),
      checkRun L s (xs ++ ys) = (checkRun L s xs).bind fun s' => checkRun L s' ys := by
  intro s xs ys
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.cons_append, checkRun]
      split
      · exact ih _
      · rfl

theorem treeStates_spec (L : ℕ → Lbl) (root : CState) (edges : List TEdge) :
    ∀ n, n ≤ edges.length →
      (treeStates L root edges n).size = n + 1 ∧
        ∀ k ≤ n, (treeStates L root edges n)[k]? = some ((pathTo edges k).bind (checkRun L root)) := by
  intro n
  induction n with
  | zero =>
      intro _
      refine ⟨rfl, fun k hk => ?_⟩
      have : k = 0 := by omega
      subst this
      simp [treeStates, pathTo, checkRun]
  | succ n ih =>
      intro hn
      obtain ⟨size, states⟩ := ih (by omega)
      have hlt : n < edges.length := by omega
      have unfold : treeStates L root edges (n + 1) =
          treeStep L (treeStates L root edges n) edges[n] := by
        simp only [treeStates]
        rw [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some, List.foldl_append]
        rfl
      rw [unfold]
      refine ⟨by simp [treeStep, size], fun k hk => ?_⟩
      simp only [treeStep]
      rw [Array.getElem?_push]
      split
      · next same =>
        have kEq : k = n + 1 := by omega
        subst kEq
        rw [pathTo]
        simp only [List.getElem?_eq_getElem hlt]
        by_cases hp : edges[n].parent ≤ n
        · rw [states _ hp, dif_pos hp]
          simp only [Option.join_some]
          cases pathTo edges edges[n].parent with
          | none => rfl
          | some es => simp [checkRun_append]
        · rw [dif_neg hp]
          have big : (treeStates L root edges n).size ≤ edges[n].parent := by omega
          rw [Array.getElem?_eq_none big]
          rfl
      · next differ =>
        exact states k (by omega)

/-- **The tree checker accepts exactly when the path to every node is a valid run.** -/
theorem checkTree_iff (L : ℕ → Lbl) (root : CState) (edges : List TEdge) :
    checkTree L root edges = true ↔
      ∀ k ≤ edges.length, ∃ es, pathTo edges k = some es ∧
        RunValid L root.decode (es.map TEvent.decode) := by
  obtain ⟨_, states⟩ := treeStates_spec L root edges edges.length le_rfl
  simp only [checkTree, List.all_eq_true, List.mem_range]
  constructor
  · intro h k hk
    have := h k (by omega)
    rw [states k hk, Option.join_some] at this
    cases found : pathTo edges k with
    | none => rw [found] at this; simp at this
    | some es =>
        rw [found] at this
        exact ⟨es, rfl, (checkRun_isSome_iff L root es).mp this⟩
  · intro h k hk
    obtain ⟨es, found, valid⟩ := h k (by omega)
    rw [states k (by omega), Option.join_some, found]
    exact (checkRun_isSome_iff L root es).mpr valid

/-! ## Histories -/

/-- The commits an event publishes, computed. -/
def committedByC (s : CState) : TEvent → List TCommit
  | .fire c => [c]
  | .commit t dropped =>
      match s.active.lookup t with
      | some (_, c) => [c.dropMade dropped]
      | none => []
  | .batch cs => cs
  | .observe c => [c]
  | _ => []

/-- The history of a run, computed. -/
def historyC : CState → List TEvent → List TCommit
  | _, [] => []
  | s, e :: es => committedByC s e ++ historyC (nextC s e) es

theorem committedByC_decode (s : CState) (e : TEvent) :
    (committedByC s e).map TCommit.decode = committedBy s.decode e.decode := by
  cases e with
  | commit t dropped =>
      simp only [committedByC, TEvent.decode, committedBy]
      rw [show s.decode.active.lookup t = (s.active.lookup t).map fun x => (x.1.toChecks, x.2.decode)
        from lookup_map_decodeActive _ _]
      cases s.active.lookup t with
      | none => rfl
      | some x => simp [dropMade_decode]
  | fire c => rfl
  | begin t m c => rfl
  | abort t => rfl
  | batch cs => rfl
  | observe c => rfl
  | branch b c => rfl
  | tau => rfl

theorem historyC_decode : ∀ (s : CState) (es : List TEvent),
    (historyC s es).map TCommit.decode = history s.decode (es.map TEvent.decode) := by
  intro s es
  induction es generalizing s with
  | nil => rfl
  | cons e es ih =>
      simp only [historyC, List.map_append, committedByC_decode, ih, List.map_cons, history,
        nextC_decode]

/-- The history test with a bound on the depth of the search. -/
def serializableAux (L : ℕ → Lbl) : ℕ → List ℕ → List TCommit → Bool
  | 0, _, cs => cs.isEmpty
  | n + 1, store, cs =>
      cs.isEmpty || cs.any fun c => enabledB L store c && serializableAux L n (fireL store c) (cs.erase c)

/-- The history test: some order of the commits is executable from the store. -/
def serializableB (L : ℕ → Lbl) (store : List ℕ) (cs : List TCommit) : Bool :=
  serializableAux L cs.length store cs

theorem serializableAux_iff (L : ℕ → Lbl) :
    ∀ (n : ℕ) (store : List ℕ) (cs : List TCommit), cs.length = n →
      (serializableAux L n store cs = true ↔
        SerializableHistory L store.toFinset (cs.map TCommit.decode)) := by
  intro n
  induction n with
  | zero =>
      intro store cs len
      have : cs = [] := List.eq_nil_of_length_eq_zero len
      subst this
      simp only [serializableAux, List.isEmpty_nil, List.map_nil, true_iff]
      exact ⟨[], List.Perm.refl _, Executable.nil _⟩
  | succ n ih =>
      intro store cs len
      cases cs with
      | nil => simp at len
      | cons x xs =>
          simp only [serializableAux, List.isEmpty_cons, Bool.false_or, List.any_eq_true,
            Bool.and_eq_true]
          constructor
          · rintro ⟨c, member, enabled, rest⟩
            have lenErase : ((x :: xs).erase c).length = n := by
              rw [List.length_erase_of_mem member]; simp at len ⊢; omega
            obtain ⟨l, perm, executable⟩ := (ih _ _ lenErase).mp rest
            refine ⟨c.decode :: l, ?_, executable_cons_iff.mpr ⟨(enabledB_iff L _ _).mp enabled,
              by rw [← fireL_toFinset]; exact executable⟩⟩
            have := (List.perm_cons_erase member).map TCommit.decode
            exact (perm.cons _).trans this.symm
          · rintro ⟨l, perm, executable⟩
            cases l with
            | nil => exact absurd perm.length_eq (by simp)
            | cons d l =>
                obtain ⟨enabledD, rest⟩ := executable_cons_iff.mp executable
                obtain ⟨c, member, rfl⟩ := List.mem_map.mp (perm.subset List.mem_cons_self)
                refine ⟨c, member, (enabledB_iff L _ _).mpr enabledD, ?_⟩
                have lenErase : ((x :: xs).erase c).length = n := by
                  rw [List.length_erase_of_mem member]; simp at len ⊢; omega
                refine (ih _ _ lenErase).mpr ⟨l, ?_, by rw [fireL_toFinset]; exact rest⟩
                have := (List.perm_cons_erase member).map TCommit.decode
                exact (List.perm_cons _).mp (perm.trans this)

/-- **The history test computes `SerializableHistory`.** -/
theorem serializableB_iff (L : ℕ → Lbl) (store : List ℕ) (cs : List TCommit) :
    serializableB L store cs = true ↔ SerializableHistory L store.toFinset (cs.map TCommit.decode) :=
  serializableAux_iff L cs.length store cs rfl

/-! ## Rows of `every` -/

/-- The rows of a firing with `every` take no occurrence in common, and each takes only what the
firing takes. A firing whose rows share a take would consume one occurrence for two rows. -/
def TCommit.rowsOk (c : TCommit) : Bool :=
  pairwiseB disjointB c.rows && c.rows.all fun r => subsetB r c.taken

/-- The commits an event carries. -/
def TEvent.commits : TEvent → List TCommit
  | .fire c => [c]
  | .begin _ _ c => [c]
  | .batch cs => cs
  | .observe c => [c]
  | .branch _ c => [c]
  | _ => []

/-- Every commit of every event has rows without a common take. -/
def rowsCheck (es : List TEvent) : Bool := es.all fun e => e.commits.all TCommit.rowsOk

theorem rowsOk_iff (c : TCommit) :
    c.rowsOk = true ↔
      c.rows.Pairwise (fun r r' => Disjoint r.toFinset r'.toFinset) ∧
        ∀ r ∈ c.rows, r.toFinset ⊆ c.taken.toFinset := by
  simp only [TCommit.rowsOk, Bool.and_eq_true, pairwiseB_iff, disjointB_iff, List.all_eq_true,
    subsetB_iff]

theorem rowsCheck_iff (es : List TEvent) :
    rowsCheck es = true ↔
      ∀ e ∈ es, ∀ c ∈ e.commits,
        c.rows.Pairwise (fun r r' => Disjoint r.toFinset r'.toFinset) ∧
          ∀ r ∈ c.rows, r.toFinset ⊆ c.taken.toFinset := by
  simp only [rowsCheck, List.all_eq_true, rowsOk_iff]

/-! ## Takes as printed -/

/-- A commit lists each occurrence among its takes at most once. -/
def TCommit.takesOnce (c : TCommit) : Bool := decide c.taken.Nodup

/-- **The take test**: no commit of any event lists one take twice. -/
def linearCheck (es : List TEvent) : Bool := es.all fun e => e.commits.all TCommit.takesOnce

theorem linearCheck_iff (es : List TEvent) :
    linearCheck es = true ↔ ∀ e ∈ es, ∀ c ∈ e.commits, c.taken.Nodup := by
  simp only [linearCheck, TCommit.takesOnce, List.all_eq_true, decide_eq_true_eq]

/-! ## Labels of fresh occurrences -/

/-- Every fresh occurrence of every event carries the label the table gives it. -/
def consistentB (tbl : List (ℕ × Lbl)) (es : List TEvent) : Bool :=
  let ok := fun (c : TCommit) => c.made.all fun x => decide (tbl.lookup x.1 = some x.2)
  es.all fun e =>
    match e with
    | .fire c => ok c
    | .begin _ _ c => ok c
    | .batch cs => cs.all ok
    | .observe c => ok c
    | .branch _ c => ok c
    | _ => true

theorem consistent_made_labels (tbl : List (ℕ × Lbl)) (c : TCommit)
    (ok : (c.made.all fun x => decide (tbl.lookup x.1 = some x.2)) = true) :
    ∀ x ∈ c.made, labelOf tbl x.1 = x.2 := by
  intro x member
  have := List.all_eq_true.mp ok x member
  simp only [decide_eq_true_eq] at this
  simp [labelOf, this]

/-! ## Controls -/

namespace Controls

def tok : Lbl := ⟨.sym "&s", .sym "x"⟩
def out (name : String) : Lbl := ⟨.sym "&s", .sym name⟩

/-- Occurrence `0` carries the token; `5`, `6`, `7` carry outputs. -/
def table : List (ℕ × Lbl) := [(0, tok), (5, out "y"), (6, out "taken"), (7, out "z")]

def L : ℕ → Lbl := labelOf table

/-- Keep the token and make `y`. -/
def reader : TCommit := ⟨[], [0], [(5, out "y")], [], []⟩

/-- Take the token and make `taken`. -/
def taker : TCommit := ⟨[0], [], [(6, out "taken")], [], []⟩

/-- Take the token again and make `z`. -/
def taker₂ : TCommit := ⟨[0], [], [(7, out "z")], [], []⟩

def start : CState := ⟨[0], [0], [], []⟩

def takerFirst (m : TMode) : List TEvent :=
  [.begin 1 m reader, .begin 2 m taker, .commit 2 [], .commit 1 []]

/-- **Positive control**: the taker-then-reader run is valid under `snapshot`, and its history
is serializable (reader first). -/
theorem taker_first_valid : (checkRun L start (takerFirst .snapshot)).isSome = true := by decide

theorem taker_first_serializable :
    serializableB L start.store (historyC start (takerFirst .snapshot)) = true := by decide

/-- **Negative control**: validated in `serializable` mode, the reader is refused. -/
theorem serializable_refuses_stale : (checkRun L start (takerFirst .serializable)).isSome = false := by
  decide

/-- **Negative control**: two atomic takes of one occurrence. -/
theorem double_take_refused :
    (checkRun L start [.fire taker, .fire taker₂]).isSome = false := by decide

/-- Write skew: each keeps the other's token and takes its own. -/
def skewTable : List (ℕ × Lbl) :=
  [(30, ⟨.sym "&h", .sym "a"⟩), (31, ⟨.sym "&h", .sym "b"⟩), (32, out "offA"), (33, out "offB")]

def skewA : TCommit := ⟨[30], [31], [(32, out "offA")], [], []⟩
def skewB : TCommit := ⟨[31], [30], [(33, out "offB")], [], []⟩
def skewStart : CState := ⟨[30, 31], [30, 31], [], []⟩
def skewRun : List TEvent := [.begin 1 .snapshot skewA, .begin 2 .snapshot skewB, .commit 1 [], .commit 2 []]

theorem write_skew_valid : (checkRun (labelOf skewTable) skewStart skewRun).isSome = true := by decide

/-- **Negative control**: the write-skew history is not serializable. -/
theorem write_skew_not_serializable :
    serializableB (labelOf skewTable) skewStart.store (historyC skewStart skewRun) = false := by
  decide

/-- An absence read over the region of outputs at `&s`, written as a pattern with a variable. -/
def absenceQuery : TQuery := ⟨[(.sym "&s", .var 0)], []⟩

/-- A region with a variable matches every atom of its location. -/
theorem region_matches_location : regionPred absenceQuery.spec tok = true := by decide

/-- **Negative control**: the absence read fails at a store holding an occurrence of its region. -/
theorem absence_fails_when_present : holdsB L [0] absenceQuery = false := by decide

/-- A facet is opaque: a pattern with the facet's shape does not see through it. -/
theorem facet_opaque :
    (matchTm (.expr [.sym "facet", .var 0, .var 1])
      (.expr [.sym "facet", .sym "c", .expr [.sym "send"]]) []).isSome = false := by decide

/-- An `every` whose two rows take occurrence `0`: enabled as one commit, refused by the row
check. -/
def mergedRows : TCommit := ⟨[0], [], [(6, out "taken"), (7, out "z")], [], [[], [0], [0]]⟩

/-- **Negative control**: the merged commit is enabled, so only the row check refuses it. -/
theorem merged_rows_enabled : enabledB L start.store mergedRows = true := by decide

theorem merged_rows_refused : rowsCheck [.fire mergedRows] = false := by decide

/-- **Positive control**: rows that take apart pass. -/
theorem apart_rows_pass :
    rowsCheck [.fire ⟨[0, 5], [], [], [], [[], [0], [5]]⟩] = true := by decide

/-- A firing whose kernel takes occurrence `0` and whose one row takes `0` too, printed as the
interaction kernel prints it: the takes of the row, then the kernel's, and the row alone. -/
def kernelRowDoubleTake : TCommit := ⟨[0, 0], [], [(6, out "taken")], [], [[0]]⟩

/-- **Negative control for the row test**: the run is valid and passes the row test, because the
decoded commit takes `0` once and the kernel's takes are not a listed row; only the take test
refuses it. -/
theorem kernel_row_double_take :
    (checkRun L start [.fire kernelRowDoubleTake]).isSome = true ∧
      rowsCheck [.fire kernelRowDoubleTake] = true ∧
      linearCheck [.fire kernelRowDoubleTake] = false := by
  decide

/-- **Ground terms**: a region name is ground; a pattern with a variable is not, and it matches
more than itself. -/
theorem ground_controls :
    (Tm.expr [.sym "nm", .sym "1"]).ground = true ∧ (Tm.expr [.sym "msg", .var 0]).ground = false ∧
      (matchTm (.expr [.sym "msg", .var 0]) (.expr [.sym "msg", .sym "7"]) []).isSome = true := by
  decide

/-- **Positive control for the take test**: a commit that takes `0` and `5` once each passes. -/
theorem takes_once_pass : linearCheck [.fire ⟨[0, 5], [], [], [], [[0], [5]]⟩] = true := by decide

end Controls

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.TraceChecker
