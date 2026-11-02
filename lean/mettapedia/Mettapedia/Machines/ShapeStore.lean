import Mathlib.Tactic

/-!
# Shape stores: a fact as a skeleton plus the values in its holes

A shape store keeps a ground fact as two parts: a *skeleton* (the term with
some subterms replaced by holes) and the list of the subterms it cut out, in
order.  Facts with the same skeleton form one table whose rows are those
lists, so a fact needs no record of its own: its identity is the pair.  Which
subterms become holes is a *cut*, chosen per position and allowed to look at
the subterm itself (a frequent constant can stay in the skeleton while other
values at the same position become holes).

This file proves, for every cut:
* `fill_dec`, `reassemble_dec`, `dec_injective`, `length_dec`: reassembly
  (filling the holes in order) inverts the decomposition, so the
  decomposition is injective, and a skeleton has as many holes as its row
  has values;
* `Cut`: any decomposition that reassembly inverts; `rootCut` (one hole
  holding the whole fact: a store of records) and `noCut` (no hole: every fact
  its own skeleton, as in a trie of facts) are its two limits;
* `denote_store`, `insert_store`, `remove_store`, `Reach.canonical`: a store
  under bag semantics denotes the bag of its facts, and every store reachable
  by inserts and removes is the decomposition of its bag;
* `transfer_store`, `transfer_insert`, `transfer_remove`, `transfer_match`:
  moving a store from one cut to another (a re-cut) commutes with insert,
  remove and match;
* `matchSk_of_fill`, `matchRow_dec`, `matchStore_store`: matching a pattern
  against a skeleton and its values agrees with matching the reassembled
  fact, for every row;
* `matchSk_staged`: that matching splits into a program compiled once per
  skeleton and run on each row's values.

Negative examples: forgetting the values is not injective
(`skeleton_only_not_injective`), and a store that no sequence of inserts and
removes reaches can break the re-cut law for removal
(`transfer_remove_needs_reachable`).
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ShapeStore

/-- Ground terms: atoms and binary nodes.  An S-expression `(f a b)` is a
chain of nodes. -/
inductive Tm (α : Type) where
  | atom (a : α)
  | node (l r : Tm α)
  deriving DecidableEq

/-- Skeletons: terms with holes. -/
inductive Skel (α : Type) where
  | hole
  | atom (a : α)
  | node (l r : Skel α)
  deriving DecidableEq

/-- A row: a skeleton and the values of its holes, left to right. -/
abbrev Row (α : Type) := Skel α × List (Tm α)

variable {α : Type}

/-- The holes of a skeleton. -/
def Skel.holes : Skel α → ℕ
  | .hole => 1
  | .atom _ => 0
  | .node l r => l.holes + r.holes

/-- The skeleton of a term with no hole. -/
def Tm.toSkel : Tm α → Skel α
  | .atom a => .atom a
  | .node l r => .node l.toSkel r.toSkel

/-- Positions: the left (`false`) and right (`true`) turns from the root. -/
abbrev Pos := List Bool

/-- A cut policy: at each position, given the subterm there, whether that
subterm becomes a hole. -/
abbrev Policy (α : Type) := Pos → Tm α → Bool

/-- The decomposition of a term under a policy. -/
def dec : Policy α → Tm α → Row α
  | c, .atom a => if c [] (.atom a) then (.hole, [.atom a]) else (.atom a, [])
  | c, .node l r =>
    if c [] (.node l r) then (.hole, [.node l r]) else
      ((dec (fun q => c (false :: q)) l).1.node (dec (fun q => c (true :: q)) r).1,
        (dec (fun q => c (false :: q)) l).2 ++ (dec (fun q => c (true :: q)) r).2)

/-- Filling a skeleton's holes from a list of values, left to right; returns
the term and the unused values. -/
def fill : Skel α → List (Tm α) → Option (Tm α × List (Tm α))
  | .hole, t :: ts => some (t, ts)
  | .hole, [] => none
  | .atom a, ts => some (.atom a, ts)
  | .node l r, ts =>
    (fill l ts).bind fun r₁ => (fill r r₁.2).map fun r₂ => (.node r₁.1 r₂.1, r₂.2)

/-- Reassembly: the term a row denotes, when its values fill the skeleton
exactly. -/
def reassemble (row : Row α) : Option (Tm α) :=
  match fill row.1 row.2 with
  | some (t, []) => some t
  | _ => none

theorem fill_dec (c : Policy α) (t : Tm α) (rest : List (Tm α)) :
    fill (dec c t).1 ((dec c t).2 ++ rest) = some (t, rest) := by
  induction t generalizing c rest with
  | atom a => by_cases h : c [] (.atom a) <;> simp [dec, h, fill]
  | node l r ihl ihr =>
    by_cases h : c [] (.node l r)
    · simp [dec, h, fill]
    · simp [dec, h, fill, List.append_assoc, ihl, ihr]

theorem reassemble_dec (c : Policy α) (t : Tm α) : reassemble (dec c t) = some t := by
  have h := fill_dec c t []
  simp only [List.append_nil] at h
  simp [reassemble, h]

theorem dec_injective (c : Policy α) : Function.Injective (dec c) := by
  intro t₁ t₂ h
  have h₁ := reassemble_dec c t₁
  rw [h, reassemble_dec] at h₁
  exact (Option.some.inj h₁).symm

theorem fill_length {s : Skel α} {ts : List (Tm α)} {t : Tm α} {rest : List (Tm α)}
    (h : fill s ts = some (t, rest)) : ts.length = s.holes + rest.length := by
  induction s generalizing ts t rest with
  | hole =>
    cases ts with
    | nil => simp [fill] at h
    | cons u us => simp only [fill, Option.some.injEq, Prod.mk.injEq] at h; simp [Skel.holes, h.2]; omega
  | atom a => simp only [fill, Option.some.injEq, Prod.mk.injEq] at h; simp [Skel.holes, h.2]
  | node l r ihl ihr =>
    simp only [fill] at h
    rcases hl : fill l ts with _ | ⟨tl, mid⟩
    · simp [hl] at h
    rcases hr : fill r mid with _ | ⟨tr, rest'⟩
    · simp [hl, hr] at h
    simp only [hl, hr, Option.bind_some, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    rw [ihl hl, ihr hr, h.2]; simp [Skel.holes]; omega

/-- A skeleton has as many holes as its row has values. -/
theorem length_dec (c : Policy α) (t : Tm α) : (dec c t).2.length = (dec c t).1.holes := by
  have := fill_length (fill_dec c t [])
  simpa using this

/-! ## Cuts and their two limits -/

/-- A cut: any decomposition that reassembly inverts. -/
structure Cut (α : Type) where
  d : Tm α → Row α
  sec : ∀ t, reassemble (d t) = some t

/-- The cut of a policy. -/
def Cut.ofPolicy (c : Policy α) : Cut α := ⟨dec c, reassemble_dec c⟩

theorem Cut.injective (k : Cut α) : Function.Injective k.d := by
  intro t₁ t₂ h
  have h₁ := k.sec t₁
  rw [h, k.sec] at h₁
  exact (Option.some.inj h₁).symm

/-- Every fact one hole: one table whose single column holds whole facts. -/
def rootCut : Cut α := Cut.ofPolicy fun _ _ => true

/-- No hole: every fact is its own skeleton with an empty row. -/
def noCut : Cut α := Cut.ofPolicy fun _ _ => false

theorem rootCut_d (t : Tm α) : (rootCut : Cut α).d t = (.hole, [t]) := by
  cases t <;> simp [rootCut, Cut.ofPolicy, dec]

theorem noCut_d (t : Tm α) : (noCut : Cut α).d t = (t.toSkel, []) := by
  induction t with
  | atom a => simp [noCut, Cut.ofPolicy, dec, Tm.toSkel]
  | node l r ihl ihr =>
    simp only [noCut, Cut.ofPolicy] at ihl ihr ⊢
    simp [dec, Tm.toSkel, ihl, ihr]

/-! ## Stores under bag semantics -/

variable [DecidableEq α]

/-- The store of a bag of facts under a cut: one row per fact. -/
def store (k : Cut α) (B : Multiset (Tm α)) : Multiset (Row α) := B.map k.d

/-- The facts a store denotes. -/
def denote (S : Multiset (Row α)) : Multiset (Tm α) := S.filterMap reassemble

def insert (k : Cut α) (t : Tm α) (S : Multiset (Row α)) : Multiset (Row α) := k.d t ::ₘ S

def remove (k : Cut α) (t : Tm α) (S : Multiset (Row α)) : Multiset (Row α) := S.erase (k.d t)

omit [DecidableEq α] in
theorem denote_store (k : Cut α) (B : Multiset (Tm α)) : denote (store k B) = B := by
  have h : (reassemble ∘ k.d) = some := funext k.sec
  simp [denote, store, Multiset.filterMap_map, h, Multiset.filterMap_some]

omit [DecidableEq α] in
theorem insert_store (k : Cut α) (t : Tm α) (B : Multiset (Tm α)) :
    insert k t (store k B) = store k (t ::ₘ B) := by
  simp [insert, store]

theorem remove_store (k : Cut α) (t : Tm α) (B : Multiset (Tm α)) :
    remove k t (store k B) = store k (B.erase t) := by
  simp [remove, store, Multiset.map_erase _ k.injective]

omit [DecidableEq α] in
theorem denote_insert (k : Cut α) (t : Tm α) (S : Multiset (Row α)) :
    denote (insert k t S) = t ::ₘ denote S := by
  simp [denote, insert, Multiset.filterMap_cons_some _ _ _ (k.sec t)]

/-- The stores that inserts and removes reach from the empty store. -/
inductive Reach (k : Cut α) : Multiset (Row α) → Prop
  | empty : Reach k 0
  | insert {S : Multiset (Row α)} (t : Tm α) : Reach k S → Reach k (insert k t S)
  | remove {S : Multiset (Row α)} (t : Tm α) : Reach k S → Reach k (remove k t S)

/-- A reachable store is the decomposition of the bag it denotes. -/
theorem Reach.canonical {k : Cut α} {S : Multiset (Row α)} (h : Reach k S) :
    S = store k (denote S) := by
  induction h with
  | empty => simp [store, denote]
  | insert t _ ih =>
    rw [ih, insert_store, denote_store]
  | remove t _ ih =>
    rw [ih, remove_store, denote_store]

/-! ## Re-cuts -/

/-- Moving a store to another cut: reassemble each row, decompose again. -/
def transfer (k₂ : Cut α) (S : Multiset (Row α)) : Multiset (Row α) := store k₂ (denote S)

omit [DecidableEq α] in
theorem transfer_store (k₁ k₂ : Cut α) (B : Multiset (Tm α)) :
    transfer k₂ (store k₁ B) = store k₂ B := by
  simp [transfer, denote_store]

/-- A re-cut maps the stores one cut reaches to stores the other reaches. -/
theorem transfer_reach {k₁ : Cut α} (k₂ : Cut α) {S : Multiset (Row α)} (h : Reach k₁ S) :
    Reach k₂ (transfer k₂ S) := by
  induction h with
  | empty => simpa [transfer, denote, store] using (Reach.empty : Reach k₂ 0)
  | @insert S t _ ih =>
    have e : transfer k₂ (insert k₁ t S) = insert k₂ t (transfer k₂ S) := by
      simp [transfer, denote_insert, insert_store]
    rw [e]; exact Reach.insert t ih
  | @remove S t hS ih =>
    have e : transfer k₂ (remove k₁ t S) = remove k₂ t (transfer k₂ S) := by
      rw [hS.canonical, remove_store, transfer_store, transfer_store, remove_store]
    rw [e]; exact Reach.remove t ih

omit [DecidableEq α] in
/-- A re-cut commutes with insert, for every store. -/
theorem transfer_insert (k₁ k₂ : Cut α) (t : Tm α) (S : Multiset (Row α)) :
    transfer k₂ (insert k₁ t S) = insert k₂ t (transfer k₂ S) := by
  simp [transfer, denote_insert, insert_store]

/-- A re-cut commutes with remove, for every reachable store. -/
theorem transfer_remove {k₁ : Cut α} (k₂ : Cut α) (t : Tm α) {S : Multiset (Row α)}
    (h : Reach k₁ S) : transfer k₂ (remove k₁ t S) = remove k₂ t (transfer k₂ S) := by
  rw [h.canonical, remove_store, transfer_store, transfer_store, remove_store]

/-! ## Matching at two levels -/

/-- Patterns: variables, atoms and nodes. -/
inductive Pat (α : Type) where
  | var (x : ℕ)
  | atom (a : α)
  | node (l r : Pat α)
  deriving DecidableEq

/-- Substitutions, as association lists. -/
abbrev Subst (α : Type) := List (ℕ × Tm α)

/-- Binding a variable: a first occurrence binds, a repeated one checks. -/
def bindVar (x : ℕ) (t : Tm α) (σ : Subst α) : Option (Subst α) :=
  match σ.lookup x with
  | some u => if u = t then some σ else none
  | none => some ((x, t) :: σ)

/-- Matching a pattern against a term, extending a substitution. -/
def matchTm : Pat α → Tm α → Subst α → Option (Subst α)
  | .var x, t, σ => bindVar x t σ
  | .atom a, .atom b, σ => if a = b then some σ else none
  | .node p q, .node l r, σ => (matchTm p l σ).bind (matchTm q r)
  | .atom _, .node _ _, _ => none
  | .node _ _, .atom _, _ => none

/-- Matching a pattern against a skeleton and its values: the skeleton is
walked with the pattern; a hole passes its value to `matchTm`; a variable
facing a part of the skeleton binds the subterm that part rebuilds. -/
def matchSk : Pat α → Skel α → List (Tm α) → Subst α → Option (Subst α × List (Tm α))
  | p, .hole, ts, σ =>
    match ts with
    | t :: ts' => (matchTm p t σ).map fun σ' => (σ', ts')
    | [] => none
  | .var x, .atom b, ts, σ => (bindVar x (.atom b) σ).map fun σ' => (σ', ts)
  | .var x, .node l r, ts, σ =>
    (fill (.node l r) ts).bind fun u => (bindVar x u.1 σ).map fun σ' => (σ', u.2)
  | .atom a, .atom b, ts, σ => if a = b then some (σ, ts) else none
  | .node p q, .node l r, ts, σ => (matchSk p l ts σ).bind fun r₁ => matchSk q r r₁.2 r₁.1
  | .atom _, .node _ _, _, _ => none
  | .node _ _, .atom _, _, _ => none

/-- Two-level matching agrees with matching the reassembled term, for every
skeleton and values that fill it. -/
theorem matchSk_of_fill (p : Pat α) (s : Skel α) (ts : List (Tm α)) (σ : Subst α)
    {t : Tm α} {rest : List (Tm α)} (h : fill s ts = some (t, rest)) :
    matchSk p s ts σ = (matchTm p t σ).map fun σ' => (σ', rest) := by
  induction s generalizing p ts σ t rest with
  | hole =>
    cases ts with
    | nil => simp [fill] at h
    | cons u us =>
      simp only [fill, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      cases p <;> simp [matchSk]
  | atom b =>
    simp only [fill, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    cases p with
    | var x => simp [matchSk, matchTm]
    | atom a => by_cases hab : a = b <;> simp [matchSk, matchTm, hab]
    | node p q => simp [matchSk, matchTm]
  | node l r ihl ihr =>
    have hfill := h
    simp only [fill] at h
    rcases hl : fill l ts with _ | ⟨tl, mid⟩
    · simp [hl] at h
    rcases hr : fill r mid with _ | ⟨tr, rest'⟩
    · simp [hl, hr] at h
    simp only [hl, hr, Option.bind_some, Option.map_some, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    cases p with
    | var x => simp [matchSk, matchTm, hfill]
    | atom a => simp [matchSk, matchTm]
    | node p q =>
      simp only [matchSk, matchTm]
      rw [ihl p ts σ hl]
      rcases hm : matchTm p tl σ with _ | σ₁
      · simp
      · simp [ihr q mid σ₁ hr]

/-- Matching a row: the substitution, when the row's values are used exactly. -/
def matchRow (p : Pat α) (row : Row α) : Option (Subst α) :=
  match matchSk p row.1 row.2 [] with
  | some (σ, []) => some σ
  | _ => none

theorem matchRow_of_reassemble (p : Pat α) {row : Row α} {t : Tm α}
    (h : reassemble row = some t) : matchRow p row = matchTm p t [] := by
  have hf : fill row.1 row.2 = some (t, []) := by
    unfold reassemble at h
    split at h
    · rename_i u hu; simp only [Option.some.injEq] at h; subst h; exact hu
    · simp at h
  simp only [matchRow, matchSk_of_fill p row.1 row.2 [] hf]
  cases matchTm p t [] <;> simp

theorem matchRow_dec (k : Cut α) (p : Pat α) (t : Tm α) :
    matchRow p (k.d t) = matchTm p t [] :=
  matchRow_of_reassemble p (k.sec t)

/-- The answers of a pattern over a store: one per matching row. -/
def matchStore (p : Pat α) (S : Multiset (Row α)) : Multiset (Subst α) := S.filterMap (matchRow p)

/-- Over a store, the answers are those of the facts it holds, whatever the cut. -/
theorem matchStore_store (k : Cut α) (p : Pat α) (B : Multiset (Tm α)) :
    matchStore p (store k B) = B.filterMap fun t => matchTm p t [] := by
  have h : (matchRow p ∘ k.d) = fun t => matchTm p t [] := funext (matchRow_dec k p)
  simp [matchStore, store, Multiset.filterMap_map, h]

/-- A re-cut commutes with match, for every reachable store. -/
theorem transfer_match {k₁ : Cut α} (k₂ : Cut α) (p : Pat α) {S : Multiset (Row α)}
    (h : Reach k₁ S) : matchStore p (transfer k₂ S) = matchStore p S := by
  rw [h.canonical, transfer_store, matchStore_store, matchStore_store]

/-! ## Compiling a pattern once per skeleton -/

/-- A column program: what to do with the next values of a row. -/
inductive Instr (α : Type) where
  /-- match the next value against a pattern -/
  | col (p : Pat α)
  /-- bind a variable to the subterm a skeleton part rebuilds from the next values -/
  | derived (x : ℕ) (s : Skel α)

/-- Unifying a pattern with a skeleton: a column program, or none when the
skeleton cannot match. -/
def compile : Pat α → Skel α → Option (List (Instr α))
  | p, .hole => some [.col p]
  | .var x, .atom b => some [.derived x (.atom b)]
  | .var x, .node l r => some [.derived x (.node l r)]
  | .atom a, .atom b => if a = b then some [] else none
  | .node p q, .node l r => (compile p l).bind fun i₁ => (compile q r).map fun i₂ => i₁ ++ i₂
  | .atom _, .node _ _ => none
  | .node _ _, .atom _ => none

/-- Running a column program on a row's values. -/
def run : List (Instr α) → List (Tm α) → Subst α → Option (Subst α × List (Tm α))
  | [], ts, σ => some (σ, ts)
  | .col p :: is, ts, σ =>
    match ts with
    | t :: ts' => (matchTm p t σ).bind fun σ' => run is ts' σ'
    | [] => none
  | .derived x s :: is, ts, σ =>
    (fill s ts).bind fun u => (bindVar x u.1 σ).bind fun σ' => run is u.2 σ'

theorem run_append (i₁ i₂ : List (Instr α)) (ts : List (Tm α)) (σ : Subst α) :
    run (i₁ ++ i₂) ts σ = (run i₁ ts σ).bind fun r => run i₂ r.2 r.1 := by
  induction i₁ generalizing ts σ with
  | nil => simp [run]
  | cons i is ih =>
    cases i with
    | col p =>
      cases ts with
      | nil => simp [run]
      | cons t ts' =>
        simp only [List.cons_append, run]
        cases matchTm p t σ <;> simp [ih]
    | derived x s =>
      simp only [List.cons_append, run]
      rcases fill s ts with _ | u
      · simp
      · simp [ih, Option.bind_assoc]

/-- Matching a row is the column program of its skeleton run on its values:
the skeleton part is decided once per table. -/
theorem matchSk_staged (p : Pat α) (s : Skel α) (ts : List (Tm α)) (σ : Subst α) :
    matchSk p s ts σ = (compile p s).bind fun is => run is ts σ := by
  induction s generalizing p ts σ with
  | hole =>
    cases ts with
    | nil => cases p <;> simp [matchSk, compile, run]
    | cons t ts' => cases p <;> simp [matchSk, compile, run] <;> cases matchTm _ t σ <;> simp
  | atom b =>
    cases p with
    | var x => simp [matchSk, compile, run, fill]; cases bindVar x (.atom b) σ <;> simp
    | atom a => by_cases hab : a = b <;> simp [matchSk, compile, run, hab]
    | node p q => simp [matchSk, compile]
  | node l r ihl ihr =>
    cases p with
    | var x =>
      simp only [matchSk, compile, Option.bind_some, run]
      congr 1; funext u
      cases h : bindVar x u.1 σ <;> rfl
    | atom a => simp [matchSk, compile]
    | node p q =>
      simp only [matchSk, compile, ihl]
      cases hp : compile p l with
      | none => simp
      | some i₁ =>
        cases hq : compile q r with
        | none =>
          simp only [Option.bind_some, Option.map_none, Option.bind_none]
          cases run i₁ ts σ with
          | none => simp
          | some r₁ => simp [ihr, hq]
        | some i₂ =>
          simp only [Option.bind_some, Option.map_some, run_append]
          cases run i₁ ts σ with
          | none => simp
          | some r₁ => simp [ihr, hq]

/-! ## Examples -/

/-- `(SPO g p o)` as a chain of nodes. -/
def spo (g p o : String) : Tm String :=
  .node (.atom "SPO") (.node (.atom g) (.node (.atom p) (.atom o)))

/-- The predicate stays in the skeleton; subject and object become holes. -/
def predicatePolicy : Policy String := fun q t =>
  match q, t with
  | [true, false], .atom _ => true
  | [true, true, true], .atom _ => true
  | _, _ => false

example : dec predicatePolicy (spo "g1" "transcribed_to" "t7") =
    (.node (.atom "SPO") (.node .hole (.node (.atom "transcribed_to") .hole)),
      [.atom "g1", .atom "t7"]) := by decide

example : reassemble (dec predicatePolicy (spo "g1" "transcribed_to" "t7")) =
    some (spo "g1" "transcribed_to" "t7") := reassemble_dec _ _

/-- Two facts of one table share a skeleton and differ in their rows. -/
example : (dec predicatePolicy (spo "g1" "transcribed_to" "t7")).1 =
    (dec predicatePolicy (spo "g2" "transcribed_to" "t9")).1 := by decide

/-- Keeping only the skeleton loses the facts: not injective. -/
theorem skeleton_only_not_injective :
    ¬ Function.Injective fun t : Tm String => (dec predicatePolicy t).1 := by
  intro h
  have := h (a₁ := spo "g1" "transcribed_to" "t7") (a₂ := spo "g2" "transcribed_to" "t9")
    (by decide)
  exact absurd this (by decide)

/-- A store no insert or remove reaches can break the re-cut law for removal:
a row cut at the root is not the row an uncut store would hold. -/
theorem transfer_remove_needs_reachable :
    ∃ (S : Multiset (Row String)) (t : Tm String),
      transfer (rootCut : Cut String) (remove (noCut : Cut String) t S) ≠
        remove (rootCut : Cut String) t (transfer (rootCut : Cut String) S) := by
  refine ⟨{(.hole, [.atom "a"])}, .atom "a", ?_⟩
  simp only [transfer, remove, store, denote, noCut_d, rootCut_d]
  decide

end Mettapedia.Machines.ShapeStore
