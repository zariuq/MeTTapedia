import Mathlib.Data.List.Nodup
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Init.Data.Vector.OfFn

/-!
# Answer tables retain derivations, not just distinct answers

An answer key may include both a call and a returned value. A clause
occurrence supplies one alternative, with a list of ordered prerequisites.
Proofs are finite trees labelled by clause occurrences: two equal
clauses are still two choices, and using an answer twice is two
independent choices of a proof of it.

One table layer stores a count per key, without expanding the product of
the prerequisite proofs. A separate set computation answers existence.
Neither computation claims to have detected completion at a finite depth.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.Derivation.AnswerTable

variable {n : ℕ}

structure Clause (n : ℕ) where
  conclusion : Fin n
  premises : List (Fin n)
  deriving DecidableEq, Repr

inductive Proof where
  | node (clause : ℕ) (premises : List Proof)

def eligible (program : List (Clause n)) (key : Fin n) : List (Fin program.length) :=
  (List.finRange program.length).filter fun i => (program.get i).conclusion == key

@[simp] theorem eligible_iff (program : List (Clause n)) (key : Fin n) (i : Fin program.length) :
    i ∈ eligible program key ↔ (program.get i).conclusion = key := by
  simp [eligible]

def choices {Q A : Type*} (available : Q → List A) : List Q → List (List A)
  | [] => [[]]
  | query :: rest =>
    (available query).flatMap fun first => (choices available rest).map (List.cons first)

theorem mem_choices {Q A : Type*} (available : Q → List A) (queries : List Q) (proofs : List A) :
    proofs ∈ choices available queries ↔ List.Forall₂ (fun q a => a ∈ available q) queries proofs := by
  induction queries generalizing proofs with
  | nil =>
    constructor
    · intro found
      obtain rfl := List.mem_singleton.mp found
      exact .nil
    · intro found
      cases found
      exact List.mem_cons_self
  | cons query rest ih =>
    simp only [choices, List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨first, belongs, tail, listed, rfl⟩
      exact .cons belongs ((ih tail).mp listed)
    · intro proof
      cases proof with
      | cons first others => exact ⟨_, first, _, (ih _).mpr others, rfl⟩

theorem choices_distinct {Q A : Type*} (available : Q → List A) (queries : List Q)
    (distinct : ∀ q, (available q).Nodup) : (choices available queries).Nodup := by
  induction queries with
  | nil => simp [choices]
  | cons query rest ih =>
    apply List.nodup_flatMap.mpr
    refine ⟨fun first _ => ih.map (fun _ _ eq => (List.cons.inj eq).2), (distinct query).imp ?_⟩
    intro first second separated
    apply List.disjoint_left.mpr
    intro path inFirst inSecond
    obtain ⟨tail₁, _, equals₁⟩ := List.mem_map.mp inFirst
    obtain ⟨tail₂, _, equals₂⟩ := List.mem_map.mp inSecond
    exact separated (List.cons.inj (equals₁.trans equals₂.symm)).1

theorem choices_length {Q A : Type*} (available : Q → List A) (queries : List Q) :
    (choices available queries).length = (queries.map (List.length ∘ available)).prod := by
  induction queries with
  | nil => rfl
  | cons query rest ih =>
    simp [choices, List.length_flatMap, ih, Function.comp_def]

/-- The proof judgment for a height allowance. This checks the chosen
clause and its given proof children; it does not run the enumeration
or build an answer table. -/
def DerivesAt (program : List (Clause n)) : ℕ → Fin n → Proof → Prop
  | 0, _, _ => False
  | height + 1, key, .node clause premises =>
    ∃ i : Fin program.length, i.val = clause ∧ (program.get i).conclusion = key ∧
      List.Forall₂ (DerivesAt program height) (program.get i).premises premises

def Derives (program : List (Clause n)) (key : Fin n) (proof : Proof) : Prop :=
  ∃ limit, DerivesAt program limit key proof

/-- Direct expansion, including proof children for all independent
uses. This is the reference for the compressed table. -/
def enumerate (program : List (Clause n)) : ℕ → Fin n → List Proof
  | 0, _ => []
  | height + 1, key => (eligible program key).flatMap fun i =>
    (choices (enumerate program height) (program.get i).premises).map (.node i.val)

theorem mem_enumerate_iff (program : List (Clause n)) (height : ℕ) (key : Fin n) (proof : Proof) :
    proof ∈ enumerate program height key ↔ DerivesAt program height key proof := by
  induction height generalizing key proof with
  | zero => simp [enumerate, DerivesAt]
  | succ height ih =>
    cases proof with
    | node label children =>
      simp only [enumerate, DerivesAt, List.mem_flatMap, eligible_iff, List.mem_map]
      constructor
      · rintro ⟨i, concludes, kids, present, equal⟩
        obtain ⟨tag, rfl⟩ := Proof.node.inj equal
        exact ⟨i, tag, concludes, ((mem_choices _ _ _).mp present).imp
          (fun q proof member => (ih q proof).mp member)⟩
      · rintro ⟨i, rfl, concludes, childrenValid⟩
        exact ⟨i, concludes, children, (mem_choices _ _ _).mpr
          (childrenValid.imp (fun q proof derives => (ih q proof).mpr derives)), rfl⟩

theorem enumerate_distinct (program : List (Clause n)) (height : ℕ) (key : Fin n) :
    (enumerate program height key).Nodup := by
  induction height generalizing key with
  | zero => simp [enumerate]
  | succ height ih =>
    rw [enumerate]
    apply List.nodup_flatMap.mpr
    refine ⟨fun i _ => (choices_distinct _ _ ih).map (fun _ _ eq => (Proof.node.inj eq).2), ?_⟩
    have distinct : (eligible program key).Nodup := List.Nodup.filter _ (List.nodup_finRange _)
    apply distinct.imp
    intro i j separates
    apply List.disjoint_left.mpr
    intro proof fromI fromJ
    obtain ⟨_, _, sameI⟩ := List.mem_map.mp fromI
    obtain ⟨_, _, sameJ⟩ := List.mem_map.mp fromJ
    exact separates (Fin.ext (Proof.node.inj (sameI.trans sameJ.symm)).1)

/-! ## Table recurrence -/

def countRound (program : List (Clause n)) (previous : Fin n → ℕ) (key : Fin n) : ℕ :=
  ((eligible program key).map fun i => ((program.get i).premises.map previous).prod).sum

/-- Each layer materializes all its counts. Lookup of a prerequisite
does not recompute its earlier layer or expand its proof trees. -/
def counts (program : List (Clause n)) : ℕ → Vector ℕ n
  | 0 => Vector.replicate n 0
  | limit + 1 =>
    let previous := counts program limit
    Vector.ofFn fun key => countRound program (fun q => previous[q.val]'q.isLt) key

theorem counts_exact (program : List (Clause n)) (limit : ℕ) (key : Fin n) :
    (counts program limit)[key.val]'key.isLt = (enumerate program limit key).length := by
  induction limit generalizing key with
  | zero => simp [counts, enumerate]
  | succ limit ih =>
    simp only [counts, Vector.getElem_ofFn, enumerate, List.length_flatMap, countRound, List.length_map,
      choices_length]
    congr 1
    apply List.map_congr_left
    intro i _
    congr 1
    apply List.map_congr_left
    intro q _
    exact ih q

def presence (program : List (Clause n)) : ℕ → Finset (Fin n)
  | 0 => ∅
  | depth + 1 =>
    let previous := presence program depth
    Finset.univ.filter fun q => (eligible program q).any
      (fun i => (program.get i).premises.all (fun p => decide (p ∈ previous)))

private theorem exists_children {Q A : Type*} (R : Q → A → Prop) (queries : List Q) :
    (∃ children, List.Forall₂ R queries children) ↔ ∀ q ∈ queries, ∃ a, R q a := by
  induction queries with
  | nil => simp
  | cons q rest ih =>
    constructor
    · rintro ⟨children, proof⟩
      cases proof with
      | cons first remaining =>
        intro p present
        rcases List.mem_cons.mp present with rfl | found
        · exact ⟨_, first⟩
        · exact ih.mp ⟨_, remaining⟩ p found
    · intro all
      obtain ⟨head, validHead⟩ := all q List.mem_cons_self
      obtain ⟨tail, validTail⟩ := ih.mpr (fun k found => all k (List.mem_cons_of_mem _ found))
      exact ⟨head :: tail, .cons validHead validTail⟩

theorem presence_exact (program : List (Clause n)) (limit : ℕ) (key : Fin n) :
    key ∈ presence program limit ↔ ∃ proof, DerivesAt program limit key proof := by
  induction limit generalizing key with
  | zero => simp [presence, DerivesAt]
  | succ limit ih =>
    simp only [presence, Finset.mem_filter, Finset.mem_univ, true_and, List.any_eq_true,
      eligible_iff, List.all_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨i, concludes, all⟩
      obtain ⟨children, valid⟩ := (exists_children _ _).mpr
        (fun q member => (ih q).mp (all q member))
      exact ⟨.node i.val children, i, rfl, concludes, valid⟩
    · rintro ⟨proof, derives⟩
      cases proof with
      | node label children =>
        obtain ⟨i, _, concludes, valid⟩ := derives
        have child := (exists_children (DerivesAt program limit) (program.get i).premises).mp ⟨children, valid⟩
        exact ⟨i, concludes, fun q member => (ih q).mpr (child q member)⟩

end Mettapedia.Machines.TIsa.Derivation.AnswerTable
