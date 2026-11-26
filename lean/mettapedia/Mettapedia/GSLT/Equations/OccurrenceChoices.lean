import Mathlib.Data.List.Basic
import Mathlib.Data.List.Forall2

/-! # From match witnesses to occurrence replacements

The finite input at a row is the complete list of admissible replacement
blocks, possibly repeated because different witnesses produce them.
A nondeterministic rewrite chooses one block per nonempty fibre. A
deterministic rewrite needs exactly one *distinct* block in each nonempty
fibre. Neither of these readings permits taking the same occurrence twice.

The block is the observable effect, not a witness or an implementation's
representative. If raw storage is observable, compare raw blocks. If a
client really observes a quotient, the same results apply after mapping
to its observations; this alone does not authorize choosing a raw block.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Equations.OccurrenceChoices

variable {I B K : Type*}

/-- A single permitted choice, with no edit only for an empty fibre. -/
def Permitted (answers : List B) : Option B → Prop
  | none => answers = []
  | some b => b ∈ answers

/-- The option describes the *entire* fibre of results, not merely one
witness. In particular there is no confusion between absence and conflict. -/
def Exact (answers : List B) (result : Option B) : Prop :=
  ∀ b, b ∈ answers ↔ result = some b

def Unambiguous (answers : List B) : Prop :=
  ∀ a ∈ answers, ∀ b ∈ answers, a = b

theorem exact_permitted {answers : List B} {result : Option B}
    (exact : Exact answers result) : Permitted answers result := by
  cases result with
  | none =>
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro b mem
    have bad := (exact b).1 mem
    cases bad
  | some b => exact (exact b).2 rfl

theorem exact_unique {answers : List B} {a b : Option B}
    (first : Exact answers a) (second : Exact answers b) : a = b := by
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some y =>
      have impossible := (first y).1 ((second y).2 rfl)
      cases impossible
  | some x => exact ((second x).1 ((first x).2 rfl)).symm

/-- Distinct witness bindings are harmless exactly when they give the same
replacement. This is an existence theorem about the replacement, not a
choice of a witness or tie-breaking order. -/
theorem exact_exists_iff (answers : List B) :
    (∃ result, Exact answers result) ↔ Unambiguous answers := by
  constructor
  · rintro ⟨result, exact⟩ x hx y hy
    exact Option.some.inj (((exact x).1 hx).symm.trans ((exact y).1 hy))
  · intro same
    cases answers with
    | nil => exact ⟨none, by simp [Exact]⟩
    | cons x xs =>
      refine ⟨some x, fun y => ?_⟩
      exact ⟨fun mem => congrArg some (same x (by simp) y mem),
        fun eq => by cases eq; simp⟩

theorem selected_count (answers : I → List B) {rows : List I} {plan : List (Option B)}
    (valid : List.Forall₂ (fun i result => Permitted (answers i) result) rows plan) :
    (plan.filterMap id).length =
      (rows.filter fun i => !(answers i).isEmpty).length := by
  induction valid with
  | nil => rfl
  | @cons i pick is ps atRow tail ih =>
    cases pick with
    | none =>
      simp [Permitted] at atRow
      change (ps.filterMap id).length = _
      simpa [atRow] using ih
    | some b =>
      have nonempty : (answers i).isEmpty = false := by
        cases it : answers i with
        | nil => simp [Permitted, it] at atRow
        | cons _ _ => rfl
      simp [nonempty]
      exact ih

/-- Every finite row population has a per-occurrence choice, even if some
fibres disagree. This witness is not a prescribed selection order. -/
theorem a_plan_exists (answers : I → List B) (rows : List I) :
    ∃ plan, List.Forall₂ (fun i result => Permitted (answers i) result) rows plan := by
  induction rows with
  | nil => exact ⟨[], .nil⟩
  | cons i later ih =>
    obtain ⟨rest, permitted⟩ := ih
    cases h : answers i with
    | nil => exact ⟨none :: rest, .cons h permitted⟩
    | cons b bs => exact ⟨some b :: rest, .cons (by simp [Permitted, h]) permitted⟩

/-- If the exposed replacement is a quotient value, agreement is asked
of the entire projected fibre. One successful raw witness alone is not
sufficient even for this weaker observation. -/
theorem observed_exact_iff (observe : B → K) (answers : List B) (pick : Option K) :
    Exact (answers.map observe) pick ↔
      ∀ value, (∃ b ∈ answers, observe b = value) ↔ pick = some value := by
  simp only [Exact, List.mem_map]

section Executable

variable [DecidableEq B]

/-- The outer option signals a disagreement. `some none` means the row
had no replacement. This one-pass check is independent of witness order. -/
def resolve (answers : List B) : Option (Option B) :=
  if ∀ b ∈ answers, answers.head? = some b then some answers.head? else none

theorem resolve_iff (answers : List B) (p : Option B) :
    resolve answers = some p ↔ Exact answers p := by
  constructor
  · unfold resolve
    split
    · rename_i agrees
      intro eq
      have same : answers.head? = p := Option.some.inj eq
      exact fun b => ⟨fun mem => same ▸ agrees b mem,
        fun h => List.mem_of_head? (same.trans h)⟩
    · intro impossible
      cases impossible
  · intro exact
    have headEq : answers.head? = p := by
      cases h : answers with
      | nil =>
        cases p with
        | none => rfl
        | some b => have bad := (exact b).2 rfl; simp [h] at bad
      | cons b bs =>
        exact ((exact b).1 (by simp [h])).symm
    unfold resolve
    rw [headEq]
    exact if_pos (fun b mem => (exact b).1 mem)

def prepare (answers : I → List B) : List I → Option (List (Option B))
  | [] => some []
  | i :: later => do
    let head ← resolve (answers i)
    let tail ← prepare answers later
    pure (head :: tail)

theorem prepare_iff (answers : I → List B) (rows : List I) (plan : List (Option B)) :
    prepare answers rows = some plan ↔ List.Forall₂ (fun i p => Exact (answers i) p) rows plan := by
  induction rows generalizing plan with
  | nil =>
    rw [List.forall₂_nil_left_iff]
    simp [prepare, eq_comm]
  | cons i later ih =>
    cases plan with
    | nil => simp [prepare, Option.bind_eq_some_iff, List.forall₂_nil_right_iff]
    | cons p tail =>
      simp [prepare, Option.bind_eq_some_iff, List.forall₂_cons, ih, resolve_iff]

theorem prepare_exists_iff (answers : I → List B) (rows : List I) :
    (∃ plan, prepare answers rows = some plan) ↔ ∀ i ∈ rows, Unambiguous (answers i) := by
  induction rows with
  | nil => simp [prepare]
  | cons i later ih =>
    constructor
    · rintro ⟨plan, eq⟩
      cases plan with
      | nil => simp [prepare, Option.bind_eq_some_iff] at eq
      | cons p tail =>
        obtain ⟨atHead, atTail⟩ := List.forall₂_cons.mp ((prepare_iff ..).1 eq)
        exact List.forall_mem_cons.mpr ⟨(exact_exists_iff _).mp ⟨p, atHead⟩,
          ih.mp ⟨tail, (prepare_iff ..).2 atTail⟩⟩
    · intro all
      obtain ⟨atHead, laterOK⟩ := List.forall_mem_cons.mp all
      obtain ⟨p, hit⟩ := (exact_exists_iff (answers i)).2 atHead
      obtain ⟨tail, compiled⟩ := ih.mpr laterOK
      exact ⟨p :: tail, (prepare_iff ..).2
        (.cons hit ((prepare_iff ..).1 compiled))⟩

omit [DecidableEq B] in
private theorem same_plan_iff
    (before after : I → List B) {rows : List I} {plan : List (Option B)}
    (old : List.Forall₂ (fun i p => Exact (before i) p) rows plan) :
    List.Forall₂ (fun i p => Exact (after i) p) rows plan ↔
      ∀ i ∈ rows, ∀ b, b ∈ before i ↔ b ∈ after i := by
  induction old with
  | nil => simp
  | @cons i p rows plan head _ ih =>
    rw [List.forall₂_cons, List.forall_mem_cons, ih]
    exact and_congr (by
      constructor
      · intro next b
        exact (head b).trans (next b).symm
      · intro next b
        exact (next b).symm.trans (head b)) Iff.rfl

/-- Reusing a deterministic plan after changing equations is exact iff
every old replacement fibre still exposes the same results. A previously
admissible replacement remaining admissible is weaker than this: an alias
append can enable an old miss or introduce another replacement. -/
theorem reuse_iff (before after : I → List B) {rows : List I} {plan : List (Option B)}
    (old : prepare before rows = some plan) :
    prepare after rows = some plan ↔
      ∀ i ∈ rows, ∀ b, b ∈ before i ↔ b ∈ after i := by
  rw [prepare_iff]
  exact same_plan_iff before after ((prepare_iff ..).1 old)

end Executable

end Mettapedia.GSLT.Equations.OccurrenceChoices
