import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.Dedup
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Lemmas

/-!
# Streaming a step equals its batch

A step's **rows** are the matches of its sources. Each **sink** of the step collects what every row
gives it in a **stage**, and when the matches are done the sink **publishes** its stage into the
space. A streaming implementation joins each row into the stage as the row arrives, in whatever
order its query engine finds the rows; the step's own meaning takes all the rows at once.

Example: the rows `σ₁ = {x ↦ a}` and `σ₂ = {x ↦ b}` of the source `(item $x)` give the sink
`(+ (seen $x))` the stage `{(seen a)} ∪ {(seen b)}`, in either order, and the publication adds both.

* `Stage.Commutative`: the stage is a commutative monoid (a unit and an associative,
  commutative join).
* `stream_eq_of_perm`, `streamStep_eq_of_perm`: **with a commutative stage the order of the rows
  cannot be observed**: any two arrival orders of one bag of rows stage, and publish, the same.
* `stream_eq_of_mem_iff`, `streamStep_eq_of_mem_iff`: **with an idempotent stage only the set of
  rows can be observed**, so a stage needs to hold only distinct contributions, not one per match.
* `finsetUnion`: union of finite sets is such a stage; every MM2 sink of the 17 programs stages
  this way (`+`, `-`, `count`, `fmin`, `fmax`, `sum`, `pure`).
* `first_observes_order`: **a non-commutative stage observes the order of the rows.** The sink
  that keeps the first row's value publishes `a` for the arrival order `[a, b]` and `b` for
  `[b, a]`, so streaming it is not a function of the step's rows.
* `liveRead_not_batch`: **reads must see the snapshot.** If each row is published as it
  arrives and later rows are checked against the space so changed, a row can disable another:
  two rows that each remove what the other reads leave one atom live, where the step removes
  both.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK.StepSpecialization

universe uR uS uM

/-- **A stage**: where a sink collects what the rows give it. -/
structure Stage (M : Type uM) where
  empty : M
  join : M → M → M

/-- **A commutative stage**: a commutative monoid. -/
structure Stage.Commutative {M : Type uM} (st : Stage M) : Prop where
  assoc : ∀ a b c, st.join (st.join a b) c = st.join a (st.join b c)
  comm : ∀ a b, st.join a b = st.join b a
  unit : ∀ a, st.join st.empty a = a

/-- **An idempotent stage**: joining a contribution twice is joining it once. -/
def Stage.Idempotent {M : Type uM} (st : Stage M) : Prop := ∀ a, st.join a a = a

/-- **A sink**: its stage, what each row contributes, and its publication. -/
structure Sink (ρ : Type uR) (S : Type uS) (M : Type uM) where
  stage : Stage M
  inject : ρ → M
  publish : M → S → S

namespace Sink

variable {ρ : Type uR} {S : Type uS} {M : Type uM} (k : Sink ρ S M)

/-- **Streaming**: the rows arrive as a list; each is joined into the stage as it arrives. -/
def stream (rows : List ρ) : M := rows.foldl (fun acc r => k.stage.join acc (k.inject r)) k.stage.empty

/-- The streamed step: stage the rows in their arrival order, then publish once. -/
def streamStep (rows : List ρ) (s : S) : S := k.publish (k.stream rows) s

/-- The stage of a list of rows from a starting stage, folded from the right. -/
def gather (rows : List ρ) : M := rows.foldr (fun r acc => k.stage.join (k.inject r) acc) k.stage.empty

variable {k}

theorem foldl_join (comm : k.stage.Commutative) :
    ∀ (rows : List ρ) (a : M),
      rows.foldl (fun acc r => k.stage.join acc (k.inject r)) a = k.stage.join a (k.gather rows)
  | [], a => by
      simp only [List.foldl_nil, gather, List.foldr_nil]
      rw [comm.comm, comm.unit]
  | r :: rs, a => by
      simp only [List.foldl_cons, gather, List.foldr_cons]
      rw [foldl_join comm rs, comm.assoc]
      rfl

/-- **Streaming is the gathered stage**, whatever the arrival order. -/
theorem stream_eq_gather (comm : k.stage.Commutative) (rows : List ρ) :
    k.stream rows = k.gather rows := by
  unfold stream
  rw [foldl_join comm, comm.unit]

theorem gather_perm (comm : k.stage.Commutative) {l l' : List ρ} (perm : l.Perm l') :
    k.gather l = k.gather l' := by
  induction perm with
  | nil => rfl
  | cons r _ ih => simp only [gather, List.foldr_cons] at ih ⊢; rw [ih]
  | swap a b l =>
      simp only [gather, List.foldr_cons]
      rw [← comm.assoc, comm.comm (k.inject b) (k.inject a), comm.assoc]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- **With a commutative stage the order of the rows cannot be observed.** -/
theorem stream_eq_of_perm (comm : k.stage.Commutative) {l l' : List ρ} (perm : l.Perm l') :
    k.stream l = k.stream l' := by
  rw [stream_eq_gather comm, stream_eq_gather comm, gather_perm comm perm]

/-- **Two arrival orders of one bag of rows publish the same space.** -/
theorem streamStep_eq_of_perm (comm : k.stage.Commutative) {l l' : List ρ} (perm : l.Perm l')
    (s : S) : k.streamStep l s = k.streamStep l' s := by
  unfold streamStep
  rw [stream_eq_of_perm comm perm]

/-- With an idempotent stage, a row already gathered adds nothing. -/
theorem gather_cons_of_mem [DecidableEq ρ] (comm : k.stage.Commutative)
    (idem : k.stage.Idempotent) {r : ρ} {l : List ρ} (mem : r ∈ l) :
    k.gather (r :: l) = k.gather l := by
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem mem
  have perm : (l₁ ++ r :: l₂).Perm (r :: (l₁ ++ l₂)) := List.perm_middle
  rw [gather_perm comm (perm.cons r), gather_perm comm perm]
  simp only [gather, List.foldr_cons]
  rw [← comm.assoc, idem]

theorem gather_dedup [DecidableEq ρ] (comm : k.stage.Commutative) (idem : k.stage.Idempotent) :
    ∀ l : List ρ, k.gather l.dedup = k.gather l
  | [] => rfl
  | r :: l => by
      by_cases mem : r ∈ l
      · rw [List.dedup_cons_of_mem mem, gather_dedup comm idem l, gather_cons_of_mem comm idem mem]
      · rw [List.dedup_cons_of_notMem mem]
        simp only [gather, List.foldr_cons]
        rw [show List.foldr (fun r acc => k.stage.join (k.inject r) acc) k.stage.empty l.dedup =
          k.gather l.dedup from rfl, gather_dedup comm idem l]
        rfl

/-- **With an idempotent stage only the set of rows can be observed**: two arrival lists holding
the same rows, with any multiplicities, in any order, stage the same. -/
theorem stream_eq_of_mem_iff [DecidableEq ρ] (comm : k.stage.Commutative)
    (idem : k.stage.Idempotent) {l l' : List ρ} (same : ∀ r, r ∈ l ↔ r ∈ l') :
    k.stream l = k.stream l' := by
  rw [stream_eq_gather comm, stream_eq_gather comm, ← gather_dedup comm idem l,
    ← gather_dedup comm idem l']
  apply gather_perm comm
  exact (List.perm_ext_iff_of_nodup (List.nodup_dedup l) (List.nodup_dedup l')).mpr fun r => by
    simp only [List.mem_dedup]; exact same r

theorem streamStep_eq_of_mem_iff [DecidableEq ρ] (comm : k.stage.Commutative)
    (idem : k.stage.Idempotent) {l l' : List ρ} (same : ∀ r, r ∈ l ↔ r ∈ l') (s : S) :
    k.streamStep l s = k.streamStep l' s := by
  unfold streamStep
  rw [stream_eq_of_mem_iff comm idem same]

end Sink

/-! ## Union of finite sets is such a stage -/

section FinsetUnion

variable {α : Type uM} [DecidableEq α]

/-- **Union of finite sets**: the stage of every MM2 sink here. -/
def finsetUnion : Stage (Finset α) := ⟨∅, (· ∪ ·)⟩

theorem finsetUnion_commutative : (finsetUnion (α := α)).Commutative where
  assoc := Finset.union_assoc
  comm := Finset.union_comm
  unit := Finset.empty_union

theorem finsetUnion_idempotent : (finsetUnion (α := α)).Idempotent := Finset.union_self

/-- The streamed stage of a union sink is the union of the rows' contributions. -/
theorem stream_finsetUnion {ρ : Type uR} {S : Type uS} (inject : ρ → Finset α)
    (publish : Finset α → S → S) (rows : List ρ) (x : α) :
    x ∈ (⟨finsetUnion, inject, publish⟩ : Sink ρ S (Finset α)).stream rows ↔
      ∃ r ∈ rows, x ∈ inject r := by
  rw [Sink.stream_eq_gather finsetUnion_commutative]
  induction rows with
  | nil => simp [Sink.gather, finsetUnion]
  | cons r rs ih =>
      simp only [Sink.gather, List.foldr_cons, finsetUnion, Finset.mem_union, List.mem_cons] at ih ⊢
      rw [ih]
      constructor
      · rintro (h | ⟨r', m, h⟩)
        · exact ⟨r, Or.inl rfl, h⟩
        · exact ⟨r', Or.inr m, h⟩
      · rintro ⟨r', (rfl | m), h⟩
        · exact Or.inl h
        · exact Or.inr ⟨r', m, h⟩

end FinsetUnion

/-! ## A stage that is not commutative observes the order of the rows -/

/-- **The first row's value**: a monoid (a unit and an associative join) that is not
commutative. -/
def firstStage (α : Type uM) : Stage (Option α) :=
  ⟨none, fun a b => match a with | some x => some x | none => b⟩

theorem firstStage_assoc {α : Type uM} (a b c : Option α) :
    (firstStage α).join ((firstStage α).join a b) c =
      (firstStage α).join a ((firstStage α).join b c) := by
  cases a <;> rfl

theorem firstStage_unit {α : Type uM} (a : Option α) : (firstStage α).join (firstStage α).empty a = a :=
  rfl

/-- The sink writing the first row's value: rows are values, and the publication replaces the
space by the first value seen. -/
def firstSink (α : Type uM) : Sink α (Option α) (Option α) := ⟨firstStage α, some, fun st _ => st⟩

/-- **Streaming a sink that is not commutative observes the order of the rows**: the arrival
orders `[a, b]` and `[b, a]` of one bag of two rows publish different spaces. -/
theorem first_observes_order {α : Type uM} {a b : α} (ne : a ≠ b) :
    [a, b].Perm [b, a] ∧
      (firstSink α).streamStep [a, b] none ≠ (firstSink α).streamStep [b, a] none := by
  refine ⟨List.Perm.swap b a [], ?_⟩
  simp only [Sink.streamStep, Sink.stream, firstSink, firstStage, List.foldl_cons, List.foldl_nil]
  intro h
  exact ne (Option.some.inj h)

theorem firstStage_not_commutative {α : Type uM} {a b : α} (ne : a ≠ b) :
    ¬ (firstStage α).Commutative := fun comm => by
  have := comm.comm (some a) (some b)
  simp only [firstStage] at this
  exact ne (Option.some.inj this)

/-! ## Reads must see the snapshot -/

section LiveRead

variable {α : Type uM} [DecidableEq α] {ρ : Type uR}

/-- **A step that removes**: each row reads some atoms and removes some; the step's rows are the
rows whose reads the snapshot holds, and the step removes what all of them remove. -/
structure RemovalStep (α : Type uM) (ρ : Type uR) where
  reads : ρ → Finset α
  removes : ρ → Finset α

namespace RemovalStep

variable (rs : RemovalStep α ρ)

/-- The step's meaning: the rows enabled at the snapshot, all published at once. -/
def batch (candidates : List ρ) (s : Finset α) : Finset α :=
  s \ (candidates.filter fun r => rs.reads r ⊆ s).foldr (fun r acc => rs.removes r ∪ acc) ∅

/-- **Live reads**: each row is checked against the space as earlier rows left it, and published
at once. -/
def live : List ρ → Finset α → Finset α
  | [], s => s
  | r :: rest, s => if rs.reads r ⊆ s then live rest (s \ rs.removes r) else live rest s

end RemovalStep

/-- **Reads must see the snapshot**: two rows that each remove what the other reads. The step
removes both atoms; read live, the first row disables the second and one atom stays. -/
theorem liveRead_not_batch :
    let rs : RemovalStep Bool Bool := ⟨fun r => {r}, fun r => {!r}⟩
    rs.live [true, false] {true, false} = {true} ∧
      rs.batch [true, false] {true, false} = ∅ := by
  decide

end LiveRead

end Mettapedia.Languages.ProcessCalculi.MORK.StepSpecialization
