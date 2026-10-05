import Mettapedia.TypeTheory.MaterialSets.Hypersets.Presentations
import Mathlib.SetTheory.ZFC.Rank

/-!
# Two readings of a stream

A labelled graph `r : α → β → α → Prop` can be read at a node in two ways. As a hyperset it is
the decoration `decorateLabelled r ℓ a`, with the labels read as hypersets by `ℓ`. As a process
it is what an observer records while walking along its edges: the words of labels along the
finite paths from the node (`Trace`), and, when the walk is forced, the sequence of labels.

**Equality is labelled bisimilarity.** Two nodes, of two labelled graphs whose nodes and labels
may have different types, have the same decoration exactly when a relation matches every step
of one by a step of the other whose label has the same reading, landing on related nodes
(`decorateLabelled_eq_iff_labelledBisimilar`).

**For streams the two readings agree.** A labelled graph is deterministic when every node has
exactly one outgoing edge (`Deterministic`). Its label sequence at a node (`Deterministic.labels`)
is the sequence of labels along the one path from the node (`Deterministic.eq_of_path`).

* Two nodes of deterministic graphs have the same decoration exactly when their label sequences,
  read through the labels' readings, are equal (`decorateLabelled_eq_iff_comp_labels`); for one
  injective reading, exactly when the label sequences are equal (`decorateLabelled_eq_iff_labels`).
* The words of a deterministic graph are the prefixes of its label sequence
  (`Deterministic.trace_iff`), so there the sets of words decide equality as well
  (`decorateLabelled_eq_iff_traces_eq`).
* The function reading: the position graph of a sequence `σ : ℕ → β` steps from `n` to `n + 1`
  with the label `σ n` (`positionRel`), and `streamOf ℓ σ` is its decoration at `0`. It is the
  pair of the first label with the stream of the rest (`streamOf_cons`). Every deterministic
  graph decorates a node as `streamOf` of its label sequence (`decorateLabelled_eq_streamOf`),
  `streamOf ℓ` is injective for an injective reading (`streamOf_injective`), and the hyperset
  streams over `β` are in bijection with the sequences `ℕ → β` (`streamEquiv`), the inverse
  reading off the label sequence (`streamEquiv_symm_decorateLabelled`).

**Where the readings part.** For an injective reading, equal decorations have equal sets of
words (`traces_eq_of_decorateLabelled_eq`). The converse fails once a node may branch:

* `x·(y + z)`, which chooses after its first step (`lateRel`), and `x·y + x·z`, which chooses
  with its first step (`earlyRel`), both have the words `[]`, `[x]`, `[x, y]` and `[x, z]`
  (`late_traces`, `early_traces`), and they are two hypersets whenever `y` and `z` are read
  differently (`late_early_decorateLabelled_ne`).
* The length of a cycle is forgotten: the two-node cycle with alternating labels `b` and `c` is
  the one-node loop that repeats `d` exactly when `b = d` and `c = d`
  (`alternating_eq_repeatStream_iff`), although the cycle comes back to its start after two
  steps and never after one, and the loop after one (`alternating_cycle_length_forgotten`).

**The stream `from n`.** The program `from n = cons n (from (n + 1))` is the deterministic graph
on the numbers that steps from `m` to `m + 1` with the label `m` (`fromRel`). With the labels
read as the hypersets of the finite ordinals (`numeralLabel`), its decoration at `n` is
`fromStream n`. Its label sequence is `k ↦ n + k` (`labels_fromRel`). It satisfies the
program's equation `fromStream n = {kpair (numeralLabel n) (fromStream (n + 1))}`
(`fromStream_spec`), and no other family does (`fromStream_unique`). It is the decoration at `0` of the position graph of
`k ↦ n + k` (`fromStream_eq_streamOf`), a different graph with the same label sequence. It is
not well-founded (`fromStream_not_wf`), it repeats no label (`fromStream_ne_repeatStream`), and
distinct starting numbers give distinct streams (`fromStream_injective`).

R. Milner, *Communication and Concurrency*, Prentice Hall, 1989 (bisimilarity is finer than
trace equivalence); P. Aczel, *Non-well-founded Sets*, CSLI Lecture Notes 14, 1988.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets

open Relation

universe u

/-! ## Labelled bisimulations -/

section LabelledBisimulation

variable {α α' β β' : Type u}

/-- A labelled bisimulation between `r`, whose labels are read by `ℓ`, and `s`, whose labels are
read by `ℓ'`: at related nodes, every step of one is matched by a step of the other whose label
has the same reading, and the two targets are related. -/
def IsLabelledBisimulation (r : α → β → α → Prop) (s : α' → β' → α' → Prop)
    (ℓ : β → HSet.{u}) (ℓ' : β' → HSet.{u}) (R : α → α' → Prop) : Prop :=
  ∀ ⦃a a'⦄, R a a' →
    (∀ b c, r a b c → ∃ b' c', s a' b' c' ∧ ℓ b = ℓ' b' ∧ R c c') ∧
    (∀ b' c', s a' b' c' → ∃ b c, r a b c ∧ ℓ b = ℓ' b' ∧ R c c')

/-- Two nodes are labelled-bisimilar when some labelled bisimulation relates them. -/
def LabelledBisimilar (r : α → β → α → Prop) (s : α' → β' → α' → Prop)
    (ℓ : β → HSet.{u}) (ℓ' : β' → HSet.{u}) (a : α) (a' : α') : Prop :=
  ∃ R, IsLabelledBisimulation r s ℓ ℓ' R ∧ R a a'

end LabelledBisimulation

/-! ## Deterministic labelled graphs -/

section Deterministic

variable {α β : Type u}

/-- A labelled graph is deterministic when every node has exactly one outgoing edge. -/
def Deterministic (r : α → β → α → Prop) : Prop :=
  ∀ a, ∃! e : β × α, r a e.1 e.2

namespace Deterministic

variable {r : α → β → α → Prop} (hr : Deterministic r)

/-- The edge out of a node: its label and its target. -/
noncomputable def step (a : α) : β × α :=
  (hr a).exists.choose

theorem step_spec (a : α) : r a (hr.step a).1 (hr.step a).2 :=
  (hr a).exists.choose_spec

/-- Every edge out of a node is the edge `step`. -/
theorem step_eq {a : α} {b : β} {c : α} (h : r a b c) : hr.step a = (b, c) :=
  (hr a).unique (hr.step_spec a) (show r a (b, c).1 (b, c).2 from h)

/-- The node reached from `a` after `n` steps. -/
noncomputable def node (a : α) (n : ℕ) : α :=
  (fun c => (hr.step c).2)^[n] a

/-- The label sequence at a node: the labels along the one path from it. -/
noncomputable def labels (a : α) (n : ℕ) : β :=
  (hr.step (hr.node a n)).1

theorem node_zero (a : α) : hr.node a 0 = a :=
  rfl

theorem node_succ (a : α) (n : ℕ) : hr.node a (n + 1) = (hr.step (hr.node a n)).2 :=
  Function.iterate_succ_apply' _ n a

theorem node_succ' (a : α) (n : ℕ) : hr.node a (n + 1) = hr.node (hr.step a).2 n :=
  Function.iterate_succ_apply _ n a

theorem labels_zero (a : α) : hr.labels a 0 = (hr.step a).1 :=
  rfl

theorem labels_succ (a : α) (n : ℕ) : hr.labels a (n + 1) = hr.labels (hr.step a).2 n := by
  unfold labels
  rw [node_succ']

/-- The path from `a` follows the edges, labelled by the label sequence. -/
theorem path_spec (a : α) (n : ℕ) : r (hr.node a n) (hr.labels a n) (hr.node a (n + 1)) := by
  rw [node_succ]
  exact hr.step_spec _

/-- A path from `a` along the edges is the path `node a`, and its labels are `labels a`. -/
theorem eq_of_path {a : α} {p : ℕ → α} {σ : ℕ → β} (h0 : p 0 = a)
    (hp : ∀ n, r (p n) (σ n) (p (n + 1))) : p = hr.node a ∧ σ = hr.labels a := by
  have hnode : ∀ n, p n = hr.node a n := by
    intro n
    induction n with
    | zero => exact h0
    | succ n ih => rw [node_succ, ← ih, hr.step_eq (hp n)]
  refine ⟨funext hnode, funext fun n => ?_⟩
  show σ n = (hr.step (hr.node a n)).1
  rw [← hnode n, hr.step_eq (hp n)]

end Deterministic

end Deterministic

/-! ## Words along paths -/

section Traces

variable {α β : Type u}

/-- The words of labels along the finite paths from a node. -/
inductive Trace (r : α → β → α → Prop) : α → List β → Prop
  | nil (a : α) : Trace r a []
  | cons {a : α} {b : β} {c : α} {w : List β} : r a b c → Trace r c w → Trace r a (b :: w)

namespace Trace

variable {r : α → β → α → Prop}

theorem cons_iff {a : α} {b : β} {w : List β} :
    Trace r a (b :: w) ↔ ∃ c, r a b c ∧ Trace r c w := by
  constructor
  · intro h
    cases h with
    | cons hr hw => exact ⟨_, hr, hw⟩
  · rintro ⟨c, hr, hw⟩
    exact Trace.cons hr hw

/-- A node without edges has only the empty word. -/
theorem iff_nil_of_forall_not {a : α} (h : ∀ b c, ¬ r a b c) {w : List β} :
    Trace r a w ↔ w = [] := by
  constructor
  · intro t
    cases t with
    | nil => rfl
    | cons hr _ => exact absurd hr (h _ _)
  · rintro rfl
    exact Trace.nil a

end Trace

/-- The words of a deterministic graph are the prefixes of its label sequence. -/
theorem Deterministic.trace_iff {r : α → β → α → Prop} (hr : Deterministic r) {a : α}
    {w : List β} : Trace r a w ↔ w = (List.range w.length).map (hr.labels a) := by
  induction w generalizing a with
  | nil => exact ⟨fun _ => rfl, fun _ => Trace.nil a⟩
  | cons b w ih =>
    have shift : hr.labels a ∘ Nat.succ = hr.labels (hr.step a).2 :=
      funext fun n => hr.labels_succ a n
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, shift,
      hr.labels_zero, Trace.cons_iff]
    constructor
    · rintro ⟨c, hrc, hw⟩
      have hstep := hr.step_eq hrc
      rw [hstep]
      exact congrArg (b :: ·) ((ih (a := c)).mp hw)
    · intro h
      obtain ⟨hb, hw⟩ := List.cons.inj h
      refine ⟨(hr.step a).2, ?_, (ih (a := (hr.step a).2)).mpr hw⟩
      rw [hb]
      exact hr.step_spec a

end Traces

namespace HSet

/-! ## Equality of decorations is labelled bisimilarity -/

section Bisimilarity

variable {α α' β β' : Type u} {r : α → β → α → Prop} {s : α' → β' → α' → Prop}
  {ℓ : β → HSet.{u}} {ℓ' : β' → HSet.{u}}

/-- Equal decorations: the relation of equal decorations is a labelled bisimulation. -/
theorem labelledBisimilar_of_decorateLabelled_eq {a : α} {a' : α'}
    (h : decorateLabelled r ℓ a = decorateLabelled s ℓ' a') : LabelledBisimilar r s ℓ ℓ' a a' := by
  refine ⟨fun c c' => decorateLabelled r ℓ c = decorateLabelled s ℓ' c', ?_, h⟩
  intro c c' hcc'
  constructor
  · intro b d hrd
    have hmem : kpair (ℓ b) (decorateLabelled r ℓ d) ∈ decorateLabelled s ℓ' c' := by
      rw [← hcc']
      exact mem_decorateLabelled.mpr ⟨b, d, hrd, rfl⟩
    obtain ⟨b', d', hsd, he⟩ := mem_decorateLabelled.mp hmem
    obtain ⟨hl, hd⟩ := kpair_inj.mp he
    exact ⟨b', d', hsd, hl, hd⟩
  · intro b' d' hsd
    have hmem : kpair (ℓ' b') (decorateLabelled s ℓ' d') ∈ decorateLabelled r ℓ c := by
      rw [hcc']
      exact mem_decorateLabelled.mpr ⟨b', d', hsd, rfl⟩
    obtain ⟨b, d, hrd, he⟩ := mem_decorateLabelled.mp hmem
    obtain ⟨hl, hd⟩ := kpair_inj.mp he
    exact ⟨b, d, hrd, hl.symm, hd.symm⟩

/-- The graph on the related pairs of a relation: a step of the first graph together with a step
of the second whose label has the same reading. -/
def pairRel (r : α → β → α → Prop) (s : α' → β' → α' → Prop) (ℓ : β → HSet.{u})
    (ℓ' : β' → HSet.{u}) (R : α → α' → Prop) (p : {p : α × α' // R p.1 p.2}) (b : β)
    (q : {p : α × α' // R p.1 p.2}) : Prop :=
  r p.1.1 b q.1.1 ∧ ∃ b', s p.1.2 b' q.1.2 ∧ ℓ b = ℓ' b'

/-- Labelled-bisimilar nodes have equal decorations: both decorations, read on the pairs of a
labelled bisimulation, decorate the graph `pairRel`, which has only one decoration. -/
theorem decorateLabelled_eq_of_labelledBisimilar {a : α} {a' : α'}
    (h : LabelledBisimilar r s ℓ ℓ' a a') : decorateLabelled r ℓ a = decorateLabelled s ℓ' a' := by
  obtain ⟨R, hR, haa'⟩ := h
  have left : IsLabelledDecoration (pairRel r s ℓ ℓ' R) ℓ
      (fun p => decorateLabelled r ℓ p.1.1) := by
    intro p y
    show y ∈ decorateLabelled r ℓ p.1.1 ↔ _
    rw [mem_decorateLabelled]
    constructor
    · rintro ⟨b, c, hrc, rfl⟩
      obtain ⟨b', c', hsc, hl, hc⟩ := (hR p.2).1 b c hrc
      exact ⟨b, ⟨(c, c'), hc⟩, ⟨hrc, b', hsc, hl⟩, rfl⟩
    · rintro ⟨b, q, ⟨hrq, _⟩, rfl⟩
      exact ⟨b, q.1.1, hrq, rfl⟩
  have right : IsLabelledDecoration (pairRel r s ℓ ℓ' R) ℓ
      (fun p => decorateLabelled s ℓ' p.1.2) := by
    intro p y
    show y ∈ decorateLabelled s ℓ' p.1.2 ↔ _
    rw [mem_decorateLabelled]
    constructor
    · rintro ⟨b', c', hsc, rfl⟩
      obtain ⟨b, c, hrc, hl, hc⟩ := (hR p.2).2 b' c' hsc
      exact ⟨b, ⟨(c, c'), hc⟩, ⟨hrc, b', hsc, hl⟩, by rw [hl]⟩
    · rintro ⟨b, q, ⟨_, b', hsq, hl⟩, rfl⟩
      exact ⟨b', q.1.2, hsq, by rw [hl]⟩
  exact congrFun (left.eq_decorateLabelled.trans right.eq_decorateLabelled.symm) ⟨(a, a'), haa'⟩

/-- **Equality of decorations is labelled bisimilarity.** -/
theorem decorateLabelled_eq_iff_labelledBisimilar {a : α} {a' : α'} :
    decorateLabelled r ℓ a = decorateLabelled s ℓ' a' ↔ LabelledBisimilar r s ℓ ℓ' a a' :=
  ⟨labelledBisimilar_of_decorateLabelled_eq, decorateLabelled_eq_of_labelledBisimilar⟩

end Bisimilarity

/-! ## For streams the two readings agree -/

section Streams

variable {α α' β β' : Type u} {r : α → β → α → Prop} {s : α' → β' → α' → Prop}
  {ℓ : β → HSet.{u}} {ℓ' : β' → HSet.{u}}

/-- On deterministic graphs, labelled bisimilarity is equality of the label sequences read
through the readings of the labels. -/
theorem labelledBisimilar_iff_comp_labels (hr : Deterministic r) (hs : Deterministic s)
    {a : α} {a' : α'} :
    LabelledBisimilar r s ℓ ℓ' a a' ↔ ℓ ∘ hr.labels a = ℓ' ∘ hs.labels a' := by
  constructor
  · rintro ⟨R, hR, haa'⟩
    have next : ∀ {c c'}, R c c' →
        ℓ (hr.step c).1 = ℓ' (hs.step c').1 ∧ R (hr.step c).2 (hs.step c').2 := by
      intro c c' hcc'
      obtain ⟨b', d', hsd, hl, hd⟩ := (hR hcc').1 _ _ (hr.step_spec c)
      rw [hs.step_eq hsd]
      exact ⟨hl, hd⟩
    suffices ∀ n c c', R c c' → ℓ (hr.labels c n) = ℓ' (hs.labels c' n) from
      funext fun n => this n a a' haa'
    intro n
    induction n with
    | zero => exact fun c c' hcc' => (next hcc').1
    | succ n ih =>
      intro c c' hcc'
      rw [hr.labels_succ, hs.labels_succ]
      exact ih _ _ (next hcc').2
  · intro h
    refine ⟨fun c c' => ℓ ∘ hr.labels c = ℓ' ∘ hs.labels c', ?_, h⟩
    intro c c' hcc'
    have head : ℓ (hr.step c).1 = ℓ' (hs.step c').1 := congrFun hcc' 0
    have tail : ℓ ∘ hr.labels (hr.step c).2 = ℓ' ∘ hs.labels (hs.step c').2 :=
      funext fun n => by
        have hn := congrFun hcc' (n + 1)
        simp only [Function.comp_apply, hr.labels_succ, hs.labels_succ] at hn
        exact hn
    constructor
    · intro b d hrd
      rw [hr.step_eq hrd] at head tail
      exact ⟨(hs.step c').1, (hs.step c').2, hs.step_spec c', head, tail⟩
    · intro b' d' hsd
      rw [hs.step_eq hsd] at head tail
      exact ⟨(hr.step c).1, (hr.step c).2, hr.step_spec c, head, tail⟩

/-- **The two readings of a stream agree**: two nodes of deterministic graphs have the same
decoration exactly when their label sequences, read through the readings of the labels, are
equal. -/
theorem decorateLabelled_eq_iff_comp_labels (hr : Deterministic r) (hs : Deterministic s)
    {a : α} {a' : α'} :
    decorateLabelled r ℓ a = decorateLabelled s ℓ' a' ↔ ℓ ∘ hr.labels a = ℓ' ∘ hs.labels a' :=
  decorateLabelled_eq_iff_labelledBisimilar.trans (labelledBisimilar_iff_comp_labels hr hs)

/-- **The two readings of a stream agree**, for one injective reading of the labels: a stream's
hyperset determines and is determined by its sequence of labels. -/
theorem decorateLabelled_eq_iff_labels {s : α' → β → α' → Prop} (hr : Deterministic r)
    (hs : Deterministic s) (hℓ : Function.Injective ℓ) {a : α} {a' : α'} :
    decorateLabelled r ℓ a = decorateLabelled s ℓ a' ↔ hr.labels a = hs.labels a' :=
  (decorateLabelled_eq_iff_comp_labels hr hs).trans hℓ.comp_left.eq_iff

/-- On deterministic graphs, equal sets of words are equal label sequences. -/
theorem traces_eq_iff_labels {s : α' → β → α' → Prop} (hr : Deterministic r)
    (hs : Deterministic s) {a : α} {a' : α'} :
    {w | Trace r a w} = {w | Trace s a' w} ↔ hr.labels a = hs.labels a' := by
  constructor
  · intro h
    funext n
    have hw : (List.range (n + 1)).map (hr.labels a) ∈ {w | Trace s a' w} := by
      rw [← h]
      show Trace r a _
      rw [hr.trace_iff, List.length_map, List.length_range]
    have hw' := hs.trace_iff.mp hw
    rw [List.length_map, List.length_range] at hw'
    have hnth := congrArg (fun l : List β => l[n]?) hw'
    simpa using hnth
  · intro h
    ext w
    show Trace r a w ↔ Trace s a' w
    rw [hr.trace_iff, hs.trace_iff, h]

/-- On deterministic graphs, for one injective reading of the labels, equal sets of words are
equal decorations. -/
theorem decorateLabelled_eq_iff_traces_eq {s : α' → β → α' → Prop} (hr : Deterministic r)
    (hs : Deterministic s) (hℓ : Function.Injective ℓ) {a : α} {a' : α'} :
    decorateLabelled r ℓ a = decorateLabelled s ℓ a' ↔ {w | Trace r a w} = {w | Trace s a' w} :=
  (decorateLabelled_eq_iff_labels hr hs hℓ).trans (traces_eq_iff_labels hr hs).symm

/-! ## The function reading -/

/-- The position graph of a sequence: from `n` one step, labelled by the sequence at `n`, to
`n + 1`. -/
def positionRel (σ : ℕ → β) (n : ULift.{u} ℕ) (b : β) (m : ULift.{u} ℕ) : Prop :=
  b = σ n.down ∧ m.down = n.down + 1

theorem deterministic_positionRel (σ : ℕ → β) : Deterministic (positionRel σ) := fun n =>
  ⟨(σ n.down, ⟨n.down + 1⟩), ⟨rfl, rfl⟩, fun e he => by
    obtain ⟨b, ⟨m⟩⟩ := e
    obtain ⟨hb, hm⟩ := he
    simp only at hb hm
    rw [hb, hm]⟩

/-- The label sequence of the position graph at `k` is the sequence from `k` on. -/
theorem labels_positionRel (σ : ℕ → β) (k : ℕ) :
    (deterministic_positionRel σ).labels ⟨k⟩ = fun n => σ (k + n) :=
  ((deterministic_positionRel σ).eq_of_path (p := fun n => ⟨k + n⟩) (σ := fun n => σ (k + n))
    rfl fun _ => ⟨rfl, rfl⟩).2.symm

/-- The hyperset stream of a sequence: the decoration at `0` of its position graph. -/
noncomputable def streamOf (ℓ : β → HSet.{u}) (σ : ℕ → β) : HSet.{u} :=
  decorateLabelled (positionRel σ) ℓ ⟨0⟩

/-- **Every deterministic graph decorates a node as the stream of its label sequence.** -/
theorem decorateLabelled_eq_streamOf (hr : Deterministic r) (a : α) :
    decorateLabelled r ℓ a = streamOf ℓ (hr.labels a) := by
  refine (decorateLabelled_eq_iff_comp_labels hr (deterministic_positionRel _)).mpr ?_
  rw [labels_positionRel]
  funext n
  simp only [Function.comp_apply, Nat.zero_add]

/-- Two sequences give the same stream exactly when their readings agree. -/
theorem streamOf_eq_streamOf_iff {σ τ : ℕ → β} : streamOf ℓ σ = streamOf ℓ τ ↔ ℓ ∘ σ = ℓ ∘ τ := by
  rw [streamOf, streamOf, decorateLabelled_eq_iff_comp_labels (deterministic_positionRel σ)
    (deterministic_positionRel τ), labels_positionRel, labels_positionRel]
  simp only [Nat.zero_add]

/-- For an injective reading of the labels, distinct sequences give distinct streams. -/
theorem streamOf_injective (hℓ : Function.Injective ℓ) : Function.Injective (streamOf ℓ) :=
  fun _ _ h => hℓ.comp_left (streamOf_eq_streamOf_iff.mp h)

/-- The stream of a sequence is the pair of its first label with the stream of the rest. -/
theorem streamOf_cons (σ : ℕ → β) :
    streamOf ℓ σ = {kpair (ℓ (σ 0)) (streamOf ℓ fun n => σ (n + 1))} := by
  have rest : decorateLabelled (positionRel σ) ℓ ⟨1⟩ = streamOf ℓ fun n => σ (n + 1) := by
    rw [decorateLabelled_eq_streamOf (deterministic_positionRel σ), labels_positionRel]
    congr 1
    funext n
    rw [Nat.add_comm]
  ext y
  show y ∈ decorateLabelled (positionRel σ) ℓ ⟨0⟩ ↔ _
  rw [mem_decorateLabelled, mem_singleton]
  constructor
  · rintro ⟨b, ⟨m⟩, ⟨hb, hm⟩, rfl⟩
    simp only at hb hm
    subst hb hm
    rw [← rest]
  · rintro rfl
    exact ⟨σ 0, ⟨1⟩, ⟨rfl, rfl⟩, by rw [← rest]⟩

/-- A hyperset stream over `β`: the decoration of a node of a deterministic graph labelled in
`β`. -/
def IsStream (ℓ : β → HSet.{u}) (x : HSet.{u}) : Prop :=
  ∃ (γ : Type u) (t : γ → β → γ → Prop), Deterministic t ∧ ∃ c, decorateLabelled t ℓ c = x

/-- The hyperset streams are the streams of sequences. -/
theorem isStream_iff {x : HSet.{u}} : IsStream ℓ x ↔ ∃ σ, streamOf ℓ σ = x := by
  constructor
  · rintro ⟨γ, t, ht, c, rfl⟩
    exact ⟨ht.labels c, (decorateLabelled_eq_streamOf ht c).symm⟩
  · rintro ⟨σ, rfl⟩
    exact ⟨ULift.{u} ℕ, positionRel σ, deterministic_positionRel σ, ⟨0⟩, rfl⟩

/-- **The hyperset streams over `β` are in bijection with the sequences `ℕ → β`**, for an
injective reading of the labels. -/
noncomputable def streamEquiv (hℓ : Function.Injective ℓ) : (ℕ → β) ≃ {x // IsStream ℓ x} :=
  Equiv.ofBijective (fun σ => ⟨streamOf ℓ σ, isStream_iff.mpr ⟨σ, rfl⟩⟩)
    ⟨fun _ _ h => streamOf_injective hℓ (congrArg Subtype.val h),
      fun x => by
        obtain ⟨σ, hσ⟩ := isStream_iff.mp x.2
        exact ⟨σ, Subtype.ext hσ⟩⟩

theorem streamEquiv_apply (hℓ : Function.Injective ℓ) (σ : ℕ → β) :
    (streamEquiv hℓ σ : HSet.{u}) = streamOf ℓ σ :=
  rfl

/-- The inverse of `streamEquiv` reads the label sequence off a deterministic graph. -/
theorem streamEquiv_symm_decorateLabelled (hℓ : Function.Injective ℓ) (hr : Deterministic r)
    (a : α) :
    (streamEquiv hℓ).symm ⟨decorateLabelled r ℓ a, ⟨α, r, hr, a, rfl⟩⟩ = hr.labels a :=
  (Equiv.symm_apply_eq _).mpr (Subtype.ext (decorateLabelled_eq_streamOf hr a))

end Streams

/-! ## Where the readings part -/

section Branching

variable {α α' β : Type u} {r : α → β → α → Prop} {s : α' → β → α' → Prop} {ℓ : β → HSet.{u}}

/-- A word of one node is a word of a labelled-bisimilar node, for an injective reading. -/
theorem trace_of_labelledBisimilar (hℓ : Function.Injective ℓ) {a : α} {a' : α'}
    (h : LabelledBisimilar r s ℓ ℓ a a') {w : List β} (hw : Trace r a w) : Trace s a' w := by
  obtain ⟨R, hR, haa'⟩ := h
  induction hw generalizing a' with
  | nil => exact Trace.nil a'
  | cons hrc _ ih =>
    obtain ⟨b', c', hsc, hl, hc⟩ := (hR haa').1 _ _ hrc
    rw [hℓ hl]
    exact Trace.cons hsc (ih (a' := c') hc)

/-- For an injective reading, equal decorations have equal sets of words. -/
theorem traces_eq_of_decorateLabelled_eq (hℓ : Function.Injective ℓ) {a : α} {a' : α'}
    (h : decorateLabelled r ℓ a = decorateLabelled s ℓ a') :
    {w | Trace r a w} = {w | Trace s a' w} :=
  Set.ext fun _ =>
    ⟨trace_of_labelledBisimilar hℓ (decorateLabelled_eq_iff_labelledBisimilar.mp h),
      trace_of_labelledBisimilar hℓ (decorateLabelled_eq_iff_labelledBisimilar.mp h.symm)⟩

end Branching

/-- The nodes of `x·(y + z)`: one step, then the choice, then the end. -/
inductive LateNode : Type u
  | start
  | choice
  | stop

/-- The nodes of `x·y + x·z`: the choice with the first step, then a second step, then the
end. -/
inductive EarlyNode : Type u
  | start
  | left
  | right
  | stop

section Branching

variable {β : Type u}

/-- `x·(y + z)`: a step labelled `x`, then a step labelled `y` or `z` to the final node. -/
def lateRel (x y z : β) : LateNode.{u} → β → LateNode.{u} → Prop
  | .start, b, .choice => b = x
  | .choice, b, .stop => b = y ∨ b = z
  | _, _, _ => False

/-- `x·y + x·z`: a step labelled `x` to one of two nodes, then a step labelled `y` from the
first and `z` from the second to the final node. -/
def earlyRel (x y z : β) : EarlyNode.{u} → β → EarlyNode.{u} → Prop
  | .start, b, .left => b = x
  | .start, b, .right => b = x
  | .left, b, .stop => b = y
  | .right, b, .stop => b = z
  | _, _, _ => False

variable {x y z b : β}

theorem lateRel_start {c : LateNode.{u}} : lateRel x y z .start b c ↔ b = x ∧ c = .choice := by
  cases c <;> simp [lateRel]

theorem lateRel_choice {c : LateNode.{u}} :
    lateRel x y z .choice b c ↔ (b = y ∨ b = z) ∧ c = .stop := by
  cases c <;> simp [lateRel]

theorem not_lateRel_stop {c : LateNode.{u}} : ¬ lateRel x y z .stop b c := by
  cases c <;> simp [lateRel]

theorem earlyRel_start {c : EarlyNode.{u}} :
    earlyRel x y z .start b c ↔ b = x ∧ (c = .left ∨ c = .right) := by
  cases c <;> simp [earlyRel]

theorem earlyRel_left {c : EarlyNode.{u}} : earlyRel x y z .left b c ↔ b = y ∧ c = .stop := by
  cases c <;> simp [earlyRel]

theorem earlyRel_right {c : EarlyNode.{u}} : earlyRel x y z .right b c ↔ b = z ∧ c = .stop := by
  cases c <;> simp [earlyRel]

theorem not_earlyRel_stop {c : EarlyNode.{u}} : ¬ earlyRel x y z .stop b c := by
  cases c <;> simp [earlyRel]

/-- The words of `x·(y + z)` after its first step. -/
theorem trace_late_choice {w : List β} :
    Trace (lateRel x y z) .choice w ↔ w = [] ∨ w = [y] ∨ w = [z] := by
  cases w with
  | nil => exact ⟨fun _ => Or.inl rfl, fun _ => Trace.nil _⟩
  | cons b w =>
    rw [Trace.cons_iff]
    constructor
    · rintro ⟨c, hc, hw⟩
      obtain ⟨hb, rfl⟩ := lateRel_choice.mp hc
      rw [(Trace.iff_nil_of_forall_not fun _ _ => not_lateRel_stop).mp hw]
      rcases hb with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    · rintro (h | h | h)
      · cases h
      · obtain ⟨rfl, rfl⟩ := List.cons.inj h
        exact ⟨.stop, lateRel_choice.mpr ⟨Or.inl rfl, rfl⟩, Trace.nil _⟩
      · obtain ⟨rfl, rfl⟩ := List.cons.inj h
        exact ⟨.stop, lateRel_choice.mpr ⟨Or.inr rfl, rfl⟩, Trace.nil _⟩

/-- The words of `x·y + x·z` after its first step to the left. -/
theorem trace_early_left {w : List β} : Trace (earlyRel x y z) .left w ↔ w = [] ∨ w = [y] := by
  cases w with
  | nil => exact ⟨fun _ => Or.inl rfl, fun _ => Trace.nil _⟩
  | cons b w =>
    rw [Trace.cons_iff]
    constructor
    · rintro ⟨c, hc, hw⟩
      obtain ⟨rfl, rfl⟩ := earlyRel_left.mp hc
      rw [(Trace.iff_nil_of_forall_not fun _ _ => not_earlyRel_stop).mp hw]
      exact Or.inr rfl
    · rintro (h | h)
      · cases h
      · obtain ⟨rfl, rfl⟩ := List.cons.inj h
        exact ⟨.stop, earlyRel_left.mpr ⟨rfl, rfl⟩, Trace.nil _⟩

/-- The words of `x·y + x·z` after its first step to the right. -/
theorem trace_early_right {w : List β} : Trace (earlyRel x y z) .right w ↔ w = [] ∨ w = [z] := by
  cases w with
  | nil => exact ⟨fun _ => Or.inl rfl, fun _ => Trace.nil _⟩
  | cons b w =>
    rw [Trace.cons_iff]
    constructor
    · rintro ⟨c, hc, hw⟩
      obtain ⟨rfl, rfl⟩ := earlyRel_right.mp hc
      rw [(Trace.iff_nil_of_forall_not fun _ _ => not_earlyRel_stop).mp hw]
      exact Or.inr rfl
    · rintro (h | h)
      · cases h
      · obtain ⟨rfl, rfl⟩ := List.cons.inj h
        exact ⟨.stop, earlyRel_right.mpr ⟨rfl, rfl⟩, Trace.nil _⟩

/-- The words of `x·(y + z)`. -/
theorem late_traces :
    {w | Trace (lateRel x y z) .start w} = {[], [x], [x, y], [x, z]} := by
  ext w
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  cases w with
  | nil => exact ⟨fun _ => Or.inl rfl, fun _ => Trace.nil _⟩
  | cons b w =>
    rw [Trace.cons_iff]
    constructor
    · rintro ⟨c, hc, hw⟩
      obtain ⟨rfl, rfl⟩ := lateRel_start.mp hc
      rcases trace_late_choice.mp hw with rfl | rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr rfl))
    · rintro (h | h | h | h)
      · cases h
      · obtain ⟨rfl, rfl⟩ := List.cons.inj h
        exact ⟨.choice, lateRel_start.mpr ⟨rfl, rfl⟩, Trace.nil _⟩
      · obtain ⟨rfl, rfl⟩ := List.cons.inj h
        exact ⟨.choice, lateRel_start.mpr ⟨rfl, rfl⟩, trace_late_choice.mpr (Or.inr (Or.inl rfl))⟩
      · obtain ⟨rfl, rfl⟩ := List.cons.inj h
        exact ⟨.choice, lateRel_start.mpr ⟨rfl, rfl⟩, trace_late_choice.mpr (Or.inr (Or.inr rfl))⟩

/-- The words of `x·y + x·z`. -/
theorem early_traces :
    {w | Trace (earlyRel x y z) .start w} = {[], [x], [x, y], [x, z]} := by
  ext w
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  cases w with
  | nil => exact ⟨fun _ => Or.inl rfl, fun _ => Trace.nil _⟩
  | cons b w =>
    rw [Trace.cons_iff]
    constructor
    · rintro ⟨c, hc, hw⟩
      obtain ⟨rfl, rfl | rfl⟩ := earlyRel_start.mp hc
      · rcases trace_early_left.mp hw with rfl | rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inl rfl))
      · rcases trace_early_right.mp hw with rfl | rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inr rfl))
    · rintro (h | h | h | h)
      · cases h
      · obtain ⟨rfl, rfl⟩ := List.cons.inj h
        exact ⟨.left, earlyRel_start.mpr ⟨rfl, Or.inl rfl⟩, Trace.nil _⟩
      · obtain ⟨rfl, rfl⟩ := List.cons.inj h
        exact ⟨.left, earlyRel_start.mpr ⟨rfl, Or.inl rfl⟩, trace_early_left.mpr (Or.inr rfl)⟩
      · obtain ⟨rfl, rfl⟩ := List.cons.inj h
        exact ⟨.right, earlyRel_start.mpr ⟨rfl, Or.inr rfl⟩, trace_early_right.mpr (Or.inr rfl)⟩

/-- `x·(y + z)` and `x·y + x·z` have the same words. -/
theorem late_early_traces_eq :
    {w | Trace (lateRel x y z) .start w} = {w | Trace (earlyRel x y z) .start w} := by
  rw [late_traces, early_traces]

/-- `x·(y + z)` and `x·y + x·z` are two hypersets when `y` and `z` are read differently: after
the step `x` to the left, `x·y + x·z` can no longer take `z`. -/
theorem late_early_decorateLabelled_ne {ℓ : β → HSet.{u}} (h : ℓ y ≠ ℓ z) :
    decorateLabelled (lateRel x y z) ℓ .start ≠ decorateLabelled (earlyRel x y z) ℓ .start := by
  intro he
  obtain ⟨R, hR, h0⟩ := decorateLabelled_eq_iff_labelledBisimilar.mp he
  obtain ⟨_, c, hc, _, hcl⟩ := (hR h0).2 x EarlyNode.left (earlyRel_start.mpr ⟨rfl, Or.inl rfl⟩)
  obtain ⟨_, rfl⟩ := lateRel_start.mp hc
  obtain ⟨b', _, hb', hl, _⟩ := (hR hcl).1 z LateNode.stop (lateRel_choice.mpr ⟨Or.inr rfl, rfl⟩)
  obtain ⟨rfl, _⟩ := earlyRel_left.mp hb'
  exact h hl.symm

/-- **Where the readings part**: for an injective reading and distinct `y` and `z`, `x·(y + z)`
and `x·y + x·z` have the same words and different hypersets. -/
theorem late_early_part {ℓ : β → HSet.{u}} (hℓ : Function.Injective ℓ) (h : y ≠ z) :
    {w | Trace (lateRel x y z) .start w} = {w | Trace (earlyRel x y z) .start w} ∧
      decorateLabelled (lateRel x y z) ℓ .start ≠ decorateLabelled (earlyRel x y z) ℓ .start :=
  ⟨late_early_traces_eq, late_early_decorateLabelled_ne (hℓ.ne h)⟩

end Branching

/-! ## The length of a cycle is forgotten -/

/-- The one-node loop is deterministic. -/
theorem deterministic_repeatRel : Deterministic repeatRel.{u} := fun _ =>
  ⟨(PUnit.unit, PUnit.unit), trivial, fun _ _ => rfl⟩

/-- The step of the alternating graph: the node's own label, to the other node. -/
theorem alternateRel_self (a : ULift.{u} Bool) : alternateRel a a ⟨!a.down⟩ := by
  obtain ⟨d⟩ := a
  cases d
  · exact Or.inr ⟨rfl, rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl, rfl⟩

/-- The two-node cycle is deterministic. -/
theorem deterministic_alternateRel : Deterministic alternateRel.{u} := fun a =>
  ⟨(a, ⟨!a.down⟩), alternateRel_self a, fun e he => by
    obtain ⟨⟨l⟩, ⟨c⟩⟩ := e
    obtain ⟨d⟩ := a
    rcases he with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> simp only at h1 h2 h3 <;> subst h1 h2 h3 <;> rfl⟩

theorem alternate_step (a : ULift.{u} Bool) : deterministic_alternateRel.step a = (a, ⟨!a.down⟩) :=
  deterministic_alternateRel.step_eq (alternateRel_self a)

/-- The two-node cycle with labels `b` and `c` is the loop that repeats `d` exactly when both
labels are `d`. -/
theorem alternating_eq_repeatStream_iff (b c d : HSet.{u}) :
    alternating b c ⟨true⟩ = repeatStream d ↔ b = d ∧ c = d := by
  unfold alternating repeatStream
  rw [decorateLabelled_eq_iff_labelledBisimilar]
  constructor
  · rintro ⟨R, hR, h0⟩
    obtain ⟨_, _, _, hb, h1⟩ := (hR h0).1 ⟨true⟩ ⟨false⟩ (alternateRel_self ⟨true⟩)
    obtain ⟨_, _, _, hc, _⟩ := (hR h1).1 ⟨false⟩ ⟨true⟩ (alternateRel_self ⟨false⟩)
    exact ⟨hb, hc⟩
  · rintro ⟨rfl, rfl⟩
    refine ⟨fun _ _ => True, fun a _ _ => ⟨fun l _ _ => ⟨PUnit.unit, PUnit.unit, trivial, ?_, trivial⟩,
      fun _ _ _ => ⟨a, ⟨!a.down⟩, alternateRel_self a, ?_, trivial⟩⟩, trivial⟩
    · simp only [ite_self]
    · simp only [ite_self]

/-- **The length of a cycle is forgotten**: with one label, the two-node cycle is the one-node
loop, while the path of the cycle comes back to its start after two steps and never after one,
and the path of the loop after one. -/
theorem alternating_cycle_length_forgotten (b : HSet.{u}) :
    alternating b b ⟨true⟩ = repeatStream b ∧
      (∀ a, deterministic_alternateRel.node a 1 ≠ a ∧ deterministic_alternateRel.node a 2 = a) ∧
      ∀ a, deterministic_repeatRel.node a 1 = a := by
  refine ⟨(alternating_eq_repeatStream_iff b b b).mpr ⟨rfl, rfl⟩, fun a => ⟨?_, ?_⟩, fun _ => rfl⟩
  · show (deterministic_alternateRel.step a).2 ≠ a
    rw [alternate_step]
    obtain ⟨d⟩ := a
    cases d <;> simp
  · show (deterministic_alternateRel.step (deterministic_alternateRel.step a).2).2 = a
    rw [alternate_step, alternate_step]
    obtain ⟨d⟩ := a
    cases d <;> rfl

/-! ## The stream `from n` -/

/-- A deterministic graph in which every node has an edge decorates nodes that are not
well-founded: below the decoration of a node lies the decoration of its child. -/
theorem not_wf_decorateLabelled_of_serial {α β : Type u} {r : α → β → α → Prop}
    {ℓ : β → HSet.{u}} (serial : ∀ a, ∃ b c, r a b c) (a : α) :
    ¬ (decorateLabelled r ℓ a).WF := by
  intro hwf
  have key : ∀ x : HSet.{u}, Acc (TransGen (· ∈ ·)) x → ∀ a, x ≠ decorateLabelled r ℓ a := by
    intro x hx
    induction hx with
    | intro x _ ih =>
      rintro a rfl
      obtain ⟨b, c, hrc⟩ := serial a
      refine ih _ ?_ c rfl
      exact TransGen.head (mem_pair.mpr (Or.inr rfl))
        (TransGen.head (mem_kpair.mpr (Or.inr rfl))
          (TransGen.single (mem_decorateLabelled.mpr ⟨b, c, hrc, rfl⟩)))
  exact key _ (Acc.transGen hwf) a rfl

/-- The rank of the finite ordinal `k` is `k`. -/
theorem rank_mk_ofNat : ∀ k : ℕ, (ZFSet.mk (PSet.ofNat.{u} k)).rank = k
  | 0 => ZFSet.rank_empty
  | k + 1 => by
    show (insert (ZFSet.mk (PSet.ofNat k)) (ZFSet.mk (PSet.ofNat k))).rank = ((k + 1 : ℕ) : Ordinal)
    rw [ZFSet.rank_insert, rank_mk_ofNat k, max_eq_left (Order.le_succ _), Order.succ_eq_add_one]
    push_cast
    rfl

/-- The finite ordinal `k`, read as a hyperset. -/
def numeralLabel (k : ℕ) : HSet.{u} :=
  ofZFSet (ZFSet.mk (PSet.ofNat.{u} k))

theorem numeralLabel_injective : Function.Injective numeralLabel.{u} := fun j k h => by
  have hrank := congrArg ZFSet.rank (ofZFSet_injective h)
  rw [rank_mk_ofNat, rank_mk_ofNat] at hrank
  exact_mod_cast hrank

/-- A number label, read as the hyperset of its finite ordinal. -/
def readNumber (b : ULift.{u} ℕ) : HSet.{u} :=
  numeralLabel b.down

/-- The program `from`: `from m` steps, with the label `m`, to `from (m + 1)`. -/
def fromRel (m b m' : ULift.{u} ℕ) : Prop :=
  b = m ∧ m'.down = m.down + 1

theorem deterministic_fromRel : Deterministic fromRel.{u} := fun m =>
  ⟨(m, ⟨m.down + 1⟩), ⟨rfl, rfl⟩, fun e he => by
    obtain ⟨b, ⟨m'⟩⟩ := e
    obtain ⟨hb, hm⟩ := he
    simp only at hb hm
    rw [hb, hm]⟩

/-- The stream `from n`: the decoration of the program `from` at `n`, with the labels read as
finite ordinals. -/
noncomputable def fromStream (n : ℕ) : HSet.{u} :=
  decorateLabelled fromRel readNumber ⟨n⟩

/-- The label sequence of `from n` is `k ↦ n + k`. -/
theorem labels_fromRel (n : ℕ) : deterministic_fromRel.labels ⟨n⟩ = fun k => ⟨n + k⟩ :=
  (deterministic_fromRel.eq_of_path (p := fun k => ⟨n + k⟩) (σ := fun k => ⟨n + k⟩) rfl
    fun _ => ⟨rfl, rfl⟩).2.symm

/-- `from n = cons n (from (n + 1))`. -/
theorem fromStream_spec (n : ℕ) :
    fromStream.{u} n = {kpair (numeralLabel n) (fromStream (n + 1))} := by
  ext y
  rw [fromStream, mem_decorateLabelled, mem_singleton]
  constructor
  · rintro ⟨b, ⟨m⟩, ⟨rfl, hm⟩, rfl⟩
    simp only at hm
    subst hm
    rfl
  · rintro rfl
    exact ⟨⟨n⟩, ⟨n + 1⟩, ⟨rfl, rfl⟩, rfl⟩

/-- `fromStream` is the only family that satisfies the program's equation. -/
theorem fromStream_unique {d : ℕ → HSet.{u}}
    (h : ∀ n, d n = {kpair (numeralLabel n) (d (n + 1))}) : d = fromStream := by
  have hd : IsLabelledDecoration fromRel readNumber (fun m : ULift.{u} ℕ => d m.down) := by
    intro m y
    show y ∈ d m.down ↔ _
    rw [h, mem_singleton]
    constructor
    · rintro rfl
      exact ⟨m, ⟨m.down + 1⟩, ⟨rfl, rfl⟩, rfl⟩
    · rintro ⟨b, ⟨m'⟩, ⟨rfl, hm⟩, rfl⟩
      simp only at hm
      subst hm
      rfl
  funext n
  exact congrFun hd.eq_decorateLabelled ⟨n⟩

/-- **`from n` on both readings**: its hyperset is the decoration at `0` of the position graph of
its label sequence `k ↦ n + k`. -/
theorem fromStream_eq_streamOf (n : ℕ) :
    fromStream.{u} n = streamOf readNumber fun k => ⟨n + k⟩ := by
  rw [fromStream, decorateLabelled_eq_streamOf deterministic_fromRel, labels_fromRel]

/-- `from n` is not well-founded. -/
theorem fromStream_not_wf (n : ℕ) : ¬ (fromStream.{u} n).WF :=
  not_wf_decorateLabelled_of_serial (r := fromRel) (ℓ := readNumber)
    (fun m => ⟨m, ⟨m.down + 1⟩, rfl, rfl⟩) _

/-- `from n` repeats no label. -/
theorem fromStream_ne_repeatStream (n : ℕ) (x : HSet.{u}) : fromStream n ≠ repeatStream x := by
  intro h
  have hl := (decorateLabelled_eq_iff_comp_labels deterministic_fromRel deterministic_repeatRel).mp h
  rw [labels_fromRel] at hl
  have h0 := congrFun hl 0
  have h1 := congrFun hl 1
  simp only [Function.comp_apply, readNumber] at h0 h1
  exact absurd (numeralLabel_injective (h0.trans h1.symm)) (by omega)

/-- Distinct starting numbers give distinct streams. -/
theorem fromStream_injective : Function.Injective fromStream.{u} := fun n m h => by
  have hl := (decorateLabelled_eq_iff_comp_labels deterministic_fromRel deterministic_fromRel).mp h
  rw [labels_fromRel, labels_fromRel] at hl
  have h0 := congrFun hl 0
  simp only [Function.comp_apply, readNumber, Nat.add_zero] at h0
  exact numeralLabel_injective h0

end HSet

end Mettapedia.TypeTheory.MaterialSets.Hypersets
