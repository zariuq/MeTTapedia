import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsPaths
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunUnfolding

/-!
# Events of the unfolding: firings with their causes

A run of the candidate step is a word of firings, and the arrows of the contextual trace
category from a configuration are its runs up to round equivalence
(`AnnotatedRuns.trace_eq_iff_roundEquiv`). This module gives those arrows an event-structure
reading, in the manner of Winskel: a configuration is a set of events, and an event is a firing
together with its causes.

## Three relations and two conflicts

The relations between two firings stay apart, as in `GuardFreeProcessOrders` (`NoCause`,
`NoAsym`) and in `AnnotatedRunUnfolding` (`Flow`, `ReadBeforeTake`, `InhibitsAt`).

* **Flow** (`Flow`): one makes an occurrence the other takes or reads. It is causality.
* **Read before take** (`ReadBeforeTake`): one reads an occurrence the other takes. Both may
  happen only in that order: the asymmetric conflict of contextual nets (Baldan, Corradini and
  Montanari 2001).
* **Inhibition** (`Inhibits`): one takes or makes an occurrence inside the space observed by a
  predicate query of the other. Both orders may happen, and they are different histories: the
  inhibitor arc of Baldan, Busi, Corradini and Pinna (2004). A configuration records which of the
  two came first, as their choice relation does.
* **Conflicts:** two firings taking one occurrence (`TakeConflict`), or making one identity
  (`MadeConflict`). Joint consistency of the equations is a further, non-binary consistency.

## Configurations

`IsConfiguration A label C X` is stated without runs. The firings of `X` must be

* in the fragment (no guards, query spaces independent of the solution), well formed, with
  made identities fresh at `C` and pairwise apart, and no occurrence taken twice;
* causally closed: every occurrence a firing takes or reads is present at `C` or made by a member;
* oriented: every inhibition pair is ordered by `X.before`, and `X.before` orders nothing else;
* acyclic: flow, read-before-take and the recorded inhibition order have no cycle;
* admitted where their causes leave them: each predicate query sees exactly what it recorded,
  among the occurrences present after the writers ordered before it (`presentAfter`,
  `writersBefore`);
* jointly consistent.

The **causes** of a firing are its predecessors under the three relations (`causes`), and its
**event** is the pair of the firing and its causes (`events`). A configuration is determined by
its events (`config_eq_of_events_eq`).

## The correspondence

For runs of the fragment from a configuration `C`, whose firings are distinct, make fresh
identities, and make no identity twice (`Fragment`):

* round-equivalent runs have one configuration (`configOf_eq_of_roundEquiv`);
* runs with one configuration are one static trace, hence round equivalent
  (`staticTraceEquiv_of_configOf_eq`, `roundEquiv_of_configOf_eq`): the projection lemma, since
  every dependent pair of firings is ordered alike in both. So in the fragment the contextual and
  the static trace equivalences coincide (`roundEquiv_iff_staticTraceEquiv`);
* every run gives a configuration (`configOf_isConfiguration`), and every configuration is the
  configuration of a run (`exists_run`), by firing a minimal event first.

Hence the traces of the fragment from `C` and its configurations are in bijection
(`configuration_bijective`), two runs are one trace exactly when their events agree
(`roundEquiv_iff_events_eq`), and at the level of paths, two arrows of the contextual trace
category from the class of `C` are equal exactly when their configurations are
(`trace_eq_iff_configOf_eq`).

Without predicate queries there are no inhibition pairs, and the configuration is the set of
firings (`queryFree_roundEquiv_iff_perm`): the occurrence identities carry the causes. With them
the same set can be two configurations (`AnnotatedRunEventsControls`).

A run of the fragment ends, up to solutions, where its configuration does (`endOf`,
`follow_sameUpTo_endOf`): the end of a history is a function of its events.

Guards, query spaces that depend on the solution, and repeated firings are outside the
fragment. For guards this is necessary, not a convenience: an equation guard admitted after
either of two tells gives one trace in which the tell before it differs between two
linearizations, so no set of causes of the guarded firing is a property of its trace
(`AnnotatedRunEventsControls.Guards.guard_or_causality`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunEvents

open AnnotatedRuns
open AnnotatedRunUnfolding (Flow ReadBeforeTake InhibitsAt)
open MeTTaCalculus.OccurrenceCommits (regionOf mem_regionOf fire mem_fire)
open Mettapedia.GSLT.Causality.OccurrenceHistory (OccurrencePath)
open Mettapedia.GSLT.Causality.EventConcurrency (Trace)

/-! ## Precedence in a word -/

section Precedence

variable {α : Type*}

/-- `x` occurs before `y` in the word. -/
def Precedes : List α → α → α → Prop
  | [], _, _ => False
  | f :: w, x, y => (x = f ∧ y ∈ w) ∨ Precedes w x y

theorem precedes_nil (x y : α) : ¬ Precedes ([] : List α) x y := by
  simp [Precedes]

theorem precedes_cons {f x y : α} {w : List α} :
    Precedes (f :: w) x y ↔ (x = f ∧ y ∈ w) ∨ Precedes w x y := by
  simp only [Precedes]

theorem Precedes.mem_left : ∀ {w : List α} {x y : α}, Precedes w x y → x ∈ w
  | [], x, y, h => absurd h (precedes_nil x y)
  | _ :: _, _, _, h => by
      rcases precedes_cons.mp h with ⟨rfl, _⟩ | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ h.mem_left

theorem Precedes.mem_right : ∀ {w : List α} {x y : α}, Precedes w x y → y ∈ w
  | [], x, y, h => absurd h (precedes_nil x y)
  | _ :: _, _, _, h => by
      rcases precedes_cons.mp h with ⟨_, inW⟩ | h
      · exact List.mem_cons_of_mem _ inW
      · exact List.mem_cons_of_mem _ h.mem_right

theorem precedes_irrefl : ∀ {w : List α}, w.Nodup → ∀ x, ¬ Precedes w x x
  | [], _, x, h => precedes_nil x x h
  | _ :: _, nodup, x, h => by
      rcases precedes_cons.mp h with ⟨rfl, inW⟩ | h
      · exact (List.nodup_cons.mp nodup).1 inW
      · exact precedes_irrefl (List.nodup_cons.mp nodup).2 x h

theorem precedes_asymm : ∀ {w : List α}, w.Nodup → ∀ {x y : α}, Precedes w x y → ¬ Precedes w y x
  | [], _, x, y, h, _ => precedes_nil x y h
  | _ :: _, nodup, _, _, h, h' => by
      have fresh := (List.nodup_cons.mp nodup).1
      have rest := (List.nodup_cons.mp nodup).2
      rcases precedes_cons.mp h with ⟨rfl, yw⟩ | hw
      · rcases precedes_cons.mp h' with ⟨rfl, _⟩ | hw'
        · exact fresh yw
        · exact fresh hw'.mem_right
      · rcases precedes_cons.mp h' with ⟨rfl, _⟩ | hw'
        · exact fresh hw.mem_right
        · exact precedes_asymm rest hw hw'

theorem precedes_trans : ∀ {w : List α}, w.Nodup → ∀ {x y z : α},
    Precedes w x y → Precedes w y z → Precedes w x z
  | [], _, x, y, _, h, _ => absurd h (precedes_nil x y)
  | _ :: _, nodup, _, _, _, h, h' => by
      have fresh := (List.nodup_cons.mp nodup).1
      have rest := (List.nodup_cons.mp nodup).2
      rcases precedes_cons.mp h with ⟨rfl, yw⟩ | hw
      · rcases precedes_cons.mp h' with ⟨rfl, _⟩ | hw'
        · exact absurd yw fresh
        · exact precedes_cons.mpr (Or.inl ⟨rfl, hw'.mem_right⟩)
      · rcases precedes_cons.mp h' with ⟨rfl, _⟩ | hw'
        · exact absurd hw.mem_right fresh
        · exact precedes_cons.mpr (Or.inr (precedes_trans rest hw hw'))

theorem precedes_total : ∀ {w : List α} {x y : α}, x ∈ w → y ∈ w → x ≠ y →
    Precedes w x y ∨ Precedes w y x
  | [], _, _, hx, _, _ => by simp at hx
  | _ :: _, _, _, hx, hy, ne => by
      rcases List.mem_cons.mp hx with rfl | hxw
      · rcases List.mem_cons.mp hy with rfl | hyw
        · exact absurd rfl ne
        · exact Or.inl (precedes_cons.mpr (Or.inl ⟨rfl, hyw⟩))
      · rcases List.mem_cons.mp hy with rfl | hyw
        · exact Or.inr (precedes_cons.mpr (Or.inl ⟨rfl, hxw⟩))
        · rcases precedes_total hxw hyw ne with h | h
          · exact Or.inl (precedes_cons.mpr (Or.inr h))
          · exact Or.inr (precedes_cons.mpr (Or.inr h))

theorem precedes_cons_of_ne {f x y : α} {w : List α} (ne : x ≠ f) :
    Precedes (f :: w) x y ↔ Precedes w x y := by
  rw [precedes_cons]
  exact ⟨fun h => h.resolve_left fun h' => ne h'.1, Or.inr⟩

theorem not_precedes_head {f g : α} {w : List α} (nodup : (f :: w).Nodup) :
    ¬ Precedes (f :: w) g f := by
  intro h
  rcases precedes_cons.mp h with ⟨_, inW⟩ | h
  · exact (List.nodup_cons.mp nodup).1 inW
  · exact (List.nodup_cons.mp nodup).1 h.mem_right

theorem precedes_append_cons_of_mem {f g : α} : ∀ {p : List α} (q : List α), g ∈ p →
    Precedes (p ++ f :: q) g f
  | [], _, h => by simp at h
  | _ :: p, q, h => by
      rw [List.cons_append, precedes_cons]
      rcases List.mem_cons.mp h with rfl | h
      · exact Or.inl ⟨rfl, by simp⟩
      · exact Or.inr (precedes_append_cons_of_mem q h)

theorem precedes_append_cons_iff {f x y : α} (hx : x ≠ f) (hy : y ≠ f) :
    ∀ (p q : List α), Precedes (p ++ f :: q) x y ↔ Precedes (p ++ q) x y
  | [], q => by
      simp only [List.nil_append]
      exact precedes_cons_of_ne hx
  | a :: p, q => by
      simp only [List.cons_append, precedes_cons]
      have mem : y ∈ p ++ f :: q ↔ y ∈ p ++ q := by simp [hy]
      rw [mem, precedes_append_cons_iff hx hy p q]

/-- Swapping two adjacent entries changes the order of no other pair. -/
theorem precedes_swap_iff {f g x y : α} (fg : ¬ (x = f ∧ y = g)) (gf : ¬ (x = g ∧ y = f)) :
    ∀ (u v : List α), Precedes (u ++ f :: g :: v) x y ↔ Precedes (u ++ g :: f :: v) x y
  | [], v => by
      simp only [List.nil_append, precedes_cons, List.mem_cons]
      constructor
      · rintro (⟨rfl, rfl | yv⟩ | ⟨rfl, yv⟩ | rest)
        · exact absurd ⟨rfl, rfl⟩ fg
        · exact Or.inr (Or.inl ⟨rfl, yv⟩)
        · exact Or.inl ⟨rfl, Or.inr yv⟩
        · exact Or.inr (Or.inr rest)
      · rintro (⟨rfl, rfl | yv⟩ | ⟨rfl, yv⟩ | rest)
        · exact absurd ⟨rfl, rfl⟩ gf
        · exact Or.inr (Or.inl ⟨rfl, yv⟩)
        · exact Or.inl ⟨rfl, Or.inr yv⟩
        · exact Or.inr (Or.inr rest)
  | a :: u, v => by
      simp only [List.cons_append, precedes_cons]
      have mem : y ∈ u ++ f :: g :: v ↔ y ∈ u ++ g :: f :: v := by
        simp only [List.mem_append, List.mem_cons]
        tauto
      rw [mem, precedes_swap_iff fg gf u v]

/-- **The projection lemma.** Two orders of distinct letters that agree on every pair of
dependent letters are trace equivalent. -/
theorem traceEquiv_of_ordered {I : α → α → Prop} (symm : ∀ a b, I a b → I b a) :
    ∀ (w w' : List α), w.Nodup → w.Perm w' →
      (∀ x ∈ w, ∀ y ∈ w, x ≠ y → ¬ I x y → (Precedes w x y ↔ Precedes w' x y)) →
      Mettapedia.GSLT.Distinction.CausalGluing.TraceEquiv I w w'
  | [], w', _, perm, _ => by
      rw [List.nil_perm.mp perm]
      exact .refl _
  | f :: w, w', nodup, perm, ordered => by
      obtain ⟨p, q, rfl⟩ := List.append_of_mem (perm.subset List.mem_cons_self)
      have nodup' : (p ++ f :: q).Nodup := perm.nodup_iff.mp nodup
      have fNotP : f ∉ p := fun inP =>
        (List.nodup_append.mp nodup').2.2 f inP f List.mem_cons_self rfl
      have fNotW : f ∉ w := (List.nodup_cons.mp nodup).1
      have across : ∀ g ∈ p, I f g := by
        intro g inP
        have ne : g ≠ f := fun same => fNotP (same ▸ inP)
        by_contra notI
        have gw : g ∈ f :: w := perm.symm.subset (List.mem_append_left _ inP)
        have agree := ordered g gw f List.mem_cons_self ne (fun related => notI (symm g f related))
        have later : Precedes (p ++ f :: q) g f := precedes_append_cons_of_mem q inP
        rcases precedes_cons.mp (agree.mpr later) with ⟨same, _⟩ | h
        · exact ne same
        · exact fNotW h.mem_right
      have restPerm : w.Perm (p ++ q) := (perm.trans List.perm_middle).cons_inv
      have restOrdered : ∀ x ∈ w, ∀ y ∈ w, x ≠ y → ¬ I x y →
          (Precedes w x y ↔ Precedes (p ++ q) x y) := by
        intro x hx y hy ne notI
        have xf : x ≠ f := fun same => fNotW (same ▸ hx)
        have yf : y ≠ f := fun same => fNotW (same ▸ hy)
        rw [← precedes_cons_of_ne (w := w) xf, ← precedes_append_cons_iff xf yf p q]
        exact ordered x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy) ne notI
      have tail := traceEquiv_of_ordered symm w (p ++ q) (List.nodup_cons.mp nodup).2 restPerm
        restOrdered
      have front : Mettapedia.GSLT.Distinction.CausalGluing.TraceEquiv I (f :: (p ++ q)) (p ++ f :: q) :=
        Mettapedia.GSLT.Distinction.CausalGluing.TraceEquiv.cons_across f p q across
      exact .trans _ _ _ (Mettapedia.GSLT.Distinction.CausalGluing.TraceEquiv.append_left [f] tail)
        front

/-- A finite set with an acyclic relation has a member with no predecessor in it. -/
theorem exists_minimal (F : Finset α) (R : α → α → Prop) (acyclic : ∀ a, ¬ Relation.TransGen R a a)
    (nonempty : F.Nonempty) : ∃ a ∈ F, ∀ b ∈ F, ¬ R b a := by
  classical
  obtain ⟨a, aF, least⟩ := F.exists_min_image
    (fun a => (F.filter fun b => Relation.TransGen R b a).card) nonempty
  refine ⟨a, aF, fun b bF edge => ?_⟩
  have smaller : F.filter (fun c => Relation.TransGen R c b) ⊂
      F.filter (fun c => Relation.TransGen R c a) := by
    refine (Finset.ssubset_iff_of_subset ?_).mpr ⟨b, ?_, ?_⟩
    · intro c hc
      rw [Finset.mem_filter] at hc ⊢
      exact ⟨hc.1, hc.2.tail edge⟩
    · rw [Finset.mem_filter]
      exact ⟨bF, .single edge⟩
    · rw [Finset.mem_filter]
      exact fun h => acyclic b h.2
  exact absurd (least b bF) (not_le.mpr (Finset.card_lt_card smaller))

end Precedence

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

/-! ## Three relations and two conflicts -/

section Relations

variable (label : O → T)

/-- Two firings take one occurrence: no run has both. -/
def TakeConflict (f g : Firing T S O) : Prop :=
  ∃ o ∈ f.selection.taken, o ∈ g.selection.taken

/-- Two firings make one identity. -/
def MadeConflict (f g : Firing T S O) : Prop :=
  ∃ o ∈ f.selection.made, o ∈ g.selection.made

/-- `writer` takes or makes an occurrence inside the space of a predicate query of `observer`, at
some solution: the inhibitor arc of the query. -/
def Inhibits (writer observer : Firing T S O) : Prop :=
  ∃ σ : S, InhibitsAt label σ writer observer

/-- The pairs whose order a configuration records. -/
def InhibitionPair (f g : Firing T S O) : Prop :=
  Inhibits label f g ∨ Inhibits label g f

omit [DecidableEq O] in
theorem InhibitionPair.symm' {f g : Firing T S O} (pair : InhibitionPair label f g) :
    InhibitionPair label g f :=
  Or.symm pair

omit [DecidableEq O] in
/-- What a firing that does not inhibit an observer writes lies outside every query space of the
observer, at every solution. -/
theorem not_inhibitsAt {writer observer : Firing T S O} (no : ¬ Inhibits label writer observer)
    (σ : S) : ∀ query ∈ observer.queries, ∀ o,
      (o ∈ writer.selection.taken ∨ o ∈ writer.selection.made) → query.region σ (label o) = false := by
  intro query member o written
  cases inside : query.region σ (label o) with
  | false => rfl
  | true => exact absurd ⟨σ, query, member, o, written, inside⟩ no

/-- **Without the three relations and the two conflicts, two firings of the fragment are
statically independent** in R22's sense. -/
theorem staticIndependent_of_parts {x y : Firing T S O} (sx : x.Static) (sy : y.Static)
    (flow : ¬ Flow x y) (flow' : ¬ Flow y x) (read : ¬ ReadBeforeTake x y)
    (read' : ¬ ReadBeforeTake y x) (inhibits : ¬ Inhibits label x y) (inhibits' : ¬ Inhibits label y x)
    (take : ¬ TakeConflict x y) (made : ¬ MadeConflict x y) : StaticIndependent label x y := by
  refine ⟨sx, sy, fun σ => ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩⟩
  · rintro (taken | made')
    · obtain ⟨o, a, b⟩ := Finset.not_disjoint_iff.mp taken
      exact take ⟨o, by simpa using a, by simpa using b⟩
    · obtain ⟨o, a, b⟩ := Finset.not_disjoint_iff.mp made'
      exact made ⟨o, by simpa using a, by simpa using b⟩
  · rintro (kept | ⟨query, member, o, written, inside⟩)
    · obtain ⟨o, a, b⟩ := Finset.not_disjoint_iff.mp kept
      exact read' ⟨o, by simpa using b, by simpa using a⟩
    · rw [Firing.footprintAt_queries, List.mem_map] at member
      obtain ⟨query, inQueries, rfl⟩ := member
      exact inhibits ⟨σ, query, inQueries, o, by simpa using written, inside⟩
  · rintro (kept | ⟨query, member, o, written, inside⟩)
    · obtain ⟨o, a, b⟩ := Finset.not_disjoint_iff.mp kept
      exact read ⟨o, by simpa using b, by simpa using a⟩
    · rw [Firing.footprintAt_queries, List.mem_map] at member
      obtain ⟨query, inQueries, rfl⟩ := member
      exact inhibits' ⟨σ, query, inQueries, o, by simpa using written, inside⟩
  · refine Finset.disjoint_left.mpr fun o inMade used => ?_
    rcases MeTTaCalculus.OccurrenceCommits.Commit.mem_uses.mp used with taken | kept
    · exact flow ⟨o, by simpa using inMade, Or.inl (by simpa using taken)⟩
    · exact flow ⟨o, by simpa using inMade, Or.inr (by simpa using kept)⟩
  · refine Finset.disjoint_left.mpr fun o inMade used => ?_
    rcases MeTTaCalculus.OccurrenceCommits.Commit.mem_uses.mp used with taken | kept
    · exact flow' ⟨o, by simpa using inMade, Or.inl (by simpa using taken)⟩
    · exact flow' ⟨o, by simpa using inMade, Or.inr (by simpa using kept)⟩

end Relations

/-! ## The fragment -/

/-- The parts of admission that do not depend on the configuration. -/
structure Shape (label : O → T) (f : Firing T S O) : Prop where
  take_distinct : f.selection.taken.Nodup
  output_distinct : f.selection.made.Nodup
  take_length : f.rule.take.length = f.selection.taken.length
  read_length : f.rule.read.length = f.selection.read.length
  outputs : f.selection.made.map label = f.rule.produce
  apart : ∀ o ∈ f.selection.taken, o ∉ f.selection.read

/-- **The fragment of the correspondence**: no guards and query spaces independent of the
solution (`Firing.Static`), distinct firings, made identities fresh at the start, and no identity
made twice. -/
structure Fragment (C : Configuration T O) (w : List (Firing T S O)) : Prop where
  static : ∀ f ∈ w, f.Static
  nodup : w.Nodup
  fresh : ∀ f ∈ w, ∀ o ∈ f.selection.made, o ∉ C.present
  makers : ∀ f ∈ w, ∀ g ∈ w, f ≠ g → ∀ o ∈ f.selection.made, o ∉ g.selection.made

theorem Fragment.tail (label : O → T) {C : Configuration T O} {f : Firing T S O}
    {w : List (Firing T S O)} (fragment : Fragment C (f :: w)) : Fragment (f.result label C) w where
  static g member := fragment.static g (List.mem_cons_of_mem f member)
  nodup := (List.nodup_cons.mp fragment.nodup).2
  fresh g member o made := by
    have notF : g ≠ f := fun same => (List.nodup_cons.mp fragment.nodup).1 (same ▸ member)
    intro present
    have present' : o ∈ fire C.present (f.selection.commit (T := T)) := present
    rcases mem_fire.mp present' with ⟨old, _⟩ | made'
    · exact fragment.fresh g (List.mem_cons_of_mem f member) o made old
    · exact fragment.makers g (List.mem_cons_of_mem f member) f List.mem_cons_self notF o made
        (by simpa [Selection.commit] using made')
  makers g gm h hm ne :=
    fragment.makers g (List.mem_cons_of_mem f gm) h (List.mem_cons_of_mem f hm) ne

omit [DecidableEq O] in
theorem Fragment.perm {C : Configuration T O} {w w' : List (Firing T S O)} (fragment : Fragment C w)
    (perm : w.Perm w') : Fragment C w' where
  static f member := fragment.static f (perm.mem_iff.mpr member)
  nodup := perm.nodup_iff.mp fragment.nodup
  fresh f member := fragment.fresh f (perm.mem_iff.mpr member)
  makers f fm g gm ne := fragment.makers f (perm.mem_iff.mpr fm) g (perm.mem_iff.mpr gm) ne

/-! ## Admission in the fragment -/

section Admission

variable (A : SubstitutionAction T S) (label : O → T)

theorem Shape.of_valid {f : Firing T S O} {C : Configuration T O} (valid : f.Valid A label C) :
    Shape label f where
  take_distinct := valid.firing.take_distinct
  output_distinct := valid.firing.output_distinct
  take_length := valid.firing.take_length
  read_length := valid.firing.read_length
  outputs := valid.firing.outputs
  apart o taken read := Finset.disjoint_left.mp valid.firing.occurrences.apart
    (by simpa [Selection.commit] using taken) (by simpa [Selection.commit] using read)

theorem taken_present {f : Firing T S O} {C : Configuration T O} (valid : f.Valid A label C)
    {o : O} (member : o ∈ f.selection.taken) : o ∈ C.present :=
  valid.firing.occurrences.taken_subset (by simpa [Selection.commit] using member)

theorem read_present {f : Firing T S O} {C : Configuration T O} (valid : f.Valid A label C)
    {o : O} (member : o ∈ f.selection.read) : o ∈ C.present :=
  valid.firing.occurrences.kept_subset (by simpa [Selection.commit] using member)

theorem made_absent {f : Firing T S O} {C : Configuration T O} (valid : f.Valid A label C)
    {o : O} (member : o ∈ f.selection.made) : o ∉ C.present :=
  Finset.disjoint_left.mp valid.firing.occurrences.fresh (by simpa [Selection.commit] using member)

/-- With query spaces independent of the solution, each predicate query holds at every solution. -/
theorem queries_hold_of_valid {f : Firing T S O} {C : Configuration T O} (static : f.Static)
    (valid : f.Valid A label C) :
    ∀ query ∈ f.queries, ∀ σ : S, regionOf label C.present (query.region σ) = query.seen := by
  intro query member σ
  obtain ⟨τ, solved⟩ := valid.firing.consistent
  rw [static.queries query member σ τ]
  exact valid.observations query member τ solved

/-- **Admission in the fragment from its parts.** -/
theorem valid_of_parts {f : Firing T S O} {C : Configuration T O} (static : f.Static)
    (shape : Shape label f) (taken : ∀ o ∈ f.selection.taken, o ∈ C.present)
    (read : ∀ o ∈ f.selection.read, o ∈ C.present) (fresh : ∀ o ∈ f.selection.made, o ∉ C.present)
    (consistent : A.Consistent (C.equations ++ f.added label))
    (observed : ∀ query ∈ f.queries, ∀ σ : S, regionOf label C.present (query.region σ) = query.seen) :
    f.Valid A label C := by
  refine ⟨⟨shape.take_distinct, shape.output_distinct, shape.take_length, shape.read_length,
    shape.outputs, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · intro o member
    exact taken o (by simpa [Selection.commit] using member)
  · intro o member
    exact read o (by simpa [Selection.commit] using member)
  · exact Finset.disjoint_left.mpr fun o a b =>
      shape.apart o (by simpa [Selection.commit] using a) (by simpa [Selection.commit] using b)
  · exact Finset.disjoint_left.mpr fun o made present =>
      fresh o (by simpa [Selection.commit] using made) present
  · intro query member
    simp [Selection.commit] at member
  · rw [Firing.problem_eq']
    exact consistent
  · intro check member
    rw [static.checks] at member
    cases member
  · intro query member σ _
    exact observed query member σ

/-- What a firing takes is gone after it. -/
theorem taken_absent_after {f : Firing T S O} {C : Configuration T O} (valid : f.Valid A label C)
    {o : O} (taken : o ∈ f.selection.taken) : o ∉ (f.result label C).present := by
  intro present
  have present' : o ∈ fire C.present (f.selection.commit (T := T)) := present
  rcases mem_fire.mp present' with ⟨_, notTaken⟩ | made
  · exact notTaken (by simpa [Selection.commit] using taken)
  · exact made_absent A label valid (by simpa [Selection.commit] using made)
      (taken_present A label valid taken)

/-- An absent occurrence that a run never makes is never taken or read in it. -/
theorem absent_unused {D : Configuration T O} {w : List (Firing T S O)}
    (run : Executable A label D w) {o : O} (absent : o ∉ D.present)
    (unmade : ∀ z ∈ w, o ∉ z.selection.made) :
    ∀ z ∈ w, o ∉ z.selection.read ∧ o ∉ z.selection.taken := by
  intro z member
  exact GuardFreeProcessOrders.absent_stays A label (w.map Firing.plain) D o
    (Executable.plain A label run) absent (by
      intro y inMap
      obtain ⟨x, inW, rfl⟩ := List.mem_map.mp inMap
      exact unmade x inW) z.plain (List.mem_map.mpr ⟨z, member, rfl⟩)

end Admission

/-! ## Dependent pairs are ordered alike in every run -/

section Orders

variable (A : SubstitutionAction T S) (label : O → T)

/-- **Flow orders a run.** -/
theorem precedes_of_flow : ∀ {C : Configuration T O} {w : List (Firing T S O)},
    Executable A label C w → Fragment C w → ∀ {x y : Firing T S O}, x ∈ w → y ∈ w →
      Flow x y → Precedes w x y
  | _, [], _, _, _, _, hx, _, _ => by simp at hx
  | C, f :: w, run, fragment, x, y, hx, hy, ⟨o, made, used⟩ => by
      have uses : ∀ {o : O}, (o ∈ f.selection.taken ∨ o ∈ f.selection.read) → o ∈ C.present := by
        rintro o (taken | read)
        · exact taken_present A label run.1 taken
        · exact read_present A label run.1 read
      rcases List.mem_cons.mp hx with rfl | hxw
      · rcases List.mem_cons.mp hy with rfl | hyw
        · exact absurd (uses used) (fragment.fresh _ List.mem_cons_self o made)
        · exact precedes_cons.mpr (Or.inl ⟨rfl, hyw⟩)
      · rcases List.mem_cons.mp hy with rfl | hyw
        · exact absurd (uses used) (fragment.fresh x (List.mem_cons_of_mem _ hxw) o made)
        · exact precedes_cons.mpr (Or.inr
            (precedes_of_flow run.2 (fragment.tail label) hxw hyw ⟨o, made, used⟩))

/-- **Read before take orders a run.** -/
theorem precedes_of_readBeforeTake : ∀ {C : Configuration T O} {w : List (Firing T S O)},
    Executable A label C w → Fragment C w → ∀ {x y : Firing T S O}, x ∈ w → y ∈ w →
      ReadBeforeTake x y → Precedes w x y
  | _, [], _, _, _, _, hx, _, _ => by simp at hx
  | C, f :: w, run, fragment, x, y, hx, hy, ⟨o, read, taken⟩ => by
      rcases List.mem_cons.mp hx with rfl | hxw
      · rcases List.mem_cons.mp hy with rfl | hyw
        · exact absurd read ((Shape.of_valid A label run.1).apart o taken)
        · exact precedes_cons.mpr (Or.inl ⟨rfl, hyw⟩)
      · rcases List.mem_cons.mp hy with rfl | hyw
        · have unmade : ∀ z ∈ w, o ∉ z.selection.made := fun z member made =>
            fragment.fresh z (List.mem_cons_of_mem _ member) o made (taken_present A label run.1 taken)
          exact absurd read
            (absent_unused A label run.2 (taken_absent_after A label run.1 taken) unmade x hxw).1
        · exact precedes_cons.mpr (Or.inr
            (precedes_of_readBeforeTake run.2 (fragment.tail label) hxw hyw ⟨o, read, taken⟩))

/-- **Two firings taking one occurrence are never in one run.** -/
theorem not_takeConflict : ∀ {C : Configuration T O} {w : List (Firing T S O)},
    Executable A label C w → Fragment C w → ∀ {x y : Firing T S O}, x ∈ w → y ∈ w → x ≠ y →
      ¬ TakeConflict x y
  | _, [], _, _, _, _, hx, _, _, _ => by simp at hx
  | C, f :: w, run, fragment, x, y, hx, hy, ne, ⟨o, tx, ty⟩ => by
      have later : ∀ {z : Firing T S O}, z ∈ w → o ∈ f.selection.taken → o ∉ z.selection.taken :=
        fun {z} member taken =>
          (absent_unused A label run.2 (taken_absent_after A label run.1 taken)
            (fun z' m made => fragment.fresh z' (List.mem_cons_of_mem _ m) o made
              (taken_present A label run.1 taken)) z member).2
      rcases List.mem_cons.mp hx with rfl | hxw
      · rcases List.mem_cons.mp hy with rfl | hyw
        · exact ne rfl
        · exact later hyw tx ty
      · rcases List.mem_cons.mp hy with rfl | hyw
        · exact later hxw ty tx
        · exact not_takeConflict run.2 (fragment.tail label) hxw hyw ne ⟨o, tx, ty⟩

end Orders

/-! ## Configurations -/

/-- A candidate configuration: the firings that happened, and, for each inhibition pair, which of
the two came first. -/
@[ext] structure Config (T : Type uT) (S : Type uS) (O : Type uO) where
  firings : Finset (Firing T S O)
  before : Firing T S O → Firing T S O → Prop

/-- The order a run records: inhibition pairs in the order of the run. -/
def beforeOf (label : O → T) (w : List (Firing T S O)) (x y : Firing T S O) : Prop :=
  Precedes w x y ∧ InhibitionPair label x y

open Classical in
/-- **The configuration of a run.** -/
noncomputable def configOf (label : O → T) (w : List (Firing T S O)) : Config T S O :=
  ⟨w.toFinset, beforeOf label w⟩

omit [DecidableEq O] in
theorem mem_configOf_firings {label : O → T} {w : List (Firing T S O)} {f : Firing T S O} :
    f ∈ (configOf label w).firings ↔ f ∈ w := by
  classical
  simp [configOf]

omit [DecidableEq O] in
theorem configOf_before (label : O → T) (w : List (Firing T S O)) :
    (configOf label w).before = beforeOf label w := rfl

/-- One step of the causal order of a configuration: flow, read before take, or the recorded
inhibition order. -/
def Edge (X : Config T S O) (g f : Firing T S O) : Prop :=
  g ∈ X.firings ∧ f ∈ X.firings ∧ (Flow g f ∨ ReadBeforeTake g f ∨ X.before g f)

open Classical in
/-- The members that write into a query space of `q` and are ordered before it. -/
noncomputable def writersBefore (label : O → T) (X : Config T S O) (q : Firing T S O) :
    Finset (Firing T S O) :=
  X.firings.filter fun g => Inhibits label g q ∧ X.before g q

omit [DecidableEq O] in
theorem mem_writersBefore {label : O → T} {X : Config T S O} {q g : Firing T S O} :
    g ∈ writersBefore label X q ↔ g ∈ X.firings ∧ Inhibits label g q ∧ X.before g q := by
  classical
  simp [writersBefore]

/-- What a set of firings makes. -/
def madeBy (P : Finset (Firing T S O)) : Finset O := P.biUnion fun g => g.selection.made.toFinset

/-- What a set of firings takes. -/
def takenBy (P : Finset (Firing T S O)) : Finset O := P.biUnion fun g => g.selection.taken.toFinset

/-- The occurrences present after a set of firings of an occurrence net. -/
def presentAfter (C : Configuration T O) (P : Finset (Firing T S O)) : Finset O :=
  (C.present ∪ madeBy P) \ takenBy P

theorem mem_presentAfter {C : Configuration T O} {P : Finset (Firing T S O)} {o : O} :
    o ∈ presentAfter C P ↔
      (o ∈ C.present ∨ ∃ g ∈ P, o ∈ g.selection.made) ∧ ∀ g ∈ P, o ∉ g.selection.taken := by
  simp [presentAfter, madeBy, takenBy]

/-- **A configuration**, stated without runs. -/
structure IsConfiguration (A : SubstitutionAction T S) (label : O → T) (C : Configuration T O)
    (X : Config T S O) : Prop where
  static : ∀ f ∈ X.firings, f.Static
  shape : ∀ f ∈ X.firings, Shape label f
  fresh : ∀ f ∈ X.firings, ∀ o ∈ f.selection.made, o ∉ C.present
  makers : ∀ f ∈ X.firings, ∀ g ∈ X.firings, f ≠ g → ∀ o ∈ f.selection.made, o ∉ g.selection.made
  takes : ∀ f ∈ X.firings, ∀ g ∈ X.firings, f ≠ g → ∀ o ∈ f.selection.taken, o ∉ g.selection.taken
  closed : ∀ f ∈ X.firings, ∀ o, (o ∈ f.selection.taken ∨ o ∈ f.selection.read) →
    o ∈ C.present ∨ ∃ g ∈ X.firings, o ∈ g.selection.made
  oriented : ∀ f ∈ X.firings, ∀ g ∈ X.firings, f ≠ g → Inhibits label f g →
    X.before f g ∨ X.before g f
  before_spec : ∀ f g, X.before f g →
    f ∈ X.firings ∧ g ∈ X.firings ∧ f ≠ g ∧ InhibitionPair label f g
  acyclic : ∀ f, ¬ Relation.TransGen (Edge X) f f
  observed : ∀ q ∈ X.firings, ∀ query ∈ q.queries, ∀ σ : S,
    regionOf label (presentAfter C (writersBefore label X q)) (query.region σ) = query.seen
  joint : ∃ σ, A.Models σ C.equations ∧ ∀ f ∈ X.firings, A.Models σ (f.added label)

/-! ## Events: firings with their causes -/

/-- The causes of a firing in a configuration: its predecessors under flow, read before take and
the recorded inhibition order. -/
def causes (X : Config T S O) (f : Firing T S O) : Set (Firing T S O) :=
  {g | Relation.TransGen (Edge X) g f}

/-- The events of a configuration: each firing with its causes. -/
def events (X : Config T S O) : Set (Firing T S O × Set (Firing T S O)) :=
  {e | e.1 ∈ X.firings ∧ e.2 = causes X e.1}

section EventsDetermine

variable (A : SubstitutionAction T S) (label : O → T)

/-- In a configuration, a cause of an inhibition partner was ordered before it. -/
theorem before_of_cause {C : Configuration T O} {Y : Config T S O}
    (hY : IsConfiguration A label C Y) {g h : Firing T S O} (hg : g ∈ Y.firings)
    (hh : h ∈ Y.firings) (ne : g ≠ h) (pair : InhibitionPair label g h)
    (path : Relation.TransGen (Edge Y) g h) : Y.before g h := by
  have oriented : Y.before g h ∨ Y.before h g := by
    rcases pair with inhibits | inhibits
    · exact hY.oriented g hg h hh ne inhibits
    · exact (hY.oriented h hh g hg ne.symm inhibits).symm
  rcases oriented with before | before
  · exact before
  · exact absurd (path.tail ⟨hh, hg, Or.inr (Or.inr before)⟩) (hY.acyclic g)

/-- **A configuration is determined by its events.** -/
theorem config_eq_of_events_eq {C D : Configuration T O} {X Y : Config T S O}
    (hX : IsConfiguration A label C X) (hY : IsConfiguration A label D Y)
    (same : events X = events Y) : X = Y := by
  have toY : ∀ f ∈ X.firings, f ∈ Y.firings ∧ causes X f = causes Y f := by
    intro f hf
    have member : (f, causes X f) ∈ events Y := same ▸ (show (f, causes X f) ∈ events X from ⟨hf, rfl⟩)
    exact member
  have toX : ∀ f ∈ Y.firings, f ∈ X.firings ∧ causes Y f = causes X f := by
    intro f hf
    have member : (f, causes Y f) ∈ events X :=
      same.symm ▸ (show (f, causes Y f) ∈ events Y from ⟨hf, rfl⟩)
    exact member
  refine Config.ext (Finset.ext fun f => ⟨fun hf => (toY f hf).1, fun hf => (toX f hf).1⟩) ?_
  funext g h
  apply propext
  constructor
  · intro before
    obtain ⟨hg, hh, ne, pair⟩ := hX.before_spec g h before
    have path : g ∈ causes X h := Relation.TransGen.single ⟨hg, hh, Or.inr (Or.inr before)⟩
    rw [(toY h hh).2] at path
    exact before_of_cause A label hY (toY g hg).1 (toY h hh).1 ne pair path
  · intro before
    obtain ⟨hg, hh, ne, pair⟩ := hY.before_spec g h before
    have path : g ∈ causes Y h := Relation.TransGen.single ⟨hg, hh, Or.inr (Or.inr before)⟩
    rw [(toX h hh).2] at path
    exact before_of_cause A label hX (toX g hg).1 (toX h hh).1 ne pair path

end EventsDetermine

/-! ## Present occurrences after a set of firings -/

section Present

variable (label : O → T)

theorem presentAfter_result [DecidableEq (Firing T S O)] {f : Firing T S O} {C : Configuration T O}
    {P : Finset (Firing T S O)}
    (apart : ∀ o ∈ f.selection.taken, o ∉ f.selection.made ∧ ∀ g ∈ P, o ∉ g.selection.made) :
    presentAfter (f.result label C) P = presentAfter C (insert f P) := by
  ext o
  have unfold : o ∈ (f.result label C).present ↔
      (o ∈ C.present ∧ o ∉ f.selection.taken) ∨ o ∈ f.selection.made := by
    change o ∈ fire C.present (f.selection.commit (T := T)) ↔ _
    simp [mem_fire, Selection.commit]
  rw [mem_presentAfter, mem_presentAfter, unfold]
  constructor
  · rintro ⟨source, notTaken⟩
    refine ⟨?_, fun g hg => ?_⟩
    · rcases source with (⟨present, _⟩ | made) | ⟨g, hg, made⟩
      · exact Or.inl present
      · exact Or.inr ⟨f, Finset.mem_insert_self f P, made⟩
      · exact Or.inr ⟨g, Finset.mem_insert_of_mem hg, made⟩
    · rcases Finset.mem_insert.mp hg with rfl | hg
      · intro taken
        rcases source with (⟨_, notF⟩ | made) | ⟨g', hg', made⟩
        · exact notF taken
        · exact (apart o taken).1 made
        · exact (apart o taken).2 g' hg' made
      · exact notTaken g hg
  · rintro ⟨source, notTaken⟩
    have notF : o ∉ f.selection.taken := notTaken f (Finset.mem_insert_self f P)
    refine ⟨?_, fun g hg => notTaken g (Finset.mem_insert_of_mem hg)⟩
    rcases source with present | ⟨g, hg, made⟩
    · exact Or.inl (Or.inl ⟨present, notF⟩)
    · rcases Finset.mem_insert.mp hg with rfl | hg
      · exact Or.inl (Or.inr made)
      · exact Or.inr ⟨g, hg, made⟩

theorem regionOf_presentAfter_insert [DecidableEq (Firing T S O)] {f : Firing T S O}
    {C : Configuration T O} {P : Finset (Firing T S O)} {region : T → Bool}
    (outside : ∀ o, (o ∈ f.selection.taken ∨ o ∈ f.selection.made) → region (label o) = false) :
    regionOf label (presentAfter C (insert f P)) region = regionOf label (presentAfter C P) region := by
  ext o
  rw [mem_regionOf, mem_regionOf, mem_presentAfter, mem_presentAfter]
  constructor
  · rintro ⟨⟨source, notTaken⟩, inside⟩
    refine ⟨⟨?_, fun g hg => notTaken g (Finset.mem_insert_of_mem hg)⟩, inside⟩
    rcases source with present | ⟨g, hg, made⟩
    · exact Or.inl present
    · rcases Finset.mem_insert.mp hg with rfl | hg
      · have out := outside o (Or.inr made)
        rw [inside] at out
        exact absurd out (by decide)
      · exact Or.inr ⟨g, hg, made⟩
  · rintro ⟨⟨source, notTaken⟩, inside⟩
    refine ⟨⟨?_, fun g hg => ?_⟩, inside⟩
    · rcases source with present | ⟨g, hg, made⟩
      · exact Or.inl present
      · exact Or.inr ⟨g, Finset.mem_insert_of_mem hg, made⟩
    · rcases Finset.mem_insert.mp hg with rfl | hg
      · intro taken
        have out := outside o (Or.inl taken)
        rw [inside] at out
        exact absurd out (by decide)
      · exact notTaken g hg

end Present

/-! ## Every run gives a configuration -/

section Image

variable (A : SubstitutionAction T S) (label : O → T)

theorem shape_of_run : ∀ {C : Configuration T O} {w : List (Firing T S O)},
    Executable A label C w → ∀ f ∈ w, Shape label f
  | _, [], _, f, hf => by simp at hf
  | _, _ :: _, run, f, hf => by
      rcases List.mem_cons.mp hf with rfl | hf
      · exact Shape.of_valid A label run.1
      · exact shape_of_run run.2 f hf

theorem closed_of_run : ∀ {C : Configuration T O} {w : List (Firing T S O)},
    Executable A label C w → ∀ f ∈ w, ∀ o, (o ∈ f.selection.taken ∨ o ∈ f.selection.read) →
      o ∈ C.present ∨ ∃ g ∈ w, o ∈ g.selection.made
  | _, [], _, f, hf, _, _ => by simp at hf
  | C, g :: w, run, f, hf, o, used => by
      rcases List.mem_cons.mp hf with rfl | hf
      · rcases used with taken | read
        · exact Or.inl (taken_present A label run.1 taken)
        · exact Or.inl (read_present A label run.1 read)
      · rcases closed_of_run run.2 f hf o used with present | ⟨h, hh, made⟩
        · have present' : o ∈ fire C.present (g.selection.commit (T := T)) := present
          rcases mem_fire.mp present' with ⟨old, _⟩ | made
          · exact Or.inl old
          · exact Or.inr ⟨g, List.mem_cons_self, by simpa [Selection.commit] using made⟩
        · exact Or.inr ⟨h, List.mem_cons_of_mem _ hh, made⟩

omit [DecidableEq O] in
theorem mem_writersBefore_configOf {w : List (Firing T S O)} {q g : Firing T S O} :
    g ∈ writersBefore label (configOf label w) q ↔ Inhibits label g q ∧ Precedes w g q := by
  rw [mem_writersBefore, mem_configOf_firings, configOf_before]
  constructor
  · rintro ⟨_, inhibits, precedes, _⟩
    exact ⟨inhibits, precedes⟩
  · rintro ⟨inhibits, precedes⟩
    exact ⟨precedes.mem_left, inhibits, precedes, Or.inl inhibits⟩

theorem queries_hold_of_run : ∀ {C : Configuration T O} {w : List (Firing T S O)},
    Executable A label C w → Fragment C w → ∀ q ∈ w, ∀ query ∈ q.queries, ∀ σ : S,
      regionOf label (presentAfter C (writersBefore label (configOf label w) q)) (query.region σ) =
        query.seen
  | _, [], _, _, q, hq, _, _, _ => by simp at hq
  | C, f :: w, run, fragment, q, hq, query, member, σ => by
      classical
      have nodup := fragment.nodup
      rcases List.mem_cons.mp hq with rfl | hqw
      · have empty : presentAfter C (writersBefore label (configOf label (q :: w)) q) = C.present := by
          ext o
          rw [mem_presentAfter]
          constructor
          · rintro ⟨present | ⟨g, hg, _⟩, _⟩
            · exact present
            · exact absurd (mem_writersBefore_configOf label |>.mp hg).2 (not_precedes_head nodup)
          · intro present
            exact ⟨Or.inl present, fun g hg =>
              absurd (mem_writersBefore_configOf label |>.mp hg).2 (not_precedes_head nodup)⟩
        rw [empty]
        exact queries_hold_of_valid A label (fragment.static q List.mem_cons_self) run.1 query member σ
      · have ih := queries_hold_of_run run.2 (fragment.tail label) q hqw query member σ
        have shift : presentAfter (f.result label C) (writersBefore label (configOf label w) q) =
            presentAfter C (insert f (writersBefore label (configOf label w) q)) := by
          refine presentAfter_result label fun o taken => ⟨fun made => ?_, fun g hg made => ?_⟩
          · exact made_absent A label run.1 made (taken_present A label run.1 taken)
          · have gw : g ∈ w := (mem_writersBefore_configOf label |>.mp hg).2.mem_left
            exact fragment.fresh g (List.mem_cons_of_mem _ gw) o made
              (taken_present A label run.1 taken)
        rw [shift] at ih
        by_cases inhibits : Inhibits label f q
        · have same : writersBefore label (configOf label (f :: w)) q =
              insert f (writersBefore label (configOf label w) q) := by
            ext g
            rw [mem_writersBefore_configOf, Finset.mem_insert, mem_writersBefore_configOf,
              precedes_cons]
            constructor
            · rintro ⟨inh, ⟨rfl, _⟩ | precedes⟩
              · exact Or.inl rfl
              · exact Or.inr ⟨inh, precedes⟩
            · rintro (rfl | ⟨inh, precedes⟩)
              · exact ⟨inhibits, Or.inl ⟨rfl, hqw⟩⟩
              · exact ⟨inh, Or.inr precedes⟩
          rw [same]
          exact ih
        · have same : writersBefore label (configOf label (f :: w)) q =
              writersBefore label (configOf label w) q := by
            ext g
            rw [mem_writersBefore_configOf, mem_writersBefore_configOf, precedes_cons]
            constructor
            · rintro ⟨inh, ⟨rfl, _⟩ | precedes⟩
              · exact absurd inh inhibits
              · exact ⟨inh, precedes⟩
            · rintro ⟨inh, precedes⟩
              exact ⟨inh, Or.inr precedes⟩
          rw [same, ← regionOf_presentAfter_insert label (not_inhibitsAt label inhibits σ query member)]
          exact ih

theorem precedes_of_edge {C : Configuration T O} {w : List (Firing T S O)}
    (run : Executable A label C w) (fragment : Fragment C w) {a b : Firing T S O}
    (edge : Edge (configOf label w) a b) : Precedes w a b := by
  obtain ⟨ha, hb, flow | read | before⟩ := edge
  · exact precedes_of_flow A label run fragment (mem_configOf_firings.mp ha)
      (mem_configOf_firings.mp hb) flow
  · exact precedes_of_readBeforeTake A label run fragment (mem_configOf_firings.mp ha)
      (mem_configOf_firings.mp hb) read
  · exact before.1

theorem precedes_of_transGen {C : Configuration T O} {w : List (Firing T S O)}
    (run : Executable A label C w) (fragment : Fragment C w) {a b : Firing T S O}
    (path : Relation.TransGen (Edge (configOf label w)) a b) : Precedes w a b := by
  induction path with
  | single edge => exact precedes_of_edge A label run fragment edge
  | tail _ edge ih => exact precedes_trans fragment.nodup ih (precedes_of_edge A label run fragment edge)

/-- **Every run of the fragment gives a configuration.** -/
theorem configOf_isConfiguration {C : Configuration T O} {w : List (Firing T S O)}
    (run : Executable A label C w) (fragment : Fragment C w) :
    IsConfiguration A label C (configOf label w) where
  static f hf := fragment.static f (mem_configOf_firings.mp hf)
  shape f hf := shape_of_run A label run f (mem_configOf_firings.mp hf)
  fresh f hf := fragment.fresh f (mem_configOf_firings.mp hf)
  makers f hf g hg ne := fragment.makers f (mem_configOf_firings.mp hf) g (mem_configOf_firings.mp hg) ne
  takes f hf g hg ne o tf tg := not_takeConflict A label run fragment (mem_configOf_firings.mp hf)
    (mem_configOf_firings.mp hg) ne ⟨o, tf, tg⟩
  closed f hf o used := by
    rcases closed_of_run A label run f (mem_configOf_firings.mp hf) o used with h | ⟨g, hg, made⟩
    · exact Or.inl h
    · exact Or.inr ⟨g, mem_configOf_firings.mpr hg, made⟩
  oriented f hf g hg ne inhibits := by
    rcases precedes_total (mem_configOf_firings.mp hf) (mem_configOf_firings.mp hg) ne with h | h
    · exact Or.inl ⟨h, Or.inl inhibits⟩
    · exact Or.inr ⟨h, Or.inr inhibits⟩
  before_spec f g before := by
    obtain ⟨precedes, pair⟩ := before
    exact ⟨mem_configOf_firings.mpr precedes.mem_left, mem_configOf_firings.mpr precedes.mem_right,
      fun same => precedes_irrefl fragment.nodup f (same ▸ precedes), pair⟩
  acyclic f cycle := precedes_irrefl fragment.nodup f (precedes_of_transGen A label run fragment cycle)
  observed q hq query member σ :=
    queries_hold_of_run A label run fragment q (mem_configOf_firings.mp hq) query member σ
  joint := by
    obtain ⟨σ, solved⟩ := Executable.joint A label run
    rw [jointProblem, A.models_append] at solved
    exact ⟨σ, solved.1, fun f hf e member =>
      solved.2 e (List.mem_flatMap.mpr ⟨f, mem_configOf_firings.mp hf, member⟩)⟩

end Image

/-! ## Round-equivalent runs have one configuration -/

section WellDefined

variable (A : SubstitutionAction T S) (label : O → T)

/-- **A round pair of the fragment is not an inhibition pair.** -/
theorem not_inhibitionPair_of_round {D : Configuration T O} {f g : Firing T S O}
    (fs : f.Static) (gs : g.Static) (isRound : Round A label D [f, g]) :
    ¬ InhibitionPair label f g := by
  have compatible : Compatible A label D f g := List.pairwise_pair.mp isRound.compatible
  obtain ⟨τ, solved⟩ := isRound.joint
  have cut : A.Models τ (pairCut label D f g) := by
    simp only [jointProblem, pairCut, SubstitutionAction.models_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil] at solved ⊢
    exact ⟨⟨solved.1, solved.2.1⟩, solved.2.2⟩
  rintro (⟨σ, query, member, o, written, inside⟩ | ⟨σ, query, member, o, written, inside⟩)
  · have ignored := compatible.2.2.2.2 query member τ cut o (List.mem_append.mpr written)
    rw [gs.queries query member σ τ, ignored] at inside
    exact absurd inside (by decide)
  · have ignored := compatible.2.2.2.1 query member τ cut o (List.mem_append.mpr written)
    rw [fs.queries query member σ τ, ignored] at inside
    exact absurd inside (by decide)

omit [DecidableEq O] in
theorem configOf_swap {u v : List (Firing T S O)} {f g : Firing T S O}
    (notPair : ¬ InhibitionPair label f g) :
    configOf label (u ++ f :: g :: v) = configOf label (u ++ g :: f :: v) := by
  refine Config.ext ?_ ?_
  · ext x
    rw [mem_configOf_firings, mem_configOf_firings]
    simp only [List.mem_append, List.mem_cons]
    tauto
  · funext x y
    apply propext
    rw [configOf_before, configOf_before]
    by_cases fg : x = f ∧ y = g
    · obtain ⟨rfl, rfl⟩ := fg
      exact iff_of_false (fun h => notPair h.2) (fun h => notPair h.2)
    · by_cases gf : x = g ∧ y = f
      · obtain ⟨rfl, rfl⟩ := gf
        exact iff_of_false (fun h => notPair (InhibitionPair.symm' label h.2))
          (fun h => notPair (InhibitionPair.symm' label h.2))
      · exact and_congr_left' (precedes_swap_iff fg gf u v)

/-- **Round-equivalent runs of the fragment have one configuration.** -/
theorem configOf_eq_of_roundEquiv {C : Configuration T O} {w w' : List (Firing T S O)}
    (equivalent : RoundEquiv A label C w w') (static : ∀ f ∈ w, f.Static) :
    configOf label w = configOf label w' := by
  revert static
  induction equivalent with
  | rel _ _ swapped =>
      cases swapped with
      | swap u v f g isRound =>
          intro static
          exact configOf_swap label (not_inhibitionPair_of_round A label (static f (by simp))
            (static g (by simp)) isRound)
  | refl => exact fun _ => rfl
  | symm _ _ first ih =>
      intro static
      exact (ih fun f hf => static f ((RoundEquiv.perm A label first).mem_iff.mp hf)).symm
  | trans _ _ _ first _ ih₁ ih₂ =>
      intro static
      exact (ih₁ static).trans (ih₂ fun f hf => static f ((RoundEquiv.perm A label first).mem_iff.mpr hf))

end WellDefined

/-! ## Runs with one configuration are round equivalent -/

section Injective

variable (A : SubstitutionAction T S) (label : O → T)

/-- **Runs of the fragment with one configuration are one static trace**: the projection lemma,
since every dependent pair of firings is ordered alike in both. -/
theorem staticTraceEquiv_of_configOf_eq {C : Configuration T O} {w w' : List (Firing T S O)}
    (run : Executable A label C w) (run' : Executable A label C w')
    (fragment : Fragment C w) (fragment' : Fragment C w')
    (same : configOf label w = configOf label w') :
    Mettapedia.GSLT.Distinction.CausalGluing.TraceEquiv (StaticIndependent label) w w' := by
  have members : ∀ f, f ∈ w ↔ f ∈ w' := fun f => by
    rw [← mem_configOf_firings (label := label), ← mem_configOf_firings (label := label) (w := w'),
      same]
  have perm : w.Perm w' := (List.perm_ext_iff_of_nodup fragment.nodup fragment'.nodup).mpr members
  have befores : ∀ x y, beforeOf label w x y ↔ beforeOf label w' x y := fun x y =>
    Iff.of_eq (congrFun (congrFun (congrArg Config.before same) x) y)
  have ordered : ∀ x ∈ w, ∀ y ∈ w, x ≠ y → ¬ StaticIndependent label x y →
      (Precedes w x y ↔ Precedes w' x y) := by
    intro x hx y hy ne notIndependent
    have hx' := (members x).mp hx
    have hy' := (members y).mp hy
    by_cases flow : Flow x y
    · exact iff_of_true (precedes_of_flow A label run fragment hx hy flow)
        (precedes_of_flow A label run' fragment' hx' hy' flow)
    by_cases flow' : Flow y x
    · exact iff_of_false (precedes_asymm fragment.nodup (precedes_of_flow A label run fragment hy hx flow'))
        (precedes_asymm fragment'.nodup (precedes_of_flow A label run' fragment' hy' hx' flow'))
    by_cases read : ReadBeforeTake x y
    · exact iff_of_true (precedes_of_readBeforeTake A label run fragment hx hy read)
        (precedes_of_readBeforeTake A label run' fragment' hx' hy' read)
    by_cases read' : ReadBeforeTake y x
    · exact iff_of_false
        (precedes_asymm fragment.nodup (precedes_of_readBeforeTake A label run fragment hy hx read'))
        (precedes_asymm fragment'.nodup (precedes_of_readBeforeTake A label run' fragment' hy' hx' read'))
    by_cases pair : InhibitionPair label x y
    · constructor
      · intro precedes
        exact ((befores x y).mp ⟨precedes, pair⟩).1
      · intro precedes
        exact ((befores x y).mpr ⟨precedes, pair⟩).1
    by_cases take : TakeConflict x y
    · exact absurd take (not_takeConflict A label run fragment hx hy ne)
    by_cases made : MadeConflict x y
    · obtain ⟨o, mx, my⟩ := made
      exact absurd my (fragment.makers x hx y hy ne o mx)
    exact absurd (staticIndependent_of_parts label (fragment.static x hx) (fragment.static y hy)
      flow flow' read read' (fun h => pair (Or.inl h)) (fun h => pair (Or.inr h)) take made)
      notIndependent
  exact traceEquiv_of_ordered (fun a b related => StaticIndependent.symm related) w w'
    fragment.nodup perm ordered

/-- **Runs of the fragment with one configuration are round equivalent.** -/
theorem roundEquiv_of_configOf_eq {C : Configuration T O} {w w' : List (Firing T S O)}
    (run : Executable A label C w) (run' : Executable A label C w')
    (fragment : Fragment C w) (fragment' : Fragment C w')
    (same : configOf label w = configOf label w') : RoundEquiv A label C w w' :=
  traceEquiv_roundEquiv A label
    (staticTraceEquiv_of_configOf_eq A label run run' fragment fragment' same) C run

/-- **In the fragment the two independences give one trace equivalence**: on runs of the
fragment, round equivalence is the static (Mazurkiewicz) trace equivalence of R22. -/
theorem roundEquiv_iff_staticTraceEquiv {C : Configuration T O} {w w' : List (Firing T S O)}
    (run : Executable A label C w) (run' : Executable A label C w')
    (fragment : Fragment C w) (fragment' : Fragment C w') :
    RoundEquiv A label C w w' ↔
      Mettapedia.GSLT.Distinction.CausalGluing.TraceEquiv (StaticIndependent label) w w' :=
  ⟨fun equivalent => staticTraceEquiv_of_configOf_eq A label run run' fragment fragment'
      (configOf_eq_of_roundEquiv A label equivalent fragment.static),
    fun static => traceEquiv_roundEquiv A label static C run⟩

end Injective

/-! ## Every configuration is the configuration of a run -/

section Surjective

variable (A : SubstitutionAction T S) (label : O → T)

/-- **Every configuration is the configuration of a run**, which fires a minimal event first. -/
theorem exists_run : ∀ (n : ℕ) {C : Configuration T O} {X : Config T S O}, X.firings.card = n →
    IsConfiguration A label C X →
      ∃ w, Executable A label C w ∧ Fragment C w ∧ configOf label w = X
  | 0, C, X, card, config => by
      classical
      have empty : X.firings = ∅ := Finset.card_eq_zero.mp card
      refine ⟨[], ?_, ⟨by simp, List.nodup_nil, by simp, by simp⟩, ?_⟩
      · obtain ⟨σ, solved, _⟩ := config.joint
        exact ⟨σ, solved⟩
      · refine Config.ext ?_ ?_
        · ext f
          rw [mem_configOf_firings, empty]
          simp
        · funext g h
          apply propext
          constructor
          · rintro ⟨precedes, _⟩
            exact absurd precedes (precedes_nil g h)
          · intro before
            have member := (config.before_spec g h before).1
            rw [empty] at member
            simp at member
  | n + 1, C, X, card, config => by
      classical
      have nonempty : X.firings.Nonempty := by
        rw [← Finset.card_pos, card]
        omega
      obtain ⟨f₀, hf₀, minimal⟩ := exists_minimal X.firings (Edge X) config.acyclic nonempty
      have noEdge : ∀ g, ¬ Edge X g f₀ := fun g edge => minimal g edge.1 edge
      have notBefore : ∀ g, ¬ X.before g f₀ := fun g before =>
        noEdge g ⟨(config.before_spec g f₀ before).1, hf₀, Or.inr (Or.inr before)⟩
      have uses : ∀ o, (o ∈ f₀.selection.taken ∨ o ∈ f₀.selection.read) → o ∈ C.present := by
        intro o used
        rcases config.closed f₀ hf₀ o used with present | ⟨g, hg, made⟩
        · exact present
        · exact absurd ⟨hg, hf₀, Or.inl ⟨o, made, used⟩⟩ (noEdge g)
      have orientedHead : ∀ q ∈ X.firings, q ≠ f₀ → Inhibits label f₀ q → X.before f₀ q := by
        intro q hq ne inhibits
        rcases config.oriented f₀ hf₀ q hq ne.symm inhibits with before | before
        · exact before
        · exact absurd before (notBefore q)
      have valid : f₀.Valid A label C := by
        refine valid_of_parts A label (config.static f₀ hf₀) (config.shape f₀ hf₀)
          (fun o taken => uses o (Or.inl taken)) (fun o read => uses o (Or.inr read))
          (config.fresh f₀ hf₀) ?_ ?_
        · obtain ⟨σ, base, all⟩ := config.joint
          exact ⟨σ, (A.models_append σ _ _).mpr ⟨base, all f₀ hf₀⟩⟩
        · intro query member σ
          have holds := config.observed f₀ hf₀ query member σ
          have empty : presentAfter C (writersBefore label X f₀) = C.present := by
            ext o
            rw [mem_presentAfter]
            constructor
            · rintro ⟨present | ⟨g, hg, _⟩, _⟩
              · exact present
              · exact absurd (mem_writersBefore.mp hg).2.2 (notBefore g)
            · intro present
              exact ⟨Or.inl present, fun g hg => absurd (mem_writersBefore.mp hg).2.2 (notBefore g)⟩
          rwa [empty] at holds
      have presentNext : ∀ {o : O}, o ∈ (f₀.result label C).present ↔
          (o ∈ C.present ∧ o ∉ f₀.selection.taken) ∨ o ∈ f₀.selection.made := by
        intro o
        change o ∈ fire C.present (f₀.selection.commit (T := T)) ↔ _
        simp [mem_fire, Selection.commit]
      let X' : Config T S O := ⟨X.firings.erase f₀, fun g h => X.before g h ∧ g ≠ f₀⟩
      have memX' : ∀ {g : Firing T S O}, g ∈ X'.firings ↔ g ≠ f₀ ∧ g ∈ X.firings :=
        Finset.mem_erase
      have config' : IsConfiguration A label (f₀.result label C) X' := by
        refine ⟨fun g hg => config.static g (memX'.mp hg).2, fun g hg => config.shape g (memX'.mp hg).2,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro g hg o made present
          rcases presentNext.mp present with ⟨old, _⟩ | made₀
          · exact config.fresh g (memX'.mp hg).2 o made old
          · exact config.makers g (memX'.mp hg).2 f₀ hf₀ (memX'.mp hg).1 o made made₀
        · intro g hg h hh ne
          exact config.makers g (memX'.mp hg).2 h (memX'.mp hh).2 ne
        · intro g hg h hh ne
          exact config.takes g (memX'.mp hg).2 h (memX'.mp hh).2 ne
        · intro g hg o used
          rcases config.closed g (memX'.mp hg).2 o used with present | ⟨h, hh, made⟩
          · refine Or.inl (presentNext.mpr (Or.inl ⟨present, fun taken => ?_⟩))
            rcases used with taken' | read
            · exact config.takes f₀ hf₀ g (memX'.mp hg).2 (memX'.mp hg).1.symm o taken taken'
            · exact noEdge g ⟨(memX'.mp hg).2, hf₀, Or.inr (Or.inl ⟨o, read, taken⟩)⟩
          · by_cases hf : h = f₀
            · subst hf
              exact Or.inl (presentNext.mpr (Or.inr made))
            · exact Or.inr ⟨h, memX'.mpr ⟨hf, hh⟩, made⟩
        · intro g hg h hh ne inhibits
          rcases config.oriented g (memX'.mp hg).2 h (memX'.mp hh).2 ne inhibits with before | before
          · exact Or.inl ⟨before, (memX'.mp hg).1⟩
          · exact Or.inr ⟨before, (memX'.mp hh).1⟩
        · rintro g h ⟨before, ne⟩
          obtain ⟨hg, hh, gh, pair⟩ := config.before_spec g h before
          exact ⟨memX'.mpr ⟨ne, hg⟩, memX'.mpr ⟨fun same => notBefore g (same ▸ before), hh⟩, gh, pair⟩
        · intro g cycle
          have edgeLift : ∀ {a b : Firing T S O}, Edge X' a b → Edge X a b := by
            rintro a b ⟨ha, hb, relation⟩
            refine ⟨(memX'.mp ha).2, (memX'.mp hb).2, ?_⟩
            rcases relation with flow | read | ⟨before, _⟩
            · exact Or.inl flow
            · exact Or.inr (Or.inl read)
            · exact Or.inr (Or.inr before)
          have lift : ∀ {a b : Firing T S O}, Relation.TransGen (Edge X') a b →
              Relation.TransGen (Edge X) a b := by
            intro a b path
            induction path with
            | single edge => exact .single (edgeLift edge)
            | tail _ edge ih => exact ih.tail (edgeLift edge)
          exact config.acyclic g (lift cycle)
        · intro q hq query member σ
          have hq' := memX'.mp hq
          have base := config.observed q hq'.2 query member σ
          have shift : presentAfter (f₀.result label C) (writersBefore label X' q) =
              presentAfter C (insert f₀ (writersBefore label X' q)) := by
            refine presentAfter_result label fun o taken => ⟨fun made => ?_, fun g hg made => ?_⟩
            · exact config.fresh f₀ hf₀ o made (uses o (Or.inl taken))
            · exact config.fresh g (memX'.mp (mem_writersBefore.mp hg).1).2 o made
                (uses o (Or.inl taken))
          rw [shift]
          by_cases inhibits : Inhibits label f₀ q
          · have same : insert f₀ (writersBefore label X' q) = writersBefore label X q := by
              ext g
              rw [Finset.mem_insert, mem_writersBefore, mem_writersBefore]
              constructor
              · rintro (rfl | ⟨hg, inh, before, _⟩)
                · exact ⟨hf₀, inhibits, orientedHead q hq'.2 hq'.1 inhibits⟩
                · exact ⟨(memX'.mp hg).2, inh, before⟩
              · rintro ⟨hg, inh, before⟩
                by_cases ne : g = f₀
                · exact Or.inl ne
                · exact Or.inr ⟨memX'.mpr ⟨ne, hg⟩, inh, before, ne⟩
            rw [same]
            exact base
          · have same : writersBefore label X' q = writersBefore label X q := by
              ext g
              rw [mem_writersBefore, mem_writersBefore]
              constructor
              · rintro ⟨hg, inh, before, _⟩
                exact ⟨(memX'.mp hg).2, inh, before⟩
              · rintro ⟨hg, inh, before⟩
                have ne : g ≠ f₀ := fun same => inhibits (same ▸ inh)
                exact ⟨memX'.mpr ⟨ne, hg⟩, inh, before, ne⟩
            rw [regionOf_presentAfter_insert label (not_inhibitsAt label inhibits σ query member), same]
            exact base
        · obtain ⟨σ, base, all⟩ := config.joint
          refine ⟨σ, ?_, fun g hg => all g (memX'.mp hg).2⟩
          rw [Firing.result_equations', A.models_append]
          exact ⟨base, all f₀ hf₀⟩
      have card' : X'.firings.card = n := by
        change (X.firings.erase f₀).card = n
        rw [Finset.card_erase_of_mem hf₀, card]
        rfl
      obtain ⟨w', run', fragment', same'⟩ := exists_run n card' config'
      have memW' : ∀ g, g ∈ w' ↔ g ≠ f₀ ∧ g ∈ X.firings := by
        intro g
        rw [← mem_configOf_firings (label := label), same']
        exact memX'
      have before' : ∀ a b, beforeOf label w' a b ↔ (X.before a b ∧ a ≠ f₀) := fun a b =>
        Iff.of_eq (congrFun (congrFun (congrArg Config.before same') a) b)
      have inX : ∀ {g}, g ∈ f₀ :: w' → g ∈ X.firings := by
        intro g hg
        rcases List.mem_cons.mp hg with rfl | hg
        · exact hf₀
        · exact ((memW' g).mp hg).2
      refine ⟨f₀ :: w', ⟨valid, run'⟩, ⟨fun g hg => config.static g (inX hg), ?_,
        fun g hg => config.fresh g (inX hg), fun g hg h hh ne => config.makers g (inX hg) h (inX hh) ne⟩, ?_⟩
      · exact List.nodup_cons.mpr ⟨fun h => ((memW' f₀).mp h).1 rfl, fragment'.nodup⟩
      · refine Config.ext ?_ ?_
        · ext g
          rw [mem_configOf_firings]
          constructor
          · exact inX
          · intro hg
            by_cases gf : g = f₀
            · exact gf ▸ List.mem_cons_self
            · exact List.mem_cons_of_mem _ ((memW' g).mpr ⟨gf, hg⟩)
        · funext g h
          apply propext
          rw [configOf_before]
          constructor
          · rintro ⟨precedes, pair⟩
            rcases precedes_cons.mp precedes with ⟨rfl, hh⟩ | precedes
            · have hh' := (memW' h).mp hh
              rcases pair with inh | inh
              · exact orientedHead h hh'.2 hh'.1 inh
              · rcases config.oriented h hh'.2 g hf₀ hh'.1 inh with b | b
                · exact absurd b (notBefore h)
                · exact b
            · exact ((before' g h).mp ⟨precedes, pair⟩).1
          · intro before
            obtain ⟨hg, hh, ne, pair⟩ := config.before_spec g h before
            by_cases gf : g = f₀
            · subst gf
              exact ⟨precedes_cons.mpr (Or.inl ⟨rfl, (memW' h).mpr ⟨ne.symm, hh⟩⟩), pair⟩
            · obtain ⟨precedes, pair'⟩ := (before' g h).mpr ⟨before, gf⟩
              exact ⟨precedes_cons.mpr (Or.inr precedes), pair'⟩

end Surjective

/-! ## The correspondence -/

section Correspondence

variable (A : SubstitutionAction T S) (label : O → T)

/-- **Two runs of the fragment are one trace exactly when their events agree.** -/
theorem roundEquiv_iff_events_eq {C : Configuration T O} {w w' : List (Firing T S O)}
    (run : Executable A label C w) (run' : Executable A label C w')
    (fragment : Fragment C w) (fragment' : Fragment C w') :
    RoundEquiv A label C w w' ↔ events (configOf label w) = events (configOf label w') := by
  constructor
  · intro equivalent
    rw [configOf_eq_of_roundEquiv A label equivalent fragment.static]
  · intro same
    exact roundEquiv_of_configOf_eq A label run run' fragment fragment'
      (config_eq_of_events_eq A label (configOf_isConfiguration A label run fragment)
        (configOf_isConfiguration A label run' fragment') same)

/-- The runs of the fragment from `C`. -/
def FragmentRun (C : Configuration T O) : Type _ :=
  {w : List (Firing T S O) // Executable A label C w ∧ Fragment C w}

/-- Their traces: the runs up to round equivalence. -/
def FragmentTrace (C : Configuration T O) : Type _ :=
  Quot fun a b : FragmentRun A label C => RoundEquiv A label C a.1 b.1

/-- The configurations from `C`. -/
def Configurations (C : Configuration T O) : Type _ :=
  {X : Config T S O // IsConfiguration A label C X}

/-- The configuration of a trace. -/
noncomputable def configuration (C : Configuration T O) :
    FragmentTrace A label C → Configurations A label C :=
  Quot.lift (fun a => ⟨configOf label a.1, configOf_isConfiguration A label a.2.1 a.2.2⟩)
    fun a _ related => Subtype.ext (configOf_eq_of_roundEquiv A label related a.2.2.static)

/-- **The traces of the fragment from `C` and its configurations are in bijection.** -/
theorem configuration_bijective (C : Configuration T O) :
    Function.Bijective (configuration A label C) := by
  constructor
  · intro x y same
    induction x using Quot.ind with
    | mk a =>
      induction y using Quot.ind with
      | mk b =>
        exact Quot.sound (roundEquiv_of_configOf_eq A label a.2.1 b.2.1 a.2.2 b.2.2
          (congrArg Subtype.val same))
  · rintro ⟨X, config⟩
    obtain ⟨w, run, fragment, same⟩ := exists_run A label X.firings.card rfl config
    exact ⟨Quot.mk _ ⟨w, run, fragment⟩, Subtype.ext same⟩

/-- **Arrows of the contextual trace category are configurations.** Two paths from the class of
`C` to one class, both of the fragment, are one arrow exactly when their configurations are
equal. -/
theorem trace_eq_iff_configOf_eq {C : Configuration T O} {y : (theory A label).Term}
    (p q : OccurrencePath (presentation A label) (classOf A label C) y)
    (fragmentP : Fragment C (OccurrencePath.sites p)) (fragmentQ : Fragment C (OccurrencePath.sites q)) :
    Trace.mk (T := (concurrency A label).tiles) p = Trace.mk q ↔
      configOf label (OccurrencePath.sites p) = configOf label (OccurrencePath.sites q) := by
  rw [trace_eq_iff_roundEquiv A label p q]
  by_cases consistent : A.Consistent C.equations
  · have runP := executable_of_path A label p C rfl consistent
    have runQ := executable_of_path A label q C rfl consistent
    exact ⟨fun equivalent => configOf_eq_of_roundEquiv A label equivalent fragmentP.static,
      roundEquiv_of_configOf_eq A label runP runQ fragmentP fragmentQ⟩
  · rw [sites_eq_nil_of_inconsistent A label p C rfl consistent,
      sites_eq_nil_of_inconsistent A label q C rfl consistent]
    exact ⟨fun _ => rfl, fun _ => .refl _⟩

/-! ### The clean fragment: without predicate queries a configuration is a set -/

omit [DecidableEq O] in
theorem not_beforeOf_of_queryFree {w : List (Firing T S O)} (queryFree : ∀ f ∈ w, f.queries = [])
    (x y : Firing T S O) : ¬ beforeOf label w x y := by
  rintro ⟨precedes, ⟨σ, query, member, _⟩ | ⟨σ, query, member, _⟩⟩
  · rw [queryFree y precedes.mem_right] at member
    cases member
  · rw [queryFree x precedes.mem_left] at member
    cases member

/-- **Without predicate queries, the trace is the set of firings.** Two runs of the fragment
whose firings have no predicate queries are one trace exactly when they fire the same firings:
the occurrence identities carry every cause. -/
theorem queryFree_roundEquiv_iff_perm {C : Configuration T O} {w w' : List (Firing T S O)}
    (run : Executable A label C w) (run' : Executable A label C w')
    (fragment : Fragment C w) (fragment' : Fragment C w') (queryFree : ∀ f ∈ w, f.queries = []) :
    RoundEquiv A label C w w' ↔ w.Perm w' := by
  refine ⟨RoundEquiv.perm A label, fun perm => ?_⟩
  refine roundEquiv_of_configOf_eq A label run run' fragment fragment' (Config.ext ?_ ?_)
  · ext f
    rw [mem_configOf_firings, mem_configOf_firings]
    exact perm.mem_iff
  · funext x y
    apply propext
    rw [configOf_before, configOf_before]
    exact iff_of_false (not_beforeOf_of_queryFree label queryFree x y)
      (not_beforeOf_of_queryFree label (fun f hf => queryFree f (perm.mem_iff.mpr hf)) x y)

end Correspondence

/-! ## The end of a run is a function of its configuration -/

section Ends

variable (A : SubstitutionAction T S) (label : O → T)

open Classical in
/-- The configuration a configuration of firings leaves: the start's equations with every
firing's, and the occurrences present after the firings. -/
noncomputable def endOf (C : Configuration T O) (X : Config T S O) : Configuration T O :=
  ⟨C.equations ++ X.firings.toList.flatMap (Firing.added label), presentAfter C X.firings⟩

omit [DecidableEq O] in
theorem models_flatMap_added (σ : S) (l : List (Firing T S O)) :
    A.Models σ (l.flatMap (Firing.added label)) ↔ ∀ f ∈ l, A.Models σ (f.added label) := by
  constructor
  · intro solved f member e inAdded
    exact solved e (List.mem_flatMap.mpr ⟨f, member, inAdded⟩)
  · intro solved e member
    obtain ⟨f, inList, inAdded⟩ := List.mem_flatMap.mp member
    exact solved f inList e inAdded

/-- **The occurrences a run leaves are those its configuration leaves.** -/
theorem follow_present_eq : ∀ {C : Configuration T O} {w : List (Firing T S O)},
    Executable A label C w → Fragment C w →
      (follow label C w).present = presentAfter C (configOf label w).firings
  | C, [], _, _ => by
      classical
      ext o
      rw [mem_presentAfter]
      simp [configOf, follow]
  | C, f :: w, run, fragment => by
      classical
      have later := follow_present_eq run.2 (fragment.tail label)
      change (follow label (f.result label C) w).present = _
      rw [later, presentAfter_result label]
      · congr 1
        ext g
        rw [Finset.mem_insert, mem_configOf_firings, mem_configOf_firings, List.mem_cons]
      · intro o taken
        refine ⟨fun made => made_absent A label run.1 made (taken_present A label run.1 taken),
          fun g hg made => ?_⟩
        exact fragment.fresh g (List.mem_cons_of_mem _ (mem_configOf_firings.mp hg)) o made
          (taken_present A label run.1 taken)

/-- **A run of the fragment ends where its configuration does**, up to solutions. -/
theorem follow_sameUpTo_endOf {C : Configuration T O} {w : List (Firing T S O)}
    (run : Executable A label C w) (fragment : Fragment C w) :
    GuardFreeProcessOrders.SameUpTo A (follow label C w) (endOf label C (configOf label w)) := by
  classical
  refine ⟨fun σ => ?_, follow_present_eq A label run fragment⟩
  change A.Models σ (follow label C w).equations ↔
    A.Models σ (C.equations ++ (configOf label w).firings.toList.flatMap (Firing.added label))
  rw [follow_equations, A.models_append, A.models_append, models_flatMap_added A label,
    models_flatMap_added A label]
  refine and_congr Iff.rfl (forall_congr' fun f => imp_congr ?_ Iff.rfl)
  rw [Finset.mem_toList, mem_configOf_firings]

end Ends

#print axioms precedes_swap_iff
#print axioms traceEquiv_of_ordered
#print axioms exists_minimal
#print axioms staticIndependent_of_parts
#print axioms valid_of_parts
#print axioms precedes_of_flow
#print axioms precedes_of_readBeforeTake
#print axioms not_takeConflict
#print axioms config_eq_of_events_eq
#print axioms presentAfter_result
#print axioms queries_hold_of_run
#print axioms configOf_isConfiguration
#print axioms not_inhibitionPair_of_round
#print axioms configOf_eq_of_roundEquiv
#print axioms staticTraceEquiv_of_configOf_eq
#print axioms roundEquiv_of_configOf_eq
#print axioms roundEquiv_iff_staticTraceEquiv
#print axioms exists_run
#print axioms roundEquiv_iff_events_eq
#print axioms configuration_bijective
#print axioms trace_eq_iff_configOf_eq
#print axioms queryFree_roundEquiv_iff_perm
#print axioms follow_present_eq
#print axioms follow_sameUpTo_endOf

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunEvents
