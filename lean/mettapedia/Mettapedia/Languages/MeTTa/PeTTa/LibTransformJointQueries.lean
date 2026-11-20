import Mettapedia.Languages.MeTTa.PeTTa.LibTransformPredicateQueries
import Mettapedia.Languages.MeTTa.PeTTa.LibTransformAbsent

/-!
# Conditions over joint matches are reads with one predicate query for each pattern

`absent`, `unique` and `collect` of a conjunction `(, p1 ... pn)` range over its joint
matches: a match of `p1`, then a match of `p2` under its bindings, and so on. No single
predicate on stored atoms says "takes part in a joint match", because the parts share
variables. What the ordered-store step can observe is, for each pattern, all the occurrences
whose atom the pattern meets (a read request with its predicate query). This module shows
that this is enough.

* `rel_weaken`, `meets_of_match`: a match under some bindings is a match under fewer; so a
  row matched in the course of a joint match is among the rows its pattern meets alone.
* `jointIn_observed`: the joint matches in a store are the joint matches computed from one
  list for each pattern, the rows of the store that the pattern meets (`jointOf`).
* `joint_read_queries`: over distinct occurrences the step admits the read request with its
  predicate query for every pattern, and the model's joint matches are `jointOf` of what
  those requests read. `joint_reads_run`: those requests in order are a run of the step
  that leaves the state as it is.
* `walk_absent_reads`, `walk_unique_reads`, `collected_read_reads`,
  `walk_collect_read_reads`: the model's `absent`, `unique` and read-mode `collect`
  conjuncts, at any place among other conjuncts and under any bindings, decided from those
  reads.
* `collect_take_joint_query`: `(collect (take (, p1 ... pn)) C)` leaves the store that one
  removal request leaves, whose predicate query is "the atom takes part in a kept tuple";
  `keptTuples_observed`: the kept tuples depend only on the rows some pattern meets.

Positive and negative examples: `Controls.joint_match_from_reads` (two rows that agree on the
shared variable are one joint match), `Controls.parts_present_joint_absent` (each pattern
reads a row, and there is no joint match: the absence of the conjunction holds where the
absence of neither part does).

Not here: stores with atoms that hold variables (the model's matching is one-way).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.LibTransformStep

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK
  (Subst matchAtom MatchAtomRel matchAtom_sound matchAtom_complete)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled)
open Interface
open Mettapedia.Languages.MeTTa.ContextualTransform
open PeTTaStoreSelection (atomFrames)
open LibTransform

/-! ## A match under fewer bindings -/

/-- **A match under some bindings is a match under fewer.** When `σ` extends `σ₀`, a pattern
that matches under `σ` matches under `σ₀`, and the bindings it gives extend those. -/
theorem rel_weaken {σ τ : Subst} {p c : Atom} (h : MatchAtomRel σ p c τ) :
    ∀ {σ₀ : Subst}, Subst.lookupExtends σ σ₀ →
      ∃ τ₀, MatchAtomRel σ₀ p c τ₀ ∧ Subst.lookupExtends τ τ₀ := by
  induction h with
  | @var_fresh σ v a fresh =>
      intro σ₀ ext
      have fresh₀ : Subst.lookup σ₀ v = none := by
        cases found : Subst.lookup σ₀ v with
        | none => rfl
        | some b =>
            rw [ext v b found] at fresh
            cases fresh
      refine ⟨(v, a) :: σ₀, .var_fresh fresh₀, ?_⟩
      intro w b found
      rw [lookup_cons] at found ⊢
      by_cases same : v = w
      · rw [if_pos same] at found ⊢
        exact found
      · rw [if_neg same] at found ⊢
        exact ext w b found
  | @var_bound σ v a bound =>
      intro σ₀ ext
      cases found : Subst.lookup σ₀ v with
      | none =>
          refine ⟨(v, a) :: σ₀, .var_fresh found, ?_⟩
          intro w b stored
          rw [lookup_cons] at stored
          by_cases same : v = w
          · rw [if_pos same] at stored
            cases stored
            rw [← same]
            exact bound
          · rw [if_neg same] at stored
            exact ext w b stored
      | some b =>
          have equal : b = a := by
            have inherited := ext v b found
            rw [bound] at inherited
            exact (Option.some.inj inherited).symm
          subst equal
          exact ⟨σ₀, .var_bound found, ext⟩
  | symbol => intro σ₀ ext; exact ⟨σ₀, .symbol, ext⟩
  | grounded => intro σ₀ ext; exact ⟨σ₀, .grounded, ext⟩
  | expr_nil => intro σ₀ ext; exact ⟨σ₀, .expr_nil, ext⟩
  | expr_cons _ _ head tail =>
      intro σ₀ ext
      obtain ⟨σ₁, first, ext₁⟩ := head ext
      obtain ⟨τ₀, rest, ext₂⟩ := tail ext₁
      exact ⟨τ₀, .expr_cons first rest, ext₂⟩

/-- A row a pattern matches under some bindings is a row the pattern meets alone. -/
theorem meets_of_match {σ τ : Subst} {p c : Atom} (matched : matchAtom σ p c = some τ) :
    meets p c = true := by
  obtain ⟨τ₀, rel, -⟩ := rel_weaken (matchAtom_sound matched) (σ₀ := [])
    (by intro v a found; simp [Subst.lookup] at found)
  simp [meets, matchAtom_complete rel]

/-- Matching a pattern in a store meets only the rows the pattern meets alone. -/
theorem matchesIn_observed (s : Store) (σ : Subst) (p : Atom) :
    matchesIn (s.filter (meets p)) σ p = matchesIn s σ p := by
  unfold matchesIn
  rw [List.filterMap_filter]
  apply List.filterMap_congr
  intro b _
  cases matched : matchAtom σ p b with
  | none => simp
  | some τ => simp [meets_of_match matched]

/-! ## Joint matches from one list of rows for each pattern -/

/-- The joint matches of patterns each given its own list of rows: a match of the first
pattern in its rows, then a match of the second in its rows under those bindings, and so
on. -/
def jointOf : Subst → List (Atom × Store) → List (Subst × List Atom)
  | σ, [] => [(σ, [])]
  | σ, (p, rows) :: more =>
      (matchesIn rows σ p).flatMap fun r => (jointOf r.1 more).map fun t => (t.1, r.2 :: t.2)

/-- **The joint matches in a store are those of the rows each pattern meets alone.** -/
theorem jointIn_observed (s : Store) : ∀ (ps : List Atom) (σ : Subst),
    jointIn s σ ps = jointOf σ (ps.map fun p => (p, s.filter (meets p)))
  | [], _ => rfl
  | p :: ps, σ => by
      simp only [jointIn, List.map_cons, jointOf, matchesIn_observed, jointIn_observed s ps]

/-! ## The reads of the step -/

section Step

variable {O : Type} [DecidableEq O] (label : O → Atom)

/-- What the read request with the predicate query of `p` reads, as atoms. -/
theorem read_observes (p : Atom) (rows : List O) :
    (readMatches label p rows).selection.read.map label = (rows.map label).filter (meets p) := by
  show (rows.filter fun occurrence => meets p (label occurrence)).map label = _
  simp [List.filter_map, Function.comp_def]

/-- For each pattern, the atoms its read request with its predicate query reads. -/
def observations (rows : List O) (ps : List Atom) : List (Atom × Store) :=
  ps.map fun p => (p, (readMatches label p rows).selection.read.map label)

/-- The model's joint matches, from the reads. -/
theorem jointIn_reads (rows : List O) (ps : List Atom) (σ : Subst) :
    jointIn (rows.map label) σ ps = jointOf σ (observations label rows ps) := by
  rw [jointIn_observed, observations]
  congr 1
  apply List.map_congr_left
  intro p _
  rw [read_observes]

/-- **Joint matches are a function of one read with its predicate query for each pattern.**
Over distinct occurrences the step admits each of those read requests, and the model's joint
matches under any bindings are the joint matches of what the requests read. -/
theorem joint_read_queries (rows : List O) (unique : rows.Nodup) (ps : List Atom) (σ : Subst)
    (knowledge : EquationStore Atom)
    (consistent : atomFrames.Solvable (a := PUnit.unit) knowledge) :
    (∀ p ∈ ps, (OrderedStore.step atomFrames PUnit.unit label).Admits
        (s := (knowledge, rows)) (readMatches label p rows)) ∧
      jointIn (rows.map label) σ ps = jointOf σ (observations label rows ps) :=
  ⟨fun p _ => (StoreOperations.read_admits_exact atomFrames PUnit.unit label (meets p)
      knowledge rows).mpr ⟨unique, consistent⟩,
    jointIn_reads label rows ps σ⟩

/-- **The reads of the patterns, in order, are a run of the step that leaves the state as it
is.** -/
theorem joint_reads_run (rows : List O) (unique : rows.Nodup) (knowledge : EquationStore Atom)
    (consistent : atomFrames.Solvable (a := PUnit.unit) knowledge) :
    ∀ (ps : List Atom) (state : EquationStore Atom × List O), state = (knowledge, rows) →
      ∃ run : (OrderedStore.step atomFrames PUnit.unit label).Run state,
        run.word.map (fun firing => (firing.2 : OrderedStore.Publication Atom O)) =
          ps.map (fun p => readMatches label p rows) ∧
        run.last = (knowledge, rows)
  | [], _, rfl => ⟨.nil _, rfl, rfl⟩
  | p :: ps, _, rfl => by
      have admitted := (StoreOperations.read_admits_exact atomFrames PUnit.unit label (meets p)
        knowledge rows).mpr ⟨unique, consistent⟩
      obtain ⟨run, word, last⟩ := joint_reads_run rows unique knowledge consistent ps _
        (StoreOperations.read_store_unchanged atomFrames PUnit.unit label (meets p) knowledge rows
          admitted)
      exact ⟨.cons (readMatches label p rows) admitted run,
        congrArg (List.cons (readMatches label p rows)) word, last⟩

/-! ## The model's conjuncts, decided from the reads -/

/-- **`(absent q)` among other conjuncts**: it lets the walk go on exactly when the reads of
its patterns have no joint match under the bindings so far. -/
theorem walk_absent_reads (rows : List O) (firing : Bool) (σ : Subst) (q : Query)
    (cs : List Conj) :
    walk (rows.map label) firing σ (.absent q :: cs) =
      if jointOf σ (observations label rows q.parts) = [] then
        walk (rows.map label) firing σ cs
      else [] := by
  simp only [walk, jointIn_reads]

/-- **`(unique c)` among other conjuncts**: its one row is the one joint match of the reads of
its patterns, when there is exactly one. -/
theorem walk_unique_reads (rows : List O) (firing : Bool) (σ : Subst) (m : Mode) (q : Query)
    (cs : List Conj) :
    walk (rows.map label) firing σ (.unique m q :: cs) =
      match jointOf σ (observations label rows q.parts) with
      | [t] =>
          (walk (rows.map label) firing t.1 cs).map fun w =>
            (w.1, t.2.map (fun a => (m, a)) ++ w.2)
      | _ => [] := by
  simp only [walk, jointIn_reads]
  generalize jointOf σ (observations label rows q.parts) = found
  rcases found with _ | ⟨t, _ | ⟨u, rest⟩⟩ <;> rfl

/-- **A read-mode `collect`** collects the joint matches of the reads of its patterns. -/
theorem collected_read_reads (rows : List O) (σ : Subst) (q : Query) :
    collected (rows.map label) σ .read q = jointOf σ (observations label rows q.parts) := by
  rw [collected_eq_jointIn (Or.inl rfl), jointIn_reads]

/-- **A read-mode `collect` among other conjuncts**: the collection of the reads' joint matches
is matched against its pattern, and the walk goes on under the bindings that gives. -/
theorem walk_collect_read_reads (rows : List O) (firing : Bool) (σ : Subst) (q : Query)
    (c : Atom) (cs : List Conj) :
    walk (rows.map label) firing σ (.collect .read q c :: cs) =
      match matchAtom σ c
          (q.collection ((jointOf σ (observations label rows q.parts)).map Prod.snd)) with
      | none => []
      | some τ => walk (rows.map label) firing τ cs := by
  simp only [walk, collected_read_reads, collectTakes_read, List.nil_append]
  generalize matchAtom σ c
    (q.collection ((jointOf σ (observations label rows q.parts)).map Prod.snd)) = found
  cases found with
  | none => rfl
  | some τ => simp

/-! ## The joint take -/

/-- "The atom takes part in a kept joint tuple of `ps`", the predicate of the removal's
query. -/
def takesPart (s : Store) (ps : List Atom) (atom : Atom) : Bool :=
  decide (atom ∈ (keptTuples s ps).flatten)

/-- **`(collect (take (, p1 ... pn)) C)` is one removal with its predicate query.** The step
admits the removal request for the atoms that take part in a kept tuple; the model's
transform leaves the labels of the step's rows after it and answers the template with `C`
bound to the kept tuples. -/
theorem collect_take_joint_query (rows : List O) (unique : rows.Nodup) (ps : List Atom)
    (template : Atom) (C : String) (knowledge : EquationStore Atom)
    (consistent : atomFrames.Solvable (a := PUnit.unit) knowledge) :
    ∃ admitted : (OrderedStore.step atomFrames PUnit.unit label).Admits
        (s := (knowledge, rows))
        (StoreOperations.removeRequest (Tm := fun _ : PUnit.{1} => Atom) (a := PUnit.unit) label
          (takesPart (rows.map label) ps) rows),
      (transform (collectTakeJoint ps C) template (rows.map label)).drain =
        (instances template
            [(C, (Query.conj ps).collection (keptTuples (rows.map label) ps))],
          ((OrderedStore.step atomFrames PUnit.unit label).result
            (StoreOperations.removeRequest (Tm := fun _ : PUnit.{1} => Atom) (a := PUnit.unit)
              label (takesPart (rows.map label) ps) rows) admitted).2.map label) := by
  have admitted := (StoreOperations.remove_admits_exact atomFrames PUnit.unit label
    (takesPart (rows.map label) ps) knowledge rows).mpr ⟨unique, consistent⟩
  refine ⟨admitted, ?_⟩
  have left := StoreOperations.remove_all_correspondence atomFrames PUnit.unit label
    (takesPart (rows.map label) ps) knowledge rows admitted
  rw [transform_collect_take_joint]
  refine Prod.ext rfl ?_
  have rowsLeft := congrArg Prod.fst left
  simpa [StoreAndDemand.StoreEffects.removeAll, takesPart] using rowsLeft

end Step

/-! ## The kept tuples depend only on the rows some pattern meets -/

/-- "Some pattern of `ps` meets the atom." -/
def anyMeets (ps : List Atom) (atom : Atom) : Bool := ps.any fun p => meets p atom

theorem filter_meets_of_any (s : Store) {ps : List Atom} {p : Atom} (member : p ∈ ps) :
    (s.filter (anyMeets ps)).filter (meets p) = s.filter (meets p) := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro atom _
  by_cases met : meets p atom = true
  · have any : anyMeets ps atom = true := List.any_eq_true.mpr ⟨p, member, met⟩
    simp [met, any]
  · simp [met]

/-- The joint matches depend only on the rows some pattern meets. -/
theorem jointIn_any (s : Store) (ps : List Atom) (σ : Subst) :
    jointIn (s.filter (anyMeets ps)) σ ps = jointIn s σ ps := by
  rw [jointIn_observed, jointIn_observed]
  congr 1
  apply List.map_congr_left
  intro p member
  rw [filter_meets_of_any s member]

/-- Every atom of a joint tuple is met by one of the patterns. -/
theorem tuple_met (s : Store) : ∀ (ps : List Atom) (σ : Subst) (t : Subst × List Atom),
    t ∈ jointIn s σ ps → ∀ atom ∈ t.2, anyMeets ps atom = true
  | [], _, t, member, atom, inTuple => by
      simp only [jointIn, List.mem_singleton] at member
      subst member
      cases inTuple
  | p :: ps, σ, t, member, atom, inTuple => by
      simp only [jointIn, List.mem_flatMap, List.mem_map] at member
      obtain ⟨r, matched, rest, inRest, rfl⟩ := member
      rcases List.mem_cons.mp inTuple with rfl | later
      · have met := meets_of_match (mem_matchesIn.mp matched).2
        exact List.any_eq_true.mpr ⟨p, List.mem_cons_self, met⟩
      · obtain ⟨q, inPs, met⟩ := List.any_eq_true.mp (tuple_met s ps r.1 rest inRest atom later)
        exact List.any_eq_true.mpr ⟨q, List.mem_cons_of_mem _ inPs, met⟩

theorem all_congr_mem {α : Type} (l : List α) (f g : α → Bool)
    (same : ∀ a ∈ l, f a = g a) : l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      simp only [List.all_cons, same a List.mem_cons_self,
        ih fun b member => same b (List.mem_cons_of_mem _ member)]

/-- **The kept tuples of a joint take depend only on the rows some pattern meets**: whether a
tuple fits counts copies of its own atoms, each of which a pattern meets. -/
theorem keptTuples_observed (s : Store) (ps : List Atom) :
    keptTuples (s.filter (anyMeets ps)) ps = keptTuples s ps := by
  simp only [keptTuples, collected, jointIn_any]
  congr 1
  apply List.filter_congr
  intro t member
  simp only [fits]
  apply all_congr_mem
  intro atom inTuple
  rw [List.count_filter (tuple_met s ps [] t member atom inTuple)]

/-! ## Candidate order on a fixed physical view -/

/-- Traversing the same rows in a different order preserves every joint
binding/tuple occurrence, including duplicates. -/
theorem jointIn_perm {s t : Store} (order : s.Perm t) :
    ∀ (ps : List Atom) (σ : Subst), (jointIn s σ ps).Perm (jointIn t σ ps)
  | [], _ => .refl _
  | p :: ps, σ => by
    have selected : (matchesIn s σ p).Perm (matchesIn t σ p) := order.filterMap _
    exact (selected.flatMap_right _).trans
      (List.Perm.flatMap_left _ fun row _ => (jointIn_perm order ps row.1).map _)

/-- Absence and uniqueness are stable under traversal reordering. An authored
`collect` is excluded because its ordered result can be a later pattern. -/
theorem walk_perm_of_no_collect {s t : Store} (order : s.Perm t) (firing : Bool) :
    ∀ (cs : List Conj) (σ : Subst),
      (∀ m q c, Conj.collect m q c ∉ cs) →
      (walk s firing σ cs).Perm (walk t firing σ cs)
  | [], _, _ => .refl _
  | c :: cs, σ, noCollect => by
    have tail (τ : Subst) := walk_perm_of_no_collect order firing cs τ
      (fun m q value member => noCollect m q value (List.mem_cons_of_mem c member))
    cases c with
    | pat m p =>
        have selected : (matchesIn s σ p).Perm (matchesIn t σ p) := order.filterMap _
        exact (selected.flatMap_right _).trans
          (List.Perm.flatMap_left _ fun row _ => (tail row.1).map _)
    | absent q =>
        have same := jointIn_perm order q.parts σ
        have empty : (jointIn s σ q.parts = []) = (jointIn t σ q.parts = []) :=
          propext ⟨fun e => (e ▸ same).nil_eq.symm, fun e => (e ▸ same).eq_nil⟩
        simp only [walk, empty]
        split
        · exact tail σ
        · rfl
    | unique m q =>
        have same := jointIn_perm order q.parts σ
        cases selected : jointIn s σ q.parts with
        | nil =>
            have none : jointIn t σ q.parts = [] := (selected ▸ same).nil_eq.symm
            simp [walk, selected, none]
        | cons row rest =>
            cases rest with
            | nil =>
                have singleton : jointIn t σ q.parts = [row] := (selected ▸ same).singleton_eq.symm
                simpa only [walk, selected, singleton] using (tail row.1).map
                  (fun w => (w.1, row.2.map (fun a => (m, a)) ++ w.2))
            | cons next remaining =>
                cases other : jointIn t σ q.parts with
                | nil => simp [selected, other] at same
                | cons first rest =>
                    cases rest with
                    | nil => simp [selected, other] at same
                    | cons second more => simp [walk, selected, other]
    | collect m q value => exact absurd List.mem_cons_self (noCollect m q value)
    | as p a =>
        simp only [walk]
        split
        · rfl
        · exact tail _

/-- For a fixed guide with no order-observing collection in its search,
reordering the store enumeration cannot turn success into refusal. It may
change which valid witness a first-valid policy selects. -/
theorem fire_admitted_perm_of_no_collect {s t : Store} (order : s.Perm t)
    (g : Footprint) (src : Sources) {A : Type} (emit : Subst → List A)
    (kernel : ∀ m q c, Conj.collect m q c ∉ guided src.kernel g ++ src.choice)
    (extension : ∀ ext, src.every = some ext → ∀ m q c, Conj.collect m q c ∉ ext) :
    (LibTransform.fire s g src emit).isSome = (LibTransform.fire t g src emit).isSome := by
  have verdict {first second : Store} (perm : first.Perm second)
      (c d : Candidate) (sameKernel : c.kernel = d.kernel)
      (sameRows : c.rows.Perm d.rows) :
      valid first c.footprint = true ↔ valid second d.footprint = true := by
    have footprint : c.footprint.Perm d.footprint := by
      simp only [Candidate.footprint, sameKernel]
      exact (sameRows.flatMap_right Prod.snd).append_left _
    have takesSame : (takes c.footprint).Perm (takes d.footprint) := footprint.filterMap _
    have readsSame : (reads c.footprint).Perm (reads d.footprint) := footprint.filterMap _
    have takeCounts (a : Atom) : (takes c.footprint).count a = (takes d.footprint).count a :=
      takesSame.count_eq a
    have tmem (a : Atom) : a ∈ takes c.footprint ↔ a ∈ takes d.footprint := takesSame.mem_iff
    have rmem (a : Atom) : (a ∈ reads c.footprint) = (a ∈ reads d.footprint) :=
      propext readsSame.mem_iff
    rw [valid_iff, valid_iff]
    simp only [takeCounts, rmem, perm.count_eq, tmem]
  have forward {first second : Store} (perm : first.Perm second)
      (admitted : (LibTransform.fire first g src emit).isSome = true) :
      (LibTransform.fire second g src emit).isSome = true := by
    simp only [LibTransform.fire, Option.isSome_map, List.find?_isSome] at admitted ⊢
    obtain ⟨c, generated, ok⟩ := admitted
    obtain ⟨row, inFirst, rfl⟩ := List.mem_map.mp generated
    have inSecond := (walk_perm_of_no_collect perm true _ [] kernel).mem_iff.mp inFirst
    let packet (store : Store) : Candidate :=
      ⟨row.2, match src.every with
        | none => [(row.1, [])]
        | some ext => walk store true row.1 ext⟩
    have sameRows : (packet first).rows.Perm (packet second).rows := by
      cases ext : src.every with
      | none => simp [packet, ext]
      | some other =>
          simpa only [packet, ext] using walk_perm_of_no_collect perm true other row.1 (extension other ext)
    exact ⟨packet second, List.mem_map.mpr ⟨row, inSecond, rfl⟩,
      (verdict perm (packet first) (packet second) rfl sameRows).mp ok⟩
  exact Bool.eq_iff_iff.mpr ⟨forward order, forward order.symm⟩

private theorem guided_no_collect :
    ∀ (cs : List Conj) (guide : Footprint), (∀ m q c, Conj.collect m q c ∉ cs) →
      ∀ m q c, Conj.collect m q c ∉ guided cs guide
  | [], _, _, _, _, _ => List.not_mem_nil
  | head :: tail, guide, noCollect, m, q, c => by
    have tailClean : ∀ m q c, Conj.collect m q c ∉ tail :=
      fun use query pattern member => noCollect use query pattern (List.mem_cons_of_mem head member)
    cases head with
    | pat use pattern =>
        cases guide with
        | nil => simpa [guided] using guided_no_collect tail [] tailClean m q c
        | cons selected rest =>
            obtain ⟨mode, atom⟩ := selected
            simpa [guided] using guided_no_collect tail rest tailClean m q c
    | unique use query =>
        have gone := guided_no_collect tail (guide.drop query.parts.length) tailClean m q c
        simp [guided, asParts, List.mem_map, gone]
    | absent query => simpa [guided] using guided_no_collect tail guide tailClean m q c
    | collect use query pattern => exact absurd List.mem_cons_self (noCollect use query pattern)
    | as pattern atom => simpa [guided] using guided_no_collect tail guide tailClean m q c

/-- Reordering the complete proposal scan preserves the existence of a
commit, including a successful commit that emits no answers. This does not
reorder a sequence of commits on changing worlds. -/
theorem fireFirst_admitted_perm_of_no_collect {s t : Store} (order : s.Perm t)
    (src : Sources) {A : Type} (emit : Subst → List A)
    (kernel : ∀ m q c, Conj.collect m q c ∉ src.kernel)
    (choice : ∀ m q c, Conj.collect m q c ∉ src.choice)
    (extension : ∀ ext, src.every = some ext → ∀ m q c, Conj.collect m q c ∉ ext) :
    (fireFirst s src emit).isSome = (fireFirst t src emit).isSome := by
  have transport {first second : Store} (perm : first.Perm second) :
      (fireFirst first src emit).isSome = true → (fireFirst second src emit).isSome = true := by
    simp only [fireFirst, List.findSome?_isSome_iff]
    rintro ⟨guide, member, fired⟩
    have scanned : (proposals first src).Perm (proposals second src) :=
      (walk_perm_of_no_collect perm false src.kernel [] kernel).map Prod.snd
    refine ⟨guide, scanned.mem_iff.mp member, ?_⟩
    rw [← fire_admitted_perm_of_no_collect perm guide src emit
      (fun m q c => by
        simp [List.mem_append, guided_no_collect src.kernel guide kernel m q c, choice m q c]) extension]
    exact fired
  exact Bool.eq_iff_iff.mpr ⟨transport order, transport order.symm⟩

namespace Controls

/-- Rows 0 and 1 hold `(p a)` and `(q a)`. -/
def agreeing : Nat → Atom
  | 0 => .expression [.symbol "p", .symbol "a"]
  | _ => .expression [.symbol "q", .symbol "a"]

/-- Rows 0 and 1 hold `(p a)` and `(q b)`. -/
def disagreeing : Nat → Atom
  | 0 => .expression [.symbol "p", .symbol "a"]
  | _ => .expression [.symbol "q", .symbol "b"]

/-- The conjunction `(, (p $x) (q $x))`, as its parts. -/
def shared : List Atom :=
  [.expression [.symbol "p", .var "x"], .expression [.symbol "q", .var "x"]]

/-- Positive: each pattern reads one row, the two agree on the shared variable, and the reads
have one joint match. -/
theorem joint_match_from_reads :
    jointOf [] (observations agreeing [0, 1] shared) =
      [([("x", .symbol "a")],
        [.expression [.symbol "p", .symbol "a"], .expression [.symbol "q", .symbol "a"]])] := by
  decide

/-- Negative: each pattern reads one row, so the absence of neither part holds, and the reads
have no joint match: the absence of the conjunction holds. -/
theorem parts_present_joint_absent :
    (observations disagreeing [0, 1] shared).map (fun observed => observed.2.length) = [1, 1] ∧
      jointOf [] (observations disagreeing [0, 1] shared) = [] ∧
      walk ([0, 1].map disagreeing) false [] [.absent (.conj shared)] = [([], [])] := by
  refine ⟨by decide, by decide, ?_⟩
  rw [walk_absent_reads]
  decide

private def edge (left right : Atom) : Atom := .expression [.symbol "edge", left, right]
private def blocked (node : Atom) : Atom := .expression [.symbol "blocked", node]

private def guardedRows : Store :=
  [edge a b, edge b (.symbol "c"), blocked b, edge a (.symbol "d"), edge (.symbol "d") (.symbol "c")]

private def unguardedPair : List Conj :=
  [.pat .take (edge a (.var "mid")), .pat .take (edge (.var "mid") (.symbol "c"))]

private def routeGuard : Conj := .absent (.one (blocked (.var "mid")))
private def guardedPair : Sources := ⟨[], unguardedPair ++ [routeGuard], none⟩
private def emitMid : Subst → Answers := instances (.var "mid")

/-- Testing the first joined candidate would refuse, although there is a
valid guarded pair. The real search takes both edges of that pair together. -/
theorem bad_first_candidate_does_not_block_the_later_pair :
    ((candidates guardedRows [] ⟨[], unguardedPair, none⟩).head?.map fun candidate =>
      (candidate.instances emitMid, valid guardedRows candidate.footprint,
        candidate.rows.any fun row => !(walk guardedRows true row.1 [routeGuard]).isEmpty)) =
      some ([b], true, false) ∧
    LibTransform.fire guardedRows [] guardedPair emitMid =
      some ([edge a b, edge b (.symbol "c"), blocked b], [.symbol "d"]) := by
  decide +kernel

/-- If no guarded pair exists, the library neither consumes the first edge
nor reroutes an answer from a partial join. -/
theorem blocked_pair_cannot_consume_an_edge :
    let rows := [edge a b, edge b (.symbol "c"), blocked b]
    firing guardedPair emitMid [] rows = .done rows := by
  rfl

private def numberedGuardedRow (n : Nat) : Atom :=
  guardedRows[n]?.getD (.symbol "outside")

/-- The concrete result has a single enabled occurrence commit with exactly
two distinct takes, both drawn from the same space. -/
theorem guarded_pair_has_one_two_take_commit :
    ∃ selection : Selection Nat,
      selection.taken.Nodup ∧ selection.taken.map numberedGuardedRow =
        [edge a (.symbol "d"), edge (.symbol "d") (.symbol "c")] ∧
      Enabled numberedGuardedRow {0, 1, 2, 3, 4} (selection.commit (T := Atom)) := by
  have starts : Represents numberedGuardedRow [0, 1, 2, 3, 4] guardedRows := ⟨by decide, rfl⟩
  obtain ⟨candidate, member, selection, _, real, enabled, _, _, _, _⟩ :=
    fire_publishes starts bad_first_candidate_does_not_block_the_later_pair.2
  have footprints : (candidates guardedRows [] guardedPair).map (fun c => takes c.footprint) =
      [[edge a (.symbol "d"), edge (.symbol "d") (.symbol "c")]] := by decide +kernel
  have found := List.mem_map_of_mem (f := fun c => takes c.footprint) member
  rw [footprints, List.mem_singleton] at found
  exact ⟨selection, real.taken_distinct, real.taken_labels.trans found, enabled⟩

/-- With both pairs allowed, the reordered search still commits but can
choose the other pair and leave a different store. -/
theorem traversal_can_change_the_committed_pair :
    let src : Sources := ⟨[], unguardedPair, none⟩
    fireFirst guardedRows src emitMid =
      some ([blocked b, edge a (.symbol "d"), edge (.symbol "d") (.symbol "c")], [b]) ∧
    fireFirst guardedRows.reverse src emitMid =
      some ([blocked b, edge b (.symbol "c"), edge a b], [.symbol "d"]) := by
  decide +kernel

/-- A reordering law for guards cannot silently quotient an authored
collection that is itself compared with ordered data. -/
theorem ordered_collection_can_change_admission :
    let src : Sources := ⟨[.collect .read (.one (.var "item")) (.expression [a, b])], [], none⟩
    ([a, b] : Store).Perm [b, a] ∧
      (LibTransform.fire [a, b] [] src emitMid).isSome = true ∧
      (LibTransform.fire [b, a] [] src emitMid).isSome = false := by
  exact ⟨List.Perm.swap .., by decide +kernel, by decide +kernel⟩

end Controls

end Mettapedia.Languages.MeTTa.PeTTa.LibTransformStep
