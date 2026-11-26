import Mettapedia.Machines.TIsa.Derivation.Semantics

/-!
# The evaluator against the step theory

A store is a state of the step theory at one frame (`Semantics.state`): no knowledge, its identities
present, each labelled by its value. A firing of the evaluator is a firing of
`RuleSyntax.step (frames A) ℕ (ext A)` with the identity opening (`stepFiring`).

* **Soundness** (`admits_stepFiring`): every firing the evaluator finds is admitted by the step
  theory, with any fresh made identities, and its result, read through any solution of its
  knowledge, is the published store.
* **Completeness** (`firing_of_admits`): every admitted firing of the step theory, with any fresh
  opening and any fresh made identities, is found by the evaluator with the same rule, the same
  taken and read occurrences and the same seen sets, and reads as the same published store. This
  needs range restriction (`RangeRestricted`): after its premises, a rule's other terms
  instantiate.
* **The step relation** (`groundStep_iff`): `GroundStep`, the step theory's admission followed by
  reading the result through its knowledge, is exactly a firing of the evaluator published with some
  fresh made identities. Quiescence is terminality (`firings_eq_nil_iff`).
* **Runs** (`run_quiescent_sound`, `run_exhausted_sound`): a run of the evaluator is a path of
  `GroundStep`, ending in a store with no step when it is quiescent.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.Derivation

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Interface (Frames)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled fire)
open RuleSyntax.OneFrame (Terms frames ext)

universe u s v w

variable {T : Type u} {S : Type s} {V : Type v} {B : Type w}

/-- The program of a list of rules. -/
def programOf (P : List (Rule T)) : RuleSyntax.Program (Terms T) := {r | r ∈ P}

namespace Store

variable {V : Type v}

/-- The value of an identity. -/
def valueOf (s : Store V) (o : ℕ) : Option V :=
  (s.occurrences.find? (fun x => x.1 == o)).map Prod.snd

theorem mem_ids {s : Store V} {o : ℕ} : o ∈ s.ids ↔ ∃ a, (o, a) ∈ s.occurrences := by
  simp [ids]

theorem valueOf_eq_some {s : Store V} (distinct : (s.occurrences.map Prod.fst).Nodup) {o : ℕ} {a : V} :
    s.valueOf o = some a ↔ (o, a) ∈ s.occurrences := by
  unfold valueOf
  constructor
  · intro found
    obtain ⟨x, located, rfl⟩ := Option.map_eq_some_iff.mp found
    have same : x.1 = o := by simpa using List.find?_some located
    have inside := List.mem_of_find?_eq_some located
    rw [← same]
    exact inside
  · intro inside
    cases located : s.occurrences.find? (fun x => x.1 == o) with
    | none =>
        have absent := List.find?_eq_none.mp located (o, a) inside
        simp at absent
    | some x =>
        have same : x.1 = o := by simpa using List.find?_some located
        have xInside := List.mem_of_find?_eq_some located
        have equal : x = (o, a) := List.inj_on_of_nodup_map distinct xInside inside (by simpa using same)
        simp [equal]

theorem valueOf_isSome {s : Store V} (distinct : (s.occurrences.map Prod.fst).Nodup) {o : ℕ}
    (present : o ∈ s.ids) : ∃ a, s.valueOf o = some a ∧ (o, a) ∈ s.occurrences := by
  obtain ⟨a, inside⟩ := mem_ids.mp present
  exact ⟨a, (valueOf_eq_some distinct).mpr inside, inside⟩

/-- Identities are distinct. -/
def Distinct (s : Store V) : Prop := (s.occurrences.map Prod.fst).Nodup

/-- Two stores with distinct identities, the same identities and the same values. -/
def SameOccurrences (first second : Store V) : Prop :=
  first.Distinct ∧ second.Distinct ∧ first.ids.toFinset = second.ids.toFinset ∧
    ∀ o ∈ first.ids, first.valueOf o = second.valueOf o

end Store

/-- Publication with chosen made identities. -/
def publishWith {V : Type v} {B : Type w} (s : Store V) (m : Match V B) (ids : List ℕ) : Store V :=
  ⟨s.occurrences.filter (fun x => !(m.taken.contains x.1)) ++ ids.zip m.made, s.fresh + m.made.length⟩

/-- The identities `publish` gives the made values. -/
def freshIds {V : Type v} (s : Store V) (n : ℕ) : List ℕ := (List.range n).map (s.fresh + ·)

theorem zipIdx_map_offset {α : Type v} (l : List α) (c k : ℕ) :
    (l.zipIdx k).map (fun x => (c + x.2, x.1)) = ((List.range' k l.length).map (c + ·)).zip l := by
  induction l generalizing k with
  | nil => simp
  | cons a l ih =>
      simp only [List.zipIdx_cons, List.map_cons, List.length_cons, List.range'_succ,
        List.zip_cons_cons, ih (k + 1)]

theorem publish_eq_publishWith {V : Type v} {B : Type w} (s : Store V) (m : Match V B) :
    publish s m = publishWith s m (freshIds s m.made.length) := by
  obtain ⟨occurrences, fresh⟩ := publish_occurrences s m
  cases published : publish s m with
  | mk occs next =>
      rw [published] at occurrences fresh
      simp only at occurrences fresh
      simp only [publishWith, freshIds, occurrences, fresh, Store.mk.injEq, and_true]
      congr 1
      rw [List.range_eq_range', ← zipIdx_map_offset]

/-! ## Stores as states of the step theory -/

section Adequacy

variable [DecidableEq V] [Inhabited T] {A : SubstitutionAction T S} {M : Matcher T V B}
  (Sem : Semantics A M)

/-- The label of an identity: its value, embedded. -/
def Semantics.label (s : Store V) (o : ℕ) : T := (s.valueOf o).elim default Sem.embed

/-- **A store as a state of the step theory**: no knowledge, its identities present, each
labelled by its value. -/
def Semantics.state (s : Store V) : RuleSyntax.State (Terms T) ℕ :=
  ⟨PUnit.unit, [], s.ids.toFinset, Sem.label s⟩

omit [DecidableEq V] in
/-- The firings of the step theory of a program, at the one frame. -/
abbrev StepFiring (A : SubstitutionAction T S) (P : List (Rule T)) :=
  RuleSyntax.Firing ℕ (ext A) (programOf P) PUnit.unit

omit [DecidableEq V] [Inhabited T] in
/-- **An evaluator firing as a firing of the step theory**: the rule, the identity opening, the
taken and read occurrences, the made identities and the seen sets. -/
def stepFiring (A : SubstitutionAction T S) (P : List (Rule T)) (r : Rule T)
    (member : r ∈ programOf P) (m : Match V B) (ids : List ℕ) : StepFiring A P :=
  ⟨r, member, PUnit.unit, A.identity, ⟨m.taken, m.read, ids⟩, m.seen⟩

/-- **The store a state reads as**: distinct identities, the state's present ones, and every
solution of its knowledge reads each label as the store's value. -/
def Semantics.ReadsAs (st : RuleSyntax.State (Terms T) ℕ) (s' : Store V) : Prop :=
  s'.Distinct ∧ st.present = s'.ids.toFinset ∧ ∀ σ : S, A.Models σ st.knowledge → ∀ o ∈ st.present,
    ∃ a, s'.valueOf o = some a ∧ A.E (A.apply σ (st.label o)) (Sem.embed a)

/-- **One step of the step theory on ground stores**: an admitted firing whose result reads as the
next store. -/
def Semantics.GroundStep (P : List (Rule T)) (s s' : Store V) : Prop :=
  ∃ f : StepFiring A P, f.Admits (frames A) (Sem.state s) ∧
    Sem.ReadsAs (f.result (frames A) (Sem.state s)) s'

omit [DecidableEq V] in
/-- The admission in `GroundStep` is the step's own. -/
theorem step_admits_iff (P : List (Rule T)) (s : Store V) (f : StepFiring A P) :
    (RuleSyntax.step (frames A) ℕ (ext A) (programOf P)).Admits (s := Sem.state s) f ↔
      f.Admits (frames A) (Sem.state s) := Iff.rfl

omit [DecidableEq V] in
theorem Semantics.label_of_mem {s : Store V} (distinct : (s.occurrences.map Prod.fst).Nodup)
    {o : ℕ} {a : V} (inside : (o, a) ∈ s.occurrences) : Sem.label s o = Sem.embed a := by
  simp [Semantics.label, (Store.valueOf_eq_some distinct).mpr inside]

omit [DecidableEq V] in
theorem Semantics.row_eq {P : List (Rule T)} (s : Store V) (f : StepFiring A P) (o : ℕ) :
    f.row (frames A) (Sem.state s) o = Sem.label s o :=
  A.apply_identity _

omit [DecidableEq V] in
/-- **A matching equation at a store occurrence** is the pattern's equation with the value. -/
theorem Semantics.solves_matching {P : List (Rule T)} {s : Store V}
    (distinct : (s.occurrences.map Prod.fst).Nodup) (f : StepFiring A P) {σ τ : S}
    (composite : ∀ t, A.apply σ (A.apply f.opening t) = A.apply τ t) (p : T) (x : ℕ × V)
    (inside : x ∈ s.occurrences) :
    A.E (A.apply σ (A.apply f.opening p)) (A.apply σ (f.row (frames A) (Sem.state s) x.1)) ↔
      A.E (A.apply τ p) (Sem.embed x.2) := by
  rw [composite, Sem.row_eq, Sem.label_of_mem distinct inside]
  exact Sem.to_embed_iff σ _ _

omit [DecidableEq V] in
theorem Semantics.models_matching {P : List (Rule T)} {s : Store V}
    (distinct : (s.occurrences.map Prod.fst).Nodup) (f : StepFiring A P) {σ τ : S}
    (composite : ∀ t, A.apply σ (A.apply f.opening t) = A.apply τ t) (patterns : List T)
    (xs : List (ℕ × V)) (inside : ∀ x ∈ xs, x ∈ s.occurrences) (lengths : patterns.length = xs.length) :
    (frames A).Models (a := PUnit.unit) (b := PUnit.unit) σ
        (f.matching (frames A) (Sem.state s) (patterns.map (A.apply f.opening)) (xs.map Prod.fst)) ↔
      List.Forall₂ (fun p x => A.E (A.apply τ p) (Sem.embed x.2)) patterns xs := by
  induction patterns generalizing xs with
  | nil =>
      cases xs with
      | nil => simp [RuleSyntax.Firing.matching]
      | cons _ _ => simp at lengths
  | cons p ps ih =>
      cases xs with
      | nil => simp at lengths
      | cons x xs =>
          have rest := ih xs (fun y member => inside y (List.mem_cons_of_mem _ member))
            (Nat.succ.inj lengths)
          rw [List.forall₂_cons, ← rest]
          change A.Models σ ((A.apply f.opening p, f.row (frames A) (Sem.state s) x.1) :: _) ↔ _
          rw [SubstitutionAction.models_cons]
          exact and_congr (Sem.solves_matching distinct f composite p x (inside x List.mem_cons_self))
            Iff.rfl

omit [DecidableEq V] in
/-- **The information of a firing at a store**, solved at `σ`, is the premise equations and the
tells solved at the substitution `τ` that `σ` composes with the opening. -/
theorem Semantics.models_information {P : List (Rule T)} {s : Store V}
    (distinct : (s.occurrences.map Prod.fst).Nodup) (f : StepFiring A P) (xs ys : List (ℕ × V))
    (xsIds : xs.map Prod.fst = f.selection.taken) (ysIds : ys.map Prod.fst = f.selection.read)
    (xsIn : ∀ x ∈ xs, x ∈ s.occurrences) (ysIn : ∀ y ∈ ys, y ∈ s.occurrences)
    (takeLength : f.rule.body.take.length = xs.length)
    (readLength : f.rule.body.read.length = ys.length) {σ τ : S}
    (composite : ∀ t, A.apply σ (A.apply f.opening t) = A.apply τ t) :
    (frames A).Models (a := PUnit.unit) (b := PUnit.unit) σ (f.information (frames A) (Sem.state s)) ↔
      List.Forall₂ (fun p x => A.E (A.apply τ p) (Sem.embed x.2)) f.rule.body.take xs ∧
      List.Forall₂ (fun p x => A.E (A.apply τ p) (Sem.embed x.2)) f.rule.body.read ys ∧
      ∀ e ∈ f.rule.body.tell, A.E (A.apply τ e.1) (A.apply τ e.2) := by
  have split : f.information (frames A) (Sem.state s) =
      f.matching (frames A) (Sem.state s) (f.rule.body.take.map (A.apply f.opening)) (xs.map Prod.fst) ++
        f.matching (frames A) (Sem.state s) (f.rule.body.read.map (A.apply f.opening)) (ys.map Prod.fst) ++
        f.rule.body.tell.map (fun e => (A.apply f.opening e.1, A.apply f.opening e.2)) := by
    rw [xsIds, ysIds]
    rfl
  rw [split, Frames.models_append, Frames.models_append,
    Sem.models_matching distinct f composite _ xs xsIn takeLength,
    Sem.models_matching distinct f composite _ ys ysIn readLength, and_assoc]
  apply and_congr Iff.rfl
  apply and_congr Iff.rfl
  change A.Models σ _ ↔ _
  constructor
  · intro solved e member
    have here := solved _ (List.mem_map.mpr ⟨e, member, rfl⟩)
    simpa only [SubstitutionAction.Solves, composite] using here
  · intro solved e member
    obtain ⟨e', member', rfl⟩ := List.mem_map.mp member
    have here := solved e' member'
    simpa only [SubstitutionAction.Solves, composite] using here

omit [DecidableEq V] in
/-- The pattern of a query, at a store occurrence, matches exactly when the occurrence carries the
pattern's value. -/
theorem Semantics.matches_iff {P : List (Rule T)} {s : Store V}
    (distinct : (s.occurrences.map Prod.fst).Nodup) (f : StepFiring A P) {σ τ : S}
    (composite : ∀ t, A.apply σ (A.apply f.opening t) = A.apply τ t) {p : T} {w : V}
    (valued : A.E (A.apply τ p) (Sem.embed w)) {o : ℕ} {a : V} (inside : (o, a) ∈ s.occurrences) :
    A.E (A.apply σ (A.apply f.opening p)) (A.apply σ (f.row (frames A) (Sem.state s) o)) ↔
      w = a := by
  have equation := Sem.solves_matching distinct f composite p (o, a) inside
  rw [equation]
  exact Sem.value_iff valued

theorem Store.mem_carrying {s : Store V} {value : V} {o : ℕ} :
    o ∈ s.carrying value ↔ (o, value) ∈ s.occurrences := by
  simp only [Store.carrying, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨x, ⟨inside, rfl⟩, rfl⟩
    exact inside
  · intro inside
    exact ⟨(o, value), ⟨inside, rfl⟩, rfl⟩

omit [Inhabited T] in
/-- **The occurrences a query pattern matches** are the occurrences carrying its value. -/
theorem Semantics.matchesAt_eq [Inhabited T] {P : List (Rule T)} {s : Store V}
    (distinct : (s.occurrences.map Prod.fst).Nodup) (f : StepFiring A P) {σ τ : S}
    (composite : ∀ t, A.apply σ (A.apply f.opening t) = A.apply τ t) {p : T} {w : V}
    (valued : A.E (A.apply τ p) (Sem.embed w)) :
    RuleSyntax.matchesAt (frames A) (a := PUnit.unit) (b := PUnit.unit) σ
        (f.row (frames A) (Sem.state s)) (Sem.state s).present (A.apply f.opening p) =
      (s.carrying w).toFinset := by
  ext o
  rw [RuleSyntax.mem_matchesAt, List.mem_toFinset, Store.mem_carrying]
  constructor
  · rintro ⟨present, equal⟩
    obtain ⟨a, _, inside⟩ := Store.valueOf_isSome distinct (List.mem_toFinset.mp present)
    have same := (Sem.matches_iff distinct f composite valued inside).mp equal
    rw [same]
    exact inside
  · intro inside
    refine ⟨List.mem_toFinset.mpr (Store.mem_ids.mpr ⟨w, inside⟩), ?_⟩
    exact (Sem.matches_iff distinct f composite valued inside).mpr rfl

theorem Store.carrying_nodup {s : Store V} (distinct : (s.occurrences.map Prod.fst).Nodup)
    (value : V) : (s.carrying value).Nodup := by
  unfold Store.carrying
  exact (List.filter_sublist).map Prod.fst |>.nodup distinct

theorem Store.card_carrying {s : Store V} (distinct : (s.occurrences.map Prod.fst).Nodup)
    (value : V) :
    (s.carrying value).toFinset.card = s.occurrences.countP (fun x => decide (x.2 = value)) := by
  rw [List.toFinset_card_of_nodup (Store.carrying_nodup distinct value), Store.carrying,
    List.length_map, List.countP_eq_length_filter]

theorem Store.any_iff {s : Store V} (value : V) :
    s.occurrences.any (fun x => decide (x.2 = value)) = true ↔ ∃ o, (o, value) ∈ s.occurrences := by
  simp only [List.any_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨x, inside, rfl⟩
    exact ⟨x.1, inside⟩
  · rintro ⟨o, inside⟩
    exact ⟨(o, value), inside, rfl⟩

/-! ## Guards at a store -/

omit [Inhabited T] in
theorem Semantics.agree_sound {θ : B} {σ : S} (denoted : Sem.Denotes θ σ) {l r : T}
    (agreeing : agree M θ l r = true) : A.E (A.apply σ l) (A.apply σ r) := by
  unfold agree at agreeing
  cases left : M.instantiate θ l with
  | none => simp [left] at agreeing
  | some a =>
      cases right : M.instantiate θ r with
      | none => simp [left, right] at agreeing
      | some b =>
          simp only [left, right, decide_eq_true_eq] at agreeing
          subst agreeing
          exact (Sem.values_iff (Sem.instantiate_sound θ l a σ left denoted)
            (Sem.instantiate_sound θ r a σ right denoted)).mpr rfl

omit [Inhabited T] in
theorem Semantics.agree_complete {θ : B} {σ : S} (denoted : Sem.Denotes θ σ) {l r : T}
    (leftDefined : (M.instantiate θ l).isSome) (rightDefined : (M.instantiate θ r).isSome)
    (equal : A.E (A.apply σ l) (A.apply σ r)) : agree M θ l r = true := by
  obtain ⟨a, left⟩ := Option.isSome_iff_exists.mp leftDefined
  obtain ⟨b, right⟩ := Option.isSome_iff_exists.mp rightDefined
  have same := (Sem.values_iff (Sem.instantiate_sound θ l a σ left denoted)
    (Sem.instantiate_sound θ r b σ right denoted)).mp equal
  simp [agree, left, right, same]

/-- **A passing check holds at every solution** read through the store. -/
theorem Semantics.checkHolds_of_passes {P : List (Rule T)} {s : Store V}
    (distinct : (s.occurrences.map Prod.fst).Nodup) (f : StepFiring A P) {σ τ : S}
    (composite : ∀ t, A.apply σ (A.apply f.opening t) = A.apply τ t) {θ : B}
    (denoted : Sem.Denotes θ τ) (c : Check T) (passing : passes M s θ c = true) :
    RuleSyntax.checkHolds (frames A) (a := PUnit.unit) (b := PUnit.unit) σ
      (f.row (frames A) (Sem.state s)) (Sem.state s).present (c.map (A.apply f.opening)) := by
  cases c with
  | equal l r =>
      change A.E (A.apply σ (A.apply f.opening l)) (A.apply σ (A.apply f.opening r))
      rw [composite, composite]
      exact Sem.agree_sound denoted passing
  | predicate q p =>
      cases q with
      | any =>
          simp only [passes] at passing
          cases inst : M.instantiate θ p with
          | none => simp [inst] at passing
          | some w =>
              rw [inst] at passing
              obtain ⟨o, inside⟩ := (Store.any_iff w).mp passing
              have valued := Sem.instantiate_sound θ p w τ inst denoted
              refine ⟨o, List.mem_toFinset.mpr (Store.mem_ids.mpr ⟨w, inside⟩), ?_⟩
              exact (Sem.matches_iff distinct f composite valued inside).mpr rfl
      | none =>
          simp only [passes] at passing
          cases inst : M.instantiate θ p with
          | none => simp [inst] at passing
          | some w =>
              rw [inst] at passing
              have valued := Sem.instantiate_sound θ p w τ inst denoted
              intro o present equal
              obtain ⟨a, _, inside⟩ := Store.valueOf_isSome distinct (List.mem_toFinset.mp present)
              have same := (Sem.matches_iff distinct f composite valued inside).mp equal
              subst same
              have found : s.occurrences.any (fun x => decide (x.2 = w)) = true :=
                (Store.any_iff w).mpr ⟨o, inside⟩
              simp [found] at passing
  | count p n =>
      simp only [passes] at passing
      cases inst : M.instantiate θ p with
      | none => simp [inst] at passing
      | some w =>
          rw [inst, decide_eq_true_eq] at passing
          have valued := Sem.instantiate_sound θ p w τ inst denoted
          change (RuleSyntax.matchesAt (frames A) σ _ _ (A.apply f.opening p)).card = n
          rw [Sem.matchesAt_eq distinct f composite valued, Store.card_carrying distinct]
          exact passing

/-- **A check that holds at a solution passes**, when its terms instantiate. -/
theorem Semantics.passes_of_checkHolds {P : List (Rule T)} {s : Store V}
    (distinct : (s.occurrences.map Prod.fst).Nodup) (f : StepFiring A P) {σ τ : S}
    (composite : ∀ t, A.apply σ (A.apply f.opening t) = A.apply τ t) {θ : B}
    (denoted : Sem.Denotes θ τ) (c : Check T)
    (defined : ∀ t ∈ RuleSyntax.checkTerms c, (M.instantiate θ t).isSome)
    (holds : RuleSyntax.checkHolds (frames A) (a := PUnit.unit) (b := PUnit.unit) σ
      (f.row (frames A) (Sem.state s)) (Sem.state s).present (c.map (A.apply f.opening))) :
    passes M s θ c = true := by
  cases c with
  | equal l r =>
      change A.E (A.apply σ (A.apply f.opening l)) (A.apply σ (A.apply f.opening r)) at holds
      rw [composite, composite] at holds
      exact Sem.agree_complete denoted (defined l (by simp [RuleSyntax.checkTerms]))
        (defined r (by simp [RuleSyntax.checkTerms])) holds
  | predicate q p =>
      obtain ⟨w, inst⟩ := Option.isSome_iff_exists.mp (defined p (by simp [RuleSyntax.checkTerms]))
      have valued := Sem.instantiate_sound θ p w τ inst denoted
      cases q with
      | any =>
          simp only [passes, inst]
          obtain ⟨o, present, equal⟩ := holds
          obtain ⟨a, _, inside⟩ := Store.valueOf_isSome distinct (List.mem_toFinset.mp present)
          have same := (Sem.matches_iff distinct f composite valued inside).mp equal
          subst same
          exact (Store.any_iff w).mpr ⟨o, inside⟩
      | none =>
          simp only [passes, inst, Bool.not_eq_true']
          cases found : s.occurrences.any (fun x => decide (x.2 = w)) with
          | false => rfl
          | true =>
              obtain ⟨o, inside⟩ := (Store.any_iff w).mp found
              exact absurd ((Sem.matches_iff distinct f composite valued inside).mpr rfl)
                (holds o (List.mem_toFinset.mpr (Store.mem_ids.mpr ⟨w, inside⟩)))
  | count p n =>
      obtain ⟨w, inst⟩ := Option.isSome_iff_exists.mp (defined p (by simp [RuleSyntax.checkTerms]))
      have valued := Sem.instantiate_sound θ p w τ inst denoted
      simp only [passes, inst, decide_eq_true_eq]
      change (RuleSyntax.matchesAt (frames A) σ _ _ (A.apply f.opening p)).card = n at holds
      rw [Sem.matchesAt_eq distinct f composite valued, Store.card_carrying distinct] at holds
      exact holds

/-- The collect queries hold at the sets of the occurrences carrying their values. -/
theorem Semantics.collect_holds {P : List (Rule T)} {s : Store V}
    (distinct : (s.occurrences.map Prod.fst).Nodup) (f : StepFiring A P) {σ τ : S}
    (composite : ∀ t, A.apply σ (A.apply f.opening t) = A.apply τ t) {θ : B}
    (denoted : Sem.Denotes θ τ) :
    ∀ (patterns : List T) (cs : List V),
      List.Forall₂ (fun p w => M.instantiate θ p = some w) patterns cs →
      ∀ q ∈ (patterns.map (A.apply f.opening)).zip (cs.map fun w => (s.carrying w).toFinset),
        RuleSyntax.matchesAt (frames A) (a := PUnit.unit) (b := PUnit.unit) σ
          (f.row (frames A) (Sem.state s)) (Sem.state s).present q.1 = q.2
  | [], [], _, q, inside => by simp at inside
  | p :: ps, w :: ws, related, q, inside => by
      obtain ⟨head, tail⟩ := List.forall₂_cons.mp related
      simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at inside
      rcases inside with rfl | later
      · exact Sem.matchesAt_eq distinct f composite (Sem.instantiate_sound θ p w τ head denoted)
      · exact Semantics.collect_holds distinct f composite denoted ps ws tail q later

/-- The seen sets of holding collect queries are the sets of the occurrences carrying their values. -/
theorem Semantics.seen_eq {P : List (Rule T)} {s : Store V}
    (distinct : (s.occurrences.map Prod.fst).Nodup) (f : StepFiring A P) {σ τ : S}
    (composite : ∀ t, A.apply σ (A.apply f.opening t) = A.apply τ t) {θ : B}
    (denoted : Sem.Denotes θ τ) :
    ∀ (patterns : List T) (cs : List V) (seen : List (Finset ℕ)),
      List.Forall₂ (fun p w => M.instantiate θ p = some w) patterns cs → patterns.length = seen.length →
      (∀ q ∈ (patterns.map (A.apply f.opening)).zip seen,
        RuleSyntax.matchesAt (frames A) (a := PUnit.unit) (b := PUnit.unit) σ
          (f.row (frames A) (Sem.state s)) (Sem.state s).present q.1 = q.2) →
      seen = cs.map fun w => (s.carrying w).toFinset
  | [], [], [], _, _, _ => rfl
  | [], _ :: _, _, related, _, _ => by simp at related
  | _ :: _, [], _, related, _, _ => by simp at related
  | [], [], _ :: _, _, lengths, _ => by simp at lengths
  | _ :: _, _ :: _, [], _, lengths, _ => by simp at lengths
  | p :: ps, w :: ws, x :: xs, related, lengths, holds => by
      obtain ⟨head, tail⟩ := List.forall₂_cons.mp related
      have first := holds (A.apply f.opening p, x) (by simp)
      rw [Sem.matchesAt_eq distinct f composite (Sem.instantiate_sound θ p w τ head denoted)] at first
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨first.symm, Semantics.seen_eq distinct f composite denoted ps ws xs tail (Nat.succ.inj lengths)
        (fun q inside => holds q (by simp only [List.map_cons, List.zip_cons_cons]; exact List.mem_cons_of_mem _ inside))⟩

/-! ## Freshness, publication and reading -/

omit [DecidableEq V] in
/-- **The identity opening is fresh at every store**: a store mentions only values, which every
substitution fixes. -/
theorem Semantics.identity_fresh {P : List (Rule T)} (s : Store V)
    (distinct : (s.occurrences.map Prod.fst).Nodup) (f : StepFiring A P)
    (identity : f.opening = A.identity) : f.Fresh (frames A) (Sem.state s) := by
  intro b g h
  refine ⟨h, ?_, ?_⟩
  · intro t mentioned
    rcases mentioned with known | known | ⟨o, present, rfl⟩
    · simp [Semantics.state] at known
    · simp [Semantics.state] at known
    · obtain ⟨a, _, inside⟩ := Store.valueOf_isSome distinct (List.mem_toFinset.mp present)
      change A.E (A.apply h (A.apply A.identity (Sem.label s o))) (A.apply g (Sem.label s o))
      rw [A.apply_identity, Sem.label_of_mem distinct inside]
      exact Semantics.E_trans (Sem.fixed h a) (Semantics.E_symm (Sem.fixed g a))
  · intro t _
    change A.E (A.apply h (A.apply f.opening t)) (A.apply h t)
    rw [identity, A.apply_identity]
    exact A.equivalence.refl _

omit [DecidableEq V] [Inhabited T] in
theorem Store.lift_ids {s : Store V} :
    ∀ os : List ℕ, (∀ o ∈ os, o ∈ s.ids) →
      ∃ xs : List (ℕ × V), xs.map Prod.fst = os ∧ ∀ x ∈ xs, x ∈ s.occurrences
  | [], _ => ⟨[], rfl, by simp⟩
  | o :: os, present => by
      obtain ⟨a, inside⟩ := Store.mem_ids.mp (present o List.mem_cons_self)
      obtain ⟨xs, ids, within⟩ := Store.lift_ids os (fun o' member => present o' (List.mem_cons_of_mem _ member))
      refine ⟨(o, a) :: xs, by simp [ids], ?_⟩
      intro x member
      rcases List.mem_cons.mp member with rfl | later
      · exact inside
      · exact within x later

omit [DecidableEq V] [Inhabited T] in
theorem publishWith_ids {B : Type w} (s : Store V) (m : Match V B) (ids : List ℕ)
    (lengths : ids.length = m.made.length) :
    (publishWith s m ids).ids =
      (s.occurrences.filter (fun x => !(m.taken.contains x.1))).map Prod.fst ++ ids := by
  simp only [publishWith, Store.ids, List.map_append, List.map_fst_zip (le_of_eq lengths)]

omit [DecidableEq V] [Inhabited T] in
theorem publishWith_distinct {B : Type w} {s : Store V} (distinct : s.Distinct) (m : Match V B)
    (ids : List ℕ) (lengths : ids.length = m.made.length) (nodup : ids.Nodup)
    (fresh : ∀ o ∈ ids, o ∉ s.ids) : ((publishWith s m ids).occurrences.map Prod.fst).Nodup := by
  have equal := publishWith_ids s m ids lengths
  unfold Store.ids at equal
  rw [equal]
  refine List.nodup_append.mpr ⟨(List.filter_sublist.map Prod.fst).nodup distinct, nodup, ?_⟩
  intro a old b new same
  subst same
  apply fresh a new
  exact (List.filter_sublist.map Prod.fst).subset old

omit [DecidableEq V] in
/-- **Reading the result of a firing**: its present identities are the survivors and the made
identities, survivors read as their values and made identities as their made values. -/
theorem Semantics.readsAs_result {P : List (Rule T)} {s : Store V} (wf : s.Distinct)
    (f : StepFiring A P) (m : Match V B) (shapes : f.Shapes (frames A) (Sem.state s))
    (taken : f.selection.taken = m.taken) (fresh : ∀ o ∈ f.selection.made, o ∉ s.ids)
    (madeLength : f.selection.made.length = m.made.length)
    (produced : ∀ σ : S, (frames A).Models (a := PUnit.unit) (b := PUnit.unit) σ
        (f.information (frames A) (Sem.state s)) →
      List.Forall₂ (fun t w => A.E (A.apply σ (A.apply f.opening t)) (Sem.embed w))
        f.rule.body.produce m.made) :
    Sem.ReadsAs (f.result (frames A) (Sem.state s)) (publishWith s m f.selection.made) := by
  have distinct := publishWith_distinct wf m f.selection.made madeLength shapes.2.2.1 fresh
  refine ⟨distinct, ?_, ?_⟩
  · rw [publishWith_ids s m _ madeLength]
    ext o
    simp only [RuleSyntax.Firing.result, fire, Selection.commit, Finset.mem_union, Finset.mem_sdiff,
      List.mem_toFinset, List.mem_append, List.mem_map, List.mem_filter, Bool.not_eq_true',
      Semantics.state, Store.ids, taken]
    constructor
    · rintro (⟨⟨x, inside, rfl⟩, notTaken⟩ | made)
      · left
        refine ⟨x, ⟨inside, ?_⟩, rfl⟩
        simpa [List.contains_iff_mem] using notTaken
      · exact Or.inr made
    · rintro (⟨x, ⟨inside, notTaken⟩, rfl⟩ | made)
      · left
        refine ⟨⟨x, inside, rfl⟩, ?_⟩
        simpa [List.contains_iff_mem] using notTaken
      · exact Or.inr made
  · intro σ solved o present
    by_cases made : o ∈ f.selection.made
    · obtain ⟨i, bound, rfl⟩ := List.mem_iff_getElem.mp made
      have produceBound : i < f.rule.body.produce.length := by
        rw [shapes.2.2.2.2.2.1]
        exact bound
      have valueBound : i < m.made.length := by rw [← madeLength]; exact bound
      have pair : (f.selection.made[i], A.apply f.opening (f.rule.body.produce[i])) ∈
          f.selection.made.zip (f.opened (frames A)).produce := by
        apply List.mem_iff_getElem.mpr
        refine ⟨i, by simp [RuleSyntax.Firing.opened, RuleInstance.map, bound, produceBound], ?_⟩
        simp only [RuleSyntax.Firing.opened, RuleInstance.map, List.getElem_zip, List.getElem_map]
        rfl
      rw [RuleSyntax.Firing.result_label_made f shapes pair]
      refine ⟨m.made[i], ?_, ?_⟩
      · apply (Store.valueOf_eq_some distinct).mpr
        apply List.mem_append_right
        apply List.mem_iff_getElem.mpr
        exact ⟨i, by simp [bound, valueBound], by simp⟩
      · have related := (produced σ solved).get produceBound valueBound
        simpa using related
    · rw [RuleSyntax.Firing.result_label_other f made, Sem.row_eq]
      have survivor : o ∈ (Sem.state s).present ∧ o ∉ f.selection.taken := by
        simpa [RuleSyntax.Firing.result, fire, Selection.commit, made] using present
      obtain ⟨a, _, inside⟩ := Store.valueOf_isSome wf (List.mem_toFinset.mp survivor.1)
      refine ⟨a, ?_, ?_⟩
      · apply (Store.valueOf_eq_some distinct).mpr
        apply List.mem_append_left
        apply List.mem_filter.mpr
        refine ⟨inside, ?_⟩
        have notTaken := survivor.2
        rw [taken] at notTaken
        simpa [List.contains_iff_mem] using notTaken
      · rw [Sem.label_of_mem wf inside]
        exact Sem.fixed σ a

/-! ## Soundness -/

/-- **Soundness**: every firing the evaluator finds is admitted by the step theory, with any fresh
made identities, and its result reads as the published store. -/
theorem Semantics.admits_stepFiring (P : List (Rule T)) (s : Store V) (wf : s.Distinct)
    (r : Rule T) (m : Match V B) (found : (r, m) ∈ firings M P s) (ids : List ℕ)
    (idsNodup : ids.Nodup) (idsFresh : ∀ o ∈ ids, o ∉ s.ids) (idsLength : ids.length = m.made.length) :
    ∃ member : r ∈ programOf P,
      (stepFiring A P r member m ids).Admits (frames A) (Sem.state s) ∧
      Sem.ReadsAs ((stepFiring A P r member m ids).result (frames A) (Sem.state s))
        (publishWith s m ids) := by
  obtain ⟨inP, solved⟩ := (mem_firings P s r m).mp found
  obtain ⟨xs, ys, m₁, m₂, xsIn, ysIn, takes, reads, dets⟩ := (mem_solve_goals s r m).mp solved
  obtain ⟨takenEq, readEq₁, _, _, nodup₁, _⟩ := attemptAll_take r.body.take _ m₁ xs takes
  obtain ⟨readEq₂, takenEq₂, seenEq₂, madeEq₂, apart₂⟩ := attemptAll_read r.body.read m₁ m₂ ys reads
  have takeLength := attemptAll_length .take r.body.take _ m₁ xs takes
  have readLength := attemptAll_length .read r.body.read m₁ m₂ ys reads
  obtain ⟨tells, checks, cs, ws, csRel, wsRel, rfl⟩ := (applyAll_determinates_iff s r m₂ m).mp dets
  simp only [Match.start, List.nil_append] at takenEq readEq₁ nodup₁
  have seenStart : m₁.seen = [] := by
    obtain ⟨_, _, seen, _, _, _⟩ := attemptAll_take r.body.take _ m₁ xs takes
    exact seen
  have madeStart : m₁.made = [] := by
    obtain ⟨_, _, _, made, _, _⟩ := attemptAll_take r.body.take _ m₁ xs takes
    exact made
  let f := stepFiring A P r inP (Match.record m₂ (cs.map fun w => (s.carrying w).toFinset) ws) ids
  have fTaken : f.selection.taken = xs.map Prod.fst := by
    change m₂.taken = _
    rw [takenEq₂, takenEq]
  have fRead : f.selection.read = ys.map Prod.fst := by
    change m₂.read = _
    rw [readEq₂, readEq₁]
    rfl
  have fSeen : f.seen = cs.map fun w => (s.carrying w).toFinset := by
    change m₂.seen ++ _ = _
    rw [seenEq₂, seenStart]
    rfl
  have fMadeValues : (Match.record m₂ (cs.map fun w => (s.carrying w).toFinset) ws).made = ws := by
    change m₂.made ++ ws = ws
    rw [madeEq₂, madeStart]
    rfl
  have composite : ∀ σ : S, ∀ t, A.apply σ (A.apply f.opening t) = A.apply σ t :=
    fun σ t => by change A.apply σ (A.apply A.identity t) = _; rw [A.apply_identity]
  -- the bindings of the match denote exactly the solutions of its premise equations
  have denotes : ∀ σ : S, Sem.Denotes m₂.bindings σ ↔
      List.Forall₂ (fun p x => A.E (A.apply σ p) (Sem.embed x.2)) r.body.take xs ∧
        List.Forall₂ (fun p x => A.E (A.apply σ p) (Sem.embed x.2)) r.body.read ys := by
    intro σ
    rw [Sem.attemptAll_denotes .read _ _ _ ys reads, Sem.attemptAll_denotes .take _ _ _ xs takes]
    simp only [Match.start, Sem.denotes_empty, true_and]
  have information : ∀ σ : S, (frames A).Models (a := PUnit.unit) (b := PUnit.unit) σ
      (f.information (frames A) (Sem.state s)) ↔
      (List.Forall₂ (fun p x => A.E (A.apply σ p) (Sem.embed x.2)) r.body.take xs ∧
        List.Forall₂ (fun p x => A.E (A.apply σ p) (Sem.embed x.2)) r.body.read ys) ∧
        ∀ e ∈ r.body.tell, A.E (A.apply σ e.1) (A.apply σ e.2) := by
    intro σ
    rw [Sem.models_information wf f xs ys fTaken.symm fRead.symm xsIn ysIn takeLength readLength
      (composite σ), and_assoc]
    exact Iff.rfl
  have shapes : f.Shapes (frames A) (Sem.state s) := by
    refine ⟨Sem.identity_fresh s wf f rfl, ?_, idsNodup, ?_, ?_, ?_, ?_⟩
    · rw [fTaken, ← takenEq]; exact nodup₁ List.nodup_nil
    · rw [fTaken, List.length_map]; exact takeLength
    · rw [fRead, List.length_map]; exact readLength
    · change r.body.produce.length = ids.length
      rw [idsLength, fMadeValues]
      exact wsRel.length_eq
    · change r.collect.length = f.seen.length
      rw [fSeen, List.length_map]
      exact csRel.length_eq
  have enabled : Enabled (fun _ : ℕ => ()) (Sem.state s).present (f.selection.commit (T := Unit)) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro o member
      have inside : o ∈ xs.map Prod.fst := by
        rw [← fTaken]; simpa [Selection.commit] using member
      obtain ⟨x, xMember, rfl⟩ := List.mem_map.mp inside
      exact List.mem_toFinset.mpr (Store.mem_ids.mpr ⟨x.2, xsIn x xMember⟩)
    · intro o member
      have inside : o ∈ ys.map Prod.fst := by
        rw [← fRead]; simpa [Selection.commit] using member
      obtain ⟨y, yMember, rfl⟩ := List.mem_map.mp inside
      exact List.mem_toFinset.mpr (Store.mem_ids.mpr ⟨y.2, ysIn y yMember⟩)
    · apply Finset.disjoint_left.mpr
      intro o takenMember readMember
      have isTaken : o ∈ xs.map Prod.fst := by
        rw [← fTaken]; simpa [Selection.commit] using takenMember
      have isRead : o ∈ ys.map Prod.fst := by
        rw [← fRead]; simpa [Selection.commit] using readMember
      exact apart₂ o isRead (by rw [takenEq]; exact isTaken)
    · apply Finset.disjoint_left.mpr
      intro o madeMember present
      change o ∈ ids.toFinset at madeMember
      exact idsFresh o (List.mem_toFinset.mp madeMember) (List.mem_toFinset.mp present)
    · intro query member
      simp [Selection.commit] at member
  obtain ⟨σ₀, denoted₀⟩ := Sem.attemptAll_inhabited .read _ _ _ ys reads
    (Sem.attemptAll_inhabited .take _ _ _ xs takes ⟨A.identity, Sem.denotes_empty _⟩)
  have solvable : (frames A).Solvable (a := PUnit.unit) (f.information (frames A) (Sem.state s)) := by
    refine ⟨PUnit.unit, σ₀, (information σ₀).mpr ⟨(denotes σ₀).mp denoted₀, ?_⟩⟩
    intro e member
    exact Sem.agree_sound denoted₀ (tells e member)
  refine ⟨inP, ⟨shapes, enabled, solvable, ?_⟩, ?_⟩
  · intro b σ solved
    cases b
    have denoted := (denotes σ).mpr ((information σ).mp solved).1
    refine ⟨?_, ?_⟩
    · intro c member
      obtain ⟨c', member', rfl⟩ := List.mem_map.mp member
      exact Sem.checkHolds_of_passes wf f (composite σ) denoted c' (checks c' member')
    · intro q member
      change q ∈ (r.collect.map (A.apply f.opening)).zip f.seen at member
      rw [fSeen] at member
      exact Sem.collect_holds wf f (composite σ) denoted r.collect cs csRel q member
  · apply Sem.readsAs_result wf f _ shapes rfl idsFresh idsLength
    intro σ solved
    have denoted := (denotes σ).mpr ((information σ).mp solved).1
    rw [fMadeValues]
    exact wsRel.imp fun t w inst => by
      rw [composite σ]
      exact Sem.instantiate_sound _ t w σ inst denoted

/-! ## Completeness -/

omit [DecidableEq V] in
/-- The terms of a rule that its premises must determine: tells, check terms, collect patterns and
produced terms. -/
def groundedTerms (r : Rule T) : List T :=
  r.body.tell.map Prod.fst ++ r.body.tell.map Prod.snd ++
    r.body.checks.flatMap RuleSyntax.checkTerms ++ r.collect ++ r.body.produce

omit [DecidableEq V] [Inhabited T] in
/-- Bindings reached by matching a rule's premises against some values. -/
def Reached (M : Matcher T V B) (r : Rule T) (θ : B) : Prop :=
  ∃ (xs ys : List (ℕ × V)) (m₁ m₂ : Match V B),
    attemptAll M .take r.body.take (Match.start M) xs = some m₁ ∧
    attemptAll M .read r.body.read m₁ ys = some m₂ ∧ m₂.bindings = θ

omit [DecidableEq V] [Inhabited T] in
/-- **Range restriction**: after its premises, every other term of the rule instantiates. -/
def RangeRestricted (M : Matcher T V B) (r : Rule T) : Prop :=
  ∀ θ, Reached M r θ → ∀ t ∈ groundedTerms r, (M.instantiate θ t).isSome

omit [DecidableEq V] [Inhabited T] in
theorem forall₂_of_isSome {θ : B} (ts : List T)
    (defined : ∀ t ∈ ts, (M.instantiate θ t).isSome) :
    ∃ ws : List V, List.Forall₂ (fun t w => M.instantiate θ t = some w) ts ws := by
  induction ts with
  | nil => exact ⟨[], .nil⟩
  | cons t ts ih =>
      obtain ⟨w, inst⟩ := Option.isSome_iff_exists.mp (defined t List.mem_cons_self)
      obtain ⟨ws, rest⟩ := ih (fun t' member => defined t' (List.mem_cons_of_mem _ member))
      exact ⟨w :: ws, .cons inst rest⟩

/-- **Completeness**: every admitted firing of the step theory, with any fresh opening and any fresh
made identities, is a firing of the evaluator with the same rule, the same taken and read occurrences
and the same seen sets, and its result reads as the store published with its made identities. -/
theorem Semantics.firing_of_admits (P : List (Rule T)) (s : Store V) (wf : s.Distinct)
    (f : StepFiring A P) (admitted : f.Admits (frames A) (Sem.state s))
    (ranged : RangeRestricted M f.rule) :
    ∃ m : Match V B, (f.rule, m) ∈ firings M P s ∧ m.taken = f.selection.taken ∧
      m.read = f.selection.read ∧ m.seen = f.seen ∧ m.made.length = f.selection.made.length ∧
      Sem.ReadsAs (f.result (frames A) (Sem.state s)) (publishWith s m f.selection.made) := by
  obtain ⟨shapes, enabled, ⟨_, σ, solved⟩, entails⟩ := admitted
  obtain ⟨_, takenNodup, _, takeLength, readLength, produceLength, collectLength⟩ := shapes
  have takenPresent : ∀ o ∈ f.selection.taken, o ∈ s.ids := fun o member =>
    List.mem_toFinset.mp (enabled.taken_subset (by simpa [Selection.commit] using member))
  have readPresent : ∀ o ∈ f.selection.read, o ∈ s.ids := fun o member =>
    List.mem_toFinset.mp (enabled.kept_subset (by simpa [Selection.commit] using member))
  obtain ⟨xs, xsIds, xsIn⟩ := Store.lift_ids f.selection.taken takenPresent
  obtain ⟨ys, ysIds, ysIn⟩ := Store.lift_ids f.selection.read readPresent
  have xsLength : f.rule.body.take.length = xs.length := by
    rw [takeLength, ← xsIds, List.length_map]
  have ysLength : f.rule.body.read.length = ys.length := by
    rw [readLength, ← ysIds, List.length_map]
  have information : ∀ σ' : S, (frames A).Models (a := PUnit.unit) (b := PUnit.unit) σ'
      (f.information (frames A) (Sem.state s)) ↔
      List.Forall₂ (fun p x => A.E (A.apply (A.compose σ' f.opening) p) (Sem.embed x.2)) f.rule.body.take xs ∧
      List.Forall₂ (fun p x => A.E (A.apply (A.compose σ' f.opening) p) (Sem.embed x.2)) f.rule.body.read ys ∧
      ∀ e ∈ f.rule.body.tell,
        A.E (A.apply (A.compose σ' f.opening) e.1) (A.apply (A.compose σ' f.opening) e.2) :=
    fun σ' => Sem.models_information wf f xs ys xsIds ysIds xsIn ysIn xsLength ysLength
      (fun t => (A.apply_compose σ' f.opening t).symm)
  obtain ⟨takeSolved, readSolved, tellSolved⟩ := (information σ).mp solved
  let τ := A.compose σ f.opening
  have composite : ∀ t, A.apply σ (A.apply f.opening t) = A.apply τ t :=
    fun t => (A.apply_compose σ f.opening t).symm
  obtain ⟨m₁, takes⟩ := Sem.attemptAll_take_complete f.rule.body.take (Match.start M) xs τ
    (by simpa [Match.start, xsIds] using takenNodup) (by simp [Match.start])
    (Sem.denotes_empty τ) takeSolved
  have denoted₁ : Sem.Denotes m₁.bindings τ :=
    (Sem.attemptAll_denotes .take _ _ _ xs takes τ).mpr ⟨Sem.denotes_empty τ, takeSolved⟩
  obtain ⟨takenEq, readEq₁, seenEq₁, madeEq₁, _, _⟩ := attemptAll_take f.rule.body.take _ m₁ xs takes
  simp only [Match.start, List.nil_append] at takenEq readEq₁ seenEq₁ madeEq₁
  obtain ⟨m₂, reads⟩ := Sem.attemptAll_read_complete f.rule.body.read m₁ ys τ
    (by
      intro o member taken
      rw [takenEq, xsIds] at taken
      rw [ysIds] at member
      exact Finset.disjoint_left.mp enabled.apart (List.mem_toFinset.mpr taken)
        (List.mem_toFinset.mpr member))
    denoted₁ readSolved
  have denoted₂ : Sem.Denotes m₂.bindings τ :=
    (Sem.attemptAll_denotes .read _ _ _ ys reads τ).mpr ⟨denoted₁, readSolved⟩
  obtain ⟨readEq₂, takenEq₂, seenEq₂, madeEq₂, _⟩ := attemptAll_read f.rule.body.read m₁ m₂ ys reads
  have defined := ranged m₂.bindings ⟨xs, ys, m₁, m₂, takes, reads, rfl⟩
  have tellsAgree : ∀ e ∈ f.rule.body.tell, agree M m₂.bindings e.1 e.2 = true := by
    intro e member
    exact Sem.agree_complete denoted₂
      (defined e.1 (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ (List.mem_map_of_mem member))))))
      (defined e.2 (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_right _ (List.mem_map_of_mem member))))))
      (tellSolved e member)
  have holds := entails PUnit.unit σ solved
  have checksPass : ∀ c ∈ f.rule.body.checks, passes M s m₂.bindings c = true := by
    intro c member
    refine Sem.passes_of_checkHolds wf f composite denoted₂ c ?_ (holds.1 _ (List.mem_map.mpr ⟨c, member, rfl⟩))
    intro t inside
    exact defined t (by
      simp only [groundedTerms, List.mem_append, List.mem_flatMap]
      exact Or.inl (Or.inl (Or.inr ⟨c, member, inside⟩)))
  obtain ⟨cs, csRel⟩ := forall₂_of_isSome (M := M) f.rule.collect
    (fun t inside => defined t (by simp [groundedTerms, inside]))
  obtain ⟨ws, wsRel⟩ := forall₂_of_isSome (M := M) f.rule.body.produce
    (fun t inside => defined t (by simp [groundedTerms, inside]))
  let m := Match.record m₂ (cs.map fun w => (s.carrying w).toFinset) ws
  have dets : applyAll M s (determinates f.rule) m₂ = some m :=
    (applyAll_determinates_iff s f.rule m₂ m).mpr ⟨tellsAgree, checksPass, cs, ws, csRel, wsRel, rfl⟩
  have found : (f.rule, m) ∈ firings M P s :=
    (mem_firings P s f.rule m).mpr ⟨f.member, (mem_solve_goals s f.rule m).mpr
      ⟨xs, ys, m₁, m₂, xsIn, ysIn, takes, reads, dets⟩⟩
  have mTaken : m.taken = f.selection.taken := by
    change m₂.taken = _
    rw [takenEq₂, takenEq, xsIds]
  have mRead : m.read = f.selection.read := by
    change m₂.read = _
    rw [readEq₂, readEq₁, ysIds]
    rfl
  have mSeen : m.seen = f.seen := by
    change m₂.seen ++ _ = _
    rw [seenEq₂, seenEq₁, List.nil_append]
    exact (Sem.seen_eq wf f composite denoted₂ f.rule.collect cs f.seen csRel collectLength holds.2).symm
  have mMade : m.made = ws := by
    change m₂.made ++ ws = ws
    rw [madeEq₂, madeEq₁, List.nil_append]
  have madeLength : m.made.length = f.selection.made.length := by
    rw [mMade, ← wsRel.length_eq, produceLength]
  refine ⟨m, found, mTaken, mRead, mSeen, madeLength, ?_⟩
  apply Sem.readsAs_result wf f m ⟨‹_›, takenNodup, ‹_›, takeLength, readLength, produceLength,
    collectLength⟩ mTaken.symm
    (fun o member present => Finset.disjoint_left.mp enabled.fresh
      (by simpa [Selection.commit] using member) (List.mem_toFinset.mpr present)) madeLength.symm
  intro σ' solved'
  obtain ⟨takeSolved', readSolved', _⟩ := (information σ').mp solved'
  have denoted' : Sem.Denotes m₂.bindings (A.compose σ' f.opening) :=
    (Sem.attemptAll_denotes .read _ _ _ ys reads _).mpr
      ⟨(Sem.attemptAll_denotes .take _ _ _ xs takes _).mpr ⟨Sem.denotes_empty _, takeSolved'⟩, readSolved'⟩
  rw [mMade]
  exact wsRel.imp fun t w inst => by
    rw [← A.apply_compose]
    exact Sem.instantiate_sound _ t w _ inst denoted'

/-! ## The step relation, terminality and runs -/

omit [DecidableEq V] [Inhabited T] in
/-- A state with solvable knowledge reads as at most one store, up to the order of occurrences. -/
theorem Semantics.readsAs_unique {st : RuleSyntax.State (Terms T) ℕ} {first second : Store V}
    (solvable : ∃ σ : S, A.Models σ st.knowledge) (one : Sem.ReadsAs st first)
    (two : Sem.ReadsAs st second) : Store.SameOccurrences first second := by
  obtain ⟨σ, solved⟩ := solvable
  refine ⟨one.1, two.1, one.2.1.symm.trans two.2.1, ?_⟩
  intro o member
  have present : o ∈ st.present := by rw [one.2.1]; exact List.mem_toFinset.mpr member
  obtain ⟨a, va, ea⟩ := one.2.2 σ solved o present
  obtain ⟨b, vb, eb⟩ := two.2.2 σ solved o present
  have same : a = b := (Sem.reflects a b).mp (Semantics.E_trans (Semantics.E_symm ea) eb)
  rw [va, vb, same]

omit [DecidableEq V] [Inhabited T] in
theorem Semantics.readsAs_of_same {st : RuleSyntax.State (Terms T) ℕ} {first second : Store V}
    (reads : Sem.ReadsAs st first) (same : Store.SameOccurrences first second) :
    Sem.ReadsAs st second := by
  refine ⟨same.2.1, reads.2.1.trans same.2.2.1, ?_⟩
  intro σ solved o present
  obtain ⟨a, value, equal⟩ := reads.2.2 σ solved o present
  have member : o ∈ first.ids := List.mem_toFinset.mp (reads.2.1 ▸ present)
  exact ⟨a, (same.2.2.2 o member).symm.trans value, equal⟩

omit [DecidableEq V] [Inhabited T] in
theorem freshIds_nodup (s : Store V) (n : ℕ) : (freshIds s n).Nodup :=
  (List.nodup_range).map (fun _ _ same => Nat.add_left_cancel same)

omit [DecidableEq V] [Inhabited T] in
theorem freshIds_fresh {s : Store V} (wf : s.WellFormed) (n : ℕ) :
    ∀ o ∈ freshIds s n, o ∉ s.ids := by
  intro o member present
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp member
  obtain ⟨a, inside⟩ := Store.mem_ids.mp present
  have below := wf.2 _ inside
  simp only at below
  omega

/-- **The step relation of the step theory on ground stores is the evaluator's**: a step is a
firing the evaluator finds, published with some fresh made identities. -/
theorem Semantics.groundStep_iff (P : List (Rule T)) (s s' : Store V) (wf : s.Distinct)
    (ranged : ∀ r ∈ P, RangeRestricted M r) :
    Sem.GroundStep P s s' ↔ ∃ f ∈ firings M P s, ∃ ids : List ℕ, ids.Nodup ∧
      (∀ o ∈ ids, o ∉ s.ids) ∧ ids.length = f.2.made.length ∧
      Store.SameOccurrences (publishWith s f.2 ids) s' := by
  constructor
  · rintro ⟨f, admitted, reads⟩
    obtain ⟨m, found, _, _, _, madeLength, reads'⟩ :=
      Sem.firing_of_admits P s wf f admitted (ranged f.rule f.member)
    refine ⟨(f.rule, m), found, f.selection.made, admitted.1.2.2.1, ?_, madeLength.symm, ?_⟩
    · intro o member present
      exact Finset.disjoint_left.mp admitted.2.1.fresh (by simpa [Selection.commit] using member)
        (List.mem_toFinset.mpr present)
    · obtain ⟨_, σ, solved⟩ := admitted.2.2.1
      exact Sem.readsAs_unique (st := f.result (frames A) (Sem.state s)) ⟨σ, solved⟩ reads' reads
  · rintro ⟨⟨r, m⟩, found, ids, nodup, fresh, length, same⟩
    obtain ⟨member, admitted, reads⟩ := Sem.admits_stepFiring P s wf r m found ids nodup fresh length
    exact ⟨_, admitted, Sem.readsAs_of_same reads same⟩

/-- A firing the evaluator finds is a step to its publication. -/
theorem Semantics.groundStep_publish (P : List (Rule T)) {s : Store V} (wf : s.WellFormed)
    {r : Rule T} {m : Match V B} (found : (r, m) ∈ firings M P s) :
    Sem.GroundStep P s (publish s m) := by
  obtain ⟨member, admitted, reads⟩ := Sem.admits_stepFiring P s wf.1 r m found
    (freshIds s m.made.length) (freshIds_nodup s _) (freshIds_fresh wf _) (by simp [freshIds])
  refine ⟨_, admitted, ?_⟩
  rw [publish_eq_publishWith]
  exact reads

/-- **Quiescence is terminality**: the evaluator finds no firing exactly when the step theory has
no step. -/
theorem Semantics.firings_eq_nil_iff (P : List (Rule T)) (s : Store V) (wf : s.WellFormed)
    (ranged : ∀ r ∈ P, RangeRestricted M r) :
    firings M P s = [] ↔ ∀ s', ¬ Sem.GroundStep P s s' := by
  constructor
  · intro none s' step
    obtain ⟨f, found, _⟩ := (Sem.groundStep_iff P s s' wf.1 ranged).mp step
    rw [none] at found
    cases found
  · intro terminal
    cases first : firings M P s with
    | nil => rfl
    | cons f rest =>
        exact absurd (Sem.groundStep_publish P wf (r := f.1) (m := f.2)
          (by rw [first]; exact List.mem_cons_self)) (terminal _)

omit [DecidableEq V] [Inhabited T] in
theorem publish_wellFormed {B : Type w} {s : Store V} (wf : s.WellFormed) (m : Match V B) :
    (publish s m).WellFormed := by
  rw [publish_eq_publishWith]
  refine ⟨publishWith_distinct wf.1 m _ (by simp [freshIds]) (freshIds_nodup s _) (freshIds_fresh wf _), ?_⟩
  intro x member
  simp only [publishWith, List.mem_append, List.mem_filter] at member ⊢
  rcases member with ⟨inside, _⟩ | made
  · have := wf.2 x inside
    omega
  · have position := (List.of_mem_zip made).1
    obtain ⟨i, bound, equal⟩ := List.mem_map.mp position
    simp only [List.mem_range] at bound
    omega

/-- **A quiescent run is a path of steps to a store with no step.** -/
theorem Semantics.run_quiescent_sound (P : List (Rule T)) :
    ∀ (a : ℕ) (s s' : Store V), s.WellFormed → run M P a s = .quiescent s' →
      Relation.ReflTransGen (Sem.GroundStep P) s s' ∧ firings M P s' = []
  | 0, s, s', _, ran => by
      cases first : firings M P s with
      | nil =>
          rw [run, first] at ran
          cases ran
          exact ⟨.refl, first⟩
      | cons f rest =>
          rw [run, first] at ran
          cases ran
  | a + 1, s, s', wf, ran => by
      cases first : firings M P s with
      | nil =>
          rw [run, first] at ran
          cases ran
          exact ⟨.refl, first⟩
      | cons f rest =>
          rw [run, first] at ran
          obtain ⟨path, last⟩ := Semantics.run_quiescent_sound P a _ s' (publish_wellFormed wf f.2) ran
          exact ⟨.head (Sem.groundStep_publish P wf (r := f.1) (m := f.2)
            (by rw [first]; exact List.mem_cons_self)) path, last⟩

/-- **An exhausted run is a path of steps to a store that still has a step.** -/
theorem Semantics.run_exhausted_sound (P : List (Rule T)) :
    ∀ (a : ℕ) (s s' : Store V), s.WellFormed → run M P a s = .exhausted s' →
      Relation.ReflTransGen (Sem.GroundStep P) s s' ∧ ∃ s'', Sem.GroundStep P s' s''
  | 0, s, s', wf, ran => by
      cases first : firings M P s with
      | nil =>
          rw [run, first] at ran
          cases ran
      | cons f rest =>
          rw [run, first] at ran
          cases ran
          exact ⟨.refl, _, Sem.groundStep_publish P wf (r := f.1) (m := f.2)
            (by rw [first]; exact List.mem_cons_self)⟩
  | a + 1, s, s', wf, ran => by
      cases first : firings M P s with
      | nil =>
          rw [run, first] at ran
          cases ran
      | cons f rest =>
          rw [run, first] at ran
          obtain ⟨path, next⟩ := Semantics.run_exhausted_sound P a _ s' (publish_wellFormed wf f.2) ran
          exact ⟨.head (Sem.groundStep_publish P wf (r := f.1) (m := f.2)
            (by rw [first]; exact List.mem_cons_self)) path, next⟩

end Adequacy

end Mettapedia.Machines.TIsa.Derivation
