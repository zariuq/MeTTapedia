import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Equivalence.LaneSpecialization
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.SourceQuantifiers

/-!
# The lanes' space operations as instances of one transform, under the bag observation

`Equivalence.LaneSpecialization` states what "lane L's operation equals this transform instance"
means and proves the first instance, Prime `match` as `every (read p)`. This module proves the
others over the same compiled rows (`SourceCompilation`), under the bag lane: the Prime lane's
observation, and the coarsest one every lane shares.

* **`get-atoms` is `match` of a bare variable** (`getAtoms_rel`): with a sound, complete and
  minimal matcher, the bag of answers is the store's bag of labels, up to the declared theory
  (equal when the theory is equality, `getAtoms_eq`). Minimality is needed: a matcher that
  answers twice doubles every atom (`Controls.doubled_getAtoms`).
* **`add-atom` is the transform with no sources and the atom as template** (`add_fires_labels`):
  one row, one commit, which takes and reads nothing (`add_fires_monotone`) and adds the atom.
  The lanes answer differently (`()`, `true`, or the number routed); the answer is a lane
  convention, a function of the count (`addLane`, `add_specializes`).
* **`remove-atom` on the Prime and HE lanes is an `else` chain of three transforms**
  (`chain_fires_labels`, `chain_fires_exists`): take an occurrence of the identical atom; else take
  the occurrence of the `unique` atom equal to it modulo the second theory (alpha-equivalence in
  the runtimes); else nothing. The `unique` source is what makes two alpha-equal copies remove
  nothing. A runtime that removes only identical atoms is the chain without its middle
  transform (`exactRemove`). The PeTTa lane's removal of every matching atom is `all take`
  (`SourceQuantifiers.fires_allTake_removeAll`).
* **`collapse` over a `match` is an `all` source, not an `every`** (`collapse_answers_rel`): it
  answers exactly one value, the packed bag of `match`'s answers, also when nothing matches;
  `match` as `every` answers once per match, so nothing when nothing matches
  (`collapse_card`, `match_every_card`).
* **`unify` is a `let` source** (`unify_rows`, `unify_footprint`): it touches no occurrence of any
  store, and it has a row exactly when the pattern covers the value modulo the theory
  (`unify_rows_ne_zero_iff`).

The matcher for remove-atom's argument is a **constant-pattern layer** (`constLayer`,
`constMatcher`): the argument is a value, its variables literal, compared modulo a theory. It is
sound, complete, minimal and unitary.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.LaneSpecializations

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Equivalence.Lanes

universe uO uV uT uP

variable {O : Type uO} {V : Type uV} {T : Type uT} {P : Type uP}

/-! ## A bare variable has exactly one answer per value -/

section Variable

variable (L : TermLayer V T P)

/-- A pattern that is one variable: its only variable is `v`, and it instantiates to `v`'s value. -/
structure IsVarPattern (x : P) (v : V) : Prop where
  vars_eq : L.vars x = {v}
  inst_eq : ∀ σ, L.inst σ x = σ v

variable {L} {m : Matcher V T P}

/-- An answer of a bare variable from the empty substitution binds the variable, nothing else, to a
value equal to the matched one modulo the theory. -/
theorem var_answer_shape (sound : Matcher.Sound L m) {x : P} {v : V} (var : IsVarPattern L x v)
    {t : T} {τ : Subst V T} (answer : τ ∈ m x (fun _ => none) t) :
    (∀ w, w ≠ v → τ w = none) ∧ ∃ u, τ v = some u ∧ L.E u t := by
  have step := sound answer
  refine ⟨fun w ne => ?_, ?_⟩
  · have notIn : w ∉ L.vars x := by rw [var.vars_eq]; simpa using ne
    exact step.only w notIn
  · obtain ⟨u, inst, related⟩ := step.solves
    rw [var.inst_eq] at inst
    exact ⟨u, inst, related⟩

/-- **A bare variable has exactly one answer per value**, for a sound, complete, minimal matcher. -/
theorem var_answers [DecidableEq V] (sound : Matcher.Sound L m) (complete : Matcher.Complete L m)
    (minimal : Matcher.Minimal L m) {x : P} {v : V} (var : IsVarPattern L x v) (t : T) :
    ∃ τ u, m x (fun _ => none) t = [τ] ∧ τ v = some u ∧ L.E u t := by
  let τ' : Subst V T := fun w => if w = v then some t else none
  have step : L.Step (fun _ => none) x t τ' := by
    refine ⟨fun _ _ bound => (by simp at bound), fun w notIn => ?_, ⟨t, ?_, L.equivalence.refl t⟩⟩
    · have : w ≠ v := by rw [var.vars_eq] at notIn; simpa using notIn
      simp [τ', this]
    · rw [var.inst_eq]; simp [τ']
  obtain ⟨τ, member, -⟩ := complete (SubstEquiv.refl L.equivalence _) step
  have pairwise := minimal x (fun _ => none) t
  cases h : m x (fun _ => none) t with
  | nil => rw [h] at member; cases member
  | cons τ₁ rest =>
      cases rest with
      | nil =>
          obtain ⟨-, u, bound, related⟩ := var_answer_shape sound var (show τ₁ ∈ m x _ t by simp [h])
          exact ⟨τ₁, u, rfl, bound, related⟩
      | cons τ₂ rest' =>
          exfalso
          rw [h] at pairwise
          have notEquiv := List.rel_of_pairwise_cons pairwise (List.mem_cons_self ..)
          obtain ⟨only₁, u₁, bound₁, rel₁⟩ := var_answer_shape sound var (show τ₁ ∈ m x _ t by simp [h])
          obtain ⟨only₂, u₂, bound₂, rel₂⟩ := var_answer_shape sound var (show τ₂ ∈ m x _ t by simp [h])
          apply notEquiv
          intro w
          by_cases same : w = v
          · subst same
            rw [bound₁, bound₂]
            exact Option.Rel.some (L.equivalence.trans rel₁ (L.equivalence.symm rel₂))
          · rw [only₁ w same, only₂ w same]
            exact Option.Rel.none

/-- The template `[x]` of a bare variable instantiates to the variable's value. -/
theorem instBag_var {x : P} {v : V} (var : IsVarPattern L x v) {τ : Subst V T} {u : T}
    (bound : τ v = some u) : instBag L [x] τ = {u} := by
  unfold instBag instTemplate
  simp [var.inst_eq, bound]

end Variable

/-! ## `get-atoms` -/

section GetAtoms

variable [DecidableEq O] [DecidableEq V] {L : TermLayer V T P} {m : Matcher V T P} {label : O → T}

omit [DecidableEq O] in
/-- **`get-atoms` is `match` of a bare variable**: the bag of answers is the store's bag of labels,
each up to the declared theory. -/
theorem getAtoms_rel (sound : Matcher.Sound L m) (complete : Matcher.Complete L m)
    (minimal : Matcher.Minimal L m) {x : P} {v : V} (var : IsVarPattern L x v) (S : Finset O) :
    Multiset.Rel L.E (primeMatch L m label S x [x]) (labels label S) := by
  unfold primeMatch labels
  rw [show S.val.map label = S.val.bind fun o => {label o} by simp [Multiset.bind_singleton]]
  refine Multiset.rel_bind (fun o o' same => ?_) (Multiset.rel_eq.mpr rfl)
  subst same
  obtain ⟨τ, u, answers, bound, related⟩ := var_answers sound complete minimal var (label o)
  rw [answers]
  simp only [Multiset.coe_singleton, Multiset.singleton_bind, instBag_var var bound]
  exact Multiset.Rel.cons related Multiset.Rel.zero

omit [DecidableEq O] in
/-- **With equality as the theory, `get-atoms` is exactly the store's labels.** -/
theorem getAtoms_eq (equality : ∀ a b, L.E a b ↔ a = b) (sound : Matcher.Sound L m)
    (complete : Matcher.Complete L m) (minimal : Matcher.Minimal L m) {x : P} {v : V}
    (var : IsVarPattern L x v) (S : Finset O) :
    primeMatch L m label S x [x] = labels label S := by
  have rel := getAtoms_rel (label := label) sound complete minimal var S
  have : Multiset.Rel (· = ·) (primeMatch L m label S x [x]) (labels label S) :=
    rel.mono fun a _ b _ h => (equality a b).mp h
  exact Multiset.rel_eq.mp this

/-- **`get-atoms` specializes `every` over a bare-variable read** under the bag lane. -/
theorem getAtoms_specializes (equality : ∀ a b, L.E a b ↔ a = b) (sound : Matcher.Sound L m)
    (complete : Matcher.Complete L m) (minimal : Matcher.Minimal L m) {x : P} {v : V}
    (var : IsVarPattern L x v) :
    (bagLane (Finset O) T).Specializes (fun S => labels label S)
      (fun S => answers L m label (matchEvery x [x]) S) := fun S => by
  show labels label S = answers L m label (matchEvery x [x]) S
  rw [answers_matchEvery, getAtoms_eq equality sound complete minimal var]

end GetAtoms

/-! ## `add-atom` -/

section AddAtom

variable [DecidableEq O] {L : TermLayer V T P} {m : Matcher V T P} {label : O → T} {S : Finset O}

/-- A pattern that is the ground value `t`. -/
def IsGround (L : TermLayer V T P) (a : P) (t : T) : Prop := ∀ σ, L.inst σ a = some t

/-- `add-atom` as a transform: no sources (one empty row), the atom as template. -/
def addT (a : P) : Transform V T P := ⟨.done, [a]⟩

theorem add_rows {a : P} {t : T} (ground : IsGround L a t) :
    (addT a).rows L m label S = {(fun _ => none, [Pick.make {t}])} := by
  unfold Transform.rows addT
  rw [rows_done]
  simp [instTemplate, ground _]

/-- **Firing `add-atom`'s transform adds the atom**: the store's labels gain one copy. -/
theorem add_fires_labels [DecidableEq T] {a : P} {t : T} (ground : IsGround L a t) {c : Commit O T}
    (fires : Fires L m label S (addT a) c) : labels label (fire S c) = labels label S + {t} := by
  obtain ⟨x, member, linear, commit⟩ := fires
  have enabled : Enabled label S c := Fires.enabled ⟨x, member, linear, commit⟩
  rw [add_rows ground, Multiset.mem_singleton] at member
  subst member
  rw [labels_fire_of_isCommitOf commit linear enabled]
  simp [footprintOf_cons]

/-- **`add-atom`'s commit is monotone**: it takes nothing and queries nothing. -/
theorem add_fires_monotone {a : P} {t : T} (ground : IsGround L a t) {c : Commit O T}
    (fires : Fires L m label S (addT a) c) : c.Monotone := by
  obtain ⟨x, member, -, commit⟩ := fires
  rw [add_rows ground, Multiset.mem_singleton] at member
  subst member
  refine ⟨by rw [commit.taken]; simp [footprintOf_cons], ?_⟩
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro r member
  have := (commit.queries r).mp member
  simp [footprintOf_cons] at this

/-- A commit of `add-atom`'s transform exists, given fresh occurrences of every label. -/
theorem add_fires_exists {a : P} {t : T} (ground : IsGround L a t)
    (supply : ∀ (X : Finset O) (t : T), ∃ o, o ∉ X ∧ label o = t) :
    ∃ c, Fires L m label S (addT a) c := by
  obtain ⟨c, commit⟩ := exists_isCommitOf (S := S) supply (footprintOf [Pick.make ({t} : Multiset T)])
  exact ⟨c, _, by rw [add_rows ground]; exact Multiset.mem_singleton_self _,
    ⟨by simp [footprintOf_cons], by simp [footprintOf_cons]⟩, commit⟩

/-- What a lane answers for `add-atom`, as a function of the number of atoms added: `()` on the
Prime and HE lanes, `true` on the PeTTa lane, the count for a transform with a space destination. -/
inductive AddAnswer where
  | unit
  | true_
  | count (n : ℕ)
  deriving DecidableEq, Repr

/-- The add-atom lanes: the observation is the store's bag after the commit and the answer, which
the lane's convention computes from the count of what the transform made. -/
def addLane (convention : ℕ → AddAnswer) :
    Lane (Multiset T) T (Multiset T × AddAnswer) (Multiset T × AddAnswer) :=
  ⟨fun M made => (M + made, convention (Multiset.card made)), id⟩

/-- **`add-atom` specializes its transform under each lane's answer convention.** -/
theorem add_specializes (convention : ℕ → AddAnswer) (t : T) :
    (addLane convention).Specializes (fun M => (M + {t}, convention 1)) (fun _ => {t}) :=
  fun _ => rfl

end AddAtom

/-! ## A constant-pattern layer: values compared modulo a theory -/

section Constant

variable (E : T → T → Prop) (equivalence : Equivalence E)

/-- **The constant-pattern layer**: patterns are values with no variables, compared modulo `E`.
`remove-atom`'s argument is read this way: its variables are literal. -/
def constLayer : TermLayer V T T where
  E := E
  equivalence := equivalence
  vars := fun _ => ∅
  inst := fun _ p => some p
  inst_bound := by simp
  inst_local := by simp
  inst_congr := fun _ _ p _ => Option.Rel.some (equivalence.refl p)

variable [DecidableRel E]

/-- The matcher of the constant layer: the start, when the value is equal modulo `E`. -/
def constMatcher : Matcher V T T := fun p σ t => if E p t then [σ] else []

theorem constMatcher_sound : Matcher.Sound (constLayer (V := V) E equivalence) (constMatcher E) := by
  intro p σ t τ member
  unfold constMatcher at member
  split_ifs at member with related
  · rw [List.mem_singleton] at member
    subst member
    exact ⟨Extends.refl _, fun _ _ => rfl, ⟨p, rfl, related⟩⟩
  · cases member

theorem constMatcher_complete :
    Matcher.Complete (constLayer (V := V) E equivalence) (constMatcher E) := by
  intro p σ σ' t τ' same step
  have unchanged : τ' = σ' := funext fun v => step.only v (by simp [constLayer])
  obtain ⟨u, inst, related⟩ := step.solves
  have : u = p := by simpa [constLayer] using inst.symm
  subst this
  refine ⟨σ, by simp [constMatcher, show E u t from related], ?_⟩
  rw [unchanged]
  exact same

theorem constMatcher_minimal :
    Matcher.Minimal (constLayer (V := V) E equivalence) (constMatcher E) := by
  intro p σ t
  unfold constMatcher
  split_ifs <;> simp

theorem constMatcher_unitary : Matcher.Unitary (constMatcher (V := V) E) := by
  intro p σ t
  unfold constMatcher
  split_ifs <;> simp

theorem constMatcher_region (σ : Subst V T) (p t : T) :
    Matcher.region (constMatcher (V := V) E) σ p t = decide (E p t) := by
  unfold Matcher.region constMatcher
  split_ifs with h <;> simp [h]

end Constant

/-! ## `remove-atom` -/

section Remove

variable [DecidableEq O] [DecidableEq T] {label : O → T} {S : Finset O}

/-- The Prime and HE lanes' removal, counted: one copy of the identical atom; else the one atom
equal to it modulo `E`, if there is exactly one; else nothing. -/
def chainRemove (E : T → T → Prop) [DecidableRel E] (M : Multiset T) (a : T) : Multiset T :=
  if a ∈ M then M.erase a
  else if (M.filter (E a)).card = 1 then M - M.filter (E a)
  else M

omit [DecidableEq O] in
/-- Adding a value and then resolving the exact-first removal returns the
    original bag. -/
theorem chainRemove_after_add (E : T → T → Prop) [DecidableRel E]
    (M : Multiset T) (a : T) : chainRemove E (a ::ₘ M) a = M := by
  simp [chainRemove]

omit [DecidableEq O] in
/-- Adding after removal gives the original bag exactly when the exact value
    was already present. -/
theorem add_after_chainRemove_eq_iff (E : T → T → Prop) [DecidableRel E]
    (M : Multiset T) (a : T) : a ::ₘ chainRemove E M a = M ↔ a ∈ M := by
  constructor
  · intro same
    have present : a ∈ a ::ₘ chainRemove E M a := by simp
    simpa [same] using present
  · intro present
    simp [chainRemove, present]

omit [DecidableEq O] in
/-- The two authored orders agree exactly when the original bag contained
    the exact value. -/
theorem add_remove_order_agrees_iff (E : T → T → Prop) [DecidableRel E]
    (M : Multiset T) (a : T) :
    a ::ₘ chainRemove E M a = chainRemove E (a ::ₘ M) a ↔ a ∈ M := by
  rw [chainRemove_after_add]
  exact add_after_chainRemove_eq_iff E M a

/-- A removal of identical atoms only. -/
def exactRemove (M : Multiset T) (a : T) : Multiset T := if a ∈ M then M.erase a else M

/-- A transform **has a row** at a store: one of its rows is linear. -/
def HasRow (L : TermLayer V T P) (m : Matcher V T P) (label : O → T) (S : Finset O)
    (t : Transform V T P) : Prop :=
  ∃ x ∈ t.rows L m label S, (footprintOf x.2).Linear

/-- **`else X K`**: fire a commit of `X`; or, when `X` has no row, a commit of `K`. -/
def ElseFires (X K : Commit O T → Prop) (xHasRow : Prop) (c : Commit O T) : Prop :=
  X c ∨ (¬ xHasRow ∧ K c)

variable (E : T → T → Prop) (equivalence : Equivalence E) [DecidableRel E]

/-- The identity layer and its matcher. -/
abbrev idLayer : TermLayer V T T := constLayer (· = ·) ⟨fun _ => rfl, fun h => h.symm, fun h k => h.trans k⟩

/-- Take one occurrence of the identical atom. -/
def takeIdentical (a : T) : Transform V T T := ⟨.cons (.take a) .done, []⟩

/-- Take the occurrence of the unique atom equal to `a` modulo the theory. -/
def takeUnique (a : T) : Transform V T T := ⟨.cons (.unique .take a) .done, []⟩

/-- Do nothing. -/
def skipT : Transform V T T := ⟨.done, []⟩

/-- **The removal chain** `else (take a) (else (unique take a) ())`: identity first, the theory
second. -/
def ChainFires (a : T) (c : Commit O T) : Prop :=
  ElseFires (Fires (idLayer (V := V)) (constMatcher (· = ·)) label S (takeIdentical a))
    (ElseFires (Fires (constLayer (V := V) E equivalence) (constMatcher E) label S (takeUnique a))
      (Fires (constLayer (V := V) E equivalence) (constMatcher E) label S skipT)
      (HasRow (constLayer (V := V) E equivalence) (constMatcher E) label S (takeUnique a)))
    (HasRow (idLayer (V := V)) (constMatcher (· = ·)) label S (takeIdentical a)) c

variable {E equivalence}

omit [DecidableEq T] in
theorem rows_done_empty (L : TermLayer V T T) (m : Matcher V T T) (σ : Subst V T) :
    rows L m label S [] .done σ = {(σ, [Pick.make 0])} := by
  rw [rows_done]
  simp [instTemplate]

theorem mem_rows_takeIdentical {a : T} {x : Subst V T × List (Pick O T)} :
    x ∈ (takeIdentical (V := V) a).rows (idLayer (V := V)) (constMatcher (· = ·)) label S ↔
      ∃ o ∈ S, label o = a ∧ x = ((fun _ => none), [Pick.take o, Pick.make 0]) := by
  unfold Transform.rows takeIdentical
  rw [mem_rows_cons]
  constructor
  · rintro ⟨y, inStep, z, inRest, rfl⟩
    obtain ⟨o, inS, τ, answer, rfl⟩ := mem_stepRows_take.mp inStep
    simp only [constMatcher] at answer
    split_ifs at answer with same
    · rw [List.mem_singleton] at answer
      subst answer
      rw [rows_done_empty, Multiset.mem_singleton] at inRest
      subst inRest
      exact ⟨o, inS, same.symm, rfl⟩
    · cases answer
  · rintro ⟨o, inS, same, rfl⟩
    refine ⟨((fun _ => none), Pick.take o),
      mem_stepRows_take.mpr ⟨o, inS, _, by simp [constMatcher, same], rfl⟩,
      ((fun _ => none), [Pick.make 0]), ?_, rfl⟩
    rw [rows_done_empty]
    exact Multiset.mem_singleton_self _

/-- The region of the constant pattern `a` modulo `E`. -/
def eqRegion (E : T → T → Prop) [DecidableRel E] (a : T) : T → Bool := fun t => decide (E a t)

omit [DecidableEq T] in
theorem constRegion_eq (σ : Subst V T) (a : T) :
    Matcher.region (constMatcher (V := V) E) σ a = eqRegion E a :=
  funext fun t => constMatcher_region E σ a t

omit [DecidableEq T] in
theorem mem_rows_takeUnique {a : T} {x : Subst V T × List (Pick O T)} :
    x ∈ (takeUnique (V := V) a).rows (constLayer (V := V) E equivalence) (constMatcher E) label S ↔
      (regionOf label S (eqRegion E a)).card = 1 ∧
        x = ((fun _ => none), [Pick.query ⟨eqRegion E a, regionOf label S (eqRegion E a)⟩ true,
          Pick.make 0]) := by
  unfold Transform.rows takeUnique
  rw [mem_rows_cons]
  constructor
  · rintro ⟨y, inStep, z, inRest, rfl⟩
    obtain ⟨one, o, inRegion, τ, answer, rfl⟩ := mem_stepRows_unique.mp inStep
    simp only [constMatcher] at answer
    split_ifs at answer with same
    · rw [List.mem_singleton] at answer
      subst answer
      rw [rows_done_empty, Multiset.mem_singleton] at inRest
      subst inRest
      rw [constRegion_eq] at one ⊢
      exact ⟨one, rfl⟩
    · cases answer
  · rintro ⟨one, rfl⟩
    obtain ⟨o, single⟩ := Finset.card_eq_one.mp one
    have inRegion : o ∈ regionOf label S (eqRegion E a) := by rw [single]; exact Finset.mem_singleton_self o
    have related : E a (label o) := by simpa [eqRegion] using (mem_regionOf.mp inRegion).2
    refine ⟨((fun _ => none), Pick.query ⟨eqRegion E a, regionOf label S (eqRegion E a)⟩ true),
      mem_stepRows_unique.mpr ⟨by rw [constRegion_eq]; exact one, o, by rw [constRegion_eq]; exact inRegion,
        (fun _ => none), by simp [constMatcher, related], by rw [constRegion_eq]; simp⟩,
      ((fun _ => none), [Pick.make 0]), ?_, rfl⟩
    rw [rows_done_empty]
    exact Multiset.mem_singleton_self _

omit [DecidableEq T] in
theorem mem_rows_skip {L : TermLayer V T T} {m : Matcher V T T} {x : Subst V T × List (Pick O T)} :
    x ∈ (skipT (V := V)).rows L m label S ↔ x = ((fun _ => none), [Pick.make 0]) := by
  unfold Transform.rows skipT
  rw [rows_done_empty, Multiset.mem_singleton]

omit [DecidableEq T] in
/-- A commit of a footprint that makes nothing. -/
theorem isCommitOf_noMakes (fp : Footprint O T) (none : fp.makes = 0) :
    IsCommitOf label S fp ⟨fp.takes.toFinset, fp.keeps.toFinset, ∅, fp.queries.toList⟩ :=
  ⟨rfl, rfl, fun _ => Multiset.mem_toList, Finset.disjoint_empty_left _, by rw [none]; rfl⟩

theorem hasRow_takeIdentical_iff {a : T} :
    HasRow (idLayer (V := V)) (constMatcher (· = ·)) label S (takeIdentical a) ↔ a ∈ labels label S := by
  constructor
  · rintro ⟨x, member, -⟩
    obtain ⟨o, inS, same, -⟩ := mem_rows_takeIdentical.mp member
    exact Multiset.mem_map.mpr ⟨o, Finset.mem_val.mpr inS, same⟩
  · intro present
    obtain ⟨o, inS, same⟩ := Multiset.mem_map.mp present
    exact ⟨_, mem_rows_takeIdentical.mpr ⟨o, Finset.mem_val.mp inS, same, rfl⟩,
      ⟨by simp [footprintOf_cons], by simp [footprintOf_cons]⟩⟩

omit [DecidableEq O] [DecidableEq T] in
theorem card_regionOf_eq {a : T} :
    (regionOf label S (eqRegion E a)).card = ((labels label S).filter (E a)).card := by
  rw [← Finset.card_val, ← Multiset.card_map label, labels_regionOf]
  congr 1
  exact Multiset.filter_congr fun t _ => by simp [eqRegion]

omit [DecidableEq T] in
theorem hasRow_takeUnique_iff {a : T} :
    HasRow (constLayer (V := V) E equivalence) (constMatcher E) label S (takeUnique a) ↔
      ((labels label S).filter (E a)).card = 1 := by
  rw [← card_regionOf_eq]
  constructor
  · rintro ⟨x, member, -⟩
    exact (mem_rows_takeUnique.mp member).1
  · intro one
    exact ⟨_, mem_rows_takeUnique.mpr ⟨one, rfl⟩,
      ⟨by simpa [footprintOf_cons] using (regionOf label S (eqRegion E a)).nodup,
        by simp [footprintOf_cons]⟩⟩

/-- **Every commit the removal chain fires leaves the Prime/HE removal's bag.** -/
theorem chain_fires_labels {a : T} {c : Commit O T}
    (fires : ChainFires (V := V) (label := label) (S := S) E equivalence a c) :
    labels label (fire S c) = chainRemove E (labels label S) a := by
  unfold ChainFires ElseFires at fires
  rcases fires with first | ⟨noFirst, second | ⟨noSecond, third⟩⟩
  · have enabled := first.enabled
    obtain ⟨x, member, linear, commit⟩ := first
    obtain ⟨o, -, same, rfl⟩ := mem_rows_takeIdentical.mp member
    have present : a ∈ labels label S := (hasRow_takeIdentical_iff (V := V)).mp ⟨_, member, linear⟩
    rw [labels_fire_of_isCommitOf commit linear enabled, chainRemove, if_pos present]
    simp [footprintOf_cons, same, Multiset.sub_singleton]
  · have absent : a ∉ labels label S := fun present => noFirst ((hasRow_takeIdentical_iff (V := V)).mpr present)
    have enabled := second.enabled
    obtain ⟨x, member, linear, commit⟩ := second
    have one := (hasRow_takeUnique_iff (V := V)).mp ⟨_, member, linear⟩
    obtain ⟨-, rfl⟩ := mem_rows_takeUnique.mp member
    rw [labels_fire_of_isCommitOf commit linear enabled, chainRemove, if_neg absent, if_pos one]
    simp only [footprintOf_cons, footprintOf_nil, footprint_query, footprint_make, add_zero,
      Footprint.takes_add, Footprint.makes_add, ite_true]
    rw [show (fun x => label x) = label from rfl, labels_regionOf]
    congr 1
    exact Multiset.filter_congr fun t _ => by simp [eqRegion]
  · have absent : a ∉ labels label S := fun present => noFirst ((hasRow_takeIdentical_iff (V := V)).mpr present)
    have notOne : ((labels label S).filter (E a)).card ≠ 1 := fun one =>
      noSecond ((hasRow_takeUnique_iff (V := V)).mpr one)
    have enabled := third.enabled
    obtain ⟨x, member, linear, commit⟩ := third
    rw [mem_rows_skip] at member
    subst member
    rw [labels_fire_of_isCommitOf commit linear enabled, chainRemove, if_neg absent, if_neg notOne]
    simp [footprintOf_cons]

/-- **The removal chain always fires.** -/
theorem chain_fires_exists (a : T) : ∃ c, ChainFires (V := V) (label := label) (S := S) E equivalence a c := by
  by_cases present : a ∈ labels label S
  · obtain ⟨x, member, linear⟩ := (hasRow_takeIdentical_iff (V := V)).mpr present
    exact ⟨_, Or.inl ⟨x, member, linear, isCommitOf_noMakes _ (by
      obtain ⟨o, -, -, rfl⟩ := mem_rows_takeIdentical.mp member
      simp [footprintOf_cons])⟩⟩
  · have noFirst : ¬ HasRow (idLayer (V := V)) (constMatcher (· = ·)) label S (takeIdentical a) :=
      fun h => present ((hasRow_takeIdentical_iff (V := V)).mp h)
    by_cases one : ((labels label S).filter (E a)).card = 1
    · obtain ⟨x, member, linear⟩ := hasRow_takeUnique_iff (E := E) (equivalence := equivalence)
        (label := label) (S := S) |>.mpr one
      exact ⟨_, Or.inr ⟨noFirst, Or.inl ⟨x, member, linear, isCommitOf_noMakes _ (by
        obtain ⟨-, rfl⟩ := mem_rows_takeUnique.mp member
        simp [footprintOf_cons])⟩⟩⟩
    · have noSecond : ¬ HasRow (constLayer (V := V) E equivalence) (constMatcher E) label S
          (takeUnique a) := fun h => one ((hasRow_takeUnique_iff (V := V)).mp h)
      exact ⟨_, Or.inr ⟨noFirst, Or.inr ⟨noSecond, ⟨_, mem_rows_skip.mpr rfl,
        ⟨by simp [footprintOf_cons], by simp [footprintOf_cons]⟩,
        isCommitOf_noMakes _ (by simp [footprintOf_cons])⟩⟩⟩⟩

/-- **The removal of identical atoms only is the chain without its middle transform.** -/
theorem exact_fires_labels {a : T} {c : Commit O T}
    (fires : ElseFires (Fires (idLayer (V := V)) (constMatcher (· = ·)) label S (takeIdentical a))
      (Fires (idLayer (V := V)) (constMatcher (· = ·)) label S skipT)
      (HasRow (idLayer (V := V)) (constMatcher (· = ·)) label S (takeIdentical a)) c) :
    labels label (fire S c) = exactRemove (labels label S) a := by
  rcases fires with first | ⟨noFirst, third⟩
  · have enabled := first.enabled
    obtain ⟨x, member, linear, commit⟩ := first
    obtain ⟨o, -, same, rfl⟩ := mem_rows_takeIdentical.mp member
    have present : a ∈ labels label S := (hasRow_takeIdentical_iff (V := V)).mp ⟨_, member, linear⟩
    rw [labels_fire_of_isCommitOf commit linear enabled, exactRemove, if_pos present]
    simp [footprintOf_cons, same, Multiset.sub_singleton]
  · have absent : a ∉ labels label S := fun present => noFirst ((hasRow_takeIdentical_iff (V := V)).mpr present)
    have enabled := third.enabled
    obtain ⟨x, member, linear, commit⟩ := third
    rw [mem_rows_skip] at member
    subst member
    rw [labels_fire_of_isCommitOf commit linear enabled, exactRemove, if_neg absent]
    simp [footprintOf_cons]

end Remove

/-! ## `collapse` over a `match` -/

section Collapse

variable [DecidableEq O] [DecidableEq V] {L : TermLayer V T P} {m : Matcher V T P} {label : O → T}

variable (L m) in
/-- The fold of `collapse (match p template)`: the packed bag of the template's instances for the
matched values. -/
def collapseFold (p : P) (template : List P) (pack : Multiset T → T) : Multiset T → T :=
  fun b => pack (b.bind fun t => (↑(m p (fun _ => none) t) : Multiset (Subst V T)).bind (instBag L template))

variable (L m) in
/-- **`collapse (match p template)` as a transform**: an `all` read of the region of `p`, its folded
value bound to the collection variable `xs`, which is the template. -/
def collapseT (p xs : P) (template : List P) (pack : Multiset T → T) : Transform V T P :=
  ⟨.cons (.all .read p xs (collapseFold L m p template pack)) .done, [xs]⟩

omit [DecidableEq O] [DecidableEq V] in
/-- Prime's `match` reads only the region of its pattern. -/
theorem primeMatch_eq_region (S : Finset O) (p : P) (template : List P) :
    primeMatch L m label S p template =
      ((regionOf label S (Matcher.region m (fun _ => none) p)).val.map label).bind
        fun t => (↑(m p (fun _ => none) t) : Multiset (Subst V T)).bind (instBag L template) := by
  unfold primeMatch
  rw [bind_eq_bind_regionOf (label := label) (r := Matcher.region m (fun _ => none) p)
    fun o out => by simp [matcher_eq_nil_of_region out], Multiset.bind_map]

/-- **`collapse` over a `match` answers one value: the packed bag of `match`'s answers**, up to
the theory, whatever the store. -/
theorem collapse_answers_rel (sound : Matcher.Sound L m) (complete : Matcher.Complete L m)
    (minimal : Matcher.Minimal L m) {xs : P} {v : V} (var : IsVarPattern L xs v) (S : Finset O)
    (p : P) (template : List P) (pack : Multiset T → T) :
    Multiset.Rel L.E (answers L m label (collapseT L m p xs template pack) S)
      {pack (primeMatch L m label S p template)} := by
  obtain ⟨τ, u, single, bound, related⟩ := var_answers sound complete minimal var
    (collapseFold L m p template pack
      ((regionOf label S (Matcher.region m (fun _ => none) p)).val.map label))
  have rowsEq : (collapseT L m p xs template pack).rows L m label S =
      {(τ, [Pick.query ⟨Matcher.region m (fun _ => none) p,
        regionOf label S (Matcher.region m (fun _ => none) p)⟩ false, Pick.make {u}])} := by
    unfold Transform.rows collapseT
    simp only [rows, stepRows, single, instTemplate]
    simp [var.inst_eq, bound]
  unfold answers
  rw [rowsEq]
  simp only [Multiset.map_singleton, Multiset.sum_singleton, footprintOf_cons, footprintOf_nil,
    footprint_query, footprint_make, add_zero, Footprint.makes_add]
  simp only [zero_add]
  refine Multiset.Rel.cons ?_ Multiset.Rel.zero
  rw [primeMatch_eq_region]
  exact related

/-- `collapse` over a `match` answers exactly once. -/
theorem collapse_card (sound : Matcher.Sound L m) (complete : Matcher.Complete L m)
    (minimal : Matcher.Minimal L m) {xs : P} {v : V} (var : IsVarPattern L xs v) (S : Finset O)
    (p : P) (template : List P) (pack : Multiset T → T) :
    Multiset.card (answers L m label (collapseT L m p xs template pack) S) = 1 :=
  (Multiset.card_eq_card_of_rel (collapse_answers_rel sound complete minimal var S p template pack)).trans rfl

omit [DecidableEq V] in
/-- `match` as `every` answers once per match. -/
theorem match_every_card (S : Finset O) (p : P) (template : List P) :
    Multiset.card (answers L m label (matchEvery p template) S) =
      Multiset.card (primeMatch L m label S p template) := by
  rw [answers_matchEvery]

/-- **The vacuity separation**: when nothing matches, `match` as `every` answers nothing and
`collapse` as `all` answers once (the packed empty bag). -/
theorem collapse_vacuous (sound : Matcher.Sound L m) (complete : Matcher.Complete L m)
    (minimal : Matcher.Minimal L m) {xs : P} {v : V} (var : IsVarPattern L xs v) {S : Finset O}
    {p : P} (nothing : ∀ o ∈ S, m p (fun _ => none) (label o) = []) (template : List P)
    (pack : Multiset T → T) :
    answers L m label (matchEvery p template) S = 0 ∧
      Multiset.Rel L.E (answers L m label (collapseT L m p xs template pack) S) {pack 0} := by
  have zero : primeMatch L m label S p template = 0 := by
    unfold primeMatch
    rw [Multiset.bind_congr (g := fun _ => 0) fun o member => by
      rw [nothing o (Finset.mem_val.mp member)]; rfl, Multiset.bind_zero]
  refine ⟨by rw [answers_matchEvery, zero], ?_⟩
  have := collapse_answers_rel (label := label) sound complete minimal var S p template pack
  rwa [zero] at this

end Collapse

/-! ## `unify` -/

section Unify

variable [DecidableEq O] {L : TermLayer V T P} {m : Matcher V T P} {label : O → T} {S : Finset O}

/-- **`unify` as a transform**: a `let` source matching the pattern against the value, the
`then` branch as template. It names no space. -/
def unifyT (a : P) (b : T) (template : List P) : Transform V T P :=
  ⟨.cons (.letBind a fun _ => [b]) .done, template⟩

theorem unify_rows (a : P) (b : T) (template : List P) :
    (unifyT a b template).rows L m label S =
      (↑(m a (fun _ => none) b) : Multiset (Subst V T)).bind
        fun τ => (rows L m label S template .done τ).map fun y => (y.1, Pick.result 0 :: y.2) := by
  unfold Transform.rows unifyT
  simp only [rows, stepRows, List.zipIdx_cons, List.zipIdx_nil]
  simp only [Multiset.coe_singleton, Multiset.singleton_bind]
  rw [Multiset.bind_map]

/-- **`unify` touches no occurrence**: its rows take, keep and read nothing. -/
theorem unify_footprint {a : P} {b : T} {template : List P} {y : Subst V T × List (Pick O T)}
    (member : y ∈ (unifyT a b template).rows L m label S) :
    (footprintOf y.2).takes = 0 ∧ (footprintOf y.2).keeps = 0 ∧ (footprintOf y.2).queries = 0 := by
  rw [unify_rows] at member
  obtain ⟨τ, -, inner⟩ := Multiset.mem_bind.mp member
  obtain ⟨z, inDone, rfl⟩ := Multiset.mem_map.mp inner
  rw [rows_done] at inDone
  cases h : instTemplate L τ template with
  | none => rw [h] at inDone; simp at inDone
  | some ls =>
      rw [h, Multiset.mem_singleton] at inDone
      subst inDone
      simp [footprintOf_cons]

/-- **`unify` has a row exactly when the pattern covers the value modulo the theory**, for a sound
and complete matcher and a template that instantiates under every answer. -/
theorem unify_rows_ne_zero_iff (sound : Matcher.Sound L m) (complete : Matcher.Complete L m)
    {a : P} {b : T} {template : List P}
    (instantiates : ∀ τ ∈ m a (fun _ => none) b, (instTemplate L τ template).isSome) :
    (unifyT a b template).rows L m label S ≠ 0 ↔ L.Covers (fun _ => none) a b := by
  rw [← Matcher.region_eq_true_iff sound complete, Matcher.region_eq_true_iff_exists, unify_rows]
  constructor
  · intro nonzero
    by_contra noAnswer
    push Not at noAnswer
    apply nonzero
    have : m a (fun _ => none) b = [] := List.eq_nil_iff_forall_not_mem.mpr noAnswer
    rw [this]
    rfl
  · rintro ⟨τ, answer⟩ zero
    obtain ⟨ls, hls⟩ := Option.isSome_iff_exists.mp (instantiates τ answer)
    have : ((τ, [Pick.result 0, Pick.make (ls : Multiset T)]) : Subst V T × List (Pick O T)) ∈
        (↑(m a (fun _ => none) b) : Multiset (Subst V T)).bind
          fun τ => (rows L m label S template .done τ).map fun y => (y.1, Pick.result 0 :: y.2) := by
      refine Multiset.mem_bind.mpr ⟨τ, by simpa using answer, ?_⟩
      rw [rows_done, hls]
      simp
    rw [zero] at this
    simp at this

end Unify

/-! ## Controls -/

namespace Controls

section Doubled

variable [DecidableEq O] {L : TermLayer V T P} {m : Matcher V T P} {label : O → T}

/-- A matcher that answers everything twice: still sound and complete, not minimal. -/
def doubled (m : Matcher V T P) : Matcher V T P := fun p σ t => m p σ t ++ m p σ t

omit [DecidableEq O] in
theorem primeMatch_doubled (S : Finset O) (p : P) (template : List P) :
    primeMatch L (doubled m) label S p template =
      primeMatch L m label S p template + primeMatch L m label S p template := by
  unfold primeMatch doubled
  rw [← Multiset.bind_add]
  refine Multiset.bind_congr fun o _ => ?_
  rw [← Multiset.coe_add, Multiset.add_bind]

omit [DecidableEq O] in
/-- **Minimality is needed for `get-atoms`**: a doubled matcher answers every atom twice, so on a
nonempty store its bag is not the store's. -/
theorem doubled_getAtoms [DecidableEq V] (equality : ∀ a b, L.E a b ↔ a = b)
    (sound : Matcher.Sound L m) (complete : Matcher.Complete L m) (minimal : Matcher.Minimal L m)
    {x : P} {v : V} (var : IsVarPattern L x v) {S : Finset O} (nonempty : S.Nonempty) :
    primeMatch L (doubled m) label S x [x] ≠ labels label S := by
  rw [primeMatch_doubled, getAtoms_eq equality sound complete minimal var]
  intro same
  have := congrArg Multiset.card same
  simp only [Multiset.card_add, labels, Multiset.card_map, Finset.card_val] at this
  have : 0 < S.card := Finset.card_pos.mpr nonempty
  omega

end Doubled

/-- Four stored atoms: `(p $x)`, `(p $y)`, `(p $w)` are alpha-equal and not identical; `(p 1)` is
alone. -/
inductive Atm where
  | px
  | py
  | pw
  | p1
  deriving DecidableEq, Repr

open Atm

/-- The alpha classes. -/
def Atm.shape : Atm → ℕ
  | px => 0
  | py => 0
  | pw => 0
  | p1 => 1

/-- Alpha-equivalence of the four atoms. -/
def alphaEq (a b : Atm) : Prop := a.shape = b.shape

instance : DecidableRel alphaEq := fun a b => inferInstanceAs (Decidable (a.shape = b.shape))

/-- **Two alpha-equal copies: the chain removes nothing**, where taking one atom modulo alpha
would remove either copy. -/
theorem two_alpha_copies :
    chainRemove alphaEq ({px, py} : Multiset Atm) pw = {px, py} ∧
      ({px, py} : Multiset Atm).erase px ≠ {px, py} ∧ ({px, py} : Multiset Atm).erase py ≠ {px, py} := by
  decide

/-- Excluding a kept copy before resolving a legacy removal changes an
    ambiguous alpha removal into a successful one. -/
theorem preexclude_changes_alpha_ambiguity :
    chainRemove alphaEq ({px, py} : Multiset Atm) pw = {px, py} ∧
      ({px} + chainRemove alphaEq ({py} : Multiset Atm) pw) = {px} := by
  decide

/-- Even with an exact match, pre-excluding it selects a different
    alpha-equivalent value than resolving against the full bag first. -/
theorem preexclude_changes_exact_precedence :
    chainRemove alphaEq ({px, py} : Multiset Atm) px = {py} ∧
      ({px} + chainRemove alphaEq ({py} : Multiset Atm) px) = {px} := by
  decide

/-- **One alpha-equal copy: the chain removes it, the identical-only removal keeps it**, so a
runtime that removes alpha-equal atoms and one that removes identical atoms only are different
lanes. -/
theorem one_alpha_copy :
    chainRemove alphaEq ({px} : Multiset Atm) pw = 0 ∧ exactRemove ({px} : Multiset Atm) pw = {px} := by
  decide

/-- **An identical copy is removed by both.** -/
theorem identical_copy :
    chainRemove alphaEq ({p1, px} : Multiset Atm) p1 = {px} ∧
      exactRemove ({p1, px} : Multiset Atm) p1 = {px} := by
  decide

end Controls

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.LaneSpecializations
