import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NamedSpacesAuthority

/-!
# Selection relative to the actor's reach

The resolved-location law of `NamedSpaces` (`Resolved`, `LocatedStep`) is withdrawn here. It asked
the store before the step to resolve every space position of a rule, and so refused two firings a
mind must make without friction:

* **atomic indirection**: read a space handle at an index and use it in the same firing;
* **search**: a rule whose space is a variable finds a match in whichever held space has one.

It is replaced by selection relative to the acting context's reach (`ReachAdmits`, `ReachStep`).
An actor is the set `K` of terms it holds. A selection of the candidate step is admitted when

* the actor holds the rule (`HoldsRule r K`);
* every occurrence the selection takes or reads lies at a name `K` reaches before the step
  (`Reach`, the least set of names closed under reading at reached names);
* the selection's own problem resolves every space position of the rule (take, read, produce,
  absence, count). Ports of one firing may resolve one another's spaces, and an unbound space
  variable of a take or read port ranges over the actor's reach.

The step is the candidate step on such a selection (`ReachStep.step`): no second step relation.

## What is proved, with no pre-selection law

* **What a firing resolves, it reaches** (`resolved_in_firing_reached`): every term the actor
  holds that the selection's problem resolves to a name resolves to a reached name. The problem
  adds only equations between the actor's own terms and labels at reached names, so it can
  distinguish no name the actor could not reach. Hence every space position lands in reach
  (`ReachAdmits.space_reached`), and so does every made occurrence (`ReachAdmits.made_reached`).
* **Every effect lies in reach** (`ReachAdmits.effects_in_reach`): taken, read and made
  occurrences, and every occurrence an absence or count check can match
  (`ReachAdmits.check_matches_reached`).
* **No name, no effect, no observation.** Outside reach nothing leaves, nothing arrives and no
  space position resolves there (`unreached_no_effect`). Validity depends only on the store and
  the occurrences at reached names (`reachAdmits_iff_of_agree`); reach itself depends only on
  those (`AgreeOnReach.reached_iff`). Two configurations that differ only at an unreached name admit
  the same selections (`unreached_no_observation`).
* **Reach grows only by reading or by creation** (`reach_after_reach_step`,
  `reach_after_reach_run`): along the actor's own steps it reaches nothing it did not reach
  before; another party learns from them only what it reached jointly with the actor
  (`other_reach_after_reach_step`). The step keeps configurations well located
  (`ReachStep.wellLocated`).
* **The old law's firings are admitted** (`located_step_is_reach_step`), and more terms admit more
  firings (`ReachStep.mono`).
* **Zero friction for the owner** (`owner_admits_iff`, `owner_admits_iff_outputs`): an actor that
  possesses every name is admitted exactly the candidate step's selections whose produce and check
  spaces name a space; take and read ports need nothing (`selected_ports_resolve`).

## Controls (`ReachControls`)

* *Indirection*: read `(index task s)` at space 1, then `(edge x y)` at `s`, in one firing:
  admitted, and refused by the old law (`indirection_separates`).
* *Reach by reading*: with the handle present, space 7 is reached through the handle's label and
  the firing touches it (`handle_gives_reach`); without it, 7 is not reached and no step of the
  actor touches 7 (`no_handle_no_reach`).
* *Search*: a rule with an unbound space variable finds the contradiction in the one held space
  that has one (`search_finds_held_contradiction`) and only there (`search_only_there`), while an
  unheld space with a contradiction is ignored although the candidate step would take it
  (`search_ignores_unheld`).
* *Guest*: an actor holding only `pub` cannot select at `thm` with an unbound space variable,
  although `thm` holds a match (`guest_match_at_thm`, `guest_cannot_select_at_thm`).
* *Smallest separation*: a single take at an unbound space variable is admitted to an actor that
  reaches the space and refused by the old law (`one_port_search_separates`).
* *The withdrawn law's own example*: of the two selections of the ambient take, both valid for the
  candidate step, the actor holding space 1 is admitted the one at 1 and refused the one at 2
  (`ambient_take_within_reach`).
* *Why every check space must resolve*: in the candidate step an absence check at an unbound space
  observes `thm` (`candidate_absence_observes_thm`); the reach step refuses it
  (`reach_refuses_unbound_absence`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NamedSpaces

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

universe uT uS uN uO

/-! ## The terms of a rule -/

section Terms

variable {T : Type uT} {S : Type uS} {N : Type uN} {A : SubstitutionAction T S}

variable (sts : SpaceTerms A N) in
/-- The terms a located rule writes: its take and read ports as terms, both sides of its tells,
its produced terms and its space positions. -/
def LocatedRule.terms (r : LocatedRule T) : Set T :=
  {t | t ∈ (r.toRule sts).take ++ (r.toRule sts).read ∨ (∃ e ∈ r.tell, t = e.1 ∨ t = e.2) ∨
    t ∈ (r.toRule sts).produce ∨ t ∈ r.spaces}

variable {sts : SpaceTerms A N}

/-- A rule holds the terms it writes. -/
theorem holdsRule_terms (r : LocatedRule T) : HoldsRule (sts := sts) r (r.terms sts) :=
  ⟨fun _ member => Or.inl member,
    fun e member => ⟨Or.inr (Or.inl ⟨e, member, Or.inl rfl⟩),
      Or.inr (Or.inl ⟨e, member, Or.inr rfl⟩)⟩,
    fun _ member => Or.inr (Or.inr (Or.inl member)),
    fun _ member => Or.inr (Or.inr (Or.inr member))⟩

theorem HoldsRule.mono {r : LocatedRule T} {K K' : Set T} (holds : HoldsRule (sts := sts) r K)
    (more : K ⊆ K') : HoldsRule (sts := sts) r K' :=
  ⟨fun p member => more (holds.ports p member),
    fun e member => ⟨more (holds.tells e member).1, more (holds.tells e member).2⟩,
    fun p member => more (holds.produce p member), fun s member => more (holds.spaces s member)⟩

end Terms

/-! ## Ports and the selection's equations -/

section Ports

variable {T : Type uT} {O : Type uO}

/-- Each pattern is paired, in the selection's equations, with one selected occurrence. -/
theorem mem_equations_of_mem (label : O → T) :
    ∀ {patterns : List T} {selected : List O}, patterns.length = selected.length →
      ∀ {p : T}, p ∈ patterns → ∃ o ∈ selected, (p, label o) ∈ Selection.equations label patterns selected
  | [], _, _, _, member => by cases member
  | _ :: _, [], lengths, _, _ => by simp at lengths
  | q :: qs, o :: os, lengths, p, member => by
      rcases List.mem_cons.mp member with rfl | tail
      · exact ⟨o, List.mem_cons_self, by simp [Selection.equations]⟩
      · obtain ⟨o', mem', pair⟩ := mem_equations_of_mem label (Nat.succ.inj lengths) tail
        refine ⟨o', List.mem_cons_of_mem _ mem', ?_⟩
        simp only [Selection.equations, List.zipWith_cons_cons, List.mem_cons] at pair ⊢
        exact Or.inr pair

/-- Each selected occurrence is paired, in the selection's equations, with one pattern. -/
theorem mem_equations_of_mem_right (label : O → T) :
    ∀ {patterns : List T} {selected : List O}, patterns.length = selected.length →
      ∀ {o : O}, o ∈ selected →
        ∃ p ∈ patterns, (p, label o) ∈ Selection.equations label patterns selected
  | _, [], _, _, member => by cases member
  | [], _ :: _, lengths, _, _ => by simp at lengths
  | q :: qs, o' :: os, lengths, o, member => by
      rcases List.mem_cons.mp member with rfl | tail
      · exact ⟨q, List.mem_cons_self, by simp [Selection.equations]⟩
      · obtain ⟨p, mem', pair⟩ := mem_equations_of_mem_right label (Nat.succ.inj lengths) tail
        refine ⟨p, List.mem_cons_of_mem _ mem', ?_⟩
        simp only [Selection.equations, List.zipWith_cons_cons, List.mem_cons] at pair ⊢
        exact Or.inr pair

end Ports

/-! ## The reach step -/

section ReachSelection

variable {T : Type uT} {S : Type uS} {N : Type uN} {O : Type uO} [DecidableEq N] [DecidableEq O]
  {A : SubstitutionAction T S} {sts : SpaceTerms A N} (ns : NameSwap sts)

/-- The names the terms `K` reach at a configuration whose labels follow `located`. -/
abbrev Reached (K : Set T) (space payload : O → T) (C : Configuration T O) (k : N) : Prop :=
  Reach ns C.equations space (located sts space payload) C.present K k

/-- An occurrence lies at a name the terms `K` reach. -/
def AtReached (K : Set T) (space payload : O → T) (C : Configuration T O) (o : O) : Prop :=
  ∃ k, Reached ns K space payload C k ∧ ResolvesTo sts C.equations (space o) k

/-- **Selection relative to reach.** The actor holding the terms `K` may fire a selection of the
rule when it holds the rule, the selection is valid for the candidate step, every occurrence it
takes or reads lies at a name `K` reaches, and the selection's own problem resolves every space
position of the rule. No resolution by the store before selection is asked. -/
structure ReachAdmits (K : Set T) (space payload : O → T) (r : LocatedRule T)
    (C : Configuration T O) (selection : Selection O) : Prop where
  holds : HoldsRule (sts := sts) r K
  valid : selection.Valid A (located sts space payload) (r.toRule sts) C
  selected : ∀ o ∈ selection.taken ++ selection.read, AtReached ns K space payload C o
  resolved : ∀ s ∈ r.spaces,
    Resolves sts (selection.problem (located sts space payload) (r.toRule sts) C) s

/-- **The reach step**: the candidate step on a selection the actor's reach admits. -/
def ReachStep (K : Set T) (space payload : O → T) (r : LocatedRule T)
    (before after : Configuration T O) : Prop :=
  ∃ selection, ReachAdmits ns K space payload r before selection ∧
    after = selection.result (located sts space payload) (r.toRule sts) before

/-- Two configurations agree on the reach of `K`: one store, and the same occurrences among those
at names `K` reaches in the first. -/
def AgreeOnReach (K : Set T) (space payload : O → T) (C D : Configuration T O) : Prop :=
  C.equations = D.equations ∧
    ∀ o, AtReached ns K space payload C o → (o ∈ C.present ↔ o ∈ D.present)

variable {ns}
variable {K : Set T} {space payload : O → T} {r : LocatedRule T} {C : Configuration T O}
  {selection : Selection O}

/-- The reach step is the candidate step on an admitted selection. -/
theorem ReachStep.step {D : Configuration T O} (step : ReachStep ns K space payload r C D) :
    Step A (located sts space payload) (r.toRule sts) C D := by
  obtain ⟨selection, admits, rfl⟩ := step
  exact ⟨selection, admits.valid, rfl⟩

theorem ReachAdmits.present (admits : ReachAdmits ns K space payload r C selection) {o : O}
    (member : o ∈ selection.taken ++ selection.read) : o ∈ C.present := by
  rcases List.mem_append.mp member with taken | read
  · exact admits.valid.occurrences.taken_subset (by simpa [Selection.commit] using taken)
  · exact admits.valid.occurrences.kept_subset (by simpa [Selection.commit] using read)

/-- The labels a firing selects are labels at reached names. -/
theorem ReachAdmits.selected_labels (admits : ReachAdmits ns K space payload r C selection) :
    ∀ o ∈ selection.taken ++ selection.read,
      located sts space payload o ∈ labelsAt sts C.equations space (located sts space payload)
        C.present (Reached ns K space payload C) := by
  intro o member
  obtain ⟨k, reached, at_k⟩ := admits.selected o member
  exact ⟨o, admits.present member, k, reached, at_k, rfl⟩

/-- **What a firing resolves, it reaches.** If every occurrence a valid selection takes or reads
lies at a reached name, every term of `K` that the selection's problem resolves to a name resolves
to a reached name. -/
theorem resolved_in_firing_reached_of
    (valid : selection.Valid A (located sts space payload) (r.toRule sts) C)
    (ports : ∀ p ∈ (r.toRule sts).take ++ (r.toRule sts).read, p ∈ K)
    (tells : ∀ e ∈ r.tell, e.1 ∈ K ∧ e.2 ∈ K)
    (selected : ∀ o ∈ selection.taken ++ selection.read, AtReached ns K space payload C o)
    {s : T} (member : s ∈ K) {n : N}
    (resolved : ResolvesTo sts (selection.problem (located sts space payload) (r.toRule sts) C)
      s n) :
    Reached ns K space payload C n := by
  have labels : ∀ o ∈ selection.taken ++ selection.read,
      located sts space payload o ∈ K ∪ labelsAt sts C.equations space (located sts space payload)
        C.present (Reached ns K space payload C) := by
    intro o selectedMember
    obtain ⟨k, reached, at_k⟩ := selected o selectedMember
    have present : o ∈ C.present := by
      rcases List.mem_append.mp selectedMember with taken | read
      · exact valid.occurrences.taken_subset (by simpa [Selection.commit] using taken)
      · exact valid.occurrences.kept_subset (by simpa [Selection.commit] using read)
    exact Or.inr ⟨o, present, k, reached, at_k, rfl⟩
  have after : Possesses ns
      (selection.result (located sts space payload) (r.toRule sts) C).equations
      (K ∪ labelsAt sts C.equations space (located sts space payload) C.present
        (Reached ns K space payload C)) n :=
    resolved_name_possessed valid.consistent (Or.inl member) resolved
  have before := possession_after_step valid (fun p portMember => Or.inl (ports p portMember))
    (fun e tellMember => ⟨Or.inl (tells e tellMember).1, Or.inl (tells e tellMember).2⟩)
    labels after
  exact Reach.closed before

/-- **What a firing resolves, it reaches**, for a rule the actor holds. -/
theorem resolved_in_firing_reached
    (valid : selection.Valid A (located sts space payload) (r.toRule sts) C)
    (holds : HoldsRule (sts := sts) r K)
    (selected : ∀ o ∈ selection.taken ++ selection.read, AtReached ns K space payload C o)
    {s : T} (member : s ∈ K) {n : N}
    (resolved : ResolvesTo sts (selection.problem (located sts space payload) (r.toRule sts) C)
      s n) :
    Reached ns K space payload C n :=
  resolved_in_firing_reached_of valid holds.ports holds.tells selected member resolved

/-- **Every space position of an admitted firing lands in reach.** -/
theorem ReachAdmits.space_reached (admits : ReachAdmits ns K space payload r C selection) {s : T}
    (member : s ∈ r.spaces) :
    ∃ k, Reached ns K space payload C k ∧
      ResolvesTo sts (selection.problem (located sts space payload) (r.toRule sts) C) s k := by
  obtain ⟨k, at_k⟩ := admits.resolved s member
  exact ⟨k, resolved_in_firing_reached admits.valid admits.holds admits.selected
    (admits.holds.spaces s member) at_k, at_k⟩

omit [DecidableEq N] in
/-- A made occurrence carries the space term and the payload of one of the rule's produce
ports. -/
theorem made_port (valid : selection.Valid A (located sts space payload) (r.toRule sts) C)
    {o : O} (made : o ∈ selection.made) :
    ∃ port ∈ r.produce, port.1 = space o ∧ port.2 = payload o := by
  have output : located sts space payload o ∈ (r.toRule sts).produce := by
    rw [← valid.outputs]
    exact List.mem_map.mpr ⟨o, made, rfl⟩
  simp only [LocatedRule.toRule, List.mem_map] at output
  obtain ⟨port, member, same⟩ := output
  obtain ⟨spaces, payloads⟩ := sts.atSpace_injective _ _ _ _ same
  exact ⟨port, member, spaces, payloads⟩

/-- **A made occurrence lies at a reached name**, resolved by the store after the step. -/
theorem ReachAdmits.made_reached (admits : ReachAdmits ns K space payload r C selection) {o : O}
    (made : o ∈ selection.made) :
    ∃ k, Reached ns K space payload C k ∧
      ResolvesTo sts (selection.problem (located sts space payload) (r.toRule sts) C)
        (space o) k := by
  obtain ⟨port, member, same, _⟩ := made_port admits.valid made
  obtain ⟨k, reached, at_k⟩ := admits.space_reached (produce_space_mem member)
  exact ⟨k, reached, same ▸ at_k⟩

/-- **A check looks only within reach.** An occurrence present before the step that matches a
pattern placed at one of the rule's space positions, under a solution of the selection's problem,
lies at a reached name. -/
theorem ReachAdmits.check_matches_reached (admits : ReachAdmits ns K space payload r C selection)
    (wellLocated : WellLocated sts space C) {s p : T} (member : s ∈ r.spaces) {σ : S}
    (solved : A.Models σ (selection.problem (located sts space payload) (r.toRule sts) C))
    {o : O} (present : o ∈ C.present)
    (matching : A.E (A.apply σ (sts.atSpace s p)) (A.apply σ (located sts space payload o))) :
    AtReached ns K space payload C o := by
  obtain ⟨k, reached, at_k⟩ := admits.space_reached member
  obtain ⟨m, at_m⟩ := wellLocated o present
  simp only [located, sts.apply_atSpace, sts.E_atSpace] at matching
  have lifted : ResolvesTo sts (selection.problem (located sts space payload) (r.toRule sts) C)
      (space o) m :=
    ResolvesTo.of_refines admits.valid.refines at_m
  have names : k = m := at_k.name_eq solved lifted matching.1
  subst names
  exact ⟨k, reached, at_m⟩

/-- **Every effect of an admitted firing lies in reach**: what it takes and reads, what it makes,
and what its checks can match. -/
theorem ReachAdmits.effects_in_reach (admits : ReachAdmits ns K space payload r C selection)
    (wellLocated : WellLocated sts space C) :
    (∀ o ∈ selection.taken ++ selection.read, AtReached ns K space payload C o) ∧
      (∀ o ∈ selection.made, ∃ k, Reached ns K space payload C k ∧
        ResolvesTo sts (selection.problem (located sts space payload) (r.toRule sts) C)
          (space o) k) ∧
      ∀ s ∈ r.spaces, ∀ p : T, ∀ σ : S,
        A.Models σ (selection.problem (located sts space payload) (r.toRule sts) C) →
          ∀ o ∈ C.present,
            A.E (A.apply σ (sts.atSpace s p)) (A.apply σ (located sts space payload o)) →
              AtReached ns K space payload C o :=
  ⟨admits.selected, fun _ made => admits.made_reached made,
    fun _ member _ _ solved _ present matching =>
      admits.check_matches_reached wellLocated member solved present matching⟩

/-- An occurrence at an unreached name survives the firing. -/
theorem ReachAdmits.unreached_survives (admits : ReachAdmits ns K space payload r C selection)
    {o : O} (present : o ∈ C.present) {n : N} (at_n : ResolvesTo sts C.equations (space o) n)
    (unreached : ¬ Reached ns K space payload C n) :
    o ∈ (selection.result (located sts space payload) (r.toRule sts) C).present := by
  apply mem_fire.mpr
  left
  refine ⟨present, fun takenMember => unreached ?_⟩
  have taken : o ∈ selection.taken := by simpa [Selection.commit] using takenMember
  obtain ⟨k, reached, at_k⟩ := admits.selected o (List.mem_append_left _ taken)
  have names : n = k := ResolvesTo.unique (valid_before_consistent admits.valid) at_n at_k
  exact names ▸ reached

/-- Nothing arrives at an unreached name. -/
theorem ReachAdmits.unreached_no_arrival (admits : ReachAdmits ns K space payload r C selection)
    {o : O} (after : o ∈ (selection.result (located sts space payload) (r.toRule sts) C).present)
    {n : N}
    (at_n : ResolvesTo sts (selection.problem (located sts space payload) (r.toRule sts) C)
      (space o) n)
    (unreached : ¬ Reached ns K space payload C n) : o ∈ C.present := by
  rcases mem_fire.mp after with ⟨present, _⟩ | madeMember
  · exact present
  · have made : o ∈ selection.made := by simpa [Selection.commit] using madeMember
    obtain ⟨k, reached, at_k⟩ := admits.made_reached made
    have names : n = k := ResolvesTo.unique admits.valid.consistent at_n at_k
    exact absurd (names ▸ reached) unreached

/-- An admitted firing takes and reads nothing at an unreached name. -/
theorem ReachAdmits.unreached_untouched (admits : ReachAdmits ns K space payload r C selection)
    {n : N} (unreached : ¬ Reached ns K space payload C n) :
    ∀ o ∈ selection.taken ++ selection.read, ¬ ResolvesTo sts C.equations (space o) n := by
  intro o member at_n
  obtain ⟨k, reached, at_k⟩ := admits.selected o member
  have names : n = k := ResolvesTo.unique (valid_before_consistent admits.valid) at_n at_k
  exact unreached (names ▸ reached)

/-- **No name, no effect.** At a name the actor does not reach, a reach step takes nothing, makes
nothing, and resolves none of the rule's space positions there (so it reads and checks nothing
there either). -/
theorem unreached_no_effect {D : Configuration T O} (step : ReachStep ns K space payload r C D)
    {n : N} (unreached : ¬ Reached ns K space payload C n) :
    (∀ o ∈ C.present, ResolvesTo sts C.equations (space o) n → o ∈ D.present) ∧
      (∀ o ∈ D.present, ResolvesTo sts D.equations (space o) n → o ∈ C.present) ∧
      ∀ s ∈ r.spaces, ¬ ResolvesTo sts D.equations s n := by
  obtain ⟨selection, admits, rfl⟩ := step
  refine ⟨fun o present at_n => admits.unreached_survives present at_n unreached,
    fun o present at_n => admits.unreached_no_arrival present at_n unreached, ?_⟩
  intro s member at_n
  obtain ⟨k, reached, at_k⟩ := admits.space_reached member
  have names : n = k := ResolvesTo.unique admits.valid.consistent at_n at_k
  exact unreached (names ▸ reached)

/-- No check of an admitted firing matches an occurrence at an unreached name. -/
theorem ReachAdmits.unreached_unobserved (admits : ReachAdmits ns K space payload r C selection)
    (wellLocated : WellLocated sts space C) {s p : T} (member : s ∈ r.spaces) {σ : S}
    (solved : A.Models σ (selection.problem (located sts space payload) (r.toRule sts) C))
    {o : O} (present : o ∈ C.present) {n : N} (at_n : ResolvesTo sts C.equations (space o) n)
    (unreached : ¬ Reached ns K space payload C n) :
    ¬ A.E (A.apply σ (sts.atSpace s p)) (A.apply σ (located sts space payload o)) := by
  intro matching
  obtain ⟨k, reached, at_k⟩ := admits.check_matches_reached wellLocated member solved present
    matching
  have names : n = k := ResolvesTo.unique (valid_before_consistent admits.valid) at_n at_k
  exact unreached (names ▸ reached)

/-! ### Reach depends only on what is in reach -/

omit [DecidableEq O] in
theorem AgreeOnReach.reached_iff {D : Configuration T O}
    (agree : AgreeOnReach ns K space payload C D) (n : N) :
    Reached ns K space payload C n ↔ Reached ns K space payload D n := by
  obtain ⟨E, P⟩ := C
  obtain ⟨E', P'⟩ := D
  obtain ⟨sameStore, same⟩ := agree
  simp only at sameStore
  subst sameStore
  have toC : ∀ m, Reach ns E space (located sts space payload) P' K m →
      Reach ns E space (located sts space payload) P K m := by
    intro m reached
    apply reached (Reach ns E space (located sts space payload) P K)
    intro j possessed
    apply Reach.closed
    refine possessed.mono (Set.union_subset_union_right K ?_)
    rintro t ⟨o, present', k, inR, at_k, rfl⟩
    exact ⟨o, (same o ⟨k, inR, at_k⟩).mpr present', k, inR, at_k, rfl⟩
  refine ⟨fun reached => ?_, toC n⟩
  apply reached (Reach ns E space (located sts space payload) P' K)
  intro j possessed
  apply Reach.closed
  refine possessed.mono (Set.union_subset_union_right K ?_)
  rintro t ⟨o, present, k, inR, at_k, rfl⟩
  exact ⟨o, (same o ⟨k, toC k inR, at_k⟩).mp present, k, inR, at_k, rfl⟩

omit [DecidableEq O] in
theorem AgreeOnReach.symm {D : Configuration T O} (agree : AgreeOnReach ns K space payload C D) :
    AgreeOnReach ns K space payload D C := by
  refine ⟨agree.1.symm, fun o ⟨k, reached, at_k⟩ => ?_⟩
  have reachedC : Reached ns K space payload C k := (agree.reached_iff k).mpr reached
  exact (agree.2 o ⟨k, reachedC, agree.1 ▸ at_k⟩).symm

/-- **The core of locality.** A valid selection whose taken and read occurrences lie at reached
names, and whose absence and count spaces its problem resolves to reached names, stays valid in a
well-located configuration that agrees on the reach. -/
theorem valid_of_agree_on_reach {D : Configuration T O}
    (valid : selection.Valid A (located sts space payload) (r.toRule sts) C)
    (selected : ∀ o ∈ selection.taken ++ selection.read, AtReached ns K space payload C o)
    (checked : ∀ s ∈ r.checks.filterMap LocatedCheck.space?, ∃ k,
      Reached ns K space payload C k ∧
        ResolvesTo sts (selection.problem (located sts space payload) (r.toRule sts) C) s k)
    (agree : AgreeOnReach ns K space payload C D) (wellC : WellLocated sts space C)
    (wellD : WellLocated sts space D) (fresh : Disjoint selection.made.toFinset D.present) :
    selection.Valid A (located sts space payload) (r.toRule sts) D := by
  obtain ⟨E, P⟩ := C
  obtain ⟨E', P'⟩ := D
  obtain ⟨sameStore, same⟩ := agree
  simp only at sameStore
  subst sameStore
  have inD : ∀ o ∈ selection.taken ++ selection.read, o ∈ P' := by
    intro o member
    have presentC : o ∈ P := by
      rcases List.mem_append.mp member with taken | read
      · exact valid.occurrences.taken_subset (by simpa [Selection.commit] using taken)
      · exact valid.occurrences.kept_subset (by simpa [Selection.commit] using read)
    exact (same o (selected o member)).mp presentC
  -- an occurrence matched by a check lies at a reached name, in either configuration
  have matchedAt : ∀ {s p : T}, s ∈ r.checks.filterMap LocatedCheck.space? → ∀ {σ : S},
      A.Models σ (selection.problem (located sts space payload) (r.toRule sts) ⟨E, P⟩) →
        ∀ {o : O} {m : N}, ResolvesTo sts E (space o) m →
          A.E (A.apply σ (sts.atSpace s p)) (A.apply σ (located sts space payload o)) →
            AtReached ns K space payload ⟨E, P⟩ o := by
    intro s p member σ solved o m at_m matching
    obtain ⟨k, reached, at_k⟩ := checked s member
    simp only [located, sts.apply_atSpace, sts.E_atSpace] at matching
    have lifted : ResolvesTo sts (selection.problem (located sts space payload) (r.toRule sts)
        ⟨E, P⟩) (space o) m := ResolvesTo.of_refines valid.refines at_m
    have names : k = m := at_k.name_eq solved lifted matching.1
    subst names
    exact ⟨k, reached, at_m⟩
  refine ⟨valid.take_distinct, valid.output_distinct, valid.take_length,
    valid.read_length, valid.outputs, ⟨?_, ?_, valid.occurrences.apart, fresh,
      by simp [Selection.commit]⟩, valid.consistent, ?_⟩
  · intro o member
    exact inD o (List.mem_append_left _ (by simpa [Selection.commit] using member))
  · intro o member
    exact inD o (List.mem_append_right _ (by simpa [Selection.commit] using member))
  · intro check member σ solved
    have holdsC := valid.checks check member σ solved
    simp only [LocatedRule.toRule, List.mem_map] at member
    obtain ⟨locatedCheck, checkMember, rfl⟩ := member
    have spaceMember : ∀ {s : T}, locatedCheck.space? = some s →
        s ∈ r.checks.filterMap LocatedCheck.space? :=
      fun same => List.mem_filterMap.mpr ⟨locatedCheck, checkMember, same⟩
    cases locatedCheck with
    | equal l r => exact holdsC
    | absent s p =>
        intro o presentD matching
        obtain ⟨m, at_m⟩ := wellD o presentD
        exact holdsC o ((same o (matchedAt (spaceMember rfl) solved at_m matching)).mpr presentD)
          matching
    | count s p k =>
        change (Check.matches A σ (located sts space payload) P' (sts.atSpace s p)).card = k
        have sameMatches : Check.matches A σ (located sts space payload) P' (sts.atSpace s p) =
            Check.matches A σ (located sts space payload) P (sts.atSpace s p) := by
          classical
          ext o
          simp only [Check.matches, Finset.mem_filter]
          constructor
          · rintro ⟨presentD, matching⟩
            obtain ⟨m, at_m⟩ := wellD o presentD
            exact ⟨(same o (matchedAt (spaceMember rfl) solved at_m matching)).mpr presentD,
              matching⟩
          · rintro ⟨presentC, matching⟩
            obtain ⟨m, at_m⟩ := wellC o presentC
            exact ⟨(same o (matchedAt (spaceMember rfl) solved at_m matching)).mp presentC,
              matching⟩
        rw [sameMatches]
        exact holdsC

/-- One direction of locality. -/
theorem ReachAdmits.of_agree {D : Configuration T O}
    (admits : ReachAdmits ns K space payload r C selection)
    (agree : AgreeOnReach ns K space payload C D) (wellC : WellLocated sts space C)
    (wellD : WellLocated sts space D) (fresh : Disjoint selection.made.toFinset D.present) :
    ReachAdmits ns K space payload r D selection := by
  refine ⟨admits.holds, valid_of_agree_on_reach admits.valid admits.selected
    (fun s member => admits.space_reached (List.mem_append_right _ member)) agree wellC wellD fresh,
    fun o member => ?_, ?_⟩
  · obtain ⟨k, reached, at_k⟩ := admits.selected o member
    refine ⟨k, (agree.reached_iff k).mp reached, ?_⟩
    rw [← agree.1]
    exact at_k
  · have problems : selection.problem (located sts space payload) (r.toRule sts) D =
        selection.problem (located sts space payload) (r.toRule sts) C := by
      simp only [Selection.problem, agree.1]
    rw [problems]
    exact admits.resolved

/-- **Locality**: validity of an admitted firing depends only on the store and on the occurrences
at reached names. -/
theorem reachAdmits_iff_of_agree {D : Configuration T O}
    (agree : AgreeOnReach ns K space payload C D) (wellC : WellLocated sts space C)
    (wellD : WellLocated sts space D) (freshC : Disjoint selection.made.toFinset C.present)
    (freshD : Disjoint selection.made.toFinset D.present) :
    ReachAdmits ns K space payload r C selection ↔ ReachAdmits ns K space payload r D selection :=
  ⟨fun admits => admits.of_agree agree wellC wellD freshD,
    fun admits => admits.of_agree agree.symm wellD wellC freshC⟩

/-- **No name, no observation.** Two configurations with one consistent store that differ only
in occurrences at a name the actor does not reach admit the same selections. -/
theorem unreached_no_observation {D : Configuration T O} {n : N}
    (consistent : A.Consistent C.equations) (sameStore : C.equations = D.equations)
    (elsewhere : ∀ o, ¬ ResolvesTo sts C.equations (space o) n → (o ∈ C.present ↔ o ∈ D.present))
    (unreached : ¬ Reached ns K space payload C n) (wellC : WellLocated sts space C)
    (wellD : WellLocated sts space D) (freshC : Disjoint selection.made.toFinset C.present)
    (freshD : Disjoint selection.made.toFinset D.present) :
    ReachAdmits ns K space payload r C selection ↔ ReachAdmits ns K space payload r D selection := by
  refine reachAdmits_iff_of_agree ⟨sameStore, ?_⟩ wellC wellD freshC freshD
  rintro o ⟨k, reached, at_k⟩
  apply elsewhere o
  intro at_n
  have names : n = k := ResolvesTo.unique consistent at_n at_k
  exact unreached (names ▸ reached)

/-! ### Reach grows only by reading or by creation -/

/-- **The reach step keeps configurations well located.** -/
theorem ReachStep.wellLocated {D : Configuration T O} (step : ReachStep ns K space payload r C D)
    (wellLocated : WellLocated sts space C) : WellLocated sts space D := by
  obtain ⟨selection, admits, rfl⟩ := step
  intro o present
  rcases mem_fire.mp present with ⟨old, _⟩ | madeMember
  · obtain ⟨n, at_n⟩ := wellLocated o old
    exact ⟨n, ResolvesTo.of_refines admits.valid.refines at_n⟩
  · have made : o ∈ selection.made := by simpa [Selection.commit] using madeMember
    obtain ⟨k, _, at_k⟩ := admits.made_reached made
    exact ⟨k, at_k⟩

/-- **Reach grows only by reading or by creation.** After a reach step of a rule the actor holds,
it reaches only names it reached before; new names enter only as new terms of `K`. -/
theorem reach_after_reach_step {D : Configuration T O} (step : ReachStep ns K space payload r C D)
    (wellLocated : WellLocated sts space C) {n : N} (reached : Reached ns K space payload D n) :
    Reached ns K space payload C n := by
  obtain ⟨selection, admits, rfl⟩ := step
  apply reached (Reached ns K space payload C)
  intro m possessedAfter
  have labelsAfter : labelsAt sts
      (selection.result (located sts space payload) (r.toRule sts) C).equations space
      (located sts space payload)
      (selection.result (located sts space payload) (r.toRule sts) C).present
      (Reached ns K space payload C) ⊆
      K ∪ labelsAt sts C.equations space (located sts space payload) C.present
        (Reached ns K space payload C) := by
    rintro t ⟨o, presentAfter, k, inR, at_k, rfl⟩
    rcases mem_fire.mp presentAfter with ⟨old, _⟩ | madeMember
    · obtain ⟨k', at_k'⟩ := wellLocated o old
      have names : k = k' :=
        ResolvesTo.unique admits.valid.consistent at_k (ResolvesTo.of_refines admits.valid.refines at_k')
      subst names
      exact Or.inr ⟨o, old, k, inR, at_k', rfl⟩
    · have made : o ∈ selection.made := by simpa [Selection.commit] using madeMember
      left
      apply admits.holds.produce
      rw [← admits.valid.outputs]
      exact List.mem_map.mpr ⟨o, made, rfl⟩
  have widened := possessedAfter.mono (Set.union_subset Set.subset_union_left labelsAfter)
  have possessedBefore := possession_after_step admits.valid
    (fun p member => Or.inl (admits.holds.ports p member))
    (fun e member => ⟨Or.inl (admits.holds.tells e member).1, Or.inl (admits.holds.tells e member).2⟩)
    (fun o member => Or.inr (admits.selected_labels o member)) widened
  exact Reach.closed possessedBefore

/-- More terms reach more and admit more. -/
theorem ReachAdmits.mono {K' : Set T} (more : K ⊆ K')
    (admits : ReachAdmits ns K space payload r C selection) :
    ReachAdmits ns K' space payload r C selection :=
  ⟨admits.holds.mono more, admits.valid,
    fun o member => by
      obtain ⟨k, reached, at_k⟩ := admits.selected o member
      exact ⟨k, reached.mono more, at_k⟩,
    admits.resolved⟩

theorem ReachStep.mono {K' : Set T} (more : K ⊆ K') {D : Configuration T O}
    (step : ReachStep ns K space payload r C D) : ReachStep ns K' space payload r C D := by
  obtain ⟨selection, admits, after⟩ := step
  exact ⟨selection, admits.mono more, after⟩

/-- **Only connectivity begets connectivity**: what another party with terms `K'` reaches after
the actor's step, it reached together with the actor before. -/
theorem other_reach_after_reach_step {D : Configuration T O}
    (step : ReachStep ns K space payload r C D) (wellLocated : WellLocated sts space C)
    {K' : Set T} {n : N} (reached : Reached ns K' space payload D n) :
    Reached ns (K' ∪ K) space payload C n :=
  reach_after_reach_step (step.mono Set.subset_union_right) wellLocated
    (reached.mono Set.subset_union_left)

variable (ns) in
/-- A run of reach steps of one actor. -/
inductive ReachRun (K : Set T) (space payload : O → T) :
    Configuration T O → List (LocatedRule T) → Configuration T O → Prop
  | nil (C : Configuration T O) : ReachRun K space payload C [] C
  | cons {C D E : Configuration T O} {r : LocatedRule T} {rest : List (LocatedRule T)} :
      ReachStep ns K space payload r C D → ReachRun K space payload D rest E →
        ReachRun K space payload C (r :: rest) E

/-- **Reach over a run**: along the actor's own reach steps, from a well-located configuration,
what it reaches at the end it reached at the start. -/
theorem reach_after_reach_run {E : Configuration T O} {rules : List (LocatedRule T)}
    (run : ReachRun ns K space payload C rules E) (wellLocated : WellLocated sts space C) {n : N}
    (reached : Reached ns K space payload E n) : Reached ns K space payload C n := by
  induction run with
  | nil => exact reached
  | cons step _ ih =>
      exact reach_after_reach_step step wellLocated (ih (step.wellLocated wellLocated) reached)

/-! ### The old law, and the owner -/

/-- **The old law's firings are admitted**: a located step (resolved before selection) of a rule
the actor holds, from a well-located configuration, is a reach step. -/
theorem located_step_is_reach_step {D : Configuration T O}
    (step : LocatedStep sts space payload r C D) (wellLocated : WellLocated sts space C)
    (holds : HoldsRule (sts := sts) r K) : ReachStep ns K space payload r C D := by
  obtain ⟨resolved, selection, valid, rfl⟩ := step
  refine ⟨selection, ⟨holds, valid, fun o member => ?_, fun s member => ?_⟩, rfl⟩
  · exact (effects_in_reach (ns := ns) valid resolved wellLocated holds).1 o
      (List.mem_append_left _ member)
  · obtain ⟨k, at_k⟩ := resolved s member
    exact ⟨k, ResolvesTo.of_refines valid.refines at_k⟩

omit [DecidableEq N] in
/-- **Take and read ports resolve by selection.** In a valid selection from a well-located
configuration, the problem resolves the space of every take and read port to the name of the
occurrence it selected. -/
theorem selected_ports_resolve
    (valid : selection.Valid A (located sts space payload) (r.toRule sts) C)
    (wellLocated : WellLocated sts space C) {port : T × T} (member : port ∈ r.take ++ r.read) :
    Resolves sts (selection.problem (located sts space payload) (r.toRule sts) C) port.1 := by
  have resolveAt : ∀ {o : O}, o ∈ C.present →
      (place sts port, located sts space payload o) ∈
        selection.problem (located sts space payload) (r.toRule sts) C →
      Resolves sts (selection.problem (located sts space payload) (r.toRule sts) C) port.1 := by
    intro o present pair
    obtain ⟨m, at_m⟩ := wellLocated o present
    refine ⟨m, fun σ solved => ?_⟩
    have same := solved _ pair
    simp only [SubstitutionAction.Solves, place, located, sts.apply_atSpace, sts.E_atSpace] at same
    exact A.equivalence.trans same.1 (ResolvesTo.of_refines valid.refines at_m σ solved)
  rcases List.mem_append.mp member with takeMember | readMember
  · have placed : place sts port ∈ (r.toRule sts).take := List.mem_map.mpr ⟨port, takeMember, rfl⟩
    obtain ⟨o, taken, pair⟩ := mem_equations_of_mem (located sts space payload) valid.take_length
      placed
    refine resolveAt (valid.occurrences.taken_subset (by simpa [Selection.commit] using taken)) ?_
    simp only [Selection.problem, List.mem_append]
    exact Or.inl (Or.inl (Or.inr pair))
  · have placed : place sts port ∈ (r.toRule sts).read := List.mem_map.mpr ⟨port, readMember, rfl⟩
    obtain ⟨o, read, pair⟩ := mem_equations_of_mem (located sts space payload) valid.read_length
      placed
    refine resolveAt (valid.occurrences.kept_subset (by simpa [Selection.commit] using read)) ?_
    simp only [Selection.problem, List.mem_append]
    exact Or.inl (Or.inr pair)

/-- **Zero friction for the owner.** An actor that possesses every name is admitted exactly the
candidate step's selections of rules it holds whose space positions all name a space after
selection. -/
theorem owner_admits_iff (everything : ∀ n, Possesses ns C.equations K n)
    (wellLocated : WellLocated sts space C) :
    ReachAdmits ns K space payload r C selection ↔
      HoldsRule (sts := sts) r K ∧ selection.Valid A (located sts space payload) (r.toRule sts) C ∧
        ∀ s ∈ r.spaces,
          Resolves sts (selection.problem (located sts space payload) (r.toRule sts) C) s := by
  constructor
  · intro admits
    exact ⟨admits.holds, admits.valid, admits.resolved⟩
  · rintro ⟨holds, valid, resolved⟩
    refine ⟨holds, valid, fun o member => ?_, resolved⟩
    have present : o ∈ C.present := by
      rcases List.mem_append.mp member with taken | read
      · exact valid.occurrences.taken_subset (by simpa [Selection.commit] using taken)
      · exact valid.occurrences.kept_subset (by simpa [Selection.commit] using read)
    obtain ⟨k, at_k⟩ := wellLocated o present
    exact ⟨k, Reach.of_possesses (everything k), at_k⟩

/-- The owner needs nothing for its take and read ports: only its produce and check spaces must
name a space after selection. -/
theorem owner_admits_iff_outputs (everything : ∀ n, Possesses ns C.equations K n)
    (wellLocated : WellLocated sts space C) :
    ReachAdmits ns K space payload r C selection ↔
      HoldsRule (sts := sts) r K ∧ selection.Valid A (located sts space payload) (r.toRule sts) C ∧
        ∀ s ∈ r.produce.map Prod.fst ++ r.checks.filterMap LocatedCheck.space?,
          Resolves sts (selection.problem (located sts space payload) (r.toRule sts) C) s := by
  rw [owner_admits_iff everything wellLocated]
  constructor
  · rintro ⟨holds, valid, resolved⟩
    refine ⟨holds, valid, fun s member => resolved s ?_⟩
    rcases List.mem_append.mp member with produced | checked
    · obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp produced
      exact produce_space_mem portMember
    · obtain ⟨check, checkMember, space⟩ := List.mem_filterMap.mp checked
      exact check_space_mem checkMember space
  · rintro ⟨holds, valid, resolved⟩
    refine ⟨holds, valid, fun s member => ?_⟩
    simp only [LocatedRule.spaces, List.mem_append] at member
    rcases member with ((taken | read) | produced) | checked
    · obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp taken
      exact selected_ports_resolve valid wellLocated (List.mem_append_left _ portMember)
    · obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp read
      exact selected_ports_resolve valid wellLocated (List.mem_append_right _ portMember)
    · exact resolved s (List.mem_append_left _ produced)
    · exact resolved s (List.mem_append_right _ checked)

omit [DecidableEq O] in
/-- An actor that writes every name possesses every name. -/
theorem writes_every_name {store : EquationStore T} (consistent : A.Consistent store)
    (writes : ∀ n, sts.name n ∈ K) (n : N) : Possesses ns store K n :=
  written_name_possessed consistent (writes n)

end ReachSelection

/-! ## Names written in a first-order term -/

namespace Controls

/-- The names written in a term. -/
def Tm.namesIn : Tm → List Nat
  | .var _ => []
  | .nm n => [n]
  | .sym _ => []
  | .app f x => f.namesIn ++ x.namesIn
  | .loc s p => s.namesIn ++ p.namesIn

/-- Exchanging two names a term does not write leaves it unchanged. -/
theorem Tm.swap_eq_self {a b : Nat} : ∀ {t : Tm}, a ∉ t.namesIn → b ∉ t.namesIn → t.swap a b = t
  | .var _, _, _ => rfl
  | .nm n, ha, hb => by
      simp only [Tm.namesIn, List.mem_singleton] at ha hb
      show Tm.nm (Equiv.swap a b n) = Tm.nm n
      rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm ha) (Ne.symm hb)]
  | .sym _, _, _ => rfl
  | .app f x, ha, hb => by
      simp only [Tm.namesIn, List.mem_append, not_or] at ha hb
      show Tm.app (f.swap a b) (x.swap a b) = Tm.app f x
      rw [Tm.swap_eq_self ha.1 hb.1, Tm.swap_eq_self ha.2 hb.2]
  | .loc s p, ha, hb => by
      simp only [Tm.namesIn, List.mem_append, not_or] at ha hb
      show Tm.loc (s.swap a b) (p.swap a b) = Tm.loc s p
      rw [Tm.swap_eq_self ha.1 hb.1, Tm.swap_eq_self ha.2 hb.2]

/-- **Reach is bounded by the names written.** If the terms, the labels at names below `B` and
the store write only names below `B`, the terms reach only names below `B`. -/
theorem reach_below (B : Nat) (positive : 0 < B) {store : EquationStore Tm}
    {space label : Nat → Tm} {present : Finset Nat} {K : Set Tm}
    (termsK : ∀ t ∈ K, ∀ j ∈ t.namesIn, j < B)
    (labels : ∀ o ∈ present, ∀ k, k < B → ResolvesTo spaces store (space o) k →
      ∀ j ∈ (label o).namesIn, j < B)
    (storeNames : ∀ e ∈ store, (∀ j ∈ e.1.namesIn, j < B) ∧ ∀ j ∈ e.2.namesIn, j < B)
    {n : Nat} (reached : Reach names store space label present K n) : n < B := by
  apply reached (· < B)
  intro m possessed
  by_contra notBelow
  have avoid : ∀ t : Tm, (∀ j ∈ t.namesIn, j < B) → t.swap m (m + B) = t := by
    intro t below
    apply Tm.swap_eq_self
    · intro member
      exact notBelow (below m member)
    · intro member
      have := below (m + B) member
      omega
  apply possessed
  refine ⟨m + B, by omega, indistinguishable_of_invariant ?_ ?_⟩
  · rintro t (member | ⟨o, present', k, below, at_k, rfl⟩)
    · exact avoid t (termsK t member)
    · exact avoid _ (labels o present' k below at_k)
  · intro e member
    exact ⟨avoid _ (storeNames e member).1, avoid _ (storeNames e member).2⟩

/-- In the empty store a written name resolves to itself and to nothing else. -/
theorem resolvesTo_nm_nil {j k : Nat} :
    ResolvesTo spaces ([] : EquationStore Tm) (.nm j) k ↔ j = k := by
  constructor
  · intro at_k
    have := at_k Tm.var (by simp)
    simpa [spaces, Tm.subst] using this
  · rintro rfl
    exact resolvesTo_name (sts := spaces) [] j

end Controls

/-! ## Controls for reach-relative selection -/

namespace ReachControls

open Controls

/-! ### Atomic indirection, and reach by reading -/

/-- `(index task s)`. -/
def indexOf (s : Tm) : Tm := .app (.app (.sym "index") (.sym "task")) s

/-- `(edge x y)`. -/
def edgeXY : Tm := .app (.app (.sym "edge") (.sym "x")) (.sym "y")

/-- Occurrence 0: the index row `(index task 7)` at space 1; occurrence 1: `(edge x y)` at 7. -/
def idxSpace : Nat → Tm
  | 0 => .nm 1
  | _ => .nm 7

def idxPayload : Nat → Tm
  | 0 => indexOf (.nm 7)
  | _ => edgeXY

def idxWorld : Configuration Tm Nat := ⟨[], {0, 1}⟩

/-- The same world without the handle: only the edge at 7. -/
def edgeWorld : Configuration Tm Nat := ⟨[], {1}⟩

/-- Read the index at space 1 and, in the same firing, the edge at the space it names. -/
def follow : LocatedRule Tm := ⟨[], [(.nm 1, indexOf (.var 0)), (.var 0, edgeXY)], [], [], []⟩

/-- The actor holds the terms of its rule; the only name it writes is 1. -/
def follower : Set Tm :=
  {.nm 1, .var 0, .loc (.nm 1) (indexOf (.var 0)), .loc (.var 0) edgeXY}

def followSel : Selection Nat := ⟨[], [0, 1], []⟩

theorem follower_holds : HoldsRule (sts := spaces) follow follower := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [follow, LocatedRule.toRule, LocatedRule.spaces, place, follower, spaces]

theorem follower_names : ∀ t ∈ follower, ∀ j ∈ t.namesIn, j < 7 := by
  intro t member j named
  simp only [follower, Set.mem_insert_iff, Set.mem_singleton_iff] at member
  rcases member with rfl | rfl | rfl | rfl <;>
    simp [Tm.namesIn, indexOf, edgeXY] at named <;> omega

theorem one_reached (C : Configuration Tm Nat) (consistent : action.Consistent C.equations) :
    Reached names follower idxSpace idxPayload C 1 :=
  Reach.of_possesses (written_name_possessed consistent (by simp [follower, spaces]))

/-- **Reach by reading**: the handle's label at the reached space 1 names 7, so 7 is reached. -/
theorem seven_reached : Reached names follower idxSpace idxPayload idxWorld 7 := by
  apply Reach.closed
  refine ground_term_possessed (t := Tm.loc (.nm 1) (indexOf (.nm 7))) ⟨Tm.var, by simp [idxWorld]⟩
    (Or.inr ⟨0, by simp [idxWorld], 1, one_reached idxWorld ⟨Tm.var, by simp [idxWorld]⟩,
      resolvesTo_name _ 1, rfl⟩) (fun σ => rfl) ?_
  intro m different same
  have named := congrArg Tm.namesIn same
  simp [names, Tm.swap, Tm.namesIn, indexOf] at named
  omega

theorem follow_valid :
    followSel.Valid action (located spaces idxSpace idxPayload) (follow.toRule spaces) idxWorld := by
  refine ⟨by simp [followSel], by simp [followSel], rfl, rfl, rfl,
    ⟨by simp [Selection.commit, followSel], by simp [Selection.commit, followSel, idxWorld],
      by simp [Selection.commit, followSel], by simp [Selection.commit, followSel],
      by simp [Selection.commit]⟩,
    ⟨fun _ => .nm 7, ?_⟩, by simp [follow, LocatedRule.toRule]⟩
  simp [SubstitutionAction.Solves, Selection.problem, Selection.equations, follow,
    LocatedRule.toRule, followSel, idxWorld, place, located, spaces, idxSpace, idxPayload,
    indexOf, edgeXY, Tm.subst]

theorem follow_resolves_seven :
    ResolvesTo spaces (followSel.problem (located spaces idxSpace idxPayload)
      (follow.toRule spaces) idxWorld) (.var 0) 7 := by
  intro σ solved
  simp [SubstitutionAction.Solves, Selection.problem, Selection.equations, follow,
    LocatedRule.toRule, followSel, idxWorld, place, located, spaces, idxSpace, idxPayload,
    indexOf, edgeXY, Tm.subst] at solved
  simpa [spaces, Tm.subst] using solved

theorem follow_admits :
    ReachAdmits names follower idxSpace idxPayload follow idxWorld followSel := by
  refine ⟨follower_holds, follow_valid, ?_, ?_⟩
  · intro o member
    simp only [followSel, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact ⟨1, one_reached idxWorld ⟨Tm.var, by simp [idxWorld]⟩, resolvesTo_name _ 1⟩
    · exact ⟨7, seven_reached, resolvesTo_name _ 7⟩
  · intro s member
    simp only [LocatedRule.spaces, follow, List.map_cons, List.map_nil, List.filterMap_nil,
      List.nil_append, List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact ⟨1, resolvesTo_name _ 1⟩
    · exact ⟨7, follow_resolves_seven⟩

/-- **Atomic indirection is admitted**: reading the handle at 1 and the edge at the space it
names, in one firing. -/
theorem indirection_admitted :
    ReachStep names follower idxSpace idxPayload follow idxWorld
      (followSel.result (located spaces idxSpace idxPayload) (follow.toRule spaces) idxWorld) :=
  ⟨followSel, follow_admits, rfl⟩

/-- The old law refuses the indirection: the store before the step does not resolve the handle's
variable. -/
theorem follow_not_resolved : ¬ Resolved spaces idxWorld.equations follow := by
  intro resolved
  obtain ⟨n, at_n⟩ := resolved (.var 0) (by simp [LocatedRule.spaces, follow])
  have := at_n (fun _ => .nm (n + 1)) (by simp [idxWorld])
  simp [spaces, Tm.subst] at this

/-- **Atomic indirection separates the two laws**: admitted here, refused by the old law. -/
theorem indirection_separates :
    ReachStep names follower idxSpace idxPayload follow idxWorld
        (followSel.result (located spaces idxSpace idxPayload) (follow.toRule spaces) idxWorld) ∧
      ∀ D, ¬ LocatedStep spaces idxSpace idxPayload follow idxWorld D :=
  ⟨indirection_admitted, fun _ step => follow_not_resolved step.1⟩

/-- **A handle read in the same firing extends what the firing may touch**: with the index row,
7 is reached through the closure and the firing reads the edge at 7. -/
theorem handle_gives_reach :
    Reached names follower idxSpace idxPayload idxWorld 7 ∧
      ∃ selection, ReachAdmits names follower idxSpace idxPayload follow idxWorld selection ∧
        1 ∈ selection.read :=
  ⟨seven_reached, followSel, follow_admits, by simp [followSel]⟩

theorem seven_unreached_without_handle : ¬ Reached names follower idxSpace idxPayload edgeWorld 7 := by
  intro reached
  have below := reach_below 7 (by norm_num) follower_names ?_ (by simp [edgeWorld]) reached
  · omega
  · intro o present k below at_k
    simp only [edgeWorld, Finset.mem_singleton] at present
    subst present
    have := (resolvesTo_nm_nil (j := 7) (k := k)).mp at_k
    omega

/-- **Without the handle, nothing at 7 is touched**: 7 is not reached, and every reach step of
the actor, of any rule it holds, leaves the edge at 7 in place. -/
theorem no_handle_no_reach :
    ¬ Reached names follower idxSpace idxPayload edgeWorld 7 ∧
      ∀ (r : LocatedRule Tm) (D : Configuration Tm Nat),
        ReachStep names follower idxSpace idxPayload r edgeWorld D → 1 ∈ D.present :=
  ⟨seven_unreached_without_handle, fun _ _ step =>
    (unreached_no_effect step seven_unreached_without_handle).1 1 (by simp [edgeWorld])
      (resolvesTo_name _ 7)⟩

/-! ### Search across held spaces -/

/-- `(not t)`. -/
def notP (t : Tm) : Tm := .app (.sym "not") t

/-- Occurrences: 0 `a` at 1; 1 `b` and 2 `(not b)` at 2; 3 `(not a)` at 3; 4 `c` and 5 `(not c)`
at 4, a space the searcher does not hold; 6 the report the firing makes at 0. -/
def findSpace : Nat → Tm
  | 0 => .nm 1
  | 1 => .nm 2
  | 2 => .nm 2
  | 3 => .nm 3
  | 6 => .nm 0
  | _ => .nm 4

def findPayload : Nat → Tm
  | 0 => .sym "a"
  | 1 => .sym "b"
  | 2 => notP (.sym "b")
  | 3 => notP (.sym "a")
  | 4 => .sym "c"
  | 5 => notP (.sym "c")
  | _ => .app (.sym "contradiction") (.var 0)

def findWorld : Configuration Tm Nat := ⟨[], {0, 1, 2, 3, 4, 5}⟩

/-- Find a space holding a claim and its negation, and report it at 0. -/
def findContradiction : LocatedRule Tm :=
  ⟨[], [(.var 0, .var 1), (.var 0, notP (.var 1))], [], [],
    [(.nm 0, .app (.sym "contradiction") (.var 0))]⟩

/-- The searcher holds spaces 0 to 3 and the terms of its rule. -/
def searcher : Set Tm :=
  {.nm 0, .nm 1, .nm 2, .nm 3, .var 0, .loc (.var 0) (.var 1), .loc (.var 0) (notP (.var 1)),
    .loc (.nm 0) (.app (.sym "contradiction") (.var 0))}

theorem searcher_holds : HoldsRule (sts := spaces) findContradiction searcher := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [findContradiction, LocatedRule.toRule, LocatedRule.spaces, place, searcher, spaces]

theorem searcher_names : ∀ t ∈ searcher, ∀ j ∈ t.namesIn, j < 4 := by
  intro t member j named
  simp only [searcher, Set.mem_insert_iff, Set.mem_singleton_iff] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Tm.namesIn, notP] at named <;> omega

theorem find_labels_below : ∀ o ∈ findWorld.present, ∀ k, k < 4 →
    ResolvesTo spaces findWorld.equations (findSpace o) k →
      ∀ j ∈ (located spaces findSpace findPayload o).namesIn, j < 4 := by
  intro o present k below at_k j named
  simp only [findWorld, Finset.mem_insert, Finset.mem_singleton] at present
  rcases present with rfl | rfl | rfl | rfl | rfl | rfl <;>
    have := (resolvesTo_nm_nil).mp at_k <;>
    simp [located, spaces, findSpace, findPayload, notP, Tm.namesIn] at named <;> omega

theorem searcher_reach_below {k : Nat}
    (reached : Reached names searcher findSpace findPayload findWorld k) : k < 4 :=
  reach_below 4 (by norm_num) searcher_names find_labels_below (by simp [findWorld]) reached

theorem held_reached (k : Nat) (held : k < 4) :
    Reached names searcher findSpace findPayload findWorld k := by
  apply Reach.of_possesses
  apply written_name_possessed ⟨Tm.var, by simp [findWorld]⟩
  show Tm.nm k ∈ searcher
  simp only [searcher, Set.mem_insert_iff, Set.mem_singleton_iff, Tm.nm.injEq, reduceCtorEq,
    or_false]
  omega

def findAtTwo : Selection Nat := ⟨[], [1, 2], [6]⟩

def findAtFour : Selection Nat := ⟨[], [4, 5], [6]⟩

/-- The search's selection at 2 is valid for the candidate step. -/
theorem findAtTwo_valid :
    findAtTwo.Valid action (located spaces findSpace findPayload) (findContradiction.toRule spaces)
      findWorld := by
  refine ⟨by simp [findAtTwo], by simp [findAtTwo], rfl, rfl, rfl,
    ⟨by simp [Selection.commit, findAtTwo], by simp [Selection.commit, findAtTwo, findWorld, Finset.insert_subset_iff],
      by simp [Selection.commit, findAtTwo], by simp [Selection.commit, findAtTwo, findWorld],
      by simp [Selection.commit]⟩,
    ⟨fun i => if i = 0 then .nm 2 else .sym "b", ?_⟩, by simp [findContradiction, LocatedRule.toRule]⟩
  simp [SubstitutionAction.Solves, Selection.problem, Selection.equations, findContradiction,
    LocatedRule.toRule, findAtTwo, findWorld, place, located, spaces, findSpace, findPayload, notP,
    Tm.subst]

/-- The candidate step would also take the contradiction at the unheld space 4. -/
theorem findAtFour_valid :
    findAtFour.Valid action (located spaces findSpace findPayload) (findContradiction.toRule spaces)
      findWorld := by
  refine ⟨by simp [findAtFour], by simp [findAtFour], rfl, rfl, rfl,
    ⟨by simp [Selection.commit, findAtFour], by simp [Selection.commit, findAtFour, findWorld, Finset.insert_subset_iff],
      by simp [Selection.commit, findAtFour], by simp [Selection.commit, findAtFour, findWorld],
      by simp [Selection.commit]⟩,
    ⟨fun i => if i = 0 then .nm 4 else .sym "c", ?_⟩, by simp [findContradiction, LocatedRule.toRule]⟩
  simp [SubstitutionAction.Solves, Selection.problem, Selection.equations, findContradiction,
    LocatedRule.toRule, findAtFour, findWorld, place, located, spaces, findSpace, findPayload, notP,
    Tm.subst]

/-- **Search finds the contradiction in the held space that has one.** -/
theorem search_finds_held_contradiction :
    ReachStep names searcher findSpace findPayload findContradiction findWorld
      (findAtTwo.result (located spaces findSpace findPayload) (findContradiction.toRule spaces)
        findWorld) := by
  refine ⟨findAtTwo, ⟨searcher_holds, findAtTwo_valid, ?_, ?_⟩, rfl⟩
  · intro o member
    simp only [findAtTwo, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact ⟨2, held_reached 2 (by norm_num), resolvesTo_name _ 2⟩
    · exact ⟨2, held_reached 2 (by norm_num), resolvesTo_name _ 2⟩
  · intro s member
    simp only [LocatedRule.spaces, findContradiction, List.map_cons, List.map_nil,
      List.filterMap_nil, List.nil_append, List.append_nil, List.cons_append, List.mem_cons,
      List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · refine ⟨2, fun σ solved => ?_⟩
      simp [SubstitutionAction.Solves, Selection.problem, Selection.equations, findContradiction,
        LocatedRule.toRule, findAtTwo, findWorld, place, located, spaces, findSpace, findPayload,
        notP, Tm.subst] at solved
      simpa [spaces, Tm.subst] using solved.1
    · refine ⟨2, fun σ solved => ?_⟩
      simp [SubstitutionAction.Solves, Selection.problem, Selection.equations, findContradiction,
        LocatedRule.toRule, findAtTwo, findWorld, place, located, spaces, findSpace, findPayload,
        notP, Tm.subst] at solved
      simpa [spaces, Tm.subst] using solved.1
    · exact ⟨0, resolvesTo_name _ 0⟩

/-- **An unheld space is ignored**: the candidate step would take the contradiction at 4, the
searcher's reach does not admit it. -/
theorem search_ignores_unheld :
    findAtFour.Valid action (located spaces findSpace findPayload) (findContradiction.toRule spaces)
        findWorld ∧
      ¬ ReachAdmits names searcher findSpace findPayload findContradiction findWorld findAtFour := by
  refine ⟨findAtFour_valid, fun admits => ?_⟩
  obtain ⟨k, reached, at_k⟩ := admits.selected 4 (by simp [findAtFour])
  have below := searcher_reach_below reached
  have := (resolvesTo_nm_nil (j := 4) (k := k)).mp at_k
  omega

/-- **And only there**: every admitted selection of the search reads `b` and `(not b)` at 2. -/
theorem search_only_there (selection : Selection Nat)
    (admits : ReachAdmits names searcher findSpace findPayload findContradiction findWorld
      selection) :
    selection.read = [1, 2] := by
  have valid := admits.valid
  have readLength : selection.read.length = 2 := by
    simpa [findContradiction, LocatedRule.toRule] using valid.read_length.symm
  obtain ⟨o1, o2, read⟩ := List.length_eq_two.mp readLength
  obtain ⟨σ, solved⟩ := valid.consistent
  have reads := (Selection.models_problem action valid solved).2.2.1
  rw [read] at reads
  have pair : action.E (action.apply σ (Tm.loc (.var 0) (.var 1)))
        (action.apply σ (located spaces findSpace findPayload o1)) ∧
      action.E (action.apply σ (Tm.loc (.var 0) (notP (.var 1))))
        (action.apply σ (located spaces findSpace findPayload o2)) := by
    simpa [findContradiction, LocatedRule.toRule, place, spaces] using reads
  obtain ⟨first, second⟩ := pair
  simp only [action_E, action_apply, located, spaces, notP, Tm.subst, Tm.loc.injEq] at first second
  -- the two rows share a space, and the second negates the first
  have sameSpace : (findSpace o1).subst σ = (findSpace o2).subst σ := first.1.symm.trans second.1
  have negated : (findPayload o2).subst σ = Tm.app (.sym "not") ((findPayload o1).subst σ) := by
    rw [← second.2, first.2]
  have mem1 : o1 ∈ findWorld.present :=
    valid.occurrences.kept_subset (by simp [Selection.commit, read])
  have mem2 : o2 ∈ findWorld.present :=
    valid.occurrences.kept_subset (by simp [Selection.commit, read])
  obtain ⟨k, reached, at_k⟩ := admits.selected o1 (by simp [read])
  have below := searcher_reach_below reached
  have atK : findSpace o1 = .nm k := by
    have := at_k Tm.var (by simp [findWorld])
    simpa [spaces, Tm.subst_var] using this
  rw [read]
  clear reads first second solved reached at_k admits valid read readLength
  simp only [findWorld, Finset.mem_insert, Finset.mem_singleton] at mem1 mem2
  rcases mem1 with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases mem2 with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [findSpace, findPayload, notP, Tm.subst] at sameSpace negated atK ⊢
  all_goals omega

/-! ### A guest confined to its reach -/

/-- Occurrence 0: `p` at `thm` (3); occurrence 1: `q` at `pub` (2); occurrence 9: a probe's output
at `pub`. -/
def guestSpace : Nat → Tm
  | 0 => .nm 3
  | _ => .nm 2

def guestPayload : Nat → Tm
  | 0 => .sym "p"
  | 9 => .sym "probe"
  | _ => .sym "q"

def guestWorld : Configuration Tm Nat := ⟨[], {0, 1}⟩

/-- The same world with `thm` empty. -/
def guestWorldNoP : Configuration Tm Nat := ⟨[], {1}⟩

/-- Take a `p` at whatever space the variable denotes. -/
def grabP : LocatedRule Tm := ⟨[(.var 0, .sym "p")], [], [], [], []⟩

/-- The guest holds `pub` and the terms of its rule. -/
def guest : Set Tm := {.nm 2, .var 0, .loc (.var 0) (.sym "p")}

theorem guest_holds : HoldsRule (sts := spaces) grabP guest := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [grabP, LocatedRule.toRule, LocatedRule.spaces, place, guest, spaces]

theorem guest_names : ∀ t ∈ guest, ∀ j ∈ t.namesIn, j < 3 := by
  intro t member j named
  simp only [guest, Set.mem_insert_iff, Set.mem_singleton_iff] at member
  rcases member with rfl | rfl | rfl
  all_goals simp [Tm.namesIn] at named
  all_goals omega

theorem guest_reach_below {C : Configuration Tm Nat} (store : C.equations = [])
    (present : C.present ⊆ {0, 1}) {k : Nat}
    (reached : Reached names guest guestSpace guestPayload C k) : k < 3 := by
  apply reach_below 3 (by norm_num) guest_names ?_ (by simp [store]) reached
  intro o member k' below at_k j named
  rw [store] at at_k
  rcases Finset.mem_insert.mp (present member) with rfl | other
  · have := (resolvesTo_nm_nil (j := 3) (k := k')).mp at_k
    omega
  · rw [Finset.mem_singleton] at other
    subst other
    simp [located, spaces, guestSpace, guestPayload, Tm.namesIn] at named
    omega

/-- `thm` is not in the guest's reach. -/
theorem guest_thm_unreached : ¬ Reached names guest guestSpace guestPayload guestWorld 3 :=
  fun reached => by
    have := guest_reach_below (C := guestWorld) rfl (by simp [guestWorld]) reached
    omega

/-- **`thm` holds a match**: the candidate step would take the `p` at `thm`. -/
theorem guest_match_at_thm :
    (⟨[0], [], []⟩ : Selection Nat).Valid action (located spaces guestSpace guestPayload)
      (grabP.toRule spaces) guestWorld := by
  refine ⟨by simp, by simp, rfl, rfl, rfl,
    ⟨by simp [Selection.commit, guestWorld], by simp [Selection.commit], by simp [Selection.commit],
      by simp [Selection.commit], by simp [Selection.commit]⟩, ⟨fun _ => .nm 3, ?_⟩,
    by simp [grabP, LocatedRule.toRule]⟩
  simp [SubstitutionAction.Solves, Selection.problem, Selection.equations, grabP,
    LocatedRule.toRule, guestWorld, place, located, spaces, guestSpace, guestPayload, Tm.subst]

/-- **Negative control: the guest cannot select at `thm`.** No selection of its search is
admitted, although `thm` holds a match. -/
theorem guest_cannot_select_at_thm (selection : Selection Nat) :
    ¬ ReachAdmits names guest guestSpace guestPayload grabP guestWorld selection := by
  intro admits
  have valid := admits.valid
  have takeLength : selection.taken.length = 1 := by
    simpa [grabP, LocatedRule.toRule] using valid.take_length.symm
  obtain ⟨o, taken⟩ := List.length_eq_one_iff.mp takeLength
  obtain ⟨σ, solved⟩ := valid.consistent
  have takes := (Selection.models_problem action valid solved).2.1
  rw [taken] at takes
  have present : o ∈ guestWorld.present :=
    valid.occurrences.taken_subset (by simp [Selection.commit, taken])
  obtain ⟨k, reached, at_k⟩ := admits.selected o (by simp [taken])
  have below := guest_reach_below (C := guestWorld) rfl (by simp [guestWorld]) reached
  simp only [guestWorld, Finset.mem_insert, Finset.mem_singleton] at present
  rcases present with rfl | rfl
  · have := (resolvesTo_nm_nil (j := 3) (k := k)).mp at_k
    omega
  · simp [grabP, LocatedRule.toRule, place, located, spaces, guestSpace, guestPayload, Tm.subst]
      at takes

/-- Every reach step of the guest, of any rule it holds, leaves the `p` at `thm` in place. -/
theorem guest_cannot_affect_thm (r : LocatedRule Tm) (D : Configuration Tm Nat)
    (step : ReachStep names guest guestSpace guestPayload r guestWorld D) : 0 ∈ D.present :=
  (unreached_no_effect step guest_thm_unreached).1 0 (by simp [guestWorld]) (resolvesTo_name _ 3)

/-! ### The smallest separation from the old law -/

/-- An actor that holds `thm`. -/
def thmHolder : Set Tm := {.nm 3, .var 0, .loc (.var 0) (.sym "p")}

/-- **One port suffices to separate the laws**: a single take at an unbound space variable is a
reach step for an actor that reaches the space, and the old law refuses it. -/
theorem one_port_search_separates :
    ReachStep names thmHolder guestSpace guestPayload grabP guestWorld
        ((⟨[0], [], []⟩ : Selection Nat).result (located spaces guestSpace guestPayload)
          (grabP.toRule spaces) guestWorld) ∧
      ¬ Resolved spaces guestWorld.equations grabP := by
  refine ⟨⟨⟨[0], [], []⟩, ⟨?_, guest_match_at_thm, ?_, ?_⟩, rfl⟩, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp [grabP, LocatedRule.toRule, LocatedRule.spaces, place, thmHolder, spaces]
  · intro o member
    simp only [List.cons_append, List.nil_append, List.mem_singleton] at member
    subst member
    exact ⟨3, Reach.of_possesses (written_name_possessed ⟨Tm.var, by simp [guestWorld]⟩
      (by simp [thmHolder, spaces])), resolvesTo_name _ 3⟩
  · intro s member
    simp only [LocatedRule.spaces, grabP, List.map_cons, List.map_nil, List.filterMap_nil,
      List.append_nil, List.mem_singleton] at member
    subst member
    refine ⟨3, fun σ solved => ?_⟩
    simp [SubstitutionAction.Solves, Selection.problem, Selection.equations, grabP,
      LocatedRule.toRule, guestWorld, place, located, spaces, guestSpace, guestPayload,
      Tm.subst] at solved
    simpa [spaces, Tm.subst] using solved
  · intro resolved
    obtain ⟨n, at_n⟩ := resolved (.var 0) (by simp [LocatedRule.spaces, grabP])
    have := at_n (fun _ => .nm (n + 1)) (by simp [guestWorld])
    simp [spaces, Tm.subst] at this

/-! ### The withdrawn law's own example, under reach -/

/-- An actor that holds space 1 and the terms of the ambient take of `NamedSpaces.Controls`. -/
def holderOfOne : Set Tm := {.nm 1, .var 0, .loc (.var 0) (.sym "letter")}

theorem holderOfOne_names : ∀ t ∈ holderOfOne, ∀ j ∈ t.namesIn, j < 2 := by
  intro t member j named
  simp only [holderOfOne, Set.mem_insert_iff, Set.mem_singleton_iff] at member
  rcases member with rfl | rfl | rfl
  all_goals simp [Tm.namesIn] at named
  all_goals omega

/-- **The ambient take of the old controls, under reach.** Both selections are valid for the
candidate step, and each selection's own problem resolves the space; the actor that holds space 1
is admitted the take at 1 and refused the take at 2. Resolution after selection, vacuous on its
own, is not vacuous relative to reach. -/
theorem ambient_take_within_reach :
    ReachAdmits names holderOfOne twoSpaces letter grabAnywhere twoWorld takeFirst ∧
      ¬ ReachAdmits names holderOfOne twoSpaces letter grabAnywhere twoWorld takeSecond := by
  constructor
  · refine ⟨?_, unresolved_takes_from_either_space.1, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_⟩ <;>
        simp [grabAnywhere, LocatedRule.toRule, LocatedRule.spaces, place, holderOfOne, spaces]
    · intro o member
      simp only [takeFirst, List.append_nil, List.mem_singleton] at member
      subst member
      exact ⟨1, Reach.of_possesses (written_name_possessed ⟨Tm.var, by simp [twoWorld]⟩
        (by simp [holderOfOne, spaces])), resolvesTo_name _ 1⟩
    · intro s member
      simp only [LocatedRule.spaces, grabAnywhere, List.map_cons, List.map_nil,
        List.filterMap_nil, List.append_nil, List.mem_singleton] at member
      subst member
      refine ⟨1, fun σ solved => ?_⟩
      simpa [spaces, Tm.subst] using unresolved_space_differs_by_selection.1 σ solved
  · intro admits
    obtain ⟨k, reached, at_k⟩ := admits.selected 1 (by simp [takeSecond])
    have below := reach_below 2 (by norm_num) holderOfOne_names ?_ (by simp [twoWorld]) reached
    · have named : twoSpaces 1 = .nm 2 := by simp [twoSpaces]
      rw [named] at at_k
      have := (resolvesTo_nm_nil (j := 2) (k := k)).mp at_k
      omega
    · intro o present k' below' at_k' j named
      simp only [twoWorld, Finset.mem_insert, Finset.mem_singleton] at present
      rcases present with rfl | rfl
      · simp [located, spaces, twoSpaces, letter, Tm.namesIn] at named
        omega
      · have spaceOne : twoSpaces 1 = .nm 2 := by simp [twoSpaces]
        rw [spaceOne] at at_k'
        have := (resolvesTo_nm_nil (j := 2) (k := k')).mp at_k'
        omega

/-! ### Why every check space must resolve -/

/-- An absence check at an unbound space, then an output at `pub`. -/
def probe : LocatedRule Tm := ⟨[], [], [], [.absent (.var 5) (.sym "p")], [(.nm 2, .sym "probe")]⟩

def probeSel : Selection Nat := ⟨[], [], [9]⟩

/-- **In the candidate step an unbound check observes `thm`**: the probe fires when `thm` is
empty and not when `thm` holds `p`, and the two worlds differ only at `thm`. -/
theorem candidate_absence_observes_thm :
    probeSel.Valid action (located spaces guestSpace guestPayload) (probe.toRule spaces)
        guestWorldNoP ∧
      ¬ probeSel.Valid action (located spaces guestSpace guestPayload) (probe.toRule spaces)
        guestWorld := by
  constructor
  · refine ⟨by simp [probeSel], by simp [probeSel], rfl, rfl, rfl,
      ⟨by simp [Selection.commit, probeSel], by simp [Selection.commit, probeSel],
        by simp [Selection.commit, probeSel], by simp [Selection.commit, probeSel, guestWorldNoP],
        by simp [Selection.commit]⟩, ⟨Tm.var, by simp [Selection.problem, Selection.equations,
          probe, LocatedRule.toRule, guestWorldNoP, probeSel]⟩, ?_⟩
    intro check member σ _
    simp only [probe, LocatedRule.toRule, LocatedCheck.toCheck, List.map_cons, List.map_nil,
      List.mem_singleton] at member
    subst member
    intro o present
    simp only [guestWorldNoP, Finset.mem_singleton] at present
    subst present
    simp [spaces, located, guestSpace, guestPayload, Tm.subst]
  · intro valid
    have holds := valid.checks (.absent (spaces.atSpace (.var 5) (.sym "p")))
      (by simp [probe, LocatedRule.toRule, LocatedCheck.toCheck]) (fun _ => .nm 3)
      (by simp [Selection.problem, Selection.equations, probe, LocatedRule.toRule, guestWorld,
        probeSel])
    exact holds 0 (by simp [guestWorld]) (by simp [spaces, located, guestSpace, guestPayload,
      Tm.subst])

/-- **The reach step refuses it**: the check's space is resolved by nothing in the firing. -/
theorem reach_refuses_unbound_absence (K : Set Tm) (C : Configuration Tm Nat)
    (store : C.equations = []) (selection : Selection Nat) :
    ¬ ReachAdmits names K guestSpace guestPayload probe C selection := by
  intro admits
  obtain ⟨n, at_n⟩ := admits.resolved (.var 5) (by simp [LocatedRule.spaces, probe, LocatedCheck.space?])
  have := at_n (fun _ => .nm (n + 1)) (by
    simp [Selection.problem, Selection.equations, probe, LocatedRule.toRule, store])
  simp [spaces, Tm.subst] at this

end ReachControls

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NamedSpaces

/-! ## Axiom audit -/

section Audit

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NamedSpaces

#print axioms holdsRule_terms
#print axioms HoldsRule.mono
#print axioms mem_equations_of_mem
#print axioms mem_equations_of_mem_right
#print axioms ReachStep.step
#print axioms ReachAdmits.present
#print axioms ReachAdmits.selected_labels
#print axioms resolved_in_firing_reached_of
#print axioms resolved_in_firing_reached
#print axioms ReachAdmits.space_reached
#print axioms made_port
#print axioms ReachAdmits.made_reached
#print axioms ReachAdmits.check_matches_reached
#print axioms ReachAdmits.effects_in_reach
#print axioms ReachAdmits.unreached_survives
#print axioms ReachAdmits.unreached_no_arrival
#print axioms ReachAdmits.unreached_untouched
#print axioms unreached_no_effect
#print axioms ReachAdmits.unreached_unobserved
#print axioms AgreeOnReach.reached_iff
#print axioms AgreeOnReach.symm
#print axioms valid_of_agree_on_reach
#print axioms ReachAdmits.of_agree
#print axioms reachAdmits_iff_of_agree
#print axioms unreached_no_observation
#print axioms ReachStep.wellLocated
#print axioms reach_after_reach_step
#print axioms ReachAdmits.mono
#print axioms ReachStep.mono
#print axioms other_reach_after_reach_step
#print axioms reach_after_reach_run
#print axioms located_step_is_reach_step
#print axioms selected_ports_resolve
#print axioms owner_admits_iff
#print axioms owner_admits_iff_outputs
#print axioms writes_every_name
#print axioms Controls.Tm.swap_eq_self
#print axioms Controls.reach_below
#print axioms Controls.resolvesTo_nm_nil
#print axioms ReachControls.follower_holds
#print axioms ReachControls.follower_names
#print axioms ReachControls.one_reached
#print axioms ReachControls.seven_reached
#print axioms ReachControls.follow_valid
#print axioms ReachControls.follow_resolves_seven
#print axioms ReachControls.follow_admits
#print axioms ReachControls.indirection_admitted
#print axioms ReachControls.follow_not_resolved
#print axioms ReachControls.indirection_separates
#print axioms ReachControls.handle_gives_reach
#print axioms ReachControls.seven_unreached_without_handle
#print axioms ReachControls.no_handle_no_reach
#print axioms ReachControls.searcher_holds
#print axioms ReachControls.searcher_names
#print axioms ReachControls.find_labels_below
#print axioms ReachControls.searcher_reach_below
#print axioms ReachControls.held_reached
#print axioms ReachControls.findAtTwo_valid
#print axioms ReachControls.findAtFour_valid
#print axioms ReachControls.search_finds_held_contradiction
#print axioms ReachControls.search_ignores_unheld
#print axioms ReachControls.search_only_there
#print axioms ReachControls.guest_holds
#print axioms ReachControls.guest_names
#print axioms ReachControls.guest_reach_below
#print axioms ReachControls.guest_thm_unreached
#print axioms ReachControls.guest_match_at_thm
#print axioms ReachControls.guest_cannot_select_at_thm
#print axioms ReachControls.guest_cannot_affect_thm
#print axioms ReachControls.one_port_search_separates
#print axioms ReachControls.candidate_absence_observes_thm
#print axioms ReachControls.reach_refuses_unbound_absence
#print axioms ReachControls.holderOfOne_names
#print axioms ReachControls.ambient_take_within_reach

end Audit
