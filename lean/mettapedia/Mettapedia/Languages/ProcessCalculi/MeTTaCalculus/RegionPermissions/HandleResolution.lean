import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.RegionPermissions.OwnedReads
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Reflection.QuotedNames

/-!
# Where a location's facets come from: handles, and names

A region is addressed by a name (`Reflection.Name`: a fresh atom, a public symbol, or a quoted
term). A process holds fresh atoms `K` and a list of **handles**: opaque references to a region,
each carrying facets, that it can only receive, never write down.

Two ways to resolve a location to facets:

* **Handles only** (`handleFacets`): a location's facets are those of the handles the process
  holds for it. Writing a name grants nothing.
* **Names resolve to the holder's facets** (`nameFacets`): a location the process can write down
  (`Builds K n`) also gives it the facets of the region's holder. This is how the draft's
  interaction kernel resolves a location that is not a handle.

## Naming is authority under the second rule

* **A public name gives every process the holder's facets** (`public_name_gives_holder`), even a
  process with no atoms and no handles (`Public.builds`). So a board region named by a public
  symbol has as many minters as processes (`public_board_others_send`), and its universal reads
  are falsified by any of them (`OwnedReads.absence_falsified_of_other_send`).
* **A fresh name gives nothing to a non-holder of its atom** (`fresh_name_handles_only`): the two
  rules agree there. A region created fresh and never given a public name is protected under both.

## Handles attenuate

The facet operation intersects a handle's facets with the wanted facets and with what the profile
lets the holder hand out (`facetOf`, `facetOf_le`, `facetOf_le_handout`), so a process whose
handles were all derived from the holder's handle by the facet operation holds at most what the
profile hands out (`handout_bound`), and a board region that hands out only `peek` has no other
minter (`board_handles_no_other_send`).

## Learning: names and facets, dynamic runs and authority runs

Reading a carried name as every facet at it, the facets a commit teaches are the names it teaches
(`facets_learned_eq_names`). Every one-process authority run is a dynamic run of the names where a
facet is held (`AuthorityRun.dynamicRun`), and a dynamic run is an authority run with name-level
rights exactly when each of its commits makes only names held before it (`MakesHeld`,
`authorityRun_iff_dynamicRun`). They part at same-step forwarding and at constants
(`Controls.same_step_forwarding_parts`, `Controls.constant_parts`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.RegionPermissions

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Reflection
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.InteractionTypes

universe uA uF

variable {A : Type uA} [DecidableEq A] {F : Type uF} [DecidableEq F]

/-- A region's profile: its holder's facets, and the most a handed-out facet may carry. -/
structure Profile where
  holder : Facet → Bool
  handout : Facet → Bool

/-- A handle: the region it designates and the facets it carries. -/
abbrev Handle (A : Type uA) (F : Type uF) := Reflection.Name A F × (Facet → Bool)

/-- **Handles only**: the facets of the handles held for the region. -/
def handleFacets (handles : List (Handle A F)) (n : Reflection.Name A F) (f : Facet) : Bool :=
  handles.any fun h => decide (h.1 = n) && h.2 f

/-- **Names resolve to the holder's facets**: handles, plus the holder's facets when the process
can write the region's name. -/
def nameFacets (profile : Reflection.Name A F → Profile) (K : Finset A) (handles : List (Handle A F))
    (n : Reflection.Name A F) (f : Facet) : Bool :=
  handleFacets handles n f || (heldBy K n && (profile n).holder f)

/-- **A public name gives every process the holder's facets.** -/
theorem public_name_gives_holder (profile : Reflection.Name A F → Profile) {n : Reflection.Name A F}
    (public_ : Public n) {f : Facet} (holder : (profile n).holder f = true) (K : Finset A)
    (handles : List (Handle A F)) : nameFacets profile K handles n f = true := by
  simp [nameFacets, heldBy_public public_ K, holder]

/-- **A fresh name gives a non-holder of its atom nothing beyond its handles.** -/
theorem fresh_name_handles_only (profile : Reflection.Name A F → Profile) {K : Finset A} {a : A}
    (notHeld : a ∉ K) (handles : List (Handle A F)) (f : Facet) :
    nameFacets profile K handles (.nu a) f = handleFacets handles (.nu a) f := by
  have : heldBy K (.nu a : Reflection.Name A F) = false := by
    cases held : heldBy K (.nu a : Reflection.Name A F) with
    | false => rfl
    | true => exact absurd (heldBy_iff.mp held) (nu_not_builds notHeld)
  simp [nameFacets, this]

/-- The facet operation: the handle's facets, the wanted facets, and the profile's hand-out. -/
def facetOf (profile : Reflection.Name A F → Profile) (h : Handle A F) (wanted : Facet → Bool) :
    Handle A F :=
  (h.1, fun f => h.2 f && wanted f && (profile h.1).handout f)

omit [DecidableEq A] [DecidableEq F] in
theorem facetOf_le (profile : Reflection.Name A F → Profile) (h : Handle A F) (wanted : Facet → Bool)
    {f : Facet} (has : (facetOf profile h wanted).2 f = true) : h.2 f = true := by
  simp only [facetOf, Bool.and_eq_true] at has
  exact has.1.1

omit [DecidableEq A] [DecidableEq F] in
theorem facetOf_le_handout (profile : Reflection.Name A F → Profile) (h : Handle A F)
    (wanted : Facet → Bool) {f : Facet} (has : (facetOf profile h wanted).2 f = true) :
    (profile h.1).handout f = true := by
  simp only [facetOf, Bool.and_eq_true] at has
  exact has.2

/-- **Handed-out handles carry at most the profile's hand-out**: if every handle a process holds
was made by the facet operation, its handle facets at a region lie within the hand-out. -/
theorem handout_bound (profile : Reflection.Name A F → Profile) {handles : List (Handle A F)}
    (derived : ∀ h ∈ handles, ∃ g wanted, h = facetOf profile g wanted) {n : Reflection.Name A F}
    {f : Facet} (has : handleFacets handles n f = true) : (profile n).handout f = true := by
  obtain ⟨h, member, hit⟩ := List.any_eq_true.mp has
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hit
  obtain ⟨g, wanted, rfl⟩ := derived h member
  have := facetOf_le_handout profile g wanted hit.2
  rw [← hit.1]
  exact this

section Systems

variable {O : Type} {R : Type} {I : Type}

/-- **A board named by a public symbol has a minter in every process**: under name resolution,
every process other than the holder holds `send` at it, so the others' authority there is not
empty. -/
theorem public_board_others_send (profile : Reflection.Name A F → Profile) {n : Reflection.Name A F}
    (public_ : Public n) (holderSends : (profile n).holder .send = true)
    (label : O → R) (carries : R → Rights (Reflection.Name A F)) (K : I → Finset A)
    (handles : I → List (Handle A F)) (S : Finset O) {holder i : I} (notHolder : i ≠ holder) :
    OthersAuthority label carries (fun j => nameFacets profile (K j) (handles j)) S holder n .send :=
  Or.inl ⟨i, notHolder, public_name_gives_holder profile public_ holderSends (K i) (handles i)⟩

/-- **A board whose profile hands out only `peek` has no other minter under handle-only
resolution**, when every handle another process holds was handed out through the facet operation
and no occurrence carries `send` there. -/
theorem board_handles_no_other_send (profile : Reflection.Name A F → Profile) {n : Reflection.Name A F}
    (noSendOut : (profile n).handout .send = false) (label : O → R)
    (carries : R → Rights (Reflection.Name A F)) (handles : I → List (Handle A F)) (S : Finset O)
    {holder : I}
    (derived : ∀ j, j ≠ holder → ∀ h ∈ handles j, ∃ g wanted, h = facetOf profile g wanted)
    (inert : ∀ o ∈ S, carries (label o) n .send = false) :
    ¬ OthersAuthority label carries (fun j => handleFacets (handles j)) S holder n .send := by
  rintro (⟨j, notHolder, held⟩ | ⟨o, member, carried⟩)
  · have := handout_bound profile (derived j notHolder) held
    rw [noSendOut] at this
    exact absurd this (by decide)
  · rw [inert o member] at carried
    exact absurd carried (by decide)

end Systems

/-! ## Names carried are facets carried

`OccurrenceCommits.ScopeExtrusion` lets a process learn the names carried by what it takes, keeps or
sees in a predicate query; `InteractionTypes.Facets` lets it learn the facets carried by the same
occurrences (`Commit.learnedFrom`). Reading a carried name as every facet at it, the two coincide
(`facets_learned_eq_names`). The step disciplines differ: a dynamic run may forward a name in the
commit that learns it and may use constants (`BuildsFromHeld`), while an authority step makes only
capabilities its process already held (`Attenuates`); the next section says exactly where. -/

section Learning

variable {O : Type} [DecidableEq O] {R : Type} {N : Type} [DecidableEq N]

/-- Every facet at each carried name. -/
def namesCarry (names : R → Finset N) : R → Rights N := fun r n _ => decide (n ∈ names r)

/-- **The facets a commit teaches are the names it teaches**, with every facet at each. -/
theorem facets_learned_eq_names (label : O → R) (names : R → Finset N) (c : Commit O R) (n : N)
    (f : Facet) :
    InteractionTypes.learned label (namesCarry names) c n f =
      decide (n ∈ OccurrenceCommits.learned label names c) := by
  unfold InteractionTypes.learned OccurrenceCommits.learned namesCarry
  apply decide_eq_decide.mpr
  simp only [decide_eq_true_eq, Finset.mem_biUnion]

end Learning

/-! ## Dynamic runs and authority runs: where the step disciplines part

`OccurrenceCommits.DynamicRun` grows a process's rights, as a set of names, by the names it learns,
and lets a commit make occurrences carrying held names, names it learns in the same commit, and
constants (`BuildsFromHeld`). `InteractionTypes.AuthorityRun` grows rights, as facets, by the facets
it learns, and lets a commit make only capabilities its process held before the commit
(`Attenuates`). Reading a carried name as every facet at it (`namesCarry`) and a held name as every
facet at it (`atNames`), the two meet exactly at one condition on the commits of a run: each makes
only names held before it (`MakesHeld`).

* **An authority run is a dynamic run**, of the names where some facet is held, for any constants
  (`AuthorityRun.dynamicRun`); so the closed-scope laws of `ScopeExtrusion` hold for it.
* **A dynamic run is an authority run exactly when its commits make only names held before them**
  (`authorityRun_iff_dynamicRun`). They part at same-step forwarding
  (`Controls.same_step_forwarding_parts`) and at constants (`Controls.constant_parts`); forwarding
  a name in a later commit is in both (`Controls.later_forwarding_in_both`). -/

section Runs

variable {O : Type} [DecidableEq O] {R : Type} {N : Type} [DecidableEq N]
variable (label : O → R) (loc : R → N) (names : R → Finset N)

/-- Rights held as names: every facet at each name of `K`, for the one process. -/
def atNames (K : Finset N) : Unit → Rights N := fun _ n _ => decide (n ∈ K)

/-- **Every commit of a run makes only names held before it**: no name forwarded in the commit
that learns it, and no constant. -/
inductive MakesHeld : Finset N → List (Commit O R) → Prop
  | nil (K : Finset N) : MakesHeld K []
  | cons {K : Finset N} {c : Commit O R} {rest : List (Commit O R)}
      (held : ∀ o ∈ c.made, names (label o) ⊆ K)
      (after : MakesHeld (K ∪ OccurrenceCommits.learned label names c) rest) :
      MakesHeld K (c :: rest)

variable {label loc names}

omit [DecidableEq O] in
/-- Formation under name-level rights is scoping to the names. -/
theorem formedUnder_atNames_iff {K : Finset N} {c : Commit O R} :
    FormedUnder label loc (atNames K ()) c ↔ Scoped label loc (holds K) c :=
  ⟨fun f => ⟨f.taken, f.kept, f.made, f.queries⟩, fun s => ⟨s.taken, s.kept, s.made, s.queries⟩⟩

omit [DecidableEq O] in
/-- Attenuation under name-level rights is making only held names. -/
theorem attenuates_atNames_iff {K : Finset N} {c : Commit O R} :
    Attenuates label (namesCarry names) (atNames K ()) c ↔ ∀ o ∈ c.made, names (label o) ⊆ K := by
  constructor
  · intro att o made n carried
    have := att o made n .send (by simp [namesCarry, carried])
    simpa [atNames] using this
  · intro held o made n f carried
    simp only [namesCarry, decide_eq_true_eq] at carried
    simpa [atNames] using held o made carried

/-- What an authority step learns, under name-level rights, is the names it learns. -/
theorem learned_atNames {K : Finset N} {c : Commit O R} :
    Function.update (atNames K) ()
        (fun n f => atNames K () n f || InteractionTypes.learned label (namesCarry names) c n f) =
      atNames (K ∪ OccurrenceCommits.learned label names c) := by
  funext i n f
  cases i
  simp [atNames, facets_learned_eq_names]

theorem atNames_injective {K K' : Finset N} (h : atNames K = atNames K') : K = K' := by
  ext n
  have := congrFun (congrFun (congrFun h ()) n) .send
  simpa [atNames] using this

/-- **A dynamic run is an authority run exactly when its commits make only names held before
them.** Under name-level rights, a one-process authority run of a list of commits ends at
name-level rights `K'` exactly when the commits are a dynamic run to `K'` (for any constants) that
makes only held names. -/
theorem authorityRun_iff_dynamicRun {constants : Finset N} :
    ∀ {run : List (Commit O R)} {S S' : Finset O} {K : Finset N} {Γ' : Unit → Rights N},
      AuthorityRun (label := label) (loc := loc) (carries := namesCarry names) (atNames K) S
          (run.map fun c => ((), c)) Γ' S' ↔
        ∃ K', Γ' = atNames K' ∧ DynamicRun label loc names constants S K run S' K' ∧
          MakesHeld label names K run
  | [], S, S', K, Γ' => by
      constructor
      · intro r
        cases r
        exact ⟨K, rfl, .nil _ _, .nil _⟩
      · rintro ⟨K', rfl, dyn, -⟩
        cases dyn
        exact .nil _ _
  | c :: rest, S, S', K, Γ' => by
      constructor
      · intro r
        cases r with
        | cons step after =>
            obtain ⟨enabled, formed, att, rights, store⟩ := step
            rw [learned_atNames] at rights
            subst rights store
            obtain ⟨K', hK', dyn, mh⟩ := (authorityRun_iff_dynamicRun (constants := constants)).mp after
            have held := attenuates_atNames_iff.mp att
            refine ⟨K', hK', .cons enabled (formedUnder_atNames_iff.mp formed) ?_ dyn, .cons held mh⟩
            intro o made n carried
            exact Finset.mem_union_left _ (Finset.mem_union_left _ (held o made carried))
      · rintro ⟨K', rfl, dyn, mh⟩
        cases dyn with
        | cons enabled inScope _ after =>
            cases mh with
            | cons held mhAfter =>
                refine .cons ⟨enabled, formedUnder_atNames_iff.mpr inScope,
                  attenuates_atNames_iff.mpr held, learned_atNames.symm, rfl⟩ ?_
                exact (authorityRun_iff_dynamicRun (constants := constants)).mpr
                  ⟨K', rfl, after, mhAfter⟩

/-- **An authority run is a dynamic run** of the names where its process holds some facet, for any
constants: formed commits are scoped to those names, attenuating commits make only them, and the
names learned are the facets learned. -/
theorem AuthorityRun.dynamicRun {constants : Finset N} :
    ∀ {run : List (Commit O R)} {S S' : Finset O} {Γ Γ' : Unit → Rights N} {K : Finset N},
      AuthorityRun (label := label) (loc := loc) (carries := namesCarry names) Γ S
          (run.map fun c => ((), c)) Γ' S' →
      (∀ n, holdsSome (Γ ()) n = true ↔ n ∈ K) →
      ∃ K', DynamicRun label loc names constants S K run S' K' ∧
        ∀ n, holdsSome (Γ' ()) n = true ↔ n ∈ K'
  | [], S, S', Γ, Γ', K, r, represents => by
      cases r
      exact ⟨K, .nil _ _, represents⟩
  | c :: rest, S, S', Γ, Γ', K, r, represents => by
      cases r with
      | cons step after =>
          obtain ⟨enabled, formed, att, rights, store⟩ := step
          subst rights store
          have toK : ∀ n, holdsSome (Γ ()) n = true → holds K n = true := fun n h => by
            simpa [holds] using (represents n).mp h
          have inScope : Scoped label loc (holds K) c :=
            let s := formed.scoped
            ⟨fun o m => toK _ (s.taken o m), fun o m => toK _ (s.kept o m),
              fun o m => toK _ (s.made o m), fun q m r hr => toK _ (s.queries q m r hr)⟩
          have builds : BuildsFromHeld label names constants K c := by
            intro o made n carried
            have : Γ () n .send = true := att o made n .send (by simp [namesCarry, carried])
            exact Finset.mem_union_left _ (Finset.mem_union_left _
              ((represents n).mp (by simp [holdsSome, this])))
          have representsNext : ∀ n, holdsSome (Function.update Γ ()
              (fun n f => Γ () n f || InteractionTypes.learned label (namesCarry names) c n f) ()) n =
                true ↔ n ∈ K ∪ OccurrenceCommits.learned label names c := by
            intro n
            simp only [Function.update_self, facets_learned_eq_names, holdsSome, Bool.or_eq_true,
              decide_eq_true_eq, Finset.mem_union]
            rw [← represents n]
            simp only [holdsSome, Bool.or_eq_true]
            tauto
          obtain ⟨K', dyn, represents'⟩ := AuthorityRun.dynamicRun after representsNext
          exact ⟨K', .cons enabled inScope builds dyn, represents'⟩

end Runs

namespace Controls

/-- A message `0` carrying name `7`, seen by a predicate query. -/
def learnLabel : ℕ → Finset ℕ := fun o => if o = 0 then {7} else ∅

/-- Query the region of every occurrence, having seen `0`. -/
def readAll : Commit ℕ ℕ := ⟨∅, ∅, ∅, [⟨fun _ => true, {0}⟩]⟩

/-- **A predicate query teaches facets**: the commit that saw `0` learns every facet at name `7`,
and no facet at name `8`. -/
theorem predicate_query_teaches :
    InteractionTypes.learned id (namesCarry learnLabel) readAll 7 .send = true ∧
      InteractionTypes.learned id (namesCarry learnLabel) readAll 8 .send = false := by
  refine ⟨?_, ?_⟩ <;> rw [facets_learned_eq_names] <;> decide

/-! ### Where dynamic runs and authority runs part -/

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Controls in
/-- **Same-step forwarding parts them**: taking the message that carries name `0` and sending `0`
on in the same commit is a dynamic run from rights `{1}`, and no authority run with name-level
rights. -/
theorem same_step_forwarding_parts :
    DynamicRun fwdLabel Prod.fst carried ∅ {300} {1} [learnAndForward] {303} {1, 0} ∧
      ¬ MakesHeld fwdLabel carried {1} [learnAndForward] ∧
      ¬ ∃ Γ' S', AuthorityRun (label := fwdLabel) (loc := Prod.fst) (carries := namesCarry carried)
        (atNames {1}) {300} [((), learnAndForward)] Γ' S' := by
  have notHeld : ¬ MakesHeld fwdLabel carried {1} [learnAndForward] := by
    intro mh
    cases mh with
    | cons held _ =>
        have := held 303 (by simp [learnAndForward])
        revert this
        decide
  refine ⟨?_, notHeld, fun ⟨Γ', S', r⟩ => ?_⟩
  · refine .cons ⟨by decide, by decide, by decide, by decide, by simp [learnAndForward]⟩
      ⟨by decide, by simp [learnAndForward], by decide, by simp [learnAndForward]⟩
      learnAndForward_builds_from_held ?_
    convert DynamicRun.nil (label := fwdLabel) (loc := Prod.fst) (names := carried)
      (constants := ∅) ({303} : Finset ℕ) ({1, 0} : Finset ℕ) using 2 <;> decide
  · obtain ⟨K', -, -, mh⟩ := (authorityRun_iff_dynamicRun (constants := ∅)
      (run := [learnAndForward])).mp r
    exact notHeld mh

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Controls in
/-- **Constants part them**: with name `7` a constant, sending a message carrying `7` is a dynamic
run from rights `{1}`, and no authority run with name-level rights. -/
theorem constant_parts :
    DynamicRun fwdLabel Prod.fst carried {7} ∅ {1} [OccurrenceCommits.Controls.forge] {304} {1} ∧
      ¬ ∃ Γ' S', AuthorityRun (label := fwdLabel) (loc := Prod.fst) (carries := namesCarry carried)
        (atNames {1}) ∅ [((), OccurrenceCommits.Controls.forge)] Γ' S' := by
  refine ⟨?_, fun ⟨Γ', S', r⟩ => ?_⟩
  · refine .cons ⟨by simp [OccurrenceCommits.Controls.forge], by simp [OccurrenceCommits.Controls.forge],
        by simp [OccurrenceCommits.Controls.forge], by decide, by simp [OccurrenceCommits.Controls.forge]⟩
      ⟨by simp [OccurrenceCommits.Controls.forge], by simp [OccurrenceCommits.Controls.forge], by decide,
        by simp [OccurrenceCommits.Controls.forge]⟩ (by unfold BuildsFromHeld OccurrenceCommits.learned; decide) ?_
    convert DynamicRun.nil (label := fwdLabel) (loc := Prod.fst) (names := carried)
      (constants := {7}) ({304} : Finset ℕ) ({1} : Finset ℕ) using 2 <;> decide
  · obtain ⟨K', -, -, mh⟩ := (authorityRun_iff_dynamicRun (constants := ∅)
      (run := [OccurrenceCommits.Controls.forge])).mp r
    cases mh with
    | cons held _ =>
        have := held 304 (by simp [OccurrenceCommits.Controls.forge])
        revert this
        decide

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Controls in
/-- **Forwarding a learned name in a later commit is in both**: the run that takes the message
carrying `0` and then sends `0` on makes only held names, so it is an authority run. -/
theorem later_forwarding_in_both :
    MakesHeld fwdLabel carried {1} [takeMessage, forward] ∧
      AuthorityRun (label := fwdLabel) (loc := Prod.fst) (carries := namesCarry carried)
        (atNames {1}) {300} [((), takeMessage), ((), forward)] (atNames {1, 0}) {303} := by
  have mh : MakesHeld fwdLabel carried {1} [takeMessage, forward] := by
    refine .cons (by simp [takeMessage]) (.cons ?_ ?_)
    · intro o made
      simp only [forward, Finset.mem_singleton] at made
      subst made
      unfold OccurrenceCommits.learned
      decide
    · convert MakesHeld.nil (label := fwdLabel) (names := carried) _ using 1
  refine ⟨mh, (authorityRun_iff_dynamicRun (constants := ∅) (run := [takeMessage, forward])).mpr
    ⟨{1, 0}, rfl, forwarding_in_class, mh⟩⟩

end Controls

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.RegionPermissions
