import Mettapedia.GSLT.Causality.ResourceInteraction

/-!
# Exploring a resource system: runs, outcomes and what all-answer search counts

A run fires enabled instances until none is enabled. A rho execution follows
one run. An all-answer search enumerates every run and collects the final
bags; that list is the outcome of the search.

The explorer below enumerates the runs through a finite catalogue of instances.
Every run it returns is a genuine run ending in a terminal bag, and every run
of the catalogued instances within the fuel is returned, with its order.

A firing is named by its instance, so two firings of one instance on two copies
of a resource are one run: the enumeration does not tell copies apart.
Different concurrent instances give two runs, one per order, with one final
bag, and they are one trace: collecting per run counts interleavings. Equal
answers from conflicting firings are two runs, not one. A choice shared by two
uses gives only the diagonal outcomes, while two independent choices give every
combination.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.ResourceInteraction

open Mettapedia.GSLT

universe uRes uRule

namespace System

variable {R : Type uRes} [DecidableEq R] (S : System.{uRes, uRule} R)

/-- A catalogued instance: a site with one of its instances. -/
abbrev Entry := Σ site : S.Site, S.Instance site

/-- Whether an instance is enabled, as a computation. -/
def enabledB (M : Multiset R) (entry : S.Entry) : Bool :=
  decide (S.consume entry.2 + S.read entry.2 ≤ M)

theorem enabledB_iff (M : Multiset R) (entry : S.Entry) :
    S.enabledB M entry = true ↔ S.Enables M entry.2 := by
  unfold enabledB Enables
  exact decide_eq_true_iff

variable (catalogue : List S.Entry)

/-- The catalogued instances enabled at a bag, in catalogue order. -/
def enabledAt (M : Multiset R) : List S.Entry :=
  catalogue.filter (S.enabledB M)

/-- Every maximal run of at most `fuel` firings: its entries in firing order and
its final bag. Runs that would need more fuel are not returned. -/
def runs : ℕ → Multiset R → List (List S.Entry × Multiset R)
  | 0, M => if (S.enabledAt catalogue M).isEmpty then [([], M)] else []
  | fuel + 1, M =>
      if (S.enabledAt catalogue M).isEmpty then [([], M)]
      else (S.enabledAt catalogue M).flatMap fun entry =>
        (runs fuel (S.fire M entry.2)).map fun run => (entry :: run.1, run.2)

/-- The final bags of the runs, one per run. -/
def outcomes (fuel : ℕ) (M : Multiset R) : List (Multiset R) :=
  (S.runs catalogue fuel M).map Prod.snd

/-- A sequence of firings, each enabled at the bag it fires in. -/
def Fires : List S.Entry → Multiset R → Multiset R → Prop
  | [], M, N => N = M
  | entry :: rest, M, N => S.Enables M entry.2 ∧ Fires rest (S.fire M entry.2) N

/-- **Every returned run is a genuine run**: its firings are enabled in turn,
and it ends in a bag where no catalogued instance is enabled. -/
theorem runs_sound : ∀ (fuel : ℕ) (M : Multiset R) (run : List S.Entry × Multiset R),
    run ∈ S.runs catalogue fuel M →
      S.Fires run.1 M run.2 ∧ S.enabledAt catalogue run.2 = []
  | 0, M, run, h => by
      unfold runs at h
      split at h
      · next empty =>
          simp only [List.mem_singleton] at h
          subst h
          exact ⟨rfl, List.isEmpty_iff.mp empty⟩
      · simp at h
  | fuel + 1, M, run, h => by
      unfold runs at h
      split at h
      · next empty =>
          simp only [List.mem_singleton] at h
          subst h
          exact ⟨rfl, List.isEmpty_iff.mp empty⟩
      · obtain ⟨entry, member, h⟩ := List.mem_flatMap.mp h
        obtain ⟨tail, tailMember, rfl⟩ := List.mem_map.mp h
        obtain ⟨fires, terminal⟩ := runs_sound fuel _ tail tailMember
        refine ⟨⟨?_, fires⟩, terminal⟩
        have := (List.mem_filter.mp member).2
        exact (S.enabledB_iff M entry).mp this

/-- **Every run of catalogued instances within the fuel is returned**, with its
order. -/
theorem runs_complete : ∀ (fuel : ℕ) (M : Multiset R) (path : List S.Entry) (N : Multiset R),
    path.length ≤ fuel → (∀ entry ∈ path, entry ∈ catalogue) → S.Fires path M N →
      S.enabledAt catalogue N = [] → (path, N) ∈ S.runs catalogue fuel M
  | fuel, M, [], N, _, _, fires, terminal => by
      change N = M at fires
      subst fires
      cases fuel with
      | zero =>
          unfold runs
          simp [terminal]
      | succ fuel =>
          unfold runs
          simp [terminal]
  | 0, M, entry :: rest, N, length, _, _, _ => by
      simp at length
  | fuel + 1, M, entry :: rest, N, length, catalogued, fires, terminal => by
      obtain ⟨enabled, restFires⟩ := fires
      have enabledMember : entry ∈ S.enabledAt catalogue M :=
        List.mem_filter.mpr ⟨catalogued entry List.mem_cons_self,
          (S.enabledB_iff M entry).mpr enabled⟩
      have nonempty : (S.enabledAt catalogue M).isEmpty = false := by
        cases h : S.enabledAt catalogue M with
        | nil => rw [h] at enabledMember; cases enabledMember
        | cons _ _ => rfl
      unfold runs
      rw [if_neg (by simp [nonempty])]
      refine List.mem_flatMap.mpr ⟨entry, enabledMember, ?_⟩
      refine List.mem_map.mpr ⟨(rest, N), ?_, rfl⟩
      exact runs_complete fuel _ rest N (by simpa using length)
        (fun e h => catalogued e (List.mem_cons_of_mem entry h)) restFires terminal

end System

/-! ## Controls: what an all-answer search counts -/

namespace ExplorationControls

open Controls

/-- The entry answering the call by equation `index`. -/
def spaceEntry (index : ℕ) : space.Entry := ⟨(), index⟩

/-- **Two calls answered by one equation: one run.** The explorer names a firing
by its instance, and the two firings of the shared equation are one instance on
two copies of the call: the enumeration does not tell the copies apart. -/
theorem shared_equation_one_run :
    (space.runs [spaceEntry 1] 2 twoCallsOneEquation).map
        (fun run => (run.1.map fun entry => (entry.2 : ℕ), run.2)) =
      [([1, 1], {SpaceRes.answer 1, SpaceRes.answer 1, SpaceRes.equation 1})] := by
  decide

/-- **One call, two equations with equal answers: two runs, two answer
occurrences.** Conflicting firings are not identified by their equal results. -/
def twinSpace : System SpaceRes where
  Site := Unit
  Instance := fun _ => ℕ
  consume := fun _ => {SpaceRes.call}
  read := fun index => {SpaceRes.equation index}
  produce := fun _ => {SpaceRes.answer 0}

def twinEntry (index : ℕ) : twinSpace.Entry := ⟨(), index⟩

theorem twin_equations_two_occurrences :
    twinSpace.outcomes [twinEntry 1, twinEntry 2] 1 oneCallTwoEquations =
      [{SpaceRes.answer 0, SpaceRes.equation 1, SpaceRes.equation 2},
       {SpaceRes.answer 0, SpaceRes.equation 1, SpaceRes.equation 2}] := by
  decide

/-- Resources for choosing a colour: calls, the two colour equations, a chosen
value, a duplicator, and the two answer slots. -/
inductive ChoiceRes where
  | call (slot : ℕ)
  | colour (value : Bool)
  | chosen (value : Bool)
  | duplicator
  | answer (slot : ℕ) (value : Bool)
  deriving DecidableEq

/-- Firings for the choice controls. -/
inductive ChoiceSite where
  | answerSlot
  | choose
  | duplicate
  deriving DecidableEq

/-- Instances: a slot and a colour, or a colour. -/
def choiceInstance : ChoiceSite → Type
  | .answerSlot => ℕ × Bool
  | .choose => Bool
  | .duplicate => Bool

/-- Two independent calls, each answered by either colour; or one choice whose
value a duplicator copies into both slots. -/
def choices : System ChoiceRes where
  Site := ChoiceSite
  Instance := choiceInstance
  consume := fun {site} i => match site, i with
    | .answerSlot, (slot, _) => {ChoiceRes.call slot}
    | .choose, _ => {ChoiceRes.call 0}
    | .duplicate, value => {ChoiceRes.chosen value, ChoiceRes.duplicator}
  read := fun {site} i => match site, i with
    | .answerSlot, (_, value) => {ChoiceRes.colour value}
    | .choose, value => {ChoiceRes.colour value}
    | .duplicate, _ => 0
  produce := fun {site} i => match site, i with
    | .answerSlot, (slot, value) => {ChoiceRes.answer slot value}
    | .choose, value => {ChoiceRes.chosen value}
    | .duplicate, value => {ChoiceRes.answer 1 value, ChoiceRes.answer 2 value}

def answerSlot (slot : ℕ) (value : Bool) : choices.Entry := ⟨.answerSlot, (slot, value)⟩
def choose (value : Bool) : choices.Entry := ⟨.choose, value⟩
def duplicate (value : Bool) : choices.Entry := ⟨.duplicate, value⟩

def colours : Multiset ChoiceRes := {ChoiceRes.colour false, ChoiceRes.colour true}

/-- Two calls, each choosing independently. -/
def independentCalls : Multiset ChoiceRes := ChoiceRes.call 1 ::ₘ ChoiceRes.call 2 ::ₘ colours

/-- One call whose chosen value is duplicated. -/
def sharedCall : Multiset ChoiceRes := ChoiceRes.call 0 ::ₘ ChoiceRes.duplicator ::ₘ colours

def independentCatalogue : List choices.Entry :=
  [answerSlot 1 false, answerSlot 1 true, answerSlot 2 false, answerSlot 2 true]

def sharedCatalogue : List choices.Entry :=
  [choose false, choose true, duplicate false, duplicate true]

/-- The mixed outcome: slot 1 false, slot 2 true. -/
def mixed : Multiset ChoiceRes :=
  ChoiceRes.answer 1 false ::ₘ ChoiceRes.answer 2 true ::ₘ colours

/-- **Independent choices reach the mixed outcome.** -/
theorem independent_reaches_mixed :
    mixed ∈ choices.outcomes independentCatalogue 2 independentCalls := by
  decide

/-- **A shared choice never does**: its outcomes are the two diagonal ones. -/
theorem shared_is_diagonal :
    choices.outcomes sharedCatalogue 2 sharedCall =
      [ChoiceRes.answer 1 false ::ₘ ChoiceRes.answer 2 false ::ₘ colours,
       ChoiceRes.answer 1 true ::ₘ ChoiceRes.answer 2 true ::ₘ colours] := by
  decide

theorem shared_misses_mixed : mixed ∉ choices.outcomes sharedCatalogue 2 sharedCall := by
  decide

/-- **Collecting per run counts interleavings.** The two independent answers
reach the mixed outcome in either order, so it is collected twice, although
the two runs are one trace: the firings are concurrent. -/
theorem mixed_collected_twice :
    (choices.outcomes independentCatalogue 2 independentCalls).count mixed = 2 ∧
      choices.Concurrent independentCalls (answerSlot 1 false).2 (answerSlot 2 true).2 := by
  refine ⟨by decide, ?_⟩
  unfold System.Concurrent
  decide

/-- Every colour pair is an outcome, each collected twice: eight runs, four
traces. -/
theorem independent_eight_runs :
    (choices.outcomes independentCatalogue 2 independentCalls).length = 8 := by
  decide

end ExplorationControls

#print axioms System.runs_sound
#print axioms System.runs_complete
#print axioms ExplorationControls.shared_equation_one_run
#print axioms ExplorationControls.twin_equations_two_occurrences
#print axioms ExplorationControls.independent_reaches_mixed
#print axioms ExplorationControls.shared_is_diagonal
#print axioms ExplorationControls.shared_misses_mixed
#print axioms ExplorationControls.mixed_collected_twice

end Mettapedia.GSLT.Causality.ResourceInteraction
