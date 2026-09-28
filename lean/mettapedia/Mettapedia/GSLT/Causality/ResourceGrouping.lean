import Mettapedia.GSLT.Causality.ResourceConfluence
import Mathlib.Data.List.Perm.Basic

/-!
# Grouping a search: exchanges, reordering and sleeping firings

Two runs are equivalent when one comes from the other by exchanging adjacent
firings that are concurrent at the bag where they occur. Equivalent runs start
and end in the same bags, so the final bag belongs to the class, while the
order of the firings does not.

An exhaustive search that takes the catalogued instances in another order finds
the same runs, with the same multiplicities, in another order. Its bag of
outcomes is unchanged; its first outcome can change.

A search can skip interleavings. Once a firing has been explored, it sleeps in
each later sibling concurrent with it, and a sleeping firing is not explored
first. This reduced search returns only runs of the full search, and every run
of the full search is equivalent to a run it returns. It finds every outcome.

It need not return each class once. Two firings that contend for a resource
present once are explored as alternatives; when a third firing supplies a
second copy, the two runs that took the copies in opposite orders become
equivalent through the bag holding both copies, and both are returned.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.ResourceInteraction

open Mettapedia.GSLT

universe uRes uRule

namespace System

variable {R : Type uRes} [DecidableEq R] (S : System.{uRes, uRule} R)

/-! ## Exchanging concurrent firings -/

/-- One exchange of two adjacent firings, concurrent at the bag where they
occur. -/
inductive RunSwap : Multiset R → List S.Entry → List S.Entry → Prop
  | here {M : Multiset R} {first second : S.Entry} {rest : List S.Entry} :
      S.Concurrent M first.2 second.2 →
        RunSwap M (first :: second :: rest) (second :: first :: rest)
  | later {M : Multiset R} {entry : S.Entry} {rest rest' : List S.Entry} :
      RunSwap (S.fire M entry.2) rest rest' → RunSwap M (entry :: rest) (entry :: rest')

/-- Runs equivalent up to exchanges of concurrent firings. -/
def RunEquiv (M : Multiset R) : List S.Entry → List S.Entry → Prop :=
  Relation.EqvGen (S.RunSwap M)

theorem runSwap_symm {M : Multiset R} {p q : List S.Entry} (swap : S.RunSwap M p q) :
    S.RunSwap M q p := by
  induction swap with
  | here concurrent => exact .here (S.concurrent_symm concurrent)
  | later _ ih => exact .later ih

theorem perm_of_runSwap {M : Multiset R} {p q : List S.Entry} (swap : S.RunSwap M p q) :
    p.Perm q := by
  induction swap with
  | here _ => exact List.Perm.swap _ _ _
  | later _ ih => exact ih.cons _

theorem perm_of_runEquiv {M : Multiset R} {p q : List S.Entry} (equiv : S.RunEquiv M p q) :
    p.Perm q := by
  induction equiv with
  | rel _ _ swap => exact S.perm_of_runSwap swap
  | refl => exact List.Perm.refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem fires_of_runSwap {M : Multiset R} {p q : List S.Entry} (swap : S.RunSwap M p q) :
    ∀ {N : Multiset R}, S.Fires p M N → S.Fires q M N := by
  induction swap with
  | @here M first second rest concurrent =>
      intro N fires
      obtain ⟨_, _, restFires⟩ := fires
      have square := S.square_of_concurrent concurrent
      refine ⟨square.second, square.firstAfter, ?_⟩
      rw [← square.meet]
      exact restFires
  | later _ ih =>
      intro N fires
      exact ⟨fires.1, ih fires.2⟩

/-- **Equivalent runs are runs between the same bags.** -/
theorem fires_iff_of_runEquiv {M : Multiset R} {p q : List S.Entry}
    (equiv : S.RunEquiv M p q) {N : Multiset R} : S.Fires p M N ↔ S.Fires q M N := by
  induction equiv generalizing N with
  | rel _ _ swap =>
      exact ⟨S.fires_of_runSwap swap, S.fires_of_runSwap (S.runSwap_symm swap)⟩
  | refl => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem runEquiv_cons {M : Multiset R} (entry : S.Entry) {p q : List S.Entry}
    (equiv : S.RunEquiv (S.fire M entry.2) p q) : S.RunEquiv M (entry :: p) (entry :: q) := by
  induction equiv with
  | rel _ _ swap => exact .rel _ _ (.later swap)
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

/-- A run reaches one bag. -/
theorem fires_functional : ∀ (path : List S.Entry) {M N N' : Multiset R},
    S.Fires path M N → S.Fires path M N' → N = N'
  | [], _, _, _, first, second => by
      change _ = _ at first
      change _ = _ at second
      rw [first, second]
  | _ :: rest, _, _, _, first, second => fires_functional rest first.2 second.2

/-- **The final bag belongs to the class of a run.** -/
theorem final_eq_of_runEquiv {M N N' : Multiset R} {p q : List S.Entry}
    (equiv : S.RunEquiv M p q) (first : S.Fires p M N) (second : S.Fires q M N') : N = N' :=
  S.fires_functional q ((S.fires_iff_of_runEquiv equiv).mp first) second

/-! ## Reordering the catalogue -/

theorem enabledAt_perm {catalogue catalogue' : List S.Entry} (perm : catalogue.Perm catalogue')
    (M : Multiset R) : (S.enabledAt catalogue M).Perm (S.enabledAt catalogue' M) :=
  perm.filter _

private theorem isEmpty_eq_of_perm {α : Type _} {l l' : List α} (perm : l.Perm l') :
    l.isEmpty = l'.isEmpty := by
  cases l with
  | nil => rw [List.nil_perm.mp perm]
  | cons a l =>
      cases l' with
      | nil => exact absurd (List.perm_nil.mp perm) (List.cons_ne_nil a l)
      | cons b l' => rfl

/-- **Reordering the catalogue permutes the runs**, keeping every run and its
multiplicity. -/
theorem runs_perm {catalogue catalogue' : List S.Entry} (perm : catalogue.Perm catalogue') :
    ∀ (fuel : ℕ) (M : Multiset R),
      (S.runs catalogue fuel M).Perm (S.runs catalogue' fuel M)
  | 0, M => by
      unfold runs
      rw [isEmpty_eq_of_perm (S.enabledAt_perm perm M)]
  | fuel + 1, M => by
      unfold runs
      rw [isEmpty_eq_of_perm (S.enabledAt_perm perm M)]
      split
      · exact List.Perm.refl _
      · exact (S.enabledAt_perm perm M).flatMap fun entry _ =>
          (runs_perm perm fuel (S.fire M entry.2)).map _

/-- **Reordering the catalogue keeps the bag of outcomes.** -/
theorem outcomes_perm {catalogue catalogue' : List S.Entry} (perm : catalogue.Perm catalogue')
    (fuel : ℕ) (M : Multiset R) :
    (S.outcomes catalogue fuel M).Perm (S.outcomes catalogue' fuel M) :=
  (S.runs_perm perm fuel M).map _

/-- A returned run fits in the fuel. -/
theorem runs_length (catalogue : List S.Entry) : ∀ (fuel : ℕ) (M : Multiset R)
    (run : List S.Entry × Multiset R), run ∈ S.runs catalogue fuel M → run.1.length ≤ fuel
  | 0, M, run, member => by
      unfold runs at member
      split at member
      · simp only [List.mem_singleton] at member
        subst member
        simp
      · simp at member
  | fuel + 1, M, run, member => by
      unfold runs at member
      split at member
      · simp only [List.mem_singleton] at member
        subst member
        simp
      · obtain ⟨entry, _, member⟩ := List.mem_flatMap.mp member
        obtain ⟨tail, tailMember, rfl⟩ := List.mem_map.mp member
        have := runs_length catalogue fuel _ tail tailMember
        simp only [List.length_cons]
        omega

/-! ## The reduced search -/

variable [DecidableEq S.Entry] (catalogue : List S.Entry)

/-- Concurrency of two entries, as a computation. -/
def concurrentB (M : Multiset R) (first second : S.Entry) : Bool :=
  decide (S.consume first.2 + S.consume second.2 + S.read first.2 ≤ M) &&
    decide (S.consume first.2 + S.consume second.2 + S.read second.2 ≤ M)

omit [DecidableEq S.Entry] in
theorem concurrentB_iff (M : Multiset R) (first second : S.Entry) :
    S.concurrentB M first second = true ↔ S.Concurrent M first.2 second.2 := by
  simp [concurrentB, Concurrent]

/-- The siblings of a node: each enabled entry not asleep is explored, with the
sleeping entries and the explored earlier siblings that are concurrent with it
asleep in its subtree. -/
def siblings (child : Multiset R → List S.Entry → List (List S.Entry × Multiset R))
    (M : Multiset R) (sleep : List S.Entry) :
    List S.Entry → List S.Entry → List (List S.Entry × Multiset R)
  | _, [] => []
  | done, entry :: later =>
      if entry ∈ sleep then siblings child M sleep done later
      else ((child (S.fire M entry.2)
          ((sleep ++ done).filter fun z => S.concurrentB M z entry)).map
            fun run => (entry :: run.1, run.2)) ++
        siblings child M sleep (done ++ [entry]) later

/-- The reduced search from a bag with a sleep set. -/
def reduced : ℕ → Multiset R → List S.Entry → List (List S.Entry × Multiset R)
  | 0, M, _ => if (S.enabledAt catalogue M).isEmpty then [([], M)] else []
  | fuel + 1, M, sleep =>
      if (S.enabledAt catalogue M).isEmpty then [([], M)]
      else S.siblings (reduced fuel) M sleep [] (S.enabledAt catalogue M)

theorem mem_siblings {child : Multiset R → List S.Entry → List (List S.Entry × Multiset R)}
    {M : Multiset R} {sleep : List S.Entry} :
    ∀ (done later : List S.Entry) (run : List S.Entry × Multiset R),
      run ∈ S.siblings child M sleep done later →
        ∃ entry ∈ later, ∃ z tail, tail ∈ child (S.fire M entry.2) z ∧
          run = (entry :: tail.1, tail.2)
  | _, [], _, member => by simp [siblings] at member
  | done, entry :: later, run, member => by
      unfold siblings at member
      split at member
      · obtain ⟨found, foundMember, rest⟩ := mem_siblings done later run member
        exact ⟨found, List.mem_cons_of_mem _ foundMember, rest⟩
      · rcases List.mem_append.mp member with here | there
        · obtain ⟨tail, tailMember, rfl⟩ := List.mem_map.mp here
          exact ⟨entry, List.mem_cons_self, _, tail, tailMember, rfl⟩
        · obtain ⟨found, foundMember, rest⟩ := mem_siblings (done ++ [entry]) later run there
          exact ⟨found, List.mem_cons_of_mem _ foundMember, rest⟩

/-- **The reduced search returns runs of the full search.** -/
theorem reduced_sub_runs : ∀ (fuel : ℕ) (M : Multiset R) (sleep : List S.Entry)
    (run : List S.Entry × Multiset R), run ∈ S.reduced catalogue fuel M sleep →
      run ∈ S.runs catalogue fuel M
  | 0, M, _, run, member => by
      unfold reduced at member
      unfold runs
      exact member
  | fuel + 1, M, sleep, run, member => by
      unfold reduced at member
      unfold runs
      split
      · next empty => rw [if_pos empty] at member; exact member
      · next nonempty =>
          rw [if_neg nonempty] at member
          obtain ⟨entry, enabled, z, tail, tailMember, rfl⟩ :=
            S.mem_siblings [] _ run member
          exact List.mem_flatMap.mpr ⟨entry, enabled,
            List.mem_map.mpr ⟨tail, reduced_sub_runs fuel _ z tail tailMember, rfl⟩⟩

/-- An entry that some exchange of the run brings to the front. -/
def FreeFirst (M : Multiset R) (entry : S.Entry) (path : List S.Entry) : Prop :=
  ∃ rest, S.RunEquiv M path (entry :: rest)

/-- The search over the siblings of a node finds a run equivalent to a given
maximal run, provided some sibling can come first in it, and no sleeping or
earlier sibling can. -/
theorem siblings_complete (fuel : ℕ) (M : Multiset R) (sleep : List S.Entry)
    (childComplete : ∀ (M' : Multiset R) (sleep' : List S.Entry) (path : List S.Entry)
      (N : Multiset R), path.length ≤ fuel → (∀ entry ∈ path, entry ∈ catalogue) →
      S.Fires path M' N → S.enabledAt catalogue N = [] →
      (∀ z ∈ sleep', S.Enables M' z.2) → (∀ z ∈ sleep', ¬ S.FreeFirst M' z path) →
      ∃ run ∈ S.reduced catalogue fuel M' sleep', S.RunEquiv M' run.1 path ∧ run.2 = N)
    (path : List S.Entry) (N : Multiset R) (length : path.length ≤ fuel + 1)
    (catalogued : ∀ entry ∈ path, entry ∈ catalogue) (fires : S.Fires path M N)
    (terminal : S.enabledAt catalogue N = []) :
    ∀ (done later : List S.Entry), (∀ z ∈ sleep ++ done, S.Enables M z.2) →
      (∀ z ∈ sleep ++ done, ¬ S.FreeFirst M z path) → (∀ entry ∈ later, S.Enables M entry.2) →
      (∃ entry ∈ later, S.FreeFirst M entry path) →
      ∃ run ∈ S.siblings (S.reduced catalogue fuel) M sleep done later,
        S.RunEquiv M run.1 path ∧ run.2 = N
  | _, [], _, _, _, witness => by
      obtain ⟨_, impossible, _⟩ := witness
      cases impossible
  | done, entry :: later, enabledSleep, notFree, enabledLater, witness => by
      unfold siblings
      by_cases asleep : entry ∈ sleep
      · rw [if_pos asleep]
        refine siblings_complete fuel M sleep childComplete path N length catalogued fires
          terminal done later enabledSleep notFree
          (fun other member => enabledLater other (List.mem_cons_of_mem _ member)) ?_
        obtain ⟨found, foundMember, foundFree⟩ := witness
        rcases List.mem_cons.mp foundMember with rfl | later'
        · exact absurd foundFree (notFree found (List.mem_append_left _ asleep))
        · exact ⟨found, later', foundFree⟩
      · rw [if_neg asleep]
        by_cases free : S.FreeFirst M entry path
        · obtain ⟨rest, equiv⟩ := free
          have restFires : S.Fires rest (S.fire M entry.2) N :=
            ((S.fires_iff_of_runEquiv equiv).mp fires).2
          have perm := S.perm_of_runEquiv equiv
          have restLength : rest.length ≤ fuel := by
            have := perm.length_eq
            simp only [List.length_cons] at this
            omega
          have restCatalogued : ∀ other ∈ rest, other ∈ catalogue := fun other member =>
            catalogued other (perm.symm.subset (List.mem_cons_of_mem _ member))
          obtain ⟨run, runMember, runEquiv, runFinal⟩ :=
            childComplete (S.fire M entry.2)
              ((sleep ++ done).filter fun z => S.concurrentB M z entry) rest N restLength
              restCatalogued restFires terminal
              (by
                intro z member
                obtain ⟨inSleep, concurrent⟩ := List.mem_filter.mp member
                exact S.enables_fire (S.concurrent_symm ((S.concurrentB_iff M z entry).mp concurrent)))
              (by
                intro z member zFree
                obtain ⟨inSleep, concurrent⟩ := List.mem_filter.mp member
                obtain ⟨rest', restEquiv⟩ := zFree
                apply notFree z inSleep
                refine ⟨entry :: rest', ?_⟩
                exact .trans _ _ _ equiv (.trans _ _ _ (S.runEquiv_cons entry restEquiv)
                  (.rel _ _ (.here (S.concurrent_symm
                    ((S.concurrentB_iff M z entry).mp concurrent))))))
          refine ⟨(entry :: run.1, run.2), List.mem_append_left _ (List.mem_map.mpr ⟨run, runMember, rfl⟩),
            ?_, runFinal⟩
          exact .trans _ _ _ (S.runEquiv_cons entry runEquiv) (.symm _ _ equiv)
        · obtain ⟨run, runMember, runEquiv, runFinal⟩ :=
            siblings_complete fuel M sleep childComplete path N length catalogued fires terminal
              (done ++ [entry]) later
              (by
                intro z member
                rcases List.mem_append.mp member with inSleep | inDone
                · exact enabledSleep z (List.mem_append_left _ inSleep)
                · rcases List.mem_append.mp inDone with inDone | isEntry
                  · exact enabledSleep z (List.mem_append_right _ inDone)
                  · rw [List.mem_singleton.mp isEntry]
                    exact enabledLater entry List.mem_cons_self)
              (by
                intro z member
                rcases List.mem_append.mp member with inSleep | inDone
                · exact notFree z (List.mem_append_left _ inSleep)
                · rcases List.mem_append.mp inDone with inDone | isEntry
                  · exact notFree z (List.mem_append_right _ inDone)
                  · rw [List.mem_singleton.mp isEntry]
                    exact free)
              (fun other member => enabledLater other (List.mem_cons_of_mem _ member))
              (by
                obtain ⟨found, foundMember, foundFree⟩ := witness
                rcases List.mem_cons.mp foundMember with rfl | later'
                · exact absurd foundFree free
                · exact ⟨found, later', foundFree⟩)
          exact ⟨run, List.mem_append_right _ runMember, runEquiv, runFinal⟩

/-- **Every maximal run is equivalent to a run of the reduced search**, when no
sleeping entry can come first in it. -/
theorem reduced_complete : ∀ (fuel : ℕ) (M : Multiset R) (sleep : List S.Entry)
    (path : List S.Entry) (N : Multiset R), path.length ≤ fuel →
    (∀ entry ∈ path, entry ∈ catalogue) → S.Fires path M N → S.enabledAt catalogue N = [] →
    (∀ z ∈ sleep, S.Enables M z.2) → (∀ z ∈ sleep, ¬ S.FreeFirst M z path) →
      ∃ run ∈ S.reduced catalogue fuel M sleep, S.RunEquiv M run.1 path ∧ run.2 = N
  | fuel, M, sleep, [], N, _, _, fires, terminal, _, _ => by
      change N = M at fires
      subst fires
      refine ⟨([], N), ?_, .refl _, rfl⟩
      cases fuel with
      | zero => simp [reduced, terminal]
      | succ fuel => simp [reduced, terminal]
  | 0, _, _, _ :: _, _, length, _, _, _, _, _ => by simp at length
  | fuel + 1, M, sleep, first :: rest, N, length, catalogued, fires, terminal, enabledSleep,
      notFree => by
      have firstEnabled : first ∈ S.enabledAt catalogue M :=
        List.mem_filter.mpr ⟨catalogued first List.mem_cons_self,
          (S.enabledB_iff M first).mpr fires.1⟩
      have nonempty : (S.enabledAt catalogue M).isEmpty = false := by
        cases h : S.enabledAt catalogue M with
        | nil => rw [h] at firstEnabled; cases firstEnabled
        | cons _ _ => rfl
      unfold reduced
      rw [if_neg (by simp [nonempty])]
      exact S.siblings_complete catalogue fuel M sleep
        (fun M' sleep' path N' => reduced_complete fuel M' sleep' path N')
        (first :: rest) N length catalogued fires terminal [] (S.enabledAt catalogue M)
        (by simpa using enabledSleep) (by simpa using notFree)
        (fun entry member => (S.enabledB_iff M entry).mp (List.mem_filter.mp member).2)
        ⟨first, firstEnabled, rest, .refl _⟩

/-- **The reduced search finds every outcome of the full search.** -/
theorem mem_reduced_outcomes_iff (fuel : ℕ) (M N : Multiset R) :
    N ∈ (S.reduced catalogue fuel M []).map Prod.snd ↔ N ∈ S.outcomes catalogue fuel M := by
  constructor
  · intro member
    obtain ⟨run, runMember, rfl⟩ := List.mem_map.mp member
    exact List.mem_map.mpr ⟨run, S.reduced_sub_runs catalogue fuel M [] run runMember, rfl⟩
  · intro member
    obtain ⟨run, runMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨fires, terminal⟩ := S.runs_sound catalogue fuel M run runMember
    have length := S.runs_length catalogue fuel M run runMember
    obtain ⟨found, foundMember, _, final⟩ := S.reduced_complete catalogue fuel M [] run.1 run.2
      length (S.runs_catalogued catalogue fuel M run runMember) fires terminal
      (by simp) (by simp)
    exact List.mem_map.mpr ⟨found, foundMember, final⟩

end System

/-! ## Controls -/

namespace ExplorationControls

open Controls

instance (site : ChoiceSite) : DecidableEq (choiceInstance site) := by
  cases site <;> (unfold choiceInstance; infer_instance)

instance : DecidableEq choices.Entry :=
  inferInstanceAs (DecidableEq (Σ site : ChoiceSite, choiceInstance site))

/-- **Four traces, four reduced runs.** The full search of two independent
choices finds eight runs; the reduced search one per class of exchanges. -/
theorem independent_four_reduced_runs :
    (choices.reduced independentCatalogue 2 independentCalls []).length = 4 ∧
      (choices.outcomes independentCatalogue 2 independentCalls).length = 8 := by
  decide

/-- The reduced search and the full search find the same outcomes. -/
theorem independent_reduced_outcomes :
    (choices.reduced independentCatalogue 2 independentCalls []).map Prod.snd =
      [ChoiceRes.answer 1 false ::ₘ ChoiceRes.answer 2 false ::ₘ colours,
       ChoiceRes.answer 1 false ::ₘ ChoiceRes.answer 2 true ::ₘ colours,
       ChoiceRes.answer 1 true ::ₘ ChoiceRes.answer 2 false ::ₘ colours,
       ChoiceRes.answer 1 true ::ₘ ChoiceRes.answer 2 true ::ₘ colours] := by
  decide

/-- **Reordering changes the first outcome and keeps the bag.** A retraction
catalogued first makes the stranded call the first outcome. -/
theorem reordering_changes_first_outcome :
    (editableSpace.outcomes [answerEntry 1, retractEntry 1] 2 pendingRetraction).head? =
        some {EditRes.answer 1} ∧
      (editableSpace.outcomes [retractEntry 1, answerEntry 1] 2 pendingRetraction).head? =
        some {EditRes.call} := by
  decide

/-- Two kinds of resource: a contested one, and fuel for a second copy. -/
inductive SupplyRes where
  | contested
  | fuel
  deriving DecidableEq

/-- Takers `0` and `1` consume the contested resource; instance `2` turns fuel
into a second copy of it. -/
def supply : System SupplyRes where
  Site := Unit
  Instance := fun _ => ℕ
  consume := fun index => match index with
    | 2 => {SupplyRes.fuel}
    | _ => {SupplyRes.contested}
  read := fun _ => 0
  produce := fun index => match index with
    | 2 => {SupplyRes.contested}
    | _ => 0

instance : DecidableEq supply.Entry := inferInstanceAs (DecidableEq (Σ _ : Unit, ℕ))

def supplyEntry (index : ℕ) : supply.Entry := ⟨(), index⟩

def supplyCatalogue : List supply.Entry := [supplyEntry 0, supplyEntry 1, supplyEntry 2]

/-- One copy of the contested resource, and fuel for another. -/
def oneCopy : Multiset SupplyRes := {SupplyRes.fuel, SupplyRes.contested}

/-- The reduced search returns four runs. -/
theorem supply_reduced_runs :
    (supply.reduced supplyCatalogue 4 oneCopy []).map Prod.fst =
      [[supplyEntry 0, supplyEntry 2, supplyEntry 0], [supplyEntry 0, supplyEntry 2, supplyEntry 1],
       [supplyEntry 1, supplyEntry 2, supplyEntry 0], [supplyEntry 1, supplyEntry 2, supplyEntry 1]] := by
  decide

/-- The two takers exchange places through the bag holding both copies. -/
theorem supply_detour :
    supply.RunEquiv oneCopy [supplyEntry 0, supplyEntry 2, supplyEntry 1]
      [supplyEntry 1, supplyEntry 2, supplyEntry 0] := by
  have first : supply.Concurrent oneCopy (supplyEntry 0).2 (supplyEntry 2).2 := by
    unfold System.Concurrent; decide
  have middle : supply.Concurrent (supply.fire oneCopy (supplyEntry 2).2)
      (supplyEntry 0).2 (supplyEntry 1).2 := by
    unfold System.Concurrent System.fire; decide
  have last : supply.Concurrent oneCopy (supplyEntry 2).2 (supplyEntry 1).2 := by
    unfold System.Concurrent; decide
  exact .trans _ _ _ (.rel _ _ (.here first))
    (.trans _ _ _ (.rel _ _ (.later (.here middle))) (.rel _ _ (.here last)))

/-- **The reduced search can return one class twice.** -/
theorem reduced_repeats_a_class :
    ∃ first ∈ supply.reduced supplyCatalogue 4 oneCopy [],
      ∃ second ∈ supply.reduced supplyCatalogue 4 oneCopy [],
        first.1 ≠ second.1 ∧ supply.RunEquiv oneCopy first.1 second.1 := by
  have runs := supply_reduced_runs
  have firstMember : [supplyEntry 0, supplyEntry 2, supplyEntry 1] ∈
      (supply.reduced supplyCatalogue 4 oneCopy []).map Prod.fst := by
    rw [runs]; simp
  have secondMember : [supplyEntry 1, supplyEntry 2, supplyEntry 0] ∈
      (supply.reduced supplyCatalogue 4 oneCopy []).map Prod.fst := by
    rw [runs]; simp
  obtain ⟨first, firstIn, firstPath⟩ := List.mem_map.mp firstMember
  obtain ⟨second, secondIn, secondPath⟩ := List.mem_map.mp secondMember
  refine ⟨first, firstIn, second, secondIn, ?_, ?_⟩
  · rw [firstPath, secondPath]
    decide
  · rw [firstPath, secondPath]
    exact supply_detour

end ExplorationControls

#print axioms System.fires_iff_of_runEquiv
#print axioms System.final_eq_of_runEquiv
#print axioms System.runs_perm
#print axioms System.outcomes_perm
#print axioms System.reduced_sub_runs
#print axioms System.reduced_complete
#print axioms System.mem_reduced_outcomes_iff
#print axioms ExplorationControls.independent_four_reduced_runs
#print axioms ExplorationControls.independent_reduced_outcomes
#print axioms ExplorationControls.reordering_changes_first_outcome
#print axioms ExplorationControls.supply_reduced_runs
#print axioms ExplorationControls.reduced_repeats_a_class

end Mettapedia.GSLT.Causality.ResourceInteraction
