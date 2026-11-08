import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RaceSpectrum

/-!
# Steps and histories: the causal end of the spectrum

Above branching time sit identities that see concurrency itself. This module defines them for the
labelled step of `RaceSpectrum`, for every program.

## Multi-firing steps (`StepMoves`)

A step fires a nonempty finite word of offered firings, **pairwise statically independent**
(`AnnotatedRuns.StaticIndependent`), each admitted where the earlier ones left the configuration. Its
label is the multiset of their labels. The order is immaterial: every permutation of the word is
executable and reaches a configuration with the same solutions and occurrences
(`step_order_irrelevant`), by the step's own swap theorem (`AnnotatedRuns.traceEquiv_executable`).
This is the synchronous rule "Par-2" read in the step.

* **Step bisimilarity** (`StepBisimilar`) is bisimilarity for these moves.
* **Step bisimilarity implies interleaving bisimilarity** (`bisimilar_of_stepBisimilar`): a step of
  one firing is a move (`stepMoves_singleton_iff`).

## Histories (`HMoves`, `HPBisimilar`)

A history is the list of events of a run so far: each event is a firing together with the positions
of its causal past. A firing **depends** on an earlier event when the two are not statically
independent (`directPast`); its causal past is that set closed under the pasts already recorded
(`past`). A history move fires an offered firing and is labelled by its label *and* its causal past.
History-preserving bisimilarity relates two configurations when their empty histories are
bisimilar for history moves: matched events have the same labels and the same causal pasts, so the
labelled causal orders of matched runs coincide position by position.

* **History-preserving bisimilarity implies step bisimilarity** (`stepBisimilar_of_hpBisimilar`):
  a step is a word of independent firings, its events have no causal past among themselves, and a
  matching word with the same pasts is again pairwise independent (`match_word`).
* Hence **history-preserving ⊆ step ⊆ interleaving** (`bisimilar_of_hpBisimilar`). Strictness of both
  inclusions is in `RaceStepControls`.

## Provenance (`staticIndependent_iff_provenance`)

On pure firings (no reads, checks or predicate queries) that take different occurrences and make
different identities, static independence is exactly "neither takes what the other made". Along a run
whose identities are never reused, the earlier firing cannot take what the later one makes, so the
causal order is read off take and make: a firing depends on an earlier one exactly when it takes an
occurrence the earlier one made.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race

open AnnotatedRuns (Firing follow Executable StaticIndependent)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)
open Mettapedia.GSLT (GSLT)
open Mettapedia.GSLT.HennessyMilner (Formula System)
open GuardFreeProcessOrders (SameUpTo)
open Mettapedia.GSLT.Distinction.CausalGluing (TraceEquiv Swap)

universe uT uS uO uL

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O] {L : Type uL}

/-! ## Words of independent firings fire in any order -/

section Order

variable {α : Type*} {R : α → α → Prop}

theorem traceEquiv_cons (x : α) {w w' : List α} (equivalent : TraceEquiv R w w') :
    TraceEquiv R (x :: w) (x :: w') := by
  induction equivalent with
  | rel _ _ swapped =>
      cases swapped with
      | swap u v independent => exact .rel _ _ (Swap.swap (x :: u) v independent)
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ first second => exact .trans _ _ _ first second

/-- **A permutation of a pairwise independent word is a trace-equivalent word.** -/
theorem traceEquiv_of_perm (symm : ∀ a b, R a b → R b a) :
    ∀ {w w' : List α}, w.Perm w' → w.Pairwise R → TraceEquiv R w w' := by
  intro w w' perm
  induction perm with
  | nil => exact fun _ => .refl _
  | cons x _ ih => exact fun pairwise => traceEquiv_cons x (ih (List.pairwise_cons.mp pairwise).2)
  | swap x y l =>
      intro pairwise
      exact .rel _ _ (Swap.swap [] l ((List.pairwise_cons.mp pairwise).1 x (List.mem_cons_self ..)))
  | trans first _ ih₁ ih₂ =>
      intro pairwise
      exact .trans _ _ _ (ih₁ pairwise) (ih₂ (pairwise.perm first fun related => symm _ _ related))

end Order

variable (A : SubstitutionAction T S) (label : O → T)

/-- **The order of a step is immaterial**: a permutation of a pairwise statically independent
executable word is executable, and reaches a configuration with the same solutions and
occurrences. -/
theorem step_order_irrelevant {C : Configuration T O} {w w' : List (Firing T S O)}
    (independent : w.Pairwise (StaticIndependent label)) (perm : w.Perm w')
    (executable : Executable A label C w) :
    Executable A label C w' ∧ SameUpTo A (follow label C w) (follow label C w') :=
  let equivalent := traceEquiv_of_perm (fun _ _ related => related.symm) perm independent
  ⟨(AnnotatedRuns.traceEquiv_executable A label equivalent C).1.mp executable,
    (AnnotatedRuns.traceEquiv_executable A label equivalent C).2 executable⟩

/-- Firing a word: each firing admitted where the earlier ones left the configuration. -/
def Fires : Configuration T O → List (Firing T S O) → Prop
  | _, [] => True
  | C, f :: rest => f.Valid A label C ∧ Fires (f.result label C) rest

theorem executable_of_fires : ∀ {C : Configuration T O} {w : List (Firing T S O)}, w ≠ [] →
    Fires A label C w → Executable A label C w
  | _, [], nonempty, _ => absurd rfl nonempty
  | _, [_], _, ⟨valid, _⟩ => ⟨valid, valid.firing.consistent⟩
  | _, _ :: _ :: _, _, ⟨valid, later⟩ => ⟨valid, executable_of_fires (List.cons_ne_nil _ _) later⟩

theorem fires_of_executable : ∀ {C : Configuration T O} {w : List (Firing T S O)},
    Executable A label C w → Fires A label C w
  | _, [], _ => trivial
  | _, _ :: _, ⟨valid, later⟩ => ⟨valid, fires_of_executable later⟩

/-! ## Multi-firing steps -/

section Steps

variable (offers : L → Firing T S O → Prop)

/-- **A multi-firing step**: a nonempty word of offered firings, pairwise statically independent,
each admitted where the earlier ones left the configuration; its label is the multiset of their
labels. -/
def StepMoves (C : Configuration T O) (M : Multiset L) (D : Configuration T O) : Prop :=
  ∃ w : List (L × Firing T S O), w ≠ [] ∧ (∀ x ∈ w, offers x.1 x.2) ∧
    (w.map Prod.snd).Pairwise (StaticIndependent label) ∧ Executable A label C (w.map Prod.snd) ∧
    M = (↑(w.map Prod.fst) : Multiset L) ∧ D = follow label C (w.map Prod.snd)

/-- The step moves as a Hennessy–Milner system. -/
def stepSystem : System (gslt A label offers) where
  Atom := PEmpty.{1}
  observes atom _ := atom.elim
  observes_resp atom := atom.elim
  Label := Multiset L
  act M C D := StepMoves A label offers C M D
  act_resp_left := by
    intro M C C' D same step
    exact ⟨D, (same : C = C') ▸ step, rfl⟩
  act_resp_right := by
    intro M C D D' step same
    exact (same : D = D') ▸ step

/-- **Step bisimilarity.** -/
def StepBisimilar (C D : Configuration T O) : Prop := (stepSystem A label offers).Bisimilar C D

variable {A label offers}

/-- **A step of one firing is a move.** -/
theorem stepMoves_singleton_iff {C D : Configuration T O} {ℓ : L} :
    StepMoves A label offers C {ℓ} D ↔ Moves A label offers C ℓ D := by
  constructor
  · rintro ⟨w, _, offered, _, executable, labels, rfl⟩
    have length : (w.map Prod.fst).length = 1 := by
      have := congrArg Multiset.card labels
      simpa using this.symm
    rw [List.length_map] at length
    obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp length
    have same : ℓ = x.1 := by
      simpa using labels
    subst same
    exact ⟨x.2, offered x (List.mem_singleton_self _), executable.1, rfl⟩
  · rintro ⟨f, offered, valid, rfl⟩
    refine ⟨[(ℓ, f)], List.cons_ne_nil _ _, ?_, List.pairwise_singleton _ _,
      ⟨valid, valid.firing.consistent⟩, (Multiset.coe_singleton ℓ).symm, rfl⟩
    intro x member
    rw [List.mem_singleton.mp member]
    exact offered

/-- **Step bisimilarity implies interleaving bisimilarity.** -/
theorem bisimilar_of_stepBisimilar {C D : Configuration T O}
    (bisimilar : StepBisimilar A label offers C D) : Bisimilar A label offers C D := by
  obtain ⟨R, ⟨forward, backward, _⟩, related⟩ := bisimilar
  refine ⟨R, ⟨?_, ?_, ?_⟩, related⟩
  · intro C D related ℓ C' moved
    obtain ⟨D', stepped, related'⟩ := forward related ({ℓ} : Multiset L) (stepMoves_singleton_iff.mpr moved)
    exact ⟨D', stepMoves_singleton_iff.mp stepped, related'⟩
  · intro C D related ℓ D' moved
    obtain ⟨C', stepped, related'⟩ := backward related ({ℓ} : Multiset L) (stepMoves_singleton_iff.mpr moved)
    exact ⟨C', stepMoves_singleton_iff.mp stepped, related'⟩
  · intro _ _ _ atom
    exact atom.elim

end Steps

/-! ## Histories -/

section Histories

theorem lt_of_getElem?_eq_some {α : Type*} {h : List α} {e : α} {i : ℕ} (get : h[i]? = some e) :
    i < h.length := by
  obtain ⟨lt, _⟩ := List.getElem?_eq_some_iff.mp get
  exact lt

/-- An event of a run: the firing and the positions of its causal past. -/
abbrev Event (T : Type uT) (S : Type uS) (O : Type uO) := Firing T S O × Finset ℕ

/-- The events of a run so far, in order. -/
abbrev History (T : Type uT) (S : Type uS) (O : Type uO) := List (Event T S O)

/-- **Direct dependence**: the positions of earlier events whose firings are not statically
independent of `f`. -/
noncomputable def directPast (h : History T S O) (f : Firing T S O) : Finset ℕ := by
  classical
  exact (Finset.range h.length).filter fun i => ∃ e, h[i]? = some e ∧ ¬ StaticIndependent label e.1 f

/-- **The causal past of a firing after a history**: its direct dependences, closed under their
recorded pasts. -/
noncomputable def past (h : History T S O) (f : Firing T S O) : Finset ℕ :=
  directPast label h f ∪ (directPast label h f).biUnion fun i => (h[i]?.map Prod.snd).getD ∅

/-- Every recorded past lies before its event. -/
def WF (h : History T S O) : Prop := ∀ i e, h[i]? = some e → e.2 ⊆ Finset.range i

variable {label}

theorem mem_directPast {h : History T S O} {f : Firing T S O} {i : ℕ} :
    i ∈ directPast label h f ↔ i < h.length ∧ ∃ e, h[i]? = some e ∧ ¬ StaticIndependent label e.1 f := by
  classical
  unfold directPast
  rw [Finset.mem_filter, Finset.mem_range]

theorem directPast_subset_past (h : History T S O) (f : Firing T S O) :
    directPast label h f ⊆ past label h f :=
  Finset.subset_union_left

/-- An event outside the causal past of `f` is statically independent of it. -/
theorem independent_of_not_mem_past {h : History T S O} {f : Firing T S O} {i : ℕ}
    {e : Event T S O} (get : h[i]? = some e) (outside : i ∉ past label h f) :
    StaticIndependent label e.1 f := by
  by_contra dependent
  have lt : i < h.length := lt_of_getElem?_eq_some get
  exact outside (directPast_subset_past h f (mem_directPast.mpr ⟨lt, e, get, dependent⟩))

/-- **The causal past avoids every later event independent of `f`**: if every event from position
`n` on is independent of `f`, the past of `f` lies before `n`. -/
theorem past_subset_of_independent {h : History T S O} {f : Firing T S O} {n : ℕ}
    (wf : WF h)
    (fresh : ∀ i e, n ≤ i → h[i]? = some e → StaticIndependent label e.1 f) :
    past label h f ⊆ Finset.range n := by
  have direct : directPast label h f ⊆ Finset.range n := by
    intro i member
    obtain ⟨_, e, get, dependent⟩ := mem_directPast.mp member
    rw [Finset.mem_range]
    by_contra notLt
    exact dependent (fresh i e (Nat.le_of_not_lt notLt) get)
  intro j member
  rcases Finset.mem_union.mp member with inDirect | inClosure
  · exact direct inDirect
  · obtain ⟨i, inDirect, inPast⟩ := Finset.mem_biUnion.mp inClosure
    have iLt : i < n := Finset.mem_range.mp (direct inDirect)
    cases get : h[i]? with
    | none => simp [get] at inPast
    | some e =>
        simp only [get, Option.map_some, Option.getD_some] at inPast
        have := Finset.mem_range.mp (wf i e get inPast)
        exact Finset.mem_range.mpr (by omega)

theorem past_subset_range {h : History T S O} {f : Firing T S O} (wf : WF h) :
    past label h f ⊆ Finset.range h.length :=
  past_subset_of_independent wf fun _ _ le get =>
    absurd (lt_of_getElem?_eq_some get) (Nat.not_lt.mpr le)

theorem getElem?_concat_eq_some {α : Type*} {h : List α} {x e : α} {i : ℕ}
    (get : (h ++ [x])[i]? = some e) : (i < h.length ∧ h[i]? = some e) ∨ (i = h.length ∧ e = x) := by
  rcases Nat.lt_or_ge i h.length with lt | ge
  · exact .inl ⟨lt, by rwa [List.getElem?_append_left lt] at get⟩
  · rw [List.getElem?_append_right ge] at get
    rcases Nat.eq_or_lt_of_le ge with eq | lt
    · subst eq
      simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at get
      exact .inr ⟨rfl, get.symm⟩
    · obtain ⟨k, hk⟩ : ∃ k, i - h.length = k + 1 := ⟨i - h.length - 1, by omega⟩
      rw [hk] at get
      simp at get

omit [DecidableEq O] in
theorem wf_nil : WF ([] : History T S O) := fun _ _ get => by simp at get

omit [DecidableEq O] in
theorem wf_concat {h : History T S O} {f : Firing T S O} {P : Finset ℕ} (wf : WF h)
    (before : P ⊆ Finset.range h.length) : WF (h ++ [(f, P)]) := by
  intro i e get
  rcases getElem?_concat_eq_some get with ⟨_, old⟩ | ⟨rfl, rfl⟩
  · exact wf i e old
  · exact before

variable (label)
variable (offers : L → Firing T S O → Prop)

/-- **A history move**: an offered firing admitted at the configuration, labelled by its label and
its causal past, appended to the history. -/
def HMoves (x : Configuration T O × History T S O) (lab : L × Finset ℕ)
    (y : Configuration T O × History T S O) : Prop :=
  ∃ f, offers lab.1 f ∧ f.Valid A label x.1 ∧ lab.2 = past label x.2 f ∧
    y = (f.result label x.1, x.2 ++ [(f, lab.2)])

/-- Configurations with histories, with discrete equations. -/
def histGslt : GSLT where
  Term := Configuration T O × History T S O
  equations := ⟨Eq, eq_equivalence⟩
  rewrites x y := ∃ lab, HMoves A label offers x lab y
  rewrites_resp_left := by
    intro x x' y same step
    exact ⟨y, (same : x = x') ▸ step, rfl⟩
  rewrites_resp_right := by
    intro x y y' step same
    exact (same : y = y') ▸ step

/-- History moves as a Hennessy–Milner system. -/
def histSystem : System (histGslt A label offers) where
  Atom := PEmpty.{1}
  observes atom _ := atom.elim
  observes_resp atom := atom.elim
  Label := L × Finset ℕ
  act lab x y := HMoves A label offers x lab y
  act_resp_left := by
    intro lab x x' y same step
    exact ⟨y, (same : x = x') ▸ step, rfl⟩
  act_resp_right := by
    intro lab x y y' step same
    exact (same : y = y') ▸ step

/-- **History-preserving bisimilarity**: the empty histories are bisimilar for history moves. -/
def HPBisimilar (C D : Configuration T O) : Prop :=
  (histSystem A label offers).Bisimilar (C, []) (D, [])

variable {A label offers}

/-- **Matching a word of independent firings.** Under a history bisimulation, a word of offered,
pairwise independent firings fired after position `n`, each independent of the events from `n` on,
is matched by a word with the same labels that is pairwise independent and independent of the
other side's events from `n` on, with related ends. -/
theorem match_word {R : Configuration T O × History T S O → Configuration T O × History T S O → Prop}
    (bisimulation : (histSystem A label offers).IsBisimulation R) :
    ∀ (w : List (L × Firing T S O)) (n : ℕ) (C D : Configuration T O) (hC hD : History T S O),
      R (C, hC) (D, hD) → hC.length = hD.length → n ≤ hC.length → WF hC → WF hD →
      (∀ x ∈ w, offers x.1 x.2) → (w.map Prod.snd).Pairwise (StaticIndependent label) →
      (∀ x ∈ w, ∀ i e, n ≤ i → hC[i]? = some e → StaticIndependent label e.1 x.2) →
      Fires A label C (w.map Prod.snd) →
      ∃ v : List (L × Firing T S O), v.map Prod.fst = w.map Prod.fst ∧ (∀ x ∈ v, offers x.1 x.2) ∧
        Fires A label D (v.map Prod.snd) ∧ (v.map Prod.snd).Pairwise (StaticIndependent label) ∧
        (∀ x ∈ v, ∀ i e, n ≤ i → hD[i]? = some e → StaticIndependent label e.1 x.2) ∧
        ∃ hC' hD' : History T S O, R (follow label C (w.map Prod.snd), hC')
          (follow label D (v.map Prod.snd), hD') ∧ hC'.length = hD'.length ∧ WF hC' ∧ WF hD'
  | [], _, _, _, hC, hD, related, length, _, wfC, wfD, _, _, _, _ =>
      ⟨[], rfl, by simp, trivial, List.Pairwise.nil, by simp, hC, hD, related, length, wfC, wfD⟩
  | (ℓ, f) :: rest, n, C, D, hC, hD, related, length, le, wfC, wfD, offered, pairwise, fresh,
      ⟨valid, later⟩ => by
      have head : (ℓ, f) ∈ (ℓ, f) :: rest := List.mem_cons_self ..
      have pastOld : past label hC f ⊆ Finset.range n :=
        past_subset_of_independent wfC (fresh (ℓ, f) head)
      obtain ⟨y, moved, related'⟩ := bisimulation.1 related (ℓ, past label hC f)
        (show HMoves A label offers (C, hC) (ℓ, past label hC f)
          (f.result label C, hC ++ [(f, past label hC f)]) from
          ⟨f, offered (ℓ, f) head, valid, rfl, rfl⟩)
      obtain ⟨g, gOffered, gValid, gPast, rfl⟩ := moved
      have samePast : past label hD g = past label hC f := gPast.symm
      have gFresh : ∀ i e, n ≤ i → hD[i]? = some e → StaticIndependent label e.1 g := by
        intro i e le' get
        refine independent_of_not_mem_past get fun member => ?_
        rw [samePast] at member
        have := Finset.mem_range.mp (pastOld member)
        omega
      have restPairwise := (List.pairwise_cons.mp pairwise).2
      have restFresh : ∀ x ∈ rest, ∀ i e, n ≤ i → (hC ++ [(f, past label hC f)])[i]? = some e →
          StaticIndependent label e.1 x.2 := by
        intro x member i e le' get
        rcases getElem?_concat_eq_some get with ⟨_, old⟩ | ⟨_, rfl⟩
        · exact fresh x (List.mem_cons_of_mem _ member) i e le' old
        · exact (List.pairwise_cons.mp pairwise).1 x.2 (List.mem_map_of_mem member)
      obtain ⟨v, labels, vOffered, vFires, vPairwise, vFresh, hC', hD', related'', length',
          wfC', wfD'⟩ :=
        match_word bisimulation rest n (f.result label C) (g.result label D)
          (hC ++ [(f, past label hC f)]) (hD ++ [(g, past label hC f)]) related'
          (by simp [length]) (by simp only [List.length_append, List.length_singleton]; omega)
          (wf_concat wfC (past_subset_range wfC))
          (wf_concat wfD (samePast ▸ past_subset_range wfD))
          (fun x member => offered x (List.mem_cons_of_mem _ member)) restPairwise restFresh later
      refine ⟨(ℓ, g) :: v, by simp [labels], ?_, ⟨gValid, vFires⟩, ?_, ?_, hC', hD', related'',
        length', wfC', wfD'⟩
      · intro x member
        rcases List.mem_cons.mp member with rfl | member
        · exact gOffered
        · exact vOffered x member
      · refine List.pairwise_cons.mpr ⟨?_, vPairwise⟩
        intro g' member
        obtain ⟨x, xMember, rfl⟩ := List.mem_map.mp member
        exact vFresh x xMember hD.length (g, past label hC f) (by omega)
          (by simp)
      · intro x member i e le' get
        rcases List.mem_cons.mp member with rfl | member
        · exact gFresh i e le' get
        · have lt : i < hD.length := lt_of_getElem?_eq_some get
          exact vFresh x member i e le' (by rw [List.getElem?_append_left lt]; exact get)

theorem isBisimulation_flip {R : Configuration T O × History T S O → Configuration T O × History T S O → Prop}
    (bisimulation : (histSystem A label offers).IsBisimulation R) :
    (histSystem A label offers).IsBisimulation (fun x y => R y x) :=
  ⟨fun _ _ related lab _ moved => bisimulation.2.1 related lab moved,
    fun _ _ related lab _ moved => bisimulation.1 related lab moved,
    fun _ _ _ atom => atom.elim⟩

/-- One direction of the step bisimulation read off a history bisimulation. -/
theorem step_forward {R : Configuration T O × History T S O → Configuration T O × History T S O → Prop}
    (bisimulation : (histSystem A label offers).IsBisimulation R) {C D C' : Configuration T O}
    {M : Multiset L} {hC hD : History T S O} (related : R (C, hC) (D, hD))
    (length : hC.length = hD.length) (wfC : WF hC) (wfD : WF hD)
    (stepped : StepMoves A label offers C M C') :
    ∃ D', StepMoves A label offers D M D' ∧ ∃ hC' hD' : History T S O, R (C', hC') (D', hD') ∧
      hC'.length = hD'.length ∧ WF hC' ∧ WF hD' := by
  obtain ⟨w, nonempty, offered, pairwise, executable, rfl, rfl⟩ := stepped
  obtain ⟨v, labels, vOffered, vFires, vPairwise, _, hC', hD', related', length', wfC', wfD'⟩ :=
    match_word bisimulation w hC.length C D hC hD related length le_rfl wfC wfD offered pairwise
      (fun _ _ i _ le get => absurd (lt_of_getElem?_eq_some get) (by omega))
      (fires_of_executable A label executable)
  have vNonempty : v ≠ [] := by
    intro empty
    rw [empty] at labels
    exact nonempty (List.map_eq_nil_iff.mp labels.symm)
  refine ⟨follow label D (v.map Prod.snd), ⟨v, vNonempty, vOffered, vPairwise,
    executable_of_fires A label (by simpa using vNonempty) vFires, by rw [labels], rfl⟩,
    hC', hD', related', length', wfC', wfD'⟩

/-- **History-preserving bisimilarity implies step bisimilarity.** -/
theorem stepBisimilar_of_hpBisimilar {C D : Configuration T O}
    (bisimilar : HPBisimilar A label offers C D) : StepBisimilar A label offers C D := by
  obtain ⟨R, bisimulation, related⟩ := bisimilar
  refine ⟨fun C D => ∃ hC hD : History T S O, R (C, hC) (D, hD) ∧ hC.length = hD.length ∧
    WF hC ∧ WF hD, ⟨?_, ?_, ?_⟩, ⟨[], [], related, rfl, wf_nil, wf_nil⟩⟩
  · rintro C D ⟨hC, hD, related, length, wfC, wfD⟩ M C' stepped
    exact step_forward bisimulation related length wfC wfD stepped
  · rintro C D ⟨hC, hD, related, length, wfC, wfD⟩ M D' stepped
    obtain ⟨C', back, hD', hC', related', length', wfD', wfC'⟩ :=
      step_forward (isBisimulation_flip bisimulation) related length.symm wfD wfC stepped
    exact ⟨C', back, hC', hD', related', length'.symm, wfC', wfD'⟩
  · intro _ _ _ atom
    exact atom.elim

/-- **History-preserving ⊆ step ⊆ interleaving.** -/
theorem bisimilar_of_hpBisimilar {C D : Configuration T O}
    (bisimilar : HPBisimilar A label offers C D) : Bisimilar A label offers C D :=
  bisimilar_of_stepBisimilar (stepBisimilar_of_hpBisimilar bisimilar)

end Histories

/-! ## Provenance: the causal order read off take and make -/

section Provenance

/-- A pure firing: it takes and makes, and has no reads, checks or predicate queries. -/
structure Pure (f : Firing T S O) : Prop where
  read : f.selection.read = []
  checks : f.rule.checks = []
  queries : f.queries = []

/-- **Static independence is provenance on pure firings.** For pure firings that take different
occurrences and make different identities, static independence holds exactly when neither takes
an identity the other made. -/
theorem staticIndependent_iff_provenance [Nonempty S] {e f : Firing T S O} (pe : Pure e)
    (pf : Pure f) (takes : Disjoint e.selection.taken.toFinset f.selection.taken.toFinset)
    (makes : Disjoint e.selection.made.toFinset f.selection.made.toFinset) :
    StaticIndependent label e f ↔
      Disjoint e.selection.made.toFinset f.selection.taken.toFinset ∧
        Disjoint f.selection.made.toFinset e.selection.taken.toFinset := by
  have eStatic : e.Static :=
    ⟨pe.checks, fun query member => by rw [pe.queries] at member; simp at member⟩
  have fStatic : f.Static :=
    ⟨pf.checks, fun query member => by rw [pf.queries] at member; simp at member⟩
  constructor
  · rintro ⟨_, _, independent⟩
    obtain ⟨σ⟩ := ‹Nonempty S›
    have trace := independent σ
    exact ⟨Finset.disjoint_of_subset_right (fun _ member => Finset.mem_union_left _ member) trace.2.1,
      Finset.disjoint_of_subset_right (fun _ member => Finset.mem_union_left _ member) trace.2.2⟩
  · rintro ⟨first, second⟩
    refine ⟨eStatic, fStatic, fun σ => ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩⟩
    · rintro (clash | clash)
      · exact clash takes
      · exact clash makes
    · rintro (spoil | ⟨query, member, _⟩)
      · apply spoil
        show Disjoint e.selection.taken.toFinset f.selection.read.toFinset
        rw [pf.read, List.toFinset_nil]
        exact Finset.disjoint_empty_right _
      · rw [AnnotatedRuns.Firing.footprintAt_queries, pf.queries] at member
        simp at member
    · rintro (spoil | ⟨query, member, _⟩)
      · apply spoil
        show Disjoint f.selection.taken.toFinset e.selection.read.toFinset
        rw [pe.read, List.toFinset_nil]
        exact Finset.disjoint_empty_right _
      · rw [AnnotatedRuns.Firing.footprintAt_queries, pe.queries] at member
        simp at member
    · show Disjoint e.selection.made.toFinset (f.selection.taken.toFinset ∪ f.selection.read.toFinset)
      rw [pf.read, List.toFinset_nil, Finset.union_empty]
      exact first
    · show Disjoint f.selection.made.toFinset (e.selection.taken.toFinset ∪ e.selection.read.toFinset)
      rw [pe.read, List.toFinset_nil, Finset.union_empty]
      exact second

end Provenance

#print axioms traceEquiv_of_perm
#print axioms step_order_irrelevant
#print axioms executable_of_fires
#print axioms stepMoves_singleton_iff
#print axioms bisimilar_of_stepBisimilar
#print axioms past_subset_of_independent
#print axioms match_word
#print axioms stepBisimilar_of_hpBisimilar
#print axioms bisimilar_of_hpBisimilar
#print axioms staticIndependent_iff_provenance

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race
