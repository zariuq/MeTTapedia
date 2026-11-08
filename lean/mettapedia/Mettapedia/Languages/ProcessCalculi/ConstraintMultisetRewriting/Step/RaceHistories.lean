import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RaceRecords

/-!
# Records that carry makes: history-preserving identity from records

The choice escape records what each firing took (`RaceCommit.choiceEscape_records`), so its records
are blind to causality (`RaceRecords.records_blind_to_causality`). Here each firing's record also
holds what it made.

## The extended record (`Entry`)

An entry holds references to the occurrences a firing took and to those it made (`Entry.ofFiring`).
Read by the observer, it is the choice escape's record followed by held references to what was made
(`Entry.references_ofFiring`), and it is equivariant (`Entry.references_rename`).

## The record-extended step (`RMoves`, `RecordBisimilar`)

A state carries the extended record: the entries so far, each with its causal past read off the
record. A firing's **provenance past** is the set of earlier entries that made something it takes
(`provDirect`), closed under their recorded pasts (`provPast`). A move fires an offered firing and is
labelled by its label and its provenance past. Bisimilarity of this step from empty records is
`RecordBisimilar`.

## History-preserving identity from records

A program is **pure** when its offered firings take and make only (`PureProgram`). A start is
**reuse-free** when, along every run from it, no admitted firing makes an identity that an earlier
firing of the run took (`ReuseFree`). Along such runs every earlier take is gone and every earlier
make is present or taken (`Accounted`), so static dependence on an earlier firing is exactly taking
something it made (`staticIndependent_iff_made_taken`), and the causal past of history-preserving
bisimulation is the provenance past (`past_eq_provPast`).

* **History-preserving bisimilarity is bisimilarity of the record-extended step**
  (`hpBisimilar_iff_recordBisimilar`), on pure programs from reuse-free starts.
* **The extended record determines the causal order** (`toRecord_eq_annotate`): the recorded pasts
  are the annotation of the entries alone (`annotate`).
* **The matchings of history-preserving bisimulations are isomorphisms of the causal orders read
  off the extended records** (`matching_causal_eq`): along the rounds of the bisimulation game, the
  two records have the same causal pasts, position by position.

They are not isomorphisms of the records themselves: a matched pair can differ in which earlier
entry a firing took from, as long as the transitive closure agrees. That control, and two runs that
the choice escape identifies and the extended record separates, are in `RaceHistoriesControls`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race

open AnnotatedRuns (Firing StaticIndependent)
open Mettapedia.GSLT (GSLT)
open Mettapedia.GSLT.HennessyMilner (System)
open Observation (Record)

universe uT uS uO uL

/-- **What the extended record holds of one firing**: references to the occurrences it took and to
those it made. -/
structure Entry (O : Type uO) where
  taken : List O
  made : List O

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O] {L : Type uL}

namespace Entry

/-- The entry of a firing. -/
def ofFiring (f : Firing T S O) : Entry O := ⟨f.selection.taken, f.selection.made⟩

/-- Rename the identities an entry refers to. -/
def rename (π : O ≃ O) (e : Entry O) : Entry O := ⟨e.taken.map π, e.made.map π⟩

/-- **The entry as the observer reads it**: held references to what was taken, then to what was
made. -/
def references (e : Entry O) : Record O := Record.references e.taken ++ Record.references e.made

omit [DecidableEq O] in
theorem ofFiring_rename (π : O ≃ O) (f : Firing T S O) :
    ofFiring (f.rename π) = (ofFiring f).rename π := rfl

/-- **The extension of the choice escape**: for a firing without predicate queries, the observer's
reading of its entry is what the choice escape records, followed by references to what it made. -/
theorem references_ofFiring (A : SubstitutionAction T S) (label : O → T) {C : Configuration T O}
    {f : Firing T S O} (noQueries : f.queries = []) :
    (ofFiring f).references =
      (AnnotatedRuns.choiceEscape A label).records (s := C) f ++ Record.references f.selection.made := by
  rw [choiceEscape_records A label noQueries]
  rfl

omit [DecidableEq O] in
/-- **The extension is equivariant.** -/
theorem references_rename (π : O ≃ O) (e : Entry O) :
    (e.rename π).references = Record.rename π e.references := by
  simp only [references, rename, Record.rename_append, Observation.Record.references_rename]

end Entry

/-- **An extended record**: the entries so far, each with its causal past read off the record. -/
abbrev ExtRecord (O : Type uO) := List (Entry O × Finset ℕ)

/-- **Direct provenance**: the positions of earlier entries that made something the entry takes. -/
noncomputable def provDirect (rec : ExtRecord O) (e : Entry O) : Finset ℕ := by
  classical
  exact (Finset.range rec.length).filter fun i =>
    ∃ x, rec[i]? = some x ∧ ¬ Disjoint x.1.made.toFinset e.taken.toFinset

/-- **The provenance past**: direct provenance, closed under the recorded pasts. -/
noncomputable def provPast (rec : ExtRecord O) (e : Entry O) : Finset ℕ :=
  provDirect rec e ∪ (provDirect rec e).biUnion fun i => (rec[i]?.map Prod.snd).getD ∅

theorem mem_provDirect {rec : ExtRecord O} {e : Entry O} {i : ℕ} :
    i ∈ provDirect rec e ↔
      i < rec.length ∧ ∃ x, rec[i]? = some x ∧ ¬ Disjoint x.1.made.toFinset e.taken.toFinset := by
  classical
  unfold provDirect
  rw [Finset.mem_filter, Finset.mem_range]

/-! ## The record-extended step -/

section RecordStep

variable (A : SubstitutionAction T S) (label : O → T) (offers : L → Firing T S O → Prop)

/-- **A move of the record-extended step**: an offered firing admitted at the configuration,
labelled by its label and its provenance past, its entry appended to the record. -/
def RMoves (x : Configuration T O × ExtRecord O) (lab : L × Finset ℕ)
    (y : Configuration T O × ExtRecord O) : Prop :=
  ∃ f, offers lab.1 f ∧ f.Valid A label x.1 ∧ lab.2 = provPast x.2 (Entry.ofFiring f) ∧
    y = (f.result label x.1, x.2 ++ [(Entry.ofFiring f, lab.2)])

/-- Configurations with extended records, with discrete equations. -/
def recordGslt : GSLT where
  Term := Configuration T O × ExtRecord O
  equations := ⟨Eq, eq_equivalence⟩
  rewrites x y := ∃ lab, RMoves A label offers x lab y
  rewrites_resp_left := by
    intro x x' y same step
    exact ⟨y, (same : x = x') ▸ step, rfl⟩
  rewrites_resp_right := by
    intro x y y' step same
    exact (same : y = y') ▸ step

/-- The record-extended step as a Hennessy–Milner system. -/
def recordSystem : System (recordGslt A label offers) where
  Atom := PEmpty.{1}
  observes atom _ := atom.elim
  observes_resp atom := atom.elim
  Label := L × Finset ℕ
  act lab x y := RMoves A label offers x lab y
  act_resp_left := by
    intro lab x x' y same step
    exact ⟨y, (same : x = x') ▸ step, rfl⟩
  act_resp_right := by
    intro lab x y y' step same
    exact (same : y = y') ▸ step

/-- **Bisimilarity of the record-extended step**, from empty records. -/
def RecordBisimilar (C D : Configuration T O) : Prop :=
  (recordSystem A label offers).Bisimilar (C, []) (D, [])

/-- A history move, under some label. -/
def HStep (x y : Configuration T O × History T S O) : Prop := ∃ lab, HMoves A label offers x lab y

/-- The states a run from `C` reaches, with their histories. -/
def HReach (C : Configuration T O) (x : Configuration T O × History T S O) : Prop :=
  Relation.ReflTransGen (HStep A label offers) (C, []) x

/-- **No reuse at a state**: every offered firing admitted there makes nothing that an earlier firing
of the history took. -/
def FreshAt (x : Configuration T O × History T S O) : Prop :=
  ∀ ℓ f, offers ℓ f → f.Valid A label x.1 →
    ∀ e ∈ x.2, ∀ o ∈ f.selection.made, o ∉ e.1.selection.taken

/-- **A reuse-free start**: along every run from it, no admitted firing makes an identity that an
earlier firing of the run took. -/
def ReuseFree (C : Configuration T O) : Prop :=
  ∀ x, HReach A label offers C x → FreshAt A label offers x

/-- **A pure program**: its offered firings take and make only. -/
def PureProgram : Prop := ∀ ℓ f, offers ℓ f → Pure f

end RecordStep

/-! ## Accounting along reuse-free runs -/

section Accounting

/-- **An accounted state**: its events are pure, what they took is gone, and what they made is
present or was taken later. -/
structure Accounted (x : Configuration T O × History T S O) : Prop where
  pure : ∀ e ∈ x.2, Pure e.1
  gone : ∀ e ∈ x.2, ∀ o ∈ e.1.selection.taken, o ∉ x.1.present
  kept : ∀ e ∈ x.2, ∀ o ∈ e.1.selection.made,
    o ∈ x.1.present ∨ ∃ e' ∈ x.2, o ∈ e'.1.selection.taken

variable {A : SubstitutionAction T S} {label : O → T} {offers : L → Firing T S O → Prop}

omit [DecidableEq O] in
theorem accounted_nil (C : Configuration T O) : Accounted ((C, []) : Configuration T O × History T S O) :=
  ⟨fun _ member => (List.not_mem_nil member).elim, fun _ member => (List.not_mem_nil member).elim,
    fun _ member => (List.not_mem_nil member).elim⟩

/-- **Accounting is kept by moves that reuse nothing.** -/
theorem accounted_step (pure : PureProgram offers) {x y : Configuration T O × History T S O}
    (accounted : Accounted x) (fresh : FreshAt A label offers x) {lab : L × Finset ℕ}
    (moved : HMoves A label offers x lab y) : Accounted y := by
  obtain ⟨f, offered, valid, _, rfl⟩ := moved
  have enabled := valid.firing.occurrences
  refine ⟨?_, ?_, ?_⟩
  · intro e member
    rcases List.mem_append.mp member with old | new
    · exact accounted.pure e old
    · obtain rfl := List.mem_singleton.mp new
      exact pure _ _ offered
  · intro e member o taken present
    have present' : o ∈ MeTTaCalculus.OccurrenceCommits.fire x.1.present
        (f.selection.commit (T := T)) := present
    rcases MeTTaCalculus.OccurrenceCommits.mem_fire.mp present' with ⟨before, notTaken⟩ | made
    · rcases List.mem_append.mp member with old | new
      · exact accounted.gone e old o taken before
      · obtain rfl := List.mem_singleton.mp new
        exact notTaken (List.mem_toFinset.mpr taken)
    · have made' : o ∈ f.selection.made.toFinset := made
      rcases List.mem_append.mp member with old | new
      · exact fresh lab.1 f offered valid e old o (List.mem_toFinset.mp made') taken
      · obtain rfl := List.mem_singleton.mp new
        exact Finset.disjoint_left.mp enabled.fresh made'
          (enabled.taken_subset (List.mem_toFinset.mpr taken))
  · intro e member o made
    rcases List.mem_append.mp member with old | new
    · rcases accounted.kept e old o made with before | ⟨e', member', taken'⟩
      · by_cases taken : o ∈ f.selection.taken
        · exact .inr ⟨(f, lab.2), List.mem_append_right _ (List.mem_singleton_self _), taken⟩
        · exact .inl (MeTTaCalculus.OccurrenceCommits.mem_fire.mpr
            (.inl ⟨before, fun inTaken => taken (List.mem_toFinset.mp inTaken)⟩))
      · exact .inr ⟨e', List.mem_append_left _ member', taken'⟩
    · obtain rfl := List.mem_singleton.mp new
      exact .inl (MeTTaCalculus.OccurrenceCommits.mem_fire.mpr (.inr (List.mem_toFinset.mpr made)))

/-- **Every state reached from a reuse-free start of a pure program is accounted.** -/
theorem accounted_of_reach (pure : PureProgram offers) {C : Configuration T O}
    (reuse : ReuseFree A label offers C) {x : Configuration T O × History T S O}
    (reach : HReach A label offers C x) : Accounted x := by
  induction reach with
  | refl => exact accounted_nil C
  | tail reached step ih =>
      obtain ⟨lab, moved⟩ := step
      exact accounted_step pure ih (reuse _ reached) moved

/-- **Static dependence is provenance along reuse-free runs**: at an accounted state, a pure firing
admitted there that reuses nothing is statically independent of an earlier event exactly when it
takes nothing that event made. -/
theorem staticIndependent_iff_made_taken {x : Configuration T O × History T S O}
    (accounted : Accounted x) {f : Firing T S O} (pf : Pure f) (valid : f.Valid A label x.1)
    (fresh : ∀ e ∈ x.2, ∀ o ∈ f.selection.made, o ∉ e.1.selection.taken) {e : Event T S O}
    (member : e ∈ x.2) :
    StaticIndependent label e.1 f ↔
      Disjoint e.1.selection.made.toFinset f.selection.taken.toFinset := by
  have : Nonempty S := ⟨A.identity⟩
  have enabled := valid.firing.occurrences
  have takes : Disjoint e.1.selection.taken.toFinset f.selection.taken.toFinset :=
    Finset.disjoint_left.mpr fun o taken taken' =>
      accounted.gone e member o (List.mem_toFinset.mp taken) (enabled.taken_subset taken')
  have makes : Disjoint e.1.selection.made.toFinset f.selection.made.toFinset :=
    Finset.disjoint_left.mpr fun o made made' => by
      rcases accounted.kept e member o (List.mem_toFinset.mp made) with present | ⟨e', member', taken'⟩
      · exact Finset.disjoint_left.mp enabled.fresh made' present
      · exact fresh e' member' o (List.mem_toFinset.mp made') taken'
  rw [staticIndependent_iff_provenance label (accounted.pure e member) pf takes makes]
  exact ⟨And.left, fun first => ⟨first, Finset.disjoint_left.mpr fun o made taken =>
    fresh e member o (List.mem_toFinset.mp made) (List.mem_toFinset.mp taken)⟩⟩

end Accounting

/-! ## The record of a history -/

section Correspondence

/-- **The extended record of a history**: the entry of each event, with its recorded past. -/
def toRecord (h : History T S O) : ExtRecord O := h.map fun e => (Entry.ofFiring e.1, e.2)

/-- A state with its history read as an extended record. -/
def recordOf (x : Configuration T O × History T S O) : Configuration T O × ExtRecord O :=
  (x.1, toRecord x.2)

omit [DecidableEq O] in
theorem toRecord_map_snd : ∀ h : History T S O, (toRecord h).map Prod.snd = h.map Prod.snd
  | [] => rfl
  | e :: h => by
      show e.2 :: (toRecord h).map Prod.snd = e.2 :: h.map Prod.snd
      rw [toRecord_map_snd h]

variable {A : SubstitutionAction T S} {label : O → T} {offers : L → Firing T S O → Prop}

/-- **The causal past is the provenance past** along reuse-free runs. -/
theorem past_eq_provPast {x : Configuration T O × History T S O} (accounted : Accounted x)
    {f : Firing T S O} (pf : Pure f) (valid : f.Valid A label x.1)
    (fresh : ∀ e ∈ x.2, ∀ o ∈ f.selection.made, o ∉ e.1.selection.taken) :
    past label x.2 f = provPast (toRecord x.2) (Entry.ofFiring f) := by
  have direct : directPast label x.2 f = provDirect (toRecord x.2) (Entry.ofFiring f) := by
    ext i
    rw [mem_directPast, mem_provDirect]
    simp only [toRecord, List.length_map, List.getElem?_map]
    constructor
    · rintro ⟨lt, e, get, dependent⟩
      refine ⟨lt, (Entry.ofFiring e.1, e.2), by rw [get]; rfl, fun disjoint => dependent ?_⟩
      exact (staticIndependent_iff_made_taken accounted pf valid fresh
        (List.mem_iff_getElem?.mpr ⟨i, get⟩)).mpr disjoint
    · rintro ⟨lt, y, get, overlap⟩
      rcases h : x.2[i]? with _ | e
      · rw [h] at get
        cases get
      · rw [h] at get
        cases get
        exact ⟨lt, e, rfl, fun independent => overlap ((staticIndependent_iff_made_taken accounted pf
          valid fresh (List.mem_iff_getElem?.mpr ⟨i, h⟩)).mp independent)⟩
  unfold past provPast
  rw [direct]
  congr 1
  refine Finset.biUnion_congr rfl fun i _ => ?_
  simp only [toRecord, List.getElem?_map]
  rcases x.2[i]? with _ | e <;> rfl

/-- A history move is a move of the record-extended step. -/
theorem rmoves_of_hmoves (pure : PureProgram offers) {x : Configuration T O × History T S O}
    (accounted : Accounted x) (fresh : FreshAt A label offers x) {lab : L × Finset ℕ}
    {y : Configuration T O × History T S O} (moved : HMoves A label offers x lab y) :
    RMoves A label offers (recordOf x) lab (recordOf y) := by
  obtain ⟨f, offered, valid, labelled, rfl⟩ := moved
  refine ⟨f, offered, valid, labelled.trans (past_eq_provPast accounted (pure _ _ offered) valid
    (fresh lab.1 f offered valid)), ?_⟩
  simp [recordOf, toRecord]

/-- A move of the record-extended step is a history move. -/
theorem hmoves_of_rmoves (pure : PureProgram offers) {x : Configuration T O × History T S O}
    (accounted : Accounted x) (fresh : FreshAt A label offers x) {lab : L × Finset ℕ}
    {u : Configuration T O × ExtRecord O} (moved : RMoves A label offers (recordOf x) lab u) :
    ∃ y, HMoves A label offers x lab y ∧ u = recordOf y := by
  obtain ⟨f, offered, valid, labelled, rfl⟩ := moved
  refine ⟨(f.result label x.1, x.2 ++ [(f, lab.2)]), ⟨f, offered, valid,
    labelled.trans (past_eq_provPast accounted (pure _ _ offered) valid
      (fresh lab.1 f offered valid)).symm, rfl⟩, ?_⟩
  simp [recordOf, toRecord]

/-- **History-preserving bisimilarity is bisimilarity of the record-extended step**, on pure
programs from reuse-free starts. -/
theorem hpBisimilar_iff_recordBisimilar (pure : PureProgram offers) {C D : Configuration T O}
    (reuseC : ReuseFree A label offers C) (reuseD : ReuseFree A label offers D) :
    HPBisimilar A label offers C D ↔ RecordBisimilar A label offers C D := by
  constructor
  · rintro ⟨R, bisimulation, related⟩
    refine ⟨fun u v => ∃ x y, HReach A label offers C x ∧ HReach A label offers D y ∧ R x y ∧
      u = recordOf x ∧ v = recordOf y, ⟨?_, ?_, ?_⟩,
      ⟨(C, []), (D, []), .refl, .refl, related, rfl, rfl⟩⟩
    · rintro u v ⟨x, y, reachX, reachY, rel, rfl, rfl⟩ lab u' moved
      obtain ⟨x', movedX, rfl⟩ := hmoves_of_rmoves pure (accounted_of_reach pure reuseC reachX)
        (reuseC x reachX) moved
      obtain ⟨y', movedY, rel'⟩ := bisimulation.1 rel lab movedX
      exact ⟨recordOf y', rmoves_of_hmoves pure (accounted_of_reach pure reuseD reachY)
        (reuseD y reachY) movedY, x', y', reachX.tail ⟨lab, movedX⟩, reachY.tail ⟨lab, movedY⟩,
        rel', rfl, rfl⟩
    · rintro u v ⟨x, y, reachX, reachY, rel, rfl, rfl⟩ lab v' moved
      obtain ⟨y', movedY, rfl⟩ := hmoves_of_rmoves pure (accounted_of_reach pure reuseD reachY)
        (reuseD y reachY) moved
      obtain ⟨x', movedX, rel'⟩ := bisimulation.2.1 rel lab movedY
      exact ⟨recordOf x', rmoves_of_hmoves pure (accounted_of_reach pure reuseC reachX)
        (reuseC x reachX) movedX, x', y', reachX.tail ⟨lab, movedX⟩, reachY.tail ⟨lab, movedY⟩,
        rel', rfl, rfl⟩
    · intro _ _ _ atom
      exact atom.elim
  · rintro ⟨R, bisimulation, related⟩
    refine ⟨fun x y => HReach A label offers C x ∧ HReach A label offers D y ∧
      R (recordOf x) (recordOf y), ⟨?_, ?_, ?_⟩, ⟨.refl, .refl, related⟩⟩
    · rintro x y ⟨reachX, reachY, rel⟩ lab x' movedX
      obtain ⟨v', movedV, rel'⟩ := bisimulation.1 rel lab
        (rmoves_of_hmoves pure (accounted_of_reach pure reuseC reachX) (reuseC x reachX) movedX)
      obtain ⟨y', movedY, rfl⟩ := hmoves_of_rmoves pure (accounted_of_reach pure reuseD reachY)
        (reuseD y reachY) movedV
      exact ⟨y', movedY, reachX.tail ⟨lab, movedX⟩, reachY.tail ⟨lab, movedY⟩, rel'⟩
    · rintro x y ⟨reachX, reachY, rel⟩ lab y' movedY
      obtain ⟨u', movedU, rel'⟩ := bisimulation.2.1 rel lab
        (rmoves_of_hmoves pure (accounted_of_reach pure reuseD reachY) (reuseD y reachY) movedY)
      obtain ⟨x', movedX, rfl⟩ := hmoves_of_rmoves pure (accounted_of_reach pure reuseC reachX)
        (reuseC x reachX) movedU
      exact ⟨x', movedX, reachX.tail ⟨lab, movedX⟩, reachY.tail ⟨lab, movedY⟩, rel'⟩
    · intro _ _ _ atom
      exact atom.elim

end Correspondence

/-! ## The extended record determines the causal order -/

section Determination

/-- The entries of a history: what each event took and made. -/
def entries (h : History T S O) : List (Entry O) := h.map fun e => Entry.ofFiring e.1

/-- **The causal pasts read off the entries alone**: each entry with its provenance past after the
earlier ones. -/
noncomputable def annotate (l : List (Entry O)) : ExtRecord O :=
  l.foldl (fun rec e => rec ++ [(e, provPast rec e)]) []

theorem annotate_concat (l : List (Entry O)) (e : Entry O) :
    annotate (l ++ [e]) = annotate l ++ [(e, provPast (annotate l) e)] := by
  unfold annotate
  rw [List.foldl_append]
  rfl

variable {A : SubstitutionAction T S} {label : O → T} {offers : L → Firing T S O → Prop}

/-- **The extended record determines the causal order**: along a pure, reuse-free run, the record of
the history is the annotation of its entries. -/
theorem toRecord_eq_annotate (pure : PureProgram offers) {C : Configuration T O}
    (reuse : ReuseFree A label offers C) {x : Configuration T O × History T S O}
    (reach : HReach A label offers C x) : toRecord x.2 = annotate (entries x.2) := by
  induction reach with
  | refl => rfl
  | @tail b c reached step ih =>
      obtain ⟨lab, f, offered, valid, labelled, rfl⟩ := step
      have accounted := accounted_of_reach pure reuse reached
      have pastEq := past_eq_provPast accounted (pure _ _ offered) valid
        (reuse _ reached lab.1 f offered valid)
      have concat : entries (b.2 ++ [(f, lab.2)]) = entries b.2 ++ [Entry.ofFiring f] :=
        List.map_append
      have record : toRecord (b.2 ++ [(f, lab.2)]) = toRecord b.2 ++ [(Entry.ofFiring f, lab.2)] :=
        List.map_append
      show toRecord (b.2 ++ [(f, lab.2)]) = annotate (entries (b.2 ++ [(f, lab.2)]))
      rw [concat, record, annotate_concat, ← ih, labelled, pastEq]

variable (A label offers) in
/-- **One round of the bisimulation game**: both sides move with one label, and the ends are
related. -/
def Round (R : Configuration T O × History T S O → Configuration T O × History T S O → Prop)
    (p q : (Configuration T O × History T S O) × (Configuration T O × History T S O)) : Prop :=
  ∃ lab, HMoves A label offers p.1 lab q.1 ∧ HMoves A label offers p.2 lab q.2 ∧ R q.1 q.2

theorem matched_invariant
    {R : Configuration T O × History T S O → Configuration T O × History T S O → Prop}
    {C D : Configuration T O}
    {p : (Configuration T O × History T S O) × (Configuration T O × History T S O)}
    (matched : Relation.ReflTransGen (Round A label offers R) ((C, []), (D, [])) p) :
    HReach A label offers C p.1 ∧ HReach A label offers D p.2 ∧
      p.1.2.map Prod.snd = p.2.2.map Prod.snd := by
  induction matched with
  | refl => exact ⟨.refl, .refl, rfl⟩
  | tail _ round ih =>
      obtain ⟨reachX, reachY, pasts⟩ := ih
      obtain ⟨lab, movedX, movedY, _⟩ := round
      refine ⟨reachX.tail ⟨lab, movedX⟩, reachY.tail ⟨lab, movedY⟩, ?_⟩
      obtain ⟨f, _, _, _, hx⟩ := movedX
      obtain ⟨g, _, _, _, hy⟩ := movedY
      rw [hx, hy]
      simp [pasts]

/-- **The matchings of history-preserving bisimulations are isomorphisms of the causal orders read
off the extended records**: along the rounds of the bisimulation game from two reuse-free starts of
a pure program, the causal pasts that the two records determine agree position by position. -/
theorem matching_causal_eq (pure : PureProgram offers) {C D : Configuration T O}
    (reuseC : ReuseFree A label offers C) (reuseD : ReuseFree A label offers D)
    {R : Configuration T O × History T S O → Configuration T O × History T S O → Prop}
    {x y : Configuration T O × History T S O}
    (matched : Relation.ReflTransGen (Round A label offers R) ((C, []), (D, [])) (x, y)) :
    (annotate (entries x.2)).map Prod.snd = (annotate (entries y.2)).map Prod.snd := by
  obtain ⟨reachX, reachY, pasts⟩ := matched_invariant matched
  rw [← toRecord_eq_annotate pure reuseC reachX, ← toRecord_eq_annotate pure reuseD reachY,
    toRecord_map_snd, toRecord_map_snd]
  exact pasts

end Determination

#print axioms Entry.references_ofFiring
#print axioms Entry.references_rename
#print axioms accounted_step
#print axioms accounted_of_reach
#print axioms staticIndependent_iff_made_taken
#print axioms past_eq_provPast
#print axioms rmoves_of_hmoves
#print axioms hmoves_of_rmoves
#print axioms hpBisimilar_iff_recordBisimilar
#print axioms toRecord_eq_annotate
#print axioms matching_causal_eq

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race
