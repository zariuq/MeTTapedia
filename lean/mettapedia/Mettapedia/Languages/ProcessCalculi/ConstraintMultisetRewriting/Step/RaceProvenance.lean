import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RaceHistories

/-!
# Provenance bisimilarity: a rung above history-preserving identity

`RaceHistories` labels each move of the record-extended step with its provenance *past*: the earlier
entries that made something it takes, closed under their recorded pasts. That closure is the causal
order, and on pure programs from reuse-free starts the identity it gives is history-preserving
bisimilarity (`hpBisimilar_iff_recordBisimilar`). The record itself holds more: which earlier entry
each firing took from directly (`HistoryControls.matching_not_record_iso`).

## The provenance step (`PMoves`, `ProvenanceBisimilar`)

The same states, extended records with their provenance pasts, and the same moves; a move is labelled
by its label and its **direct provenance** (`provDirect`): the positions of the earlier entries that
made something it takes, without closure. Matched runs then have the same direct-provenance graph,
position by position.

* **Provenance bisimilarity implies record bisimilarity** (`recordBisimilar_of_provenanceBisimilar`):
  the provenance past is determined by the direct provenance and the recorded pasts
  (`provPast_congr`). Hence, on pure programs from reuse-free starts, **provenance bisimilarity implies
  history-preserving bisimilarity** (`hpBisimilar_of_provenanceBisimilar`). It is strictly finer
  (`RaceProvenanceControls`).

## A static criterion for reuse-freedom (`SingleAssignment`, `reuseFree_of_singleAssignment`)

`ReuseFree` is a property of runs. A **single-assignment** start of a program is one where

* nothing an offered firing makes is present at the start (`unmade`);
* each identity is made by at most one offered firing (`unique`);
* every offered firing that makes something takes something (`takes`).

**A single-assignment start is reuse-free.** Along every run, every identity an event took is gone,
and the makers of every identity that an event took or that is present have already fired
(`Assigned`, `assigned_of_reach`). A firing that made something an earlier event took would therefore
have fired before, and taken something that is now gone, so it is not admitted
(`freshAt_of_assigned`). Each of the three conditions is needed (`RaceProvenanceControls`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race

open AnnotatedRuns (Firing StaticIndependent)
open Mettapedia.GSLT (GSLT)
open Mettapedia.GSLT.HennessyMilner (System)

universe uT uS uO uL

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O] {L : Type uL}

/-! ## The provenance step -/

section ProvenanceStep

variable (A : SubstitutionAction T S) (label : O → T) (offers : L → Firing T S O → Prop)

/-- **A move of the provenance step**: an offered firing admitted at the configuration, labelled by
its label and its direct provenance; its entry is appended to the record with its provenance past. -/
def PMoves (x : Configuration T O × ExtRecord O) (lab : L × Finset ℕ)
    (y : Configuration T O × ExtRecord O) : Prop :=
  ∃ f, offers lab.1 f ∧ f.Valid A label x.1 ∧ lab.2 = provDirect x.2 (Entry.ofFiring f) ∧
    y = (f.result label x.1, x.2 ++ [(Entry.ofFiring f, provPast x.2 (Entry.ofFiring f))])

/-- The provenance step as a Hennessy–Milner system on configurations with extended records. -/
def provSystem : System (recordGslt A label offers) where
  Atom := PEmpty.{1}
  observes atom _ := atom.elim
  observes_resp atom := atom.elim
  Label := L × Finset ℕ
  act lab x y := PMoves A label offers x lab y
  act_resp_left := by
    intro lab x x' y same step
    exact ⟨y, (same : x = x') ▸ step, rfl⟩
  act_resp_right := by
    intro lab x y y' step same
    exact (same : y = y') ▸ step

/-- **Provenance bisimilarity**: bisimilarity of the provenance step, from empty records. -/
def ProvenanceBisimilar (C D : Configuration T O) : Prop :=
  (provSystem A label offers).Bisimilar (C, []) (D, [])

end ProvenanceStep

/-- **The provenance past is determined by the direct provenance and the recorded pasts.** -/
theorem provPast_congr {r r' : ExtRecord O} {e e' : Entry O}
    (direct : provDirect r e = provDirect r' e') (pasts : r.map Prod.snd = r'.map Prod.snd) :
    provPast r e = provPast r' e' := by
  unfold provPast
  rw [direct]
  congr 1
  refine Finset.biUnion_congr rfl fun i _ => ?_
  rw [← List.getElem?_map, ← List.getElem?_map, pasts]

variable {A : SubstitutionAction T S} {label : O → T} {offers : L → Firing T S O → Prop}

theorem record_forward {R : Configuration T O × ExtRecord O → Configuration T O × ExtRecord O → Prop}
    (forward : ∀ ⦃x y⦄, R x y → ∀ lab ⦃x'⦄, PMoves A label offers x lab x' →
      ∃ y', PMoves A label offers y lab y' ∧ R x' y')
    {x y : Configuration T O × ExtRecord O} (related : R x y)
    (pasts : x.2.map Prod.snd = y.2.map Prod.snd) {lab : L × Finset ℕ}
    {x' : Configuration T O × ExtRecord O} (moved : RMoves A label offers x lab x') :
    ∃ y', RMoves A label offers y lab y' ∧ R x' y' ∧ x'.2.map Prod.snd = y'.2.map Prod.snd := by
  obtain ⟨f, offered, valid, labelled, rfl⟩ := moved
  obtain ⟨y', ⟨g, offeredG, validG, labelledG, rfl⟩, related'⟩ :=
    forward related (lab.1, provDirect x.2 (Entry.ofFiring f))
      (x' := (f.result label x.1, x.2 ++ [(Entry.ofFiring f, lab.2)]))
      ⟨f, offered, valid, rfl, by rw [labelled]⟩
  have samePast : provPast x.2 (Entry.ofFiring f) = provPast y.2 (Entry.ofFiring g) :=
    provPast_congr labelledG pasts
  refine ⟨_, ⟨g, offeredG, validG, labelled.trans samePast, ?_⟩, related', ?_⟩
  · rw [labelled, samePast]
  · simp [pasts, labelled, samePast]

/-- **Provenance bisimilarity implies record bisimilarity.** -/
theorem recordBisimilar_of_provenanceBisimilar {C D : Configuration T O}
    (bisimilar : ProvenanceBisimilar A label offers C D) : RecordBisimilar A label offers C D := by
  obtain ⟨R, ⟨forward, backward, _⟩, related⟩ := bisimilar
  refine ⟨fun x y => R x y ∧ x.2.map Prod.snd = y.2.map Prod.snd,
    ⟨?_, ?_, fun _ _ _ atom => atom.elim⟩, related, rfl⟩
  · rintro x y ⟨rel, pasts⟩ lab x' moved
    obtain ⟨y', moved', rel', pasts'⟩ := record_forward forward rel pasts moved
    exact ⟨y', moved', rel', pasts'⟩
  · rintro x y ⟨rel, pasts⟩ lab y' moved
    obtain ⟨x', moved', rel', pasts'⟩ := record_forward (R := fun a b => R b a)
      (fun _ _ r lab' _ m => backward r lab' m) rel pasts.symm moved
    exact ⟨x', moved', rel', pasts'.symm⟩

/-- **On pure programs from reuse-free starts, provenance bisimilarity implies history-preserving
bisimilarity.** -/
theorem hpBisimilar_of_provenanceBisimilar (pure : PureProgram offers) {C D : Configuration T O}
    (reuseC : ReuseFree A label offers C) (reuseD : ReuseFree A label offers D)
    (bisimilar : ProvenanceBisimilar A label offers C D) : HPBisimilar A label offers C D :=
  (hpBisimilar_iff_recordBisimilar pure reuseC reuseD).mpr
    (recordBisimilar_of_provenanceBisimilar bisimilar)

/-! ## A static criterion for reuse-freedom -/

section SingleAssignment

variable (offers) in
/-- **A single-assignment start**: nothing an offered firing makes is present; each identity has at
most one offered maker; every offered firing that makes something takes something. -/
structure SingleAssignment (C : Configuration T O) : Prop where
  unmade : ∀ ℓ f, offers ℓ f → ∀ o ∈ f.selection.made, o ∉ C.present
  unique : ∀ ℓ ℓ' f g, offers ℓ f → offers ℓ' g → ∀ o ∈ f.selection.made, o ∈ g.selection.made → f = g
  takes : ∀ ℓ f, offers ℓ f → f.selection.made ≠ [] → f.selection.taken ≠ []

variable (offers) in
/-- **The invariant of single-assignment runs**: what events took is gone, and the makers of what
events took and of what is present have fired. -/
structure Assigned (x : Configuration T O × History T S O) : Prop where
  gone : ∀ e ∈ x.2, ∀ o ∈ e.1.selection.taken, o ∉ x.1.present
  fired : ∀ e ∈ x.2, ∀ o ∈ e.1.selection.taken, ∀ ℓ m, offers ℓ m → o ∈ m.selection.made →
    ∃ e' ∈ x.2, e'.1 = m
  present : ∀ o ∈ x.1.present, ∀ ℓ m, offers ℓ m → o ∈ m.selection.made → ∃ e' ∈ x.2, e'.1 = m

/-- **No reuse at an assigned state**, for single-assignment programs. -/
theorem freshAt_of_assigned {C : Configuration T O} (single : SingleAssignment offers C)
    {x : Configuration T O × History T S O} (assigned : Assigned offers x) :
    FreshAt A label offers x := by
  intro ℓ f offered valid e member o made taken
  obtain ⟨e', member', rfl⟩ := assigned.fired e member o taken ℓ f offered made
  obtain ⟨p, inTaken⟩ := List.exists_mem_of_ne_nil _
    (single.takes ℓ e'.1 offered (List.ne_nil_of_mem made))
  exact assigned.gone e' member' p inTaken
    (valid.firing.occurrences.taken_subset (List.mem_toFinset.mpr inTaken))

omit [DecidableEq O] in
theorem assigned_nil {C : Configuration T O} (single : SingleAssignment offers C) :
    Assigned offers ((C, []) : Configuration T O × History T S O) :=
  ⟨fun _ member => (List.not_mem_nil member).elim, fun _ member => (List.not_mem_nil member).elim,
    fun o present ℓ m offered made => absurd present (single.unmade ℓ m offered o made)⟩

/-- **Single-assignment runs keep the invariant.** -/
theorem assigned_step {C : Configuration T O} (single : SingleAssignment offers C)
    {x y : Configuration T O × History T S O} (assigned : Assigned offers x) {lab : L × Finset ℕ}
    (moved : HMoves A label offers x lab y) : Assigned offers y := by
  have fresh := freshAt_of_assigned (A := A) (label := label) single assigned
  obtain ⟨g, offered, valid, _, rfl⟩ := moved
  have enabled := valid.firing.occurrences
  have inHistory : (g, lab.2) ∈ x.2 ++ [(g, lab.2)] := List.mem_append_right _ (List.mem_singleton_self _)
  refine ⟨?_, ?_, ?_⟩
  · intro e member o taken present
    have present' : o ∈ MeTTaCalculus.OccurrenceCommits.fire x.1.present
        (g.selection.commit (T := T)) := present
    rcases MeTTaCalculus.OccurrenceCommits.mem_fire.mp present' with ⟨before, notTaken⟩ | made
    · rcases List.mem_append.mp member with old | new
      · exact assigned.gone e old o taken before
      · obtain rfl := List.mem_singleton.mp new
        exact notTaken (List.mem_toFinset.mpr taken)
    · have made' : o ∈ g.selection.made.toFinset := made
      rcases List.mem_append.mp member with old | new
      · exact fresh lab.1 g offered valid e old o (List.mem_toFinset.mp made') taken
      · obtain rfl := List.mem_singleton.mp new
        exact Finset.disjoint_left.mp enabled.fresh made'
          (enabled.taken_subset (List.mem_toFinset.mpr taken))
  · intro e member o taken ℓ m offeredM madeM
    rcases List.mem_append.mp member with old | new
    · obtain ⟨e', member', same⟩ := assigned.fired e old o taken ℓ m offeredM madeM
      exact ⟨e', List.mem_append_left _ member', same⟩
    · obtain rfl := List.mem_singleton.mp new
      obtain ⟨e', member', same⟩ := assigned.present o
        (enabled.taken_subset (List.mem_toFinset.mpr taken)) ℓ m offeredM madeM
      exact ⟨e', List.mem_append_left _ member', same⟩
  · intro o present ℓ m offeredM madeM
    have present' : o ∈ MeTTaCalculus.OccurrenceCommits.fire x.1.present
        (g.selection.commit (T := T)) := present
    rcases MeTTaCalculus.OccurrenceCommits.mem_fire.mp present' with ⟨before, _⟩ | made
    · obtain ⟨e', member', same⟩ := assigned.present o before ℓ m offeredM madeM
      exact ⟨e', List.mem_append_left _ member', same⟩
    · have same : g = m := single.unique lab.1 ℓ g m offered offeredM o
        (List.mem_toFinset.mp made) madeM
      exact ⟨(g, lab.2), inHistory, same⟩

/-- **Every state reached from a single-assignment start is assigned.** -/
theorem assigned_of_reach {C : Configuration T O} (single : SingleAssignment offers C)
    {x : Configuration T O × History T S O} (reach : HReach A label offers C x) : Assigned offers x := by
  induction reach with
  | refl => exact assigned_nil single
  | tail _ step ih =>
      obtain ⟨lab, moved⟩ := step
      exact assigned_step single ih moved

/-- **A single-assignment start is reuse-free.** -/
theorem reuseFree_of_singleAssignment {C : Configuration T O} (single : SingleAssignment offers C) :
    ReuseFree A label offers C :=
  fun _ reach => freshAt_of_assigned single (assigned_of_reach single reach)

/-- **On pure single-assignment programs, history-preserving bisimilarity is record bisimilarity.** -/
theorem hpBisimilar_iff_recordBisimilar_of_singleAssignment (pure : PureProgram offers)
    {C D : Configuration T O} (singleC : SingleAssignment offers C)
    (singleD : SingleAssignment offers D) :
    HPBisimilar A label offers C D ↔ RecordBisimilar A label offers C D :=
  hpBisimilar_iff_recordBisimilar pure (reuseFree_of_singleAssignment singleC)
    (reuseFree_of_singleAssignment singleD)

end SingleAssignment

#print axioms provPast_congr
#print axioms recordBisimilar_of_provenanceBisimilar
#print axioms hpBisimilar_of_provenanceBisimilar
#print axioms freshAt_of_assigned
#print axioms assigned_step
#print axioms reuseFree_of_singleAssignment
#print axioms hpBisimilar_iff_recordBisimilar_of_singleAssignment

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race
