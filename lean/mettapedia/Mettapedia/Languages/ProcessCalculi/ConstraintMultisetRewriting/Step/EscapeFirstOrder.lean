import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EscapeTransport
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.FirstOrderIndependence

/-!
# Escape-relative transport of the one-frame instance: sightings escape mid-run

* **The one-frame transport is natural** (`firstOrderNatural`): its frame isomorphisms and its
  occurrence renamings are identities.
* **What clients read and what a first-order firing makes escape** (`firstOrderEscape`): the labels
  are the rows; a firing makes the environment record each set its predicate queries sighted, as one
  unary relation (`Observation.querySightings`), and publishes nothing.
* **The record at the end of a run** (`record_last`): the start's record followed by the run's
  sightings (`Observation.runSightings`). Flattened, it is what a watching client records
  (`support_last`, `support_last_ofClient`, with `Observation.Client.watch`), so every identity a fired
  query sighted has escaped by the end of the run (`sighted_escaped_last`).
* **Pointwise fixing is the wrong notion** (`EscapeControls.sighting_reveals`): exchanging two private
  present occurrences with one label fixes the start and carries a firing that takes one and sights
  both to the firing that takes the other. No renaming that fixes the two sighted identities
  pointwise relates the results. The exchange carries the sighted set to itself, and the transports
  that rename occurrences relate the two runs (`ObserverControls.sighting_dissolved`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

open Interface (Frames Transport Escaped)
open Observation (Client Record runSighted runSightings querySightings)

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]
variable (A : SubstitutionAction T S) (label : O → T)

/-- **The one-frame transport is natural.** -/
theorem firstOrderNatural : (firstOrderTransport A label).Natural where
  refl _ := Frames.Agree.refl _
  symm _ := Frames.Agree.refl _
  trans _ _ := fun t => by
    show A.E (A.apply A.identity t) (A.apply (A.compose A.identity A.identity) t)
    simp only [A.apply_compose, A.apply_identity]
    exact A.equivalence.refl _
  result_move _ _ _ := fun t => by
    show A.E (A.apply (A.compose A.identity (A.compose A.identity A.identity)) t)
      (A.apply (A.compose (A.compose A.identity A.identity) A.identity) t)
    simp only [A.apply_compose, A.apply_identity]
    exact A.equivalence.refl _
  result_alike {C} {f} _ same _ _ := by
    subst same
    exact fun t => by
      show A.E (A.apply (A.compose A.identity (A.compose A.identity A.identity)) t)
        (A.apply (A.compose A.identity A.identity) t)
      simp only [A.apply_compose, A.apply_identity]
      exact A.equivalence.refl _
  rename_refl _ := rfl
  rename_symm _ := rfl
  rename_trans _ _ := rfl
  rename_result_move _ _ _ := rfl
  rename_result_alike {C} {f} _ same _ _ := by
    subst same
    rfl

/-- **What clients read of a configuration and what a first-order firing makes escape**: the labels
are the rows, and a firing makes the environment record each set its predicate queries sighted. -/
def firstOrderEscape : (firstOrderTransport A label).Escape where
  row _ o := some (label o)
  row_iso _ o := .some (Frames.Carried.of_E (by
    show A.E (A.apply A.identity (label o)) (label o)
    rw [A.apply_identity]
    exact A.equivalence.refl _))
  records f := querySightings f.queries
  publishes _ _ := []
  records_move _ f := (Record.rename_refl (querySightings f.queries)).symm
  publishes_move _ _ _ := .nil
  records_alike {C} {f} _ same := by
    subst same
    rfl
  publishes_alike {C} {f} _ same _ _ := by
    subst same
    exact .nil

/-- **The record at the end of a run**: the start's record followed by the run's sightings. -/
theorem record_last : ∀ {x : Escaped (firstOrder A label).toStep} (r : (firstOrderEscape A label).step.Run x),
    r.last.record = x.record ++ runSightings (r.word.map fun e => (e.2 : Firing T S O))
  | x, .nil _ => (List.append_nil _).symm
  | x, .cons f admitted rest => by
      have later := record_last rest
      have head : ((firstOrderEscape A label).step.result f admitted).record =
          x.record ++ querySightings f.queries := rfl
      show rest.last.record = x.record ++ runSightings (f :: rest.word.map fun e => (e.2 : Firing T S O))
      rw [later, head, Observation.runSightings_cons, List.append_assoc]

/-- **Flattened, the record at the end is the start's with the run's sightings.** -/
theorem support_last {x : Escaped (firstOrder A label).toStep} (r : (firstOrderEscape A label).step.Run x) :
    Record.support r.last.record =
      Record.support x.record ∪ runSighted (r.word.map fun e => (e.2 : Firing T S O)) := by
  rw [record_last A label r, Record.support_append, Observation.support_runSightings]

omit [DecidableEq O] in
theorem escaped_watch (c : Client O) [DecidableEq O] (w : List (Firing T S O)) :
    (c.watch w).escaped = c.escaped ∪ runSighted w := by
  ext o
  simp only [Client.escaped, Client.watch, Finset.mem_union]
  tauto

/-- **For a client context of the client layer, the record at the end is what the client records
watching the run** (`Observation.Client.watch`), flattened. -/
theorem support_last_ofClient {x : Escaped (firstOrder A label).toStep} {c : Client O}
    (held : x.record = Record.ofClient c) (r : (firstOrderEscape A label).step.Run x) :
    Record.support r.last.record = (c.watch (r.word.map fun e => (e.2 : Firing T S O))).escaped := by
  rw [support_last A label r, held, Record.support_ofClient, escaped_watch]

/-- **Every identity a fired query sighted has escaped by the end of the run.** -/
theorem sighted_escaped_last {x : Escaped (firstOrder A label).toStep}
    (r : (firstOrderEscape A label).step.Run x) {f : Firing T S O}
    (inRun : f ∈ r.word.map fun e => (e.2 : Firing T S O))
    {query : PredicateQueryAdmission.Query T S O} (asked : query ∈ f.queries) :
    query.seen ⊆ Record.support r.last.record := by
  rw [support_last A label r]
  intro o member
  exact Finset.mem_union_right _ (Observation.mem_runSighted.mpr ⟨f, inRun, query, asked, member⟩)

/-! ## Control: pointwise fixing cannot relate sightings -/

namespace EscapeControls

open Mettapedia.Logic.LP
open ConstraintMultisetRewriting.Controls (signature)

/-- Every occurrence is labelled `0`. -/
def blank : Nat → Term signature := fun _ => .const 0

/-- Occurrences `5` and `6`, and no knowledge. -/
def twins : Configuration (Term signature) Nat := ⟨[], {5, 6}⟩

/-- A query whose region is every label: it sights `5` and `6`. -/
def seeAll : PredicateQueryAdmission.Query (Term signature) (Subst signature) Nat :=
  ⟨fun _ _ => true, {5, 6}⟩

/-- Takes occurrence `5` and sights both. -/
def takeFive : Firing (Term signature) (Subst signature) Nat :=
  ⟨⟨[.const 0], [], [], [], []⟩, [seeAll], ⟨[5], [], []⟩⟩

/-- The renaming that exchanges `5` and `6`. -/
abbrev swapTwins : Nat ≃ Nat := Equiv.swap 5 6

theorem swapTwins_keeps (o : Nat) : blank (swapTwins o) = blank o := rfl

theorem twins_renamed : renameConfiguration swapTwins twins = twins := by
  show (⟨[], ({5, 6} : Finset Nat).map swapTwins.toEmbedding⟩ : Configuration (Term signature) Nat) = ⟨[], {5, 6}⟩
  congr 1
  decide

theorem takeFive_valid : takeFive.Valid Controls.A blank twins := by
  refine ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide,
    ⟨Subst.id signature, by
      simp [Selection.problem, Selection.equations, twins, takeFive, blank]
      exact Controls.A.equivalence.refl _⟩,
    by simp [takeFive]⟩, ?_⟩
  intro query member σ _
  obtain rfl := List.mem_singleton.mp member
  show MeTTaCalculus.OccurrenceCommits.regionOf blank twins.present (fun _ => true) = {5, 6}
  decide

theorem takeSix_valid : (takeFive.rename swapTwins).Valid Controls.A blank twins := by
  have valid := (Firing.valid_rename Controls.A swapTwins_keeps takeFive twins).mpr takeFive_valid
  rwa [twins_renamed] at valid

/-- **Pointwise fixing cannot relate sightings.** At the start, `5` and `6` are present, private and
labelled alike: the exchange keeps every label and fixes the start, and it carries the firing that
takes `5` to the firing that takes `6`. Both fire, and both sight `{5, 6}`. After them, no renaming
that fixes `5` and `6` pointwise relates the two results: one has `6` present, the other `5`. The
exchange itself carries the sighted set to itself, and relates them
(`ObserverControls.sighting_dissolved`). -/
theorem sighting_reveals :
    renameConfiguration swapTwins twins = twins ∧ takeFive.Valid Controls.A blank twins ∧
      (takeFive.rename swapTwins).Valid Controls.A blank twins ∧
      Observation.sighted takeFive.queries = {5, 6} ∧
      Observation.sighted (takeFive.rename swapTwins).queries = {5, 6} ∧
      ∀ ρ : Nat ≃ Nat, (∀ o ∈ ({5, 6} : Finset Nat), ρ o = o) →
        (takeFive.result blank twins).present.map ρ.toEmbedding ≠
          ((takeFive.rename swapTwins).result blank twins).present := by
  refine ⟨twins_renamed, takeFive_valid, takeSix_valid, by decide, by decide, fun ρ fixes same => ?_⟩
  have five : (takeFive.result blank twins).present = {6} := by decide
  have six : ((takeFive.rename swapTwins).result blank twins).present = {5} := by decide
  rw [five, six, Finset.map_singleton, Equiv.coe_toEmbedding, fixes 6 (by decide)] at same
  exact absurd same (by decide)

end EscapeControls

#print axioms firstOrderNatural
#print axioms firstOrderEscape
#print axioms record_last
#print axioms support_last
#print axioms support_last_ofClient
#print axioms sighted_escaped_last
#print axioms EscapeControls.sighting_reveals

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns
