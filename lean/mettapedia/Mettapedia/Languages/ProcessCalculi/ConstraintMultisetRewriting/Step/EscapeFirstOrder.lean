import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EscapeTransport
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.FirstOrderIndependence

/-!
# Escape-relative transport of the exact-query alphabet: sightings escape mid-run

The sighting profile carries the original exact queries and their image equation. Its step is the
actual region-query first-order step reindexed along the firing projection. Arbitrary region
observations retain their generic admission; they do not supply a fixed sighted set.

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

/-- The exact-query alphabet inherits the actual first-order state transport. -/
def exactFirstOrderTransport : Transport (ExactQueryAlphabet.step A label) where
  Iso C D := PLift (GuardFreeProcessOrders.SameUpTo A C D)
  toStateIso i := ⟨(sameStateIso A label i.down).frame,(sameStateIso A label i.down).knowledge,
    (sameStateIso A label i.down).rename,(sameStateIso A label i.down).present⟩
  refl C := ⟨GuardFreeProcessOrders.SameUpTo.refl A C⟩
  symm i := ⟨sameUpTo_symm A i.down⟩
  trans i j := ⟨GuardFreeProcessOrders.SameUpTo.trans A i.down j.down⟩
  Alike f f' := f = f'
  alike_equivalence _ := ⟨Eq.refl, Eq.symm, Eq.trans⟩
  selection_alike same := congrArg _ same
  admits_alike same := same ▸ Iff.rfl
  result_alike {C} {f} _ same _ _ := by
    subst same
    exact ⟨GuardFreeProcessOrders.SameUpTo.refl A _⟩
  move _ f := f
  move_alike _ _ _ same := same
  move_refl _ := rfl
  move_trans _ _ _ := rfl
  move_symm _ _ := rfl
  selection_move _ f := (Interface.renameSelection_refl f.1.selection).symm
  admits_move i f := (Firing.valid_congr A label i.down (f := f.1)).symm
  result_move i f _ := ⟨f.1.result_congr A label i.down⟩
  residual _ _ f := f
  selection_residual _ _ _ := rfl
  move_residual _ _ _ _ := rfl

/-- **The one-frame transport is natural.** -/
theorem exactFirstOrderNatural : (exactFirstOrderTransport A label).Natural where
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
def firstOrderEscape : (exactFirstOrderTransport A label).Escape where
  row _ o := some (label o)
  row_iso _ o := .some (Frames.Carried.of_E (by
    show A.E (A.apply A.identity (label o)) (label o)
    rw [A.apply_identity]
    exact A.equivalence.refl _))
  records f := querySightings f.2.queries
  publishes _ _ := []
  records_move _ f := (Record.rename_refl (querySightings f.2.queries)).symm
  publishes_move _ _ _ := .nil
  records_alike {C} {f} _ same := by
    subst same
    rfl
  publishes_alike {C} {f} _ same _ _ := by
    subst same
    exact .nil

/-- **The record at the end of a run**: the start's record followed by the run's sightings. -/
theorem record_last : ∀ {x : Escaped (ExactQueryAlphabet.step A label)} (r : (firstOrderEscape A label).step.Run x),
    r.last.record = x.record ++ runSightings (r.word.map fun e => (e.2 : ExactQueryAlphabet.Alphabet T S O))
  | x, .nil _ => (List.append_nil _).symm
  | x, .cons f admitted rest => by
      have later := record_last rest
      have head : ((firstOrderEscape A label).step.result f admitted).record =
          x.record ++ querySightings f.2.queries := rfl
      show rest.last.record = x.record ++ runSightings (f :: rest.word.map fun e => (e.2 : ExactQueryAlphabet.Alphabet T S O))
      rw [later, head, Observation.runSightings_cons, List.append_assoc]

/-- **Flattened, the record at the end is the start's with the run's sightings.** -/
theorem support_last {x : Escaped (ExactQueryAlphabet.step A label)} (r : (firstOrderEscape A label).step.Run x) :
    Record.support r.last.record =
      Record.support x.record ∪ runSighted (r.word.map fun e => (e.2 : ExactQueryAlphabet.Alphabet T S O)) := by
  rw [record_last A label r, Record.support_append, Observation.support_runSightings]

omit [DecidableEq O] in
theorem escaped_watch (c : Client O) [DecidableEq O] (w : List (ExactQueryAlphabet.Alphabet T S O)) :
    (c.watch w).escaped = c.escaped ∪ runSighted w := by
  ext o
  simp only [Client.escaped, Client.watch, Finset.mem_union]
  tauto

/-- **For a client context of the client layer, the record at the end is what the client records
watching the run** (`Observation.Client.watch`), flattened. -/
theorem support_last_ofClient {x : Escaped (ExactQueryAlphabet.step A label)} {c : Client O}
    (held : x.record = Record.ofClient c) (r : (firstOrderEscape A label).step.Run x) :
    Record.support r.last.record = (c.watch (r.word.map fun e => (e.2 : ExactQueryAlphabet.Alphabet T S O))).escaped := by
  rw [support_last A label r, held, Record.support_ofClient, escaped_watch]

/-- **Every identity a fired query sighted has escaped by the end of the run.** -/
theorem sighted_escaped_last {x : Escaped (ExactQueryAlphabet.step A label)}
    (r : (firstOrderEscape A label).step.Run x) {f : ExactQueryAlphabet.Alphabet T S O}
    (inRun : f ∈ r.word.map fun e => (e.2 : ExactQueryAlphabet.Alphabet T S O))
    {query : PredicateQueryAdmission.Query T S O} (asked : query ∈ f.2.queries) :
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
  ⟨⟨[.const 0], [], [], [], []⟩, [seeAll.toRegion], ⟨[5], [], []⟩⟩

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

/-- The same firing with its explicit exact query data. -/
def takeFiveExact : ExactQueryAlphabet.Alphabet (Term signature) (Subst signature) Nat :=
  ⟨takeFive,⟨[seeAll],rfl⟩⟩

def takeSixExact : ExactQueryAlphabet.Alphabet (Term signature) (Subst signature) Nat :=
  ExactQueryAlphabet.rename swapTwins takeFiveExact

theorem takeFiveExact_valid : (ExactQueryAlphabet.step Controls.A blank).Admits (s := twins) takeFiveExact :=
  takeFive_valid

theorem takeSixExact_valid : (ExactQueryAlphabet.step Controls.A blank).Admits (s := twins) takeSixExact := by
  change takeSixExact.1.Valid Controls.A blank twins
  rw [takeSixExact,ExactQueryAlphabet.rename_fst]
  exact takeSix_valid

/-- **Pointwise fixing cannot relate sightings.** At the start, `5` and `6` are present, private and
labelled alike: the exchange keeps every label and fixes the start, and it carries the firing that
takes `5` to the firing that takes `6`. Both fire, and both sight `{5, 6}`. After them, no renaming
that fixes `5` and `6` pointwise relates the two results: one has `6` present, the other `5`. The
exchange itself carries the sighted set to itself, and relates them
(`ObserverControls.sighting_dissolved`). -/
theorem sighting_reveals :
    renameConfiguration swapTwins twins = twins ∧ takeFive.Valid Controls.A blank twins ∧
      (takeFive.rename swapTwins).Valid Controls.A blank twins ∧
      Observation.sighted takeFiveExact.2.queries = {5, 6} ∧
      Observation.sighted takeSixExact.2.queries = {5, 6} ∧
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
