import Mettapedia.OSLF.Syntax.IntrinsicRulePremiseRequest
import Mettapedia.OSLF.Syntax.ScopedPremiseEvidenceComparison

/-!
# From categorical premise bundles to intrinsic rule evidence

The ordered categorical input supplies an individual event in each authored
premise's binder-extended context. The event's endpoint equation recovers
the exact indexed child judgment. The rule constructor therefore gives a
natural action from the ordered premise bundle to retained conclusion events.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicRuleActionComparison

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalSubstitution
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPresheaf
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalModelPresheaf
open Mettapedia.OSLF.Binding.IntrinsicRuleOccurrencePresheaf
open Mettapedia.OSLF.Binding.IntrinsicRulePremiseRequest
open Mettapedia.OSLF.Binding.CategoricalScopedRuleAction
open Mettapedia.OSLF.Binding.ScopedOperationalEvidenceExponential
open Mettapedia.OSLF.Binding.MultiBinderPresheaf
open Mettapedia.OSLF.Binding.ScopedPremiseEvidenceComparison
open Mettapedia.OSLF.Binding.BindingSubstitutionAlgebra
open Mettapedia.GSLT.LanguageDef.MultiSortedClone
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment)

universe u
variable {S : Signature} {M : List (MetaArity S)}
variable (R : List (Rule S M))
variable {A : BindingCloneAlgebra.Algebra.{u} S}

/-- Equal sorted endpoint pairs determine the same indexed judgment. -/
theorem eventJudgment_eq_of_endpointPair
    {Γ : Ctx S} {Y : SubstitutionModel R A}
    (event : ModelEvent R Y Γ)
    (sort : S.Srt) (source target : A.substitution.Carrier Γ sort)
    (same :
      ((⟨event.1, event.2.1.1⟩,
        ⟨event.1, event.2.1.2⟩) :
        (Σ s : S.Srt, A.substitution.Carrier Γ s) ×
          (Σ s : S.Srt, A.substitution.Carrier Γ s)) =
        (⟨sort, source⟩, ⟨sort, target⟩)) :
    eventJudgment R event =
      (⟨Γ, sort, (source, target)⟩ : Judgment A) := by
  rcases event with ⟨eventSort, ⟨eventSource, eventTarget⟩, evidence⟩
  have hs : (⟨eventSort, eventSource⟩ :
      Σ s : S.Srt, A.substitution.Carrier Γ s) =
        ⟨sort, source⟩ := congrArg Prod.fst same
  have ht : (⟨eventSort, eventTarget⟩ :
      Σ s : S.Srt, A.substitution.Carrier Γ s) =
        ⟨sort, target⟩ := congrArg Prod.snd same
  have hsort : eventSort = sort := (Sigma.mk.inj_iff.mp hs).1
  cases hsort
  have hsource : eventSource = source :=
    eq_of_heq (Sigma.mk.inj_iff.mp hs).2
  have htarget : eventTarget = target :=
    eq_of_heq (Sigma.mk.inj_iff.mp ht).2
  cases hsource
  cases htarget
  rfl

/-- Equality of retained events includes heterogeneous equality of their
individual evidence, even when the sorted endpoint indices are dependent. -/
theorem eventEvidence_heq_of_eq {Γ : Ctx S}
    {Y : SubstitutionModel R A}
    {first second : ModelEvent R Y Γ}
    (same : first = second) : HEq first.2.2 second.2.2 := by
  cases same
  rfl

/-- An event is determined by its exact sorted judgment and its individual
evidence value. This keeps distinct firing witnesses at equal endpoints. -/
theorem modelEvent_ext {Γ : Ctx S} {Y : SubstitutionModel R A}
    {first second : ModelEvent R Y Γ}
    (sameJudgment : eventJudgment R first = eventJudgment R second)
    (sameEvidence : HEq first.2.2 second.2.2) : first = second := by
  rcases first with ⟨firstSort, firstPair, firstEvidence⟩
  rcases second with ⟨secondSort, secondPair, secondEvidence⟩
  cases sameJudgment
  cases sameEvidence
  rfl

/-- Reindexing an event's sorted judgment is the original contextual
substitution on that judgment. -/
theorem eventJudgment_mapModelEvent (Y : SubstitutionModel R A)
    {X Z : Base A} (f : X ⟶ Z)
    (event : ModelEvent R Y X.unop.context) :
    eventJudgment R (mapModelEvent R Y f event) =
      substJudgment (eventJudgment R event)
        (fromPositions X.unop.context f.unop) := by
  rcases event with ⟨sort, ⟨source, target⟩, evidence⟩
  rfl

/-- The evidence component of a reindexed event is the model's specified
substitution action on that same individual firing. -/
theorem eventEvidence_map_heq (Y : SubstitutionModel R A)
    {X Z : Base A} (f : X ⟶ Z)
    (event : ModelEvent R Y X.unop.context) :
    HEq (mapModelEvent R Y f event).2.2
      (Y.act (eventJudgment R event) event.2.2
        (fromPositions X.unop.context f.unop)
        (eventJudgment R (mapModelEvent R Y f event))
        (eventJudgment_mapModelEvent R Y f event).symm) := by
  rcases event with ⟨sort, ⟨source, target⟩, evidence⟩
  rfl

/-- One actual retained firing in the extended context of an authored
premise, selected from the complete ordered rule-input bundle. -/
noncomputable def childEventAt (index : Fin R.length)
    (position : Fin (R.get index).premises.length)
    (Y : SubstitutionModel R A)
    (X : Base A)
    (input : (Bundle (authoredPremises R index Y)).obj X) :
    ModelEvent R Y
      (((R.get index).premises.get position).binders ++
        X.unop.context) :=
  (authoredChildFiring R index position Y).app X input

/-- The observed endpoints of the selected event are the actual authored
premise endpoints at the same rule occurrence. -/
theorem childEventAt_endpoints (index : Fin R.length)
    (position : Fin (R.get index).premises.length)
    (Y : SubstitutionModel R A)
    (X : Base A)
    (input : (Bundle (authoredPremises R index Y)).obj X) :
    let event := childEventAt R index position Y X input
    ((⟨event.1, event.2.1.1⟩,
      ⟨event.1, event.2.1.2⟩) :
        (Σ s : S.Srt,
          A.substitution.Carrier
            (((R.get index).premises.get position).binders ++
              X.unop.context) s) ×
        (Σ s : S.Srt,
          A.substitution.Carrier
            (((R.get index).premises.get position).binders ++
              X.unop.context) s)) =
      childEndpointsAt R index position
        ((assignment (authoredPremises R index Y)).app X input) := by
  have h := congrArg (fun transformation => transformation.app X input)
    (authoredChildFiring_endpoints R index position Y)
  exact h

/-- The retained firing is typed at the original intrinsic child judgment,
including the premise's exact binder context and endpoint sort. -/
theorem childEventAt_judgment (index : Fin R.length)
    (position : Fin (R.get index).premises.length)
    (Y : SubstitutionModel R A)
    (X : Base A)
    (input : (Bundle (authoredPremises R index Y)).obj X) :
    eventJudgment R (childEventAt R index position Y X input) =
      childJudgment R A
        (OccurrenceAt.toInstance R index
          ((assignment (authoredPremises R index Y)).app X input))
        position := by
  let occurrence :=
    (assignment (authoredPremises R index Y)).app X input
  let judgment :=
    childJudgment R A (OccurrenceAt.toInstance R index occurrence)
      position
  have same := childEventAt_endpoints R index position Y X input
  change
      ((⟨(childEventAt R index position Y X input).1,
        (childEventAt R index position Y X input).2.1.1⟩,
        ⟨(childEventAt R index position Y X input).1,
          (childEventAt R index position Y X input).2.1.2⟩) :
        (Σ s : S.Srt,
          A.substitution.Carrier
            (((R.get index).premises.get position).binders ++
              X.unop.context) s) ×
        (Σ s : S.Srt,
          A.substitution.Carrier
            (((R.get index).premises.get position).binders ++
              X.unop.context) s)) =
      (⟨judgment.2.1, judgment.2.2.1⟩,
        ⟨judgment.2.1, judgment.2.2.2⟩) at same
  exact eventJudgment_eq_of_endpointPair R
    (childEventAt R index position Y X input)
    judgment.2.1 judgment.2.2.1 judgment.2.2.2 same

/-- Reindexing a retained authored child firing along an ambient
substitution reindexes its event beneath the same premise-local binders. -/
theorem childEventAt_reindex (index : Fin R.length)
    (position : Fin (R.get index).premises.length)
    (Y : SubstitutionModel R A)
    {X Z : Base A} (f : X ⟶ Z)
    (input : (Bundle (authoredPremises R index Y)).obj X) :
    mapModelEvent R Y
        (Quiver.Hom.op
          (extendScope A
            ((R.get index).premises.get position).binders f.unop))
        (childEventAt R index position Y X input) =
      childEventAt R index position Y Z
        ((Bundle (authoredPremises R index Y)).map f input) := by
  have natural := (authoredChildFiring R index position Y).naturality f
  have pointwise := ConcreteCategory.congr_hom natural input
  exact pointwise.symm

/-- A lawful interpretation transports the selected retained firing under
the premise's own binder extension, at its original authored position. -/
theorem childEventAt_mapModel (index : Fin R.length)
    (position : Fin (R.get index).premises.length)
    {Y Z : SubstitutionModel R A}
    (h : SubstitutionModel.Hom R Y Z)
    (X : Base A)
    (input : (Bundle (authoredPremises R index Y)).obj X) :
    (mapModelEvents R h).app
        (Opposite.op (concat A.substitution.toClone
          (ContextObject.ofList A.substitution.toClone
            ((R.get index).premises.get position).binders) X.unop))
        (childEventAt R index position Y X input) =
      childEventAt R index position Z X
        ((authoredBundleMap R index h).app X input) := by
  have hmap := congrArg (fun transformation => transformation.app X)
    (authoredChildFiring_map R index position h)
  have pointwise := ConcreteCategory.congr_hom hmap input
  exact pointwise.symm

/-- The shared authored rule occurrence reindexes by the same contextual
substitution as all its premise firings. -/
theorem bundleOccurrenceAt_reindex (index : Fin R.length)
    (Y : SubstitutionModel R A)
    {X Z : Base A} (f : X ⟶ Z)
    (input : (Bundle (authoredPremises R index Y)).obj X) :
    (assignment (authoredPremises R index Y)).app Z
        ((Bundle (authoredPremises R index Y)).map f input) =
      reindexOccurrence R index f
        ((assignment (authoredPremises R index Y)).app X input) := by
  have natural := (assignment (authoredPremises R index Y)).naturality f
  exact ConcreteCategory.congr_hom natural input

/-- The target recursive judgment of a reindexed bundle is the original
child judgment with the ambient substitution lifted under that child's
local binders. -/
theorem childJudgment_bundle_reindex (index : Fin R.length)
    (position : Fin (R.get index).premises.length)
    (Y : SubstitutionModel R A)
    {X Z : Base A} (f : X ⟶ Z)
    (input : (Bundle (authoredPremises R index Y)).obj X) :
    childJudgment R A
        (OccurrenceAt.toInstance R index
          ((assignment (authoredPremises R index Y)).app Z
            ((Bundle (authoredPremises R index Y)).map f input)))
        position =
      substJudgment
        (childJudgment R A
          (OccurrenceAt.toInstance R index
            ((assignment (authoredPremises R index Y)).app X input))
          position)
        (A.substitution.liftEnvironment
          (fromPositions X.unop.context f.unop)
          ((R.get index).premises.get position).binders) := by
  rw [bundleOccurrenceAt_reindex R index Y f input]
  exact childJudgment_reindex R index position f
    ((assignment (authoredPremises R index Y)).app X input)

/-- Reindexing the shared occurrence substitutes the authored conclusion
judgment by the ambient environment, without binder extension. -/
theorem conclusionJudgment_bundle_reindex (index : Fin R.length)
    (Y : SubstitutionModel R A)
    {X Z : Base A} (f : X ⟶ Z)
    (input : (Bundle (authoredPremises R index Y)).obj X) :
    conclusionJudgment R A
        (OccurrenceAt.toInstance R index
          ((assignment (authoredPremises R index Y)).app Z
            ((Bundle (authoredPremises R index Y)).map f input))) =
      substJudgment
        (conclusionJudgment R A
          (OccurrenceAt.toInstance R index
            ((assignment (authoredPremises R index Y)).app X input)))
        (fromPositions X.unop.context f.unop) := by
  rw [bundleOccurrenceAt_reindex R index Y f input]
  change conclusionJudgment R A
      (Instance.subst R
        (OccurrenceAt.toInstance R index
          ((assignment (authoredPremises R index Y)).app X input))
        (fromPositions X.unop.context f.unop)) = _
  exact conclusionJudgment_subst R
    (OccurrenceAt.toInstance R index
      ((assignment (authoredPremises R index Y)).app X input))
    (fromPositions X.unop.context f.unop)

/-- The reindexed bundle's constructor occurrence is exactly intrinsic
instance substitution, with its authored rule index retained. -/
theorem bundleInstance_reindex (index : Fin R.length)
    (Y : SubstitutionModel R A)
    {X Z : Base A} (f : X ⟶ Z)
    (input : (Bundle (authoredPremises R index Y)).obj X) :
    OccurrenceAt.toInstance R index
        ((assignment (authoredPremises R index Y)).app Z
          ((Bundle (authoredPremises R index Y)).map f input)) =
      Instance.subst R
        (OccurrenceAt.toInstance R index
          ((assignment (authoredPremises R index Y)).app X input))
        (fromPositions X.unop.context f.unop) := by
  rw [bundleOccurrenceAt_reindex R index Y f input]
  exact toInstance_reindex R index f
    ((assignment (authoredPremises R index Y)).app X input)

/-- The individual event in a categorical premise bundle supplies the
actual recursive evidence expected by the indexed rule constructor. -/
noncomputable def childEvidenceAt (index : Fin R.length)
    (position : Fin (R.get index).premises.length)
    (Y : SubstitutionModel R A)
    (X : Base A)
    (input : (Bundle (authoredPremises R index Y)).obj X) :
    Y.evidence.carrier ()
      (childJudgment R A
        (OccurrenceAt.toInstance R index
          ((assignment (authoredPremises R index Y)).app X input))
        position) :=
  (eventFiberEquiv R Y
    (childJudgment R A
      (OccurrenceAt.toInstance R index
        ((assignment (authoredPremises R index Y)).app X input))
      position)).symm
    ⟨childEventAt R index position Y X input,
      childEventAt_judgment R index position Y X input⟩

/-- Extraction changes only the dependent judgment index. It returns the
same individual evidence value carried by the selected firing. -/
theorem childEvidenceAt_eq_transport (index : Fin R.length)
    (position : Fin (R.get index).premises.length)
    (Y : SubstitutionModel R A)
    (X : Base A)
    (input : (Bundle (authoredPremises R index Y)).obj X) :
    childEvidenceAt R index position Y X input =
      (childEventAt_judgment R index position Y X input) ▸
        (childEventAt R index position Y X input).2.2 := by
  rfl

theorem childEvidenceAt_heq_raw (index : Fin R.length)
    (position : Fin (R.get index).premises.length)
    (Y : SubstitutionModel R A)
    (X : Base A)
    (input : (Bundle (authoredPremises R index Y)).obj X) :
    HEq (childEvidenceAt R index position Y X input)
      (childEventAt R index position Y X input).2.2 := by
  rw [childEvidenceAt_eq_transport]
  exact heq_transport (childEventAt_judgment R index position Y X input)
    (childEventAt R index position Y X input).2.2

/-- A dependent evidence map respects equality of judgments and
heterogeneous equality of the individual firing evidence. -/
theorem evidenceHom_heq {Y Z : SubstitutionModel R A}
    (h : SubstitutionModel.Hom R Y Z)
    {first second : Judgment A} (sameJudgment : first = second)
    {firstValue : Y.evidence.carrier () first}
    {secondValue : Y.evidence.carrier () second}
    (sameValue : HEq firstValue secondValue) :
    HEq (h.evidence.toFun () first firstValue)
      (h.evidence.toFun () second secondValue) := by
  cases sameJudgment
  cases sameValue
  rfl

/-- Mapping an event maps its exact dependent evidence component. -/
theorem modelEventMap_evidence_heq {Y Z : SubstitutionModel R A}
    (h : SubstitutionModel.Hom R Y Z)
    (X : Base A) (event : ModelEvent R Y X.unop.context) :
    HEq ((mapModelEvents R h).app X event).2.2
      (h.evidence.toFun () (eventJudgment R event) event.2.2) := by
  rcases event with ⟨sort, ⟨source, target⟩, evidence⟩
  rfl

/-- The authored full-bundle map transports the actual recursive evidence
used by the rule constructor, for each original premise position. -/
theorem childEvidenceAt_mapModel (index : Fin R.length)
    (position : Fin (R.get index).premises.length)
    {Y Z : SubstitutionModel R A}
    (h : SubstitutionModel.Hom R Y Z)
    (X : Base A)
    (input : (Bundle (authoredPremises R index Y)).obj X) :
    let mappedInput := (authoredBundleMap R index h).app X input
    HEq
      (h.evidence.toFun ()
        (childJudgment R A
          (OccurrenceAt.toInstance R index
            ((assignment (authoredPremises R index Y)).app X input))
          position)
        (childEvidenceAt R index position Y X input))
      (childEvidenceAt R index position Z X mappedInput) := by
  let mappedInput := (authoredBundleMap R index h).app X input
  let extended : Base A :=
    Opposite.op (concat A.substitution.toClone
      (ContextObject.ofList A.substitution.toClone
        ((R.get index).premises.get position).binders) X.unop)
  let oldEvent := childEventAt R index position Y X input
  let newEvent := childEventAt R index position Z X mappedInput
  have sameEvent : (mapModelEvents R h).app extended oldEvent =
      newEvent := childEventAt_mapModel R index position h X input
  have mappedChild : HEq
      (h.evidence.toFun ()
        (childJudgment R A
          (OccurrenceAt.toInstance R index
            ((assignment (authoredPremises R index Y)).app X input))
          position)
        (childEvidenceAt R index position Y X input))
      (h.evidence.toFun () (eventJudgment R oldEvent) oldEvent.2.2) :=
    evidenceHom_heq R h
      (childEventAt_judgment R index position Y X input).symm
      (childEvidenceAt_heq_raw R index position Y X input)
  exact mappedChild.trans
    ((modelEventMap_evidence_heq R h extended oldEvent).symm.trans
      ((eventEvidence_heq_of_eq R sameEvent).trans
        (childEvidenceAt_heq_raw R index position Z X mappedInput).symm))

/-- Extracting one premise's evidence commutes with ambient substitution
lifted under that premise's binder list. This is the exact recursive-input
law needed for the rule constructor's substitution equation. -/
theorem childEvidenceAt_reindex (index : Fin R.length)
    (position : Fin (R.get index).premises.length)
    (Y : SubstitutionModel R A)
    {X Z : Base A} (f : X ⟶ Z)
    (input : (Bundle (authoredPremises R index Y)).obj X) :
    let oldOccurrence :=
      (assignment (authoredPremises R index Y)).app X input
    let newInput := (Bundle (authoredPremises R index Y)).map f input
    let newOccurrence :=
      (assignment (authoredPremises R index Y)).app Z newInput
    let oldJudgment := childJudgment R A
      (OccurrenceAt.toInstance R index oldOccurrence) position
    let newJudgment := childJudgment R A
      (OccurrenceAt.toInstance R index newOccurrence) position
    Y.act oldJudgment (childEvidenceAt R index position Y X input)
        (A.substitution.liftEnvironment
          (fromPositions X.unop.context f.unop)
          ((R.get index).premises.get position).binders)
        newJudgment
        (childJudgment_bundle_reindex R index position Y f input).symm =
      childEvidenceAt R index position Y Z newInput := by
  let scope := ((R.get index).premises.get position).binders
  let newInput := (Bundle (authoredPremises R index Y)).map f input
  let oldEvent := childEventAt R index position Y X input
  let newEvent := childEventAt R index position Y Z newInput
  let extended :
      (Opposite.op (ContextObject.ofList A.substitution.toClone
        (scope ++ X.unop.context)) : Base A) ⟶
      (Opposite.op (ContextObject.ofList A.substitution.toClone
        (scope ++ Z.unop.context)) : Base A) :=
    Quiver.Hom.op (extendScope A scope f.unop)
  let oldJudgment := childJudgment R A
    (OccurrenceAt.toInstance R index
      ((assignment (authoredPremises R index Y)).app X input)) position
  let newJudgment := childJudgment R A
    (OccurrenceAt.toInstance R index
      ((assignment (authoredPremises R index Y)).app Z newInput)) position
  have sameEnv :
      fromPositions (S := S) (scope ++ X.unop.context)
        (extendScope A scope f.unop) =
        A.substitution.liftEnvironment
          (fromPositions X.unop.context f.unop) scope :=
    fromPositions_extendScope (S := S) A scope f.unop
  have sameEvent : mapModelEvent R Y extended oldEvent = newEvent :=
    childEventAt_reindex R index position Y f input
  have sameTarget :
      eventJudgment R (mapModelEvent R Y extended oldEvent) =
        newJudgment :=
    (congrArg (eventJudgment R) sameEvent).trans
      (childEventAt_judgment R index position Y Z newInput)
  have sameAction : HEq
      (Y.act oldJudgment (childEvidenceAt R index position Y X input)
        (A.substitution.liftEnvironment
          (fromPositions X.unop.context f.unop) scope)
        newJudgment
        (childJudgment_bundle_reindex R index position Y f input).symm)
      (Y.act (eventJudgment R oldEvent) oldEvent.2.2
        (fromPositions (S := S) (scope ++ X.unop.context)
          (extendScope A scope f.unop))
        (eventJudgment R (mapModelEvent R Y extended oldEvent))
        (eventJudgment_mapModelEvent R Y extended oldEvent).symm) :=
    Y.toAction.act_heq
      (childEventAt_judgment R index position Y X input).symm
      (childEvidenceAt_heq_raw R index position Y X input)
      (heq_of_eq sameEnv.symm)
      sameTarget.symm
      (childJudgment_bundle_reindex R index position Y f input).symm
      (eventJudgment_mapModelEvent R Y extended oldEvent).symm
  have sameRaw : HEq
      (mapModelEvent R Y extended oldEvent).2.2 newEvent.2.2 :=
    eventEvidence_heq_of_eq R sameEvent
  exact eq_of_heq
    (sameAction.trans
      ((eventEvidence_map_heq R Y extended oldEvent).symm.trans
        (sameRaw.trans
          (childEvidenceAt_heq_raw R index position Y Z newInput).symm)))

/-- At each ambient context, the existing indexed rule algebra fires on
precisely the evidence extracted from the authored ordered premise bundle.
This is the pointwise construction underlying the required natural rule
action; naturality under substitution remains a separate theorem. -/
noncomputable def ruleFireAt (index : Fin R.length)
    (Y : SubstitutionModel R A)
    (X : Base A)
    (input : (Bundle (authoredPremises R index Y)).obj X) :
    ModelEvent R Y X.unop.context := by
  let occurrence :=
    (assignment (authoredPremises R index Y)).app X input
  let selected := OccurrenceAt.toInstance R index occurrence
  let judgment := conclusionJudgment R A selected
  exact ⟨judgment.2.1, judgment.2.2,
    Y.evidence.rules.act () judgment
      ⟨⟨selected, rfl⟩,
        fun position => childEvidenceAt R index position Y X input⟩⟩

/-- The pointwise rule firing has the declared source, target and result
sort of its exact authored occurrence. -/
theorem ruleFireAt_judgment (index : Fin R.length)
    (Y : SubstitutionModel R A)
    (X : Base A)
    (input : (Bundle (authoredPremises R index Y)).obj X) :
    eventJudgment R (ruleFireAt R index Y X input) =
      conclusionJudgment R A
        (OccurrenceAt.toInstance R index
          ((assignment (authoredPremises R index Y)).app X input)) := by
  rfl

/-- At each context, the constructed firing observes the authored
conclusion pair. The remaining categorical obligation is naturality of
this pointwise construction under contextual substitution. -/
theorem ruleFireAt_endpoints (index : Fin R.length)
    (Y : SubstitutionModel R A)
    (X : Base A)
    (input : (Bundle (authoredPremises R index Y)).obj X) :
    (modelEndpointPair R Y).app X (ruleFireAt R index Y X input) =
      (conclusionEndpointsNat R index).app X
        ((assignment (authoredPremises R index Y)).app X input) := by
  rfl

/-- Substitution of the constructed rule evidence is governed by the
model's rule-constructor law and the binder-local substitution law for
every ordered child. -/
theorem ruleFireAt_evidence_reindex (index : Fin R.length)
    (Y : SubstitutionModel R A)
    {X Z : Base A} (f : X ⟶ Z)
    (input : (Bundle (authoredPremises R index Y)).obj X) :
    let newInput := (Bundle (authoredPremises R index Y)).map f input
    let oldOccurrence :=
      (assignment (authoredPremises R index Y)).app X input
    let newOccurrence :=
      (assignment (authoredPremises R index Y)).app Z newInput
    Y.act
        (conclusionJudgment R A
          (OccurrenceAt.toInstance R index oldOccurrence))
        (ruleFireAt R index Y X input).2.2
        (fromPositions X.unop.context f.unop)
        (conclusionJudgment R A
          (OccurrenceAt.toInstance R index newOccurrence))
        (conclusionJudgment_bundle_reindex R index Y f input).symm =
      (ruleFireAt R index Y Z newInput).2.2 := by
  let oldOccurrence :=
    (assignment (authoredPremises R index Y)).app X input
  let newInput := (Bundle (authoredPremises R index Y)).map f input
  let newOccurrence :=
    (assignment (authoredPremises R index Y)).app Z newInput
  let selected := OccurrenceAt.toInstance R index oldOccurrence
  let σ := fromPositions X.unop.context f.unop
  let oldJudgment := conclusionJudgment R A selected
  let newJudgment :=
    conclusionJudgment R A (OccurrenceAt.toInstance R index newOccurrence)
  have hconstructor := Y.act_rules
    (⟨selected, rfl⟩ : Shape R A oldJudgment)
    (fun position => childEvidenceAt R index position Y X input)
    σ newJudgment
    (conclusionJudgment_bundle_reindex R index Y f input).symm
  have hCast : ∀ (pf : conclusionJudgment R A selected = oldJudgment),
      castEnv pf σ = σ :=
    fun pf => eq_of_heq (castEnv_heq pf σ)
  simp only [hCast] at hconstructor
  change Y.act oldJudgment
      (Y.evidence.rules.act () oldJudgment
        ⟨⟨selected, rfl⟩,
          fun position => childEvidenceAt R index position Y X input⟩)
      σ newJudgment
      (conclusionJudgment_bundle_reindex R index Y f input).symm =
    Y.evidence.rules.act () newJudgment
      ⟨⟨OccurrenceAt.toInstance R index newOccurrence, rfl⟩,
        fun position => childEvidenceAt R index position Y Z newInput⟩
  refine hconstructor.trans ?_
  have hInstance : ∀ (pf : conclusionJudgment R A selected = oldJudgment),
      Instance.subst R selected (castEnv pf σ) =
        OccurrenceAt.toInstance R index newOccurrence := by
    intro pf
    rw [hCast pf]
    exact (bundleInstance_reindex R index Y f input).symm
  refine rulesAct_congr_instance R Y.evidence (hInstance _) _ _ _ _ ?_
  intro position otherPosition samePosition
  cases samePosition
  refine HEq.trans ?_
    (heq_of_eq (childEvidenceAt_reindex R index position Y f input))
  refine Y.toAction.act_heq rfl HEq.rfl HEq.rfl
    (childJudgment_congr R (hInstance _) position position HEq.rfl) _ _

/-- Firing an authored rule commutes with contextual substitution, including
every retained premise firing under its own binder extension. -/
theorem ruleFireAt_reindex (index : Fin R.length)
    (Y : SubstitutionModel R A)
    {X Z : Base A} (f : X ⟶ Z)
    (input : (Bundle (authoredPremises R index Y)).obj X) :
    mapModelEvent R Y f (ruleFireAt R index Y X input) =
      ruleFireAt R index Y Z
        ((Bundle (authoredPremises R index Y)).map f input) := by
  let newInput := (Bundle (authoredPremises R index Y)).map f input
  let oldEvent := ruleFireAt R index Y X input
  let newEvent := ruleFireAt R index Y Z newInput
  have hJudgment : eventJudgment R (mapModelEvent R Y f oldEvent) =
      eventJudgment R newEvent := by
    calc
      eventJudgment R (mapModelEvent R Y f oldEvent) =
          substJudgment (eventJudgment R oldEvent)
            (fromPositions X.unop.context f.unop) :=
              eventJudgment_mapModelEvent R Y f oldEvent
      _ = eventJudgment R newEvent := by
        change substJudgment
          (conclusionJudgment R A
            (OccurrenceAt.toInstance R index
              ((assignment (authoredPremises R index Y)).app X input)))
          (fromPositions X.unop.context f.unop) =
          conclusionJudgment R A
            (OccurrenceAt.toInstance R index
              ((assignment (authoredPremises R index Y)).app Z newInput))
        exact (conclusionJudgment_bundle_reindex R index Y f input).symm
  have hAction : HEq
      (Y.act (eventJudgment R oldEvent) oldEvent.2.2
        (fromPositions X.unop.context f.unop)
        (eventJudgment R (mapModelEvent R Y f oldEvent))
        (eventJudgment_mapModelEvent R Y f oldEvent).symm)
      (Y.act (eventJudgment R oldEvent) oldEvent.2.2
        (fromPositions X.unop.context f.unop)
        (eventJudgment R newEvent)
        (conclusionJudgment_bundle_reindex R index Y f input).symm) :=
    Y.toAction.act_heq rfl HEq.rfl HEq.rfl
      hJudgment _ _
  exact modelEvent_ext R hJudgment
    ((eventEvidence_map_heq R Y f oldEvent).trans
      (hAction.trans
        (heq_of_eq (ruleFireAt_evidence_reindex R index Y f input))))

/-- Every lawful substitution-operational model interprets an authored
conditional rule as a natural action from its ordered scoped premise bundle
to an individual conclusion event. -/
noncomputable def authoredRuleAction (index : Fin R.length)
    (Y : SubstitutionModel R A) : AuthoredRuleAction R index Y where
  fire := {
    app X := TypeCat.ofHom (ruleFireAt R index Y X)
    naturality X Z f := by
      apply ConcreteCategory.hom_ext
      intro input
      exact (ruleFireAt_reindex R index Y f input).symm
  }
  endpoint_law := by
    apply NatTrans.ext
    funext X
    apply ConcreteCategory.hom_ext
    intro input
    exact ruleFireAt_endpoints R index Y X input

/-- Equal constructor occurrences and equal recursive evidence produce the
same firing even when their dependent judgment indices are presented by
different equalities. -/
theorem ruleConstructor_heq_instance (Y : SubstitutionModel R A)
    {first second : Instance R A} (same : first = second)
    (firstChildren : ∀ position : Fin (R.get first.index).premises.length,
      Y.evidence.carrier () (childJudgment R A first position))
    (secondChildren : ∀ position : Fin (R.get second.index).premises.length,
      Y.evidence.carrier () (childJudgment R A second position))
    (children : ∀ firstPosition secondPosition,
      HEq firstPosition secondPosition →
        HEq (firstChildren firstPosition)
          (secondChildren secondPosition)) :
    HEq
      (Y.evidence.rules.act () (conclusionJudgment R A first)
        ⟨⟨first, rfl⟩, firstChildren⟩)
      (Y.evidence.rules.act () (conclusionJudgment R A second)
        ⟨⟨second, rfl⟩, secondChildren⟩) := by
  cases same
  have childrenEq : firstChildren = secondChildren :=
    funext fun position => eq_of_heq
      (children position position HEq.rfl)
  cases childrenEq
  rfl

/-- A model map preserves the authored constructor whenever it maps each
retained scoped premise firing. The remaining categorical comparison is to
derive this precise child condition from the authored bundle map. -/
theorem ruleFireAt_mapModel_of_children (index : Fin R.length)
    {Y Z : SubstitutionModel R A}
    (h : SubstitutionModel.Hom R Y Z)
    (X : Base A)
    (inputY : (Bundle (authoredPremises R index Y)).obj X)
    (inputZ : (Bundle (authoredPremises R index Z)).obj X)
    (sameOccurrence :
      (assignment (authoredPremises R index Y)).app X inputY =
        (assignment (authoredPremises R index Z)).app X inputZ)
    (sameChildren : ∀ position : Fin (R.get index).premises.length,
      HEq
        (h.evidence.toFun ()
          (childJudgment R A
            (OccurrenceAt.toInstance R index
              ((assignment (authoredPremises R index Y)).app X inputY))
            position)
          (childEvidenceAt R index position Y X inputY))
        (childEvidenceAt R index position Z X inputZ)) :
    (mapModelEvents R h).app X (ruleFireAt R index Y X inputY) =
      ruleFireAt R index Z X inputZ := by
  have sameInstance :
      OccurrenceAt.toInstance R index
          ((assignment (authoredPremises R index Y)).app X inputY) =
        OccurrenceAt.toInstance R index
          ((assignment (authoredPremises R index Z)).app X inputZ) :=
    congrArg (OccurrenceAt.toInstance R index) sameOccurrence
  have sameJudgment :
      eventJudgment R ((mapModelEvents R h).app X
        (ruleFireAt R index Y X inputY)) =
      eventJudgment R (ruleFireAt R index Z X inputZ) := by
    change conclusionJudgment R A
        (OccurrenceAt.toInstance R index
          ((assignment (authoredPremises R index Y)).app X inputY)) =
      conclusionJudgment R A
        (OccurrenceAt.toInstance R index
          ((assignment (authoredPremises R index Z)).app X inputZ))
    exact congrArg (conclusionJudgment R A) sameInstance
  apply modelEvent_ext R sameJudgment
  have hconstructor := h.evidence.commutes ()
    (conclusionJudgment R A
      (OccurrenceAt.toInstance R index
        ((assignment (authoredPremises R index Y)).app X inputY)))
    ⟨⟨OccurrenceAt.toInstance R index
        ((assignment (authoredPremises R index Y)).app X inputY), rfl⟩,
      fun position => childEvidenceAt R index position Y X inputY⟩
  refine (heq_of_eq hconstructor).trans ?_
  refine ruleConstructor_heq_instance R Z sameInstance _ _ ?_
  intro position otherPosition samePosition
  cases samePosition
  exact sameChildren position

/-- Every lawful model interpretation commutes with firing a complete
authored rule input, including all ordered binder-local premise evidence. -/
theorem ruleFireAt_mapModel (index : Fin R.length)
    {Y Z : SubstitutionModel R A}
    (h : SubstitutionModel.Hom R Y Z)
    (X : Base A)
    (input : (Bundle (authoredPremises R index Y)).obj X) :
    (mapModelEvents R h).app X (ruleFireAt R index Y X input) =
      ruleFireAt R index Z X
        ((authoredBundleMap R index h).app X input) := by
  apply ruleFireAt_mapModel_of_children R index h X input
    ((authoredBundleMap R index h).app X input)
  · exact (authoredBundleMap_assignment_at R index h X input).symm
  · intro position
    exact childEvidenceAt_mapModel R index position h X input

/-- The constructed authored rule action is natural in ordinary
substitution-operational model maps. Coverage and injectivity of target
events are not required. -/
theorem authoredRuleAction_map (index : Fin R.length)
    {Y Z : SubstitutionModel R A}
    (h : SubstitutionModel.Hom R Y Z) :
    authoredBundleMap R index h ≫ (authoredRuleAction R index Z).fire =
      (authoredRuleAction R index Y).fire ≫ mapModelEvents R h := by
  apply NatTrans.ext
  funext X
  apply ConcreteCategory.hom_ext
  intro input
  exact (ruleFireAt_mapModel R index h X input).symm

/-- Retained event presheaves and their evidence-preserving maps form a
functor on lawful substitution-operational models. -/
noncomputable def modelEventsFunctor :
    SubstitutionModel R A ⥤ (Base A ⥤ Type u) where
  obj Y := modelEvents R Y
  map h := mapModelEvents R h
  map_id Y := by
    ext X event
    rfl
  map_comp f g := by
    ext X event
    rfl

/-- The actual authored conditional-rule constructor is natural both in
contextual substitution and in interpretation maps between lawful models.
Its domain retains all ordered, binder-local firing witnesses. -/
noncomputable def authoredRuleActionNatural (index : Fin R.length) :
    authoredBundleFunctor R (A := A) index ⟶
      modelEventsFunctor R (A := A) :=
  {
    app Y := (authoredRuleAction R index Y).fire
    naturality _ _ h := authoredRuleAction_map R index h
  }

end Mettapedia.OSLF.Binding.IntrinsicRuleActionComparison

#print axioms Mettapedia.OSLF.Binding.IntrinsicRuleActionComparison.eventJudgment_eq_of_endpointPair
#print axioms Mettapedia.OSLF.Binding.IntrinsicRuleActionComparison.childEventAt_judgment
#print axioms Mettapedia.OSLF.Binding.IntrinsicRuleActionComparison.childEventAt_reindex
#print axioms Mettapedia.OSLF.Binding.IntrinsicRuleActionComparison.childEvidenceAt
#print axioms Mettapedia.OSLF.Binding.IntrinsicRuleActionComparison.ruleFireAt
#print axioms Mettapedia.OSLF.Binding.IntrinsicRuleActionComparison.ruleFireAt_reindex
#print axioms Mettapedia.OSLF.Binding.IntrinsicRuleActionComparison.authoredRuleAction
#print axioms Mettapedia.OSLF.Binding.IntrinsicRuleActionComparison.ruleFireAt_mapModel_of_children
#print axioms Mettapedia.OSLF.Binding.IntrinsicRuleActionComparison.childEvidenceAt_mapModel
#print axioms Mettapedia.OSLF.Binding.IntrinsicRuleActionComparison.authoredRuleAction_map
#print axioms Mettapedia.OSLF.Binding.IntrinsicRuleActionComparison.authoredRuleActionNatural
