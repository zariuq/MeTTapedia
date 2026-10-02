import Mettapedia.OSLF.Syntax.IntrinsicScopedOperationalPresheafBoundContexts
import Mettapedia.OSLF.Syntax.IntrinsicScopedOperationalPresheafRulePoints
import Mettapedia.OSLF.Syntax.IntrinsicScopedOperationalPresheafPremisePoints
import Mettapedia.OSLF.Syntax.IntrinsicScopedOperationalPresheafNaturalEvidence
import Mettapedia.OSLF.Syntax.IntrinsicScopedOperationalPresheafEventPowers

/-!
# Retained premise functions at actual operational presheaf points

The canonical point opening an ordered binder context commutes with every
ambient clone substitution. Bound evidence functions retain their original
values, with their endpoints evaluated in the same extended context.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedOperationalPresheafRuleFunctions

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.CartesianMonoidalCategory
open Mettapedia.GSLT.LanguageDef.MultiSortedClone
open IntrinsicScopedConditionalPresheaf (Base)
open IntrinsicScopedOperationalPresheafPrograms (target model contextAtEquiv contextAtEquiv_natural)
open IntrinsicScopedOperationalPresheafReadback (extendedStage canonicalPoint)
open MultiBinderPresheaf
open IntrinsicScopedOperationalPresheafEvents (sortEvents)
open IntrinsicScopedJudgmentAction (JudgmentAction)
open AuthoredPositionedRulePolynomial (Judgment)
open IntrinsicScopedOperationalPresheafBoundContexts (boundContextArrow boundContextArrow_value)
open IntrinsicScopedLocalPolynomial (LocalRule Instance childJudgment)
open IntrinsicScopedOperationalPresheafRulePoints (occurrenceStage pointInstance)

universe u
variable {S : Signature} (A : BindingCloneAlgebra.Algebra.{u} S)

/-- Opening the actual ordered binder variables is natural at every ambient stage. -/
theorem canonicalPoint_natural {Z : target A} (bs : Ctx S)
    {X Y : Base A} (f : X ⟶ Y) (point : Z.obj X) :
    (((model A).ctx bs ⊗ Z).map (Quiver.Hom.op (extendScope A bs f.unop)))
        (canonicalPoint A bs X point) =
      canonicalPoint A bs Y (Z.map f point) := by
  apply Prod.ext
  · apply (contextAtEquiv A bs (extendedStage A bs Y)).injective
    change contextAtEquiv A bs (extendedStage A bs Y)
        (((model A).ctx bs).map (Quiver.Hom.op (extendScope A bs f.unop))
          ((contextAtEquiv A bs (extendedStage A bs X)).symm
            (fstProjection A.substitution.toClone _ _))) = _
    have natural := contextAtEquiv_natural A bs
      (Quiver.Hom.op (extendScope A bs f.unop))
      ((contextAtEquiv A bs (extendedStage A bs X)).symm
        (fstProjection A.substitution.toClone _ _))
    have represented := congrArg
      (fun assignment => (binders A bs).map (Quiver.Hom.op (extendScope A bs f.unop)) assignment)
      ((contextAtEquiv A bs (extendedStage A bs X)).apply_symm_apply
        (fstProjection A.substitution.toClone _ _))
    exact natural.trans (represented.trans ((extendScope_fst A bs f.unop).trans
      ((contextAtEquiv A bs (extendedStage A bs Y)).apply_symm_apply
        (fstProjection A.substitution.toClone _ _)).symm))
  · change Z.map (Quiver.Hom.op (extendScope A bs f.unop))
        (Z.map (Quiver.Hom.op (sndProjection A.substitution.toClone _ _)) point) =
      Z.map (Quiver.Hom.op (sndProjection A.substitution.toClone _ _)) (Z.map f point)
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
    apply congrArg (fun arrow => Z.map arrow point)
    apply Quiver.Hom.unop_inj
    exact extendScope_snd A bs f.unop

/-- Both endpoints of a retained sorted event, without discarding its evidence. -/
def sortEventJudgment (Y : JudgmentAction.{u,u} A) {s : S.Srt} (X : Base A)
    (event : (sortEvents Y s).obj X) : Judgment A :=
  ⟨X.unop.context, s,
    (IntrinsicScopedOperationalPresheafEventPowers.sourceSemantic Y s |>.app X event),
    (IntrinsicScopedOperationalPresheafEventPowers.targetSemantic Y s |>.app X event)⟩

/-- The actual evidence in a sorted event belongs to precisely its two retained endpoints. -/
def sortEventEvidence (Y : JudgmentAction.{u,u} A) {s : S.Srt} (X : Base A)
    (event : (sortEvents Y s).obj X) : Y.carrier (sortEventJudgment A Y X event) := by
  rcases event with ⟨⟨sort, pair, evidence⟩, same⟩
  cases same
  exact evidence

/-- Equal retained sorted events retain the same individual evidence through its endpoint indices. -/
theorem sortEventEvidence_congr (Y : JudgmentAction.{u,u} A) {s : S.Srt} (X : Base A)
    {first second : (sortEvents Y s).obj X} (same : first = second) :
    HEq (sortEventEvidence A Y X first) (sortEventEvidence A Y X second) := by
  cases same
  rfl

/-- The represented source evaluates to the original retained source. -/
theorem sortEvent_source (Y : JudgmentAction.{u,u} A) {s : S.Srt} (X : Base A)
    (event : (sortEvents Y s).obj X) :
    IntrinsicScopedConditionalPresheaf.programsAtEquiv A s X
        ((IntrinsicScopedOperationalPresheafEventPowers.source Y s).app X event) =
      (sortEventJudgment A Y X event).2.2.1 := rfl

/-- The represented target evaluates to the original retained target. -/
theorem sortEvent_target (Y : JudgmentAction.{u,u} A) {s : S.Srt} (X : Base A)
    (event : (sortEvents Y s).obj X) :
    IntrinsicScopedConditionalPresheaf.programsAtEquiv A s X
        ((IntrinsicScopedOperationalPresheafEventPowers.target Y s).app X event) =
      (sortEventJudgment A Y X event).2.2.2 := rfl

/-- The complete function of one ordered bound premise, on its actual context product. -/
def boundChild (R : List (LocalRule S)) (Y : JudgmentAction.{u,u} A)
    {Z : target A} (occurrence : Instance R ((model A).stage Z))
    (position : Fin (R.get occurrence.index).2.premises.length)
    (event : IntrinsicScopedOperationalPresheafNaturalEvidence.Evidence (model A)
      (sortEvents Y) (IntrinsicScopedOperationalPresheafEventPowers.source Y)
      (IntrinsicScopedOperationalPresheafEventPowers.target Y) Z
      (childJudgment R ((model A).stage Z) occurrence position)) :
    (model A).ctx ((R.get occurrence.index).2.premises.get position).binders ⊗
        occurrenceStage R occurrence ⟶ sortEvents Y
          (childJudgment R ((model A).stage Z) occurrence position).2.1 :=
  boundContextArrow (model A) ((R.get occurrence.index).2.premises.get position).binders
    occurrence.ambient Z ≫ event.1

/-- A bound premise retains its original generalized source at every point. -/
theorem boundChild_source (R : List (LocalRule S)) (Y : JudgmentAction.{u,u} A)
    {Z : target A} (occurrence : Instance R ((model A).stage Z))
    (position : Fin (R.get occurrence.index).2.premises.length)
    (event : IntrinsicScopedOperationalPresheafNaturalEvidence.Evidence (model A)
      (sortEvents Y) (IntrinsicScopedOperationalPresheafEventPowers.source Y)
      (IntrinsicScopedOperationalPresheafEventPowers.target Y) Z
      (childJudgment R ((model A).stage Z) occurrence position)) :
    boundChild A R Y occurrence position event ≫
        IntrinsicScopedOperationalPresheafEventPowers.source Y _ =
      (childJudgment R ((model A).stage Z) occurrence position).2.2.1.value
        ((model A).ctx ((R.get occurrence.index).2.premises.get position).binders ⊗
          occurrenceStage R occurrence) (snd _ _ ≫ snd _ _)
        ((model A).extendEnv ((R.get occurrence.index).2.premises.get position).binders
          ((model A).genericEnv occurrence.ambient Z)) :=
  (Category.assoc _ _ _).trans ((congrArg
    (boundContextArrow (model A) ((R.get occurrence.index).2.premises.get position).binders
      occurrence.ambient Z ≫ ·) event.2.1).trans
      (boundContextArrow_value (model A) _ _ _))

/-- A bound premise retains its original generalized target under the same binders. -/
theorem boundChild_target (R : List (LocalRule S)) (Y : JudgmentAction.{u,u} A)
    {Z : target A} (occurrence : Instance R ((model A).stage Z))
    (position : Fin (R.get occurrence.index).2.premises.length)
    (event : IntrinsicScopedOperationalPresheafNaturalEvidence.Evidence (model A)
      (sortEvents Y) (IntrinsicScopedOperationalPresheafEventPowers.source Y)
      (IntrinsicScopedOperationalPresheafEventPowers.target Y) Z
      (childJudgment R ((model A).stage Z) occurrence position)) :
    boundChild A R Y occurrence position event ≫
        IntrinsicScopedOperationalPresheafEventPowers.target Y _ =
      (childJudgment R ((model A).stage Z) occurrence position).2.2.2.value
        ((model A).ctx ((R.get occurrence.index).2.premises.get position).binders ⊗
          occurrenceStage R occurrence) (snd _ _ ≫ snd _ _)
        ((model A).extendEnv ((R.get occurrence.index).2.premises.get position).binders
          ((model A).genericEnv occurrence.ambient Z)) :=
  (Category.assoc _ _ _).trans ((congrArg
    (boundContextArrow (model A) ((R.get occurrence.index).2.premises.get position).binders
      occurrence.ambient Z ≫ ·) event.2.2).trans
      (boundContextArrow_value (model A) _ _ _))

/-- A premise function evaluated at its actual canonical binder point. -/
def childAtPoint (R : List (LocalRule S)) (Y : JudgmentAction.{u,u} A)
    {Z : target A} (occurrence : Instance R ((model A).stage Z))
    (position : Fin (R.get occurrence.index).2.premises.length)
    (event : IntrinsicScopedOperationalPresheafNaturalEvidence.Evidence (model A)
      (sortEvents Y) (IntrinsicScopedOperationalPresheafEventPowers.source Y)
      (IntrinsicScopedOperationalPresheafEventPowers.target Y) Z
      (childJudgment R ((model A).stage Z) occurrence position))
    (X : Base A) (point : (occurrenceStage R occurrence).obj X) :
    (sortEvents Y (childJudgment R ((model A).stage Z) occurrence position).2.1).obj
      (extendedStage A ((R.get occurrence.index).2.premises.get position).binders X) :=
  (boundChild A R Y occurrence position event).app
    (extendedStage A ((R.get occurrence.index).2.premises.get position).binders X)
    (canonicalPoint A ((R.get occurrence.index).2.premises.get position).binders X point)

/-- Each evaluated premise supplies evidence at precisely the original rule's child judgment. -/
theorem childAtPoint_judgment (R : List (LocalRule S)) (Y : JudgmentAction.{u,u} A)
    {Z : target A} (occurrence : Instance R ((model A).stage Z))
    (position : Fin (R.get occurrence.index).2.premises.length)
    (event : IntrinsicScopedOperationalPresheafNaturalEvidence.Evidence (model A)
      (sortEvents Y) (IntrinsicScopedOperationalPresheafEventPowers.source Y)
      (IntrinsicScopedOperationalPresheafEventPowers.target Y) Z
      (childJudgment R ((model A).stage Z) occurrence position))
    (X : Base A) (point : (occurrenceStage R occurrence).obj X) :
    sortEventJudgment A Y _ (childAtPoint A R Y occurrence position event X point) =
      childJudgment R A (pointInstance R occurrence X point) position := by
  let bs : Ctx S := ((R.get occurrence.index).2.premises.get position).binders
  let X' := extendedStage A bs X
  let p := canonicalPoint A bs X point
  have source := congrArg
    (fun arrow => IntrinsicScopedConditionalPresheaf.programsAtEquiv A _ X'
      (arrow.app X' p)) (boundChild_source A R Y occurrence position event)
  have target := congrArg
    (fun arrow => IntrinsicScopedConditionalPresheaf.programsAtEquiv A _ X'
      (arrow.app X' p)) (boundChild_target A R Y occurrence position event)
  have source' :
      (sortEventJudgment A Y X' (childAtPoint A R Y occurrence position event X point)).2.2.1 =
        IntrinsicScopedConditionalPresheaf.programsAtEquiv A _ X'
          (((childJudgment R ((model A).stage Z) occurrence position).2.2.1.value
            ((model A).ctx bs ⊗ occurrenceStage R occurrence) (snd _ _ ≫ snd _ _)
            ((model A).extendEnv bs ((model A).genericEnv occurrence.ambient Z))).app X' p) := source
  have target' :
      (sortEventJudgment A Y X' (childAtPoint A R Y occurrence position event X point)).2.2.2 =
        IntrinsicScopedConditionalPresheaf.programsAtEquiv A _ X'
          (((childJudgment R ((model A).stage Z) occurrence position).2.2.2.value
            ((model A).ctx bs ⊗ occurrenceStage R occurrence) (snd _ _ ≫ snd _ _)
            ((model A).extendEnv bs ((model A).genericEnv occurrence.ambient Z))).app X' p) := target
  have paired :
      (sortEventJudgment A Y X' (childAtPoint A R Y occurrence position event X point)).2.2 =
        (IntrinsicScopedConditionalPresheaf.programsAtEquiv A _ X'
          (((childJudgment R ((model A).stage Z) occurrence position).2.2.1.value
            ((model A).ctx bs ⊗ occurrenceStage R occurrence) (snd _ _ ≫ snd _ _)
            ((model A).extendEnv bs ((model A).genericEnv occurrence.ambient Z))).app X' p),
        IntrinsicScopedConditionalPresheaf.programsAtEquiv A _ X'
          (((childJudgment R ((model A).stage Z) occurrence position).2.2.2.value
            ((model A).ctx bs ⊗ occurrenceStage R occurrence) (snd _ _ ≫ snd _ _)
            ((model A).extendEnv bs ((model A).genericEnv occurrence.ambient Z))).app X' p)) :=
    Prod.ext source' target'
  have endpoints := congrArg
    (fun pair => (⟨bs ++ X.unop.context,
      (childJudgment R ((model A).stage Z) occurrence position).2.1, pair⟩ : Judgment A))
      paired
  exact endpoints.trans
    (IntrinsicScopedOperationalPresheafPremisePoints.pointInstance_child R occurrence position X point)

/-- The actual retained child witness required by the original substitution model. -/
def pointChildEvidence (R : List (LocalRule S)) (Y : JudgmentAction.{u,u} A)
    {Z : target A} (occurrence : Instance R ((model A).stage Z))
    (position : Fin (R.get occurrence.index).2.premises.length)
    (event : IntrinsicScopedOperationalPresheafNaturalEvidence.Evidence (model A)
      (sortEvents Y) (IntrinsicScopedOperationalPresheafEventPowers.source Y)
      (IntrinsicScopedOperationalPresheafEventPowers.target Y) Z
      (childJudgment R ((model A).stage Z) occurrence position))
    (X : Base A) (point : (occurrenceStage R occurrence).obj X) :
    Y.carrier (childJudgment R A (pointInstance R occurrence X point) position) :=
  childAtPoint_judgment A R Y occurrence position event X point ▸
    sortEventEvidence A Y _ (childAtPoint A R Y occurrence position event X point)

/-- Every bound premise function is natural under the actual extended ambient substitution. -/
theorem childAtPoint_reindex (R : List (LocalRule S)) (Y : JudgmentAction.{u,u} A)
    {Z : target A} (occurrence : Instance R ((model A).stage Z))
    (position : Fin (R.get occurrence.index).2.premises.length)
    (event : IntrinsicScopedOperationalPresheafNaturalEvidence.Evidence (model A)
      (sortEvents Y) (IntrinsicScopedOperationalPresheafEventPowers.source Y)
      (IntrinsicScopedOperationalPresheafEventPowers.target Y) Z
      (childJudgment R ((model A).stage Z) occurrence position))
    {X V : Base A} (f : X ⟶ V) (point : (occurrenceStage R occurrence).obj X) :
    childAtPoint A R Y occurrence position event V ((occurrenceStage R occurrence).map f point) =
      (sortEvents Y _).map (Quiver.Hom.op
        (extendScope A ((R.get occurrence.index).2.premises.get position).binders f.unop))
        (childAtPoint A R Y occurrence position event X point) := by
  let bs : Ctx S := ((R.get occurrence.index).2.premises.get position).binders
  have natural := (boundChild A R Y occurrence position event).naturality_apply
    (Quiver.Hom.op (extendScope A bs f.unop))
    (canonicalPoint A (Z := occurrenceStage R occurrence) bs X point)
  exact (congrArg ((boundChild A R Y occurrence position event).app (extendedStage A bs V))
    (canonicalPoint_natural A bs f point).symm).trans natural

/-- The sorted event's actual judgment follows the original clone substitution. -/
theorem sortEventJudgment_reindex (Y : JudgmentAction.{u,u} A) {s : S.Srt}
    {X V : Base A} (f : X ⟶ V) (event : (sortEvents Y s).obj X) :
    sortEventJudgment A Y V ((sortEvents Y s).map f event) =
      IntrinsicScopedConditionalSubstitution.substJudgment (sortEventJudgment A Y X event)
        (BindingSubstitutionAlgebra.fromPositions X.unop.context f.unop) := by
  rcases event with ⟨⟨sort, pair, evidence⟩, same⟩
  cases same
  rfl

/-- Reindexing sorted events uses precisely the original evidence action. -/
theorem sortEventEvidence_reindex (Y : JudgmentAction.{u,u} A) {s : S.Srt}
    {X V : Base A} (f : X ⟶ V) (event : (sortEvents Y s).obj X) :
    HEq (sortEventEvidence A Y V ((sortEvents Y s).map f event))
      (Y.act (sortEventJudgment A Y X event) (sortEventEvidence A Y X event)
        (BindingSubstitutionAlgebra.fromPositions X.unop.context f.unop)
        (IntrinsicScopedConditionalSubstitution.substJudgment (sortEventJudgment A Y X event)
          (BindingSubstitutionAlgebra.fromPositions X.unop.context f.unop)) rfl) := by
  rcases event with ⟨⟨sort, pair, evidence⟩, same⟩
  cases same
  rfl

/-- Every ordered child witness is substituted under its own binders by the
original operational action; endpoint transports retain the individual witness. -/
theorem pointChildEvidence_reindex (R : List (LocalRule S)) (Y : JudgmentAction.{u,u} A)
    {Z : target A} (occurrence : Instance R ((model A).stage Z))
    (position : Fin (R.get occurrence.index).2.premises.length)
    (event : IntrinsicScopedOperationalPresheafNaturalEvidence.Evidence (model A)
      (sortEvents Y) (IntrinsicScopedOperationalPresheafEventPowers.source Y)
      (IntrinsicScopedOperationalPresheafEventPowers.target Y) Z
      (childJudgment R ((model A).stage Z) occurrence position))
    {X V : Base A} (f : X ⟶ V) (point : (occurrenceStage R occurrence).obj X) :
    HEq (pointChildEvidence A R Y occurrence position event V
      ((occurrenceStage R occurrence).map f point))
      (Y.act (childJudgment R A (pointInstance R occurrence X point) position)
        (pointChildEvidence A R Y occurrence position event X point)
        (A.substitution.liftEnvironment
          (BindingSubstitutionAlgebra.fromPositions X.unop.context f.unop)
          ((R.get occurrence.index).2.premises.get position).binders)
        (IntrinsicScopedConditionalSubstitution.substJudgment
          (childJudgment R A (pointInstance R occurrence X point) position)
          (A.substitution.liftEnvironment
            (BindingSubstitutionAlgebra.fromPositions X.unop.context f.unop)
            ((R.get occurrence.index).2.premises.get position).binders)) rfl) := by
  let bs : Ctx S := ((R.get occurrence.index).2.premises.get position).binders
  let g : extendedStage A bs X ⟶ extendedStage A bs V :=
    Quiver.Hom.op (extendScope A bs f.unop)
  have value := childAtPoint_reindex A R Y occurrence position event f point
  have source := childAtPoint_judgment A R Y occurrence position event X point
  have raw := sortEventEvidence_reindex A Y g
    (childAtPoint A R Y occurrence position event X point)
  have lifted := fromPositions_extendScope A bs f.unop
  have casted := eq_of_heq (IntrinsicScopedConditionalSubstitution.castEnv_heq source
    (A.substitution.liftEnvironment
      (BindingSubstitutionAlgebra.fromPositions X.unop.context f.unop) bs))
  have targetSame :=
    (congrArg (IntrinsicScopedConditionalSubstitution.substJudgment
      (sortEventJudgment A Y _ (childAtPoint A R Y occurrence position event X point)))
      (lifted.trans casted.symm)).trans
        (IntrinsicScopedConditionalSubstitution.substJudgment_castEnv source
          (A.substitution.liftEnvironment
            (BindingSubstitutionAlgebra.fromPositions X.unop.context f.unop) bs))
  have acted := Y.act_heq source
    (IntrinsicScopedConditionalSubstitution.heq_transport source
      (sortEventEvidence A Y _ (childAtPoint A R Y occurrence position event X point))).symm
    (heq_of_eq lifted)
    targetSame rfl rfl
  have changed :
      HEq (sortEventEvidence A Y _ (childAtPoint A R Y occurrence position event V
        ((occurrenceStage R occurrence).map f point)))
        (sortEventEvidence A Y _ ((sortEvents Y _).map g
          (childAtPoint A R Y occurrence position event X point))) :=
    sortEventEvidence_congr A Y _ value
  exact (IntrinsicScopedConditionalSubstitution.heq_transport
    (childAtPoint_judgment A R Y occurrence position event V
      ((occurrenceStage R occurrence).map f point)) _).trans
        (changed.trans (raw.trans acted))

end Mettapedia.OSLF.Binding.IntrinsicScopedOperationalPresheafRuleFunctions
