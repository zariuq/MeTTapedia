import Mettapedia.OSLF.Syntax.IntrinsicScopedOperationalPresheafRuleFirings
import Mettapedia.OSLF.Syntax.IntrinsicScopedOperationalPresheafRuleSubstitutionPoints
import Mettapedia.OSLF.Syntax.IntrinsicScopedOperationalPresheafBaseAdapter
import Mettapedia.OSLF.Syntax.IntrinsicScopedOperationalPresheafControls
import Mettapedia.OSLF.Syntax.IntrinsicScopedOperationalPresheafCategoricalModel

/-!
# A genuine binder-local firing through the categorical presheaf model

The original Boolean function model's LamCong occurrence is mapped through
the actual binding-clone adapter. Its retained child is represented beneath
the declared term binder, and the implemented categorical rule action keeps
the original distinct false and true endpoints.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedOperationalPresheafCategoricalControls

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.CartesianMonoidalCategory
open IntrinsicScopedLocalActedTypeComparisonControls
open IntrinsicScopedOperationalPresheafControls (algebra liftedModel stage generalizedStage)
open IntrinsicScopedOperationalPresheafPrograms (model powerBodiesIso)
open IntrinsicScopedOperationalPresheafReadback (read)
open IntrinsicScopedOperationalPresheafBaseAdapter
open IntrinsicScopedOperationalPresheafEvents (events eventAtEquiv)
open IntrinsicScopedOperationalPresheafEventPowers (objects sourcePower targetPower)
open IntrinsicScopedOperationalPresheafEventFunctions (stageEventEquiv)
open IntrinsicScopedOperationalPresheafRulePoints (pointInstance occurrenceStage capturedBody)
open IntrinsicScopedOperationalPresheafRuleFirings
open IntrinsicScopedLocalPolynomial (Instance mapInstance childJudgment conclusionJudgment)
open AuthoredPositionedRulePolynomial (Judgment mapJudgment)
open SecondOrderContext
open LambdaContextualRung (sig Srt)

/-- The original LamCong occurrence mapped by the genuine original-clone adapter. -/
def categoricalLamOccurrence : Instance lambdaRules ((model algebra).stage generalizedStage) :=
  mapInstance lambdaRules (baseHom algebra generalizedStage) lamOccurrence

/-- The unique ordered premise is still beneath its declared term binder. -/
theorem categoricalLam_child_context :
    (childJudgment lambdaRules _ categoricalLamOccurrence ⟨0, by decide⟩).1 = [.term] := rfl

private theorem read_one_base {Z : IntrinsicScopedOperationalPresheafPrograms.target algebra}
    (x : algebra.substitution.Carrier [.term] .term) (z : Z.obj stage) :
    read algebra (baseElem algebra (Z := Z) x) stage z = x := by
  have original := read_baseElem algebra (Z := Z) x stage z
  have projections :
      (fun s (v : Var [Srt.term] s) =>
        algebra.substitution.injectVar (injPrefix (Γ := []) [Srt.term] v)) =
      (fun s (v : Var [Srt.term] s) => algebra.substitution.injectVar v) := by
    funext s v
    cases v with
    | zero => rfl
    | succ impossible => nomatch impossible
  exact original.trans ((congrArg (fun env => algebra.substitution.substitute env x)
    projections).trans (algebra.substitution.substitute_identity x))

private theorem read_empty_base {Z : IntrinsicScopedOperationalPresheafPrograms.target algebra}
    (x : algebra.substitution.Carrier [] .term) (z : Z.obj stage) :
    read algebra (baseElem algebra (Z := Z) x) stage z = x := by
  have original := read_baseElem algebra (Z := Z) x stage z
  have projections :
      (fun s (v : Var [] s) => algebra.substitution.injectVar (injPrefix (Γ := []) [] v)) =
      (fun s (v : Var [] s) => algebra.substitution.injectVar v) := by
    funext s v
    nomatch v
  exact original.trans ((congrArg (fun env => algebra.substitution.substitute env x)
    projections).trans (algebra.substitution.substitute_identity x))

/-- The real child witness is retained as a section in its whole binder context. -/
def categoricalLamChildSection : (events liftedModel.toAction [.term] .term).obj stage :=
  (eventAtEquiv liftedModel.toAction [.term] .term stage).symm
    ⟨(childJudgment lambdaRules algebra lamOccurrence ⟨0, by decide⟩).2.2,
      ULift.up (lamChildren ⟨0, by decide⟩)⟩

/-- Yoneda represents that individual child witness without changing its context. -/
def categoricalLamChildArrow : generalizedStage ⟶ events liftedModel.toAction [.term] .term :=
  yonedaEquiv.symm categoricalLamChildSection

/-- Evaluating the represented child recovers its original individual
evidence in the extended term-binder context. -/
theorem categoricalLamChildArrow_recovers :
    categoricalLamChildArrow.app stage (𝟙 stage.unop) = categoricalLamChildSection :=
  yonedaEquiv.apply_symm_apply categoricalLamChildSection

/-- The represented child reads the original binder-dependent source body. -/
theorem categoricalLamChild_source :
    categoricalLamChildArrow ≫ sourcePower liftedModel.toAction [.term] .term =
      (model algebra).elemEquiv (baseElem algebra (Z := generalizedStage)
        (childJudgment lambdaRules algebra lamOccurrence ⟨0, by decide⟩).2.2.1) := by
  apply yonedaEquiv.injective
  change (sourcePower liftedModel.toAction [.term] .term).app stage
      (yonedaEquiv categoricalLamChildArrow) = _
  have represented : yonedaEquiv categoricalLamChildArrow = categoricalLamChildSection :=
    yonedaEquiv.apply_symm_apply _
  rw [represented]
  apply (MultiBinderPresheaf.scopedBodyEquiv algebra stage.unop [.term] .term).injective
  exact (IntrinsicScopedOperationalPresheafEventPowers.sourcePower_body
    liftedModel.toAction [.term] .term stage categoricalLamChildSection).trans
      (read_one_base _ (𝟙 stage.unop)).symm

/-- Its target is the original second binder-dependent body. -/
theorem categoricalLamChild_target :
    categoricalLamChildArrow ≫ targetPower liftedModel.toAction [.term] .term =
      (model algebra).elemEquiv (baseElem algebra (Z := generalizedStage)
        (childJudgment lambdaRules algebra lamOccurrence ⟨0, by decide⟩).2.2.2) := by
  apply yonedaEquiv.injective
  change (targetPower liftedModel.toAction [.term] .term).app stage
      (yonedaEquiv categoricalLamChildArrow) = _
  have represented : yonedaEquiv categoricalLamChildArrow = categoricalLamChildSection :=
    yonedaEquiv.apply_symm_apply _
  rw [represented]
  apply (MultiBinderPresheaf.scopedBodyEquiv algebra stage.unop [.term] .term).injective
  exact (IntrinsicScopedOperationalPresheafEventPowers.targetPower_body
    liftedModel.toAction [.term] .term stage categoricalLamChildSection).trans
      (read_one_base _ (𝟙 stage.unop)).symm

/-- Both checked endpoint clauses place the retained child in the actual
categorical event fiber of the adapted original child judgment. -/
def categoricalLamMappedChild : (objects liftedModel.toAction).StageEvent generalizedStage
    (mapJudgment (baseHom algebra generalizedStage)
      (childJudgment lambdaRules algebra lamOccurrence ⟨0, by decide⟩)) :=
  ⟨categoricalLamChildArrow, categoricalLamChild_source, categoricalLamChild_target⟩

/-- Every actual ordered child position receives that original retained witness. -/
def categoricalLamChildren
    (position : Fin (lambdaRules.get categoricalLamOccurrence.index).2.premises.length) :
    (objects liftedModel.toAction).StageEvent generalizedStage
      (childJudgment lambdaRules _ categoricalLamOccurrence position) := by
  have same : position = ⟨0, by decide⟩ := Fin.eq_zero position
  cases same
  exact (IntrinsicScopedLocalPolynomial.mapInstance_child lambdaRules
    (baseHom algebra generalizedStage) lamOccurrence ⟨0, by decide⟩).symm ▸
      categoricalLamMappedChild

private theorem capture_one {D : Type*} [Category D] [CartesianMonoidalCategory D]
    (M : CategoricalBindingModel.Model sig D) {Z W : D}
    (body : M.ElemOver Z [Srt.term] Srt.term) (m : W ⟶ Z) (ambient : M.Env W []) :
    M.captureBody (dependencies := [Srt.term]) (Γ := []) body m ambient =
      M.restageElem m body := by
  apply CategoricalBindingModel.Model.ElemOver.ext
  funext U point arguments
  change body.value U (point ≫ m)
      (SemanticContextualMetavariables.joinEnvironment
        (F := fun _ s => U ⟶ M.sort s) (Δ := []) arguments (M.restage point ambient)) =
    body.value U (point ≫ m) arguments
  apply congrArg (body.value U (point ≫ m))
  funext s v
  cases v with
  | zero => rfl
  | succ impossible => nomatch impossible

private theorem capture_empty {D : Type*} [Category D] [CartesianMonoidalCategory D]
    (M : CategoricalBindingModel.Model sig D) {Z W : D}
    (body : M.ElemOver Z [] Srt.term) (m : W ⟶ Z) (ambient : M.Env W []) :
    M.captureBody (dependencies := []) (Γ := []) body m ambient = M.restageElem m body := by
  apply CategoricalBindingModel.Model.ElemOver.ext
  funext U point arguments
  change body.value U (point ≫ m)
      (SemanticContextualMetavariables.joinEnvironment
        (F := fun _ s => U ⟶ M.sort s) (Δ := []) arguments (M.restage point ambient)) =
    body.value U (point ≫ m) arguments
  apply congrArg (body.value U (point ≫ m))
  funext s v
  nomatch v

private theorem read_captured_one (x : algebra.substitution.Carrier [.term] .term) :
    read algebra ((model algebra).captureBody (dependencies := [.term]) (Γ := [])
      (baseElem algebra (Z := generalizedStage) x) (snd _ _)
      ((model algebra).genericEnv [] generalizedStage)) stage (PUnit.unit, 𝟙 stage.unop) = x := by
  have captured := capture_one (model algebra) (baseElem algebra (Z := generalizedStage) x)
    (snd _ _) ((model algebra).genericEnv [] generalizedStage)
  exact (congrArg (fun e : (model algebra).ElemOver
      ((model algebra).ctx [] ⊗ generalizedStage) [Srt.term] Srt.term =>
        read algebra e stage (PUnit.unit, 𝟙 stage.unop)) captured).trans
    ((IntrinsicScopedOperationalPresheafReadback.read_restage algebra
      (snd ((model algebra).ctx []) generalizedStage)
      (baseElem algebra (Z := generalizedStage) x) stage (PUnit.unit, 𝟙 stage.unop)).trans
        (read_one_base x (𝟙 stage.unop)))

private theorem read_captured_empty (x : algebra.substitution.Carrier [] .term) :
    read algebra ((model algebra).captureBody (dependencies := []) (Γ := [])
      (baseElem algebra (Z := generalizedStage) x) (snd _ _)
      ((model algebra).genericEnv [] generalizedStage)) stage (PUnit.unit, 𝟙 stage.unop) = x := by
  have captured := capture_empty (model algebra) (baseElem algebra (Z := generalizedStage) x)
    (snd _ _) ((model algebra).genericEnv [] generalizedStage)
  exact (congrArg (fun e : (model algebra).ElemOver
      ((model algebra).ctx [] ⊗ generalizedStage) [] Srt.term =>
        read algebra e stage (PUnit.unit, 𝟙 stage.unop)) captured).trans
    ((IntrinsicScopedOperationalPresheafReadback.read_restage algebra
      (snd ((model algebra).ctx []) generalizedStage)
      (baseElem algebra (Z := generalizedStage) x) stage (PUnit.unit, 𝟙 stage.unop)).trans
        (read_empty_base x (𝟙 stage.unop)))

/-- The actual point keeps the full original occurrence, including both
dependency bodies, all three ordinary metavariables and its declaration address. -/
theorem categoricalLamOccurrence_recovers :
    pointInstance lambdaRules categoricalLamOccurrence stage
      (PUnit.unit, 𝟙 stage.unop) = lamOccurrence := by
  have bodies :
      (pointInstance lambdaRules categoricalLamOccurrence stage
        (PUnit.unit, 𝟙 stage.unop)).valuation = lamOccurrence.valuation := by
    funext index
    rcases index with ⟨i, bound⟩
    change i < 5 at bound
    interval_cases i
    · exact read_captured_one _
    · exact read_captured_one _
    · exact read_captured_empty _
    · exact read_captured_empty _
    · exact read_captured_empty _
  have close :
      (pointInstance lambdaRules categoricalLamOccurrence stage
        (PUnit.unit, 𝟙 stage.unop)).close = lamOccurrence.close := by
    funext s v
    nomatch v
  exact congrArg₂
    (fun valuation close => (⟨lamIndex, [], valuation, close⟩ : Instance lambdaRules algebra))
    bodies close

/-- The actual categorical operational model uses the original Boolean
programs and the original lifted lawful evidence model. -/
def categoricalBoolModel :=
  IntrinsicScopedOperationalPresheafCategoricalModel.categoricalModel
    lambdaRules liftedModel noEquations (fun i => Fin.elim0 i)

/-- The actual categorical rule algebra fires the mapped LamCong occurrence
with its represented original binder-local child. -/
def categoricalLamFiring : categoricalBoolModel.objects.StageEvent generalizedStage
    (conclusionJudgment lambdaRules ((model algebra).stage generalizedStage) categoricalLamOccurrence) :=
  (categoricalBoolModel.rules generalizedStage).act () _
    ⟨⟨categoricalLamOccurrence, rfl⟩, categoricalLamChildren⟩

/-- The categorical rule action compares to the implemented pointwise firing
of the actual original operational model, retaining every ordered child. -/
theorem categoricalLamFiring_comparison :
    stageEventEquiv liftedModel.toAction generalizedStage _ categoricalLamFiring =
      ruleEvidence lambdaRules liftedModel categoricalLamOccurrence
        (fun position => stageEventEquiv liftedModel.toAction generalizedStage _
          (categoricalLamChildren position)) :=
  IntrinsicScopedOperationalPresheafCategoricalModel.actualStage_rules_comparison
    lambdaRules liftedModel generalizedStage _ ⟨categoricalLamOccurrence, rfl⟩ categoricalLamChildren

/-- At the representing point, the actual categorical firing is precisely
the original model's implemented rule firing at the recovered occurrence. -/
theorem categoricalLamFiring_point :
    (stageEventEquiv liftedModel.toAction generalizedStage _ categoricalLamFiring).1.app stage
      (PUnit.unit, 𝟙 stage.unop) =
    pointFire lambdaRules liftedModel categoricalLamOccurrence
      (fun position => stageEventEquiv liftedModel.toAction generalizedStage _
        (categoricalLamChildren position)) stage (PUnit.unit, 𝟙 stage.unop) := by
  exact congrArg
    (fun arrow : occurrenceStage lambdaRules categoricalLamOccurrence ⟶
        IntrinsicScopedOperationalPresheafEvents.sortEvents liftedModel.toAction .term =>
      arrow.app stage (PUnit.unit, 𝟙 stage.unop))
    (congrArg Subtype.val categoricalLamFiring_comparison)

private theorem lifted_evidence_heq {first second : Judgment algebra}
    (same : first = second) (x : liftedModel.carrier first) (y : liftedModel.carrier second) :
    HEq x y := by
  cases same
  change ULift.{1,0} (IntrinsicScopedOperationalPresheafControls.originalModel.carrier first) at x y
  have sameOriginal : x.down = y.down :=
    (EndpointPairs.stageSubsingleton boolPrograms PUnit first).elim x.down y.down
  exact heq_of_eq (ULift.ext _ _ sameOriginal)

/-- The actual categorical firing recovers the original retained LamCong
event, including its individual lifted evidence and ordered endpoints. -/
theorem categoricalLamFiring_recovers :
    (stageEventEquiv liftedModel.toAction generalizedStage _ categoricalLamFiring).1.app stage
      (PUnit.unit, 𝟙 stage.unop) = IntrinsicScopedOperationalPresheafControls.lamEvent := by
  rw [categoricalLamFiring_point]
  apply sortedEvent_ext lambdaRules liftedModel stage
  · exact (pointFire_judgment lambdaRules liftedModel categoricalLamOccurrence _ stage _).trans
      (congrArg (conclusionJudgment lambdaRules algebra) categoricalLamOccurrence_recovers)
  · exact lifted_evidence_heq
      ((pointFire_judgment lambdaRules liftedModel categoricalLamOccurrence _ stage _).trans
        (congrArg (conclusionJudgment lambdaRules algebra) categoricalLamOccurrence_recovers))
      _ IntrinsicScopedOperationalPresheafControls.lamEvidence

/-- Both generalized conclusion endpoints are the actual adapted original
LamCong endpoints, by the adapter's original operation and substitution laws. -/
theorem categoricalLamConclusion_pair :
    (conclusionJudgment lambdaRules ((model algebra).stage generalizedStage)
      categoricalLamOccurrence).2.2 =
    (baseElem algebra (Z := generalizedStage)
        (conclusionJudgment lambdaRules algebra lamOccurrence).2.2.1,
      baseElem algebra (Z := generalizedStage)
        (conclusionJudgment lambdaRules algebra lamOccurrence).2.2.2) := by
  have mapped := IntrinsicScopedLocalPolynomial.mapInstance_conclusion lambdaRules
    (baseHom algebra generalizedStage) lamOccurrence
  have inner := eq_of_heq (Sigma.mk.inj_iff.mp mapped).2
  exact eq_of_heq (Sigma.mk.inj_iff.mp inner).2

/-- The actual categorical source power reads the original LamCong source. -/
theorem categoricalLamFiring_source_body :
    MultiBinderPresheaf.scopedBodyEquiv algebra stage.unop [] .term
      ((categoricalLamFiring.1 ≫ sourcePower liftedModel.toAction [] .term).app stage
        (𝟙 stage.unop)) = (conclusionJudgment lambdaRules algebra lamOccurrence).2.2.1 := by
  have source := congrArg
    (fun arrow : generalizedStage ⟶ IntrinsicScopedOperationalPresheafPrograms.power algebra [] .term =>
      MultiBinderPresheaf.scopedBodyEquiv algebra stage.unop [] .term
        (arrow.app stage (𝟙 stage.unop))) categoricalLamFiring.2.1
  have adapted := congrArg
    (fun e : (model algebra).ElemOver generalizedStage [] Srt.term =>
      read algebra e stage (𝟙 stage.unop))
    (congrArg Prod.fst categoricalLamConclusion_pair)
  exact source.trans (adapted.trans (read_empty_base _ (𝟙 stage.unop)))

/-- The same actual target power reads the original LamCong target. -/
theorem categoricalLamFiring_target_body :
    MultiBinderPresheaf.scopedBodyEquiv algebra stage.unop [] .term
      ((categoricalLamFiring.1 ≫ targetPower liftedModel.toAction [] .term).app stage
        (𝟙 stage.unop)) = (conclusionJudgment lambdaRules algebra lamOccurrence).2.2.2 := by
  have target := congrArg
    (fun arrow : generalizedStage ⟶ IntrinsicScopedOperationalPresheafPrograms.power algebra [] .term =>
      MultiBinderPresheaf.scopedBodyEquiv algebra stage.unop [] .term
        (arrow.app stage (𝟙 stage.unop))) categoricalLamFiring.2.2
  have adapted := congrArg
    (fun e : (model algebra).ElemOver generalizedStage [] Srt.term =>
      read algebra e stage (𝟙 stage.unop))
    (congrArg Prod.snd categoricalLamConclusion_pair)
  exact target.trans (adapted.trans (read_empty_base _ (𝟙 stage.unop)))

/-- The real categorical firing's source evaluates to the false constant function. -/
theorem categoricalLamFiring_source :
    IntrinsicScopedLocalActedTypeComparison.TypeModel.carrierEquiv boolModel [] .term
      (MultiBinderPresheaf.scopedBodyEquiv algebra stage.unop [] .term
        ((categoricalLamFiring.1 ≫ sourcePower liftedModel.toAction [] .term).app stage
          (𝟙 stage.unop))) = (fun _ => false) :=
  (congrArg (IntrinsicScopedLocalActedTypeComparison.TypeModel.carrierEquiv boolModel [] .term)
    categoricalLamFiring_source_body).trans lam_conclusion_source

/-- Its target evaluates to the distinct true constant function. -/
theorem categoricalLamFiring_target :
    IntrinsicScopedLocalActedTypeComparison.TypeModel.carrierEquiv boolModel [] .term
      (MultiBinderPresheaf.scopedBodyEquiv algebra stage.unop [] .term
        ((categoricalLamFiring.1 ≫ targetPower liftedModel.toAction [] .term).app stage
          (𝟙 stage.unop))) = (fun _ => true) :=
  (congrArg (IntrinsicScopedLocalActedTypeComparison.TypeModel.carrierEquiv boolModel [] .term)
    categoricalLamFiring_target_body).trans lam_conclusion_target

/-- The implemented categorical firing cannot collapse its false and true
endpoints into a diagonal event. -/
theorem categoricalLamFiring_not_diagonal :
    categoricalLamFiring.1 ≫ sourcePower liftedModel.toAction [] .term ≠
      categoricalLamFiring.1 ≫ targetPower liftedModel.toAction [] .term := by
  intro same
  have values := congrArg
    (fun arrow : generalizedStage ⟶ IntrinsicScopedOperationalPresheafPrograms.power algebra [] .term =>
      IntrinsicScopedLocalActedTypeComparison.TypeModel.carrierEquiv boolModel [] .term
        (MultiBinderPresheaf.scopedBodyEquiv algebra stage.unop [] .term
          (arrow.app stage (𝟙 stage.unop)))) same
  rw [categoricalLamFiring_source, categoricalLamFiring_target] at values
  have impossible : false = true := congrFun values PUnit.unit
  cases impossible

end Mettapedia.OSLF.Binding.IntrinsicScopedOperationalPresheafCategoricalControls
