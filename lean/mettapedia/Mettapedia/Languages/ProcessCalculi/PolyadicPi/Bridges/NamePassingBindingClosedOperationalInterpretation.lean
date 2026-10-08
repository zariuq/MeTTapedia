import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBindingClosedOperationalNativeReadout
import Mettapedia.CategoryTheory.RelativeClosedInternalCategoryRuleUniversal

/-!
# Native interpretation of authored beta and fetch evidence generators

The actual private/binary COMM beta path and unary COMM fetch path act on
the complete independently declared premise objects. The separately proved
schema readings earn both endpoint equations. This supplies a finite-limit
closed interpretation of the generated operational guest, its complete
original restriction and whole firing-function readings. Primitive-only
admitted comparisons inherit the genuine generated universal property.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBindingClosedOperationalInterpretation

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory RelativeClosedSyntax GeneratedCategory Interpretation
open NamePassingCategoricalCompiler
open NamePassingBindingClosedOperationalPresentation
open NamePassingBindingClosedOperationalNativeReadout
open NamePassingCategoricalOperationalCategory

def nativeReceipt : (origin : Origin) → domain origin ⟶ CategoricalOperationalContinuations.category.edge
  | .beta => betaInput ≫ betaPath
  | .fetch => fetchInput ≫ fetchPath

theorem native_source (origin : Origin) :
    nativeReceipt origin ≫ CategoricalOperationalContinuations.category.source = genericBefore origin := by
  cases origin with
  | beta =>
      simp only [nativeReceipt,Category.assoc,betaPath_source]
      exact beta_before.symm
  | fetch =>
      simp only [nativeReceipt,Category.assoc,fetchPath_source]
      exact fetch_before.symm

theorem native_target (origin : Origin) :
    nativeReceipt origin ≫ CategoricalOperationalContinuations.category.target = genericAfter origin := by
  cases origin with
  | beta =>
      simp only [nativeReceipt,Category.assoc,betaPath_target]
      exact beta_after.symm
  | fetch =>
      simp only [nativeReceipt,Category.assoc,fetchPath_target]
      exact fetch_after.symm

def firing (origin : Origin) : NamePassingBindingClosedOperationalNativeReadout.premise origin ⟶ edges :=
  eqToHom (premise_object origin) ≫ nativeReceipt origin ≫ eqToHom edge_object.symm

theorem local_laws : RelativeClosedInternalCategory.RuleInterpretation.LocalLaws
    vertex categoryMap declarations originalMeanings originalRealization firing where
  source origin := by
    change firing origin ≫ originalFunctor.map
        (classOf (RelativeClosedInternalCategory.NativeCategory.source vertex categoryMap)) =
      originalFunctor.map (classOf (before origin))
    rw [source_arrow,before_arrow]
    simp only [firing,Category.assoc,eqToHom_refl,Category.id_comp]
    simpa only [Category.assoc] using
      congrArg (fun arrow => eqToHom (premise_object origin) ≫ arrow ≫
        NamePassingBindingClosedOperationalCategory.programComparison.inv) (native_source origin)
  target origin := by
    change firing origin ≫ originalFunctor.map
        (classOf (RelativeClosedInternalCategory.NativeCategory.target vertex categoryMap)) =
      originalFunctor.map (classOf (after origin))
    rw [target_arrow,after_arrow]
    simp only [firing,Category.assoc,eqToHom_refl,Category.id_comp]
    simpa only [Category.assoc] using
      congrArg (fun arrow => eqToHom (premise_object origin) ≫ arrow ≫
        NamePassingBindingClosedOperationalCategory.programComparison.inv) (native_target origin)

abbrev assignment := RelativeClosedInternalCategory.RuleInterpretation.assignment
  vertex categoryMap declarations originalMeanings originalRealization firing

theorem realization : Realization signature assignment :=
  RelativeClosedInternalCategory.RuleInterpretation.realization
    vertex categoryMap declarations originalMeanings originalRealization firing local_laws

/-- The admitted generated guest has a genuine finite-limit closed native map. -/
def interpretation : Mettapedia.GSLT.Core.LambdaTheoryMap
    (Mettapedia.GSLT.Core.LambdaTheory.ofCategory (Object signature))
      (Mettapedia.GSLT.Core.LambdaTheory.ofCategory Ambient) where
  functor := Interpretation.functor assignment realization
  preservesFiniteLimits := Interpretation.functor_preservesFiniteLimits assignment realization
  preservesExponentials := Interpretation.functor_closed assignment realization

theorem complete_original_restriction :
    (RelativeClosedInternalCategory.RulePresentation.arrowInclusion vertex categoryMap declarations).functor ⋙
      (RelativeClosedInternalCategory.RulePresentation.equationInclusion vertex categoryMap declarations).functor ⋙
        interpretation.functor = originalFunctor :=
  RelativeClosedInternalCategory.RuleInterpretation.complete_original_restriction
    vertex categoryMap declarations originalMeanings originalRealization firing local_laws

theorem complete_static_restriction :
    (RelativeClosedInternalCategory.Presentation.baseMap vertex).functor ⋙
      (RelativeClosedInternalCategory.RulePresentation.arrowInclusion vertex categoryMap declarations).functor ⋙
        (RelativeClosedInternalCategory.RulePresentation.equationInclusion vertex categoryMap declarations).functor ⋙
          interpretation.functor = NamePassingBindingClosedOperationalCategory.base := by
  rw [complete_original_restriction]
  exact NamePassingBindingClosedOperationalCategory.complete_static_restriction

private theorem cast_complete {X Y X' Y' : Ambient} (source : X = X') (target : Y = Y')
    (arrow : X' ⟶ Y') :
    (⟨X,Y,eqToHom source ≫ arrow ≫ eqToHom target.symm⟩ : ArrowValue Ambient) = ⟨X',Y',arrow⟩ := by
  subst X'
  subst Y'
  simp only [eqToHom_refl,Category.id_comp,Category.comp_id]

def generatedValue (origin : Origin) : ArrowValue Ambient :=
  ⟨interpretation.functor.obj
      (RelativeClosedInternalCategory.RulePresentation.ruleDomain vertex categoryMap declarations origin),
    interpretation.functor.obj (RelativeClosedInternalCategory.RulePresentation.edges vertex categoryMap declarations),
    interpretation.functor.map (classOf (fire origin))⟩

theorem whole_generated_firing (origin : Origin) : generatedValue origin =
    ⟨domain origin,CategoricalOperationalContinuations.category.edge,nativeReceipt origin⟩ :=
  (RelativeClosedInternalCategory.RuleInterpretation.fire_complete_read
    vertex categoryMap declarations originalMeanings originalRealization firing local_laws origin).trans
      (cast_complete (premise_object origin) edge_object (nativeReceipt origin))

def readFire (origin : Origin) : Option (domain origin ⟶ CategoricalOperationalContinuations.category.edge) :=
  ArrowValue.readAt (some (generatedValue origin)) (domain origin) CategoricalOperationalContinuations.category.edge

theorem generated_function (origin : Origin) : readFire origin = some (nativeReceipt origin) := by
  unfold readFire
  rw [whole_generated_firing,ArrowValue.readAt_supplied]

theorem firing_substitution (origin : Origin) {world future : Base} (change : world ⟶ future)
    (supplied : (domain origin).obj world) :
    CategoricalOperationalContinuations.category.edge.map change ((nativeReceipt origin).app world supplied) =
      (nativeReceipt origin).app future ((domain origin).map change supplied) :=
  NamePassingCategoricalOperational.receipt_substitution (nativeReceipt origin) change supplied

/-- Every future return argument reads the original complete beta receipt. -/
theorem beta_future (world future : Base) (change : world ⟶ future)
    (supplied : (domain .beta).obj world) (result : operations.names.obj future) :
    ((CategoricalOperationalContinuations.edgeComparison.inv.app world
      ((nativeReceipt .beta).app world supplied)).app future change result) =
      InternalCategoryPathDiagram.edge CategoricalOperational.graph future
        ((NamePassingCategoricalOperational.beta.app world (betaInput.app world supplied)).app future change result) :=
  includeReceipt_future (betaInput ≫ NamePassingCategoricalOperational.beta) world future change supplied result

/-- Every future return argument reads the original unary fetch receipt. -/
theorem fetch_future (world future : Base) (change : world ⟶ future)
    (supplied : (domain .fetch).obj world) (result : operations.names.obj future) :
    ((CategoricalOperationalContinuations.edgeComparison.inv.app world
      ((nativeReceipt .fetch).app world supplied)).app future change result) =
      InternalCategoryPathDiagram.edge CategoricalOperational.graph future
        ((NamePassingCategoricalOperational.fetch.app world (fetchInput.app world supplied)).app future change result) :=
  includeReceipt_future (fetchInput ≫ NamePassingCategoricalOperational.fetch) world future change supplied result

section Classification

variable (candidate : Object signature ⥤ Ambient)
variable [PreservesFiniteLimits candidate] [MonoidalClosedFunctor candidate]
variable (images : AtomicPresentation.PrimitiveImages candidate assignment)
variable (readings : RelativeClosedInternalCategory.RuleUniversal.LocalReadings vertex categoryMap declarations
  (RelativeClosedInternalCategory.Presentation.nativeHeaders vertex)
  originalMeanings originalRealization firing candidate images)

/-- Local complete old-primitive and firing readings determine the full comparison. -/
@[instance_reducible] def comparisonUnique := RelativeClosedInternalCategory.RuleUniversal.admittedIsoUnique
  vertex categoryMap declarations (RelativeClosedInternalCategory.Presentation.nativeHeaders vertex)
    originalMeanings originalRealization firing candidate images readings

end Classification

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBindingClosedOperationalInterpretation
