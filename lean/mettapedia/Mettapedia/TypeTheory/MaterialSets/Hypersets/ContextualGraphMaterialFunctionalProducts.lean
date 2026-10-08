import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphMaterialProducts

/-!
# Constructed compatible material function families

The full native product is refined by compatibility of argument and result
readings at every actual future arrow. The classified carrier is original
small. Uniform matching certificates remain explicit data for dependent
consumers; the classification proposition does not extract those data.

For compatible terms, equality of the attached application graphs has
exactly the uniform pointwise kernel. This is a statement about material
functions, not a claim that every native section descends to one.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphMaterialFunctionalProducts

open CategoryTheory Mettapedia.TypeTheory
open ContextualWitnessCover ContextualSmallFamilyUniverse ContextualSmallFamilyComprehension
open ContextualGraphDiagrams ContextualRealizedGraphs ContextualGraphMaterialFamilies
open ContextualGraphMaterialProducts

universe u
variable {D : Type u} [Category.{u} D] {base : D ⥤ Type u}
variable (domain : Family base) (body : Family (total domain.native))

abbrev LocalData (point : D) (receipt : (total (nativeProduct domain body)).obj point) : Type u :=
  ApplicationCompatible domain body ⟨point, receipt.1⟩ receipt.2

/-- A single retained strategy covers every future, including distinct
arrows with the same endpoints. -/
abbrev FullData (point : D) (receipt : (total (nativeProduct domain body)).obj point) : Type u :=
  ∀ future : ContextualGraphRealizers.Future point,
    LocalData domain body future.1 ((total (nativeProduct domain body)).map future.2 receipt)

def restrictData {first second : D} (arrival : first ⟶ second)
    (receipt : (total (nativeProduct domain body)).obj first)
    (certificate : FullData domain body first receipt) :
    FullData domain body second ((total (nativeProduct domain body)).map arrival receipt) :=
  fun future => cast
    (congrArg (LocalData domain body future.1)
      ((total (nativeProduct domain body)).map_comp_apply arrival future.2 receipt))
    (certificate ⟨future.1, arrival ≫ future.2⟩)

def currentData (point : D) (receipt : (total (nativeProduct domain body)).obj point)
    (certificate : FullData domain body point receipt) : LocalData domain body point receipt :=
  cast (congrArg (LocalData domain body point)
    ((total (nativeProduct domain body)).map_id_apply point receipt))
    (certificate ⟨point, 𝟙 point⟩)

theorem totalReceipt_move {first second : base.Elements} (step : first ⟶ second)
    (function : (nativeProduct domain body).obj first) :
    (total (nativeProduct domain body)).map step.1 ⟨first.2, function⟩ =
      ⟨second.2, (nativeProduct domain body).map step function⟩ := by
  rcases first with ⟨first, parameter⟩
  rcases second with ⟨second, next⟩
  rcases step with ⟨arrival, follows⟩
  change first ⟶ second at arrival
  change base.map arrival parameter = next at follows
  subst next
  rfl

def restrictFunctionData {first second : base.Elements} (step : first ⟶ second)
    (function : (nativeProduct domain body).obj first)
    (certificate : FullData domain body first.1 ⟨first.2, function⟩) :
    FullData domain body second.1 ⟨second.2, (nativeProduct domain body).map step function⟩ :=
  cast (congrArg (FullData domain body second.1) (totalReceipt_move domain body step function))
    (restrictData domain body step.1 ⟨first.2, function⟩ certificate)

/-- The complete compatible subfamily is constructed by a small subtype
of the actual complete native product, not supplied as a section carrier. -/
def compatibleNative : base.Elements ⥤ Type u where
  obj point := {function : (nativeProduct domain body).obj point //
    Nonempty (FullData domain body point.1 ⟨point.2, function⟩)}
  map step := TypeCat.ofHom fun function =>
    ⟨(nativeProduct domain body).map step function.val,
      function.property.elim (fun certificate =>
        ⟨restrictFunctionData domain body step function.val certificate⟩)⟩
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro function
    exact Subtype.ext ((nativeProduct domain body).map_id_apply point function.val)
  map_comp earlier later := by
    apply ConcreteCategory.hom_ext
    intro function
    exact Subtype.ext ((nativeProduct domain body).map_comp_apply earlier later function.val)

def forget : NaturalHom (compatibleNative domain body) (nativeProduct domain body) where
  app _ function := function.val
  naturality _ _ := rfl

def totalForget : NaturalHom (total (compatibleNative domain body)) (total (nativeProduct domain body)) where
  app _ receipt := ⟨receipt.1, receipt.2.val⟩
  naturality _ _ := rfl

def functionalPi : Family base where
  native := compatibleNative domain body
  reading := (totalForget domain body).comp (functionReading domain body)

def certify (point : base.Elements) (function : (nativeProduct domain body).obj point)
    (certificate : FullData domain body point.1 ⟨point.2, function⟩) :
    (compatibleNative domain body).obj point := ⟨function, ⟨certificate⟩⟩

theorem functional_value (point : base.Elements) (function : (compatibleNative domain body).obj point) :
    termValue (functionalPi domain body) point function = productElement domain body point function.val := rfl

theorem compatible_classification (point : base.Elements) (function : (nativeProduct domain body).obj point) :
    (∃ compatible : (compatibleNative domain body).obj point, compatible.val = function) ↔
      Nonempty (FullData domain body point.1 ⟨point.2, function⟩) := by
  constructor
  · rintro ⟨compatible, same⟩
    cases same
    exact compatible.property
  · intro certificate
    exact ⟨⟨function, certificate⟩, rfl⟩

def futureData (point : base.Elements) (function : (nativeProduct domain body).obj point)
    (certificate : FullData domain body point.1 ⟨point.2, function⟩)
    (future : ContextualGraphRealizers.Future point.1) :
    ApplicationCompatible domain body (futurePoint point future)
      ((nativeProduct domain body).map (futureStep point future) function) := certificate future

/-- The entire pointwise matching strategy is retained. Merely knowing
each individual result pair is related is a different statement. -/
abbrev PointwiseData (point : base.Elements) (first second : (nativeProduct domain body).obj point) : Type u :=
  ∀ (future : ContextualGraphRealizers.Future point.1)
    (argument : domain.native.obj (futurePoint point future)),
    Equal (resultValue domain body (futurePoint point future)
      ((nativeProduct domain body).map (futureStep point future) first) argument)
      (resultValue domain body (futurePoint point future)
        ((nativeProduct domain body).map (futureStep point future) second) argument)

def pointwiseFromGraph (point : base.Elements) (first second : (nativeProduct domain body).obj point)
    (same : Equal (productElement domain body point first) (productElement domain body point second))
    (certificate : FullData domain body point.1 ⟨point.2, second⟩) :
    PointwiseData domain body point first second := by
  intro future argument
  let response := applicationMatching domain body point first second same future argument
  exact response.2.2.trans
    (futureData domain body point second certificate future response.1 argument response.2.1.symm)

def graphFromPointwise (point : base.Elements) (first second : (nativeProduct domain body).obj point)
    (matching : PointwiseData domain body point first second) :
    Equal (productElement domain body point first) (productElement domain body point second) :=
  productEquality domain body point first second
    (fun future argument => ⟨argument, Equal.refl _, matching future argument⟩)
    (fun future argument => ⟨argument, Equal.refl _, (matching future argument).symm⟩)

theorem functional_kernel (point : base.Elements) (first second : (compatibleNative domain body).obj point) :
    Nonempty (Equal (termValue (functionalPi domain body) point first)
      (termValue (functionalPi domain body) point second)) ↔
      Nonempty (PointwiseData domain body point first.val second.val) := by
  constructor
  · rintro ⟨same⟩
    exact second.property.elim (fun certificate =>
      ⟨pointwiseFromGraph domain body point first.val second.val same certificate⟩)
  · rintro ⟨matching⟩
    exact ⟨graphFromPointwise domain body point first.val second.val matching⟩

def compatibleApplication (point : base.Elements)
    (first second : (nativeProduct domain body).obj point)
    (firstArgument secondArgument : domain.native.obj point)
    (sameFunction : Equal (productElement domain body point first) (productElement domain body point second))
    (sameArgument : Equal (termValue domain point firstArgument) (termValue domain point secondArgument))
    (certificate : FullData domain body point.1 ⟨point.2, second⟩) :
    Equal (resultValue domain body point first firstArgument)
      (resultValue domain body point second secondArgument) :=
  applicationCongr domain body point first second firstArgument secondArgument sameFunction sameArgument
    (currentData domain body point.1 ⟨point.2, second⟩ certificate)

def singleValued (point : base.Elements) (function : (nativeProduct domain body).obj point)
    (certificate : FullData domain body point.1 ⟨point.2, function⟩)
    (argument firstResult secondResult : Value D point.1)
    (first : Member (ContextualGraphOrderedPairs.orderedPair argument firstResult)
      (productElement domain body point function))
    (second : Member (ContextualGraphOrderedPairs.orderedPair argument secondResult)
      (productElement domain body point function)) : Equal firstResult secondResult := by
  let firstReceipt := applicationDecode domain body point function _ first
  let secondReceipt := applicationDecode domain body point function _ second
  have sameArgument := (ContextualGraphOrderedPairs.orderedPairReflectFirst firstReceipt.2).symm.trans
    (ContextualGraphOrderedPairs.orderedPairReflectFirst secondReceipt.2)
  exact (ContextualGraphOrderedPairs.orderedPairReflectSecond firstReceipt.2).trans
    ((currentData domain body point.1 ⟨point.2, function⟩ certificate firstReceipt.1 secondReceipt.1 sameArgument).trans
      (ContextualGraphOrderedPairs.orderedPairReflectSecond secondReceipt.2).symm)

/-- At each stage, classified compatible graphs have a single output
reading for each input reading; proof-relevant output transport still
requires an explicit certificate. -/
theorem classified_single_valued (point : base.Elements) (function : (compatibleNative domain body).obj point)
    (argument firstResult secondResult : Value D point.1)
    (first : Member (ContextualGraphOrderedPairs.orderedPair argument firstResult)
      (termValue (functionalPi domain body) point function))
    (second : Member (ContextualGraphOrderedPairs.orderedPair argument secondResult)
      (termValue (functionalPi domain body) point function)) : Nonempty (Equal firstResult secondResult) :=
  function.property.elim (fun certificate =>
    ⟨singleValued domain body point function.val certificate argument firstResult secondResult first second⟩)

def wholeData (whole : (nativeProduct domain body).sections)
    (localData : ∀ point : base.Elements,
      ApplicationCompatible domain body point (whole.val point))
    (point : base.Elements) : FullData domain body point.1 ⟨point.2, whole.val point⟩ :=
  fun future => cast
    (congrArg (ApplicationCompatible domain body (futurePoint point future))
      (whole.property (futureStep point future)).symm)
    (localData (futurePoint point future))

/-- Entire compatible native sections are classified without selecting
from a proposition. Their future certificates are built from the supplied
uniform local strategy and the actual section naturality proof. -/
def classifySection (whole : (nativeProduct domain body).sections)
    (localData : ∀ point : base.Elements,
      ApplicationCompatible domain body point (whole.val point)) :
    (compatibleNative domain body).sections :=
  ⟨fun point => certify domain body point (whole.val point) (wholeData domain body whole localData point),
    fun {_ _} step => Subtype.ext (whole.property step)⟩

theorem forget_classified (whole : (nativeProduct domain body).sections)
    (localData : ∀ point : base.Elements,
      ApplicationCompatible domain body point (whole.val point)) :
    (forget domain body).mapSection (classifySection domain body whole localData) = whole := rfl

theorem forget_sections_injective : Function.Injective (forget domain body).mapSection := by
  intro first second same
  apply Subtype.ext
  funext point
  exact Subtype.ext (congrArg (fun whole : (nativeProduct domain body).sections => whole.val point) same)

/-- Equality of whole observed compatible sections is the pointwise
material function kernel. The existential certificate remains local to
each comparison; no uniform witness is extracted from these propositions. -/
theorem observed_section_kernel (first second : (compatibleNative domain body).sections) :
    (observe (functionalPi domain body)).mapSection first =
        (observe (functionalPi domain body)).mapSection second ↔
      ∀ point : base.Elements,
        Nonempty (PointwiseData domain body point (first.val point).val (second.val point).val) := by
  constructor
  · intro same point
    have observedSame := congrArg (fun whole : (observed (functionalPi domain body)).sections => whole.val point) same
    exact (functional_kernel domain body point (first.val point) (second.val point)).mp
      ((observed_kernel (functionalPi domain body) point (first.val point) (second.val point)).mp observedSame)
  · intro same
    apply Subtype.ext
    funext point
    exact (observed_kernel (functionalPi domain body) point (first.val point) (second.val point)).mpr
      ((functional_kernel domain body point (first.val point) (second.val point)).mpr (same point))

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphMaterialFunctionalProducts
