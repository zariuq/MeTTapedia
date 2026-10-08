import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphMaterialFunctionalProducts

/-!
# Natural material application on the exact argument kernel

The small argument and result quotient families are formed over the
constructed compatible function parameters. The natural result reading
factors through the argument observation exactly because of the retained
all-future compatibility certificate. Its computation square holds for
each actual native receipt, and therefore for whole natural sections.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphMaterialFunctionalApplication

open CategoryTheory Mettapedia.TypeTheory
open ContextualWitnessCover ContextualSmallFamilyUniverse ContextualSmallFamilyComprehension
open ContextualGraphDiagrams ContextualRealizedGraphs ContextualGraphMaterialFamilies
open ContextualGraphMaterialProducts ContextualGraphMaterialFunctionalProducts

universe u
variable {D : Type u} [Category.{u} D] {base : D ⥤ Type u}
variable (domain : Family base) (body : Family (total domain.native))

def nativeArguments : (total (compatibleNative domain body)).Elements ⥤ Type u :=
  substitutedFamily (arguments domain body) (totalForget domain body)

def argumentReceipts : NaturalHom (total (nativeArguments domain body)) (total (arguments domain body)) where
  app _ receipt := ⟨⟨receipt.1.1, receipt.1.2.val⟩, receipt.2⟩
  naturality _ _ := rfl

def argumentFamily : Family.{u} (total (compatibleNative domain body)) where
  native := nativeArguments domain body
  reading := ((argumentReceipts domain body).comp (argumentTarget domain body)).comp domain.reading

def resultFamily : Family.{u} (total (compatibleNative domain body)) where
  native := nativeArguments domain body
  reading := ((argumentReceipts domain body).comp (resultTarget domain body)).comp body.reading

def resultConsumer : NaturalHom (argumentFamily domain body).native (observed (resultFamily domain body)) :=
  observe (resultFamily domain body)

theorem result_consumer_compatible : Compatible (argumentFamily domain body) (resultConsumer domain body) := by
  intro point first second same
  rcases same with ⟨same⟩
  apply (observed_kernel (resultFamily domain body) point first second).mpr
  exact point.2.2.property.elim (fun certificate =>
    ⟨currentData domain body point.1 ⟨point.2.1, point.2.2.val⟩ certificate first second same⟩)

def materialApplication : NaturalHom (observed (argumentFamily domain body)) (observed (resultFamily domain body)) :=
  ContextualGraphMaterialFamilies.descend (argumentFamily domain body) (resultConsumer domain body) (result_consumer_compatible domain body)

theorem application_square :
    (observe (argumentFamily domain body)).comp (materialApplication domain body) = resultConsumer domain body :=
  descend_square (argumentFamily domain body) (resultConsumer domain body) (result_consumer_compatible domain body)

theorem application_receipt (point : (total (compatibleNative domain body)).Elements)
    (argument : (nativeArguments domain body).obj point) :
    (materialApplication domain body).app point ((observe (argumentFamily domain body)).app point argument) =
      (observe (resultFamily domain body)).app point argument := rfl

theorem application_sections (whole : (nativeArguments domain body).sections) :
    (materialApplication domain body).mapSection ((observe (argumentFamily domain body)).mapSection whole) =
      (observe (resultFamily domain body)).mapSection whole := rfl

/-- An actual natural application consumer through the argument readout
exists precisely when its result values respect that readout kernel. -/
theorem consumer_descends_iff {output : (total (compatibleNative domain body)).Elements ⥤ Type u}
    (consumer : NaturalHom (nativeArguments domain body) output) :
    (∃ descended : NaturalHom (observed (argumentFamily domain body)) output,
      (observe (argumentFamily domain body)).comp descended = consumer) ↔
      Compatible (argumentFamily domain body) consumer :=
  descends_iff (argumentFamily domain body) consumer

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphMaterialFunctionalApplication
