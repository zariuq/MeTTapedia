import Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphRealizedReceiptFamilies
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualAuthoredMaterialCwf

/-!
# Realized graph receipts for actual contextual dependent families

An authored family supplies genuine small native fibres and constructed
material dictionaries. Its realized graph is built from every native term
graph, retaining the authored term as the root-child index. Context maps
act on those indices through the actual native functor, so the decoder is
natural and recovers whole compatible sections.

Dependent products use the existing complete future-argument carrier,
including its naturality evidence. They are not products over the current
fibre alone. Abstraction and application transport the actual contextual
adjunction through the section decoders. Material equality of graph values
does not license transport of an arbitrary native dependent consumer.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphRealizedContextualFamilies

open CategoryTheory Mettapedia.TypeTheory
open ContextualWitnessCover ContextualSmallFamilyUniverse
open ContextualAuthoredMaterialFamilies GraphRealizedReceiptFamilies
open GraphSetRealization

universe u v w
variable {D : Type u} [Category.{u} D] {base : D ⥤ Type (max u v)}

variable (domain : Family base)

/-- Componentwise equivalences with their actual naturality equations.
The record does not assume a particular presentation of the category of
functors. -/
structure NaturalEquiv {E : Type (max u v)} [Category.{u} E]
    (first second : E ⥤ Type u) where
  app : (point : E) → first.obj point ≃ second.obj point
  naturality : ∀ {firstPoint secondPoint : E} (step : firstPoint ⟶ secondPoint)
    (value : first.obj firstPoint),
    app secondPoint (first.map step value) = second.map step (app firstPoint value)

/-- The original small native fibre is the constructed graph index. -/
def graph (point : base.Elements) : Graph.{u} :=
  AccessiblePointedGraph.sup (fun value : domain.native.obj point =>
    (domain.models point).termGraph value)

def decode (point : base.Elements) : Receipts (graph domain point) ≃ domain.native.obj point :=
  supDecode _

def restriction {first second : base.Elements} (step : first ⟶ second)
    (receipt : Receipts (graph domain first)) : Receipts (graph domain second) :=
  (decode domain second).symm (domain.native.map step (decode domain first receipt))

theorem restriction_decode {first second : base.Elements} (step : first ⟶ second)
    (receipt : Receipts (graph domain first)) :
    decode domain second (restriction domain step receipt) =
      domain.native.map step (decode domain first receipt) :=
  (decode domain second).apply_symm_apply _

theorem restriction_identity (point : base.Elements) (receipt : Receipts (graph domain point)) :
    restriction domain (𝟙 point) receipt = receipt := by
  apply (decode domain point).injective
  rw [restriction_decode, domain.native.map_id_apply]

theorem restriction_composition {first middle last : base.Elements}
    (earlier : first ⟶ middle) (later : middle ⟶ last)
    (receipt : Receipts (graph domain first)) :
    restriction domain (earlier ≫ later) receipt =
      restriction domain later (restriction domain earlier receipt) := by
  apply (decode domain last).injective
  rw [restriction_decode, restriction_decode, restriction_decode,
    domain.native.map_comp_apply]

def family : base.Elements ⥤ Type u where
  obj point := Receipts (graph domain point)
  map step := TypeCat.ofHom (restriction domain step)
  map_id point := by
    apply ConcreteCategory.hom_ext
    exact restriction_identity domain point
  map_comp earlier later := by
    apply ConcreteCategory.hom_ext
    exact restriction_composition domain earlier later

def decoder : NaturalEquiv (family domain) domain.native where
  app := decode domain
  naturality := restriction_decode domain

def nativeSection (term : (family domain).sections) : domain.native.sections :=
  ⟨fun point => decode domain point (term.val point), by
    intro first second step
    exact (restriction_decode domain step (term.val first)).symm.trans
      (congrArg (decode domain second) (term.property step))⟩

def realizedSection (term : domain.native.sections) : (family domain).sections :=
  ⟨fun point => (decode domain point).symm (term.val point), by
    intro first second step
    change restriction domain step _ = _
    unfold restriction
    rw [Equiv.apply_symm_apply, term.property step]⟩

def sectionEquiv : (family domain).sections ≃ domain.native.sections where
  toFun := nativeSection domain
  invFun := realizedSection domain
  left_inv term := by
    apply Subtype.ext
    funext point
    exact (decode domain point).symm_apply_apply _
  right_inv term := by
    apply Subtype.ext
    funext point
    exact (decode domain point).apply_symm_apply _

/-- The retained child reads the same material value as its native term.
This is an observation comparison, not an equality-reflection rule. -/
theorem receipt_value (point : base.Elements) (receipt : (family domain).obj point) :
    HSet.mk ((graph domain point).repoint receipt.val) =
      (domain.models point).value (decode domain point receipt) := by
  have same := (Sup.picture (fun value : domain.native.obj point =>
    (domain.models point).termGraph value) (decode domain point receipt)).forget
  have rootSame : Sup.child (fun value : domain.native.obj point =>
    (domain.models point).termGraph value) (decode domain point receipt) = receipt :=
    (decode domain point).symm_apply_apply receipt
  rw [rootSame] at same
  exact ((HSet.mk_eq_mk_iff).mpr same).symm.trans ((domain.models point).mk_termGraph _)

theorem graph_carrier (point : base.Elements) :
    HSet.mk (graph domain point) = (domain.models point).carrier := by
  apply HSet.ext
  intro value
  change value ∈ HSet.range (fun term : domain.native.obj point =>
    (domain.models point).termGraph term) ↔ _
  rw [HSet.mem_range]
  constructor
  · rintro ⟨term, same⟩
    rw [(domain.models point).mk_termGraph] at same
    exact same ▸ (domain.models point).value_mem term
  · intro available
    refine ⟨(domain.models point).decode ⟨value, available⟩, ?_⟩
    rw [(domain.models point).mk_termGraph]
    exact (domain.models point).value_decode ⟨value, available⟩

def memberDecoder : (family domain).sections ≃ domain.members.sections :=
  (sectionEquiv domain).trans domain.sectionDecoder

theorem memberDecoder_value (term : (family domain).sections) (point : base.Elements) :
    ((memberDecoder domain term).val point).val =
      HSet.mk ((graph domain point).repoint (term.val point).val) :=
  (receipt_value domain point (term.val point)).symm

def consumer {target : Family base} (operation : domain ⟶ target) :
    WiderPresheafDependentFunctions.Hom (family domain) (family target) where
  app point receipt := (decode target point).symm
    (operation.app point (decode domain point receipt))
  naturality {first second} step receipt := by
    apply (decode target second).injective
    exact (restriction_decode target step ((decode target first).symm (operation.app first (decode domain first receipt)))).trans
      ((congrArg (fun value => target.native.map step value)
        ((decode target first).apply_symm_apply _)).trans
        ((operation.naturality step (decode domain first receipt)).trans
          ((congrArg (operation.app second) (restriction_decode domain step receipt)).symm.trans
            ((decode target second).apply_symm_apply _).symm)))

theorem consumer_decode {target : Family base} (operation : domain ⟶ target)
    (point : base.Elements) (receipt : (family domain).obj point) :
    decode target point ((consumer domain operation).app point receipt) =
      operation.app point (decode domain point receipt) :=
  (decode target point).apply_symm_apply _

theorem consumer_identity : consumer domain (𝟙 domain) =
    WiderPresheafDependentFunctions.Hom.identity (family domain) := by
  apply WiderPresheafDependentFunctions.Hom.ext
  intro point receipt
  exact (decode domain point).symm_apply_apply receipt

theorem consumer_composition {middle last : Family base}
    (earlier : domain ⟶ middle) (later : middle ⟶ last) :
    consumer domain (earlier ≫ later) =
      (consumer domain earlier).comp (consumer middle later) := by
  apply WiderPresheafDependentFunctions.Hom.ext
  intro point receipt
  change (decode last point).symm (later.app point (earlier.app point (decode domain point receipt))) =
    (decode last point).symm (later.app point (decode middle point
      ((decode middle point).symm (earlier.app point (decode domain point receipt)))))
  rw [Equiv.apply_symm_apply]

def restrictSection {other : D ⥤ Type (max u w)} (change : NaturalHom other base)
    (term : (family domain).sections) : (family (domain.reindex change)).sections :=
  ⟨fun point => term.val ((elementMap change).obj point),
    fun {_ _} step => term.property ((elementMap change).map step)⟩

theorem reindex_restriction {other : D ⥤ Type (max u w)} (change : NaturalHom other base)
    {first second : other.Elements} (step : first ⟶ second)
    (receipt : (family (domain.reindex change)).obj first) :
    restriction (domain.reindex change) step receipt =
      restriction domain ((elementMap change).map step) receipt := rfl

theorem section_substitution {other : D ⥤ Type (max u w)} (change : NaturalHom other base)
    (term : (family domain).sections) :
    sectionEquiv (domain.reindex change) (restrictSection domain change term) =
      ContextualSmallFamilyIdentity.reindexSection change domain.native
        (sectionEquiv domain term) := rfl

section ProductsAndSums

variable (body : Family domain.extension) (worlds : ArgumentCoding D)
variable (arrows : (first second : D) → ArgumentCoding (first ⟶ second))

def futureProductDecoder (point : base.Elements) :
    (family (domain.pi body worlds arrows)).obj point ≃
      ContextualSmallFamilyTypeFormers.ProductAt domain.native (domain.bodyNative body) point :=
  decode _ point

def futureDependentSectionDecoder (point : base.Elements) :
    (family (domain.pi body worlds arrows)).obj point ≃
      WiderPresheafDependentFunctions.DependentSection domain.native (domain.bodyNative body) point :=
  (futureProductDecoder domain body worlds arrows point).trans
    (ContextualSmallFamilyNativeAdjunction.nativeSmallEquiv domain.native (domain.bodyNative body) point).symm

/-- Abstraction acts on whole compatible body sections, preserving every
future argument required by the actual native dependent adjunction. -/
def lambdaEquiv : (family body).sections ≃ (family (domain.pi body worlds arrows)).sections :=
  (sectionEquiv body).trans ((ContextualAuthoredMaterialCwf.lambdaEquiv domain body worlds arrows).trans
    (sectionEquiv (domain.pi body worlds arrows)).symm)

theorem lambda_future_value (term : (family body).sections) (point : base.Elements)
    (argument : (ContextualSmallFamilyTypeFormers.futureDomain domain.native point).Elements) :
    (futureProductDecoder domain body worlds arrows point
      ((lambdaEquiv domain body worlds arrows term).val point)).val argument =
        decode body ((ContextualSmallFamilyComprehension.flatten domain.native).obj
          ((ContextualSmallFamilyTypeFormers.futureArguments domain.native point).obj argument))
          (term.val ((ContextualSmallFamilyComprehension.flatten domain.native).obj
            ((ContextualSmallFamilyTypeFormers.futureArguments domain.native point).obj argument))) := by
  change (decode _ point
    ((decode _ point).symm
      ((ContextualAuthoredMaterialCwf.lambdaEquiv domain body worlds arrows
        (sectionEquiv body term)).val point))).val argument = _
  rw [Equiv.apply_symm_apply]
  exact ContextualAuthoredMaterialCwf.lambda_value domain body worlds arrows _ point argument

theorem lambda_eta (function : (family (domain.pi body worlds arrows)).sections) :
    lambdaEquiv domain body worlds arrows ((lambdaEquiv domain body worlds arrows).symm function) = function :=
  (lambdaEquiv domain body worlds arrows).apply_symm_apply function

/-- Application uses a genuine compatible argument section and the
corresponding comprehension substitution. -/
def applyTerm (function : (family (domain.pi body worlds arrows)).sections)
    (argument : (family domain).sections) :
    (family (body.reindex (ContextualAuthoredMaterialCwf.pair
      (ContextualSmallMapConstructions.identity base) domain (sectionEquiv domain argument)))).sections :=
  restrictSection body (ContextualAuthoredMaterialCwf.pair
    (ContextualSmallMapConstructions.identity base) domain (sectionEquiv domain argument))
    ((lambdaEquiv domain body worlds arrows).symm function)

theorem application_beta (term : (family body).sections) (argument : (family domain).sections) :
    applyTerm domain body worlds arrows (lambdaEquiv domain body worlds arrows term) argument =
      restrictSection body (ContextualAuthoredMaterialCwf.pair
        (ContextualSmallMapConstructions.identity base) domain (sectionEquiv domain argument)) term := by
  unfold applyTerm
  rw [Equiv.symm_apply_apply]

theorem application_native (function : (family (domain.pi body worlds arrows)).sections)
    (argument : (family domain).sections) :
    sectionEquiv _ (applyTerm domain body worlds arrows function argument) =
      ContextualAuthoredMaterialCwf.applyTerm domain body worlds arrows
        (sectionEquiv _ function) (sectionEquiv domain argument) := by
  unfold applyTerm
  rw [section_substitution]
  apply congrArg
  apply Subtype.ext
  funext point
  change decode body point ((decode body point).symm
    (((ContextualAuthoredMaterialCwf.lambdaEquiv domain body worlds arrows).symm
      (sectionEquiv _ function)).val point)) = _
  exact (decode body point).apply_symm_apply _

/-- Both projections of the actual contextual sum, including the second
projection's dependent comprehension, are recovered through the decoder. -/
def sigmaFirst (term : (family (domain.sigma body)).sections) : (family domain).sections :=
  (sectionEquiv domain).symm
    (ContextualAuthoredMaterialCwf.sigmaFirst domain body (sectionEquiv _ term))

def sigmaSecond (term : (family (domain.sigma body)).sections) :
    (family (body.reindex (ContextualAuthoredMaterialCwf.pair
      (ContextualSmallMapConstructions.identity base) domain
      (ContextualAuthoredMaterialCwf.sigmaFirst domain body (sectionEquiv _ term))))).sections :=
  (sectionEquiv _).symm
    (ContextualAuthoredMaterialCwf.sigmaSecond domain body (sectionEquiv _ term))

def sigmaPair (firstTerm : (family domain).sections)
    (secondTerm : (family (body.reindex (ContextualAuthoredMaterialCwf.pair
      (ContextualSmallMapConstructions.identity base) domain (sectionEquiv domain firstTerm)))).sections) :
    (family (domain.sigma body)).sections :=
  (sectionEquiv _).symm (ContextualAuthoredMaterialCwf.sigmaPair domain body
    (sectionEquiv domain firstTerm) (sectionEquiv _ secondTerm))

theorem sigmaPair_decode (firstTerm : (family domain).sections)
    (secondTerm : (family (body.reindex (ContextualAuthoredMaterialCwf.pair
      (ContextualSmallMapConstructions.identity base) domain (sectionEquiv domain firstTerm)))).sections) :
    sectionEquiv _ (sigmaPair domain body firstTerm secondTerm) =
      ContextualAuthoredMaterialCwf.sigmaPair domain body
        (sectionEquiv domain firstTerm) (sectionEquiv _ secondTerm) :=
  (sectionEquiv _).apply_symm_apply _

theorem sigmaFirst_pair (firstTerm : (family domain).sections)
    (secondTerm : (family (body.reindex (ContextualAuthoredMaterialCwf.pair
      (ContextualSmallMapConstructions.identity base) domain (sectionEquiv domain firstTerm)))).sections) :
    sigmaFirst domain body (sigmaPair domain body firstTerm secondTerm) = firstTerm := by
  unfold sigmaFirst
  rw [sigmaPair_decode]
  exact (sectionEquiv domain).symm_apply_apply firstTerm

theorem sigma_eta_native (term : (family (domain.sigma body)).sections) :
    (sectionEquiv _).symm (ContextualAuthoredMaterialCwf.sigmaPair domain body
      (ContextualAuthoredMaterialCwf.sigmaFirst domain body (sectionEquiv _ term))
      (ContextualAuthoredMaterialCwf.sigmaSecond domain body (sectionEquiv _ term))) = term := by
  rw [ContextualAuthoredMaterialCwf.sigma_eta]
  exact (sectionEquiv _).symm_apply_apply term

end ProductsAndSums

end Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphRealizedContextualFamilies
