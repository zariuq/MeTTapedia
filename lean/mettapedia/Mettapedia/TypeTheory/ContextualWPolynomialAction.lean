import Mettapedia.TypeTheory.ContextualWPolynomialReindexing

/-!
# Constructed target action of the full future polynomial

The action applies a natural map to every retained future branch value.
It commutes with actual category restriction, including complete dependent
position tables.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualWPolynomialAction

open CategoryTheory MaterialSets.Hypersets
open PowerClassPresheafBaseChange

universe u v
variable {D E : Type u} [Category.{u} D] [Category.{u} E]

def mapValue (signature : ContextualWReindexing.Signature D)
    {first second : D ⥤ Type u} (operation : NatTrans first second) (point : D)
    (node : ContextualWPolynomialReindexing.At ⟨signature, first⟩ point) :
    ContextualWPolynomialReindexing.At ⟨signature, second⟩ point :=
  ⟨node.1, node.2.map operation⟩

theorem mapValue_restrict (signature : ContextualWReindexing.Signature D)
    {first second : D ⥤ Type u} (operation : NatTrans first second)
    {source target : D} (step : source ⟶ target)
    (node : ContextualWPolynomialReindexing.At ⟨signature, first⟩ source) :
    (ContextualWPolynomialReindexing.family ⟨signature, second⟩).map step
      (mapValue signature operation source node) =
      mapValue signature operation target
        ((ContextualWPolynomialReindexing.family ⟨signature, first⟩).map step node) := by
  rcases node with ⟨label, branches⟩
  apply congrArg (Sigma.mk _)
  apply ContextualWTypes.Branches.ext
  intro next arrow position
  rfl

def map (signature : ContextualWReindexing.Signature D)
    {first second : D ⥤ Type u} (operation : NatTrans first second) :
    NatTrans (ContextualWPolynomialReindexing.family ⟨signature, first⟩)
      (ContextualWPolynomialReindexing.family ⟨signature, second⟩) where
  app point := TypeCat.ofHom (mapValue signature operation point)
  naturality source target step := by
    apply ConcreteCategory.hom_ext
    intro node
    exact (mapValue_restrict signature operation step node).symm

def restrictNat (change : D ⥤ E) {first second : E ⥤ Type u} (operation : NatTrans first second) :
    NatTrans (ContextualSmallFamilyUniverse.restrict change first)
      (ContextualSmallFamilyUniverse.restrict change second) where
  app point := operation.app (change.obj point)
  naturality _ _ step := operation.naturality (change.map step)

theorem mapValue_pullData (change : D ⥤ E) (signature : ContextualWReindexing.Signature E)
    {first second : E ⥤ Type u} (operation : NatTrans first second) {target : E}
    (node : ContextualWPolynomialReindexing.At ⟨signature, first⟩ target)
    (point : D) (same : change.obj point = target) :
    ContextualWPolynomialReindexing.pullData change ⟨signature, second⟩
      (mapValue signature operation target node) point same =
      mapValue (ContextualWReindexing.under change signature) (restrictNat change operation) point
        (ContextualWPolynomialReindexing.pullData change ⟨signature, first⟩ node point same) := by
  cases same
  rcases node with ⟨label, branches⟩
  apply congrArg (Sigma.mk label)
  apply ContextualWTypes.Branches.ext
  intro next arrow position
  rfl

theorem mapValue_heq {firstSignature secondSignature : ContextualWReindexing.Signature D}
    (signatures : firstSignature = secondSignature)
    {firstSource secondSource firstTarget secondTarget : D ⥤ Type u}
    (sources : firstSource = secondSource) (targets : firstTarget = secondTarget)
    (firstOperation : NatTrans firstSource firstTarget) (secondOperation : NatTrans secondSource secondTarget)
    (operations : HEq firstOperation secondOperation) (point : D)
    (firstNode : ContextualWPolynomialReindexing.At ⟨firstSignature, firstSource⟩ point)
    (secondNode : ContextualWPolynomialReindexing.At ⟨secondSignature, secondSource⟩ point)
    (nodes : HEq firstNode secondNode) :
    HEq (mapValue firstSignature firstOperation point firstNode)
      (mapValue secondSignature secondOperation point secondNode) := by
  cases signatures
  cases sources
  cases targets
  cases eq_of_heq operations
  cases eq_of_heq nodes
  rfl

theorem nat_ext_heq {K : Type v} [Category.{u} K]
    {firstSource secondSource firstTarget secondTarget : K ⥤ Type u}
    (sources : firstSource = secondSource) (targets : firstTarget = secondTarget)
    (first : NatTrans firstSource firstTarget) (second : NatTrans secondSource secondTarget)
    (values : ∀ (point : K) (left : firstSource.obj point) (right : secondSource.obj point),
      HEq left right → HEq (first.app point left) (second.app point right)) : HEq first second := by
  cases sources
  cases targets
  apply heq_of_eq
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  intro value
  exact eq_of_heq (values point value value HEq.rfl)

end Mettapedia.TypeTheory.ContextualWPolynomialAction
