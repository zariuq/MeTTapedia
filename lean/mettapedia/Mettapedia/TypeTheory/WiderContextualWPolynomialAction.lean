import Mettapedia.TypeTheory.WiderContextualWPolynomialReindexing

/-!
# Complete polynomial action between independent result universes

A cross-universe natural map acts on every future branch. Its action
commutes with all actual restriction and future-prefix readouts.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.WiderContextualWPolynomialAction

open CategoryTheory MaterialSets.Hypersets
open PowerClassPresheafBaseChange

universe u v h k
variable {D E : Type u} [Category.{u} D] [Category.{u} E]

def mapValue (signature : ContextualWReindexing.Signature D)
    {first : D ⥤ Type h} {second : D ⥤ Type k} (operation : WiderPresheafDependentFunctions.Hom first second) (point : D)
    (node : WiderContextualWPolynomialReindexing.At ⟨signature, first⟩ point) :
    WiderContextualWPolynomialReindexing.At ⟨signature, second⟩ point :=
  ⟨node.1, node.2.map operation⟩

theorem mapValue_restrict (signature : ContextualWReindexing.Signature D)
    {first : D ⥤ Type h} {second : D ⥤ Type k} (operation : WiderPresheafDependentFunctions.Hom first second)
    {source target : D} (step : source ⟶ target)
    (node : WiderContextualWPolynomialReindexing.At ⟨signature, first⟩ source) :
    (WiderContextualWPolynomialReindexing.family ⟨signature, second⟩).map step
      (mapValue signature operation source node) =
      mapValue signature operation target
        ((WiderContextualWPolynomialReindexing.family ⟨signature, first⟩).map step node) := by
  rcases node with ⟨label, branches⟩
  apply congrArg (Sigma.mk _)
  apply WiderContextualWAlgebras.Branches.ext
  intro next arrow position
  rfl

def map (signature : ContextualWReindexing.Signature D)
    {first : D ⥤ Type h} {second : D ⥤ Type k} (operation : WiderPresheafDependentFunctions.Hom first second) :
    WiderPresheafDependentFunctions.Hom (WiderContextualWPolynomialReindexing.family ⟨signature, first⟩)
      (WiderContextualWPolynomialReindexing.family ⟨signature, second⟩) where
  app point := mapValue signature operation point
  naturality step node := mapValue_restrict signature operation step node

def restrictNat {K : Type v} [Category.{u} K] (change : D ⥤ K)
    {first : K ⥤ Type h} {second : K ⥤ Type k} (operation : WiderPresheafDependentFunctions.Hom first second) :
    WiderPresheafDependentFunctions.Hom (ContextualSmallFamilyUniverse.restrict change first)
      (ContextualSmallFamilyUniverse.restrict change second) where
  app point := operation.app (change.obj point)
  naturality step value := operation.naturality (change.map step) value

theorem mapValue_pullData (change : D ⥤ E) (signature : ContextualWReindexing.Signature E)
    {first : E ⥤ Type h} {second : E ⥤ Type k} (operation : WiderPresheafDependentFunctions.Hom first second) {target : E}
    (node : WiderContextualWPolynomialReindexing.At ⟨signature, first⟩ target)
    (point : D) (same : change.obj point = target) :
    WiderContextualWPolynomialReindexing.pullData change ⟨signature, second⟩
      (mapValue signature operation target node) point same =
      mapValue (ContextualWReindexing.under change signature) (restrictNat change operation) point
        (WiderContextualWPolynomialReindexing.pullData change ⟨signature, first⟩ node point same) := by
  cases same
  rcases node with ⟨label, branches⟩
  apply congrArg (Sigma.mk label)
  apply WiderContextualWAlgebras.Branches.ext
  intro next arrow position
  rfl

theorem mapValue_heq {firstSignature secondSignature : ContextualWReindexing.Signature D}
    (signatures : firstSignature = secondSignature)
    {firstSource secondSource : D ⥤ Type h} {firstTarget secondTarget : D ⥤ Type k}
    (sources : firstSource = secondSource) (targets : firstTarget = secondTarget)
    (firstOperation : WiderPresheafDependentFunctions.Hom firstSource firstTarget) (secondOperation : WiderPresheafDependentFunctions.Hom secondSource secondTarget)
    (operations : HEq firstOperation secondOperation) (point : D)
    (firstNode : WiderContextualWPolynomialReindexing.At ⟨firstSignature, firstSource⟩ point)
    (secondNode : WiderContextualWPolynomialReindexing.At ⟨secondSignature, secondSource⟩ point)
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
    {firstSource secondSource : K ⥤ Type h} {firstTarget secondTarget : K ⥤ Type k}
    (sources : firstSource = secondSource) (targets : firstTarget = secondTarget)
    (first : WiderPresheafDependentFunctions.Hom firstSource firstTarget) (second : WiderPresheafDependentFunctions.Hom secondSource secondTarget)
    (values : ∀ (point : K) (left : firstSource.obj point) (right : secondSource.obj point),
      HEq left right → HEq (first.app point left) (second.app point right)) : HEq first second := by
  cases sources
  cases targets
  apply heq_of_eq
  apply WiderPresheafDependentFunctions.Hom.ext
  intro point value
  exact eq_of_heq (values point value value HEq.rfl)


end Mettapedia.TypeTheory.WiderContextualWPolynomialAction
