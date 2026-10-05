import Mettapedia.TypeTheory.ContextualSmallFamilyWCone

/-!
# Complete contextual polynomial reindexing

The polynomial contains one shape and a compatible result for every
future arrow and dependent position. Actual context functors reindex
those values, and all coherence laws preserve the full branch table.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualWPolynomialReindexing

open CategoryTheory MaterialSets.Hypersets
open PowerClassPresheafBaseChange
open Mettapedia.GSLT.Topos.ConstructivePresheaf

universe u
variable {D E F : Type u} [Category.{u} D] [Category.{u} E] [Category.{u} F]

abbrev Signature (D : Type u) [Category.{u} D] := ContextualWReindexing.Signature D × (D ⥤ Type u)

def under (change : D ⥤ E) (signature : Signature E) : Signature D :=
  ⟨ContextualWReindexing.under change signature.1, restrict change signature.2⟩

def family (signature : Signature D) : D ⥤ Type u :=
  ContextualWTypes.polynomial signature.1.1 signature.1.2 signature.2

abbrev At (signature : Signature D) (point : D) := (family signature).obj point

def pullBranches (change : D ⥤ E) (signature : Signature E) (point : D)
    (label : signature.1.1.obj (change.obj point))
    (branches : ContextualWTypes.Branches signature.1.1 signature.1.2 signature.2 label) :
    ContextualWTypes.Branches (under change signature).1.1 (under change signature).1.2
      (under change signature).2 label where
  app next arrow branch := branches.app (change.obj next) (change.map arrow) branch
  naturality _ _ first later branch :=
    (branches.naturality _ _ (change.map first) (change.map later) branch).trans
      (branches.app_eq (change.map_comp first later).symm
        (ContextualWTypes.positionAlong signature.1.1 signature.1.2 label (change.map first) (change.map later) branch)
        (ContextualWTypes.positionAlong (under change signature).1.1 (under change signature).1.2 label first later branch)
        ((cast_heq _ _).trans (cast_heq _ _).symm))

def pullData (change : D ⥤ E) (signature : Signature E) {target : E} (node : At signature target)
    (point : D) (same : change.obj point = target) : At (under change signature) point := by
  cases same
  exact ⟨node.1, pullBranches change signature point node.1 node.2⟩

def pull (change : D ⥤ E) (signature : Signature E) (point : D)
    (node : At signature (change.obj point)) : At (under change signature) point :=
  pullData change signature node point rfl

theorem pull_restrict (change : D ⥤ E) (signature : Signature E)
    {first second : D} (step : first ⟶ second) (node : At signature (change.obj first)) :
    pull change signature second ((family signature).map (change.map step) node) =
      (family (under change signature)).map step (pull change signature first node) := by
  rcases node with ⟨label, branches⟩
  apply congrArg (Sigma.mk _)
  apply ContextualWTypes.Branches.ext
  intro next arrow branch
  exact branches.app_eq (change.map_comp step arrow).symm
    (ContextualWTypes.compositePosition signature.1.1 signature.1.2 label (change.map step) (change.map arrow) branch)
    (ContextualWTypes.compositePosition (under change signature).1.1 (under change signature).1.2 label step arrow branch)
    ((cast_heq _ _).trans (cast_heq _ _).symm)

theorem pull_identity (signature : Signature D) (point : D) (node : At signature point) :
    HEq (pull (Cat.identity D) signature point node) node := by
  rcases signature with ⟨⟨shape, position⟩, target⟩
  cases shape
  cases target
  rcases node with ⟨label, branches⟩
  apply heq_of_eq
  apply congrArg (Sigma.mk label)
  apply ContextualWTypes.Branches.ext
  intro _ _ _
  rfl

theorem pull_comp_data (first : D ⥤ E) (later : E ⥤ F) (signature : Signature F)
    {target : F} (node : At signature target)
    (middle : E) (atMiddle : later.obj middle = target) (point : D) (atPoint : first.obj point = middle) :
    HEq (pullData first (under later signature) (pullData later signature node middle atMiddle) point atPoint)
      (pullData (Cat.compose first later) signature node point ((congrArg later.obj atPoint).trans atMiddle)) := by
  cases atPoint
  cases atMiddle
  rfl

theorem pull_comp (first : D ⥤ E) (later : E ⥤ F) (signature : Signature F) (point : D)
    (node : At signature (later.obj (first.obj point))) :
    HEq (pull first (under later signature) point (pull later signature (first.obj point) node))
      (pull (Cat.compose first later) signature point node) := HEq.rfl

def castAt {first second : Signature D} (same : first = second) (point : D) : At first point → At second point := by
  cases same
  exact id

theorem castAt_heq {first second : Signature D} (same : first = second) (point : D) (node : At first point) :
    HEq (castAt same point node) node := by
  cases same
  rfl

theorem pull_congr {first second : D ⥤ E} (contexts : first = second)
    {leftSignature rightSignature : Signature E} (signatures : leftSignature = rightSignature)
    {leftPoint rightPoint : D} (points : leftPoint = rightPoint)
    (left : At leftSignature (first.obj leftPoint)) (right : At rightSignature (second.obj rightPoint)) (nodes : HEq left right) :
    HEq (pull first leftSignature leftPoint left) (pull second rightSignature rightPoint right) := by
  cases contexts
  cases signatures
  cases points
  cases eq_of_heq nodes
  rfl

theorem pullData_congr {first second : D ⥤ E} (contexts : first = second)
    {leftSignature rightSignature : Signature E} (signatures : leftSignature = rightSignature)
    {leftPoint rightPoint : D} (points : leftPoint = rightPoint) {X Y : E}
    (left : At leftSignature X) (right : At rightSignature Y) (nodes : HEq left right)
    (atLeft : first.obj leftPoint = X) (atRight : second.obj rightPoint = Y) :
    HEq (pullData first leftSignature left leftPoint atLeft) (pullData second rightSignature right rightPoint atRight) := by
  cases contexts
  cases signatures
  cases points
  have targets : X = Y := atLeft.symm.trans atRight
  cases targets
  cases eq_of_heq nodes
  rfl

theorem restrict_signature_heq {first second : Signature D} (signatures : first = second)
    {source target : D} (step : source ⟶ target) (left : At first source) (right : At second source) (nodes : HEq left right) :
    HEq ((family first).map step left) ((family second).map step right) := by
  cases signatures
  cases eq_of_heq nodes
  rfl

theorem pullData_restrict (change : D ⥤ E) (signature : Signature E)
    {first second : D} (step : first ⟶ second) {source target : E}
    (atSource : change.obj first = source) (atTarget : change.obj second = target)
    (actual : source ⟶ target) (arrows : HEq (change.map step) actual) (node : At signature source) :
    HEq (pullData change signature ((family signature).map actual node) second atTarget)
      ((family (under change signature)).map step (pullData change signature node first atSource)) := by
  cases atSource
  cases atTarget
  cases eq_of_heq arrows
  exact heq_of_eq (pull_restrict change signature step node)

def pullEquiv (change : ContextualWLocalChange.LocalFutures D E) (signature : Signature E) (point : D) :
    At signature (change.functor.obj point) ≃ At (under change.functor signature) point where
  toFun := pull change.functor signature point
  invFun node := ⟨node.1, ContextualWLocalChange.pushBranches change signature.1.1 signature.1.2 signature.2 point node.1 node.2⟩
  left_inv node := by
    rcases node with ⟨label, branches⟩
    exact congrArg (Sigma.mk label)
      (ContextualWLocalChange.push_pullBranches change signature.1.1 signature.1.2 signature.2 point label branches)
  right_inv node := by
    rcases node with ⟨label, branches⟩
    exact congrArg (Sigma.mk label)
      (ContextualWLocalChange.pull_pushBranches change signature.1.1 signature.1.2 signature.2 point label branches)

def pointEquiv (signature : Signature D) {first second : D} (same : first = second) : At signature first ≃ At signature second := by
  cases same
  exact Equiv.refl _

theorem pointEquiv_heq (signature : Signature D) {first second : D} (same : first = second) (node : At signature first) :
    HEq (pointEquiv signature same node) node := by
  cases same
  rfl

def signatureEquiv {first second : Signature D} (same : first = second) (point : D) : At first point ≃ At second point := by
  cases same
  exact Equiv.refl _

theorem signatureEquiv_heq {first second : Signature D} (same : first = second) (point : D) (node : At first point) :
    HEq (signatureEquiv same point node) node := by
  cases same
  rfl

theorem node_label_heq {first second : Signature D} (same : first = second) (point : D)
    (left : At first point) (right : At second point) (nodes : HEq left right) : HEq left.1 right.1 := by
  cases same
  cases eq_of_heq nodes
  rfl

theorem node_branches_heq {first second : Signature D} (same : first = second) (point : D)
    (left : At first point) (right : At second point) (nodes : HEq left right) : HEq left.2 right.2 := by
  cases same
  cases eq_of_heq nodes
  rfl

theorem branch_app_heq {first second : Signature D} (same : first = second) {point : D}
    (leftLabel : first.1.1.obj point) (rightLabel : second.1.1.obj point) (labels : HEq leftLabel rightLabel)
    (left : ContextualWTypes.Branches first.1.1 first.1.2 first.2 leftLabel)
    (right : ContextualWTypes.Branches second.1.1 second.1.2 second.2 rightLabel) (branches : HEq left right)
    (next : D) (firstArrow secondArrow : point ⟶ next) (arrows : HEq firstArrow secondArrow)
    (leftBranch : ContextualWTypes.Position first.1.1 first.1.2 leftLabel firstArrow)
    (rightBranch : ContextualWTypes.Position second.1.1 second.1.2 rightLabel secondArrow) (positions : HEq leftBranch rightBranch) :
    HEq (left.app next firstArrow leftBranch) (right.app next secondArrow rightBranch) := by
  cases same
  cases eq_of_heq labels
  cases eq_of_heq branches
  cases eq_of_heq arrows
  cases eq_of_heq positions
  rfl

theorem node_ext_heq {first second : Signature D} (same : first = second) (point : D)
    (left : At first point) (right : At second point) (labels : HEq left.1 right.1)
    (values : ∀ (next : D) (firstArrow secondArrow : point ⟶ next), HEq firstArrow secondArrow →
      ∀ (firstPosition : ContextualWTypes.Position first.1.1 first.1.2 left.1 firstArrow)
        (secondPosition : ContextualWTypes.Position second.1.1 second.1.2 right.1 secondArrow),
        HEq firstPosition secondPosition →
        HEq (left.2.app next firstArrow firstPosition) (right.2.app next secondArrow secondPosition)) : HEq left right := by
  cases same
  rcases left with ⟨label, branches⟩
  rcases right with ⟨otherLabel, otherBranches⟩
  cases eq_of_heq labels
  apply heq_of_eq
  apply congrArg (Sigma.mk label)
  apply ContextualWTypes.Branches.ext
  intro next arrow position
  exact eq_of_heq (values next arrow arrow HEq.rfl position position HEq.rfl)

end Mettapedia.TypeTheory.ContextualWPolynomialReindexing
