import Mettapedia.TypeTheory.ContextualWLocalChange

/-!
# Constructive W reindexing and signature coherence

Actual context functors induce indexed raw-tree operations. Their laws
are proved by tree induction, with signature and endpoint transports
made explicit. These operations need no inverse future functor; the
separate local-inverse construction supplies the stronger equivalences.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualWReindexing

open CategoryTheory MaterialSets.Hypersets
open ContextualWTypes (RawTree Position Natural NaturalTree)
open PowerClassPresheafBaseChange
open Mettapedia.GSLT.Topos.ConstructivePresheaf

universe u
variable {D E F : Type u} [Category.{u} D] [Category.{u} E] [Category.{u} F]

abbrev Signature (D : Type u) [Category.{u} D] :=
  Σ shape : D ⥤ Type u, shape.Elements ⥤ Type u

def under (change : D ⥤ E) (signature : Signature E) : Signature D :=
  ⟨restrict change signature.1, restrict (Cat.elementsMap change signature.1) signature.2⟩

theorem under_identity (signature : Signature D) :
    under (Cat.identity D) signature = signature := by
  rcases signature with ⟨shape, position⟩
  cases shape
  rfl

theorem under_comp (first : D ⥤ E) (later : E ⥤ F) (signature : Signature F) :
    under (Cat.compose first later) signature = under first (under later signature) := rfl

abbrev Raw (signature : Signature D) (point : D) := RawTree signature.1 signature.2 point
abbrev Tree (signature : Signature D) (point : D) := NaturalTree signature.1 signature.2 point

noncomputable def pullData (change : D ⥤ E) (signature : Signature E)
    {target : E} (tree : Raw signature target) :
    (point : D) → change.obj point = target → Raw (under change signature) point :=
  RawTree.rec (motive := fun target _ => (point : D) → change.obj point = target →
      Raw (under change signature) point)
    (fun {target} label _children earlier point same => by
      cases same
      exact .sup label (fun next arrow branch => earlier (change.obj next)
        (change.map arrow) branch next rfl)) tree

noncomputable def pull (change : D ⥤ E) (signature : Signature E) (point : D)
    (tree : Raw signature (change.obj point)) : Raw (under change signature) point :=
  pullData change signature tree point rfl

theorem pull_sup (change : D ⥤ E) (signature : Signature E) (point : D)
    (label : signature.1.obj (change.obj point))
    (children : (target : E) → (arrow : change.obj point ⟶ target) →
      Position signature.1 signature.2 label arrow → Raw signature target) :
    pull change signature point (.sup label children) = .sup label (fun next arrow branch =>
      pull change signature next (children (change.obj next) (change.map arrow) branch)) := rfl

theorem pullData_heq (change : D ⥤ E) (signature : Signature E)
    {first second : D} {X Y : E} (points : first = second)
    (left : Raw signature X) (right : Raw signature Y) (trees : HEq left right)
    (atFirst : change.obj first = X) (atSecond : change.obj second = Y) :
    HEq (pullData change signature left first atFirst) (pullData change signature right second atSecond) := by
  cases points
  have targets : X = Y := atFirst.symm.trans atSecond
  cases targets
  cases eq_of_heq trees
  rfl

theorem pull_identity_data (signature : Signature D) {target : D} (tree : Raw signature target) :
    ∀ point : D, ∀ same : point = target,
      HEq (pullData (Cat.identity D) signature tree point same) tree := by
  rcases signature with ⟨shape, position⟩
  cases shape
  induction tree with
  | @sup target label children earlier =>
    intro point same
    cases same
    apply heq_of_eq
    apply RawTree.sup_eq_of_cast rfl
    intro next arrow branch
    exact eq_of_heq (earlier next arrow branch next rfl)

theorem pull_identity (signature : Signature D) (point : D) (tree : Raw signature point) :
    HEq (pull (Cat.identity D) signature point tree) tree :=
  pull_identity_data signature tree point rfl

theorem pull_comp_data (first : D ⥤ E) (later : E ⥤ F) (signature : Signature F)
    {target : F} (tree : Raw signature target) :
    ∀ middle : E, ∀ atMiddle : later.obj middle = target, ∀ point : D, ∀ atPoint : first.obj point = middle,
      HEq (pullData first (under later signature) (pullData later signature tree middle atMiddle) point atPoint)
        (pullData (Cat.compose first later) signature tree point ((congrArg later.obj atPoint).trans atMiddle)) := by
  induction tree with
  | @sup target label children earlier =>
    intro middle atMiddle point atPoint
    cases atPoint
    cases atMiddle
    apply heq_of_eq
    apply RawTree.sup_eq_of_cast rfl
    intro next arrow branch
    exact eq_of_heq (earlier (later.obj (first.obj next)) (later.map (first.map arrow)) branch
      (first.obj next) rfl next rfl)

theorem pull_comp (first : D ⥤ E) (later : E ⥤ F) (signature : Signature F) (point : D)
    (tree : Raw signature (later.obj (first.obj point))) :
    HEq (pull first (under later signature) point (pull later signature (first.obj point) tree))
      (pull (Cat.compose first later) signature point tree) :=
  pull_comp_data first later signature tree (first.obj point) rfl point rfl

theorem pull_restrict (change : D ⥤ E) (signature : Signature E)
    {first second : D} (step : first ⟶ second) (tree : Raw signature (change.obj first)) :
    pull change signature second (ContextualWTypes.restrict signature.1 signature.2 (change.map step) tree) =
      ContextualWTypes.restrict (under change signature).1 (under change signature).2 step
        (pull change signature first tree) := by
  cases tree with
  | sup label children =>
    apply RawTree.sup_eq_of_cast rfl
    intro next arrow branch
    apply congrArg (pull change signature next)
    exact RawTree.children_eq label children (change.map_comp step arrow).symm
      (ContextualWTypes.compositePosition signature.1 signature.2 label (change.map step) (change.map arrow) branch)
      (ContextualWTypes.compositePosition (under change signature).1 (under change signature).2 label step arrow branch)
      ((cast_heq _ _).trans (cast_heq _ _).symm)

theorem pull_natural_data (change : D ⥤ E) (signature : Signature E) {target : E}
    (tree : Raw signature target) :
    ∀ point : D, ∀ same : change.obj point = target,
      Natural signature.1 signature.2 tree →
        Natural (under change signature).1 (under change signature).2 (pullData change signature tree point same) := by
  induction tree with
  | @sup target label children earlier =>
    intro point same natural
    cases same
    constructor
    · intro next arrow branch
      exact earlier _ _ _ next rfl (natural.1 (change.obj next) (change.map arrow) branch)
    · intro Y Z first later branch
      change ContextualWTypes.restrict (under change signature).1 (under change signature).2 later
        (pull change signature Y (children (change.obj Y) (change.map first) branch)) =
        pull change signature Z (children (change.obj Z) (change.map (first ≫ later))
          (ContextualWTypes.positionAlong (under change signature).1 (under change signature).2 label first later branch))
      rw [← pull_restrict]
      apply congrArg (pull change signature Z)
      exact (natural.2 _ _ (change.map first) (change.map later) branch).trans
        (RawTree.children_eq label children (change.map_comp first later).symm
          (ContextualWTypes.positionAlong signature.1 signature.2 label (change.map first) (change.map later) branch)
          (ContextualWTypes.positionAlong (under change signature).1 (under change signature).2 label first later branch)
          ((cast_heq _ _).trans (cast_heq _ _).symm))

noncomputable def pullTree (change : D ⥤ E) (signature : Signature E) (point : D)
    (tree : Tree signature (change.obj point)) : Tree (under change signature) point :=
  ⟨pull change signature point tree.val, pull_natural_data change signature tree.val point rfl tree.property⟩

/-- Whole-signature equality acts by dependent equality elimination. -/
def castTree {first second : Signature D} (same : first = second) (point : D) :
    Tree first point → Tree second point := by
  cases same
  exact id

theorem castTree_raw {first second : Signature D} (same : first = second) (point : D)
    (tree : Tree first point) : HEq (castTree same point tree).val tree.val := by
  cases same
  rfl

theorem pull_congr {first second : D ⥤ E} (contexts : first = second)
    {leftSignature rightSignature : Signature E} (signatures : leftSignature = rightSignature)
    {leftPoint rightPoint : D} (points : leftPoint = rightPoint)
    (left : Raw leftSignature (first.obj leftPoint)) (right : Raw rightSignature (second.obj rightPoint))
    (trees : HEq left right) :
    HEq (pull first leftSignature leftPoint left) (pull second rightSignature rightPoint right) := by
  cases contexts
  cases signatures
  cases points
  cases eq_of_heq trees
  rfl

theorem restrict_signature_heq {first second : Signature D} (signatures : first = second)
    {source target : D} (step : source ⟶ target) (left : Raw first source) (right : Raw second source)
    (trees : HEq left right) :
    HEq (ContextualWTypes.restrict first.1 first.2 step left)
      (ContextualWTypes.restrict second.1 second.2 step right) := by
  cases signatures
  cases eq_of_heq trees
  rfl

theorem position_transport_heq {first second : D ⥤ Type u} (same : first = second)
    (position : first.Elements ⥤ Type u) (other : second.Elements ⥤ Type u)
    (transport : restrict (Cat.elementsTransport same.symm) position = other) : HEq position other := by
  cases same
  change restrict (Cat.identity _) position = other at transport
  rw [Cat.restrict_identity] at transport
  exact heq_of_eq transport

theorem pullData_congr {first second : D ⥤ E} (contexts : first = second)
    {leftSignature rightSignature : Signature E} (signatures : leftSignature = rightSignature)
    {leftPoint rightPoint : D} (points : leftPoint = rightPoint) {X Y : E}
    (left : Raw leftSignature X) (right : Raw rightSignature Y) (trees : HEq left right)
    (atLeft : first.obj leftPoint = X) (atRight : second.obj rightPoint = Y) :
    HEq (pullData first leftSignature left leftPoint atLeft)
      (pullData second rightSignature right rightPoint atRight) := by
  cases contexts
  cases signatures
  cases points
  have targets : X = Y := atLeft.symm.trans atRight
  cases targets
  cases eq_of_heq trees
  rfl

theorem pullData_restrict (change : D ⥤ E) (signature : Signature E)
    {first second : D} (step : first ⟶ second) {source target : E}
    (atSource : change.obj first = source) (atTarget : change.obj second = target)
    (actual : source ⟶ target) (arrows : HEq (change.map step) actual) (tree : Raw signature source) :
    HEq (pullData change signature (ContextualWTypes.restrict signature.1 signature.2 actual tree) second atTarget)
      (ContextualWTypes.restrict (under change signature).1 (under change signature).2 step
        (pullData change signature tree first atSource)) := by
  cases atSource
  cases atTarget
  cases eq_of_heq arrows
  exact heq_of_eq (pull_restrict change signature step tree)

def pointEquiv (signature : Signature D) {first second : D} (same : first = second) :
    Tree signature first ≃ Tree signature second := by
  cases same
  exact Equiv.refl _

theorem pointEquiv_raw (signature : Signature D) {first second : D} (same : first = second)
    (tree : Tree signature first) : HEq (pointEquiv signature same tree).val tree.val := by
  cases same
  rfl

def signatureEquiv {first second : Signature D} (same : first = second) (point : D) :
    Tree first point ≃ Tree second point := by
  cases same
  exact Equiv.refl _

theorem signatureEquiv_raw {first second : Signature D} (same : first = second) (point : D)
    (tree : Tree first point) : HEq (signatureEquiv same point tree).val tree.val := by
  cases same
  rfl

theorem sup_heq {first second : Signature D} (same : first = second)
    {firstPoint secondPoint : D} (points : firstPoint = secondPoint)
    (leftLabel : first.1.obj firstPoint) (rightLabel : second.1.obj secondPoint) (labels : HEq leftLabel rightLabel)
    (leftChildren : (next : D) → (arrow : firstPoint ⟶ next) → Position first.1 first.2 leftLabel arrow → Raw first next)
    (rightChildren : (next : D) → (arrow : secondPoint ⟶ next) → Position second.1 second.2 rightLabel arrow → Raw second next)
    (children : ∀ (next : D) (firstArrow : firstPoint ⟶ next) (secondArrow : secondPoint ⟶ next),
      HEq firstArrow secondArrow →
      ∀ (leftBranch : Position first.1 first.2 leftLabel firstArrow) (rightBranch : Position second.1 second.2 rightLabel secondArrow),
        HEq leftBranch rightBranch → HEq (leftChildren next firstArrow leftBranch) (rightChildren next secondArrow rightBranch)) :
    HEq (RawTree.sup leftLabel leftChildren) (RawTree.sup rightLabel rightChildren) := by
  cases same
  cases points
  cases eq_of_heq labels
  apply heq_of_eq
  apply RawTree.sup_eq_of_cast rfl
  intro next arrow branch
  exact eq_of_heq (children next arrow arrow HEq.rfl branch branch HEq.rfl)

end Mettapedia.TypeTheory.ContextualWReindexing
