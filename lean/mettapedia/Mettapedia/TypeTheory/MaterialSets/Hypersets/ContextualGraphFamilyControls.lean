import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphFamilyProducts
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphFamilyIdentity
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphFamilyEnclosure
import Mathlib.CategoryTheory.Category.Preorder

/-!
# Controls for contextual receipt representations and their material limit

The represented native family grows at every natural stage. Complete
future products retain arguments unavailable at the current stage.
Distinct receipt cardinalities can nevertheless have matching material
roots: receipt representation is not extensional element encoding.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphFamilyControls

open CategoryTheory Mettapedia.TypeTheory ContextualWitnessCover
open ContextualGraphDiagrams ContextualRealizedGraphs ContextualSmallFamilyUniverse
open ContextualGraphFamilyRepresentation ContextualGraphFamilyProducts

section Leaves
universe u
variable {D : Type u} [Category.{u} D] {base other : D ⥤ Type u}
variable (native : base.Elements ⥤ Type u) (next : other.Elements ⥤ Type u)

def leaf (point : base.Elements) (term : native.obj point) : Value D point.1 :=
  ⟨diagram native, .inr ⟨point.2, term⟩⟩

def leavesEqual (point : D) (parameter : base.obj point) (otherParameter : other.obj point)
    (first : native.obj ⟨point, parameter⟩) (second : next.obj ⟨point, otherParameter⟩) :
    Equal (leaf native ⟨point, parameter⟩ first) (leaf next ⟨point, otherParameter⟩ second) :=
  ContextualGraphRealizers.roll (diagram native) (diagram next)
    (fun _ child => False.elim (by cases child.property))
    (fun _ child => False.elim (by cases child.property))

theorem child_reading (point : base.Elements) (receipt : (literal native).obj point) :
    childValue D (value native point.1 point.2) receipt = leaf native point (decode native point receipt) :=
  congrArg (childValue D (value native point.1 point.2)) (encode_decode native point receipt).symm

end Leaves

def unitBase : Nat ⥤ Type where
  obj _ := PUnit
  map _ := TypeCat.ofHom id
  map_id _ := rfl
  map_comp _ _ := rfl

def constant (A : Type) : unitBase.Elements ⥤ Type where
  obj _ := A
  map _ := TypeCat.ofHom id
  map_id _ := rfl
  map_comp _ _ := rfl

def growing : unitBase.Elements ⥤ Type where
  obj point := Fin (point.1+1)
  map {_first _second} step := TypeCat.ofHom fun index =>
    ⟨index.val, Nat.lt_of_lt_of_le index.isLt (Nat.succ_le_succ (leOfHom step.1))⟩
  map_id _ := rfl
  map_comp _ _ := rfl

def parameter (stage : Nat) : unitBase.Elements := ⟨stage, PUnit.unit⟩
def stageStep (stage : Nat) : parameter stage ⟶ parameter (stage+1) :=
  ⟨homOfLE (Nat.le_succ stage), rfl⟩
def newest (stage : Nat) : (literal growing).obj (parameter (stage+1)) :=
  encode growing (parameter (stage+1)) ⟨stage+1, Nat.lt_succ_self _⟩

theorem every_stage_has_new_receipt (stage : Nat) :
    ¬ ∃ earlier : (literal growing).obj (parameter stage),
      (literal growing).map (stageStep stage) earlier = newest stage := by
  rintro ⟨earlier, same⟩
  have decoded := (decode_naturality growing (stageStep stage) earlier).symm.trans
    (congrArg (decode growing (parameter (stage+1))) same)
  have numeric := congrArg Fin.val decoded
  exact (Nat.ne_of_lt (decode growing (parameter stage) earlier).isLt) numeric

/-- Matching keeps only membership behavior; the occurrence decoders still
have one and two distinct values, respectively. -/
def unit_bool_material_equal (stage : Nat) :
    Equal (value (constant PUnit) stage PUnit.unit) (value (constant Bool) stage PUnit.unit) :=
  ContextualGraphRealizers.roll (diagram (constant PUnit)) (diagram (constant Bool))
    (fun future receipt => ⟨encode (constant Bool) (parameter future.1) false,
      (Equal.ofEq (child_reading (constant PUnit) (parameter future.1) receipt)).trans
        (leavesEqual (constant PUnit) (constant Bool) future.1 PUnit.unit PUnit.unit
          (decode (constant PUnit) (parameter future.1) receipt) false)⟩)
    (fun future receipt => ⟨encode (constant PUnit) (parameter future.1) PUnit.unit,
      (leavesEqual (constant PUnit) (constant Bool) future.1 PUnit.unit PUnit.unit
        PUnit.unit (decode (constant Bool) (parameter future.1) receipt)).trans
        (Equal.ofEq (child_reading (constant Bool) (parameter future.1) receipt)).symm⟩)

theorem matching_does_not_give_receipt_equivalence (stage : Nat) :
    ¬ Nonempty ((literal (constant PUnit)).obj (parameter stage) ≃
      (literal (constant Bool)).obj (parameter stage)) := by
  rintro ⟨equivalence⟩
  let native := (decoder (constant PUnit) (parameter stage)).symm.trans
    (equivalence.trans (decoder (constant Bool) (parameter stage)))
  have same : native.symm false = native.symm true := @Subsingleton.elim PUnit inferInstance _ _
  have impossible : (false : Bool) = true :=
    (native.apply_symm_apply false).symm.trans ((congrArg native same).trans (native.apply_symm_apply true))
  cases impossible

def boolBody : (total growing).Elements ⥤ Type where
  obj _ := Bool
  map _ := TypeCat.ofHom id
  map_id _ := rfl
  map_comp _ _ := rfl

def allFalse : boolBody.sections := ⟨fun _ => false, fun {_ _} _ => rfl⟩
def freshTrue : boolBody.sections :=
  ⟨fun point => decide (0 < point.2.2.val), by
    intro first second step
    exact congrArg (fun receipt : (total growing).obj second.1 => decide (0 < receipt.2.val)) step.2⟩

def falseFunction : (literal (ContextualSmallFamilyComprehension.piDisplayed growing boolBody)).sections :=
  lambdaEquiv growing boolBody ((sectionDecoder boolBody).symm allFalse)
def futureFunction : (literal (ContextualSmallFamilyComprehension.piDisplayed growing boolBody)).sections :=
  lambdaEquiv growing boolBody ((sectionDecoder boolBody).symm freshTrue)

def futureArgument : (ContextualSmallFamilyTypeFormers.futureDomain growing (parameter 0)).Elements :=
  ⟨⟨1, homOfLE (by decide : 0 ≤ 1)⟩, ⟨1, by decide⟩⟩
def currentArgument : (ContextualSmallFamilyTypeFormers.futureDomain growing (parameter 0)).Elements :=
  ⟨⟨0, 𝟙 0⟩, ⟨0, by decide⟩⟩

theorem current_product_readings_agree :
    (decode _ (parameter 0) (falseFunction.val (parameter 0))).val currentArgument =
      (decode _ (parameter 0) (futureFunction.val (parameter 0))).val currentArgument := rfl

theorem future_product_readings_differ :
    (decode _ (parameter 0) (falseFunction.val (parameter 0))).val futureArgument ≠
      (decode _ (parameter 0) (futureFunction.val (parameter 0))).val futureArgument := by
  change (false : Bool) ≠ true
  decide

theorem whole_functions_differ : falseFunction ≠ futureFunction := by
  intro same
  exact future_product_readings_differ (congrArg (fun term :
      (literal (ContextualSmallFamilyComprehension.piDisplayed growing boolBody)).sections =>
    (decode (ContextualSmallFamilyComprehension.piDisplayed growing boolBody)
      (parameter 0) (term.val (parameter 0))).val futureArgument) same)

def endpointMethod :
    (literal (ContextualSmallFamilyIdentity.reindex
      (ContextualSmallFamilyIdentity.endpointMotive growing) (ContextualSmallFamilyIdentity.diagonal growing))).sections :=
  (sectionDecoder _).symm (ContextualSmallFamilyIdentity.endpointMethod growing)

theorem endpoint_J_decodes (point : (ContextualSmallFamilyIdentity.identityContext growing).Elements) :
    decode _ point ((ContextualGraphFamilyIdentity.receiptJ growing
      (ContextualSmallFamilyIdentity.endpointMotive growing) endpointMethod).val point) = point.2.1.1.2 := by
  have square := ContextualGraphFamilyIdentity.receiptJ_native growing
    (ContextualSmallFamilyIdentity.endpointMotive growing) endpointMethod
  exact (congrArg (fun term => term.val point) square).trans
    (ContextualSmallFamilyIdentity.J_endpoint_value growing point)

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphFamilyControls
