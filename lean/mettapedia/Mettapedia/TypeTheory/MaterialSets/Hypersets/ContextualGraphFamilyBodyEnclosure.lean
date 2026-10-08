import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphFamilyBodyComparison
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphUniverseLift
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphFamilyEnclosure

/-!
# Actual material family bodies at the successor bound

Wider lower parameters and original-small fibres yield one strict global
attached-body graph on the raised site. Its literal decoder recovers
whole original sections, and its material members are precisely the
raised declared element denotations. The universal literal member family
is a concrete instance: its attached carrier matches the original graph
value after raising, with both directions constructed at every future.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphFamilyBodyEnclosure

open CategoryTheory Mettapedia.TypeTheory ContextualWitnessCover
open ContextualSmallFamilyUniverse ContextualGraphDiagrams ContextualRealizedGraphs
universe u
variable {D : Type u} [Category.{u} D] {base : D ⥤ Type (u+1)}
variable (native : base.Elements ⥤ Type u) (termReading : NaturalHom (total native) (values D))

abbrev Upper := ContextualGraphUniverseLift.Raised (D := D)
abbrev upperNative := ContextualFutureSiteLift.family base native

def upperReading : NaturalHom (total (upperNative native)) (values (Upper (D := D))) where
  app _ receipt := ContextualGraphUniverseLift.value (termReading.app _ ⟨receipt.1, receipt.2.down⟩)
  naturality {_first _second} arrival receipt :=
    congrArg ContextualGraphUniverseLift.value (termReading.naturality arrival.down ⟨receipt.1, receipt.2.down⟩)

def parent : NaturalHom (ContextualFutureSiteLift.base base) (values (Upper (D := D))) :=
  ContextualGraphFamilyBodies.parent (upperNative native) (upperReading native termReading)

def carrier (point : Upper (D := D)) (parameter : base.obj point.down) : Value (Upper (D := D)) point :=
  (parent native termReading).app point parameter

abbrev literal := ContextualGraphFamilyBodies.literal (upperNative native) (upperReading native termReading)

def decoder (point : Upper (D := D)) (parameter : base.obj point.down) :
    Child (Upper (D := D)) (carrier native termReading point parameter) ≃ native.obj ⟨point.down, parameter⟩ :=
  (ContextualGraphFamilyBodies.decoder (upperNative native) (upperReading native termReading) ⟨point, parameter⟩).trans
    Equiv.ulift

def sectionDecoder : (literal native termReading).sections ≃ native.sections :=
  (ContextualGraphFamilyBodies.sectionDecoder (upperNative native) (upperReading native termReading)).trans
    (ContextualFutureSiteLift.sections base native).symm

def selectionDecoder : native.sections ≃ ContextualGraphReceiptFamilies.Selection (parent native termReading) :=
  (ContextualFutureSiteLift.sections base native).trans
    (ContextualGraphFamilyBodies.selectionDecoder (upperNative native) (upperReading native termReading))

def childComparison (point : Upper (D := D)) (parameter : base.obj point.down)
    (term : native.obj ⟨point.down, parameter⟩) :
    Equal (ContextualGraphUniverseLift.value (termReading.app point.down ⟨parameter, term⟩))
      (childValue _ (carrier native termReading point parameter) ((decoder native termReading point parameter).symm term)) :=
  ContextualGraphFamilyBodyComparison.childComparison (upperNative native) (upperReading native termReading)
    ⟨point, parameter⟩ (ULift.up term)

theorem material_membership_iff (point : Upper (D := D)) (parameter : base.obj point.down)
    (element : Value D point.down) :
    Nonempty (Member (ContextualGraphUniverseLift.value element) (carrier native termReading point parameter)) ↔
      ∃ term : native.obj ⟨point.down, parameter⟩,
        Nonempty (Equal element (termReading.app point.down ⟨parameter, term⟩)) := by
  constructor
  · rintro ⟨membership⟩
    let receipt := ContextualGraphFamilyBodyComparison.memberDecode (upperNative native) (upperReading native termReading)
      ⟨point, parameter⟩ (ContextualGraphUniverseLift.value element) membership
    exact ⟨receipt.1.down, ⟨ContextualGraphUniverseLift.reflect receipt.2⟩⟩
  · rintro ⟨term, ⟨matching⟩⟩
    exact ⟨ContextualGraphFamilyBodyComparison.memberIntro (upperNative native) (upperReading native termReading)
      ⟨point, parameter⟩ _ (ULift.up term) (ContextualGraphUniverseLift.preserve matching)⟩

def originalSelection (term : native.sections) : NaturalHom base (total native) where
  app point parameter := ⟨parameter, term.val ⟨point, parameter⟩⟩
  naturality {first second} arrival parameter :=
    Sigma.ext rfl (heq_of_eq (term.property (CategoryOfElements.homMk (F := base)
      ⟨first, parameter⟩ ⟨second, base.map arrival parameter⟩ arrival rfl)))

def originalSectionReading (term : (literal native termReading).sections) : NaturalHom base (values D) :=
  (originalSelection native (sectionDecoder native termReading term)).comp termReading

def sectionMaterialComparison (term : (literal native termReading).sections)
    (point : Upper (D := D)) (parameter : base.obj point.down) :
    Equal (ContextualGraphUniverseLift.value ((originalSectionReading native termReading term).app point.down parameter))
      ((ContextualGraphReceiptFamilies.sectionReading (parent native termReading) term).app point parameter) :=
  ContextualGraphFamilyBodyComparison.sectionComparison (upperNative native) (upperReading native termReading)
    term ⟨point, parameter⟩

section ActualMembers

abbrev members := ContextualGraphReceiptFamilies.family D
abbrev memberReading := ContextualGraphReceiptFamilies.childReading D

def membersCarrier (point : Upper (D := D)) (original : Value D point.down) : Value (Upper (D := D)) point :=
  carrier (members (D := D)) (memberReading (D := D)) point original

def membersForth (point : Upper (D := D)) (original : Value D point.down) (element : Value (Upper (D := D)) point)
    (proof : Member element (membersCarrier point original)) :
    Member element (ContextualGraphUniverseLift.value original) :=
  let decoded := ContextualGraphFamilyBodyComparison.memberDecode
    (upperNative (members (D := D))) (upperReading (members (D := D)) (memberReading (D := D)))
    ⟨point, original⟩ element proof
  ⟨(ContextualGraphUniverseLift.childDecoder original).symm decoded.1.down, decoded.2⟩

def membersBack (point : Upper (D := D)) (original : Value D point.down) (element : Value (Upper (D := D)) point)
    (proof : Member element (ContextualGraphUniverseLift.value original)) :
    Member element (membersCarrier point original) :=
  ContextualGraphFamilyBodyComparison.memberIntro
    (upperNative (members (D := D))) (upperReading (members (D := D)) (memberReading (D := D)))
    ⟨point, original⟩ element (ULift.up (ContextualGraphUniverseLift.childDecoder original proof.1)) proof.2

/-- The actual member family of every varying graph has the expected
material carrier at the successor bound. Arbitrary upper elements are
covered by the two matching directions; they need not be lower images. -/
def membersCarrierEquality (point : Upper (D := D)) (original : Value D point.down) :
    Equal (membersCarrier point original) (ContextualGraphUniverseLift.value original) :=
  extensionality
    (fun target arrival element proof =>
      Member.transportParent (Equal.ofEq (ContextualGraphUniverseLift.value_move arrival original).symm)
        (membersForth target (move D arrival.down original) element
          (Member.transportParent (Equal.ofEq ((parent (members (D := D)) (memberReading (D := D))).naturality
            arrival original)) proof)))
    (fun target arrival element proof =>
      Member.transportParent (Equal.ofEq ((parent (members (D := D)) (memberReading (D := D))).naturality
          arrival original).symm)
        (membersBack target (move D arrival.down original) element
          (Member.transportParent (Equal.ofEq (ContextualGraphUniverseLift.value_move arrival original)) proof)))

end ActualMembers

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphFamilyBodyEnclosure
