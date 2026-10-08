import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphFamilyBodyComparison
import Mettapedia.TypeTheory.ContextualSmallFamilyComprehension
import Mettapedia.TypeTheory.ContextualSmallFamilyIdentity

/-!
# Substitution of actual attached material families

Rebuilding the attached graph after parameter substitution and retaining
the original graph have inverse natural receipt comparisons. Their
complete section decoders commute. An independent full-future matching
compares the two material carriers using their actual body readings.
The authored diagrams need not be equal.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphFamilyBodySubstitution

open CategoryTheory Mettapedia.TypeTheory ContextualWitnessCover
open ContextualSmallFamilyUniverse ContextualGraphDiagrams ContextualRealizedGraphs
open ContextualGraphFamilyBodies

universe u
variable {D : Type u} [Category.{u} D] {base other : D ⥤ Type u}
variable (native : base.Elements ⥤ Type u) (termReading : NaturalHom (total native) (values D))
variable (change : NaturalHom other base)

abbrev nativeUnder := restrict (elementMap change) native

def readingUnder : NaturalHom (total (nativeUnder native change)) (values D) :=
  (ContextualSmallFamilyComprehension.totalChange native change).comp termReading

abbrev retainedParent := change.comp (parent native termReading)
abbrev retained := ContextualGraphReceiptFamilies.along (retainedParent native termReading change)
abbrev rebuilt := literal (nativeUnder native change) (readingUnder native termReading change)

def forward : NaturalHom (retained native termReading change) (rebuilt native termReading change) where
  app point receipt := encode (nativeUnder native change) (readingUnder native termReading change) point
    (decode native termReading ((elementMap change).obj point) receipt)
  naturality {_first second} step receipt :=
    (encode_naturality (nativeUnder native change) (readingUnder native termReading change) step _).trans
      (congrArg (encode (nativeUnder native change) (readingUnder native termReading change) second)
        (decode_naturality native termReading ((elementMap change).map step) receipt).symm)

def backward : NaturalHom (rebuilt native termReading change) (retained native termReading change) where
  app point receipt := encode native termReading ((elementMap change).obj point)
    (decode (nativeUnder native change) (readingUnder native termReading change) point receipt)
  naturality {_first second} step receipt :=
    (encode_naturality native termReading ((elementMap change).map step) _).trans
      (congrArg (encode native termReading ((elementMap change).obj second))
        (decode_naturality (nativeUnder native change) (readingUnder native termReading change) step receipt).symm)

theorem forward_backward : (forward native termReading change).comp (backward native termReading change) =
    ContextualSmallMapConstructions.identity (retained native termReading change) := by
  apply NaturalHom.ext
  intro point receipt
  exact encode_decode native termReading ((elementMap change).obj point) receipt

theorem backward_forward : (backward native termReading change).comp (forward native termReading change) =
    ContextualSmallMapConstructions.identity (rebuilt native termReading change) := by
  apply NaturalHom.ext
  intro point receipt
  exact encode_decode (nativeUnder native change) (readingUnder native termReading change) point receipt

def sectionComparison : (retained native termReading change).sections ≃
    (rebuilt native termReading change).sections where
  toFun := (forward native termReading change).mapSection
  invFun := (backward native termReading change).mapSection
  left_inv term := by
    apply Subtype.ext
    funext point
    exact encode_decode native termReading ((elementMap change).obj point) (term.val point)
  right_inv term := by
    apply Subtype.ext
    funext point
    exact encode_decode (nativeUnder native change) (readingUnder native termReading change) point (term.val point)

def pullSection (term : (literal native termReading).sections) : (retained native termReading change).sections :=
  ⟨fun point => term.val ((elementMap change).obj point),
    fun {_ _} step => term.property ((elementMap change).map step)⟩

def substituteSection (term : (literal native termReading).sections) :
    (rebuilt native termReading change).sections :=
  sectionComparison native termReading change (pullSection native termReading change term)

theorem decoder_substitution (term : (literal native termReading).sections) :
    sectionDecoder (nativeUnder native change) (readingUnder native termReading change)
        (substituteSection native termReading change term) =
      ContextualSmallFamilyIdentity.reindexSection change native (sectionDecoder native termReading term) := by
  apply Subtype.ext
  funext point
  rfl

theorem substitution_identity (term : (literal native termReading).sections) :
    substituteSection native termReading (ContextualSmallMapConstructions.identity base) term = term := by
  apply Subtype.ext
  funext point
  exact encode_decode native termReading point (term.val point)

theorem substitution_composition {third : D ⥤ Type u} (later : NaturalHom third other)
    (term : (literal native termReading).sections) :
    substituteSection (nativeUnder native change) (readingUnder native termReading change) later
        (substituteSection native termReading change term) =
      substituteSection native termReading (later.comp change) term := by
  apply Subtype.ext
  funext point
  rfl

def membersForth (point : other.Elements) (element : Value D point.1)
    (proof : Member element (carrier (nativeUnder native change)
      (readingUnder native termReading change) point.1 point.2)) :
    Member element (carrier native termReading point.1 (change.app point.1 point.2)) :=
  let decoded := ContextualGraphFamilyBodyComparison.memberDecode (nativeUnder native change)
    (readingUnder native termReading change) point element proof
  ContextualGraphFamilyBodyComparison.memberIntro native termReading
    ((elementMap change).obj point) element decoded.1 decoded.2

def membersBack (point : other.Elements) (element : Value D point.1)
    (proof : Member element (carrier native termReading point.1 (change.app point.1 point.2))) :
    Member element (carrier (nativeUnder native change)
      (readingUnder native termReading change) point.1 point.2) :=
  let decoded := ContextualGraphFamilyBodyComparison.memberDecode native termReading
    ((elementMap change).obj point) element proof
  ContextualGraphFamilyBodyComparison.memberIntro (nativeUnder native change)
    (readingUnder native termReading change) point element decoded.1 decoded.2

/-- Both actual parent maps commute with every future arrow. Their
current membership comparisons therefore extend to full-future matching. -/
def carrierComparison (point : other.Elements) :
    Equal (carrier (nativeUnder native change) (readingUnder native termReading change) point.1 point.2)
      (carrier native termReading point.1 (change.app point.1 point.2)) :=
  extensionality
    (fun target arrival element proof =>
      Member.transportParent (Equal.ofEq ((retainedParent native termReading change).naturality arrival point.2).symm)
        (membersForth native termReading change ⟨target, other.map arrival point.2⟩ element
          (Member.transportParent (Equal.ofEq ((parent (nativeUnder native change)
            (readingUnder native termReading change)).naturality arrival point.2)) proof)))
    (fun target arrival element proof =>
      Member.transportParent (Equal.ofEq ((parent (nativeUnder native change)
        (readingUnder native termReading change)).naturality arrival point.2).symm)
        (membersBack native termReading change ⟨target, other.map arrival point.2⟩ element
          (Member.transportParent (Equal.ofEq ((retainedParent native termReading change).naturality arrival point.2)) proof)))

/-- The natural receipt comparison preserves the declared material
element at every parameter; no equality of matching strategies is used. -/
def sectionMaterialComparison (term : (retained native termReading change).sections) (point : other.Elements) :
    Equal ((ContextualGraphReceiptFamilies.sectionReading
      (parent (nativeUnder native change) (readingUnder native termReading change))
      (sectionComparison native termReading change term)).app point.1 point.2)
      ((ContextualGraphReceiptFamilies.sectionReading (retainedParent native termReading change) term).app point.1 point.2) :=
  (ContextualGraphFamilyBodyComparison.sectionComparison (nativeUnder native change)
    (readingUnder native termReading change) (sectionComparison native termReading change term) point).symm.trans
    (ContextualGraphFamilyBodyComparison.receiptComparison native termReading
      ((elementMap change).obj point) (term.val point))

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphFamilyBodySubstitution
