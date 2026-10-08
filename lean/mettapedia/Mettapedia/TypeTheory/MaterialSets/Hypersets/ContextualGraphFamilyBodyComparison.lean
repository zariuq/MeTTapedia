import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphFamilyBodies

/-!
# Full future comparison of attached bodies and their declared denotations

An explicit coiteration compares every internal attached node with the
same node of its actual contextual body. Both matching directions retain
the receipt and every future arrow. Material membership is therefore
exactly witnessed by a native receipt and matching with its declared
body; the construction does not replace that body with a terminal tag.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphFamilyBodyComparison

open CategoryTheory Mettapedia.TypeTheory ContextualWitnessCover
open ContextualGraphDiagrams ContextualSmallFamilyUniverse ContextualRealizedGraphs
open ContextualGraphFamilyBodies
universe u
variable {D : Type u} [Category.{u} D] {base : D ⥤ Type u}
variable (native : base.Elements ⥤ Type u) (termReading : NaturalHom (total native) (values D))

abbrev BodyReceipt (point : D) := (total (bodyNodes native termReading)).obj point

def embedChild {point : D} (receipt : BodyReceipt native termReading point)
    (child : Child D ((bodyReading native termReading).app point receipt)) :
    Child D (component native termReading point receipt.1 receipt.2) :=
  ⟨.inr ⟨receipt.1, child.val⟩, Edge.inner receipt.1 child.property⟩

def projectChild {point : D} (receipt : BodyReceipt native termReading point)
    (child : Child D (component native termReading point receipt.1 receipt.2)) :
    {original : Child D ((bodyReading native termReading).app point receipt) //
      (.inr ⟨receipt.1, original.val⟩ : (nodes native termReading).obj point) = child.val} := by
  rcases child with ⟨child, edge⟩
  cases child with
  | inl impossible => exact False.elim (by cases edge)
  | inr child =>
    rcases child with ⟨other, node⟩
    have same : other = receipt.1 := by cases edge; rfl
    subst other
    have actual : (termReading.app point receipt.1).1.edge point receipt.2 node := by
      cases edge with
      | inner _ available => exact available
    exact ⟨⟨node, actual⟩, rfl⟩

abbrev ComponentWitness (source : Diagram D) (point : D)
    (first : source.nodes.obj point) (second : (diagram native termReading).nodes.obj point) : Type u :=
  Σ receipt : BodyReceipt native termReading point,
    PLift ((bodyReading native termReading).app point receipt = (⟨source, first⟩ : Value D point)) ×
      PLift (second = .inr receipt)

def componentForth (source : Diagram D) (point : D)
    (first : source.nodes.obj point) (second : (diagram native termReading).nodes.obj point)
    (proof : ComponentWitness native termReading source point first second)
    (future : ContextualGraphRealizers.Future point)
    (child : ContextualGraphRealizers.Child source future.1 (source.nodes.map future.2 first)) :
    Σ matched : ContextualGraphRealizers.Child (diagram native termReading) future.1
        ((diagram native termReading).nodes.map future.2 second),
      ComponentWitness native termReading source future.1 child.val matched.val := by
  rcases proof with ⟨receipt, ⟨same⟩, ⟨atNode⟩⟩
  subst second
  let nextReceipt := (total (bodyNodes native termReading)).map future.2 receipt
  have readings : (bodyReading native termReading).app future.1 nextReceipt =
      (⟨source, source.nodes.map future.2 first⟩ : Value D future.1) :=
    ((bodyReading native termReading).naturality future.2 receipt).symm.trans
      (congrArg (move D future.2) same)
  let actual := cast (congrArg (Child D) readings.symm) child
  exact ⟨embedChild native termReading nextReceipt actual,
    ⟨nextReceipt.1, actual.val⟩,
    ⟨ContextualGraphReceiptFamilies.childValue_cast D readings.symm child⟩, ⟨rfl⟩⟩

def componentBack (source : Diagram D) (point : D)
    (first : source.nodes.obj point) (second : (diagram native termReading).nodes.obj point)
    (proof : ComponentWitness native termReading source point first second)
    (future : ContextualGraphRealizers.Future point)
    (child : ContextualGraphRealizers.Child (diagram native termReading) future.1
      ((diagram native termReading).nodes.map future.2 second)) :
    Σ matched : ContextualGraphRealizers.Child source future.1 (source.nodes.map future.2 first),
      ComponentWitness native termReading source future.1 matched.val child.val := by
  rcases proof with ⟨receipt, ⟨same⟩, ⟨atNode⟩⟩
  subst second
  let nextReceipt := (total (bodyNodes native termReading)).map future.2 receipt
  have readings : (bodyReading native termReading).app future.1 nextReceipt =
      (⟨source, source.nodes.map future.2 first⟩ : Value D future.1) :=
    ((bodyReading native termReading).naturality future.2 receipt).symm.trans
      (congrArg (move D future.2) same)
  let projected := projectChild native termReading nextReceipt child
  let actual := cast (congrArg (Child D) readings) projected.val
  exact ⟨actual, ⟨nextReceipt.1, projected.val.val⟩,
    ⟨(ContextualGraphReceiptFamilies.childValue_cast D readings projected.val).symm⟩,
    ⟨projected.property.symm⟩⟩

def componentEquality (point : D) (receipt : BodyReceipt native termReading point) :
    Equal ((bodyReading native termReading).app point receipt)
      (component native termReading point receipt.1 receipt.2) :=
  ContextualGraphRealizers.corec (termReading.app point receipt.1).1 (diagram native termReading)
    (componentForth native termReading (termReading.app point receipt.1).1)
    (componentBack native termReading (termReading.app point receipt.1).1)
    ⟨receipt, ⟨rfl⟩, ⟨rfl⟩⟩

def childComparison (point : base.Elements) (term : native.obj point) :
    Equal (termReading.app point.1 ⟨point.2, term⟩)
      (childValue D (carrier native termReading point.1 point.2) (encode native termReading point term)) :=
  componentEquality native termReading point.1 ⟨⟨point.2, term⟩, (termReading.app point.1 ⟨point.2, term⟩).2⟩

/-- The attached material readout identifies exactly the pairs already
identified by the declared body reading. No injectivity is imposed. -/
theorem attached_kernel (point : base.Elements) (first second : native.obj point) :
    Nonempty (Equal
      (childValue D (carrier native termReading point.1 point.2) (encode native termReading point first))
      (childValue D (carrier native termReading point.1 point.2) (encode native termReading point second))) ↔
      Nonempty (Equal (termReading.app point.1 ⟨point.2, first⟩) (termReading.app point.1 ⟨point.2, second⟩)) :=
  ⟨fun ⟨same⟩ => ⟨(childComparison native termReading point first).trans
    (same.trans (childComparison native termReading point second).symm)⟩,
    fun ⟨same⟩ => ⟨(childComparison native termReading point first).symm.trans
      (same.trans (childComparison native termReading point second))⟩⟩

def receiptComparison (point : base.Elements) (receipt : (literal native termReading).obj point) :
    Equal (termReading.app point.1 ⟨point.2, decode native termReading point receipt⟩)
      (childValue D (carrier native termReading point.1 point.2) receipt) :=
  (childComparison native termReading point (decode native termReading point receipt)).trans
    (Equal.ofEq (congrArg (childValue D (carrier native termReading point.1 point.2))
      (encode_decode native termReading point receipt)))

def memberIntro (point : base.Elements) (element : Value D point.1) (term : native.obj point)
    (matching : Equal element (termReading.app point.1 ⟨point.2, term⟩)) :
    Member element (carrier native termReading point.1 point.2) :=
  ⟨encode native termReading point term, matching.trans (childComparison native termReading point term)⟩

def memberDecode (point : base.Elements) (element : Value D point.1)
    (membership : Member element (carrier native termReading point.1 point.2)) :
    Σ term : native.obj point, Equal element (termReading.app point.1 ⟨point.2, term⟩) :=
  ⟨decode native termReading point membership.1,
    membership.2.trans (receiptComparison native termReading point membership.1).symm⟩

theorem material_membership_iff (point : base.Elements) (element : Value D point.1) :
    Nonempty (Member element (carrier native termReading point.1 point.2)) ↔
      ∃ term : native.obj point, Nonempty (Equal element (termReading.app point.1 ⟨point.2, term⟩)) :=
  ⟨fun ⟨receipt⟩ => ⟨(memberDecode native termReading point element receipt).1,
    ⟨(memberDecode native termReading point element receipt).2⟩⟩,
    fun ⟨term, ⟨matching⟩⟩ => ⟨memberIntro native termReading point element term matching⟩⟩

/-- Actual complete sections retain the declared material body at every
parameter. The resulting matching acts on all future internal body edges. -/
def sectionComparison (term : (literal native termReading).sections) (point : base.Elements) :
    Equal (termReading.app point.1 ⟨point.2, ((sectionDecoder native termReading) term).val point⟩)
      ((ContextualGraphReceiptFamilies.sectionReading (parent native termReading) term).app point.1 point.2) :=
  receiptComparison native termReading point (term.val point)

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphFamilyBodyComparison
