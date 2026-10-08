import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphEvidenceTransport

/-!
# Coherent restriction of full contextual matching evidence

The direct one-step restriction preserves the exact future replies and
continuations. Explicit endpoint transports establish its identity and
composition laws. Indexed finality then identifies it with the existing
coiterated restriction, giving the same laws for that operation itself.
These are equalities of retained strategies after their endpoint
transports, not an identification of graph matching with native Id.
-/

set_option autoImplicit false
namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphRealizers
open CategoryTheory ContextualGraphDiagrams
universe u
variable {D : Type u} [Category.{u} D] {left right : Diagram D}

namespace Realizer

theorem child_values {graph : Diagram D} {point : D} {first second : graph.nodes.obj point}
    (same : first = second) (a : Child graph point first) (b : Child graph point second)
    (agree : HEq a b) : a.val = b.val := by
  cases same
  exact congrArg Subtype.val (eq_of_heq agree)

theorem child_hext {graph : Diagram D} {point : D} {first second : graph.nodes.obj point}
    (same : first = second) (a : Child graph point first) (b : Child graph point second)
    (agree : a.val = b.val) : HEq a b := by
  cases same
  exact heq_of_eq (Subtype.ext agree)

theorem forth_heq {point : D} {first : left.nodes.obj point} {second : right.nodes.obj point}
    (proof : Realizer left right point first second) {future other : Future point}
    (same : future = other)
    (a : Child left future.1 (left.nodes.map future.2 first))
    (b : Child left other.1 (left.nodes.map other.2 first)) (agree : HEq a b) :
    HEq (proof.forth future a) (proof.forth other b) := by
  cases same
  cases eq_of_heq agree
  rfl

theorem back_heq {point : D} {first : left.nodes.obj point} {second : right.nodes.obj point}
    (proof : Realizer left right point first second) {future other : Future point}
    (same : future = other)
    (a : Child right future.1 (right.nodes.map future.2 second))
    (b : Child right other.1 (right.nodes.map other.2 second)) (agree : HEq a b) :
    HEq (proof.back future a) (proof.back other b) := by
  cases same
  cases eq_of_heq agree
  rfl

theorem forth_castReply {point : D} {first : left.nodes.obj point}
    {before after : right.nodes.obj point} (same : before = after)
    (reply : Σ child : Child right point before, Realizer left right point first child.val) :
    HEq (⟨castChild right same reply.1, reply.2⟩ :
      Σ child : Child right point after, Realizer left right point first child.val) reply := by
  cases same
  rfl

theorem back_castReply {point : D} {second : right.nodes.obj point}
    {before after : left.nodes.obj point} (same : before = after)
    (reply : Σ child : Child left point before, Realizer left right point child.val second) :
    HEq (⟨castChild left same reply.1, reply.2⟩ :
      Σ child : Child left point after, Realizer left right point child.val second) reply := by
  cases same
  rfl

theorem futureForth_identity {point : D} {first : left.nodes.obj point} {second : right.nodes.obj point}
    (proof : Realizer left right point first second) (future : Future point)
    (a : Child left future.1 (left.nodes.map future.2 (left.nodes.map (𝟙 point) first)))
    (b : Child left future.1 (left.nodes.map future.2 first)) (agree : HEq a b) :
    HEq (Realizer.futureForth (𝟙 point) proof future a) (proof.forth future b) := by
  unfold Realizer.futureForth
  apply (forth_castReply (right.nodes.map_comp_apply (𝟙 point) future.2 second) _).trans
  have futures : (⟨future.1, 𝟙 point ≫ future.2⟩ : Future point) = future :=
    Sigma.ext rfl (heq_of_eq (Category.id_comp future.2))
  apply forth_heq proof futures
  apply child_hext (congrArg (fun path => left.nodes.map path first) (Category.id_comp future.2))
  exact child_values (congrArg (fun node => left.nodes.map future.2 node)
    (left.nodes.map_id_apply point first)) a b agree

theorem futureBack_identity {point : D} {first : left.nodes.obj point} {second : right.nodes.obj point}
    (proof : Realizer left right point first second) (future : Future point)
    (a : Child right future.1 (right.nodes.map future.2 (right.nodes.map (𝟙 point) second)))
    (b : Child right future.1 (right.nodes.map future.2 second)) (agree : HEq a b) :
    HEq (Realizer.futureBack (𝟙 point) proof future a) (proof.back future b) := by
  unfold Realizer.futureBack
  apply (back_castReply (left.nodes.map_comp_apply (𝟙 point) future.2 first) _).trans
  have futures : (⟨future.1, 𝟙 point ≫ future.2⟩ : Future point) = future :=
    Sigma.ext rfl (heq_of_eq (Category.id_comp future.2))
  apply back_heq proof futures
  apply child_hext (congrArg (fun path => right.nodes.map path second) (Category.id_comp future.2))
  exact child_values (congrArg (fun node => right.nodes.map future.2 node)
    (right.nodes.map_id_apply point second)) a b agree


abbrev Forward (point : D) (first : left.nodes.obj point) (second : right.nodes.obj point) :=
  (future : Future point) → (child : Child left future.1 (left.nodes.map future.2 first)) →
    Σ matched : Child right future.1 (right.nodes.map future.2 second),
      Realizer left right future.1 child.val matched.val

abbrev Backward (point : D) (first : left.nodes.obj point) (second : right.nodes.obj point) :=
  (future : Future point) → (child : Child right future.1 (right.nodes.map future.2 second)) →
    Σ matched : Child left future.1 (left.nodes.map future.2 first),
      Realizer left right future.1 matched.val child.val

def layerFromReplies {point : D} {first : left.nodes.obj point} {second : right.nodes.obj point}
    (forth : Forward point first second) (back : Backward point first second) :
    Layer left right (fun index => Realizer left right index.1 index.2.1 index.2.2) point first second :=
  ⟨fun future => ⟨fun child => (forth future child).1, fun child => (back future child).1⟩,
    fun ⟨future, position⟩ => match position with
      | .inl child => (forth future child).2
      | .inr child => (back future child).2⟩

theorem layerFromReplies_hext {point : D} {first otherFirst : left.nodes.obj point}
    {second otherSecond : right.nodes.obj point} (firstSame : first = otherFirst) (secondSame : second = otherSecond)
    (forward : Forward point first second) (backward : Backward point first second)
    (otherForward : Forward point otherFirst otherSecond) (otherBackward : Backward point otherFirst otherSecond)
    (forth : ∀ future a b, HEq a b → HEq (forward future a) (otherForward future b))
    (back : ∀ future a b, HEq a b → HEq (backward future a) (otherBackward future b)) :
    HEq (layerFromReplies forward backward) (layerFromReplies otherForward otherBackward) := by
  cases firstSame
  cases secondSame
  have forwards : forward = otherForward := funext fun future => funext fun child =>
    eq_of_heq (forth future child child HEq.rfl)
  have backwards : backward = otherBackward := funext fun future => funext fun child =>
    eq_of_heq (back future child child HEq.rfl)
  cases forwards
  cases backwards
  rfl

theorem layerFromReplies_out {point : D} {first : left.nodes.obj point} {second : right.nodes.obj point}
    (proof : Realizer left right point first second) :
    layerFromReplies proof.forth proof.back = IndexedLimit.Realizer.out proof := by
  refine Sigma.ext ?_ ?_
  · rfl
  apply heq_of_eq
  funext position
  rcases position with ⟨future, position⟩
  cases position <;> rfl

theorem restrictedLayer_replies {origin point : D} {first : left.nodes.obj origin}
    {second : right.nodes.obj origin} (arrival : origin ⟶ point)
    (proof : Realizer left right origin first second) :
    restrictedLayer arrival proof = layerFromReplies (futureForth arrival proof) (futureBack arrival proof) := by
  refine Sigma.ext ?_ ?_
  · rfl
  apply heq_of_eq
  funext position
  rcases position with ⟨future, position⟩
  cases position <;> rfl

theorem restrictedLayer_identity {point : D} {first : left.nodes.obj point} {second : right.nodes.obj point}
    (proof : Realizer left right point first second) :
    HEq (restrictedLayer (𝟙 point) proof) (IndexedLimit.Realizer.out proof) := by
  have layers : HEq (restrictedLayer (𝟙 point) proof) (layerFromReplies proof.forth proof.back) := by
    rw [restrictedLayer_replies]
    apply layerFromReplies_hext (left.nodes.map_id_apply point first) (right.nodes.map_id_apply point second)
    · exact futureForth_identity proof
    · exact futureBack_identity proof
  exact layers.trans (heq_of_eq (layerFromReplies_out proof))

theorem roll_hext {point : D} {first otherFirst : left.nodes.obj point}
    {second otherSecond : right.nodes.obj point} (firstSame : first = otherFirst) (secondSame : second = otherSecond)
    (source : Layer left right (fun index => Realizer left right index.1 index.2.1 index.2.2) point first second)
    (target : Layer left right (fun index => Realizer left right index.1 index.2.1 index.2.2) point otherFirst otherSecond)
    (same : HEq source target) :
    HEq (IndexedLimit.Realizer.roll source) (IndexedLimit.Realizer.roll target) := by
  cases firstSame
  cases secondSame
  exact heq_of_eq (congrArg IndexedLimit.Realizer.roll (eq_of_heq same))

theorem restrictDirect_identity {point : D} {first : left.nodes.obj point} {second : right.nodes.obj point}
    (proof : Realizer left right point first second) : HEq (restrictDirect (𝟙 point) proof) proof := by
  have rolled : HEq (restrictDirect (𝟙 point) proof) (IndexedLimit.Realizer.roll (IndexedLimit.Realizer.out proof)) := by
    apply roll_hext (left.nodes.map_id_apply point first) (right.nodes.map_id_apply point second)
    exact restrictedLayer_identity proof
  exact rolled.trans (heq_of_eq (IndexedLimit.Realizer.roll_out proof))

theorem forth_restrictDirect {origin point : D} {first : left.nodes.obj origin} {second : right.nodes.obj origin}
    (arrival : origin ⟶ point) (proof : Realizer left right origin first second) (future : Future point)
    (child : Child left future.1 (left.nodes.map future.2 (left.nodes.map arrival first))) :
    (restrictDirect arrival proof).forth future child = Realizer.futureForth arrival proof future child := by
  unfold Realizer.forth restrictDirect
  rw [IndexedLimit.Realizer.out_roll]
  rfl

theorem back_restrictDirect {origin point : D} {first : left.nodes.obj origin} {second : right.nodes.obj origin}
    (arrival : origin ⟶ point) (proof : Realizer left right origin first second) (future : Future point)
    (child : Child right future.1 (right.nodes.map future.2 (right.nodes.map arrival second))) :
    (restrictDirect arrival proof).back future child = Realizer.futureBack arrival proof future child := by
  unfold Realizer.back restrictDirect
  rw [IndexedLimit.Realizer.out_roll]
  rfl

theorem futureForth_unwrap {origin point : D} {first : left.nodes.obj origin} {second : right.nodes.obj origin}
    (arrival : origin ⟶ point) (proof : Realizer left right origin first second) (future : Future point)
    (child : Child left future.1 (left.nodes.map future.2 (left.nodes.map arrival first))) :
    HEq (Realizer.futureForth arrival proof future child)
      (proof.forth ⟨future.1, arrival ≫ future.2⟩
        (castChild left (left.nodes.map_comp_apply arrival future.2 first).symm child)) := by
  unfold Realizer.futureForth
  exact forth_castReply (right.nodes.map_comp_apply arrival future.2 second) _

theorem futureBack_unwrap {origin point : D} {first : left.nodes.obj origin} {second : right.nodes.obj origin}
    (arrival : origin ⟶ point) (proof : Realizer left right origin first second) (future : Future point)
    (child : Child right future.1 (right.nodes.map future.2 (right.nodes.map arrival second))) :
    HEq (Realizer.futureBack arrival proof future child)
      (proof.back ⟨future.1, arrival ≫ future.2⟩
        (castChild right (right.nodes.map_comp_apply arrival future.2 second).symm child)) := by
  unfold Realizer.futureBack
  exact back_castReply (left.nodes.map_comp_apply arrival future.2 first) _

theorem futureForth_composition {origin middle point : D} {first : left.nodes.obj origin}
    {second : right.nodes.obj origin} (earlier : origin ⟶ middle) (later : middle ⟶ point)
    (proof : Realizer left right origin first second) (future : Future point)
    (a : Child left future.1 (left.nodes.map future.2 (left.nodes.map (earlier ≫ later) first)))
    (b : Child left future.1 (left.nodes.map future.2 (left.nodes.map later (left.nodes.map earlier first))))
    (agree : HEq a b) :
    HEq (Realizer.futureForth (earlier ≫ later) proof future a)
      (Realizer.futureForth later (restrictDirect earlier proof) future b) := by
  let middleChild := castChild left
    (left.nodes.map_comp_apply later future.2 (left.nodes.map earlier first)).symm b
  let rightChild := castChild left (left.nodes.map_comp_apply earlier (later ≫ future.2) first).symm middleChild
  let leftChild := castChild left (left.nodes.map_comp_apply (earlier ≫ later) future.2 first).symm a
  have laterUnwrap : HEq (Realizer.futureForth later (restrictDirect earlier proof) future b)
      (Realizer.futureForth earlier proof ⟨future.1, later ≫ future.2⟩ middleChild) :=
    (futureForth_unwrap later (restrictDirect earlier proof) future b).trans
      (heq_of_eq (forth_restrictDirect earlier proof ⟨future.1, later ≫ future.2⟩ middleChild))
  have rightUnwrap : HEq (Realizer.futureForth later (restrictDirect earlier proof) future b)
      (proof.forth ⟨future.1, earlier ≫ (later ≫ future.2)⟩ rightChild) :=
    laterUnwrap.trans (futureForth_unwrap earlier proof ⟨future.1, later ≫ future.2⟩ middleChild)
  have futures : (⟨future.1, (earlier ≫ later) ≫ future.2⟩ : Future origin) =
      ⟨future.1, earlier ≫ (later ≫ future.2)⟩ := Sigma.ext rfl (heq_of_eq (Category.assoc earlier later future.2))
  have children : HEq leftChild rightChild := by
    apply child_hext (congrArg (fun path => left.nodes.map path first) (Category.assoc earlier later future.2))
    exact child_values (congrArg (fun node => left.nodes.map future.2 node)
      (left.nodes.map_comp_apply earlier later first)) a b agree
  exact (futureForth_unwrap (earlier ≫ later) proof future a).trans
    ((forth_heq proof futures leftChild rightChild children).trans rightUnwrap.symm)

theorem futureBack_composition {origin middle point : D} {first : left.nodes.obj origin}
    {second : right.nodes.obj origin} (earlier : origin ⟶ middle) (later : middle ⟶ point)
    (proof : Realizer left right origin first second) (future : Future point)
    (a : Child right future.1 (right.nodes.map future.2 (right.nodes.map (earlier ≫ later) second)))
    (b : Child right future.1 (right.nodes.map future.2 (right.nodes.map later (right.nodes.map earlier second))))
    (agree : HEq a b) :
    HEq (Realizer.futureBack (earlier ≫ later) proof future a)
      (Realizer.futureBack later (restrictDirect earlier proof) future b) := by
  let middleChild := castChild right
    (right.nodes.map_comp_apply later future.2 (right.nodes.map earlier second)).symm b
  let rightChild := castChild right (right.nodes.map_comp_apply earlier (later ≫ future.2) second).symm middleChild
  let leftChild := castChild right (right.nodes.map_comp_apply (earlier ≫ later) future.2 second).symm a
  have laterUnwrap : HEq (Realizer.futureBack later (restrictDirect earlier proof) future b)
      (Realizer.futureBack earlier proof ⟨future.1, later ≫ future.2⟩ middleChild) :=
    (futureBack_unwrap later (restrictDirect earlier proof) future b).trans
      (heq_of_eq (back_restrictDirect earlier proof ⟨future.1, later ≫ future.2⟩ middleChild))
  have rightUnwrap : HEq (Realizer.futureBack later (restrictDirect earlier proof) future b)
      (proof.back ⟨future.1, earlier ≫ (later ≫ future.2)⟩ rightChild) :=
    laterUnwrap.trans (futureBack_unwrap earlier proof ⟨future.1, later ≫ future.2⟩ middleChild)
  have futures : (⟨future.1, (earlier ≫ later) ≫ future.2⟩ : Future origin) =
      ⟨future.1, earlier ≫ (later ≫ future.2)⟩ := Sigma.ext rfl (heq_of_eq (Category.assoc earlier later future.2))
  have children : HEq leftChild rightChild := by
    apply child_hext (congrArg (fun path => right.nodes.map path second) (Category.assoc earlier later future.2))
    exact child_values (congrArg (fun node => right.nodes.map future.2 node)
      (right.nodes.map_comp_apply earlier later second)) a b agree
  exact (futureBack_unwrap (earlier ≫ later) proof future a).trans
    ((back_heq proof futures leftChild rightChild children).trans rightUnwrap.symm)

theorem restrictedLayer_composition {origin middle point : D} {first : left.nodes.obj origin}
    {second : right.nodes.obj origin} (earlier : origin ⟶ middle) (later : middle ⟶ point)
    (proof : Realizer left right origin first second) :
    HEq (restrictedLayer (earlier ≫ later) proof) (restrictedLayer later (restrictDirect earlier proof)) := by
  rw [restrictedLayer_replies, restrictedLayer_replies]
  apply layerFromReplies_hext (left.nodes.map_comp_apply earlier later first) (right.nodes.map_comp_apply earlier later second)
  · exact futureForth_composition earlier later proof
  · exact futureBack_composition earlier later proof

theorem restrictDirect_composition {origin middle point : D} {first : left.nodes.obj origin}
    {second : right.nodes.obj origin} (earlier : origin ⟶ middle) (later : middle ⟶ point)
    (proof : Realizer left right origin first second) :
    HEq (restrictDirect (earlier ≫ later) proof) (restrictDirect later (restrictDirect earlier proof)) := by
  apply roll_hext (left.nodes.map_comp_apply earlier later first) (right.nodes.map_comp_apply earlier later second)
  exact restrictedLayer_composition earlier later proof

def restrictionMorphism (index : Index left right) (retained : Realizer.RestrictionWitness index) :
    Realizer left right index.1 index.2.1 index.2.2 := by
  rcases index with ⟨point, first, second⟩
  rcases retained with ⟨⟨origin, earlierFirst, earlierSecond⟩, arrival, proof, ⟨firstSame⟩, ⟨secondSame⟩⟩
  change origin ⟶ point at arrival
  change Realizer left right origin earlierFirst earlierSecond at proof
  change left.nodes.map arrival earlierFirst = first at firstSame
  change right.nodes.map arrival earlierSecond = second at secondSame
  subst first second
  exact restrictDirect arrival proof

theorem restrictionMorphism_heq {origin point : D} {earlierFirst : left.nodes.obj origin}
    {earlierSecond : right.nodes.obj origin} {first : left.nodes.obj point} {second : right.nodes.obj point}
    (arrival : origin ⟶ point) (proof : Realizer left right origin earlierFirst earlierSecond)
    (firstSame : left.nodes.map arrival earlierFirst = first)
    (secondSame : right.nodes.map arrival earlierSecond = second) :
    HEq (restrictionMorphism (⟨point,first,second⟩ : Index left right)
      ⟨⟨origin,earlierFirst,earlierSecond⟩,arrival,proof,⟨firstSame⟩,⟨secondSame⟩⟩)
      (restrictDirect arrival proof) := by
  subst first second
  rfl

theorem restrictionMorphism_identity {point : D} {first : left.nodes.obj point} {second : right.nodes.obj point}
    (proof : Realizer left right point first second) :
    restrictionMorphism (⟨point,first,second⟩ : Index left right)
      ⟨⟨point,first,second⟩,𝟙 point,proof,⟨left.nodes.map_id_apply point first⟩,⟨right.nodes.map_id_apply point second⟩⟩ =
        proof :=
  eq_of_heq ((restrictionMorphism_heq (𝟙 point) proof (left.nodes.map_id_apply point first)
    (right.nodes.map_id_apply point second)).trans (restrictDirect_identity proof))

theorem restrictionMorphism_commutes (index : Index left right) (retained : Realizer.RestrictionWitness index) :
    IndexedLimit.Realizer.out (restrictionMorphism index retained) =
      IndexedLimit.map (Shape left right) (Position left right) (next left right)
        restrictionMorphism (Realizer.restrictionStep index retained) := by
  rcases index with ⟨point, first, second⟩
  rcases retained with ⟨⟨origin, earlierFirst, earlierSecond⟩, arrival, proof, ⟨firstSame⟩, ⟨secondSame⟩⟩
  change origin ⟶ point at arrival
  change Realizer left right origin earlierFirst earlierSecond at proof
  change left.nodes.map arrival earlierFirst = first at firstSame
  change right.nodes.map arrival earlierSecond = second at secondSame
  subst first second
  change IndexedLimit.Realizer.out (restrictDirect arrival proof) = _
  unfold restrictDirect
  rw [IndexedLimit.Realizer.out_roll]
  refine Sigma.ext ?_ ?_
  · rfl
  apply heq_of_eq
  funext position
  rcases position with ⟨future, position⟩
  cases position with
  | inl child => exact (restrictionMorphism_identity (Realizer.futureForth arrival proof future child).2).symm
  | inr child => exact (restrictionMorphism_identity (Realizer.futureBack arrival proof future child).2).symm

/-- The existing coiteration and the direct one-step construction agree
as complete strategies, by the actual indexed coalgebra finality law. -/
theorem restrictDirect_eq_restrict {origin point : D} {first : left.nodes.obj origin}
    {second : right.nodes.obj origin} (arrival : origin ⟶ point)
    (proof : Realizer left right origin first second) : restrictDirect arrival proof = Realizer.restrict arrival proof :=
  IndexedLimit.corec_unique Realizer.restrictionStep restrictionMorphism restrictionMorphism_commutes
    ⟨point,left.nodes.map arrival first,right.nodes.map arrival second⟩
    ⟨⟨origin,first,second⟩,arrival,proof,⟨rfl⟩,⟨rfl⟩⟩

/-- Restriction along an identity changes only the endpoint transports. -/
theorem restrict_identity {point : D} {first : left.nodes.obj point} {second : right.nodes.obj point}
    (proof : Realizer left right point first second) : HEq (Realizer.restrict (𝟙 point) proof) proof := by
  rw [← restrictDirect_eq_restrict]
  exact restrictDirect_identity proof

/-- Composing contexts once or successively yields the same retained
matching strategy after the functorial endpoint comparison. -/
theorem restrict_composition {origin middle point : D} {first : left.nodes.obj origin}
    {second : right.nodes.obj origin} (earlier : origin ⟶ middle) (later : middle ⟶ point)
    (proof : Realizer left right origin first second) :
    HEq (Realizer.restrict (earlier ≫ later) proof) (Realizer.restrict later (Realizer.restrict earlier proof)) := by
  simp only [← restrictDirect_eq_restrict]
  exact restrictDirect_composition earlier later proof


end Realizer
end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphRealizers
