import Mettapedia.TypeTheory.PresheafNativePredicateRefinement
import Mettapedia.TypeTheory.DisplayedPresheafEvidenceUniversal

/-!
# Predicate refinement through proof-retaining dependent sums

Selecting the satisfying source inhabitants commutes with dependent-sum
transport when the predicate on the receipt is read through the actual
source-total comparison. The comparison retains both the supplied inhabitant
and its origin. A predicate-respecting map into a target family extends to
every refined receipt by the computational sum adjunction.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DisplayedPresheafRefinementTransport

open _root_.CategoryTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafSlice
open DisplayedPresheafSliceSubstitution
open DisplayedPresheafEvidenceTransport DisplayedPresheafEvidenceUniversal

namespace Refinement
export PresheafNativePredicateRefinement (displayed forgetFamily)
end Refinement

universe u
variable {C : Type u} [Category.{u} C]
variable {P Q R : Cᵒᵖ ⥤ Type u}

/-- A receipt satisfies the source predicate exactly when its retained
source program and supplied inhabitant satisfy it. -/
def receiptPredicate (f : P ⟶ Q) (A : DisplayedFamily P)
    (predicate : Subfunctor (totalSpace A)) :
    Subfunctor (totalSpace (transport f A)) :=
  predicate.preimage (DisplayedPresheafEvidenceTransport.totalIso f A).hom

/-- The fibre comparison keeps the original source index and inhabitant;
it only reassociates the two membership proofs. -/
def fibreEquiv (f : P ⟶ Q) (A : DisplayedFamily P)
    (predicate : Subfunctor (totalSpace A)) (point : Q.Elements) :
    (transport f (Refinement.displayed A predicate)).obj point ≃
      (Refinement.displayed (transport f A) (receiptPredicate f A predicate)).obj point where
  toFun receipt := ⟨⟨⟨receipt.val.1, receipt.val.2.val⟩, receipt.property⟩,
    receipt.val.2.property⟩
  invFun selected := ⟨⟨selected.val.val.1,
    ⟨selected.val.val.2, selected.property⟩⟩, selected.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Refinement before transport and refinement of the retained receipt
are naturally isomorphic over the actual target program context. -/
def transportIso (f : P ⟶ Q) (A : DisplayedFamily P)
    (predicate : Subfunctor (totalSpace A)) :
    transport f (Refinement.displayed A predicate) ≅
      Refinement.displayed (transport f A) (receiptPredicate f A predicate) :=
  NatIso.ofComponents (fun point => (fibreEquiv f A predicate point).toIso) (by
    intro first second arrow
    ext receipt
    apply Subtype.ext
    apply Subtype.ext
    rfl)

/-- Forgetting membership commutes with the sum comparison, including
every source index and every inhabitant in the unrefined receipt. -/
theorem transportIso_forget (f : P ⟶ Q) (A : DisplayedFamily P)
    (predicate : Subfunctor (totalSpace A)) :
    (transportIso f A predicate).hom ≫
      Refinement.forgetFamily (transport f A) (receiptPredicate f A predicate) =
        (transportFunctor f).map (Refinement.forgetFamily A predicate) := by
  ext point receipt
  apply Subtype.ext
  rfl

theorem transportIso_unit (f : P ⟶ Q) (A : DisplayedFamily P)
    (predicate : Subfunctor (totalSpace A)) (point : P.Elements)
    (value : (Refinement.displayed A predicate).obj point) :
    ((transportIso f A predicate).hom.app (f.mapElements.obj point)
      ((unit f (Refinement.displayed A predicate)).app point value)).val =
        (unit f A).app point value.val := rfl

/-- Reading the source predicate after two stages agrees with reading
it after their composite, along the actual flattening of sum receipts. -/
theorem receiptPredicate_composition (f : P ⟶ Q) (g : Q ⟶ R)
    (A : DisplayedFamily P) (predicate : Subfunctor (totalSpace A)) :
    (receiptPredicate (f ≫ g) A predicate).preimage
        (totalHom (compositionIso f g A).hom) =
      receiptPredicate g (transport f A) (receiptPredicate f A predicate) := by
  ext world entry
  rfl

/-- Removing an identity-stage receipt also removes its predicate
comparison without changing the selected source inhabitants. -/
theorem receiptPredicate_identity (A : DisplayedFamily P)
    (predicate : Subfunctor (totalSpace A)) :
    receiptPredicate (𝟙 P) A predicate =
      predicate.preimage (totalHom (DisplayedPresheafEvidenceCoherence.identityIso A).hom) := by
  ext world entry
  rcases entry with ⟨program, ⟨⟨origin, value⟩, same⟩⟩
  change origin = program at same
  subst origin
  rfl

/-- A local predicate-respecting source map supplies a coherent map
between the corresponding refinements. No inhabitant is selected from
the erased support of either predicate. -/
def liftSource (f : P ⟶ Q) {A : DisplayedFamily P} {B : DisplayedFamily Q}
    (body : A ⟶ reindexDisplayed f B)
    (sourcePredicate : Subfunctor (totalSpace A))
    (targetPredicate : Subfunctor (totalSpace B))
    (respects : sourcePredicate ≤ targetPredicate.preimage (evidenceTotalMap f body)) :
    Refinement.displayed A sourcePredicate ⟶
      reindexDisplayed f (Refinement.displayed B targetPredicate) where
  app point := TypeCat.ofHom fun selected =>
    ⟨body.app point selected.val, respects point.1 selected.property⟩
  naturality first second arrow := by
    ext selected
    apply Subtype.ext
    exact body.naturality_apply arrow selected.val

theorem liftSource_forget (f : P ⟶ Q)
    {A : DisplayedFamily P} {B : DisplayedFamily Q}
    (body : A ⟶ reindexDisplayed f B)
    (sourcePredicate : Subfunctor (totalSpace A))
    (targetPredicate : Subfunctor (totalSpace B))
    (respects : sourcePredicate ≤ targetPredicate.preimage (evidenceTotalMap f body)) :
    liftSource f body sourcePredicate targetPredicate respects ≫
      (reindexFunctor f).map (Refinement.forgetFamily B targetPredicate) =
        Refinement.forgetFamily A sourcePredicate ≫ body := by
  ext point selected
  rfl

/-- Universal elimination of refined receipts uses the supplied
predicate-respecting implementation and preserves its exact result. -/
def descendRefined (f : P ⟶ Q) {A : DisplayedFamily P} {B : DisplayedFamily Q}
    (body : A ⟶ reindexDisplayed f B)
    (sourcePredicate : Subfunctor (totalSpace A))
    (targetPredicate : Subfunctor (totalSpace B))
    (respects : sourcePredicate ≤ targetPredicate.preimage (evidenceTotalMap f body)) :
    transport f (Refinement.displayed A sourcePredicate) ⟶
      Refinement.displayed B targetPredicate :=
  descend f (liftSource f body sourcePredicate targetPredicate respects)

theorem descendRefined_unit (f : P ⟶ Q)
    {A : DisplayedFamily P} {B : DisplayedFamily Q}
    (body : A ⟶ reindexDisplayed f B)
    (sourcePredicate : Subfunctor (totalSpace A))
    (targetPredicate : Subfunctor (totalSpace B))
    (respects : sourcePredicate ≤ targetPredicate.preimage (evidenceTotalMap f body))
    (point : P.Elements) (selected : (Refinement.displayed A sourcePredicate).obj point) :
    ((descendRefined f body sourcePredicate targetPredicate respects).app
      (f.mapElements.obj point)
      ((unit f (Refinement.displayed A sourcePredicate)).app point selected)).val =
        body.app point selected.val := by
  rw [descendRefined, descend_unit]
  rfl

theorem descendRefined_forget (f : P ⟶ Q)
    {A : DisplayedFamily P} {B : DisplayedFamily Q}
    (body : A ⟶ reindexDisplayed f B)
    (sourcePredicate : Subfunctor (totalSpace A))
    (targetPredicate : Subfunctor (totalSpace B))
    (respects : sourcePredicate ≤ targetPredicate.preimage (evidenceTotalMap f body)) :
    descendRefined f body sourcePredicate targetPredicate respects ≫
      Refinement.forgetFamily B targetPredicate =
        (transportFunctor f).map (Refinement.forgetFamily A sourcePredicate) ≫
          descend f body := by
  rw [descendRefined, ← descend_naturality]
  exact (congrArg (descend f)
    (liftSource_forget f body sourcePredicate targetPredicate respects)).trans
      (descend_naturality_left f (Refinement.forgetFamily A sourcePredicate) body)

/-- The extension is unique among coherent maps having the supplied
source computation, including the refinement membership. -/
theorem descendRefined_unique (f : P ⟶ Q)
    {A : DisplayedFamily P} {B : DisplayedFamily Q}
    (body : A ⟶ reindexDisplayed f B)
    (sourcePredicate : Subfunctor (totalSpace A))
    (targetPredicate : Subfunctor (totalSpace B))
    (respects : sourcePredicate ≤ targetPredicate.preimage (evidenceTotalMap f body))
    (candidate : transport f (Refinement.displayed A sourcePredicate) ⟶
      Refinement.displayed B targetPredicate)
    (computes : restrict f candidate =
      liftSource f body sourcePredicate targetPredicate respects) :
    candidate = descendRefined f body sourcePredicate targetPredicate respects :=
  descend_unique f _ candidate computes

end Mettapedia.TypeTheory.DisplayedPresheafRefinementTransport
