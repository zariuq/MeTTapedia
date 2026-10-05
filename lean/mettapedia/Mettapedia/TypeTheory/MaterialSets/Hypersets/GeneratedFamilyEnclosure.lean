import Mettapedia.TypeTheory.GeneratedUniverseCoherence
import Mettapedia.TypeTheory.MaterialSets.Hypersets.LiftedFamilyModel
import Mettapedia.TypeTheory.MaterialSets.Hypersets.FamilyIdentity
import Mettapedia.TypeTheory.MaterialSets.Hypersets.MaterialWType

/-!
# Generated enclosure of actual material dependent families

Every material family determines a generated semantic universe enclosing its
actual base members and fibre members. Its product and sum codes are compared
with the independently constructed raised material sets, whose inverse maps
retain the original members. Neither presentations nor small section carriers
are supplied to these constructions.

The bounds are explicit: original sets have graph size `u`, their members and
sections have size `u + 1`, the material products and sums have graph size
`u + 1`, and the generated code carrier lives in `Type (u + 2)`. Identity
comparison describes the discrete equality model. The W-code is compared to
an independently constructed material W-set retaining shapes and dependent
positions; its decoder is constructed by accessibility and bounded rows.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.GeneratedFamilyEnclosure

open Mettapedia.TypeTheory.GeneratedFamilyUniverse
open Mettapedia.TypeTheory.FamilyEnclosingUniverse
open LiftedFamilyModel

universe u

abbrev Codes (X : HSet.{u}) (B : Elements X → HSet.{u}) :=
  Code (Elements X) (fun a => Elements (B a))

/-- Construct a generated enclosure of an arbitrary actual material family. -/
def enclosure (X : HSet.{u}) (B : Elements X → HSet.{u}) :
    ClosedTarskiUniverseOver.{u + 2, u + 1}
      (Elements X) (fun a => Elements (B a)) :=
  GeneratedFamilyUniverse.envelope (Elements X) (fun a => Elements (B a))

def productCode (X : HSet.{u}) (B : Elements X → HSet.{u}) : Codes X B :=
  Code.pi Code.base (fun a => Code.fibre a)

def sumCode (X : HSet.{u}) (B : Elements X → HSet.{u}) : Codes X B :=
  Code.sigma Code.base (fun a => Code.fibre a)

def identityCode (X : HSet.{u}) (B : Elements X → HSet.{u})
    (left right : Elements X) : Codes X B := Code.identity Code.base left right

def wCode (X : HSet.{u}) (B : Elements X → HSet.{u}) : Codes X B :=
  Code.w Code.base (fun a => Code.fibre a)

/-- The material product is decoded by proved row evaluation, not by a
chosen section witnessing its membership. -/
def productDecode (X : HSet.{u}) (B : Elements X → HSet.{u}) :
    Elements (productUp X B) ≃ (productCode X B).El := productEquiv X B

/-- Material projections decode the actual dependent sum. -/
def sumDecode (X : HSet.{u}) (B : Elements X → HSet.{u}) :
    Elements (sumUp X B) ≃ (sumCode X B).El :=
  (sumEquiv X B).trans (Equiv.psigmaEquivSigma (fun a => Elements (B a)))

/-- The independently separated material equality fibre has the generated
identity code's decoding, including its actual inverse witness operation. -/
def identityDecode (X : HSet.{u}) (B : Elements X → HSet.{u})
    (left right : Elements X) :
    Elements (FamilyIdentity.identitySet left right) ≃ (identityCode X B left right).El :=
  FamilyIdentity.identityMemberEquiv left right

/-- The actual material W-set has the generated W-code's decoding. The
inverse operations were constructed from its labelled membership graph. -/
def wDecode (X : HSet.{u}) (B : Elements X → HSet.{u}) :
    Elements (MaterialWType.materialW X B) ≃ (wCode X B).El :=
  MaterialWType.materialWEquiv X B

theorem wDecode_constructor {X : HSet.{u}} {B : Elements X → HSet.{u}}
    (a : Elements X) (children : Elements (B a) → Elements (MaterialWType.materialW X B)) :
    wDecode X B (MaterialWType.node a children) =
      WTree.sup a (fun p => wDecode X B (children p)) :=
  MaterialWType.decode_node a children

theorem wDecode_substitution {X Y : HSet.{u}}
    {B : Elements X → HSet.{u}} {C : Elements Y → HSet.{u}}
    (shapes : Elements X → Elements Y)
    (positions : (a : Elements X) → Elements (C (shapes a)) → Elements (B a))
    (root : Elements (MaterialWType.materialW X B)) :
    wDecode Y C (MaterialWType.reindex shapes positions root) =
      MaterialWType.mapTree shapes positions (wDecode X B root) :=
  MaterialWType.decode_reindex shapes positions root

theorem productDecode_application {X : HSet.{u}} {B : Elements X → HSet.{u}}
    (sectionValue : Section X B) (a : Elements X) :
    productDecode X B (LiftedFamilyModel.graphMember sectionValue) a = sectionValue a := by
  exact congrFun (evaluate_graph sectionValue) a

/-- Substitution is a comparison of two actual independently generated
enclosures; original member evaluation commutes on every argument. -/
theorem productDecode_substitution {X Y : HSet.{u}} {B : Elements X → HSet.{u}}
    (σ : Elements Y → Elements X) (graph : Elements (productUp X B)) :
    productDecode Y (B ∘ σ) (pullGraph σ graph) =
      fun a => productDecode X B graph (σ a) := evaluate_pullGraph σ graph

theorem sumDecode_first {X : HSet.{u}} {B : Elements X → HSet.{u}}
    (a : Elements X) (b : Elements (B a)) :
    (sumDecode X B (sumPair a b)).1 = a := sumFirst_pair a b

theorem sumDecode_second_value {X : HSet.{u}} {B : Elements X → HSet.{u}}
    (a : Elements X) (b : Elements (B a)) :
    (sumDecode X B (sumPair a b)).2.1 = b.1 := sumSecond_pair_value a b

/-- A material witness and a generated identity witness agree on formation;
decoding returns the actual equality of endpoints in this discrete model. -/
theorem identityDecode_refl {X : HSet.{u}} {B : Elements X → HSet.{u}}
    (endpoint : Elements X) :
    identityDecode X B endpoint endpoint (FamilyIdentity.identityEncode rfl) =
      (⟨⟨rfl⟩⟩ : (identityCode X B endpoint endpoint).El) := rfl

/-- Propositional material membership makes endpoint equality equivalent to
value equality, without any rule about identity of another calculus. -/
theorem identityCode_inhabited_iff_values {X : HSet.{u}} {B : Elements X → HSet.{u}}
    (left right : Elements X) :
    Nonempty (identityCode X B left right).El ↔ left.1 = right.1 := by
  constructor
  · rintro ⟨witness⟩
    exact congrArg PSigma.fst witness.down.down
  · intro values
    exact ⟨⟨⟨El.ext HSet.propositional values⟩⟩⟩

theorem no_identityCode_between_distinct_values {X : HSet.{u}}
    {B : Elements X → HSet.{u}} {left right : Elements X} (different : left.1 ≠ right.1) :
    ¬ Nonempty (identityCode X B left right).El :=
  fun inhabited => different ((identityCode_inhabited_iff_values left right).mp inhabited)

/-- All these material decodings have actually constructed small carriers at
the raised family level, rather than an independent supplied size witness. -/
theorem material_family_bounds (X : HSet.{u}) (B : Elements X → HSet.{u}) :
    Small.{u + 1} (Elements (productUp X B)) ∧
      Small.{u + 1} (Elements (sumUp X B)) :=
  ⟨product_members_small X B, sum_members_small X B⟩

theorem material_w_bound (X : HSet.{u}) (B : Elements X → HSet.{u}) :
    Small.{u + 1} (Elements (MaterialWType.materialW X B)) :=
  MaterialWType.materialW_members_small X B

#print axioms enclosure
#print axioms productDecode
#print axioms sumDecode
#print axioms identityDecode
#print axioms wDecode
#print axioms wDecode_substitution
#print axioms productDecode_substitution
#print axioms material_family_bounds

end Mettapedia.TypeTheory.MaterialSets.Hypersets.GeneratedFamilyEnclosure
