import Mettapedia.Logic.HOL.Embedding.ZFSetListContextual
import Mettapedia.Logic.HOL.Embedding.ZFSetIndexedClosure
import Mettapedia.Logic.HOL.Embedding.UniformListPredicateFamily

/-!
# The retained HOL list theory over actual set-coded lists

The three ground carriers are elements of actual sets. The sequence carrier
is the recursively encoded list set; the count carrier is the injective set
code of natural indices. Every original theory assumption is independently
validated, including induction. The original proof tree can consequently be
interpreted without replacing it by a semantic proof of map composition.

Functions in the full-domain Henkin model correspond to actual set graphs.
The map constant uses the existing graph construction and its application.
No internal-universe closure or choice for an empty element carrier is claimed.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.Embedding.ZFSetUniformListModel

open UniformListInduction UniformListMapFusion
open ZFSetDependentProducts ZFSetIndexedClosure
open HenkinDependentFamilyInterpretation HenkinPredicateFamilyInterpretation

universe u

noncomputable def encodeCount (n : Nat) : Elements finiteRankIndex.{u} :=
  ⟨finiteRank n, ZFSet.mem_range_self (f := finiteRank.{u}) n⟩

noncomputable def decodeCount (n : Elements finiteRankIndex.{u}) : Nat :=
  Classical.choose (ZFSet.mem_range.mp n.2)

theorem encode_decodeCount (n : Elements finiteRankIndex.{u}) :
    encodeCount (decodeCount n) = n :=
  Subtype.ext (Classical.choose_spec (ZFSet.mem_range.mp n.2))

@[simp] theorem decode_encodeCount (n : Nat) : decodeCount (encodeCount.{u} n) = n :=
  finiteRank_injective (congrArg Subtype.val (encode_decodeCount (encodeCount n)))

noncomputable def countEquiv : Elements finiteRankIndex.{u} ≃ Nat where
  toFun := decodeCount
  invFun := encodeCount
  left_inv := encode_decodeCount
  right_inv := decode_encodeCount

noncomputable def carrier (a : ZFSet.{u}) : BaseSort → Type (u + 1)
  | .element => Elements a
  | .sequence => Elements (ZFSetList.listCode a)
  | .count => Elements finiteRankIndex

noncomputable def mapValue {a : ZFSet.{u}} (f : Elements a → Elements a)
    (xs : Elements (ZFSetList.listCode a)) : Elements (ZFSetList.listCode a) :=
  graphValue (a := ZFSetList.listCode a) (b := fun _ => ZFSetList.listCode a)
    (ZFSetList.mapGraph f) xs

theorem mapValue_eq {a : ZFSet.{u}} (f : Elements a → Elements a)
    (xs : Elements (ZFSetList.listCode a)) : mapValue f xs = ZFSetList.map f xs :=
  ZFSetList.mapGraph_apply f xs

noncomputable def lengthValue {a : ZFSet.{u}} (xs : Elements (ZFSetList.listCode a)) :
    Elements finiteRankIndex := encodeCount (ZFSetList.decode xs).length

noncomputable def constant (a : ZFSet.{u}) :
    {A : Ty BaseSort} → Symbol A → Ty.denote.{0, u + 1} (carrier a) A
  | _, .nil => ZFSetList.nil a
  | _, .cons => ZFSetList.cons
  | _, .map => mapValue
  | _, .length => lengthValue
  | _, .zero => encodeCount 0
  | _, .succ => fun n => encodeCount (decodeCount n + 1)

noncomputable def model (a : ZFSet.{u}) : HenkinModel.{0, 0, u + 1} BaseSort Symbol :=
  HenkinModel.standard (carrier a) (constant a)

theorem fullDomains (a : ZFSet.{u}) : (model a).FullDomains :=
  HenkinModel.fullDomains_standard (carrier a) (constant a)

theorem respects (a : ZFSet.{u}) : (model a).FunctionsRespectEqv :=
  (model a).functionsRespectEqv_of_fullDomains (fullDomains a)

theorem mapNil_valid (a : ZFSet.{u}) : (model a).models mapNil := by
  intro f _
  change Elements a → Elements a at f
  change mapValue f (ZFSetList.nil a) = ZFSetList.nil a
  rw [mapValue_eq, ZFSetList.map_nil]

theorem mapCons_valid (a : ZFSet.{u}) : (model a).models mapCons := by
  intro f _ x _ xs _
  change Elements a → Elements a at f
  change Elements a at x
  change Elements (ZFSetList.listCode a) at xs
  change mapValue f (ZFSetList.cons x xs) = ZFSetList.cons (f x) (mapValue f xs)
  rw [mapValue_eq, mapValue_eq, ZFSetList.map_cons]

theorem lengthNil_valid (a : ZFSet.{u}) : (model a).models lengthNil := by
  change lengthValue (ZFSetList.nil a) = encodeCount 0
  simp only [lengthValue, ZFSetList.decode_nil, List.length_nil]

theorem lengthCons_valid (a : ZFSet.{u}) : (model a).models lengthCons := by
  intro x _ xs _
  change Elements a at x
  change Elements (ZFSetList.listCode a) at xs
  change lengthValue (ZFSetList.cons x xs) = encodeCount (decodeCount (lengthValue xs) + 1)
  simp only [lengthValue, ZFSetList.decode_cons, List.length_cons, decode_encodeCount]

theorem induction_valid (a : ZFSet.{u}) : (model a).models inductionPrinciple := by
  intro p _ base step xs _
  exact ZFSetList.eliminate (fun ys => (p ys).down) base
    (fun x ys ih => step x trivial ys trivial ih) xs

theorem equations_valid (a : ZFSet.{u}) :
    ∀ φ ∈ equations (Γ := []), (model a).models φ := by
  intro φ member
  simp only [equations, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact mapNil_valid a
  · exact mapCons_valid a
  · exact lengthNil_valid a
  · exact lengthCons_valid a

theorem theory_valid (a : ZFSet.{u}) :
    ∀ φ ∈ theory (Γ := []), (model a).models φ := by
  intro φ member
  rcases List.mem_cons.mp member with rfl | member
  · exact induction_valid a
  · exact equations_valid a φ member

noncomputable def emptyContext (a : ZFSet.{u}) : AdmissibleContext (model a) [] :=
  ⟨(fun boundVar => nomatch boundVar), by intro A boundVar; exact nomatch boundVar⟩

noncomputable def satisfied (a : ZFSet.{u}) : SatisfiedContext (model a) (theory (Γ := [])) :=
  ⟨emptyContext a, by
    intro φ member
    refine Eq.mp ?_ (theory_valid a φ member)
    unfold HenkinModel.models PreModel.models
    apply congrArg ULift.down
    apply congrArg (PreModel.denote (model a).toPreModel φ)
    funext A boundVar
    nomatch boundVar⟩

/-- The exact closed source tree is supplied to the existing proof interpreter. -/
noncomputable def retainedFusion (a : ZFSet.{u}) :
    truthFamily (model a) (mapFusion (Γ := [])) (emptyContext a) :=
  proofSection (model a) (respects a) mapFusionProof (satisfied a)

theorem retainedFusion_equation {a : ZFSet.{u}} (f g : Elements a → Elements a)
    (xs : Elements (ZFSetList.listCode a)) :
    mapValue f (mapValue g xs) = mapValue (fun x => f (g x)) xs :=
  (retainedFusion a).down.down f trivial g trivial xs trivial

noncomputable def functionValue {a : ZFSet.{u}} (f : Elements a → Elements a) :
    AdmissibleValue (model a) mapping := ⟨f, by trivial⟩

noncomputable def listValue {a : ZFSet.{u}} (xs : Elements (ZFSetList.listCode a)) :
    AdmissibleValue (model a) sequence := ⟨xs, by trivial⟩

noncomputable def functionContext {a : ZFSet.{u}}
    (f g : Elements a → Elements a) :
    SatisfiedContext (model a) (theory (Γ := [mapping, mapping])) :=
  UniformListPredicateFamily.extendTheoryContext (model a)
    (UniformListPredicateFamily.extendTheoryContext (model a) (satisfied a) (functionValue f))
    (functionValue g)

/-- This section is obtained from the retained source induction proof. -/
noncomputable def fusionWitness {a : ZFSet.{u}} (f g : Elements a → Elements a)
    (xs : Elements (ZFSetList.listCode a)) :
    predicateFamily (model a)
      (fuses (.var (.vs (.vs .vz))) (.var (.vs .vz)) (.var .vz))
      (functionContext f g).1 (listValue xs) :=
  UniformListPredicateFamily.fusionSection (model a) (respects a)
    (.var (.vs .vz)) (.var .vz) (functionContext f g) (listValue xs)

theorem fusionWitness_equation {a : ZFSet.{u}} (f g : Elements a → Elements a)
    (xs : Elements (ZFSetList.listCode a)) :
    mapValue f (mapValue g xs) = mapValue (fun x => f (g x)) xs :=
  (fusionWitness f g xs).down.down

#print axioms countEquiv
#print axioms mapValue_eq
#print axioms induction_valid
#print axioms theory_valid
#print axioms retainedFusion
#print axioms retainedFusion_equation
#print axioms fusionWitness
#print axioms fusionWitness_equation

end Mettapedia.Logic.HOL.Embedding.ZFSetUniformListModel
