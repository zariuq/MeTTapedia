import Mettapedia.TypeTheory.PresheafNativePredicateTail

/-!
# Predicate comprehension with arbitrary complete context suffixes

An arbitrary suffix is supplied by its complete context presheaf and its
projection to the original dependent prefix. Selecting the suffix by the
prefix predicate is the categorical pullback of the stable refinement
inclusion. Its universal lift keeps every suffix value. For a native-family
suffix, it is canonically isomorphic to the native reindexed comprehension,
with both complete projections preserved.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.PresheafNativePredicateContextTail

open _root_.CategoryTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension
open ContextualLocalUniverses NativeLocalTypeFormers
open PresheafNativePredicateRefinement PresheafNativeStableRefinement
open PresheafNativePredicateTail

universe u
variable {C : Type u} [Category.{u} C] {P Q T : Cᵒᵖ ⥤ Type u}

def guardSuffix (A : NativeType P) (predicate : Subfunctor (totalSpace A.decoded))
    (projection : T ⟶ totalSpace A.decoded) : Subfunctor T :=
  predicate.preimage projection

def selected (A : NativeType P) (predicate : Subfunctor (totalSpace A.decoded))
    (projection : T ⟶ totalSpace A.decoded) : Cᵒᵖ ⥤ Type u :=
  (guardSuffix A predicate projection).toFunctor

def includeSuffix (A : NativeType P) (predicate : Subfunctor (totalSpace A.decoded))
    (projection : T ⟶ totalSpace A.decoded) : selected A predicate projection ⟶ T :=
  (guardSuffix A predicate projection).ι

instance includeSuffix_mono (A : NativeType P)
    (predicate : Subfunctor (totalSpace A.decoded))
    (projection : T ⟶ totalSpace A.decoded) : Mono (includeSuffix A predicate projection) := by
  exact inferInstanceAs (Mono (predicate.preimage projection).ι)

noncomputable def refinedPrefix (A : NativeType P)
    (predicate : Subfunctor (totalSpace A.decoded))
    (projection : T ⟶ totalSpace A.decoded) :
    selected A predicate projection ⟶ totalSpace (chosen A predicate).decoded :=
  introComplete A predicate (includeSuffix A predicate projection ≫ projection)
    (fun _ value => value.property)

theorem prefix_square (A : NativeType P) (predicate : Subfunctor (totalSpace A.decoded))
    (projection : T ⟶ totalSpace A.decoded) :
    refinedPrefix A predicate projection ≫ forgetComplete A predicate =
      includeSuffix A predicate projection ≫ projection :=
  complete_beta A predicate (includeSuffix A predicate projection ≫ projection)
    (fun _ value => value.property)

noncomputable def contextLift (A : NativeType P)
    (predicate : Subfunctor (totalSpace A.decoded))
    (projection : T ⟶ totalSpace A.decoded)
    (toPrefix : Q ⟶ totalSpace (chosen A predicate).decoded) (whole : Q ⟶ T)
    (compatible : toPrefix ≫ forgetComplete A predicate = whole ≫ projection) :
    Q ⟶ selected A predicate projection where
  app world := TypeCat.ofHom fun value => ⟨whole.app world value, by
    have same := ConcreteCategory.congr_hom (NatTrans.congr_app compatible world) value
    change (forgetComplete A predicate).app world (toPrefix.app world value) =
      projection.app world (whole.app world value) at same
    change projection.app world (whole.app world value) ∈ predicate.obj world
    exact same ▸ forgetComplete_satisfies A predicate world (toPrefix.app world value)⟩
  naturality first second arrow := by
    apply ConcreteCategory.hom_ext
    intro value
    apply Subtype.ext
    exact whole.naturality_apply arrow value

theorem contextLift_suffix (A : NativeType P)
    (predicate : Subfunctor (totalSpace A.decoded))
    (projection : T ⟶ totalSpace A.decoded)
    (toPrefix : Q ⟶ totalSpace (chosen A predicate).decoded) (whole : Q ⟶ T)
    (compatible : toPrefix ≫ forgetComplete A predicate = whole ≫ projection) :
    contextLift A predicate projection toPrefix whole compatible ≫ includeSuffix A predicate projection =
      whole := by
  ext world value
  rfl

theorem contextLift_prefix (A : NativeType P)
    (predicate : Subfunctor (totalSpace A.decoded))
    (projection : T ⟶ totalSpace A.decoded)
    (toPrefix : Q ⟶ totalSpace (chosen A predicate).decoded) (whole : Q ⟶ T)
    (compatible : toPrefix ≫ forgetComplete A predicate = whole ≫ projection) :
    contextLift A predicate projection toPrefix whole compatible ≫
        refinedPrefix A predicate projection = toPrefix := by
  apply (cancel_mono (forgetComplete A predicate)).mp
  rw [Category.assoc, prefix_square, ← Category.assoc, contextLift_suffix]
  exact compatible.symm

/-- The selected suffix is the actual categorical pullback. This includes
suffixes formed from many variable extensions and proposition assumptions. -/
theorem context_isPullback (A : NativeType P)
    (predicate : Subfunctor (totalSpace A.decoded))
    (projection : T ⟶ totalSpace A.decoded) :
    IsPullback (refinedPrefix A predicate projection) (includeSuffix A predicate projection)
      (forgetComplete A predicate) projection := by
  apply IsPullback.mk' (prefix_square A predicate projection)
  · intro probe first second _ sameSuffix
    exact (cancel_mono (includeSuffix A predicate projection)).mp sameSuffix
  · intro probe toPrefix whole compatible
    exact ⟨contextLift A predicate projection toPrefix whole compatible,
      contextLift_prefix A predicate projection toPrefix whole compatible,
      contextLift_suffix A predicate projection toPrefix whole compatible⟩

theorem eliminateConsequent (A : NativeType P)
    (predicate : Subfunctor (totalSpace A.decoded))
    (projection : T ⟶ totalSpace A.decoded) (consequent : Subfunctor T)
    (derivation : guardSuffix A predicate projection ≤ consequent) :
    ⊤ ≤ consequent.preimage (includeSuffix A predicate projection) := by
  intro world receipt _
  exact derivation world receipt.property

noncomputable def familySuffixIso (A : NativeType P)
    (predicate : Subfunctor (totalSpace A.decoded))
    (B : NativeType (totalSpace A.decoded)) :
    totalSpace (suffix A predicate B).decoded ≅
      selected A predicate (totalProjection B.decoded) :=
  (totalReindexMap_isPullback (forgetComplete A predicate) B.decoded).isoIsPullback _ _
    (context_isPullback A predicate (totalProjection B.decoded))

theorem familySuffixIso_prefix (A : NativeType P)
    (predicate : Subfunctor (totalSpace A.decoded))
    (B : NativeType (totalSpace A.decoded)) :
    (familySuffixIso A predicate B).hom ≫
        refinedPrefix A predicate (totalProjection B.decoded) =
      totalProjection (suffix A predicate B).decoded :=
  (totalReindexMap_isPullback (forgetComplete A predicate) B.decoded).isoIsPullback_hom_fst _ _
    (context_isPullback A predicate (totalProjection B.decoded))

theorem familySuffixIso_whole (A : NativeType P)
    (predicate : Subfunctor (totalSpace A.decoded))
    (B : NativeType (totalSpace A.decoded)) :
    (familySuffixIso A predicate B).hom ≫
        includeSuffix A predicate (totalProjection B.decoded) = suffixMap A predicate B :=
  (totalReindexMap_isPullback (forgetComplete A predicate) B.decoded).isoIsPullback_hom_snd _ _
    (context_isPullback A predicate (totalProjection B.decoded))

end Mettapedia.TypeTheory.PresheafNativePredicateContextTail
