import Mettapedia.TypeTheory.PresheafNativePredicateIntroduction
import Mettapedia.TypeTheory.PresheafNativePropositionReadout

/-!
# Stable native predicate comprehension

The chosen native refinement is the genuine dependent sum of the original
native type with the fixed truth-proof family named by its predicate. Its
decoder is an isomorphism to the direct satisfying-inhabitant family.
Predicate substitution is derived from characteristic-map substitution and
the native sum parameter construction. Original inhabitants are retained;
only proposition-valued truth proofs are uniquely determined.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.PresheafNativeStableRefinement

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open DisplayedPresheafTransport DisplayedPresheafComprehension DisplayedPresheafCwf
open DisplayedPresheafSigma ContextualLocalUniverses NativeLocalTypeFormers
open DisplayedPresheafSlice
open NativeLocalTheoryTransformation NativeLocalDisplayComparisons
open PresheafNativePredicateRefinement PresheafNativePropositionReadout

universe u
variable {C : Type u} [Category.{u} C] {P Q : Cᵒᵖ ⥤ Type u}

local instance decodedCategory (P : Cᵒᵖ ⥤ Type u) :
    Category.{u} ((presheafCwf.{u, u, u} C).Ty P) :=
  inferInstanceAs (Category.{u} (DisplayedFamily.{u, u, u, u} P))

noncomputable def chosen (A : NativeType P)
    (predicate : Subfunctor (totalSpace A.decoded)) : NativeType P :=
  sigma A (guard predicate)

/-- The sum proof is precisely truth of the original complete receipt.
The comparison retains its first dependent component in both directions. -/
noncomputable def sumTruthIso (A : DisplayedFamily P)
    (predicate : Subfunctor (totalSpace A)) :
    sigmaDisplayed A (guard predicate).decoded ≅ displayed A predicate where
  hom :=
    { app := fun point => TypeCat.ofHom fun value =>
        ⟨value.1, (characteristic_member_iff predicate point.1
          ⟨point.2, value.1⟩).2 value.2.down.down⟩
      naturality := by
        intro first second arrow
        apply ConcreteCategory.hom_ext
        intro value
        apply Subtype.ext
        rfl }
  inv :=
    { app := fun point => TypeCat.ofHom fun value =>
        ⟨value.val, ⟨⟨(characteristic_member_iff predicate point.1
          ⟨point.2, value.val⟩).1 value.property⟩⟩⟩
      naturality := by
        intro first second arrow
        apply ConcreteCategory.hom_ext
        intro value
        apply Sigma.ext rfl
        rfl }
  hom_inv_id := by
    ext point value
    apply Sigma.ext rfl
    rfl
  inv_hom_id := by ext point value; rfl

noncomputable def decodeIso (A : NativeType P)
    (predicate : Subfunctor (totalSpace A.decoded)) :
    (show DisplayedFamily P from (chosen A predicate).decoded) ≅
      displayed A.decoded predicate :=
  eqToIso (sigmaDecode A (guard predicate)) ≪≫ sumTruthIso A.decoded predicate

noncomputable def sectionEquiv (A : NativeType P)
    (predicate : Subfunctor (totalSpace A.decoded)) :
    (chosen A predicate).decoded.sections ≃ (displayed A.decoded predicate).sections :=
  ((Functor.sectionsFunctor P.Elements).mapIso (decodeIso A predicate)).toEquiv

noncomputable def completeDecodeIso (A : NativeType P)
    (predicate : Subfunctor (totalSpace A.decoded)) :
    totalSpace (chosen A predicate).decoded ≅ totalSpace (displayed A.decoded predicate) :=
  ((totalFunctor P) ⋙ Over.forget P).mapIso (decodeIso A predicate)

noncomputable def completeIso (A : NativeType P)
    (predicate : Subfunctor (totalSpace A.decoded)) :
    totalSpace (chosen A predicate).decoded ≅ predicate.toFunctor :=
  completeDecodeIso A predicate ≪≫ totalIso A.decoded predicate

noncomputable def forgetComplete (A : NativeType P)
    (predicate : Subfunctor (totalSpace A.decoded)) :
    totalSpace (chosen A predicate).decoded ⟶ totalSpace A.decoded :=
  (completeIso A predicate).hom ≫ predicate.ι

instance forgetComplete_mono (A : NativeType P)
    (predicate : Subfunctor (totalSpace A.decoded)) : Mono (forgetComplete A predicate) := by
  unfold forgetComplete
  infer_instance

/-- The stable chosen presentation has the same actual comprehension
inclusion as the independently constructed direct subtype. -/
theorem forgetComplete_decoder (A : NativeType P)
    (predicate : Subfunctor (totalSpace A.decoded)) :
    forgetComplete A predicate =
      (completeDecodeIso A predicate).hom ≫
        PresheafNativePredicateRefinement.forgetTotal A.decoded predicate := by
  change ((completeDecodeIso A predicate).hom ≫
    (totalIso A.decoded predicate).hom) ≫ predicate.ι = _
  exact (Category.assoc _ _ _).trans
    (congrArg (fun operation => (completeDecodeIso A predicate).hom ≫ operation)
      (forget_is_comprehension A.decoded predicate))

noncomputable def forgetNativeDisplay (A : NativeType P)
    (predicate : Subfunctor (totalSpace A.decoded)) :
    (⟨chosen A predicate⟩ : TypeOver (nativeLocalModel C).toCwf P) ⟶ ⟨A⟩ :=
  displayHom _ _ ((decodeIso A predicate).hom ≫
    PresheafNativePredicateRefinement.forgetFamily A.decoded predicate)

theorem forgetNativeDisplay_substitution (A : NativeType P)
    (predicate : Subfunctor (totalSpace A.decoded)) :
    (forgetNativeDisplay A predicate).substitution = forgetComplete A predicate := by
  change totalHom ((decodeIso A predicate).hom ≫
    PresheafNativePredicateRefinement.forgetFamily A.decoded predicate) = _
  ext world value
  rfl

theorem forgetComplete_satisfies (A : NativeType P)
    (predicate : Subfunctor (totalSpace A.decoded)) (world : Cᵒᵖ)
    (value : (totalSpace (chosen A predicate).decoded).obj world) :
    (forgetComplete A predicate).app world value ∈ predicate.obj world :=
  ((completeIso A predicate).hom.app world value).property

noncomputable def introComplete (A : NativeType P)
    (predicate : Subfunctor (totalSpace A.decoded)) (term : Q ⟶ totalSpace A.decoded)
    (satisfies : ∀ world value, term.app world value ∈ predicate.obj world) :
    Q ⟶ totalSpace (chosen A predicate).decoded :=
  guardedMap A.decoded predicate term satisfies ≫ (completeIso A predicate).inv

theorem complete_beta (A : NativeType P)
    (predicate : Subfunctor (totalSpace A.decoded)) (term : Q ⟶ totalSpace A.decoded)
    (satisfies : ∀ world value, term.app world value ∈ predicate.obj world) :
    introComplete A predicate term satisfies ≫ forgetComplete A predicate = term := by
  unfold introComplete forgetComplete
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  ext world value
  rfl

theorem complete_eta (A : NativeType P)
    (predicate : Subfunctor (totalSpace A.decoded))
    (term : Q ⟶ totalSpace (chosen A predicate).decoded) :
    introComplete A predicate (term ≫ forgetComplete A predicate)
      (fun world value => forgetComplete_satisfies A predicate world (term.app world value)) =
        term := by
  have guarded : guardedMap A.decoded predicate (term ≫ forgetComplete A predicate)
      (fun world value => forgetComplete_satisfies A predicate world (term.app world value)) =
      term ≫ (completeIso A predicate).hom := by
    ext world value
    apply Subtype.ext
    rfl
  unfold introComplete
  rw [guarded, Category.assoc, Iso.hom_inv_id, Category.comp_id]

noncomputable def intro (A : NativeType P)
    (predicate : Subfunctor (totalSpace A.decoded)) (term : A.decoded.sections)
    (satisfies : ∀ world (base : P.obj world),
      (⟨base, term.val ⟨world, base⟩⟩ : (totalSpace A.decoded).obj world) ∈
        predicate.obj world) : (chosen A predicate).decoded.sections :=
  (sectionEquiv A predicate).symm (introSection A.decoded predicate term satisfies)

noncomputable def forget (A : NativeType P)
    (predicate : Subfunctor (totalSpace A.decoded))
    (term : (chosen A predicate).decoded.sections) : A.decoded.sections :=
  forgetSection A.decoded predicate (sectionEquiv A predicate term)

theorem forgetComplete_section (A : NativeType P)
    (predicate : Subfunctor (totalSpace A.decoded))
    (term : (chosen A predicate).decoded.sections) :
    sectionLift (chosen A predicate).decoded term ≫ forgetComplete A predicate =
      sectionLift A.decoded (forget A predicate term) := by
  ext world value
  rfl

theorem beta (A : NativeType P) (predicate : Subfunctor (totalSpace A.decoded))
    (term : A.decoded.sections)
    (satisfies : ∀ world (base : P.obj world),
      (⟨base, term.val ⟨world, base⟩⟩ : (totalSpace A.decoded).obj world) ∈
        predicate.obj world) :
    forget A predicate (intro A predicate term satisfies) = term := by
  unfold forget intro
  rw [Equiv.apply_symm_apply]
  exact introSection_beta A.decoded predicate term satisfies

theorem introduced_section_forgets (A : NativeType P)
    (predicate : Subfunctor (totalSpace A.decoded)) (term : A.decoded.sections)
    (satisfies : ∀ world (base : P.obj world),
      (⟨base, term.val ⟨world, base⟩⟩ : (totalSpace A.decoded).obj world) ∈ predicate.obj world) :
    sectionLift (chosen A predicate).decoded (intro A predicate term satisfies) ≫
      forgetComplete A predicate = sectionLift A.decoded term := by
  rw [forgetComplete_section, beta]

theorem forget_satisfies (A : NativeType P)
    (predicate : Subfunctor (totalSpace A.decoded))
    (term : (chosen A predicate).decoded.sections) (world : Cᵒᵖ) (base : P.obj world) :
    (⟨base, (forget A predicate term).val ⟨world, base⟩⟩ :
      (totalSpace A.decoded).obj world) ∈ predicate.obj world :=
  ((sectionEquiv A predicate term).val ⟨world, base⟩).property

theorem eta (A : NativeType P) (predicate : Subfunctor (totalSpace A.decoded))
    (term : (chosen A predicate).decoded.sections) :
    intro A predicate (forget A predicate term) (forget_satisfies A predicate term) = term := by
  apply (sectionEquiv A predicate).injective
  unfold intro forget
  rw [Equiv.apply_symm_apply]
  exact introSection_eta A.decoded predicate (sectionEquiv A predicate term)

theorem forget_injective (A : NativeType P)
    (predicate : Subfunctor (totalSpace A.decoded)) :
    Function.Injective (forget A predicate) := by
  intro first second same
  apply (sectionEquiv A predicate).injective
  apply (Functor.sections_ext_iff).2
  intro point
  apply Subtype.ext
  exact congrArg (fun term => term.val point) same

set_option backward.isDefEq.respectTransparency false in
/-- This is equality of the chosen native presentations, with their fixed
parameter families, not merely an equality of inhabited support. -/
theorem chosen_reindex (substitution : Q ⟶ P) (A : NativeType P)
    (predicate : Subfunctor (totalSpace A.decoded)) :
    (chosen A predicate).reindex substitution =
      chosen (A.reindex substitution)
        (predicate.preimage (totalReindexMap substitution A.decoded)) := by
  unfold chosen
  rw [sigma_reindex]
  exact congrArg (sigma (A.reindex substitution))
    (guard_reindex (totalReindexMap substitution A.decoded) predicate)

end Mettapedia.TypeTheory.PresheafNativeStableRefinement
