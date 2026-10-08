import Mettapedia.TypeTheory.PresheafNativeStableRefinement
import Mettapedia.TypeTheory.NativeLocalTypeOperations

/-!
# Substitution of actual native refinement terms

Forgetting a refined term is the first projection of its genuine native
sum presentation. Consequently its substitution law follows the proved
native sum projection square. Truth-family substitution supplies the exact
codomain comparison, and membership proofs remain subsingleton. Both
introduction and forgetting commute with the actual local CwF term action.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.PresheafNativeRefinementTermSubstitution

open _root_.CategoryTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension DisplayedPresheafCwf
open ContextualLocalUniverses NativeLocalTypeFormers
open PresheafNativePropositionReadout PresheafNativeStableRefinement

universe u
variable {C : Type u} [Category.{u} C] {P Q : Cᵒᵖ ⥤ Type u}

private theorem sections_map_cast {P : Cᵒᵖ ⥤ Type u}
    {A B : DisplayedFamily P} (same : A = B) (term : A.sections) :
    (Functor.sectionsFunctor P.Elements).map (eqToHom same) term =
      cast (congrArg (fun family : DisplayedFamily P => ↥family.sections) same) term := by
  cases same
  rfl

theorem sectionEquiv_sum (A : NativeType P)
    (predicate : Subfunctor (totalSpace A.decoded))
    (term : (chosen A predicate).decoded.sections) :
    sectionEquiv A predicate term =
      (Functor.sectionsFunctor P.Elements).map (sumTruthIso A.decoded predicate).hom
        (NativeLocalTypeOperations.sumTermEquiv A (guard predicate) term) := by
  change (Functor.sectionsFunctor P.Elements).map (decodeIso A predicate).hom term = _
  rw [decodeIso, Iso.trans_hom, Functor.map_comp]
  change (Functor.sectionsFunctor P.Elements).map (sumTruthIso A.decoded predicate).hom
      ((Functor.sectionsFunctor P.Elements).map (eqToHom (sigmaDecode A (guard predicate))) term) = _
  exact congrArg ((Functor.sectionsFunctor P.Elements).map (sumTruthIso A.decoded predicate).hom)
    (sections_map_cast (sigmaDecode A (guard predicate)) term)

/-- Refinement elimination is the actual native dependent sum projection. -/
theorem forget_is_fst (A : NativeType P)
    (predicate : Subfunctor (totalSpace A.decoded))
    (term : (chosen A predicate).decoded.sections) :
    forget A predicate term = NativeLocalTypeOperations.fst (A := A) (B := guard predicate) term := by
  unfold PresheafNativeStableRefinement.forget
  rw [sectionEquiv_sum]
  apply (Functor.sections_ext_iff).2
  intro point
  rfl

noncomputable def substituteChosen (substitution : Q ⟶ P) (A : NativeType P)
    (predicate : Subfunctor (totalSpace A.decoded))
    (term : (chosen A predicate).decoded.sections) :
    (chosen (A.reindex substitution)
      (predicate.preimage (totalReindexMap substitution A.decoded))).decoded.sections :=
  cast (congrArg (fun type : NativeType Q => ↥type.decoded.sections)
    (chosen_reindex substitution A predicate))
      (substituteTerm (C := presheafCwf C) (type := chosen A predicate) term substitution)

private theorem fst_codomain_heq {P : Cᵒᵖ ⥤ Type u} {A : NativeType P}
    {B otherB : NativeType (totalSpace A.decoded)} (same : B = otherB)
    {first : (sigma A B).decoded.sections} {second : (sigma A otherB).decoded.sections}
    (values : HEq first second) :
    HEq (NativeLocalTypeOperations.fst (A := A) (B := B) first)
      (NativeLocalTypeOperations.fst (A := A) (B := otherB) second) := by
  cases same
  cases values
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem forget_substitution (substitution : Q ⟶ P) (A : NativeType P)
    (predicate : Subfunctor (totalSpace A.decoded))
    (term : (chosen A predicate).decoded.sections) :
    HEq (substituteTerm (C := presheafCwf C) (type := A) (forget A predicate term) substitution)
      (forget (A.reindex substitution)
        (predicate.preimage (totalReindexMap substitution A.decoded))
        (substituteChosen substitution A predicate term)) := by
  let intermediate : (sigma (A.reindex substitution)
      ((guard predicate).reindex (totalReindexMap substitution A.decoded))).decoded.sections :=
    cast (congrArg (fun type : NativeType Q => ↥type.decoded.sections)
      (sigma_reindex substitution A (guard predicate)))
        (substituteTerm (C := presheafCwf C) (type := chosen A predicate) term substitution)
  have fromSource : HEq
      (substituteTerm (C := presheafCwf C) (type := chosen A predicate) term substitution)
      intermediate := (cast_heq _ _).symm
  have projection := (NativeLocalTypeOperations.projections_reindex substitution
    (A := A) (B := guard predicate) term intermediate fromSource).1
  have compared : HEq intermediate (substituteChosen substitution A predicate term) :=
    (cast_heq _ _).trans (cast_heq _ _).symm
  have firstComparison := fst_codomain_heq
    (guard_reindex (totalReindexMap substitution A.decoded) predicate) compared
  rw [forget_is_fst, forget_is_fst]
  exact projection.trans firstComparison

theorem substitutedSatisfaction (substitution : Q ⟶ P) (A : NativeType P)
    (predicate : Subfunctor (totalSpace A.decoded)) (term : A.decoded.sections)
    (satisfies : ∀ world (base : P.obj world),
      (⟨base, term.val ⟨world, base⟩⟩ : (totalSpace A.decoded).obj world) ∈ predicate.obj world) :
    ∀ world (base : Q.obj world),
      (⟨base, (substituteTerm (C := presheafCwf C) (type := A) term substitution).val
        ⟨world, base⟩⟩ : (totalSpace (A.reindex substitution).decoded).obj world) ∈
        (predicate.preimage (totalReindexMap substitution A.decoded)).obj world := by
  intro world base
  have same := eq_of_heq (NativeLocalTypeOperations.substituteTerm_value A term substitution
    ⟨world, base⟩)
  change (⟨substitution.app world base,
    (substituteTerm (C := presheafCwf C) (type := A) term substitution).val ⟨world, base⟩⟩ :
      (totalSpace A.decoded).obj world) ∈ predicate.obj world
  rw [same]
  exact satisfies world (substitution.app world base)

set_option backward.isDefEq.respectTransparency false in
theorem introduction_substitution (substitution : Q ⟶ P) (A : NativeType P)
    (predicate : Subfunctor (totalSpace A.decoded)) (term : A.decoded.sections)
    (satisfies : ∀ world (base : P.obj world),
      (⟨base, term.val ⟨world, base⟩⟩ : (totalSpace A.decoded).obj world) ∈ predicate.obj world) :
    substituteChosen substitution A predicate (intro A predicate term satisfies) =
      intro (A.reindex substitution) (predicate.preimage (totalReindexMap substitution A.decoded))
        (substituteTerm (C := presheafCwf C) (type := A) term substitution)
        (substitutedSatisfaction substitution A predicate term satisfies) := by
  apply forget_injective (A.reindex substitution)
    (predicate.preimage (totalReindexMap substitution A.decoded))
  rw [beta]
  have square := eq_of_heq
    (forget_substitution substitution A predicate (intro A predicate term satisfies))
  rw [beta] at square
  exact square.symm

end Mettapedia.TypeTheory.PresheafNativeRefinementTermSubstitution
