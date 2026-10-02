import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedProgramPartialRepresentatives
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedProgramMeaningRepresentatives
import Mettapedia.OSLF.Syntax.CategoricalBindingGenericApplication
import Mettapedia.OSLF.Syntax.BindingPrefixContextCast

/-!
# Ordered argument projections in the actual program interpretation

Each component of the semantic argument tuple is the curried meaning of its
own binder-local body. Generalized family points are determined by these
ordered components, and the genuine family comparison reads each component
through the corresponding contextual assignment arrow.

The raw partial-substitution comparison identifies the established
renaming-based prefix reading with explicit context transport.
-/

set_option autoImplicit false
noncomputable section
namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedPresheaf
open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open CategoricalBindingModel SecondOrderContext
open IntrinsicScopedLocalCongruence (getArg)
open IntrinsicScopedLocalPolynomial IntrinsicScopedLocalActedClassifier
universe u v w
variable {S : Signature} {K : List (MetaArity S)}

/-- Partial substitution in the raw clone reads the filled body in its
retained binder context through the same established prefix operation. -/
theorem partialSubstitute_terms_unScope {T : Signature} {Γ : Ctx T}
    (bs : Ctx T) (environment : Sub T Γ []) {s : T.Srt}
    (body : Term T (bs ++ Γ) s) :
    partialSubstitute (BindingCloneAlgebra.terms T) bs environment body =
      unScope bs (bind (liftSub environment bs) body) := by
  have transported := bind_castTermCtx (S := T) rfl (List.append_nil bs)
    (liftSub environment bs) body
  unfold partialSubstitute liftClosedEnvironment
  change bind (fun r var => castTermCtx (List.append_nil bs)
    ((BindingSubstitutionAlgebra.terms T).liftEnvironment environment bs r var)) body = _
  rw [BindingSubstitutionAlgebra.terms_liftEnvironment_eq_liftSub]
  exact transported.trans
    (unScope_contextCast bs (bind (liftSub environment bs) body)).symm

section GenericArgumentProjection
variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]
variable {F : Object S ⥤ D} (data : PreservingData F) (X : Object S)

/-- Each ordered argument projection is exactly the curried meaning of
that body under its own local binders. -/
theorem tupleArgs_meaning_proj :
    ∀ {arity : List (MetaArity S)} {Γ : Ctx S}
      (args : Args (withMetas S X.arities) arity Γ) (Z : D)
      (assignment : Z ⟶ data.toModel.family X.arities)
      (environment : data.toModel.Env Z Γ) (i : Fin arity.length),
      data.toModel.tupleArgs
          (FreeBindingTerms.FamilyArgs.map (fun term => data.meaning term)
            (FreeBindingTerms.syntaxToFamily args)) Z assignment environment ≫
          data.toModel.familyProj arity i =
        data.toModel.curry (((data.meaning (getArg args i)).value
          (data.toModel.ctx (arity.get i).1 ⊗ Z) (snd _ _ ≫ assignment)
          (data.toModel.extendEnv (arity.get i).1 environment)))
  | _ :: _, _, .cons _ _, _, _, _, ⟨0, _⟩ => lift_fst _ _
  | _ :: rest, _, .cons _ tail, _, _, _, ⟨n + 1, bound⟩ => by
      change lift _ _ ≫ snd _ _ ≫ data.toModel.familyProj rest
        ⟨n, Nat.lt_of_succ_lt_succ bound⟩ = _
      rw [lift_snd_assoc]
      exact tupleArgs_meaning_proj tail _ _ _ ⟨n, Nat.lt_of_succ_lt_succ bound⟩
end GenericArgumentProjection

section GenericFamilyPoints
variable {C : Type u} [Category.{v} C]
variable (M : Model S (Cᵒᵖ ⥤ Type w))

/-- A generalized family point is determined by all its ordered binder
components, including at stages containing event variables. -/
theorem familyPoint_ext (a : Cᵒᵖ) :
    ∀ (arity : List (MetaArity S))
      {first second : (M.family arity).obj a},
      (∀ i : Fin arity.length, (M.familyProj arity i).app a first =
        (M.familyProj arity i).app a second) → first = second
  | [], first, second, _ => by
      change PUnit at first second
      exact Subsingleton.elim first second
  | _ :: rest, first, second, components => by
      apply Prod.ext
      · exact components ⟨0, Nat.succ_pos _⟩
      · apply familyPoint_ext a rest
        intro i
        exact components i.succ

variable {M}
variable {F : Object S ⥤ (Cᵒᵖ ⥤ Type w)} (data : PreservingData F)

/-- Reading an ordered component of a genuine family comparison is the
actual functor image of the corresponding contextual assignment. -/
theorem famIso_image_project (arity : List (MetaArity S))
    (i : Fin arity.length) (a : Cᵒᵖ) (point : (F.obj ⟨arity⟩).obj a) :
    (data.toModel.familyProj arity i).app a ((data.famIso arity).hom.app a point) =
      (F.map (slot arity i)).app a point :=
  ConcreteCategory.congr_hom (NatTrans.congr_app (data.famIso_proj arity i) a) point
end GenericFamilyPoints

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedPresheaf
end
