import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.SimpleFragmentCwf
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.SimpleFragmentSubstitutionTranslation
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.ContextualLadderBridge
import Mettapedia.GSLT.Core.ContextualStrictCwfMorphism

/-!
# A strict CwF morphism from simple syntax to the cumulative tower

The term translation erases intrinsic typing indices while preserving their
typing judgments.  Its substitution laws extend to a functor of contexts and
a natural map of type-and-term families, preserving terminal context and
comprehension.  Strictness concerns this structure; it does not assert
injectivity of erased terms or conservativity of the target calculus.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace SimpleFragmentCwfMorphism

open _root_.CategoryTheory
open scoped _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open FourFaceBetaExperiment.IntrinsicSTT
open FourFaceBetaExperiment.TowerDTT
open SimpleFragmentSubstitutionTranslation

open Presentation

variable {Γ Δ Θ : List Ty}

theorem eraseContext_wellFormed (Γ : List Ty) :
    Presentation.Declaration.ContextWellFormed Presentation.Tower.rules (eraseContext Γ) := by
  induction Γ with
  | nil => exact .nil
  | cons A Γ ih => exact .snoc ih (eraseTypeAt_hasType A (eraseContext Γ)) (.sort (levelOf A))

/-- Translate a simple context, retaining its telescope formation proof. -/
def mapContext (Γ : List Ty) : SyntacticContextual.FormedContext Presentation.Tower.rules where
  arity := Γ.length
  context := eraseContext Γ
  wellFormed := eraseContext_wellFormed Γ

/-- Every simple type is closed, so it forms a type over any tower context. -/
def simpleType (Γ : SyntacticContextual.FormedContext Presentation.Tower.rules) (A : Ty) : SyntacticContextual.TypeOver Γ where
  code := eraseTypeAt Γ.arity A
  level := .sort (levelOf A)
  isUniverse := .sort (levelOf A)
  formed := eraseTypeAt_hasType A Γ.context

def mapTerm {A : Ty} (t : Term Γ A) : SyntacticContextual.Term (mapContext Γ) (simpleType (mapContext Γ) A) where
  code := eraseTerm t
  typed := eraseTerm_hasType t

def mapSubstitution (σ : Substitution Δ Γ) : SyntacticContextual.ContextHom (mapContext Γ) (mapContext Δ) where
  substitution := eraseSubstitution σ
  typed := by
    intro index
    have typed := eraseTerm_hasType (σ (typedVarAt Δ index))
    have lookup := lookup_eraseContext (typedVarAt Δ index)
    rw [eraseVar_typedVarAt] at lookup
    change Presentation.Tower.HasType (eraseContext Γ) (eraseSubstitution σ index)
      (Presentation.subst (eraseSubstitution σ) ((eraseContext Δ).lookup index))
    rw [lookup, eraseTypeAt_subst]
    simpa only [← eraseSubstitution_apply, eraseVar_typedVarAt] using typed

theorem eraseSubstitution_comp (σ : Substitution Θ Δ) (τ : Substitution Δ Γ) :
    eraseSubstitution (Substitution.comp σ τ) =
      Presentation.subComp (eraseSubstitution τ) (eraseSubstitution σ) := by
  funext index
  obtain ⟨v, hv⟩ : ∃ v : Var Θ (contextTypeAt Θ index), eraseVar v = index :=
    ⟨typedVarAt Θ index, eraseVar_typedVarAt Θ index⟩
  rw [← hv]
  simp only [eraseSubstitution_apply, Substitution.comp, eraseTerm_substitute,
    Presentation.subComp]

/-- The existing substitution translation is a functor on context categories. -/
def contextFunctor : CategoryTheory.Functor syntacticCwfWithTerminal.toCwf.base.Context
    (SyntacticContextual.asCwfWithTerminal Presentation.Tower.rules).toCwf.base.Context where
  obj Γ := ⟨mapContext Γ.val⟩
  map σ := mapSubstitution σ
  map_id Γ := by
    apply SyntacticContextual.ContextHom.ext
    exact eraseSubstitution_variables Γ.val
  map_comp σ τ := by
    apply SyntacticContextual.ContextHom.ext
    exact eraseSubstitution_comp τ σ

theorem simpleType_reindex (Γ Δ : SyntacticContextual.FormedContext Presentation.Tower.rules)
    (σ : SyntacticContextual.ContextHom Γ Δ) (A : Ty) :
    (simpleType Δ A).reindex σ = simpleType Γ A := by
  apply SyntacticContextual.TypeOver.ext
  · exact eraseTypeAt_subst A σ.substitution
  · rfl

/-- Types and terms translate together, naturally under every substitution. -/
def familyMorphism : CwfFamilyMorphism syntacticCwfWithTerminal.toCwf
    (SyntacticContextual.asCwfWithTerminal Presentation.Tower.rules).toCwf where
  base := contextFunctor
  family :=
    { app := fun Γ =>
        { onIndex := simpleType (mapContext Γ.unop.val)
          onFibre := fun _ t => mapTerm t }
      naturality := by
        intro Γ Δ σ
        apply IndexedFamily.Hom.ext
        · funext A
          exact (simpleType_reindex _ _ (mapSubstitution σ.unop) A).symm
        · intro A t
          apply SyntacticContextual.Term.heq_of_type_eq_of_code_eq
          · exact (simpleType_reindex _ _ (mapSubstitution σ.unop) A).symm
          · exact eraseTerm_substitute σ.unop t }

/-- Translation preserves the chosen terminal context and comprehension,
including the projection and generic variable. -/
def strictMorphism : StrictCwfMorphism syntacticCwfWithTerminal
    (SyntacticContextual.asCwfWithTerminal Presentation.Tower.rules) where
  toFamilyMorphism := familyMorphism
  empty_preserved := rfl
  extension_preserved _ _ := rfl
  projection_preserved Γ A := by
    apply SyntacticContextual.ContextHom.ext
    change eraseSubstitution (fun v => Term.var (Var.succ v)) =
      Presentation.subComp Presentation.ids Presentation.projection
    rw [Presentation.subComp_ids_left]
    funext index
    rw [← eraseVar_typedVarAt Γ index, eraseSubstitution_apply]
    rfl
  variable_preserved Γ A := by
    apply SyntacticContextual.Term.heq_of_type_eq_of_code_eq
    · apply SyntacticContextual.TypeOver.ext
      · change eraseTypeAt (A :: Γ).length A =
          Presentation.subst Presentation.ids
            (Presentation.subst Presentation.projection (eraseTypeAt Γ.length A))
        rw [eraseTypeAt_subst, eraseTypeAt_subst]
        rfl
      · rfl
    · rfl

#print axioms contextFunctor
#print axioms familyMorphism
#print axioms strictMorphism

end SimpleFragmentCwfMorphism
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
