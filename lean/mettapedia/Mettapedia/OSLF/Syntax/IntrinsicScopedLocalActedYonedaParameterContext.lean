import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedMappedParameterContext
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedProgramExponential
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedProgramParameterCoordinates

/-!
# Ordered parameter products under the operational Yoneda embedding

The raw parameter products and coordinates map to the ordinary ordered
context product. The closed-sort identity comparison connects their source
presentation to the canonical program restriction before the projection
laws are specialized.
-/

set_option autoImplicit false
noncomputable section
namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedPresheaf
open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open SecondOrderContext IntrinsicScopedLocalPolynomial IntrinsicScopedLocalActedClassifier
open CategoricalBindingModel
universe w
variable {S : Signature} {K : List (MetaArity S)}
variable (R : List (LocalRule S)) (equations : List (EqAxiom S K))

abbrev parameterEmbedding : Base equations ⥤ Presheaf.{w} R equations :=
  programSection R equations ⋙ embedding.{w} R equations

def parameterSourceSort (s : S.Srt) : Base equations :=
  (authoredEquationPresentation S equations).quotientFunctor.obj (single S [] s)

def parameterSourcePairs (Γ : Ctx S) (s : S.Srt) :
    parameterContext equations (s :: Γ) ≅ parameterContext equations Γ ⨯ parameterSourceSort equations s :=
  Iso.refl _

def parameterSourceHead (Γ : Ctx S) (s : S.Srt) :
    parameterContext equations (s :: Γ) ⟶ parameterSourceSort equations s := prod.snd

def parameterSourceTail (Γ : Ctx S) (s : S.Srt) :
    parameterContext equations (s :: Γ) ⟶ parameterContext equations Γ := prod.fst

theorem parameterSourcePairs_head (Γ : Ctx S) (s : S.Srt) :
    (parameterSourcePairs equations Γ s).hom ≫ prod.snd = parameterSourceHead equations Γ s :=
  Category.id_comp _

theorem parameterSourcePairs_tail (Γ : Ctx S) (s : S.Srt) :
    (parameterSourcePairs equations Γ s).hom ≫ prod.fst = parameterSourceTail equations Γ s :=
  Category.id_comp _

def parameterSourceCoordinate {Γ : Ctx S} {s : S.Srt} (v : Var Γ s) :
    parameterContext equations Γ ⟶ parameterSourceSort equations s := parameterVariable equations v

theorem parameterSourceCoordinate_head (Γ : Ctx S) (s : S.Srt) :
    parameterSourceHead equations Γ s = parameterSourceCoordinate equations (Var.zero : Var (s :: Γ) s) := rfl

theorem parameterSourceCoordinate_succ (s : S.Srt) {Γ : Ctx S} {r : S.Srt} (v : Var Γ r) :
    parameterSourceCoordinate equations (Var.succ v : Var (s :: Γ) r) =
      parameterSourceTail equations Γ s ≫ parameterSourceCoordinate equations v := rfl

def parameterClosedSortIso (s : S.Srt) :
    (parameterEmbedding.{w} R equations).obj (parameterSourceSort equations s) ≅ program R equations [] s :=
  Iso.refl _

def parameterPairIso (Γ : Ctx S) (s : S.Srt) :
    (parameterEmbedding.{w} R equations).obj (parameterContext equations (s :: Γ)) ≅
      (parameterEmbedding.{w} R equations).obj (parameterContext equations Γ) ⊗ program R equations [] s := by
  let _ := programEmbedding_preservesLimits.{w} R equations
  exact ParameterImage.imagePair (parameterEmbedding.{w} R equations) (parameterContext equations)
    (parameterSourceSort equations) (program R equations []) (parameterSourcePairs equations)
    (parameterClosedSortIso R equations) Γ s

def parameterContextRepresentableIso (Γ : Ctx S) :
    (parameterEmbedding.{w} R equations).obj (parameterContext equations Γ) ≅ contextOf (program R equations []) Γ := by
  let _ := programEmbedding_preservesLimits.{w} R equations
  exact ParameterImage.contextIso (parameterEmbedding.{w} R equations) (parameterContext equations) (parameterSourceSort equations)
    (program R equations []) (terminalIsTerminal (C := Base equations)) (parameterSourcePairs equations)
    (parameterClosedSortIso R equations) Γ


end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedPresheaf
end
