import Mettapedia.OSLF.Syntax.FiniteLimitGeneratedContextEmbedding
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# Why finite-limit extension restricts the source morphisms

The represented-context embedding preserves existing finite limits of every
finite shape, including the terminal and product contexts of authored syntax.
A constant two-element-set functor out of a concrete authored context category
fails the terminal-object law, so it cannot be the restriction of any
finite-limit-preserving functor from the generated category. A genuine free
extension property must restrict to interpretations preserving all source
finite limits that actually exist, not just arbitrary context functors.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.UnaryContextBoundary

open CategoryTheory
open CategoryTheory.Limits

/-- The constant two-element-set interpretation of unary contexts. -/
def constantBool : Syntactic.Ctxt signature ⥤ Type :=
  (Functor.const (Syntactic.Ctxt signature)).obj Bool

/-- A two-element set cannot be terminal: the two constant maps from a
singleton distinguish its points. -/
theorem bool_not_terminal : IsTerminal (Bool : Type) → False := by
  intro terminal
  let no : PUnit ⟶ Bool := TypeCat.ofHom (fun _ => false)
  let yes : PUnit ⟶ Bool := TypeCat.ofHom (fun _ => true)
  have equal : no = yes := terminal.hom_ext no yes
  have point : no PUnit.unit = yes PUnit.unit :=
    congrArg (fun f => f PUnit.unit) equal
  exact Bool.false_ne_true point

/-- The constant interpretation does not preserve the terminal authored
context. -/
theorem constantBool_not_preserves_terminal :
    ¬ PreservesLimit (Functor.empty.{0} (Syntactic.Ctxt signature)) constantBool := by
  intro preserves
  have : PreservesLimit (Functor.empty.{0} (Syntactic.Ctxt signature))
      constantBool := preserves
  exact bool_not_terminal (isLimitOfHasTerminalOfPreservesLimit constantBool)

/-- No finite-limit-preserving semantics on the generated category restricts,
even up to natural isomorphism, to this arbitrary context functor. -/
theorem no_finite_limit_extension_of_constantBool
    (G : (finiteLimitGenerated signature).FullSubcategory ⥤ Type)
    [PreservesFiniteLimits G]
    (comparison : contextIntoFiniteLimitGenerated signature ⋙ G ≅ constantBool) :
    False := by
  have : PreservesFiniteProducts (contextIntoFiniteLimitGenerated signature) :=
    contextIntoFiniteLimitGenerated_preservesFiniteProducts signature
  have : PreservesLimit (Functor.empty.{0} (Syntactic.Ctxt signature))
      (contextIntoFiniteLimitGenerated signature) := by
    infer_instance
  have : PreservesLimit (Functor.empty.{0}
      (finiteLimitGenerated signature).FullSubcategory) G := by
    infer_instance
  have : PreservesLimit (Functor.empty.{0} (Syntactic.Ctxt signature))
      (contextIntoFiniteLimitGenerated signature ⋙ G) := by
    infer_instance
  exact constantBool_not_preserves_terminal
    (preservesLimit_of_natIso
      (Functor.empty.{0} (Syntactic.Ctxt signature)) comparison)

end Mettapedia.OSLF.Binding.UnaryContextBoundary

namespace Mettapedia.OSLF.FiniteLimitYoneda

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits

/-- Any finite-limit-preserving semantics extending Yoneda's generated
subcategory must preserve each finite-shaped limit already present in the
source category. This necessary condition is independent of the target model
and of the particular authored language. -/
theorem extension_preserves_existing_finite_limit_shape
    {C : Type} [SmallCategory C]
    (J : Type) [SmallCategory J] [FinCategory J]
    [HasLimitsOfShape J C]
    {D : Type} [Category D]
    (source : C ⥤ D)
    (extension : (Generated C).FullSubcategory ⥤ D)
    [PreservesLimitsOfShape J extension]
    (comparison : intoGenerated C ⋙ extension ≅ source) :
    PreservesLimitsOfShape J source := by
  have : PreservesLimitsOfShape J (intoGenerated C) :=
    intoGenerated_preservesExistingFiniteLimitsOfShape C J
  have : PreservesLimitsOfShape J (intoGenerated C ⋙ extension) :=
    inferInstance
  exact preservesLimitsOfShape_of_natIso comparison

end Mettapedia.OSLF.FiniteLimitYoneda
