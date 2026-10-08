import Mettapedia.OSLF.Syntax.BindingClosedGeneratedModel

/-!
# The recovered binding parser and actual normalized functor

Their equality follows from the earned complete assignment reconstruction and
the independent raw-expression evaluator. It retains every generated object
and arrow, including the chosen product and function comparisons.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Binding.ClosedPresentation.GeneratedModel

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory.RelativeClosedSyntax
open GeneratedCategory FunctorNormalization Interpretation

universe k w

variable {binding : Mettapedia.OSLF.Binding.Signature}
variable {D : Type w} [Category.{k} D] [CartesianMonoidalCategory D]
variable [MonoidalClosed D] [HasFiniteLimits D]
variable (mapping : Object (signature.{k} binding) ⥤ D)
variable [PreservesFiniteLimits mapping] [MonoidalClosedFunctor mapping]

private theorem parser_equal {first second : Assignment Base.{k} (symbols binding) D}
    (before : Realization (signature binding) first) (after : Realization (signature binding) second)
    (same : first = second) : functor first before = functor second after := by
  cases same
  rfl

theorem interpretation_eq_normalized :
    (operations mapping).interpretation.functor = normalizedFunctor mapping :=
  (parser_equal (operations mapping).realization
    (reconstruction_realization mapping (headers binding)) (assignment_equal mapping)).trans
      (reconstructed_functor_equal mapping (headers binding))

end Mettapedia.OSLF.Binding.ClosedPresentation.GeneratedModel
