import Mettapedia.CategoryTheory.RelativeClosedSyntaxTranslationLimits
import Mettapedia.CategoryTheory.RelativeClosedSyntaxClosedReadout
import Mathlib.CategoryTheory.Monoidal.Closed.Functor

/-!
# Actual closed preservation of the expression-translation functor

Annotated abstraction and complete evaluation survive the generated quotient
map. The real left-oriented monoidal evaluation is recovered through the
earned exchange comparison. At a common hom universe, the canonical Mathlib
exponential comparison is therefore the identity on the retained formal
function object; its isomorphism earns closed functoriality. The constructor
and evaluation readouts keep independently sized bases.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.Translation

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open GeneratedCategory

universe u v a w z b k

variable {C : Type u} [Category.{v} C] {symbols : Symbols.{a}}
variable {D : Type w} [Category.{z} D] {nextSymbols : Symbols.{b}}
variable {signature : Signature (C := C) (symbols := symbols)}
variable {next : Signature (C := D) (symbols := nextSymbols)}
variable (mapping : Translation signature next)

theorem functor_pairing {source left right : Object signature}
    (before : source ⟶ left) (after : source ⟶ right) :
    mapping.functor.map (pairing before after) =
      pairing (mapping.functor.map before) (mapping.functor.map after) := by
  refine Quotient.inductionOn₂ before after ?_
  intro first second
  rfl

theorem functor_abstraction {context argument result : Object signature}
    (body : product context argument ⟶ result) :
    mapping.functor.map (abstraction body) =
      abstraction (signature := next) (context := mapping.functor.obj context)
        (argument := mapping.functor.obj argument) (result := mapping.functor.obj result)
        (mapping.functor.map body) := by
  refine Quotient.inductionOn body ?_
  intro representative
  rfl

theorem functor_evaluation (argument result : Object signature) :
    mapping.functor.map (evaluation argument result) =
      evaluation (mapping.functor.obj argument) (mapping.functor.obj result) := rfl

theorem functor_exchange_inv (first second : Object signature) :
    mapping.functor.map (exchange first second).inv =
      (exchange (mapping.functor.obj first) (mapping.functor.obj second)).inv := rfl

theorem monoidal_left_evaluation (argument result : Object signature) :
    (ihom.ev argument).app result =
      (exchange (exponentialObject argument result) argument).inv ≫ evaluation argument result :=
  (MonoidalClosed.uncurry_id_eq_ev argument result).symm.trans
    ((monoidal_uncurry (𝟙 (exponentialObject argument result))).trans
      (congrArg ((exchange (exponentialObject argument result) argument).inv ≫ ·)
        (unabstract_identity argument result)))

theorem functor_monoidal_evaluation (argument result : Object signature) :
    mapping.functor.map ((ihom.ev argument).app result) =
      (ihom.ev (mapping.functor.obj argument)).app (mapping.functor.obj result) := by
  have first := congrArg mapping.functor.map (monoidal_left_evaluation argument result)
  have transported := mapping.functor.map_comp
    (exchange (exponentialObject argument result) argument).inv (evaluation argument result)
  have complete := congrArg₂ (fun incoming outgoing => incoming ≫ outgoing)
    (mapping.functor_exchange_inv (exponentialObject argument result) argument)
    (mapping.functor_evaluation argument result)
  exact first.trans (transported.trans
    (complete.trans (monoidal_left_evaluation (mapping.functor.obj argument)
      (mapping.functor.obj result)).symm))

section CommonUniverse

variable {E H : Type k} [Category.{k} E] [Category.{k} H]
variable {firstSymbols secondSymbols : Symbols.{k}}
variable {first : Signature (C := E) (symbols := firstSymbols)}
variable {second : Signature (C := H) (symbols := secondSymbols)}
variable (map : Translation first second)

theorem expComparison_identity (argument result : Object first) :
    (expComparison map.functor argument).natTrans.app result =
      𝟙 (exponentialObject (map.functor.obj argument) (map.functor.obj result)) := by
  apply MonoidalClosed.uncurry_injective
  have inverse : inv (CartesianMonoidalCategory.prodComparison map.functor argument
      (exponentialObject argument result)) =
      𝟙 (product (map.functor.obj argument) (map.functor.obj (exponentialObject argument result))) := by
    symm
    apply IsIso.eq_inv_of_hom_inv_id (f := CartesianMonoidalCategory.prodComparison map.functor
      argument (exponentialObject argument result))
    exact (Category.comp_id (CartesianMonoidalCategory.prodComparison map.functor
      argument (exponentialObject argument result))).trans
        (map.productComparison_identity argument (exponentialObject argument result))
  have actual := uncurry_expComparison map.functor argument result
  have substituted := congrArg
    (fun incoming => incoming ≫ map.functor.map ((ihom.ev argument).app result)) inverse
  exact actual.trans (substituted.trans
    ((Category.id_comp _).trans
      ((map.functor_monoidal_evaluation argument result).trans
        (MonoidalClosed.uncurry_id_eq_ev (map.functor.obj argument) (map.functor.obj result)).symm)))

instance functor_expComparison_isIso (argument result : Object first) :
    IsIso ((expComparison map.functor argument).natTrans.app result) := by
  rw [map.expComparison_identity]
  exact (inferInstance : IsIso
    (𝟙 (exponentialObject (map.functor.obj argument) (map.functor.obj result)) :
      exponentialObject (map.functor.obj argument) (map.functor.obj result) ⟶
        exponentialObject (map.functor.obj argument) (map.functor.obj result)))

instance functor_closed : MonoidalClosedFunctor map.functor where
  comparison_iso _argument := NatIso.isIso_of_isIso_app _

end CommonUniverse

end Mettapedia.CategoryTheory.RelativeClosedSyntax.Translation
