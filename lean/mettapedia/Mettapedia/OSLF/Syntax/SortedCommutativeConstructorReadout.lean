import Mettapedia.OSLF.Syntax.SortedCommutativeValues

/-!
# Complete free-constructor argument readout

The independently formed equation quotient retains every child class of a
free constructor. The result applies at all declared sorts, including fresh
bundle sorts, without a literal decoder on arbitrary quotient classes.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.SortedCommutative

universe u v

variable {signature : Mettapedia.OSLF.SortedConstructors.Signature.{u,v}}
variable {Parallel : signature.Srt → Prop}

theorem node_class_eq_iff (constructor : signature.Constructor)
    (first second : (position : Fin (signature.arity constructor)) →
      Term signature Parallel (signature.input constructor position)) :
    classOf (.node constructor first) = classOf (.node constructor second) ↔
      ∀ position, classOf (first position) = classOf (second position) := by
  refine ⟨fun same => ?_, fun arguments => Quotient.sound (.node (fun position => Quotient.exact (arguments position)))⟩
  have heads := Head.class_injective
    ((Head.class_node constructor first).trans (same.trans (Head.class_node constructor second).symm))
  have arrays : (fun position => classOf (first position)) = fun position => classOf (second position) := by
    simpa only [Head.node.injEq, heq_eq_eq, true_and] using heads
  exact fun position => congrFun arrays position

end Mettapedia.OSLF.SortedCommutative
