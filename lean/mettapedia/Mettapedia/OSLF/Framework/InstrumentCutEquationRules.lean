import Mettapedia.OSLF.Framework.InstrumentCutEquationExposure

/-!
# Actual equation-matching ask/get/build rules and free argument bundles

The supplied raw arguments are retained. The matching condition is the
authored unary-unit congruence, while the result is the whole supplied bundle
or selected component. Equality of argument bundles earns componentwise
equations, rather than assuming freeness for arbitrary equational theories.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.InstrumentCutContexts

open Mettapedia.OSLF.SortedConstructors
open Mettapedia.OSLF.SortedConstructors.Padding

universe u w

variable {Symbols : Type u} (arity : Symbols → Nat)

abbrev RawBase := RawTerm (signature arity) (Srt.base : Srt Symbols arity) .base

def rawOriginal (constructor : Symbols) (arguments : Fin (arity constructor) → RawBase arity) : RawBase arity :=
  Term.node (signature := extended (signature arity) .base) (Sum.inl (Constructor.original constructor)) arguments

def rawBundle (constructor : Symbols) (arguments : Fin (arity constructor) → RawBase arity) :
    RawTerm (signature arity) .base (.arguments constructor) :=
  Term.node (signature := extended (signature arity) .base) (Sum.inl (Constructor.arguments constructor)) arguments

theorem rawBundle_equations_iff (constructor : Symbols)
    (first second : Fin (arity constructor) → RawBase arity) :
    Equation (signature arity) .base (rawBundle arity constructor first) (rawBundle arity constructor second) ↔
      ∀ position, Equation (signature arity) .base (first position) (second position) := by
  constructor
  · intro equation position
    have readout := equation_normalizes equation
    have components := Term.node.inj readout
    exact (equation_iff_normalizes _ _).mpr (congrFun components position)
  · intro components
    exact Equation.congruence (signature := signature arity) (paddingSort := .base)
      (Sum.inl (Constructor.arguments constructor)) first second components

theorem rawBundle_class_iff (constructor : Symbols)
    (first second : Fin (arity constructor) → RawBase arity) :
    classOf (rawBundle arity constructor first) = classOf (rawBundle arity constructor second) ↔
      ∀ position, Equation (signature arity) .base (first position) (second position) := by
  rw [classOf_eq_iff, rawBundle_equations_iff]

theorem equation_ask_iff (constructor : Symbols)
    (arguments : Fin (arity constructor) → RawBase arity) (source : RawBase arity)
    (target : RawTerm (signature arity) .base (.arguments constructor)) :
    EquationProbeExposure arity (.ask constructor) (classOf source)
      (classOf (rawOriginal arity constructor arguments)) (classOf (rawBundle arity constructor arguments))
      (classOf target) ↔
      Equation (signature arity) .base source (rawOriginal arity constructor arguments) ∧
        Equation (signature arity) .base target (rawBundle arity constructor arguments) :=
  equationProbeExposure_raw_iff arity (.ask constructor) source (rawOriginal arity constructor arguments)
    (rawBundle arity constructor arguments) target

theorem equation_get_iff (constructor : Symbols) (position : Fin (arity constructor))
    (arguments : Fin (arity constructor) → RawBase arity)
    (source : RawTerm (signature arity) .base (.arguments constructor)) (target : RawBase arity) :
    EquationProbeExposure arity (.get constructor position) (classOf source)
      (classOf (rawBundle arity constructor arguments)) (classOf (arguments position)) (classOf target) ↔
      Equation (signature arity) .base source (rawBundle arity constructor arguments) ∧
        Equation (signature arity) .base target (arguments position) :=
  equationProbeExposure_raw_iff arity (.get constructor position) source (rawBundle arity constructor arguments)
    (arguments position) target

theorem equation_build_iff (constructor : Symbols)
    (arguments : Fin (arity constructor) → RawBase arity)
    (source : RawTerm (signature arity) .base (.arguments constructor)) (target : RawBase arity) :
    EquationProbeExposure arity (.build constructor) (classOf source)
      (classOf (rawBundle arity constructor arguments)) (classOf (rawOriginal arity constructor arguments)) (classOf target) ↔
      Equation (signature arity) .base source (rawBundle arity constructor arguments) ∧
        Equation (signature arity) .base target (rawOriginal arity constructor arguments) :=
  equationProbeExposure_raw_iff arity (.build constructor) source (rawBundle arity constructor arguments)
    (rawOriginal arity constructor arguments) target

structure EquationAskReceipt (Origins : Type w) (constructor : Symbols) (source : RawBase arity)
    (target : RawTerm (signature arity) .base (.arguments constructor)) where
  origin : Origins
  arguments : Fin (arity constructor) → RawBase arity
  matching : Equation (signature arity) .base source (rawOriginal arity constructor arguments)
  target_readout : Equation (signature arity) .base target (rawBundle arity constructor arguments)

theorem EquationAskReceipt.exposure {Origins : Type w} {constructor : Symbols}
    {source : RawBase arity} {target : RawTerm (signature arity) .base (.arguments constructor)}
    (receipt : EquationAskReceipt arity Origins constructor source target) :
    EquationProbeExposure arity (.ask constructor) (classOf source)
      (classOf (rawOriginal arity constructor receipt.arguments))
      (classOf (rawBundle arity constructor receipt.arguments)) (classOf target) :=
  (equation_ask_iff arity constructor receipt.arguments source target).mpr
    ⟨receipt.matching, receipt.target_readout⟩

end Mettapedia.OSLF.Framework.InstrumentCutContexts
