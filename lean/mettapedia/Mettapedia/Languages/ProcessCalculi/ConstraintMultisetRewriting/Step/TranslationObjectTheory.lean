import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TranslationFrames

/-!
# The Π/Σ/Id fragment as an object theory inside the second-order base

The constructors of the dependent fragment, written as a binding signature with two sorts (`ty`,
`tm`): `Π` and `Σ` bind a term variable in their codomain, `λ` binds a term variable, and the rest
bind nothing (`sig`). Nine operators, three computation rules (`Π`-beta and the two projections).

In this design the frame equivalence is syntactic equality of observations. An object-level
beta redex and its reduct are different observations, so the equation between them has **no
solution** in the second-order frames (`object_beta_unsolvable`): object conversion is not the
frame equivalence, and must be run as rewriting. At dependent frames the same beta step is part of
the equivalence itself (`native_beta`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
namespace Translation
namespace ObjectTheory

open Mettapedia.OSLF
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation

/-- The two sorts of the object theory. -/
inductive Kind
  | ty
  | tm
  deriving DecidableEq

/-- The constructors of the Π/Σ/Id fragment, indexed by the sort they produce. -/
inductive Op : Kind → Type
  | pi : Op .ty
  | sigma : Op .ty
  | id : Op .ty
  | lam : Op .tm
  | app : Op .tm
  | pair : Op .tm
  | fst : Op .tm
  | snd : Op .tm
  | refl : Op .tm

/-- Binding arities: `Π A (x. B)`, `Σ A (x. B)`, `Id A a b`, `λ (x. b)`, `app f a`, `pair a b`,
`fst p`, `snd p`, `refl a`. -/
def arity : {s : Kind} → Op s → List (List Kind × Kind)
  | _, .pi => [([], .ty), ([.tm], .ty)]
  | _, .sigma => [([], .ty), ([.tm], .ty)]
  | _, .id => [([], .ty), ([], .tm), ([], .tm)]
  | _, .lam => [([.tm], .tm)]
  | _, .app => [([], .tm), ([], .tm)]
  | _, .pair => [([], .tm), ([], .tm)]
  | _, .fst => [([], .tm)]
  | _, .snd => [([], .tm)]
  | _, .refl => [([], .tm)]

/-- **The Π/Σ/Id fragment as a second-order binding signature.** -/
def sig : Binding.Signature := ⟨Kind, Op, arity⟩

/-- The empty list frame: no metavariables. -/
abbrev noMetas : List (Binding.MetaArity sig) := []

/-- `(λx. x) y`, in the object context `y : tm`. -/
def redex : Binding.Term (Sig sig noMetas) [Kind.tm] Kind.tm :=
  .op (.inl Op.app)
    (.cons (.op (.inl Op.lam) (.cons (.var .zero) .nil)) (.cons (.var .zero) .nil))

/-- The object-level beta equation `(λx. x) y ≐ y`. -/
def betaStore : EquationStore (Binding.ContextualFamily.Observation sig noMetas.get) :=
  [(⟨[Kind.tm], Kind.tm, redex⟩, ⟨[Kind.tm], Kind.tm, .var .zero⟩)]

/-- **Object conversion is not the frame equivalence**: the beta equation has no solution in the
second-order frames, at any later frame. -/
theorem object_beta_unsolvable : ¬ (listFrames sig).Solvable (a := noMetas) betaStore := by
  rintro ⟨N, f, solved⟩
  have equation := solved _ (List.mem_singleton_self _)
  change Binding.ContextualFamily.observe (Binding.ContextualFamily.instantiate f redex) =
    Binding.ContextualFamily.observe
      (Binding.ContextualFamily.instantiate f (.var .zero : Binding.Term (Sig sig noMetas) _ _))
    at equation
  have terms := Binding.ContextualFamily.observe_injective equation
  cases terms

/-- At dependent frames the same beta step is part of the equivalence. -/
theorem native_beta {Head : Type} (rules : Rules Head) :
    Conv rules.headEq (.app (.lam (.var 0)) (.var 0) : Tm Head 1) (.var 0) rules.computation :=
  .rel _ _ (StepCore.betaPi (.var 0) (.var 0))

end ObjectTheory
end Translation

#print axioms Translation.ObjectTheory.object_beta_unsolvable
#print axioms Translation.ObjectTheory.native_beta

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
