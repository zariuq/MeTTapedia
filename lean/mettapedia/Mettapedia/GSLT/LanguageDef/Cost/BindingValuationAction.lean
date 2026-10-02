import Mettapedia.GSLT.LanguageDef.BindingSignatureValuation
import Mathlib.Algebra.Group.Action.Defs

/-!
# Open account expressions acting on full binding values

At a context an account is a complete semantic value of its account sort.
Its grade can depend on every variable in the mixed context. Unit, product
and the selected value action are pointwise in the existing natural-family
binding model. Simultaneous substitution transports both the account and
the complete value, including function values beneath binders.

The action is specified only at its selected result sort. This does not
assert that it commutes through arbitrary language constructors.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Cost.BindingValuationAction

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.CategoricalBindingModel
open _root_.CategoryTheory
open BindingSyntax.Valuation

universe u

variable {language : LanguageDef} {base : String → Type u}
  (constructors : Constructors language base) (accountSort : TypeExpr)

abbrev Account (Γ : List TypeExpr) :=
  (algebra constructors).substitution.Carrier Γ accountSort

variable [Monoid (Value base accountSort)]

/-- The unit expression is constant, although other account expressions
can depend on the valuation. -/
def one {Γ : List TypeExpr} : Account constructors accountSort Γ where
  value := fun _ _ _ => TypeCat.ofHom (fun _ => (1 : Value base accountSort))
  natural := fun _ _ _ => rfl

/-- Ordered multiplication is evaluated at the same full valuation. -/
def mul {Γ : List TypeExpr} (first second : Account constructors accountSort Γ) :
    Account constructors accountSort Γ where
  value := fun Z m ρ => TypeCat.ofHom (fun z =>
    (first.value Z m ρ z : Value base accountSort) *
      (second.value Z m ρ z : Value base accountSort))
  natural := by
    intro Z Z' h m ρ
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext z
    exact congrArg₂ ((· * ·) : Value base accountSort → Value base accountSort → _)
      (congrArg (fun f => f z) (first.natural h m ρ))
      (congrArg (fun f => f z) (second.natural h m ρ))

instance accountMonoid (Γ : List TypeExpr) : Monoid (Account constructors accountSort Γ) where
  one := one constructors accountSort
  mul := mul constructors accountSort
  mul_assoc := by
    intro first second third
    apply Model.ElemOver.ext
    funext Z m ρ
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext z
    change ((first.value Z m ρ z : Value base accountSort) * second.value Z m ρ z) *
        third.value Z m ρ z = _
    exact mul_assoc _ _ _
  one_mul := by
    intro value
    apply Model.ElemOver.ext
    funext Z m ρ
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext z
    change (1 : Value base accountSort) * value.value Z m ρ z = value.value Z m ρ z
    exact one_mul _
  mul_one := by
    intro value
    apply Model.ElemOver.ext
    funext Z m ρ
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext z
    change (value.value Z m ρ z : Value base accountSort) * 1 = value.value Z m ρ z
    exact mul_one _

/-- Genuine simultaneous substitution is a monoid map on open grades. -/
def substitute {Γ Δ : List TypeExpr}
    (env : BindingSubstitutionAlgebra.Environment (BindingSyntax.signatureOf language)
      (algebra constructors).substitution.Carrier Γ Δ) :
    Account constructors accountSort Γ →* Account constructors accountSort Δ where
  toFun := (algebra constructors).substitution.substitute env
  map_one' := rfl
  map_mul' := fun _ _ => rfl

theorem substitute_identity {Γ : List TypeExpr} :
    substitute constructors accountSort
        (fun _ v => (algebra constructors).substitution.injectVar v) =
      MonoidHom.id (Account constructors accountSort Γ) := by
  apply MonoidHom.ext
  intro value
  exact (algebra constructors).substitution.substitute_identity value

theorem substitute_comp {Γ Δ Θ : List TypeExpr}
    (first : BindingSubstitutionAlgebra.Environment (BindingSyntax.signatureOf language)
      (algebra constructors).substitution.Carrier Γ Δ)
    (second : BindingSubstitutionAlgebra.Environment (BindingSyntax.signatureOf language)
      (algebra constructors).substitution.Carrier Δ Θ) :
    (substitute constructors accountSort second).comp
        (substitute constructors accountSort first) =
      substitute constructors accountSort
        (fun sort v => (algebra constructors).substitution.substitute second (first sort v)) := by
  apply MonoidHom.ext
  intro value
  exact (algebra constructors).substitution.substitute_comp first second value

variable (valueSort : TypeExpr) [MulAction (Value base accountSort) (Value base valueSort)]

/-- The selected action keeps a full natural value at every stage. -/
def act {Γ : List TypeExpr} (account : Account constructors accountSort Γ)
    (value : (algebra constructors).substitution.Carrier Γ valueSort) :
    (algebra constructors).substitution.Carrier Γ valueSort where
  value := fun Z m ρ => TypeCat.ofHom (fun z =>
    (account.value Z m ρ z : Value base accountSort) •
      (value.value Z m ρ z : Value base valueSort))
  natural := by
    intro Z Z' h m ρ
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext z
    exact congrArg₂ ((· • ·) : Value base accountSort → Value base valueSort → _)
      (congrArg (fun f => f z) (account.natural h m ρ))
      (congrArg (fun f => f z) (value.natural h m ρ))

theorem act_one {Γ : List TypeExpr}
    (value : (algebra constructors).substitution.Carrier Γ valueSort) :
    act constructors accountSort valueSort 1 value = value := by
  apply Model.ElemOver.ext
  funext Z m ρ
  apply TypeCat.Hom.ext
  apply TypeCat.Fun.ext
  funext z
  change (1 : Value base accountSort) • (value.value Z m ρ z : Value base valueSort) = _
  exact one_smul _ _

theorem act_mul {Γ : List TypeExpr}
    (first second : Account constructors accountSort Γ)
    (value : (algebra constructors).substitution.Carrier Γ valueSort) :
    act constructors accountSort valueSort (first * second) value =
      act constructors accountSort valueSort first
        (act constructors accountSort valueSort second value) := by
  apply Model.ElemOver.ext
  funext Z m ρ
  apply TypeCat.Hom.ext
  apply TypeCat.Fun.ext
  funext z
  change ((first.value Z m ρ z : Value base accountSort) * second.value Z m ρ z) •
      (value.value Z m ρ z : Value base valueSort) = _
  exact mul_smul _ _ _

/-- Both coordinates use the actual full environment; no erased environment
is substituted for the semantic one. -/
theorem act_substitute {Γ Δ : List TypeExpr}
    (env : BindingSubstitutionAlgebra.Environment (BindingSyntax.signatureOf language)
      (algebra constructors).substitution.Carrier Γ Δ)
    (account : Account constructors accountSort Γ)
    (value : (algebra constructors).substitution.Carrier Γ valueSort) :
    (algebra constructors).substitution.substitute env
        (act constructors accountSort valueSort account value) =
      act constructors accountSort valueSort
        (substitute constructors accountSort env account)
        ((algebra constructors).substitution.substitute env value) := rfl

theorem read_act {Γ : List TypeExpr}
    (account : Account constructors accountSort Γ)
    (value : (algebra constructors).substitution.Carrier Γ valueSort)
    (assignment : (type : TypeExpr) → Var Γ type → Value base type) :
    read constructors (act constructors accountSort valueSort account value) assignment =
      read constructors account assignment • read constructors value assignment := rfl

end Mettapedia.GSLT.LanguageDef.Cost.BindingValuationAction
