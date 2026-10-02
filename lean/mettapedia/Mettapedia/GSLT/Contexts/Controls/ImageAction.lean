import Mettapedia.GSLT.Contexts.ContextMorphism

/-!
# Image action need not be an ambient context functor

Equivariance determines the action of translated contexts on translated
fillings. It need not determine their action on other target terms. The
small function model below separates these two assertions even for a map
that transports transitions and preserves every probe's bisimilarity.

This is an abstract contract control, not an authored language or an
implementation of a language encoding.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Contexts.Controls.ImageAction

/-- Operations on a carrier form a context theory by ordinary function
composition. This control equips it with no reductions and equality of terms. -/
def functionTheory (Value : Type) : ContextTheory.{0} where
  Interface := Unit
  Term := fun _ => Value
  equations := fun _ => ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun _ _ => False
  rewrites_resp_left := fun _ step => False.elim step
  rewrites_resp_right := fun step _ => False.elim step
  Context := fun {arity} _ _ => (arity → Value) → Value
  fill := fun context filling => context filling
  fill_resp := by
    intro arity holes result context first second same
    exact congrArg context (funext same)
  identity := fun _ filling => filling ()
  fill_identity := fun _ _ => rfl
  plug := fun context inner filling =>
    context fun index => inner index fun leaf => filling ⟨index, leaf⟩
  fill_plug := fun _ _ _ => rfl
  relabel := fun rename _ context filling => context fun index => filling (rename index)
  fill_relabel := fun _ _ _ _ => rfl
  constant := fun value _ => value
  fill_constant := fun _ _ => rfl

/-- The unique source value translates to `false`. Translated contexts also
return `false`, so their action agrees on every translated filling. -/
def unitToBoolMap : ContextMap (functionTheory Unit) (functionTheory Bool) where
  interface := fun _ => ()
  term := fun _ => false
  context := fun _ _ => false
  term_resp := fun _ => rfl
  equivariant := fun _ _ => rfl

/-- The image action also meets the operational morphism contract for these
two reduction-free control theories. -/
def unitToBool : ContextMorphism (functionTheory Unit) (functionTheory Bool) where
  toContextMap := unitToBoolMap
  transitions := by
    intro origin result label term next step
    exact False.elim step
  preserves := by
    intro probe index left right related
    exact ContextTheory.Probe.bisimilar_refl (index := index) (unitToBoolMap.push probe) false

/-- The derived identity law holds on every source image. -/
theorem identity_on_image (term : (functionTheory Unit).Term ()) :
    (functionTheory Bool).apply (unitToBool.context ((functionTheory Unit).identity ()))
      (unitToBool.term term) = unitToBool.term term :=
  unitToBool.toContextMap.context_identity_on_image term

/-- The same context fails the identity law at a target value outside the
image. Thus image action does not yield a functor on ambient context classes. -/
theorem identity_not_on_target :
    ¬ (functionTheory Bool).ContextEquiv
      (unitToBool.context ((functionTheory Unit).identity ()))
      ((functionTheory Bool).identity ()) := by
  intro same
  have impossible : false = true := same (fun _ => true)
  cases impossible

/-- An actual identity map satisfies the ambient identity law. -/
theorem identity_map_on_target :
    (functionTheory Bool).ContextEquiv
      ((ContextMap.id (functionTheory Bool)).context ((functionTheory Bool).identity ()))
      ((functionTheory Bool).identity ()) :=
  (functionTheory Bool).contextEquiv_refl _

end Mettapedia.GSLT.Contexts.Controls.ImageAction
