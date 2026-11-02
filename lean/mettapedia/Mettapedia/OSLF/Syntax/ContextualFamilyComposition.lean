import Mettapedia.OSLF.Syntax.ContextualFamily

/-!
# Composition between contextual declaration families

Assignments may change the declaration family. Their composition is the
existing contextual instantiation of each image, and its action on every
object context agrees with sequential instantiation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ContextualFamily.Assignment

variable {S : Signature} {V W X Y : Type}
  {source : V → MetaArity S} {middle : W → MetaArity S}
  {target : X → MetaArity S} {last : Y → MetaArity S}

abbrev compose (outer : Assignment middle target) (inner : Assignment source middle) :
    Assignment source target := fun identity => instantiate outer (inner identity)

theorem instantiate_compose (outer : Assignment middle target) (inner : Assignment source middle)
    {Γ : Ctx S} {sort : S.Srt} (term : Term (signature S source) Γ sort) :
    instantiate (compose outer inner) term = instantiate outer (instantiate inner term) :=
  (instantiate_comp inner outer term).symm

theorem compose_associative (first : Assignment source middle) (second : Assignment middle target)
    (third : Assignment target last) :
    compose third (compose second first) = compose (compose third second) first := by
  funext identity
  exact instantiate_comp second third (first identity)

theorem compose_identity_left (assignment : Assignment source middle) :
    compose (generator middle) assignment = assignment := by
  funext identity
  exact instantiate_identity (assignment identity)

theorem compose_identity_right (assignment : Assignment source middle) :
    compose assignment (generator source) = assignment := by
  funext identity
  exact instantiate_generator assignment identity

end Mettapedia.OSLF.Binding.ContextualFamily.Assignment
