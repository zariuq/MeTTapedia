import Mettapedia.Languages.Lean.Declarations.QuotientProfile

namespace Mettapedia.Languages.Lean.Declarations.QuotientProfileControls

open _root_.Lean Meta Elab Command

run_cmd liftTermElabM do
  for name in [``Quot, ``Quot.mk, ``Quot.lift, ``Quot.liftOn] do
    let (type, levels) ← QuotientProfile.typeInstance name
    if let some reason ← QuotientProfile.refusal? name levels then
      throwError "Type quotient instance refused: {reason}"
    unless ← isDefEq type (← inferType (mkConst name levels)) do
      throwError "quotient signature differs from the kernel declaration: {name}"
  unless (← QuotientProfile.refusal? ``Quot [.zero]).isSome do
    throwError "a Prop quotient carrier was accepted by the Type profile"
  unless (← QuotientProfile.refusal? ``Quot [.param `u]).isSome do
    throwError "an unconstrained Sort quotient carrier was accepted by the Type profile"

example {α : Type u} {β : Type v} (r : α → α → Prop) (f : α → β)
    (respect : ∀ a b, r a b → f a = f b) (a : α) :
    Quot.lift f respect (Quot.mk r a) = f a := rfl

example : ¬ (∀ a b : Bool, True → a = b) := by
  intro respect
  have contradiction := respect true false trivial
  cases contradiction

end Mettapedia.Languages.Lean.Declarations.QuotientProfileControls
