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
  unless (← QuotientProfile.soundRefusal? [.zero]).isSome do
    throwError "Quot.sound at a Prop carrier was accepted by the Type profile"
  if let some reason ← QuotientProfile.soundRefusal? [.succ (.param `u)] then
    throwError "Quot.sound at a Type carrier refused: {reason}"
  -- What a set reading must refuse in an expression, as a reading of syntax records it.
  let some funextProof := (← getConstInfo ``funext).value? (allowOpaque := true)
    | throwError "funext without its proof"
  let funextOutside ← QuotientProfile.outside funextProof
  unless funextOutside.any (·.startsWith "Quot.sound at level imax") do
    throwError "funext's proof is a quotient at a Sort carrier, but outside it was found: {funextOutside}"
  let liftOutside ← QuotientProfile.outside (← getConstInfo ``QuotientProfile.lift_beta).type
  unless liftOutside.isEmpty do
    throwError "lift_beta's statement is in the profile, but outside it was found: {liftOutside}"

example {α : Type u} {β : Type v} (r : α → α → Prop) (f : α → β)
    (respect : ∀ a b, r a b → f a = f b) (a : α) :
    Quot.lift f respect (Quot.mk r a) = f a := rfl

example : ¬ (∀ a b : Bool, True → a = b) := by
  intro respect
  have contradiction := respect true false trivial
  cases contradiction

end Mettapedia.Languages.Lean.Declarations.QuotientProfileControls
