import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.FormationSensitiveBeta
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationSignature

/-!
# Formation-sensitive preservation for transparent definitions

A closed body checked at its constant's declared type can replace that
constant at every displayed type reached by the original derivation. The
proof replays the original cumulative and conversion tail, retaining every
target-formation premise. It does not assume general subject reduction.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace FormationSensitive

variable {Head : Type} {R : Rules Head} {n : Nat}

private theorem replaceConstantAux {Γ : Ctx Head n} {term displayed : Tm Head n}
    (typing : Typing R Γ term displayed) :
    ∀ {name : DeclName} {body : Tm Head 0}, term = .const name →
      (∀ type, R.constantType name = some type → Typing R .nil body type) →
        Typing R Γ (liftClosed body) displayed := by
  induction typing with
  | const known _ _ _ =>
      intro name body equality checked
      cases equality
      exact (checked _ known).renameTyping (ρ := Fin.elim0)
        (fun i => Fin.elim0 i)
  | cumul _ order ih =>
      intro name body equality checked
      exact .cumul (ih equality checked) order
  | conv _ formed universeWitness conversion ih _ =>
      intro name body equality checked
      exact .conv (ih equality checked) formed universeWitness conversion
  | _ =>
      intro name body equality
      cases equality

/-- The displayed type can differ from the declared type through any number
of conversion and cumulativity rules. Those original rules are replayed. -/
theorem Typing.unfoldConstant {Γ : Ctx Head n} {name : DeclName}
    {body declared : Tm Head 0} {displayed : Tm Head n}
    (typing : Typing R Γ (.const name) displayed)
    (known : R.constantType name = some declared)
    (bodyTyped : Typing R .nil body declared) :
    Typing R Γ (liftClosed body) displayed := by
  apply replaceConstantAux typing rfl
  intro type lookup
  rw [known] at lookup
  cases lookup
  exact bodyTyped

/-- The actual signature's delta step and the complete refined judgment
are returned together, using its actual body lookup. -/
theorem Judgment.delta {base : Rules Head} {signature : Declaration.Signature Head}
    {Γ : Ctx Head n} {name : DeclName} {body declared : Tm Head 0}
    {displayed : Tm Head n}
    (judgment : Judgment (Declaration.extendRules base signature) Γ (.const name) displayed)
    (lookup : signature.valueOf? name = some body)
    (known : (Declaration.extendRules base signature).constantType name = some declared)
    (bodyTyped : Typing (Declaration.extendRules base signature) .nil body declared) :
    Step base.headEq (.const name : Tm Head n) (liftClosed body)
        (Declaration.rootComputation base signature) ∧
      Judgment (Declaration.extendRules base signature) Γ (liftClosed body) displayed :=
  ⟨.root (.delta lookup), ⟨judgment.context,
    judgment.typing.unfoldConstant known bodyTyped⟩⟩

#print axioms Typing.unfoldConstant
#print axioms Judgment.delta

end FormationSensitive
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
