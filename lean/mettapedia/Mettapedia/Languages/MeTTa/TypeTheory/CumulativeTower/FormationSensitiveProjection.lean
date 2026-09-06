import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.FormationSensitiveContextConversion
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.SigmaConversionBoundary

/-!
# Formation-sensitive dependent projection preservation

Generation recovers the pair's original dependent component types. Sigma
conversion qualification aligns them with the type seen by elimination.
The dependent second projection also accounts for conversion of the first
projection appearing in its result type.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace FormationSensitive

variable {Head : Type} {n : Nat} {R : Rules Head}

namespace Typing

private theorem pairGenerationAux {Γ : Ctx Head n} {term displayed : Tm Head n}
    (typing : Typing R Γ term displayed) :
    ∀ {first second : Tm Head n}, term = .pair first second →
      ∃ A B u, Typing R Γ (.sigma A B) (.head u) ∧ R.isUniverse u ∧
        Typing R Γ first A ∧ Typing R Γ second (inst0 first B) ∧
        TypeAdjustment R (.sigma A B) displayed := by
  induction typing with
  | pairIntro formed universeWitness firstTyped secondTyped _ _ _ =>
      intro first second equality
      cases equality
      exact ⟨_, _, _, formed, universeWitness, firstTyped, secondTyped, .refl _⟩
  | cumul _ order ih =>
      intro first second equality
      obtain ⟨A, B, u, formed, universeWitness, firstTyped, secondTyped, adjustment⟩ := ih equality
      exact ⟨A, B, u, formed, universeWitness, firstTyped, secondTyped,
        .trans adjustment (.cumulative order)⟩
  | conv _ _ _ conversion ih _ =>
      intro first second equality
      obtain ⟨A, B, u, formed, universeWitness, firstTyped, secondTyped, adjustment⟩ := ih equality
      exact ⟨A, B, u, formed, universeWitness, firstTyped, secondTyped,
        .trans adjustment (.conversion conversion)⟩
  | _ => intro first second equality; cases equality

theorem pairGeneration {Γ : Ctx Head n} {first second displayed : Tm Head n}
    (typing : Typing R Γ (.pair first second) displayed) :
    ∃ A B u, Typing R Γ (.sigma A B) (.head u) ∧ R.isUniverse u ∧
      Typing R Γ first A ∧ Typing R Γ second (inst0 first B) ∧
      TypeAdjustment R (.sigma A B) displayed :=
  pairGenerationAux typing rfl

/-- The first component keeps the type observed by the projection, even
when the pair's introduction used different convertible component types. -/
theorem betaSigmaFst {Γ : Ctx Head n} {first second A : Tm Head n}
    {B : Tm Head (n + 1)} (pairTyped : Typing R Γ (.pair first second) (.sigma A B))
    (universes : UniverseRegularity R) (boundary : SigmaConversionBoundary R)
    (context : ContextFormation R Γ) : Typing R Γ first A := by
  obtain ⟨oldA, oldB, u, formed, universeWitness, firstTyped, secondTyped, adjustment⟩ :=
    pairTyped.pairGeneration
  have components := boundary.components (adjustment.toConvOfSigmaTarget boundary)
  exact firstTyped.withResultOf (.fstElim pairTyped) universes context components.1

/-- The second component's displayed type mentions the first projection;
both component conversion and that projection's beta rule are accounted for. -/
theorem betaSigmaSnd {Γ : Ctx Head n} {first second A : Tm Head n}
    {B : Tm Head (n + 1)} (pairTyped : Typing R Γ (.pair first second) (.sigma A B))
    (universes : UniverseRegularity R) (boundary : SigmaConversionBoundary R)
    (context : ContextFormation R Γ) :
    Typing R Γ second (inst0 (.fst (.pair first second)) B) := by
  obtain ⟨oldA, oldB, u, formed, universeWitness, firstTyped, secondTyped, adjustment⟩ :=
    pairTyped.pairGeneration
  have components := boundary.components (adjustment.toConvOfSigmaTarget boundary)
  have firstProjection : Conv R.headEq first (.fst (.pair first second)) R.computation :=
    .symm _ _ (.rel _ _ (.betaSigmaFst first second))
  exact secondTyped.withResultOf (.sndElim pairTyped) universes context
    (.trans _ _ _ (components.2.substitute (subst0 first))
      (firstProjection.inst0Argument B))

#print axioms pairGeneration
#print axioms betaSigmaFst
#print axioms betaSigmaSnd

end Typing
end FormationSensitive
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
