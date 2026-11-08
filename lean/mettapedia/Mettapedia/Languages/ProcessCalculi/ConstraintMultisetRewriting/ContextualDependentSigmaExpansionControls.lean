import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSigmaExpansion
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentGeneralPatternDispatchControls

/-!
# A projection pattern solved after curried expansion

Under a rigid local `z : Σ (x : T). T`, the equation
`F (π₁ z) (π₂ z) ≐ Id T (π₂ z) (π₁ z)` is not a variable pattern. Curried
expansion of `z` and typed pair beta turn it into `F a b ≐ Id T b a`, with
exactly the same solutions at every outer substitution. The general pattern
replacement then gives the principal answer `F := λ a b. Id T b a` for the
original projection equation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentSigmaExpansion.Controls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentPiSpine ContextualDependentScope ContextualDependentSigma
open TypedContextual.QuotientComprehensionSyntax
open ContextualDependentParameterExchange ContextualDependentReductionReflection TypedEquality.StrongNormalization
open ContextualDependentGeneralPattern ContextualDependentGeneralPattern.Controls

abbrev source := extend types outerWhole

def pairDomain : TypeOver source := ⟨.var 1, .sort Tower.zero, .sort _, .var (1 : Fin 2)⟩
def pairCodomain : TypeOver (extend source pairDomain) := ⟨.var 2, .sort Tower.zero, .sort _, .var (2 : Fin 3)⟩
def pairWhole : TypeOver source :=
  ⟨.sigma (.var 1) (.var 2), .sort (.max Tower.zero Tower.zero), .sort _,
    .sigmaForm pairDomain.formed pairDomain.universeWitness pairCodomain.formed pairCodomain.universeWitness (.sorts _ _)⟩
def pairShape : Shape source := ⟨pairDomain, pairCodomain, pairWhole, rfl⟩

/-- `F (π₁ z) (π₂ z)`. -/
def projectedLeft : Term pairShape.packed (universeAt pairShape.packed) :=
  ⟨(.app (.app (.var 1) (.fst (.var 0))) (.snd (.var 0)) : Tower.Tm 3),
    .appElim (A := (.var 2 : Tower.Tm 3)) (B := (.head (.sort Tower.zero) : Tower.Tm 4))
      (.appElim (A := (.var 2 : Tower.Tm 3)) (B := (.pi (.var 3) (.head (.sort Tower.zero)) : Tower.Tm 4)) (.var (1 : Fin 3))
        (.fstElim (A := (.var 2 : Tower.Tm 3)) (B := (.var 3 : Tower.Tm 4)) (.var (0 : Fin 3))))
      (.sndElim (A := (.var 2 : Tower.Tm 3)) (B := (.var 3 : Tower.Tm 4)) (.var (0 : Fin 3)))⟩

/-- `Id T (π₂ z) (π₁ z)`. -/
def projectedRight : Term pairShape.packed (universeAt pairShape.packed) :=
  ⟨(.id (.var 2) (.snd (.var 0)) (.fst (.var 0)) : Tower.Tm 3),
    .idForm (.var (2 : Fin 3)) (.sort _) (.sndElim (A := (.var 2 : Tower.Tm 3)) (B := (.var 3 : Tower.Tm 4)) (.var (0 : Fin 3)))
      (.fstElim (A := (.var 2 : Tower.Tm 3)) (B := (.var 3 : Tower.Tm 4)) (.var (0 : Fin 3)))⟩

def projected : Active pairShape.packed := ⟨universeAt pairShape.packed, projectedLeft, projectedRight⟩

/-- The original equation under the rigid pair binder. -/
def original : Scoped source := .bind pairShape.whole (.active projected)

def expanded := reindexActive projected pairShape.pack

theorem expanded_left_code : expanded.left.code =
    (.app (.app (.var 2) (.fst (.pair (.var 1) (.var 0)))) (.snd (.pair (.var 1) (.var 0))) : Tower.Tm 4) := by rfl'

def compare (first second : TotalTerm pairShape.split) :=
  Conversion.compare (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentInversion.Controls.reducer 64 first second

def applicationHere : Term pairShape.split expanded.type := ⟨straight.application.code, straight.application.typed⟩
def swappedHere : Term pairShape.split expanded.type := ⟨swapped.code, swapped.typed⟩

theorem left_beta : Equal Tower.rules pairShape.split.raw expanded.left.code applicationHere.code expanded.type.code :=
  ((compare ⟨expanded.type, expanded.left⟩ ⟨expanded.type, applicationHere⟩).get (by decide +kernel)).down.2

theorem right_beta : Equal Tower.rules pairShape.split.raw expanded.right.code swappedHere.code expanded.type.code :=
  ((compare ⟨expanded.type, expanded.right⟩ ⟨expanded.type, swappedHere⟩).get (by decide +kernel)).down.2

/-- Exact solution correspondence with the variable pattern `F a b ≐ Id T b a`. -/
theorem original_holds_iff {Δ : Context Tower.rules} (solution : Δ ⟶ source) :
    original.Holds solution ↔ (straight.constraint swapped).Holds solution := by
  rw [original, split_holds_iff pairShape setting.levels projected solution, Pattern.constraint,
    Spine.toScoped_holds_iff]
  change expanded.Holds (rawLift (rawLift solution pairDomain) pairCodomain) ↔
    (⟨expanded.type, applicationHere, swappedHere⟩ : Active pairShape.split).Holds
      (rawLift (rawLift solution pairDomain) pairCodomain)
  exact (left_congr expanded applicationHere left_beta _).trans
    (right_congr ⟨expanded.type, applicationHere, expanded.right⟩ swappedHere right_beta _)

/-- The principal replacement, rephrased for the original projection equation. -/
def result : ContextualDependentScopedDispatch.Result setting.levels [original] :=
  ContextualDependentGeneralPattern.Controls.result.rephrase (by
    intro Δ solution
    constructor
    · intro held constraint member
      obtain rfl := List.mem_singleton.mp member
      exact (original_holds_iff solution).mp (held _ (List.mem_singleton_self _))
    · intro held constraint member
      obtain rfl := List.mem_singleton.mp member
      exact (original_holds_iff solution).mpr (held _ (List.mem_singleton_self _)))

theorem computed_answer :
    result.update.answer.substitution 0 = (.lam (.lam (.id (.var 2) (.var 0) (.var 1))) : Tower.Tm 1) := by rfl'

theorem principal :
    ContextualDependentScopedDispatch.Holds [original] result.update.answer ∧
      ∀ (Δ : Context Tower.rules) (solution : Δ ⟶ source),
        ContextualDependentScopedDispatch.Holds [original] solution →
          ∃ residual : Δ ⟶ result.update.target, ∀ term : TotalTerm source,
            (frames setting.levels).E (term.reindex solution) (term.reindex (residual ≫ result.update.answer)) :=
  result.completed ContextualDependentGeneralPattern.Controls.finished

end ContextualDependentSigmaExpansion.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
