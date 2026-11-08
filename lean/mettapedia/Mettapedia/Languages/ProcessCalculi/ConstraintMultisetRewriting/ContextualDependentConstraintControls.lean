import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentElimination
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.CumulativeConversion

/-!
# Dependent pair obligations that suspend and wake

In the cumulative tower, `(X, refl X)` inhabits `Sigma A : U0, Id U0 A A`.
Its second projection and `refl Ground` have different types before the type
variable X is assigned. The actual bounded scanner retains their equation,
then definition elimination sets X to Ground and the same scanner discharges
it using checked beta conversion.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentConstraints.Controls

open CategoryTheory Interface Interface.Dependent
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open FormationSensitiveContextual

instance : DecidableRel Tower.rules.headEq := fun left right =>
  LevelTower.instDecidableHeadEq left right

def universeType : TypeOver (empty Tower.rules) :=
  ⟨.head (.sort Tower.zero), .sort (.succ Tower.zero), .sort _, .headType (.sort _)⟩

def ground : Term (empty Tower.rules) universeType :=
  ⟨.head .legacyGround, .headType .legacyGround⟩

abbrev frame := extend (empty Tower.rules) universeType

def family {n : Nat} : Tower.Tm (n + 1) :=
  .id (.head (.sort Tower.zero)) (.var 0) (.var 0)

def pairType {n : Nat} : Tower.Tm n := .sigma (.head (.sort Tower.zero)) family

theorem pairType_formed {n : Nat} (Γ : Tower.Ctx n) :
    FormationSensitive.Typing Tower.rules Γ pairType
      (.head (.sort (.max (.succ Tower.zero) (.succ Tower.zero)))) :=
  .sigmaForm (.headType (.sort _)) (.sort _)
    (.idForm (.headType (.sort _)) (.sort _) (.var 0) (.var 0)) (.sort _) (.sorts _ _)

def pairAt {Γ : Context Tower.rules} (value : Term Γ
    (universeType.reindex (toEmpty Γ))) :
    Term Γ ⟨pairType, .sort (.max (.succ Tower.zero) (.succ Tower.zero)),
      .sort _, pairType_formed Γ.raw⟩ :=
  ⟨.pair value.code (.refl value.code),
    .pairIntro (pairType_formed Γ.raw) (.sort _) value.typed (.reflIntro value.typed)⟩

def secondAt {Γ : Context Tower.rules} (value : Term Γ
    (universeType.reindex (toEmpty Γ))) : Entry Γ :=
  let pair := pairAt value
  let first : FormationSensitive.Typing Tower.rules Γ.raw (.fst pair.code)
      (.head (.sort Tower.zero)) := .fstElim pair.typed
  ⟨⟨.id (.head (.sort Tower.zero)) (.fst pair.code) (.fst pair.code),
      .sort (.succ Tower.zero), .sort _,
      .idForm (.headType (.sort _)) (.sort _) first first⟩,
    ⟨.snd pair.code, .sndElim pair.typed⟩⟩

def typeVariable : Term frame (universeType.reindex (toEmpty frame)) := ⟨.var 0, .var 0⟩
def fixed : Term frame (universeType.reindex (toEmpty frame)) :=
  ⟨.head .legacyGround, .headType .legacyGround⟩

def reflexivityAt {Γ : Context Tower.rules} (value : Term Γ
    (universeType.reindex (toEmpty Γ))) : Entry Γ :=
  ⟨⟨.id (.head (.sort Tower.zero)) value.code value.code,
      .sort (.succ Tower.zero), .sort _,
      .idForm (.headType (.sort _)) (.sort _) value.typed value.typed⟩,
    ⟨.refl value.code, .reflIntro value.typed⟩⟩

def equation : Equation (Entry frame) := (secondAt typeVariable, reflexivityAt fixed)

def decoder : StructuralConversionCode.RootDecoder Tower.rules.computation :=
  .ofEmpty _ rfl

def noRoot {n : Nat} (_ : Tower.Tm n) : Option (decoder.Code n) := none

def suspended : Worklist frame := scan decoder noRoot 4 [equation]

/-- The type mismatch prevents premature homogeneous processing. -/
theorem starts_pending : suspended.active = [] ∧ suspended.pending = [equation] := by
  constructor <;> rfl

/-- These are different dependent types, not different spellings of an
already identical type. -/
theorem endpoint_types_differ : equation.1.type.code ≠ equation.2.type.code := by
  intro same
  cases same

def resumed : Worklist (empty Tower.rules) :=
  eliminateDefinition decoder noRoot 4 ground suspended

/-- A real typed substitution and checked computation discharge the
previously suspended second-projection equation. -/
theorem resumes_and_finishes : resumed.active = [] ∧ resumed.pending = [] := by
  constructor <;> decide

theorem original_has_a_solution :
    (frames Tower.rules).Solvable (definition (empty Tower.rules) ground :: suspended.store) := by
  refine ⟨empty Tower.rules, instantiate (empty Tower.rules) ground, ?_⟩
  apply (eliminateDefinition_models_iff decoder noRoot 4 ground suspended _).mpr
  refine ⟨𝟙 _, ?_, ?_⟩
  · have result : resumed.store = [] := by
      simp only [Worklist.store, resumes_and_finishes.1, resumes_and_finishes.2,
        List.map_nil, List.nil_append]
    change (frames Tower.rules).Models (𝟙 _) resumed.store
    rw [result]
    exact Frames.models_nil _
  · intro term
    rw [Category.id_comp]
    exact Entry.Convertible.refl _

/-- A zero budget keeps reducible dependent endpoints as obligations. It
does not silently turn resource exhaustion into rejection or success. -/
theorem insufficient_budget_keeps_obligation :
    (eliminateDefinition decoder noRoot 0 ground suspended).store ≠ [] := by
  decide

/-- This example's answer is principal for the entire problem, including
the equation whose types initially prevented processing. -/
theorem resumed_answer_is_principal :
    (frames Tower.rules).Principal (definition (empty Tower.rules) ground :: suspended.store)
      (instantiate (empty Tower.rules) ground) := by
  have finished : (scan decoder noRoot 4
      ((frames Tower.rules).applyStore (instantiate (empty Tower.rules) ground)
        suspended.store)).store = [] := by
    rw [← suspended.reindex_store]
    change resumed.store = []
    simp only [Worklist.store, resumes_and_finishes.1, resumes_and_finishes.2,
      List.map_nil, List.nil_append]
  have principal := principal_definition_residual ground suspended.store
    (scan_empty_principal decoder noRoot 4 _ finished)
  simpa only [Category.id_comp] using principal

def arrow {n : Nat} : Tower.Tm n := .pi (.head .legacyGround) (.head .legacyGround)

theorem arrow_formed {n : Nat} (Γ : Tower.Ctx n) :
    FormationSensitive.Typing Tower.rules Γ arrow (.head (.sort (.max Tower.zero Tower.zero))) :=
  .piForm (.headType .legacyGround) (.sort _) (.headType .legacyGround) (.sort _) (.sorts _ _)

def arrowType : TypeOver (empty Tower.rules) :=
  ⟨arrow, .sort (.max Tower.zero Tower.zero), .sort _, arrow_formed _⟩

def higherArrowType : TypeOver (empty Tower.rules) :=
  ⟨.pi arrow arrow, .sort (.max (.max Tower.zero Tower.zero) (.max Tower.zero Tower.zero)),
    .sort _, .piForm (arrow_formed _) (.sort _) (arrow_formed _) (.sort _) (.sorts _ _)⟩

def lowIdentity : Entry (empty Tower.rules) :=
  ⟨arrowType, ⟨.lam (.var 0), .lamIntro arrowType.formed (.sort _) (.var 0)⟩⟩

def highIdentity : Entry (empty Tower.rules) :=
  ⟨higherArrowType, ⟨.lam (.var 0), .lamIntro higherArrowType.formed (.sort _) (.var 0)⟩⟩

/-- Erasing the endpoint types would accept identical term syntax, but the
actual typed problem has no solution in any future frame. -/
theorem same_terms_incompatible_types :
    lowIdentity.term.code = highIdentity.term.code ∧
      ¬ (frames Tower.rules).Solvable [(lowIdentity, highIdentity)] := by
  refine ⟨rfl, fun solved => ?_⟩
  have converted := (solvable_empty_iff _).mp solved _ (List.mem_singleton_self _)
  have domains := (LevelTower.piConversionBoundary.components converted.1).1
  exact LevelTower.piConversionBoundary.headDisjoint (.symm _ _ domains)

theorem incompatible_types_are_retained :
    (scan decoder noRoot 4 [(lowIdentity, highIdentity)]).pending =
      [(lowIdentity, highIdentity)] := rfl

end ContextualDependentConstraints.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
