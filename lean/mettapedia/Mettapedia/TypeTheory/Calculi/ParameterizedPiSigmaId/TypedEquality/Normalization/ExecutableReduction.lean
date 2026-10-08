import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Algorithm

/-!
# Executable reduction with reconstructed paths

The root evaluator proposes a single declared computation and supplies its
root-rule derivation. `step` implements beta contraction, pair projections and
the contextual traversal itself. `normalize` consumes finite fuel and returns
the reconstructed reduction path. No typing or normalization evidence is an
execution input, and fuel exhaustion does not refute normalization.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization
namespace ExecutableReduction

variable {Head : Type}

abbrev RootEvaluator (R : Rules Head) :=
  {n : Nat} → (term : Tm Head n) → Option {target : Tm Head n // R.computation.step term target}

abbrev StepResult (R : Rules Head) {n : Nat} (term : Tm Head n) :=
  {target : Tm Head n // StepCore R.computation R.headEq term target}

abbrev Result (R : Rules Head) {n : Nat} (term : Tm Head n) :=
  {target : Tm Head n // Reduces R term target}

/-- A finite-budget reduction strategy. The strategy constructs its path;
callers supply terms and budget rather than normal forms or derivations. -/
abbrev Reducer (R : Rules Head) :=
  Nat → {n : Nat} → (term : Tm Head n) → Option (Result R term)

/-- Declared root computation takes precedence. If none applies, primitive
contractions and all children are visited in source order. -/
def step (R : Rules Head) (root : RootEvaluator R) :
    {n : Nat} → (term : Tm Head n) → Option (StepResult R term)
  | _, term => match root term with
    | some next => some ⟨next.val, .root next.property⟩
    | none => match term with
      | .var _ | .const _ | .head _ => none
      | .pi domain body =>
          match step R root domain with
          | some next => some ⟨.pi next.val body, .congPiDom next.property⟩
          | none => match step R root body with
            | some next => some ⟨.pi domain next.val, .congPiCod next.property⟩
            | none => none
      | .sigma domain body =>
          match step R root domain with
          | some next => some ⟨.sigma next.val body, .congSigmaDom next.property⟩
          | none => match step R root body with
            | some next => some ⟨.sigma domain next.val, .congSigmaCod next.property⟩
            | none => none
      | .id carrier left right =>
          match step R root carrier with
          | some next => some ⟨.id next.val left right, .congIdTy next.property⟩
          | none => match step R root left with
            | some next => some ⟨.id carrier next.val right, .congIdLeft next.property⟩
            | none => match step R root right with
              | some next => some ⟨.id carrier left next.val, .congIdRight next.property⟩
              | none => none
      | .lam body => match step R root body with
          | some next => some ⟨.lam next.val, .congLam next.property⟩
          | none => none
      | .app (.lam body) argument => some ⟨inst0 argument body, .betaPi body argument⟩
      | .app function argument =>
          match step R root function with
          | some next => some ⟨.app next.val argument, .congAppFun next.property⟩
          | none => match step R root argument with
            | some next => some ⟨.app function next.val, .congAppArg next.property⟩
            | none => none
      | .pair first second =>
          match step R root first with
          | some next => some ⟨.pair next.val second, .congPairFst next.property⟩
          | none => match step R root second with
            | some next => some ⟨.pair first next.val, .congPairSnd next.property⟩
            | none => none
      | .fst (.pair first second) => some ⟨first, .betaSigmaFst first second⟩
      | .fst pair => match step R root pair with
          | some next => some ⟨.fst next.val, .congFst next.property⟩
          | none => none
      | .snd (.pair first second) => some ⟨second, .betaSigmaSnd first second⟩
      | .snd pair => match step R root pair with
          | some next => some ⟨.snd next.val, .congSnd next.property⟩
          | none => none
      | .refl subject => match step R root subject with
          | some next => some ⟨.refl next.val, .congRefl next.property⟩
          | none => none


def normalize (R : Rules Head) (root : RootEvaluator R) :
    Nat → {n : Nat} → (term : Tm Head n) → Option (Result R term)
  | 0, _, _ => none
  | fuel+1, _, term =>
      match step R root term with
      | none => some ⟨term, .refl⟩
      | some next => match normalize R root fuel next.val with
        | none => none
        | some result => some ⟨result.val, .head next.property result.property⟩

def normalizeTerm (R : Rules Head) (root : RootEvaluator R) (fuel : Nat)
    {n : Nat} (term : Tm Head n) : Option (Tm Head n) :=
  (normalize R root fuel term).map Subtype.val

theorem normalizeTerm_sound (R : Rules Head) (root : RootEvaluator R) {fuel n : Nat}
    {term target : Tm Head n}
    (accepted : normalizeTerm R root fuel term = some target) : Reduces R term target := by
  unfold normalizeTerm at accepted
  cases computed : normalize R root fuel term with
  | none => simp only [computed, Option.map_none] at accepted; cases accepted
  | some result =>
      simp only [computed, Option.map_some, Option.some.injEq] at accepted
      exact accepted ▸ result.property

theorem exhausted (R : Rules Head) (root : RootEvaluator R) {n : Nat} (term : Tm Head n) :
    normalize R root 0 term = none := rfl

end ExecutableReduction
end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
