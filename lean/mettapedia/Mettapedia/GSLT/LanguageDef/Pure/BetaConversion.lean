/-
# Beta conversion for the Pure dependent fragment

This is an additive extension of the conversion-free Pure statics.  It keeps
the existing normal-form syntax and dependent-spine rules, but permits types
to be compared through beta conversion.  The executable decision path is
fuel-bounded and exposes exhaustion as data; exhaustion is never evidence of
conversion and is never conflated with a computed mismatch.
-/

import Mettapedia.GSLT.LanguageDef.Pure.Statics

namespace Mettapedia.GSLT.LanguageDef.PureBeta

open Mettapedia.GSLT.LanguageDef.Pure

/-- One beta contraction, closed under every Pure expression constructor. -/
inductive BetaStep : Expr → Expr → Prop where
  | beta {domain body argument} :
      BetaStep (.app (.lam domain body) argument) (Expr.subst0 argument body)
  | piDomain {domain domain' body} :
      BetaStep domain domain' →
      BetaStep (.pi domain body) (.pi domain' body)
  | piBody {domain body body'} :
      BetaStep body body' →
      BetaStep (.pi domain body) (.pi domain body')
  | lamDomain {domain domain' body} :
      BetaStep domain domain' →
      BetaStep (.lam domain body) (.lam domain' body)
  | lamBody {domain body body'} :
      BetaStep body body' →
      BetaStep (.lam domain body) (.lam domain body')
  | appFn {fn fn' argument} :
      BetaStep fn fn' →
      BetaStep (.app fn argument) (.app fn' argument)
  | appArgument {fn argument argument'} :
      BetaStep argument argument' →
      BetaStep (.app fn argument) (.app fn argument')

/-- Reflexive-transitive beta reduction, with simultaneous congruence rules. -/
inductive Reduces : Expr → Expr → Prop where
  | refl {expression} : Reduces expression expression
  | beta {domain body argument} :
      Reduces (.app (.lam domain body) argument) (Expr.subst0 argument body)
  | pi {domain domain' body body'} :
      Reduces domain domain' → Reduces body body' →
      Reduces (.pi domain body) (.pi domain' body')
  | lam {domain domain' body body'} :
      Reduces domain domain' → Reduces body body' →
      Reduces (.lam domain body) (.lam domain' body')
  | app {fn fn' argument argument'} :
      Reduces fn fn' → Reduces argument argument' →
      Reduces (.app fn argument) (.app fn' argument')
  | trans {first second third} :
      Reduces first second → Reduces second third → Reduces first third

/-- Definitional beta conversion is the equivalence closure of reduction. -/
inductive Conv : Expr → Expr → Prop where
  | refl {expression} : Conv expression expression
  | ofReduces {left right} : Reduces left right → Conv left right
  | symm {left right} : Conv left right → Conv right left
  | trans {first second third} :
      Conv first second → Conv second third → Conv first third

namespace BetaStep

/-- Every congruence-closed single beta step is a multi-step reduction. -/
theorem toReduces {first second : Expr} (hstep : BetaStep first second) :
    Reduces first second := by
  induction hstep with
  | beta => exact Reduces.beta
  | piDomain _ ih => exact Reduces.pi ih Reduces.refl
  | piBody _ ih => exact Reduces.pi Reduces.refl ih
  | lamDomain _ ih => exact Reduces.lam ih Reduces.refl
  | lamBody _ ih => exact Reduces.lam Reduces.refl ih
  | appFn _ ih => exact Reduces.app ih Reduces.refl
  | appArgument _ ih => exact Reduces.app Reduces.refl ih

end BetaStep

namespace Reduces

theorem toConv {first second : Expr} (hreduces : Reduces first second) :
    Conv first second := Conv.ofReduces hreduces

end Reduces

namespace Conv

theorem reduces_left {first second third : Expr}
    (hreduces : Reduces first second) (hconv : Conv second third) :
    Conv first third := Conv.trans hreduces.toConv hconv

theorem reduces_right {first second third : Expr}
    (hconv : Conv first second) (hreduces : Reduces second third) :
    Conv first third := Conv.trans hconv hreduces.toConv

end Conv

/-- A normalizer either returns a candidate normal form or reports fuel exhaustion. -/
inductive NormalizationResult where
  | normalized : Expr → NormalizationResult
  | conversionFuelExhausted : NormalizationResult
  deriving DecidableEq, Repr

mutual
/-- Fuel-bounded full beta normalization.  Zero fuel is an explicit verdict. -/
def normalize : Nat → Expr → NormalizationResult
  | 0, _ => .conversionFuelExhausted
  | _fuel + 1, .sort => .normalized .sort
  | _fuel + 1, .bvar index => .normalized (.bvar index)
  | fuel + 1, .pi domain body =>
      match normalize fuel domain, normalize fuel body with
      | .normalized domain', .normalized body' => .normalized (.pi domain' body')
      | _, _ => .conversionFuelExhausted
  | fuel + 1, .lam domain body =>
      match normalize fuel domain, normalize fuel body with
      | .normalized domain', .normalized body' => .normalized (.lam domain' body')
      | _, _ => .conversionFuelExhausted
  | fuel + 1, .app fn argument =>
      match normalize fuel fn, normalize fuel argument with
      | .normalized fn', .normalized argument' => normalizeApp fuel fn' argument'
      | _, _ => .conversionFuelExhausted

/-- Normalize an application after both children have been normalized. -/
def normalizeApp : Nat → Expr → Expr → NormalizationResult
  | 0, _, _ => .conversionFuelExhausted
  | fuel + 1, .lam _ body, argument => normalize fuel (Expr.subst0 argument body)
  | _fuel + 1, fn, argument => .normalized (.app fn argument)
end

/-- Fixed decision fuel recorded by the DTTBench authentication manifest. -/
def normalizationFuel : Nat := 512

/-- The three semantically distinct outcomes of the bounded conversion test. -/
inductive ConversionVerdict where
  | convertible
  | normalFormsDiffer
  | conversionFuelExhausted
  deriving DecidableEq, Repr

/-- Compare two expressions only after both bounded normalizations succeed. -/
def conversionVerdict (fuel : Nat) (left right : Expr) : ConversionVerdict :=
  match normalize fuel left, normalize fuel right with
  | .normalized left', .normalized right' =>
      if left' = right' then .convertible else .normalFormsDiffer
  | _, _ => .conversionFuelExhausted

mutual
/-- Successful normalization and normalized application both produce beta reducts. -/
theorem normalize_normalizeApp_sound : ∀ fuel,
    (∀ expression result,
      normalize fuel expression = .normalized result → Reduces expression result) ∧
    (∀ fn argument result,
      normalizeApp fuel fn argument = .normalized result →
        Reduces (.app fn argument) result) := by
  intro fuel
  induction fuel with
  | zero =>
      constructor
      · intro expression result h
        simp [normalize] at h
      · intro fn argument result h
        simp [normalizeApp] at h
  | succ fuel ih =>
      constructor
      · intro expression result hnormalize
        cases expression with
        | sort =>
            simp only [normalize, NormalizationResult.normalized.injEq] at hnormalize
            subst result
            exact Reduces.refl
        | bvar index =>
            simp only [normalize, NormalizationResult.normalized.injEq] at hnormalize
            subst result
            exact Reduces.refl
        | pi domain body =>
            simp only [normalize] at hnormalize
            cases hdomain : normalize fuel domain with
            | conversionFuelExhausted => simp [hdomain] at hnormalize
            | normalized domain' =>
                cases hbody : normalize fuel body with
                | conversionFuelExhausted => simp [hdomain, hbody] at hnormalize
                | normalized body' =>
                    simp [hdomain, hbody] at hnormalize
                    subst result
                    exact Reduces.pi (ih.1 _ _ hdomain) (ih.1 _ _ hbody)
        | lam domain body =>
            simp only [normalize] at hnormalize
            cases hdomain : normalize fuel domain with
            | conversionFuelExhausted => simp [hdomain] at hnormalize
            | normalized domain' =>
                cases hbody : normalize fuel body with
                | conversionFuelExhausted => simp [hdomain, hbody] at hnormalize
                | normalized body' =>
                    simp [hdomain, hbody] at hnormalize
                    subst result
                    exact Reduces.lam (ih.1 _ _ hdomain) (ih.1 _ _ hbody)
        | app fn argument =>
            simp only [normalize] at hnormalize
            cases hfn : normalize fuel fn with
            | conversionFuelExhausted => simp [hfn] at hnormalize
            | normalized fn' =>
                cases hargument : normalize fuel argument with
                | conversionFuelExhausted => simp [hfn, hargument] at hnormalize
                | normalized argument' =>
                    simp [hfn, hargument] at hnormalize
                    exact Reduces.trans
                      (Reduces.app (ih.1 _ _ hfn) (ih.1 _ _ hargument))
                      (ih.2 _ _ _ hnormalize)
      · intro fn argument result hnormalize
        cases fn with
        | lam domain body =>
            simp only [normalizeApp] at hnormalize
            exact Reduces.trans Reduces.beta (ih.1 _ _ hnormalize)
        | sort =>
            simp only [normalizeApp, NormalizationResult.normalized.injEq] at hnormalize
            subst result
            exact Reduces.refl
        | bvar index =>
            simp only [normalizeApp, NormalizationResult.normalized.injEq] at hnormalize
            subst result
            exact Reduces.refl
        | pi domain body =>
            simp only [normalizeApp, NormalizationResult.normalized.injEq] at hnormalize
            subst result
            exact Reduces.refl
        | app nestedFn nestedArgument =>
            simp only [normalizeApp, NormalizationResult.normalized.injEq] at hnormalize
            subst result
            exact Reduces.refl
end

theorem normalize_sound {fuel : Nat} {expression result : Expr}
    (hnormalize : normalize fuel expression = .normalized result) :
    Reduces expression result :=
  (normalize_normalizeApp_sound fuel).1 expression result hnormalize

theorem normalizeApp_sound {fuel : Nat} {fn argument result : Expr}
    (hnormalize : normalizeApp fuel fn argument = .normalized result) :
    Reduces (.app fn argument) result :=
  (normalize_normalizeApp_sound fuel).2 fn argument result hnormalize

/-- A positive bounded verdict is proof-producing evidence of beta conversion. -/
theorem conversionVerdict_sound {fuel : Nat} {left right : Expr}
    (hverdict : conversionVerdict fuel left right = .convertible) :
    Conv left right := by
  unfold conversionVerdict at hverdict
  cases hleft : normalize fuel left with
  | conversionFuelExhausted => simp [hleft] at hverdict
  | normalized left' =>
      cases hright : normalize fuel right with
      | conversionFuelExhausted => simp [hleft, hright] at hverdict
      | normalized right' =>
          by_cases heq : left' = right'
          · subst right'
            exact Conv.trans (normalize_sound hleft).toConv
              (Conv.symm (normalize_sound hright).toConv)
          · simp [hleft, hright, heq] at hverdict

/-- A result type is atomic after a proved beta reduction. -/
def BetaAtomic (type : Expr) : Prop :=
  ∃ reduced, Reduces type reduced ∧ reduced.Atomic

mutual
/-- Conversion-inclusive typing of Pure normal forms. -/
inductive HasType : Ctx → Nf → Expr → Prop where
  | lam {context domain body bodyType} :
      HasType (domain :: context) body bodyType →
      HasType context (.lam domain body) (.pi domain bodyType)
  | head {context index headType arguments resultType} :
      ctxLookup context index = some headType →
      SpineHasType context headType arguments resultType →
      BetaAtomic resultType →
      HasType context (.head index arguments) resultType
  | conv {context term actual expected} :
      HasType context term actual → Conv actual expected →
      HasType context term expected

/-- Ordered dependent application with beta conversion at each argument slot. -/
inductive SpineHasType : Ctx → Expr → List Nf → Expr → Prop where
  | nil {context headType} : SpineHasType context headType [] headType
  | cons {context domain body argument actualType rest resultType} :
      HasType context argument actualType →
      Conv actualType domain →
      SpineHasType context (Expr.subst0 argument.erase body) rest resultType →
      SpineHasType context (.pi domain body) (argument :: rest) resultType
end

mutual
/-- Every conversion-free term derivation embeds into the beta-conversion statics. -/
theorem oldHasType_embed : ∀ {context term type},
    Mettapedia.GSLT.LanguageDef.Pure.HasType context term type →
      HasType context term type
  | _, _, _, .lam hbody => .lam (oldHasType_embed hbody)
  | _, _, _, .head hlookup hspine hatomic =>
      .head hlookup (oldSpineHasType_embed hspine)
        ⟨_, Reduces.refl, hatomic⟩

/-- Every conversion-free spine derivation embeds without changing its result. -/
theorem oldSpineHasType_embed : ∀ {context headType arguments resultType},
    Mettapedia.GSLT.LanguageDef.Pure.SpineHasType
      context headType arguments resultType →
      SpineHasType context headType arguments resultType
  | _, _, _, _, .nil => .nil
  | _, _, _, _, .cons hargument hrest =>
      .cons (oldHasType_embed hargument) Conv.refl
        (oldSpineHasType_embed hrest)
end

/-- Closed inhabitants remain typed when their result type takes one beta step. -/
theorem closed_beta_subject_reduction {term : Nf} {type reduced : Expr}
    (htype : HasType [] term type) (hstep : BetaStep type reduced) :
    HasType [] term reduced :=
  HasType.conv htype (Conv.ofReduces hstep.toReduces)

/-- Closed inhabitants remain typed along any finite beta reduction of the result type. -/
theorem closed_beta_reduction_preserves_typing {term : Nf} {type reduced : Expr}
    (htype : HasType [] term type) (hreduces : Reduces type reduced) :
    HasType [] term reduced :=
  HasType.conv htype hreduces.toConv

/-! ## Positive and negative executable fixtures -/

def betaFixture : Expr := .app (.lam .sort (.bvar 0)) .sort

/-- A beta-shaped motive with the wrong bound-variable dependency. -/
def wrongMotiveBetaFixture : Expr :=
  .app (.lam .sort (.bvar 1)) .sort

/-- A shallow fuel bound is intentionally insufficient for this constructor depth. -/
def fuelExhaustionFixture : Expr := .pi .sort .sort

example : conversionVerdict 8 betaFixture .sort = .convertible := by decide

example : conversionVerdict 8 (.bvar 0) .sort = .normalFormsDiffer := by decide

example : conversionVerdict 8 wrongMotiveBetaFixture .sort = .normalFormsDiffer := by decide

example : conversionVerdict 1 fuelExhaustionFixture fuelExhaustionFixture =
    .conversionFuelExhausted := by decide

#print axioms BetaStep.toReduces
#print axioms conversionVerdict_sound
#print axioms oldHasType_embed
#print axioms closed_beta_subject_reduction

end Mettapedia.GSLT.LanguageDef.PureBeta
