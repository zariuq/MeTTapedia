import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingLambda
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.AuthoredCommunication
import Mettapedia.OSLF.Framework.GSLTTypeSynthesis

/-!
# Native predicates of the supported name-passing interpretation

The unary/binary communication interpretation, with parallel and restriction
descent and its explicit structural equations, supplies a GSLT. The shared
OSLF construction generates its native predicate frame. The compiler's
checked head-step comparison transports existential execution observations
and actual finite paths into this frame.

The source GSLT here is exactly the supported head-reduction fragment. It
does not add environment propagation or reduction beneath lambda guards.
AuthoredNativeTypes independently identifies the target equations and
operations with the intrinsically scoped authored classified presentation.
The legacy LanguageDef engine and the full classifying theories of NTT
Proposition 32 are distinct comparisons. NamePassingSpine supplies two-sided
returned-function reachability for the environment fragment; unrestricted
logical preservation needs its own observer obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.NativeTypes

open Mettapedia.OSLF.Binding
open Mettapedia.GSLT
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.Languages.LambdaCalculus
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingLambda

/-- The directed active reduction profile before structural rearrangement.
Its equations are literal term equality; the static-quotient interpretation
is `operationalTheory`. In particular, this profile does not silently allow
reduction under input guards. -/
def rawOperationalTheory (Γ : Ctx sig) : GSLT where
  Term := Proc Γ
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := Step
  rewrites_resp_left := by
    rintro source source' target rfl step
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    rintro source target target' step rfl
    exact step

/-- The explicit operational interpretation of the authored unary/binary
communication schemas, taken modulo its stated structural equations. -/
def operationalTheory (Γ : Ctx sig) : GSLT where
  Term := Proc Γ
  equations :=
    ⟨StructuralEq, ⟨StructuralEq.refl, StructuralEq.symm, StructuralEq.trans⟩⟩
  rewrites := StepModulo
  rewrites_resp_left := by
    intro source source' target equal step
    obtain ⟨redex, contractum, before, firing, after⟩ := step
    exact ⟨target, ⟨redex, contractum, .trans (.symm equal) before, firing, after⟩,
      .refl target⟩
  rewrites_resp_right := by
    intro source target target' step equal
    obtain ⟨redex, contractum, before, firing, after⟩ := step
    exact ⟨redex, contractum, before, firing, .trans after equal⟩

/-- The source instance uses the established head-step relation and no extra
static identifications. It is an explicitly delimited operational fragment. -/
def headTheory (Γ : Ctx sig) : GSLT where
  Term := NamePassing.Expr Srt.nm Γ
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := NamePassing.HeadStep
  rewrites_resp_left := by
    intro source source' target equal step
    cases equal
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    cases equal
    exact step

/-- Observation of one structural class, independent of its representative. -/
def classPredicate {Γ : Ctx sig} (representative : Proc Γ) :
    EquationPredicate (operationalTheory Γ) :=
  ⟨fun process => StructuralEq process representative,
    by
      intro first second equal
      exact ⟨fun related => .trans (.symm equal) related,
        fun related => .trans equal related⟩⟩

/-- A target native observation, read along the actual supplied compiler. -/
def compiledPredicate {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ)
    (result : Var Δ .nm) (predicate : EquationPredicate (operationalTheory Δ)) :
    EquationPredicate (headTheory Γ) :=
  ⟨fun term => predicate.1 (compile term environment result),
    by intro first second equal; change first = second at equal; cases equal; rfl⟩

/-- The generated target diamond observes the supported actual execution
blocks, with no existential replacement of the supplied final process. -/
theorem nativeDiamond_iff {Γ : Ctx sig}
    (predicate : EquationPredicate (operationalTheory Γ)) (process : Proc Γ) :
    (semanticDiamond (operationalTheory Γ) predicate).1 process ↔
      ∃ target, StepModulo process target ∧ predicate.1 target :=
  gsltDiamond_spec (operationalTheory Γ) predicate.1 process

/-- Replaying a source head step carries an endpoint's native certificate
into the generated target diamond. -/
theorem headStep_nativeDiamond {Γ Δ : Ctx sig} {source target : Expr Γ}
    (step : NamePassing.HeadStep source target) (environment : Ren sig Γ Δ)
    (result : Var Δ .nm) (predicate : EquationPredicate (operationalTheory Δ))
    (holds : predicate.1 (compile target environment result)) :
    (semanticDiamond (operationalTheory Δ) predicate).1
      (compile source environment result) :=
  (nativeDiamond_iff predicate _).mpr
    ⟨compile target environment result, headStep_preserved step environment result, holds⟩

/-- Existential source execution observations transport forward through the
compiler. This does not assert that every target observation lifts back. -/
theorem compiledDiamond_le {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ)
    (result : Var Δ .nm) (predicate : EquationPredicate (operationalTheory Δ)) :
    (semanticDiamond (headTheory Γ) (compiledPredicate environment result predicate)).1 ≤
      fun source => (semanticDiamond (operationalTheory Δ) predicate).1
        (compile source environment result) := by
  intro source possible
  obtain ⟨target, step, holds⟩ :=
    (gsltDiamond_spec (headTheory Γ) _ source).mp possible
  exact headStep_nativeDiamond step environment result predicate holds

/-- Compile a retained source path into a retained target path, with every
translated intermediate state and the actual translated endpoint. -/
def compilePath {Γ Δ : Ctx sig} {source target : (headTheory Γ).Term}
    (environment : Ren sig Γ Δ) (result : Var Δ .nm)
    (path : (headTheory Γ).RewritePath source target) :
    (operationalTheory Δ).RewritePath (compile source environment result)
      (compile target environment result) :=
  match path with
  | .nil _ => .nil _
  | .cons step rest =>
      .cons (headStep_preserved step environment result) (compilePath environment result rest)

/-- This block-level path keeps one supported communication per source
firing; structural endpoint rearrangements are not counted as firings. -/
theorem compilePath_length {Γ Δ : Ctx sig} {source target : (headTheory Γ).Term}
    (environment : Ren sig Γ Δ) (result : Var Δ .nm)
    (path : (headTheory Γ).RewritePath source target) :
    (compilePath environment result path).length = path.length := by
  induction path with
  | nil => rfl
  | cons step rest ih =>
      simp only [compilePath, GSLT.RewritePath.length, ih]

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.NativeTypes
