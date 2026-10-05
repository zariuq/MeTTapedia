import Mettapedia.Languages.ProcessCalculi.PolyadicPi.AuthoredClassified
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.NativeTypes

/-!
# Existing native predicates read through the authored classification

The existing operational GSLTs receive exact comparisons with the authored
active profile, equation quotient and cocontinuous classified interpretation.
No additional operational carrier or native-type construction is introduced.
The underlying relations are checked by independent syntax and occurrence
proofs in the imported adequacy modules.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.AuthoredNativeTypes

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.NativeTypes
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.AuthoredEquations
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.AuthoredOperationalProfile
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.AuthoredClassified

/-- A directed native step is exactly a tree of the independently authored
active rules at the supplied context and endpoints. -/
theorem raw_step_iff_authored {Γ : Ctx sig} (source target : Proc Γ) :
    (rawOperationalTheory Γ).rewrites source target ↔
      Nonempty (IntrinsicScopedLocalPolynomial.Tree rules (BindingCloneAlgebra.terms sig)
        ⟨Γ, Srt.pr, source, target⟩) :=
  step_iff_tree source target

theorem static_equations_iff_authored {Γ : Ctx sig} (source target : Proc Γ) :
    (operationalTheory Γ).equations.r source target ↔
      EqClosure presentation.eqs source target :=
  (eqClosure_iff_structuralEq source target).symm

/-- The native frame's edge relation is exactly the existing extended
classified reduction at the actual program sections. -/
theorem static_step_iff_classified {Γ : Ctx sig} (source target : Proc Γ) :
    (operationalTheory Γ).rewrites source target ↔
      IntrinsicScopedAuthoredClassifiedReduction.ExtendedReduction rules equations source target :=
  (extension_iff_stepModulo source target).symm

/-- Native possibility reads the genuinely classified authored operation,
rather than an unqualified one-hole contextual reduction. -/
theorem nativeDiamond_iff_classified {Γ : Ctx sig}
    (predicate : EquationPredicate (operationalTheory Γ)) (source : Proc Γ) :
    (semanticDiamond (operationalTheory Γ) predicate).1 source ↔
      ∃ target, IntrinsicScopedAuthoredClassifiedReduction.ExtendedReduction
        rules equations source target ∧ predicate.1 target := by
  rw [nativeDiamond_iff]
  exact exists_congr fun target => and_congr (extension_iff_stepModulo source target).symm Iff.rfl

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.AuthoredNativeTypes
