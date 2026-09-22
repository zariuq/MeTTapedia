import Mettapedia.Logic.HOL.Embedding.ZFSetTraceProducts
import Mettapedia.Logic.HOL.Embedding.ZFSetContextualInterpretation

/-!
# Trace-coded products in the existing set-coded contextual model

Contexts, families, sections, comprehension and sums are unchanged. The
alternative product representation uses actual Aczel traces. It supports
arbitrary dependent set families, beta--eta and strict substitution laws.
Typed graph/trace comparison preserves application and abstraction; no
untyped recovery of a function's domain is asserted.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.Embedding.ZFSetTraceContextual

open ZFSetDependentProducts ZFSetTraceProducts
open ZFSetContextualInterpretation (SetFamily Section Extension totalFamily totalFamily_at
  codedCwf extensionSubstitution)
open Mettapedia.TypeTheory.ContextualProductComparison

universe u

noncomputable def piFamily {Γ : Type (u + 1)} (a : SetFamily Γ)
    (b : SetFamily (Extension a)) : SetFamily Γ :=
  fun γ => tracePiSet (a γ) (totalFamily (a γ) (fun x => b ⟨γ, x⟩))

noncomputable def piDecode {Γ : Type (u + 1)} (a : SetFamily Γ)
    (b : SetFamily (Extension a)) (γ : Γ) :
    Elements (piFamily a b γ) ≃ ((x : Elements (a γ)) → Elements (b ⟨γ, x⟩)) :=
  (tracePiEquiv (a γ) (totalFamily (a γ) (fun x => b ⟨γ, x⟩))).trans
    (Equiv.piCongrRight (fun x => Equiv.cast
      (congrArg Elements (totalFamily_at (a γ) (fun y => b ⟨γ, y⟩) x))))

private theorem cast_elements_value {a b : ZFSet.{u}} (equal : a = b)
    (value : Elements a) :
    ((Equiv.cast (congrArg Elements equal)) value).1 = value.1 := by
  subst b
  rfl

theorem piDecode_value {Γ : Type (u + 1)} (a : SetFamily Γ)
    (b : SetFamily (Extension a)) (γ : Γ)
    (function : Elements (piFamily a b γ)) (argument : Elements (a γ)) :
    (piDecode a b γ function argument).1 = traceApp function.1 argument.1 :=
  cast_elements_value (totalFamily_at (a γ) (fun x => b ⟨γ, x⟩) argument) _

noncomputable def lam {Γ : Type (u + 1)} {a : SetFamily Γ}
    {b : SetFamily (Extension a)} (body : Section b) : Section (piFamily a b) :=
  fun γ => (piDecode a b γ).symm (fun x => body ⟨γ, x⟩)

noncomputable def app {Γ : Type (u + 1)} {a : SetFamily Γ}
    {b : SetFamily (Extension a)} (f : Section (piFamily a b)) (argument : Section a) :
    Section (fun γ => b ⟨γ, argument γ⟩) :=
  fun γ => piDecode a b γ (f γ) (argument γ)

theorem app_lam {Γ : Type (u + 1)} {a : SetFamily Γ}
    {b : SetFamily (Extension a)} (body : Section b) (argument : Section a) :
    app (lam body) argument = fun γ => body ⟨γ, argument γ⟩ := by
  funext γ
  exact congrFun ((piDecode a b γ).apply_symm_apply (fun x => body ⟨γ, x⟩)) (argument γ)

theorem lam_eta {Γ : Type (u + 1)} {a : SetFamily Γ}
    {b : SetFamily (Extension a)} (f : Section (piFamily a b)) :
    lam (fun pair => piDecode a b pair.1 (f pair.1) pair.2) = f := by
  funext γ
  exact (piDecode a b γ).symm_apply_apply (f γ)

noncomputable def products : DependentProductBeta codedCwf.{u} where
  pi := piFamily
  lam := lam
  app := app
  beta := app_lam

theorem piFamily_substitution {Γ Δ : Type (u + 1)} (θ : Δ → Γ)
    (a : SetFamily Γ) (b : SetFamily (Extension a)) :
    piFamily a b ∘ θ = piFamily (a ∘ θ) (b ∘ extensionSubstitution θ a) := rfl

theorem lam_substitution {Γ Δ : Type (u + 1)} (θ : Δ → Γ)
    {a : SetFamily Γ} {b : SetFamily (Extension a)} (body : Section b) :
    (fun δ => lam body (θ δ)) =
      lam (fun pair => body (extensionSubstitution θ a pair)) := rfl

theorem app_substitution {Γ Δ : Type (u + 1)} (θ : Δ → Γ)
    {a : SetFamily Γ} {b : SetFamily (Extension a)}
    (f : Section (piFamily a b)) (argument : Section a) :
    (fun δ => app f argument (θ δ)) =
      app (b := b ∘ extensionSubstitution θ a)
        (fun δ => f (θ δ)) (fun δ => argument (θ δ)) := rfl

/-! ## Comparison uses the same actual contextual fibres -/

noncomputable def fromGraph {Γ : Type (u + 1)} {a : SetFamily Γ}
    {b : SetFamily (Extension a)}
    (f : Section (ZFSetContextualInterpretation.piFamily a b)) : Section (piFamily a b) :=
  fun γ => graphToTrace (f γ)

noncomputable def toGraph {Γ : Type (u + 1)} {a : SetFamily Γ}
    {b : SetFamily (Extension a)}
    (f : Section (piFamily a b)) : Section (ZFSetContextualInterpretation.piFamily a b) :=
  fun γ => traceToGraph (f γ)

theorem to_fromGraph {Γ : Type (u + 1)} {a : SetFamily Γ}
    {b : SetFamily (Extension a)}
    (f : Section (ZFSetContextualInterpretation.piFamily a b)) :
    toGraph (fromGraph f) = f := funext (fun γ => traceToGraph_graphToTrace (f γ))

theorem from_toGraph {Γ : Type (u + 1)} {a : SetFamily Γ}
    {b : SetFamily (Extension a)} (f : Section (piFamily a b)) :
    fromGraph (toGraph f) = f := funext (fun γ => graphToTrace_traceToGraph (f γ))

theorem decode_fromGraph {Γ : Type (u + 1)} (a : SetFamily Γ)
    (b : SetFamily (Extension a)) (γ : Γ)
    (f : Elements (ZFSetContextualInterpretation.piFamily a b γ)) :
    piDecode a b γ (graphToTrace f) = ZFSetContextualInterpretation.piDecode a b γ f := by
  exact congrArg (Equiv.piCongrRight (fun x => Equiv.cast
    (congrArg Elements (totalFamily_at (a γ) (fun y => b ⟨γ, y⟩) x))))
    (traceValue_graphToTrace f)

theorem application_agreement {Γ : Type (u + 1)} {a : SetFamily Γ}
    {b : SetFamily (Extension a)}
    (f : Section (ZFSetContextualInterpretation.piFamily a b)) (argument : Section a) :
    app (fromGraph f) argument = ZFSetContextualInterpretation.app f argument :=
  funext (fun γ => congrFun (decode_fromGraph a b γ (f γ)) (argument γ))

theorem lambda_agreement {Γ : Type (u + 1)} {a : SetFamily Γ}
    {b : SetFamily (Extension a)} (body : Section b) :
    fromGraph (ZFSetContextualInterpretation.lam body) = lam body := by
  funext γ
  apply (piDecode a b γ).injective
  unfold fromGraph
  rw [decode_fromGraph]
  exact (ZFSetContextualInterpretation.piDecode a b γ).apply_symm_apply _ |>.trans
    ((piDecode a b γ).apply_symm_apply _).symm

theorem fromGraph_substitution {Γ Δ : Type (u + 1)} (θ : Δ → Γ)
    {a : SetFamily Γ} {b : SetFamily (Extension a)}
    (f : Section (ZFSetContextualInterpretation.piFamily a b)) :
    (fun δ => fromGraph f (θ δ)) =
      fromGraph (b := b ∘ extensionSubstitution θ a) (fun δ => f (θ δ)) := rfl

namespace Controls

open ZFSetContextualInterpretation.Controls (domain codomain body zeroArgument oneArgument)

theorem dependent_zero : (app (lam body.{u}) zeroArgument PUnit.unit).1 = ∅ := by
  rw [app_lam]
  rfl

theorem dependent_one :
    (app (lam body.{u}) oneArgument PUnit.unit).1 = ZFSet.powerset ∅ := by
  rw [app_lam]
  rfl

theorem wrong_constant_result : (app (lam body.{u}) oneArgument PUnit.unit).1 ≠ ∅ := by
  rw [← lambda_agreement, application_agreement]
  exact ZFSetContextualInterpretation.Controls.wrong_constant_result

end Controls

#print axioms products
#print axioms piDecode_value
#print axioms app_lam
#print axioms lam_eta
#print axioms piFamily_substitution
#print axioms lam_substitution
#print axioms app_substitution
#print axioms application_agreement
#print axioms lambda_agreement
#print axioms fromGraph_substitution
#print axioms Controls.wrong_constant_result

end Mettapedia.Logic.HOL.Embedding.ZFSetTraceContextual
