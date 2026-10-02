import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.Soundness
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Domain.ChurchDefinitions

/-!
# Root steps of constants that carry their declared types

A declared constant read as a function projected onto its declared type computes, at a
spine with spine facts, to every contractum its function computes to that is an element
of the spine's type (`SpineFacts.church_root`).

In particular, a constant defined by one equation `f x₁ ⋯ x_k ⟶ E`, declared at
`pisCtx Θ T` and read as `defConst Θ T E`, denotes its right side at every spine with
spine facts whose contractum is an element of the spine's type
(`SpineFacts.defConst_root`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Annotated

open Impredicative.Domain
open Impredicative.Domain.Ideal (projT appSpine churchConst_root)

variable {Head : Type} {R : Rules Head} {Rd : Reading Head} {P : ChurchRules R}

/-- **A constant that carries its declared type computes** at a spine with spine facts
to every contractum its function computes to that is an element of the spine's type. -/
theorem SpineFacts.church_root {c : DeclName} {D : CTm Head 0}
    (declared : P.constantType c = some D) {f : Ideal}
    (value : Rd.const c = projT (cinterp Rd D Env.nil) f) {n : Nat} {args : List (CTm Head n)}
    (hlen : args.length ≤ piArity D) {τ : Ideal} {ρ : Env n} {r : Ideal}
    (facts : SpineFacts Rd P (CTm.appSpine (.const c) args) τ ρ)
    (body : appSpine f (args.map (cinterp Rd · ρ)) = r) (right : projT τ r = r) :
    cinterp Rd (CTm.appSpine (.const c) args) ρ = r := by
  obtain ⟨⟨inst, spine⟩, -⟩ := SpineFacts.constSpine declared facts
  rw [cinterp_appSpine]
  change appSpine (Rd.const c) _ = r
  rw [value]
  exact churchConst_root (churchTele_cinterp Rd D Env.nil) (by simpa using hlen) spine body
    (inst ▸ right)

/-- **A constant defined by one equation denotes its right side** at every spine with
spine facts whose contractum is an element of the spine's type. -/
theorem SpineFacts.defConst_root {f : DeclName} {k : Nat} {Θ : CCtx Head k} {T E : CTm Head k}
    (declared : P.constantType f = some (pisCtx Θ T)) (value : Rd.const f = defConst Rd Θ T E)
    {n : Nat} {args : List (CTm Head n)} (hlen : args.length = k) {τ : Ideal} {ρ : Env n}
    (facts : SpineFacts Rd P (CTm.appSpine (.const f) args) τ ρ)
    (right : projT τ (cinterp Rd E (Env.ofArgs k (args.map (cinterp Rd · ρ)))) =
      cinterp Rd E (Env.ofArgs k (args.map (cinterp Rd · ρ)))) :
    cinterp Rd (CTm.appSpine (.const f) args) ρ =
      cinterp Rd E (Env.ofArgs k (args.map (cinterp Rd · ρ))) := by
  obtain ⟨⟨inst, spine⟩, -⟩ := SpineFacts.constSpine declared facts
  have hlen' : (args.map (cinterp Rd · ρ)).length = k := by rw [List.length_map, hlen]
  rw [cinterp_appSpine]
  change appSpine (Rd.const f) _ = _
  rw [value, appSpine_defConst Rd Θ T E hlen' spine,
    ← instPi_pisCtx_of_spineTyped Rd Θ T hlen' spine, inst]
  exact right

end Annotated
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
