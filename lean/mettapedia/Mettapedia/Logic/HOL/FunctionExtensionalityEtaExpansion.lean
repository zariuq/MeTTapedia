import Mettapedia.Logic.HOL.ContextualTrinity

/-!
# Expanding the function-extensionality rule through eta

Universal elimination at a fresh variable and lambda congruence give equality
of the eta expansions. Two eta equations then give equality of the original
functions. The construction retains the exact context, ordered hypotheses
and conclusion. It uses eta explicitly, so it does not satisfy the existing
FunctionExtensionalityFree observation, which excludes both eta and funExt.

The recursive expansion replaces every direct funExt node by that recipe.
Its rule-use observation reports primitive funExt occurrences, not semantic
intensionality, proof identity, axiom-policy independence or execution cost.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.ProofSyntax
universe u v
variable {Base : Type u} {Const : Ty Base → Type v}
  {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ}

/-- Number of direct applications of the primitive funExt constructor. -/
def primitiveFunExtUses {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
    {φ : Formula Const Γ} : ProofSyntax Const Δ φ → Nat
  | .hyp _ | .topI | .eqRefl _ | .beta _ _ | .eta _ => 0
  | .funExt proof => primitiveFunExtUses proof + 1
  | .botE proof | .andEL proof | .andER proof | .orIL proof | .orIR proof
  | .impI proof | .notI proof | .allI proof | .allE _ proof | .exI _ proof
  | .eqSymm proof | .eqPropEL proof | .eqPropER proof | .eqApp _ proof
  | .eqAppArg _ proof | .eqLam proof => primitiveFunExtUses proof
  | .andI first second | .impE first second | .notE first second
  | .exE first second | .eqTrans first second | .eqPropI first second =>
      primitiveFunExtUses first + primitiveFunExtUses second
  | .orE cases first second =>
      primitiveFunExtUses cases + primitiveFunExtUses first + primitiveFunExtUses second

@[simp] theorem primitiveFunExtUses_cast {ψ : Formula Const Γ} (same : φ = ψ)
    (proof : ProofSyntax Const Δ φ) : primitiveFunExtUses (same ▸ proof) = primitiveFunExtUses proof := by
  cases same
  rfl

@[simp] theorem primitiveFunExtUses_castIndices {target : List (Formula Const Γ)} {ψ : Formula Const Γ}
    (assumptions : Δ = target) (conclusion : φ = ψ) (proof : ProofSyntax Const Δ φ) :
    primitiveFunExtUses (proof.castIndices assumptions conclusion) = primitiveFunExtUses proof := by
  cases assumptions
  cases conclusion
  rfl

@[simp] theorem primitiveFunExtUses_rename {Ξ : Ctx Base} (rho : Rename Base Γ Ξ)
    (proof : ProofSyntax Const Δ φ) : primitiveFunExtUses (proof.rename rho) = primitiveFunExtUses proof := by
  induction proof generalizing Ξ with
  | _ => simp_all only [rename, primitiveFunExtUses_castIndices, primitiveFunExtUses]

def funExtViaEta {domain codomain : Ty Base} {first second : Term Const Γ (domain ⇒ codomain)}
    (pointwise : ProofSyntax Const Δ
      (.all (.eq (.app (weaken first) (.var .vz)) (.app (weaken second) (.var .vz))))) :
    ProofSyntax Const Δ (.eq first second) :=
  .eqTrans (.eqSymm (.eta first))
    (.eqTrans (.eqLam (ContextualTrinity.instantiateFresh (pointwise.rename Rename.weaken))) (.eta second))

theorem funExtViaEta_not_free {domain codomain : Ty Base} {first second : Term Const Γ (domain ⇒ codomain)}
    (pointwise : ProofSyntax Const Δ
      (.all (.eq (.app (weaken first) (.var .vz)) (.app (weaken second) (.var .vz))))) :
    ¬ (funExtViaEta pointwise).FunctionExtensionalityFree := by
  simp only [funExtViaEta,FunctionExtensionalityFree,false_and,not_false_eq_true]

@[simp] theorem primitiveFunExtUses_funExtViaEta {domain codomain : Ty Base}
    {first second : Term Const Γ (domain ⇒ codomain)}
    (pointwise : ProofSyntax Const Δ
      (.all (.eq (.app (weaken first) (.var .vz)) (.app (weaken second) (.var .vz))))) :
    primitiveFunExtUses (funExtViaEta pointwise) = primitiveFunExtUses pointwise := by
  simp [funExtViaEta,primitiveFunExtUses,ContextualTrinity.instantiateFresh,ContextualTrinity.castConclusion]

/-- Replace every direct funExt node by its eta-using derivation. All proof
indices and other rule arguments remain the original ones. -/
def expandFunExt {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ} :
    ProofSyntax Const Δ φ → ProofSyntax Const Δ φ
  | .hyp occurrence => .hyp occurrence
  | .topI => .topI
  | .botE proof => .botE (expandFunExt proof)
  | .andI first second => .andI (expandFunExt first) (expandFunExt second)
  | .andEL proof => .andEL (expandFunExt proof)
  | .andER proof => .andER (expandFunExt proof)
  | .orIL proof => .orIL (expandFunExt proof)
  | .orIR proof => .orIR (expandFunExt proof)
  | .orE cases first second => .orE (expandFunExt cases) (expandFunExt first) (expandFunExt second)
  | .impI proof => .impI (expandFunExt proof)
  | .impE first second => .impE (expandFunExt first) (expandFunExt second)
  | .notI proof => .notI (expandFunExt proof)
  | .notE first second => .notE (expandFunExt first) (expandFunExt second)
  | .allI proof => .allI (expandFunExt proof)
  | .allE term proof => .allE term (expandFunExt proof)
  | .exI term proof => .exI term (expandFunExt proof)
  | .exE first second => .exE (expandFunExt first) (expandFunExt second)
  | .eqRefl term => .eqRefl term
  | .eqSymm proof => .eqSymm (expandFunExt proof)
  | .eqTrans first second => .eqTrans (expandFunExt first) (expandFunExt second)
  | .eqPropI first second => .eqPropI (expandFunExt first) (expandFunExt second)
  | .eqPropEL proof => .eqPropEL (expandFunExt proof)
  | .eqPropER proof => .eqPropER (expandFunExt proof)
  | .eqApp term proof => .eqApp term (expandFunExt proof)
  | .eqAppArg function proof => .eqAppArg function (expandFunExt proof)
  | .eqLam proof => .eqLam (expandFunExt proof)
  | .funExt proof => funExtViaEta (expandFunExt proof)
  | .beta term body => .beta term body
  | .eta function => .eta function

theorem expandFunExt_primitiveUses (proof : ProofSyntax Const Δ φ) :
    primitiveFunExtUses (expandFunExt proof) = 0 := by
  induction proof with
  | _ => simp_all only [expandFunExt,primitiveFunExtUses,primitiveFunExtUses_funExtViaEta,Nat.add_zero]

#print axioms funExtViaEta
#print axioms funExtViaEta_not_free
#print axioms expandFunExt_primitiveUses

end Mettapedia.Logic.HOL.ProofSyntax
