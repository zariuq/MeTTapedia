import Mettapedia.Logic.HOL.ImpredicativeConnectives
import Mettapedia.Logic.HOL.ProofSyntaxStructural

/-!
# The retained implication, quantification and equality proof fragment

`IsCoreProof` checks both rule inventory and the term parameters inspected by
those rules. It is stable under occurrence transport and object renaming.
Derived logical rules are excluded even when their conclusions happen to be
core formulas. This distinguishes a proof translation from a term translation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.ImpredicativeConnectives

universe u v
variable {Base : Type u} {Const : Ty Base → Type v}
variable {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ}

@[simp] theorem isCore_rename {Ξ : Ctx Base} {τ : Ty Base}
    (ρ : Rename Base Γ Ξ) (term : Term Const Γ τ) :
    IsCore (rename ρ term) ↔ IsCore term := by
  induction term generalizing Ξ <;> simp_all [rename, IsCore]

/-- Syntactic support, not a derivability or semantic-validity assumption. -/
def IsCoreProof {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ} :
    ProofSyntax Const Δ φ → Prop
  | .hyp _ => True
  | @ProofSyntax.impI _ _ _ _ premise _ body => IsCore premise ∧ IsCoreProof body
  | .impE function argument => IsCoreProof function ∧ IsCoreProof argument
  | .allI body => IsCoreProof body
  | .allE term function => IsCore term ∧ IsCoreProof function
  | .eqRefl term => IsCore term
  | @ProofSyntax.eqSymm _ _ _ _ _ left right proof =>
      IsCore left ∧ IsCore right ∧ IsCoreProof proof
  | @ProofSyntax.eqTrans _ _ _ _ _ left middle right first second =>
      IsCore left ∧ IsCore middle ∧ IsCore right ∧ IsCoreProof first ∧ IsCoreProof second
  | @ProofSyntax.eqPropI _ _ _ _ left right forward backward =>
      IsCore left ∧ IsCore right ∧ IsCoreProof forward ∧ IsCoreProof backward
  | @ProofSyntax.eqPropEL _ _ _ _ left right proof =>
      IsCore left ∧ IsCore right ∧ IsCoreProof proof
  | @ProofSyntax.eqPropER _ _ _ _ left right proof =>
      IsCore left ∧ IsCore right ∧ IsCoreProof proof
  | @ProofSyntax.eqApp _ _ _ _ _ _ function other argument proof =>
      IsCore function ∧ IsCore other ∧ IsCore argument ∧ IsCoreProof proof
  | @ProofSyntax.eqAppArg _ _ _ _ _ _ function left right proof =>
      IsCore function ∧ IsCore left ∧ IsCore right ∧ IsCoreProof proof
  | @ProofSyntax.eqLam _ _ _ _ _ _ left right proof =>
      IsCore left ∧ IsCore right ∧ IsCoreProof proof
  | @ProofSyntax.funExt _ _ _ _ _ _ function other proof =>
      IsCore function ∧ IsCore other ∧ IsCoreProof proof
  | .beta term body => IsCore term ∧ IsCore body
  | .eta function => IsCore function
  | _ => False

@[simp] theorem isCoreProof_cast {ψ : Formula Const Γ} (equal : φ = ψ)
    (proof : ProofSyntax Const Δ φ) :
    IsCoreProof (equal ▸ proof : ProofSyntax Const Δ ψ) ↔ IsCoreProof proof := by
  cases equal
  rfl

@[simp] theorem isCoreProof_castIndices {Δ' : List (Formula Const Γ)} {ψ : Formula Const Γ}
    (assumptions : Δ = Δ') (conclusion : φ = ψ) (proof : ProofSyntax Const Δ φ) :
    IsCoreProof (proof.castIndices assumptions conclusion) ↔ IsCoreProof proof := by
  cases assumptions
  cases conclusion
  rfl

@[simp] theorem isCoreProof_mono {Δ' : List (Formula Const Γ)}
    (transport : ProofSyntax.OccurrenceMap Δ Δ') (proof : ProofSyntax Const Δ φ) :
    IsCoreProof (proof.mono transport) ↔ IsCoreProof proof := by
  induction proof with
  | hyp occurrence => simp [ProofSyntax.mono, IsCoreProof]
  | _ => simp_all only [ProofSyntax.mono, IsCoreProof]

@[simp] theorem isCoreProof_rename {Ξ : Ctx Base} (ρ : Rename Base Γ Ξ)
    (proof : ProofSyntax Const Δ φ) :
    IsCoreProof (proof.rename ρ) ↔ IsCoreProof proof := by
  induction proof generalizing Ξ with
  | _ => simp_all only [ProofSyntax.rename, isCoreProof_castIndices, IsCoreProof, isCore_rename]

end Mettapedia.Logic.HOL.ImpredicativeConnectives
