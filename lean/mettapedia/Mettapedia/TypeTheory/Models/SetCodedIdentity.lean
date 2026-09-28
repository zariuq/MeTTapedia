import Mettapedia.TypeTheory.ContextualIdentityTypes
import Mettapedia.Logic.HOL.Embedding.ZFSetTraceProofDecoding

/-!
# Identity elimination in the set-coded contextual model

Identity fibres use the existing separated truth code of equality of their
endpoints. Formation, reflexivity and full dependent J inhabit the same
set-coded CwF as the trace products and dependent sums. The motive of J may
depend on both endpoints and on the set-coded witness.

This equality model validates endpoint reflection and proof irrelevance.
Those are properties of this model, not new conversion or proof-erasure rules
for an interpreted syntax. Native typing soundness is a separate obligation.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Models.SetCodedIdentity

open Mettapedia.Logic.HOL.Embedding
open ZFSetDependentProducts (Elements)
open ZFSetContextualInterpretation (SetFamily Section Extension codedCwf extensionSubstitution)
open ZFSetTraceProofDecoding (truthCode mem_truthCode)
open ContextualIdentityTypes

universe u

noncomputable def identityFamily {Γ : Type (u + 1)} {a : SetFamily Γ}
    (left right : Section a) : SetFamily Γ :=
  fun γ => truthCode (left γ = right γ)

noncomputable def formation : IdentityFormation codedCwf.{u} where
  idTy _ left right := identityFamily left right
  idTy_sub _ _ _ _ := rfl

noncomputable def reflSection {Γ : Type (u + 1)} {a : SetFamily Γ}
    (term : Section a) : Section (identityFamily term term) :=
  fun _ => ⟨∅, (mem_truthCode _ _).mpr ⟨rfl, rfl⟩⟩

noncomputable def reflexivity : IdentityReflexivity codedCwf.{u} formation where
  refl := reflSection
  refl_sub := by
    intro source target substitution type term
    exact HEq.rfl

theorem witness_endpoints {Γ : Type (u + 1)} {a : SetFamily Γ}
    {left right : Section a} {γ : Γ}
    (witness : Elements (identityFamily left right γ)) : left γ = right γ :=
  ((mem_truthCode _ _).mp witness.2).2

theorem witness_value {Γ : Type (u + 1)} {a : SetFamily Γ}
    {left right : Section a} {γ : Γ}
    (witness : Elements (identityFamily left right γ)) : witness.1 = ∅ :=
  ((mem_truthCode _ _).mp witness.2).1

noncomputable def reflexivitySubstitution {Γ : Type (u + 1)} (a : SetFamily Γ) :
    Extension a → identityContext codedCwf formation a :=
  fun point => ⟨⟨point, point.2⟩, ⟨∅, (mem_truthCode _ _).mpr ⟨rfl, rfl⟩⟩⟩

/-- Eliminate the actual set-coded witness, retaining the full dependent
motive. Equality of endpoints alone would not type this operation without
also identifying the witness with the canonical reflexivity code. -/
noncomputable def j {Γ : Type (u + 1)} {a : SetFamily Γ}
    (motive : SetFamily (identityContext codedCwf formation a))
    (base : Section (motive ∘ reflexivitySubstitution a)) : Section motive := by
  intro point
  rcases point with ⟨⟨⟨γ, left⟩, right⟩, witness⟩
  have endpoints : left = right := ((mem_truthCode _ _).mp witness.2).2
  subst right
  have canonical : witness =
      (⟨∅, (mem_truthCode _ _).mpr ⟨rfl, rfl⟩⟩ : Elements (truthCode (left = left))) :=
    Subtype.ext ((mem_truthCode _ _).mp witness.2).1
  cases canonical
  exact base ⟨γ, left⟩

theorem j_beta {Γ : Type (u + 1)} {a : SetFamily Γ}
    (motive : SetFamily (identityContext codedCwf formation a))
    (base : Section (motive ∘ reflexivitySubstitution a)) :
    (fun point => j motive base (reflexivitySubstitution a point)) = base := by
  funext point
  rfl

noncomputable def elimination : IdentityEliminationBeta codedCwf.{u} formation reflexivity where
  reflexivitySubstitution := reflexivitySubstitution
  over_diagonal _ := rfl
  witness_is_refl _ := HEq.rfl
  j := j
  beta := j_beta

/-- Reindexing preserves the set-coded witness, not just its inhabitation. -/
def identityReindex {Γ Δ : Type (u + 1)} (θ : Δ → Γ) (a : SetFamily Γ) :
    identityContext codedCwf formation (a ∘ θ) → identityContext codedCwf formation a :=
  fun point => ⟨⟨⟨θ point.1.1.1, point.1.1.2⟩, point.1.2⟩, point.2⟩

@[simp] theorem identityReindex_id {Γ : Type (u + 1)} (a : SetFamily Γ) :
    identityReindex id a = id := rfl

@[simp] theorem identityReindex_comp {Γ Δ Ξ : Type (u + 1)}
    (θ : Δ → Γ) (σ : Ξ → Δ) (a : SetFamily Γ) :
    identityReindex (θ ∘ σ) a = identityReindex θ a ∘ identityReindex σ (a ∘ θ) := rfl

theorem reflexivity_square {Γ Δ : Type (u + 1)} (θ : Δ → Γ) (a : SetFamily Γ) :
    identityReindex θ a ∘ reflexivitySubstitution (a ∘ θ) =
      reflexivitySubstitution a ∘ extensionSubstitution θ a := rfl

theorem j_substitution {Γ Δ : Type (u + 1)} (θ : Δ → Γ) (a : SetFamily Γ)
    (motive : SetFamily (identityContext codedCwf formation a))
    (base : Section (motive ∘ reflexivitySubstitution a)) :
    (fun point => j motive base (identityReindex θ a point)) =
      j (motive ∘ identityReindex θ a)
        (fun point => base (extensionSubstitution θ a point)) := by
  funext point
  rcases point with ⟨⟨⟨δ, left⟩, right⟩, witness⟩
  have endpoints : left = right := ((mem_truthCode _ _).mp witness.2).2
  subst right
  have canonical : witness =
      (⟨∅, (mem_truthCode _ _).mpr ⟨rfl, rfl⟩⟩ : Elements (truthCode (left = left))) :=
    Subtype.ext ((mem_truthCode _ _).mp witness.2).1
  cases canonical
  rfl

theorem j_beta_substitution {Γ Δ : Type (u + 1)} (θ : Δ → Γ) (a : SetFamily Γ)
    (motive : SetFamily (identityContext codedCwf formation a))
    (base : Section (motive ∘ reflexivitySubstitution a)) :
    (fun point => j motive base
      (identityReindex θ a (reflexivitySubstitution (a ∘ θ) point))) =
        fun point => base (extensionSubstitution θ a point) := by
  funext point
  exact congrFun (j_beta motive base) (extensionSubstitution θ a point)

theorem endpointReflection : IdentityEndpointReflection codedCwf.{u} formation := by
  intro Γ a left right proof
  funext γ
  exact witness_endpoints (proof γ)

theorem proofIrrelevance : IdentityProofIrrelevance codedCwf.{u} formation := by
  intro Γ a left right
  constructor
  intro first second
  funext γ
  exact Subtype.ext ((witness_value (first γ)).trans (witness_value (second γ)).symm)

/-! ## Comparison with the independently constructed full family model -/

open Mettapedia.GSLT.Core.ContextualLadder (familiesCwf)

/-- Decode the identity witness while leaving the environment and both
actual set elements unchanged. -/
def decodeContext {Γ : Type (u + 1)} (a : SetFamily Γ) :
    identityContext codedCwf formation a →
      identityContext familiesCwf Families.identityFormation (fun γ => Elements (a γ)) :=
  fun point => ⟨point.1, ⟨⟨((mem_truthCode _ _).mp point.2.2).2⟩⟩⟩

noncomputable def encodeContext {Γ : Type (u + 1)} (a : SetFamily Γ) :
    identityContext familiesCwf Families.identityFormation (fun γ => Elements (a γ)) →
      identityContext codedCwf formation a :=
  fun point => ⟨point.1, ⟨∅, (mem_truthCode _ _).mpr ⟨rfl, point.2.down.down⟩⟩⟩

theorem encode_decode {Γ : Type (u + 1)} (a : SetFamily Γ)
    (point : identityContext codedCwf formation a) :
    encodeContext a (decodeContext a point) = point := by
  rcases point with ⟨endpoints, witness⟩
  dsimp only [encodeContext, decodeContext]
  exact congrArg (Sigma.mk endpoints)
    (Subtype.ext ((mem_truthCode _ _).mp witness.2).1.symm)

theorem decode_encode {Γ : Type (u + 1)} (a : SetFamily Γ)
    (point : identityContext familiesCwf Families.identityFormation (fun γ => Elements (a γ))) :
    decodeContext a (encodeContext a point) = point := by
  rfl

noncomputable def contextEquiv {Γ : Type (u + 1)} (a : SetFamily Γ) :
    identityContext codedCwf formation a ≃
      identityContext familiesCwf Families.identityFormation (fun γ => Elements (a γ)) where
  toFun := decodeContext a
  invFun := encodeContext a
  left_inv := encode_decode a
  right_inv := decode_encode a

/-- The two independently defined eliminators agree after decoding their
identity contexts. HEq records the context isomorphism in the result fibre;
no equality of an arbitrary Lean type with its set code is asserted. -/
theorem j_agrees_with_families {Γ : Type (u + 1)} (a : SetFamily Γ)
    (motive : SetFamily (identityContext codedCwf formation a))
    (base : Section (motive ∘ reflexivitySubstitution a))
    (point : identityContext codedCwf formation a) :
    HEq (j motive base point)
      (Families.identityElimination.j (fun p => Elements (motive (encodeContext a p)))
        base (decodeContext a point)) := by
  rcases point with ⟨⟨⟨γ, left⟩, right⟩, witness⟩
  have endpoints : left = right := ((mem_truthCode _ _).mp witness.2).2
  subst right
  have canonical : witness =
      (⟨∅, (mem_truthCode _ _).mpr ⟨rfl, rfl⟩⟩ : Elements (truthCode (left = left))) :=
    Subtype.ext ((mem_truthCode _ _).mp witness.2).1
  cases canonical
  exact HEq.rfl

#print axioms elimination
#print axioms j_substitution
#print axioms j_beta_substitution
#print axioms endpointReflection
#print axioms proofIrrelevance
#print axioms contextEquiv
#print axioms j_agrees_with_families

end Mettapedia.TypeTheory.Models.SetCodedIdentity
