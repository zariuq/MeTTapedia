import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Consistency.Telescopes
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Consistency.Functions
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Eliminator

/-!
# Identity elimination in the consistency model, at every level

In the consistency model an identity type relates terms only when its endpoints
are related (`Den.id_endpoints`). So a valid path makes the motive's instance at
the base point with reflexivity, and its instance at the endpoint with the
path, types with one interpretation at the level of the motive's universe
(`idMotive_same`), whatever the level of the carrier.

* **The cast.** Identity elimination that returns its method on every path,
  `J A x P d y e ⟶ d`, is a valid term of `elimType u w` for every carrier
  universe `u` and every motive universe `w` (`ValidTm.castEliminator`): the
  method is related at the method's type, which is the result type's
  interpretation.
* **The transport.** Identity elimination that transports its method,
  `J A x P d y e ⟶ coe (P x (refl x)) (P y e) d`, is valid at every level pair
  once the transport is *coherent* in the consistency model at the motive's
  level: between two types with one interpretation, the transport of a valid
  value is related to it (`ValidTm.transportEliminator_of_coherent`). The model's
  universe relation relates types by their interpretation alone, with no shape,
  and the model has no daimon clause: a transport whose rows reach the daimon is
  no number, no type and no code. Coherence is therefore a statement that types
  of one interpretation have transport-compatible forms; it is the hypothesis of
  this theorem, not a consequence of the transport table.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Consistency

open Normalization (WhRed WhStep appSpine elimType elimTelescope elimBody motiveType
  inst0_motiveCod)
open TelescopeAbstraction (applyClosed)

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L] {M : Model Head L}

/-! ## Motives -/

section Motives

variable (laws : M.Laws)
include laws

/-- **A motive related to another, applied to the base point and to a point
related to it, and to any two paths, gives types related in the motive's
universe.** At the base point the identity type `Id A x x` relates every two
paths. -/
theorem idMotive_universe {n : Nat} {ξ : World M.reading n} {A x b f g p q : Tm Head n}
    {w : Head} (hw : M.rules.isUniverse w) {RF : Rel Head n}
    (denF : Den M ξ (motiveType A x w) RF) (hfg : RF f g)
    (hxb : ∀ {RA : Rel Head n}, Den M ξ A RA → RA x b) :
    universeAt M (M.levels.level w) ξ (.app (.app f x) p) (.app (.app g b) q) := by
  obtain ⟨R₂, den₂, h₂⟩ := Den.pi_app_exists laws denF hfg hxb
  rw [inst0_motiveCod] at den₂
  obtain ⟨R₃, den₃, h₃⟩ := Den.pi_app_exists laws den₂ h₂
    fun denI => Den.id_diag laws denI p q
  have den₃' : Den M ξ (.head w) R₃ := den₃
  obtain rfl := Den.sort_inv laws hw den₃'
  exact @h₃

/-- **At related endpoints, the motive's instance at the base point with
reflexivity and its instance at the endpoint with any path have one
interpretation** at the level of the motive's universe. -/
theorem idMotive_same {n : Nat} {ξ : World M.reading n} {A x y f p : Tm Head n} {w : Head}
    (hw : M.rules.isUniverse w) {RF : Rel Head n} (denF : Den M ξ (motiveType A x w) RF)
    (hf : RF f f) (hxy : ∀ {RA : Rel Head n}, Den M ξ A RA → RA x y) :
    ∃ R, InterpAt M (M.levels.level w) ξ (.app (.app f x) (.refl x)) R ∧
      InterpAt M (M.levels.level w) ξ (.app (.app f y) p) R :=
  universeAt.den (idMotive_universe laws hw denF hf hxy)

end Motives

/-! ## The cast -/

/-- **Identity elimination by a cast is a valid term of the eliminator's type at
every carrier universe `u` and every motive universe `w`** in the consistency
model, when that type is valid with valid parts. No premise is placed on the
level of `u`: a valid path relates its endpoints. -/
theorem ValidTm.castEliminator (laws : M.Laws) {J : DeclName} {u w : Head}
    (hw : M.rules.isUniverse w)
    (castStep : ∀ {m : Nat} (a₀ a₁ a₂ a₃ a₄ a₅ : Tm Head m),
      M.rules.computation.step (appSpine (.const J) [a₀, a₁, a₂, a₃, a₄, a₅]) a₃)
    (validType : ValidTy M .nil (elimType u w)) (partsType : Structured M .nil (elimType u w)) :
    ValidTm M .nil (.const J) (elimType u w) := by
  obtain ⟨_, validC, _⟩ := ValidTy.close_parts (elimTelescope u w) (C := elimBody)
    validType partsType
  refine ValidTm.close laws (elimTelescope u w) (C := elimBody) (f := .const J) validType
    partsType ⟨validC, ?_⟩
  intro m ξ σ σ' e R den
  have red : ∀ τ : Sub Head 6 m, WhRed M.rules M.roles
      (Presentation.subst τ (applyClosed (elimTelescope u w) ids (liftClosed (.const J))))
      (τ 2) := fun τ => .single (.root (castStep _ _ _ _ _ _))
  refine Den.expandLeft den (red σ) (Den.expandRight den (red σ') ?_)
  obtain ⟨⟨⟨⟨⟨⟨-, -, -, -⟩, -, -, -⟩, RP, denP, hP⟩, Rd, dend, hd⟩, -, -, -⟩, Rp, denp, hp⟩ := e
  change Den M ξ (motiveType (σ 5) (σ 4) w) RP at denP
  change RP (σ 3) (σ' 3) at hP
  change Den M ξ (.app (.app (σ 3) (σ 4)) (.refl (σ 4))) Rd at dend
  change Rd (σ 2) (σ' 2) at hd
  change Den M ξ (.id (σ 5) (σ 4) (σ 1)) Rp at denp
  change Den M ξ (.app (.app (σ 3) (σ 1)) (σ 0)) R at den
  obtain ⟨R', base, endpoint⟩ := idMotive_same laws hw denP (Den.refl_left laws denP hP)
    (fun denA => Den.id_endpoints laws denp hp denA) (p := σ 0)
  rw [Den.deterministic laws den ⟨_, endpoint⟩]
  rw [Den.deterministic laws dend ⟨_, base⟩] at hd
  exact hd

/-! ## The transport -/

/-- **Transport coherence at a level**: between two types with one
interpretation at level `k`, the transport of a valid value is related to it. -/
def TransportCoherent (M : Model Head L) (coe : DeclName) (k : L) : Prop :=
  ∀ {n : Nat} {ξ : World M.reading n} {X Y d : Tm Head n} {R : Rel Head n},
    InterpAt M k ξ X R → InterpAt M k ξ Y R → R d d → R (appSpine (.const coe) [X, Y, d]) d

/-- **Identity elimination by transport is valid at every carrier universe and
every motive universe `w` in the consistency model, when the transport is
coherent at the level of `w`.** A valid path relates its endpoints, so the four
instances of the related motives, at the base points with reflexivity and at the
endpoints with the paths, have one interpretation; coherence relates both
transports to the related methods. -/
theorem ValidTm.transportEliminator_of_coherent (laws : M.Laws) {J coe : DeclName} {u w : Head}
    (hw : M.rules.isUniverse w)
    (jStep : ∀ {m : Nat} (a₀ a₁ a₂ a₃ a₄ a₅ : Tm Head m),
      M.rules.computation.step (appSpine (.const J) [a₀, a₁, a₂, a₃, a₄, a₅])
        (appSpine (.const coe) [.app (.app a₂ a₁) (.refl a₁), .app (.app a₂ a₄) a₅, a₃]))
    (coherent : TransportCoherent M coe (M.levels.level w))
    (validType : ValidTy M .nil (elimType u w)) (partsType : Structured M .nil (elimType u w)) :
    ValidTm M .nil (.const J) (elimType u w) := by
  obtain ⟨_, validC, _⟩ := ValidTy.close_parts (elimTelescope u w) (C := elimBody)
    validType partsType
  refine ValidTm.close laws (elimTelescope u w) (C := elimBody) (f := .const J) validType
    partsType ⟨validC, ?_⟩
  intro m ξ σ σ' e R den
  have red : ∀ τ : Sub Head 6 m, WhRed M.rules M.roles
      (Presentation.subst τ (applyClosed (elimTelescope u w) ids (liftClosed (.const J))))
      (appSpine (.const coe) [.app (.app (τ 3) (τ 4)) (.refl (τ 4)),
        .app (.app (τ 3) (τ 1)) (τ 0), τ 2]) := fun τ => .single (.root (jStep _ _ _ _ _ _))
  refine Den.expandLeft den (red σ) (Den.expandRight den (red σ') ?_)
  obtain ⟨⟨⟨⟨⟨⟨-, -, -, -⟩, RA, denA, hx⟩, RP, denP, hP⟩, Rd, dend, hd⟩, RA', denA', hy⟩,
    Rp, denp, hp⟩ := e
  change Den M ξ (σ 5) RA at denA
  change RA (σ 4) (σ' 4) at hx
  change Den M ξ (motiveType (σ 5) (σ 4) w) RP at denP
  change RP (σ 3) (σ' 3) at hP
  change Den M ξ (.app (.app (σ 3) (σ 4)) (.refl (σ 4))) Rd at dend
  change Rd (σ 2) (σ' 2) at hd
  change Den M ξ (σ 5) RA' at denA'
  change RA' (σ 1) (σ' 1) at hy
  change Den M ξ (.id (σ 5) (σ 4) (σ 1)) Rp at denp
  change Den M ξ (.app (.app (σ 3) (σ 1)) (σ 0)) R at den
  rw [Den.deterministic laws denA' denA] at hy
  have uniq : ∀ {RA'' : Rel Head m}, Den M ξ (σ 5) RA'' → RA'' = RA :=
    fun d => Den.deterministic laws d denA
  -- The path relates its endpoints.
  have hxy : RA (σ 4) (σ 1) := Den.id_endpoints laws denp hp denA
  have hxy' : RA (σ 4) (σ' 1) := Den.trans laws denA hxy hy
  have hxx' : RA (σ 4) (σ' 4) := hx
  -- The four instances of the motives have one interpretation.
  have hPP := Den.refl_left laws denP hP
  obtain ⟨Q, hX, hY⟩ := universeAt.den (idMotive_universe laws hw denP hPP (p := .refl (σ 4))
    (q := σ 0) fun d => uniq d ▸ hxy)
  obtain ⟨Q₁, hX₁, hX'⟩ := universeAt.den (idMotive_universe laws hw denP hP
    (p := .refl (σ 4)) (q := .refl (σ' 4)) fun d => uniq d ▸ hxx')
  obtain ⟨Q₂, hX₂, hY'⟩ := universeAt.den (idMotive_universe laws hw denP hP
    (p := .refl (σ 4)) (q := σ' 0) fun d => uniq d ▸ hxy')
  obtain rfl := InterpAt.deterministic laws hX₁ hX
  obtain rfl := InterpAt.deterministic laws hX₂ hX₁
  obtain rfl := Den.deterministic laws den ⟨_, hY⟩
  obtain rfl := Den.deterministic laws dend ⟨_, hX₂⟩
  -- Coherence at both pairs, and the related methods.
  have left := coherent hX₂ hY (Den.refl_left laws dend hd)
  have right := coherent hX' hY' (Den.refl_right laws dend hd)
  exact Den.trans laws den left (Den.trans laws den hd (Den.symm laws den right))

end Consistency
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
