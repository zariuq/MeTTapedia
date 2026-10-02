import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Domain.ChurchLaws

/-!
# The identity eliminator read at the reflexivity point

The function of the identity eliminator read at the reflexivity point
(`Ideal.jAlignedRaw`) returns, at a path that is a reflexivity, the method projected
onto the motive at the path's point and the reflexivity there
(`Ideal.appSpine_jAlignedRaw`); projected onto its declared type it is the constant
`jAlignedConst`. Its value is observed only through the point of the path.

**Its linear rule is valid** at every spine `J A x P d y (refl a)` with spine facts
whose path has as parameter type an identity type between the point `a` and itself
(`jAlignedConst_linear`). At a spine with spine facts the path's parameter type is
`Id A x y` (`dom_instPi_jType`); an identity type determines its endpoints, so `x`, `a`
and `y` denote alike, and the method is an element of its parameter type
`P x (refl x)` (`jType_method`), which is the motive at the point. No hypothesis on
the contractum is needed.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Domain

open Annotated (CTm)

namespace Ideal

/-- The function of the identity eliminator read at the reflexivity point: at a path
that is a reflexivity, the method projected onto the motive at the path's point and
the reflexivity there. -/
def jAlignedRaw : Ideal :=
  lam fun _ => lam fun _ => lam fun P => lam fun D => lam fun _ => lam fun Q =>
    whenTag .refl (principal Q)
      (projT (app (app (principal P) (reflPoint (principal Q))) (refl (reflPoint (principal Q))))
        (principal D))

/-- The method projected onto the motive at the point of a path is continuous in the
path. -/
theorem cont_reflMotive (π δ : Ideal) :
    Cont fun q => projT (app (app π (reflPoint q)) (refl (reflPoint q))) δ :=
  (cont_projT_type δ).comp
    (cont₂_app.comp ((cont₂_app.right π).comp cont_reflPoint) (cont_refl.comp cont_reflPoint))

theorem appSpine_jAlignedRaw (α ξ π δ η p : Ideal) :
    appSpine jAlignedRaw [α, ξ, π, δ, η, p] =
      whenTag .refl p (projT (app (app π (reflPoint p)) (refl (reflPoint p))) δ) := by
  have hP : Cont fun π' => lam fun D => lam fun _ => lam fun Q =>
      whenTag .refl (principal Q) (projT (app (app π' (reflPoint (principal Q)))
        (refl (reflPoint (principal Q)))) (principal D)) :=
    cont_lam_param fun D => cont_lam_param fun _ => cont_lam_param fun Q =>
      ((cont₂_whenTag .refl).right (principal Q)).comp
        ((cont_projT_type (principal D)).comp
          ((cont₂_app.left (refl (reflPoint (principal Q)))).comp
            (cont₂_app.left (reflPoint (principal Q)))))
  have hD : Cont fun d => lam fun _ => lam fun Q =>
      whenTag .refl (principal Q) (projT (app (app π (reflPoint (principal Q)))
        (refl (reflPoint (principal Q)))) d) :=
    cont_lam_param fun _ => cont_lam_param fun Q =>
      ((cont₂_whenTag .refl).right (principal Q)).comp (cont_projT _)
  have hQ : Cont fun q =>
      whenTag .refl q (projT (app (app π (reflPoint q)) (refl (reflPoint q))) δ) :=
    (cont₂_whenTag .refl).comp Cont.id (cont_reflMotive π δ)
  have e₃ : app (lam fun P => lam fun D => lam fun _ => lam fun Q =>
      whenTag .refl (principal Q) (projT (app (app (principal P) (reflPoint (principal Q)))
        (refl (reflPoint (principal Q)))) (principal D))) π =
      lam fun D => lam fun _ => lam fun Q =>
        whenTag .refl (principal Q) (projT (app (app π (reflPoint (principal Q)))
          (refl (reflPoint (principal Q)))) (principal D)) :=
    app_lam_principal hP π
  have e₄ : app (lam fun D => lam fun _ => lam fun Q =>
      whenTag .refl (principal Q) (projT (app (app π (reflPoint (principal Q)))
        (refl (reflPoint (principal Q)))) (principal D))) δ =
      lam fun _ => lam fun Q =>
        whenTag .refl (principal Q) (projT (app (app π (reflPoint (principal Q)))
          (refl (reflPoint (principal Q)))) δ) :=
    app_lam_principal hD δ
  have e₆ : app (lam fun Q => whenTag .refl (principal Q) (projT (app (app π
      (reflPoint (principal Q))) (refl (reflPoint (principal Q)))) δ)) p =
      whenTag .refl p (projT (app (app π (reflPoint p)) (refl (reflPoint p))) δ) :=
    app_lam_principal hQ p
  show app (app (app (app (app (app jAlignedRaw α) ξ) π) δ) η) p = _
  unfold jAlignedRaw
  rw [app_lam_const, app_lam_const, e₃, e₄, app_lam_const, e₆]

end Ideal

open Ideal

variable {Head : Type}

/-- **The identity eliminator read at the reflexivity point**: its function projected
onto its declared type. -/
def jAlignedConst (Rd : Reading Head) (u : Head) : Ideal := projT (jTypeI Rd u) jAlignedRaw

/-- At a spine of the eliminator's first five arguments with spine facts, the method
is an element of the motive at the base point and its reflexivity. -/
theorem jType_method {Rd : Reading Head} {u : Head} {α ξ π δ η : Ideal}
    (spine : SpineTyped (jTypeI Rd u) [α, ξ, π, δ, η]) :
    projT (app (app π ξ) (refl ξ)) δ = δ := by
  obtain ⟨-, s1⟩ := (spineTyped_cinterp_pi Rd _ _ _ _ _).1 spine
  obtain ⟨-, s2⟩ := (spineTyped_cinterp_pi Rd _ _ _ _ _).1 s1
  obtain ⟨-, s3⟩ := (spineTyped_cinterp_pi Rd _ _ _ _ _).1 s2
  exact ((spineTyped_cinterp_pi Rd _ _ _ _ _).1 s3).1

/-- At a spine of the eliminator's first five arguments with spine facts, the path's
parameter type is the identity type between the base point and the endpoint. -/
theorem dom_instPi_jType {Rd : Reading Head} {u : Head} {α ξ π δ η : Ideal}
    (spine : SpineTyped (jTypeI Rd u) [α, ξ, π, δ, η]) :
    dom .pi (instPi (jTypeI Rd u) [α, ξ, π, δ, η]) = ident α ξ η := by
  obtain ⟨h1, s1⟩ := (spineTyped_cinterp_pi Rd _ _ _ _ _).1 spine
  obtain ⟨h2, s2⟩ := (spineTyped_cinterp_pi Rd _ _ _ _ _).1 s1
  obtain ⟨h3, s3⟩ := (spineTyped_cinterp_pi Rd _ _ _ _ _).1 s2
  obtain ⟨h4, s4⟩ := (spineTyped_cinterp_pi Rd _ _ _ _ _).1 s3
  obtain ⟨h5, -⟩ := (spineTyped_cinterp_pi Rd _ _ _ _ _).1 s4
  have e : instPi (jTypeI Rd u) [α, ξ, π, δ, η] =
      cinterp Rd (.pi (.id (.var 4) (.var 3) (.var 0)) (.app (.app (.var 3) (.var 1)) (.var 0)))
        (Env.cons η (Env.cons δ (Env.cons π (Env.cons ξ (Env.cons α Env.nil))))) :=
    (instPi_cinterp_pi_of Rd _ h1).trans ((instPi_cinterp_pi_of Rd _ h2).trans
      ((instPi_cinterp_pi_of Rd _ h3).trans ((instPi_cinterp_pi_of Rd _ h4).trans
        ((instPi_cinterp_pi_of Rd [] h5).trans rfl))))
  rw [e]
  exact dom_cinterp_pi Rd _ _ _

/-- **The linear rule of the eliminator read at the reflexivity point is valid** at
every spine `J A x P d y (refl a)` with spine facts at `τ` whose path has as parameter
type an identity type between the point `a` and itself: the spine denotes the
method. -/
theorem jAlignedConst_linear (Rd : Reading Head) (u : Head) {α ξ π δ η a τ : Ideal}
    (facts : SpineFacts (jTypeI Rd u) [α, ξ, π, δ, η, refl a] τ)
    (reflFact : ∃ T, dom .pi (instPi (jTypeI Rd u) [α, ξ, π, δ, η]) = ident T a a) :
    appSpine (jAlignedConst Rd u) [α, ξ, π, δ, η, refl a] = δ := by
  obtain ⟨rfl, spine⟩ := facts
  have pre : SpineTyped (jTypeI Rd u) [α, ξ, π, δ, η] :=
    ((spineTyped_append (args := [α, ξ, π, δ, η]) (args' := [refl a])).1 spine).1
  obtain ⟨T, hT⟩ := reflFact
  rw [dom_instPi_jType pre] at hT
  obtain ⟨hξ, hη⟩ := ident_endpoints_eq hT
  have hδ : projT (app (app π a) (refl a)) δ = δ := by
    rw [← hξ]
    exact jType_method pre
  refine churchConst_root (churchTele_cinterp Rd (jTypeC u) Env.nil) (Nat.le_refl _) spine ?_ ?_
  · rw [appSpine_jAlignedRaw, whenTag_of_mem (refl_mem_tag a), reflPoint_refl, hδ]
  · rw [instPi_jType spine, hη, hδ]

end Domain
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
