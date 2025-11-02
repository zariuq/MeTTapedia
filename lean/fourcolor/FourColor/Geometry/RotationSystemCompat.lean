import FourColor.Triangulation

namespace FourColor.Geometry

open scoped BigOperators

variable {V E : Type*}
variable [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable (RS : RotationSystem V E)

namespace RotationSystem

lemma phi_maps_faceOrbit {d d₀ : RS.D}
  (hd : d ∈ RS.faceOrbit d₀) :
  RS.phi d ∈ RS.faceOrbit d₀ := by
  classical
  have h : RS.phi.SameCycle d₀ d := by simpa [faceOrbit] using hd
  have : RS.phi.SameCycle d₀ (RS.phi d) :=
    h.trans (RS.phi.sameCycle_apply_self d)
  simpa [faceOrbit] using this

lemma phi_symm_maps_faceOrbit {d d₀ : RS.D}
  (hd : d ∈ RS.faceOrbit d₀) :
  RS.phi.symm d ∈ RS.faceOrbit d₀ := by
  classical
  have h : RS.phi.SameCycle d₀ d := by simpa [faceOrbit] using hd
  have h₁ : RS.phi.SameCycle (RS.phi.symm d) d :=
    RS.phi.sameCycle_apply_self (RS.phi.symm d)
  have h₂ : RS.phi.SameCycle (RS.phi.symm d) d₀ :=
    h₁.trans h.symm
  have : RS.phi.SameCycle d₀ (RS.phi.symm d) := h₂.symm
  simpa [faceOrbit] using this

lemma sum_comp_phi_faceOrbit
  {β : Type*} [AddCommMonoid β] {d₀ : RS.D} (g : RS.D → β) :
  ∑ d in RS.faceOrbit d₀, g (RS.phi d)
    = ∑ d in RS.faceOrbit d₀, g d := by
  classical
  refine Finset.sum_bij
    (fun d _ => RS.phi d)
    (fun d hd => phi_maps_faceOrbit RS hd)
    (fun _ _ _ _ h => RS.phi.injective h)
    ?surj
    (fun _ _ => rfl)
  intro d hd
  use RS.phi.symm d
  constructor
  · exact phi_symm_maps_faceOrbit RS hd
  · simp

end RotationSystem

end FourColor.Geometry
