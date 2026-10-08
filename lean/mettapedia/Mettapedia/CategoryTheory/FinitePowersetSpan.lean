import Mettapedia.CategoryTheory.FinitePowerset

/-!
# Relation coverage of finite span images

A finite set of actual span points supplies both successor images. If each
point satisfies the declared endpoint relation, the images satisfy complete
two-sided coverage. Collisions do not require a unique original span point.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.FinitePowersetSpan

open FinitePowerset

universe u v w

variable {Middle : Type u} {Left : Type v} {Right : Type w}

theorem images_related (relation : Left → Right → Prop)
    (first : Middle → Left) (second : Middle → Right) (points : Finset Middle)
    (coherent : ∀ point ∈ points, relation (first point) (second point)) :
    Related relation (map first points) (map second points) := by
  constructor
  · intro value member
    obtain ⟨point, present, rfl⟩ := (mem_map _ _ _).mp member
    exact ⟨second point, (mem_map _ _ _).mpr ⟨point, present, rfl⟩,
      coherent point present⟩
  · intro other member
    obtain ⟨point, present, rfl⟩ := (mem_map _ _ _).mp member
    exact ⟨first point, (mem_map _ _ _).mpr ⟨point, present, rfl⟩,
      coherent point present⟩

end Mettapedia.CategoryTheory.FinitePowersetSpan
