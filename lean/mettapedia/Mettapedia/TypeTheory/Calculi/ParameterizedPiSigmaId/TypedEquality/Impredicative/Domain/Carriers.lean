import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Domain.Families

/-!
# The carrier of an identity type

The domain of an identity type is below its carrier (`Ideal.dom_ident_le`), so the
carrier tokens of a compact element below an identity type are below the carrier
(`Ideal.below_args_ident`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Domain
namespace Ideal

/-- **The domain of an identity type is below its carrier.** -/
theorem dom_ident_le (A I J : Ideal) : dom .ident (ident A I J) ≤ A := by
  refine closure_le fun s hs => ?_
  obtain ⟨w, hw, h⟩ := hs
  rw [ent_arg, List.all_nil, Bool.true_and] at h
  refine A.closed (fun c hc => ?_) h
  rcases mem_args_iff.1 hc with ⟨C, hC⟩ | ⟨-, t, ht, -, hd⟩
  · rcases hw _ hC with h' | ⟨d, h', hd⟩ | ⟨C', r, h', -, -⟩ | ⟨C', r, h', -, -⟩
    · cases h'
    · cases h'
      exact hd
    · cases h'
    · cases h'
  · rcases hw _ ht with rfl | ⟨d, rfl, -⟩ | ⟨C', r, rfl, hC', -⟩ | ⟨C', r, rfl, hC', -⟩
    · cases hd
    · cases hd
    · exact hC' c hd
    · exact hC' c hd

/-- The carrier tokens of a compact element below an identity type are below its
carrier. -/
theorem below_args_ident {A I J : Ideal} {b : List Tok} (hb : Below b (ident A I J)) :
    Below (args .ident 0 b) A :=
  (below_dom_args (k := .ident) hb).mono (dom_ident_le A I J)

end Ideal
end Domain
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
