import Mettapedia.OSLF.Syntax.CartesianModelFinitePresentations
import Mettapedia.OSLF.Syntax.FormalFiniteLimitObjects

/-!
# Ordinary and authored-relative finite-limit object categories

The ordinary formal finite-limit embedding freely adds a terminal object even
when the authored category already has one. The finite-presentation embedding
respects that authored terminal object and all authored finite products. Hence
the two completions cannot be equivalent over the authored base category.

This obstruction does not by itself prove a universal property for the
relative completion; it identifies a necessary distinction in that theorem.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.CartesianContextModels

open CategoryTheory CategoryTheory.Limits
open Mettapedia.OSLF.FormalFiniteLimits

variable (C : Type) [SmallCategory C] [HasFiniteProducts C]

/-- There is no equivalence of the two finite-limit object categories that
intertwines their canonical embeddings of the authored context category. -/
theorem no_formal_equivalence_over_authored_context :
    ¬ ∃ e : Objects C ≌ FinitePresentationObjects C,
      Nonempty (base C ⋙ e.functor ≅ authoredContext C) := by
  rintro ⟨e, ⟨iso⟩⟩
  have hrelative : PreservesLimit (Functor.empty.{0} C)
      (authoredContext C) := by
    have : PreservesFiniteProducts (authoredContext C) :=
      authoredContext_preservesFiniteProducts C
    infer_instance
  have hcomposite : PreservesLimit (Functor.empty.{0} C)
      (base C ⋙ e.functor) :=
    preservesLimit_of_natIso (Functor.empty.{0} C) iso.symm
  have hreflect : ReflectsLimits e.functor := inferInstance
  have hbase : PreservesLimit (Functor.empty.{0} C) (base C) :=
    preservesLimit_of_reflects_of_preserves (base C) e.functor
  exact base_not_preserves_terminal C hbase

end Mettapedia.OSLF.CartesianContextModels
