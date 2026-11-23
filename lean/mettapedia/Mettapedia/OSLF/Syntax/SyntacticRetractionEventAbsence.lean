import Mettapedia.OSLF.Syntax.SyntacticRetractionContexts
import Mettapedia.GSLT.Topos.PresheafEventAbsence

/-!
# Event absence over retractable syntactic futures

The full contextual event graph supplies an actual backwards map along a
section. This earns reflection of its source fibres after restricting future
changes to split substitutions. The native negative predicate can therefore
be compared with present absence without assuming the desired equivalence.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.SyntacticRetractionEventAbsence

open _root_.CategoryTheory SyntacticRetractionContexts
open Mettapedia.GSLT.Topos.PresheafEventAbsence

universe u
variable {S : Signature}
variable {E P : (Syntactic.Ctxt S)ᵒᵖ ⥤ Type u}

def restrict (family : (Syntactic.Ctxt S)ᵒᵖ ⥤ Type u) :
    (Object S)ᵒᵖ ⥤ Type u :=
  (forget S).op ⋙ family

def restrictSource (source : E ⟶ P) : restrict E ⟶ restrict P :=
  Functor.whiskerLeft (forget S).op source

theorem action_left_inverse (family : (Syntactic.Ctxt S)ᵒᵖ ⥤ Type u)
    {source target : Object S} (change : source ⟶ target) :
    Function.LeftInverse (family.map (backward change).op) (family.map change.val.op) := by
  intro value
  rw [← Functor.map_comp_apply]
  change family.map (backward change ≫ change.val).op value = value
  rw [backward_section, op_id, Functor.map_id_apply]

theorem action_injective (family : (Syntactic.Ctxt S)ᵒᵖ ⥤ Type u)
    {source target : Object S} (change : source ⟶ target) :
    Function.Injective (family.map change.val.op) :=
  (action_left_inverse family change).injective

theorem source_fibre_reflection (source : E ⟶ P) :
    ReflectsAvailability (restrictSource source) ⊤ := by
  intro world future change program event _ over
  change P.obj (Opposite.op world.unop.context) at program
  change E.obj (Opposite.op future.unop.context) at event
  change source.app _ event = P.map change.unop.val.op program at over
  refine ⟨E.map (backward change.unop).op event, by trivial, ?_⟩
  change source.app _ (E.map (backward change.unop).op event) = program
  rw [source.naturality_apply, over, ← Functor.map_comp_apply]
  change P.map (backward change.unop ≫ change.unop.val).op program = program
  rw [backward_section, op_id, Functor.map_id_apply]

theorem native_absence_iff_present (source : E ⟶ P)
    (world : (Object S)ᵒᵖ) (program : (restrict P).obj world) :
    program ∈ (absent (restrictSource source) ⊤).obj world ↔
      ¬ ∃ event : (restrict E).obj world,
        (restrictSource source).app world event = program := by
  rw [absent_iff_present _ _ (source_fibre_reflection source)]
  simp only [Subfunctor.top_obj, Set.top_eq_univ, Set.mem_univ, true_and]

end Mettapedia.OSLF.Binding.SyntacticRetractionEventAbsence
