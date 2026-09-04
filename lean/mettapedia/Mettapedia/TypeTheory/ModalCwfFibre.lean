import Mettapedia.GSLT.Core.ContextualLadder
import Mettapedia.TypeTheory.ModalCwF

/-!
# Fixed-mode fibres of multimodal categories with families

A multimodal CwF contains an ordinary contextual theory at every mode.
This module states that fact as a forgetful construction.  It retains
contexts, substitutions, dependent types, terms, and comprehension at one
selected mode.  It deliberately forgets modal arrows, locking, boxed types,
quotation, cost grading, the chosen empty context, dependent products, and
the chosen Tarski universe.

The construction is therefore a comparison interface, not a claim that
modal and ordinary dependent type theories are equivalent.  In particular,
two modal theories can have the same fixed-mode fibre while differing in
their cross-mode or representation-sensitive structure.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ModalCwfFibre

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory

/-- A cast is heterogeneously equal to the term it transports. -/
private theorem heq_cast {Source Target : Sort _} (same : Source = Target)
    (value : Source) : HEq value (cast same value) := by
  subst Target
  rfl

/-- The modal term transport is heterogeneously equal to its input. -/
private theorem heq_castTm {modes : ModeTheory} (modal : ModalCwF modes)
    {mode : modes.Mode} {context : modal.Con mode}
    {Source Target : modal.Ty context} (same : Source = Target)
    (value : modal.Tm context Source) :
    HEq value (modal.castTm same value) := by
  subst Target
  rfl

/-- Forget the modal structure of a multimodal CwF at one selected mode. -/
def fibreCwf {modes : ModeTheory} (modal : ModalCwF modes)
    (laws : ModalCwFLaws modes modal)
    (coherence : ModalCwFCoherence modes modal laws)
    (mode : modes.Mode) :
    Cwf.{1, 0, 1, 0} where
  Ctx := modal.Con mode
  Sub := modal.Sub
  idS := modal.sid
  compS later earlier := modal.scomp earlier later
  id_comp := laws.scomp_sid_right
  comp_id := laws.scomp_sid_left
  comp_assoc := by
    intro first second third last later middle earlier
    exact (laws.scomp_assoc earlier middle later).symm
  Ty := modal.Ty
  tySub := modal.tySub
  tySub_id := modal.tySub_id
  tySub_comp := by
    intro first middle last type later earlier
    exact modal.tySub_comp type earlier later
  Tm := modal.Tm
  tmSub := modal.tmSub
  tmSub_id := by
    intro context type term
    apply eq_of_heq
    exact (laws.tmSub_id term).trans (heq_cast _ term)
  tmSub_comp := by
    intro first middle last type term later earlier
    apply eq_of_heq
    exact (laws.tmSub_comp term earlier later).trans
      (heq_cast _ (modal.tmSub (modal.tmSub term later) earlier))
  ext := modal.ext
  wk := modal.wk
  vz := modal.vz
  pair substitution type term := modal.sext substitution term
  wk_pair := by
    intro first last substitution type term
    exact laws.wk_sext substitution term
  vz_pair := by
    intro first last substitution type term
    apply eq_of_heq
    exact (laws.vz_sext substitution term).trans (heq_cast _ term)
  pair_eta := by
    intro first last type substitution
    have canonical := (ModalCwFCoherence.sext_unique
      (cwf := modal) (laws := laws) coherence
      type substitution).symm
    calc
      _ = modal.sext (modal.scomp substitution (modal.wk type))
          (modal.castTm
            (modal.tySub_comp type substitution (modal.wk type)).symm
            (modal.tmSub (modal.vz type) substitution)) := by
        apply congrArg
          (modal.sext (modal.scomp substitution (modal.wk type)))
        apply eq_of_heq
        exact (heq_cast _ (modal.tmSub (modal.vz type) substitution)).symm.trans
          (heq_castTm modal _ (modal.tmSub (modal.vz type) substitution))
      _ = substitution := canonical

end Mettapedia.TypeTheory.ModalCwfFibre
