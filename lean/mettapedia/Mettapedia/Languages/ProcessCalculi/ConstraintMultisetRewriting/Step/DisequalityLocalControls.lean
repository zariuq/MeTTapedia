import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DisequalityLocal
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.SettlementCoverage

/-!
# Committing settlement with local inequality preservation

The existing two-bit observation frame supplies the same model used by the
HOL controls. Resetting the first bit preserves `Y ≠ true`, but collapses
`X ≠ false`. Both input constraint stores are solvable. The globally
reflecting construction excludes this settlement; the local one admits the
compatible firing and refuses only the conflicting one.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DisequalityLocalControls

open Interface
open AdmissionObservationCover.Controls (World frame)
open DisequalityFrames (Separates)

def resetFirst (world : World) : World := fun i => if i = 0 then false else world i
def x : World → Bool := fun world => world 0
def y : World → Bool := fun world => world 1
def falsity : World → Bool := fun _ => false
def truth : World → Bool := fun _ => true

def yApart : Disequality.DisequationStore (World → Bool) := [(y, truth)]
def xApart : Disequality.DisequationStore (World → Bool) := [(x, falsity)]

abbrev base := (SettlementCoverage.Controls.quiet resetFirst).step

theorem y_identity_separates : Separates frame (a := ()) (b := ()) id yApart := by
  intro d member same
  obtain rfl := List.mem_singleton.mp member
  have point := congrFun same (fun _ => false)
  change false = true at point
  cases point

theorem x_identity_separates : Separates frame (a := ()) (b := ()) id xApart := by
  intro d member same
  obtain rfl := List.mem_singleton.mp member
  have point := congrFun same (fun _ => true)
  change true = false at point
  cases point

theorem reset_separates_y : Separates frame (a := ()) (b := ()) resetFirst yApart := by
  intro d member same
  obtain rfl := List.mem_singleton.mp member
  have point := congrFun same (fun _ => false)
  change resetFirst (fun _ => false) 1 = true at point
  simp [resetFirst] at point

theorem reset_collapses_x :
    frame.E (a := ()) (frame.act (a := ()) (b := ()) resetFirst x)
      (frame.act (a := ()) (b := ()) resetFirst falsity) := by
  funext world
  change resetFirst world 0 = false
  simp [resetFirst]

def stateY : base.DState := ⟨(), yApart, y_identity_separates⟩
def stateX : base.DState := ⟨(), xApart, x_identity_separates⟩

def firingY : base.DFiring stateY where
  base := ()
  tells := []
  formed := by
    change Separates frame id yApart
    exact y_identity_separates

def firingX : base.DFiring stateX where
  base := ()
  tells := []
  formed := by
    change Separates frame id xApart
    exact x_identity_separates

theorem base_prepares : base.Prepares (s := ()) () :=
  base.prepares (SettlementCoverage.Controls.quiet_admitted resetFirst)

theorem not_globally_reflecting : ¬ base.Reflects := by
  intro reflects
  have same := reflects (s := ()) () base_prepares reset_collapses_x
  have point := congrFun same (fun _ => true)
  change true = false at point
  cases point

theorem firingY_compatible : base.LocalCompatible firingY := by
  intro p
  change Separates frame resetFirst yApart
  exact reset_separates_y

theorem firingY_admitted : base.withLocalDisequations.Admits firingY := by
  apply (base.withLocalDisequations_admits_iff_separating firingY).mpr
  refine ⟨⟨List.nodup_nil, EvidenceInterface.Controls.enabled_nothing ∅,
    ⟨(), id, Frames.models_nil _, ?_⟩, ?_⟩, firingY_compatible⟩
  · change Separates frame id yApart
    exact y_identity_separates
  · intro b g _ _
    exact Frames.models_nil (X := frame) (a := ()) (b := b) g

theorem firingX_input_admitted : firingX.Admits := by
  refine ⟨List.nodup_nil, EvidenceInterface.Controls.enabled_nothing ∅, ?_, ?_⟩
  · apply (DisequalityFrames.solvable_iff (D := firingX.target) _).mpr
    refine ⟨(), id, Frames.models_nil _, ?_⟩
    change Separates frame id xApart
    exact x_identity_separates
  · intro B g _
    exact Frames.models_nil (X := frame) (a := ()) (b := B.obj) g.1

theorem firingX_refused : ¬ base.withLocalDisequations.Admits firingX := by
  apply base.withLocalDisequations_refused_of_collapsed firingX base_prepares
    (d := (x, falsity))
  · change (x, falsity) ∈ [(x, falsity)]
    exact List.mem_singleton_self _
  · exact reset_collapses_x

theorem strictly_more_general :
    base.withLocalDisequations.Admits firingY ∧ ¬ base.Reflects :=
  ⟨firingY_admitted, not_globally_reflecting⟩

/-- The input problem has separating solutions; only this commitment is refused. -/
theorem conflicting_commit_not_problem_refutation :
    firingX.Admits ∧ ¬ base.withLocalDisequations.Admits firingX :=
  ⟨firingX_input_admitted, firingX_refused⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DisequalityLocalControls
