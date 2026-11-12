import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentRunRearrangement

/-!
# The actual dependent state comparisons form a groupoid

Unlike a bare transport interface, `PlainIso` retains a genuine contextual
isomorphism. Its other fields are preservation proofs. The category laws
therefore follow from those of contextual isomorphisms. This supplies a
concrete target for interpreting the boundary maps of run comparisons.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.RunStateGroupoid

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}
  (levels : LevelModel rules L) (O : Type)

def Object (_ : LevelModel rules L) (Occurrence : Type) := State rules Occurrence

theorem iso_ext {source target : State rules O} {first second : PlainIso levels source target}
    (same : first.frame = second.frame) : first = second := by
  cases first
  cases second
  cases same
  rfl

instance stateGroupoid : Groupoid (Object levels O) where
  Hom := PlainIso levels
  id := PlainIso.refl
  comp := PlainIso.trans
  id_comp := by
    intro source target arrow
    apply iso_ext
    simp [PlainIso.trans, PlainIso.refl]
  comp_id := by
    intro source target arrow
    apply iso_ext
    simp [PlainIso.trans, PlainIso.refl]
  assoc := by
    intro a b c d first second third
    apply iso_ext
    simp [PlainIso.trans, Iso.trans_assoc]
  inv := PlainIso.symm
  inv_comp := by
    intro source target arrow
    apply iso_ext
    simp [PlainIso.trans, PlainIso.symm, PlainIso.refl]
  comp_inv := by
    intro source target arrow
    apply iso_ext
    simp [PlainIso.trans, PlainIso.symm, PlainIso.refl]

noncomputable section

variable [DecidableEq O]

def endpointGenerators (start : State rules O) :
    Transport.RunRearrangement.Object (helperTransport levels O) start ⥤q Object levels O where
  obj run := run.last
  map witness := match witness with
    | .inl similar => similar.lastIso
    | .inr interchange => interchange.lastIso

def endpointFunctor (start : State rules O) :
    Transport.RunRearrangement.Groupoid (helperTransport levels O) start ⥤ Object levels O :=
  Transport.RunRearrangement.interpret (helperTransport levels O) (endpointGenerators levels O start)

def endpointMap {start : State rules O} {first second : (helperStep levels O).toStep.Run start}
    (cell : Transport.RunRearrangement.Cell (helperTransport levels O) first second) :
    PlainIso levels first.last second.last := (endpointFunctor levels O start).map cell

theorem endpointMap_comp {start : State rules O}
    {first second third : (helperStep levels O).toStep.Run start}
    (one : Transport.RunRearrangement.Cell (helperTransport levels O) first second)
    (two : Transport.RunRearrangement.Cell (helperTransport levels O) second third) :
    endpointMap levels O (one ≫ two) = (endpointMap levels O one).trans (endpointMap levels O two) :=
  (endpointFunctor levels O start).map_comp one two

theorem typed_rows {start : State rules O} {first second : (helperStep levels O).toStep.Run start}
    (cell : Transport.RunRearrangement.Cell (helperTransport levels O) first second) (occurrence : O) :
    second.last.label occurrence =
      (first.last.label occurrence).reindex (endpointMap levels O cell).frame.hom :=
  (endpointMap levels O cell).label occurrence

end

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.RunStateGroupoid

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.RunStateGroupoid.stateGroupoid
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.RunStateGroupoid.typed_rows
