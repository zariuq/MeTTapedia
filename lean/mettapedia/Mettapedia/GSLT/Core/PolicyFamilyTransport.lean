import Mettapedia.GSLT.Core.PolicyFamilySufficiency

/-!
# Transport of dependent policy families along state maps

A policy family on a target state space pulls back contravariantly along any
state map.  Executable readout realizations and policy support therefore
transport to the source.  The converse is valid precisely under an adequate
coverage premise: surjectivity of the state map is sufficient, while a
non-surjective map can hide the target states that distinguish a policy.

This is the state-level counterpart of observation pullback.  It does not
assert that the state map is an admitted language route or that a readout is
faithful.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core

universe uSource uTarget uPolicy uResult uReadout

namespace PolicyFamily

/-- Pull a dependent target policy family back along a map of retained
semantic states. -/
def pullback {Source : Type uSource} {Target : Type uTarget}
    (mapState : Source → Target)
    (family : PolicyFamily.{uTarget, uPolicy, uResult} Target) :
    PolicyFamily Source where
  Policy := family.Policy
  Result := family.Result
  decide := fun policy source => family.decide policy (mapState source)

@[simp] theorem pullback_decide
    {Source : Type uSource} {Target : Type uTarget}
    (mapState : Source → Target)
    (family : PolicyFamily.{uTarget, uPolicy, uResult} Target)
    (policy : family.Policy) (source : Source) :
    (family.pullback mapState).decide policy source =
      family.decide policy (mapState source) :=
  rfl

/-- Pullback respects composition at every dependent policy coordinate. -/
theorem pullback_comp_decide
    {First : Type uSource} {Middle : Type uTarget} {Last : Type*}
    (earlier : First → Middle) (later : Middle → Last)
    (family : PolicyFamily Last)
    (policy : family.Policy) (state : First) :
    ((family.pullback later).pullback earlier).decide policy state =
      (family.pullback (later ∘ earlier)).decide policy state :=
  rfl

/-- An executable target readout realization pulls back without changing its
runner: both the readout and semantic policy are precomposed with the same
state map. -/
def ReadoutRealization.pullback
    {Source : Type uSource} {Target : Type uTarget}
    {family : PolicyFamily.{uTarget, uPolicy, uResult} Target}
    {Readout : Type uReadout} {readout : Target → Readout}
    (realization : family.ReadoutRealization readout)
    (mapState : Source → Target) :
    (family.pullback mapState).ReadoutRealization (readout ∘ mapState) where
  run := realization.run
  agrees := fun policy state => realization.agrees policy (mapState state)

/-- Policy-family support always transports contravariantly along a state
map. -/
theorem supportsReadout_pullback
    {Source : Type uSource} {Target : Type uTarget}
    {family : PolicyFamily.{uTarget, uPolicy, uResult} Target}
    {Readout : Type uReadout} {readout : Target → Readout}
    (mapState : Source → Target)
    (supported : family.SupportsReadout readout) :
    (family.pullback mapState).SupportsReadout (readout ∘ mapState) := by
  obtain ⟨realization⟩ := supported
  exact ⟨realization.pullback mapState⟩

/-- A surjective state map makes policy support reflect as well as preserve:
the source sees every target state on which a policy could distinguish a
readout collision. -/
theorem supportsReadout_pullback_iff_of_surjective
    {Source : Type uSource} {Target : Type uTarget}
    {family : PolicyFamily.{uTarget, uPolicy, uResult} Target}
    {Readout : Type uReadout} {readout : Target → Readout}
    (mapState : Source → Target) (surjective : Function.Surjective mapState) :
    (family.pullback mapState).SupportsReadout (readout ∘ mapState) ↔
      family.SupportsReadout readout := by
  constructor
  · rintro ⟨sourceRealization⟩
    refine ⟨{
      run := sourceRealization.run
      agrees := ?_ }⟩
    intro policy target
    obtain ⟨source, maps⟩ := surjective target
    calc
      sourceRealization.run policy (readout target) =
          sourceRealization.run policy (readout (mapState source)) := by
        rw [maps]
      _ = (family.pullback mapState).decide policy source :=
        sourceRealization.agrees policy source
      _ = family.decide policy target := by
        simp [maps]
  · exact family.supportsReadout_pullback mapState

/-! ## Positive and negative controls -/

namespace TransportCanary

inductive Query where
  | value
deriving DecidableEq

def targetFamily : PolicyFamily Bool where
  Policy := Query
  Result := fun _ => Bool
  decide := fun _ state => state

def collapsedReadout : Bool → Unit := fun _ => ()

/-- The target family cannot run from the collapsed readout because it must
distinguish both Boolean states. -/
theorem target_refuses_collapsed :
    ¬ targetFamily.SupportsReadout collapsedReadout := by
  apply targetFamily.not_supportsReadout_of_policy_collision
    collapsedReadout (first := false) (second := true) rfl .value
  change false ≠ true
  decide

def includeFalse : Unit → Bool := fun _ => false

/-- A non-surjective pullback sees only `false`, so the same collapsed readout
is sufficient at the source.  Preservation therefore has no converse without
a coverage premise. -/
theorem nonsurjective_pullback_can_hide_refusal :
    (targetFamily.pullback includeFalse).SupportsReadout
      (collapsedReadout ∘ includeFalse) ∧
      ¬ targetFamily.SupportsReadout collapsedReadout := by
  constructor
  · refine ⟨{
      run := fun _ _ => false
      agrees := ?_ }⟩
    intro policy state
    cases state
    rfl
  · exact target_refuses_collapsed

def negate : Bool → Bool := not

theorem negate_surjective : Function.Surjective negate := by
  intro target
  cases target
  · exact ⟨true, rfl⟩
  · exact ⟨false, rfl⟩

/-- A surjective transport reflects the target refusal exactly. -/
theorem surjective_pullback_reflects_refusal :
    ¬ (targetFamily.pullback negate).SupportsReadout
        (collapsedReadout ∘ negate) := by
  intro sourceSupport
  exact target_refuses_collapsed
    ((targetFamily.supportsReadout_pullback_iff_of_surjective
      negate negate_surjective).1 sourceSupport)

end TransportCanary

#print axioms pullback_comp_decide
#print axioms ReadoutRealization.pullback
#print axioms supportsReadout_pullback
#print axioms supportsReadout_pullback_iff_of_surjective
#print axioms TransportCanary.nonsurjective_pullback_can_hide_refusal
#print axioms TransportCanary.surjective_pullback_reflects_refusal

end PolicyFamily

end Mettapedia.GSLT.Core
