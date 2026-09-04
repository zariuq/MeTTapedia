import Mettapedia.GSLT.Dynamics.ProofRelevantNeedSharing
import Mettapedia.TypeTheory.ContextualCodeObserverFactorization
import Mettapedia.TypeTheory.RevisionHorizonObserverFactorization

/-!
# Dependent families over lazy-sharing keys

A lazy-sharing key merges demand sites before evaluation.  Such reuse has two
independent obligations.

* **Fibre compatibility:** dependent payload types at merged sites must be
  equivalent, with a selected factorization supplying the transport.
* **Meaning invariance:** the declared observable meaning of merged sites must
  be equal.

Neither condition implies the other.  A constant dependent fibre can coexist
with observably different meanings, while a constant meaning can coexist with
non-equivalent dependent fibres.  Safe sharing requires both.

The generic results are instantiated twice.  Sharing contextual code only by
its spliced body is unsafe for tag-sensitive dependent payloads.  Sharing
unbounded revisions only by a finite horizon is unsafe for growing
revision-indexed history fibres.  Retaining exact code or revision identity
restores fibre compatibility without asserting that either key is the most
profitable implementation policy.

No cache implementation, evaluator, language, or product calculus is selected
here.
-/

set_option autoImplicit false

open Mettapedia.GSLT.Dynamics.ProofRelevantNeed
open Mettapedia.TypeTheory.DependentFamilyObserverFactorization

universe uSite uKey uMeaning uFibre uFine uCoarse

namespace Mettapedia.GSLT.Dynamics.ProofRelevantNeed.SharingScheme

variable {Site : Type uSite}

/-- A sharing key is fibre-compatible with a dependent payload family when
every pair of merged sites has equivalent fibres. -/
def FibreSoundFor
    (scheme : SharingScheme.{uSite, uKey} Site)
    (family : Site -> Type uFibre) : Prop :=
  forall {left right : Site}, scheme.Shares left right ->
    Nonempty (family left ≃ family right)

/-- Full reuse admissibility is the conjunction of meaning invariance and
dependent-fibre compatibility. -/
def ReuseAdmissible
    (scheme : SharingScheme.{uSite, uKey} Site)
    (meaning : Site -> Type uMeaning)
    (family : Site -> Type uFibre) : Prop :=
  scheme.SoundFor meaning ∧ scheme.FibreSoundFor family

/-- A dependent-family factorization through the sharing key supplies all
required fibre equivalences. -/
def fibreSoundFor_of_factorization
    (scheme : SharingScheme.{uSite, uKey} Site)
    {family : Site -> Type uFibre}
    (factorization : FamilyFactorization scheme.key family) :
    scheme.FibreSoundFor family := by
  intro left right shares
  exact ⟨factorization.fibreEquiv shares⟩

/-- A factorization gives a canonical transport between any two sites merged
by the sharing key. -/
def reuseEquiv
    (scheme : SharingScheme.{uSite, uKey} Site)
    {family : Site -> Type uFibre}
    (factorization : FamilyFactorization scheme.key family)
    {left right : Site} (shares : scheme.Shares left right) :
    family left ≃ family right :=
  factorization.fibreEquiv shares

@[simp] theorem reuseEquiv_roundtrip
    (scheme : SharingScheme.{uSite, uKey} Site)
    {family : Site -> Type uFibre}
    (factorization : FamilyFactorization scheme.key family)
    {left right : Site} (shares : scheme.Shares left right)
    (value : family left) :
    (scheme.reuseEquiv factorization shares).symm
        (scheme.reuseEquiv factorization shares value) = value :=
  Equiv.symm_apply_apply _ _

/-- Fibre compatibility descends from a coarse scheme to every refinement.
The converse is absent: merging more keys creates new dependent obligations. -/
theorem Coarsening.fibreSound_fine_of_coarse
    {fine : SharingScheme.{uSite, uFine} Site}
    {coarse : SharingScheme.{uSite, uCoarse} Site}
    (coarsening : Coarsening fine coarse)
    {family : Site -> Type uFibre}
    (sound : coarse.FibreSoundFor family) :
    fine.FibreSoundFor family := by
  intro left right shares
  exact sound (coarsening.map_shares shares)

/-- Full reuse admissibility also descends from coarse sharing to a finer
scheme. -/
theorem Coarsening.reuseAdmissible_fine_of_coarse
    {fine : SharingScheme.{uSite, uFine} Site}
    {coarse : SharingScheme.{uSite, uCoarse} Site}
    (coarsening : Coarsening fine coarse)
    {meaning : Site -> Type uMeaning}
    {family : Site -> Type uFibre}
    (admissible : coarse.ReuseAdmissible meaning family) :
    fine.ReuseAdmissible meaning family :=
  ⟨coarsening.sound_fine_of_sound_coarse admissible.1,
    coarsening.fibreSound_fine_of_coarse admissible.2⟩

/-- A single merged pair with non-equivalent fibres refutes dependent reuse. -/
theorem not_fibreSoundFor_of_collision
    (scheme : SharingScheme.{uSite, uKey} Site)
    {family : Site -> Type uFibre}
    {left right : Site} (shares : scheme.Shares left right)
    (notEquivalent : Not (Nonempty (family left ≃ family right))) :
    Not (scheme.FibreSoundFor family) := by
  intro sound
  exact notEquivalent (sound shares)

end Mettapedia.GSLT.Dynamics.ProofRelevantNeed.SharingScheme

namespace Mettapedia.GSLT.Dynamics.DependentSharingObserver

/-! ## Independence of type safety and semantic soundness -/

namespace OrthogonalityCanary

open ProofRelevantNeed.SharingCanary
open Mettapedia.TypeTheory.DependentFamilyObserverFactorization.Canary

/-- Constant fibres are compatible with the maximally coarse Boolean sharing
key. -/
theorem collapse_fibreSound_constant :
    collapseSites.FibreSoundFor (fun _ : Bool => PUnit) := by
  intro left right shares
  exact ⟨Equiv.refl PUnit⟩

/-- Constant meanings are invariant under the same coarse sharing key. -/
theorem collapse_meaningSound_constant :
    collapseSites.SoundFor (fun _ : Bool => PUnit) := by
  intro left right shares
  rfl

/-- The coarse key is type-compatible for a constant family but is not
semantically sound for the identity meaning. -/
theorem fibreSound_does_not_imply_meaningSound :
    collapseSites.FibreSoundFor (fun _ : Bool => PUnit) ∧
      Not (collapseSites.SoundFor id) :=
  ⟨collapse_fibreSound_constant,
    collapseSites_not_sound_for_identity⟩

/-- Conversely, constant meaning does not make the varying singleton/Boolean
family type-compatible. -/
theorem meaningSound_does_not_imply_fibreSound :
    collapseSites.SoundFor (fun _ : Bool => PUnit) ∧
      Not (collapseSites.FibreSoundFor varying) := by
  refine ⟨collapse_meaningSound_constant, ?_⟩
  exact collapseSites.not_fibreSoundFor_of_collision
    (left := false) (right := true) rfl unit_not_equiv_bool

/-- The two reuse obligations are logically independent on one fixed sharing
scheme. -/
theorem dependent_sharing_obligations_are_independent :
    (collapseSites.FibreSoundFor (fun _ : Bool => PUnit) ∧
      Not (collapseSites.SoundFor id)) ∧
    (collapseSites.SoundFor (fun _ : Bool => PUnit) ∧
      Not (collapseSites.FibreSoundFor varying)) :=
  ⟨fibreSound_does_not_imply_meaningSound,
    meaningSound_does_not_imply_fibreSound⟩

end OrthogonalityCanary

/-! ## Contextual-code sharing -/

namespace ContextualCodeCanary

open Mettapedia.TypeTheory.ContextualCode
open Mettapedia.TypeTheory.ContextualCodeObserverFactorization.Canary

/-- Share tagged code sites only by their spliced body. -/
def bodySharing : SharingScheme (PUnit × Bool) where
  Key := PUnit
  decEq := inferInstance
  key := (FibreCanary.taggedReadout PUnit).observe

/-- Body-only sharing is compatible with a body-constant payload family. -/
theorem bodySharing_constant_fibreSound :
    bodySharing.FibreSoundFor (fun _ : PUnit × Bool => PUnit) := by
  intro left right shares
  exact ⟨Equiv.refl PUnit⟩

/-- Body-only sharing is not compatible with a payload family that observes
the retained code tag. -/
theorem bodySharing_tagSensitive_not_fibreSound :
    Not (bodySharing.FibreSoundFor tagSensitiveFamily) := by
  exact bodySharing.not_fibreSoundFor_of_collision
    (left := (PUnit.unit, false)) (right := (PUnit.unit, true)) rfl
    Mettapedia.TypeTheory.DependentFamilyObserverFactorization.Canary.unit_not_equiv_bool

/-- Retaining exact code identity as the sharing key restores fibre
compatibility for every dependent code family. -/
def exactCodeSharing : SharingScheme (PUnit × Bool) where
  Key := PUnit × Bool
  decEq := inferInstance
  key := id

theorem exactCodeSharing_fibreSound
    (family : PUnit × Bool -> Type uFibre) :
    exactCodeSharing.FibreSoundFor family := by
  intro left right shares
  have equal : left = right := by
    simpa [SharingScheme.Shares, exactCodeSharing] using shares
  subst right
  exact ⟨Equiv.refl _⟩

/-- Exact code identity is sufficient for dependent fibre safety, whereas
spliced-body identity alone is not.  This does not claim exact identity is the
optimal cache key for every observer. -/
theorem contextual_code_sharing_boundary :
    bodySharing.FibreSoundFor (fun _ : PUnit × Bool => PUnit) ∧
      Not (bodySharing.FibreSoundFor tagSensitiveFamily) ∧
      exactCodeSharing.FibreSoundFor tagSensitiveFamily :=
  ⟨bodySharing_constant_fibreSound,
    bodySharing_tagSensitive_not_fibreSound,
    exactCodeSharing_fibreSound tagSensitiveFamily⟩

end ContextualCodeCanary

/-! ## Revision-horizon sharing -/

namespace RevisionCanary

open Mettapedia.TypeTheory.RevisionHorizonObserverFactorization

/-- Share unbounded revisions only by their finite horizon observation. -/
def horizonSharing (horizon : Nat) : SharingScheme Nat where
  Key := Fin (horizon + 1)
  decEq := inferInstance
  key := (horizonReadout horizon).observe

/-- Revision-independent fibres remain compatible with every finite horizon. -/
theorem horizonSharing_constant_fibreSound (horizon : Nat) :
    (horizonSharing horizon).FibreSoundFor (fun _ : Nat => PUnit) := by
  intro left right shares
  exact ⟨Equiv.refl PUnit⟩

/-- A growing revision-indexed history family is not safe to share through a
finite horizon which identifies adjacent revisions. -/
theorem horizonSharing_history_not_fibreSound (horizon : Nat) :
    Not ((horizonSharing horizon).FibreSoundFor finiteHistoryFamily) := by
  exact (horizonSharing horizon).not_fibreSoundFor_of_collision
    (left := horizon) (right := horizon + 1)
    (horizon_and_successor_same_observation horizon)
    (adjacent_history_fibres_not_equivalent horizon)

/-- Retain exact revision identity in the sharing key. -/
def exactRevisionSharing : SharingScheme Nat where
  Key := Nat
  decEq := inferInstance
  key := id

theorem exactRevisionSharing_fibreSound
    (family : Nat -> Type uFibre) :
    exactRevisionSharing.FibreSoundFor family := by
  intro left right shares
  have equal : left = right := by
    simpa [SharingScheme.Shares, exactRevisionSharing] using shares
  subst right
  exact ⟨Equiv.refl _⟩

/-- Finite-horizon sharing is safe for revision-independent data but unsafe
for growing history fibres; exact revision identity restores type safety. -/
theorem revision_sharing_boundary (horizon : Nat) :
    (horizonSharing horizon).FibreSoundFor (fun _ : Nat => PUnit) ∧
      Not ((horizonSharing horizon).FibreSoundFor finiteHistoryFamily) ∧
      exactRevisionSharing.FibreSoundFor finiteHistoryFamily :=
  ⟨horizonSharing_constant_fibreSound horizon,
    horizonSharing_history_not_fibreSound horizon,
    exactRevisionSharing_fibreSound finiteHistoryFamily⟩

end RevisionCanary

#print axioms ProofRelevantNeed.SharingScheme.fibreSoundFor_of_factorization
#print axioms ProofRelevantNeed.SharingScheme.reuseEquiv_roundtrip
#print axioms ProofRelevantNeed.SharingScheme.Coarsening.fibreSound_fine_of_coarse
#print axioms OrthogonalityCanary.dependent_sharing_obligations_are_independent
#print axioms ContextualCodeCanary.contextual_code_sharing_boundary
#print axioms RevisionCanary.revision_sharing_boundary

end Mettapedia.GSLT.Dynamics.DependentSharingObserver
