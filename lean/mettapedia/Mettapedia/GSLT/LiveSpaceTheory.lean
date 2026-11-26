import Mettapedia.GSLT.Contracts.DialectProfileComposition
import Mettapedia.GSLT.Contracts.LiveTheoryProjections
import Mettapedia.GSLT.Contracts.OccurrenceObservers
import Mettapedia.GSLT.Contracts.ScopedAliasDispatch
import Mettapedia.GSLT.Contracts.GroundAliasUnion
import Mettapedia.GSLT.LanguageDef.LiveModuleSteps

/-! # Reading a live space as a theory

Admission is relative to a caller's observation. To carry an established
agreement between a source region and a plan to a later cut, validate both
read footprints; they need not use the same algorithm or ask the same
questions. To carry it to another profile, check its effective answers.
These are read-only results, not authority to repeat an effect. No default
realization or equation theory is selected here. -/
set_option autoImplicit false
namespace Mettapedia.GSLT.LiveSpaceTheory

open Mettapedia.Machines.ReadOnlyQuery (Program run)
open Mettapedia.Machines.VersionedValidation
open Contracts
open Contracts.LiveTheoryProjections
open Contracts.OccurrenceObservers
open Contracts.ReadWindowCuts (Cut)

theorem at_later_cut {S N R : Type*} [DecidableEq S] [DecidableEq N] [DecidableEq R]
    {A : Type} {m : Nat} (c : Classifier N R) (w : Cut m → World S R)
    (source plan : Program (Port S N) (Reply S R) (OccurrenceObservers.Trace A))
    (licensed requested : Demand) (coarsens : covers licensed requested = true)
    {old now : Cut m} (later : old ≤ now)
    (original : observe licensed (run (read c (w old)) plan).answer =
      observe licensed (run (read c (w old)) source).answer)
    (valid : StampAgrees (revision c w) now (takeStamp protects (revision c w) old
      ((run (read c (w old)) plan).reads ++ (run (read c (w old)) source).reads))) :
    observe requested (run (read c (w now)) plan).answer =
      observe requested (run (read c (w now)) source).answer := by
  have checked := stampAgrees_takeStamp_iff.mp valid
  have hp := replay c w later plan (stampAgrees_takeStamp_iff.mpr
    (fun r hr => checked r (List.mem_append_left _ hr)))
  have hs := replay c w later source (stampAgrees_takeStamp_iff.mpr
    (fun r hr => checked r (List.mem_append_right _ hr)))
  rw [hp, hs]
  exact (determines_iff licensed requested).2 coarsens _ _ original

open Contracts.DialectProfileComposition in
theorem across_profiles {S K B R : Type*} {A : Type}
    (p₁ p₂ : Layer S K B R)
    (source plan : Program (DialectProfileComposition.Port S K)
      (DialectProfileComposition.Reply B R) (OccurrenceObservers.Trace A))
    (licensed requested : Demand) (coarsens : covers licensed requested = true)
    (original : observe licensed (run (DialectProfileComposition.read p₁) plan).answer =
      observe licensed (run (DialectProfileComposition.read p₁) source).answer)
    (agrees : ∀ event ∈ (run (DialectProfileComposition.read p₁) plan).reads ++
      (run (DialectProfileComposition.read p₁) source).reads,
        DialectProfileComposition.read p₂ event.1 = event.2) :
    observe requested (run (DialectProfileComposition.read p₂) plan).answer =
      observe requested (run (DialectProfileComposition.read p₂) source).answer := by
  apply (determines_iff licensed requested).2 coarsens
  exact transport_region p₁ p₂ source plan _ _ original agrees

end Mettapedia.GSLT.LiveSpaceTheory
