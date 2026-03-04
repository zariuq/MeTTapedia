import Mettapedia.Languages.ProcessCalculi.PiCalculus.Syntax
import Mettapedia.Languages.ProcessCalculi.PiCalculus.StructuralCongruence
import Mettapedia.Languages.ProcessCalculi.PiCalculus.Reduction
import Mettapedia.Languages.ProcessCalculi.PiCalculus.MultiStep
import Mettapedia.Languages.ProcessCalculi.PiCalculus.RhoEncoding
import Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation
import Mettapedia.Languages.ProcessCalculi.PiCalculus.WeakBisim
import Mettapedia.Languages.ProcessCalculi.PiCalculus.WeakBisimDerived
import Mettapedia.Languages.ProcessCalculi.PiCalculus.WeakBisimOpenMapBridge
import Mettapedia.Languages.ProcessCalculi.PiCalculus.BranchingBisim
import Mettapedia.Languages.ProcessCalculi.PiCalculus.OpenMapBridgeRegression
import Mettapedia.Languages.ProcessCalculi.PiCalculus.EncodingMorphism
import Mettapedia.Languages.ProcessCalculi.PiCalculus.BackwardAdminReflection

/-!
# π-Calculus Formalization

Main entry point that re-exports the core π-calculus modules plus open-map bridges.

## Contents
- Syntax: Process syntax and names
- StructuralCongruence: α-equivalence and ≡ relation
- Reduction: Operational semantics
- MultiStep: Reflexive-transitive closure of reduction
- ForwardSimulation: π→ρ simulation infrastructure
- WeakBisim / WeakBisimDerived: restricted weak bisimilarity
- WeakBisimOpenMapBridge / BranchingBisim: generalized open-map bridges
- OpenMapBridgeRegression: theorem-level bridge regressions
- RhoEncoding: Encoding π → ρ (Lybech 2022)
-/

namespace Mettapedia.Languages.ProcessCalculi.PiCalculus

/-- Freshness-threaded umbrella re-export theorem: non-RF administrative
correspondence with explicit `EncodingFresh` hypothesis for the ν/listener path. -/
theorem nonRF_admin_correspondence_umbrella_fresh {N : Finset String}
    (x : Name) (P : Process)
    (nuListenerBody seedListenerBody : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (xr yr : Name) (Pr : Process) (n v : String)
    (hfresh : EncodingFresh P) :
    (∃ Trep, Nonempty ((encode (.replicate xr yr Pr) n v) ⇝ᵈ* Trep) ∧
      Trep ≈ᵈ{N}
        (rhoPar
          (rhoInput (piNameToRhoName xr) yr (encode Pr (n ++ "_rep") v))
          (encode (.replicate xr yr Pr) n v))) ∧
    (∃ Tnu Tseed TrepNu,
      fullEncode (.nu x P) =
        rhoPar (encode (.nu x P) "n_init" "v_init")
          (nameServer "ns_x" "ns_z" "v_init" "ns_seed") ∧
      Nonempty
        ((.collection .hashBag
          [rhoPar (encode (.nu x P) "n_init" "v_init")
             (.apply "PInput" [.fvar "v_init", .lambda nuListenerBody]),
           rhoPar (nameServer "ns_x" "ns_z" "v_init" "ns_seed")
             (.apply "PInput" [.fvar "ns_z", .lambda seedListenerBody]),
           encode (.replicate "ns_x" "_drop" .nil) "n_init" "v_init"] none) ⇝ᵈ*
          (.collection .hashBag [Tnu, Tseed, TrepNu] none)) ∧
      (.collection .hashBag [Tnu, Tseed] none ≡
        .collection .hashBag [Tseed, Tnu] none) ∧
      WeakRestrictedBisimD N Tnu
        (.collection .hashBag
          [Mettapedia.OSLF.MeTTaIL.Substitution.commSubst nuListenerBody (.fvar "n_init"),
           rhoInput (.fvar "n_init") x (encode P ("n_init" ++ "_" ++ "n_init") "v_init")] none) ∧
      WeakRestrictedBisimD N Tseed
        (.collection .hashBag
          [Mettapedia.OSLF.MeTTaIL.Substitution.commSubst seedListenerBody (.apply "PDrop" [.fvar "ns_seed"]),
           rhoReplicate (Mettapedia.Languages.ProcessCalculi.PiCalculus.nameServerBody "ns_x" "ns_z" "v_init"),
           dropOperation "ns_x"] none) ∧
      WeakRestrictedBisimD N TrepNu
        (rhoPar
          (rhoInput (piNameToRhoName "ns_x") "_drop" (encode .nil ("n_init" ++ "_rep") "v_init"))
          (encode (.replicate "ns_x" "_drop" .nil) "n_init" "v_init"))) ∧
    BackwardAdminReflection.WeakBackwardOutcome N
      (rhoPar (encode (.nu x P) "n_init" "v_init")
        (.apply "PInput" [.fvar "v_init", .lambda nuListenerBody])) ∧
    BackwardAdminReflection.WeakBackwardOutcome N
      (rhoPar (nameServer "ns_x" "ns_z" "v_init" "ns_seed")
        (.apply "PInput" [.fvar "ns_z", .lambda seedListenerBody])) ∧
    BackwardAdminReflection.WeakBackwardOutcome N
      (encode (.replicate xr yr Pr) n v) := by
  simpa using
    (BackwardAdminReflection.full_nonRF_admin_correspondence_bidir_fresh
      (N := N) x P nuListenerBody seedListenerBody xr yr Pr n v hfresh)

/-- Observation-set weakening for the freshness-threaded non-RF admin umbrella:
if the package holds at `Nsup`, it holds at any subset `N ⊆ Nsup`. -/
theorem nonRF_admin_correspondence_umbrella_fresh_of_obsSuperset
    {N Nsup : Finset String}
    (hsub : N ⊆ Nsup)
    (x : Name) (P : Process)
    (nuListenerBody seedListenerBody : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (xr yr : Name) (Pr : Process) (n v : String)
    (hfresh : EncodingFresh P) :
    (∃ Trep, Nonempty ((encode (.replicate xr yr Pr) n v) ⇝ᵈ* Trep) ∧
      Trep ≈ᵈ{N}
        (rhoPar
          (rhoInput (piNameToRhoName xr) yr (encode Pr (n ++ "_rep") v))
          (encode (.replicate xr yr Pr) n v))) ∧
    (∃ Tnu Tseed TrepNu,
      fullEncode (.nu x P) =
        rhoPar (encode (.nu x P) "n_init" "v_init")
          (nameServer "ns_x" "ns_z" "v_init" "ns_seed") ∧
      Nonempty
        ((.collection .hashBag
          [rhoPar (encode (.nu x P) "n_init" "v_init")
             (.apply "PInput" [.fvar "v_init", .lambda nuListenerBody]),
           rhoPar (nameServer "ns_x" "ns_z" "v_init" "ns_seed")
             (.apply "PInput" [.fvar "ns_z", .lambda seedListenerBody]),
           encode (.replicate "ns_x" "_drop" .nil) "n_init" "v_init"] none) ⇝ᵈ*
          (.collection .hashBag [Tnu, Tseed, TrepNu] none)) ∧
      (.collection .hashBag [Tnu, Tseed] none ≡
        .collection .hashBag [Tseed, Tnu] none) ∧
      WeakRestrictedBisimD N Tnu
        (.collection .hashBag
          [Mettapedia.OSLF.MeTTaIL.Substitution.commSubst nuListenerBody (.fvar "n_init"),
           rhoInput (.fvar "n_init") x (encode P ("n_init" ++ "_" ++ "n_init") "v_init")] none) ∧
      WeakRestrictedBisimD N Tseed
        (.collection .hashBag
          [Mettapedia.OSLF.MeTTaIL.Substitution.commSubst seedListenerBody (.apply "PDrop" [.fvar "ns_seed"]),
           rhoReplicate (Mettapedia.Languages.ProcessCalculi.PiCalculus.nameServerBody "ns_x" "ns_z" "v_init"),
           dropOperation "ns_x"] none) ∧
      WeakRestrictedBisimD N TrepNu
        (rhoPar
          (rhoInput (piNameToRhoName "ns_x") "_drop" (encode .nil ("n_init" ++ "_rep") "v_init"))
          (encode (.replicate "ns_x" "_drop" .nil) "n_init" "v_init"))) ∧
    BackwardAdminReflection.WeakBackwardOutcome N
      (rhoPar (encode (.nu x P) "n_init" "v_init")
        (.apply "PInput" [.fvar "v_init", .lambda nuListenerBody])) ∧
    BackwardAdminReflection.WeakBackwardOutcome N
      (rhoPar (nameServer "ns_x" "ns_z" "v_init" "ns_seed")
        (.apply "PInput" [.fvar "ns_z", .lambda seedListenerBody])) ∧
    BackwardAdminReflection.WeakBackwardOutcome N
      (encode (.replicate xr yr Pr) n v) := by
  have hsup :=
    nonRF_admin_correspondence_umbrella_fresh
      (N := Nsup) x P nuListenerBody seedListenerBody xr yr Pr n v hfresh
  rcases hsup with ⟨hrep, hcombo, hnuOut, hseedOut, hrepOut⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rcases hrep with ⟨Trep, hstar, hbisim⟩
    exact ⟨Trep, hstar,
      Mettapedia.Languages.ProcessCalculi.PiCalculus.WeakRestrictedBisimD.mono hbisim hsub⟩
  · rcases hcombo with ⟨Tnu, Tseed, TrepNu, hfull, hstar, hswap, hbNu, hbSeed, hbRepNu⟩
    exact ⟨Tnu, Tseed, TrepNu, hfull, hstar, hswap,
      Mettapedia.Languages.ProcessCalculi.PiCalculus.WeakRestrictedBisimD.mono hbNu hsub,
      Mettapedia.Languages.ProcessCalculi.PiCalculus.WeakRestrictedBisimD.mono hbSeed hsub,
      Mettapedia.Languages.ProcessCalculi.PiCalculus.WeakRestrictedBisimD.mono hbRepNu hsub⟩
  · exact
      BackwardAdminReflection.WeakBackwardOutcome.mono
        hnuOut hsub
  · exact
      BackwardAdminReflection.WeakBackwardOutcome.mono
        hseedOut hsub
  · exact
      BackwardAdminReflection.WeakBackwardOutcome.mono
        hrepOut hsub

/-- Calculus-level non-RF administrative correspondence package with explicit
freshness threading: forward admin closure + backward outcomes for ν/seed/replicate
sources under derived semantics. -/
theorem calculus_correspondence_nonRF_admin_package_fresh_umbrella
    {N : Finset String}
    (x : Name) (P : Process)
    (nuListenerBody seedListenerBody : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (xr yr : Name) (Pr : Process) (n v : String)
    (hfresh : EncodingFresh P) :
    (∃ Trep, Nonempty ((encode (.replicate xr yr Pr) n v) ⇝ᵈ* Trep) ∧
      Trep ≈ᵈ{N}
        (rhoPar
          (rhoInput (piNameToRhoName xr) yr (encode Pr (n ++ "_rep") v))
          (encode (.replicate xr yr Pr) n v))) ∧
    (∃ Tnu Tseed TrepNu,
      fullEncode (.nu x P) =
        rhoPar (encode (.nu x P) "n_init" "v_init")
          (nameServer "ns_x" "ns_z" "v_init" "ns_seed") ∧
      Nonempty
        ((.collection .hashBag
          [rhoPar (encode (.nu x P) "n_init" "v_init")
             (.apply "PInput" [.fvar "v_init", .lambda nuListenerBody]),
           rhoPar (nameServer "ns_x" "ns_z" "v_init" "ns_seed")
             (.apply "PInput" [.fvar "ns_z", .lambda seedListenerBody]),
           encode (.replicate "ns_x" "_drop" .nil) "n_init" "v_init"] none) ⇝ᵈ*
          (.collection .hashBag [Tnu, Tseed, TrepNu] none)) ∧
      (.collection .hashBag [Tnu, Tseed] none ≡
        .collection .hashBag [Tseed, Tnu] none) ∧
      WeakRestrictedBisimD N Tnu
        (.collection .hashBag
          [Mettapedia.OSLF.MeTTaIL.Substitution.commSubst nuListenerBody (.fvar "n_init"),
           rhoInput (.fvar "n_init") x (encode P ("n_init" ++ "_" ++ "n_init") "v_init")] none) ∧
      WeakRestrictedBisimD N Tseed
        (.collection .hashBag
          [Mettapedia.OSLF.MeTTaIL.Substitution.commSubst seedListenerBody (.apply "PDrop" [.fvar "ns_seed"]),
           rhoReplicate (Mettapedia.Languages.ProcessCalculi.PiCalculus.nameServerBody "ns_x" "ns_z" "v_init"),
           dropOperation "ns_x"] none) ∧
      WeakRestrictedBisimD N TrepNu
        (rhoPar
          (rhoInput (piNameToRhoName "ns_x") "_drop" (encode .nil ("n_init" ++ "_rep") "v_init"))
          (encode (.replicate "ns_x" "_drop" .nil) "n_init" "v_init"))) ∧
    BackwardAdminReflection.WeakBackwardOutcome N
      (rhoPar (encode (.nu x P) "n_init" "v_init")
        (.apply "PInput" [.fvar "v_init", .lambda nuListenerBody])) ∧
    BackwardAdminReflection.WeakBackwardOutcome N
      (rhoPar (nameServer "ns_x" "ns_z" "v_init" "ns_seed")
        (.apply "PInput" [.fvar "ns_z", .lambda seedListenerBody])) ∧
    BackwardAdminReflection.WeakBackwardOutcome N
      (encode (.replicate xr yr Pr) n v) := by
  exact nonRF_admin_correspondence_umbrella_fresh
    (N := N) x P nuListenerBody seedListenerBody xr yr Pr n v hfresh

/-- Complete pre-OSLF calculus correspondence package:
bundles RF forward correspondence, strongest one-step backward outcomes,
strongest star-level backward partitions, and freshness-threaded non-RF
administrative correspondence into one export theorem. -/
theorem calculus_correspondence_prelude_complete_package_umbrella
    {N : Finset String}
    (x : Name) (P : Process)
    (nuListenerBody seedListenerBody : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (xr yr : Name) (Pr : Process) (n v : String)
    (hfresh : EncodingFresh P) :
    (∀ {P0 P1 : Process},
      (h : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.MultiStepRF P0 P1) →
      (hrf : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.RestrictionFree P0) →
      (hsafe : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.MultiCommSafe h) →
      ∀ n0 v0,
      ∃ T,
        Nonempty
          (Mettapedia.Languages.ProcessCalculi.RhoCalculus.ReducesStar
            (encode P0 n0 v0) T) ∧
        Mettapedia.Languages.ProcessCalculi.PiCalculus.WeakRestrictedBisim N T (encode P1 n0 v0))
    ∧
    (∀ {src tgt : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern},
      BackwardAdminReflection.EncodedSCStepSource N src →
      Nonempty
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerived src tgt) →
      BackwardAdminReflection.WeakBackwardOutcome N src)
    ∧
    (∀ {src tgt : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern},
      BackwardAdminReflection.EncodedSCStepSource N src →
      Nonempty
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar src tgt) →
      (∃ tgt' canon,
        Nonempty
          (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar src tgt') ∧
        BackwardAdminReflection.AdminCanonicalTarget src canon ∧
        Mettapedia.Languages.ProcessCalculi.PiCalculus.WeakRestrictedBisimD N tgt' canon)
      ∨
      (∃ P0 P1 n0 v0 tgt',
        Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence src (encode P0 n0 v0) ∧
        Nonempty (P0 ⇝ P1) ∧
        Nonempty
          (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar (encode P0 n0 v0) tgt') ∧
        Mettapedia.Languages.ProcessCalculi.PiCalculus.WeakRestrictedBisimD N tgt' (encode P1 n0 v0)))
    ∧
    ((∃ Trep, Nonempty ((encode (.replicate xr yr Pr) n v) ⇝ᵈ* Trep) ∧
      Trep ≈ᵈ{N}
        (rhoPar
          (rhoInput (piNameToRhoName xr) yr (encode Pr (n ++ "_rep") v))
          (encode (.replicate xr yr Pr) n v))) ∧
    (∃ Tnu Tseed TrepNu,
      fullEncode (.nu x P) =
        rhoPar (encode (.nu x P) "n_init" "v_init")
          (nameServer "ns_x" "ns_z" "v_init" "ns_seed") ∧
      Nonempty
        ((.collection .hashBag
          [rhoPar (encode (.nu x P) "n_init" "v_init")
             (.apply "PInput" [.fvar "v_init", .lambda nuListenerBody]),
           rhoPar (nameServer "ns_x" "ns_z" "v_init" "ns_seed")
             (.apply "PInput" [.fvar "ns_z", .lambda seedListenerBody]),
           encode (.replicate "ns_x" "_drop" .nil) "n_init" "v_init"] none) ⇝ᵈ*
          (.collection .hashBag [Tnu, Tseed, TrepNu] none)) ∧
      (.collection .hashBag [Tnu, Tseed] none ≡
        .collection .hashBag [Tseed, Tnu] none) ∧
      WeakRestrictedBisimD N Tnu
        (.collection .hashBag
          [Mettapedia.OSLF.MeTTaIL.Substitution.commSubst nuListenerBody (.fvar "n_init"),
           rhoInput (.fvar "n_init") x (encode P ("n_init" ++ "_" ++ "n_init") "v_init")] none) ∧
      WeakRestrictedBisimD N Tseed
        (.collection .hashBag
          [Mettapedia.OSLF.MeTTaIL.Substitution.commSubst seedListenerBody (.apply "PDrop" [.fvar "ns_seed"]),
           rhoReplicate (Mettapedia.Languages.ProcessCalculi.PiCalculus.nameServerBody "ns_x" "ns_z" "v_init"),
           dropOperation "ns_x"] none) ∧
      WeakRestrictedBisimD N TrepNu
        (rhoPar
          (rhoInput (piNameToRhoName "ns_x") "_drop" (encode .nil ("n_init" ++ "_rep") "v_init"))
          (encode (.replicate "ns_x" "_drop" .nil) "n_init" "v_init"))) ∧
    BackwardAdminReflection.WeakBackwardOutcome N
      (rhoPar (encode (.nu x P) "n_init" "v_init")
        (.apply "PInput" [.fvar "v_init", .lambda nuListenerBody])) ∧
    BackwardAdminReflection.WeakBackwardOutcome N
      (rhoPar (nameServer "ns_x" "ns_z" "v_init" "ns_seed")
        (.apply "PInput" [.fvar "ns_z", .lambda seedListenerBody])) ∧
    BackwardAdminReflection.WeakBackwardOutcome N
      (encode (.replicate xr yr Pr) n v)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro P0 P1 h hrf hsafe n0 v0
    exact Mettapedia.Languages.ProcessCalculi.PiCalculus.EncodingMorphism.prop4_forward
      (N := N) h hrf hsafe n0 v0
  · intro src tgt hsrc hstep
    exact
      BackwardAdminReflection.weak_backward_reflection_oneStep_encodedSC
        (N := N) (src := src) (tgt := tgt) hsrc hstep
  · intro src tgt hsrc hstep
    exact
      BackwardAdminReflection.weak_backward_reflection_star_encodedSC_partition
        (N := N) (src := src) (tgt := tgt) hsrc hstep
  · exact calculus_correspondence_nonRF_admin_package_fresh_umbrella
      (N := N) x P nuListenerBody seedListenerBody xr yr Pr n v hfresh

/-- Forward RF correspondence clause used by the pre-OSLF calculus package. -/
abbrev CalcRFForwardClause (N : Finset String) : Prop :=
  ∀ {P0 P1 : Process},
    (h : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.MultiStepRF P0 P1) →
    (hrf : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.RestrictionFree P0) →
    (hsafe : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.MultiCommSafe h) →
    ∀ n0 v0,
    ∃ T,
      Nonempty
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.ReducesStar
          (encode P0 n0 v0) T) ∧
      Mettapedia.Languages.ProcessCalculi.PiCalculus.WeakRestrictedBisim N T (encode P1 n0 v0)

/-- One-step backward-outcome clause used by the pre-OSLF calculus package. -/
abbrev CalcBackwardOneStepOutcomeClause (N : Finset String) : Prop :=
  ∀ {src tgt : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern},
    BackwardAdminReflection.EncodedSCStepSource N src →
    Nonempty
      (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerived src tgt) →
    BackwardAdminReflection.WeakBackwardOutcome N src

/-- Star-level backward partition clause used by the pre-OSLF calculus package. -/
abbrev CalcBackwardStarPartitionClause (N : Finset String) : Prop :=
  ∀ {src tgt : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern},
    BackwardAdminReflection.EncodedSCStepSource N src →
    Nonempty
      (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar src tgt) →
    (∃ tgt' canon,
      Nonempty
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar src tgt') ∧
      BackwardAdminReflection.AdminCanonicalTarget src canon ∧
      Mettapedia.Languages.ProcessCalculi.PiCalculus.WeakRestrictedBisimD N tgt' canon)
    ∨
    (∃ P0 P1 n0 v0 tgt',
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence src (encode P0 n0 v0) ∧
      Nonempty (P0 ⇝ P1) ∧
      Nonempty
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar (encode P0 n0 v0) tgt') ∧
      Mettapedia.Languages.ProcessCalculi.PiCalculus.WeakRestrictedBisimD N tgt' (encode P1 n0 v0))

/-- Trace-sensitive + target-sensitive star-level backward decomposition clause
used by the canonical pre-OSLF calculus export. -/
abbrev CalcBackwardStarTraceTargetSensitiveClause (N : Finset String) : Prop :=
  ∀ {src tgt : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern},
    BackwardAdminReflection.EncodedSCStepSource N src →
    Nonempty
      (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar src tgt) →
    src = tgt
    ∨
    (∃ mid,
      Nonempty
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerived src mid) ∧
      Nonempty
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar mid tgt) ∧
      ((∃ tgt' canon,
        Nonempty
          (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar src tgt') ∧
        BackwardAdminReflection.AdminCanonicalTarget src canon ∧
        Mettapedia.Languages.ProcessCalculi.PiCalculus.WeakRestrictedBisimD N tgt' canon)
      ∨
      (Nonempty (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces src mid) ∧
        ∃ P0 P1 n0 v0 tgt',
          Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence src (encode P0 n0 v0) ∧
          Nonempty (P0 ⇝ P1) ∧
          Nonempty
            (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar (encode P0 n0 v0) tgt') ∧
          Mettapedia.Languages.ProcessCalculi.PiCalculus.WeakRestrictedBisimD N tgt' (encode P1 n0 v0))))

/-- RF multi-step trace reflection clause: admin-progress or RF trace branch. -/
abbrev CalcBackwardRFTraceClause (N : Finset String) : Prop :=
  ∀ {src : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern},
    BackwardAdminReflection.EncodedRFTraceSource N src →
      (∃ tgt canon,
        Nonempty
          (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar src tgt) ∧
        BackwardAdminReflection.AdminCanonicalTarget src canon ∧
        Mettapedia.Languages.ProcessCalculi.PiCalculus.WeakRestrictedBisimD N tgt canon)
      ∨
      (∃ P Q n v T,
        src = encode P n v ∧
        Nonempty (Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.MultiStepRF P Q) ∧
        Nonempty
          (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar src T) ∧
        Mettapedia.Languages.ProcessCalculi.PiCalculus.WeakRestrictedBisimD N T (encode Q n v))

/-- Freshness-threaded non-RF admin correspondence clause used by the pre-OSLF
calculus package. -/
abbrev CalcNonRFAdminFreshClause
    (N : Finset String)
    (x : Name) (P : Process)
    (nuListenerBody seedListenerBody : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (xr yr : Name) (Pr : Process) (n v : String)
    (_hfresh : EncodingFresh P) : Prop :=
  ((∃ Trep, Nonempty ((encode (.replicate xr yr Pr) n v) ⇝ᵈ* Trep) ∧
    Trep ≈ᵈ{N}
      (rhoPar
        (rhoInput (piNameToRhoName xr) yr (encode Pr (n ++ "_rep") v))
        (encode (.replicate xr yr Pr) n v))) ∧
  (∃ Tnu Tseed TrepNu,
    fullEncode (.nu x P) =
      rhoPar (encode (.nu x P) "n_init" "v_init")
        (nameServer "ns_x" "ns_z" "v_init" "ns_seed") ∧
    Nonempty
      ((.collection .hashBag
        [rhoPar (encode (.nu x P) "n_init" "v_init")
           (.apply "PInput" [.fvar "v_init", .lambda nuListenerBody]),
         rhoPar (nameServer "ns_x" "ns_z" "v_init" "ns_seed")
           (.apply "PInput" [.fvar "ns_z", .lambda seedListenerBody]),
         encode (.replicate "ns_x" "_drop" .nil) "n_init" "v_init"] none) ⇝ᵈ*
        (.collection .hashBag [Tnu, Tseed, TrepNu] none)) ∧
    (.collection .hashBag [Tnu, Tseed] none ≡
      .collection .hashBag [Tseed, Tnu] none) ∧
    WeakRestrictedBisimD N Tnu
      (.collection .hashBag
        [Mettapedia.OSLF.MeTTaIL.Substitution.commSubst nuListenerBody (.fvar "n_init"),
         rhoInput (.fvar "n_init") x (encode P ("n_init" ++ "_" ++ "n_init") "v_init")] none) ∧
    WeakRestrictedBisimD N Tseed
      (.collection .hashBag
        [Mettapedia.OSLF.MeTTaIL.Substitution.commSubst seedListenerBody (.apply "PDrop" [.fvar "ns_seed"]),
         rhoReplicate (Mettapedia.Languages.ProcessCalculi.PiCalculus.nameServerBody "ns_x" "ns_z" "v_init"),
         dropOperation "ns_x"] none) ∧
    WeakRestrictedBisimD N TrepNu
      (rhoPar
        (rhoInput (piNameToRhoName "ns_x") "_drop" (encode .nil ("n_init" ++ "_rep") "v_init"))
        (encode (.replicate "ns_x" "_drop" .nil) "n_init" "v_init"))) ∧
  BackwardAdminReflection.WeakBackwardOutcome N
    (rhoPar (encode (.nu x P) "n_init" "v_init")
      (.apply "PInput" [.fvar "v_init", .lambda nuListenerBody])) ∧
  BackwardAdminReflection.WeakBackwardOutcome N
    (rhoPar (nameServer "ns_x" "ns_z" "v_init" "ns_seed")
      (.apply "PInput" [.fvar "ns_z", .lambda seedListenerBody])) ∧
  BackwardAdminReflection.WeakBackwardOutcome N
    (encode (.replicate xr yr Pr) n v))

/-- User-observation disciplined non-RF admin umbrella: adds reserved-name
disjointness for the full-encode machinery. -/
theorem nonRF_admin_correspondence_umbrella_fresh_userObs
    {N : Finset String}
    (x : Name) (P : Process)
    (nuListenerBody seedListenerBody : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (xr yr : Name) (Pr : Process) (n v : String)
    (hobs : N ⊆ P.freeNames)
    (hfresh : EncodingFresh P) :
    Disjoint N fullEncodeReservedNames ∧
    CalcNonRFAdminFreshClause N x P nuListenerBody seedListenerBody xr yr Pr n v hfresh := by
  rcases
      (BackwardAdminReflection.full_nonRF_admin_correspondence_bidir_fresh_userObs
        (N := N) x P nuListenerBody seedListenerBody xr yr Pr n v hobs hfresh) with
    ⟨hdisj, hrep, hcombo, hnuOut, hseedOut, hrepOut⟩
  exact ⟨hdisj, ⟨hrep, hcombo, hnuOut, hseedOut, hrepOut⟩⟩

/-- Record-form pre-OSLF calculus correspondence package. This gives a stable API
surface for downstream consumers without unpacking deep conjunctions. -/
structure CalcPreludeCorrespondencePackage
    (N : Finset String)
    (x : Name) (P : Process)
    (nuListenerBody seedListenerBody : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (xr yr : Name) (Pr : Process) (n v : String)
    (hfresh : EncodingFresh P) : Prop where
  forward_rf : CalcRFForwardClause N
  backward_one_step : CalcBackwardOneStepOutcomeClause N
  backward_star_partition : CalcBackwardStarPartitionClause N
  nonRF_admin_fresh :
    CalcNonRFAdminFreshClause N x P nuListenerBody seedListenerBody xr yr Pr n v hfresh

/-- User-observation disciplined record package: adds reserved-name disjointness
to the pre-OSLF correspondence package without exposing giant conjunctions. -/
structure CalcPreludeUserObsPackage
    (N : Finset String)
    (x : Name) (P : Process)
    (nuListenerBody seedListenerBody : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (xr yr : Name) (Pr : Process) (n v : String)
    (hfresh : EncodingFresh P) : Prop where
  disjoint_reserved : Disjoint N fullEncodeReservedNames
  prelude :
    CalcPreludeCorrespondencePackage N x P nuListenerBody seedListenerBody xr yr Pr n v hfresh

/-- Canonical pre-OSLF calculus package:
user-observation disciplined correspondence package plus trace-sensitive
target-sensitive star-level backward decomposition. -/
structure CalcPreludeCanonicalPackage
    (N : Finset String)
    (x : Name) (P : Process)
    (nuListenerBody seedListenerBody : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (xr yr : Name) (Pr : Process) (n v : String)
    (hfresh : EncodingFresh P) : Prop where
  userObs :
    CalcPreludeUserObsPackage N x P nuListenerBody seedListenerBody xr yr Pr n v hfresh
  backward_star_trace_target_sensitive :
    CalcBackwardStarTraceTargetSensitiveClause N
  backward_rf_trace :
    CalcBackwardRFTraceClause N

/-- Constructor theorem for the record-form pre-OSLF correspondence package,
instantiated from `calculus_correspondence_prelude_complete_package_umbrella`. -/
theorem calculus_correspondence_prelude_complete_package_struct
    {N : Finset String}
    (x : Name) (P : Process)
    (nuListenerBody seedListenerBody : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (xr yr : Name) (Pr : Process) (n v : String)
    (hfresh : EncodingFresh P) :
    CalcPreludeCorrespondencePackage N x P nuListenerBody seedListenerBody xr yr Pr n v hfresh := by
  have hpkg := calculus_correspondence_prelude_complete_package_umbrella
    (N := N) x P nuListenerBody seedListenerBody xr yr Pr n v hfresh
  exact ⟨hpkg.1, hpkg.2.1, hpkg.2.2.1, hpkg.2.2.2⟩

/-- Observation-set weakening for the freshness-threaded non-RF admin clause in
record form. -/
theorem calcNonRFAdminFreshClause_of_obsSuperset
    {N Nsup : Finset String}
    (hsub : N ⊆ Nsup)
    (x : Name) (P : Process)
    (nuListenerBody seedListenerBody : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (xr yr : Name) (Pr : Process) (n v : String)
    (hfresh : EncodingFresh P) :
    CalcNonRFAdminFreshClause Nsup x P nuListenerBody seedListenerBody xr yr Pr n v hfresh →
    CalcNonRFAdminFreshClause N x P nuListenerBody seedListenerBody xr yr Pr n v hfresh := by
  intro h
  rcases h with ⟨hrep, hcombo, hnuOut, hseedOut, hrepOut⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rcases hrep with ⟨Trep, hstar, hbisim⟩
    exact ⟨Trep, hstar,
      Mettapedia.Languages.ProcessCalculi.PiCalculus.WeakRestrictedBisimD.mono hbisim hsub⟩
  · rcases hcombo with ⟨Tnu, Tseed, TrepNu, hfull, hstar, hswap, hbNu, hbSeed, hbRepNu⟩
    exact ⟨Tnu, Tseed, TrepNu, hfull, hstar, hswap,
      Mettapedia.Languages.ProcessCalculi.PiCalculus.WeakRestrictedBisimD.mono hbNu hsub,
      Mettapedia.Languages.ProcessCalculi.PiCalculus.WeakRestrictedBisimD.mono hbSeed hsub,
      Mettapedia.Languages.ProcessCalculi.PiCalculus.WeakRestrictedBisimD.mono hbRepNu hsub⟩
  · exact
      BackwardAdminReflection.WeakBackwardOutcome.mono
        hnuOut hsub
  · exact
      BackwardAdminReflection.WeakBackwardOutcome.mono
        hseedOut hsub
  · exact
      BackwardAdminReflection.WeakBackwardOutcome.mono
        hrepOut hsub

/-- Observation-set weakening for the record-form pre-OSLF calculus
correspondence package. -/
theorem calculus_correspondence_prelude_complete_package_struct_from_obsSuperset
    {N Nsup : Finset String}
    (hsub : N ⊆ Nsup)
    (x : Name) (P : Process)
    (nuListenerBody seedListenerBody : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (xr yr : Name) (Pr : Process) (n v : String)
    (hfresh : EncodingFresh P) :
    CalcPreludeCorrespondencePackage N x P nuListenerBody seedListenerBody xr yr Pr n v hfresh := by
  let hpkgSup := calculus_correspondence_prelude_complete_package_struct
    (N := Nsup) x P nuListenerBody seedListenerBody xr yr Pr n v hfresh
  refine
    { forward_rf := ?_
      backward_one_step := ?_
      backward_star_partition := ?_
      nonRF_admin_fresh := ?_ }
  · intro P0 P1 h hrf hsafe n0 v0
    rcases hpkgSup.forward_rf h hrf hsafe n0 v0 with ⟨T, hstar, hbisim⟩
    exact ⟨T, hstar,
      Mettapedia.Languages.ProcessCalculi.PiCalculus.WeakRestrictedBisim.mono hbisim hsub⟩
  · intro src tgt hsrc hstep
    have hsrcSup :
        BackwardAdminReflection.EncodedSCStepSource Nsup src :=
      BackwardAdminReflection.EncodedSCStepSource.mono hsrc
    have houtSup := hpkgSup.backward_one_step hsrcSup hstep
    exact
      BackwardAdminReflection.WeakBackwardOutcome.mono
        houtSup hsub
  · intro src tgt hsrc hstep
    have hsrcSup :
        BackwardAdminReflection.EncodedSCStepSource Nsup src :=
      BackwardAdminReflection.EncodedSCStepSource.mono hsrc
    rcases hpkgSup.backward_star_partition hsrcSup hstep with hleft | hright
    · rcases hleft with ⟨tgt', canon, hstar, hcanon, hbisim⟩
      exact Or.inl ⟨tgt', canon, hstar, hcanon,
        Mettapedia.Languages.ProcessCalculi.PiCalculus.WeakRestrictedBisimD.mono hbisim hsub⟩
    · rcases hright with ⟨P0, P1, n0, v0, tgt', hsrcSC, hpi, hstar, hbisim⟩
      exact Or.inr ⟨P0, P1, n0, v0, tgt', hsrcSC, hpi, hstar,
        Mettapedia.Languages.ProcessCalculi.PiCalculus.WeakRestrictedBisimD.mono hbisim hsub⟩
  · exact calcNonRFAdminFreshClause_of_obsSuperset
      (N := N) (Nsup := Nsup) hsub
      x P nuListenerBody seedListenerBody xr yr Pr n v hfresh hpkgSup.nonRF_admin_fresh

/-- OSLF-morphism-shaped prelude wrapper:
extracts the forward-simulation and one-step backward-reflection components in a
pair form aligned with `LanguageMorphism`-style interfaces. -/
theorem calculus_correspondence_prelude_langMorphism_shape
    {N : Finset String}
    (x : Name) (P : Process)
    (nuListenerBody seedListenerBody : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (xr yr : Name) (Pr : Process) (n v : String)
    (hfresh : EncodingFresh P) :
    (∀ {P0 P1 : Process},
      (h : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.MultiStepRF P0 P1) →
      (hrf : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.RestrictionFree P0) →
      (hsafe : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.MultiCommSafe h) →
      ∀ n0 v0,
      ∃ T,
        Nonempty
          (Mettapedia.Languages.ProcessCalculi.RhoCalculus.ReducesStar
            (encode P0 n0 v0) T) ∧
        Mettapedia.Languages.ProcessCalculi.PiCalculus.WeakRestrictedBisim N T (encode P1 n0 v0))
    ∧
    (∀ {src tgt : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern},
      BackwardAdminReflection.EncodedSCStepSource N src →
      Nonempty
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerived src tgt) →
      BackwardAdminReflection.WeakBackwardOutcome N src) := by
  let hpkg := calculus_correspondence_prelude_complete_package_struct
    (N := N) x P nuListenerBody seedListenerBody xr yr Pr n v hfresh
  exact ⟨hpkg.forward_rf, hpkg.backward_one_step⟩

/-- Observation-set weakening for the basic OSLF-morphism-shaped prelude wrapper:
if it holds at `Nsup`, it holds at any subset `N ⊆ Nsup`. -/
theorem calculus_correspondence_prelude_langMorphism_shape_from_obsSuperset
    {N Nsup : Finset String}
    (hsub : N ⊆ Nsup)
    (x : Name) (P : Process)
    (nuListenerBody seedListenerBody : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (xr yr : Name) (Pr : Process) (n v : String)
    (hfresh : EncodingFresh P) :
    (∀ {P0 P1 : Process},
      (h : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.MultiStepRF P0 P1) →
      (hrf : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.RestrictionFree P0) →
      (hsafe : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.MultiCommSafe h) →
      ∀ n0 v0,
      ∃ T,
        Nonempty
          (Mettapedia.Languages.ProcessCalculi.RhoCalculus.ReducesStar
            (encode P0 n0 v0) T) ∧
        Mettapedia.Languages.ProcessCalculi.PiCalculus.WeakRestrictedBisim N T (encode P1 n0 v0))
    ∧
    (∀ {src tgt : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern},
      BackwardAdminReflection.EncodedSCStepSource N src →
      Nonempty
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerived src tgt) →
      BackwardAdminReflection.WeakBackwardOutcome N src) := by
  let hpkg := calculus_correspondence_prelude_complete_package_struct_from_obsSuperset
    (N := N) (Nsup := Nsup) hsub x P nuListenerBody seedListenerBody xr yr Pr n v hfresh
  exact ⟨hpkg.forward_rf, hpkg.backward_one_step⟩

/-- Strengthened OSLF-morphism-shaped prelude wrapper:
extracts forward simulation, one-step backward outcomes, and the
trace-sensitive+target-sensitive star decomposition endpoint. -/
theorem calculus_correspondence_prelude_langMorphism_shape_trace_sensitive
    {N : Finset String}
    (x : Name) (P : Process)
    (nuListenerBody seedListenerBody : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (xr yr : Name) (Pr : Process) (n v : String)
    (hfresh : EncodingFresh P) :
    (∀ {P0 P1 : Process},
      (h : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.MultiStepRF P0 P1) →
      (hrf : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.RestrictionFree P0) →
      (hsafe : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.MultiCommSafe h) →
      ∀ n0 v0,
      ∃ T,
        Nonempty
          (Mettapedia.Languages.ProcessCalculi.RhoCalculus.ReducesStar
            (encode P0 n0 v0) T) ∧
        Mettapedia.Languages.ProcessCalculi.PiCalculus.WeakRestrictedBisim N T (encode P1 n0 v0))
    ∧
    (∀ {src tgt : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern},
      BackwardAdminReflection.EncodedSCStepSource N src →
      Nonempty
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerived src tgt) →
      BackwardAdminReflection.WeakBackwardOutcome N src)
    ∧
    (∀ {src tgt : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern},
      BackwardAdminReflection.EncodedSCStepSource N src →
      Nonempty
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar src tgt) →
      src = tgt
      ∨
      (∃ mid,
        Nonempty
          (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerived src mid) ∧
        Nonempty
          (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar mid tgt) ∧
        ((∃ tgt' canon,
          Nonempty
            (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar src tgt') ∧
          BackwardAdminReflection.AdminCanonicalTarget src canon ∧
          Mettapedia.Languages.ProcessCalculi.PiCalculus.WeakRestrictedBisimD N tgt' canon)
        ∨
        (Nonempty (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces src mid) ∧
          ∃ P0 P1 n0 v0 tgt',
            Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence src (encode P0 n0 v0) ∧
            Nonempty (P0 ⇝ P1) ∧
            Nonempty
              (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar (encode P0 n0 v0) tgt') ∧
            Mettapedia.Languages.ProcessCalculi.PiCalculus.WeakRestrictedBisimD N tgt' (encode P1 n0 v0))))) := by
  let hpkg := calculus_correspondence_prelude_complete_package_struct
    (N := N) x P nuListenerBody seedListenerBody xr yr Pr n v hfresh
  refine ⟨?_, ?_, ?_⟩
  · exact hpkg.forward_rf
  · exact hpkg.backward_one_step
  · intro src tgt hsrc hstep
    exact
      BackwardAdminReflection.weak_backward_reflection_star_encodedSC_partition_trace_sensitive_target_sensitive
        (N := N) (src := src) (tgt := tgt) hsrc hstep

/-- Branch-sensitive OSLF-morphism-shaped prelude wrapper:
extracts forward simulation plus constructor-sensitive one-step and star
backward decomposition endpoints over `EncodedSCStepSource`. -/
theorem calculus_correspondence_prelude_langMorphism_shape_branch_sensitive
    {N : Finset String}
    (x : Name) (P : Process)
    (nuListenerBody seedListenerBody : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (xr yr : Name) (Pr : Process) (n v : String)
    (hfresh : EncodingFresh P) :
    (∀ {P0 P1 : Process},
      (h : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.MultiStepRF P0 P1) →
      (hrf : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.RestrictionFree P0) →
      (hsafe : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.MultiCommSafe h) →
      ∀ n0 v0,
      ∃ T,
        Nonempty
          (Mettapedia.Languages.ProcessCalculi.RhoCalculus.ReducesStar
            (encode P0 n0 v0) T) ∧
        Mettapedia.Languages.ProcessCalculi.PiCalculus.WeakRestrictedBisim N T (encode P1 n0 v0))
    ∧
    (∀ {src tgt : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern},
      BackwardAdminReflection.EncodedSCStepSource N src →
      Nonempty
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerived src tgt) →
      (∃ tgt' canon,
        Nonempty
          (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar src tgt') ∧
        BackwardAdminReflection.AdminCanonicalTarget src canon ∧
        Mettapedia.Languages.ProcessCalculi.PiCalculus.WeakRestrictedBisimD N tgt' canon)
      ∨
      (Nonempty (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces src tgt) ∧
        ∃ P0 P1 n0 v0 tgt',
          Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence src (encode P0 n0 v0) ∧
          Nonempty (P0 ⇝ P1) ∧
          Nonempty
            (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar (encode P0 n0 v0) tgt') ∧
          Mettapedia.Languages.ProcessCalculi.PiCalculus.WeakRestrictedBisimD N tgt' (encode P1 n0 v0)))
    ∧
    (∀ {src tgt : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern},
      BackwardAdminReflection.EncodedSCStepSource N src →
      Nonempty
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar src tgt) →
      (∃ tgt' canon,
        Nonempty
          (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar src tgt') ∧
        BackwardAdminReflection.AdminCanonicalTarget src canon ∧
        Mettapedia.Languages.ProcessCalculi.PiCalculus.WeakRestrictedBisimD N tgt' canon)
      ∨
      (src = tgt
        ∨
        (∃ mid,
          Nonempty
            (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerived src mid) ∧
          Nonempty
            (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar mid tgt) ∧
          (Nonempty (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces src mid) ∧
            ∃ P0 P1 n0 v0 tgt',
              Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence src (encode P0 n0 v0) ∧
              Nonempty (P0 ⇝ P1) ∧
              Nonempty
                (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar (encode P0 n0 v0) tgt') ∧
              Mettapedia.Languages.ProcessCalculi.PiCalculus.WeakRestrictedBisimD N tgt' (encode P1 n0 v0))))) := by
  let hpkg := calculus_correspondence_prelude_complete_package_struct
    (N := N) x P nuListenerBody seedListenerBody xr yr Pr n v hfresh
  refine ⟨?_, ?_, ?_⟩
  · exact hpkg.forward_rf
  · intro src tgt hsrc hstep
    exact
      BackwardAdminReflection.weak_backward_reflection_step_encodedSC_branch_sensitive
        (N := N) (src := src) (tgt := tgt) hsrc hstep
  · intro src tgt hsrc hstep
    exact
      BackwardAdminReflection.weak_backward_reflection_star_encodedSC_branch_sensitive
        (N := N) (src := src) (tgt := tgt) hsrc hstep

/-- Branch-sensitive OSLF-morphism-shaped prelude wrapper with outcome endpoint:
extracts forward simulation, constructor-sensitive one-step decomposition, and
the star-indexed outcome witness. -/
theorem calculus_correspondence_prelude_langMorphism_shape_branch_sensitive_outcome
    {N : Finset String}
    (x : Name) (P : Process)
    (nuListenerBody seedListenerBody : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (xr yr : Name) (Pr : Process) (n v : String)
    (hfresh : EncodingFresh P) :
    (∀ {P0 P1 : Process},
      (h : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.MultiStepRF P0 P1) →
      (hrf : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.RestrictionFree P0) →
      (hsafe : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.MultiCommSafe h) →
      ∀ n0 v0,
      ∃ T,
        Nonempty
          (Mettapedia.Languages.ProcessCalculi.RhoCalculus.ReducesStar
            (encode P0 n0 v0) T) ∧
        Mettapedia.Languages.ProcessCalculi.PiCalculus.WeakRestrictedBisim N T (encode P1 n0 v0))
    ∧
    (∀ {src tgt : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern},
      BackwardAdminReflection.EncodedSCStepSource N src →
      Nonempty
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerived src tgt) →
      (∃ tgt' canon,
        Nonempty
          (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar src tgt') ∧
        BackwardAdminReflection.AdminCanonicalTarget src canon ∧
        Mettapedia.Languages.ProcessCalculi.PiCalculus.WeakRestrictedBisimD N tgt' canon)
      ∨
      (Nonempty (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces src tgt) ∧
        ∃ P0 P1 n0 v0 tgt',
          Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence src (encode P0 n0 v0) ∧
          Nonempty (P0 ⇝ P1) ∧
          Nonempty
            (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar (encode P0 n0 v0) tgt') ∧
          Mettapedia.Languages.ProcessCalculi.PiCalculus.WeakRestrictedBisimD N tgt' (encode P1 n0 v0)))
    ∧
    (∀ {src tgt : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern},
      BackwardAdminReflection.EncodedSCStepSource N src →
      Nonempty
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar src tgt) →
      BackwardAdminReflection.WeakBackwardOutcome N src) := by
  let hpkg := calculus_correspondence_prelude_complete_package_struct
    (N := N) x P nuListenerBody seedListenerBody xr yr Pr n v hfresh
  refine ⟨?_, ?_, ?_⟩
  · exact hpkg.forward_rf
  · intro src tgt hsrc hstep
    exact
      BackwardAdminReflection.weak_backward_reflection_step_encodedSC_branch_sensitive
        (N := N) (src := src) (tgt := tgt) hsrc hstep
  · intro src tgt hsrc hstep
    exact
      BackwardAdminReflection.weak_backward_reflection_star_encodedSC_from_branch_sensitive
        (N := N) (src := src) (tgt := tgt) hsrc hstep

/-- Observation-set weakening for the branch-sensitive morphism-shaped prelude
wrapper: if the package holds at `Nsup`, it holds at any subset `N ⊆ Nsup`. -/
theorem calculus_correspondence_prelude_langMorphism_shape_branch_sensitive_from_obsSuperset
    {N Nsup : Finset String}
    (hsub : N ⊆ Nsup)
    (x : Name) (P : Process)
    (nuListenerBody seedListenerBody : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (xr yr : Name) (Pr : Process) (n v : String)
    (hfresh : EncodingFresh P) :
    (∀ {P0 P1 : Process},
      (h : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.MultiStepRF P0 P1) →
      (hrf : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.RestrictionFree P0) →
      (hsafe : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.MultiCommSafe h) →
      ∀ n0 v0,
      ∃ T,
        Nonempty
          (Mettapedia.Languages.ProcessCalculi.RhoCalculus.ReducesStar
            (encode P0 n0 v0) T) ∧
        Mettapedia.Languages.ProcessCalculi.PiCalculus.WeakRestrictedBisim N T (encode P1 n0 v0))
    ∧
    (∀ {src tgt : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern},
      BackwardAdminReflection.EncodedSCStepSource N src →
      Nonempty
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerived src tgt) →
      (∃ tgt' canon,
        Nonempty
          (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar src tgt') ∧
        BackwardAdminReflection.AdminCanonicalTarget src canon ∧
        Mettapedia.Languages.ProcessCalculi.PiCalculus.WeakRestrictedBisimD N tgt' canon)
      ∨
      (Nonempty (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces src tgt) ∧
        ∃ P0 P1 n0 v0 tgt',
          Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence src (encode P0 n0 v0) ∧
          Nonempty (P0 ⇝ P1) ∧
          Nonempty
            (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar (encode P0 n0 v0) tgt') ∧
          Mettapedia.Languages.ProcessCalculi.PiCalculus.WeakRestrictedBisimD N tgt' (encode P1 n0 v0)))
    ∧
    (∀ {src tgt : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern},
      BackwardAdminReflection.EncodedSCStepSource N src →
      Nonempty
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar src tgt) →
      (∃ tgt' canon,
        Nonempty
          (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar src tgt') ∧
        BackwardAdminReflection.AdminCanonicalTarget src canon ∧
        Mettapedia.Languages.ProcessCalculi.PiCalculus.WeakRestrictedBisimD N tgt' canon)
      ∨
      (src = tgt
        ∨
        (∃ mid,
          Nonempty
            (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerived src mid) ∧
          Nonempty
            (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar mid tgt) ∧
          (Nonempty (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces src mid) ∧
            ∃ P0 P1 n0 v0 tgt',
              Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence src (encode P0 n0 v0) ∧
              Nonempty (P0 ⇝ P1) ∧
              Nonempty
                (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar (encode P0 n0 v0) tgt') ∧
              Mettapedia.Languages.ProcessCalculi.PiCalculus.WeakRestrictedBisimD N tgt' (encode P1 n0 v0))))) := by
  have hPkgSup :=
    calculus_correspondence_prelude_langMorphism_shape_branch_sensitive
      (N := Nsup) x P nuListenerBody seedListenerBody xr yr Pr n v hfresh
  refine ⟨?_, ?_, ?_⟩
  · intro P0 P1 h hrf hsafe n0 v0
    rcases hPkgSup.1 h hrf hsafe n0 v0 with ⟨T, hstar, hbisim⟩
    exact ⟨T, hstar, Mettapedia.Languages.ProcessCalculi.PiCalculus.WeakRestrictedBisim.mono hbisim hsub⟩
  · intro src tgt hsrc hstep
    have hsrcSup :
        BackwardAdminReflection.EncodedSCStepSource Nsup src :=
      BackwardAdminReflection.EncodedSCStepSource.mono hsrc
    exact
      BackwardAdminReflection.weak_backward_reflection_step_encodedSC_branch_sensitive_of_obsSuperset
        (N := N) (Nsup := Nsup) (src := src) (tgt := tgt) hsub hsrcSup hstep
  · intro src tgt hsrc hstep
    have hsrcSup :
        BackwardAdminReflection.EncodedSCStepSource Nsup src :=
      BackwardAdminReflection.EncodedSCStepSource.mono hsrc
    exact
      BackwardAdminReflection.weak_backward_reflection_star_encodedSC_branch_sensitive_of_obsSuperset
        (N := N) (Nsup := Nsup) (src := src) (tgt := tgt) hsub hsrcSup hstep

/-- Observation-set weakening for the branch-sensitive prelude wrapper with
outcome endpoint. -/
theorem calculus_correspondence_prelude_langMorphism_shape_branch_sensitive_outcome_from_obsSuperset
    {N Nsup : Finset String}
    (hsub : N ⊆ Nsup)
    (x : Name) (P : Process)
    (nuListenerBody seedListenerBody : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (xr yr : Name) (Pr : Process) (n v : String)
    (hfresh : EncodingFresh P) :
    (∀ {P0 P1 : Process},
      (h : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.MultiStepRF P0 P1) →
      (hrf : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.RestrictionFree P0) →
      (hsafe : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.MultiCommSafe h) →
      ∀ n0 v0,
      ∃ T,
        Nonempty
          (Mettapedia.Languages.ProcessCalculi.RhoCalculus.ReducesStar
            (encode P0 n0 v0) T) ∧
        Mettapedia.Languages.ProcessCalculi.PiCalculus.WeakRestrictedBisim N T (encode P1 n0 v0))
    ∧
    (∀ {src tgt : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern},
      BackwardAdminReflection.EncodedSCStepSource N src →
      Nonempty
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerived src tgt) →
      (∃ tgt' canon,
        Nonempty
          (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar src tgt') ∧
        BackwardAdminReflection.AdminCanonicalTarget src canon ∧
        Mettapedia.Languages.ProcessCalculi.PiCalculus.WeakRestrictedBisimD N tgt' canon)
      ∨
      (Nonempty (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces src tgt) ∧
        ∃ P0 P1 n0 v0 tgt',
          Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence src (encode P0 n0 v0) ∧
          Nonempty (P0 ⇝ P1) ∧
          Nonempty
            (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar (encode P0 n0 v0) tgt') ∧
          Mettapedia.Languages.ProcessCalculi.PiCalculus.WeakRestrictedBisimD N tgt' (encode P1 n0 v0)))
    ∧
    (∀ {src tgt : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern},
      BackwardAdminReflection.EncodedSCStepSource N src →
      Nonempty
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar src tgt) →
      BackwardAdminReflection.WeakBackwardOutcome N src) := by
  have hPkgSup :=
    calculus_correspondence_prelude_langMorphism_shape_branch_sensitive_outcome
      (N := Nsup) x P nuListenerBody seedListenerBody xr yr Pr n v hfresh
  refine ⟨?_, ?_, ?_⟩
  · intro P0 P1 h hrf hsafe n0 v0
    rcases hPkgSup.1 h hrf hsafe n0 v0 with ⟨T, hstar, hbisim⟩
    exact ⟨T, hstar, Mettapedia.Languages.ProcessCalculi.PiCalculus.WeakRestrictedBisim.mono hbisim hsub⟩
  · intro src tgt hsrc hstep
    have hsrcSup :
        BackwardAdminReflection.EncodedSCStepSource Nsup src :=
      BackwardAdminReflection.EncodedSCStepSource.mono hsrc
    exact
      BackwardAdminReflection.weak_backward_reflection_step_encodedSC_branch_sensitive_of_obsSuperset
        (N := N) (Nsup := Nsup) (src := src) (tgt := tgt) hsub hsrcSup hstep
  · intro src tgt hsrc hstep
    have hsrcSup :
        BackwardAdminReflection.EncodedSCStepSource Nsup src :=
      BackwardAdminReflection.EncodedSCStepSource.mono hsrc
    exact
      BackwardAdminReflection.weak_backward_reflection_star_encodedSC_from_branch_sensitive_of_obsSuperset
        (N := N) (Nsup := Nsup) (src := src) (tgt := tgt) hsub hsrcSup hstep

/-- Observation-set weakening for the strengthened morphism-shaped prelude
wrapper: if the package holds at `Nsup`, it holds at any subset `N ⊆ Nsup`. -/
theorem calculus_correspondence_prelude_langMorphism_shape_trace_sensitive_from_obsSuperset
    {N Nsup : Finset String}
    (hsub : N ⊆ Nsup)
    (x : Name) (P : Process)
    (nuListenerBody seedListenerBody : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (xr yr : Name) (Pr : Process) (n v : String)
    (hfresh : EncodingFresh P) :
    (∀ {P0 P1 : Process},
      (h : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.MultiStepRF P0 P1) →
      (hrf : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.RestrictionFree P0) →
      (hsafe : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.MultiCommSafe h) →
      ∀ n0 v0,
      ∃ T,
        Nonempty
          (Mettapedia.Languages.ProcessCalculi.RhoCalculus.ReducesStar
            (encode P0 n0 v0) T) ∧
        Mettapedia.Languages.ProcessCalculi.PiCalculus.WeakRestrictedBisim N T (encode P1 n0 v0))
    ∧
    (∀ {src tgt : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern},
      BackwardAdminReflection.EncodedSCStepSource N src →
      Nonempty
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerived src tgt) →
      BackwardAdminReflection.WeakBackwardOutcome N src)
    ∧
    (∀ {src tgt : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern},
      BackwardAdminReflection.EncodedSCStepSource N src →
      Nonempty
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar src tgt) →
      src = tgt
      ∨
      (∃ mid,
        Nonempty
          (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerived src mid) ∧
        Nonempty
          (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar mid tgt) ∧
        ((∃ tgt' canon,
          Nonempty
            (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar src tgt') ∧
          BackwardAdminReflection.AdminCanonicalTarget src canon ∧
          Mettapedia.Languages.ProcessCalculi.PiCalculus.WeakRestrictedBisimD N tgt' canon)
        ∨
        (Nonempty (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces src mid) ∧
          ∃ P0 P1 n0 v0 tgt',
            Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence src (encode P0 n0 v0) ∧
            Nonempty (P0 ⇝ P1) ∧
            Nonempty
              (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar (encode P0 n0 v0) tgt') ∧
            Mettapedia.Languages.ProcessCalculi.PiCalculus.WeakRestrictedBisimD N tgt' (encode P1 n0 v0))))) := by
  have hPkgSup :=
    calculus_correspondence_prelude_langMorphism_shape_trace_sensitive
      (N := Nsup) x P nuListenerBody seedListenerBody xr yr Pr n v hfresh
  refine ⟨?_, ?_, ?_⟩
  · intro P0 P1 h hrf hsafe n0 v0
    rcases hPkgSup.1 h hrf hsafe n0 v0 with ⟨T, hstar, hbisim⟩
    exact ⟨T, hstar, Mettapedia.Languages.ProcessCalculi.PiCalculus.WeakRestrictedBisim.mono hbisim hsub⟩
  · intro src tgt hsrc hstep
    have hsrcSup :
        BackwardAdminReflection.EncodedSCStepSource Nsup src :=
      BackwardAdminReflection.EncodedSCStepSource.mono hsrc
    have houtSup := hPkgSup.2.1 hsrcSup hstep
    exact BackwardAdminReflection.WeakBackwardOutcome.mono
      houtSup hsub
  · intro src tgt hsrc hstep
    have hsrcSup :
        BackwardAdminReflection.EncodedSCStepSource Nsup src :=
      BackwardAdminReflection.EncodedSCStepSource.mono hsrc
    rcases hPkgSup.2.2 hsrcSup hstep with hrefl | hstepd
    · exact Or.inl hrefl
    · rcases hstepd with ⟨mid, hmid, hrest, hpart⟩
      rcases hpart with hleft | hright
      · rcases hleft with ⟨tgt', canon, hstar, hcanon, hbisim⟩
        exact Or.inr ⟨mid, hmid, hrest, Or.inl
          ⟨tgt', canon, hstar, hcanon,
            Mettapedia.Languages.ProcessCalculi.PiCalculus.WeakRestrictedBisimD.mono hbisim hsub⟩⟩
      · rcases hright with ⟨hcore, P0, P1, n0, v0, tgt', hsrcSC, hpi, hstar, hbisim⟩
        exact Or.inr ⟨mid, hmid, hrest, Or.inr
          ⟨hcore, P0, P1, n0, v0, tgt', hsrcSC, hpi, hstar,
            Mettapedia.Languages.ProcessCalculi.PiCalculus.WeakRestrictedBisimD.mono hbisim hsub⟩⟩

/-- User-observation disciplined prelude package:
if observations are restricted to user free names (`N ⊆ fn(P)`), then
freshness excludes all reserved full-encode channels/seeds from `N`, and the
full pre-OSLF calculus correspondence package still holds. -/
theorem calculus_correspondence_prelude_complete_package_userObs
    {N : Finset String}
    (x : Name) (P : Process)
    (nuListenerBody seedListenerBody : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (xr yr : Name) (Pr : Process) (n v : String)
    (hobs : N ⊆ P.freeNames)
    (hfresh : EncodingFresh P) :
    Disjoint N fullEncodeReservedNames ∧
    ((∀ {P0 P1 : Process},
      (h : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.MultiStepRF P0 P1) →
      (hrf : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.RestrictionFree P0) →
      (hsafe : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.MultiCommSafe h) →
      ∀ n0 v0,
      ∃ T,
        Nonempty
          (Mettapedia.Languages.ProcessCalculi.RhoCalculus.ReducesStar
            (encode P0 n0 v0) T) ∧
        Mettapedia.Languages.ProcessCalculi.PiCalculus.WeakRestrictedBisim N T (encode P1 n0 v0))
    ∧
    (∀ {src tgt : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern},
      BackwardAdminReflection.EncodedSCStepSource N src →
      Nonempty
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerived src tgt) →
      BackwardAdminReflection.WeakBackwardOutcome N src)
    ∧
    (∀ {src tgt : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern},
      BackwardAdminReflection.EncodedSCStepSource N src →
      Nonempty
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar src tgt) →
      (∃ tgt' canon,
        Nonempty
          (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar src tgt') ∧
        BackwardAdminReflection.AdminCanonicalTarget src canon ∧
        Mettapedia.Languages.ProcessCalculi.PiCalculus.WeakRestrictedBisimD N tgt' canon)
      ∨
      (∃ P0 P1 n0 v0 tgt',
        Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence src (encode P0 n0 v0) ∧
        Nonempty (P0 ⇝ P1) ∧
        Nonempty
          (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar (encode P0 n0 v0) tgt') ∧
        Mettapedia.Languages.ProcessCalculi.PiCalculus.WeakRestrictedBisimD N tgt' (encode P1 n0 v0)))
    ∧
    ((∃ Trep, Nonempty ((encode (.replicate xr yr Pr) n v) ⇝ᵈ* Trep) ∧
      Trep ≈ᵈ{N}
        (rhoPar
          (rhoInput (piNameToRhoName xr) yr (encode Pr (n ++ "_rep") v))
          (encode (.replicate xr yr Pr) n v))) ∧
    (∃ Tnu Tseed TrepNu,
      fullEncode (.nu x P) =
        rhoPar (encode (.nu x P) "n_init" "v_init")
          (nameServer "ns_x" "ns_z" "v_init" "ns_seed") ∧
      Nonempty
        ((.collection .hashBag
          [rhoPar (encode (.nu x P) "n_init" "v_init")
             (.apply "PInput" [.fvar "v_init", .lambda nuListenerBody]),
           rhoPar (nameServer "ns_x" "ns_z" "v_init" "ns_seed")
             (.apply "PInput" [.fvar "ns_z", .lambda seedListenerBody]),
           encode (.replicate "ns_x" "_drop" .nil) "n_init" "v_init"] none) ⇝ᵈ*
          (.collection .hashBag [Tnu, Tseed, TrepNu] none)) ∧
      (.collection .hashBag [Tnu, Tseed] none ≡
        .collection .hashBag [Tseed, Tnu] none) ∧
      WeakRestrictedBisimD N Tnu
        (.collection .hashBag
          [Mettapedia.OSLF.MeTTaIL.Substitution.commSubst nuListenerBody (.fvar "n_init"),
           rhoInput (.fvar "n_init") x (encode P ("n_init" ++ "_" ++ "n_init") "v_init")] none) ∧
      WeakRestrictedBisimD N Tseed
        (.collection .hashBag
          [Mettapedia.OSLF.MeTTaIL.Substitution.commSubst seedListenerBody (.apply "PDrop" [.fvar "ns_seed"]),
           rhoReplicate (Mettapedia.Languages.ProcessCalculi.PiCalculus.nameServerBody "ns_x" "ns_z" "v_init"),
           dropOperation "ns_x"] none) ∧
      WeakRestrictedBisimD N TrepNu
        (rhoPar
          (rhoInput (piNameToRhoName "ns_x") "_drop" (encode .nil ("n_init" ++ "_rep") "v_init"))
          (encode (.replicate "ns_x" "_drop" .nil) "n_init" "v_init"))) ∧
    BackwardAdminReflection.WeakBackwardOutcome N
      (rhoPar (encode (.nu x P) "n_init" "v_init")
        (.apply "PInput" [.fvar "v_init", .lambda nuListenerBody])) ∧
    BackwardAdminReflection.WeakBackwardOutcome N
      (rhoPar (nameServer "ns_x" "ns_z" "v_init" "ns_seed")
        (.apply "PInput" [.fvar "ns_z", .lambda seedListenerBody])) ∧
    BackwardAdminReflection.WeakBackwardOutcome N
      (encode (.replicate xr yr Pr) n v))) := by
  refine ⟨obs_disjoint_reserved_of_subset_freeNames (P := P) (N := N) hobs hfresh, ?_⟩
  exact calculus_correspondence_prelude_complete_package_umbrella
    (N := N) x P nuListenerBody seedListenerBody xr yr Pr n v hfresh

/-- Record-form user-observation disciplined prelude package:
bundles reserved-name disjointness with the full pre-OSLF correspondence
package in a single API object. -/
theorem calculus_correspondence_prelude_complete_package_userObs_struct
    {N : Finset String}
    (x : Name) (P : Process)
    (nuListenerBody seedListenerBody : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (xr yr : Name) (Pr : Process) (n v : String)
    (hobs : N ⊆ P.freeNames)
    (hfresh : EncodingFresh P) :
    CalcPreludeUserObsPackage N x P nuListenerBody seedListenerBody xr yr Pr n v hfresh := by
  refine ⟨?_, ?_⟩
  · exact obs_disjoint_reserved_of_subset_freeNames (P := P) (N := N) hobs hfresh
  · exact calculus_correspondence_prelude_complete_package_struct
      (N := N) x P nuListenerBody seedListenerBody xr yr Pr n v hfresh

/-- Observation-set weakening for the record-form user-observation disciplined
prelude package. -/
theorem calculus_correspondence_prelude_complete_package_userObs_struct_from_obsSuperset
    {N Nsup : Finset String}
    (hsub : N ⊆ Nsup)
    (x : Name) (P : Process)
    (nuListenerBody seedListenerBody : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (xr yr : Name) (Pr : Process) (n v : String)
    (hobsSup : Nsup ⊆ P.freeNames)
    (hfresh : EncodingFresh P) :
    CalcPreludeUserObsPackage N x P nuListenerBody seedListenerBody xr yr Pr n v hfresh := by
  refine ⟨?_, ?_⟩
  · exact obs_disjoint_reserved_of_subset_freeNames
      (P := P) (N := N) (Set.Subset.trans hsub hobsSup) hfresh
  · exact calculus_correspondence_prelude_complete_package_struct_from_obsSuperset
      (N := N) (Nsup := Nsup) hsub
      x P nuListenerBody seedListenerBody xr yr Pr n v hfresh

/-- Single-entry user-observation + language-morphism-shaped export:
reserved-name disjointness together with the core forward/backward one-step
components from the record package. -/
theorem calculus_correspondence_prelude_userObs_langMorphism_shape
    {N : Finset String}
    (x : Name) (P : Process)
    (nuListenerBody seedListenerBody : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (xr yr : Name) (Pr : Process) (n v : String)
    (hobs : N ⊆ P.freeNames)
    (hfresh : EncodingFresh P) :
    Disjoint N fullEncodeReservedNames ∧
    (∀ {P0 P1 : Process},
      (h : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.MultiStepRF P0 P1) →
      (hrf : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.RestrictionFree P0) →
      (hsafe : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.MultiCommSafe h) →
      ∀ n0 v0,
      ∃ T,
        Nonempty
          (Mettapedia.Languages.ProcessCalculi.RhoCalculus.ReducesStar
            (encode P0 n0 v0) T) ∧
        Mettapedia.Languages.ProcessCalculi.PiCalculus.WeakRestrictedBisim N T (encode P1 n0 v0))
    ∧
    (∀ {src tgt : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern},
      BackwardAdminReflection.EncodedSCStepSource N src →
      Nonempty
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerived src tgt) →
      BackwardAdminReflection.WeakBackwardOutcome N src) := by
  let hpkg := calculus_correspondence_prelude_complete_package_userObs_struct
    (N := N) x P nuListenerBody seedListenerBody xr yr Pr n v hobs hfresh
  exact ⟨hpkg.disjoint_reserved, hpkg.prelude.forward_rf, hpkg.prelude.backward_one_step⟩

/-- Observation-set weakening for the single-entry user-observation
language-morphism-shaped export. -/
theorem calculus_correspondence_prelude_userObs_langMorphism_shape_from_obsSuperset
    {N Nsup : Finset String}
    (hsub : N ⊆ Nsup)
    (x : Name) (P : Process)
    (nuListenerBody seedListenerBody : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (xr yr : Name) (Pr : Process) (n v : String)
    (hobsSup : Nsup ⊆ P.freeNames)
    (hfresh : EncodingFresh P) :
    Disjoint N fullEncodeReservedNames ∧
    (∀ {P0 P1 : Process},
      (h : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.MultiStepRF P0 P1) →
      (hrf : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.RestrictionFree P0) →
      (hsafe : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.MultiCommSafe h) →
      ∀ n0 v0,
      ∃ T,
        Nonempty
          (Mettapedia.Languages.ProcessCalculi.RhoCalculus.ReducesStar
            (encode P0 n0 v0) T) ∧
        Mettapedia.Languages.ProcessCalculi.PiCalculus.WeakRestrictedBisim N T (encode P1 n0 v0))
    ∧
    (∀ {src tgt : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern},
      BackwardAdminReflection.EncodedSCStepSource N src →
      Nonempty
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerived src tgt) →
      BackwardAdminReflection.WeakBackwardOutcome N src) := by
  let hpkg := calculus_correspondence_prelude_complete_package_userObs_struct_from_obsSuperset
    (N := N) (Nsup := Nsup) hsub
    x P nuListenerBody seedListenerBody xr yr Pr n v hobsSup hfresh
  exact ⟨hpkg.disjoint_reserved, hpkg.prelude.forward_rf, hpkg.prelude.backward_one_step⟩

/-- Single strongest pre-OSLF calculus export:
bundles user-observation disciplined correspondence with the trace-sensitive
target-sensitive star-level backward decomposition endpoint. -/
theorem calculus_correspondence_prelude_canonical_package
    {N : Finset String}
    (x : Name) (P : Process)
    (nuListenerBody seedListenerBody : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (xr yr : Name) (Pr : Process) (n v : String)
    (hobs : N ⊆ P.freeNames)
    (hfresh : EncodingFresh P) :
    CalcPreludeCanonicalPackage N x P nuListenerBody seedListenerBody xr yr Pr n v hfresh := by
  refine ⟨?_, ?_, ?_⟩
  · exact calculus_correspondence_prelude_complete_package_userObs_struct
      (N := N) x P nuListenerBody seedListenerBody xr yr Pr n v hobs hfresh
  · intro src tgt hsrc hstep
    exact
      BackwardAdminReflection.weak_backward_reflection_star_encodedSC_partition_trace_sensitive_target_sensitive
        (N := N) (src := src) (tgt := tgt) hsrc hstep
  · intro src hsrc
    exact BackwardAdminReflection.weak_backward_reflection_trace_encodedRF
      (N := N) (src := src) hsrc

/-- Observation-set weakening for the canonical pre-OSLF calculus package:
if the package holds at `Nsup`, it holds at any subset `N ⊆ Nsup`. -/
theorem calculus_correspondence_prelude_canonical_package_from_obsSuperset
    {N Nsup : Finset String}
    (hsub : N ⊆ Nsup)
    (x : Name) (P : Process)
    (nuListenerBody seedListenerBody : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (xr yr : Name) (Pr : Process) (n v : String)
    (hobsSup : Nsup ⊆ P.freeNames)
    (hfresh : EncodingFresh P) :
    CalcPreludeCanonicalPackage N x P nuListenerBody seedListenerBody xr yr Pr n v hfresh := by
  refine ⟨?_, ?_, ?_⟩
  · exact calculus_correspondence_prelude_complete_package_userObs_struct_from_obsSuperset
      (N := N) (Nsup := Nsup) hsub
      x P nuListenerBody seedListenerBody xr yr Pr n v hobsSup hfresh
  · intro src tgt hsrc hstep
    have hsrcSup :
        BackwardAdminReflection.EncodedSCStepSource Nsup src :=
      BackwardAdminReflection.EncodedSCStepSource.mono hsrc
    exact
      BackwardAdminReflection.weak_backward_reflection_star_encodedSC_partition_trace_sensitive_target_sensitive_of_obsSuperset
        (N := N) (Nsup := Nsup) hsub (src := src) (tgt := tgt) hsrcSup hstep
  · intro src hsrc
    exact BackwardAdminReflection.weak_backward_reflection_trace_encodedRF
      (N := N) (src := src) hsrc

/-- Canonical single-theorem pre-OSLF export (flattened form):
reserved-name disjointness + forward RF + backward one-step outcomes +
trace-sensitive target-sensitive star decomposition + freshness-threaded
non-RF admin correspondence. -/
theorem calculus_correspondence_prelude_canonical_package_flat
    {N : Finset String}
    (x : Name) (P : Process)
    (nuListenerBody seedListenerBody : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (xr yr : Name) (Pr : Process) (n v : String)
    (hobs : N ⊆ P.freeNames)
    (hfresh : EncodingFresh P) :
    Disjoint N fullEncodeReservedNames ∧
    CalcRFForwardClause N ∧
    CalcBackwardOneStepOutcomeClause N ∧
    CalcBackwardStarTraceTargetSensitiveClause N ∧
    CalcBackwardRFTraceClause N ∧
    CalcNonRFAdminFreshClause N x P nuListenerBody seedListenerBody xr yr Pr n v hfresh := by
  let hcanon := calculus_correspondence_prelude_canonical_package
    (N := N) x P nuListenerBody seedListenerBody xr yr Pr n v hobs hfresh
  exact ⟨hcanon.userObs.disjoint_reserved, hcanon.userObs.prelude.forward_rf,
    hcanon.userObs.prelude.backward_one_step,
    hcanon.backward_star_trace_target_sensitive,
    hcanon.backward_rf_trace,
    hcanon.userObs.prelude.nonRF_admin_fresh⟩

/-- Observation-set weakening for the canonical flattened pre-OSLF export. -/
theorem calculus_correspondence_prelude_canonical_package_flat_from_obsSuperset
    {N Nsup : Finset String}
    (hsub : N ⊆ Nsup)
    (x : Name) (P : Process)
    (nuListenerBody seedListenerBody : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (xr yr : Name) (Pr : Process) (n v : String)
    (hobsSup : Nsup ⊆ P.freeNames)
    (hfresh : EncodingFresh P) :
    Disjoint N fullEncodeReservedNames ∧
    CalcRFForwardClause N ∧
    CalcBackwardOneStepOutcomeClause N ∧
    CalcBackwardStarTraceTargetSensitiveClause N ∧
    CalcBackwardRFTraceClause N ∧
    CalcNonRFAdminFreshClause N x P nuListenerBody seedListenerBody xr yr Pr n v hfresh := by
  let hcanon := calculus_correspondence_prelude_canonical_package_from_obsSuperset
    (N := N) (Nsup := Nsup) hsub
    x P nuListenerBody seedListenerBody xr yr Pr n v hobsSup hfresh
  exact ⟨hcanon.userObs.disjoint_reserved, hcanon.userObs.prelude.forward_rf,
    hcanon.userObs.prelude.backward_one_step,
    hcanon.backward_star_trace_target_sensitive,
    hcanon.backward_rf_trace,
    hcanon.userObs.prelude.nonRF_admin_fresh⟩

/-- CI canary for the strongest canonical pre-OSLF export:
instantiates the package on the concrete nil/user-observation-empty baseline. -/
theorem calculus_correspondence_prelude_canonical_package_canary_nil :
    CalcPreludeCanonicalPackage
      (∅ : Finset String)
      "x" .nil rhoNil rhoNil
      "ns_x" "_drop" .nil "n_init" "v_init"
      Mettapedia.Languages.ProcessCalculi.PiCalculus.encodingFresh_nil := by
  exact calculus_correspondence_prelude_canonical_package
    (N := (∅ : Finset String))
    (x := "x")
    (P := .nil)
    (nuListenerBody := rhoNil)
    (seedListenerBody := rhoNil)
    (xr := "ns_x")
    (yr := "_drop")
    (Pr := .nil)
    (n := "n_init")
    (v := "v_init")
    (hobs := by
      intro a ha
      simp at ha)
    (hfresh := Mettapedia.Languages.ProcessCalculi.PiCalculus.encodingFresh_nil)

/-- User-observation hygiene corollary:
under `N ⊆ fn(P)` and `EncodingFresh P`, the seed listener channel `ns_z` is
not observable. -/
theorem userObs_excludes_ns_z_of_encodingFresh
    {N : Finset String} {P : Process}
    (hobs : N ⊆ P.freeNames)
    (hfresh : EncodingFresh P) :
    "ns_z" ∉ N := by
  exact ns_z_notin_obs_of_subset_freeNames (P := P) (N := N) hobs hfresh

/-- User-observation hygiene corollary for `n_init`. -/
theorem userObs_excludes_n_init_of_encodingFresh
    {N : Finset String} {P : Process}
    (hobs : N ⊆ P.freeNames)
    (hfresh : EncodingFresh P) :
    "n_init" ∉ N := by
  exact reserved_notin_obs_of_subset_freeNames
    (P := P) (N := N) (r := "n_init") hobs hfresh (by
      simp [fullEncodeReservedNames])

/-- User-observation hygiene corollary for `v_init`. -/
theorem userObs_excludes_v_init_of_encodingFresh
    {N : Finset String} {P : Process}
    (hobs : N ⊆ P.freeNames)
    (hfresh : EncodingFresh P) :
    "v_init" ∉ N := by
  exact reserved_notin_obs_of_subset_freeNames
    (P := P) (N := N) (r := "v_init") hobs hfresh (by
      simp [fullEncodeReservedNames])

/-- User-observation hygiene corollary for `ns_x`. -/
theorem userObs_excludes_ns_x_of_encodingFresh
    {N : Finset String} {P : Process}
    (hobs : N ⊆ P.freeNames)
    (hfresh : EncodingFresh P) :
    "ns_x" ∉ N := by
  exact reserved_notin_obs_of_subset_freeNames
    (P := P) (N := N) (r := "ns_x") hobs hfresh (by
      simp [fullEncodeReservedNames])

/-- User-observation hygiene (general reserved-name form):
under `N ⊆ fn(P)` and `EncodingFresh P`, any reserved full-encode name is
excluded from observations. -/
theorem userObs_excludes_reserved_name_of_encodingFresh
    {N : Finset String} {P : Process} {r : String}
    (hobs : N ⊆ P.freeNames)
    (hfresh : EncodingFresh P)
    (hr : r ∈ fullEncodeReservedNames) :
    r ∉ N := by
  exact reserved_notin_obs_of_subset_freeNames
    (P := P) (N := N) (r := r) hobs hfresh hr

/-- User-observation hygiene corollary for `ns_seed`. -/
theorem userObs_excludes_ns_seed_of_encodingFresh
    {N : Finset String} {P : Process}
    (hobs : N ⊆ P.freeNames)
    (hfresh : EncodingFresh P) :
    "ns_seed" ∉ N := by
  exact userObs_excludes_reserved_name_of_encodingFresh
    (P := P) (N := N) (r := "ns_seed") hobs hfresh (by
      simp [fullEncodeReservedNames])

/-- Bundled user-observation hygiene result for all concrete reserved
full-encode names/channels. -/
theorem userObs_excludes_all_reserved_of_encodingFresh
    {N : Finset String} {P : Process}
    (hobs : N ⊆ P.freeNames)
    (hfresh : EncodingFresh P) :
    "n_init" ∉ N ∧
    "v_init" ∉ N ∧
    "ns_x" ∉ N ∧
    "ns_z" ∉ N ∧
    "ns_seed" ∉ N := by
  exact ⟨
    userObs_excludes_n_init_of_encodingFresh (N := N) (P := P) hobs hfresh,
    userObs_excludes_v_init_of_encodingFresh (N := N) (P := P) hobs hfresh,
    userObs_excludes_ns_x_of_encodingFresh (N := N) (P := P) hobs hfresh,
    userObs_excludes_ns_z_of_encodingFresh (N := N) (P := P) hobs hfresh,
    userObs_excludes_ns_seed_of_encodingFresh (N := N) (P := P) hobs hfresh
  ⟩

/-- Fully general backward-simulation endpoint (calculus API wrapper):
refl, admin-progress, or reflected π-step branch with explicit head/tail trace. -/
theorem calculus_backward_simulation_full_general
    {N : Finset String} {src tgt : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern}
    (hsrc : BackwardAdminReflection.EncodedSCStepSource N src)
    (hstep :
      Nonempty
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar src tgt)) :
    src = tgt
    ∨
    (∃ tgt' canon,
      Nonempty
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar src tgt') ∧
      BackwardAdminReflection.AdminCanonicalTarget src canon ∧
      Mettapedia.Languages.ProcessCalculi.PiCalculus.WeakRestrictedBisimD N tgt' canon)
    ∨
    (∃ mid,
      Nonempty
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerived src mid) ∧
      Nonempty
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar mid tgt) ∧
      Nonempty (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces src mid) ∧
      ∃ P P' n v tgt',
        Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence src (encode P n v) ∧
        Nonempty (P ⇝ P') ∧
        Nonempty
          (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar
            (encode P n v) tgt') ∧
        Mettapedia.Languages.ProcessCalculi.PiCalculus.WeakRestrictedBisimD N tgt'
          (encode P' n v)) := by
  exact BackwardAdminReflection.weak_backward_full_simulation_encodedSC
    (N := N) (src := src) (tgt := tgt) hsrc hstep

/-- Encoded-source specialization of `calculus_backward_simulation_full_general`. -/
theorem calculus_backward_simulation_full_general_encode
    {N : Finset String} {P : Process} {n v : String}
    {tgt : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern}
    (hsrc : BackwardAdminReflection.EncodedSCStepSource N (encode P n v))
    (hstep :
      Nonempty
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar
          (encode P n v) tgt)) :
    encode P n v = tgt
    ∨
    (∃ tgt' canon,
      Nonempty
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar
          (encode P n v) tgt') ∧
      BackwardAdminReflection.AdminCanonicalTarget (encode P n v) canon ∧
      Mettapedia.Languages.ProcessCalculi.PiCalculus.WeakRestrictedBisimD N tgt' canon)
    ∨
    (∃ mid,
      Nonempty
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerived
          (encode P n v) mid) ∧
      Nonempty
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar
          mid tgt) ∧
      Nonempty
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces (encode P n v) mid) ∧
      ∃ P0 P1 n0 v0 tgt',
        Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence
          (encode P n v) (encode P0 n0 v0) ∧
        Nonempty (P0 ⇝ P1) ∧
        Nonempty
          (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar
            (encode P0 n0 v0) tgt') ∧
        Mettapedia.Languages.ProcessCalculi.PiCalculus.WeakRestrictedBisimD N tgt'
          (encode P1 n0 v0)) := by
  exact BackwardAdminReflection.weak_backward_full_simulation_encode
    (N := N) (P := P) (n := n) (v := v) (tgt := tgt) hsrc hstep

/-- Full encoded-source weak correspondence package:
bundles RF forward simulation and full backward star decomposition in one theorem. -/
theorem calculus_weak_correspondence_full_encode
    {N : Finset String} {P P' : Process} {n v : String}
    {tgt : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern}
    (hforward : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.MultiStepRF P P')
    (hrf : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.RestrictionFree P)
    (hsafe : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.MultiCommSafe hforward)
    (hsrc : BackwardAdminReflection.EncodedSCStepSource N (encode P n v))
    (hstep :
      Nonempty
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar
          (encode P n v) tgt)) :
    (∃ T,
      Nonempty
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.ReducesStar
          (encode P n v) T) ∧
      Mettapedia.Languages.ProcessCalculi.PiCalculus.WeakRestrictedBisim N T
        (encode P' n v))
    ∧
    (encode P n v = tgt
      ∨
      (∃ tgt' canon,
        Nonempty
          (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar
            (encode P n v) tgt') ∧
        BackwardAdminReflection.AdminCanonicalTarget (encode P n v) canon ∧
        Mettapedia.Languages.ProcessCalculi.PiCalculus.WeakRestrictedBisimD N tgt' canon)
      ∨
      (∃ mid,
        Nonempty
          (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerived
            (encode P n v) mid) ∧
        Nonempty
          (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar
            mid tgt) ∧
        Nonempty
          (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces
            (encode P n v) mid) ∧
        ∃ P0 P1 n0 v0 tgt',
          Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence
            (encode P n v) (encode P0 n0 v0) ∧
          Nonempty (P0 ⇝ P1) ∧
          Nonempty
            (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar
              (encode P0 n0 v0) tgt') ∧
          Mettapedia.Languages.ProcessCalculi.PiCalculus.WeakRestrictedBisimD N tgt'
            (encode P1 n0 v0))) := by
  refine ⟨?_, ?_⟩
  · exact
      Mettapedia.Languages.ProcessCalculi.PiCalculus.EncodingMorphism.forward_multi_step_bisim
        (N := N) (P := P) (P' := P') hforward hrf hsafe n v
  · exact
      calculus_backward_simulation_full_general_encode
        (N := N) (P := P) (n := n) (v := v) (tgt := tgt) hsrc hstep

/-- Design-boundary corollary:
the non-empty seed-listener observation set `{ns_z}` cannot satisfy user-observation
discipline (`N ⊆ fn(P)`) under `EncodingFresh P`. -/
theorem seed_listener_nonempty_obs_not_userScoped
    {P : Process}
    (hfresh : EncodingFresh P) :
    ¬ (({ "ns_z" } : Finset String) ⊆ P.freeNames) := by
  exact not_obs_subset_singleton_ns_z_of_encodingFresh (P := P) hfresh

/-- General singleton reserved-name boundary wrapper in the calculus API. -/
theorem userObs_singleton_reserved_not_userScoped
    {P : Process} {r : String}
    (hfresh : EncodingFresh P)
    (hr : r ∈ fullEncodeReservedNames) :
    ¬ (({ r } : Finset String) ⊆ P.freeNames) := by
  exact not_obs_subset_singleton_reserved_of_encodingFresh
    (P := P) (r := r) hfresh hr

/-- Strict-superset regression for the freshness-threaded seed-listener canary:
if it holds at `{ns_z, aux}`, it also holds at `{ns_z}`. -/
theorem nonRF_admin_seed_canary_nonempty_from_fresh_umbrella_obs_superset_regression :
    BackwardAdminReflection.WeakBackwardOutcome
      ({ "ns_z", "aux" } : Finset String)
      (rhoPar (nameServer "ns_x" "ns_z" "v_init" "ns_seed")
        (.apply "PInput" [.fvar "ns_z", .lambda rhoNil])) →
    BackwardAdminReflection.WeakBackwardOutcome
      ({ "ns_z" } : Finset String)
      (rhoPar (nameServer "ns_x" "ns_z" "v_init" "ns_seed")
        (.apply "PInput" [.fvar "ns_z", .lambda rhoNil])) := by
  intro h
  exact BackwardAdminReflection.WeakBackwardOutcome.mono
    h
    (by
      intro x hx
      simp at hx ⊢
      exact Or.inl hx)

end Mettapedia.Languages.ProcessCalculi.PiCalculus
