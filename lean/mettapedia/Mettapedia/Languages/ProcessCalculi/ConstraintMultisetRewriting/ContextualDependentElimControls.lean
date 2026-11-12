import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSweepElimSigma
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSweepWitnessesStuckSigma

/-!
# Controls of the elimination reading and of the Σ step on the sweep's witnesses

On the three witnesses of `ContextualDependentSweep.Witnesses`:

* **A projection below an application, at `G A`** (`belowStore`). R124's reading of application spines reads nothing
  (`below_spines_none`); the elimination reading reads the sides (`below_elims_read`, `below_elimSpines`).
* **Two projections above an application, at `G A`** (`nestedStore`): the same (`nested_spines_none`,
  `nested_elims_read`).
* **A projection at a Σ base** (`sigmaBaseStore`). The elimination reading reads nothing, because a Σ type is not a
  base type as it stands (`sigmaBase_elims_none`): the check of the base type is needed there, a neutral at a Σ type
  is not its own long form. R121's Σ step leaves the sides as they are (`sigmaBase_sigmaTo_same`); the Σ step for
  every elimination spine expands them (`sigmaBase_expanded`).

The runs of the families on the three stores are reduced to the compiled runs: a store on which the compiled run
of the mixed family, or of the family above it, reads `committed` has a principal answer under that family
(`*_committed_of_ending`). The compiled runs read `committed` at budgets 16 and 64 for the stores named in each
statement; that reading is an evaluation, not a kernel statement.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentSweep.Witnesses

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentWorklist ContextualDependentDynamicFragment
open ContextualDependentPatternFiring.Controls ContextualDependentEtaDepth ContextualDependentEtaDepth.BaseControls

/-! ## A projection below an application -/

/-- **R124's reading of application spines reads nothing** on the sides. -/
theorem below_spines_none : spinesUnderN (S := setting) ContextualDependentInversion.Controls.reducer 16 []
    belowEquation.1.1.code belowEquation.1.2.code belowEquation.2.2.code = none := by decide +kernel

/-- **The elimination reading reads the sides.** -/
theorem below_elims_read : (elimsUnderN (S := setting) ContextualDependentInversion.Controls.reducer 16 []
    belowEquation.1.1.code belowEquation.1.2.code belowEquation.2.2.code).isSome = true := by decide +kernel

/-- **The sides are two elimination spines of one local under the same abstractions, at a base type as it stands.** -/
theorem below_elimSpines : ∃ pieces, ElimSpines setting.R true [] belowEquation.1.1.code belowEquation.1.2.code
    belowEquation.2.2.code pieces := by
  obtain ⟨pieces, found⟩ := Option.isSome_iff_exists.mp below_elims_read
  exact ⟨pieces, elimsUnderN_rel _ 16 [] _ _ _ found⟩

/-- The mixed family decides the store wherever its compiled run reads `committed`. -/
theorem below_committed_of_ending {fuel rounds : Nat} (read : endingMixed fuel rounds ctxAX belowStore = .committed) :
    (run (mixedTower.solver fuel) belowStore rounds).readout = .commit :=
  committed_of_endingMixed read

/-! ## Two projections above an application -/

theorem nested_spines_none : spinesUnderN (S := setting) ContextualDependentInversion.Controls.reducer 16 []
    nestedEquation.1.1.code nestedEquation.1.2.code nestedEquation.2.2.code = none := by decide +kernel

theorem nested_elims_read : (elimsUnderN (S := setting) ContextualDependentInversion.Controls.reducer 16 []
    nestedEquation.1.1.code nestedEquation.1.2.code nestedEquation.2.2.code).isSome = true := by decide +kernel

theorem nested_committed_of_ending {fuel rounds : Nat}
    (read : endingMixed fuel rounds ctxAX nestedStore = .committed) :
    (run (mixedTower.solver fuel) nestedStore rounds).readout = .commit :=
  committed_of_endingMixed read

/-! ## A projection at a Σ base -/

/-- **At a Σ base the elimination reading reads nothing**: a Σ type is not a base type as it stands. -/
theorem sigmaBase_elims_none : elimsUnderN (S := setting) ContextualDependentInversion.Controls.reducer 16 []
    sigmaBaseEquation.1.1.code sigmaBaseEquation.1.2.code sigmaBaseEquation.2.2.code = none := by decide +kernel

/-- **R121's Σ step leaves the side as it is**: its test reads application spines only. -/
theorem sigmaBase_sigmaTo_same :
    sigmaTo 0 sigmaBaseEquation.1.1.code sigmaBaseEquation.1.2.code = sigmaBaseEquation.1.2.code := by
  decide +kernel

/-- **The Σ step for every elimination spine expands the side** into the pair of its projections. -/
theorem sigmaBase_expanded :
    elimSigmaTo 0 sigmaBaseEquation.1.1.code sigmaBaseEquation.1.2.code =
      .lam (.lam (.pair (.fst (.fst (.app (.var 0) (.var 2)))) (.snd (.fst (.app (.var 0) (.var 2)))))) := by
  decide +kernel

/-- The family above the mixed family decides the store wherever its compiled run reads `committed`. -/
theorem sigmaBase_committed_of_ending {fuel rounds : Nat}
    (read : endingTop fuel rounds ctxAX sigmaBaseStore = .committed) :
    (run (elimSigmaTower.solver fuel) sigmaBaseStore rounds).readout = .commit :=
  committed_of_endingTop read

end ContextualDependentSweep.Witnesses
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
