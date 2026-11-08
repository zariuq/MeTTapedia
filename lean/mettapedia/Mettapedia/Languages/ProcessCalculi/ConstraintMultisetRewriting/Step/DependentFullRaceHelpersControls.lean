import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFullRaceHelpers
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFullTelescopesControls

/-!
# Helper firings in the races layer: controls

The firings are those of `DependentFull.TelescopeControls`, at the state `X : U0`:
`f` makes `x : X, p : Id X x x` and the row `1 : p`; `g` makes `y : X` and the row `2 : y`.

* **Positive** (`telescopes_independent`): `f` and `g` are independent in the interface's sense for
  the helper transport: both orders are admitted, and the composites are the same up to the block
  exchange.
* **Negative** (`clash_not_independent`): `g₁` makes `y : X` and the row `1 : y`, the row `f` makes.
  After `f` the row `1` is present, so the residual of `g₁` is refused and the two are not
  independent.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
namespace DependentFull.RaceHelperControls

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open DependentFull.Controls DependentFull.TelescopeControls
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (fire)

/-- `f` as a helper firing. -/
abbrev pathFiring : HelperFiring setting.levels Nat baseState := ⟨pathHelpers, fData⟩

/-- `g` as a helper firing. -/
abbrev pointFiring : HelperFiring setting.levels Nat baseState := ⟨pointHelpers, gData⟩

/-- **The two telescope firings are independent for the helper transport.** -/
theorem telescopes_independent :
    (helperTransport setting.levels Nat).Independent baseState pathFiring pointFiring := by
  obtain ⟨afterFirst, afterSecond, -⟩ := exchanged_diamond
  exact helper_independent_iff.mpr ⟨firstAdmitted, secondAdmitted, afterFirst, afterSecond⟩

/-- `g₁`'s data: the row `1 : y`, the row `f` makes. -/
def clashData : Natural setting.levels Nat pointHelpers.frame :=
  ⟨[], [], [], [], [(1, Make.ofRow pointRow)], [], [], []⟩

abbrev clashFiring : HelperFiring setting.levels Nat baseState := ⟨pointHelpers, clashData⟩

/-- **A firing that makes the row `f` makes is not independent of `f`.** -/
theorem clash_not_independent :
    ¬ (helperTransport setting.levels Nat).Independent baseState pathFiring clashFiring := by
  rintro ⟨first, -, afterFirst, -, -⟩
  have local' := (Natural.admits_withHelpers _ _).mp afterFirst
  obtain ⟨-, -, -, fresh⟩ := (Plain.enabled_iff _ _).mp local'.2.1
  have present : 1 ∈ ((helperStep setting.levels Nat).result pathFiring first).present := by
    show 1 ∈ fire (∅ : Finset Nat) (pathFiring.toFiring.selection.commit (T := Unit))
    decide
  exact fresh 1 (List.mem_singleton_self _) present

end DependentFull.RaceHelperControls

#print axioms DependentFull.RaceHelperControls.telescopes_independent
#print axioms DependentFull.RaceHelperControls.clash_not_independent

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
