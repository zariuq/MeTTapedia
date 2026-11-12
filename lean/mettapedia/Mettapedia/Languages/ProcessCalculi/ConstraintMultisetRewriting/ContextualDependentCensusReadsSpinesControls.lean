import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCensusReadsSpines
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaDepthArgGap

/-!
# Controls of the row of spines of one local

* **The shape on a store of the census.** R121's store with a binder of a local's type behind a redex
  (`ArgControls.argStore`) has the shape (`arg_localSpines`), and the decision accepts it (`arg_decided`).
* **The normality hypothesis is needed.** The executable reading takes the local's type literally. With one local
  whose type is the redex `(λ x. x → x) U`, the two sides `h U` and `h U` have a relational reading
  (`redex_rel`: the type reduces to a Π type), and the executable reading reads nothing, at any budget and with any
  reducer (`redex_reads_none`). So "the executable reading reads every relational reading" holds only where the
  locals' types are normal, as they are on the census heads of a prepared store.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentEtaDepth.SpineControls

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open ContextualDependentSpinesMany
open ContextualDependentPatternFiring.Controls

/-! ## The shape on a store of the census -/

/-- **R121's store with a hidden binder has the shape.** -/
theorem arg_localSpines : LocalSpines 0 ArgControls.argEquation.1.1.code ArgControls.argEquation.1.2.code
    ArgControls.argEquation.2.2.code := by
  obtain ⟨pieces, found⟩ := Option.isSome_iff_exists.mp ArgControls.arg_reads
  exact (dependentUnderN_rel _ 16 [] _ _ _ found).localSpines

theorem arg_decided : localSpinesAt 0 ArgControls.argEquation.1.1.code ArgControls.argEquation.1.2.code
    ArgControls.argEquation.2.2.code = true :=
  arg_localSpines.decided

/-! ## A local whose type is a redex -/

section Redex

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-- `(λ x. x → x) U`, a redex whose reduct is the Π type `U → U`. -/
def redexType (u : Head) : Tm Head 1 := .app (.lam (.pi (.var 0) (.var 1))) (.head u)

theorem redexType_reduces (R : Rules Head) (u : Head) :
    Reduces R (redexType u) (.pi (.head u) (.head u)) :=
  Relation.ReflTransGen.single (StepCore.betaPi _ _)

/-- **A relational reading with a local whose type is a redex**: the sides `h U` and `h U`, for `h` of the type
`(λ x. x → x) U`, at the base `U`. -/
theorem redex_rel (R : Rules Head) (u : Head) :
    DepRel R [redexType u] (.head u) (.app (.var 0) (.head u)) (.app (.var 0) (.head u))
      [⟨.head u, .head u, .head u, .head u⟩] :=
  DepRel.base (h := 0) (as := [.head u]) (bs := [.head u]) (T := redexType u) (F := .head u) rfl
    (show (0 : Nat) < 1 from Nat.zero_lt_one) (List.cons_ne_nil _ _) rfl (.cons (redexType_reduces R u) (redexType_reduces R u) (.nil _ _))

/-- **The executable reading reads nothing on it**, at any budget and with any reducer. -/
theorem redex_reads_none (reducer : ExecutableReduction.Reducer S.R) (fuel : Nat) (u : Head) :
    dependentUnderN (S := S) reducer fuel [redexType u] (.head u) (.app (.var 0) (.head u))
      (.app (.var 0) (.head u)) = none := rfl

end Redex

end ContextualDependentEtaDepth.SpineControls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
