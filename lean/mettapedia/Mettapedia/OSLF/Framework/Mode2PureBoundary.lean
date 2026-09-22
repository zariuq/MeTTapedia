import Mettapedia.OSLF.Framework.Mode2Skeleton
import Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Pattern.Core

/-!
# Mode2PureBoundary

Conservative pure-mode boundary facts for the current mode skeleton:
- pure has only identity morphisms
- no runtime/behavioral morphisms into or out of pure (yet)
- specialization to `twoSortDependent` runtime/behavioral objects
-/

namespace Mettapedia.OSLF.Framework.Mode2PureBoundary

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.Mode2Skeleton
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Pattern.Core

theorem no_pure_to_runtime (L : LanguageDef) :
    ModeHom .pure (.runtime L) → False := by
  intro h
  cases h

theorem no_pure_to_behavioral (L : LanguageDef) :
    ModeHom .pure (.behavioral L) → False := by
  intro h
  cases h

theorem no_runtime_to_pure (L : LanguageDef) :
    ModeHom (.runtime L) .pure → False := by
  intro h
  cases h

theorem no_behavioral_to_pure (L : LanguageDef) :
    ModeHom (.behavioral L) .pure → False := by
  intro h
  cases h

theorem pure_endo_unique (f : ModeHom .pure .pure) :
    f = (ModeHom.id (X := .pure)) := by
  cases f
  rfl

/-- Current pure-boundary characterization for the mode skeleton. -/
theorem pure_boundary_characterization
    {X Y : ModeObj} (f : ModeHom X Y) :
    X = .pure ∨ Y = .pure →
    X = .pure ∧ Y = .pure ∧ HEq f (ModeHom.id (X := .pure)) := by
  intro hp
  cases hp with
  | inl hX =>
      subst hX
      cases Y with
      | pure =>
          refine ⟨rfl, rfl, ?_⟩
          exact (pure_endo_unique f).heq
      | runtime L =>
          exact False.elim (no_pure_to_runtime L f)
      | behavioral L =>
          exact False.elim (no_pure_to_behavioral L f)
  | inr hY =>
      subst hY
      cases X with
      | pure =>
          refine ⟨rfl, rfl, ?_⟩
          exact (pure_endo_unique f).heq
      | runtime L =>
          exact False.elim (no_runtime_to_pure L f)
      | behavioral L =>
          exact False.elim (no_behavioral_to_pure L f)

/-- Runtime object induced by `twoSortDependent` in the current skeleton. -/
def twoSortDependentRuntimeObj : ModeObj := .runtime twoSortDependent

/-- Behavioral object induced by `twoSortDependent` in the current skeleton. -/
def twoSortDependentBehavioralObj : ModeObj := .behavioral twoSortDependent

/-- Canonical runtime→behavioral edge for `twoSortDependent`. -/
def twoSortDependentRuntimeToBehavioral :
    ModeHom twoSortDependentRuntimeObj twoSortDependentBehavioralObj :=
  runtimeToBehavioralCanonical twoSortDependent

/-- Current skeleton already transports a diamond witness for `twoSortDependent`
along runtime→behavioral canonical edge. -/
theorem twoSortDependent_runtime_behavioral_diamond_transport
    {φ : EquationPredicate (langGSLT twoSortDependent)} {p : Pattern}
    (h : Mettapedia.OSLF.Framework.TypeSynthesis.langDiamond twoSortDependent φ p) :
    ∃ q, Mettapedia.OSLF.Framework.TypeSynthesis.langSemanticReduces
        twoSortDependent p q ∧ φ q ∧
      ∃ T, Mettapedia.OSLF.Framework.LangMorphism.LangReducesStar twoSortDependent
        (twoSortDependentRuntimeToBehavioral.termMap p) T ∧
        T = twoSortDependentRuntimeToBehavioral.termMap q := by
  exact runtimeToBehavioral_diamond_witness twoSortDependent h

end Mettapedia.OSLF.Framework.Mode2PureBoundary
