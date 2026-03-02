import Mettapedia.OSLF.Framework.Mode2Skeleton
import Mettapedia.Languages.MeTTa.Pure.Core

/-!
# Mode2PureBoundary

Conservative pure-mode boundary facts for the current mode skeleton:
- pure has only identity morphisms
- no runtime/behavioral morphisms into or out of pure (yet)
- specialization to `mettaPure` runtime/behavioral objects
-/

namespace Mettapedia.OSLF.Framework.Mode2PureBoundary

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.Mode2Skeleton
open Mettapedia.Languages.MeTTa.Pure.Core

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

/-- Runtime object induced by `mettaPure` in the current skeleton. -/
def mettaPureRuntimeObj : ModeObj := .runtime mettaPure

/-- Behavioral object induced by `mettaPure` in the current skeleton. -/
def mettaPureBehavioralObj : ModeObj := .behavioral mettaPure

/-- Canonical runtime→behavioral edge for `mettaPure`. -/
def mettaPureRuntimeToBehavioral :
    ModeHom mettaPureRuntimeObj mettaPureBehavioralObj :=
  runtimeToBehavioralCanonical mettaPure

/-- Current skeleton already transports a diamond witness for `mettaPure`
along runtime→behavioral canonical edge. -/
theorem mettaPure_runtime_behavioral_diamond_transport
    {φ : Pattern → Prop} {p : Pattern}
    (h : Mettapedia.OSLF.Framework.TypeSynthesis.langDiamond mettaPure φ p) :
    ∃ q, Mettapedia.OSLF.Framework.TypeSynthesis.langReduces mettaPure p q ∧ φ q ∧
      ∃ T, Mettapedia.OSLF.Framework.LangMorphism.LangReducesStar mettaPure
        (mettaPureRuntimeToBehavioral.termMap p) T ∧
        T = mettaPureRuntimeToBehavioral.termMap q := by
  simpa [mettaPureRuntimeToBehavioral] using runtimeToBehavioral_diamond_witness mettaPure h

end Mettapedia.OSLF.Framework.Mode2PureBoundary
