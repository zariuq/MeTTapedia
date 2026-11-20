import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Worlds.GuardTiming
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.AskTimingControls

/-!
# Guard-timing controls on the supplied world event families

The existing self-telling program separates the two actual local families.
The existing token program supplies a positive event before the tells. These
are firing comparisons; fork and other structural world moves are not
silently classified as local firings.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Worlds.GuardTiming.Controls

open RuleSyntax RuleSyntax.Worlds
open RuleSyntax.StepWeb.AskTimingControls
open RuleSyntax.JointFirings.AskTimingControls (Tm X E)
open RuleSyntax.Equivalence (System)

theorem self_tells_separates_world_firings :
    ∃ after, Fires (events X ℕ E) WorldControls.start after ∧
      ¬ Fires (beforeEvents X ℕ E) WorldControls.start after := by
  obtain ⟨⟨after, fires⟩, refused⟩ := WorldControls.worlds_strict
  exact ⟨after, fires, fun early => refused after ((before_fires_iff X ℕ E _ _).mp early)⟩

theorem token_before_event :
    Fires (beforeEvents X ℕ E) ⟨{WorldControls.tokenWorld}, ∅⟩
      ⟨{(⟨Examples.demo, Examples.consumeFiring.result X Examples.tokenState⟩ : System Tm ℕ)}, ∅⟩ :=
  (before_fires_iff X ℕ E _ _).mpr WorldControls.quiet_world_fires

theorem token_before_event_is_after :
    Fires (events X ℕ E) ⟨{WorldControls.tokenWorld}, ∅⟩
      ⟨{(⟨Examples.demo, Examples.consumeFiring.result X Examples.tokenState⟩ : System Tm ℕ)}, ∅⟩ :=
  fires_mono (before_advances X ℕ E) token_before_event

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Worlds.GuardTiming.Controls
