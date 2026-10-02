import Mettapedia.OSLF.Syntax.IntrinsicScopedOperationalPresheafEventPowers
import Mettapedia.OSLF.Syntax.FreePresheafEventImage

/-!
# Reduction images of actual contextual retained-event powers

At every ambient clone stage, reduction sections are exactly endpoint pairs
with a retained witness in the original substitution model. This comparison
uses the actual event carrier and its two represented endpoint maps.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedOperationalPresheafReduction

open _root_.CategoryTheory
open IntrinsicScopedConditionalPresheaf (Base)
open IntrinsicScopedJudgmentAction (JudgmentAction)
open IntrinsicScopedOperationalPresheafEvents
open IntrinsicScopedOperationalPresheafEventPowers
open IntrinsicScopedOperationalPresheafPrograms (power)
open MultiBinderPresheaf (scopedBodyEquiv)

universe u
variable {S : Signature} {A : BindingCloneAlgebra.Algebra.{u} S}

/-- The actual contextual retained-event graph over the selected program powers. -/
def graph (Y : JudgmentAction.{u,u} A) (Γ : Ctx S) (s : S.Srt) :
    FreePresheafEventExtension.Graph (power A Γ s) where
  edge := events Y Γ s
  source := sourcePower Y Γ s
  target := targetPower Y Γ s

/-- The contextual reduction predicate is the actual paired-endpoint image. -/
def reduction (Y : JudgmentAction.{u,u} A) (Γ : Ctx S) (s : S.Srt) :
    Subfunctor (FunctorToTypes.prod (power A Γ s) (power A Γ s)) :=
  FreePresheafEventImage.endpointImage (graph Y Γ s)

/-- Reduction sections are exactly original witnesses in the full binder and ambient context. -/
theorem mem_reduction_iff (Y : JudgmentAction.{u,u} A) (Γ : Ctx S) (s : S.Srt)
    (X : Base A) (first last : (power A Γ s).obj X) :
    (first, last) ∈ (reduction Y Γ s).obj X ↔
      Nonempty (Y.carrier ⟨Γ ++ X.unop.context, s,
        scopedBodyEquiv A X.unop Γ s first, scopedBodyEquiv A X.unop Γ s last⟩) := by
  refine (FreePresheafEventImage.mem_endpointImage_iff (graph Y Γ s) X (first, last)).trans ?_
  constructor
  · rintro ⟨event, firstEq, lastEq⟩
    have sourceEq := (sourcePower_body Y Γ s X event).symm.trans
      (congrArg (scopedBodyEquiv A X.unop Γ s) firstEq)
    have targetEq := (targetPower_body Y Γ s X event).symm.trans
      (congrArg (scopedBodyEquiv A X.unop Γ s) lastEq)
    let actual := eventAtEquiv Y Γ s X event
    have projected : actual.1 =
        ((sourceBody Y Γ s).app X event, (targetBody Y Γ s).app X event) := by
      rcases event with ⟨⟨sort, pair, evidence⟩, same⟩
      cases same
      rfl
    have endpoints : actual.1 =
        (scopedBodyEquiv A X.unop Γ s first, scopedBodyEquiv A X.unop Γ s last) :=
      projected.trans (Prod.ext sourceEq targetEq)
    exact ⟨endpoints ▸ actual.2⟩
  · rintro ⟨evidence⟩
    let event := (eventAtEquiv Y Γ s X).symm
      ⟨(scopedBodyEquiv A X.unop Γ s first, scopedBodyEquiv A X.unop Γ s last), evidence⟩
    refine ⟨event, ?_, ?_⟩
    · apply (scopedBodyEquiv A X.unop Γ s).injective
      exact sourcePower_body Y Γ s X event
    · apply (scopedBodyEquiv A X.unop Γ s).injective
      exact targetPower_body Y Γ s X event

end Mettapedia.OSLF.Binding.IntrinsicScopedOperationalPresheafReduction
