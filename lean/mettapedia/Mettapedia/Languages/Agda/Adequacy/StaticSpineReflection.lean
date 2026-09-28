import Mettapedia.Languages.Agda.Adequacy.StaticReflection
import Mettapedia.Languages.Agda.Structural.SpineContextRegularity

/-!
# Reflection of the recursively extended spine presentation

This fold interprets every derivation in the twenty-four-rule presentation,
including core rules whose premises themselves use spine elimination. An
action is interpreted conditionally on an observed input type, and returns
successful observation of its spine and output together with a source typing
transformer. It does not infer formation from an empty action.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.StaticAdequacy.SpineReflection

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists
open Mettapedia.TypeTheory
open Structural.Statics (RawTm RawTy RawContext)
open Structural.SpineStatics

structure ActionResult {n : Nat} (Δ : StaticSpecification.RawContext n)
    (input : StaticSpecification.Ty n) (es : Structural.Spine (Structural.scope n)) (B : RawTy n) where
  spine : StaticSpecification.Spine n
  output : StaticSpecification.Ty n
  spineObserved : Observation.spine es = some spine
  outputObserved : Observation.type B = some output
  proof : Observation.SourceAction Δ input spine output
  equality : ∀ {f g : StaticSpecification.Term n}, StaticSpecification.TermEq Δ f g input →
    StaticSpecification.TermEq Δ (f.applySpine spine) (g.applySpine spine) output

def Interpretation : CombinedJudgment → Type
  | .core j => Reflection.Interpretation j
  | .spineAction Γ A es B => ∀ Δ, Observation.context Γ = some Δ →
      ∀ a, Observation.type A = some a → ActionResult Δ a es B

def interpretRule {j : CombinedJudgment} (shape : RuleShape j)
    (ih : Evidence Interpretation (premises shape)) : Interpretation j := by
  cases shape <;> simp only [premises] at ih
  case core shape =>
      exact Reflection.interpretRule shape (corePremiseEvidence ih)
  case nil Γ A =>
      intro Δ _ a observed
      exact ⟨[], a, rfl, observed, fun head => head, fun equal => equal⟩
  case cons Γ A B argument rest C =>
      intro Δ ctx input observed
      let parts := Observation.piView A B observed
      let arg := ih 0 Δ ctx
      let tail := ih 1 Δ ctx (parts.body.instantiate arg.value)
        (Observation.typeBody_instantiate B parts.body_eq arg.observed)
      refine ⟨.apply arg.value :: tail.spine, tail.output,
        Observation.cons_of_some (Observation.apply_of_some arg.observed) tail.spineObserved,
        tail.outputObserved, ?_, ?_⟩
      · intro head typedHead
        exact tail.proof (.app (parts.result_eq ▸ typedHead) (arg.atType parts.domain_eq))
      · intro first second equal
        exact tail.equality (.appCong (parts.result_eq ▸ equal) (.refl (arg.atType parts.domain_eq)))
  case append Γ A first B second C =>
      intro Δ ctx input observed
      let left := ih 0 Δ ctx input observed
      let right := ih 1 Δ ctx left.output left.outputObserved
      refine ⟨left.spine ++ right.spine, right.output,
        Observation.append_of_some left.spineObserved right.spineObserved, right.outputObserved, ?_, ?_⟩
      · intro head typedHead
        exact (congrArg (fun t => StaticSpecification.Typing Δ t right.output)
          (StaticSpecification.Term.applySpine_append head left.spine right.spine)).mpr
            (right.proof (left.proof typedHead))
      · intro first second equal
        simpa only [StaticSpecification.Term.applySpine_append] using
          right.equality (left.equality equal)
  case inputConversion Γ A' A es B =>
      intro Δ ctx input observed
      let equal := ih 0 Δ ctx
      let action := ih 1 Δ ctx equal.right equal.rightObserved
      exact ⟨action.spine, action.output, action.spineObserved, action.outputObserved,
        (fun typedHead => action.proof (.conv typedHead (equal.at observed equal.rightObserved))),
        fun terms => action.equality (.conv terms (equal.at observed equal.rightObserved))⟩
  case outputConversion Γ A es B B' =>
      intro Δ ctx input observed
      let action := ih 0 Δ ctx input observed
      let equal := ih 1 Δ ctx
      exact ⟨action.spine, equal.right, action.spineObserved, equal.rightObserved,
        (fun typedHead => .conv (action.proof typedHead) (equal.at action.outputObserved equal.rightObserved)),
        fun terms => .conv (action.equality terms) (equal.at action.outputObserved equal.rightObserved)⟩
  case elimination Γ head A es B =>
      intro Δ ctx
      let typed := ih 0 Δ ctx
      let action := ih 1 Δ ctx typed.typeValue typed.typeObserved
      exact ⟨typed.value.applySpine action.spine, action.output,
        Observation.eliminate_of_some typed.observed action.spineObserved,
        action.outputObserved, action.proof typed.proof⟩

noncomputable def interpret {j : CombinedJudgment} (tree : Derivation j) : Interpretation j :=
  IndexedPolynomial.Fix.eliminate presentation.polynomial
    (fun _ j _ => Interpretation j)
    (fun _ _ shape _ ih => interpretRule shape ih) () j tree

noncomputable def typingBack {n : Nat} {Γ : StaticSpecification.RawContext n}
    {t : StaticSpecification.Term n} {A : StaticSpecification.Ty n}
    (tree : CoreDerivation (Structural.Statics.typed (embedContext Γ) (embedTerm t) (embedTy A))) :
    StaticSpecification.Typing Γ t A :=
  (interpret tree Γ (Observation.context_embed Γ)).at (Observation.term_embed t) (Observation.type_embed A)

noncomputable def reflectTyping {n : Nat} {Γ : RawContext n} {t : RawTm n} {A : RawTy n}
    (tree : CoreDerivation (Structural.Statics.typed Γ t A)) : Reflection.ReflectedTyping Γ t A :=
  let ambient := interpret tree.contextOfTyping
  ⟨ambient, interpret tree ambient.value ambient.observed⟩

theorem typing_iff {n : Nat} (Γ : StaticSpecification.RawContext n)
    (t : StaticSpecification.Term n) (A : StaticSpecification.Ty n) :
    Nonempty (CoreDerivation (Structural.Statics.typed (embedContext Γ) (embedTerm t) (embedTy A))) ↔
      Nonempty (StaticSpecification.Typing Γ t A) :=
  ⟨fun ⟨tree⟩ => ⟨typingBack tree⟩, fun ⟨tree⟩ => ⟨includeCanonical (typingForward tree)⟩⟩

end Mettapedia.Languages.Agda.StaticAdequacy.SpineReflection
