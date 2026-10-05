import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingContexts
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingSpine

/-!
# Contextual adequacy for authored function-service clients

Wells, Stay and Meredith, `Behavior in higher-order languages`, separate
encoded source clients from arbitrary target observers. The construction
below proves that image-based contract for this particular compiler.

Clients are the independently authored scoped pi protocol contexts, admitted
by a source-context elaboration certificate. Observation executes their actual
assembled program through unary lowering and the core-rho compiler. Every
source context is covered; arbitrary quotation tests and unrelated target
frames are outside this grammar. This is a contextual comparison of program
interfaces, not unrestricted contextual equivalence of bare emitted quotes.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingObserverAdequacy

open Mettapedia.OSLF.Binding
open Mettapedia.GSLT Mettapedia.GSLT.IndexedOperational
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.Languages.LambdaCalculus
open NamePassingLambda NamePassingContexts NamePassingEnvironmentEquationsNative

def MayReturn {Γ : Ctx sig} (source : Expr Γ) : Prop :=
  (semanticDiamond (sourceTheory Γ).closure (NamePassingValueNative.sourcePredicate Γ)).1 source

/-- The observer runs actual emitted code and asks for its public receiver.
Compilation success and the finite execution are part of the observation. -/
def ProtocolMayReturn {Γ : Ctx sig} (component : ProtocolContexts.Program Γ) : Prop :=
  ∃ code : RhoUnaryCode.Code 0,
    RhoUnaryCompiler.compile (RhoUnaryWorld.initial (.nm :: Γ)).world
      (MonadicProtocol.lower (component (NamePassingUnaryForward.references Γ) .zero)) = some code ∧
      (semanticDiamond RhoUnaryReadback.Target.closure
        (RhoUnaryInputObservation.targetPredicate (RhoUnaryWorld.initial (.nm :: Γ)) .zero)).1
        (RhoUnaryReadback.runtimeProcess code (RhoUnaryWorld.initial (.nm :: Γ)).available)

theorem mayReturn_iff {Γ : Ctx sig} (source : Expr Γ) :
    MayReturn source ↔ ProtocolMayReturn (program source) := by
  constructor
  · intro returned
    obtain ⟨code, supplied⟩ := NamePassingRho.compile_total source
      (NamePassingUnaryForward.references Γ) .zero (RhoUnaryWorld.initial (.nm :: Γ)).world
    refine ⟨code, supplied, ?_⟩
    exact (NamePassingSpine.native_may_return_iff (RhoUnaryWorld.initial (.nm :: Γ))
      (NamePassingSpine.initial_related source _ code supplied)).mp returned
  · rintro ⟨code, supplied, returned⟩
    exact (NamePassingSpine.native_may_return_iff (RhoUnaryWorld.initial (.nm :: Γ))
      (NamePassingSpine.initial_related source _ code supplied)).mpr returned

/-- Contextual observation is about a caller's execution, not only the
instantaneous return of the component before the caller applies it. -/
theorem context_mayReturn_iff {Γ Δ : Ctx sig} (context : SourceContext Γ Δ)
    (source : Expr Γ) :
    MayReturn (context.plug source) ↔
      ProtocolMayReturn ((translate context).plug (program source)) := by
  rw [plug_agreement]
  exact mayReturn_iff _

def SourceEquivalent {Γ : Ctx sig} (left right : Expr Γ) : Prop :=
  ∀ (Δ : Ctx sig) (context : SourceContext Γ Δ),
    MayReturn (context.plug left) ↔ MayReturn (context.plug right)

def ProtocolEquivalent {Γ : Ctx sig} (left right : ProtocolContexts.Program Γ) : Prop :=
  ∀ (Δ : Ctx sig) (context : ProtocolContexts.Context Γ Δ), Admitted context →
    (ProtocolMayReturn (context.plug left) ↔ ProtocolMayReturn (context.plug right))

/-- Preservation and reflection for every admitted client, with actual
core-rho executions on the target side. Admission has full source coverage. -/
theorem contextual_adequacy {Γ : Ctx sig} (left right : Expr Γ) :
    SourceEquivalent left right ↔ ProtocolEquivalent (program left) (program right) := by
  constructor
  · rintro equivalent Δ context ⟨sourceContext, rfl⟩
    exact (context_mayReturn_iff sourceContext left).symm.trans
      ((equivalent Δ sourceContext).trans (context_mayReturn_iff sourceContext right))
  · intro equivalent Δ context
    exact (context_mayReturn_iff context left).trans
      ((equivalent Δ (translate context) (translated_admitted context)).trans
        (context_mayReturn_iff context right).symm)

theorem source_equivalent_refl {Γ : Ctx sig} (source : Expr Γ) :
    SourceEquivalent source source := fun _ _ => Iff.rfl

theorem source_equivalent_symm {Γ : Ctx sig} {left right : Expr Γ}
    (equivalent : SourceEquivalent left right) : SourceEquivalent right left :=
  fun Δ context => (equivalent Δ context).symm

theorem source_equivalent_trans {Γ : Ctx sig} {first middle last : Expr Γ}
    (before : SourceEquivalent first middle) (after : SourceEquivalent middle last) :
    SourceEquivalent first last :=
  fun Δ context => (before Δ context).trans (after Δ context)

/-- Client closure is earned from syntactic composition and adequacy. -/
theorem source_context_congruence {Γ Δ : Ctx sig} (context : SourceContext Γ Δ)
    {left right : Expr Γ} (equivalent : SourceEquivalent left right) :
    SourceEquivalent (context.plug left) (context.plug right) := by
  intro Θ outer
  simpa only [NamePassing.Context.plug_compose] using equivalent Θ (outer.compose context)

/-- Static source equations remain interchangeable in every admitted client,
including guarded and stored expression positions. -/
theorem structural_equivalent {Γ : Ctx sig} {left right : Expr Γ}
    (equal : NamePassing.Environment.StructuralEq left right) : SourceEquivalent left right := by
  intro Δ context
  exact (semanticDiamond (sourceTheory Δ).closure (NamePassingValueNative.sourcePredicate Δ)).2
    (context.plug_structural equal)

theorem admitted_context_congruence {Γ Δ : Ctx sig} {context : ProtocolContexts.Context Γ Δ}
    (admitted : Admitted context) {left right : ProtocolContexts.Program Γ}
    (equivalent : ProtocolEquivalent left right) :
    ProtocolEquivalent (context.plug left) (context.plug right) := by
  intro Θ outer outerAdmitted
  rw [← ProtocolContexts.Context.plug_compose, ← ProtocolContexts.Context.plug_compose]
  exact equivalent Θ (outer.compose context) (admitted_compose outerAdmitted admitted)

/-- The semantic observer boundary can be larger than the authored image.
Membership in that larger class requires preservation of the relation. -/
def PreservesEquivalence {Γ Δ : Ctx sig} (context : ProtocolContexts.Context Γ Δ) : Prop :=
  ∀ left right, ProtocolEquivalent left right →
    ProtocolEquivalent (context.plug left) (context.plug right)

theorem admitted_preserves_equivalence {Γ Δ : Ctx sig} {context : ProtocolContexts.Context Γ Δ}
    (admitted : Admitted context) : PreservesEquivalence context :=
  fun _ _ equivalent => admitted_context_congruence admitted equivalent

theorem preserving_contexts_compose {Γ Δ Θ : Ctx sig}
    (outer : ProtocolContexts.Context Δ Θ) (inner : ProtocolContexts.Context Γ Δ)
    (outerPreserves : PreservesEquivalence outer) (innerPreserves : PreservesEquivalence inner) :
    PreservesEquivalence (outer.compose inner) := by
  intro left right equivalent
  rw [ProtocolContexts.Context.plug_compose, ProtocolContexts.Context.plug_compose]
  exact outerPreserves _ _ (innerPreserves left right equivalent)

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingObserverAdequacy
