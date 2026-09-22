import Mettapedia.GSLT.Core.GSLT
import Mettapedia.GSLT.Core.InteractionEvent
import Mettapedia.GSLT.Causality.Trace
import Mettapedia.GSLT.Dynamics.CostExactness
import Mettapedia.OSLF.Framework.GSLTTypeSynthesis

/-!
# Semantic kernel of OSLF

OSLF is a construction on a rewrite theory, not a sibling of GSLT and not
a LanguageDef. A presentation (however spelled) presents a GSLT. The
logic is induced from that GSLT's one-step span.

This file records the primitive data, the two decorations, and the
induced interface. It does not clone Finding Mind's chapter list, and it
does not take Meredith's packaging as the only source.

## Primitive

* `GSLT` — terms, equations, rewrites (Bucciarelli–Salibra graph lambda
  theories; Harper–Honsell–Plotkin: a presentation generates a theory).
* Optional `InteractionPresentation` — a named site at which two things
  meet, with occurrence evidence (not an agent).

## Decorations (same carrier, extra component)

* History — writer of rewrite events: `ExtendedTerm = Term × Trace`.
  nLab: action/writer monad. Piróg–Gibbons: tracing. Danos–Krivine /
  Phillips–Ulidowski: reversibility by recording. The empty log is the
  unit; concatenation is multiplication. Forgetting the log is the
  coarsest erasure. The GSLT *value* of this writer is `spendLift`
  (`GSLT.WriterGSLT`): `π` is a `StepCover` / `GSLT.Morphism`, `η` is a
  bisimilarity section, `π ∘ η = id`. Backward reversal stays a path
  category (`ReversibleStep`), not stored evaluator state.
* Cost — a grade or coboundary on steps. nLab: graded monad.
  Proper decoration: `spendLift` (writer on `Term × V`). Envelope
  Theorem 7.1 (`envelope_conserves`) needs no exactness. Exactness is
  whether the history potential survives forgetting the log.

## Induced

* Reduction span, then `◇ ⊣ □` (Jacobs change-of-base; Williams–Stay
  NTT; Lawvere hyperdoctrine: ∃ ⊣ f* ⊣ ∀). Already
  `GSLTTypeSynthesis.gsltGalois`.
* Equation-invariant predicates: native types
  (`EquationPredicate`).
* Observational quotients: `LabelIndependence` on proof-relevant
  events (`InteractionEvent`), not on `Prop` steps.
* Bisimulation and HML (Hennessy–Milner): observers of the LTS.

## Not in the kernel

LanguageDef, generated Cost languages, hypercubes, PathMap, NTT
presheaf uplift, sentience, origins. Those spend this coin.

Weight is an endofunctor of rates, not claimed as a monad (Finding Mind
is honest about this; nLab graded monads are the place to settle it).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.SemanticKernel

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.InteractionEvent
open Mettapedia.OSLF.Framework
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

variable {S : GSLT}

/-! ## Induced logic

Every GSLT determines an OSLF type system. The Galois connection is not
language-specific: it is Jacobs change-of-base on the one-step span.
-/

/-- The kernel construction: a GSLT presents a rewrite theory, and OSLF
is the induced modal interface of that theory. -/
abbrev theoryOSLF (theory : GSLT) : OSLFTypeSystem (gsltRewriteSystem theory) :=
  gsltOSLF theory

theorem theory_galois (theory : GSLT) :
    GaloisConnection (gsltDiamond theory) (gsltBox theory) :=
  gsltGalois theory

theorem diamond_is_step_future (theory : GSLT)
    (predicate : theory.Term → Prop) (source : theory.Term) :
    gsltDiamond theory predicate source ↔
      ∃ target, theory.Step source target ∧ predicate target :=
  gsltDiamond_spec theory predicate source

/-! ## History as a writer

`Trace` is the free monoid of proved rewrite events. `ExtendedTerm` is
the writer product. Forgetting the second factor is the erase-everything
quotient (CALF: extensional behaviour is the projection).
-/

/-- `Trace` is a `def` synonym for a list of events, so concatenation is
list append after unfolding. -/
def Trace.asList (τ : Trace S) : List (TraceEntry S) := τ

def Trace.concat (first second : Trace S) : Trace S :=
  Trace.asList first ++ Trace.asList second

theorem Trace.concat_empty (τ : Trace S) :
    Trace.concat τ (Trace.empty S) = τ :=
  List.append_nil (Trace.asList τ)

theorem Trace.empty_concat (τ : Trace S) :
    Trace.concat (Trace.empty S) τ = τ :=
  List.nil_append (Trace.asList τ)

theorem Trace.concat_assoc (σ τ υ : Trace S) :
    Trace.concat (Trace.concat σ τ) υ = Trace.concat σ (Trace.concat τ υ) :=
  List.append_assoc (Trace.asList σ) (Trace.asList τ) (Trace.asList υ)

theorem embed_is_writer_unit (t : S.Term) :
    envelopeEmbed S t = ExtendedTerm.initial S t :=
  rfl

theorem project_forgets_log (et : ExtendedTerm S) :
    envelopeProject S et = et.current :=
  rfl

/-- Coarsest history erasure: identify runs that share a current term. -/
def forgetHistory (first second : ExtendedTerm S) : Prop :=
  first.current = second.current

theorem forgetHistory_iff_same_projection (first second : ExtendedTerm S) :
    forgetHistory first second ↔
      envelopeProject S first = envelopeProject S second :=
  Iff.rfl

/-- Extensional predicates ignore the log. This is the CALF
non-interference law at the predicate layer: cost/history are
intensional. -/
def ignoreHistory (predicate : S.Term → Prop) : ExtendedTerm S → Prop :=
  fun et => predicate et.current

theorem ignoreHistory_on_embed (predicate : S.Term → Prop) (t : S.Term) :
    ignoreHistory predicate (envelopeEmbed S t) ↔ predicate t :=
  Iff.rfl

theorem ignoreHistory_stable_under_forget
    (predicate : S.Term → Prop) {first second : ExtendedTerm S}
    (identified : forgetHistory first second) :
    ignoreHistory predicate first ↔ ignoreHistory predicate second := by
  simp [ignoreHistory, forgetHistory] at identified ⊢
  exact identified ▸ Iff.rfl

/-- Recording a forward step, then undoing it, returns the same extended
term. Unique parent on the free history (Danos–Krivine; covering-space
reading). -/
def forward_backward_inverse {source target : S.Term}
    (step : S.Step source target) (τ : Trace S) :
    ReversibleStep S
      { current := target, history := ⟨source, target, step⟩ :: τ }
      { current := source, history := τ } :=
  ReversibleStep.backward step τ

/-! ## Cost

Theorem 7.1 is `envelope_conserves`: closed envelope paths cost zero
for every `ActionMap`. Exactness is `SurvivesForgetting`. Forward-only
`Conserves` is weaker (see `twoRoute_conserves`).
-/

theorem envelope_loops_conserve {A : Type*} [AddCommGroup A]
    (am : ActionMap S A) (et : ExtendedTerm S)
    (γ : EnvelopePath (S := S) et et) :
    totalEnvelopeAction am γ = 0 :=
  envelope_conserves am et γ

theorem exact_survives_forgetting {A : Type*} [AddCommGroup A]
    (am : ActionMap S A) {φ : S.Term → A} (hex : am.Exact φ) :
    SurvivesForgetting am :=
  survivesForgetting_of_exact am hex

/-! ## Optional interaction site

A site names where two things meet. Completeness (every step is some
event) is optional: partial, observer-indexed sites remain honest.
Erasing an enabled event recovers the semantic step.
-/

variable {site : InteractionPresentation S}

theorem enabled_event_is_a_step {source : S.Term}
    (event : site.Enabled source) :
    S.Step source event.target :=
  InteractionPresentation.Enabled.step event

theorem enabled_event_erases_to_labeled {source : S.Term}
    (event : site.Enabled source) :
    event.erase.source = source ∧ event.erase.target = event.target :=
  ⟨rfl, rfl⟩

/-! ## Interactive theories

Kernel iGSLT is a GSLT with a named meeting site. A cut is a site only
once contraction is a step. LanguageDef `IGSLT` and Meredith cut
combinators spell this object; they are not a second theory.
-/

theorem interactive_erases (I : Interactive) : I.erase = I.theory :=
  Interactive.erase_theory I

theorem interactive_erase_is_functor_obj (I : Interactive) :
    Interactive.eraseFunctor.obj I = I.theory :=
  rfl

theorem sound_cut_is_interactive {theory : GSLT} (c : SoundCut theory) :
    c.toInteractive.erase = theory :=
  SoundCut.toInteractive_erase c

/-! ## Independence

Mazurkiewicz swaps need events that keep their identity across a
commutation (nLab: trace monoid). `Prop` steps cannot do that.
Generated diamonds live in `GSLT.Causality.Mazurkiewicz`: paths modulo
independence tiles, descent iff tile-invariant. Those modules, not a
global `stepsCommute` on endpoints, are the kernel.
-/

end Mettapedia.OSLF.Framework.SemanticKernel
