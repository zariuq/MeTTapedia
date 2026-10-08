import Mettapedia.OSLF.Framework.InstrumentCutContexts
import Mettapedia.OSLF.Syntax.SortedConstructorContextFaithfulness
import Mettapedia.GSLT.Logic.IPOSystem

/-!
# Actual probe-context minimality and administrative exposure

The comparison uses actual sorted contexts and the RPO universal property.
A nonidentity reaction context matching a probe cut supplies a removable
common outer probe frame, contradicting IPO leastness. Nullary probe sorts
exclude the other hole position. No faithfulness of ground filling is assumed.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.InstrumentCutContexts

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedConstructors
open Mettapedia.CategoryTheory.GroundPath
open Mettapedia.GSLT.RelativePushout
open Mettapedia.GSLT.RedexRelativeCongruence

universe u

variable {Symbols : Type u} (arity : Symbols → Nat)

local instance instrumentCutExposureQuiver : Quiver (Srt Symbols arity) := frameQuiver (signature arity)

theorem result_ne_probe (first second : Probe Symbols arity) :
    result arity first ≠ Srt.probe second := by
  cases first <;> simp [result]

theorem no_frame_into_probe {source : Srt Symbols arity} (instrument : Probe Symbols arity)
    (frame : Frame (signature arity) source (.probe instrument)) : False := by
  have output := Frame.output_eq frame
  have position := Frame.position frame
  cases head : Frame.constructor frame with
  | original constructor => simp [head, signature] at output
  | arguments constructor => simp [head, signature] at output
  | probe other =>
    rw [head] at position
    exact Fin.elim0 position
  | cut other =>
    rw [head] at output
    exact result_ne_probe arity other instrument output

theorem path_into_probe_length {source : Srt Symbols arity} (instrument : Probe Symbols arity)
    (path : Context (signature arity) source (.probe instrument)) : path.length = 0 := by
  cases path with
  | nil => rfl
  | cons _ frame => exact (no_frame_into_probe arity instrument frame).elim

/-- Both sides may have different interfaces. Minimality itself rules out
every nonempty reaction context; the redex interface only excludes a probe. -/
theorem probe_ipo_reaction_length {reactionSource : Srt Symbols arity}
    (instrument : Probe Symbols arity) (source : Value arity (receiver arity instrument))
    (redex : Value arity reactionSource)
    (notProbe : reactionSource ≠ Srt.probe instrument)
    (reaction : Context (signature arity) reactionSource (result arity instrument))
    (square : termArrow (signature arity) source ≫ contextArrow (signature arity) (probeContext arity instrument) =
      termArrow (signature arity) redex ≫ contextArrow (signature arity) reaction)
    (ipo : IsIdemPushout (termArrow (signature arity) source) (termArrow (signature arity) redex)
      (contextArrow (signature arity) (probeContext arity instrument))
      (contextArrow (signature arity) reaction) square) : reaction.length = 0 := by
  have values := Arrow.value.inj square
  rw [probeContext_fill] at values
  cases reaction with
  | nil => rfl
  | @cons middle _ previous frame =>
    change cut arity instrument (probe arity instrument) source =
      Frame.fill frame ((action (signature arity)).path previous redex) at values
    have heads : Constructor.cut instrument = frame.constructor :=
      (Term.head_eq (signature := signature arity) _ _ values).trans
        (Frame.fill_head (signature := signature arity) frame
          ((action (signature arity)).path previous redex))
    obtain ⟨position, siblings, sourceEq, _, frameEq⟩ :=
      Frame.deconstruct frame (Constructor.cut instrument) heads.symm
    cases sourceEq
    cases eq_of_heq frameEq
    fin_cases position
    · have zero := path_into_probe_length arity instrument previous
      exact (notProbe (Quiver.Path.eq_of_length_zero previous zero)).elim
    · have arguments := Term.node.inj values
      have probeRead := congrFun arguments 0
      have bodyRead := congrFun arguments 1
      change probe arity instrument = siblings 0 (by change (0 : Fin 2) ≠ 1; decide) at probeRead
      change source = (action (signature arity)).path previous redex at bodyRead
      have sameFrame : Frame.slot (signature := signature arity) (Constructor.cut instrument) 1 siblings =
          probeFrame arity instrument := by
        apply congrArg (Frame.slot (signature := signature arity) (Constructor.cut instrument) 1)
        funext other absent
        fin_cases other
        · exact probeRead.symm
        · exact (absent rfl).elim
      let candidate : PathCandidate (action (signature arity)) source redex
          (probeContext arity instrument) (previous.cons (probeFrame arity instrument)) :=
        { apex := receiver arity instrument
          inl := .nil
          inr := previous
          down := probeContext arity instrument
          comm := bodyRead
          fac_left := rfl
          fac_right := rfl }
      cases sameFrame
      have impossible := ipo_no_context_descent (action (signature arity)) source redex
        (probeContext arity instrument) (previous.cons (probeFrame arity instrument)) square ipo candidate
      change 1 = 0 at impossible
      omega

def reactionRule (rule : AdministrativeRule arity) :
    ReactionRule (.origin : ContextObject (signature arity)) where
  codomain := .interface rule.interface
  redex := termArrow (signature arity) rule.redex
  reactum := termArrow (signature arity) rule.reactum

/-- At the matching interface the actual minimal probe-labelled reaction is
equivalent to a root exposure and its complete reactum readout. -/
theorem probe_exposure_iff (instrument : Probe Symbols arity)
    (body redexBody : Value arity (receiver arity instrument))
    (reactum target : Value arity (result arity instrument)) :
    (∃ reaction : Context (signature arity) (result arity instrument) (result arity instrument),
      ∃ square : termArrow (signature arity) body ≫
          contextArrow (signature arity) (probeContext arity instrument) =
        termArrow (signature arity) (cut arity instrument (probe arity instrument) redexBody) ≫
          contextArrow (signature arity) reaction,
        IsIdemPushout (termArrow (signature arity) body)
          (termArrow (signature arity) (cut arity instrument (probe arity instrument) redexBody))
          (contextArrow (signature arity) (probeContext arity instrument))
          (contextArrow (signature arity) reaction) square ∧
        target = (action (signature arity)).path reaction reactum) ↔
      body = redexBody ∧ target = reactum := by
  constructor
  · rintro ⟨reaction, square, ipo, targetEq⟩
    have zero := probe_ipo_reaction_length arity instrument body
      (cut arity instrument (probe arity instrument) redexBody)
      (result_ne_probe arity instrument instrument) reaction square ipo
    have nil := Quiver.Path.eq_nil_of_length_zero reaction zero
    rw [nil] at square
    have values := Arrow.value.inj square
    rw [probeContext_fill] at values
    rw [nil] at targetEq
    change target = reactum at targetEq
    exact ⟨congrFun (Term.node.inj values) 1, targetEq⟩
  · rintro ⟨same, rfl⟩
    subst redexBody
    have square : termArrow (signature arity) body ≫
        contextArrow (signature arity) (probeContext arity instrument) =
      termArrow (signature arity) (cut arity instrument (probe arity instrument) body) ≫
        𝟙 (.interface (result arity instrument) : ContextObject (signature arity)) := by
      rw [Category.comp_id, termArrow_comp, probeContext_fill]
    exact ⟨.nil, square, ground_identityReactionIPO (action (signature arity)) body
      (cut arity instrument (probe arity instrument) body) (probeContext arity instrument) square, rfl⟩

end Mettapedia.OSLF.Framework.InstrumentCutContexts
