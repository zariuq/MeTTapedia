import Mettapedia.OSLF.Framework.InstrumentCutExposure

/-!
# Full administrative probe reactions with retained authored occurrences

The rule family contains actual ask/get/build redexes and complete targets.
Its labelled relation is the shared categorical IPO relation. Occurrences
retain the supplied origin and argument trees; support never silently assumes
that an arbitrary origin type is inhabited.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.InstrumentCutContexts

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedConstructors
open Mettapedia.CategoryTheory.GroundPath
open Mettapedia.GSLT.RelativePushout
open Mettapedia.GSLT.RedexRelativeCongruence

universe u w

variable {Symbols : Type u} (arity : Symbols → Nat)

local instance instrumentCutReactionsQuiver : Quiver (Srt Symbols arity) := frameQuiver (signature arity)

inductive AdministrativeInstance : Probe Symbols arity → Type u where
  | ask (constructor : Symbols) (arguments : Fin (arity constructor) → Value arity .base) :
      AdministrativeInstance (.ask constructor)
  | get (constructor : Symbols) (position : Fin (arity constructor))
      (arguments : Fin (arity constructor) → Value arity .base) :
      AdministrativeInstance (.get constructor position)
  | build (constructor : Symbols) (arguments : Fin (arity constructor) → Value arity .base) :
      AdministrativeInstance (.build constructor)

namespace AdministrativeInstance

def body : {instrument : Probe Symbols arity} → AdministrativeInstance arity instrument →
    Value arity (receiver arity instrument)
  | _, .ask constructor arguments => original arity constructor arguments
  | _, .get constructor _ arguments => bundle arity constructor arguments
  | _, .build constructor arguments => bundle arity constructor arguments

def output : {instrument : Probe Symbols arity} → AdministrativeInstance arity instrument →
    Value arity (result arity instrument)
  | _, .ask constructor arguments => bundle arity constructor arguments
  | _, .get _ position arguments => arguments position
  | _, .build constructor arguments => original arity constructor arguments

def rule {instrument : Probe Symbols arity} (instance_ : AdministrativeInstance arity instrument) :
    ReactionRule (.origin : ContextObject (signature arity)) where
  codomain := .interface (result arity instrument)
  redex := termArrow (signature arity) (cut arity instrument (probe arity instrument) instance_.body)
  reactum := termArrow (signature arity) instance_.output

end AdministrativeInstance

structure AdministrativeOccurrence (Origins : Type w) (instrument : Probe Symbols arity) where
  origin : Origins
  instance_ : AdministrativeInstance arity instrument

def administrativeRules (Origins : Type w) (rule : ReactionRule (.origin : ContextObject (signature arity))) : Prop :=
  ∃ instrument : Probe Symbols arity, ∃ occurrence : AdministrativeOccurrence arity Origins instrument,
    rule = occurrence.instance_.rule

theorem zero_path_head {source target : Srt Symbols arity}
    (path : Context (signature arity) source target) (supplied : Value arity source)
    (zero : path.length = 0) : ((action (signature arity)).path path supplied).head = supplied.head := by
  cases path with
  | nil => rfl
  | cons previous frame => simp only [Quiver.Path.length_cons] at zero; omega

/-- The full rule family cannot hide another administrative redex behind the
same probe label: its nonempty common outer frame violates IPO minimality. -/
theorem administrative_step_iff (Origins : Type w) (instrument : Probe Symbols arity)
    (source : Value arity (receiver arity instrument)) (target : Value arity (result arity instrument)) :
    ActIPO (administrativeRules arity Origins)
      (contextArrow (signature arity) (probeContext arity instrument))
      (termArrow (signature arity) source) (termArrow (signature arity) target) ↔
      ∃ occurrence : AdministrativeOccurrence arity Origins instrument,
        source = occurrence.instance_.body ∧ target = occurrence.instance_.output := by
  constructor
  · rintro ⟨rule, ⟨other, occurrence, rfl⟩, reaction, square, ipo, targetEq⟩
    cases reaction with
    | context path =>
      have zero := probe_ipo_reaction_length arity instrument source
        (cut arity other (probe arity other) occurrence.instance_.body)
        (result_ne_probe arity other instrument) path square ipo
      have values := Arrow.value.inj square
      have heads := Term.head_eq (signature := signature arity) _ _ values
      have same : instrument = other := by
        apply Constructor.cut.inj
        exact (show Constructor.cut instrument =
          ((action (signature arity)).path path
            (cut arity other (probe arity other) occurrence.instance_.body)).head from heads).trans
          (zero_path_head arity path _ zero)
      subst other
      have nil := Quiver.Path.eq_nil_of_length_zero path zero
      rw [nil] at square targetEq
      have exposed := Arrow.value.inj square
      rw [probeContext_fill] at exposed
      exact ⟨occurrence, congrFun (Term.node.inj exposed) 1, Arrow.value.inj targetEq⟩
  · rintro ⟨occurrence, rfl, rfl⟩
    let rule := occurrence.instance_.rule
    have square : termArrow (signature arity) occurrence.instance_.body ≫
        contextArrow (signature arity) (probeContext arity instrument) =
        rule.redex ≫ 𝟙 rule.codomain := by
      rw [Category.comp_id, termArrow_comp, probeContext_fill]
      rfl
    exact ⟨rule, ⟨instrument, occurrence, rfl⟩, 𝟙 rule.codomain, square,
      ground_identityReactionIPO (action (signature arity)) occurrence.instance_.body
        (cut arity instrument (probe arity instrument) occurrence.instance_.body)
        (probeContext arity instrument) square, rfl⟩

structure FiringReceipt (Origins : Type w) (instrument : Probe Symbols arity)
    (source : Value arity (receiver arity instrument)) (target : Value arity (result arity instrument)) where
  occurrence : AdministrativeOccurrence arity Origins instrument
  source_readout : source = occurrence.instance_.body
  target_readout : target = occurrence.instance_.output

theorem FiringReceipt.step {Origins : Type w} {instrument : Probe Symbols arity}
    {source : Value arity (receiver arity instrument)} {target : Value arity (result arity instrument)}
    (receipt : FiringReceipt arity Origins instrument source target) :
    ActIPO (administrativeRules arity Origins)
      (contextArrow (signature arity) (probeContext arity instrument))
      (termArrow (signature arity) source) (termArrow (signature arity) target) :=
  (administrative_step_iff arity Origins instrument source target).mpr
    ⟨receipt.occurrence, receipt.source_readout, receipt.target_readout⟩

theorem firingReceipt_support {Origins : Type w} {instrument : Probe Symbols arity}
    {source : Value arity (receiver arity instrument)} {target : Value arity (result arity instrument)} :
    Nonempty (FiringReceipt arity Origins instrument source target) ↔
      ActIPO (administrativeRules arity Origins)
        (contextArrow (signature arity) (probeContext arity instrument))
        (termArrow (signature arity) source) (termArrow (signature arity) target) := by
  constructor
  · rintro ⟨receipt⟩; exact receipt.step
  · intro step
    obtain ⟨occurrence, first, second⟩ := (administrative_step_iff arity Origins instrument source target).mp step
    exact ⟨⟨occurrence, first, second⟩⟩

end Mettapedia.OSLF.Framework.InstrumentCutContexts
