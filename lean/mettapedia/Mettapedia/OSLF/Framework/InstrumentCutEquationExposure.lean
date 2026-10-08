import Mettapedia.OSLF.Framework.InstrumentCutReactions
import Mettapedia.OSLF.Syntax.SortedConstructorPaddingRelativePushout

/-!
# Equation-class exposure by the original-cut probe contexts

Unary-unit equations act on actual terms and actual typed contexts. The
exposure judgment below uses the quotient category's actual IPO universal
property and complete target readout. Normalization transports that judgment
through the earned based equivalence; root matching is equality of authored
term classes, rather than a raw root inspection.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.InstrumentCutContexts

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedConstructors
open Mettapedia.OSLF.SortedConstructors.Padding
open Mettapedia.CategoryTheory.GroundPath
open Mettapedia.GSLT.RelativePushout

universe u

variable {Symbols : Type u} (arity : Symbols → Nat)

local instance instrumentCutEquationExposureQuiver : Quiver (Srt Symbols arity) := frameQuiver (signature arity)

abbrev EqObject := EquationObject (signature arity) (Srt.base : Srt Symbols arity)

def probeClass (instrument : Probe Symbols arity) :
    ContextClass (signature arity) .base (receiver arity instrument) (result arity instrument) :=
  contextClassOf (embedContext (signature arity) .base (probeContext arity instrument))

def equationProbeLabel (instrument : Probe Symbols arity) :
    (.interface (receiver arity instrument) : EqObject arity) ⟶ .interface (result arity instrument) :=
  classContextArrow (signature arity) .base (probeClass arity instrument)

theorem probeClass_value (instrument : Probe Symbols arity) :
    contextValue (signature arity) .base (probeClass arity instrument) = probeContext arity instrument :=
  normalize_embedContext (signature arity) .base (probeContext arity instrument)

theorem value_classFill {source target : (signature arity).Srt}
    (term : Class (signature arity) .base source)
    (context : ContextClass (signature arity) .base source target) :
    value (signature arity) .base (classFill term context) =
      (action (signature arity)).path (contextValue (signature arity) .base context)
        (value (signature arity) .base term) :=
  Arrow.value.inj (EquationArrow.down_comp (EquationArrow.value term) (EquationArrow.context context))

theorem value_probeFill (instrument : Probe Symbols arity)
    (term : Class (signature arity) .base (receiver arity instrument)) :
    value (signature arity) .base (classFill term (probeClass arity instrument)) =
      cut arity instrument (probe arity instrument) (value (signature arity) .base term) := by
  rw [value_classFill, probeClass_value]
  exact probeContext_fill arity instrument (value (signature arity) .base term)

theorem classFill_nil {sort : Srt Symbols arity}
    (term : Class (signature arity) .base sort) :
    classFill term (contextClassOf (@Quiver.Path.nil (Srt Symbols arity)
      (frameQuiver (extended (signature arity) .base)) sort)) = term := by
  induction term using Quotient.inductionOn with
  | _ supplied => rfl

def EquationProbeExposure (instrument : Probe Symbols arity)
    (body redexBody : Class (signature arity) .base (receiver arity instrument))
    (output target : Class (signature arity) .base (result arity instrument)) : Prop :=
  ∃ reaction : ContextClass (signature arity) .base (result arity instrument) (result arity instrument),
    ∃ square : classTermArrow (signature arity) .base body ≫ equationProbeLabel arity instrument =
      classTermArrow (signature arity) .base (classFill redexBody (probeClass arity instrument)) ≫
        classContextArrow (signature arity) .base reaction,
      IsIdemPushout (classTermArrow (signature arity) .base body)
        (classTermArrow (signature arity) .base (classFill redexBody (probeClass arity instrument)))
        (equationProbeLabel arity instrument) (classContextArrow (signature arity) .base reaction) square ∧
      target = classFill output reaction

set_option backward.isDefEq.respectTransparency false in
theorem equationProbeExposure_iff (instrument : Probe Symbols arity)
    (body redexBody : Class (signature arity) .base (receiver arity instrument))
    (output target : Class (signature arity) .base (result arity instrument)) :
    EquationProbeExposure arity instrument body redexBody output target ↔
      body = redexBody ∧ target = output := by
  let F := normalizationFunctor (signature arity) (Srt.base : Srt Symbols arity)
  constructor
  · rintro ⟨reaction, square, ipo, targetEq⟩
    have mappedSquare := congrArg F.map square
    rw [Functor.map_comp, Functor.map_comp] at mappedSquare
    change termArrow (signature arity) (value (signature arity) .base body) ≫
        contextArrow (signature arity) (contextValue (signature arity) .base (probeClass arity instrument)) =
      termArrow (signature arity) (value (signature arity) .base (classFill redexBody (probeClass arity instrument))) ≫
        contextArrow (signature arity) (contextValue (signature arity) .base reaction) at mappedSquare
    rw [probeClass_value, value_probeFill] at mappedSquare
    have mappedIPO := (equation_idemPushout_iff (signature arity) .base
      (classTermArrow (signature arity) .base body)
      (classTermArrow (signature arity) .base (classFill redexBody (probeClass arity instrument)))
      (equationProbeLabel arity instrument) (classContextArrow (signature arity) .base reaction) square).mp ipo
    change IsIdemPushout (termArrow (signature arity) (value (signature arity) .base body))
      (termArrow (signature arity) (value (signature arity) .base (classFill redexBody (probeClass arity instrument))))
      (contextArrow (signature arity) (contextValue (signature arity) .base (probeClass arity instrument)))
      (contextArrow (signature arity) (contextValue (signature arity) .base reaction)) _ at mappedIPO
    have normalizedIPO : IsIdemPushout
        (termArrow (signature arity) (value (signature arity) .base body))
        (termArrow (signature arity) (cut arity instrument (probe arity instrument)
          (value (signature arity) .base redexBody)))
        (contextArrow (signature arity) (probeContext arity instrument))
        (contextArrow (signature arity) (contextValue (signature arity) .base reaction)) mappedSquare := by
      simpa only [probeClass_value, value_probeFill] using mappedIPO
    have mappedTarget : value (signature arity) .base target =
        (action (signature arity)).path (contextValue (signature arity) .base reaction)
          (value (signature arity) .base output) :=
      (congrArg (value (signature arity) .base) targetEq).trans (value_classFill arity output reaction)
    have exposed := (probe_exposure_iff arity instrument
      (value (signature arity) .base body) (value (signature arity) .base redexBody)
      (value (signature arity) .base output) (value (signature arity) .base target)).mp
        ⟨contextValue (signature arity) .base reaction, mappedSquare, normalizedIPO, mappedTarget⟩
    exact ⟨(termEquiv (signature arity) .base _).injective exposed.1,
      (termEquiv (signature arity) .base _).injective exposed.2⟩
  · rintro ⟨rfl, rfl⟩
    let reaction : ContextClass (signature arity) .base (result arity instrument) (result arity instrument) :=
      contextClassOf (@Quiver.Path.nil (Srt Symbols arity)
        (frameQuiver (extended (signature arity) .base)) (result arity instrument))
    have square : classTermArrow (signature arity) .base body ≫ equationProbeLabel arity instrument =
        classTermArrow (signature arity) .base (classFill body (probeClass arity instrument)) ≫
          classContextArrow (signature arity) .base reaction := by
      change EquationArrow.value (classFill body (probeClass arity instrument)) =
        EquationArrow.value (classFill (classFill body (probeClass arity instrument)) reaction)
      apply congrArg EquationArrow.value
      exact (classFill_nil arity (classFill body (probeClass arity instrument))).symm
    have mappedSquare := congrArg F.map square
    rw [Functor.map_comp, Functor.map_comp] at mappedSquare
    change termArrow (signature arity) (value (signature arity) .base body) ≫
        contextArrow (signature arity) (contextValue (signature arity) .base (probeClass arity instrument)) =
      termArrow (signature arity) (value (signature arity) .base (classFill body (probeClass arity instrument))) ≫
        𝟙 (.interface (result arity instrument) : ContextObject (signature arity)) at mappedSquare
    rw [probeClass_value, value_probeFill] at mappedSquare
    have mappedIPO := ground_identityReactionIPO (action (signature arity))
      (value (signature arity) .base body)
      (cut arity instrument (probe arity instrument) (value (signature arity) .base body))
      (probeContext arity instrument) mappedSquare
    have ipo : IsIdemPushout (classTermArrow (signature arity) .base body)
        (classTermArrow (signature arity) .base (classFill body (probeClass arity instrument)))
        (equationProbeLabel arity instrument) (classContextArrow (signature arity) .base reaction) square := by
      apply (equation_idemPushout_iff (signature arity) .base _ _ _ _ square).mpr
      change IsIdemPushout (termArrow (signature arity) (value (signature arity) .base body))
        (termArrow (signature arity) (value (signature arity) .base (classFill body (probeClass arity instrument))))
        (contextArrow (signature arity) (contextValue (signature arity) .base (probeClass arity instrument)))
        (𝟙 (.interface (result arity instrument) : ContextObject (signature arity))) _
      simp only [probeClass_value, value_probeFill]
      exact mappedIPO
    refine ⟨reaction, square, ipo, ?_⟩
    exact (classFill_nil arity target).symm

/-- At actual supplied raw representatives, exposure is precisely the
authored equation judgment and equality of complete result classes. -/
theorem equationProbeExposure_raw_iff (instrument : Probe Symbols arity)
    (body redexBody : RawTerm (signature arity) .base (receiver arity instrument))
    (output target : RawTerm (signature arity) .base (result arity instrument)) :
    EquationProbeExposure arity instrument (classOf body) (classOf redexBody)
      (classOf output) (classOf target) ↔
      Equation (signature arity) .base body redexBody ∧ Equation (signature arity) .base target output := by
  rw [equationProbeExposure_iff, classOf_eq_iff, classOf_eq_iff]

end Mettapedia.OSLF.Framework.InstrumentCutContexts
