import Mettapedia.OSLF.Syntax.SortedConstructorContexts
import Mettapedia.OSLF.Framework.InstrumentObservations
import Mathlib.Tactic.FinCases

/-!
# Typed original-cut observer contexts

The closed one-sort source signature is extended by separate argument and
nullary-probe sorts. The interaction family contains the original binary cut
and its ask/get/build profiles. Each administrative left side is an actual
binary cut with a nullary probe in its first argument; the least-context
comparison uses the sorted constructor/context category.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.InstrumentCutContexts

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedConstructors
open Mettapedia.CategoryTheory.GroundPath

universe u

variable {Symbols : Type u} (arity : Symbols → Nat)

inductive Probe (Symbols : Type u) (arity : Symbols → Nat) where
  | ask (constructor : Symbols)
  | get (constructor : Symbols) (position : Fin (arity constructor))
  | build (constructor : Symbols)

inductive Srt (Symbols : Type u) (arity : Symbols → Nat) where
  | base
  | arguments (constructor : Symbols)
  | probe (instrument : Probe Symbols arity)

def receiver : Probe Symbols arity → Srt Symbols arity
  | .ask _ => .base
  | .get constructor _ => .arguments constructor
  | .build constructor => .arguments constructor

def result : Probe Symbols arity → Srt Symbols arity
  | .ask constructor => .arguments constructor
  | .get _ _ => .base
  | .build _ => .base

inductive Constructor (Symbols : Type u) (arity : Symbols → Nat) where
  | original (constructor : Symbols)
  | arguments (constructor : Symbols)
  | probe (instrument : Probe Symbols arity)
  | cut (instrument : Probe Symbols arity)

abbrev signature : Signature.{u,u} where
  Srt := Srt Symbols arity
  Constructor := Constructor Symbols arity
  arity
    | .original constructor => arity constructor
    | .arguments constructor => arity constructor
    | .probe _ => 0
    | .cut _ => 2
  input
    | .original _ => fun _ => .base
    | .arguments _ => fun _ => .base
    | .probe _ => Fin.elim0
    | .cut instrument => fun position => if position = 0 then .probe instrument else receiver arity instrument
  output
    | .original _ => .base
    | .arguments constructor => .arguments constructor
    | .probe instrument => .probe instrument
    | .cut instrument => result arity instrument

local instance instrumentCutContextsQuiver : Quiver (Srt Symbols arity) := frameQuiver (signature arity)

abbrev Value (sort : Srt Symbols arity) := Term (signature arity) sort

def original (constructor : Symbols) (arguments : Fin (arity constructor) → Value arity .base) :
    Value arity .base := Term.node (signature := signature arity) (Constructor.original constructor) arguments

def bundle (constructor : Symbols) (arguments : Fin (arity constructor) → Value arity .base) :
    Value arity (.arguments constructor) := Term.node (signature := signature arity) (Constructor.arguments constructor) arguments

def probe (instrument : Probe Symbols arity) : Value arity (.probe instrument) :=
  Term.node (signature := signature arity) (Constructor.probe instrument) (fun position => Fin.elim0 position)

def cut (instrument : Probe Symbols arity) (suppliedProbe : Value arity (.probe instrument))
    (body : Value arity (receiver arity instrument)) : Value arity (result arity instrument) :=
  Term.node (signature := signature arity) (Constructor.cut instrument)
    (Fin.cases suppliedProbe (fun position => by
      change Value arity (if position.succ = 0 then .probe instrument else receiver arity instrument)
      simpa only [Fin.succ_ne_zero, if_false] using body))

def probeFrame (instrument : Probe Symbols arity) :
    Frame (signature arity) (receiver arity instrument) (result arity instrument) :=
  Frame.slot (signature := signature arity) (Constructor.cut instrument) 1
    (Fin.cases (fun _ => probe arity instrument) (fun position absent => by
      have zero : position = 0 := Subsingleton.elim position 0
      subst position
      exact (absent rfl).elim))

def probeContext (instrument : Probe Symbols arity) :
    Context (signature arity) (receiver arity instrument) (result arity instrument) :=
  @Quiver.Hom.toPath (Srt Symbols arity) (frameQuiver (signature arity)) _ _ (probeFrame arity instrument)

theorem probeFrame_fill (instrument : Probe Symbols arity)
    (body : Value arity (receiver arity instrument)) :
    Frame.fill (probeFrame arity instrument) body = cut arity instrument (probe arity instrument) body := by
  simp only [probeFrame, Frame.fill, cut]
  congr 1
  funext position
  fin_cases position <;> rfl

theorem probeContext_fill (instrument : Probe Symbols arity)
    (body : Value arity (receiver arity instrument)) :
    (action (signature arity)).path (probeContext arity instrument) body =
      cut arity instrument (probe arity instrument) body := probeFrame_fill arity instrument body

/-- The source term is traversed and retains every original constructor. -/
def embedSource (source : InstrumentObservations.Tree Symbols arity) : Value arity .base :=
  @InstrumentObservations.Tree.rec Symbols arity (fun _ => Value arity .base)
    (fun constructor _ inductionHypothesis => original arity constructor inductionHypothesis) source

theorem embedSource_node (constructor : Symbols)
    (arguments : Fin (arity constructor) → InstrumentObservations.Tree Symbols arity) :
    embedSource arity (.node constructor arguments) =
      original arity constructor (fun position => embedSource arity (arguments position)) := rfl

/-- A selected binary source cut is a member of the same overloaded interaction
family as the observer cuts. No fresh unary eliminator replaces it. -/
structure OriginalCut (Symbols : Type u) (arity : Symbols → Nat) where
  symbol : Symbols
  binary : arity symbol = 2

inductive CutProfile (sourceCut : OriginalCut Symbols arity) where
  | proper
  | observer (instrument : Probe Symbols arity)

def cutConstructor (sourceCut : OriginalCut Symbols arity) : CutProfile arity sourceCut → Constructor Symbols arity
  | .proper => .original sourceCut.symbol
  | .observer instrument => .cut instrument

theorem cutConstructor_binary (sourceCut : OriginalCut Symbols arity) (profile : CutProfile arity sourceCut) :
    (signature arity).arity (cutConstructor arity sourceCut profile) = 2 := by
  cases profile with
  | proper => exact sourceCut.binary
  | observer => rfl

def originalCut (sourceCut : OriginalCut Symbols arity) (first second : Value arity .base) : Value arity .base :=
  original arity sourceCut.symbol (fun position => ![first, second] (Fin.cast sourceCut.binary position))

theorem sourceCut_retained (sourceCut : OriginalCut Symbols arity)
    (first second : InstrumentObservations.Tree Symbols arity) :
    embedSource arity (.node sourceCut.symbol
      (fun position => ![first, second] (Fin.cast sourceCut.binary position))) =
      originalCut arity sourceCut (embedSource arity first) (embedSource arity second) := by
  rw [embedSource_node]
  apply congrArg (original arity sourceCut.symbol)
  funext position
  generalize Fin.cast sourceCut.binary position = index
  fin_cases index <;> rfl

structure AdministrativeRule where
  interface : Srt Symbols arity
  redex : Value arity interface
  reactum : Value arity interface

def askRule (constructor : Symbols) (arguments : Fin (arity constructor) → Value arity .base) :
    AdministrativeRule arity where
  interface := .arguments constructor
  redex := cut arity (.ask constructor) (probe arity (.ask constructor)) (original arity constructor arguments)
  reactum := bundle arity constructor arguments

def getRule (constructor : Symbols) (arguments : Fin (arity constructor) → Value arity .base)
    (position : Fin (arity constructor)) : AdministrativeRule arity where
  interface := .base
  redex := cut arity (.get constructor position) (probe arity (.get constructor position))
    (bundle arity constructor arguments)
  reactum := arguments position

def buildRule (constructor : Symbols) (arguments : Fin (arity constructor) → Value arity .base) :
    AdministrativeRule arity where
  interface := .base
  redex := cut arity (.build constructor) (probe arity (.build constructor)) (bundle arity constructor arguments)
  reactum := original arity constructor arguments

end Mettapedia.OSLF.Framework.InstrumentCutContexts
