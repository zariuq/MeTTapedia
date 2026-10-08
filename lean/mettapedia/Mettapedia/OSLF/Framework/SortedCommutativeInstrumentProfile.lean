import Mettapedia.OSLF.Framework.SortedCommutativeContextReactiveSystem
import Mettapedia.OSLF.Framework.InstrumentCutContexts

/-!
# Sorted observer profiles for a genuine designated AC1 Cut

The source retains its ordinary constructors, original binary Cut and unit.
The observer extension adds actual fresh bundle and probe sorts. Its overloaded
administrative Cuts are free typed binary constructors, not parallel Cut at
those sorts. Ask, get and build retain every supplied argument and selected
position. Their occurrences retain independently supplied origins; matching
modulo equations may be nondeterministic and is not a root-view function.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedCommutativeInstruments

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedCommutative

universe u w

inductive SourceSymbol (Symbols : Type u) where
  | ordinary (symbol : Symbols)
  | properCut
  | unit

variable {Symbols : Type u} (arity : Symbols → Nat)

abbrev sourceArity : SourceSymbol Symbols → Nat
  | .ordinary symbol => arity symbol
  | .properCut => 2
  | .unit => 0

abbrev Probe := InstrumentCutContexts.Probe (SourceSymbol Symbols) (sourceArity arity)
abbrev Srt := InstrumentCutContexts.Srt (SourceSymbol Symbols) (sourceArity arity)

inductive Constructor where
  | original (symbol : Symbols)
  | arguments (constructor : SourceSymbol Symbols)
  | probe (instrument : Probe arity)
  | cut (instrument : Probe arity)

abbrev signature : Mettapedia.OSLF.SortedConstructors.Signature.{u,u} where
  Srt := Srt arity
  Constructor := Constructor arity
  arity
    | .original symbol => arity symbol
    | .arguments constructor => sourceArity arity constructor
    | .probe _ => 0
    | .cut _ => 2
  input
    | .original _ => fun _ => .base
    | .arguments _ => fun _ => .base
    | .probe _ => Fin.elim0
    | .cut instrument => fun position => if position = 0 then .probe instrument
        else InstrumentCutContexts.receiver (sourceArity arity) instrument
  output
    | .original _ => .base
    | .arguments constructor => .arguments constructor
    | .probe instrument => .probe instrument
    | .cut instrument => InstrumentCutContexts.result (sourceArity arity) instrument

def Parallel (sort : Srt arity) : Prop := sort = .base

abbrev Value (sort : Srt arity) := Term (signature arity) (Parallel arity) sort
abbrev ValueClass (sort : Srt arity) := Class (signature arity) (Parallel arity) sort
abbrev ContextCategory := RawObject (signature arity) (Parallel arity)
abbrev SourceTerm := InstrumentObservations.Tree (SourceSymbol Symbols) (sourceArity arity)

def sourceNode (constructor : SourceSymbol Symbols)
    (arguments : Fin (sourceArity arity constructor) → Value arity .base) : Value arity .base := by
  cases constructor with
  | ordinary symbol =>
    exact Term.node (signature := signature arity) (Parallel := Parallel arity)
      (Constructor.original symbol) arguments
  | properCut => exact .cut rfl (arguments 0) (arguments 1)
  | unit => exact .zero rfl

def embedSource (source : SourceTerm arity) : Value arity .base :=
  @InstrumentObservations.Tree.rec (SourceSymbol Symbols) (sourceArity arity) (fun _ => Value arity .base)
    (fun constructor _ inductionHypothesis => sourceNode arity constructor inductionHypothesis) source

theorem embedSource_node (constructor : SourceSymbol Symbols)
    (arguments : Fin (sourceArity arity constructor) → SourceTerm arity) :
    embedSource arity (.node constructor arguments) =
      sourceNode arity constructor (fun position => embedSource arity (arguments position)) := rfl

def originalCut : InstrumentCutContexts.OriginalCut (SourceSymbol Symbols) (sourceArity arity) :=
  ⟨.properCut, rfl⟩

def cutConstructor : InstrumentCutContexts.CutProfile (sourceArity arity) (originalCut arity) →
    (syntaxSignature (signature arity) (Parallel arity)).Constructor
  | .proper => .cut .base rfl
  | .observer instrument => .ordinary (.cut instrument)

theorem cutConstructor_binary (profile : InstrumentCutContexts.CutProfile (sourceArity arity) (originalCut arity)) :
    (syntaxSignature (signature arity) (Parallel arity)).arity (cutConstructor arity profile) = 2 := by
  cases profile <;> rfl

theorem originalCut_retained (first second : SourceTerm arity) :
    embedSource arity (.node (originalCut arity).symbol (Fin.cases first (fun _ => second))) =
      .cut rfl (embedSource arity first) (embedSource arity second) := rfl

def bundle (constructor : SourceSymbol Symbols)
    (arguments : Fin (sourceArity arity constructor) → Value arity .base) : Value arity (.arguments constructor) :=
  .node (signature := signature arity) (.arguments constructor) arguments

def probe (instrument : Probe arity) : Value arity (.probe instrument) :=
  .node (signature := signature arity) (.probe instrument) (fun position => Fin.elim0 position)

def cut (instrument : Probe arity) (suppliedProbe : Value arity (.probe instrument))
    (body : Value arity (InstrumentCutContexts.receiver (sourceArity arity) instrument)) :
    Value arity (InstrumentCutContexts.result (sourceArity arity) instrument) :=
  .node (signature := signature arity) (.cut instrument)
    (Fin.cases suppliedProbe (fun position => by
      change Value arity (if position.succ = 0 then .probe instrument
        else InstrumentCutContexts.receiver (sourceArity arity) instrument)
      simpa only [Fin.succ_ne_zero, if_false] using body))

def probeContext (instrument : Probe arity) :
    RawContext (signature arity) (Parallel arity)
      (InstrumentCutContexts.receiver (sourceArity arity) instrument)
      (InstrumentCutContexts.result (sourceArity arity) instrument) :=
  RawContext.frame (signature := signature arity) (Parallel := Parallel arity) (Constructor.cut instrument) 1
    (Fin.cases (fun _ => probe arity instrument) (fun position absent => by
      have zero : position = 0 := Subsingleton.elim position 0
      subst position
      exact (absent rfl).elim)) .hole

theorem probeContext_fill (instrument : Probe arity)
    (body : Value arity (InstrumentCutContexts.receiver (sourceArity arity) instrument)) :
    (probeContext arity instrument).fill body = cut arity instrument (probe arity instrument) body := by
  apply congrArg (Term.node (signature := signature arity) (.cut instrument))
  funext position
  fin_cases position <;> rfl

theorem arguments_not_parallel (constructor : SourceSymbol Symbols) :
    ¬Parallel arity (.arguments constructor) := by
  intro same
  cases same

theorem probe_not_parallel (instrument : Probe arity) : ¬Parallel arity (.probe instrument) := by
  intro same
  cases same

structure AdministrativeRule where
  interface : Srt arity
  redex : Value arity interface
  reactum : Value arity interface

def askRule (constructor : SourceSymbol Symbols)
    (arguments : Fin (sourceArity arity constructor) → Value arity .base) : AdministrativeRule arity where
  interface := .arguments constructor
  redex := cut arity (.ask constructor) (probe arity (.ask constructor)) (sourceNode arity constructor arguments)
  reactum := bundle arity constructor arguments

def getRule (constructor : SourceSymbol Symbols)
    (arguments : Fin (sourceArity arity constructor) → Value arity .base)
    (position : Fin (sourceArity arity constructor)) : AdministrativeRule arity where
  interface := .base
  redex := cut arity (.get constructor position) (probe arity (.get constructor position)) (bundle arity constructor arguments)
  reactum := arguments position

def buildRule (constructor : SourceSymbol Symbols)
    (arguments : Fin (sourceArity arity constructor) → Value arity .base) : AdministrativeRule arity where
  interface := .base
  redex := cut arity (.build constructor) (probe arity (.build constructor)) (bundle arity constructor arguments)
  reactum := sourceNode arity constructor arguments

def AdministrativeRule.rule (supplied : AdministrativeRule arity) :
    Mettapedia.GSLT.RedexRelativeCongruence.ReactionRule (.origin : ContextCategory arity) where
  codomain := .interface supplied.interface
  redex := RawArrow.value (classOf supplied.redex)
  reactum := RawArrow.value (classOf supplied.reactum)

inductive Occurrence (Origins : Type w) where
  | ask (origin : Origins) (constructor : SourceSymbol Symbols)
      (arguments : Fin (sourceArity arity constructor) → Value arity .base)
  | get (origin : Origins) (constructor : SourceSymbol Symbols)
      (arguments : Fin (sourceArity arity constructor) → Value arity .base)
      (position : Fin (sourceArity arity constructor))
  | build (origin : Origins) (constructor : SourceSymbol Symbols)
      (arguments : Fin (sourceArity arity constructor) → Value arity .base)

variable {arity} {Origins : Type w}

def Occurrence.origin : Occurrence arity Origins → Origins
  | .ask origin _ _ => origin
  | .get origin _ _ _ => origin
  | .build origin _ _ => origin

def Occurrence.administrative : Occurrence arity Origins → AdministrativeRule arity
  | .ask _ constructor arguments => askRule arity constructor arguments
  | .get _ constructor arguments position => getRule arity constructor arguments position
  | .build _ constructor arguments => buildRule arity constructor arguments

def Occurrence.rule (supplied : Occurrence arity Origins) := (supplied.administrative).rule arity

def rules (arity : Symbols → Nat) (Origins : Type w) :
    Mettapedia.GSLT.RedexRelativeCongruence.ReactionRule (.origin : ContextCategory arity) → Prop :=
  fun rule => ∃ supplied : Occurrence arity Origins, supplied.rule = rule

theorem redex_relativePushouts {first second : ContextCategory arity}
    (agent : (.origin : ContextCategory arity) ⟶ first) (redex : (.origin : ContextCategory arity) ⟶ second) :
    Mettapedia.GSLT.RelativePushout.HasRelativePushouts agent redex := raw_redex_relativePushouts agent redex

theorem bisimulation_congruence {source target : ContextCategory arity}
    {first second : (.origin : ContextCategory arity) ⟶ source}
    (related : Mettapedia.GSLT.RedexRelativeCongruence.IPOBisimilar (rules arity Origins) first second)
    (context : source ⟶ target) :
    Mettapedia.GSLT.RedexRelativeCongruence.IPOBisimilar (rules arity Origins) (first ≫ context) (second ≫ context) :=
  raw_bisimulation_congruence (rules arity Origins) related context

end Mettapedia.OSLF.Framework.SortedCommutativeInstruments
