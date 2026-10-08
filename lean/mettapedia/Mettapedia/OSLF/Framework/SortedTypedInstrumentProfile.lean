import Mettapedia.OSLF.Framework.SortedCommutativeContextReactiveSystem
import Mathlib.Tactic.FinCases

/-!
# Heterogeneous source profiles and actual sorted administrative instruments

Every original constructor retains its declared ordered input and output
sorts. Designated AC1 Cut and unit heads exist only at an independently
admitted parallel sort. Fresh argument bundles retain heterogeneous source
coordinates; get returns its selected coordinate at that original sort.

Fresh probe sorts are rigid and have no parallel structure. No inhabitant or
unit is supplied at an arbitrary original sort, and no total source erasure
is used. Source terms are recursively included through their actual typed
constructors, designated Cuts and units.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedTypedInstruments

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedCommutative
open Mettapedia.GSLT.RedexRelativeCongruence

universe u v

inductive SourceHead (source : Mettapedia.OSLF.SortedConstructors.Signature.{u,v})
    (Parallel : source.Srt → Prop) : Type (max u v) where
  | ordinary (constructor : source.Constructor)
  | properCut (sort : source.Srt) (parallel : Parallel sort)
  | unit (sort : source.Srt) (parallel : Parallel sort)

variable {source : Mettapedia.OSLF.SortedConstructors.Signature.{u,v}}
  {Parallel : source.Srt → Prop}

abbrev headArity : SourceHead source Parallel → Nat
  | .ordinary constructor => source.arity constructor
  | .properCut _ _ => 2
  | .unit _ _ => 0

def headInput : (head : SourceHead source Parallel) → Fin (headArity head) → source.Srt
  | .ordinary constructor => source.input constructor
  | .properCut sort _ => fun _ => sort
  | .unit _ _ => Fin.elim0

def headOutput : SourceHead source Parallel → source.Srt
  | .ordinary constructor => source.output constructor
  | .properCut sort _ => sort
  | .unit sort _ => sort

inductive Probe (source : Mettapedia.OSLF.SortedConstructors.Signature.{u,v})
    (Parallel : source.Srt → Prop) : Type (max u v) where
  | ask (head : SourceHead source Parallel)
  | get (head : SourceHead source Parallel) (position : Fin (headArity head))
  | build (head : SourceHead source Parallel)

inductive Srt (source : Mettapedia.OSLF.SortedConstructors.Signature.{u,v})
    (Parallel : source.Srt → Prop) : Type (max u v) where
  | original (sort : source.Srt)
  | arguments (head : SourceHead source Parallel)
  | probe (instrument : Probe source Parallel)

def receiver : Probe source Parallel → Srt source Parallel
  | .ask head => .original (headOutput head)
  | .get head _ => .arguments head
  | .build head => .arguments head

def result : Probe source Parallel → Srt source Parallel
  | .ask head => .arguments head
  | .get head position => .original (headInput head position)
  | .build head => .original (headOutput head)

inductive Constructor (source : Mettapedia.OSLF.SortedConstructors.Signature.{u,v})
    (Parallel : source.Srt → Prop) : Type (max u v) where
  | original (constructor : source.Constructor)
  | arguments (head : SourceHead source Parallel)
  | probe (instrument : Probe source Parallel)
  | cut (instrument : Probe source Parallel)

abbrev signature (source : Mettapedia.OSLF.SortedConstructors.Signature.{u,v})
    (Parallel : source.Srt → Prop) : Mettapedia.OSLF.SortedConstructors.Signature.{max u v,max u v} where
  Srt := Srt source Parallel
  Constructor := Constructor source Parallel
  arity
    | .original constructor => source.arity constructor
    | .arguments head => headArity head
    | .probe _ => 0
    | .cut _ => 2
  input
    | .original constructor => fun position => .original (source.input constructor position)
    | .arguments head => fun position => .original (headInput head position)
    | .probe _ => Fin.elim0
    | .cut instrument => fun position => if position = 0 then .probe instrument else receiver instrument
  output
    | .original constructor => .original (source.output constructor)
    | .arguments head => .arguments head
    | .probe instrument => .probe instrument
    | .cut instrument => result instrument

def NativeParallel : Srt source Parallel → Prop
  | .original sort => Parallel sort
  | .arguments _ => False
  | .probe _ => False

abbrev Value (sort : Srt source Parallel) := Term (signature source Parallel) NativeParallel sort
abbrev ValueClass (sort : Srt source Parallel) := Class (signature source Parallel) NativeParallel sort
abbrev ContextCategory (source : Mettapedia.OSLF.SortedConstructors.Signature.{u,v})
    (Parallel : source.Srt → Prop) := RawObject (signature source Parallel) NativeParallel

abbrev Arguments (head : SourceHead source Parallel) :=
  (position : Fin (headArity head)) →
    Value (source := source) (Parallel := Parallel) (.original (headInput head position))

def sourceNode (head : SourceHead source Parallel) (arguments : Arguments head) :
    Value (source := source) (Parallel := Parallel) (.original (headOutput head)) := by
  cases head with
  | ordinary constructor =>
    exact .node (signature := signature source Parallel)
      (Parallel := NativeParallel) (.original constructor) arguments
  | properCut sort parallel => exact .cut parallel (arguments 0) (arguments 1)
  | unit sort parallel => exact .zero parallel

def bundle (head : SourceHead source Parallel) (arguments : Arguments head) : Value (.arguments head) :=
  .node (signature := signature source Parallel) (Parallel := NativeParallel) (.arguments head) arguments

def probe (instrument : Probe source Parallel) : Value (.probe instrument) :=
  .node (signature := signature source Parallel) (Parallel := NativeParallel)
    (.probe instrument) (fun position => Fin.elim0 position)

def cut (instrument : Probe source Parallel) (suppliedProbe : Value (.probe instrument))
    (body : Value (receiver instrument)) : Value (result instrument) :=
  .node (signature := signature source Parallel) (Parallel := NativeParallel)
    (.cut instrument) (Fin.cases suppliedProbe (fun position => by
    change Value (if position.succ = 0 then .probe instrument else receiver instrument)
    simpa only [Fin.succ_ne_zero, if_false] using body))

def probeContext (instrument : Probe source Parallel) :
    RawContext (signature source Parallel) NativeParallel (receiver instrument) (result instrument) :=
  RawContext.frame (signature := signature source Parallel) (Parallel := NativeParallel) (.cut instrument) 1
    (Fin.cases (fun _ => probe instrument) (fun position absent => by
      have zero : position = 0 := Subsingleton.elim position 0
      subst position
      exact (absent rfl).elim)) .hole

theorem probeContext_fill (instrument : Probe source Parallel) (body : Value (receiver instrument)) :
    (probeContext instrument).fill body = cut instrument (probe instrument) body := by
  apply congrArg (Term.node (signature := signature source Parallel) (Parallel := NativeParallel)
    (.cut instrument))
  funext position
  fin_cases position <;> rfl

def embed {sort : source.Srt} : Term source Parallel sort →
    Value (source := source) (Parallel := Parallel) (.original sort)
  | .zero parallel => .zero parallel
  | .cut parallel first second => .cut parallel (embed first) (embed second)
  | .node constructor arguments =>
      .node (signature := signature source Parallel) (Parallel := NativeParallel)
        (.original constructor) (fun position => embed (arguments position))

theorem embed_zero {sort : source.Srt} (parallel : Parallel sort) :
    embed (.zero parallel) =
      (.zero parallel : Value (source := source) (Parallel := Parallel) (.original sort)) := rfl

theorem embed_cut {sort : source.Srt} (parallel : Parallel sort)
    (first second : Term source Parallel sort) :
    embed (.cut parallel first second) = .cut parallel (embed first) (embed second) := rfl

theorem embed_node (constructor : source.Constructor)
    (arguments : (position : Fin (source.arity constructor)) → Term source Parallel (source.input constructor position)) :
    embed (.node constructor arguments) =
      .node (signature := signature source Parallel) (Parallel := NativeParallel)
        (.original constructor) (fun position => embed (arguments position)) := rfl

theorem embed_equation {sort : source.Srt} {first second : Term source Parallel sort}
    (equation : Equation first second) : Equation (embed first) (embed second) := by
  induction equation with
  | refl first => exact .refl (embed first)
  | symm _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ firstInduction secondInduction => exact firstInduction.trans secondInduction
  | cut parallel _ _ firstInduction secondInduction =>
    exact Equation.cut (signature := signature source Parallel) (Parallel := NativeParallel)
      (sort := .original _)
      parallel firstInduction secondInduction
  | node _ inductionHypothesis => exact .node inductionHypothesis
  | assoc parallel first second third =>
    exact Equation.assoc (signature := signature source Parallel) (Parallel := NativeParallel)
      (sort := .original _)
      parallel (embed first) (embed second) (embed third)
  | comm parallel first second =>
    exact Equation.comm (signature := signature source Parallel) (Parallel := NativeParallel)
      (sort := .original _)
      parallel (embed first) (embed second)
  | unit parallel first =>
    exact Equation.unit (signature := signature source Parallel) (Parallel := NativeParallel)
      (sort := .original _)
      parallel (embed first)

def classEmbedding {sort : source.Srt} : Class source Parallel sort →
    ValueClass (source := source) (Parallel := Parallel) (.original sort) :=
  Quotient.map embed (fun _ _ equation => embed_equation equation)

structure AdministrativeRule (source : Mettapedia.OSLF.SortedConstructors.Signature.{u,v})
    (Parallel : source.Srt → Prop) where
  interface : Srt source Parallel
  redex : Value interface
  reactum : Value interface

def askRule (head : SourceHead source Parallel) (arguments : Arguments head) : AdministrativeRule source Parallel where
  interface := .arguments head
  redex := cut (.ask head) (probe (.ask head)) (sourceNode head arguments)
  reactum := bundle head arguments

def getRule (head : SourceHead source Parallel) (arguments : Arguments head)
    (position : Fin (headArity head)) : AdministrativeRule source Parallel where
  interface := .original (headInput head position)
  redex := cut (.get head position) (probe (.get head position)) (bundle head arguments)
  reactum := arguments position

def buildRule (head : SourceHead source Parallel) (arguments : Arguments head) : AdministrativeRule source Parallel where
  interface := .original (headOutput head)
  redex := cut (.build head) (probe (.build head)) (bundle head arguments)
  reactum := sourceNode head arguments

def AdministrativeRule.rule (supplied : AdministrativeRule source Parallel) :
    ReactionRule (.origin : ContextCategory source Parallel) where
  codomain := .interface supplied.interface
  redex := RawArrow.value (classOf supplied.redex)
  reactum := RawArrow.value (classOf supplied.reactum)

theorem arguments_not_parallel (head : SourceHead source Parallel) :
    ¬NativeParallel (.arguments head) := fun absent => absent

theorem probe_not_parallel (instrument : Probe source Parallel) :
    ¬NativeParallel (.probe instrument) := fun absent => absent

theorem original_parallel_iff (sort : source.Srt) :
    NativeParallel (.original sort : Srt source Parallel) ↔ Parallel sort := Iff.rfl

end Mettapedia.OSLF.Framework.SortedTypedInstruments
