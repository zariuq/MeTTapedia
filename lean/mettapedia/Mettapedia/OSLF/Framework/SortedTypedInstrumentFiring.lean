import Mettapedia.OSLF.Framework.SortedTypedInstrumentProfile
import Mettapedia.OSLF.Syntax.SortedCommutativeContextMonomorphisms

/-!
# Actual heterogeneous probe firings and retained supplied occurrences

Every supplied tuple occupies its independently declared coordinate sorts.
Ask, get and build determine their actual typed source and target values.
The complete probe-filling square and independently earned IPO universal
property prove each administrative firing. Its receipt retains the whole
tuple, selected position and independently supplied origin beside the step.
No source-sort inhabitant or global origin is chosen.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedTypedInstruments

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedCommutative
open Mettapedia.GSLT.RedexRelativeCongruence

universe u v w

variable {source : Mettapedia.OSLF.SortedConstructors.Signature.{u,v}}
  {Parallel : source.Srt → Prop}

inductive Occurrence (source : Mettapedia.OSLF.SortedConstructors.Signature.{u,v})
    (Parallel : source.Srt → Prop) (Origins : Type w) where
  | ask (origin : Origins) (head : SourceHead source Parallel) (arguments : Arguments head)
  | get (origin : Origins) (head : SourceHead source Parallel) (arguments : Arguments head)
      (position : Fin (headArity head))
  | build (origin : Origins) (head : SourceHead source Parallel) (arguments : Arguments head)

variable {Origins : Type w}

def Occurrence.origin : Occurrence source Parallel Origins → Origins
  | .ask origin _ _ => origin
  | .get origin _ _ _ => origin
  | .build origin _ _ => origin

def Occurrence.instrument : Occurrence source Parallel Origins → Probe source Parallel
  | .ask _ head _ => .ask head
  | .get _ head _ position => .get head position
  | .build _ head _ => .build head

def Occurrence.body (supplied : Occurrence source Parallel Origins) : Value (receiver supplied.instrument) :=
  match supplied with
  | .ask _ head arguments => sourceNode head arguments
  | .get _ head arguments _ => bundle head arguments
  | .build _ head arguments => bundle head arguments

def Occurrence.output (supplied : Occurrence source Parallel Origins) : Value (result supplied.instrument) :=
  match supplied with
  | .ask _ head arguments => bundle head arguments
  | .get _ _ arguments position => arguments position
  | .build _ head arguments => sourceNode head arguments

def Occurrence.label (supplied : Occurrence source Parallel Origins) :
    (.interface (receiver supplied.instrument) : ContextCategory source Parallel) ⟶
      .interface (result supplied.instrument) :=
  RawArrow.context (contextClassOf (probeContext supplied.instrument))

def Occurrence.agent (supplied : Occurrence source Parallel Origins) :
    (.origin : ContextCategory source Parallel) ⟶ .interface (receiver supplied.instrument) :=
  RawArrow.value (classOf supplied.body)

def Occurrence.target (supplied : Occurrence source Parallel Origins) :
    (.origin : ContextCategory source Parallel) ⟶ .interface (result supplied.instrument) :=
  RawArrow.value (classOf supplied.output)

def Occurrence.rule (supplied : Occurrence source Parallel Origins) :
    ReactionRule (.origin : ContextCategory source Parallel) where
  codomain := .interface (result supplied.instrument)
  redex := RawArrow.value (classOf (cut supplied.instrument (probe supplied.instrument) supplied.body))
  reactum := supplied.target

def rules (source : Mettapedia.OSLF.SortedConstructors.Signature.{u,v})
    (Parallel : source.Srt → Prop) (Origins : Type w)
    (rule : ReactionRule (.origin : ContextCategory source Parallel)) : Prop :=
  ∃ occurrence : Occurrence source Parallel Origins, occurrence.rule = rule

theorem Occurrence.complete_probe_square (supplied : Occurrence source Parallel Origins) :
    supplied.agent ≫ supplied.label = supplied.rule.redex :=
  congrArg RawArrow.value (congrArg classOf (probeContext_fill supplied.instrument supplied.body))

theorem Occurrence.direct_step (supplied : Occurrence source Parallel Origins) :
    ActIPO (rules source Parallel Origins) supplied.label supplied.agent supplied.target := by
  have square := supplied.complete_probe_square
  refine ⟨supplied.rule, ⟨supplied, rfl⟩, 𝟙 _,
    square.trans (Category.comp_id supplied.rule.redex).symm, ?_, ?_⟩
  · exact raw_right_identity_isIPO _ square
  · exact (Category.comp_id supplied.rule.reactum).symm

theorem Occurrence.ask_rule_readout (origin : Origins) (head : SourceHead source Parallel)
    (arguments : Arguments head) :
    (Occurrence.ask origin head arguments).rule = (askRule head arguments).rule := rfl

theorem Occurrence.get_rule_readout (origin : Origins) (head : SourceHead source Parallel)
    (arguments : Arguments head) (position : Fin (headArity head)) :
    (Occurrence.get origin head arguments position).rule = (getRule head arguments position).rule := rfl

theorem Occurrence.build_rule_readout (origin : Origins) (head : SourceHead source Parallel)
    (arguments : Arguments head) :
    (Occurrence.build origin head arguments).rule = (buildRule head arguments).rule := rfl

structure FiringReceipt (source : Mettapedia.OSLF.SortedConstructors.Signature.{u,v})
    (Parallel : source.Srt → Prop) (Origins : Type w) where
  occurrence : Occurrence source Parallel Origins
  step : ActIPO (rules source Parallel Origins) occurrence.label occurrence.agent occurrence.target

def directReceipt (supplied : Occurrence source Parallel Origins) : FiringReceipt source Parallel Origins :=
  ⟨supplied, supplied.direct_step⟩

theorem directReceipt_injective :
    Function.Injective (directReceipt (source := source) (Parallel := Parallel) (Origins := Origins)) :=
  fun _ _ same => congrArg FiringReceipt.occurrence same

theorem no_receipt_without_origins (receipt : FiringReceipt source Parallel Empty) : False :=
  Empty.elim receipt.occurrence.origin

theorem complete_redex_relative_pushouts {first second : Srt source Parallel}
    (agent : ValueClass (source := source) (Parallel := Parallel) first)
    (redex : ValueClass (source := source) (Parallel := Parallel) second) :
    Mettapedia.GSLT.RelativePushout.HasRelativePushouts
      (C := ContextCategory source Parallel)
      (RawArrow.value agent : (.origin : ContextCategory source Parallel) ⟶ .interface first)
      (RawArrow.value redex : (.origin : ContextCategory source Parallel) ⟶ .interface second) :=
  raw_redex_relativePushouts _ _

end Mettapedia.OSLF.Framework.SortedTypedInstruments
