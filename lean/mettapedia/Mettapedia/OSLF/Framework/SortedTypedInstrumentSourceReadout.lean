import Mettapedia.OSLF.Framework.SortedTypedInstrumentSupport
import Mathlib.Data.Option.NAry

/-!+# Partial sorted source readings and conservative equation inclusion

The reading returns an actual original source equation class only when every
declared child has such a reading. Auxiliary outputs have a separate carrier;
an administrative constructor at an original sort returns failure. The lifted
AC1 operations and complete child assembly respect every generated equation.
This earns source-class injectivity without a total source erasure.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedTypedInstruments

open Mettapedia.OSLF.SortedCommutative

universe u v i j

def optionTuple {Index : Type i} {Carrier : Index → Type j}
    (values : (index : Index) → Option (Carrier index)) : Option ((index : Index) → Carrier index) := by
  classical
  exact if supplied : ∃ tuple : (index : Index) → Carrier index,
      ∀ index, values index = some (tuple index)
    then some supplied.choose else none

theorem optionTuple_some {Index : Type i} {Carrier : Index → Type j}
    (tuple : (index : Index) → Carrier index) :
    optionTuple (fun index => some (tuple index)) = some tuple := by
  classical
  have supplied : ∃ chosen : (index : Index) → Carrier index,
      ∀ index, some (tuple index) = some (chosen index) := ⟨tuple, fun _ => rfl⟩
  rw [optionTuple, dif_pos supplied]
  apply congrArg some
  funext index
  exact (Option.some.inj (supplied.choose_spec index)).symm

variable {source : Mettapedia.OSLF.SortedConstructors.Signature.{u,v}}
  {Parallel : source.Srt → Prop}

def SourceReading : Srt source Parallel → Type (max u v)
  | .original sort => Option (Class source Parallel sort)
  | .arguments _ => PUnit
  | .probe _ => PUnit

def readZero {sort : Srt source Parallel} (parallel : NativeParallel sort) :
    SourceReading sort := by
  cases sort with
  | original sort => exact some (classOf (.zero parallel : Term source Parallel sort))
  | arguments => exact parallel.elim
  | probe => exact parallel.elim

def readCut {sort : Srt source Parallel} (parallel : NativeParallel sort)
    (first second : SourceReading sort) : SourceReading sort := by
  cases sort with
  | original sort => exact Option.map₂ (classCut parallel) first second
  | arguments => exact parallel.elim
  | probe => exact parallel.elim

def readNode (constructor : Constructor source Parallel)
    (arguments : (position : Fin ((signature source Parallel).arity constructor)) →
      SourceReading ((signature source Parallel).input constructor position)) :
    SourceReading ((signature source Parallel).output constructor) := by
  cases constructor with
  | original constructor =>
    exact (optionTuple arguments).map (fun tuple => (Head.node constructor tuple).class)
  | arguments => exact PUnit.unit
  | probe => exact PUnit.unit
  | cut instrument =>
    cases instrument with
    | ask => exact PUnit.unit
    | get => exact none
    | build => exact none

def readSource {sort : Srt source Parallel}
    (supplied : Value (source := source) (Parallel := Parallel) sort) : SourceReading sort :=
  @Term.rec (signature source Parallel) NativeParallel (fun sort _ => SourceReading sort)
    (fun parallel => readZero parallel) (fun parallel _ _ first second => readCut parallel first second)
    (fun constructor _ arguments => readNode constructor arguments) sort supplied

theorem readCut_assoc {sort : Srt source Parallel} (parallel : NativeParallel sort)
    (first second third : SourceReading sort) :
    readCut parallel (readCut parallel first second) third =
      readCut parallel first (readCut parallel second third) := by
  cases sort with
  | original sort =>
    change Option.map₂ (classCut parallel) (Option.map₂ (classCut parallel) first second) third =
      Option.map₂ (classCut parallel) first (Option.map₂ (classCut parallel) second third)
    exact Option.map₂_assoc (fun a b c => Quotient.inductionOn₃ a b c
      (fun a b c => Quotient.sound (Equation.assoc parallel a b c)))
  | arguments => exact parallel.elim
  | probe => exact parallel.elim

theorem readCut_comm {sort : Srt source Parallel} (parallel : NativeParallel sort)
    (first second : SourceReading sort) : readCut parallel first second = readCut parallel second first := by
  cases sort with
  | original sort =>
    change Option.map₂ (classCut parallel) first second = Option.map₂ (classCut parallel) second first
    exact Option.map₂_comm (fun a b => Quotient.inductionOn₂ a b
      (fun a b => Quotient.sound (Equation.comm parallel a b)))
  | arguments => exact parallel.elim
  | probe => exact parallel.elim

theorem readCut_unit {sort : Srt source Parallel} (parallel : NativeParallel sort)
    (first : SourceReading sort) : readCut parallel first (readZero parallel) = first := by
  cases sort with
  | original sort =>
    cases first with
    | none => rfl
    | some first =>
      apply congrArg some
      exact Quotient.inductionOn first (fun raw => Quotient.sound (Equation.unit parallel raw))
  | arguments => exact parallel.elim
  | probe => exact parallel.elim

theorem readSource_equation {sort : Srt source Parallel}
    {first second : Value (source := source) (Parallel := Parallel) sort}
    (equation : Equation first second) : readSource first = readSource second := by
  apply @Equation.rec (signature source Parallel) NativeParallel
    (fun {_sort} {first second} _ => readSource first = readSource second) (t := equation)
  · intro sort term
    rfl
  · intro sort first second equation inductionHypothesis
    exact inductionHypothesis.symm
  · intro sort first second third before after firstRead secondRead
    exact firstRead.trans secondRead
  · intro constructor first second equations inductionHypothesis
    exact congrArg (readNode constructor) (funext inductionHypothesis)
  · intro sort parallel first first' second second' before after firstRead secondRead
    exact congrArg₂ (readCut parallel) firstRead secondRead
  · intro sort parallel first second third
    exact readCut_assoc parallel _ _ _
  · intro sort parallel first second
    exact readCut_comm parallel _ _
  · intro sort parallel first
    exact readCut_unit parallel _

def classSourceReading {sort : Srt source Parallel} :
    ValueClass (source := source) (Parallel := Parallel) sort → SourceReading sort :=
  Quotient.lift readSource (fun _ _ equation => readSource_equation equation)

theorem readSource_embed {sort : source.Srt} (supplied : Term source Parallel sort) :
    readSource (embed supplied) = some (classOf supplied) := by
  induction supplied with
  | zero => rfl
  | cut parallel first second firstRead secondRead =>
    change Option.map₂ (classCut parallel) (readSource (embed first)) (readSource (embed second)) = _
    rw [firstRead, secondRead]
    rfl
  | node constructor arguments inductionHypothesis =>
    change (optionTuple (fun position => readSource (embed (arguments position)))).map
      (fun tuple => (Head.node constructor tuple).class) = some (classOf (.node constructor arguments))
    have childrenRead : (fun position => readSource (embed (arguments position))) =
        fun position => some (classOf (arguments position)) := funext inductionHypothesis
    rw [childrenRead, optionTuple_some]
    exact congrArg some (Head.class_node constructor arguments)

theorem classSourceReading_embedding {sort : source.Srt} (supplied : Class source Parallel sort) :
    classSourceReading (classEmbedding supplied) = some supplied :=
  Quotient.inductionOn supplied readSource_embed

theorem classEmbedding_injective {sort : source.Srt} :
    Function.Injective (classEmbedding (source := source) (Parallel := Parallel) (sort := sort)) := by
  intro first second same
  have readings := congrArg classSourceReading same
  rw [classSourceReading_embedding, classSourceReading_embedding] at readings
  exact Option.some.inj readings

theorem embed_equation_iff {sort : source.Srt} (first second : Term source Parallel sort) :
    Equation (embed first) (embed second) ↔ Equation first second := by
  refine ⟨fun equation => ?_, embed_equation⟩
  exact Quotient.exact (classEmbedding_injective (Quotient.sound equation))

theorem sourceReading_zero_original {sort : source.Srt}
    (supplied : ValueClass (source := source) (Parallel := Parallel) (.original sort))
    (pure : classObserverCount supplied = 0) :
    ∃! original : Class source Parallel sort,
      classEmbedding original = supplied ∧ classSourceReading supplied = some original := by
  obtain ⟨original, reading⟩ := classObserverCount_zero_original supplied pure
  refine ⟨original, ⟨reading, ?_⟩, ?_⟩
  · rw [← reading]
    exact classSourceReading_embedding original
  · intro other otherReading
    exact classEmbedding_injective (otherReading.1.trans reading.symm)

end Mettapedia.OSLF.Framework.SortedTypedInstruments
