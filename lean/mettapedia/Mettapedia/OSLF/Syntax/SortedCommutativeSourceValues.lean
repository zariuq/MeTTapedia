import Mettapedia.OSLF.Framework.SortedCommutativeInstrumentProfile

/-!
# Unchanged source equations inside the sorted observer extension

The original one-sort syntax has its own ordinary constructor heads, binary
AC1 Cut and unit. Its embedding is compared with an independently defined
syntax erasure. The erasure sends auxiliary observer heads to the source
unit; it is a syntax retraction, not a semantic model or an observer decoder.
Generated equality is both preserved and reflected on all source terms.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedCommutativeInstruments.Source

open Mettapedia.OSLF.SortedCommutative

universe u

variable {Symbols : Type u} (arity : Symbols → Nat)

abbrev signature : Mettapedia.OSLF.SortedConstructors.Signature.{u,u} where
  Srt := ULift.{u} Unit
  Constructor := Symbols
  arity := arity
  input _ _ := ULift.up ()
  output _ := ULift.up ()

def Parallel (sort : (signature arity).Srt) : Prop := sort = ULift.up ()

abbrev Value := Term (signature arity) (Parallel arity) (ULift.up ())
abbrev ValueClass := Class (signature arity) (Parallel arity) (ULift.up ())

variable {arity}

def embed {sort : (signature arity).Srt} :
    Term (signature arity) (Parallel arity) sort → SortedCommutativeInstruments.Value arity .base
  | .zero _ => .zero rfl
  | .cut _ first second => .cut rfl (embed first) (embed second)
  | .node constructor arguments =>
    .node (signature := SortedCommutativeInstruments.signature arity) (.original constructor)
      (fun position => embed (arguments position))

def erase {sort : SortedCommutativeInstruments.Srt arity}
    (supplied : SortedCommutativeInstruments.Value arity sort) : Value arity :=
  @Term.rec (SortedCommutativeInstruments.signature arity) (SortedCommutativeInstruments.Parallel arity)
    (fun _ _ => Value arity)
    (fun _ => .zero rfl)
    (fun _ _ _ first second => .cut rfl first second)
    (fun constructor _ arguments => match constructor with
      | .original symbol => .node (signature := signature arity) symbol arguments
      | .arguments _ => .zero rfl
      | .probe _ => .zero rfl
      | .cut _ => .zero rfl) sort supplied

theorem embed_equation {sort : (signature arity).Srt}
    {first second : Term (signature arity) (Parallel arity) sort} (equation : Equation (signature := signature arity) (Parallel := Parallel arity) first second) :
    Equation (signature := SortedCommutativeInstruments.signature arity)
      (Parallel := SortedCommutativeInstruments.Parallel arity) (embed first) (embed second) := by
  induction equation with
  | refl => exact .refl _
  | symm _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ before after => exact before.trans after
  | node _ inductionHypothesis => exact .node inductionHypothesis
  | cut _ _ _ before after => exact Equation.cut _ before after
  | assoc => exact Equation.assoc _ _ _ _
  | comm => exact Equation.comm _ _ _
  | unit => exact Equation.unit _ _

theorem erase_equation {sort : SortedCommutativeInstruments.Srt arity}
    {first second : SortedCommutativeInstruments.Value arity sort} (equation : Equation (signature := SortedCommutativeInstruments.signature arity)
      (Parallel := SortedCommutativeInstruments.Parallel arity) first second) :
    Equation (signature := signature arity) (Parallel := Parallel arity) (erase first) (erase second) := by
  apply @Equation.rec (SortedCommutativeInstruments.signature arity)
    (SortedCommutativeInstruments.Parallel arity)
    (fun {_sort} {first second} _ => Equation (signature := signature arity) (Parallel := Parallel arity)
      (erase first) (erase second)) (t := equation)
  · intro sort term
    exact .refl _
  · intro sort first second equation inductionHypothesis
    exact inductionHypothesis.symm
  · intro sort first second third before after firstRead secondRead
    exact firstRead.trans secondRead
  · intro constructor first second equations inductionHypothesis
    cases constructor with
    | original => exact .node inductionHypothesis
    | arguments => exact .refl _
    | probe => exact .refl _
    | cut => exact .refl _
  · intro sort parallel first first' second second' before after firstRead secondRead
    exact Equation.cut _ firstRead secondRead
  · intro sort parallel first second third
    exact Equation.assoc _ _ _ _
  · intro sort parallel first second
    exact Equation.comm _ _ _
  · intro sort parallel term
    exact Equation.unit _ _

private theorem erase_embed_heq {sort : (signature arity).Srt}
    (supplied : Term (signature arity) (Parallel arity) sort) : HEq (erase (embed supplied)) supplied := by
  apply @Term.rec (signature arity) (Parallel arity)
    (fun _ supplied => HEq (erase (embed supplied)) supplied) (t := supplied)
  · intro sort parallel
    cases sort with
    | up sort => cases sort; rfl
  · intro sort parallel first second firstRead secondRead
    cases sort with
    | up sort =>
      cases sort
      exact heq_of_eq (congrArg₂ (Term.cut rfl) (eq_of_heq firstRead) (eq_of_heq secondRead))
  · intro constructor arguments inductionHypothesis
    exact heq_of_eq (congrArg (Term.node constructor) (funext (fun position => eq_of_heq (inductionHypothesis position))))

theorem erase_embed (supplied : Value arity) : erase (embed supplied) = supplied :=
  eq_of_heq (erase_embed_heq supplied)

theorem equation_iff_embedded (first second : Value arity) :
    Equation (signature := signature arity) (Parallel := Parallel arity) first second ↔
      Equation (signature := SortedCommutativeInstruments.signature arity)
        (Parallel := SortedCommutativeInstruments.Parallel arity) (embed first) (embed second) := by
  refine ⟨embed_equation, fun equation => ?_⟩
  simpa only [erase_embed] using erase_equation equation

def classEmbedding : ValueClass arity → SortedCommutativeInstruments.ValueClass arity .base :=
  Quotient.map embed (fun _ _ equation => embed_equation equation)

def classRetraction {sort : SortedCommutativeInstruments.Srt arity} :
    SortedCommutativeInstruments.ValueClass arity sort → ValueClass arity :=
  Quotient.map erase (fun _ _ equation => erase_equation equation)

theorem retraction_embedding (supplied : ValueClass arity) :
    classRetraction (classEmbedding supplied) = supplied :=
  Quotient.inductionOn supplied (fun raw => congrArg classOf (erase_embed raw))

theorem classEmbedding_injective : Function.Injective (classEmbedding (arity := arity)) := by
  intro first second same
  exact (retraction_embedding first).symm.trans ((congrArg classRetraction same).trans (retraction_embedding second))

theorem class_embedding_readout (supplied : Value arity) :
    classEmbedding (classOf supplied) = classOf (embed supplied) := rfl

end Mettapedia.OSLF.Framework.SortedCommutativeInstruments.Source
