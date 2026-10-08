import Mettapedia.OSLF.Syntax.SortedCommutativeEquations

/-!
# Literal sorted constructor profile of the designated Cut syntax

The raw mixed syntax is compared with the independent sorted constructor-tree
syntax. Its designated Cut is an actual binary member of that signature, and
each zero is an actual nullary member. Encode and decode traverse every free
constructor and every argument of its original declared sort.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.SortedCommutative

open Mettapedia.OSLF.SortedConstructors

universe u v

variable (signature : Signature.{u,v}) (Parallel : signature.Srt → Prop)

inductive Constructor where
  | ordinary (constructor : signature.Constructor)
  | zero (sort : signature.Srt) (parallel : Parallel sort)
  | cut (sort : signature.Srt) (parallel : Parallel sort)

abbrev syntaxSignature : Signature.{u,max u v} where
  Srt := signature.Srt
  Constructor := Constructor signature Parallel
  arity
    | .ordinary constructor => signature.arity constructor
    | .zero _ _ => 0
    | .cut _ _ => 2
  input
    | .ordinary constructor => signature.input constructor
    | .zero _ _ => Fin.elim0
    | .cut sort _ => fun _ => sort
  output
    | .ordinary constructor => signature.output constructor
    | .zero sort _ => sort
    | .cut sort _ => sort

variable {signature Parallel}

def encode {sort : signature.Srt} :
    Term signature Parallel sort → SortedConstructors.Term (syntaxSignature signature Parallel) sort
  | .zero parallel => SortedConstructors.Term.node (signature := syntaxSignature signature Parallel)
      (Constructor.zero _ parallel) (fun position => Fin.elim0 position)
  | .cut parallel first second => SortedConstructors.Term.node (signature := syntaxSignature signature Parallel)
      (Constructor.cut _ parallel)
      (Fin.cases (encode first) (fun _ => encode second))
  | .node constructor arguments => SortedConstructors.Term.node (signature := syntaxSignature signature Parallel)
      (Constructor.ordinary constructor) (fun position => encode (arguments position))

def decode {sort : signature.Srt} :
    SortedConstructors.Term (syntaxSignature signature Parallel) sort → Term signature Parallel sort
  | .node (Constructor.ordinary constructor) arguments => .node constructor (fun position => decode (arguments position))
  | .node (Constructor.zero _ parallel) _ => .zero parallel
  | .node (Constructor.cut _ parallel) arguments => .cut parallel (decode (arguments 0)) (decode (arguments 1))

theorem decode_encode {sort : signature.Srt} (term : Term signature Parallel sort) :
    decode (encode term) = term := by
  induction term with
  | zero => rfl
  | cut parallel first second firstIH secondIH =>
    exact congrArg₂ (Term.cut parallel) firstIH secondIH
  | node constructor arguments inductionHypothesis =>
    exact congrArg (Term.node constructor) (funext inductionHypothesis)

theorem encode_decode {sort : signature.Srt}
    (term : SortedConstructors.Term (syntaxSignature signature Parallel) sort) : encode (decode term) = term := by
  apply SortedConstructors.Term.rec
    (motive := fun _ term => encode (decode term) = term) (t := term)
  intro constructor arguments inductionHypothesis
  cases constructor with
  | ordinary constructor =>
    exact congrArg
      (SortedConstructors.Term.node (signature := syntaxSignature signature Parallel) (Constructor.ordinary constructor))
      (funext inductionHypothesis)
  | zero sort parallel =>
    apply congrArg (SortedConstructors.Term.node (signature := syntaxSignature signature Parallel) (Constructor.zero sort parallel))
    funext position
    exact Fin.elim0 position
  | cut sort parallel =>
    apply congrArg (SortedConstructors.Term.node (signature := syntaxSignature signature Parallel) (Constructor.cut sort parallel))
    funext position
    refine Fin.cases (inductionHypothesis 0) (fun other => ?_) position
    have zero : other = 0 := Subsingleton.elim other 0
    subst other
    exact inductionHypothesis 1

def syntaxEquiv (sort : signature.Srt) :
    Term signature Parallel sort ≃ SortedConstructors.Term (syntaxSignature signature Parallel) sort where
  toFun := encode
  invFun := decode
  left_inv := decode_encode
  right_inv := encode_decode

theorem properCut_binary {sort : signature.Srt} (parallel : Parallel sort) :
    (syntaxSignature signature Parallel).arity (.cut sort parallel) = 2 := rfl

theorem properCut_complete_readout {sort : signature.Srt} (parallel : Parallel sort)
    (first second : Term signature Parallel sort) :
    encode (.cut parallel first second) =
      .node (signature := syntaxSignature signature Parallel) (.cut sort parallel)
        (Fin.cases (encode first) (fun _ => encode second)) := rfl

end Mettapedia.OSLF.SortedCommutative
