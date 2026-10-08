import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Basic
import Mettapedia.OSLF.Syntax.SignatureMorphismMetas

/-!
# The independently authored all-arity polyadic binding signature

Every natural number declares its own input, output and simultaneous COMM
schema. A receiver binds exactly its ordered list of names; output arguments
and metavariable dependencies use the same finite positions. Zero arity is
included. The existing unary/binary runtime signature embeds by an actual
arity-preserving signature map, without being identified with this signature.

The structural equation declarations are the original seven scope and
parallel schemas transported through that map. No behavioral equation or
operational correspondence is presumed by these declarations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.AllArity

open Mettapedia.OSLF.Binding

inductive Op : Srt → Type where
  | nil : Op .pr
  | par : Op .pr
  | inp (arity : Nat) : Op .pr
  | out (arity : Nat) : Op .pr
  | nu : Op .pr
  | rep : Op .pr
  deriving DecidableEq

def names : Nat → List Srt
  | 0 => []
  | arity + 1 => .nm :: names arity

def nameArguments (arity : Nat) : List (List Srt × Srt) :=
  (names arity).map (fun result => ([], result))

abbrev sig : Mettapedia.OSLF.Binding.Signature where
  Srt := Srt
  Op := Op
  arity := fun {_} operation => match operation with
    | .nil => []
    | .par => [([], .pr), ([], .pr)]
    | .inp arity => [([], .nm), (names arity, .pr)]
    | .out arity => ([], .nm) :: nameArguments arity
    | .nu => [(names 1, .pr)]
    | .rep => [([], .pr)]

abbrev Name (context : Ctx sig) := Term sig context .nm
abbrev Proc (context : Ctx sig) := Term sig context .pr

def orderedArguments {binding : Mettapedia.OSLF.Binding.Signature}
    (result : binding.Srt) {context : Ctx binding} :
    (arity : Nat) → (Fin arity → Term binding context result) →
      Args binding (List.replicate arity ([], result)) context
  | 0, _ => .nil
  | arity + 1, arguments => .cons (arguments 0) (orderedArguments result arity (fun index => arguments index.succ))

theorem names_eq_replicate (arity : Nat) : names arity = List.replicate arity Srt.nm := by
  induction arity with
  | zero => rfl
  | succ arity inductionHypothesis =>
      simpa only [names, List.replicate_succ] using congrArg (Srt.nm :: ·) inductionHypothesis

theorem nameArguments_eq_replicate (arity : Nat) :
    nameArguments arity = List.replicate arity ([], Srt.nm) := by
  rw [nameArguments, names_eq_replicate, List.map_replicate]

def nameVector {binding : Mettapedia.OSLF.Binding.Signature}
    (result : binding.Srt) {context : Ctx binding} (arity : Nat)
    (arguments : Fin arity → Term binding context result) :
    Args binding ((List.replicate arity result).map (fun sort => ([], sort))) context :=
  castArgsArity List.map_replicate.symm (orderedArguments result arity arguments)

def nil {context : Ctx sig} : Proc context := .op .nil .nil
def par {context : Ctx sig} (first second : Proc context) : Proc context :=
  .op .par (.cons first (.cons second .nil))
def inp {context : Ctx sig} (arity : Nat) (channel : Name context)
    (body : Proc (names arity ++ context)) : Proc context :=
  .op (.inp arity) (.cons channel (.cons body .nil))
def out {context : Ctx sig} (arity : Nat) (channel : Name context)
    (arguments : Fin arity → Name context) : Proc context :=
  .op (.out arity) (.cons channel
    (castArgsArity (nameArguments_eq_replicate arity).symm (orderedArguments Srt.nm arity arguments)))

def fragment : SigMor PolyadicPi.sig sig where
  sortMap := id
  opMap
    | .nil => .nil
    | .par => .par
    | .inp1 => .inp 1
    | .inp2 => .inp 2
    | .out1 => .out 1
    | .out2 => .out 2
    | .nu => .nu
    | .rep => .rep
  carriesArity operation := by cases operation <;> rfl

def structuralMetas : List (MetaArity sig) := fragment.mapMetas PolyadicPi.metas
def equations : List (EqAxiom sig structuralMetas) :=
  PolyadicPi.equations.map fragment.mapEqAxiom

def positions {A : Type} (result : A) (tail : List A) :
    (arity : Nat) → Fin arity → Var (List.replicate arity result ++ tail) result
  | 0, index => Fin.elim0 index
  | arity + 1, index => Fin.cases .zero (fun earlier => .succ (positions result tail arity earlier)) index

def namePosition (tail : List Srt) (arity : Nat) (index : Fin arity) :
    Var (names arity ++ tail) Srt.nm :=
  castVarCtx (congrArg (· ++ tail) (names_eq_replicate arity).symm)
    (positions Srt.nm tail arity index)

def closedNamePosition (arity : Nat) (index : Fin arity) : Var (names arity) Srt.nm :=
  castVarCtx (List.append_nil (names arity)) (namePosition [] arity index)

def communicationMetas (arity : Nat) : List (MetaArity sig) := [(names arity, Srt.pr)]
abbrev communicationSignature (arity : Nat) := withMetas sig (communicationMetas arity)

def continuation {context : Ctx sig} (arity : Nat)
    (arguments : Fin arity → Term (communicationSignature arity) context .nm) :
    Term (communicationSignature arity) context .pr :=
  .op (.inr (MetaOp.mk (M := communicationMetas arity) ⟨0, by simp [communicationMetas]⟩))
    (castArgsArity (by
      change List.replicate arity ([], Srt.nm) = nameArguments arity
      exact (nameArguments_eq_replicate arity).symm)
      (orderedArguments Srt.nm arity arguments))

def comm (arity : Nat) : UnpositionedRewrite (communicationSignature arity) where
  ctx := Srt.nm :: names arity
  sort := .pr
  lhs := .op (.inl .par)
    (.cons
      (.op (.inl (.out arity)) (.cons (.var .zero)
        (castArgsArity (nameArguments_eq_replicate arity).symm
          (orderedArguments Srt.nm arity (fun index => .var (.succ (closedNamePosition arity index)))))))
      (.cons
        (.op (.inl (.inp arity)) (.cons (.var .zero)
          (.cons (continuation arity (fun index => .var (namePosition (Srt.nm :: names arity) arity index))) .nil)))
        .nil))
  rhs := continuation arity (fun index => .var (.succ (closedNamePosition arity index)))

theorem complete_communication_domain (arity : Nat) :
    (comm arity).ctx = Srt.nm :: names arity ∧
      communicationMetas arity = [(names arity, Srt.pr)] := ⟨rfl, rfl⟩

theorem receiver_arity (arity : Nat) :
    sig.arity (Op.inp arity) = [([], Srt.nm), (names arity, Srt.pr)] := rfl

theorem sender_arity (arity : Nat) :
    sig.arity (Op.out arity) = ([], Srt.nm) :: nameArguments arity := rfl

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.AllArity
