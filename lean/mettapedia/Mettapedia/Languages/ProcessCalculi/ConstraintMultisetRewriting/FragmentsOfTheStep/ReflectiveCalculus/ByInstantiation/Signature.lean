import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Terms
import Mettapedia.OSLF.Syntax.ContextualRigidTerms

/-!
# Twin binders as a binding signature, and the read-back into the source

An input binds two positions: the received name and its *process twin*. A drop of a bound name is
the twin variable, so the signature has no drop of a name variable at all: its only drop former,
`dropq`, takes a process and means the drop of that process's quote (`*@P`, inert in the
calculus). Every other former is a constructor of the source syntax.

* `sig`: sorts `nm`, `pr` and `ps` (the components of a parallel bag); formers `zero`, `bag`,
  `pnil`, `pcons`, `input` (binds `[nm, pr]`), `output`, `dropq`, `quote`.
* `read`: the read-back of a term into the source carrier's patterns. The name bound by the
  `i`-th enclosing input is at position `2i` of the context and reads back as the bound index
  `i`; its twin, at position `2i + 1`, reads back as `*i`. Every former reads back as the
  corresponding constructor (`read_input`, `read_output`, `read_quote`, `read_dropq`, ...); no
  former reads back through a substitution or a normalizer.
* `noUnknowns`: the declaration family with no unknowns. Its terms are the ground terms.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.ByInstantiation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

/-! ## The signature -/

/-- Names, processes, and lists of processes (the components of a parallel bag). -/
inductive Srt where
  | nm
  | pr
  | ps
  deriving DecidableEq, Repr

/-- The formers. `input` is the only one that binds, and it binds a name and its twin. -/
inductive Op : Srt → Type where
  | zero : Op .pr
  | bag : Op .pr
  | pnil : Op .ps
  | pcons : Op .ps
  | input : Op .pr
  | output : Op .pr
  | dropq : Op .pr
  | quote : Op .nm

/-- **The twin-binder signature.** -/
abbrev sig : Signature where
  Srt := Srt
  Op := Op
  arity := fun {_} o => match o with
    | .zero => []
    | .bag => [([], .ps)]
    | .pnil => []
    | .pcons => [([], .pr), ([], .ps)]
    | .input => [([], .nm), ([.nm, .pr], .pr)]
    | .output => [([], .nm), ([], .pr)]
    | .dropq => [([], .pr)]
    | .quote => [([], .pr)]

/-- The declaration family with no unknowns: its terms are ground. -/
def noUnknowns : Empty → MetaArity sig := fun e => nomatch e

/-! ## Read-back -/

/-- The position of a variable in its context. -/
def position {A : Type} : {Γ : List A} → {s : A} → Var Γ s → Nat
  | _, _, .zero => 0
  | _, _, .succ v => position v + 1

/-- The binder a position belongs to: positions `2i` and `2i + 1` belong to the `i`-th. -/
def half : Nat → Nat
  | 0 => 0
  | 1 => 0
  | n + 2 => half n + 1

/-- A variable read back: a bound name, the drop of a bound name (its twin), or an empty bag. -/
def readVar : Srt → Nat → Pattern
  | .nm, n => .bvar (half n)
  | .pr, n => .apply "PDrop" [.bvar (half n)]
  | .ps, _ => .collection .hashBag [] none

/-- What read-back gives an unknown; ground terms have none. -/
def unread : Pattern := .fvar "unknown"

variable {V : Type} {D : V → MetaArity sig}

/-- A former read back from the read-backs of its arguments. -/
def build : {s : Srt} → (signature sig D).Op s → List Pattern → Pattern
  | _, .inl .zero, _ => .apply "PZero" []
  | _, .inl .bag, [l] => l
  | _, .inl .pnil, _ => .collection .hashBag [] none
  | _, .inl .pcons, [p, l] => consBag p l
  | _, .inl .input, [c, b] => .apply "PInput" [c, .lambda none b]
  | _, .inl .output, [c, p] => .apply "POutput" [c, p]
  | _, .inl .dropq, [p] => .apply "PDrop" [.apply "NQuote" [p]]
  | _, .inl .quote, [p] => .apply "NQuote" [p]
  | _, _, _ => unread

mutual
  /-- **Read-back** into the source's patterns. -/
  def read : {Γ : Ctx sig} → {s : Srt} → Term (signature sig D) Γ s → Pattern
    | _, s, .var v => readVar s (position v)
    | _, _, .op o args => build o (readArgs args)

  /-- The read-backs of the arguments, in order. -/
  def readArgs : {as : List (List Srt × Srt)} → {Γ : Ctx sig} →
      Args (signature sig D) as Γ → List Pattern
    | _, _, .nil => []
    | _, _, .cons head tail => read head :: readArgs tail
end

/-! ## Term formers, spelled out -/

section Formers

variable {Γ : Ctx sig}

/-- The null process. -/
abbrev zeroT : Term (signature sig D) Γ .pr := .op (.inl .zero) .nil

/-- A parallel bag of a list of components. -/
abbrev bagT (l : Term (signature sig D) Γ .ps) : Term (signature sig D) Γ .pr :=
  .op (.inl .bag) (.cons l .nil)

/-- The empty list of components. -/
abbrev pnilT : Term (signature sig D) Γ .ps := .op (.inl .pnil) .nil

/-- A component before a list. -/
abbrev pconsT (p : Term (signature sig D) Γ .pr) (l : Term (signature sig D) Γ .ps) :
    Term (signature sig D) Γ .ps :=
  .op (.inl .pcons) (.cons p (.cons l .nil))

/-- An input on a channel, with a continuation open in the received name and its twin. -/
abbrev inputT (c : Term (signature sig D) Γ .nm) (b : Term (signature sig D) (.nm :: .pr :: Γ) .pr) :
    Term (signature sig D) Γ .pr :=
  .op (.inl .input) (.cons c (.cons b .nil))

/-- An output of a process on a channel. -/
abbrev outputT (c : Term (signature sig D) Γ .nm) (p : Term (signature sig D) Γ .pr) :
    Term (signature sig D) Γ .pr :=
  .op (.inl .output) (.cons c (.cons p .nil))

/-- The drop of a process's quote, `*@P`. -/
abbrev dropqT (p : Term (signature sig D) Γ .pr) : Term (signature sig D) Γ .pr :=
  .op (.inl .dropq) (.cons p .nil)

/-- The quote of a process. -/
abbrev quoteT (p : Term (signature sig D) Γ .pr) : Term (signature sig D) Γ .nm :=
  .op (.inl .quote) (.cons p .nil)

/-- The name bound by the nearest input. -/
abbrev nameVar : Term (signature sig D) (.nm :: .pr :: Γ) .nm := .var .zero

/-- The twin bound by the nearest input. -/
abbrev twinVar : Term (signature sig D) (.nm :: .pr :: Γ) .pr := .var (.succ .zero)

theorem read_zero : read (zeroT (D := D) (Γ := Γ)) = .apply "PZero" [] := rfl

theorem read_bag (l : Term (signature sig D) Γ .ps) : read (bagT l) = read l := rfl

theorem read_pnil : read (pnilT (D := D) (Γ := Γ)) = .collection .hashBag [] none := rfl

theorem read_pcons (p : Term (signature sig D) Γ .pr) (l : Term (signature sig D) Γ .ps) :
    read (pconsT p l) = consBag (read p) (read l) := rfl

theorem read_input (c : Term (signature sig D) Γ .nm)
    (b : Term (signature sig D) (.nm :: .pr :: Γ) .pr) :
    read (inputT c b) = .apply "PInput" [read c, .lambda none (read b)] := rfl

theorem read_output (c : Term (signature sig D) Γ .nm) (p : Term (signature sig D) Γ .pr) :
    read (outputT c p) = .apply "POutput" [read c, read p] := rfl

theorem read_dropq (p : Term (signature sig D) Γ .pr) :
    read (dropqT p) = .apply "PDrop" [.apply "NQuote" [read p]] := rfl

theorem read_quote (p : Term (signature sig D) Γ .pr) :
    read (quoteT p) = .apply "NQuote" [read p] := rfl

theorem read_nameVar : read (nameVar (D := D) (Γ := Γ)) = .bvar 0 := rfl

theorem read_twinVar : read (twinVar (D := D) (Γ := Γ)) = .apply "PDrop" [.bvar 0] := rfl

end Formers

/-! ## Read-back of a list is a bag -/

/-- The shape a read-back has at a sort: a list of processes reads back as a bag. -/
def BagShaped : Srt → Pattern → Prop
  | .ps, p => ∃ elements, p = .collection .hashBag elements none
  | _, _ => True

mutual
  theorem read_shaped : ∀ {Γ : Ctx sig} {s : Srt} (t : Term (signature sig noUnknowns) Γ s),
      BagShaped s (read t)
    | _, .nm, .var _ => trivial
    | _, .pr, .var _ => trivial
    | _, .ps, .var _ => ⟨[], rfl⟩
    | _, _, .op (.inl .zero) _ => trivial
    | _, _, .op (.inl .bag) _ => trivial
    | _, _, .op (.inl .pnil) _ => ⟨[], rfl⟩
    | _, _, .op (.inl .pcons) (.cons p (.cons l .nil)) => by
        obtain ⟨elements, same⟩ := (read_shaped l : BagShaped .ps (read l))
        refine ⟨read p :: elements, ?_⟩
        change consBag (read p) (read l) = _
        rw [same]
        rfl
    | _, _, .op (.inl .input) _ => trivial
    | _, _, .op (.inl .output) _ => trivial
    | _, _, .op (.inl .dropq) _ => trivial
    | _, _, .op (.inl .quote) _ => trivial
    | _, _, .op (.inr o) _ => o.key.elim

  theorem readArgs_shaped : ∀ {as : List (List Srt × Srt)} {Γ : Ctx sig}
      (args : Args (signature sig noUnknowns) as Γ),
      List.Forall₂ (fun (a : List Srt × Srt) q => BagShaped a.2 q) as (readArgs args)
    | _, _, .nil => .nil
    | _, _, .cons head tail => .cons (read_shaped head) (readArgs_shaped tail)
end

/-- **A list of processes reads back as a parallel bag.** -/
theorem read_ps_ground {Γ : Ctx sig} (l : Term (signature sig noUnknowns) Γ .ps) :
    ∃ elements, read l = .collection .hashBag elements none :=
  read_shaped l

#print axioms read_ps_ground

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.ByInstantiation
