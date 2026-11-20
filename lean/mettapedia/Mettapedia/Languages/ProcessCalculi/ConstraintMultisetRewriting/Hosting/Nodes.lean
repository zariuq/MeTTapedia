import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Toolkit

/-!
# Control written as data: nodes at the top sort

The translation writes the control of a computation (what an alternative is computing, and what
waits for its value) as rows of the step. A row is a datum of the source's own signature at the top
sort, so the readings of a row are closed data of the same signature as the source's answers, and no
second sort or embedding of signatures is involved.

`Nodes S Γ star` gives, for each control former (`Tag`), a constructor at the top sort that is
* natural in the family of unknowns (`instantiate_node`: instantiation acts on the arguments),
* injective in its arguments (`args_eq`), with distinct formers never equal (`tag_eq`),
at every family of unknowns. These are the only properties of nodes the hosting theorem uses.

The MeTTa signature has nodes: the tagged tuple `(tag a₁ … aₙ)` (`mettaNodes`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage SourceLanguage.Elaboration SourceLanguage.Toolkit

/-- The control formers: the computations (`ret`, `apply`, `bind` for `let_`,
`choice`, `fail`, `query`, and `outside` for other constructs); what an alternative is doing (`eval`,
`value`); what waits for its value (`empty`, `push`); an alternative (`alt`); and the left side of
an equation as a row (`eqn`), a fact at an address (`fact`), and the current
revision occurrence for an address (`revision`). -/
inductive Tag where
  | ret | apply | bind | choice | fail | outside
  | eval | value
  | empty | push
  | alt | eqn | query
  | fact | revision
  deriving DecidableEq

/-- How many data each former carries. -/
def Tag.arity : Tag → ℕ
  | .ret => 1
  | .apply => 1
  | .bind => 3
  | .choice => 2
  | .fail => 0
  | .outside => 0
  | .eval => 1
  | .value => 1
  | .empty => 0
  | .push => 3
  | .alt => 2
  | .eqn => 1
  | .query => 3
  | .fact => 2
  | .revision => 1

/-- The name of a former, as a symbol of the MeTTa signature. -/
def Tag.name : Tag → String
  | .ret => "ret"
  | .apply => "apply"
  | .bind => "bind"
  | .choice => "choice"
  | .fail => "fail"
  | .outside => "outside"
  | .eval => "eval"
  | .value => "value"
  | .empty => "empty"
  | .push => "push"
  | .alt => "alt"
  | .eqn => "eqn"
  | .query => "query"
  | .fact => "fact"
  | .revision => "revision"

theorem Tag.name_injective : Function.Injective Tag.name := by
  intro a b same
  cases a <;> cases b <;> first | rfl | (simp [Tag.name] at same)

/-- **Nodes**: a constructor at the top sort for each control former, natural in the family of
unknowns, injective, with distinct formers distinct. -/
structure Nodes (S : Signature) (Γ : Ctx S) (star : S.Srt) where
  node : {V : Type} → {D : V → MetaArity S} → (k : Tag) →
    (Fin k.arity → Term (signature S D) Γ star) → Term (signature S D) Γ star
  instantiate_node : ∀ {V W : Type} {D : V → MetaArity S} {E : W → MetaArity S}
    (σ : Assignment D E) (k : Tag) (args : Fin k.arity → Term (signature S D) Γ star),
      instantiate σ (node k args) = node k (fun i => instantiate σ (args i))
  tag_eq : ∀ {V : Type} {D : V → MetaArity S} {k k' : Tag}
    {args : Fin k.arity → Term (signature S D) Γ star}
    {args' : Fin k'.arity → Term (signature S D) Γ star}, node k args = node k' args' → k = k'
  args_eq : ∀ {V : Type} {D : V → MetaArity S} {k : Tag}
    {args args' : Fin k.arity → Term (signature S D) Γ star}, node k args = node k args' → args = args'

section TupleArguments

variable {S : Signature} {star : S.Srt}
  {X : Type} {target : X → MetaArity S} {Δ : Ctx S}

/-- The arguments of a tuple from a function on positions. -/
def argsOfFn : (n : ℕ) → (Fin n → Term (signature S target) Δ star) →
    Args (signature S target) (List.replicate n ([], star)) Δ
  | 0, _ => .nil
  | n + 1, f => .cons (f 0) (argsOfFn n fun i => f i.succ)

theorem instantiateArgs_argsOfFn {Y : Type} {next : Y → MetaArity S}
    (σ : Assignment target next) :
    ∀ (n : ℕ) (f : Fin n → Term (signature S target) Δ star),
      instantiateArgs σ (argsOfFn n f) = argsOfFn n (fun i => instantiate σ (f i))
  | 0, _ => rfl
  | n + 1, f => by
      simp only [argsOfFn, instantiateArgs, instantiateArgs_argsOfFn σ n]

theorem argsOfFn_injective :
    ∀ (n : ℕ) {f g : Fin n → Term (signature S target) Δ star}, argsOfFn n f = argsOfFn n g → f = g
  | 0, f, g, _ => funext fun i => i.elim0
  | n + 1, f, g, same => by
      obtain ⟨first, rest⟩ := Args.cons.inj same
      have tail := argsOfFn_injective n rest
      funext i
      refine Fin.cases first (fun j => ?_) i
      exact congrFun tail j

end TupleArguments

/-! ## The MeTTa signature has nodes: tagged tuples -/

section Metta

variable {X : Type} {target : X → MetaArity MSig} {Δ : Ctx MSig}

/-- The symbol at the head of a tuple, if any. -/
def firstSymbol : {as : List (List Unit × Unit)} → Args (signature MSig target) as Δ → Option String
  | _, .nil => none
  | _, .cons (.op (.inl (.sym s)) _) _ => some s
  | _, .cons _ _ => none

/-- The symbol a tuple starts with, if any. -/
def headSymbol : Term (signature MSig target) Δ () → Option String
  | .op (.inl _) args => firstSymbol args
  | _ => none

/-- The arguments of a tagged tuple: the tag's symbol, then the data. -/
def tagArgs (k : Tag) (args : Fin k.arity → Term (signature MSig target) Δ ()) :
    Args (signature MSig target) (List.replicate (k.arity + 1) ([], ())) Δ :=
  Args.cons (bs := []) (symAt k.name) (argsOfFn k.arity args)

/-- A tuple of `n` elements from its arguments. -/
def tupleOfArgs (n : ℕ) (a : Args (signature MSig target) (List.replicate n ([], ())) Δ) :
    Term (signature MSig target) Δ () :=
  .op (.inl (.tup n)) a

theorem instantiate_tupleOfArgs {Y : Type} {next : Y → MetaArity MSig} (σ : Assignment target next)
    (n : ℕ) (a : Args (signature MSig target) (List.replicate n ([], ())) Δ) :
    instantiate σ (tupleOfArgs n a) = tupleOfArgs n (instantiateArgs σ a) :=
  rfl

theorem tupleOfArgs_injective {n : ℕ} {a b : Args (signature MSig target) (List.replicate n ([], ())) Δ}
    (same : tupleOfArgs n a = tupleOfArgs n b) : a = b :=
  op_inj same

/-- **The tagged tuple** `(tag a₁ … aₙ)`. -/
def mettaNode (k : Tag) (args : Fin k.arity → Term (signature MSig target) Δ ()) :
    Term (signature MSig target) Δ () :=
  tupleOfArgs (k.arity + 1) (tagArgs k args)

theorem headSymbol_mettaNode (k : Tag) (args : Fin k.arity → Term (signature MSig target) Δ ()) :
    headSymbol (mettaNode k args) = some k.name := by
  rfl

theorem instantiateArgs_tagArgs {Y : Type} {next : Y → MetaArity MSig} (σ : Assignment target next)
    (k : Tag) (args : Fin k.arity → Term (signature MSig target) Δ ()) :
    instantiateArgs σ (tagArgs k args) = tagArgs k (fun i => instantiate σ (args i)) := by
  have unfolded : instantiateArgs σ (tagArgs k args) =
      Args.cons (S := signature MSig next) (bs := []) (Γ := Δ) (instantiate σ (symAt k.name))
        (instantiateArgs σ (argsOfFn k.arity args)) := rfl
  rw [unfolded, instantiateArgs_argsOfFn]
  rfl

theorem tagArgs_injective (k : Tag) {args args' : Fin k.arity → Term (signature MSig target) Δ ()}
    (same : tagArgs k args = tagArgs k args') : args = args' :=
  argsOfFn_injective k.arity (Args.cons.inj same).2

end Metta

/-- **The MeTTa signature has nodes.** -/
def mettaNodes : Nodes MSig [] () where
  node k args := mettaNode k args
  instantiate_node σ k args := by
    show instantiate σ (tupleOfArgs (k.arity + 1) (tagArgs k args)) = _
    rw [instantiate_tupleOfArgs, instantiateArgs_tagArgs]
    rfl
  tag_eq {_ _ k k' args args'} same := by
    have heads := congrArg headSymbol same
    rw [headSymbol_mettaNode, headSymbol_mettaNode] at heads
    exact Tag.name_injective (Option.some.inj heads)
  args_eq {_ _ k args args'} same := tagArgs_injective k (tupleOfArgs_injective same)

#print axioms Tag.name_injective
#print axioms mettaNodes

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting
