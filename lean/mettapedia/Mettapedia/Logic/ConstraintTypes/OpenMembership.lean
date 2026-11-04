import Mettapedia.Logic.ConstraintTypes.Constraints
import Mettapedia.Logic.ConstraintTypes.Contracts

/-!
# Compiling open constructor membership into joint constraints

Known constructors are checked immediately. Unknown leaves become internal
membership atoms. Conjunction keeps shared requirements together; disjunction
keeps overload alternatives together. These formulas describe residual checks,
not additional values in the language being typed.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ConstraintTypes

inductive Formula (Variable State : Type) where
  | yes
  | no
  | atom (name : Variable) (state : State)
  | both (left right : Formula Variable State)
  | either (left right : Formula Variable State)
  deriving DecidableEq, Repr

namespace Formula

variable {X Y Q S : Type} {arity : S → Nat}

def evaluate (member : X → Q → Bool) : Formula X Q → Bool
  | .yes => true
  | .no => false
  | .atom x q => member x q
  | .both a b => evaluate member a && evaluate member b
  | .either a b => evaluate member a || evaluate member b

def and (a b : Formula X Q) : Formula X Q :=
  match a, b with
  | .no, _ | _, .no => .no
  | .yes, b => b
  | a, .yes => a
  | a, b => .both a b

def or (a b : Formula X Q) : Formula X Q :=
  match a, b with
  | .yes, _ | _, .yes => .yes
  | .no, b => b
  | a, .no => a
  | a, b => .either a b

theorem evaluate_and (member : X → Q → Bool) (a b : Formula X Q) :
    (a.and b).evaluate member = (a.evaluate member && b.evaluate member) := by
  cases a <;> cases b <;> simp [and, evaluate]

theorem evaluate_or (member : X → Q → Bool) (a b : Formula X Q) :
    (a.or b).evaluate member = (a.evaluate member || b.evaluate member) := by
  cases a <;> cases b <;> simp [or, evaluate]

def conjunction : List (Formula X Q) → Formula X Q
  | [] => .yes
  | a :: rest => a.and (conjunction rest)

def disjunction : List (Formula X Q) → Formula X Q
  | [] => .no
  | a :: rest => a.or (disjunction rest)

theorem evaluate_conjunction (member : X → Q → Bool) (formulas : List (Formula X Q)) :
    (conjunction formulas).evaluate member = formulas.all (evaluate member) := by
  induction formulas with
  | nil => rfl
  | cons a rest ih => simp [conjunction, evaluate_and, ih]

theorem evaluate_disjunction (member : X → Q → Bool) (formulas : List (Formula X Q)) :
    (disjunction formulas).evaluate member = formulas.any (evaluate member) := by
  induction formulas with
  | nil => rfl
  | cons a rest ih => simp [disjunction, evaluate_or, ih]

def variables : Formula X Q → List X
  | .yes | .no => []
  | .atom x _ => [x]
  | .both a b | .either a b => a.variables ++ b.variables

theorem evaluate_congr (formula : Formula X Q) (left right : X → Q → Bool)
    (agree : ∀ x ∈ formula.variables, ∀ q, left x q = right x q) :
    formula.evaluate left = formula.evaluate right := by
  induction formula with
  | yes | no => rfl
  | atom x q => exact agree x (by simp [variables]) q
  | both a b iha ihb =>
      simp only [evaluate]
      rw [iha (fun x hx => agree x (List.mem_append_left _ hx)),
          ihb (fun x hx => agree x (List.mem_append_right _ hx))]
  | either a b iha ihb =>
      simp only [evaluate]
      rw [iha (fun x hx => agree x (List.mem_append_left _ hx)),
          ihb (fun x hx => agree x (List.mem_append_right _ hx))]

def compile (grammar : Grammar Q S arity) : OpenTree X S arity → Q → Formula X Q
  | .var x, q => .atom x q
  | .node s children, q => disjunction ((grammar.productions q s).map fun fields =>
      conjunction ((List.finRange (arity s)).map fun i => compile grammar (children i) (fields i)))

/-- The emitted residual formula recognizes exactly the closed values described
by the grammar, under every valuation of its open variables. -/
theorem compile_correct (grammar : Grammar Q S arity) (term : OpenTree X S arity)
    (q : Q) (valuation : X → Tree S arity) :
    (compile grammar term q).evaluate (fun x state => grammar.accepts (valuation x) state) =
      grammar.accepts (term.evaluate valuation) q := by
  induction term generalizing q with
  | var _ => rfl
  | node s children ih =>
      simp only [compile, evaluate_disjunction, List.any_map, OpenTree.evaluate, Grammar.accepts]
      apply congrArg ((grammar.productions q s).any)
      funext fields
      change (conjunction ((List.finRange (arity s)).map
        (fun i => compile grammar (children i) (fields i)))).evaluate _ = _
      rw [evaluate_conjunction, List.all_map]
      apply congrArg ((List.finRange (arity s)).all)
      funext i
      exact ih i _

def substitute (grammar : Grammar Q S arity) (substitution : X → OpenTree Y S arity) :
    Formula X Q → Formula Y Q
  | .yes => .yes
  | .no => .no
  | .atom x q => compile grammar (substitution x) q
  | .both a b => (substitute grammar substitution a).and (substitute grammar substitution b)
  | .either a b => (substitute grammar substitution a).or (substitute grammar substitution b)

theorem evaluate_substitute (grammar : Grammar Q S arity)
    (substitution : X → OpenTree Y S arity) (valuation : Y → Tree S arity)
    (formula : Formula X Q) :
    (formula.substitute grammar substitution).evaluate
        (fun x state => grammar.accepts (valuation x) state) =
      formula.evaluate (fun x state => grammar.accepts ((substitution x).evaluate valuation) state) := by
  induction formula with
  | yes | no => rfl
  | atom x q => exact compile_correct grammar (substitution x) q valuation
  | both a b iha ihb => simp [substitute, evaluate_and, evaluate, iha, ihb]
  | either a b iha ihb => simp [substitute, evaluate_or, evaluate, iha, ihb]

/-- Binding before compiling a check and transferring its residual check after
binding have identical denotations, for an unchanged grammar. -/
theorem compile_binding_commutes (grammar : Grammar Q S arity)
    (substitution : X → OpenTree Y S arity) (valuation : Y → Tree S arity)
    (term : OpenTree X S arity) (q : Q) :
    (compile grammar (term.substitute substitution) q).evaluate
        (fun x state => grammar.accepts (valuation x) state) =
      ((compile grammar term q).substitute grammar substitution).evaluate
        (fun x state => grammar.accepts (valuation x) state) := by
  rw [compile_correct, evaluate_substitute, compile_correct, OpenTree.evaluate_substitute]

/-- A formula's delayed atoms use the grammar current when they are run.
Known constructor decisions in an already-entered check remain its own code. -/
def obligation {W : Type} (grammars : W → Grammar Q S arity)
    (formula : Formula X Q) : Obligation W X (Tree S arity) where
  support := formula.variables
  test world valuation := formula.evaluate fun x q => (grammars world).accepts (valuation x) q
  respects world left right agree := formula.evaluate_congr _ _ (fun x hx q => by
    rw [agree x hx])

/-- Reject a known contradiction immediately and omit completed checks. A
pending joint relation remains one item, even when it contains alternatives. -/
def prune : List (Formula X Q) → Option (List (Formula X Q))
  | [] => some []
  | formula :: rest => match formula, prune rest with
      | .no, _ => none
      | _, none => none
      | .yes, some pending => some pending
      | formula, some pending => some (formula :: pending)

def satisfiesPending (member : X → Q → Bool) : Option (List (Formula X Q)) → Bool
  | none => false
  | some pending => pending.all (evaluate member)

theorem prune_correct (member : X → Q → Bool) (pending : List (Formula X Q)) :
    satisfiesPending member (prune pending) = pending.all (evaluate member) := by
  induction pending with
  | nil => rfl
  | cons formula rest ih =>
      cases formula <;> cases hp : prune rest <;>
        simp_all [prune, satisfiesPending, evaluate]

/-- Every binding rewrites the whole residual relation, rather than waiting for
all its variables to be ground. A bad bound argument therefore fails even if
an unrelated argument is still open. -/
def transferPending (grammar : Grammar Q S arity)
    (substitution : X → OpenTree Y S arity) (pending : List (Formula X Q)) :
    Option (List (Formula Y Q)) :=
  prune (pending.map (substitute grammar substitution))

theorem transferPending_correct (grammar : Grammar Q S arity)
    (substitution : X → OpenTree Y S arity) (pending : List (Formula X Q))
    (valuation : Y → Tree S arity) :
    satisfiesPending (fun x q => grammar.accepts (valuation x) q)
        (transferPending grammar substitution pending) =
      pending.all (fun formula => formula.evaluate
        (fun x q => grammar.accepts ((substitution x).evaluate valuation) q)) := by
  rw [transferPending, prune_correct, List.all_map]
  apply congrArg pending.all
  funext formula
  exact evaluate_substitute grammar substitution valuation formula

end Formula

namespace OpenContract

variable {P Q C X S : Type} {typeArity : C → Nat} {termArity : S → Nat} {n : Nat}

def instanceFormula (grammar : Grammar Q S termArity)
    (construct : (c : C) → (Fin (typeArity c) → Q) → Q)
    (signature : Signature P Q C typeArity n) (assignment : P → Q)
    (args : Fin n → OpenTree X S termArity) (out : OpenTree X S termArity) : Formula X Q :=
  Formula.conjunction
    (((List.finRange n).map fun i => Formula.compile grammar (args i)
      ((signature.argument i).instantiate construct assignment)) ++
      [Formula.compile grammar out (signature.result.instantiate construct assignment)])

theorem instanceFormula_correct (grammar : Grammar Q S termArity)
    (construct : (c : C) → (Fin (typeArity c) → Q) → Q)
    (signature : Signature P Q C typeArity n) (assignment : P → Q)
    (args : Fin n → OpenTree X S termArity) (out : OpenTree X S termArity)
    (valuation : X → Tree S termArity) :
    (instanceFormula grammar construct signature assignment args out).evaluate
        (fun x q => grammar.accepts (valuation x) q) =
      signature.acceptsInstance (fun (_ : Unit) q v => grammar.accepts v q)
        construct () assignment (fun i => (args i).evaluate valuation) (out.evaluate valuation) := by
  simp [instanceFormula, Formula.evaluate_conjunction, Formula.compile_correct,
    Signature.acceptsInstance, Function.comp_def]

def compile (grammar : Grammar Q S termArity)
    (construct : (c : C) → (Fin (typeArity c) → Q) → Q)
    (instances : List (P → Q)) (declarations : List (Signature P Q C typeArity n))
    (args : Fin n → OpenTree X S termArity) (out : OpenTree X S termArity) : Formula X Q :=
  Formula.disjunction (declarations.map fun signature =>
    Formula.disjunction (instances.map fun assignment =>
      instanceFormula grammar construct signature assignment args out))

/-- One residual formula implements the entire overload set, using one shared
type assignment for all positions of each candidate signature. -/
theorem compile_correct (grammar : Grammar Q S termArity)
    (construct : (c : C) → (Fin (typeArity c) → Q) → Q)
    (instances : List (P → Q)) (declarations : List (Signature P Q C typeArity n))
    (args : Fin n → OpenTree X S termArity) (out : OpenTree X S termArity)
    (valuation : X → Tree S termArity) :
    (compile grammar construct instances declarations args out).evaluate
        (fun x q => grammar.accepts (valuation x) q) =
      Overloads.check (fun (_ : Unit) q v => grammar.accepts v q) construct instances declarations
        () (fun i => (args i).evaluate valuation) (out.evaluate valuation) := by
  simp [compile, Formula.evaluate_disjunction, instanceFormula_correct,
    Overloads.check, Function.comp_def]

/-- Fundamental soundness: a satisfying realization of the residual contract
has one declaration and one shared type instance, with constructor derivations
for every argument and the result. -/
theorem realization_sound (grammar : Grammar Q S termArity)
    (construct : (c : C) → (Fin (typeArity c) → Q) → Q)
    (instances : List (P → Q)) (declarations : List (Signature P Q C typeArity n))
    (args : Fin n → OpenTree X S termArity) (out : OpenTree X S termArity)
    (valuation : X → Tree S termArity)
    (satisfies : (compile grammar construct instances declarations args out).evaluate
      (fun x q => grammar.accepts (valuation x) q) = true) :
    ∃ signature ∈ declarations, ∃ assignment ∈ instances,
      (∀ i, grammar.Derives ((signature.argument i).instantiate construct assignment)
        ((args i).evaluate valuation)) ∧
      grammar.Derives (signature.result.instantiate construct assignment) (out.evaluate valuation) := by
  rw [compile_correct] at satisfies
  obtain ⟨signature, hs, assignment, ha, inputs, result⟩ :=
    (Overloads.check_iff _ _ _ _ _ _ _).1 satisfies
  exact ⟨signature, hs, assignment, ha,
    fun i => (grammar.accepts_iff_derives _ _).1 (inputs i),
    (grammar.accepts_iff_derives _ _).1 result⟩

end OpenContract

end Mettapedia.Logic.ConstraintTypes
