import Mettapedia.Logic.ConstraintTypes.ScopedConstraints
import Mettapedia.Logic.ConstraintTypes.Constraints

/-!
# Checking patterns over proper type witnesses

A checking wildcard omits an explicitly written requirement. It is not a
proper type that a scheme parameter can infer. Pattern operators have sorted
arguments: for example, an element predicate and an exact type index need not
have the same interpretation. Finite positive decompositions give an exact
compiler into the existing scoped equations and total unifier.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ConstraintTypes.CheckingPatterns

open SymbolicTypes ScopedConstraints

structure Signature (Kind : Type) where
  symbol : Kind → Type
  arity : {s : Kind} → symbol s → Nat
  argumentSort : {s : Kind} → (op : symbol s) → Fin (arity op) → Kind

variable {Kind : Type} {sig : Signature Kind} {Carrier : Kind → Type}
  {Context P Q C : Type} {typeArity : C → Nat}

structure Query {s : Kind} (op : sig.symbol s) (Carrier : Kind → Type) (Context : Type) where
  index : Fin (sig.arity op)
  context : Context
  subject : Carrier (sig.argumentSort op index)

structure Model (sig : Signature Kind) (Carrier : Kind → Type) (Context Q C : Type)
    (typeArity : C → Nat) where
  member : {s : Kind} → Context → Carrier s → Closed Q C typeArity → Prop
  branches : {s : Kind} → (op : sig.symbol s) → Context → Carrier s →
    List (List (Query op Carrier Context))

inductive Pattern (sig : Signature Kind) (P Q C : Type) (typeArity : C → Nat) : Kind → Type where
  | any {s : Kind} : Pattern sig P Q C typeArity s
  | proper {s : Kind} (type : Expr P Q C typeArity) : Pattern sig P Q C typeArity s
  | apply {s : Kind} (op : sig.symbol s)
      (arguments : (i : Fin (sig.arity op)) → Pattern sig P Q C typeArity (sig.argumentSort op i)) :
      Pattern sig P Q C typeArity s

inductive Matches (model : Model sig Carrier Context Q C typeArity)
    (parameters : P → Closed Q C typeArity) :
    {s : Kind} → Pattern sig P Q C typeArity s → Context → Carrier s → Prop where
  | any {s : Kind} (context : Context) (subject : Carrier s) : Matches model parameters .any context subject
  | proper {s : Kind} (type : Expr P Q C typeArity) (context : Context) (subject : Carrier s)
      (typed : model.member context subject (type.substitute parameters)) :
      Matches model parameters (.proper type) context subject
  | apply {s : Kind} (op : sig.symbol s)
      (arguments : (i : Fin (sig.arity op)) → Pattern sig P Q C typeArity (sig.argumentSort op i))
      (context : Context) (subject : Carrier s) (branch : List (Query op Carrier Context))
      (present : branch ∈ model.branches op context subject)
      (checked : ∀ query ∈ branch, Matches model parameters (arguments query.index) query.context query.subject) :
      Matches model parameters (.apply op arguments) context subject

@[simp] theorem matches_any (model : Model sig Carrier Context Q C typeArity)
    (parameters : P → Closed Q C typeArity) {s : Kind} (context : Context) (subject : Carrier s) :
    Matches model parameters (.any : Pattern sig P Q C typeArity s) context subject := .any _ _

@[simp] theorem matches_proper_iff (model : Model sig Carrier Context Q C typeArity)
    (parameters : P → Closed Q C typeArity) {s : Kind} (type : Expr P Q C typeArity)
    (context : Context) (subject : Carrier s) :
    Matches model parameters (.proper type) context subject ↔
      model.member context subject (type.substitute parameters) := by
  constructor
  · intro h; cases h with | proper _ _ _ typed => exact typed
  · exact .proper _ _ _

theorem matches_apply_iff (model : Model sig Carrier Context Q C typeArity)
    (parameters : P → Closed Q C typeArity) {s : Kind} (op : sig.symbol s)
    (arguments : (i : Fin (sig.arity op)) → Pattern sig P Q C typeArity (sig.argumentSort op i))
    (context : Context) (subject : Carrier s) :
    Matches model parameters (.apply op arguments) context subject ↔
      ∃ branch ∈ model.branches op context subject,
        ∀ query ∈ branch, Matches model parameters (arguments query.index) query.context query.subject := by
  constructor
  · intro h; cases h with | apply _ _ _ _ branch present checked => exact ⟨branch, present, checked⟩
  · rintro ⟨branch, present, checked⟩; exact .apply _ _ _ _ branch present checked

/-- Proper membership may use the existing declaration checker; an index leaf
may instead compile equality with the supplied closed type. -/
structure Compiler (model : Model sig Carrier Context Q C typeArity) where
  proper : {X : Type} → [DecidableEq X] → {s : Kind} → Context → Carrier s →
    Expr X Q C typeArity → List (Problem X Q C typeArity)
  correct : ∀ {X : Type} [DecidableEq X] {s : Kind} (context : Context) (subject : Carrier s)
    (type : Expr X Q C typeArity) (parameters : X → Closed Q C typeArity),
    alternativesSatisfy (proper context subject type) parameters ↔
      model.member context subject (type.substitute parameters)

def compile [DecidableEq P] (model : Model sig Carrier Context Q C typeArity)
    (compiler : Compiler model) : {s : Kind} → Pattern sig P Q C typeArity s →
      Context → Carrier s → List (Problem P Q C typeArity)
  | _, .any, _, _ => [truth]
  | _, .proper type, context, subject => compiler.proper context subject type
  | _, .apply op arguments, context, subject =>
      (model.branches op context subject).flatMap fun branch =>
        combinations (branch.map fun query => compile model compiler (arguments query.index) query.context query.subject)

theorem compile_correct [DecidableEq P] (model : Model sig Carrier Context Q C typeArity)
    (compiler : Compiler model) {s : Kind} (pattern : Pattern sig P Q C typeArity s)
    (context : Context) (subject : Carrier s) (parameters : P → Closed Q C typeArity) :
    alternativesSatisfy (compile model compiler pattern context subject) parameters ↔
      Matches model parameters pattern context subject := by
  induction pattern generalizing context with
  | any =>
      simp only [compile, alternativesSatisfy, List.mem_singleton, exists_eq_left]
      exact ⟨fun _ => .any _ _, fun _ => satisfies_truth _⟩
  | proper type => simpa only [compile, matches_proper_iff] using compiler.correct context subject type parameters
  | apply op arguments ih =>
      rw [matches_apply_iff]
      constructor
      · rintro ⟨problem, present, solved⟩
        obtain ⟨branch, branchPresent, chosen⟩ := List.mem_flatMap.1 present
        have all := (satisfies_combinations _ _).1 ⟨problem, chosen, solved⟩
        refine ⟨branch, branchPresent, ?_⟩
        intro query queryPresent
        exact (ih query.index query.context query.subject).1
          (all _ (List.mem_map.2 ⟨query, queryPresent, rfl⟩))
      · rintro ⟨branch, branchPresent, checked⟩
        have all : ∀ choice ∈ branch.map (fun query => compile model compiler
            (arguments query.index) query.context query.subject), alternativesSatisfy choice parameters := by
          intro choice present
          obtain ⟨query, queryPresent, rfl⟩ := List.mem_map.1 present
          exact (ih query.index query.context query.subject).2 (checked query queryPresent)
        obtain ⟨problem, present, solved⟩ := (satisfies_combinations _ _).2 all
        exact ⟨problem, List.mem_flatMap.2 ⟨branch, branchPresent, present⟩, solved⟩

/-- Relaxation concerns explicitly written checks, preserving every proper
parameter assignment. It assumes no variance law for an exact proper type. -/
inductive Weakens : {s : Kind} → Pattern sig P Q C typeArity s → Pattern sig P Q C typeArity s → Prop where
  | refl {s : Kind} (pattern : Pattern sig P Q C typeArity s) : Weakens pattern pattern
  | wildcard {s : Kind} (pattern : Pattern sig P Q C typeArity s) : Weakens pattern .any
  | apply {s : Kind} (op : sig.symbol s)
      (strong weak : (i : Fin (sig.arity op)) → Pattern sig P Q C typeArity (sig.argumentSort op i))
      (arguments : ∀ i, Weakens (strong i) (weak i)) : Weakens (.apply op strong) (.apply op weak)
  | trans {s : Kind} {first middle last : Pattern sig P Q C typeArity s}
      (left : Weakens first middle) (right : Weakens middle last) : Weakens first last

theorem weakening_preserves_witness (model : Model sig Carrier Context Q C typeArity)
    (parameters : P → Closed Q C typeArity) {s : Kind}
    {strong weak : Pattern sig P Q C typeArity s} (relaxed : Weakens strong weak)
    (context : Context) (subject : Carrier s) :
    Matches model parameters strong context subject → Matches model parameters weak context subject := by
  induction relaxed generalizing context with
  | refl => exact id
  | wildcard => exact fun _ => .any _ _
  | apply op strong weak _ ih =>
      intro matched
      obtain ⟨branch, present, checked⟩ := (matches_apply_iff _ _ _ _ _ _).1 matched
      exact .apply _ _ _ _ branch present (fun query member => ih query.index _ _ (checked query member))
  | trans _ _ left right => exact fun matched => right _ _ (left _ _ matched)

def Pattern.substitute {X : Type} (substitution : P → Expr X Q C typeArity) :
    {s : Kind} → Pattern sig P Q C typeArity s → Pattern sig X Q C typeArity s
  | _, .any => .any
  | _, .proper type => .proper (type.substitute substitution)
  | _, .apply op arguments => .apply op (fun i => (arguments i).substitute substitution)

theorem matches_substitute {X : Type} (model : Model sig Carrier Context Q C typeArity)
    (substitution : P → Expr X Q C typeArity) (parameters : X → Closed Q C typeArity)
    {s : Kind} (pattern : Pattern sig P Q C typeArity s) (context : Context) (subject : Carrier s) :
    Matches model parameters (pattern.substitute substitution) context subject ↔
      Matches model (fun p => (substitution p).substitute parameters) pattern context subject := by
  induction pattern generalizing context with
  | any => constructor <;> intro _ <;> exact .any _ _
  | proper type => simp only [Pattern.substitute, matches_proper_iff, TypeExpr.substitute_comp]
  | apply op arguments ih =>
      simp only [Pattern.substitute, matches_apply_iff]
      constructor <;> rintro ⟨branch, present, checked⟩
      · exact ⟨branch, present, fun query member => (ih query.index _ _).1 (checked query member)⟩
      · exact ⟨branch, present, fun query member => (ih query.index _ _).2 (checked query member)⟩

/-- A source constructor may be expanded into checking operators only with this
compatibility law. A whole-value nominal fact need not imply structural field
requirements, so this is not a law of arbitrary type constructors. -/
def Coherent {s : Kind} (model : Model sig Carrier Context Q C typeArity) (op : sig.symbol s)
    (application : (Fin (sig.arity op) → Closed Q C typeArity) → Closed Q C typeArity) : Prop :=
  ∀ (X : Type) (parameters : X → Closed Q C typeArity) types context subject,
    model.member context subject (application types) ↔
      Matches model parameters (.apply op (fun i => .proper (embedClosed (types i)))) context subject

theorem coherent_constructor_weakening {s : Kind} (model : Model sig Carrier Context Q C typeArity)
    (op : sig.symbol s) (application : (Fin (sig.arity op) → Closed Q C typeArity) → Closed Q C typeArity)
    (coherent : Coherent model op application) (parameters : P → Closed Q C typeArity)
    (types : Fin (sig.arity op) → Closed Q C typeArity)
    (checks : (i : Fin (sig.arity op)) → Pattern sig P Q C typeArity (sig.argumentSort op i))
    (relaxed : ∀ i, Weakens (.proper (embedClosed (types i))) (checks i))
    (context : Context) (subject : Carrier s) (typed : model.member context subject (application types)) :
    Matches model parameters (.apply op checks) context subject :=
  weakening_preserves_witness model parameters (.apply op _ _ relaxed) context subject
    ((coherent P parameters types context subject).1 typed)

/-- An open check denotes all completions of its term. Binding substitutes the
term, not the universe of proper type assignments. This is an extensional law;
it does not assert an implementation of incremental propagation. -/
theorem open_binding_commutes {X Y S : Type} {valueArity : S → Nat} {s : Kind}
    (model : Model sig Carrier Context Q C typeArity) (parameters : P → Closed Q C typeArity)
    (pattern : Pattern sig P Q C typeArity s) (context : Context)
    (observe : Tree S valueArity → Carrier s) (term : OpenTree X S valueArity)
    (binding : X → OpenTree Y S valueArity) (valuation : Y → Tree S valueArity) :
    Matches model parameters pattern context (observe ((term.substitute binding).evaluate valuation)) ↔
      Matches model parameters pattern context (observe (term.evaluate (fun x => (binding x).evaluate valuation))) := by
  rw [OpenTree.evaluate_substitute]

end Mettapedia.Logic.ConstraintTypes.CheckingPatterns
