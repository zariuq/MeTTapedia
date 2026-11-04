import Mettapedia.Logic.ConstraintTypes.ScopedConstraints
import Mettapedia.Logic.ConstraintTypes.RegularTree

/-!
# Parametric constructor typing as scoped equations

Each constructor rule has fresh parameters, optional field requirements and a
result type. A rule with no field requirements can express a nominal annotation
on a whole value; such an annotation does not establish field invariants.
Finite alternatives compile to finite disjunctions of scoped equation systems.
The compiler is exact for the independent typing derivation relation.

Lookup contexts are explicit. They can describe one fixed declaration world or
the rule reads at individual occurrences; no global type-world snapshot is part
of the algorithm.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ConstraintTypes.ConstructorTyping

open SymbolicTypes ScopedConstraints

variable {P Q C S Context : Type} {typeArity : C → Nat} {valueArity : S → Nat}

structure Rule (P Q C : Type) (typeArity : C → Nat) (fields : Nat) where
  field : Fin fields → Option (Expr P Q C typeArity)
  result : Expr P Q C typeArity

structure System (Context P Q C S : Type) (typeArity : C → Nat) (valueArity : S → Nat) where
  childContext : Context → (symbol : S) → Fin (valueArity symbol) → Context
  rules : Context → (symbol : S) → (Fin (valueArity symbol) → Tree S valueArity) →
    List (Rule P Q C typeArity (valueArity symbol))

inductive HasType (system : System Context P Q C S typeArity valueArity) :
    Context → Tree S valueArity → Closed Q C typeArity → Prop where
  | node {context : Context} {symbol : S} {children : Fin (valueArity symbol) → Tree S valueArity}
      (rule : Rule P Q C typeArity (valueArity symbol))
      (present : rule ∈ system.rules context symbol children)
      (parameters : P → Closed Q C typeArity)
      (typedFields : ∀ i fieldType, rule.field i = some fieldType →
        HasType system (system.childContext context symbol i) (children i) (fieldType.substitute parameters)) :
      HasType system context (.node symbol children) (rule.result.substitute parameters)

theorem hasType_node_iff (system : System Context P Q C S typeArity valueArity)
    (context : Context) (symbol : S) (children : Fin (valueArity symbol) → Tree S valueArity)
    (type : Closed Q C typeArity) :
    HasType system context (.node symbol children) type ↔
      ∃ rule ∈ system.rules context symbol children, ∃ parameters,
        type = rule.result.substitute parameters ∧
        ∀ i fieldType, rule.field i = some fieldType →
          HasType system (system.childContext context symbol i) (children i) (fieldType.substitute parameters) := by
  constructor
  · intro typed
    cases typed with | node rule present parameters fields => exact ⟨rule, present, parameters, rfl, fields⟩
  · rintro ⟨rule, present, parameters, rfl, fields⟩
    exact .node rule present parameters fields

def compile [DecidableEq P] (system : System Context P Q C S typeArity valueArity)
    {X : Type} (context : Context) : Tree S valueArity → Expr X Q C typeArity →
      List (Problem X Q C typeArity)
  | .node symbol children, target =>
      (system.rules context symbol children).flatMap fun rule =>
        (combinations ((List.finRange (valueArity symbol)).map fun i =>
          match rule.field i with
          | none => [truth]
          | some fieldType => compile system (X := X ⊕ P) (system.childContext context symbol i)
              (children i) (fieldType.rename Sum.inr))).map fun body =>
          bind (conjunction (equation (target.rename Sum.inl) (rule.result.rename Sum.inr)) body)

/-- Fresh constructor parameters and all field alternatives preserve precisely
the declarative typing relation, including shared parameters and nominal rows. -/
theorem compile_correct [DecidableEq P] (system : System Context P Q C S typeArity valueArity)
    (value : Tree S valueArity) {X : Type} (context : Context)
    (target : Expr X Q C typeArity) (outer : X → Closed Q C typeArity) :
    alternativesSatisfy (compile system context value target) outer ↔
      HasType system context value (target.substitute outer) := by
  induction value generalizing X context with
  | node symbol children ih =>
      constructor
      · rintro ⟨problem, member, solved⟩
        obtain ⟨rule, present, member⟩ := List.mem_flatMap.1 member
        obtain ⟨body, bodyMember, rfl⟩ := List.mem_map.1 member
        obtain ⟨parameters, solved⟩ := (satisfies_bind _ _).1 solved
        obtain ⟨root, fields⟩ := (satisfies_conjunction _ _ _).1 solved
        have resultType : target.substitute outer = rule.result.substitute parameters := by
          simpa only [TypeExpr.substitute_rename, Function.comp_def, Sum.elim_inl, Sum.elim_inr] using
            (satisfies_equation _ _ _).1 root
        have allFields := (satisfies_combinations _ _).1 ⟨body, bodyMember, fields⟩
        rw [resultType]
        refine .node rule present parameters ?_
        intro i fieldType required
        have child := allFields _ (List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩)
        simp only [required] at child
        have typed := (ih i (system.childContext context symbol i)
          (fieldType.rename Sum.inr) (Sum.elim outer parameters)).1 child
        simpa only [TypeExpr.substitute_rename, Function.comp_def, Sum.elim_inr] using typed
      · intro typed
        obtain ⟨rule, present, parameters, resultType, fields⟩ := (hasType_node_iff _ _ _ _ _).1 typed
        have chosen : alternativesSatisfy
            (combinations ((List.finRange (valueArity symbol)).map fun i =>
              match rule.field i with
              | none => [truth]
              | some fieldType => compile system (X := X ⊕ P) (system.childContext context symbol i)
                  (children i) (fieldType.rename Sum.inr))) (Sum.elim outer parameters) := by
          apply (satisfies_combinations _ _).2
          intro choice member
          obtain ⟨i, _, rfl⟩ := List.mem_map.1 member
          cases required : rule.field i with
          | none => exact ⟨truth, List.mem_cons_self, satisfies_truth _⟩
          | some fieldType =>
              apply (ih i (system.childContext context symbol i)
                (fieldType.rename Sum.inr) (Sum.elim outer parameters)).2
              simpa only [TypeExpr.substitute_rename, Function.comp_def, Sum.elim_inr] using
                fields i fieldType required
        obtain ⟨body, bodyMember, solved⟩ := chosen
        refine ⟨_, List.mem_flatMap.2 ⟨rule, present,
          List.mem_map.2 ⟨body, bodyMember, rfl⟩⟩, ?_⟩
        apply (satisfies_bind _ _).2
        refine ⟨parameters, (satisfies_conjunction _ _ _).2 ⟨?_, solved⟩⟩
        apply (satisfies_equation _ _ _).2
        simpa only [TypeExpr.substitute_rename, Function.comp_def, Sum.elim_inl, Sum.elim_inr] using resultType

def check [DecidableEq P] [DecidableEq Q] [DecidableEq C]
    (system : System Context P Q C S typeArity valueArity) (context : Context)
    (value : Tree S valueArity) (type : Closed Q C typeArity) : Bool :=
  accept (compile system (X := Empty) context value (embedClosed type))

/-- A complete executable checker for finite values and finite parametric
constructor alternatives. Existential fields and infinitely many possible
instances of a constructor scheme do not require type enumeration. -/
theorem check_iff_hasType [DecidableEq P] [DecidableEq Q] [DecidableEq C]
    (system : System Context P Q C S typeArity valueArity) (context : Context)
    (value : Tree S valueArity) (type : Closed Q C typeArity) :
    check system context value type = true ↔ HasType system context value type := by
  rw [check, accept_iff type]
  constructor
  · rintro ⟨outer, solved⟩
    simpa only [close_embed] using (compile_correct _ _ _ _ _).1 solved
  · intro typed
    refine ⟨Empty.elim, (compile_correct _ _ _ _ _).2 ?_⟩
    simpa only [close_embed] using typed

end Mettapedia.Logic.ConstraintTypes.ConstructorTyping
