import Mettapedia.Logic.ConstraintTypes.ConstructorTyping
import Mettapedia.Logic.ConstraintTypes.ValuePatterns

/-!
# Closed-world typing from constructor and nominal declarations

Constructor declarations impose field requirements. Nominal facts match whole
values, including nonlinear patterns, and need not impose constructor-field
requirements. Both forms feed the same scoped constraint compiler. Checking is
proved sound and complete for this declaration judgment, rather than for a
separately chosen membership oracle.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ConstraintTypes.DeclarationTyping

open SymbolicTypes ScopedConstraints ConstructorTyping

variable {P PatternVariable Q C S Context : Type} {typeArity : C → Nat} {valueArity : S → Nat}

structure Fact (PatternVariable P Q C S : Type) (typeArity : C → Nat) (valueArity : S → Nat) where
  pattern : OpenTree PatternVariable S valueArity
  type : Expr P Q C typeArity
  bindings : List (ValuePatterns.TypeBinding P pattern) := []
  readType : Tree S valueArity → Option (Closed Q C typeArity) := fun _ => none

def Fact.prepare [DecidableEq P] [DecidableEq PatternVariable] [DecidableEq Q] [DecidableEq C] [DecidableEq S]
    (fact : Fact PatternVariable P Q C S typeArity valueArity) (value : Tree S valueArity) :
    Option (Expr P Q C typeArity) :=
  ValuePatterns.specialize fact.pattern fact.bindings fact.readType fact.type value

theorem Fact.prepare_iff [DecidableEq P] [DecidableEq PatternVariable] [DecidableEq Q] [DecidableEq C] [DecidableEq S]
    (fact : Fact PatternVariable P Q C S typeArity valueArity) (value : Tree S valueArity)
    (type : Closed Q C typeArity) :
    (∃ scheme, fact.prepare value = some scheme ∧ ∃ parameters, type = scheme.substitute parameters) ↔
      ∃ values, fact.pattern.evaluate values = value ∧ ∃ parameters,
        ValuePatterns.BindingsHold fact.readType values parameters fact.bindings ∧
        type = fact.type.substitute parameters :=
  ValuePatterns.specialize_iff _ _ _ _ _ _

structure Declarations (Context PatternVariable P Q C S : Type)
    (typeArity : C → Nat) (valueArity : S → Nat) where
  childContext : Context → (symbol : S) → Fin (valueArity symbol) → Context
  constructors : Context → (symbol : S) → List (Rule P Q C typeArity (valueArity symbol))
  facts : Context → List (Fact PatternVariable P Q C S typeArity valueArity)

abbrev factRule (type : Expr P Q C typeArity) (arity : Nat) :
    Rule P Q C typeArity arity where
  field _ := none
  result := type

def asSystem [DecidableEq P] [DecidableEq PatternVariable] [DecidableEq Q] [DecidableEq C] [DecidableEq S]
    (declarations : Declarations Context PatternVariable P Q C S typeArity valueArity) :
    System Context P Q C S typeArity valueArity where
  childContext := declarations.childContext
  rules context symbol children := declarations.constructors context symbol ++
    (declarations.facts context).filterMap fun fact =>
      (fact.prepare (.node symbol children)).map (fun type => factRule type (valueArity symbol))

inductive HasType (declarations : Declarations Context PatternVariable P Q C S typeArity valueArity) :
    Context → Tree S valueArity → Closed Q C typeArity → Prop where
  | constructor {context : Context} {symbol : S} {children : Fin (valueArity symbol) → Tree S valueArity}
      (rule : Rule P Q C typeArity (valueArity symbol))
      (present : rule ∈ declarations.constructors context symbol)
      (parameters : P → Closed Q C typeArity)
      (fields : ∀ i fieldType, rule.field i = some fieldType →
        HasType declarations (declarations.childContext context symbol i)
          (children i) (fieldType.substitute parameters)) :
      HasType declarations context (.node symbol children) (rule.result.substitute parameters)
  | nominal {context : Context} {value : Tree S valueArity}
      (fact : Fact PatternVariable P Q C S typeArity valueArity)
      (present : fact ∈ declarations.facts context)
      (values : PatternVariable → Tree S valueArity)
      (matched : fact.pattern.evaluate values = value)
      (parameters : P → Closed Q C typeArity)
      (bound : ValuePatterns.BindingsHold fact.readType values parameters fact.bindings) :
      HasType declarations context value (fact.type.substitute parameters)


theorem hasType_node_iff
    (declarations : Declarations Context PatternVariable P Q C S typeArity valueArity)
    (context : Context) (symbol : S) (children : Fin (valueArity symbol) → Tree S valueArity)
    (type : Closed Q C typeArity) :
    HasType declarations context (.node symbol children) type ↔
      (∃ rule ∈ declarations.constructors context symbol, ∃ parameters,
        type = rule.result.substitute parameters ∧
        ∀ i fieldType, rule.field i = some fieldType → HasType declarations
          (declarations.childContext context symbol i) (children i) (fieldType.substitute parameters)) ∨
      (∃ fact ∈ declarations.facts context, ∃ matched : PatternVariable → Tree S valueArity,
        fact.pattern.evaluate matched = .node symbol children ∧
        ∃ parameters, ValuePatterns.BindingsHold fact.readType matched parameters fact.bindings ∧
          type = fact.type.substitute parameters) := by
  constructor
  · intro typed
    cases typed with
    | constructor rule present parameters fields => exact .inl ⟨rule, present, parameters, rfl, fields⟩
    | nominal fact present matched equal parameters bound => exact .inr ⟨fact, present, matched, equal, parameters, bound, rfl⟩
  · rintro (⟨rule, present, parameters, rfl, fields⟩ | ⟨fact, present, matched, equal, parameters, bound, rfl⟩)
    · exact .constructor rule present parameters fields
    · exact .nominal fact present matched equal parameters bound

theorem asSystem_iff [DecidableEq P] [DecidableEq PatternVariable] [DecidableEq Q] [DecidableEq C] [DecidableEq S]
    (declarations : Declarations Context PatternVariable P Q C S typeArity valueArity)
    (context : Context) (value : Tree S valueArity) (type : Closed Q C typeArity) :
    ConstructorTyping.HasType (asSystem declarations) context value type ↔ HasType declarations context value type := by
  constructor
  · intro typed
    induction typed with
    | @node context symbol children rule present parameters fields ih =>
        rcases List.mem_append.1 present with constructorRule | nominalRule
        · exact .constructor rule constructorRule parameters ih
        · obtain ⟨fact, factPresent, selected⟩ := List.mem_filterMap.1 nominalRule
          cases prepared : fact.prepare (.node symbol children) with
          | none => simp [prepared] at selected
          | some scheme =>
              simp only [prepared, Option.map_some, Option.some.injEq] at selected
              subst rule
              obtain ⟨values, matched, actual, bound, equal⟩ :=
                (Fact.prepare_iff fact (.node symbol children) (scheme.substitute parameters)).1
                  ⟨scheme, prepared, parameters, rfl⟩
              rw [equal]
              exact .nominal fact factPresent values matched actual bound
  · intro typed
    induction typed with
    | constructor rule present parameters fields ih =>
        exact .node rule (List.mem_append_left _ present) parameters ih
    | @nominal context value fact present values matched parameters bound =>
        cases value with
        | node symbol children =>
            obtain ⟨scheme, prepared, actual, equal⟩ :=
              (Fact.prepare_iff fact (.node symbol children) (fact.type.substitute parameters)).2
                ⟨values, matched, parameters, bound, rfl⟩
            rw [equal]
            refine .node (factRule scheme (valueArity symbol))
              (List.mem_append_right _ (List.mem_filterMap.2 ⟨fact, present, by simp [prepared]⟩))
              actual ?_
            intro i fieldType impossible
            cases impossible

def check [DecidableEq P] [DecidableEq PatternVariable] [DecidableEq Q] [DecidableEq C] [DecidableEq S]
    (declarations : Declarations Context PatternVariable P Q C S typeArity valueArity)
    (context : Context) (value : Tree S valueArity) (type : Closed Q C typeArity) : Bool :=
  ConstructorTyping.check (asSystem declarations) context value type

theorem check_iff [DecidableEq P] [DecidableEq PatternVariable] [DecidableEq Q] [DecidableEq C] [DecidableEq S]
    (declarations : Declarations Context PatternVariable P Q C S typeArity valueArity)
    (context : Context) (value : Tree S valueArity) (type : Closed Q C typeArity) :
    check declarations context value type = true ↔ HasType declarations context value type := by
  rw [check, ConstructorTyping.check_iff_hasType, asSystem_iff]

end Mettapedia.Logic.ConstraintTypes.DeclarationTyping
