import Mettapedia.Logic.ConstraintTypes.ConstructorTyping

/-!
# Field-determined membership as a compiled instance of constructor typing

Matching a ground result type determines every field type when all field
parameters occur in the result. This condition is checked syntactically. The
resulting grammar recognizes exactly the same membership judgment as the
general symbolic checker. Rules with hidden existential fields retain the
general checker; no unsupported field invariant is assumed. The grammar
state space may be infinite: field determination does not assert regularity
or a finite-automaton complexity bound.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ConstraintTypes.DeterminedMembership

open SymbolicTypes ConstructorTyping

variable {P Q C S Context : Type} {typeArity : C → Nat} {valueArity : S → Nat} {n : Nat}

def selectParameters [DecidableEq P] [DecidableEq Q] [DecidableEq C]
    (seed : Closed Q C typeArity) (rule : Rule P Q C typeArity n) (target : Closed Q C typeArity) :
    Option (P → Closed Q C typeArity) :=
  (SymbolicTypes.solve [(rule.result, embedClosed target)]).map fun solution p =>
    (solution p).substitute (fun _ => seed)

theorem selected_result [DecidableEq P] [DecidableEq Q] [DecidableEq C]
    (seed : Closed Q C typeArity) (rule : Rule P Q C typeArity n) (target : Closed Q C typeArity)
    (parameters : P → Closed Q C typeArity) (selected : selectParameters seed rule target = some parameters) :
    rule.result.substitute parameters = target := by
  unfold selectParameters at selected
  cases raw : SymbolicTypes.solve [(rule.result, embedClosed target)] with
  | none => simp [raw] at selected
  | some solution =>
      simp only [raw, Option.map_some, Option.some.injEq] at selected
      subst parameters
      have solved := close_solution solution (fun _ => seed) _ (solve_sound _ _ raw)
      simpa only [close_embed] using solved _ List.mem_cons_self

theorem selection_complete [DecidableEq P] [DecidableEq Q] [DecidableEq C]
    (seed : Closed Q C typeArity) (rule : Rule P Q C typeArity n) (target : Closed Q C typeArity)
    (parameters : P → Closed Q C typeArity) (same : rule.result.substitute parameters = target) :
    ∃ chosen, selectParameters seed rule target = some chosen := by
  have solved : GroundSolves parameters [(rule.result, embedClosed target)] := by
    intro pair present
    have equal := List.mem_singleton.1 present
    subst pair
    simpa only [close_embed] using same
  obtain ⟨solution, accepted⟩ := (solve_iff_ground_solution seed _).2 ⟨parameters, solved⟩
  exact ⟨(fun p => (solution p).substitute (fun _ => seed)), by simp [selectParameters, accepted]⟩

def coversFields [DecidableEq P] (rule : Rule P Q C typeArity n) : Bool :=
  (List.finRange n).all fun i => match rule.field i with
    | none => true
    | some fieldType => fieldType.variables.all fun p => decide (p ∈ rule.result.variables)

theorem covered_fields_determined [DecidableEq P] (rule : Rule P Q C typeArity n)
    (covered : coversFields rule = true) (left right : P → Closed Q C typeArity)
    (same : rule.result.substitute left = rule.result.substitute right)
    (i : Fin n) (fieldType : Expr P Q C typeArity) (required : rule.field i = some fieldType) :
    fieldType.substitute left = fieldType.substitute right := by
  have fieldCovered := (List.all_eq_true.1 covered) i (List.mem_finRange i)
  rw [required] at fieldCovered
  apply TypeExpr.substitute_congr
  intro p member
  exact TypeExpr.parameters_determined left right rule.result same p
    (of_decide_eq_true ((List.all_eq_true.1 fieldCovered) p member))

def asSystem
    (childContext : Context → (symbol : S) → Fin (valueArity symbol) → Context)
    (table : Context → (symbol : S) → List (Rule P Q C typeArity (valueArity symbol))) :
    System Context P Q C S typeArity valueArity where
  childContext := childContext
  rules context symbol _ := table context symbol

def grammar [DecidableEq P] [DecidableEq Q] [DecidableEq C]
    (seed : Closed Q C typeArity)
    (childContext : Context → (symbol : S) → Fin (valueArity symbol) → Context)
    (table : Context → (symbol : S) → List (Rule P Q C typeArity (valueArity symbol))) :
    Grammar (Context × Option (Closed Q C typeArity)) S valueArity where
  productions state symbol := match state.2 with
    | none => [fun i => (childContext state.1 symbol i, none)]
    | some type => (table state.1 symbol).filterMap fun rule =>
        (selectParameters seed rule type).map fun parameters =>
          fun i => (childContext state.1 symbol i, (rule.field i).map (TypeExpr.substitute parameters))

theorem ignored_field_accepts [DecidableEq P] [DecidableEq Q] [DecidableEq C]
    (seed : Closed Q C typeArity)
    (childContext : Context → (symbol : S) → Fin (valueArity symbol) → Context)
    (table : Context → (symbol : S) → List (Rule P Q C typeArity (valueArity symbol)))
    (value : Tree S valueArity) (context : Context) :
    (grammar seed childContext table).Derives (context, none) value := by
  induction value generalizing context with
  | node symbol children ih =>
      exact .node (fun i => (childContext context symbol i, none)) (by simp [grammar])
        (fun i => ih i _)

theorem grammar_iff_typing [DecidableEq P] [DecidableEq Q] [DecidableEq C]
    (seed : Closed Q C typeArity)
    (childContext : Context → (symbol : S) → Fin (valueArity symbol) → Context)
    (table : Context → (symbol : S) → List (Rule P Q C typeArity (valueArity symbol)))
    (determined : ∀ context symbol rule, rule ∈ table context symbol → coversFields rule = true)
    (value : Tree S valueArity) (context : Context) (type : Closed Q C typeArity) :
    (grammar seed childContext table).Derives (context, some type) value ↔
      HasType (asSystem childContext table) context value type := by
  induction value generalizing context type with
  | node symbol children ih =>
      constructor
      · intro typed
        obtain ⟨states, present, fields⟩ := (Grammar.derives_node_iff _ _ _ _).1 typed
        obtain ⟨rule, ruleMember, selected⟩ := List.mem_filterMap.1 present
        cases choice : selectParameters seed rule type with
        | none => simp [choice] at selected
        | some parameters =>
            simp only [choice, Option.map_some, Option.some.injEq] at selected
            subst states
            rw [← selected_result seed rule type parameters choice]
            refine .node rule ruleMember parameters ?_
            intro i fieldType required
            have field := fields i
            simp only [required, Option.map_some] at field
            exact (ih i _ _).1 field
      · intro typed
        obtain ⟨rule, present, parameters, same, fields⟩ := (hasType_node_iff _ _ _ _ _).1 typed
        obtain ⟨chosen, choice⟩ := selection_complete seed rule type parameters same.symm
        refine .node (fun i => (childContext context symbol i,
          (rule.field i).map (TypeExpr.substitute chosen))) ?_ ?_
        · exact List.mem_filterMap.2 ⟨rule, present, by simp [choice]⟩
        · intro i
          cases required : rule.field i with
          | none => exact ignored_field_accepts seed childContext table (children i) _
          | some fieldType =>
              have fieldTypeSame := covered_fields_determined rule (determined context symbol rule present)
                chosen parameters ((selected_result seed rule type chosen choice).trans same) i fieldType required
              simp only [Option.map_some]
              apply (ih i _ _).2
              rw [fieldTypeSame]
              exact fields i fieldType required

theorem compiled_membership_correct [DecidableEq P] [DecidableEq Q] [DecidableEq C]
    (seed : Closed Q C typeArity)
    (childContext : Context → (symbol : S) → Fin (valueArity symbol) → Context)
    (table : Context → (symbol : S) → List (Rule P Q C typeArity (valueArity symbol)))
    (determined : ∀ context symbol rule, rule ∈ table context symbol → coversFields rule = true)
    (value : Tree S valueArity) (context : Context) (type : Closed Q C typeArity) :
    (grammar seed childContext table).accepts value (context, some type) = true ↔
      HasType (asSystem childContext table) context value type := by
  rw [Grammar.accepts_iff_derives, grammar_iff_typing seed childContext table determined]

end Mettapedia.Logic.ConstraintTypes.DeterminedMembership
