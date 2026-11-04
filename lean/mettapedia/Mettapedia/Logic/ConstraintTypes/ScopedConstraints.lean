import Mettapedia.Logic.ConstraintTypes.SymbolicTypes

/-!
# Existential scopes for symbolic type constraints

Private type parameters are represented by disjoint sum coordinates. Conjoining
problems shares the outer coordinates and freshens their private coordinates.
Binding a constructor's parameters is existential hiding. These operations have
exact semantics under ground assignments and provide the scope algebra used by
the constructor-typing compiler.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ConstraintTypes.ScopedConstraints

open SymbolicTypes

variable {X Y P Q C : Type} {arity : C → Nat}

def renameEquations (rename : X → Y) (equations : Equations X Q C arity) : Equations Y Q C arity :=
  equations.map fun pair => (pair.1.rename rename, pair.2.rename rename)

theorem ground_rename (rename : X → Y) (assignment : Y → Closed Q C arity)
    (equations : Equations X Q C arity) :
    GroundSolves assignment (renameEquations rename equations) ↔
      GroundSolves (assignment ∘ rename) equations := by
  constructor
  · intro h pair hp
    have := h _ (List.mem_map.2 ⟨pair, hp, rfl⟩)
    simpa only [TypeExpr.substitute_rename] using this
  · intro h pair hp
    obtain ⟨original, originalMember, equal⟩ := List.mem_map.1 hp
    subst pair
    simpa only [TypeExpr.substitute_rename] using h original originalMember

theorem ground_append (assignment : X → Closed Q C arity)
    (left right : Equations X Q C arity) :
    GroundSolves assignment (left ++ right) ↔ GroundSolves assignment left ∧ GroundSolves assignment right := by
  constructor
  · intro h
    exact ⟨fun pair hp => h pair (List.mem_append_left _ hp),
      fun pair hp => h pair (List.mem_append_right _ hp)⟩
  · rintro ⟨hl, hr⟩ pair hp
    exact (List.mem_append.1 hp).elim (hl pair) (hr pair)

structure Problem (Public Q C : Type) (arity : C → Nat) where
  locals : Type
  localEq : DecidableEq locals
  equations : Equations (Public ⊕ locals) Q C arity

def Satisfies (problem : Problem X Q C arity) (outer : X → Closed Q C arity) : Prop :=
  ∃ privateValues : problem.locals → Closed Q C arity,
    GroundSolves (Sum.elim outer privateValues) problem.equations

def truth : Problem X Q C arity where
  locals := Empty
  localEq := inferInstance
  equations := []

theorem satisfies_truth (outer : X → Closed Q C arity) : Satisfies truth outer :=
  ⟨Empty.elim, fun _ impossible => by cases impossible⟩

abbrev equation (left right : Expr X Q C arity) : Problem X Q C arity where
  locals := Empty
  localEq := inferInstance
  equations := [(left.rename Sum.inl, right.rename Sum.inl)]

theorem satisfies_equation (left right : Expr X Q C arity) (outer : X → Closed Q C arity) :
    Satisfies (equation left right) outer ↔ left.substitute outer = right.substitute outer := by
  constructor
  · rintro ⟨privateValues, solved⟩
    have := solved _ List.mem_cons_self
    simpa only [TypeExpr.substitute_rename, Function.comp_def, Sum.elim_inl] using this
  · intro same
    refine ⟨Empty.elim, ?_⟩
    intro pair hp
    have onlyPair : pair = (left.rename Sum.inl, right.rename Sum.inl) := List.mem_singleton.1 hp
    subst pair
    simpa only [TypeExpr.substitute_rename, Function.comp_def, Sum.elim_inl] using same

def leftCoordinate {L R : Type} : X ⊕ L → X ⊕ (L ⊕ R)
  | .inl x => .inl x
  | .inr l => .inr (.inl l)

def rightCoordinate {L R : Type} : X ⊕ R → X ⊕ (L ⊕ R)
  | .inl x => .inl x
  | .inr r => .inr (.inr r)

abbrev conjunction (left right : Problem X Q C arity) : Problem X Q C arity :=
  letI := left.localEq
  letI := right.localEq
  { locals := left.locals ⊕ right.locals
    localEq := inferInstance
    equations := renameEquations leftCoordinate left.equations ++
      renameEquations rightCoordinate right.equations }

private theorem left_environment {L R : Type} (outer : X → Closed Q C arity)
    (privateValues : L ⊕ R → Closed Q C arity) :
    (Sum.elim outer privateValues) ∘ leftCoordinate =
      Sum.elim outer (fun l => privateValues (.inl l)) := by
  funext coordinate
  cases coordinate <;> rfl

private theorem right_environment {L R : Type} (outer : X → Closed Q C arity)
    (privateValues : L ⊕ R → Closed Q C arity) :
    (Sum.elim outer privateValues) ∘ rightCoordinate =
      Sum.elim outer (fun r => privateValues (.inr r)) := by
  funext coordinate
  cases coordinate <;> rfl

theorem satisfies_conjunction (left right : Problem X Q C arity) (outer : X → Closed Q C arity) :
    Satisfies (conjunction left right) outer ↔ Satisfies left outer ∧ Satisfies right outer := by
  constructor
  · rintro ⟨privateValues, solved⟩
    obtain ⟨hl, hr⟩ := (ground_append _ _ _).1 solved
    rw [ground_rename, left_environment] at hl
    rw [ground_rename, right_environment] at hr
    exact ⟨⟨fun l => privateValues (.inl l), hl⟩, ⟨fun r => privateValues (.inr r), hr⟩⟩
  · rintro ⟨⟨leftValues, hl⟩, ⟨rightValues, hr⟩⟩
    refine ⟨Sum.elim leftValues rightValues, (ground_append _ _ _).2 ⟨?_, ?_⟩⟩
    · rw [ground_rename, left_environment]
      exact hl
    · rw [ground_rename, right_environment]
      exact hr

def bindCoordinate {L : Type} : (X ⊕ P) ⊕ L → X ⊕ (P ⊕ L)
  | .inl (.inl x) => .inl x
  | .inl (.inr p) => .inr (.inl p)
  | .inr l => .inr (.inr l)

abbrev bind [DecidableEq P] (body : Problem (X ⊕ P) Q C arity) : Problem X Q C arity :=
  letI := body.localEq
  { locals := P ⊕ body.locals
    localEq := inferInstance
    equations := renameEquations bindCoordinate body.equations }

private theorem bind_environment {L : Type} (outer : X → Closed Q C arity)
    (privateValues : P ⊕ L → Closed Q C arity) :
    (Sum.elim outer privateValues) ∘ bindCoordinate =
      Sum.elim (Sum.elim outer (fun p => privateValues (.inl p)))
        (fun l => privateValues (.inr l)) := by
  funext coordinate
  cases coordinate with
  | inl coordinate => cases coordinate <;> rfl
  | inr _ => rfl

theorem satisfies_bind [DecidableEq P] (body : Problem (X ⊕ P) Q C arity)
    (outer : X → Closed Q C arity) :
    Satisfies (bind body) outer ↔
      ∃ parameters : P → Closed Q C arity, Satisfies body (Sum.elim outer parameters) := by
  constructor
  · rintro ⟨privateValues, solved⟩
    rw [ground_rename, bind_environment] at solved
    exact ⟨fun p => privateValues (.inl p), fun l => privateValues (.inr l), solved⟩
  · rintro ⟨parameters, privateValues, solved⟩
    refine ⟨Sum.elim parameters privateValues, ?_⟩
    rw [ground_rename, bind_environment]
    exact solved

abbrev close [DecidableEq X] (body : Problem X Q C arity) : Problem Empty Q C arity :=
  let _ := body.localEq
  { locals := X ⊕ body.locals
    localEq := inferInstance
    equations := renameEquations Sum.inr body.equations }

theorem satisfies_close [DecidableEq X] (body : Problem X Q C arity) :
    Satisfies (close body) Empty.elim ↔ ∃ outer, Satisfies body outer := by
  constructor
  · rintro ⟨values, solved⟩
    rw [ground_rename] at solved
    refine ⟨fun x => values (.inl x), fun l => values (.inr l), ?_⟩
    have same : (Sum.elim Empty.elim values) ∘ Sum.inr =
        Sum.elim (fun x => values (.inl x)) (fun l => values (.inr l)) := by
      funext coordinate; cases coordinate <;> rfl
    simpa only [same] using solved
  · rintro ⟨outer, inner, solved⟩
    refine ⟨Sum.elim outer inner, ?_⟩
    rw [ground_rename]
    exact solved

def alternativesSatisfy (alternatives : List (Problem X Q C arity)) (outer : X → Closed Q C arity) : Prop :=
  ∃ problem ∈ alternatives, Satisfies problem outer

def combinations : List (List (Problem X Q C arity)) → List (Problem X Q C arity)
  | [] => [truth]
  | first :: rest => first.flatMap fun left => (combinations rest).map (conjunction left)

theorem satisfies_combinations (choices : List (List (Problem X Q C arity)))
    (outer : X → Closed Q C arity) :
    alternativesSatisfy (combinations choices) outer ↔
      ∀ choice ∈ choices, alternativesSatisfy choice outer := by
  induction choices with
  | nil => simp [combinations, alternativesSatisfy, satisfies_truth]
  | cons first rest ih =>
      constructor
      · rintro ⟨problem, member, solved⟩ choice hc
        obtain ⟨left, hl, mapped⟩ := List.mem_flatMap.1 member
        obtain ⟨right, hr, equal⟩ := List.mem_map.1 mapped
        subst problem
        obtain ⟨sl, sr⟩ := (satisfies_conjunction _ _ _).1 solved
        rcases List.mem_cons.1 hc with rfl | hc
        · exact ⟨left, hl, sl⟩
        · exact ih.1 ⟨right, hr, sr⟩ choice hc
      · intro all
        obtain ⟨left, hl, sl⟩ := all first List.mem_cons_self
        obtain ⟨right, hr, sr⟩ := ih.2 (fun choice hc => all choice (List.mem_cons_of_mem _ hc))
        exact ⟨_, List.mem_flatMap.2 ⟨left, hl, List.mem_map.2 ⟨right, hr, rfl⟩⟩,
          (satisfies_conjunction _ _ _).2 ⟨sl, sr⟩⟩

def solve [DecidableEq X] [DecidableEq Q] [DecidableEq C]
    (problem : Problem X Q C arity) : Option (Assignment (X ⊕ problem.locals) Q C arity) :=
  letI := problem.localEq
  SymbolicTypes.solve problem.equations

theorem solve_sound [DecidableEq X] [DecidableEq Q] [DecidableEq C]
    (problem : Problem X Q C arity) (assignment : Assignment (X ⊕ problem.locals) Q C arity)
    (accepted : solve problem = some assignment) : Solves assignment problem.equations := by
  let _ := problem.localEq
  exact SymbolicTypes.solve_sound _ _ accepted

theorem solve_iff_satisfiable [DecidableEq X] [DecidableEq Q] [DecidableEq C]
    (seed : Closed Q C arity) (problem : Problem X Q C arity) :
    (∃ assignment, solve problem = some assignment) ↔ ∃ outer, Satisfies problem outer := by
  let _ := problem.localEq
  rw [solve, SymbolicTypes.solve_iff_ground_solution seed]
  constructor
  · rintro ⟨values, solved⟩
    refine ⟨fun x => values (.inl x), fun l => values (.inr l), ?_⟩
    have same : Sum.elim (fun x => values (.inl x)) (fun l => values (.inr l)) = values := by
      funext coordinate; cases coordinate <;> rfl
    simpa only [same] using solved
  · rintro ⟨outer, privateValues, solved⟩
    exact ⟨Sum.elim outer privateValues, solved⟩

def Refines (problem : Problem X Q C arity) (assignment : Assignment (X ⊕ problem.locals) Q C arity)
    (outer : X → Closed Q C arity) : Prop :=
  ∃ closing : X ⊕ problem.locals → Closed Q C arity,
    ∀ x, outer x = (assignment (.inl x)).substitute closing

/-- An MGU, with its private parameters existentially hidden, describes exactly
all external type assignments accepted by the original problem. -/
theorem principal_projection_exact [DecidableEq X] [DecidableEq Q] [DecidableEq C]
    (problem : Problem X Q C arity) (assignment : Assignment (X ⊕ problem.locals) Q C arity)
    (accepted : solve problem = some assignment) (outer : X → Closed Q C arity) :
    Satisfies problem outer ↔ Refines problem assignment outer := by
  let _ := problem.localEq
  constructor
  · rintro ⟨privateValues, solved⟩
    let values := Sum.elim outer privateValues
    obtain ⟨later, factors⟩ := SymbolicTypes.solve_principal problem.equations assignment
      (fun coordinate => embedClosed (values coordinate)) accepted
      (ground_solution_is_symbolic values problem.equations solved)
    refine ⟨fun coordinate => (later coordinate).substitute values, fun x => ?_⟩
    have closed := congrArg (TypeExpr.substitute values) (factors (.inl x))
    simpa only [close_embed, TypeExpr.substitute_comp, values, Sum.elim_inl] using closed
  · rintro ⟨closing, sameOuter⟩
    have solved := close_solution assignment closing problem.equations (solve_sound problem assignment accepted)
    refine ⟨fun l => (assignment (.inr l)).substitute closing, ?_⟩
    have same : Sum.elim outer (fun l => (assignment (.inr l)).substitute closing) =
        (fun coordinate => (assignment coordinate).substitute closing) := by
      funext coordinate
      cases coordinate with
      | inl x => exact sameOuter x
      | inr _ => rfl
    simpa only [same] using solved

/-- The same projection theorem with an arbitrary residual condition. The
condition is transformed by the principal substitution, not forgotten. -/
theorem principal_residual_projection_exact [DecidableEq X] [DecidableEq Q] [DecidableEq C]
    (problem : Problem X Q C arity) (assignment : Assignment (X ⊕ problem.locals) Q C arity)
    (accepted : solve problem = some assignment) (outer : X → Closed Q C arity)
    (residual : (X ⊕ problem.locals → Closed Q C arity) → Prop) :
    (∃ inner, GroundSolves (Sum.elim outer inner) problem.equations ∧ residual (Sum.elim outer inner)) ↔
      ∃ closing, (∀ x, outer x = (assignment (.inl x)).substitute closing) ∧
        residual (fun coordinate => (assignment coordinate).substitute closing) := by
  let _ := problem.localEq
  constructor
  · rintro ⟨inner, solved, pending⟩
    obtain ⟨closing, same⟩ := ground_solution_factors problem.equations assignment accepted
      (Sum.elim outer inner) solved
    exact ⟨closing, fun x => same (.inl x), by simpa only [← funext same] using pending⟩
  · rintro ⟨closing, sameOuter, pending⟩
    have same : Sum.elim outer (fun l => (assignment (.inr l)).substitute closing) =
        (fun coordinate => (assignment coordinate).substitute closing) := by
      funext coordinate
      cases coordinate with
      | inl x => exact sameOuter x
      | inr _ => rfl
    refine ⟨fun l => (assignment (.inr l)).substitute closing, ?_, ?_⟩
    · simpa only [same] using close_solution assignment closing problem.equations
        (solve_sound problem assignment accepted)
    · simpa only [same] using pending

def accept [DecidableEq X] [DecidableEq Q] [DecidableEq C]
    (alternatives : List (Problem X Q C arity)) : Bool :=
  alternatives.any fun problem => (solve problem).isSome

theorem accept_iff [DecidableEq X] [DecidableEq Q] [DecidableEq C]
    (seed : Closed Q C arity) (alternatives : List (Problem X Q C arity)) :
    accept alternatives = true ↔ ∃ outer, alternativesSatisfy alternatives outer := by
  simp only [accept, List.any_eq_true]
  constructor
  · rintro ⟨problem, member, success⟩
    have hasResult : ∃ assignment, solve problem = some assignment := Option.isSome_iff_exists.1 success
    obtain ⟨outer, solved⟩ := (solve_iff_satisfiable seed problem).1 hasResult
    exact ⟨outer, problem, member, solved⟩
  · rintro ⟨outer, problem, member, solved⟩
    obtain ⟨assignment, success⟩ := (solve_iff_satisfiable seed problem).2 ⟨outer, solved⟩
    exact ⟨problem, member, Option.isSome_iff_exists.2 ⟨assignment, success⟩⟩

theorem accept_closed_iff [DecidableEq Q] [DecidableEq C]
    (seed : Closed Q C arity) (alternatives : List (Problem Empty Q C arity)) :
    accept alternatives = true ↔ alternativesSatisfy alternatives Empty.elim := by
  rw [accept_iff seed]
  constructor
  · rintro ⟨outer, solved⟩
    have same : outer = Empty.elim := by funext x; cases x
    simpa only [same] using solved
  · exact fun solved => ⟨Empty.elim, solved⟩

end Mettapedia.Logic.ConstraintTypes.ScopedConstraints
