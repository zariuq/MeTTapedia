import Mettapedia.Logic.ConstraintTypes.ScopedConstraints

/-!
# Scoped equations with residual predicate requests

The predicate symbols are data, interpreted only when their arguments are ready.
Unification normalizes the equations and all request types together. Fresh-scope
composition and principal-solution projection preserve the complete meaning,
including requests that the unifier cannot decide.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ConstraintTypes.ResidualConstraints

open SymbolicTypes

variable {X P Q C R : Type} {arity : C → Nat}

abbrev Requests (Variable Q C R : Type) (arity : C → Nat) := List (R × Expr Variable Q C arity)

def renameRequests {Y : Type} (rename : X → Y) (requests : Requests X Q C R arity) : Requests Y Q C R arity :=
  requests.map fun request => (request.1, request.2.rename rename)

def Holds (model : R → Closed Q C arity → Prop) (values : X → Closed Q C arity)
    (requests : Requests X Q C R arity) : Prop :=
  ∀ request ∈ requests, model request.1 (request.2.substitute values)

theorem holds_rename {Y : Type} (model : R → Closed Q C arity → Prop)
    (values : Y → Closed Q C arity) (rename : X → Y) (requests : Requests X Q C R arity) :
    Holds model values (renameRequests rename requests) ↔ Holds model (values ∘ rename) requests := by
  constructor
  · intro h request present
    have := h _ (List.mem_map.2 ⟨request, present, rfl⟩)
    simpa only [TypeExpr.substitute_rename] using this
  · intro h request present
    obtain ⟨original, member, equal⟩ := List.mem_map.1 present
    subst request
    simpa only [TypeExpr.substitute_rename] using h original member

theorem holds_append (model : R → Closed Q C arity → Prop) (values : X → Closed Q C arity)
    (left right : Requests X Q C R arity) :
    Holds model values (left ++ right) ↔ Holds model values left ∧ Holds model values right := by
  constructor
  · intro h
    exact ⟨fun request present => h request (List.mem_append_left _ present),
      fun request present => h request (List.mem_append_right _ present)⟩
  · rintro ⟨hl, hr⟩ request present
    exact (List.mem_append.1 present).elim (hl request) (hr request)

structure Problem (X Q C R : Type) (arity : C → Nat) where
  equations : ScopedConstraints.Problem X Q C arity
  requests : Requests (X ⊕ equations.locals) Q C R arity

def Models (problem : Problem X Q C R arity) (model : R → Closed Q C arity → Prop)
    (outer : X → Closed Q C arity) : Prop :=
  ∃ inner, GroundSolves (Sum.elim outer inner) problem.equations.equations ∧
    Holds model (Sum.elim outer inner) problem.requests

abbrev pure (equations : ScopedConstraints.Problem X Q C arity) : Problem X Q C R arity where
  equations := equations
  requests := []

theorem models_pure (equations : ScopedConstraints.Problem X Q C arity)
    (model : R → Closed Q C arity → Prop) (outer : X → Closed Q C arity) :
    Models (pure equations) model outer ↔ ScopedConstraints.Satisfies equations outer := by
  simp [Models, Holds, ScopedConstraints.Satisfies]

abbrev atom (symbol : R) (type : Expr X Q C arity) : Problem X Q C R arity where
  equations := ScopedConstraints.truth
  requests := [(symbol, type.rename Sum.inl)]

/-- A finite conjunction of requests, with no additional type equations. -/
abbrev requestsOnly (requests : Requests X Q C R arity) : Problem X Q C R arity where
  equations := ScopedConstraints.truth
  requests := renameRequests Sum.inl requests

theorem models_requestsOnly (requests : Requests X Q C R arity)
    (model : R → Closed Q C arity → Prop) (outer : X → Closed Q C arity) :
    Models (requestsOnly requests) model outer ↔ Holds model outer requests := by
  constructor
  · rintro ⟨inner, _, pending⟩
    rw [holds_rename] at pending
    simpa only [Function.comp_def, Sum.elim_inl] using pending
  · intro pending
    refine ⟨Empty.elim, (fun _ impossible => by cases impossible), ?_⟩
    exact (holds_rename model (Sum.elim outer (Empty.elim : Empty → Closed Q C arity))
      (Sum.inl : X → X ⊕ Empty) requests).2 pending

theorem models_atom (symbol : R) (type : Expr X Q C arity)
    (model : R → Closed Q C arity → Prop) (outer : X → Closed Q C arity) :
    Models (atom symbol type) model outer ↔ model symbol (type.substitute outer) := by
  constructor
  · rintro ⟨inner, _, pending⟩
    have := pending _ List.mem_cons_self
    simpa only [TypeExpr.substitute_rename, Function.comp_def, Sum.elim_inl] using this
  · intro admitted
    refine ⟨Empty.elim, (fun _ impossible => by cases impossible), ?_⟩
    intro request present
    have equal := List.mem_singleton.1 present
    subst request
    rw [TypeExpr.substitute_rename]
    exact admitted

abbrev conjunction (left right : Problem X Q C R arity) : Problem X Q C R arity where
  equations := ScopedConstraints.conjunction left.equations right.equations
  requests := renameRequests ScopedConstraints.leftCoordinate left.requests ++
    renameRequests ScopedConstraints.rightCoordinate right.requests

private theorem left_environment {L M : Type} (outer : X → Closed Q C arity)
    (inner : L ⊕ M → Closed Q C arity) :
    (Sum.elim outer inner) ∘ ScopedConstraints.leftCoordinate =
      Sum.elim outer (fun l => inner (.inl l)) := by
  funext coordinate; cases coordinate <;> rfl

private theorem right_environment {L M : Type} (outer : X → Closed Q C arity)
    (inner : L ⊕ M → Closed Q C arity) :
    (Sum.elim outer inner) ∘ ScopedConstraints.rightCoordinate =
      Sum.elim outer (fun m => inner (.inr m)) := by
  funext coordinate; cases coordinate <;> rfl

theorem models_conjunction (left right : Problem X Q C R arity)
    (model : R → Closed Q C arity → Prop) (outer : X → Closed Q C arity) :
    Models (conjunction left right) model outer ↔ Models left model outer ∧ Models right model outer := by
  constructor
  · rintro ⟨inner, solved, pending⟩
    obtain ⟨sl, sr⟩ := (ScopedConstraints.ground_append _ _ _).1 solved
    obtain ⟨pl, pr⟩ := (holds_append _ _ _ _).1 pending
    rw [ScopedConstraints.ground_rename, left_environment] at sl
    rw [ScopedConstraints.ground_rename, right_environment] at sr
    rw [holds_rename, left_environment] at pl
    rw [holds_rename, right_environment] at pr
    exact ⟨⟨_, sl, pl⟩, ⟨_, sr, pr⟩⟩
  · rintro ⟨⟨leftValues, sl, pl⟩, ⟨rightValues, sr, pr⟩⟩
    refine ⟨Sum.elim leftValues rightValues, (ScopedConstraints.ground_append _ _ _).2 ⟨?_, ?_⟩,
      (holds_append _ _ _ _).2 ⟨?_, ?_⟩⟩
    · rw [ScopedConstraints.ground_rename, left_environment]; exact sl
    · rw [ScopedConstraints.ground_rename, right_environment]; exact sr
    · rw [holds_rename, left_environment]; exact pl
    · rw [holds_rename, right_environment]; exact pr

abbrev bind [DecidableEq P] (body : Problem (X ⊕ P) Q C R arity) : Problem X Q C R arity where
  equations := ScopedConstraints.bind body.equations
  requests := renameRequests ScopedConstraints.bindCoordinate body.requests

private theorem bind_environment {L : Type} (outer : X → Closed Q C arity)
    (inner : P ⊕ L → Closed Q C arity) :
    (Sum.elim outer inner) ∘ ScopedConstraints.bindCoordinate =
      Sum.elim (Sum.elim outer (fun p => inner (.inl p))) (fun l => inner (.inr l)) := by
  funext coordinate
  cases coordinate with
  | inl coordinate => cases coordinate <;> rfl
  | inr _ => rfl

theorem models_bind [DecidableEq P] (body : Problem (X ⊕ P) Q C R arity)
    (model : R → Closed Q C arity → Prop) (outer : X → Closed Q C arity) :
    Models (bind body) model outer ↔ ∃ parameters, Models body model (Sum.elim outer parameters) := by
  constructor
  · rintro ⟨inner, solved, pending⟩
    rw [ScopedConstraints.ground_rename, bind_environment] at solved
    rw [holds_rename, bind_environment] at pending
    exact ⟨_, _, solved, pending⟩
  · rintro ⟨parameters, inner, solved, pending⟩
    refine ⟨Sum.elim parameters inner, ?_, ?_⟩
    · rw [ScopedConstraints.ground_rename, bind_environment]; exact solved
    · rw [holds_rename, bind_environment]; exact pending



abbrev close [DecidableEq X] (body : Problem X Q C R arity) : Problem Empty Q C R arity where
  equations := ScopedConstraints.close body.equations
  requests := renameRequests Sum.inr body.requests

theorem models_close [DecidableEq X] (body : Problem X Q C R arity)
    (model : R → Closed Q C arity → Prop) :
    Models (close body) model Empty.elim ↔ ∃ outer, Models body model outer := by
  constructor
  · rintro ⟨values, solved, pending⟩
    rw [ScopedConstraints.ground_rename] at solved
    rw [holds_rename] at pending
    have same : (Sum.elim Empty.elim values) ∘ Sum.inr =
        Sum.elim (fun x => values (.inl x)) (fun l => values (.inr l)) := by
      funext coordinate; cases coordinate <;> rfl
    refine ⟨fun x => values (.inl x), fun l => values (.inr l), ?_, ?_⟩
    · simpa only [same] using solved
    · simpa only [same] using pending
  · rintro ⟨outer, inner, solved, pending⟩
    refine ⟨Sum.elim outer inner, ?_, ?_⟩
    · rw [ScopedConstraints.ground_rename]; exact solved
    · rw [holds_rename]; exact pending

def alternativesModel (alternatives : List (Problem X Q C R arity))
    (model : R → Closed Q C arity → Prop) (outer : X → Closed Q C arity) : Prop :=
  ∃ problem ∈ alternatives, Models problem model outer

def combinations : List (List (Problem X Q C R arity)) → List (Problem X Q C R arity)
  | [] => [pure ScopedConstraints.truth]
  | first :: rest => first.flatMap fun left => (combinations rest).map (conjunction left)

theorem models_combinations (choices : List (List (Problem X Q C R arity)))
    (model : R → Closed Q C arity → Prop) (outer : X → Closed Q C arity) :
    alternativesModel (combinations choices) model outer ↔
      ∀ choice ∈ choices, alternativesModel choice model outer := by
  induction choices with
  | nil => simp [combinations, alternativesModel, models_pure, ScopedConstraints.satisfies_truth]
  | cons first rest ih =>
      constructor
      · rintro ⟨problem, present, solved⟩ choice hc
        obtain ⟨left, hl, mapped⟩ := List.mem_flatMap.1 present
        obtain ⟨right, hr, equal⟩ := List.mem_map.1 mapped
        subst problem
        obtain ⟨sl, sr⟩ := (models_conjunction _ _ _ _).1 solved
        rcases List.mem_cons.1 hc with rfl | hc
        · exact ⟨left, hl, sl⟩
        · exact ih.1 ⟨right, hr, sr⟩ choice hc
      · intro all
        obtain ⟨left, hl, sl⟩ := all first List.mem_cons_self
        obtain ⟨right, hr, sr⟩ := ih.2 (fun choice hc => all choice (List.mem_cons_of_mem _ hc))
        exact ⟨_, List.mem_flatMap.2 ⟨left, hl, List.mem_map.2 ⟨right, hr, rfl⟩⟩,
          (models_conjunction _ _ _ _).2 ⟨sl, sr⟩⟩

/-- The normalized request list is executable data. It may be awakened later
with a new predicate interpretation, without retaining a declaration world. -/
def normalizeRequests (problem : Problem X Q C R arity)
    (principal : Assignment (X ⊕ problem.equations.locals) Q C arity) :
    Requests (X ⊕ problem.equations.locals) Q C R arity :=
  problem.requests.map fun request => (request.1, request.2.substitute principal)

theorem principal_model_exact [DecidableEq X] [DecidableEq Q] [DecidableEq C]
    (problem : Problem X Q C R arity)
    (principal : Assignment (X ⊕ problem.equations.locals) Q C arity)
    (accepted : ScopedConstraints.solve problem.equations = some principal)
    (model : R → Closed Q C arity → Prop) (outer : X → Closed Q C arity) :
    Models problem model outer ↔ ∃ closing,
      (∀ x, outer x = (principal (.inl x)).substitute closing) ∧
        Holds model closing (normalizeRequests problem principal) := by
  unfold Models
  rw [ScopedConstraints.principal_residual_projection_exact problem.equations principal accepted outer
    (fun values => Holds model values problem.requests)]
  apply exists_congr
  intro closing
  apply and_congr_right
  intro _
  constructor
  · intro pending request present
    obtain ⟨original, member, equal⟩ := List.mem_map.1 present
    subst request
    simpa only [TypeExpr.substitute_comp] using pending original member
  · intro pending request present
    have := pending _ (List.mem_map.2 ⟨request, present, rfl⟩)
    simpa only [TypeExpr.substitute_comp] using this

end Mettapedia.Logic.ConstraintTypes.ResidualConstraints
