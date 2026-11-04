import Mettapedia.Logic.ConstraintTypes.Contracts
import Mettapedia.Logic.LP.TotalUnification
import Mettapedia.Logic.LP.IndependentOutputUnification

/-!
# Symbolic constructor types and principal solutions

The existing type expressions are isomorphic to the existing LP terms. The
occurs-checked total unifier therefore solves their equations without introducing
another type language or a finite-universe approximation. Unsolved parameters
stay symbolic in the most-general solution.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ConstraintTypes.SymbolicTypes

variable {P Q C : Type} {arity : C → Nat}

abbrev signature (P Q C : Type) (arity : C → Nat) : LP.LPSignature where
  constants := Q
  vars := P
  relationSymbols := Empty
  relationArity := Empty.elim
  functionSymbols := C
  functionArity := arity

abbrev Expr (P Q C : Type) (arity : C → Nat) := TypeExpr P Q C arity
abbrev Closed (Q C : Type) (arity : C → Nat) := Expr Empty Q C arity
abbrev Assignment (P Q C : Type) (arity : C → Nat) := P → Expr P Q C arity
abbrev Equations (P Q C : Type) (arity : C → Nat) := List (Expr P Q C arity × Expr P Q C arity)

def encode : Expr P Q C arity → LP.Term (signature P Q C arity)
  | .parameter p => .var p
  | .closed q => .const q
  | .app c fields => .app c (fun i => encode (fields i))

def decode : LP.Term (signature P Q C arity) → Expr P Q C arity
  | .var p => .parameter p
  | .const q => .closed q
  | .app c fields => .app c (fun i => decode (fields i))

@[simp] theorem decode_encode (term : Expr P Q C arity) : decode (encode term) = term := by
  induction term with
  | parameter _ | closed _ => rfl
  | app c fields ih => exact congrArg (TypeExpr.app c) (funext ih)

@[simp] theorem encode_decode (term : LP.Term (signature P Q C arity)) : encode (decode term) = term := by
  induction term with
  | var _ | const _ => rfl
  | app c fields ih => exact congrArg (LP.Term.app c) (funext ih)

theorem encode_injective : Function.Injective (encode (P := P) (Q := Q) (C := C) (arity := arity)) :=
  fun left right same => by simpa only [decode_encode] using congrArg decode same

def encodeAssignment (assignment : Assignment P Q C arity) : LP.Subst (signature P Q C arity) :=
  fun p => encode (assignment p)

def decodeAssignment (assignment : LP.Subst (signature P Q C arity)) : Assignment P Q C arity :=
  fun p => decode (assignment p)

theorem encode_substitute (assignment : Assignment P Q C arity) (term : Expr P Q C arity) :
    encode (term.substitute assignment) = (encodeAssignment assignment).applyTerm (encode term) := by
  induction term with
  | parameter _ | closed _ => rfl
  | app c fields ih => exact congrArg (LP.Term.app (σ := signature P Q C arity) c) (funext ih)

def encodeEquations (equations : Equations P Q C arity) :
    List (LP.Term (signature P Q C arity) × LP.Term (signature P Q C arity)) :=
  equations.map fun pair => (encode pair.1, encode pair.2)

def Solves (assignment : Assignment P Q C arity) (equations : Equations P Q C arity) : Prop :=
  ∀ pair ∈ equations, pair.1.substitute assignment = pair.2.substitute assignment

theorem solves_iff_unifies (assignment : Assignment P Q C arity) (equations : Equations P Q C arity) :
    Solves assignment equations ↔ LP.Unifies (encodeAssignment assignment) (encodeEquations equations) := by
  constructor
  · intro solved pair member
    obtain ⟨⟨left, right⟩, present, rfl⟩ := List.mem_map.1 member
    simpa only [← encode_substitute] using congrArg encode (solved (left, right) present)
  · intro solved pair present
    have equal := solved (encode pair.1, encode pair.2) (List.mem_map.2 ⟨pair, present, rfl⟩)
    simpa only [← encode_substitute, decode_encode] using congrArg decode equal

def MoreGeneral (first second : Assignment P Q C arity) : Prop :=
  ∃ later : Assignment P Q C arity, ∀ p, second p = (first p).substitute later

def solve [DecidableEq P] [DecidableEq Q] [DecidableEq C]
    (equations : Equations P Q C arity) : Option (Assignment P Q C arity) :=
  (LP.unifyTotal (encodeEquations equations)).map decodeAssignment

theorem solve_sound [DecidableEq P] [DecidableEq Q] [DecidableEq C]
    (equations : Equations P Q C arity) (assignment : Assignment P Q C arity)
    (accepted : solve equations = some assignment) : Solves assignment equations := by
  unfold solve at accepted
  cases raw : LP.unifyTotal (encodeEquations equations) with
  | none => simp [raw] at accepted
  | some result =>
      simp only [raw, Option.map_some, Option.some.injEq] at accepted
      subst assignment
      apply (solves_iff_unifies _ _).2
      have same : encodeAssignment (decodeAssignment result) = result := by
        funext p; exact encode_decode (result p)
      rw [same]
      exact LP.unifyTotal_sound _ _ raw

theorem solve_complete [DecidableEq P] [DecidableEq Q] [DecidableEq C]
    (equations : Equations P Q C arity)
    (existsSolution : ∃ assignment, Solves assignment equations) :
    ∃ assignment, solve equations = some assignment := by
  obtain ⟨assignment, solved⟩ := existsSolution
  obtain ⟨result, accepted⟩ := LP.unifyTotal_complete
    ⟨encodeAssignment assignment, (solves_iff_unifies _ _).1 solved⟩
  exact ⟨decodeAssignment result, by simp [solve, accepted]⟩

theorem solve_principal [DecidableEq P] [DecidableEq Q] [DecidableEq C]
    (equations : Equations P Q C arity) (assignment candidate : Assignment P Q C arity)
    (accepted : solve equations = some assignment) (solved : Solves candidate equations) :
    MoreGeneral assignment candidate := by
  unfold solve at accepted
  cases raw : LP.unifyTotal (encodeEquations equations) with
  | none => simp [raw] at accepted
  | some result =>
      simp only [raw, Option.map_some, Option.some.injEq] at accepted
      subst assignment
      obtain ⟨later, factors⟩ := LP.unifyTotal_mgu _ _ raw (encodeAssignment candidate)
        ((solves_iff_unifies _ _).1 solved)
      refine ⟨decodeAssignment later, fun p => ?_⟩
      have same : encodeAssignment (decodeAssignment later) = later := by
        funext p; exact encode_decode (later p)
      apply encode_injective
      simp only [encode_substitute, same, decodeAssignment, encode_decode]
      exact factors p

def GroundSolves (assignment : P → Closed Q C arity) (equations : Equations P Q C arity) : Prop :=
  ∀ pair ∈ equations, pair.1.substitute assignment = pair.2.substitute assignment

def embedClosed (term : Closed Q C arity) : Expr P Q C arity := term.rename Empty.elim

theorem close_embed (assignment : P → Closed Q C arity) (term : Closed Q C arity) :
    (embedClosed term).substitute assignment = term := by
  rw [embedClosed, TypeExpr.substitute_rename]
  have same : assignment ∘ Empty.elim = TypeExpr.parameter := by funext p; cases p
  rw [same, TypeExpr.substitute_id]

theorem ground_solution_is_symbolic (assignment : P → Closed Q C arity)
    (equations : Equations P Q C arity) (solved : GroundSolves assignment equations) :
    Solves (fun p => embedClosed (assignment p)) equations := by
  intro pair present
  simpa only [embedClosed, ← TypeExpr.rename_substitute] using
    congrArg (TypeExpr.rename (Empty.elim : Empty → P)) (solved pair present)

theorem close_solution (assignment : Assignment P Q C arity)
    (closing : P → Closed Q C arity) (equations : Equations P Q C arity)
    (solved : Solves assignment equations) :
    GroundSolves (fun p => (assignment p).substitute closing) equations := by
  intro pair present
  simpa only [← TypeExpr.substitute_comp] using
    congrArg (TypeExpr.substitute closing) (solved pair present)

/-- A symbolic success has a ground realization whenever the proper type
universe has one inhabitant. No list of its possible inhabitants is needed. -/
theorem solve_iff_ground_solution [DecidableEq P] [DecidableEq Q] [DecidableEq C]
    (seed : Closed Q C arity) (equations : Equations P Q C arity) :
    (∃ assignment, solve equations = some assignment) ↔
      ∃ assignment : P → Closed Q C arity, GroundSolves assignment equations := by
  constructor
  · rintro ⟨assignment, success⟩
    exact ⟨fun p => (assignment p).substitute (fun _ => seed),
      close_solution assignment (fun _ => seed) equations (solve_sound equations assignment success)⟩
  · rintro ⟨assignment, solved⟩
    exact solve_complete equations ⟨_, ground_solution_is_symbolic assignment equations solved⟩

/-- Every ground solution is a closing instance of the principal solution. -/
theorem ground_solution_factors [DecidableEq P] [DecidableEq Q] [DecidableEq C]
    (equations : Equations P Q C arity) (principal : Assignment P Q C arity)
    (accepted : solve equations = some principal) (values : P → Closed Q C arity)
    (solved : GroundSolves values equations) :
    ∃ closing : P → Closed Q C arity,
      ∀ p, values p = (principal p).substitute closing := by
  obtain ⟨later, factors⟩ := solve_principal equations principal
    (fun p => embedClosed (values p)) accepted (ground_solution_is_symbolic values equations solved)
  refine ⟨fun p => (later p).substitute values, fun p => ?_⟩
  have closed := congrArg (TypeExpr.substitute values) (factors p)
  simpa only [close_embed, TypeExpr.substitute_comp] using closed

/-- Normalization retains arbitrary residual predicates, rather than silently
forgetting constraints not yet decided by the type equations. Pointwise use
also permits a predicate whose declaration world is supplied later. -/
theorem residual_normalization_exact [DecidableEq P] [DecidableEq Q] [DecidableEq C]
    (equations : Equations P Q C arity) (principal : Assignment P Q C arity)
    (accepted : solve equations = some principal) (residual : (P → Closed Q C arity) → Prop) :
    (∃ values, GroundSolves values equations ∧ residual values) ↔
      ∃ closing, residual (fun p => (principal p).substitute closing) := by
  constructor
  · rintro ⟨values, solved, pending⟩
    obtain ⟨closing, same⟩ := ground_solution_factors equations principal accepted values solved
    exact ⟨closing, by simpa only [← funext same] using pending⟩
  · rintro ⟨closing, pending⟩
    exact ⟨_, close_solution principal closing equations (solve_sound equations principal accepted), pending⟩

/-- Equality of closed type expressions uses the existing total unifier. -/
def equalClosed [DecidableEq Q] [DecidableEq C] (left right : Closed Q C arity) : Bool :=
  (solve [(left, right)]).isSome

theorem closed_substitute (term : Closed Q C arity) (values : Empty → Closed Q C arity) :
    term.substitute values = term := by
  have same : values = TypeExpr.parameter := by funext p; cases p
  rw [same, TypeExpr.substitute_id]

theorem equalClosed_iff [DecidableEq Q] [DecidableEq C] (left right : Closed Q C arity) :
    equalClosed left right = true ↔ left = right := by
  rw [equalClosed, Option.isSome_iff_exists, solve_iff_ground_solution left]
  constructor
  · rintro ⟨values, solved⟩
    simpa only [closed_substitute] using solved _ List.mem_cons_self
  · intro same
    subst right
    refine ⟨Empty.elim, ?_⟩
    intro pair present
    have equal := List.mem_singleton.1 present
    subst pair
    rfl

end Mettapedia.Logic.ConstraintTypes.SymbolicTypes
