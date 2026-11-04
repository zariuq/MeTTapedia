import Mettapedia.Logic.ConstraintTypes.Constraints
import Mettapedia.Logic.ConstraintTypes.SymbolicTypes

/-!
# Read-only matching of nominal value patterns

Ranked value trees use the same total unifier through a lossless encoding.
Repeated pattern variables impose equality of the corresponding subtrees.
Only the pattern receives an existential assignment; the supplied value is
closed and never modified. This supports compound nominal facts without
assuming that their languages are regular.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ConstraintTypes.ValuePatterns

open SymbolicTypes

variable {X S : Type} {arity : S → Nat}

def patternCode : OpenTree X S arity → Expr X Empty S arity
  | .var x => .parameter x
  | .node s children => .app s (fun i => patternCode (children i))

def valueCode : Tree S arity → Closed Empty S arity
  | .node s children => .app s (fun i => valueCode (children i))

def decodeValue : Closed Empty S arity → Tree S arity
  | .parameter impossible => nomatch impossible
  | .closed impossible => nomatch impossible
  | .app s children => .node s (fun i => decodeValue (children i))

@[simp] theorem decode_valueCode (value : Tree S arity) : decodeValue (valueCode value) = value := by
  induction value with
  | node s children ih => exact congrArg (Tree.node s) (funext ih)

@[simp] theorem valueCode_decode (code : Closed Empty S arity) : valueCode (decodeValue code) = code := by
  induction code with
  | parameter impossible | closed impossible => exact Empty.elim impossible
  | app s children ih => exact congrArg (TypeExpr.app s) (funext ih)

theorem valueCode_injective : Function.Injective (valueCode (S := S) (arity := arity)) :=
  fun left right same => by simpa only [decode_valueCode] using congrArg decodeValue same

theorem code_evaluate (assignment : X → Tree S arity) (pattern : OpenTree X S arity) :
    valueCode (pattern.evaluate assignment) =
      (patternCode pattern).substitute (fun x => valueCode (assignment x)) := by
  induction pattern with
  | var _ => rfl
  | node s children ih => exact congrArg (TypeExpr.app s) (funext ih)

def matchValue [DecidableEq X] [DecidableEq S]
    (pattern : OpenTree X S arity) (value : Tree S arity) : Bool :=
  (SymbolicTypes.solve [(patternCode pattern, embedClosed (valueCode value))]).isSome

theorem matchValue_iff [DecidableEq X] [DecidableEq S]
    (pattern : OpenTree X S arity) (value : Tree S arity) :
    matchValue pattern value = true ↔ ∃ assignment, pattern.evaluate assignment = value := by
  rw [matchValue, Option.isSome_iff_exists,
    SymbolicTypes.solve_iff_ground_solution (valueCode value)]
  constructor
  · rintro ⟨assignment, solved⟩
    refine ⟨fun x => decodeValue (assignment x), ?_⟩
    have equation := solved _ List.mem_cons_self
    rw [close_embed] at equation
    apply valueCode_injective
    have through := code_evaluate (fun x => decodeValue (assignment x)) pattern
    have same : (fun x => valueCode (decodeValue (assignment x))) = assignment := by
      funext x; exact valueCode_decode (assignment x)
    rw [same] at through
    exact through.trans equation
  · rintro ⟨assignment, equal⟩
    refine ⟨fun x => valueCode (assignment x), ?_⟩
    intro pair present
    have single := List.mem_singleton.1 present
    subst pair
    rw [close_embed, ← code_evaluate, equal]

/-- Recover the matched subtrees. Unused variables receive the supplied value;
variables occurring in the pattern have their uniquely determined values. -/
def matchAssignment [DecidableEq X] [DecidableEq S]
    (pattern : OpenTree X S arity) (value : Tree S arity) : Option (X → Tree S arity) :=
  (SymbolicTypes.solve [(patternCode pattern, embedClosed (valueCode value))]).map fun solution x =>
    decodeValue ((solution x).substitute (fun _ => valueCode value))

theorem matchAssignment_sound [DecidableEq X] [DecidableEq S]
    (pattern : OpenTree X S arity) (value : Tree S arity) (assignment : X → Tree S arity)
    (matched : matchAssignment pattern value = some assignment) :
    pattern.evaluate assignment = value := by
  unfold matchAssignment at matched
  cases raw : SymbolicTypes.solve [(patternCode pattern, embedClosed (valueCode value))] with
  | none => simp [raw] at matched
  | some solution =>
      simp only [raw, Option.map_some, Option.some.injEq] at matched
      subst assignment
      have solved := close_solution solution (fun _ => valueCode value) _
        (SymbolicTypes.solve_sound _ _ raw)
      have equation := solved _ List.mem_cons_self
      rw [close_embed] at equation
      apply valueCode_injective
      rw [code_evaluate]
      simpa only [TypeExpr.substitute_comp, valueCode_decode] using equation

theorem matchAssignment_exists [DecidableEq X] [DecidableEq S]
    (pattern : OpenTree X S arity) (value : Tree S arity) :
    (∃ assignment, matchAssignment pattern value = some assignment) ↔
      ∃ assignment, pattern.evaluate assignment = value := by
  rw [← Option.isSome_iff_exists, matchAssignment, Option.isSome_map]
  exact matchValue_iff pattern value

/-- Matching determines every variable that actually occurs in the pattern. -/
theorem matched_variable_determined (pattern : OpenTree X S arity)
    (left right : X → Tree S arity) (same : pattern.evaluate left = pattern.evaluate right)
    (x : X) (present : x ∈ (patternCode pattern).variables) : left x = right x := by
  apply valueCode_injective
  apply TypeExpr.parameters_determined (fun x => valueCode (left x))
    (fun x => valueCode (right x)) (patternCode pattern) _ x present
  simpa only [← code_evaluate] using congrArg valueCode same

/-- An explicit link from a type-scheme parameter to a matched value field.
The occurrence proof excludes dependence on an unmatched pattern variable. -/
structure TypeBinding (P : Type) (pattern : OpenTree X S arity) where
  parameter : P
  name : X
  present : name ∈ (patternCode pattern).variables

section Bindings

variable {P Q C : Type} {typeArity : C → Nat} {pattern : OpenTree X S arity}

def checkRead [DecidableEq X] [DecidableEq S] [DecidableEq Q] [DecidableEq C]
    (pattern : OpenTree X S arity) (name : X)
    (readType : Tree S arity → Option (Closed Q C typeArity))
    (value : Tree S arity) (type : Closed Q C typeArity) : Bool :=
  match matchAssignment pattern value with
  | none => false
  | some values => match readType (values name) with
    | none => false
    | some actual => equalClosed actual type

theorem checkRead_iff [DecidableEq X] [DecidableEq S] [DecidableEq Q] [DecidableEq C]
    (pattern : OpenTree X S arity) (name : X) (present : name ∈ (patternCode pattern).variables)
    (readType : Tree S arity → Option (Closed Q C typeArity))
    (value : Tree S arity) (type : Closed Q C typeArity) :
    checkRead pattern name readType value type = true ↔
      ∃ values, pattern.evaluate values = value ∧ readType (values name) = some type := by
  cases chosen : matchAssignment pattern value with
  | none =>
      simp only [checkRead, chosen, Bool.false_eq_true, false_iff]
      rintro ⟨values, matched, _⟩
      obtain ⟨_, success⟩ := (matchAssignment_exists pattern value).2 ⟨values, matched⟩
      simp [chosen] at success
  | some values =>
      simp only [checkRead, chosen]
      have matched := matchAssignment_sound pattern value values chosen
      have equality : (match readType (values name) with
          | none => false
          | some actual => equalClosed actual type) = true ↔
          readType (values name) = some type := by
        cases read : readType (values name) with
        | none => simp
        | some actual => simp only [equalClosed_iff, Option.some.injEq]
      rw [equality]
      constructor
      · exact fun read => ⟨values, matched, read⟩
      · rintro ⟨other, equal, read⟩
        have same := matched_variable_determined pattern values other (matched.trans equal.symm) name present
        simpa only [same] using read

def readEquations (readType : Tree S arity → Option (Closed Q C typeArity))
    (values : X → Tree S arity) : List (TypeBinding P pattern) → Option (Equations P Q C typeArity)
  | [] => some []
  | binding :: rest => do
      let type ← readType (values binding.name)
      let equations ← readEquations readType values rest
      pure ((.parameter binding.parameter, embedClosed type) :: equations)

def BindingsHold (readType : Tree S arity → Option (Closed Q C typeArity))
    (values : X → Tree S arity) (parameters : P → Closed Q C typeArity)
    (bindings : List (TypeBinding P pattern)) : Prop :=
  ∀ binding ∈ bindings, readType (values binding.name) = some (parameters binding.parameter)

theorem groundSolves_binding_cons (parameters : P → Closed Q C typeArity)
    (p : P) (type : Closed Q C typeArity) (equations : Equations P Q C typeArity) :
    GroundSolves parameters ((.parameter p, embedClosed type) :: equations) ↔
      parameters p = type ∧ GroundSolves parameters equations := by
  constructor
  · intro h
    refine ⟨?_, fun pair present => h pair (List.mem_cons_of_mem _ present)⟩
    simpa only [TypeExpr.substitute, close_embed] using h _ List.mem_cons_self
  · rintro ⟨same, rest⟩ pair present
    rcases List.mem_cons.1 present with rfl | present
    · simpa only [TypeExpr.substitute, close_embed] using same
    · exact rest pair present

theorem readEquations_correct (readType : Tree S arity → Option (Closed Q C typeArity))
    (values : X → Tree S arity) (parameters : P → Closed Q C typeArity)
    (bindings : List (TypeBinding P pattern)) :
    (∃ equations, readEquations readType values bindings = some equations ∧
      GroundSolves parameters equations) ↔ BindingsHold readType values parameters bindings := by
  induction bindings with
  | nil => simp [readEquations, GroundSolves, BindingsHold]
  | cons binding rest ih =>
      cases read : readType (values binding.name) with
      | none => simp [readEquations, read, BindingsHold]
      | some type =>
          constructor
          · rintro ⟨equations, accepted, solved⟩
            simp only [readEquations, read] at accepted
            cases decoded : readEquations readType values rest with
            | none => simp [decoded] at accepted
            | some tail =>
                simp only [decoded] at accepted
                change some ((TypeExpr.parameter binding.parameter, embedClosed type) :: tail) = some equations at accepted
                have equal := Option.some.inj accepted
                subst equations
                obtain ⟨same, all⟩ := (groundSolves_binding_cons parameters _ _ _).1 solved
                have remaining := ih.1 ⟨tail, decoded, all⟩
                intro b present
                rcases List.mem_cons.1 present with rfl | present
                · simp only [read, same]
                · exact remaining b present
          · intro all
            have head := all binding List.mem_cons_self
            have same : parameters binding.parameter = type := Option.some.inj (read.symm.trans head) |>.symm
            obtain ⟨tail, decoded, solved⟩ := ih.2 (fun b present => all b (List.mem_cons_of_mem _ present))
            refine ⟨(.parameter binding.parameter, embedClosed type) :: tail, ?_,
              (groundSolves_binding_cons parameters _ _ _).2 ⟨same, solved⟩⟩
            simp [readEquations, read, decoded]

theorem bindingsHold_match_congr (readType : Tree S arity → Option (Closed Q C typeArity))
    (left right : X → Tree S arity) (same : pattern.evaluate left = pattern.evaluate right)
    (parameters : P → Closed Q C typeArity) (bindings : List (TypeBinding P pattern)) :
    BindingsHold readType left parameters bindings ↔ BindingsHold readType right parameters bindings := by
  have agrees (binding : TypeBinding P pattern) : left binding.name = right binding.name :=
    matched_variable_determined pattern left right same binding.name binding.present
  unfold BindingsHold
  simp only [agrees]

/-- Match first, read the explicitly linked fields, and specialize the type
scheme by their principal equations. Remaining type parameters stay symbolic. -/
def specialize [DecidableEq P] [DecidableEq X] [DecidableEq Q] [DecidableEq C] [DecidableEq S]
    (pattern : OpenTree X S arity) (bindings : List (TypeBinding P pattern))
    (readType : Tree S arity → Option (Closed Q C typeArity))
    (scheme : Expr P Q C typeArity) (value : Tree S arity) : Option (Expr P Q C typeArity) :=
  match matchAssignment pattern value with
  | none => none
  | some values => match readEquations readType values bindings with
    | none => none
    | some equations => (SymbolicTypes.solve equations).map (fun solution => scheme.substitute solution)

/-- The specialized scheme has exactly the instances of a matched fact with
its linked value/type variables respected. No first type witness is chosen. -/
theorem specialize_iff [DecidableEq P] [DecidableEq X] [DecidableEq Q] [DecidableEq C] [DecidableEq S]
    (pattern : OpenTree X S arity) (bindings : List (TypeBinding P pattern))
    (readType : Tree S arity → Option (Closed Q C typeArity))
    (scheme : Expr P Q C typeArity) (value : Tree S arity) (target : Closed Q C typeArity) :
    (∃ result, specialize pattern bindings readType scheme value = some result ∧
      ∃ closing, target = result.substitute closing) ↔
      ∃ values, pattern.evaluate values = value ∧ ∃ parameters,
        BindingsHold readType values parameters bindings ∧ target = scheme.substitute parameters := by
  constructor
  · rintro ⟨result, accepted, closing, typeEqual⟩
    unfold specialize at accepted
    cases matched : matchAssignment pattern value with
    | none => simp [matched] at accepted
    | some values =>
        simp only [matched] at accepted
        cases decoded : readEquations readType values bindings with
        | none => simp [decoded] at accepted
        | some equations =>
            simp only [decoded] at accepted
            cases solved : SymbolicTypes.solve equations with
            | none => simp [solved] at accepted
            | some solution =>
                simp only [solved, Option.map_some, Option.some.injEq] at accepted
                subst result
                have ground := close_solution solution closing equations (SymbolicTypes.solve_sound _ _ solved)
                refine ⟨values, matchAssignment_sound _ _ _ matched,
                  (fun p => (solution p).substitute closing),
                  (readEquations_correct _ _ _ _).1 ⟨equations, decoded, ground⟩, ?_⟩
                simpa only [TypeExpr.substitute_comp] using typeEqual
  · rintro ⟨values, matched, parameters, bound, typeEqual⟩
    obtain ⟨chosen, choice⟩ := (matchAssignment_exists pattern value).2 ⟨values, matched⟩
    have same : pattern.evaluate values = pattern.evaluate chosen :=
      matched.trans (matchAssignment_sound _ _ _ choice).symm
    have chosenBound := (bindingsHold_match_congr readType values chosen same parameters bindings).1 bound
    obtain ⟨equations, decoded, ground⟩ := (readEquations_correct _ _ _ _).2 chosenBound
    obtain ⟨solution, solved⟩ := (SymbolicTypes.solve_iff_ground_solution target equations).2 ⟨parameters, ground⟩
    obtain ⟨closing, factors⟩ := ground_solution_factors equations solution solved parameters ground
    refine ⟨scheme.substitute solution, ?_, closing, ?_⟩
    · simp [specialize, choice, decoded, solved]
    · rw [TypeExpr.substitute_comp]
      simpa only [funext factors] using typeEqual

end Bindings

end Mettapedia.Logic.ConstraintTypes.ValuePatterns
