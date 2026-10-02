import Mettapedia.Logic.LP.Unification

/-!
# Unification with a private clause variable

A fresh anonymous clause variable unifies with an incoming term, but its
binding is invisible to observations that do not contain that variable.
The success and projection laws below use the actual LP unifier. They apply
after the caller's current substitution has been resolved. They do not erase
unification with a caller variable or with a variable inside a structured term.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.LP

variable {σ : LPSignature} [DecidableEq σ.vars] [DecidableEq σ.constants]
  [DecidableEq σ.functionSymbols]

theorem unify_private_variable (privateVar : σ.vars) (required : Term σ)
    (fresh : required.occursIn privateVar = false) :
    unifyFuel 2 [(.var privateVar, required)] =
      some (Subst.single privateVar required) := by
  cases required with
  | var callerVar =>
      have different : privateVar ≠ callerVar := by
        simpa [Term.occursIn] using fresh
      simp [unifyFuel, different, Subst.applyEqs, Subst.comp_id_left]
  | const name =>
      simp [unifyFuel, Term.occursIn, Subst.applyEqs, Subst.comp_id_left]
  | app function arguments =>
      simp [unifyFuel, fresh, Subst.applyEqs, Subst.comp_id_left]

/-- Run clause-head unification and retain the caller's observable terms.
Failure is an empty answer list; success publishes one projected answer. -/
def privateVariableAnswers (privateVar : σ.vars) (required : Term σ)
    (observations : List (Term σ)) : List (List (Term σ)) :=
  match unifyFuel 2 [(.var privateVar, required)] with
  | none => []
  | some substitution => [observations.map substitution.applyTerm]

theorem private_variable_answers_identity (privateVar : σ.vars) (required : Term σ)
    (observations : List (Term σ))
    (requiredFresh : required.occursIn privateVar = false)
    (observationsFresh : ∀ term ∈ observations, term.occursIn privateVar = false) :
    privateVariableAnswers privateVar required observations = [observations] := by
  unfold privateVariableAnswers
  rw [unify_private_variable privateVar required requiredFresh]
  change [observations.map (Subst.single privateVar required).applyTerm] = [observations]
  apply congrArg (fun terms : List (Term σ) => [terms])
  induction observations with
  | nil => rfl
  | cons term terms ih =>
      simp only [List.map_cons]
      rw [Subst.single_applyTerm_not_occursIn privateVar required term
        (observationsFresh term (by simp))]
      rw [ih (fun term member => observationsFresh term (by simp [member]))]

/-- Freshness concerns the resolved observations, not only their source
syntax. A binding can introduce the private variable transitively. -/
theorem private_variable_answers_after_binding (privateVar : σ.vars)
    (incoming : Subst σ) (required : Term σ) (observations : List (Term σ))
    (requiredFresh : (incoming.applyTerm required).occursIn privateVar = false)
    (observationsFresh : ∀ term ∈ observations,
      (incoming.applyTerm term).occursIn privateVar = false) :
    privateVariableAnswers privateVar (incoming.applyTerm required)
      (observations.map incoming.applyTerm) = [observations.map incoming.applyTerm] := by
  apply private_variable_answers_identity _ _ _ requiredFresh
  intro resolved member
  obtain ⟨term, termMember, rfl⟩ := List.mem_map.mp member
  exact observationsFresh term termMember

/-- Eliminate a fresh vector of private clause fields in source order. The
equation list below is still executed by the ordinary LP unifier. -/
def privateFieldSubstitution : List (σ.vars × Term σ) → Subst σ
  | [] => Subst.id σ
  | (fieldId, required) :: later =>
      (privateFieldSubstitution later) ∘ₛ Subst.single fieldId required

omit [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
private theorem private_field_apply_rest (fieldId : σ.vars) (required : Term σ)
    (later : List (σ.vars × Term σ))
    (different : ∀ pair ∈ later, fieldId ≠ pair.1)
    (fresh : ∀ pair ∈ later, pair.2.occursIn fieldId = false) :
    (Subst.single fieldId required).applyEqs
      (later.map (fun pair => (Term.var pair.1, pair.2))) =
      later.map (fun pair => (Term.var pair.1, pair.2)) := by
  unfold Subst.applyEqs
  rw [List.map_map]
  apply List.map_congr_left
  intro pair member
  simp only [Function.comp_apply]
  rw [Subst.single_applyTerm_not_occursIn fieldId required pair.2 (fresh pair member)]
  simp [Subst.applyTerm, Subst.single, Ne.symm (different pair member)]

/-- An arbitrary fresh field vector succeeds, with no alternatives or public
binding changes. Freshness includes every required field, not only its own. -/
theorem unify_private_fields (fields : List (σ.vars × Term σ))
    (distinct : (fields.map Prod.fst).Nodup)
    (fresh : ∀ fieldId ∈ fields.map Prod.fst, ∀ pair ∈ fields,
      pair.2.occursIn fieldId = false) :
    unifyFuel (fields.length + 1)
      (fields.map (fun pair => (Term.var pair.1, pair.2))) =
      some (privateFieldSubstitution fields) := by
  induction fields with
  | nil => rfl
  | cons pair later ih =>
      rcases pair with ⟨fieldId, required⟩
      have splitDistinct : fieldId ∉ later.map Prod.fst ∧ (later.map Prod.fst).Nodup := by
        simpa only [List.map_cons, List.nodup_cons] using distinct
      have distinctLater : (later.map Prod.fst).Nodup := splitDistinct.2
      have different : ∀ pair ∈ later, fieldId ≠ pair.1 := by
        intro pair member same
        have absent : fieldId ∉ later.map Prod.fst := splitDistinct.1
        exact absent (List.mem_map.mpr ⟨pair, member, same.symm⟩)
      have ownFresh : required.occursIn fieldId = false :=
        fresh fieldId (by simp) (fieldId, required) (by simp)
      have restFresh : ∀ pair ∈ later, pair.2.occursIn fieldId = false := by
        intro pair member
        exact fresh fieldId (by simp) pair (by simp [member])
      have laterFresh : ∀ fieldId ∈ later.map Prod.fst, ∀ pair ∈ later,
          pair.2.occursIn fieldId = false := by
        intro fieldId variableMember pair member
        exact fresh fieldId (by simp [variableMember]) pair (by simp [member])
      have unchanged := private_field_apply_rest fieldId required later different restFresh
      have recursion := ih distinctLater laterFresh
      cases required with
      | var other =>
          have differentRoot : fieldId ≠ other := by
            simpa [Term.occursIn] using ownFresh
          simp only [List.length_cons, List.map_cons, unifyFuel, differentRoot,
            ↓reduceIte, unchanged, recursion, privateFieldSubstitution]
      | const name =>
          simp only [List.length_cons, List.map_cons, unifyFuel, Term.occursIn,
            Bool.false_eq_true, ↓reduceIte, unchanged, recursion, privateFieldSubstitution]
      | app function arguments =>
          simp only [List.length_cons, List.map_cons, unifyFuel, ownFresh,
            Bool.false_eq_true, ↓reduceIte, unchanged, recursion, privateFieldSubstitution]

omit [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
theorem private_fields_keep_public_term (fields : List (σ.vars × Term σ))
    (term : Term σ)
    (fresh : ∀ fieldId ∈ fields.map Prod.fst, term.occursIn fieldId = false) :
    (privateFieldSubstitution fields).applyTerm term = term := by
  induction fields with
  | nil => exact Subst.applyTerm_id term
  | cons pair later ih =>
      rcases pair with ⟨fieldId, required⟩
      rw [privateFieldSubstitution, Subst.applyTerm_comp,
        Subst.single_applyTerm_not_occursIn fieldId required term (fresh fieldId (by simp))]
      exact ih (fun fieldId member => fresh fieldId (by simp [member]))

/-- Constructor matching introduces exactly these private field equations.
The public target is preserved even if it contains shared caller variables. -/
theorem unify_private_constructor (function : σ.functionSymbols)
    (names : Fin (σ.functionArity function) → σ.vars)
    (required : Fin (σ.functionArity function) → Term σ)
    (distinct : Function.Injective names)
    (fresh : ∀ i j, (required j).occursIn (names i) = false) :
    unifyFuel (σ.functionArity function + 2)
      [(.app function (fun i => .var (names i)), .app function required)] =
      some (privateFieldSubstitution
        ((List.finRange (σ.functionArity function)).map (fun i => (names i, required i)))) := by
  let fields := (List.finRange (σ.functionArity function)).map (fun i => (names i, required i))
  have fieldsDistinct : (fields.map Prod.fst).Nodup := by
    simpa [fields, List.map_map, Function.comp_def] using
      (List.nodup_map_iff distinct).mpr (List.nodup_finRange (σ.functionArity function))
  have fieldsFresh : ∀ fieldId ∈ fields.map Prod.fst, ∀ pair ∈ fields,
      pair.2.occursIn fieldId = false := by
    intro fieldId variableMember pair member
    obtain ⟨first, firstMember, rfl⟩ := List.mem_map.mp variableMember
    obtain ⟨i, iMember, rfl⟩ := List.mem_map.mp firstMember
    obtain ⟨j, jMember, rfl⟩ := List.mem_map.mp member
    exact fresh i j
  have result := unify_private_fields fields fieldsDistinct fieldsFresh
  simpa [unifyFuel, finPairsToList, fields, List.map_map, Function.comp_def] using result

/-- The private constructor becomes exactly the incoming constructor under
the substitution returned by the actual unifier. The required fields need
not be closed or distinct: caller variables may be shared between fields. -/
theorem private_constructor_projects (function : σ.functionSymbols)
    (names : Fin (σ.functionArity function) → σ.vars)
    (required : Fin (σ.functionArity function) → Term σ)
    (distinct : Function.Injective names)
    (fresh : ∀ i j, (required j).occursIn (names i) = false) :
    (privateFieldSubstitution
      ((List.finRange (σ.functionArity function)).map (fun i => (names i, required i)))).applyTerm
      (.app function (fun i => .var (names i))) = .app function required := by
  have solved := unifyFuel_sound _ _ _
    (unify_private_constructor function names required distinct fresh)
  have same := solved
    (.app function (fun i => .var (names i)), .app function required) (by simp)
  change _ = _ at same
  rw [same]
  simp only [Subst.applyTerm_app]
  congr 1
  funext j
  apply private_fields_keep_public_term
  intro fieldId member
  obtain ⟨pair, pairMember, rfl⟩ := List.mem_map.mp member
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp pairMember
  exact fresh i j

/-- Later matching sees the same required row whether private aliases were
allocated or the required fields were used directly. No restriction is
imposed on the later substitution. -/
theorem private_constructor_then_refine (function : σ.functionSymbols)
    (names : Fin (σ.functionArity function) → σ.vars)
    (required : Fin (σ.functionArity function) → Term σ)
    (distinct : Function.Injective names)
    (fresh : ∀ i j, (required j).occursIn (names i) = false)
    (later : Subst σ) :
    (later ∘ₛ privateFieldSubstitution
      ((List.finRange (σ.functionArity function)).map (fun i => (names i, required i)))).applyTerm
      (.app function (fun i => .var (names i))) =
      later.applyTerm (.app function required) := by
  rw [Subst.applyTerm_comp, private_constructor_projects function names required distinct fresh]

omit [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
/-- Public refinements made after the initial private matching are unaffected
by eliminating its alias fields. This is the continuation-facing law. -/
theorem private_fields_then_refine (fields : List (σ.vars × Term σ))
    (later : Subst σ) (term : Term σ)
    (fresh : ∀ fieldId ∈ fields.map Prod.fst, term.occursIn fieldId = false) :
    (later ∘ₛ privateFieldSubstitution fields).applyTerm term = later.applyTerm term := by
  rw [Subst.applyTerm_comp, private_fields_keep_public_term fields term fresh]

omit [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
/-- All caller observations retain their order and sharing after any later
refinement. This includes observations of subject terms as well as types. -/
theorem private_fields_then_refine_observations (fields : List (σ.vars × Term σ))
    (later : Subst σ) (observations : List (Term σ))
    (fresh : ∀ term ∈ observations, ∀ fieldId ∈ fields.map Prod.fst,
      term.occursIn fieldId = false) :
    observations.map (later ∘ₛ privateFieldSubstitution fields).applyTerm =
      observations.map later.applyTerm := by
  apply List.map_congr_left
  intro term member
  exact private_fields_then_refine fields later term (fresh term member)

namespace PrivateVariableControls

abbrev signature : LPSignature where
  constants := Nat
  vars := Nat
  relationSymbols := Unit
  relationArity := fun _ => 0
  functionSymbols := Unit
  functionArity := fun _ => 1

def wrap (term : Term signature) : Term signature := .app () (fun _ => term)

theorem structured_requirement_keeps_public_terms :
    privateVariableAnswers (σ := signature) 0 (wrap (.var 1))
      [.var 1, wrap (.const 6)] = [[.var 1, wrap (.const 6)]] := by
  apply private_variable_answers_identity <;>
    simp [wrap, signature, Term.occursIn]

theorem private_occurrence_rejects :
    privateVariableAnswers (σ := signature) 0 (wrap (.var 0)) [.var 1] = [] := by
  simp [privateVariableAnswers, unifyFuel, wrap, signature, Term.occursIn]

theorem observable_private_binding_is_not_identity :
    privateVariableAnswers (σ := signature) 0 (.const 6) [.var 0] = [[.const 6]] := by
  simp [privateVariableAnswers, unifyFuel, Term.occursIn, Subst.applyEqs,
    Subst.comp_id_left, Subst.applyTerm, Subst.single]

theorem caller_unification_can_refine :
    privateVariableAnswers (σ := signature) 1 (.const 6) [.var 1] ≠ [[.var 1]] := by
  simp [privateVariableAnswers, unifyFuel, Term.occursIn, Subst.applyEqs,
    Subst.comp_id_left, Subst.applyTerm, Subst.single]

abbrev rowSignature : LPSignature where
  constants := Nat
  vars := Nat
  relationSymbols := Unit
  relationArity := fun _ => 0
  functionSymbols := Nat
  functionArity := id

/-- Two private fields can refer to the same public variable. A subsequent
binding of that variable changes both result positions together. -/
theorem shared_required_variable_refines_both_fields :
    let fields : List (rowSignature.vars × Term rowSignature) :=
      (List.finRange 2).map (fun i => (i.val, .var 4))
    ((Subst.single (σ := rowSignature) 4 (.const 6)) ∘ₛ privateFieldSubstitution fields).applyTerm
      (.app 2 (fun i => .var i.val)) = .app 2 (fun _ => .const 6) := by
  have fresh : ∀ i j : Fin 2,
      (Term.var (σ := rowSignature) 4).occursIn i.val = false := by
    intro i _
    simp only [Term.occursIn, beq_eq_false_iff_ne]
    omega
  have projected := private_constructor_then_refine (σ := rowSignature)
    2 Fin.val (fun _ => .var 4) Fin.val_injective fresh (Subst.single 4 (.const 6))
  simpa [Subst.applyTerm, Subst.single] using projected

/-- Reusing one private name introduces an equality constraint between
fields. Independent incoming fields cannot then replace the private row. -/
theorem aliased_private_fields_can_reject :
    unifyFuel (σ := rowSignature) 4
      [(.app 2 (fun _ => .var 0),
        .app 2 (fun i => if i.val = 0 then .const 6 else .const 7))] = none := by
  decide

/-- A required field containing the private name can fail the occurs check;
freshness must be tested against the whole resolved required row. -/
theorem private_field_in_required_constructor_rejects :
    unifyFuel (σ := rowSignature) 3
      [(.app 1 (fun _ => .var 0), .app 1 (fun _ => .app 1 (fun _ => .var 0)))] =
      none := by
  decide

end PrivateVariableControls
end Mettapedia.Logic.LP
