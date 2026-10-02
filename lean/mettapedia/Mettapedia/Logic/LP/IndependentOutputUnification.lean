import Mettapedia.Logic.LP.UnificationIdempotence
import Mettapedia.Logic.LP.UnificationRenaming

/-!
# Publishing an output after first-order constraint solving

The two computations below use the actual total LP unifier. One includes
the output equation in its initial problem; the other solves the other
equations first, then matches the resolved output. Their chosen variable
aliases can differ. Their complete projected refinement families agree.

The ordered comparison is per alternative: it neither deduplicates nor
reorders alternatives. It does not say that a procedural query may discover
its alternatives under different bindings. Such a transformation additionally
needs a query-specific independence theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.LP.IndependentOutputUnification

open Mettapedia.Logic.LP

variable {σ : LPSignature} [DecidableEq σ.vars] [DecidableEq σ.constants]
  [DecidableEq σ.functionSymbols]

/-- Every subsequent refinement of the published caller observations. -/
def refinements (theta : Subst σ) (observations : List (Term σ)) :
    Set (List (Term σ)) :=
  { values | ∃ later : Subst σ,
      values = observations.map (later ∘ₛ theta).applyTerm }

/-- An independent specification using all solutions of the equation list. -/
def solutions (equations : List (Term σ × Term σ))
    (observations : List (Term σ)) : Set (List (Term σ)) :=
  { values | ∃ theta : Subst σ, Unifies theta equations ∧
      values = observations.map theta.applyTerm }

def publish (result : Option (Subst σ)) (observations : List (Term σ)) :
    List (Set (List (Term σ))) :=
  result.toList.map fun theta => refinements theta observations

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
theorem unifies_refinement (equations : List (Term σ × Term σ))
    (theta later : Subst σ) (solves : Unifies theta equations) :
    Unifies (later ∘ₛ theta) equations := by
  intro pair member
  simp only [Subst.applyTerm_comp]
  exact congrArg later.applyTerm (solves pair member)

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
theorem mgu_refinements_exact (equations : List (Term σ × Term σ))
    (theta : Subst σ) (sound : Unifies theta equations)
    (general : ∀ candidate, Unifies candidate equations → theta.moreGeneral candidate)
    (observations : List (Term σ)) :
    refinements theta observations = solutions equations observations := by
  ext values
  constructor
  · rintro ⟨later, rfl⟩
    exact ⟨later ∘ₛ theta, unifies_refinement equations theta later sound, rfl⟩
  · rintro ⟨candidate, solves, rfl⟩
    obtain ⟨later, same⟩ := general candidate solves
    have equal : candidate = later ∘ₛ theta := funext same
    exact ⟨later, by rw [equal]⟩

theorem total_refinements_exact (equations : List (Term σ × Term σ))
    (theta : Subst σ) (accepted : unifyTotal equations = some theta)
    (observations : List (Term σ)) :
    refinements theta observations = solutions equations observations :=
  mgu_refinements_exact equations theta
    (unifyTotal_sound equations theta accepted)
    (unifyTotal_mgu equations theta accepted) observations

/-- Solve the first problem, then solve the second under its actual bindings. -/
def sequential (first second : List (Term σ × Term σ)) : Option (Subst σ) :=
  (unifyTotal first).bind fun initial =>
    (unifyTotal (initial.applyEqs second)).map fun final => final ∘ₛ initial

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
theorem unifies_applyEqs (first second : Subst σ)
    (equations : List (Term σ × Term σ)) :
    Unifies second (first.applyEqs equations) ↔
      Unifies (second ∘ₛ first) equations := by
  constructor
  · intro solves pair member
    rcases pair with ⟨left, right⟩
    simpa only [Subst.applyTerm_comp] using
      solves _ (List.mem_map.mpr ⟨(left, right), member, rfl⟩)
  · intro solves pair member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    rcases original with ⟨left, right⟩
    simpa only [Subst.applyTerm_comp] using solves (left, right) present

theorem sequential_sound (first second : List (Term σ × Term σ))
    (theta : Subst σ) (accepted : sequential first second = some theta) :
    Unifies theta (first ++ second) := by
  unfold sequential at accepted
  cases left : unifyTotal first with
  | none => simp [left] at accepted
  | some initial =>
      cases right : unifyTotal (initial.applyEqs second) with
      | none => simp [left, right] at accepted
      | some final =>
          simp only [left, right, Option.bind_some, Option.map_some,
            Option.some.injEq] at accepted
          subst theta
          intro pair member
          rcases List.mem_append.mp member with inFirst | inSecond
          · exact unifies_refinement first initial final
              (unifyTotal_sound first initial left) pair inFirst
          · exact (unifies_applyEqs initial final second).mp
              (unifyTotal_sound _ _ right) pair inSecond

theorem sequential_mgu (first second : List (Term σ × Term σ))
    (theta : Subst σ) (accepted : sequential first second = some theta)
    (candidate : Subst σ) (solves : Unifies candidate (first ++ second)) :
    theta.moreGeneral candidate := by
  unfold sequential at accepted
  cases left : unifyTotal first with
  | none => simp [left] at accepted
  | some initial =>
      cases right : unifyTotal (initial.applyEqs second) with
      | none => simp [left, right] at accepted
      | some final =>
          simp only [left, right, Option.bind_some, Option.map_some,
            Option.some.injEq] at accepted
          subst theta
          obtain ⟨middle, factors⟩ := unifyTotal_mgu first initial left candidate
            (fun pair member => solves pair (List.mem_append_left second member))
          have remaining : Unifies middle (initial.applyEqs second) := by
            apply (unifies_applyEqs initial middle second).mpr
            have equal : candidate = middle ∘ₛ initial := funext factors
            rw [← equal]
            exact fun pair member => solves pair (List.mem_append_right first member)
          obtain ⟨later, restFactors⟩ := unifyTotal_mgu _ final right middle remaining
          refine ⟨later, ?_⟩
          have equal : middle = later ∘ₛ final := funext restFactors
          intro name
          rw [factors name, equal, Subst.applyTerm_comp]
          rfl

theorem sequential_complete (first second : List (Term σ × Term σ))
    (candidate : Subst σ) (solves : Unifies candidate (first ++ second)) :
    ∃ theta, sequential first second = some theta := by
  obtain ⟨initial, left⟩ := unifyTotal_complete
    ⟨candidate, fun pair member => solves pair (List.mem_append_left second member)⟩
  obtain ⟨middle, factors⟩ := unifyTotal_mgu first initial left candidate
    (fun pair member => solves pair (List.mem_append_left second member))
  have remaining : Unifies middle (initial.applyEqs second) := by
    apply (unifies_applyEqs initial middle second).mpr
    have equal : candidate = middle ∘ₛ initial := funext factors
    rw [← equal]
    exact fun pair member => solves pair (List.mem_append_right first member)
  obtain ⟨final, right⟩ := unifyTotal_complete ⟨middle, remaining⟩
  exact ⟨final ∘ₛ initial, by simp [sequential, left, right]⟩

theorem sequential_publication_exact (first second : List (Term σ × Term σ))
    (observations : List (Term σ)) :
    publish (sequential first second) observations =
      publish (unifyTotal (first ++ second)) observations := by
  cases sequentialResult : sequential first second with
  | none =>
      have empty : unifyTotal (first ++ second) = none := by
        apply (unifyTotal_none_iff_not_unifiable _).mpr
        rintro ⟨candidate, solves⟩
        obtain ⟨theta, accepted⟩ := sequential_complete first second candidate solves
        rw [sequentialResult] at accepted
        cases accepted
      simp [publish, empty]
  | some theta =>
      obtain ⟨direct, accepted⟩ := unifyTotal_complete
        ⟨theta, sequential_sound first second theta sequentialResult⟩
      simp only [publish, accepted, Option.toList_some, List.map_cons, List.map_nil]
      congr 1
      rw [mgu_refinements_exact (first ++ second) theta
        (sequential_sound first second theta sequentialResult)
        (sequential_mgu first second theta sequentialResult)]
      exact (total_refinements_exact _ _ accepted observations).symm

theorem total_publication_congr
    (first second : List (Term σ × Term σ))
    (equivalent : ∀ theta, Unifies theta first ↔ Unifies theta second)
    (observations : List (Term σ)) :
    publish (unifyTotal first) observations = publish (unifyTotal second) observations := by
  cases left : unifyTotal first with
  | none =>
      have right : unifyTotal second = none := by
        apply (unifyTotal_none_iff_not_unifiable second).mpr
        rintro ⟨theta, solves⟩
        exact (unifyTotal_none_iff_not_unifiable first).mp left
          ⟨theta, (equivalent theta).mpr solves⟩
      simp [publish, right]
  | some theta =>
      obtain ⟨other, right⟩ := unifyTotal_complete
        ⟨theta, (equivalent theta).mp (unifyTotal_sound first theta left)⟩
      simp only [publish, right, Option.toList_some, List.map_cons, List.map_nil]
      congr 1
      rw [total_refinements_exact first theta left,
        total_refinements_exact second other right]
      ext values
      exact exists_congr fun candidate => and_congr (equivalent candidate) Iff.rfl

def earlyOutput (output : σ.vars) (result : Term σ)
    (equations : List (Term σ × Term σ)) : Option (Subst σ) :=
  unifyTotal ((result, .var output) :: equations)

def lateOutput (output : σ.vars) (result : Term σ)
    (equations : List (Term σ × Term σ)) : Option (Subst σ) :=
  sequential equations [(result, .var output)]

/-- Solving a fixed constraint alternative before publishing its output
preserves all subsequent refinements of every caller observation. -/
theorem output_publication_exact (output : σ.vars) (result : Term σ)
    (equations : List (Term σ × Term σ)) (observations : List (Term σ)) :
    publish (earlyOutput output result equations) observations =
      publish (lateOutput output result equations) observations := by
  unfold earlyOutput lateOutput
  rw [sequential_publication_exact]
  apply total_publication_congr
  intro theta
  simp only [Unifies, List.mem_cons, List.mem_append, List.not_mem_nil, or_false]
  constructor
  · intro solves pair member
    exact solves pair (member.symm)
  · intro solves pair member
    exact solves pair (member.symm)

/-- The source alternative inventory is preserved literally, including
duplicates and its order. Each surviving branch publishes the same family. -/
theorem ordered_output_publication_exact (output : σ.vars)
    (alternatives : List (Term σ × List (Term σ × Term σ)))
    (observations : List (Term σ)) :
    alternatives.flatMap (fun branch =>
      publish (earlyOutput output branch.1 branch.2) observations) =
    alternatives.flatMap (fun branch =>
      publish (lateOutput output branch.1 branch.2) observations) := by
  apply List.flatMap_congr
  intro branch _
  exact output_publication_exact output branch.1 branch.2 observations

omit [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
theorem independent_equations_unchanged (output : σ.vars) (result : Term σ)
    (equations : List (Term σ × Term σ))
    (independent : ∀ pair ∈ equations,
      pair.1.occursIn output = false ∧ pair.2.occursIn output = false) :
    (Subst.single output result).applyEqs equations = equations := by
  calc
    _ = equations.map id := by
      apply List.map_congr_left
      intro pair member
      rcases pair with ⟨left, right⟩
      simp only [Subst.single_applyTerm_not_occursIn output result left
        (independent (left, right) member).1,
        Subst.single_applyTerm_not_occursIn output result right
        (independent (left, right) member).2, id_eq]
    _ = equations := List.map_id equations

/-- A genuinely fresh output equation cannot reject an otherwise solvable
alternative. This uses freshness of the actual pending equations and result,
not merely freshness in an unrelated source template. -/
theorem independent_output_succeeds_iff (output : σ.vars) (result : Term σ)
    (equations : List (Term σ × Term σ))
    (resultIndependent : result.occursIn output = false)
    (independent : ∀ pair ∈ equations,
      pair.1.occursIn output = false ∧ pair.2.occursIn output = false) :
    (∃ theta, earlyOutput output result equations = some theta) ↔
      ∃ theta, unifyTotal equations = some theta := by
  constructor
  · rintro ⟨theta, accepted⟩
    apply unifyTotal_complete
    exact ⟨theta, fun pair member =>
      unifyTotal_sound _ theta accepted pair (List.mem_cons_of_mem _ member)⟩
  · rintro ⟨theta, accepted⟩
    apply unifyTotal_complete
    refine ⟨theta ∘ₛ Subst.single output result, ?_⟩
    intro pair member
    rcases List.mem_cons.mp member with rfl | later
    · change (theta ∘ₛ Subst.single output result).applyTerm result =
        (theta ∘ₛ Subst.single output result).applyTerm (.var output)
      rw [Subst.applyTerm_comp, Subst.applyTerm_comp]
      rw [Subst.single_applyTerm_not_occursIn output result result resultIndependent]
      simp [Subst.single]
    · apply (unifies_applyEqs (Subst.single output result) theta equations).mp
        _ pair later
      rw [independent_equations_unchanged output result equations independent]
      exact unifyTotal_sound equations theta accepted

omit [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
/-- Aliasing a private variable to an absent output name acts on the
pending term exactly as an invertible coordinate swap. The absence premise
is what prevents identifying two independently meaningful variables. -/
theorem private_alias_is_swap (privateName output : σ.vars) (term : Term σ)
    (outputAbsent : output ∉ term.freeVars) :
    (Subst.single privateName (.var output)).applyTerm term =
      UnificationRenaming.rename (Equiv.swap privateName output) term := by
  apply Subst.applyTerm_congr
  intro name member
  by_cases same : name = privateName
  · subst same
    simp [Subst.single, Equiv.swap_apply_left]
  · have notOutput : name ≠ output := fun equal => outputAbsent (equal ▸ member)
    simp [Subst.single, same, Equiv.swap_apply_of_ne_of_ne same notOutput]

/-- The initial actual matcher for a variable codomain produces precisely
the private alias covered by `private_alias_is_swap`. -/
theorem variable_output_match (privateName output : σ.vars)
    (different : privateName ≠ output) :
    unifyTotal (σ := σ) [(.var privateName, .var output)] =
      some (Subst.single privateName (.var output)) := by
  simp [unifyTotal, different, Subst.applyEqs, Subst.comp_id_left]

/-- The actual unifier cannot alter a subject whose variables are absent
from its constraint problem. This includes variable-kind tests performed
later by a procedural consumer. -/
theorem total_unifier_keeps_disjoint_subject
    (equations : List (Term σ × Term σ)) (subject : Term σ)
    (theta : Subst σ) (accepted : unifyTotal equations = some theta)
    (separate : Disjoint subject.freeVars (eqVars equations)) :
    theta.applyTerm subject = subject := by
  apply Subst.applyTerm_eq_self
  intro name member
  apply (unifyTotal_relevantIdempotent equations theta accepted).fixes
  exact fun occurs => Finset.disjoint_left.mp separate member occurs

/-- Fresh activation separates the codomain's variables from the subject;
an independent output name separates the remaining variable in the initial
result match. Together these facts license subject noninterference. -/
theorem output_match_keeps_independent_subject
    (output : σ.vars) (result subject : Term σ) (theta : Subst σ)
    (accepted : unifyTotal [(result, .var output)] = some theta)
    (resultSeparate : Disjoint subject.freeVars result.freeVars)
    (outputAbsent : output ∉ subject.freeVars) :
    theta.applyTerm subject = subject := by
  apply total_unifier_keeps_disjoint_subject _ _ theta accepted
  apply Finset.disjoint_left.mpr
  intro name member occurs
  simp only [eqVars, Term.freeVars, Finset.union_empty,
    Finset.mem_union, Finset.mem_singleton] at occurs
  rcases occurs with inResult | same
  · exact Finset.disjoint_left.mp resultSeparate member inResult
  · exact outputAbsent (same ▸ member)

namespace Coordinates

open UnificationRenaming

abbrev transport (names : σ.vars ≃ σ.vars) (theta : Subst σ) : Subst σ :=
  push names names.symm theta

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
theorem transport_id (names : σ.vars ≃ σ.vars) :
    transport names (Subst.id σ) = Subst.id σ := by
  funext name
  simp [transport, push, Subst.id]

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
theorem transport_comp (names : σ.vars ≃ σ.vars) (first second : Subst σ) :
    transport names (first ∘ₛ second) =
      transport names first ∘ₛ transport names second := by
  funext name
  exact (push_apply names names.symm names.symm_apply_apply first
    (second (names.symm name))).symm

omit [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
theorem transport_single (names : σ.vars ≃ σ.vars) (name : σ.vars) (term : Term σ) :
    transport names (Subst.single name term) =
      Subst.single (names name) (rename names term) := by
  funext other
  by_cases same : other = names name
  · subst other
    simp [transport, push, Subst.single]
  · have different : names.symm other ≠ name := by
      intro equal
      apply same
      simpa using congrArg names equal
    simp [transport, push, Subst.single, same, different]

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
theorem transport_applyEqs (names : σ.vars ≃ σ.vars) (theta : Subst σ)
    (problem : List (Term σ × Term σ)) :
    (transport names theta).applyEqs (equations names problem) =
      equations names (theta.applyEqs problem) := by
  simp only [Subst.applyEqs, equations, List.map_map]
  apply List.map_congr_left
  intro pair _
  rcases pair with ⟨left, right⟩
  simp only [Function.comp_apply,
    push_apply names names.symm names.symm_apply_apply]

omit [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
theorem occurs_rename (names : σ.vars ≃ σ.vars) (name : σ.vars) (term : Term σ) :
    (rename names term).occursIn (names name) = term.occursIn name := by
  induction term with
  | var other => simp [Term.occursIn]
  | const _ => rfl
  | app _ children ih => simp only [rename_app, Term.occursIn, ih]

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
theorem equations_pairs (names : σ.vars ≃ σ.vars) {arity : Nat}
    (left right : Fin arity → Term σ) :
    equations names (finPairsToList left right) =
      finPairsToList (fun i => rename names (left i)) (fun i => rename names (right i)) := by
  simp only [equations, finPairsToList, List.map_map, Function.comp_def]

omit [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
theorem elimination_equations (names : σ.vars ≃ σ.vars) (name : σ.vars)
    (term : Term σ) (problem : List (Term σ × Term σ)) :
    (Subst.single (names name) (rename names term)).applyEqs (equations names problem) =
      equations names ((Subst.single name term).applyEqs problem) := by
  rw [← transport_single, transport_applyEqs]

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
@[simp] theorem equations_cons (names : σ.vars → σ.vars)
    (pair : Term σ × Term σ) (rest : List (Term σ × Term σ)) :
    equations names (pair :: rest) =
      (rename names pair.1, rename names pair.2) :: equations names rest := rfl

/-- Coordinate transport preserves the chosen unifier, including its alias
orientation, rather than merely preserving existence of a solution. -/
theorem fuel_equivariant (names : σ.vars ≃ σ.vars) (fuel : Nat)
    (problem : List (Term σ × Term σ)) :
    unifyFuel fuel (equations names problem) =
      (unifyFuel fuel problem).map (transport names) := by
  induction fuel generalizing problem with
  | zero => simp only [unifyFuel, Option.map_none]
  | succ fuel ih =>
      cases problem with
      | nil => simp [equations, unifyFuel, transport_id]
      | cons pair rest =>
          have eliminate (name : σ.vars) (term : Term σ) :
              (match unifyFuel fuel
                ((Subst.single (names name) (rename names term)).applyEqs
                  (equations names rest)) with
              | none => none
              | some theta => some
                  (theta ∘ₛ Subst.single (names name) (rename names term))) =
              (match unifyFuel fuel ((Subst.single name term).applyEqs rest) with
              | none => none
              | some theta => some (theta ∘ₛ Subst.single name term)).map
                (transport names) := by
            rw [elimination_equations, ih]
            cases unifyFuel fuel ((Subst.single name term).applyEqs rest) <;>
              simp only [Option.map_none, Option.map_some, transport_comp, transport_single]
          rcases pair with ⟨left, right⟩
          cases left with
          | var name =>
              cases right with
              | var other =>
                  by_cases same : name = other
                  · subst other
                    simpa only [equations_cons, rename_var, unifyFuel, ↓reduceIte] using ih rest
                  · have step := eliminate name (.var other)
                    simp only [equations_cons, rename_var, unifyFuel,
                      Equiv.apply_eq_iff_eq, same, ↓reduceIte]
                    cases firstResult : unifyFuel fuel ((Subst.single name (Term.var other)).applyEqs rest) <;>
                      cases secondResult : unifyFuel fuel ((Subst.single (names name) (Term.var (names other))).applyEqs
                        (equations names rest)) <;> simpa only [rename_var, firstResult, secondResult] using step
              | const constant =>
                  have step := eliminate name (.const constant)
                  simp only [equations_cons, rename_var, rename_const, unifyFuel,
                    Term.occursIn, Bool.false_eq_true, ↓reduceIte]
                  cases firstResult : unifyFuel fuel ((Subst.single name (Term.const constant)).applyEqs rest) <;>
                    cases secondResult : unifyFuel fuel ((Subst.single (names name) (Term.const constant)).applyEqs
                      (equations names rest)) <;> simpa only [rename_const, firstResult, secondResult] using step
              | app function children =>
                  have occurs := occurs_rename names name (.app function children)
                  simp only [rename_app] at occurs
                  by_cases present : (Term.app function children).occursIn name = true
                  · simp only [equations_cons, rename_var, rename_app, unifyFuel,
                      occurs, present, ↓reduceIte, Option.map_none]
                  · have step := eliminate name (.app function children)
                    simp only [equations_cons, rename_var, rename_app, unifyFuel,
                      occurs, present, Bool.false_eq_true, ↓reduceIte]
                    cases firstResult : unifyFuel fuel ((Subst.single name (Term.app function children)).applyEqs rest) <;>
                      cases secondResult : unifyFuel fuel
                        ((Subst.single (names name) (Term.app function fun i => rename names (children i))).applyEqs
                          (equations names rest)) <;> simpa only [rename_app, firstResult, secondResult] using step
          | const constant =>
              cases right with
              | var name =>
                  have step := eliminate name (.const constant)
                  simp only [equations_cons, rename_var, rename_const, unifyFuel,
                    Term.occursIn, Bool.false_eq_true, ↓reduceIte]
                  cases firstResult : unifyFuel fuel ((Subst.single name (Term.const constant)).applyEqs rest) <;>
                    cases secondResult : unifyFuel fuel ((Subst.single (names name) (Term.const constant)).applyEqs
                      (equations names rest)) <;> simpa only [rename_const, firstResult, secondResult] using step
              | const other =>
                  by_cases same : constant = other <;>
                    simp only [equations_cons, rename_const, unifyFuel, same,
                      ↓reduceIte, Option.map_none, ih]
              | app _ _ => simp only [equations_cons, rename_const, rename_app,
                  unifyFuel, Option.map_none]
          | app function children =>
              cases right with
              | var name =>
                  have occurs := occurs_rename names name (.app function children)
                  simp only [rename_app] at occurs
                  by_cases present : (Term.app function children).occursIn name = true
                  · simp only [equations_cons, rename_var, rename_app, unifyFuel,
                      occurs, present, ↓reduceIte, Option.map_none]
                  · have step := eliminate name (.app function children)
                    simp only [equations_cons, rename_var, rename_app, unifyFuel,
                      occurs, present, Bool.false_eq_true, ↓reduceIte]
                    cases firstResult : unifyFuel fuel ((Subst.single name (Term.app function children)).applyEqs rest) <;>
                      cases secondResult : unifyFuel fuel
                        ((Subst.single (names name) (Term.app function fun i => rename names (children i))).applyEqs
                          (equations names rest)) <;> simpa only [rename_app, firstResult, secondResult] using step
              | const _ => simp only [equations_cons, rename_const, rename_app,
                  unifyFuel, Option.map_none]
              | app other terms =>
                  by_cases same : function = other
                  · subst other
                    simp only [equations_cons, rename_app, unifyFuel, ↓reduceDIte]
                    have mapped := ih (finPairsToList children terms ++ rest)
                    simpa only [equations, List.map_append, ← equations_pairs] using mapped
                  · simp only [equations_cons, rename_app, unifyFuel, same,
                      ↓reduceDIte, Option.map_none]

/-- Every successful finite run is the chosen total-unifier result. -/
theorem fuel_agrees_total (fuel : Nat) (problem : List (Term σ × Term σ))
    (theta : Subst σ) (accepted : unifyFuel fuel problem = some theta) :
    unifyTotal problem = some theta := by
  induction fuel generalizing problem theta with
  | zero => simp [unifyFuel] at accepted
  | succ fuel ih =>
      cases problem with
      | nil => simpa only [unifyFuel, unifyTotal] using accepted
      | cons pair rest =>
          rcases pair with ⟨left, right⟩
          cases left <;> cases right <;> simp only [unifyFuel] at accepted
          all_goals try contradiction
          all_goals split at accepted <;> try simp at accepted
          all_goals try
            rename_i equality
            subst equality
            simpa only [unifyTotal, ↓reduceIte, ↓reduceDIte] using ih _ _ accepted
          all_goals try
            split at accepted <;> try simp at accepted
          all_goals try
            rename_i childResult childAccepted
            subst theta
            have total := ih _ _ childAccepted
            simp_all only [unifyTotal, Bool.false_eq_true, ↓reduceIte]

/-- The resource-independent matcher has the same exact coordinate law. -/
theorem total_equivariant (names : σ.vars ≃ σ.vars)
    (problem : List (Term σ × Term σ)) :
    unifyTotal (equations names problem) =
      (unifyTotal problem).map (transport names) := by
  cases result : unifyTotal problem with
  | none =>
      simpa only [Option.map_none] using
        (rejection_iff names names.symm names.symm_apply_apply problem).mpr result
  | some theta =>
      obtain ⟨fuel, accepted⟩ := unifyTotal_success_has_fuel problem theta result
      have transported : unifyFuel fuel (equations names problem) =
          some (transport names theta) := by
        rw [fuel_equivariant, accepted, Option.map_some]
      exact fuel_agrees_total fuel _ _ transported

end Coordinates

namespace Controls

abbrev signature : LPSignature where
  constants := String
  vars := Nat
  relationSymbols := Unit
  relationArity _ := 0
  functionSymbols := Nat
  functionArity := id

def aliasConstraints : List (Term signature × Term signature) := [(.var 1, .var 2)]

theorem early_alias_direction :
    (earlyOutput (σ := signature) 0 (.var 1) aliasConstraints).map (fun theta => theta 0) =
      some (.var 2) := by
  simp [earlyOutput, aliasConstraints, unifyTotal, Subst.applyEqs,
    Subst.applyTerm, Subst.single, Subst.comp, Subst.id]

theorem late_alias_direction :
    (lateOutput (σ := signature) 0 (.var 1) aliasConstraints).map (fun theta => theta 0) =
      some (.var 0) := by
  simp [lateOutput, sequential, aliasConstraints, unifyTotal, Subst.applyEqs,
    Subst.applyTerm, Subst.single, Subst.comp, Subst.id]

theorem alias_directions_have_same_public_refinements :
    publish (earlyOutput (σ := signature) 0 (.var 1) aliasConstraints) [.var 0, .var 1, .var 2] =
      publish (lateOutput (σ := signature) 0 (.var 1) aliasConstraints) [.var 0, .var 1, .var 2] :=
  output_publication_exact _ _ _ _

theorem shared_output_can_reject :
    (unifyTotal [((.var 0 : Term signature), .const "Number")]).isSome = true ∧
      earlyOutput (σ := signature) 0 (.const "Bool") [(.var 0, .const "Number")] = none := by
  simp [earlyOutput, unifyTotal, Subst.applyEqs, Subst.applyTerm,
    Subst.single, Subst.id, Term.occursIn]

end Controls

end Mettapedia.Logic.LP.IndependentOutputUnification
