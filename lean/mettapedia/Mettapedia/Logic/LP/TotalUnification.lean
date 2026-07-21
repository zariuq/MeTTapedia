import Mettapedia.Logic.LP.MMMeasure
import Mettapedia.Logic.LP.UnificationComplete

/-!
# Total Martelli--Montanari unification

`unifyFuel` deliberately uses `none` for both logical failure and exhausted
fuel.  That is appropriate for bounded search, but it is not an honest
admission boundary: a compiler must not turn an exhausted internal budget into
language rejection.  This module runs the same rules by well-founded recursion
on the already-proved Martelli--Montanari lexicographic measure.  Consequently
`none` here is a genuine conflict or occurs-check failure, never incompleteness.
-/

namespace Mettapedia.Logic.LP

private theorem mmMeasure_lt_of_var_le_size_lt
    {σ : LPSignature} [DecidableEq σ.vars]
    {newEqs oldEqs : List (Term σ × Term σ)}
    (variableBound : mmVarCount newEqs ≤ mmVarCount oldEqs)
    (size : mmSize newEqs < mmSize oldEqs) :
    Prod.Lex (· < ·) (· < ·) (mmMeasure newEqs) (mmMeasure oldEqs) := by
  unfold mmMeasure
  by_cases equal : mmVarCount newEqs = mmVarCount oldEqs
  · rw [equal]
    exact .right _ size
  · exact .left _ _ (Nat.lt_of_le_of_ne variableBound equal)

private theorem mmVarCount_swap_head
    {σ : LPSignature} [DecidableEq σ.vars]
    (left right : Term σ) (rest : List (Term σ × Term σ)) :
    mmVarCount ((left, right) :: rest) =
      mmVarCount ((right, left) :: rest) := by
  simp [mmVarCount, eqVars, Finset.union_comm]

private theorem mmMeasure_delete_var_lt
    {σ : LPSignature} [DecidableEq σ.vars]
    (v : σ.vars) (rest : List (Term σ × Term σ)) :
    Prod.Lex (· < ·) (· < ·) (mmMeasure rest)
      (mmMeasure ((.var v, .var v) :: rest)) :=
  mmMeasure_lt_of_var_le_size_lt
    (mmVarCount_cons_ge (.var v) (.var v) rest)
    (mmSize_var_eq_lt v rest)

private theorem mmMeasure_delete_const_lt
    {σ : LPSignature} [DecidableEq σ.vars]
    (constant : σ.constants) (rest : List (Term σ × Term σ)) :
    Prod.Lex (· < ·) (· < ·) (mmMeasure rest)
      (mmMeasure ((.const constant, .const constant) :: rest)) :=
  mmMeasure_lt_of_var_le_size_lt
    (mmVarCount_cons_ge (.const constant) (.const constant) rest)
    (mmSize_const_eq_lt constant rest)

private theorem mmMeasure_eliminate_lt
    {σ : LPSignature} [DecidableEq σ.vars]
    (v : σ.vars) (term : Term σ) (rest : List (Term σ × Term σ))
    (notOccurs : term.occursIn v = false) :
    Prod.Lex (· < ·) (· < ·)
      (mmMeasure ((Subst.single v term).applyEqs rest))
      (mmMeasure ((.var v, term) :: rest)) :=
  .left _ _ (mmVarCount_eliminate_lt v term rest notOccurs)

private theorem mmMeasure_eliminate_swapped_lt
    {σ : LPSignature} [DecidableEq σ.vars]
    (v : σ.vars) (term : Term σ) (rest : List (Term σ × Term σ))
    (notOccurs : term.occursIn v = false) :
    Prod.Lex (· < ·) (· < ·)
      (mmMeasure ((Subst.single v term).applyEqs rest))
      (mmMeasure ((term, .var v) :: rest)) := by
  have oldMeasure : mmMeasure ((term, .var v) :: rest) =
      mmMeasure ((.var v, term) :: rest) := by
    unfold mmMeasure
    apply Prod.ext
    · exact mmVarCount_swap_head term (.var v) rest
    · simp [mmSize, Nat.add_comm]
  rw [oldMeasure]
  exact .left _ _ (mmVarCount_eliminate_lt v term rest notOccurs)

private theorem mmMeasure_decompose_lt
    {σ : LPSignature} [DecidableEq σ.vars]
    (function : σ.functionSymbols)
    (left right : Fin (σ.functionArity function) → Term σ)
    (rest : List (Term σ × Term σ)) :
    Prod.Lex (· < ·) (· < ·)
      (mmMeasure (finPairsToList left right ++ rest))
      (mmMeasure ((.app function left, .app function right) :: rest)) :=
  mmMeasure_lt_of_var_le_size_lt
    (mmVarCount_app_eq_decompose_le function left right rest)
    (mmSize_app_eq_decompose_lt function left right rest)

/-- Total occurs-checked first-order unification.  The result has no resource
failure case: recursion is justified by the Martelli--Montanari measure. -/
def unifyTotal {σ : LPSignature} [DecidableEq σ.vars]
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] :
    List (Term σ × Term σ) → Option (Subst σ)
  | [] => some (Subst.id σ)
  | (source, target) :: rest =>
      match source with
      | .var v =>
          match target with
          | .var other =>
              if v = other then
                unifyTotal rest
              else
                match unifyTotal
                    ((Subst.single v (.var other)).applyEqs rest) with
                | none => none
                | some substitution =>
                    some (substitution ∘ₛ Subst.single v (.var other))
          | term =>
              if term.occursIn v then none
              else
                match unifyTotal ((Subst.single v term).applyEqs rest) with
                | none => none
                | some substitution =>
                    some (substitution ∘ₛ Subst.single v term)
      | .const constant =>
          match target with
          | .var v =>
              match unifyTotal
                  ((Subst.single v (.const constant)).applyEqs rest) with
              | none => none
              | some substitution =>
                  some (substitution ∘ₛ Subst.single v (.const constant))
          | .const other =>
              if constant = other then unifyTotal rest else none
          | .app _ _ => none
      | .app function arguments =>
          match target with
          | .var v =>
              if (Term.app function arguments).occursIn v then none
              else
                match unifyTotal
                    ((Subst.single v (.app function arguments)).applyEqs rest) with
                | none => none
                | some substitution =>
                    some (substitution ∘ₛ
                      Subst.single v (.app function arguments))
          | .const _ => none
          | .app other otherArguments =>
              if equal : function = other then
                unifyTotal (finPairsToList arguments
                  (equal ▸ otherArguments) ++ rest)
              else none
termination_by equations => mmMeasure equations
decreasing_by
  · subst other
    exact mmMeasure_delete_var_lt v rest
  · exact mmMeasure_eliminate_lt v (.var other) rest (by
      simp_all [Term.occursIn])
  · exact mmMeasure_eliminate_lt v term rest (by
      simpa using ‹¬term.occursIn v = true›)
  · exact mmMeasure_eliminate_swapped_lt v (.const constant) rest (by
      simp [Term.occursIn])
  · exact mmMeasure_delete_const_lt constant rest
  · exact mmMeasure_eliminate_swapped_lt v
      (.app function arguments) rest (by
        simpa using ‹¬(Term.app function arguments).occursIn v = true›)
  · subst other
    exact mmMeasure_decompose_lt function arguments otherArguments rest

/-- A total-unifier success is exactly an ordinary Martelli--Montanari run at
some finite fuel.  This connects the well-founded implementation to the
existing soundness and MGU theorems without adding a second semantics. -/
theorem unifyTotal_success_has_fuel {σ : LPSignature} [DecidableEq σ.vars]
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (equations : List (Term σ × Term σ)) (theta : Subst σ)
    (accepted : unifyTotal equations = some theta) :
    ∃ fuel, unifyFuel fuel equations = some theta := by
  fun_induction unifyTotal equations generalizing theta with
  | case1 =>
      simp at accepted
      subst theta
      exact ⟨1, by simp [unifyFuel]⟩
  | case2 rest other inductionHypothesis =>
      obtain ⟨fuel, childAccepted⟩ := inductionHypothesis theta accepted
      exact ⟨fuel + 1, by simpa [unifyFuel] using childAccepted⟩
  | case3 rest v other notEqual childResult inductionHypothesis =>
      simp at accepted
  | case4 rest v other notEqual childTheta childResult inductionHypothesis =>
      simp at accepted
      subst theta
      obtain ⟨fuel, childAccepted⟩ :=
        inductionHypothesis childTheta childResult
      exact ⟨fuel + 1, by simp [unifyFuel, notEqual, childAccepted]⟩
  | case5 rest v term notVariable occurs =>
      simp at accepted
  | case6 rest v term notVariable notOccurs childResult inductionHypothesis =>
      simp at accepted
  | case7 rest v term notVariable notOccurs childTheta childResult
      inductionHypothesis =>
      simp at accepted
      subst theta
      obtain ⟨fuel, childAccepted⟩ :=
        inductionHypothesis childTheta childResult
      have occursFalse : term.occursIn v = false := by
        cases result : term.occursIn v <;> simp_all
      exact ⟨fuel + 1, by simp [unifyFuel, occursFalse, childAccepted]⟩
  | case8 rest constant v childResult inductionHypothesis =>
      simp at accepted
  | case9 rest constant v childTheta childResult inductionHypothesis =>
      simp at accepted
      subst theta
      obtain ⟨fuel, childAccepted⟩ :=
        inductionHypothesis childTheta childResult
      have occursFalse : (Term.const constant).occursIn v = false := by
        simp [Term.occursIn]
      exact ⟨fuel + 1, by
        simp [unifyFuel, occursFalse, childAccepted]⟩
  | case10 rest constant inductionHypothesis =>
      obtain ⟨fuel, childAccepted⟩ := inductionHypothesis theta accepted
      exact ⟨fuel + 1, by simpa [unifyFuel] using childAccepted⟩
  | case11 rest left right notEqual => simp at accepted
  | case12 rest constant function arguments => simp at accepted
  | case13 rest function arguments v occurs => simp at accepted
  | case14 rest function arguments v notOccurs childResult
      inductionHypothesis =>
      simp at accepted
  | case15 rest function arguments v notOccurs childTheta childResult
      inductionHypothesis =>
      simp at accepted
      subst theta
      obtain ⟨fuel, childAccepted⟩ :=
        inductionHypothesis childTheta childResult
      have occursFalse : (Term.app function arguments).occursIn v = false := by
        cases result : (Term.app function arguments).occursIn v <;> simp_all
      exact ⟨fuel + 1, by simp [unifyFuel, occursFalse, childAccepted]⟩
  | case16 rest function arguments constant => simp at accepted
  | case17 rest function right left inductionHypothesis =>
      obtain ⟨fuel, childAccepted⟩ := inductionHypothesis theta accepted
      exact ⟨fuel + 1, by simpa [unifyFuel] using childAccepted⟩
  | case18 rest leftFunction leftArguments rightFunction rightArguments
      notEqual =>
      simp at accepted

theorem unifyTotal_sound {σ : LPSignature} [DecidableEq σ.vars]
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (equations : List (Term σ × Term σ)) (theta : Subst σ)
    (accepted : unifyTotal equations = some theta) :
    Unifies theta equations := by
  obtain ⟨fuel, fuelAccepted⟩ :=
    unifyTotal_success_has_fuel equations theta accepted
  exact unifyFuel_sound fuel equations theta fuelAccepted

theorem unifyTotal_mgu {σ : LPSignature} [DecidableEq σ.vars]
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (equations : List (Term σ × Term σ)) (theta : Subst σ)
    (accepted : unifyTotal equations = some theta)
    (candidate : Subst σ) (unifies : Unifies candidate equations) :
    theta.moreGeneral candidate := by
  obtain ⟨fuel, fuelAccepted⟩ :=
    unifyTotal_success_has_fuel equations theta accepted
  exact unifyFuel_mgu fuel equations theta fuelAccepted candidate unifies

theorem unifyTotal_complete {σ : LPSignature} [DecidableEq σ.vars]
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    {equations : List (Term σ × Term σ)}
    (unifiable : ∃ delta : Subst σ, Unifies delta equations) :
    ∃ theta, unifyTotal equations = some theta := by
  have derives := unifies_to_derives (eqs := equations) unifiable
  induction derives with
  | nil => exact ⟨Subst.id σ, by simp [unifyTotal]⟩
  | var_eq v rest child inductionHypothesis =>
      obtain ⟨theta, accepted⟩ :=
        inductionHypothesis (unifiable_of_derives child)
      exact ⟨theta, by simpa [unifyTotal] using accepted⟩
  | var_subst v term rest notOccurs child inductionHypothesis =>
      obtain ⟨theta, accepted⟩ :=
        inductionHypothesis (unifiable_of_derives child)
      cases term with
      | var other =>
          have notEqual : v ≠ other := by
            intro equal
            subst other
            simp [Term.occursIn] at notOccurs
          exact ⟨theta ∘ₛ Subst.single v (.var other), by
            simp [unifyTotal, notEqual, accepted]⟩
      | const constant =>
          exact ⟨theta ∘ₛ Subst.single v (.const constant), by
            simp [unifyTotal, notOccurs, accepted]⟩
      | app function arguments =>
          exact ⟨theta ∘ₛ Subst.single v (.app function arguments), by
            simp [unifyTotal, notOccurs, accepted]⟩
  | const_eq constant rest child inductionHypothesis =>
      obtain ⟨theta, accepted⟩ :=
        inductionHypothesis (unifiable_of_derives child)
      exact ⟨theta, by simpa [unifyTotal] using accepted⟩
  | const_var constant v rest child inductionHypothesis =>
      obtain ⟨theta, accepted⟩ :=
        inductionHypothesis (unifiable_of_derives child)
      exact ⟨theta ∘ₛ Subst.single v (.const constant), by
        simp [unifyTotal, accepted]⟩
  | app_var function arguments v rest notOccurs child inductionHypothesis =>
      obtain ⟨theta, accepted⟩ :=
        inductionHypothesis (unifiable_of_derives child)
      exact ⟨theta ∘ₛ Subst.single v (.app function arguments), by
        simp [unifyTotal, notOccurs, accepted]⟩
  | app_eq function left right rest child inductionHypothesis =>
      obtain ⟨theta, accepted⟩ :=
        inductionHypothesis (unifiable_of_derives child)
      exact ⟨theta, by simpa [unifyTotal] using accepted⟩

/-- `none` from the total unifier is a proved logical failure, never exhausted
fuel. -/
theorem unifyTotal_none_iff_not_unifiable {σ : LPSignature}
    [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols]
    (equations : List (Term σ × Term σ)) :
    unifyTotal equations = none ↔
      ¬∃ theta : Subst σ, Unifies theta equations := by
  constructor
  · intro rejected unifiable
    obtain ⟨theta, accepted⟩ := unifyTotal_complete unifiable
    rw [rejected] at accepted
    contradiction
  · intro notUnifiable
    cases result : unifyTotal equations with
    | none => rfl
    | some theta =>
        exact False.elim <| notUnifiable
          ⟨theta, unifyTotal_sound equations theta result⟩

def unifyAtomsTotal {σ : LPSignature} [DecidableEq σ.vars]
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    [DecidableEq σ.relationSymbols]
    (left right : Atom σ) : Option (Subst σ) :=
  if equal : left.symbol = right.symbol then
    unifyTotal (finPairsToList left.args (equal ▸ right.args))
  else none

theorem unifyAtomsTotal_sound {σ : LPSignature} [DecidableEq σ.vars]
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    [DecidableEq σ.relationSymbols]
    (left right : Atom σ) (theta : Subst σ)
    (accepted : unifyAtomsTotal left right = some theta) :
    theta.applyAtom left = theta.applyAtom right := by
  obtain ⟨leftSymbol, leftArguments⟩ := left
  obtain ⟨rightSymbol, rightArguments⟩ := right
  unfold unifyAtomsTotal at accepted
  split at accepted
  next equal =>
    dsimp only at equal accepted
    subst rightSymbol
    have equations := unifyTotal_sound _ theta accepted
    simp [Subst.applyAtom]
    funext index
    apply equations (leftArguments index, rightArguments index)
    rw [finPairsToList]
    exact List.mem_map.mpr ⟨index, List.mem_finRange index, rfl⟩
  next mismatch => simp at accepted

theorem unifyAtomsTotal_complete {σ : LPSignature} [DecidableEq σ.vars]
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    [DecidableEq σ.relationSymbols]
    (left right : Atom σ)
    (unifiable : ∃ candidate : Subst σ,
      candidate.applyAtom left = candidate.applyAtom right) :
    ∃ theta, unifyAtomsTotal left right = some theta := by
  obtain ⟨leftSymbol, leftArguments⟩ := left
  obtain ⟨rightSymbol, rightArguments⟩ := right
  obtain ⟨candidate, candidateUnifies⟩ := unifiable
  have symbolEq : leftSymbol = rightSymbol := by
    simpa [Subst.applyAtom] using
      congrArg Atom.symbol candidateUnifies
  subst rightSymbol
  have argumentsUnify : ∀ index,
      candidate.applyTerm (leftArguments index) =
        candidate.applyTerm (rightArguments index) := by
    have atoms := candidateUnifies
    simp only [Subst.applyAtom, Atom.mk.injEq, heq_eq_eq, true_and] at atoms
    exact fun index => congrFun atoms index
  unfold unifyAtomsTotal
  split
  next equal =>
    apply unifyTotal_complete
    exact ⟨candidate, by
      intro equation member
      simp only [finPairsToList, List.mem_map, List.mem_finRange,
        true_and] at member
      obtain ⟨index, rfl⟩ := member
      simpa using argumentsUnify index⟩
  next mismatch => contradiction

theorem unifyAtomsTotal_mgu {σ : LPSignature} [DecidableEq σ.vars]
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    [DecidableEq σ.relationSymbols]
    (left right : Atom σ) (theta : Subst σ)
    (accepted : unifyAtomsTotal left right = some theta)
    (candidate : Subst σ)
    (candidateUnifies : candidate.applyAtom left = candidate.applyAtom right) :
    theta.moreGeneral candidate := by
  obtain ⟨leftSymbol, leftArguments⟩ := left
  obtain ⟨rightSymbol, rightArguments⟩ := right
  unfold unifyAtomsTotal at accepted
  split at accepted
  next equal =>
    dsimp only at equal accepted
    subst rightSymbol
    have argumentsUnify : ∀ index,
        candidate.applyTerm (leftArguments index) =
          candidate.applyTerm (rightArguments index) := by
      have atoms := candidateUnifies
      simp only [Subst.applyAtom, Atom.mk.injEq, heq_eq_eq, true_and] at atoms
      exact fun index => congrFun atoms index
    apply unifyTotal_mgu _ theta accepted candidate
    intro equation member
    simp only [finPairsToList, List.mem_map, List.mem_finRange,
      true_and] at member
    obtain ⟨index, rfl⟩ := member
    simpa using argumentsUnify index
  next mismatch => simp at accepted

theorem unifyAtomsTotal_none_iff_not_unifiable {σ : LPSignature}
    [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (left right : Atom σ) :
    unifyAtomsTotal left right = none ↔
      ¬∃ theta : Subst σ, theta.applyAtom left = theta.applyAtom right := by
  constructor
  · intro rejected unifiable
    obtain ⟨theta, accepted⟩ := unifyAtomsTotal_complete left right unifiable
    rw [rejected] at accepted
    contradiction
  · intro notUnifiable
    cases result : unifyAtomsTotal left right with
    | none => rfl
    | some theta =>
        exact False.elim <| notUnifiable
          ⟨theta, unifyAtomsTotal_sound left right theta result⟩

end Mettapedia.Logic.LP
