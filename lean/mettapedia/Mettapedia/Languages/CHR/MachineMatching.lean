import Mettapedia.Languages.CHR.Machine

/-! Matching laws of the refined CHR machine. Matching only adds bindings for
unbound variables, and the head then instantiates to the matched value.
Conversely, any environment that extends the current one and instantiates a
head to a value is reached by matching that head against that value.
Instantiation and evaluation depend on an environment only through `lookup`. -/

set_option autoImplicit false

namespace Mettapedia.Languages.CHR.Machine

/-- `later` keeps every binding of `earlier`. -/
def Extends (later earlier : Environment) : Prop :=
  ∀ index value, lookup earlier index = some value → lookup later index = some value

theorem Extends.refl (environment : Environment) : Extends environment environment :=
  fun _ _ bound => bound

theorem Extends.trans {first second third : Environment}
    (outer : Extends first second) (inner : Extends second third) : Extends first third :=
  fun index value bound => outer index value (inner index value bound)

theorem lookup_cons (environment : Environment) (index : Nat) (value : Value) (other : Nat) :
    lookup ((index, value) :: environment) other =
      if index = other then some value else lookup environment other := by
  by_cases same : index = other
  · subst same
    simp [lookup]
  · have different : (index == other) = false := by simpa using same
    simp [lookup, different, same]

theorem extends_cons {environment : Environment} {index : Nat} (value : Value)
    (unbound : lookup environment index = none) : Extends ((index, value) :: environment) environment := by
  intro other bound present
  rw [lookup_cons]
  by_cases same : index = other
  · subst same
    rw [unbound] at present
    cases present
  · simp [same, present]

/-! ## Instantiation is monotone in the environment -/

mutual
  theorem instantiateTerm_extends {earlier later : Environment} (grown : Extends later earlier) :
      (term : Term) → (value : Value) → instantiateTerm earlier term = some value →
        instantiateTerm later term = some value
    | .value datum, value, instantiated => by simpa [instantiateTerm] using instantiated
    | .var index, value, instantiated => grown index value (by simpa [instantiateTerm] using instantiated)
    | .tuple terms, value, instantiated => by
      simp only [instantiateTerm] at instantiated ⊢
      cases values : instantiateTerms earlier terms with
      | none => rw [values] at instantiated; cases instantiated
      | some fields =>
        rw [values] at instantiated
        rw [instantiateTerms_extends grown terms fields values]
        exact instantiated
  theorem instantiateTerms_extends {earlier later : Environment} (grown : Extends later earlier) :
      (terms : List Term) → (values : List Value) → instantiateTerms earlier terms = some values →
        instantiateTerms later terms = some values
    | [], values, instantiated => by simpa [instantiateTerms] using instantiated
    | term :: rest, values, instantiated => by
      simp only [instantiateTerms] at instantiated ⊢
      cases first : instantiateTerm earlier term with
      | none => rw [first] at instantiated; cases instantiated
      | some value =>
        rw [first] at instantiated
        cases others : instantiateTerms earlier rest with
        | none => rw [others] at instantiated; cases instantiated
        | some fields =>
          rw [others] at instantiated
          rw [instantiateTerm_extends grown term value first, instantiateTerms_extends grown rest fields others]
          exact instantiated
end

/-! ## Soundness of matching -/

mutual
  theorem matchTerm_sound :
      (term : Term) → (value : Value) → (environment bound : Environment) →
        matchTerm term value environment = some bound →
        Extends bound environment ∧ instantiateTerm bound term = some value
    | .value datum, value, environment, bound, matched => by
      by_cases same : datum = value
      · subst same
        simp only [matchTerm, if_true, Option.some.injEq] at matched
        subst matched
        exact ⟨Extends.refl _, by simp [instantiateTerm]⟩
      · simp [matchTerm, same] at matched
    | .var index, value, environment, bound, matched => by
      cases present : lookup environment index with
      | none =>
        simp only [matchTerm, present, Option.some.injEq] at matched
        subst matched
        exact ⟨extends_cons value present, by simp [instantiateTerm, lookup_cons]⟩
      | some old =>
        by_cases same : old = value
        · subst same
          simp only [matchTerm, present, if_true, Option.some.injEq] at matched
          subst matched
          exact ⟨Extends.refl _, by simpa [instantiateTerm] using present⟩
        · simp [matchTerm, present, same] at matched
    | .tuple terms, .tuple fields, environment, bound, matched => by
      simp only [matchTerm] at matched
      obtain ⟨grown, instantiated⟩ := matchTerms_sound terms fields environment bound matched
      exact ⟨grown, by simp [instantiateTerm, instantiated]⟩
    | .tuple _, .integer _, _, _, matched => by simp [matchTerm] at matched
    | .tuple _, .atom _, _, _, matched => by simp [matchTerm] at matched
  theorem matchTerms_sound :
      (terms : List Term) → (values : List Value) → (environment bound : Environment) →
        matchTerms terms values environment = some bound →
        Extends bound environment ∧ instantiateTerms bound terms = some values
    | [], [], environment, bound, matched => by
      simp only [matchTerms, Option.some.injEq] at matched
      subst matched
      exact ⟨Extends.refl _, rfl⟩
    | [], _ :: _, _, _, matched => by simp [matchTerms] at matched
    | _ :: _, [], _, _, matched => by simp [matchTerms] at matched
    | term :: terms, value :: values, environment, bound, matched => by
      simp only [matchTerms] at matched
      cases first : matchTerm term value environment with
      | none => rw [first] at matched; cases matched
      | some middle =>
        rw [first] at matched
        obtain ⟨grownFirst, instantiatedFirst⟩ := matchTerm_sound term value environment middle first
        obtain ⟨grownRest, instantiatedRest⟩ := matchTerms_sound terms values middle bound matched
        refine ⟨Extends.trans grownRest grownFirst, ?_⟩
        simp [instantiateTerms, instantiateTerm_extends grownRest term value instantiatedFirst, instantiatedRest]
end

/-! ## Completeness of matching -/

mutual
  theorem matchTerm_complete :
      (term : Term) → (value : Value) → (environment target : Environment) →
        Extends target environment → instantiateTerm target term = some value →
        ∃ bound, matchTerm term value environment = some bound ∧ Extends target bound
    | .value datum, value, environment, target, grown, instantiated => by
      simp only [instantiateTerm, Option.some.injEq] at instantiated
      subst instantiated
      exact ⟨environment, by simp [matchTerm], grown⟩
    | .var index, value, environment, target, grown, instantiated => by
      simp only [instantiateTerm] at instantiated
      cases present : lookup environment index with
      | none =>
        refine ⟨(index, value) :: environment, by simp [matchTerm, present], ?_⟩
        intro other bound inside
        rw [lookup_cons] at inside
        by_cases same : index = other
        · subst same
          simp only [if_true, Option.some.injEq] at inside
          subst inside
          exact instantiated
        · simp only [same, if_false] at inside
          exact grown other bound inside
      | some old =>
        have agree := grown index old present
        rw [instantiated, Option.some.injEq] at agree
        subst agree
        exact ⟨environment, by simp [matchTerm, present], grown⟩
    | .tuple terms, value, environment, target, grown, instantiated => by
      simp only [instantiateTerm] at instantiated
      cases fields : instantiateTerms target terms with
      | none => rw [fields] at instantiated; cases instantiated
      | some fields' =>
        rw [fields, Option.some.injEq] at instantiated
        subst instantiated
        obtain ⟨bound, matched, covered⟩ := matchTerms_complete terms fields' environment target grown fields
        exact ⟨bound, by simpa [matchTerm] using matched, covered⟩
  theorem matchTerms_complete :
      (terms : List Term) → (values : List Value) → (environment target : Environment) →
        Extends target environment → instantiateTerms target terms = some values →
        ∃ bound, matchTerms terms values environment = some bound ∧ Extends target bound
    | [], values, environment, target, grown, instantiated => by
      simp only [instantiateTerms, Option.some.injEq] at instantiated
      subst instantiated
      exact ⟨environment, rfl, grown⟩
    | term :: rest, values, environment, target, grown, instantiated => by
      simp only [instantiateTerms] at instantiated
      cases first : instantiateTerm target term with
      | none => rw [first] at instantiated; cases instantiated
      | some value =>
        rw [first] at instantiated
        cases others : instantiateTerms target rest with
        | none => rw [others] at instantiated; cases instantiated
        | some fields =>
          rw [others, Option.some.injEq] at instantiated
          subst instantiated
          obtain ⟨middle, matchedFirst, coveredFirst⟩ :=
            matchTerm_complete term value environment target grown first
          obtain ⟨bound, matchedRest, coveredRest⟩ :=
            matchTerms_complete rest fields middle target coveredFirst others
          exact ⟨bound, by simp [matchTerms, matchedFirst, matchedRest], coveredRest⟩
end

/-! ## Dependence on `lookup` only -/

/-- Two environments with the same bindings. -/
def Agree (first second : Environment) : Prop := ∀ index, lookup first index = lookup second index

mutual
  theorem instantiateTerm_agree {first second : Environment} (same : Agree first second) :
      (term : Term) → instantiateTerm first term = instantiateTerm second term
    | .value _ => rfl
    | .var index => by simp [instantiateTerm, same index]
    | .tuple terms => by simp only [instantiateTerm, instantiateTerms_agree same terms]
  theorem instantiateTerms_agree {first second : Environment} (same : Agree first second) :
      (terms : List Term) → instantiateTerms first terms = instantiateTerms second terms
    | [] => rfl
    | term :: rest => by
      simp only [instantiateTerms, instantiateTerm_agree same term, instantiateTerms_agree same rest]
end

theorem instantiate_agree {first second : Environment} (same : Agree first second) (term : Term) :
    term.instantiate first = term.instantiate second := by
  rw [← instantiateTerm_eq, ← instantiateTerm_eq, instantiateTerm_agree same]

theorem eval_agree {first second : Environment} (same : Agree first second) :
    (expression : IntExpr) → expression.eval first = expression.eval second
  | .literal _ => rfl
  | .index index => by simp [IntExpr.eval, same index]
  | .operation operator left right => by
    simp only [IntExpr.eval, eval_agree same left, eval_agree same right]

theorem guard_agree {first second : Environment} (same : Agree first second) (guard : Guard) :
    guard.eval first = guard.eval second := by
  cases guard with
  | identical left right => simp only [Guard.eval, instantiate_agree same left, instantiate_agree same right]
  | distinct left right => simp only [Guard.eval, instantiate_agree same left, instantiate_agree same right]
  | compare operator left right => simp only [Guard.eval, eval_agree same left, eval_agree same right]

theorem guardsEval_agree {first second : Environment} (same : Agree first second) :
    (guards : List Guard) → guardsEval first guards = guardsEval second guards
  | [] => rfl
  | guard :: rest => by simp only [guardsEval, guard_agree same guard, guardsEval_agree same rest]

#print axioms matchTerms_sound
#print axioms matchTerms_complete
#print axioms guardsEval_agree

end Mettapedia.Languages.CHR.Machine
