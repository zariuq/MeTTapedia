import Mettapedia.Languages.MeTTa.PeTTa.UnifyingGround

/-!
# The unifier of `Unifying` is sound

When `unifyTerms` succeeds, the substitution it returns makes the two terms
equal: `resolve θ' a = resolve θ' b` (`unifyTerms_sound`). It also keeps the
substitution idempotent (no bound variable occurs in a bound value) and only
refines the substitution it started from (`Refines`): what was equal before
stays equal. Example: `(f $x 2)` and `(f 1 $y)` from no bindings give
`{$y ↦ 2, $x ↦ 1}`, under which both are `(f 1 2)`.

Completeness (enough fuel always suffices) and most-generality are not proved
here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Unifying

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst atomFreeVars)
open Mettapedia.Languages.ProcessCalculi

/-! ## Free variables -/

theorem mem_freeVars_expression {name : String} {items : List Atom} :
    name ∈ atomFreeVars (.expression items) ↔ ∃ item ∈ items, name ∈ atomFreeVars item := by
  simp only [MORK.atomFreeVars]
  induction items with
  | nil => simp [MORK.atomFreeVars.atomFreeVarsList]
  | cons first rest ih =>
      simp only [MORK.atomFreeVars.atomFreeVarsList, List.mem_append, ih, List.mem_cons,
        exists_eq_or_imp]

/-- A substitution is idempotent when no bound variable occurs in a bound value. -/
def Idempotent (bindings : Subst) : Prop :=
  ∀ name value, bindings.lookup name = some value →
    ∀ other ∈ atomFreeVars value, bindings.lookup other = none

/-- Every variable of the term is unbound. -/
def Unbound (bindings : Subst) (term : Atom) : Prop :=
  ∀ name ∈ atomFreeVars term, bindings.lookup name = none

theorem resolve_of_unbound {bindings : Subst} :
    ∀ term : Atom, Unbound bindings term → resolve bindings term = term
  | .var name, unbound => by
      simp [resolve, applySubst, unbound name (by simp [MORK.atomFreeVars])]
  | .symbol _, _ => rfl
  | .grounded _, _ => rfl
  | .expression items, unbound => by
      simp only [resolve, applySubst, Atom.expression.injEq]
      exact list items (fun item member name inItem =>
        unbound name (mem_freeVars_expression.mpr ⟨item, member, inItem⟩))
where
  list : ∀ items : List Atom, (∀ item ∈ items, Unbound bindings item) →
      applySubst.applySubstList bindings items = items
    | [], _ => rfl
    | first :: rest, unbound => by
        simp only [applySubst.applySubstList]
        rw [show applySubst bindings first = first from
          resolve_of_unbound first (unbound first List.mem_cons_self),
          list rest (fun item member => unbound item (List.mem_cons_of_mem _ member))]

/-- The variables of a resolved term are unbound. -/
theorem unbound_resolve {bindings : Subst} (idempotent : Idempotent bindings) :
    ∀ term : Atom, Unbound bindings (resolve bindings term)
  | .var name => by
      intro other inResolved
      cases found : bindings.lookup name with
      | none =>
          rw [resolve_var_free found] at inResolved
          simp only [MORK.atomFreeVars, List.mem_singleton] at inResolved
          subst inResolved; exact found
      | some value =>
          rw [resolve_var_bound found] at inResolved
          exact idempotent name value found other inResolved
  | .symbol _ => by intro other inResolved; simp [resolve, applySubst, MORK.atomFreeVars] at inResolved
  | .grounded _ => by intro other inResolved; simp [resolve, applySubst, MORK.atomFreeVars] at inResolved
  | .expression items => by
      intro other inResolved
      simp only [resolve, applySubst] at inResolved
      obtain ⟨item, member, inItem⟩ := mem_freeVars_expression.mp inResolved
      exact list items item member other inItem
where
  list : ∀ items : List Atom, ∀ item ∈ applySubst.applySubstList bindings items,
      ∀ other ∈ atomFreeVars item, bindings.lookup other = none
    | [], _, member, _, _ => by cases member
    | first :: rest, item, member, other, inItem => by
        simp only [applySubst.applySubstList, List.mem_cons] at member
        rcases member with same | member
        · subst same; exact unbound_resolve idempotent first other inItem
        · exact list rest item member other inItem

theorem resolve_idem {bindings : Subst} (idempotent : Idempotent bindings) (term : Atom) :
    resolve bindings (resolve bindings term) = resolve bindings term :=
  resolve_of_unbound _ (unbound_resolve idempotent term)

/-! ## Binding one variable -/

theorem lookup_bindVar_same (bindings : Subst) (name : String) (term : Atom) :
    (bindVar bindings name term).lookup name = some term := by
  simp [bindVar, MORK.Subst.lookup]

theorem lookup_map_values (bindings : Subst) (update : Atom → Atom) (name : String) :
    MORK.Subst.lookup (bindings.map fun binding => (binding.1, update binding.2)) name =
      (bindings.lookup name).map update := by
  induction bindings with
  | nil => rfl
  | cons first rest ih =>
      by_cases same : first.1 = name
      · simp [MORK.Subst.lookup, same]
      · have different : (first.1 == name) = false := by simpa using same
        simp only [MORK.Subst.lookup, List.map_cons, List.find?_cons, different] at ih ⊢
        exact ih

theorem lookup_bindVar_other {bindings : Subst} {name other : String} (term : Atom)
    (different : name ≠ other) :
    (bindVar bindings name term).lookup other =
      (bindings.lookup other).map (applySubst [(name, term)]) := by
  unfold bindVar
  rw [lookup_cons_ne different, lookup_map_values]

/-- **Binding one variable composes**: resolving under `bindVar θ x t` is
resolving under `θ`, then replacing `x` by `t`. -/
theorem resolve_bindVar {bindings : Subst} {name : String} {term : Atom}
    (free : bindings.lookup name = none) :
    ∀ subject : Atom, resolve (bindVar bindings name term) subject =
      applySubst [(name, term)] (resolve bindings subject)
  | .var other => by
      by_cases same : name = other
      · subst same
        rw [resolve_var_bound (lookup_bindVar_same bindings name term), resolve_var_free free]
        simp [applySubst, MORK.Subst.lookup]
      · cases found : bindings.lookup other with
        | none =>
            rw [resolve_var_free (by rw [lookup_bindVar_other term same, found]; rfl),
              resolve_var_free found]
            simp [applySubst, MORK.Subst.lookup, same]
        | some value =>
            rw [resolve_var_bound (by rw [lookup_bindVar_other term same, found]; rfl),
              resolve_var_bound found]
  | .symbol _ => rfl
  | .grounded _ => rfl
  | .expression items => by
      simp only [resolve, applySubst, Atom.expression.injEq]
      exact list items
where
  list : ∀ items : List Atom, applySubst.applySubstList (bindVar bindings name term) items =
      applySubst.applySubstList [(name, term)] (applySubst.applySubstList bindings items)
    | [] => rfl
    | first :: rest => by
        simp only [applySubst.applySubstList]
        rw [show applySubst (bindVar bindings name term) first =
            applySubst [(name, term)] (applySubst bindings first) from resolve_bindVar free first,
          list rest]

/-- The variables of `s` with `x` replaced by `t` come from `s` (other than `x`)
or from `t`. -/
theorem freeVars_single {name : String} {term : Atom} :
    ∀ subject : Atom, ∀ other ∈ atomFreeVars (applySubst [(name, term)] subject),
      (other ∈ atomFreeVars subject ∧ other ≠ name) ∨ other ∈ atomFreeVars term
  | .var variable_, other, inResult => by
      by_cases same : variable_ = name
      · subst same
        simp only [applySubst, MORK.Subst.lookup, List.find?, beq_self_eq_true, Option.map_some,
          Option.getD_some] at inResult
        exact .inr inResult
      · have different : (name == variable_) = false := by simpa using Ne.symm same
        simp only [applySubst, MORK.Subst.lookup, List.find?, different, Option.map_none,
          Option.getD_none, MORK.atomFreeVars, List.mem_singleton] at inResult
        subst inResult
        exact .inl ⟨by simp [MORK.atomFreeVars], same⟩
  | .symbol _, other, inResult => by simp [applySubst, MORK.atomFreeVars] at inResult
  | .grounded _, other, inResult => by simp [applySubst, MORK.atomFreeVars] at inResult
  | .expression items, other, inResult => by
      simp only [applySubst] at inResult
      obtain ⟨item, member, inItem⟩ := mem_freeVars_expression.mp inResult
      rcases list items item member other inItem with ⟨inSubject, different⟩ | inTerm
      · exact .inl ⟨mem_freeVars_expression.mpr inSubject, different⟩
      · exact .inr inTerm
where
  list : ∀ items : List Atom, ∀ item ∈ applySubst.applySubstList [(name, term)] items,
      ∀ other ∈ atomFreeVars item,
        ((∃ original ∈ items, other ∈ atomFreeVars original) ∧ other ≠ name) ∨
          other ∈ atomFreeVars term
    | [], _, member, _, _ => by cases member
    | first :: rest, item, member, other, inItem => by
        simp only [applySubst.applySubstList, List.mem_cons] at member
        rcases member with same | member
        · subst same
          rcases freeVars_single first other inItem with ⟨inFirst, different⟩ | inTerm
          · exact .inl ⟨⟨first, List.mem_cons_self, inFirst⟩, different⟩
          · exact .inr inTerm
        · rcases list rest item member other inItem with ⟨⟨original, inRest, inOriginal⟩, different⟩ | inTerm
          · exact .inl ⟨⟨original, List.mem_cons_of_mem _ inRest, inOriginal⟩, different⟩
          · exact .inr inTerm

/-- Binding an unbound variable to a term whose variables are unbound and
which does not contain it keeps the substitution idempotent. -/
theorem idempotent_bindVar {bindings : Subst} {name : String} {term : Atom}
    (idempotent : Idempotent bindings) (free : bindings.lookup name = none)
    (unbound : Unbound bindings term) (notIn : name ∉ atomFreeVars term) :
    Idempotent (bindVar bindings name term) := by
  have stillFree : ∀ other, bindings.lookup other = none → other ≠ name →
      (bindVar bindings name term).lookup other = none := by
    intro other found different
    rw [lookup_bindVar_other term (Ne.symm different), found]; rfl
  intro key value found other inValue
  by_cases same : key = name
  · subst same
    rw [lookup_bindVar_same] at found
    cases found
    exact stillFree other (unbound other inValue) (fun equal => notIn (equal ▸ inValue))
  · rw [lookup_bindVar_other term (Ne.symm same)] at found
    cases original : bindings.lookup key with
    | none => rw [original] at found; cases found
    | some old =>
        rw [original] at found
        simp only [Option.map_some, Option.some.injEq] at found
        subst found
        rcases freeVars_single old other inValue with ⟨inOld, different⟩ | inTerm
        · exact stillFree other (idempotent key old original other inOld) different
        · exact stillFree other (unbound other inTerm) (fun equal => notIn (equal ▸ inTerm))

/-! ## Soundness -/

/-- `later` refines `earlier`: resolving under `later` sees through `earlier`. -/
def Refines (earlier later : Subst) : Prop :=
  ∀ term, resolve later (resolve earlier term) = resolve later term

theorem Refines.refl {bindings : Subst} (idempotent : Idempotent bindings) :
    Refines bindings bindings := resolve_idem idempotent

theorem Refines.trans {first second third : Subst} (one : Refines first second)
    (two : Refines second third) : Refines first third := by
  intro term
  rw [← two (resolve first term), one term, two term]

theorem refines_bindVar {bindings : Subst} {name : String} {term : Atom}
    (idempotent : Idempotent bindings) (free : bindings.lookup name = none) :
    Refines bindings (bindVar bindings name term) := by
  intro subject
  rw [resolve_bindVar free, resolve_bindVar free, resolve_idem idempotent]

/-- **The unifier is sound.** When `unifyTerms` succeeds on an idempotent
substitution, it returns an idempotent substitution that refines the one it
started from and under which the two terms are equal. -/
theorem unifyTerms_sound (fuel : Nat) :
    ∀ (bindings bound : Subst) (left right : Atom), Idempotent bindings →
      unifyTerms fuel bindings left right = .ok bound →
        Idempotent bound ∧ Refines bindings bound ∧ resolve bound left = resolve bound right := by
  induction fuel with
  | zero => intro _ _ _ _ _ unified; cases unified
  | succ fuel ih =>
      intro bindings bound left right idempotent unified
      -- binding the resolved variable `name` of one side to the resolved other side
      have bindLeft : ∀ (name : String) (term : Atom), resolve bindings left = .var name →
          resolve bindings right = term → name ∉ atomFreeVars term →
          Idempotent (bindVar bindings name term) ∧ Refines bindings (bindVar bindings name term) ∧
            resolve (bindVar bindings name term) left = resolve (bindVar bindings name term) right := by
        intro name term leftVar rightTerm notIn
        have free : bindings.lookup name = none :=
          unbound_resolve idempotent left name (by rw [leftVar]; simp [MORK.atomFreeVars])
        have termUnbound : Unbound bindings term := by
          rw [← rightTerm]; exact unbound_resolve idempotent right
        refine ⟨idempotent_bindVar idempotent free termUnbound notIn, refines_bindVar idempotent free, ?_⟩
        rw [resolve_bindVar free, resolve_bindVar free, leftVar, rightTerm]
        have closed : applySubst [(name, term)] term = term := by
          apply resolve_of_unbound
          intro other inTerm
          have different : other ≠ name := fun equal => notIn (equal ▸ inTerm)
          simp [MORK.Subst.lookup, Ne.symm different]
        rw [closed]
        simp [applySubst, MORK.Subst.lookup]
      have bindRight : ∀ (name : String) (term : Atom), resolve bindings right = .var name →
          resolve bindings left = term → name ∉ atomFreeVars term →
          Idempotent (bindVar bindings name term) ∧ Refines bindings (bindVar bindings name term) ∧
            resolve (bindVar bindings name term) left = resolve (bindVar bindings name term) right := by
        intro name term rightVar leftTerm notIn
        have free : bindings.lookup name = none :=
          unbound_resolve idempotent right name (by rw [rightVar]; simp [MORK.atomFreeVars])
        have termUnbound : Unbound bindings term := by
          rw [← leftTerm]; exact unbound_resolve idempotent left
        refine ⟨idempotent_bindVar idempotent free termUnbound notIn, refines_bindVar idempotent free, ?_⟩
        rw [resolve_bindVar free, resolve_bindVar free, rightVar, leftTerm]
        have closed : applySubst [(name, term)] term = term := by
          apply resolve_of_unbound
          intro other inTerm
          have different : other ≠ name := fun equal => notIn (equal ▸ inTerm)
          simp [MORK.Subst.lookup, Ne.symm different]
        rw [closed]
        simp [applySubst, MORK.Subst.lookup]
      have unchanged : resolve bindings left = resolve bindings right →
          Idempotent bindings ∧ Refines bindings bindings ∧
            resolve bindings left = resolve bindings right :=
        fun equal => ⟨idempotent, Refines.refl idempotent, equal⟩
      have lists : ∀ (items others : List Atom) (current : Subst), Idempotent current →
          Refines bindings current →
          unifyLists (unifyTerms fuel) current items others = .ok bound →
            Idempotent bound ∧ Refines current bound ∧
              items.map (resolve bound) = others.map (resolve bound) := by
        intro items
        induction items with
        | nil =>
            intro others current currentIdempotent _ unified
            cases others with
            | nil =>
                simp only [unifyLists, Unified.ok.injEq] at unified
                subst unified
                exact ⟨currentIdempotent, Refines.refl currentIdempotent, rfl⟩
            | cons _ _ => simp [unifyLists] at unified
        | cons first rest restIh =>
            intro others current currentIdempotent currentRefines unified
            cases others with
            | nil => simp [unifyLists] at unified
            | cons other remaining =>
                simp only [unifyLists] at unified
                cases step : unifyTerms fuel current first other with
                | clash => rw [step] at unified; cases unified
                | exhausted => rw [step] at unified; cases unified
                | ok middle =>
                    rw [step, Unified.ok_andThen] at unified
                    obtain ⟨middleIdempotent, middleRefines, middleEqual⟩ :=
                      ih current middle first other currentIdempotent step
                    obtain ⟨boundIdempotent, boundRefines, restEqual⟩ :=
                      restIh remaining middle middleIdempotent (currentRefines.trans middleRefines) unified
                    refine ⟨boundIdempotent, middleRefines.trans boundRefines, ?_⟩
                    simp only [List.map_cons, List.cons.injEq]
                    refine ⟨?_, restEqual⟩
                    rw [← boundRefines first, ← boundRefines other, middleEqual]
      unfold unifyTerms at unified
      generalize leftEq : resolve bindings left = resolvedLeft at unified
      generalize rightEq : resolve bindings right = resolvedRight at unified
      cases resolvedLeft with
      | var name =>
          cases resolvedRight with
          | var other =>
              simp only at unified
              by_cases same : name = other
              · simp only [same, ↓reduceIte, Unified.ok.injEq] at unified
                subst unified
                exact unchanged (by rw [leftEq, rightEq, same])
              · simp only [same, ↓reduceIte, Unified.ok.injEq] at unified
                subst unified
                exact bindLeft name (.var other) leftEq rightEq (by simpa [MORK.atomFreeVars] using same)
          | symbol _ | grounded _ | expression _ =>
              simp only at unified
              split at unified
              · cases unified
              · rename_i notIn
                simp only [Unified.ok.injEq] at unified
                subst unified
                exact bindLeft name _ leftEq rightEq (by simpa [occurs] using notIn)
      | symbol name =>
          cases resolvedRight with
          | var other =>
              simp only at unified
              split at unified
              · cases unified
              · rename_i notIn
                simp only [Unified.ok.injEq] at unified
                subst unified
                exact bindRight other _ rightEq leftEq (by simpa [occurs] using notIn)
          | symbol other =>
              simp only at unified
              split at unified
              · rename_i same
                simp only [Unified.ok.injEq] at unified
                subst unified
                exact unchanged (by rw [leftEq, rightEq, same])
              · cases unified
          | grounded _ | expression _ => simp at unified
      | grounded value =>
          cases resolvedRight with
          | var other =>
              simp only at unified
              split at unified
              · cases unified
              · rename_i notIn
                simp only [Unified.ok.injEq] at unified
                subst unified
                exact bindRight other _ rightEq leftEq (by simpa [occurs] using notIn)
          | grounded other =>
              simp only at unified
              split at unified
              · rename_i same
                simp only [Unified.ok.injEq] at unified
                subst unified
                exact unchanged (by rw [leftEq, rightEq, same])
              · cases unified
          | symbol _ | expression _ => simp at unified
      | expression items =>
          cases resolvedRight with
          | var other =>
              simp only at unified
              split at unified
              · cases unified
              · rename_i notIn
                simp only [Unified.ok.injEq] at unified
                subst unified
                exact bindRight other _ rightEq leftEq (by simpa [occurs] using notIn)
          | expression others =>
              simp only at unified
              obtain ⟨boundIdempotent, boundRefines, equal⟩ :=
                lists items others bindings idempotent (Refines.refl idempotent) unified
              refine ⟨boundIdempotent, boundRefines, ?_⟩
              rw [← boundRefines left, ← boundRefines right, leftEq, rightEq]
              simp only [resolve, applySubst, Atom.expression.injEq]
              have toMap : ∀ items : List Atom,
                  applySubst.applySubstList bound items = items.map (resolve bound) := by
                intro items
                induction items with
                | nil => rfl
                | cons first rest ih => simp [applySubst.applySubstList, ih]
              rw [toMap, toMap, equal]
          | symbol _ | grounded _ => simp at unified


/-- An example: `(f $x 2)` and `(f 1 $y)`. -/
theorem unify_example :
    unify [] (.expression [.symbol "f", .var "x", .grounded (.int 2)])
        (.expression [.symbol "f", .grounded (.int 1), .var "y"]) =
      .ok [("y", .grounded (.int 2)), ("x", .grounded (.int 1))] := by
  decide +kernel

end Mettapedia.Languages.MeTTa.PeTTa.Unifying
