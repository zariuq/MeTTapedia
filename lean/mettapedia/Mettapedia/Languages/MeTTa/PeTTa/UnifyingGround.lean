import Mettapedia.Languages.MeTTa.PeTTa.Unifying

/-!
# The ground sub-profile: unification against ground values is matching

`Eval.step` selects equations and rows by one-way matching; `Unifying.step`
unifies two ways. Against a value without variables they agree exactly, with
the same substitution, as long as every value bound so far is ground
(`GroundRange`):

* `unifyTerms_ground`: unifying a term with a ground term is `MORK.matchAtom`;
* `unifyPattern_ground`: unifying a pattern that has PeTTa's list view with a
  ground value is `SpaceSemantics.matchValue`, case for case;
* `arguments_ground`: a call with ground arguments unifies an equation's
  argument patterns exactly when they match the arguments element by element
  (`matchValues`, the selection of `Eval.clauses`), with the matching
  substitution;
* `selections_ground`: so the alternatives of such a call are, in row order,
  the bodies of the equations whose renamed patterns match, each under the
  matching substitution;
* `queryBodies_ground`: a `match` on ground rows runs its body exactly under
  the bindings `matchAtom` gives, row by row;
* `survivors_ground`: `remove-atom` on ground rows keeps exactly the rows that
  `Effects.erase` keeps.

Where a value has a variable the two part: the head `(z 0)` has no match against
the argument `$u` and has the unifier `$u = 0` (`open_argument_separates`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Unifying

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst atomFreeVars isGroundAtom matchAtom)
open SpaceSemantics (matchValue)
open Mettapedia.Languages.ProcessCalculi

/-! ## Ground terms and ground ranges -/

/-- The outcome of a matching, read as a unification outcome. -/
def ofMatch : Option Subst → Unified
  | some bound => .ok bound
  | none => .clash

@[simp] theorem ofMatch_some (bound : Subst) : ofMatch (some bound) = .ok bound := rfl
@[simp] theorem ofMatch_none : ofMatch none = .clash := rfl

theorem applySubst_ground (bindings : Subst) :
    ∀ term : Atom, isGroundAtom term = true → applySubst bindings term = term
  | .var _, ground => by simp [isGroundAtom] at ground
  | .symbol _, _ => rfl
  | .grounded _, _ => rfl
  | .expression items, ground => by
      simp only [applySubst]
      congr 1
      exact list items (by simpa [isGroundAtom] using ground)
where
  list : ∀ items : List Atom, isGroundAtom.isGroundList items = true →
      applySubst.applySubstList bindings items = items
    | [], _ => rfl
    | first :: rest, ground => by
        simp only [isGroundAtom.isGroundList, Bool.and_eq_true] at ground
        simp only [applySubst.applySubstList, applySubst_ground bindings first ground.1,
          list rest ground.2]

theorem freeVars_ground : ∀ term : Atom, isGroundAtom term = true → atomFreeVars term = []
  | .var _, ground => by simp [isGroundAtom] at ground
  | .symbol _, _ => rfl
  | .grounded _, _ => rfl
  | .expression items, ground => by
      simp only [MORK.atomFreeVars]
      exact list items (by simpa [isGroundAtom] using ground)
where
  list : ∀ items : List Atom, isGroundAtom.isGroundList items = true →
      MORK.atomFreeVars.atomFreeVarsList items = []
    | [], _ => rfl
    | first :: rest, ground => by
        simp only [isGroundAtom.isGroundList, Bool.and_eq_true] at ground
        simp only [MORK.atomFreeVars.atomFreeVarsList, freeVars_ground first ground.1,
          list rest ground.2, List.nil_append]

theorem occurs_ground {name : String} {term : Atom} (ground : isGroundAtom term = true) :
    occurs name term = false := by
  simp [occurs, freeVars_ground term ground]

theorem isGround_of_mem {item : Atom} {items : List Atom} (member : item ∈ items)
    (ground : isGroundAtom (.expression items) = true) : isGroundAtom item = true := by
  have list : ∀ items : List Atom, isGroundAtom.isGroundList items = true → item ∈ items →
      isGroundAtom item = true := by
    intro items ground member
    induction items with
    | nil => cases member
    | cons first rest ih =>
        simp only [isGroundAtom.isGroundList, Bool.and_eq_true] at ground
        rcases List.mem_cons.mp member with same | member
        · subst same; exact ground.1
        · exact ih ground.2 member
  exact list items (by simpa [isGroundAtom] using ground) member

theorem isGround_tail {head : Atom} {tail : List Atom}
    (ground : isGroundAtom (.expression (head :: tail)) = true) :
    isGroundAtom (.expression tail) = true := by
  simp only [isGroundAtom, isGroundAtom.isGroundList, Bool.and_eq_true] at ground ⊢
  exact ground.2

theorem atomSize_lt_of_mem {item : Atom} {items : List Atom} (member : item ∈ items) :
    atomSize item < atomSize (.expression items) := by
  have bound : ∀ items : List Atom, item ∈ items → atomSize item ≤ atomSize.listSize items := by
    intro items member
    induction items with
    | nil => cases member
    | cons first rest ih =>
        simp only [atomSize.listSize]
        rcases List.mem_cons.mp member with same | member
        · subst same; omega
        · have := ih member; omega
  have := bound items member
  simp only [atomSize]
  omega

theorem atomSize_pos (term : Atom) : 0 < atomSize term := by
  cases term <;> simp [atomSize]

/-- Every value bound is ground. -/
def GroundRange (bindings : Subst) : Prop := ∀ binding ∈ bindings, isGroundAtom binding.2 = true

theorem GroundRange.cons {bindings : Subst} {name : String} {term : Atom}
    (range : GroundRange bindings) (ground : isGroundAtom term = true) :
    GroundRange ((name, term) :: bindings) := by
  intro binding member
  rcases List.mem_cons.mp member with same | member
  · subst same; exact ground
  · exact range binding member

theorem lookup_ground {bindings : Subst} {name : String} {value : Atom}
    (range : GroundRange bindings) (found : bindings.lookup name = some value) :
    isGroundAtom value = true := by
  unfold MORK.Subst.lookup at found
  cases search : bindings.find? (fun binding => binding.1 == name) with
  | none => simp [search] at found
  | some binding =>
      simp only [search, Option.map_some, Option.some.injEq] at found
      subst found
      exact range binding (List.mem_of_find?_eq_some search)

/-- On a substitution whose values are ground, binding a variable to a term just
adds the pair. -/
theorem bindVar_ground {bindings : Subst} {name : String} {term : Atom}
    (range : GroundRange bindings) :
    bindVar bindings name term = (name, term) :: bindings := by
  unfold bindVar
  congr 1
  conv_rhs => rw [← List.map_id bindings]
  apply List.map_congr_left
  intro binding member
  simp [applySubst_ground _ _ (range binding member)]

theorem resolve_var_bound {bindings : Subst} {name : String} {value : Atom}
    (found : bindings.lookup name = some value) : resolve bindings (.var name) = value := by
  simp [resolve, applySubst, found]

theorem resolve_var_free {bindings : Subst} {name : String}
    (missing : bindings.lookup name = none) : resolve bindings (.var name) = .var name := by
  simp [resolve, applySubst, missing]

/-- `later` keeps every binding of `earlier`. -/
def Keeps (earlier later : Subst) : Prop :=
  ∀ name value, earlier.lookup name = some value → later.lookup name = some value

theorem Keeps.refl (bindings : Subst) : Keeps bindings bindings := fun _ _ found => found

theorem Keeps.trans {first second third : Subst} (one : Keeps first second)
    (two : Keeps second third) : Keeps first third :=
  fun name value found => two name value (one name value found)

theorem lookup_cons_ne {bindings : Subst} {name other : String} {value : Atom}
    (different : name ≠ other) :
    MORK.Subst.lookup ((name, value) :: bindings) other = bindings.lookup other := by
  simp [MORK.Subst.lookup, different]

/-- One step of `matchAtom` on a constant pattern either keeps the substitution or
fails. -/
theorem matchAtom_constant {bindings bound : Subst} {pattern value : Atom}
    (constant : (∃ name, pattern = .symbol name) ∨ ∃ item, pattern = .grounded item)
    (matched : matchAtom bindings pattern value = some bound) : bound = bindings := by
  rcases constant with ⟨name, rfl⟩ | ⟨item, rfl⟩
  · cases value with
    | symbol other =>
        simp only [matchAtom] at matched
        split at matched
        · cases matched; rfl
        · cases matched
    | var _ => simp [matchAtom] at matched
    | grounded _ => simp [matchAtom] at matched
    | expression _ => simp [matchAtom] at matched
  · cases value with
    | grounded other =>
        simp only [matchAtom] at matched
        split at matched
        · cases matched; rfl
        · cases matched
    | var _ => simp [matchAtom] at matched
    | symbol _ => simp [matchAtom] at matched
    | expression _ => simp [matchAtom] at matched

/-- Matching adds bindings only for names it has not bound. -/
theorem matchAtom_keeps :
    ∀ {bindings bound : Subst} {pattern value : Atom},
      matchAtom bindings pattern value = some bound → Keeps bindings bound
  | bindings, bound, .var name, value, matched => by
      unfold matchAtom at matched
      cases found : bindings.lookup name with
      | none =>
          simp only [found, Option.some.injEq] at matched
          subst matched
          intro other old foundOther
          have different : name ≠ other := by
            rintro rfl; rw [found] at foundOther; cases foundOther
          rw [lookup_cons_ne different]
          exact foundOther
      | some old =>
          simp only [found] at matched
          split at matched
          · cases matched; exact Keeps.refl _
          · cases matched
  | bindings, bound, .symbol name, value, matched => by
      rw [matchAtom_constant (.inl ⟨name, rfl⟩) matched]; exact Keeps.refl _
  | bindings, bound, .grounded item, value, matched => by
      rw [matchAtom_constant (.inr ⟨item, rfl⟩) matched]; exact Keeps.refl _
  | bindings, bound, .expression patterns, value, matched => by
      cases value with
      | expression values =>
          simp only [matchAtom] at matched
          exact lists patterns values bindings bound matched
      | var _ => simp [matchAtom] at matched
      | symbol _ => simp [matchAtom] at matched
      | grounded _ => simp [matchAtom] at matched
where
  lists : ∀ (patterns values : List Atom) (bindings bound : Subst),
      matchAtom.matchAtomList bindings patterns values = some bound → Keeps bindings bound
    | [], [], bindings, bound, matched => by
        simp only [matchAtom.matchAtomList, Option.some.injEq] at matched
        subst matched; exact Keeps.refl _
    | [], _ :: _, _, _, matched => by simp [matchAtom.matchAtomList] at matched
    | _ :: _, [], _, _, matched => by simp [matchAtom.matchAtomList] at matched
    | pattern :: patterns, value :: values, bindings, bound, matched => by
        simp only [matchAtom.matchAtomList] at matched
        cases first : matchAtom bindings pattern value with
        | none => simp [first] at matched
        | some middle =>
            simp only [first] at matched
            exact (matchAtom_keeps first).trans (lists patterns values middle bound matched)

/-- Matching a ground term keeps every bound value ground. -/
theorem matchAtom_groundRange :
    ∀ {bindings bound : Subst} {pattern value : Atom},
      GroundRange bindings → isGroundAtom value = true →
        matchAtom bindings pattern value = some bound → GroundRange bound
  | bindings, bound, .var name, value, range, ground, matched => by
      unfold matchAtom at matched
      cases found : bindings.lookup name with
      | none =>
          simp only [found, Option.some.injEq] at matched
          subst matched
          exact range.cons ground
      | some old =>
          simp only [found] at matched
          split at matched
          · cases matched; exact range
          · cases matched
  | bindings, bound, .symbol name, value, range, _, matched => by
      rw [matchAtom_constant (.inl ⟨name, rfl⟩) matched]; exact range
  | bindings, bound, .grounded item, value, range, _, matched => by
      rw [matchAtom_constant (.inr ⟨item, rfl⟩) matched]; exact range
  | bindings, bound, .expression patterns, value, range, ground, matched => by
      cases value with
      | expression values =>
          simp only [matchAtom] at matched
          exact lists patterns values bindings bound range
            (fun item member => isGround_of_mem member ground) matched
      | var _ => simp [matchAtom] at matched
      | symbol _ => simp [matchAtom] at matched
      | grounded _ => simp [matchAtom] at matched
where
  lists : ∀ (patterns values : List Atom) (bindings bound : Subst), GroundRange bindings →
      (∀ item ∈ values, isGroundAtom item = true) →
        matchAtom.matchAtomList bindings patterns values = some bound → GroundRange bound
    | [], [], bindings, bound, range, _, matched => by
        simp only [matchAtom.matchAtomList, Option.some.injEq] at matched
        subst matched; exact range
    | [], _ :: _, _, _, _, _, matched => by simp [matchAtom.matchAtomList] at matched
    | _ :: _, [], _, _, _, _, matched => by simp [matchAtom.matchAtomList] at matched
    | pattern :: patterns, value :: values, bindings, bound, range, ground, matched => by
        simp only [matchAtom.matchAtomList] at matched
        cases first : matchAtom bindings pattern value with
        | none => simp [first] at matched
        | some middle =>
            simp only [first] at matched
            exact lists patterns values middle bound
              (matchAtom_groundRange range (ground value List.mem_cons_self) first)
              (fun item member => ground item (List.mem_cons_of_mem _ member)) matched

/-- Resolving under a substitution that keeps the ground bindings of `earlier`
undoes nothing `earlier` resolved. -/
theorem resolve_after {earlier later : Subst} (keeps : Keeps earlier later)
    (range : GroundRange earlier) :
    ∀ term : Atom, resolve later (applySubst earlier term) = resolve later term
  | .var name => by
      cases found : earlier.lookup name with
      | none => simp [resolve, applySubst, found]
      | some value =>
          rw [show applySubst earlier (.var name) = value from resolve_var_bound found,
            resolve_var_bound (keeps name value found)]
          exact applySubst_ground _ _ (lookup_ground range found)
  | .symbol _ => rfl
  | .grounded _ => rfl
  | .expression items => by
      simp only [resolve, applySubst, Atom.expression.injEq]
      exact list items
where
  list : ∀ items : List Atom, applySubst.applySubstList later
      (applySubst.applySubstList earlier items) = applySubst.applySubstList later items
    | [] => rfl
    | first :: rest => by
        simp only [applySubst.applySubstList]
        rw [show applySubst later (applySubst earlier first) = applySubst later first from
          resolve_after keeps range first, list rest]

/-- On a substitution whose values are ground, resolving twice is resolving once. -/
theorem resolve_resolve {bindings : Subst} (range : GroundRange bindings) (term : Atom) :
    resolve bindings (resolve bindings term) = resolve bindings term :=
  resolve_after (Keeps.refl bindings) range term

/-- `unifyTerms` sees only the resolved terms. -/
theorem unifyTerms_resolve {bindings : Subst} (range : GroundRange bindings) (fuel : Nat)
    (left right : Atom) :
    unifyTerms fuel bindings left right =
      unifyTerms fuel bindings (resolve bindings left) (resolve bindings right) := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      unfold unifyTerms
      rw [resolve_resolve range left, resolve_resolve range right]

/-! ## Two ground terms -/

/-- **Two ground terms unify exactly when they are equal**, binding nothing. -/
theorem unifyTerms_ground_ground (fuel : Nat) :
    ∀ (bindings : Subst) (left right : Atom),
      isGroundAtom left = true → isGroundAtom right = true → atomSize right < fuel →
        unifyTerms fuel bindings left right = if left = right then .ok bindings else .clash := by
  induction fuel with
  | zero => intro _ _ _ _ _ small; exact absurd small (Nat.not_lt_zero _)
  | succ fuel ih =>
      intro bindings left right groundLeft groundRight small
      have lists : ∀ (items others : List Atom),
          (∀ item ∈ items, isGroundAtom item = true) →
          (∀ item ∈ others, isGroundAtom item = true) →
          (∀ item ∈ others, atomSize item < fuel) →
          unifyLists (unifyTerms fuel) bindings items others =
            if items = others then .ok bindings else .clash := by
        intro items
        induction items with
        | nil => intro others _ _ _; cases others <;> simp [unifyLists]
        | cons first rest restIh =>
            intro others groundItems groundOthers smallOthers
            cases others with
            | nil => simp [unifyLists]
            | cons other remaining =>
                simp only [unifyLists]
                rw [ih bindings first other (groundItems first List.mem_cons_self)
                  (groundOthers other List.mem_cons_self) (smallOthers other List.mem_cons_self)]
                by_cases same : first = other
                · simp only [same, ↓reduceIte, Unified.ok_andThen, List.cons.injEq, true_and]
                  exact restIh remaining (fun item member => groundItems item (List.mem_cons_of_mem _ member))
                    (fun item member => groundOthers item (List.mem_cons_of_mem _ member))
                    (fun item member => smallOthers item (List.mem_cons_of_mem _ member))
                · simp [same]
      unfold unifyTerms
      rw [show resolve bindings left = left from applySubst_ground _ _ groundLeft,
        show resolve bindings right = right from applySubst_ground _ _ groundRight]
      cases left with
      | var _ => simp [isGroundAtom] at groundLeft
      | symbol name =>
          cases right with
          | var _ => simp [isGroundAtom] at groundRight
          | symbol other => by_cases same : name = other <;> simp [same]
          | grounded _ => simp
          | expression _ => simp
      | grounded value =>
          cases right with
          | var _ => simp [isGroundAtom] at groundRight
          | symbol _ => simp
          | grounded other => by_cases same : value = other <;> simp [same]
          | expression _ => simp
      | expression items =>
          cases right with
          | var _ => simp [isGroundAtom] at groundRight
          | symbol _ => simp
          | grounded _ => simp
          | expression others =>
              simp only [Atom.expression.injEq]
              exact lists items others
                (fun item member => isGround_of_mem member groundLeft)
                (fun item member => isGround_of_mem member groundRight)
                (fun item member => by
                  have := atomSize_lt_of_mem member
                  omega)

/-! ## A term against a ground term: `matchAtom` -/

/-- **A term against a ground term: unification is `MORK.matchAtom`**, with the
same substitution. -/
theorem unifyTerms_ground (fuel : Nat) :
    ∀ (bindings : Subst) (pattern value : Atom),
      GroundRange bindings → isGroundAtom value = true → atomSize value < fuel →
        unifyTerms fuel bindings pattern value = ofMatch (matchAtom bindings pattern value) := by
  induction fuel with
  | zero => intro _ _ _ _ _ small; exact absurd small (Nat.not_lt_zero _)
  | succ fuel ih =>
      intro bindings pattern value range ground small
      -- the elements of an expression were resolved under `base`; unifying them under a
      -- later substitution that keeps `base` is unifying the elements themselves
      have lists : ∀ (patterns values : List Atom) (base current : Subst),
          GroundRange base → GroundRange current → Keeps base current →
          (∀ item ∈ values, isGroundAtom item = true) → (∀ item ∈ values, atomSize item < fuel) →
          unifyLists (unifyTerms fuel) current (applySubst.applySubstList base patterns) values =
            ofMatch (matchAtom.matchAtomList current patterns values) := by
        intro patterns
        induction patterns with
        | nil =>
            intro values _ _ _ _ _ _ _
            cases values <;> simp [unifyLists, applySubst.applySubstList, matchAtom.matchAtomList]
        | cons first rest restIh =>
            intro values base current baseRange currentRange keeps groundValues smallValues
            cases values with
            | nil => simp [unifyLists, applySubst.applySubstList, matchAtom.matchAtomList]
            | cons value remaining =>
                simp only [applySubst.applySubstList, unifyLists, matchAtom.matchAtomList]
                have here : unifyTerms fuel current (applySubst base first) value =
                    ofMatch (matchAtom current first value) := by
                  rw [unifyTerms_resolve currentRange fuel (applySubst base first),
                    show resolve current (applySubst base first) = resolve current first from
                      resolve_after keeps baseRange first,
                    ← unifyTerms_resolve currentRange fuel first]
                  exact ih current first value currentRange (groundValues value List.mem_cons_self)
                    (smallValues value List.mem_cons_self)
                rw [here]
                cases matched : matchAtom current first value with
                | none => simp
                | some middle =>
                    simp only [ofMatch_some, Unified.ok_andThen]
                    exact restIh remaining base middle baseRange
                      (matchAtom_groundRange currentRange (groundValues value List.mem_cons_self) matched)
                      (keeps.trans (matchAtom_keeps matched))
                      (fun item member => groundValues item (List.mem_cons_of_mem _ member))
                      (fun item member => smallValues item (List.mem_cons_of_mem _ member))
      cases pattern with
      | var name =>
          cases found : bindings.lookup name with
          | some old =>
              rw [unifyTerms_resolve range, resolve_var_bound found,
                show resolve bindings value = value from applySubst_ground _ _ ground,
                unifyTerms_ground_ground (fuel + 1) bindings old value (lookup_ground range found)
                  ground small]
              simp only [matchAtom, found]
              by_cases same : old = value
              · subst same; simp
              · have other : (value == old) = false := by
                  simp only [beq_eq_false_iff_ne]; exact fun h => same h.symm
                simp [same, other]
          | none =>
              unfold unifyTerms
              rw [resolve_var_free found, show resolve bindings value = value from applySubst_ground _ _ ground]
              cases value with
              | var _ => simp [isGroundAtom] at ground
              | symbol _ =>
                  simp [matchAtom, found, occurs_ground ground, bindVar_ground range]
              | grounded _ =>
                  simp [matchAtom, found, occurs_ground ground, bindVar_ground range]
              | expression _ =>
                  simp [matchAtom, found, occurs_ground ground, bindVar_ground range]
      | symbol name =>
          unfold unifyTerms
          rw [show resolve bindings value = value from applySubst_ground _ _ ground]
          cases value with
          | var _ => simp [isGroundAtom] at ground
          | symbol other => by_cases same : name = other <;> simp [matchAtom, same, resolve, applySubst]
          | grounded _ => simp [matchAtom, resolve, applySubst]
          | expression _ => simp [matchAtom, resolve, applySubst]
      | grounded item =>
          unfold unifyTerms
          rw [show resolve bindings value = value from applySubst_ground _ _ ground]
          cases value with
          | var _ => simp [isGroundAtom] at ground
          | symbol _ => simp [matchAtom, resolve, applySubst]
          | grounded other => by_cases same : item = other <;> simp [matchAtom, same, resolve, applySubst]
          | expression _ => simp [matchAtom, resolve, applySubst]
      | expression patterns =>
          unfold unifyTerms
          rw [show resolve bindings value = value from applySubst_ground _ _ ground]
          cases value with
          | var _ => simp [isGroundAtom] at ground
          | symbol _ => simp [resolve, applySubst, matchAtom]
          | grounded _ => simp [resolve, applySubst, matchAtom]
          | expression values =>
              simp only [resolve, applySubst, matchAtom]
              exact lists patterns values bindings bindings range range (Keeps.refl _)
                (fun item member => isGround_of_mem member ground)
                (fun item member => by
                  have := atomSize_lt_of_mem member
                  omega)

/-! ## A pattern with the list view against a ground value: `matchValue` -/

/-- Whether a list of patterns is the list view `(cons a b)`. -/
def consView : List Atom → Bool
  | [.symbol "cons", _, _] => true
  | _ => false

/-- Whether a term is an expression. -/
def isExpression : Atom → Bool
  | .expression _ => true
  | _ => false

/-- Whether a term is a variable. -/
def isVar : Atom → Bool
  | .var _ => true
  | _ => false

/-- Whether a term is a nonempty expression. -/
def nonemptyExpression : Atom → Bool
  | .expression (_ :: _) => true
  | _ => false

theorem consView_true {items : List Atom} (view : consView items = true) :
    ∃ first rest, items = [.symbol "cons", first, rest] := by
  unfold consView at view
  split at view
  · exact ⟨_, _, rfl⟩
  · cases view

theorem not_cons_of_consView {items : List Atom} (notView : consView items = false) :
    ∀ first rest, items ≠ [.symbol "cons", first, rest] := by
  rintro first rest rfl
  simp [consView] at notView

/-- One unfolding of `unifyPattern`. -/
theorem unifyPattern_succ (fuel : Nat) (bindings : Subst) (pattern value : Atom) :
    unifyPattern (fuel + 1) bindings pattern value =
      match pattern, resolve bindings value with
      | .expression [.symbol "cons", first, rest], .expression (head :: tail) =>
          (unifyPattern fuel bindings first head).andThen fun bound =>
            unifyPattern fuel bound rest (.expression tail)
      | .expression [.symbol "cons", _, _], .var _ => unifyTerms fuel bindings pattern value
      | .expression [.symbol "cons", _, _], _ => .clash
      | .expression patterns, .expression values =>
          unifyLists (unifyPattern fuel) bindings patterns values
      | .expression _, .var _ => unifyTerms fuel bindings pattern value
      | .expression _, _ => .clash
      | _, _ => unifyTerms fuel bindings pattern value := rfl

theorem unifyPattern_expression_of_not_cons {fuel : Nat} {bindings : Subst}
    {patterns values : List Atom} (notView : consView patterns = false)
    (resolved : resolve bindings (.expression values) = .expression values) :
    unifyPattern (fuel + 1) bindings (.expression patterns) (.expression values) =
      unifyLists (unifyPattern fuel) bindings patterns values := by
  rw [unifyPattern_succ, resolved]
  split <;> first | rfl | simp_all [consView]

/-- One-step unfolding of `matchValue` on the list view. -/
theorem matchValue_cons_view (bindings : Subst) (first rest head : Atom) (tail : List Atom) :
    matchValue bindings (.expression [.symbol "cons", first, rest]) (.expression (head :: tail)) =
      (matchValue bindings first head).bind fun bound => matchValue bound rest (.expression tail) := by
  rw [matchValue]
  rfl

theorem matchValue_cons_view_other (bindings : Subst) (first rest value : Atom)
    (notList : nonemptyExpression value = false) :
    matchValue bindings (.expression [.symbol "cons", first, rest]) value = none := by
  cases value
  case expression items =>
    cases items
    · rw [matchValue]
      all_goals first | rfl | (intros; simp_all)
    · simp [nonemptyExpression] at notList
  all_goals (rw [matchValue]; all_goals first | rfl | (intros; simp_all))

theorem unifyPattern_cons_view (fuel : Nat) (bindings : Subst) (first rest head : Atom)
    (tail : List Atom) (resolved : resolve bindings (.expression (head :: tail)) =
      .expression (head :: tail)) :
    unifyPattern (fuel + 1) bindings (.expression [.symbol "cons", first, rest])
        (.expression (head :: tail)) =
      (unifyPattern fuel bindings first head).andThen fun bound =>
        unifyPattern fuel bound rest (.expression tail) := by
  rw [unifyPattern_succ, resolved]
  split <;> first | rfl | (simp_all; done) | aesop

theorem unifyPattern_cons_view_other (fuel : Nat) (bindings : Subst) (first rest value : Atom)
    (resolved : resolve bindings value = value) (notVar : isVar value = false)
    (notList : nonemptyExpression value = false) :
    unifyPattern (fuel + 1) bindings (.expression [.symbol "cons", first, rest]) value = .clash := by
  rw [unifyPattern_succ, resolved]
  cases value
  case expression items =>
    cases items
    · rfl
    · simp [nonemptyExpression] at notList
  case var => simp [isVar] at notVar
  all_goals rfl

theorem matchValue_atom (bindings : Subst) (pattern value : Atom)
    (atomic : isExpression pattern = false) :
    matchValue bindings pattern value = matchAtom bindings pattern value := by
  cases pattern
  case expression => simp [isExpression] at atomic
  all_goals (rw [matchValue]; all_goals first | rfl | (intros; simp_all))

theorem unifyPattern_atom (fuel : Nat) (bindings : Subst) (pattern value : Atom)
    (atomic : isExpression pattern = false) :
    unifyPattern (fuel + 1) bindings pattern value = unifyTerms fuel bindings pattern value := by
  rw [unifyPattern_succ]
  cases pattern
  case expression => simp [isExpression] at atomic
  all_goals rfl

/-- An expression pattern against a constant value has no unifier. -/
theorem unifyPattern_expression_constant (fuel : Nat) (bindings : Subst) (patterns : List Atom)
    (value : Atom) (resolved : resolve bindings value = value)
    (constant : isExpression value = false) (notVar : isVar value = false) :
    unifyPattern (fuel + 1) bindings (.expression patterns) value = .clash := by
  rw [unifyPattern_succ, resolved]
  cases value
  case expression => simp [isExpression] at constant
  case var => simp [isVar] at notVar
  all_goals (split <;> first | rfl | simp_all)

/-- An expression pattern does not match a constant value. -/
theorem matchValue_expression_constant (bindings : Subst) (patterns : List Atom) (value : Atom)
    (constant : isExpression value = false) :
    matchValue bindings (.expression patterns) value = none := by
  cases view : consView patterns
  · have notCons := not_cons_of_consView view
    cases value
    case expression => simp [isExpression] at constant
    all_goals (rw [matchValue]; all_goals first | rfl | exact fun h h' same => notCons h h' same | (intros; simp_all))
  · obtain ⟨first, rest, rfl⟩ := consView_true view
    exact matchValue_cons_view_other bindings first rest value
      (by cases value <;> simp_all [isExpression, nonemptyExpression])

/-- **A pattern with PeTTa's list view against a ground value: unification is
`SpaceSemantics.matchValue`**, case for case, with the same substitution; and
that substitution keeps every bound value ground. -/
theorem unifyPattern_ground (fuel : Nat) :
    ∀ (bindings : Subst) (pattern value : Atom),
      GroundRange bindings → isGroundAtom value = true → atomSize pattern + atomSize value < fuel →
        unifyPattern fuel bindings pattern value = ofMatch (matchValue bindings pattern value) ∧
          ∀ bound, matchValue bindings pattern value = some bound → GroundRange bound := by
  induction fuel with
  | zero => intro _ _ _ _ _ small; exact absurd small (Nat.not_lt_zero _)
  | succ fuel ih =>
      intro bindings pattern value range ground small
      have lists : ∀ (patterns values : List Atom) (current : Subst), GroundRange current →
          (∀ item ∈ values, isGroundAtom item = true) →
          (∀ item ∈ patterns, ∀ other ∈ values, atomSize item + atomSize other < fuel) →
          unifyLists (unifyPattern fuel) current patterns values =
              ofMatch (matchValue.matchValues current patterns values) ∧
            ∀ bound, matchValue.matchValues current patterns values = some bound →
              GroundRange bound := by
        intro patterns
        induction patterns with
        | nil =>
            intro values current currentRange _ _
            cases values with
            | nil =>
                refine ⟨by simp [unifyLists, matchValue.matchValues], ?_⟩
                intro bound matched
                simp only [matchValue.matchValues, Option.some.injEq] at matched
                subst matched; exact currentRange
            | cons _ _ => exact ⟨by simp [unifyLists, matchValue.matchValues],
                fun _ matched => by simp [matchValue.matchValues] at matched⟩
        | cons first rest restIh =>
            intro values current currentRange groundValues smallPairs
            cases values with
            | nil => exact ⟨by simp [unifyLists, matchValue.matchValues],
                fun _ matched => by simp [matchValue.matchValues] at matched⟩
            | cons value remaining =>
                have here := ih current first value currentRange (groundValues value List.mem_cons_self)
                  (smallPairs first List.mem_cons_self value List.mem_cons_self)
                simp only [unifyLists, matchValue.matchValues]
                rw [here.1]
                cases matched : matchValue current first value with
                | none =>
                    exact ⟨by simp, fun _ never => by simp at never⟩
                | some middle =>
                    simp only [ofMatch_some, Unified.ok_andThen, Option.bind_eq_bind,
                      Option.bind_some]
                    exact restIh remaining middle (here.2 middle matched)
                      (fun item member => groundValues item (List.mem_cons_of_mem _ member))
                      (fun item member other otherMember =>
                        smallPairs item (List.mem_cons_of_mem _ member) other
                          (List.mem_cons_of_mem _ otherMember))
      have resolved : resolve bindings value = value := applySubst_ground _ _ ground
      have atomCase : ∀ atom : Atom, isExpression atom = false →
          atomSize atom + atomSize value < fuel + 1 →
          unifyPattern (fuel + 1) bindings atom value = ofMatch (matchValue bindings atom value) ∧
            ∀ bound, matchValue bindings atom value = some bound → GroundRange bound := by
        intro atom atomic smallAtom
        rw [unifyPattern_atom fuel bindings atom value atomic, matchValue_atom bindings atom value atomic]
        have positive := atomSize_pos atom
        exact ⟨unifyTerms_ground fuel bindings atom value range ground (by omega),
          fun bound matched => matchAtom_groundRange range ground matched⟩
      cases pattern with
      | var name => exact atomCase _ rfl small
      | symbol name => exact atomCase _ rfl small
      | grounded item => exact atomCase _ rfl small
      | expression patterns =>
          cases view : consView patterns
          · cases value with
            | var _ => simp [isGroundAtom] at ground
            | symbol _ =>
                rw [unifyPattern_expression_constant fuel bindings patterns _ resolved rfl rfl,
                  matchValue_expression_constant bindings patterns _ rfl]
                exact ⟨rfl, fun _ never => by cases never⟩
            | grounded _ =>
                rw [unifyPattern_expression_constant fuel bindings patterns _ resolved rfl rfl,
                  matchValue_expression_constant bindings patterns _ rfl]
                exact ⟨rfl, fun _ never => by cases never⟩
            | expression values =>
                rw [unifyPattern_expression_of_not_cons view resolved,
                  SpaceSemantics.matchValue_expression_of_not_cons bindings patterns values
                    (not_cons_of_consView view)]
                exact lists patterns values bindings range
                  (fun item member => isGround_of_mem member ground)
                  (fun item member other otherMember => by
                    have one := atomSize_lt_of_mem member
                    have two := atomSize_lt_of_mem otherMember
                    omega)
          · obtain ⟨first, rest, rfl⟩ := consView_true view
            cases value with
            | var _ => simp [isGroundAtom] at ground
            | symbol _ =>
                rw [unifyPattern_cons_view_other fuel bindings first rest _ resolved rfl rfl,
                  matchValue_cons_view_other bindings first rest _ rfl]
                exact ⟨rfl, fun _ never => by cases never⟩
            | grounded _ =>
                rw [unifyPattern_cons_view_other fuel bindings first rest _ resolved rfl rfl,
                  matchValue_cons_view_other bindings first rest _ rfl]
                exact ⟨rfl, fun _ never => by cases never⟩
            | expression values =>
                cases values with
                | nil =>
                    rw [unifyPattern_cons_view_other fuel bindings first rest _ resolved rfl rfl,
                      matchValue_cons_view_other bindings first rest _ rfl]
                    exact ⟨rfl, fun _ never => by cases never⟩
                | cons head tail =>
                    rw [unifyPattern_cons_view fuel bindings first rest head tail resolved,
                      matchValue_cons_view bindings first rest head tail]
                    simp only [atomSize, atomSize.listSize] at small
                    have headGround : isGroundAtom head = true :=
                      isGround_of_mem List.mem_cons_self ground
                    have tailGround := isGround_tail ground
                    have firstStep := ih bindings first head range headGround (by omega)
                    rw [firstStep.1]
                    cases matched : matchValue bindings first head with
                    | none => exact ⟨rfl, fun _ never => by simp at never⟩
                    | some middle =>
                        simp only [ofMatch_some, Unified.ok_andThen, Option.bind_some]
                        have tailSize : atomSize (.expression tail) = atomSize.listSize tail + 1 := by
                          simp [atomSize]
                        exact ih middle rest (.expression tail) (firstStep.2 middle matched) tailGround
                          (by omega)

/-! ## Calls, `match` and `remove-atom` on ground values -/

/-- **A call with ground arguments**: an equation's argument patterns unify with
the arguments exactly when they match them element by element, as `Eval.clauses`
selects (`matchValues`), with the same substitution. -/
theorem arguments_ground {bindings : Subst} {patterns values : List Atom}
    (range : GroundRange bindings) (ground : ∀ value ∈ values, isGroundAtom value = true) :
    unifyArguments bindings patterns values =
      ofMatch (matchValue.matchValues bindings patterns values) := by
  unfold unifyArguments
  generalize fuelEq : fuelFor bindings (.expression patterns) (.expression values) = fuel
  have enough : ∀ item ∈ patterns, ∀ other ∈ values, atomSize item + atomSize other < fuel := by
    intro item member other otherMember
    have one := atomSize_lt_of_mem member
    have two := atomSize_lt_of_mem otherMember
    rw [← fuelEq]
    unfold fuelFor
    omega
  -- the list case of `unifyPattern_ground`, at this fuel
  have lists : ∀ (patterns values : List Atom) (current : Subst), GroundRange current →
      (∀ item ∈ values, isGroundAtom item = true) →
      (∀ item ∈ patterns, ∀ other ∈ values, atomSize item + atomSize other < fuel) →
      unifyLists (unifyPattern fuel) current patterns values =
        ofMatch (matchValue.matchValues current patterns values) := by
    intro patterns
    induction patterns with
    | nil => intro values _ _ _ _; cases values <;> simp [unifyLists, matchValue.matchValues]
    | cons first rest restIh =>
        intro values current currentRange groundValues smallPairs
        cases values with
        | nil => simp [unifyLists, matchValue.matchValues]
        | cons value remaining =>
            have here := unifyPattern_ground fuel current first value currentRange
              (groundValues value List.mem_cons_self)
              (smallPairs first List.mem_cons_self value List.mem_cons_self)
            simp only [unifyLists, matchValue.matchValues]
            rw [here.1]
            cases matched : matchValue current first value with
            | none => simp
            | some middle =>
                simp only [ofMatch_some, Unified.ok_andThen, Option.bind_eq_bind, Option.bind_some]
                exact restIh remaining middle (here.2 middle matched)
                  (fun item member => groundValues item (List.mem_cons_of_mem _ member))
                  (fun item member other otherMember =>
                    smallPairs item (List.mem_cons_of_mem _ member) other
                      (List.mem_cons_of_mem _ otherMember))
  exact lists patterns values bindings range ground enough

/-- The bodies that matching selects: for each equation, renamed apart for its
own use, its body under the substitution of its renamed argument patterns
matched against the arguments, in row order. -/
def matchedBodies (bindings : Subst) (values : List Atom) :
    Nat → List SpaceSemantics.Equation → List Control
  | _, [] => []
  | use, equation :: rest =>
      match matchValue.matchValues bindings (equation.arguments.map (rename use)) values with
      | some bound => .evaluate bound (rename use equation.body) ::
          matchedBodies bindings values (use + 1) rest
      | none => matchedBodies bindings values (use + 1) rest

/-- **A call with ground arguments selects, in row order, the bodies of the
equations whose renamed argument patterns match the arguments**, each under the
matching substitution. -/
theorem selections_ground {bindings : Subst} {values : List Atom}
    (range : GroundRange bindings) (ground : ∀ value ∈ values, isGroundAtom value = true) :
    ∀ (use : Nat) (chosen : List SpaceSemantics.Equation),
      selections bindings values use chosen =
        some (matchedBodies bindings values use chosen)
  | _, [] => rfl
  | use, equation :: rest => by
      simp only [selections, selections_ground range ground (use + 1) rest, Option.bind_eq_bind,
        Option.bind_some, matchedBodies]
      rw [arguments_ground range ground]
      cases matchValue.matchValues bindings (equation.arguments.map (rename use)) values <;> rfl

/-- `rename` leaves a ground term as it is. -/
theorem rename_ground (use : Nat) :
    ∀ term : Atom, isGroundAtom term = true → rename use term = term
  | .var _, ground => by simp [isGroundAtom] at ground
  | .symbol _, _ => rfl
  | .grounded _, _ => rfl
  | .expression items, ground => by
      simp only [rename]
      congr 1
      exact list items (by simpa [isGroundAtom] using ground)
where
  list : ∀ items : List Atom, isGroundAtom.isGroundList items = true →
      rename.renameList use items = items
    | [], _ => rfl
    | first :: rest, ground => by
        simp only [isGroundAtom.isGroundList, Bool.and_eq_true] at ground
        simp only [rename.renameList, rename_ground use first ground.1, list rest ground.2]

/-- Unifying with a ground term, on a substitution whose values are ground, at the
fuel `unify` gives. -/
theorem unify_ground {bindings : Subst} {pattern value : Atom} (range : GroundRange bindings)
    (ground : isGroundAtom value = true) :
    unify bindings pattern value = ofMatch (matchAtom bindings pattern value) := by
  unfold unify
  exact unifyTerms_ground _ bindings pattern value range ground (by unfold fuelFor; omega)

/-- Ground declarations rule out exhaustion in the actual two-sided row
matcher, independently of the body's later evaluation. -/
theorem queryRows_ground {Row Packet : Type} (label : Row → Atom) (emit : Row → Subst → Packet)
    {bindings : Subst} {pattern : Atom} (range : GroundRange bindings) :
    ∀ (use : Nat) (rows : List Row), (∀ row ∈ rows, isGroundAtom (label row) = true) →
      queryRows label emit bindings pattern use rows =
        some (rows.filterMap fun row => (matchAtom bindings pattern (label row)).map (emit row))
  | _, [], _ => rfl
  | use, row :: rest, ground => by
      have term := ground row List.mem_cons_self
      simp only [queryRows, queryRows_ground label emit range (use + 1) rest
        (fun item member => ground item (List.mem_cons_of_mem _ member)), Option.bind_eq_bind,
        Option.bind_some, rename_ground use (label row) term, unify_ground range term,
        List.filterMap_cons]
      cases matchAtom bindings pattern (label row) <;> rfl

/-- **`match` on ground rows**: the body runs once for each row the pattern
matches (`matchAtom`, no list view), in row order, under that row's bindings. -/
theorem queryBodies_ground {bindings : Subst} {pattern body : Atom} (range : GroundRange bindings) :
    ∀ (use : Nat) (rows : List Atom), (∀ row ∈ rows, isGroundAtom row = true) →
      queryBodies bindings pattern body use rows =
        some (rows.filterMap fun row => (matchAtom bindings pattern row).map fun bound =>
          Control.evaluate bound body) :=
  queryRows_ground id (fun _ bound => Control.evaluate bound body) range

/-- Ordered occurrence/binding hits on a ground view; the row proof
`queryRows_ground` justifies using the slot-independent matcher here. -/
def groundHits {Row : Type} (label : Row → Atom) (rows : List Row)
    (bindings : Subst) (pattern : Atom) : List (Row × Subst) :=
  rows.filterMap fun row => (matchAtom bindings pattern (label row)).map (Prod.mk row)

theorem groundHits_append_unmatched {Row : Type} (label : Row → Atom) (rows extra : List Row)
    (bindings : Subst) (pattern : Atom)
    (clashes : ∀ row ∈ extra, matchAtom bindings pattern (label row) = none) :
    groundHits label (rows ++ extra) bindings pattern = groundHits label rows bindings pattern := by
  have noHits : groundHits label extra bindings pattern = [] := by
    induction extra with
    | nil => rfl
    | cons row rest ih =>
      simp only [groundHits, List.filterMap_cons, clashes row List.mem_cons_self, Option.map_none]
      exact ih (fun item member => clashes item (List.mem_cons_of_mem _ member))
  unfold groundHits
  rw [List.filterMap_append]
  change groundHits label rows bindings pattern ++ groundHits label extra bindings pattern = _
  rw [noHits, List.append_nil]
  rfl

private theorem groundHits_range {Row : Type} {label : Row → Atom} {rows : List Row}
    {bindings : Subst} {pattern : Atom}
    (ground : ∀ row ∈ rows, isGroundAtom (label row) = true) (range : GroundRange bindings)
    {branch : Row × Subst} (member : branch ∈ groundHits label rows bindings pattern) :
    GroundRange branch.2 := by
  obtain ⟨row, present, packet⟩ := List.mem_filterMap.mp member
  obtain ⟨bound, matched, rfl⟩ := Option.map_eq_some_iff.mp packet
  exact matchAtom_groundRange range (ground row present) matched

/-- Reserve the complete compound capture's freshening range. Every reached
leg charges one full view. At the last leg no row needs to be matched to
compute this charge. Earlier prefixes may still need to be examined. -/
def groundQueryCharge {Row : Type} (label : Row → Atom) (rows : List Row) : List Atom → Subst → Nat
  | [], _ => 0
  | pattern :: legs, bindings =>
      rows.length + (if legs.isEmpty then 0 else
        ((groundHits label rows bindings pattern).map
          (fun branch => groundQueryCharge label rows legs branch.2)).sum)

private theorem queryBranches_with_charge {In Out : Type} (child : Nat → In → Option (List Out × Nat))
    (charge : In → Nat) (hits : List In)
    (children : ∀ item ∈ hits, ∀ use, ∃ packets, child use item = some (packets, charge item))
    (use : Nat) : ∃ packets, queryBranches child use hits = some (packets, (hits.map charge).sum) := by
  induction hits generalizing use with
  | nil => exact ⟨[], rfl⟩
  | cons first rest ih =>
      obtain ⟨packets, here⟩ := children first List.mem_cons_self use
      obtain ⟨later, tail⟩ :=
        ih (fun item member => children item (List.mem_cons_of_mem _ member)) (use + charge first)
      exact ⟨packets ++ later, by simp only [queryBranches, here, tail, Option.bind_eq_bind,
        Option.bind_some, List.map_cons, List.sum_cons]⟩

/-- The charge certificate is derived from groundness and the earlier
prefix counts, not from having enumerated the final answers already. -/
theorem queryJoin_ground_charge {Row : Type} (label : Row → Atom) (rows : List Row)
    (ground : ∀ row ∈ rows, isGroundAtom (label row) = true) (legs : List Atom)
    (bindings : Subst) (range : GroundRange bindings) (use : Nat) :
    ∃ packets, queryJoin label rows legs bindings use =
      some (packets, groundQueryCharge label rows legs bindings) := by
  induction legs generalizing bindings use with
  | nil => exact ⟨_, rfl⟩
  | cons pattern legs ih =>
      let hits := groundHits label rows bindings pattern
      let child (next : Nat) (branch : Row × Subst) :=
        (queryJoin label rows legs branch.2 next).map
          (fun (tails, spent) =>
            (tails.map (fun tail : List Row × Subst => (branch.1 :: tail.1, tail.2)), spent))
      let charge (branch : Row × Subst) := groundQueryCharge label rows legs branch.2
      have scanned : queryRows label Prod.mk bindings pattern use rows = some hits :=
        queryRows_ground label Prod.mk range use rows ground
      have completes (branch : Row × Subst) (member : branch ∈ hits) (next : Nat) :
          ∃ packets, child next branch = some (packets, charge branch) := by
        have preserved := groundHits_range ground range member
        obtain ⟨later, prepared⟩ := ih branch.2 preserved next
        exact ⟨later.map (fun tail => (branch.1 :: tail.1, tail.2)),
          by simp only [child, charge, prepared, Option.map_some]⟩
      obtain ⟨packets, continued⟩ :=
        queryBranches_with_charge child charge hits completes (use + rows.length)
      have charged :
          groundQueryCharge label rows (pattern :: legs) bindings =
            rows.length + (hits.map charge).sum := by
        cases legs with
        | nil => simp [groundQueryCharge, charge]
        | cons next later => rfl
      refine ⟨packets, ?_⟩
      rw [charged, queryJoin, scanned]
      change (queryBranches child (use + rows.length) hits).bind _ = _
      rw [continued]
      rfl

private theorem queryBranches_of_same_receipts {In Out : Type}
    (left right : Nat → In → Option (List Out × Nat)) (inputs : List In)
    (same : ∀ item ∈ inputs, ∀ first second, left first item = right second item)
    (first second : Nat) : queryBranches left first inputs = queryBranches right second inputs := by
  induction inputs generalizing first second with
  | nil => rfl
  | cons item rest ih =>
      simp only [queryBranches, same item List.mem_cons_self first second]
      cases right second item with
      | none => rfl
      | some result =>
        rcases result with ⟨replies, used⟩
        simp only [Option.bind_eq_bind, Option.bind_some]
        rw [ih (fun next member => same next (List.mem_cons_of_mem _ member)) (first + used) (second + used)]

/-- A prepared join can be reused across two ground views even at
different freshening supplies, provided the ordered physical hits at
each admitted query agree and the view widths agree. Width matters for
the exact allocation charge even when only nonmatches were edited. -/
theorem queryJoin_ground_reuse {Row : Type} (label : Row → Atom) (old current : List Row)
    (width : old.length = current.length)
    (oldGround : ∀ row ∈ old, isGroundAtom (label row) = true)
    (newGround : ∀ row ∈ current, isGroundAtom (label row) = true)
    (legs : List Atom)
    (screen : ∀ leg ∈ legs, ∀ bindings, GroundRange bindings →
      groundHits label old bindings leg = groundHits label current bindings leg)
    (bindings : Subst) (range : GroundRange bindings) (savedUse liveUse : Nat) :
    queryJoin label old legs bindings savedUse = queryJoin label current legs bindings liveUse := by
  induction legs generalizing bindings savedUse liveUse with
  | nil => rfl
  | cons pattern rest ih =>
    let hits := groundHits label old bindings pattern
    let children (view : List Row) (use : Nat) (branch : Row × Subst) :=
      (queryJoin label view rest branch.2 use).map (fun (packets, spent) =>
        (packets.map (fun tail : List Row × Subst => (branch.1 :: tail.1, tail.2)), spent))
    have sameChildren (branch : Row × Subst) (member : branch ∈ hits) (first second : Nat) :
        children old first branch = children current second branch := by
      unfold children
      rw [ih (fun leg present => screen leg (List.mem_cons_of_mem _ present)) _
        (groundHits_range oldGround range member) first second]
    have oldRead : queryRows label Prod.mk bindings pattern savedUse old = some hits :=
      queryRows_ground label Prod.mk range savedUse old oldGround
    have currentRead : queryRows label Prod.mk bindings pattern liveUse current = some hits :=
      (queryRows_ground label Prod.mk range liveUse current newGround).trans
        (congrArg some (screen pattern List.mem_cons_self bindings range).symm)
    simp only [queryJoin, oldRead, currentRead, Option.bind_eq_bind, Option.bind_some]
    change (queryBranches (children old) (savedUse + old.length) hits).bind _ =
      (queryBranches (children current) (liveUse + current.length) hits).bind _
    rw [queryBranches_of_same_receipts _ _ _ sameChildren, width]

/-- **`remove-atom` on ground rows** keeps exactly the rows `Effects.erase` keeps. -/
theorem survivors_ground {first : Atom} {others : List Atom} :
    ∀ (use : Nat) (rows : List Atom), (∀ row ∈ rows, isGroundAtom row = true) →
      survivors (.expression (first :: others)) use rows =
        some (rows.filter fun row => !Effects.removalMatches (.expression (first :: others)) row)
  | _, [], _ => rfl
  | use, row :: rest, ground => by
      have rowGround := ground row List.mem_cons_self
      simp only [survivors, survivors_ground (use + 1) rest
        (fun item member => ground item (List.mem_cons_of_mem _ member)), Option.bind_eq_bind,
        Option.bind_some, rename_ground use row rowGround,
        unify_ground (bindings := []) (fun _ never => by cases never) rowGround, List.filter_cons,
        Effects.removalMatches]
      cases matchAtom [] (.expression (first :: others)) row <;> simp

/-! ## Where the two part -/

/-- The head `(z 0)` against the open argument `$u`: no match, and the
unifier `$u = 0`. Against the ground argument `1`: neither. -/
theorem open_argument_separates :
    matchValue.matchValues [] [.grounded (.int 0)] [.var "u"] = none ∧
      unifyArguments [] [.grounded (.int 0)] [.var "u"] = .ok [("u", .grounded (.int 0))] ∧
      matchValue.matchValues [] [.grounded (.int 0)] [.grounded (.int 1)] = none ∧
      unifyArguments [] [.grounded (.int 0)] [.grounded (.int 1)] = .clash := by
  decide +kernel

end Mettapedia.Languages.MeTTa.PeTTa.Unifying
