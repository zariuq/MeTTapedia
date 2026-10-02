import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.CaseTree
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.RecursorDerivation

/-!
# Typed case trees

A case tree is typed in a context of pattern variables at a type
(`CaseTree.LeavesTyped`). A leaf is typed when its right side has the type. A
split is typed when the variable it inspects has the type of an inductive type,
the branches list that type's constructors in order, each declared at its
constructor type, and each branch is typed in the context in which the
inspected variable is replaced by the constructor's fields, at the type
instantiated by the constructor applied to the fields. So every leaf is reached
with a context of pattern variables, whose types come from the starting context
and the field types of the constructors on the way, and with the substitution
of the starting context by the leaf's patterns (`CaseTree.TypedLeaf`).

A typed tree covers and is scoped. Evaluating it at a typed instance of its
context gives a term of the instantiated type, given the facts about the
weak-head forms of the package's types, which invert the typing of a constructor
form into typings of its arguments.

A constant `f : Π Θ. C` computes by a typed case tree (`DeclaresCaseTree`) when
its role carries the tree's inspection skeleton, the tree is typed in `Θ` at
`C` in a package that declares `f` at its type, and the tree's steps are root
steps of the package. Then

* at every typed instance of a leaf's context, `f` applied to the instantiated
  patterns is equal, in the typed equality, to the instantiated right side, at
  the instantiated result type (`DeclaresCaseTree.leaf_equation`);
* a root step of the tree from a typed application gives a term of the same
  type (`DeclaresCaseTree.step_preserves`): subject reduction for the tree's
  root steps.

A package whose root steps are all steps of covering trees meets the root-shape
obligations of weak-head reduction (`RootShape.of_caseTrees`).

The two earlier kinds of definition are instances. A definition by one equation
computes by the tree with one leaf (`DeclaresDefinition.declaresCaseTree`). A
definition by structural recursion on one argument computes by the tree with
one split and a leaf for each constructor, the recursive calls substituted for
their hypotheses (`DeclaresRecursion.declaresCaseTree`). Each step of that tree
is an equation of the recursion, and each equation is a step of the tree when
the constructors have distinct names (`recursionTree_step`), so the subject
reduction of trees gives back the subject reduction of those equations.

Positive example: `max zero y = y; max x zero = x;
max (succ x) (succ y) = succ (max x y)` over the numbers computes by a tree with
two nested splits. Its leaf under `succ`, `succ` is typed in the context
`x : num, y : num`, and `max (succ a) (succ b)` is equal to `succ (max a b)` at
`num` for all `a` and `b` typed at `num` (`TowerCaseTreesModel.max_succ_succ_equal`).
Negative example: the tree `bad zero = junk; bad (succ n) = n`, with `junk` an
undeclared constant, covers and is scoped, but its first leaf is not typed;
`bad zero` is typed at `num` and steps to `junk`, which has no type, so the root
steps of that package do not preserve typing
(`TowerCaseTreesModel.bad_not_preserving`). Both are in
`Instances.TowerCaseTreesTyped`.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open TelescopeAbstraction (closeType applyClosed applyClosed_subst liftClosed_zero)

open UniverseLevel (LevelOrder)

variable {Head : Type}

/-! ## Arguments of telescopes and pattern contexts -/

/-- The arguments of a substitution of a context are its values at the
context's variables, left to right. -/
theorem telescopeArgs_eq_map_varTerms {m : Nat} :
    ∀ {n : Nat} (Γ : Ctx Head n) (σ : Sub Head n m),
      telescopeArgs Γ σ = (varTerms n).map (Presentation.subst σ)
  | _, .nil, _ => rfl
  | n + 1, .snoc Γ _, σ => by
      have tail : (Presentation.subst σ ∘ Presentation.rename wk : Tm Head n → Tm Head m) =
          Presentation.subst (tailSub σ) := funext fun t => subst_rename_wk σ t
      show telescopeArgs Γ (tailSub σ) ++ [σ 0] =
        ((varTerms n).map (Presentation.rename wk) ++ [Tm.var 0]).map (Presentation.subst σ)
      rw [telescopeArgs_eq_map_varTerms Γ (tailSub σ), List.map_append, List.map_map, tail]
      rfl

/-- A substitution is recovered from its arguments. -/
theorem valueSub_telescopeArgs {n m : Nat} (Γ : Ctx Head n) (σ : Sub Head n m) :
    valueSub n (telescopeArgs Γ σ) = σ := by
  funext i
  rw [telescopeArgs_eq_map_varTerms]
  exact valueSub_map_varTerms σ i

/-- The arguments of the substitution by a list of values are the values. -/
theorem telescopeArgs_valueSub {n m : Nat} (Γ : Ctx Head n) {values : List (Tm Head m)}
    (length : values.length = n) : telescopeArgs Γ (valueSub n values) = values := by
  rw [telescopeArgs_eq_map_varTerms]
  exact varTerms_map_valueSub length

/-- The arguments of the identity substitution are the variables. -/
theorem telescopeArgs_ids {n : Nat} (Γ : Ctx Head n) : telescopeArgs Γ ids = varTerms n := by
  rw [telescopeArgs_eq_map_varTerms]
  exact (List.map_congr_left fun t _ => subst_ids t).trans (List.map_id _)

/-- The arguments of a context extended by entries, under a substitution
extended by values. -/
theorem telescopeArgs_extendSub {n m : Nat} (Γ : Ctx Head n)
    (entry : (j : Nat) → Tm Head (n + j)) (ρ : Sub Head n m) (values : Nat → Tm Head m) :
    ∀ (b : Nat), telescopeArgs (extendEntries Γ entry b) (extendSub ρ values b) =
      telescopeArgs Γ ρ ++ (List.range b).map values
  | 0 => (List.append_nil _).symm
  | b + 1 => by
      show telescopeArgs (extendEntries Γ entry b) (extendSub ρ values b) ++ [values b] = _
      rw [telescopeArgs_extendSub Γ entry ρ values b, List.range_succ, List.map_append,
        List.append_assoc]
      rfl

/-- The arguments of a pattern context under a match: the arguments before the
scrutinee, the fields, and the arguments after it. -/
theorem telescopeArgs_matchSub (T c : DeclName) (e : (i : Nat) → Tm Head i) (s : Nat)
    (fields : List (Field Head)) {m : Nat} {as : List (Tm Head m)}
    (length : as.length = fields.length) :
    ∀ (d : Nat) (σ : Sub Head (s + 1 + d) m),
      telescopeArgs (patternCtx T c e s d fields) (matchSub s fields.length as d σ) =
        telescopeArgs (ofEntries e s) (prefixSub s d σ) ++ as ++ suffixArgs s d σ
  | 0, σ => by
      show telescopeArgs (extendEntries (ofEntries e s) _ fields.length)
        (extendSub (tailSub σ) (fun l => as.getD l defaultTm) fields.length) = _
      rw [telescopeArgs_extendSub, ← length, range_map_getD]
      exact (List.append_nil _).symm
  | d + 1, σ => by
      show telescopeArgs (patternCtx T c e s d fields)
        (matchSub s fields.length as d (tailSub σ)) ++ [σ 0] = _
      rw [telescopeArgs_matchSub T c e s fields length d (tailSub σ)]
      exact List.append_assoc _ _ _

/-- The values a substitution of a pattern context gives the fields, in
order: its instances of the pattern's own fields. -/
def fieldValues {m : Nat} (s a d : Nat) (τ : Sub Head (s + a + d) m) : List (Tm Head m) :=
  (patternFields s a d).map (Presentation.subst τ)

/-- There is one value for each field. -/
theorem fieldValues_length {m : Nat} (s a d : Nat) (τ : Sub Head (s + a + d) m) :
    (fieldValues s a d τ).length = a :=
  (List.length_map _).trans (length_patternFields s a d)

/-- Every substitution of a pattern context is the match of its own instance
of the pattern, at the values it gives the fields. -/
theorem matchSub_fieldValues {m : Nat} (s a d : Nat) (c : DeclName)
    (τ : Sub Head (s + a + d) m) :
    matchSub s a (fieldValues s a d τ) d
      (fun ι => Presentation.subst τ (patternSub s a d c ι)) = τ := by
  have h := subst_matchSub (s := s) (a := a) τ (patternFields s a d) d (patternSub s a d c)
  rw [matchSub_pattern s a c d] at h
  exact h.symm

/-- Under a substitution of a pattern context, the scrutinee of the pattern is
the constructor applied to the values of the fields. -/
theorem scrutOf_subst_patternSub {m : Nat} (s a d : Nat) (c : DeclName)
    (τ : Sub Head (s + a + d) m) :
    scrutOf s d (fun ι => Presentation.subst τ (patternSub s a d c ι)) =
      appSpine (.const c) (fieldValues s a d τ) := by
  have key : (fun ι => Presentation.subst τ (patternSub s a d c ι)) =
      replaceScrut s (appSpine (.const c) (fieldValues s a d τ)) d
        (fun ι => Presentation.subst τ (patternSub s a d c ι)) := by
    funext ι
    have h := subst_matchSub_patternSub c (fieldValues s a d τ) (fieldValues_length s a d τ) d
      (fun ι => Presentation.subst τ (patternSub s a d c ι)) ι
    rw [matchSub_fieldValues] at h
    exact h
  exact (congrArg (scrutOf s d) key).trans (scrutOf_replaceScrut _ d _)

/-- The arguments of a pattern context under a substitution, and the arguments
of the telescope under the substitution's instance of the pattern: the second
list has the constructor applied to the fields where the first has the
fields. -/
theorem telescopeArgs_patternSub (T c : DeclName) (e : (i : Nat) → Tm Head i) (s d : Nat)
    (fields : List (Field Head)) {m : Nat} (τ : Sub Head (s + fields.length + d) m) :
    ∃ before args after : List (Tm Head m), before.length = s ∧ args.length = fields.length ∧
      after.length = d ∧
      telescopeArgs (patternCtx T c e s d fields) τ = before ++ args ++ after ∧
      telescopeArgs (ofEntries e (s + 1 + d))
          (fun ι => Presentation.subst τ (patternSub s fields.length d c ι)) =
        before ++ appSpine (.const c) args :: after := by
  refine ⟨telescopeArgs (ofEntries e s)
      (prefixSub s d fun ι => Presentation.subst τ (patternSub s fields.length d c ι)),
    fieldValues s fields.length d τ,
    suffixArgs s d fun ι => Presentation.subst τ (patternSub s fields.length d c ι),
    telescopeArgs_length _ _, fieldValues_length _ _ _ _, suffixArgs_length _ _, ?_, ?_⟩
  · have h := telescopeArgs_matchSub T c e s fields (fieldValues_length s fields.length d τ) d
      (fun ι => Presentation.subst τ (patternSub s fields.length d c ι))
    rw [matchSub_fieldValues] at h
    exact h
  · rw [telescopeArgs_split, scrutOf_subst_patternSub]
    exact List.append_assoc _ _ _

/-- The arguments of a telescope whose scrutinee is a constructor form, and of
the pattern context under the match. -/
theorem telescopeArgs_constructor (T : DeclName) (e : (i : Nat) → Tm Head i) {s d : Nat}
    (fields : List (Field Head)) {m : Nat} {σ : Sub Head (s + 1 + d) m} {c : DeclName}
    {before args after : List (Tm Head m)} (lengthBefore : before.length = s)
    (length : args.length = fields.length)
    (values : before ++ appSpine (.const c) args :: after =
      telescopeArgs (ofEntries e (s + 1 + d)) σ) :
    scrutOf s d σ = appSpine (.const c) args ∧
      before ++ args ++ after =
        telescopeArgs (patternCtx T c e s d fields) (matchSub s fields.length args d σ) := by
  rw [telescopeArgs_split, List.append_assoc] at values
  have values' : before ++ appSpine (.const c) args :: after =
      telescopeArgs (ofEntries e s) (prefixSub s d σ) ++ scrutOf s d σ :: suffixArgs s d σ :=
    values
  obtain ⟨hbefore, hscrut, hafter⟩ := appendCons_inj values'
    (lengthBefore.trans (telescopeArgs_length _ _).symm)
  refine ⟨hscrut.symm, ?_⟩
  rw [telescopeArgs_matchSub T c e s fields length d σ, ← hbefore, ← hafter]

/-! ## Typed substitutions of pattern contexts -/

section Typings

variable {R : Rules Head}

/-- The identity is a typed substitution of a context into itself. -/
theorem SubstMor.identity {n : Nat} (Γ : Ctx Head n) : SubstMor R Γ Γ ids := by
  intro i
  rw [subst_ids]
  exact .var i

/-- Typed substitutions compose. -/
theorem SubstMor.comp {n m k : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} {Ξ : Ctx Head k}
    {σ : Sub Head n m} {τ : Sub Head m k} (first : SubstMor R Γ Δ σ)
    (second : SubstMor R Δ Ξ τ) : SubstMor R Γ Ξ fun i => Presentation.subst τ (σ i) := by
  intro i
  have h := (first i).substitute second
  rw [subst_comp] at h
  exact h

/-- A context renaming is a typed substitution. -/
theorem SubstMor.ofCtxRen {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} {ρ : Ren n m}
    (compatible : CtxRen Γ Δ ρ) : SubstMor R Γ Δ (renSub ρ) := by
  intro i
  rw [subst_renSub, ← compatible i]
  exact .var (ρ i)

/-- The variables of the fields of a constructor are typed at the field types,
in the context extended by the fields. -/
theorem fieldVars_typed (T : DeclName) (e : (i : Nat) → Tm Head i) (s : Nat)
    (fields : List (Field Head)) :
    ∀ (b : Nat), b ≤ fields.length →
      List.Forall₂
        (fun f x => Typed R
          (extendEntries (ofEntries e s)
            (fun l => liftClosed ((fields.getD l .recursive).type T)) b)
          x (liftClosed (Field.type T f)))
        (fields.take b) (fieldVars s b)
  | 0, _ => by
      rw [List.take_zero]
      exact .nil
  | b + 1, hb => by
      rw [List.take_succ_eq_append_getElem (by omega)]
      refine List.rel_append
        (forall₂_fields_weaken (fieldVars_typed T e s fields b (by omega))) (.cons ?_ .nil)
      rw [← getD_of_lt Field.recursive (by omega : b < fields.length)]
      have h := Derivable.var (R := R)
        (Γ := Ctx.snoc (extendEntries (ofEntries e s)
          (fun l => liftClosed ((fields.getD l .recursive).type T)) b)
          (liftClosed ((fields.getD b .recursive).type T))) 0
      rw [Ctx.lookup_snoc_zero, rename_liftClosed] at h
      exact h

/-- The pattern of a constructor is a typed substitution of the prefix and the
scrutinee into the context of the prefix and the fields. -/
theorem substMor_patSub {T c : DeclName} {e : (i : Nat) → Tm Head i} {s : Nat}
    {fields : List (Field Head)} (scrutinee : e s = .const T)
    (ctor : ∀ {n : Nat} {Γ : Ctx Head n},
      Typed R Γ (.const c) (liftClosed (ctorType T fields))) :
    SubstMor R (ofEntries e (s + 1)) (fieldCtx T e s fields) (patSub s fields.length c) := by
  have fieldsTyped := fieldVars_typed (R := R) T e s fields fields.length (Nat.le_refl _)
  rw [List.take_length] at fieldsTyped
  refine SubstMor.cons (A := e s)
    (SubstMor.ofCtxRen (ctxRen_wkN (ofEntries e s) _ fields.length)) ?_
  rw [scrutinee]
  exact ctorApp_typed ctor fieldsTyped

/-- The pattern of a constructor is a typed substitution of the telescope into
the pattern context. -/
theorem substMor_patternSub {T c : DeclName} {e : (i : Nat) → Tm Head i} {s : Nat} (d : Nat)
    {fields : List (Field Head)} (scrutinee : e s = .const T)
    (ctor : ∀ {n : Nat} {Γ : Ctx Head n},
      Typed R Γ (.const c) (liftClosed (ctorType T fields))) :
    SubstMor R (ofEntries e (s + 1 + d)) (patternCtx T c e s d fields)
      (patternSub s fields.length d c) := by
  rw [ofEntries_add e (s + 1) d]
  exact SubstMor.liftN (substMor_patSub scrutinee ctor) (fun j => e (s + 1 + j)) d

end Typings

/-! ## Typed case trees -/

mutual
/-- A case tree typed at the type `A` in the context `Γ` of its pattern
variables. A leaf's right side has the type `A`. A split inspects a variable
whose type is an inductive type, and its branches are typed in the pattern
contexts of the constructors. -/
inductive CaseTree.LeavesTyped (R : Rules Head) (roles : Roles Head) :
    {vars : Nat} → Ctx Head vars → Tm Head vars → CaseTree Head → Prop where
  | leaf {vars : Nat} {Γ : Ctx Head vars} {A rhs : Tm Head vars} :
      Typed R Γ rhs A → CaseTree.LeavesTyped R roles Γ A (.leaf vars rhs)
  | split {s d : Nat} {e : (i : Nat) → Tm Head i} {A : Tm Head (s + 1 + d)} {T : DeclName}
      {ctors : List (DeclName × List (Field Head))} {branches : CaseBranches Head} :
      e s = .const T → roles T = .inductive ctors →
      CaseBranches.LeavesTyped R roles e s d A T ctors branches →
        CaseTree.LeavesTyped R roles (ofEntries e (s + 1 + d)) A (.split s T branches)
/-- The branches of a split of the variable at position `s` of the telescope
`e`, typed at `A`: one branch for each listed constructor, in order. The
constructor is declared at its constructor type, which is a type, and its
branch is typed in the context with the constructor's fields in place of the
inspected variable, at `A` instantiated by the constructor applied to the
fields. -/
inductive CaseBranches.LeavesTyped (R : Rules Head) (roles : Roles Head) :
    ((i : Nat) → Tm Head i) → (s d : Nat) → Tm Head (s + 1 + d) → DeclName →
      List (DeclName × List (Field Head)) → CaseBranches Head → Prop where
  | nil {e : (i : Nat) → Tm Head i} {s d : Nat} {A : Tm Head (s + 1 + d)} {T : DeclName} :
      CaseBranches.LeavesTyped R roles e s d A T [] .nil
  | cons {e : (i : Nat) → Tm Head i} {s d : Nat} {A : Tm Head (s + 1 + d)} {T c : DeclName}
      {fields : List (Field Head)} {ctors : List (DeclName × List (Field Head))}
      {tree : CaseTree Head} {rest : CaseBranches Head} :
      R.constantType c = some (ctorType T fields) →
      (∃ w, R.isUniverse w ∧ Typed R .nil (ctorType T fields) (.head w)) →
      CaseTree.LeavesTyped R roles (patternCtx T c e s d fields)
        (Presentation.subst (patternSub s fields.length d c) A) tree →
      CaseBranches.LeavesTyped R roles e s d A T ctors rest →
        CaseBranches.LeavesTyped R roles e s d A T ((c, fields) :: ctors)
          (.cons c fields.length tree rest)
end

section Judgment

variable {R : Rules Head} {roles : Roles Head}

/-- The branch a typed split finds for a constructor: the constructor is listed
with its fields and declared at its constructor type, and the branch is typed
in the constructor's pattern context. -/
theorem CaseBranches.LeavesTyped.find {e : (i : Nat) → Tm Head i} {s d : Nat}
    {A : Tm Head (s + 1 + d)} {T : DeclName} :
    ∀ {ctors : List (DeclName × List (Field Head))} {branches : CaseBranches Head},
      CaseBranches.LeavesTyped R roles e s d A T ctors branches →
      ∀ {c : DeclName} {count : Nat} {tree : CaseTree Head},
        branches.find c = some (count, tree) →
          ∃ fields, (c, fields) ∈ ctors ∧ fields.length = count ∧
            R.constantType c = some (ctorType T fields) ∧
            (∃ w, R.isUniverse w ∧ Typed R .nil (ctorType T fields) (.head w)) ∧
            tree.LeavesTyped R roles (patternCtx T c e s d fields)
              (Presentation.subst (patternSub s fields.length d c) A)
  | _, .nil, _, _, _, _, found => by simp [CaseBranches.find] at found
  | _, .cons c' _ _ rest, typed, c, count, tree, found => by
      cases typed with
      | cons declared formed treeTyped restTyped =>
          simp only [CaseBranches.find] at found
          split at found
          · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj found)
            subst c
            exact ⟨_, List.mem_cons_self .., rfl, declared, formed, treeTyped⟩
          · obtain ⟨fields, mem, length, declared', formed', treeTyped'⟩ :=
              CaseBranches.LeavesTyped.find restTyped found
            exact ⟨fields, List.mem_cons_of_mem _ mem, length, declared', formed', treeTyped'⟩

mutual
/-- A typed tree covers: every split lists the constructors of its inductive
type, in order. -/
theorem CaseTree.LeavesTyped.covers :
    ∀ {tree : CaseTree Head} {vars : Nat} {Γ : Ctx Head vars} {A : Tm Head vars},
      tree.LeavesTyped R roles Γ A → tree.Covers roles
  | .leaf vars rhs, _, _, _, _ => .leaf vars rhs
  | .split _ _ _, _, _, _, typed => by
      cases typed with
      | split _ role branchesTyped =>
          exact .split role (CaseBranches.LeavesTyped.cover branchesTyped)
/-- Typed branches follow the listed constructors. -/
theorem CaseBranches.LeavesTyped.cover :
    ∀ {branches : CaseBranches Head} {e : (i : Nat) → Tm Head i} {s d : Nat}
      {A : Tm Head (s + 1 + d)} {T : DeclName} {ctors : List (DeclName × List (Field Head))},
      CaseBranches.LeavesTyped R roles e s d A T ctors branches →
        CaseBranches.Cover roles ctors branches
  | .nil, _, _, _, _, _, _, typed => by
      cases typed
      exact .nil
  | .cons _ _ _ _, _, _, _, _, _, _, typed => by
      cases typed with
      | cons _ _ treeTyped restTyped =>
          exact .cons (CaseTree.LeavesTyped.covers treeTyped)
            (CaseBranches.LeavesTyped.cover restTyped)
end

mutual
/-- A typed tree is scoped: every split inspects a variable of its context,
and every leaf is over exactly the variables it is reached with. -/
theorem CaseTree.LeavesTyped.scoped :
    ∀ {tree : CaseTree Head} {vars : Nat} {Γ : Ctx Head vars} {A : Tm Head vars},
      tree.LeavesTyped R roles Γ A → tree.Scoped vars
  | .leaf _ rhs, _, _, _, typed => by
      cases typed
      exact .leaf rhs
  | .split _ _ _, _, _, _, typed => by
      cases typed with
      | split _ _ branchesTyped =>
          exact .split (by omega) (CaseBranches.LeavesTyped.scoped branchesTyped)
/-- Typed branches are scoped. -/
theorem CaseBranches.LeavesTyped.scoped :
    ∀ {branches : CaseBranches Head} {e : (i : Nat) → Tm Head i} {s d : Nat}
      {A : Tm Head (s + 1 + d)} {T : DeclName} {ctors : List (DeclName × List (Field Head))},
      CaseBranches.LeavesTyped R roles e s d A T ctors branches →
        CaseBranches.Scoped (s + 1 + d) branches
  | .nil, _, _, _, _, _, _, _ => .nil
  | .cons _ _ _ _, _, s, d, _, _, _, typed => by
      cases typed with
      | @cons _ _ _ _ _ _ fields _ _ _ _ _ treeTyped restTyped =>
          have inScope := CaseTree.LeavesTyped.scoped treeTyped
          have same : s + fields.length + d = s + 1 + d - 1 + fields.length := by omega
          exact .cons (same ▸ inScope) (CaseBranches.LeavesTyped.scoped restTyped)
end

mutual
/-- A typed tree stays typed in a larger rule package. -/
theorem CaseTree.LeavesTyped.mono {R' : Rules Head} (sub : RulesSub R R') :
    ∀ {tree : CaseTree Head} {vars : Nat} {Γ : Ctx Head vars} {A : Tm Head vars},
      tree.LeavesTyped R roles Γ A → tree.LeavesTyped R' roles Γ A
  | .leaf _ _, _, _, _, typed => by
      cases typed with
      | leaf typing => exact .leaf (Derivable.mono sub typing)
  | .split _ _ _, _, _, _, typed => by
      cases typed with
      | split scrutinee role branchesTyped =>
          exact .split scrutinee role (CaseBranches.LeavesTyped.mono sub branchesTyped)
/-- Typed branches stay typed in a larger rule package. -/
theorem CaseBranches.LeavesTyped.mono {R' : Rules Head} (sub : RulesSub R R') :
    ∀ {branches : CaseBranches Head} {e : (i : Nat) → Tm Head i} {s d : Nat}
      {A : Tm Head (s + 1 + d)} {T : DeclName} {ctors : List (DeclName × List (Field Head))},
      CaseBranches.LeavesTyped R roles e s d A T ctors branches →
        CaseBranches.LeavesTyped R' roles e s d A T ctors branches
  | .nil, _, _, _, _, _, _, typed => by
      cases typed
      exact .nil
  | .cons _ _ _ _, _, _, _, _, _, _, typed => by
      cases typed with
      | cons declared formed treeTyped restTyped =>
          obtain ⟨w, hw, typing⟩ := formed
          exact .cons (sub.constantType declared)
            ⟨w, sub.isUniverse hw, Derivable.mono sub typing⟩
            (CaseTree.LeavesTyped.mono sub treeTyped) (CaseBranches.LeavesTyped.mono sub restTyped)
end

end Judgment

/-! ## Evaluation preserves typing -/

section Preservation

variable {L : Type} [LevelOrder L] {S : Setting Head L} (facts : FormFacts S.R S.roles)
include facts

/-- The arguments of a typed constructor form are typed at the constructor's
field types. -/
theorem Typed.constructor_fields {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ)
    {T c : DeclName} {fields : List (Field Head)}
    (declared : S.R.constantType c = some (ctorType T fields)) {args : List (Tm Head n)}
    (length : args.length = fields.length) {A : Tm Head n}
    (typing : Typed S.R Γ (appSpine (.const c) args) A) :
    ∀ l, l < fields.length →
      Typed S.R Γ (args.getD l defaultTm)
        (Presentation.liftClosed ((fields.getD l .recursive).type T)) := by
  have argsK : telescopeArgs (ofEntries (ctorEntry T fields) fields.length)
      (argsSub fields.length args) = args :=
    telescopeArgs_argsSub _ _ _ length
  have typingK : Typed S.R Γ (applyClosed (ctorTele T fields) (argsSub fields.length args)
      (.const c)) A := by
    rw [applyClosed_eq_appSpine]
    show Typed S.R Γ (appSpine (.const c) (telescopeArgs (ofEntries (ctorEntry T fields)
      fields.length) (argsSub fields.length args))) A
    rw [argsK]
    exact typing
  obtain ⟨morK, _, _⟩ := Typed.telescope_inv facts formed (ctorTele T fields) (.const T)
    declared typingK
  have fieldsTyped := fields_of_substMor (R := S.R) fields.length (Nat.le_refl _) morK
  rw [List.take_length, argsK] at fieldsTyped
  exact fun l hl => forall₂_getD .recursive defaultTm fieldsTyped l hl

/-- **Evaluating a typed case tree at a typed instance of its context gives a
term of the instantiated type.** At a split the inspected value is a typed
constructor form, so its arguments are typed at the field types and the match
is a typed instance of the branch's pattern context. -/
theorem CaseTree.Eval.typed {roles : Roles Head} {m : Nat} {Δ : Ctx Head m}
    (formed : CtxFormed S.R Δ) {tree : CaseTree Head} {values : List (Tm Head m)}
    {u : Tm Head m} (eval : tree.Eval values u) :
    ∀ {vars : Nat} {Γ : Ctx Head vars} {A : Tm Head vars} {σ : Sub Head vars m},
      tree.LeavesTyped S.R roles Γ A → SubstMor S.R Γ Δ σ → values = telescopeArgs Γ σ →
        Typed S.R Δ u (Presentation.subst σ A) := by
  induction eval with
  | @leaf vars rhs values length =>
      intro vars' Γ A σ typed mor hvalues
      cases typed with
      | leaf typing =>
          subst hvalues
          rw [valueSub_telescopeArgs]
          exact typing.substitute mor
  | @split position family branches before after args c tree u lengthBefore found _ ih =>
      intro vars Γ A σ typed mor hvalues
      cases typed with
      | @split _ d e _ _ ctors _ scrutinee role branchesTyped =>
          obtain ⟨fields, _, hfields, declared, _, treeTyped⟩ := branchesTyped.find found
          obtain ⟨hscrut, hinner⟩ :=
            telescopeArgs_constructor family e fields lengthBefore hfields.symm hvalues
          have tScrut : Typed S.R Δ (appSpine (.const c) args)
              (Presentation.subst (prefixSub position d σ) (e position)) := by
            have h := SubstMor.scrut e d mor
            rw [hscrut] at h
            exact h
          have fieldTyped := Typed.constructor_fields facts formed declared hfields.symm tScrut
          have morP := SubstMor.pattern e fields fieldTyped hfields.symm d mor hscrut
          have result := ih treeTyped morP hinner
          have key : (fun ι => Presentation.subst (matchSub position fields.length args d σ)
              (patternSub position fields.length d c ι)) = σ := by
            funext ι
            rw [subst_matchSub_patternSub c args hfields.symm d σ ι, ← hscrut,
              replaceScrut_self]
          rw [subst_comp, key] at result
          exact result

end Preservation

/-! ## The leaves of a typed tree -/

/-- A leaf of a typed case tree, reached from the context `Γ` at the type `A`:
its context of pattern variables, the substitution of `Γ` by its patterns, and
its right side. A split is passed through the branch found for a constructor,
into the constructor's pattern context; the patterns are composed with the
constructor's pattern. -/
inductive CaseTree.TypedLeaf (R : Rules Head) :
    CaseTree Head → {vars₀ : Nat} → Ctx Head vars₀ → Tm Head vars₀ →
      {vars : Nat} → Ctx Head vars → Sub Head vars₀ vars → Tm Head vars → Prop where
  | leaf {vars : Nat} {Γ : Ctx Head vars} {A rhs : Tm Head vars} :
      Typed R Γ rhs A → CaseTree.TypedLeaf R (.leaf vars rhs) Γ A Γ ids rhs
  | split {s d : Nat} {e : (i : Nat) → Tm Head i} {A : Tm Head (s + 1 + d)} {T : DeclName}
      {branches : CaseBranches Head} {c : DeclName} {fields : List (Field Head)}
      {tree : CaseTree Head} {vars : Nat} {Δ : Ctx Head vars}
      {π : Sub Head (s + fields.length + d) vars} {rhs : Tm Head vars} :
      e s = .const T → branches.find c = some (fields.length, tree) →
      R.constantType c = some (ctorType T fields) →
      (∃ w, R.isUniverse w ∧ Typed R .nil (ctorType T fields) (.head w)) →
      CaseTree.TypedLeaf R tree (patternCtx T c e s d fields)
        (Presentation.subst (patternSub s fields.length d c) A) Δ π rhs →
        CaseTree.TypedLeaf R (.split s T branches) (ofEntries e (s + 1 + d)) A Δ
          (fun ι => Presentation.subst π (patternSub s fields.length d c ι)) rhs

section Leaves

variable {R : Rules Head}

/-- A neighbourhood split at the inspected variable and filled with the
arguments of the pattern context is the neighbourhood filled with the arguments
of the telescope under the pattern. -/
theorem Pat.terms_patternSub (T c : DeclName) (e : (i : Nat) → Tm Head i) (s d : Nat)
    (fields : List (Field Head)) {m : Nat} (τ : Sub Head (s + fields.length + d) m)
    {N : List Pat} (hN : Pat.varsAll N = s + 1 + d) :
    Pat.terms (Pat.splitAllAt c fields.length N s)
        (telescopeArgs (patternCtx T c e s d fields) τ) =
      Pat.terms N (telescopeArgs (ofEntries e (s + 1 + d))
        (fun ι => Presentation.subst τ (patternSub s fields.length d c ι))) := by
  obtain ⟨before, args, after, hb, ha, hd, inner, outer⟩ :=
    telescopeArgs_patternSub T c e s d fields τ
  rw [inner, outer]
  have h := Pat.terms_splitAllAt_fields c N before args after (by omega)
  rw [ha, hb] at h
  exact h

/-- **Every leaf of a typed tree is a typed leaf**: it has a context of pattern
variables and a substitution of the starting context by its patterns, which
lists the leaf's neighbourhood filled with its own variables. -/
theorem CaseTree.LeavesTyped.typedLeaf {roles : Roles Head} {tree : CaseTree Head}
    {N N' : List Pat} {vars : Nat} {rhs : Tm Head vars} (leafOf : tree.LeafOf N N' vars rhs) :
    ∀ {vars₀ : Nat} {Γ : Ctx Head vars₀} {A : Tm Head vars₀},
      tree.LeavesTyped R roles Γ A → Pat.varsAll N = vars₀ →
        ∃ (Δ : Ctx Head vars) (π : Sub Head vars₀ vars), tree.TypedLeaf R Γ A Δ π rhs ∧
          Pat.terms N' (varTerms vars) = Pat.terms N (telescopeArgs Γ π) := by
  induction leafOf with
  | leaf rhs N =>
      intro vars₀ Γ A typed _
      cases typed with
      | leaf typing => exact ⟨Γ, ids, .leaf typing, by rw [telescopeArgs_ids]⟩
  | @split position family branches c fields tree N N' vars rhs found _ ih =>
      intro vars₀ Γ A typed hN
      cases typed with
      | @split _ d e _ _ ctors _ scrutinee role branchesTyped =>
          obtain ⟨fs, _, rfl, declared, formed, treeTyped⟩ := branchesTyped.find found
          have hN' : Pat.varsAll (Pat.splitAllAt c fs.length N position) =
              position + fs.length + d := by
            have := Pat.varsAll_splitAllAt c fs.length N position (by omega)
            omega
          obtain ⟨Δ, π, leaf, same⟩ := ih treeTyped hN'
          exact ⟨Δ, _, .split scrutinee found declared formed leaf,
            same.trans (Pat.terms_patternSub family c e position d fs π hN)⟩

variable {tree : CaseTree Head} {vars₀ : Nat} {Γ : Ctx Head vars₀} {A : Tm Head vars₀}
  {vars : Nat} {Δ : Ctx Head vars} {π : Sub Head vars₀ vars} {rhs : Tm Head vars}

/-- A typed leaf stays one in a larger rule package. -/
theorem CaseTree.TypedLeaf.mono {R' : Rules Head} (sub : RulesSub R R')
    (leaf : tree.TypedLeaf R Γ A Δ π rhs) : tree.TypedLeaf R' Γ A Δ π rhs := by
  induction leaf with
  | leaf typing => exact .leaf (Derivable.mono sub typing)
  | split scrutinee found declared formed _ ih =>
      obtain ⟨w, hw, typing⟩ := formed
      exact .split scrutinee found (sub.constantType declared)
        ⟨w, sub.isUniverse hw, Derivable.mono sub typing⟩ ih

/-- The patterns of a typed leaf are a typed substitution of the starting
context into the leaf's context. -/
theorem CaseTree.TypedLeaf.patterns (leaf : tree.TypedLeaf R Γ A Δ π rhs) :
    SubstMor R Γ Δ π := by
  induction leaf with
  | leaf _ => exact SubstMor.identity _
  | split scrutinee _ declared formed _ ih =>
      obtain ⟨w, hw, typing⟩ := formed
      exact SubstMor.comp
        (substMor_patternSub _ scrutinee fun {_ _} => .const declared typing hw) ih

/-- The right side of a typed leaf is typed in the leaf's context, at the type
instantiated by the leaf's patterns. -/
theorem CaseTree.TypedLeaf.typed (leaf : tree.TypedLeaf R Γ A Δ π rhs) :
    Typed R Δ rhs (Presentation.subst π A) := by
  induction leaf with
  | leaf typing =>
      rw [subst_ids]
      exact typing
  | split _ _ _ _ _ ih =>
      rw [subst_comp] at ih
      exact ih

/-- The tree evaluates, at every instance of a typed leaf's patterns, to the
instance of the leaf's right side. -/
theorem CaseTree.TypedLeaf.eval (leaf : tree.TypedLeaf R Γ A Δ π rhs) :
    ∀ {m : Nat} (σ : Sub Head vars m),
      tree.Eval (telescopeArgs Γ fun i => Presentation.subst σ (π i))
        (Presentation.subst σ rhs) := by
  induction leaf with
  | @leaf vars Γ A rhs _ =>
      intro m σ
      have h := CaseTree.Eval.leaf rhs (values := telescopeArgs Γ σ) (telescopeArgs_length Γ σ)
      rw [valueSub_telescopeArgs] at h
      exact h
  | @split s d e A T branches c fields tree vars Δ π rhs _ found _ _ _ ih =>
      intro m σ
      obtain ⟨before, args, after, hb, ha, _, inner, outer⟩ :=
        telescopeArgs_patternSub T c e s d fields fun i => Presentation.subst σ (π i)
      have composed : (fun ι => Presentation.subst σ
          (Presentation.subst π (patternSub s fields.length d c ι))) =
          fun ι => Presentation.subst (fun i => Presentation.subst σ (π i))
            (patternSub s fields.length d c ι) :=
        funext fun ι => subst_comp σ π _
      rw [composed, outer]
      refine .split hb (by rw [ha]; exact found) ?_
      rw [← inner]
      exact ih σ

end Leaves

/-! ## Constants computing by typed case trees -/

section Declaration

variable {L : Type} [LevelOrder L]

/-- The rule package of `S` declares `f : Π Θ. C` computing by the case tree
`tree`: the role of `f` carries the tree's inspection skeleton; the tree is
typed in `Θ` at `C` in the rule package `R₁`, which declares `f` at its type;
and the tree's steps are root steps of the package. -/
structure DeclaresCaseTree (S : Setting Head L) (R₁ : Rules Head) (f : DeclName) {k : Nat}
    (Θ : Ctx Head k) (C : Tm Head k) (tree : CaseTree Head) : Prop where
  role : S.roles f = .computes k tree.inspect
  sub₁ : RulesSub R₁ S.R
  declared : R₁.constantType f = some (closeType Θ C)
  typed : ∃ w, S.R.isUniverse w ∧ Typed R₁ .nil (closeType Θ C) (.head w)
  leaves : tree.LeavesTyped R₁ S.roles Θ C
  steps : ∀ {n : Nat} {t u : Tm Head n}, tree.Step f k t u → S.R.computation.step t u

section Consequences

variable {S : Setting Head L} {R₁ : Rules Head} {f : DeclName} {k : Nat} {Θ : Ctx Head k}
  {C : Tm Head k} {tree : CaseTree Head} (decl : DeclaresCaseTree S R₁ f Θ C tree)
include decl

/-- The defined constant at its declared type, in every context. -/
theorem DeclaresCaseTree.typing {n : Nat} {Γ : Ctx Head n} :
    Typed S.R Γ (.const f) (liftClosed (closeType Θ C)) := by
  obtain ⟨w, hw, typed⟩ := decl.typed
  exact .const (decl.sub₁.constantType decl.declared) (Derivable.mono decl.sub₁ typed) hw

/-- The tree of a declared constant covers. -/
theorem DeclaresCaseTree.covers : tree.Covers S.roles :=
  CaseTree.LeavesTyped.covers decl.leaves

/-- The tree of a declared constant is scoped over its arguments. -/
theorem DeclaresCaseTree.scoped : tree.Scoped k :=
  CaseTree.LeavesTyped.scoped decl.leaves

/-- Every leaf of the tree of a declared constant has a context of pattern
variables in which it is a typed leaf; the patterns are the leaf's
neighbourhood filled with its own variables. -/
theorem DeclaresCaseTree.typedLeaf {N' : List Pat} {vars : Nat} {rhs : Tm Head vars}
    (leafOf : tree.LeafOf (List.replicate k .var) N' vars rhs) :
    ∃ (Δ : Ctx Head vars) (π : Sub Head k vars), tree.TypedLeaf R₁ Θ C Δ π rhs ∧
      Pat.terms N' (varTerms vars) = telescopeArgs Θ π := by
  obtain ⟨Δ, π, leaf, same⟩ :=
    CaseTree.LeavesTyped.typedLeaf leafOf decl.leaves (Pat.varsAll_replicate k)
  have filled := Pat.terms_replicate (telescopeArgs Θ π)
  rw [telescopeArgs_length] at filled
  exact ⟨Δ, π, leaf, same.trans filled⟩

/-- **The equation of a leaf is a typed definitional equality.** At every typed
instance `σ` of a leaf's context, `f` applied to the instantiated patterns is
equal to the instantiated right side, at the instantiated result type. -/
theorem DeclaresCaseTree.leaf_equation {vars : Nat} {Δ : Ctx Head vars} {π : Sub Head k vars}
    {rhs : Tm Head vars} (leaf : tree.TypedLeaf R₁ Θ C Δ π rhs) {n : Nat} {Γ : Ctx Head n}
    {σ : Sub Head vars n} (typed : SubstMor S.R Δ Γ σ) :
    Equal S.R Γ (applyClosed Θ (fun i => Presentation.subst σ (π i)) (.const f))
      (Presentation.subst σ rhs) (Presentation.subst σ (Presentation.subst π C)) := by
  have leaf' := leaf.mono decl.sub₁
  have source : Typed S.R Γ (applyClosed Θ (fun i => Presentation.subst σ (π i)) (.const f))
      (Presentation.subst σ (Presentation.subst π C)) := by
    rw [subst_comp]
    exact Typed.telescope_apply (SubstMor.comp leaf'.patterns typed) decl.typing
  exact .root
    (decl.steps ⟨_, applyClosed_eq_appSpine Θ _ _, telescopeArgs_length Θ _, leaf.eval σ⟩)
    source (Typed.substitute leaf'.typed typed)

end Consequences

/-! ## Subject reduction for the root steps of a tree -/

section SubjectReduction

variable {S S₀ : Setting Head L} (facts : FormFacts S.R S.roles)
include facts

/-- **A root step of a declared case tree preserves typing**, in every package
containing the declaring one: a typed application of `f` that the tree
rewrites steps to a term of the application's type. -/
theorem DeclaresCaseTree.step_preserves {R₁ : Rules Head} {f : DeclName} {k : Nat}
    {Θ : Ctx Head k} {C : Tm Head k} {tree : CaseTree Head}
    (decl : DeclaresCaseTree S₀ R₁ f Θ C tree) (sub : RulesSub S₀.R S.R) {n : Nat}
    {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {t u A : Tm Head n}
    (step : tree.Step f k t u) (typing : Typed S.R Γ t A) : Typed S.R Γ u A := by
  obtain ⟨args, rfl, length, eval⟩ := step
  have hargs := telescopeArgs_valueSub Θ length
  have typing' : Typed S.R Γ (applyClosed Θ (valueSub k args) (.const f)) A := by
    rw [applyClosed_eq_appSpine, hargs]
    exact typing
  obtain ⟨mor, _, le⟩ := Typed.telescope_inv facts formed Θ C
    (sub.constantType (decl.sub₁.constantType decl.declared)) typing'
  exact Typed.subsume
    (CaseTree.Eval.typed facts formed eval (decl.leaves.mono (decl.sub₁.trans sub)) mor
      hargs.symm) le

/-- A package all of whose root steps are steps of declared case trees
preserves typing at its root steps. -/
theorem RootPreserving.of_caseTrees {definitions : List (CaseTreeDefinition Head)}
    (declared : ∀ d ∈ definitions, ∃ (R₁ : Rules Head) (Θ : Ctx Head d.arity)
      (C : Tm Head d.arity), DeclaresCaseTree S R₁ d.name Θ C d.tree)
    (only : ∀ {n : Nat} {t u : Tm Head n}, S.R.computation.step t u →
      (caseTreeComputation definitions).step t u) : RootPreserving S.R := by
  intro n Γ l r A formed step typing
  obtain ⟨d, mem, treeStep⟩ := only step
  obtain ⟨R₁, Θ, C, decl⟩ := declared d mem
  exact decl.step_preserves facts (RulesSub.refl _) formed treeStep typing

end SubjectReduction

end Declaration

/-! ## Root shape -/

/-- A rule package all of whose root steps are steps of covering case trees,
under distinct names and with the roles carrying the trees' inspection
skeletons, meets the root-shape obligations of weak-head reduction. -/
theorem RootShape.of_caseTrees {R : Rules Head} {roles : Roles Head}
    (constructors : ConstructorsDeclared roles) {definitions : List (CaseTreeDefinition Head)}
    (names : (definitions.map CaseTreeDefinition.name).Nodup)
    (role : ∀ d ∈ definitions, roles d.name = .computes d.arity d.tree.inspect)
    (covers : ∀ d ∈ definitions, d.tree.Covers roles)
    (only : ∀ {n : Nat} {t u : Tm Head n}, R.computation.step t u →
      (caseTreeComputation definitions).step t u) : RootShape R roles where
  spine := by
    intro n t u step
    obtain ⟨d, mem, treeStep⟩ := only step
    obtain ⟨args, rfl, length, settled⟩ :=
      CaseTree.step_settled constructors (covers d mem) treeStep
    exact ⟨d.name, d.arity, _, args, role d mem, rfl, length, settled.accepts⟩
  deterministic := fun first second =>
    caseTreeComputation_deterministic names (only second) (only first)

/-- A rule package all of whose root steps are steps of typed case trees
meets the root-shape obligations: typed trees cover. -/
theorem RootShape.of_typedCaseTrees {R : Rules Head} {roles : Roles Head}
    (constructors : ConstructorsDeclared roles) {definitions : List (CaseTreeDefinition Head)}
    (names : (definitions.map CaseTreeDefinition.name).Nodup)
    (role : ∀ d ∈ definitions, roles d.name = .computes d.arity d.tree.inspect)
    (typed : ∀ d ∈ definitions, ∃ (R₁ : Rules Head) (Θ : Ctx Head d.arity)
      (C : Tm Head d.arity), d.tree.LeavesTyped R₁ roles Θ C)
    (only : ∀ {n : Nat} {t u : Tm Head n}, R.computation.step t u →
      (caseTreeComputation definitions).step t u) : RootShape R roles :=
  RootShape.of_caseTrees constructors names role
    (fun d mem => by
      obtain ⟨_, _, _, leaves⟩ := typed d mem
      exact CaseTree.LeavesTyped.covers leaves)
    only

/-! ## Definitions by one equation and by structural recursion as case trees -/

section Depth

variable {L : Type} [LevelOrder L] {S : Setting Head L}

/-- A definition by one equation computes by the case tree with one leaf: its
right side, typed in the telescope. -/
theorem DeclaresDefinition.declaresCaseTree {R₀ : Rules Head} {f : DeclName} {k : Nat}
    {Θ : Ctx Head k} {C rhs : Tm Head k} (decl : DeclaresDefinition S R₀ f Θ C rhs) :
    DeclaresCaseTree S S.R f Θ C (.leaf k rhs) where
  role := decl.role
  sub₁ := RulesSub.refl _
  declared := decl.declared
  typed := by
    obtain ⟨w, hw, typed⟩ := decl.typed
    exact ⟨w, hw, Derivable.mono decl.sub₀ typed⟩
  leaves := .leaf (Derivable.mono decl.sub₀ decl.body)
  steps := by
    rintro n t u ⟨args, rfl, length, eval⟩
    cases eval with
    | leaf _ _ =>
        have step := decl.rule (valueSub k args)
        rw [applyClosed_eq_appSpine, telescopeArgs_valueSub Θ length] at step
        exact step

/-! ### The tree of a structural recursion -/

/-- The branches of the case tree of a definition by structural recursion: for
each constructor a leaf, the constructor's right-hand side with the recursive
calls substituted for their hypotheses. -/
def recursionBranches (f : DeclName) (e : (i : Nat) → Tm Head i) (s d : Nat)
    (body : (k : DeclName) → (fields : List (Field Head)) →
      Tm Head (s + fields.length + d + (recPositions fields).length)) :
    List (DeclName × List (Field Head)) → CaseBranches Head
  | [] => .nil
  | (k, fields) :: rest =>
      .cons k fields.length
        (.leaf (s + fields.length + d)
          (Presentation.subst (hypSub f e s d fields) (body k fields)))
        (recursionBranches f e s d body rest)

/-- The case tree of a definition by structural recursion on the argument at
position `s`: one split of that argument, and a leaf for each constructor. -/
def recursionTree (f T : DeclName) (ctors : List (DeclName × List (Field Head)))
    (e : (i : Nat) → Tm Head i) (s d : Nat)
    (body : (k : DeclName) → (fields : List (Field Head)) →
      Tm Head (s + fields.length + d + (recPositions fields).length)) : CaseTree Head :=
  .split s T (recursionBranches f e s d body ctors)

section Tree

variable {f : DeclName} {e : (i : Nat) → Tm Head i} {s d : Nat}
  {body : (k : DeclName) → (fields : List (Field Head)) →
    Tm Head (s + fields.length + d + (recPositions fields).length)}

/-- After its split the tree of a structural recursion inspects nothing. -/
theorem recursionBranches_inspect :
    ∀ (cs : List (DeclName × List (Field Head))) (key : InspectKey),
      (recursionBranches f e s d body cs).inspect key = .leaf
  | [], _ => rfl
  | (k, _) :: rest, key => by
      show (if key = .const k then InspectTree.leaf
        else (recursionBranches f e s d body rest).inspect key) = .leaf
      rw [recursionBranches_inspect rest key]
      exact ite_self _

/-- The branch the tree of a structural recursion finds for a constructor is
the leaf of one of the listed constructors of that name. -/
theorem recursionBranches_find :
    ∀ {cs : List (DeclName × List (Field Head))} {c : DeclName} {count : Nat}
      {tree : CaseTree Head}, (recursionBranches f e s d body cs).find c = some (count, tree) →
        ∃ fields, (c, fields) ∈ cs ∧ fields.length = count ∧
          tree = .leaf (s + fields.length + d)
            (Presentation.subst (hypSub f e s d fields) (body c fields))
  | [], _, _, _, found => by simp [recursionBranches, CaseBranches.find] at found
  | (k, fields) :: rest, c, count, tree, found => by
      simp only [recursionBranches, CaseBranches.find] at found
      split at found
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj found)
        subst c
        exact ⟨fields, List.mem_cons_self .., rfl, rfl⟩
      · obtain ⟨fields', mem, length, htree⟩ := recursionBranches_find found
        exact ⟨fields', List.mem_cons_of_mem _ mem, length, htree⟩

/-- The branch of a listed constructor, when the listed names are distinct: the
leaf of its equation. -/
theorem recursionBranches_find_mem :
    ∀ {cs : List (DeclName × List (Field Head))}, (cs.map Prod.fst).Nodup →
      ∀ {k : DeclName} {fields : List (Field Head)}, (k, fields) ∈ cs →
        (recursionBranches f e s d body cs).find k =
          some (fields.length, .leaf (s + fields.length + d)
            (Presentation.subst (hypSub f e s d fields) (body k fields)))
  | [], _, _, _, mem => nomatch mem
  | (k', fields') :: rest, nodup, k, fields, mem => by
      rw [List.map_cons, List.nodup_cons] at nodup
      show (if k = k' then some (fields'.length, CaseTree.leaf (s + fields'.length + d)
          (Presentation.subst (hypSub f e s d fields') (body k' fields')))
        else (recursionBranches f e s d body rest).find k) = _
      rcases List.mem_cons.mp mem with same | mem'
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
        rw [if_pos rfl]
      · have inRest : k ∈ rest.map Prod.fst := List.mem_map_of_mem (f := Prod.fst) mem'
        have ne : k ≠ k' := by
          intro h
          rw [h] at inRest
          exact nodup.1 inRest
        rw [if_neg ne]
        exact recursionBranches_find_mem nodup.2 mem'

/-- Each equation of a structural recursion is a step of its tree, when the
constructors have distinct names: at a constructor form the tree takes the
constructor's branch and instantiates its leaf by the match. -/
theorem recursionTree_step {T : DeclName} {ctors : List (DeclName × List (Field Head))}
    (distinct : (ctors.map Prod.fst).Nodup) {k : DeclName} {fields : List (Field Head)}
    (mem : (k, fields) ∈ ctors) {n : Nat} (σ : Sub Head (s + 1 + d) n) (as : List (Tm Head n))
    (has : as.length = fields.length) :
    (recursionTree f T ctors e s d body).Step f (s + 1 + d)
      (applyClosed (ofEntries e (s + 1 + d)) (replaceScrut s (appSpine (.const k) as) d σ)
        (.const f))
      (Presentation.subst (matchSub s fields.length as d σ)
        (Presentation.subst (hypSub f e s d fields) (body k fields))) := by
  refine ⟨_, applyClosed_split e d _ _, ?_, ?_⟩
  · rw [List.length_append, List.length_cons, telescopeArgs_length, suffixArgs_length]
    omega
  · rw [prefixSub_replaceScrut, scrutOf_replaceScrut, suffixArgs_replaceScrut]
    refine .split (telescopeArgs_length _ _)
      (by rw [has]; exact recursionBranches_find_mem distinct mem) ?_
    have leaf := CaseTree.Eval.leaf
      (Presentation.subst (hypSub f e s d fields) (body k fields))
      (values := telescopeArgs (patternCtx T k e s d fields) (matchSub s fields.length as d σ))
      (telescopeArgs_length _ _)
    rw [valueSub_telescopeArgs, telescopeArgs_matchSub T k e s fields has d σ] at leaf
    exact leaf

end Tree

/-! ### Field variables in a pattern context -/

/-- The lookup of a context extended by closed entries, at an entry of the
extension. -/
theorem extendEntries_lookup_entry {n : Nat} (Γ : Ctx Head n) (G : Nat → Tm Head 0) :
    ∀ (b : Nat) (i : Fin (n + b)), i.val < b →
      Ctx.lookup (extendEntries Γ (fun j => liftClosed (G j)) b) i =
        liftClosed (G (b - 1 - i.val))
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | b + 1, i, h => by
      revert h
      refine Fin.cases ?_ (fun j => ?_) i
      · intro _
        show Presentation.rename wk (liftClosed (G b)) = liftClosed (G (b + 1 - 1 - 0))
        rw [rename_liftClosed]
        rfl
      · intro h
        show Presentation.rename wk
          (Ctx.lookup (extendEntries Γ (fun j => liftClosed (G j)) b) j) = _
        rw [extendEntries_lookup_entry Γ G b j (Nat.lt_of_succ_lt_succ h), rename_liftClosed]
        exact congrArg (fun q => liftClosed (G q))
          (show b - 1 - j.val = b + 1 - 1 - (j.val + 1) by omega)

/-- The variable of a field in a pattern context has the field's type. -/
theorem lookup_patternCtx_field (T c : DeclName) (e : (i : Nat) → Tm Head i) (s d : Nat)
    (fields : List (Field Head)) {l : Nat} (hl : l < fields.length) :
    Ctx.lookup (patternCtx T c e s d fields) ⟨d + (fields.length - 1 - l), by omega⟩ =
      liftClosed ((fields.getD l .recursive).type T) := by
  have index : (⟨d + (fields.length - 1 - l), by omega⟩ : Fin (s + fields.length + d)) =
      wkN d (⟨fields.length - 1 - l, by omega⟩ : Fin (s + fields.length)) :=
    Fin.ext (Nat.add_comm _ _)
  rw [index]
  show Ctx.lookup (extendEntries (fieldCtx T e s fields) _ d) _ = _
  rw [ctxRen_wkN (fieldCtx T e s fields) _ d ⟨fields.length - 1 - l, by omega⟩]
  show Presentation.rename (wkN d)
    (Ctx.lookup (extendEntries (ofEntries e s)
      (fun j => liftClosed ((fields.getD j .recursive).type T)) fields.length)
      ⟨fields.length - 1 - l, by omega⟩) = _
  rw [extendEntries_lookup_entry (ofEntries e s) (fun j => (fields.getD j .recursive).type T)
    fields.length _ (by show fields.length - 1 - l < fields.length; omega), rename_liftClosed]
  exact congrArg (fun q => liftClosed ((fields.getD q .recursive).type T))
    (show fields.length - 1 - (fields.length - 1 - l) = l by omega)

/-! ### The declaration -/

section Recursion

variable {R₀ : Rules Head} {f T : DeclName} {ctors : List (DeclName × List (Field Head))}
  {e : (i : Nat) → Tm Head i} {s d : Nat} {C : Tm Head (s + 1 + d)}
  {body : (k : DeclName) → (fields : List (Field Head)) →
    Tm Head (s + fields.length + d + (recPositions fields).length)}
  (decl : DeclaresRecursion S R₀ f T ctors e s d C body)
include decl

/-- The right-hand side of an equation of a structural recursion, with the
recursive calls substituted for their hypotheses, is typed in the equation's
pattern context: each call applies the declared constant to the prefix
variables and a recursive field's variable. -/
theorem DeclaresRecursion.equation_typed {k : DeclName} {fields : List (Field Head)}
    (mem : (k, fields) ∈ ctors) :
    Typed S.R (patternCtx T k e s d fields)
      (Presentation.subst (hypSub f e s d fields) (body k fields))
      (Presentation.subst (patternSub s fields.length d k) C) := by
  have prefixMor : SubstMor S.R (ofEntries e s) (patternCtx T k e s d fields)
      (fun i => .var ⟨i.val + fields.length + d, by omega⟩) :=
    SubstMor.ofCtxRen (CtxRen.comp (ctxRen_wkN (ofEntries e s) _ fields.length)
      (ctxRen_wkN (fieldCtx T e s fields) _ d))
  have typingF : Typed S.R (patternCtx T k e s d fields) (.const f)
      (liftClosed (closeType (ofEntries e (s + 1)) (piRange e (s + 1) d C))) := by
    rw [← closeType_ofEntries_add]
    exact decl.typing
  have calls : ∀ j, j < (recPositions fields).length →
      Typed S.R (patternCtx T k e s d fields)
        (recCall f e s fields.length d ((recPositions fields).getD j 0))
        (Presentation.subst ids
          (recCallType e s fields.length d ((recPositions fields).getD j 0) C)) := by
    intro j hj
    obtain ⟨hl, hrec⟩ := recPositions_spec fields j hj
    rw [getD_of_lt 0 hj, subst_ids]
    refine Typed.telescope_apply (SubstMor.cons (A := e s) prefixMor ?_) typingF
    show Typed S.R (patternCtx T k e s d fields)
      (if h : (recPositions fields)[j] < fields.length then
        .var ⟨d + (fields.length - 1 - (recPositions fields)[j]), by omega⟩
      else defaultTm) _
    rw [dif_pos hl, decl.scrutinee]
    have h := Derivable.var (R := S.R) (Γ := patternCtx T k e s d fields)
      ⟨d + (fields.length - 1 - (recPositions fields)[j]), by omega⟩
    rw [lookup_patternCtx_field T k e s d fields hl, hrec] at h
    exact h
  have result := Typed.substitute (Derivable.mono decl.sub₀ (decl.bodyTyped mem))
    (SubstMor.hyps
      (fun j => recCallType e s fields.length d ((recPositions fields).getD j 0) C)
      (SubstMor.identity _) (recPositions fields).length calls)
  rw [subst_extendSub_wkN, subst_ids] at result
  exact result

/-- A step of the tree of a structural recursion is one of its equations, hence
a root step of the package. -/
theorem DeclaresRecursion.tree_steps {n : Nat} {t u : Tm Head n}
    (step : (recursionTree f T ctors e s d body).Step f (s + 1 + d) t u) :
    S.R.computation.step t u := by
  obtain ⟨args, rfl, length, eval⟩ := step
  unfold recursionTree at eval
  cases eval with
  | @split _ _ _ before after as c tree' _ lengthBefore found inner =>
      obtain ⟨fields, mem, hfields, rfl⟩ := recursionBranches_find found
      cases inner with
      | leaf _ _ =>
          obtain ⟨σ, hσ⟩ : ∃ σ : Sub Head (s + 1 + d) n,
              telescopeArgs (ofEntries e (s + 1 + d)) σ =
                before ++ appSpine (.const c) as :: after :=
            ⟨_, telescopeArgs_valueSub _ length⟩
          obtain ⟨hscrut, hinner⟩ :=
            telescopeArgs_constructor T e fields lengthBefore hfields.symm hσ.symm
          have hrep : replaceScrut s (appSpine (.const c) as) d σ = σ := by
            rw [← hscrut, replaceScrut_self]
          have step := decl.rule mem σ as hfields.symm
          rw [hrep, applyClosed_eq_appSpine, hσ] at step
          rw [hinner, valueSub_telescopeArgs]
          exact step

variable {R₀' R₁' R₂' : Rules Head} {u : Head} {rec : DeclName} {v : Head}
  (ind : DeclaresInductive S R₀' R₁' R₂' T u ctors rec v)
include ind

/-- The branches of the tree of a structural recursion are typed: each
constructor is declared at its constructor type, and its equation is typed in
its pattern context. -/
theorem DeclaresRecursion.branches_typed :
    ∀ (cs : List (DeclName × List (Field Head))), (∀ p ∈ cs, p ∈ ctors) →
      CaseBranches.LeavesTyped S.R S.roles e s d C T cs (recursionBranches f e s d body cs)
  | [], _ => .nil
  | (k, fields) :: rest, sub => by
      have mem : (k, fields) ∈ ctors := sub _ (List.mem_cons_self ..)
      obtain ⟨w, hw, typing⟩ := ind.ctorTyped mem
      exact .cons (ind.ctorDeclared mem) ⟨w, hw, Derivable.mono ind.sub₁ typing⟩
        (.leaf (decl.equation_typed mem))
        (DeclaresRecursion.branches_typed rest fun p hp => sub p (List.mem_cons_of_mem _ hp))

/-- **A definition by structural recursion on one argument computes by a typed
case tree**: one split of the argument, and for each constructor the leaf of
its equation. The leaves are typed in the package itself, where the defined
constant is declared. -/
theorem DeclaresRecursion.declaresCaseTree :
    DeclaresCaseTree S S.R f (ofEntries e (s + 1 + d)) C
      (recursionTree f T ctors e s d body) where
  role := by
    have inspect : (recursionBranches f e s d body ctors).inspect = fun _ => .leaf :=
      funext (recursionBranches_inspect ctors)
    show S.roles f = .computes (s + 1 + d)
      (.split s .constructor (recursionBranches f e s d body ctors).inspect)
    rw [inspect]
    exact decl.role
  sub₁ := RulesSub.refl _
  declared := decl.declared
  typed := by
    obtain ⟨w, hw, typed⟩ := decl.typed
    exact ⟨w, hw, Derivable.mono decl.sub₀ typed⟩
  leaves := .split decl.scrutinee ind.role (decl.branches_typed ind ctors fun _ h => h)
  steps := decl.tree_steps

end Recursion

/-- The subject reduction of the tree gives back the depth-one theorem
(`DeclaresRecursion.rule_preserves`): an equation of a structural recursion
preserves typing, in every package containing the declaring one. -/
example {S₀ : Setting Head L} (facts : FormFacts S.R S.roles) {R₀ : Rules Head} {f T : DeclName}
    {ctors : List (DeclName × List (Field Head))} {e : (i : Nat) → Tm Head i} {s d : Nat}
    {C : Tm Head (s + 1 + d)}
    {body : (k : DeclName) → (fields : List (Field Head)) →
      Tm Head (s + fields.length + d + (recPositions fields).length)}
    (decl : DeclaresRecursion S₀ R₀ f T ctors e s d C body) {R₀' R₁' R₂' : Rules Head}
    {u : Head} {rec : DeclName} {v : Head}
    (ind : DeclaresInductive S₀ R₀' R₁' R₂' T u ctors rec v) (sub : RulesSub S₀.R S.R)
    {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {k : DeclName}
    {fields : List (Field Head)} (mem : (k, fields) ∈ ctors) (σ : Sub Head (s + 1 + d) n)
    (as : List (Tm Head n)) (has : as.length = fields.length) {A : Tm Head n}
    (typing : Typed S.R Γ (applyClosed (ofEntries e (s + 1 + d))
      (replaceScrut s (appSpine (.const k) as) d σ) (.const f)) A) :
    Typed S.R Γ (Presentation.subst (matchSub s fields.length as d σ)
      (Presentation.subst (hypSub f e s d fields) (body k fields))) A :=
  (decl.declaresCaseTree ind).step_preserves facts sub formed
    (recursionTree_step (S₀.constructors.distinct ind.role) mem σ as has) typing

end Depth

/-! ## Axiom audit -/

#print axioms telescopeArgs_eq_map_varTerms
#print axioms valueSub_telescopeArgs
#print axioms telescopeArgs_valueSub
#print axioms telescopeArgs_ids
#print axioms telescopeArgs_extendSub
#print axioms telescopeArgs_matchSub
#print axioms fieldValues_length
#print axioms matchSub_fieldValues
#print axioms scrutOf_subst_patternSub
#print axioms telescopeArgs_patternSub
#print axioms telescopeArgs_constructor
#print axioms SubstMor.identity
#print axioms SubstMor.comp
#print axioms SubstMor.ofCtxRen
#print axioms fieldVars_typed
#print axioms substMor_patSub
#print axioms substMor_patternSub
#print axioms CaseBranches.LeavesTyped.find
#print axioms CaseTree.LeavesTyped.covers
#print axioms CaseBranches.LeavesTyped.cover
#print axioms CaseTree.LeavesTyped.scoped
#print axioms CaseBranches.LeavesTyped.scoped
#print axioms CaseTree.LeavesTyped.mono
#print axioms CaseBranches.LeavesTyped.mono
#print axioms Typed.constructor_fields
#print axioms CaseTree.Eval.typed
#print axioms Pat.terms_patternSub
#print axioms CaseTree.LeavesTyped.typedLeaf
#print axioms CaseTree.TypedLeaf.mono
#print axioms CaseTree.TypedLeaf.patterns
#print axioms CaseTree.TypedLeaf.typed
#print axioms CaseTree.TypedLeaf.eval
#print axioms DeclaresCaseTree.typing
#print axioms DeclaresCaseTree.covers
#print axioms DeclaresCaseTree.scoped
#print axioms DeclaresCaseTree.typedLeaf
#print axioms DeclaresCaseTree.leaf_equation
#print axioms DeclaresCaseTree.step_preserves
#print axioms RootPreserving.of_caseTrees
#print axioms RootShape.of_caseTrees
#print axioms RootShape.of_typedCaseTrees
#print axioms DeclaresDefinition.declaresCaseTree
#print axioms recursionBranches_inspect
#print axioms recursionBranches_find
#print axioms recursionBranches_find_mem
#print axioms recursionTree_step
#print axioms extendEntries_lookup_entry
#print axioms lookup_patternCtx_field
#print axioms DeclaresRecursion.equation_typed
#print axioms DeclaresRecursion.tree_steps
#print axioms DeclaresRecursion.branches_typed
#print axioms DeclaresRecursion.declaresCaseTree

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
