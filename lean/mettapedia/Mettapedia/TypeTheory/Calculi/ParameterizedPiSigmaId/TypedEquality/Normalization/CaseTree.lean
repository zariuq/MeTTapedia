import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.PatternTelescopes

/-!
# Case trees

A definition by several equations over nested constructor patterns computes by
a case tree. The tree works on the values of its pattern variables, which
start as the arguments. A leaf instantiates its right side by these values. A
split inspects the value at one position: when it is a constructor spine of
one of the split's branches, the position is replaced by the spine's
arguments and the branch continues; otherwise the tree is stuck. A split with
no branches is an absurd split, over a family without constructors.

Evaluation is deterministic and commutes with renaming and substitution, so
the root steps of constants computing by case trees form a root computation.
The inspection skeleton of a tree records which position each split inspects,
given the constructors found so far. A tree steps only once every value its
skeleton inspects is a constructor spine, and never when the skeleton reaches
a neutral value.

Patterns are nameless and therefore linear: each variable occurs once, and the
variables of a list of patterns are numbered left to right. Filling the
variables with values gives the instances of a pattern; replacing one variable
by a constructor applied to fresh variables is the refinement a split makes.

Each leaf of a tree is reached with a neighbourhood, the argument patterns
its path of splits refines. A scoped tree evaluates exactly at the instances
of its leaves' neighbourhoods, to the leaves' right sides at those instances
(`CaseTree.eval_iff_leaf`): the tree computes by its leaf equations.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

variable {Head : Type}

/-! ## Values of pattern variables -/

/-- The substitution of `vars` pattern variables, listed left to right, by
`values`: the last variable is `var 0`. -/
def valueSub {n : Nat} (vars : Nat) (values : List (Tm Head n)) : Sub Head vars n :=
  fun i => values.getD (vars - 1 - i.val) defaultTm

/-- The variables of a context of `vars` pattern variables, left to right. -/
def varTerms : (vars : Nat) → List (Tm Head vars)
  | 0 => []
  | vars + 1 => (varTerms vars).map (Presentation.rename wk) ++ [.var 0]

@[simp] theorem varTerms_length : ∀ vars : Nat, (varTerms (Head := Head) vars).length = vars
  | 0 => rfl
  | vars + 1 => by simp [varTerms, varTerms_length vars]

/-- Every entry of `varTerms` is a variable. -/
theorem varTerms_var :
    ∀ {vars : Nat} {t : Tm Head vars}, t ∈ varTerms vars → ∃ i, t = .var i
  | 0, _, mem => by simp [varTerms] at mem
  | _ + 1, _, mem => by
      simp only [varTerms, List.mem_append, List.mem_map, List.mem_singleton] at mem
      rcases mem with ⟨s, hs, rfl⟩ | rfl
      · obtain ⟨i, rfl⟩ := varTerms_var hs
        exact ⟨i.succ, rfl⟩
      · exact ⟨0, rfl⟩

theorem valueSub_map {n m vars : Nat} (g : Tm Head n → Tm Head m)
    (hole : g defaultTm = defaultTm) (values : List (Tm Head n)) (i : Fin vars) :
    g (valueSub vars values i) = valueSub vars (values.map g) i := by
  simp only [valueSub, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases values[vars - 1 - i.val]? <;> simp [hole]

theorem getD_append_left {α : Type} {xs : List α} (ys : List α) {k : Nat} (d : α)
    (h : k < xs.length) : (xs ++ ys).getD k d = xs.getD k d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

/-- Instantiating the pattern variables by values gives the values. -/
theorem varTerms_map_valueSub {n : Nat} : ∀ {vars : Nat} {values : List (Tm Head n)},
    values.length = vars →
      (varTerms vars).map (Presentation.subst (valueSub vars values)) = values
  | 0, values, h => by rw [List.eq_nil_of_length_eq_zero h]; rfl
  | vars + 1, values, h => by
      obtain ⟨init, last, rfl⟩ := List.eq_nil_or_concat values |>.resolve_left
        (by rintro rfl; exact absurd h (Nat.succ_ne_zero vars).symm)
      rw [List.concat_eq_append] at h ⊢
      simp only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at h
      have tail : ∀ t : Tm Head vars,
          Presentation.subst (valueSub (vars + 1) (init ++ [last])) (Presentation.rename wk t) =
            Presentation.subst (valueSub vars init) t := by
        intro t
        rw [subst_rename]
        apply subst_ext
        intro i
        show (init ++ [last]).getD (vars + 1 - 1 - (i.val + 1)) defaultTm =
          init.getD (vars - 1 - i.val) defaultTm
        rw [getD_append_left _ _ (by omega)]
        congr 1
        omega
      have front : (varTerms vars).map (fun t =>
          Presentation.subst (valueSub (vars + 1) (init ++ [last])) (Presentation.rename wk t)) =
            init := by
        rw [List.map_congr_left (fun t _ => tail t)]
        exact varTerms_map_valueSub h
      have back : Presentation.subst (valueSub (vars + 1) (init ++ [last])) (.var 0) = last := by
        show (init ++ [last]).getD (vars + 1 - 1 - 0) defaultTm = last
        rw [show vars + 1 - 1 - 0 = init.length by omega, List.getD_eq_getElem?_getD,
          List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
        rfl
      simp only [varTerms, List.map_append, List.map_map, Function.comp_def, List.map_cons,
        List.map_nil]
      rw [front, back]

/-- A substitution is recovered from the values it gives the pattern
variables. -/
theorem valueSub_map_varTerms {n : Nat} : ∀ {vars : Nat} (σ : Sub Head vars n) (i : Fin vars),
    valueSub vars ((varTerms vars).map (Presentation.subst σ)) i = σ i
  | 0, _, i => i.elim0
  | vars + 1, σ, i => by
      have tail : ((varTerms vars).map (Presentation.rename wk)).map (Presentation.subst σ) =
          (varTerms vars).map (Presentation.subst fun j => σ j.succ) := by
        simp only [List.map_map, Function.comp_def, subst_rename]
        rfl
      simp only [varTerms, List.map_append, tail, List.map_cons, List.map_nil]
      refine Fin.cases ?_ (fun j => ?_) i
      · show (_ ++ [σ 0]).getD (vars + 1 - 1 - 0) defaultTm = σ 0
        simp [List.getD_eq_getElem?_getD]
      · show (_ ++ [σ 0]).getD (vars + 1 - 1 - (j.val + 1)) defaultTm = σ j.succ
        rw [getD_append_left _ _ (by simp; omega)]
        have := valueSub_map_varTerms (fun k => σ k.succ) j
        simp only [valueSub] at this
        rw [show vars + 1 - 1 - (j.val + 1) = vars - 1 - j.val by omega]
        exact this

/-! ## Case trees -/

mutual
/-- A case tree over a list of pattern variables. -/
inductive CaseTree (Head : Type) : Type where
  /-- The right side, over the `vars` pattern variables of this leaf. -/
  | leaf (vars : Nat) (rhs : Tm Head vars)
  /-- A split of the pattern variable at `position` over the constructors of
  `family`, one branch per constructor with its number of fields. -/
  | split (position : Nat) (family : DeclName) (branches : CaseBranches Head)
/-- The branches of a split. -/
inductive CaseBranches (Head : Type) : Type where
  | nil
  | cons (constructor : DeclName) (fields : Nat) (tree : CaseTree Head)
      (rest : CaseBranches Head)
end

/-- An absurd split: a split of a family without constructors. -/
abbrev CaseTree.absurd (position : Nat) (family : DeclName) : CaseTree Head :=
  .split position family .nil

/-- The branch of a constructor: its number of fields and its tree. -/
def CaseBranches.find : CaseBranches Head → DeclName → Option (Nat × CaseTree Head)
  | .nil, _ => none
  | .cons c fields tree rest, name => if name = c then some (fields, tree) else rest.find name

/-- The constructors of the branches, in order. -/
def CaseBranches.names : CaseBranches Head → List DeclName
  | .nil => []
  | .cons c _ _ rest => c :: rest.names

/-! ## Evaluation -/

/-- A case tree evaluates on the values of its pattern variables. -/
inductive CaseTree.Eval {n : Nat} : CaseTree Head → List (Tm Head n) → Tm Head n → Prop where
  | leaf {vars : Nat} (rhs : Tm Head vars) {values : List (Tm Head n)} :
      values.length = vars →
        CaseTree.Eval (.leaf vars rhs) values (Presentation.subst (valueSub vars values) rhs)
  | split {position : Nat} {family : DeclName} {branches : CaseBranches Head}
      {before after args : List (Tm Head n)} {c : DeclName} {tree : CaseTree Head}
      {u : Tm Head n} :
      before.length = position →
      branches.find c = some (args.length, tree) →
      CaseTree.Eval tree (before ++ args ++ after) u →
        CaseTree.Eval (.split position family branches)
          (before ++ appSpine (.const c) args :: after) u

/-- A root step of the constant `f` of the given arity computing by `tree`. -/
def CaseTree.Step (tree : CaseTree Head) (f : DeclName) (arity : Nat) {n : Nat}
    (t u : Tm Head n) : Prop :=
  ∃ args : List (Tm Head n),
    t = appSpine (.const f) args ∧ args.length = arity ∧ tree.Eval args u

/-- An absurd split never evaluates. -/
theorem CaseTree.absurd_not_eval {position : Nat} {family : DeclName} {n : Nat}
    {values : List (Tm Head n)} {u : Tm Head n} :
    ¬ (CaseTree.absurd position family : CaseTree Head).Eval values u := by
  intro eval
  cases eval with
  | split _ found => simp [CaseBranches.find] at found

theorem CaseTree.Eval.deterministic {n : Nat} {tree : CaseTree Head} {values : List (Tm Head n)}
    {u : Tm Head n} (first : tree.Eval values u) :
    ∀ {u' : Tm Head n}, tree.Eval values u' → u' = u := by
  induction first with
  | leaf rhs _ =>
      intro u' second
      cases second
      rfl
  | @split position family branches before after args c tree u lengthBefore found _ ih =>
      intro u' second
      generalize hvalues : before ++ appSpine (.const c) args :: after = values at second
      cases second with
      | @split _ _ _ before' after' args' c' tree' _ lengthBefore' found' eval' =>
          obtain ⟨rfl, rest⟩ := List.append_inj hvalues (lengthBefore.trans lengthBefore'.symm)
          obtain ⟨spine, rfl⟩ := List.cons.inj rest
          obtain ⟨rfl, rfl⟩ := appSpine_const_injective spine
          rw [found] at found'
          cases found'
          exact ih eval'

theorem CaseTree.Eval.rename {n : Nat} {tree : CaseTree Head} {values : List (Tm Head n)}
    {u : Tm Head n} (eval : tree.Eval values u) {m : Nat} (ρ : Ren n m) :
    tree.Eval (values.map (Presentation.rename ρ)) (Presentation.rename ρ u) := by
  induction eval with
  | @leaf vars rhs values length =>
      rw [rename_subst]
      have e : (fun i => Presentation.rename ρ (valueSub vars values i)) =
          valueSub vars (values.map (Presentation.rename ρ)) :=
        funext fun i => valueSub_map _ rfl values i
      rw [e]
      exact .leaf rhs (by simpa using length)
  | split lengthBefore found _ ih =>
      simp only [List.map_append, List.map_cons] at ih ⊢
      rw [rename_appSpine]
      exact .split (by simpa using lengthBefore) (by simpa using found) ih

theorem CaseTree.Eval.subst {n : Nat} {tree : CaseTree Head} {values : List (Tm Head n)}
    {u : Tm Head n} (eval : tree.Eval values u) {m : Nat} (σ : Sub Head n m) :
    tree.Eval (values.map (Presentation.subst σ)) (Presentation.subst σ u) := by
  induction eval with
  | @leaf vars rhs values length =>
      rw [subst_comp]
      have e : (fun i => Presentation.subst σ (valueSub vars values i)) =
          valueSub vars (values.map (Presentation.subst σ)) :=
        funext fun i => valueSub_map _ rfl values i
      rw [e]
      exact .leaf rhs (by simpa using length)
  | split lengthBefore found _ ih =>
      simp only [List.map_append, List.map_cons] at ih ⊢
      rw [subst_appSpine]
      exact .split (by simpa using lengthBefore) (by simpa using found) ih

theorem CaseTree.step_deterministic {tree : CaseTree Head} {f : DeclName} {arity n : Nat}
    {t u u' : Tm Head n} (first : tree.Step f arity t u) (second : tree.Step f arity t u') :
    u' = u := by
  obtain ⟨args, rfl, _, eval⟩ := first
  obtain ⟨args', same, _, eval'⟩ := second
  obtain ⟨-, rfl⟩ := appSpine_const_injective same
  exact eval.deterministic eval'

theorem CaseTree.step_rename {tree : CaseTree Head} {f : DeclName} {arity n : Nat}
    {t u : Tm Head n} (step : tree.Step f arity t u) {m : Nat} (ρ : Ren n m) :
    tree.Step f arity (Presentation.rename ρ t) (Presentation.rename ρ u) := by
  obtain ⟨args, rfl, length, eval⟩ := step
  exact ⟨args.map (Presentation.rename ρ), rename_appSpine ρ _ args, by simpa using length,
    eval.rename ρ⟩

theorem CaseTree.step_subst {tree : CaseTree Head} {f : DeclName} {arity n : Nat}
    {t u : Tm Head n} (step : tree.Step f arity t u) {m : Nat} (σ : Sub Head n m) :
    tree.Step f arity (Presentation.subst σ t) (Presentation.subst σ u) := by
  obtain ⟨args, rfl, length, eval⟩ := step
  exact ⟨args.map (Presentation.subst σ), subst_appSpine σ _ args, by simpa using length,
    eval.subst σ⟩

/-! ## Constants computing by case trees -/

/-- A constant computing by a case tree, with its arity. -/
structure CaseTreeDefinition (Head : Type) where
  name : DeclName
  arity : Nat
  tree : CaseTree Head

/-- The root steps of constants computing by case trees. -/
def caseTreeComputation (definitions : List (CaseTreeDefinition Head)) : RootComputation Head where
  step t u := ∃ d ∈ definitions, d.tree.Step d.name d.arity t u
  rename := by
    intro n m ρ t u ⟨d, mem, step⟩
    exact ⟨d, mem, CaseTree.step_rename step ρ⟩
  substitute := by
    intro n m σ t u ⟨d, mem, step⟩
    exact ⟨d, mem, CaseTree.step_subst step σ⟩

/-- Case-tree definitions under distinct names compute deterministically. -/
theorem caseTreeComputation_deterministic {definitions : List (CaseTreeDefinition Head)}
    (names : (definitions.map CaseTreeDefinition.name).Nodup) {n : Nat} {t u u' : Tm Head n}
    (first : (caseTreeComputation definitions).step t u)
    (second : (caseTreeComputation definitions).step t u') : u' = u := by
  obtain ⟨d, mem, args, rfl, length, eval⟩ := first
  obtain ⟨d', mem', args', same, length', eval'⟩ := second
  obtain ⟨sameName, rfl⟩ := appSpine_const_injective same
  obtain rfl := List.inj_on_of_nodup_map names mem mem' sameName
  exact eval.deterministic eval'

/-! ## Families covered by a tree -/

mutual
/-- Every split lists exactly the constructors of an inductive type, in order,
with their numbers of fields. -/
inductive CaseTree.Covers (roles : Roles Head) : CaseTree Head → Prop where
  | leaf (vars : Nat) (rhs : Tm Head vars) : CaseTree.Covers roles (.leaf vars rhs)
  | split {position : Nat} {family : DeclName}
      {constructors : List (DeclName × List (Field Head))} {branches : CaseBranches Head} :
      roles family = .inductive constructors →
      CaseBranches.Cover roles constructors branches →
        CaseTree.Covers roles (.split position family branches)
/-- The branches of a split follow the listed constructors. -/
inductive CaseBranches.Cover (roles : Roles Head) :
    List (DeclName × List (Field Head)) → CaseBranches Head → Prop where
  | nil : CaseBranches.Cover roles [] .nil
  | cons {c : DeclName} {fields : List (Field Head)}
      {constructors : List (DeclName × List (Field Head))} {tree : CaseTree Head}
      {rest : CaseBranches Head} :
      CaseTree.Covers roles tree → CaseBranches.Cover roles constructors rest →
        CaseBranches.Cover roles ((c, fields) :: constructors) (.cons c fields.length tree rest)
end

theorem CaseBranches.Cover.names {roles : Roles Head} :
    ∀ {constructors : List (DeclName × List (Field Head))} {branches : CaseBranches Head},
      CaseBranches.Cover roles constructors branches →
        branches.names = constructors.map Prod.fst
  | _, .nil, cover => by cases cover; rfl
  | _, .cons _ _ _ rest, cover => by
      cases cover with
      | cons _ cover' => simp [CaseBranches.names, CaseBranches.Cover.names cover']

theorem CaseBranches.Cover.find {roles : Roles Head} :
    ∀ {constructors : List (DeclName × List (Field Head))} {branches : CaseBranches Head},
      CaseBranches.Cover roles constructors branches →
      ∀ {c : DeclName} {fields : Nat} {tree : CaseTree Head},
        branches.find c = some (fields, tree) →
          (∃ fs, (c, fs) ∈ constructors ∧ fs.length = fields) ∧ tree.Covers roles
  | _, .nil, _, _, _, _, found => by simp [CaseBranches.find] at found
  | _, .cons c' _ _ rest, cover, c, fields, tree, found => by
      cases cover with
      | @cons _ fs _ tree' _ covers cover' =>
          simp only [CaseBranches.find] at found
          split at found
          · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj found)
            subst c
            exact ⟨⟨fs, List.mem_cons_self .., rfl⟩, covers⟩
          · obtain ⟨⟨fs', mem, length⟩, covers'⟩ := CaseBranches.Cover.find cover' found
            exact ⟨⟨fs', List.mem_cons_of_mem _ mem, length⟩, covers'⟩

/-- A covering split finds a declared constructor of the right arity. -/
theorem CaseBranches.Cover.constructor {roles : Roles Head} (declared : ConstructorsDeclared roles)
    {family : DeclName} {constructors : List (DeclName × List (Field Head))}
    (role : roles family = .inductive constructors) {branches : CaseBranches Head}
    (cover : CaseBranches.Cover roles constructors branches) {c : DeclName} {fields : Nat}
    {tree : CaseTree Head} (found : branches.find c = some (fields, tree)) :
    roles c = .constructor fields ∧ tree.Covers roles := by
  obtain ⟨⟨fs, mem, rfl⟩, covers⟩ := cover.find found
  exact ⟨declared.arity role mem, covers⟩

/-- The absurd split covers exactly the families without constructors. -/
theorem CaseTree.covers_absurd {roles : Roles Head} {position : Nat} {family : DeclName} :
    (CaseTree.absurd position family : CaseTree Head).Covers roles ↔
      roles family = .inductive [] := by
  constructor
  · intro covers
    cases covers with
    | split role cover =>
        cases cover
        exact role
  · intro role
    exact .split role .nil

/-! ## Scoping -/

mutual
/-- Every split inspects a position within the values, and every leaf is over
exactly the pattern variables it is reached with. -/
inductive CaseTree.Scoped : Nat → CaseTree Head → Prop where
  | leaf {vars : Nat} (rhs : Tm Head vars) : CaseTree.Scoped vars (.leaf vars rhs)
  | split {vars position : Nat} {family : DeclName} {branches : CaseBranches Head} :
      position < vars → CaseBranches.Scoped vars branches →
        CaseTree.Scoped vars (.split position family branches)
/-- Each branch is scoped over the values with the inspected one replaced by
the constructor's fields. -/
inductive CaseBranches.Scoped : Nat → CaseBranches Head → Prop where
  | nil {vars : Nat} : CaseBranches.Scoped vars .nil
  | cons {vars : Nat} {c : DeclName} {fields : Nat} {tree : CaseTree Head}
      {rest : CaseBranches Head} :
      CaseTree.Scoped (vars - 1 + fields) tree → CaseBranches.Scoped vars rest →
        CaseBranches.Scoped vars (.cons c fields tree rest)
end

theorem CaseBranches.Scoped.find :
    ∀ {vars : Nat} {branches : CaseBranches Head}, CaseBranches.Scoped vars branches →
      ∀ {c : DeclName} {fields : Nat} {tree : CaseTree Head},
        branches.find c = some (fields, tree) → tree.Scoped (vars - 1 + fields)
  | _, .nil, _, _, _, _, found => by simp [CaseBranches.find] at found
  | _, .cons c' _ _ rest, hscoped, c, fields, tree, found => by
      cases hscoped with
      | cons scopedTree scopedRest =>
          simp only [CaseBranches.find] at found
          split at found
          · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj found)
            exact scopedTree
          · exact CaseBranches.Scoped.find scopedRest found

/-! ## Inspection -/

mutual
/-- The inspection skeleton of a case tree: every split inspects a
constructor. -/
def CaseTree.inspect : CaseTree Head → InspectTree
  | .leaf _ _ => .leaf
  | .split position _ branches => .split position .constructor branches.inspect
/-- The continuation of a split, by the constructor found. -/
def CaseBranches.inspect : CaseBranches Head → InspectKey → InspectTree
  | .nil, _ => .leaf
  | .cons c _ tree rest, key => if key = .const c then tree.inspect else rest.inspect key
end

theorem CaseBranches.inspect_find :
    ∀ {branches : CaseBranches Head} {c : DeclName} {fields : Nat} {tree : CaseTree Head},
      branches.find c = some (fields, tree) → branches.inspect (.const c) = tree.inspect
  | .nil, _, _, _, found => by simp [CaseBranches.find] at found
  | .cons c' _ _ rest, c, fields, tree, found => by
      simp only [CaseBranches.find] at found
      simp only [CaseBranches.inspect, InspectKey.const.injEq]
      split at found
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj found)
        simp [*]
      · rw [if_neg (by assumption)]
        exact CaseBranches.inspect_find found

/-- Every value a skeleton inspects is accepted, down to a leaf. -/
inductive InspectTree.Settled (roles : Roles Head) {n : Nat} :
    InspectTree → List (Tm Head n) → Prop where
  | leaf (values : List (Tm Head n)) : InspectTree.Settled roles .leaf values
  | split {position : Nat} {next : InspectKey → InspectTree}
      {before after fields : List (Tm Head n)} {value : Tm Head n} {key : InspectKey} :
      before.length = position → ConstructorView roles value key fields →
      InspectTree.Settled roles (next key) (before ++ fields ++ after) →
        InspectTree.Settled roles (.split position .constructor next) (before ++ value :: after)

/-- A skeleton's inspection reaches a neutral value. -/
inductive InspectTree.Stuck (roles : Roles Head) {n : Nat} :
    InspectTree → List (Tm Head n) → Prop where
  | here {position : Nat} {shape : Inspection} {next : InspectKey → InspectTree}
      {before after : List (Tm Head n)} {value : Tm Head n} :
      before.length = position → Neutral roles value →
        InspectTree.Stuck roles (.split position shape next) (before ++ value :: after)
  | later {position : Nat} {next : InspectKey → InspectTree}
      {before after fields : List (Tm Head n)} {value : Tm Head n} {key : InspectKey} :
      before.length = position → ConstructorView roles value key fields →
      InspectTree.Stuck roles (next key) (before ++ fields ++ after) →
        InspectTree.Stuck roles (.split position .constructor next) (before ++ value :: after)

/-- A covering tree evaluates only after every value its skeleton inspects is
a constructor spine. -/
theorem CaseTree.Eval.settled {roles : Roles Head} (declared : ConstructorsDeclared roles)
    {n : Nat} {tree : CaseTree Head} {values : List (Tm Head n)} {u : Tm Head n}
    (eval : tree.Eval values u) (covers : tree.Covers roles) :
    tree.inspect.Settled roles values := by
  induction eval with
  | leaf rhs _ => exact .leaf _
  | @split position family branches before after args c tree u lengthBefore found _ ih =>
      cases covers with
      | split role cover =>
          obtain ⟨constructorRole, covers'⟩ := cover.constructor declared role found
          show InspectTree.Settled roles (.split position .constructor branches.inspect) _
          refine .split lengthBefore (.spine args constructorRole) ?_
          rw [CaseBranches.inspect_find found]
          exact ih covers'

/-- A covering tree does not evaluate when its skeleton reaches a neutral
value. -/
theorem CaseTree.Eval.not_stuck {roles : Roles Head} (declared : ConstructorsDeclared roles)
    {n : Nat} {tree : CaseTree Head} {values : List (Tm Head n)} {u : Tm Head n}
    (eval : tree.Eval values u) (covers : tree.Covers roles) :
    ¬ tree.inspect.Stuck roles values := by
  induction eval with
  | leaf rhs _ => intro stuck; cases stuck
  | @split position family branches before after args c tree u lengthBefore found _ ih =>
      cases covers with
      | split role cover =>
          obtain ⟨constructorRole, covers'⟩ := cover.constructor declared role found
          intro stuck
          change InspectTree.Stuck roles (.split position .constructor branches.inspect) _ at stuck
          generalize hvalues : before ++ appSpine (.const c) args :: after = values at stuck
          cases stuck with
          | @here _ _ _ before' after' value lengthBefore' neutral =>
              obtain ⟨rfl, rest⟩ :=
                List.append_inj hvalues (lengthBefore.trans lengthBefore'.symm)
              obtain ⟨rfl, rfl⟩ := List.cons.inj rest
              exact neutral.not_canonical (.inr ⟨c, _, args, constructorRole, rfl⟩)
          | @later _ _ before' after' fields value key lengthBefore' view stuck' =>
              obtain ⟨rfl, rest⟩ :=
                List.append_inj hvalues (lengthBefore.trans lengthBefore'.symm)
              obtain ⟨hvalue, rfl⟩ := List.cons.inj rest
              cases view with
              | spine args' _ =>
                  obtain ⟨rfl, rfl⟩ := appSpine_const_injective hvalue
                  rw [CaseBranches.inspect_find found] at stuck'
                  exact ih covers' stuck'
              | refl a => exact appSpine_const_ne_refl hvalue

/-- A step of a covering tree happens at a spine whose inspected values are
all constructor spines. -/
theorem CaseTree.step_settled {roles : Roles Head} (declared : ConstructorsDeclared roles)
    {tree : CaseTree Head} (covers : tree.Covers roles) {f : DeclName} {arity n : Nat}
    {t u : Tm Head n} (step : tree.Step f arity t u) :
    ∃ args, t = appSpine (.const f) args ∧ args.length = arity ∧
      tree.inspect.Settled roles args := by
  obtain ⟨args, rfl, length, eval⟩ := step
  exact ⟨args, rfl, length, eval.settled declared covers⟩

/-- A spine whose inspection reaches a neutral value takes no step. -/
theorem CaseTree.not_step_of_stuck {roles : Roles Head} (declared : ConstructorsDeclared roles)
    {tree : CaseTree Head} (covers : tree.Covers roles) {f : DeclName} {arity n : Nat}
    {args : List (Tm Head n)} (stuck : tree.inspect.Stuck roles args) (u : Tm Head n) :
    ¬ tree.Step f arity (appSpine (.const f) args) u := by
  rintro ⟨args', same, _, eval⟩
  obtain ⟨-, rfl⟩ := appSpine_const_injective same
  exact eval.not_stuck declared covers stuck

/-! ## Case trees in weak-head reduction -/

mutual
/-- The skeleton of a case tree inspects only constructor forms. -/
theorem CaseTree.inspect_onlyConstructors :
    (tree : CaseTree Head) → tree.inspect.OnlyConstructors
  | .leaf _ _ => .leaf
  | .split _ _ branches => .split fun key => CaseBranches.inspect_onlyConstructors branches key
/-- The continuations of a split inspect only constructor forms. -/
theorem CaseBranches.inspect_onlyConstructors :
    (branches : CaseBranches Head) → (key : InspectKey) → (branches.inspect key).OnlyConstructors
  | .nil, _ => .leaf
  | .cons c _ tree rest, key => by
      show (if key = .const c then tree.inspect else rest.inspect key).OnlyConstructors
      split
      · exact CaseTree.inspect_onlyConstructors tree
      · exact CaseBranches.inspect_onlyConstructors rest key
end

/-- Settled values are accepted by the skeleton. -/
theorem InspectTree.Settled.accepts {roles : Roles Head} {n : Nat} {tree : InspectTree}
    {values : List (Tm Head n)} (settled : tree.Settled roles values) :
    tree.Accepts roles values := by
  induction settled with
  | leaf values => exact .leaf values
  | split lengthBefore view _ ih => exact .constructor lengthBefore view ih

/-- A skeleton that is stuck inspects a neutral value next. -/
theorem InspectTree.Stuck.focus {roles : Roles Head} {n : Nat} {tree : InspectTree}
    {values : List (Tm Head n)} (stuck : tree.Stuck roles values) :
    ∃ kind a, tree.Focus roles values values kind a a ∧ Neutral roles a := by
  induction stuck with
  | here lengthBefore neutral => exact ⟨_, _, .here lengthBefore, neutral⟩
  | later lengthBefore view _ ih =>
      obtain ⟨kind, a, focus, neutral⟩ := ih
      exact ⟨kind, a, .constructor lengthBefore lengthBefore rfl view view focus, neutral⟩

/-- A constant computing by a case tree, applied to its arity, whose tree's
skeleton is stuck on the arguments is neutral. -/
theorem CaseTree.neutral_of_stuck {roles : Roles Head} {tree : CaseTree Head} {f : DeclName}
    {arity n : Nat} (role : roles f = .computes arity tree.inspect) {args : List (Tm Head n)}
    (length : args.length = arity) (stuck : tree.inspect.Stuck roles args) :
    Neutral roles (appSpine (.const f) args) := by
  obtain ⟨kind, a, focus, neutral⟩ := stuck.focus
  have constructorKind := focus.kind_of_onlyConstructors tree.inspect_onlyConstructors
  exact .stuck role length focus neutral fun headForm =>
    nomatch constructorKind.symm.trans headForm

/-! ## Patterns -/

/-- A pattern: a variable, or a constructor applied to patterns. Variables are
nameless, so every pattern is linear; the variables of a list of patterns are
numbered left to right. -/
inductive Pat where
  | var
  | con (constructor : DeclName) (args : List Pat)

mutual
/-- The number of variables of a pattern. -/
def Pat.vars : Pat → Nat
  | .var => 1
  | .con _ args => Pat.varsAll args
/-- The number of variables of a list of patterns. -/
def Pat.varsAll : List Pat → Nat
  | [] => 0
  | p :: ps => p.vars + Pat.varsAll ps
end

@[simp] theorem Pat.varsAll_nil : Pat.varsAll [] = 0 := rfl

@[simp] theorem Pat.varsAll_cons (p : Pat) (ps : List Pat) :
    Pat.varsAll (p :: ps) = p.vars + Pat.varsAll ps := rfl

@[simp] theorem Pat.vars_var : Pat.var.vars = 1 := rfl

@[simp] theorem Pat.vars_con (c : DeclName) (args : List Pat) :
    (Pat.con c args).vars = Pat.varsAll args := rfl

theorem Pat.varsAll_replicate : ∀ k : Nat, Pat.varsAll (List.replicate k .var) = k
  | 0 => rfl
  | k + 1 => by simp [List.replicate_succ, Pat.varsAll_replicate k]; omega

section Fill

variable {α : Type} (node : DeclName → List α → α) (hole : α)

mutual
/-- Fill the variables of a pattern with values, left to right; `node` applies
a constructor. -/
def Pat.fill : Pat → List α → α
  | .var, values => values.headD hole
  | .con c args, values => node c (Pat.fillAll args values)
/-- Fill a list of patterns, each taking the next values. -/
def Pat.fillAll : List Pat → List α → List α
  | [], _ => []
  | p :: ps, values => p.fill (values.take p.vars) :: Pat.fillAll ps (values.drop p.vars)
end

@[simp] theorem Pat.fillAll_length :
    ∀ (ps : List Pat) (values : List α), (Pat.fillAll node hole ps values).length = ps.length
  | [], _ => rfl
  | _ :: ps, _ => by simp [Pat.fillAll, Pat.fillAll_length ps]

theorem Pat.fillAll_append : ∀ (ps qs : List Pat) (values rest : List α),
    values.length = Pat.varsAll ps →
      Pat.fillAll node hole (ps ++ qs) (values ++ rest) =
        Pat.fillAll node hole ps values ++ Pat.fillAll node hole qs rest
  | [], _, values, _, h => by
      obtain rfl : values = [] := List.eq_nil_of_length_eq_zero (by simpa using h)
      rfl
  | p :: ps, qs, values, rest, h => by
      simp only [Pat.varsAll_cons] at h
      have hp : p.vars ≤ values.length := by omega
      simp only [List.cons_append, Pat.fillAll]
      rw [List.take_append_of_le_length hp, List.drop_append_of_le_length hp,
        Pat.fillAll_append ps qs _ rest (by simp; omega)]

theorem Pat.fillAll_replicate :
    ∀ values : List α, Pat.fillAll node hole (List.replicate values.length .var) values = values
  | [] => rfl
  | v :: vs => by
      simp only [List.length_cons, List.replicate_succ, Pat.fillAll, Pat.vars_var,
        List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero]
      rw [Pat.fillAll_replicate vs]
      rfl

variable {node hole}

/-- A variable filled by one value is that value. -/
theorem Pat.fill_var_injective {values values' : List α} (h : values.length = 1)
    (h' : values'.length = 1)
    (same : Pat.fill node hole .var values = Pat.fill node hole .var values') :
    values = values' := by
  obtain ⟨v, rfl⟩ := List.length_eq_one_iff.mp h
  obtain ⟨v', rfl⟩ := List.length_eq_one_iff.mp h'
  simp only [Pat.fill, List.headD_cons] at same
  rw [same]

mutual
theorem Pat.fill_map {β : Type} {node' : DeclName → List β → β} {hole' : β} {g : α → β}
    (hnode : ∀ c xs, g (node c xs) = node' c (xs.map g)) (hhole : g hole = hole') :
    ∀ (p : Pat) (values : List α),
      g (Pat.fill node hole p values) = Pat.fill node' hole' p (values.map g)
  | .var, [] => hhole
  | .var, _ :: _ => rfl
  | .con c args, values => by
      simp only [Pat.fill]
      rw [hnode, Pat.fillAll_map hnode hhole args values]
theorem Pat.fillAll_map {β : Type} {node' : DeclName → List β → β} {hole' : β}
    {g : α → β}
    (hnode : ∀ c xs, g (node c xs) = node' c (xs.map g)) (hhole : g hole = hole') :
    ∀ (ps : List Pat) (values : List α),
      (Pat.fillAll node hole ps values).map g = Pat.fillAll node' hole' ps (values.map g)
  | [], _ => rfl
  | p :: ps, values => by
      simp only [Pat.fillAll, List.map_cons]
      rw [Pat.fill_map hnode hhole p, Pat.fillAll_map hnode hhole ps, List.map_take, List.map_drop]
end

mutual
theorem Pat.fill_injective (inj : ∀ c xs ys, node c xs = node c ys → xs = ys) :
    ∀ (p : Pat) {values values' : List α}, values.length = p.vars → values'.length = p.vars →
      Pat.fill node hole p values = Pat.fill node hole p values' → values = values'
  | .var, _, _, h, h', same => Pat.fill_var_injective h h' same
  | .con c args, _, _, h, h', same =>
      Pat.fillAll_injective inj args h h' (inj c _ _ same)
theorem Pat.fillAll_injective (inj : ∀ c xs ys, node c xs = node c ys → xs = ys) :
    ∀ (ps : List Pat) {values values' : List α}, values.length = Pat.varsAll ps →
      values'.length = Pat.varsAll ps →
        Pat.fillAll node hole ps values = Pat.fillAll node hole ps values' → values = values'
  | [], values, values', h, h', _ => by
      rw [List.eq_nil_of_length_eq_zero (l := values) h,
        List.eq_nil_of_length_eq_zero (l := values') h']
  | p :: ps, values, values', h, h', same => by
      simp only [Pat.varsAll_cons] at h h'
      simp only [Pat.fillAll, List.cons.injEq] at same
      have first := Pat.fill_injective inj p (List.length_take_of_le (by omega))
        (List.length_take_of_le (by omega)) same.1
      have second := Pat.fillAll_injective inj ps (by rw [List.length_drop]; omega)
        (by rw [List.length_drop]; omega) same.2
      rw [← List.take_append_drop p.vars values, ← List.take_append_drop p.vars values', first,
        second]
end

end Fill

/-! ## Refinement by a split -/

mutual
/-- Replace the variable at `position` by the constructor `c` applied to
`fields` fresh variables. -/
def Pat.splitAt (c : DeclName) (fields : Nat) : Pat → Nat → Pat
  | .var, 0 => .con c (List.replicate fields .var)
  | .var, _ + 1 => .var
  | .con c' args, position => .con c' (Pat.splitAllAt c fields args position)
/-- Replace the variable at `position` of a list of patterns. -/
def Pat.splitAllAt (c : DeclName) (fields : Nat) : List Pat → Nat → List Pat
  | [], _ => []
  | p :: ps, position =>
      if position < p.vars then p.splitAt c fields position :: ps
      else p :: Pat.splitAllAt c fields ps (position - p.vars)
end

@[simp] theorem Pat.splitAllAt_length (c : DeclName) (fields : Nat) :
    ∀ (ps : List Pat) (position : Nat), (Pat.splitAllAt c fields ps position).length = ps.length
  | [], _ => rfl
  | p :: ps, position => by
      simp only [Pat.splitAllAt]
      split <;> simp [Pat.splitAllAt_length c fields ps]

mutual
theorem Pat.vars_splitAt (c : DeclName) (fields : Nat) :
    ∀ (p : Pat) (position : Nat), position < p.vars →
      (p.splitAt c fields position).vars + 1 = p.vars + fields
  | .var, 0, _ => by simp [Pat.splitAt, Pat.varsAll_replicate]; omega
  | .var, _ + 1, h => by simp at h
  | .con c' args, position, h => Pat.varsAll_splitAllAt c fields args position h
theorem Pat.varsAll_splitAllAt (c : DeclName) (fields : Nat) :
    ∀ (ps : List Pat) (position : Nat), position < Pat.varsAll ps →
      Pat.varsAll (Pat.splitAllAt c fields ps position) + 1 = Pat.varsAll ps + fields
  | [], _, h => by simp at h
  | p :: ps, position, h => by
      simp only [Pat.splitAllAt]
      split
      · rename_i hp
        have := Pat.vars_splitAt c fields p position hp
        simp only [Pat.varsAll_cons]
        omega
      · rename_i hp
        simp only [Pat.varsAll_cons] at h ⊢
        have := Pat.varsAll_splitAllAt c fields ps (position - p.vars) (by omega)
        omega
end

section Split

variable {α : Type} (node : DeclName → List α → α) (hole : α)

mutual
/-- Filling a refined pattern with the fields in place of the refined variable
fills the original pattern with the constructor applied to the fields. -/
theorem Pat.fill_splitAt (c : DeclName) :
    ∀ (p : Pat) (before fields after : List α),
      before.length + 1 + after.length = p.vars →
        Pat.fill node hole (p.splitAt c fields.length before.length) (before ++ fields ++ after) =
          Pat.fill node hole p (before ++ node c fields :: after)
  | .var, before, fields, after, h => by
      simp only [Pat.vars_var] at h
      rw [List.eq_nil_of_length_eq_zero (show before.length = 0 by omega),
        List.eq_nil_of_length_eq_zero (show after.length = 0 by omega)]
      simp only [List.length_nil, Pat.splitAt, List.nil_append, List.append_nil, Pat.fill,
        List.headD_cons]
      rw [Pat.fillAll_replicate]
  | .con c' args, before, fields, after, h => by
      simp only [Pat.splitAt, Pat.fill]
      rw [Pat.fillAll_splitAllAt c args before fields after h]
theorem Pat.fillAll_splitAllAt (c : DeclName) :
    ∀ (ps : List Pat) (before fields after : List α),
      before.length + 1 + after.length = Pat.varsAll ps →
        Pat.fillAll node hole (Pat.splitAllAt c fields.length ps before.length)
            (before ++ fields ++ after) =
          Pat.fillAll node hole ps (before ++ node c fields :: after)
  | [], _, _, _, h => by simp at h
  | p :: ps, before, fields, after, h => by
      simp only [Pat.varsAll_cons] at h
      simp only [Pat.splitAllAt]
      split
      · rename_i hp
        have hv := Pat.vars_splitAt c fields.length p before.length hp
        have key := Pat.fill_splitAt c p before fields (after.take (p.vars - 1 - before.length))
          (by simp; omega)
        have split₁ : before ++ fields ++ after =
            (before ++ fields ++ after.take (p.vars - 1 - before.length)) ++
              after.drop (p.vars - 1 - before.length) := by
          simp only [List.append_assoc, List.take_append_drop]
        have split₂ : before ++ node c fields :: after =
            (before ++ node c fields :: after.take (p.vars - 1 - before.length)) ++
              after.drop (p.vars - 1 - before.length) := by
          simp only [List.append_assoc, List.cons_append, List.take_append_drop]
        simp only [Pat.fillAll]
        rw [split₁, split₂, List.take_left' (by simp; omega), List.drop_left' (by simp; omega),
          List.take_left' (by simp; omega), List.drop_left' (by simp; omega), key]
      · rename_i hp
        have hb : p.vars ≤ before.length := by omega
        have key := Pat.fillAll_splitAllAt c ps (before.drop p.vars) fields after
          (by simp; omega)
        have split₁ : before ++ fields ++ after =
            before.take p.vars ++ (before.drop p.vars ++ fields ++ after) := by
          simp only [List.append_assoc]
          conv => rhs; rw [← List.append_assoc, List.take_append_drop]
        have split₂ : before ++ node c fields :: after =
            before.take p.vars ++ (before.drop p.vars ++ node c fields :: after) := by
          simp only [← List.append_assoc, List.take_append_drop]
        simp only [Pat.fillAll]
        rw [split₁, split₂, List.take_left' (by simp; omega), List.drop_left' (by simp; omega),
          List.take_left' (by simp; omega), List.drop_left' (by simp; omega)]
        rw [show before.length - p.vars = (before.drop p.vars).length by simp, key]
end

end Split

/-! ## Patterns filled by terms -/

/-- A pattern with its variables filled by terms. -/
abbrev Pat.term {n : Nat} (p : Pat) (values : List (Tm Head n)) : Tm Head n :=
  Pat.fill (fun c args => appSpine (.const c) args) defaultTm p values

/-- A list of patterns with their variables filled by terms. -/
abbrev Pat.terms {n : Nat} (ps : List Pat) (values : List (Tm Head n)) : List (Tm Head n) :=
  Pat.fillAll (fun c args => appSpine (.const c) args) defaultTm ps values

theorem Pat.terms_subst {n m : Nat} (σ : Sub Head n m) (ps : List Pat)
    (values : List (Tm Head n)) :
    (Pat.terms ps values).map (Presentation.subst σ) =
      Pat.terms ps (values.map (Presentation.subst σ)) :=
  Pat.fillAll_map (fun c xs => subst_appSpine σ (.const c) xs) rfl ps values

theorem Pat.terms_injective {n : Nat} (ps : List Pat) {values values' : List (Tm Head n)}
    (h : values.length = Pat.varsAll ps) (h' : values'.length = Pat.varsAll ps)
    (same : Pat.terms ps values = Pat.terms ps values') : values = values' :=
  Pat.fillAll_injective (fun _ _ _ e => (appSpine_const_injective e).2) ps h h' same

/-- The arguments of a spine of fresh variables are the values filling them. -/
theorem Pat.terms_replicate {n : Nat} (values : List (Tm Head n)) :
    Pat.terms (List.replicate values.length .var) values = values :=
  Pat.fillAll_replicate _ _ values

/-- Filling a split neighbourhood with the fields in place of the split
variable fills the neighbourhood with the constructor applied to the fields. -/
theorem Pat.terms_splitAllAt_fields {n : Nat} (c : DeclName) (N : List Pat)
    (before args after : List (Tm Head n))
    (h : before.length + 1 + after.length = Pat.varsAll N) :
    Pat.terms (Pat.splitAllAt c args.length N before.length) (before ++ args ++ after) =
      Pat.terms N (before ++ appSpine (.const c) args :: after) :=
  Pat.fillAll_splitAllAt _ _ c N before args after h

/-- Filling a neighbourhood with its own variables and then substituting gives the
neighbourhood filled with the substituted variables. -/
theorem Pat.terms_varTerms_subst {n vars : Nat} (N : List Pat) {values : List (Tm Head n)}
    (length : values.length = vars) :
    (Pat.terms N (varTerms vars)).map (Presentation.subst (valueSub vars values)) =
      Pat.terms N values := by
  rw [Pat.terms_subst, varTerms_map_valueSub length]

/-! ## Refinement

A neighbourhood is a list of patterns, one per argument. Splitting one of its
variables replaces it by a constructor applied to fresh variables; a
neighbourhood refines another when it arises from it by splits. Every
instance of a refinement is an instance of the neighbourhood it refines. -/

/-- `N'` is `N` with one pattern variable split. -/
def Pat.Splits (N N' : List Pat) : Prop :=
  ∃ (c : DeclName) (fields position : Nat), position < Pat.varsAll N ∧
    N' = Pat.splitAllAt c fields N position

/-- `N'` refines `N`: it arises from `N` by splitting pattern variables. -/
abbrev Pat.Refines (N N' : List Pat) : Prop := Relation.ReflTransGen Pat.Splits N N'

/-- Values filling a split neighbourhood fill the neighbourhood with the
constructor, applied to the fields, in place of the split variable. -/
theorem Pat.terms_splitAllAt {n : Nat} {N : List Pat} {c : DeclName} {fields position : Nat}
    (inRange : position < Pat.varsAll N) {ws : List (Tm Head n)}
    (hws : ws.length = Pat.varsAll (Pat.splitAllAt c fields N position)) :
    ∃ before args after : List (Tm Head n), before.length = position ∧ args.length = fields ∧
      ws = before ++ args ++ after ∧
        Pat.terms (Pat.splitAllAt c fields N position) ws =
          Pat.terms N (before ++ appSpine (.const c) args :: after) := by
  have hv := Pat.varsAll_splitAllAt c fields N position inRange
  have hp : position ≤ ws.length := by omega
  have hf : fields ≤ (ws.drop position).length := by rw [List.length_drop]; omega
  have split : ws = ws.take position ++ (ws.drop position).take fields ++
      (ws.drop position).drop fields := by
    rw [List.append_assoc, List.take_append_drop, List.take_append_drop]
  refine ⟨ws.take position, (ws.drop position).take fields, (ws.drop position).drop fields,
    List.length_take_of_le hp, List.length_take_of_le hf, split, ?_⟩
  have key := Pat.fillAll_splitAllAt (fun c args => appSpine (.const c) args) defaultTm c N
    (ws.take position) ((ws.drop position).take fields) ((ws.drop position).drop fields) (by
      rw [List.length_take_of_le hp, List.length_drop, List.length_drop]
      omega)
  rw [List.length_take_of_le hp, List.length_take_of_le hf] at key
  exact (congrArg (Pat.terms (Pat.splitAllAt c fields N position)) split).trans key

/-- An instance of a refinement is an instance of the neighbourhood it
refines. -/
theorem Pat.Refines.terms {N N' : List Pat} (refines : Pat.Refines N N') {n : Nat}
    {ws : List (Tm Head n)} (hws : ws.length = Pat.varsAll N') :
    ∃ vs : List (Tm Head n), vs.length = Pat.varsAll N ∧ Pat.terms N' ws = Pat.terms N vs := by
  induction refines generalizing ws with
  | refl => exact ⟨ws, hws, rfl⟩
  | @tail middle _ _ step ih =>
      obtain ⟨c, fields, position, inRange, rfl⟩ := step
      obtain ⟨before, args, after, hb, ha, rfl, same⟩ := Pat.terms_splitAllAt inRange hws
      have hv := Pat.varsAll_splitAllAt c fields middle position inRange
      obtain ⟨vs, hvs, same'⟩ := ih (ws := before ++ appSpine (.const c) args :: after) (by
        simp only [List.length_append, List.length_cons] at hws ⊢
        omega)
      exact ⟨vs, hvs, same.trans same'⟩

/-! ## Leaves

A tree started at a neighbourhood reaches each leaf with a refined
neighbourhood: every split on the way replaces the inspected variable by the
constructor of the branch taken. Only the branch `find` selects for a
constructor is followed. The leaf's equation has the defined constant applied
to the leaf's neighbourhood on its left and the leaf's right side on its
right. A scoped tree evaluates on given values exactly when the neighbourhood
filled with them is an instance of a leaf's neighbourhood, and the result is
the leaf's right side at that instance. -/

/-- The leaves a tree reaches from the neighbourhood `N`, with their
neighbourhoods. -/
inductive CaseTree.LeafOf : CaseTree Head → List Pat → List Pat → (vars : Nat) →
    Tm Head vars → Prop where
  | leaf {vars : Nat} (rhs : Tm Head vars) (N : List Pat) :
      CaseTree.LeafOf (.leaf vars rhs) N N vars rhs
  | split {position : Nat} {family : DeclName} {branches : CaseBranches Head} {c : DeclName}
      {fields : Nat} {tree : CaseTree Head} {N N' : List Pat} {vars : Nat}
      {rhs : Tm Head vars} :
      branches.find c = some (fields, tree) →
      CaseTree.LeafOf tree (Pat.splitAllAt c fields N position) N' vars rhs →
      CaseTree.LeafOf (.split position family branches) N N' vars rhs

/-- A leaf of a scoped tree refines the starting neighbourhood and is over
exactly its variables. -/
theorem CaseTree.LeafOf.refines {tree : CaseTree Head} {N N' : List Pat} {vars : Nat}
    {rhs : Tm Head vars} (leaf : tree.LeafOf N N' vars rhs) :
    ∀ {k : Nat}, tree.Scoped k → Pat.varsAll N = k →
      Pat.Refines N N' ∧ Pat.varsAll N' = vars := by
  induction leaf with
  | leaf rhs N =>
      intro k inScope hk
      cases inScope
      exact ⟨.refl, hk⟩
  | @split position family branches c fields tree N N' vars rhs found _ ih =>
      intro k inScope hk
      cases inScope with
      | split inRange scopedBranches =>
          have hv := Pat.varsAll_splitAllAt c fields N position (hk ▸ inRange)
          obtain ⟨refines, same⟩ := ih (scopedBranches.find found) (by omega)
          exact ⟨.head ⟨c, fields, position, hk ▸ inRange, rfl⟩ refines, same⟩

/-- A leaf's neighbourhood has one pattern per argument. -/
theorem CaseTree.LeafOf.length {tree : CaseTree Head} {N N' : List Pat} {vars : Nat}
    {rhs : Tm Head vars} (leaf : tree.LeafOf N N' vars rhs) : N'.length = N.length := by
  induction leaf with
  | leaf => rfl
  | split _ _ ih => rw [ih, Pat.splitAllAt_length]

/-- An evaluation of a scoped tree fires one of its leaves, at an instance of
the leaf's neighbourhood. -/
theorem CaseTree.Eval.leaf_instance {tree : CaseTree Head} {n : Nat} {vs : List (Tm Head n)}
    {u : Tm Head n} (eval : tree.Eval vs u) :
    ∀ {N : List Pat} {k : Nat}, tree.Scoped k → Pat.varsAll N = k → vs.length = k →
      ∃ (N' : List Pat) (vars : Nat) (rhs : Tm Head vars) (σ : Sub Head vars n),
        tree.LeafOf N N' vars rhs ∧
          Pat.terms N' ((varTerms vars).map (Presentation.subst σ)) = Pat.terms N vs ∧
            u = Presentation.subst σ rhs := by
  induction eval with
  | @leaf vars rhs values length =>
      intro N k inScope hk _
      cases inScope
      refine ⟨N, vars, rhs, valueSub vars values, .leaf rhs N, ?_, rfl⟩
      rw [varTerms_map_valueSub length]
  | @split position family branches before after args c tree u lengthBefore found _ ih =>
      intro N k inScope hk hvs
      cases inScope with
      | split inRange scopedBranches =>
          simp only [List.length_append, List.length_cons] at hvs
          have hv := Pat.varsAll_splitAllAt c args.length N position (hk ▸ inRange)
          obtain ⟨N', vars, rhs, σ, leaf, same, rfl⟩ :=
            ih (N := Pat.splitAllAt c args.length N position) (scopedBranches.find found)
              (by omega) (by simp only [List.length_append]; omega)
          refine ⟨N', vars, rhs, σ, .split found leaf, ?_, rfl⟩
          rw [same, ← lengthBefore]
          exact Pat.fillAll_splitAllAt _ _ c N before args after (by omega)

/-- A scoped tree fires a leaf at every instance of its neighbourhood. -/
theorem CaseTree.LeafOf.eval {tree : CaseTree Head} {N N' : List Pat} {vars : Nat}
    {rhs : Tm Head vars} (leaf : tree.LeafOf N N' vars rhs) :
    ∀ {k : Nat}, tree.Scoped k → Pat.varsAll N = k →
      ∀ {n : Nat} {vs : List (Tm Head n)} (σ : Sub Head vars n), vs.length = k →
        Pat.terms N' ((varTerms vars).map (Presentation.subst σ)) = Pat.terms N vs →
          tree.Eval vs (Presentation.subst σ rhs) := by
  induction leaf with
  | leaf rhs N =>
      intro k inScope hk n vs σ hvs same
      cases inScope
      have values := Pat.terms_injective N (by rw [List.length_map, varTerms_length, hk])
        (hvs.trans hk.symm) same
      subst values
      have e : Presentation.subst (valueSub _ ((varTerms _).map (Presentation.subst σ))) rhs =
          Presentation.subst σ rhs :=
        subst_ext (valueSub_map_varTerms σ) rhs
      rw [← e]
      exact .leaf rhs (by rw [List.length_map, varTerms_length])
  | @split position family branches c fields tree N N' vars rhs found leaf ih =>
      intro k inScope hk n vs σ hvs same
      cases inScope with
      | split inRange scopedBranches =>
          have scopedTree := scopedBranches.find found
          have hv := Pat.varsAll_splitAllAt c fields N position (hk ▸ inRange)
          obtain ⟨refines, leafVars⟩ := leaf.refines scopedTree (by omega)
          obtain ⟨ws, hws, general⟩ := refines.terms (ws := (varTerms vars).map
            (Presentation.subst σ)) (by rw [List.length_map, varTerms_length, leafVars])
          obtain ⟨before, args, after, hb, rfl, rfl, split⟩ :=
            Pat.terms_splitAllAt (hk ▸ inRange) hws
          have values := Pat.terms_injective N (by
              simp only [List.length_append, List.length_cons] at hws ⊢
              omega) (hvs.trans hk.symm)
            (split.symm.trans (general.symm.trans same))
          subst values
          rw [← hb]
          exact .split rfl found (ih scopedTree (by omega) σ (by
            simp only [List.length_append] at hws ⊢
            omega) general)

/-- A scoped tree evaluates on the values of its neighbourhood's variables
exactly at the instances of its leaves' neighbourhoods, to the leaves' right
sides. -/
theorem CaseTree.eval_iff_leaf {tree : CaseTree Head} {N : List Pat}
    (inScope : tree.Scoped (Pat.varsAll N)) {n : Nat} {vs : List (Tm Head n)}
    (hvs : vs.length = Pat.varsAll N) {u : Tm Head n} :
    tree.Eval vs u ↔ ∃ (N' : List Pat) (vars : Nat) (rhs : Tm Head vars) (σ : Sub Head vars n),
      tree.LeafOf N N' vars rhs ∧
        Pat.terms N' ((varTerms vars).map (Presentation.subst σ)) = Pat.terms N vs ∧
          u = Presentation.subst σ rhs := by
  constructor
  · intro eval
    exact eval.leaf_instance inScope rfl hvs
  · rintro ⟨N', vars, rhs, σ, leaf, same, rfl⟩
    exact leaf.eval inScope rfl σ hvs same

/-! ## Axiom audit -/

#print axioms varTerms_map_valueSub
#print axioms valueSub_map_varTerms
#print axioms CaseTree.absurd_not_eval
#print axioms CaseTree.Eval.deterministic
#print axioms CaseTree.Eval.rename
#print axioms CaseTree.Eval.subst
#print axioms CaseTree.step_deterministic
#print axioms CaseTree.step_rename
#print axioms CaseTree.step_subst
#print axioms caseTreeComputation_deterministic
#print axioms CaseBranches.Cover.find
#print axioms CaseTree.covers_absurd
#print axioms CaseBranches.inspect_find
#print axioms CaseTree.Eval.settled
#print axioms CaseTree.Eval.not_stuck
#print axioms CaseTree.step_settled
#print axioms CaseTree.not_step_of_stuck
#print axioms Pat.fillAll_append
#print axioms Pat.fill_map
#print axioms Pat.fill_injective
#print axioms Pat.vars_splitAt
#print axioms Pat.fill_splitAt
#print axioms Pat.terms_subst
#print axioms Pat.terms_injective
#print axioms varTerms_length
#print axioms varTerms_var
#print axioms valueSub_map
#print axioms getD_append_left
#print axioms CaseBranches.Cover.names
#print axioms CaseBranches.Cover.constructor
#print axioms CaseBranches.Scoped.find
#print axioms Pat.varsAll_nil
#print axioms Pat.varsAll_cons
#print axioms Pat.vars_var
#print axioms Pat.vars_con
#print axioms Pat.varsAll_replicate
#print axioms Pat.fillAll_length
#print axioms Pat.fillAll_replicate
#print axioms Pat.fill_var_injective
#print axioms Pat.fillAll_map
#print axioms Pat.fillAll_injective
#print axioms Pat.splitAllAt_length
#print axioms Pat.varsAll_splitAllAt
#print axioms Pat.fillAll_splitAllAt
#print axioms Pat.terms_replicate
#print axioms Pat.terms_splitAllAt_fields
#print axioms Pat.terms_varTerms_subst
#print axioms Pat.terms_splitAllAt
#print axioms Pat.Refines.terms
#print axioms CaseTree.LeafOf.refines
#print axioms CaseTree.LeafOf.length
#print axioms CaseTree.Eval.leaf_instance
#print axioms CaseTree.LeafOf.eval
#print axioms CaseTree.eval_iff_leaf

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
