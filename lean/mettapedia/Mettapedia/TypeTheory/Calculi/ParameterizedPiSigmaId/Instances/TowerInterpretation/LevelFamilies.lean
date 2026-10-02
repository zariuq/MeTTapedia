import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerInterpretation.LevelNames
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.ConstantInstantiation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.LogicalRelationFundamental
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Domain.ChurchDefinitions

/-!
# Families over the level names

A *family* is a function on the names of the levels below a closed bound, given by its values:
a declared name `G`, a bound `c`, a type `T` over a variable name, the level expressions at
which the family computes, and its value at each of them (`Family`). The package of the tower
with level names and a list of families (`rules`, `church`), under bounds on the level
parameters, declares for each family

* the constant `G : Π (x : names c). T`, and
* the root step `G (name e) ⟶ value e` at every level expression `e` at which the family
  computes, with the premise that `name e` is a name below `c`.

Abstraction over a level is the declaration of `G`, application to a level is application to
its name, and the computation rule is the root step. There is no new term former and no new
rule of the judgment; the premise of the step is a premise of the judgment's rule for root
steps.

**Admission** (`Admitted`). A list of families is admitted when each family, over the families
before it, has a fresh name, a type over a variable name, and a typed value wherever it
computes: under every positive bounds, at every level expression `e` at which it computes and
which lies below its bound, the value at `e` has the family's type at the name of `e`. The two
sources of admitted families, values at every closed level and one check under a bounded level
parameter, are in `ParametricFamilies`.

In an admitted list a family is typed at its declared type (`family_typed`), its application to
a name below its bound is typed (`family_app_typed`), and it computes there to its value
(`family_at`). Two families of an admitted list with one name are one family
(`Admitted.eq_of_name_eq`).

**Level substitution.** For families whose types have no level parameter and whose values
commute with level substitution (`Family.Stable`), an admissible level substitution is a
morphism of the packages (`substLevels_morphism`), so derivations are stable under admissible
level substitutions (`substLevels`). Derivations hold under every stronger bounds
(`underBounds`), and the tower with level names and no family is contained in every package
(`lift_bare`).

Negative example: a family computes at names only. At a variable name no root step applies
(`CStep.not_at_var`), so a type written with a family at a λ-bound name is neutral.

Scope: the annotated judgment. Families have one level argument. Two families with equal
values at every level are not thereby equal terms.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
namespace LevelNames

open Presentation Presentation.TypedEquality Presentation.TypedEquality.Annotated
open Presentation.TypedEquality.Impredicative.Domain (termConsts)
open Mettapedia.TypeTheory.UniverseLevel
open LevelBounds (LeUnder EqUnder Admissible unbounded valid_unbounded)

variable {L : Type}

/-! ## Families and their package -/

/-- **A family over the names of the levels below a closed bound**: a declared name, the bound,
a type over a variable name, the level expressions at which it computes, and its value at a
level expression. -/
structure Family (L : Type) where
  /-- The declared name of the family. -/
  name : DeclName
  /-- The family is a function on the names of the levels below this level. -/
  bound : L
  /-- The type of the family at a variable name. -/
  type : CTm (Head L) 1
  /-- The level expressions at which the family computes. -/
  fires : LevelExpr L → Prop
  /-- The value of the family at a level expression. -/
  body : LevelExpr L → CTm (Head L) 0

/-- **The declared types** of a list of families, the latest first: each family is a function
on the names of the levels below its bound. -/
def declared : List (Family L) → DeclName → Option (CTm (Head L) 0)
  | [], _ => none
  | F :: Fs, n =>
      if n = F.name then some (.pi (levelsBelow (.const F.bound)) F.type) else declared Fs n

/-- The root steps: a family at the name of a level expression at which it computes is its
value there. -/
inductive Step (Fs : List (Family L)) : {n : Nat} → Tm (Head L) n → Tm (Head L) n → Prop
  | family {n : Nat} {F : Family L} {e : LevelExpr L} (mem : F ∈ Fs) (fires : F.fires e) :
      Step Fs (.app (.const F.name) (.head (.name e)) : Tm (Head L) n)
        (Presentation.liftClosed (F.body e).erase)

/-- At a variable no root step of the erased package applies. -/
theorem Step.not_at_var {Fs : List (Family L)} {n : Nat} {f target : Tm (Head L) n}
    {i : Fin n} : ¬ Step Fs (.app f (.var i)) target := by
  intro step
  cases step

/-- The root computation of the package. -/
def computation (Fs : List (Family L)) : RootComputation (Head L) where
  step := Step Fs
  rename := by
    intro n m ρ left right step
    cases step with
    | @family F e mem fires =>
      show Step Fs (.app (.const F.name) (.head (.name e)))
        (Presentation.rename ρ (Presentation.liftClosed (F.body e).erase))
      rw [rename_liftClosed]
      exact .family mem fires
  substitute := by
    intro n m σ left right step
    cases step with
    | @family F e mem fires =>
      show Step Fs (.app (.const F.name) (.head (.name e)))
        (Presentation.subst σ (Presentation.liftClosed (F.body e).erase))
      rw [subst_liftClosed]
      exact .family mem fires

/-- The annotated root steps of the package. -/
inductive CStep (Fs : List (Family L)) : {n : Nat} → CTm (Head L) n → CTm (Head L) n → Prop
  | family {n : Nat} {F : Family L} {e : LevelExpr L} (mem : F ∈ Fs) (fires : F.fires e) :
      CStep Fs (.app (.const F.name) (levelName e) : CTm (Head L) n) (F.body e).liftClosed

/-- **A family computes at names only**: at a variable no root step applies. -/
theorem CStep.not_at_var {Fs : List (Family L)} {n : Nat} {f target : CTm (Head L) n}
    {i : Fin n} : ¬ CStep Fs (.app f (.var i)) target := by
  intro step
  cases step

/-- **The premise of a step**: the name the family is applied to is a name below the bound of
the family. -/
inductive CRequires (Fs : List (Family L)) :
    {n : Nat} → CTm (Head L) n → CTm (Head L) n → List (CPremise (Head L) n) → Prop
  | family {n : Nat} {F : Family L} {name : DeclName} {e : LevelExpr L}
      {right : CTm (Head L) n} (mem : F ∈ Fs) (same : F.name = name) :
      CRequires Fs (.app (.const name) (levelName e)) right
        [.typing (levelName e) (levelsBelow (.const F.bound))]

/-- The annotated root computation of the package, with the premises of its steps. -/
def ccomputation (Fs : List (Family L)) : CRootComputation (Head L) where
  step := CStep Fs
  rename := by
    intro n m ρ left right step
    cases step with
    | @family F e mem fires =>
      show CStep Fs (.app (.const F.name) (levelName e)) ((F.body e).liftClosed.rename ρ)
      rw [CTm.rename_liftClosed]
      exact .family mem fires
  substitute := by
    intro n m σ left right step
    cases step with
    | @family F e mem fires =>
      show CStep Fs (.app (.const F.name) (levelName e)) ((F.body e).liftClosed.subst σ)
      rw [CTm.subst_liftClosed]
      exact .family mem fires
  requires := CRequires Fs
  requires_rename := by
    intro n m ρ left right premises required
    cases required with
    | family mem same => exact .family mem same
  requires_substitute := by
    intro n m σ left right premises required
    cases required with
    | family mem same => exact .family mem same

variable [LevelOrder L]

/-- **The package of the tower with level names and a list of families**, under bounds on the
level parameters. -/
def rules (Δ : LevelBounds L) (Fs : List (Family L)) : Rules (Head L) :=
  { baseRules Δ with
    constantType := fun n => (declared Fs n).map CTm.erase
    computation := computation Fs }

/-- **The annotation of the package.** -/
def church (Δ : LevelBounds L) (Fs : List (Family L)) : ChurchRules (rules Δ Fs) where
  constantType := declared Fs
  computation := ccomputation Fs
  erase_constantType := fun _ => rfl
  erase_step := fun step => by
    cases step with
    | @family F e mem fires =>
      show Step Fs (.app (.const F.name) (.head (.name e))) ((F.body e).liftClosed).erase
      rw [CTm.erase_liftClosed]
      exact .family mem fires

/-! ## Inclusions of packages -/

section Inclusions

variable {Δ Δ' : LevelBounds L}

/-- The tower with level names and no family is contained in every package. -/
theorem bare_sub (Δ : LevelBounds L) (Fs : List (Family L)) :
    ChurchRulesSub (bare Δ) (church Δ Fs) where
  headTyping := id
  isUniverse := id
  join := id
  cumulative := id
  headEq := id
  constantType := fun {_ D} (found : (none : Option (CTm (Head L) 0)) = some D) => nomatch found
  computation := fun step => step.elim
  requires := fun step _ => step.elim

/-- **Derivations of the tower with level names hold in every package.** -/
theorem lift_bare {Fs : List (Family L)} {s : CStatement (Head L)}
    (derivation : CDerivable (bare Δ) s) : CDerivable (church Δ Fs) s :=
  CDerivable.mono (bare_sub Δ Fs) derivation

omit [LevelOrder L] in
/-- A name declared with the earlier families keeps its type when a family with a fresh name
is added. -/
theorem declared_cons {F : Family L} {Fs : List (Family L)} (fresh : declared Fs F.name = none)
    {n : DeclName} {T : CTm (Head L) 0} (found : declared Fs n = some T) :
    declared (F :: Fs) n = some T := by
  change (if n = F.name then some (.pi (levelsBelow (.const F.bound)) F.type)
    else declared Fs n) = some T
  rw [if_neg, found]
  rintro rfl
  rw [fresh] at found
  cases found

/-- **A family with a fresh name extends the package of the earlier families.** -/
theorem cons_sub (Δ : LevelBounds L) {F : Family L} {Fs : List (Family L)}
    (fresh : declared Fs F.name = none) :
    ChurchRulesSub (church Δ Fs) (church Δ (F :: Fs)) where
  headTyping := id
  isUniverse := id
  join := id
  cumulative := id
  headEq := id
  constantType := fun found => declared_cons fresh found
  computation := by
    intro n l r step
    cases step with
    | family mem fires => exact .family (List.mem_cons_of_mem _ mem) fires
  requires := by
    intro n l r premises _ required
    cases required with
    | family mem same =>
      exact ⟨_, .family (List.mem_cons_of_mem _ mem) same, fun _ member => member⟩

/-- A package is contained in the package with stronger bounds. -/
theorem bounds_sub (stronger : ∀ ν : Nat → L, Δ'.Valid ν → Δ.Valid ν) (Fs : List (Family L)) :
    ChurchRulesSub (church Δ Fs) (church Δ' Fs) where
  headTyping := HeadTyping.mono stronger
  isUniverse := id
  join := id
  cumulative := Cumulative.mono stronger
  headEq := HeadEq.mono stronger
  constantType := id
  computation := id
  requires := fun _ required => ⟨_, required, fun _ member => member⟩

/-- **Derivations without bounds hold under every bounds.** -/
theorem underBounds (Δ : LevelBounds L) {Fs : List (Family L)} {s : CStatement (Head L)}
    (derivation : CDerivable (church (unbounded L) Fs) s) : CDerivable (church Δ Fs) s :=
  CDerivable.mono (bounds_sub (fun ν _ => valid_unbounded ν) Fs) derivation

end Inclusions

/-! ## Level substitution -/

/-- **A family commutes with level substitution**: its type has no level parameter, it computes
at every closed level and wherever a level expression at which it computes is sent, and its
value at a substituted expression is the substituted value; its value at a level expression
and at the value of that expression agree up to the values of the levels in them. -/
structure Family.Stable (F : Family L) : Prop where
  type_closed : ∀ σ : Nat → LevelExpr L, F.type.mapHead (substLevelsHead σ) = F.type
  fires_const : ∀ d : L, F.fires (.const d)
  fires_subst : ∀ {e : LevelExpr L} (σ : Nat → LevelExpr L), F.fires e → F.fires (e.subst σ)
  body_subst : ∀ {e : LevelExpr L} (σ : Nat → LevelExpr L), F.fires e →
    (F.body e).mapHead (substLevelsHead σ) = F.body (e.subst σ)
  body_eval : ∀ {e : LevelExpr L} (ν : Nat → L), F.fires e →
    (F.body e).mapHead (evalHead ν) = (F.body (.const (e.eval ν))).mapHead (evalHead ν)

section Substitution

variable {Δ Δ' : LevelBounds L} {σ : Nat → LevelExpr L}

/-- Level substitution keeps the declared types of families that commute with it. -/
theorem declared_closed (σ : Nat → LevelExpr L) :
    ∀ {Fs : List (Family L)}, (∀ F ∈ Fs, F.Stable) →
      ∀ {n : DeclName} {T : CTm (Head L) 0}, declared Fs n = some T →
        T.mapHead (substLevelsHead σ) = T
  | [], _, _, T, found => by
    have impossible : (none : Option (CTm (Head L) 0)) = some T := found
    cases impossible
  | F :: Fs, stable, n, T, found => by
    change (if n = F.name then some (.pi (levelsBelow (.const F.bound)) F.type)
      else declared Fs n) = some T at found
    by_cases isFamily : n = F.name
    · rw [if_pos isFamily] at found
      cases found
      show CTm.pi (levelsBelow (.const F.bound)) (F.type.mapHead (substLevelsHead σ)) = _
      rw [(stable F (.head _)).type_closed σ]
    · rw [if_neg isFamily] at found
      exact declared_closed σ (fun F' mem => stable F' (List.mem_cons_of_mem _ mem)) found

/-- **An admissible level substitution is a morphism of the packages** of families that commute
with level substitution. -/
theorem substLevels_morphism {Fs : List (Family L)} (stable : ∀ F ∈ Fs, F.Stable)
    (admissible : Admissible Δ' Δ σ) :
    (church Δ Fs).Morphism (church Δ' Fs) (substLevelsHead σ) where
  headTyping := HeadTyping.substLevels admissible
  isUniverse := IsUniverse.substLevels
  join := Join.substLevels
  cumulative := Cumulative.substLevels admissible
  headEq := HeadEq.substLevels admissible
  constantType := by
    intro c T found
    change declared Fs c = some (T.mapHead (substLevelsHead σ))
    rw [declared_closed σ stable found]
    exact found
  computation := by
    intro n l r step
    cases step with
    | @family F e mem fires =>
      show CStep Fs (.app (.const F.name) (levelName (e.subst σ)))
        ((F.body e).liftClosed.mapHead (substLevelsHead σ))
      rw [CTm.mapHead_liftClosed, (stable F mem).body_subst σ fires]
      exact .family mem ((stable F mem).fires_subst σ fires)
  requires := by
    intro n l r premises _ required
    cases required with
    | family mem same =>
      exact ⟨_, .family mem same,
        fun premise member => ⟨_, List.mem_singleton.mpr rfl, List.mem_singleton.mp member⟩⟩

/-- **Derivations are stable under admissible level substitutions.** -/
theorem substLevels {Fs : List (Family L)} (stable : ∀ F ∈ Fs, F.Stable)
    (admissible : Admissible Δ' Δ σ) {s : CStatement (Head L)}
    (derivation : CDerivable (church Δ Fs) s) :
    CDerivable (church Δ' Fs) (s.mapHead (substLevelsHead σ)) :=
  derivation.mapHead (substLevels_morphism stable admissible)

end Substitution

/-! ## Admitted families -/

/-- **A list of families is admitted** when each family, over the families before it, has a
fresh name that neither its own values nor the earlier values at the closed levels below their
bounds mention, commutes with level substitution, has a type over a variable name, and has a
typed value wherever it computes: under every positive bounds, at every level expression at
which it computes and which lies below its bound, the value has the family's type at the name
of that expression. -/
inductive Admitted : List (Family L) → Prop
  | nil : Admitted []
  | cons {F : Family L} {Fs : List (Family L)} (level : LevelExpr L) :
      Admitted Fs →
      declared Fs F.name = none →
      (∀ F' ∈ Fs, ∀ d, d < F'.bound → F.name ∉ termConsts (F'.body (.const d))) →
      (∀ d, d < F.bound → F.name ∉ termConsts (F.body (.const d))) →
      F.Stable →
      CDerivable (church (unbounded L) Fs)
        (.typing (.snoc .nil (levelsBelow (.const F.bound))) F.type (universeAt level)) →
      (∀ Δ : LevelBounds L, Δ.Positive → ∀ e : LevelExpr L, F.fires e →
        LeUnder Δ (.succ e) (.const F.bound) →
        CDerivable (church Δ Fs)
          (.typing .nil (F.body e) (CTm.inst0 (levelName e) F.type))) →
      Admitted (F :: Fs)

/-- The earlier families of an admitted list are admitted. -/
theorem Admitted.tail {F : Family L} {Fs : List (Family L)} (admitted : Admitted (F :: Fs)) :
    Admitted Fs := by
  cases admitted with
  | cons _ earlier => exact earlier

/-- The name of the latest family of an admitted list is fresh for the earlier ones. -/
theorem Admitted.fresh {F : Family L} {Fs : List (Family L)} (admitted : Admitted (F :: Fs)) :
    declared Fs F.name = none := by
  cases admitted with
  | cons _ _ fresh => exact fresh

/-- Every family of an admitted list commutes with level substitution. -/
theorem Admitted.stable {Fs : List (Family L)} (admitted : Admitted Fs) :
    ∀ F ∈ Fs, F.Stable := by
  induction admitted with
  | nil => exact fun _ mem => nomatch mem
  | cons _ _ _ _ _ stable _ _ ih =>
    intro F' mem
    rcases List.mem_cons.mp mem with rfl | earlier
    · exact stable
    · exact ih F' earlier

omit [LevelOrder L] in
/-- The name of a family of a list is declared in the package with the list. -/
theorem declared_ne_none_of_mem :
    ∀ {Fs : List (Family L)} {F : Family L}, F ∈ Fs → declared Fs F.name ≠ none
  | F' :: Fs, F, mem => by
    change (if F.name = F'.name then some (.pi (levelsBelow (.const F'.bound)) F'.type)
      else declared Fs F.name) ≠ none
    by_cases same : F.name = F'.name
    · rw [if_pos same]
      exact fun impossible => nomatch impossible
    · rw [if_neg same]
      rcases List.mem_cons.mp mem with rfl | earlier
      · exact absurd rfl same
      · exact declared_ne_none_of_mem earlier

omit [LevelOrder L] in
/-- A name different from the names of the families of a list is not declared with it. -/
theorem declared_eq_none :
    ∀ {Fs : List (Family L)} {n : DeclName}, (∀ F ∈ Fs, n ≠ F.name) → declared Fs n = none
  | [], _, _ => rfl
  | F :: Fs, n, others => by
    change (if n = F.name then some (.pi (levelsBelow (.const F.bound)) F.type)
      else declared Fs n) = none
    rw [if_neg (others F (.head _))]
    exact declared_eq_none fun F' mem => others F' (List.mem_cons_of_mem _ mem)

/-- **Two families of an admitted list with one name are one family.** -/
theorem Admitted.eq_of_name_eq {Fs : List (Family L)} (admitted : Admitted Fs) :
    ∀ {F F' : Family L}, F ∈ Fs → F' ∈ Fs → F.name = F'.name → F = F' := by
  induction admitted with
  | nil => exact fun mem => nomatch mem
  | @cons G Gs _ _ fresh _ _ _ _ _ ih =>
    intro F F' mem mem' same
    rcases List.mem_cons.mp mem with rfl | earlier
    · rcases List.mem_cons.mp mem' with rfl | earlier'
      · rfl
      · exact absurd (same ▸ fresh) (declared_ne_none_of_mem earlier')
    · rcases List.mem_cons.mp mem' with rfl | earlier'
      · exact absurd (same ▸ fresh) (declared_ne_none_of_mem earlier)
      · exact ih earlier earlier' same

section Lifting

variable {Δ : LevelBounds L}

/-- Derivations of the package of the earlier families hold with the latest family added. -/
theorem lift_cons {F : Family L} {Fs : List (Family L)} (admitted : Admitted (F :: Fs))
    {s : CStatement (Head L)} (derivation : CDerivable (church Δ Fs) s) :
    CDerivable (church Δ (F :: Fs)) s :=
  CDerivable.mono (cons_sub Δ admitted.fresh) derivation

/-- **Derivations of a package hold in every admitted extension of it by later families.** -/
theorem lift_append {Fs : List (Family L)} :
    ∀ {Gs : List (Family L)}, Admitted (Gs ++ Fs) →
      ∀ {s : CStatement (Head L)}, CDerivable (church Δ Fs) s →
        CDerivable (church Δ (Gs ++ Fs)) s
  | [], _, _, derivation => derivation
  | _ :: _, admitted, _, derivation => lift_cons admitted (lift_append admitted.tail derivation)

end Lifting

/-! ## Typings of a family -/

section Typings

variable {Δ : LevelBounds L} {F : Family L} {Fs : List (Family L)}

/-- The declared type of the latest family is a type. -/
theorem familyType_typed (admitted : Admitted (F :: Fs)) :
    ∃ level : LevelExpr L, CDerivable (church Δ (F :: Fs))
      (.typing .nil (.pi (levelsBelow (.const F.bound)) F.type)
        (universeAt (.max (.const F.bound) level))) := by
  cases admitted with
  | cons level earlier fresh unused selfFree stable formed instances =>
    have whole : Admitted (F :: Fs) :=
      .cons level earlier fresh unused selfFree stable formed instances
    exact ⟨level, .piForm (lift_bare (levelsBelow_typed _)) (.tower (.sort _))
      (lift_cons whole (underBounds Δ formed)) (.tower (.sort _)) (.tower (.sorts _ _))⟩

/-- The latest family is typed at its declared type in every context. -/
theorem family_const_typed (admitted : Admitted (F :: Fs)) {n : Nat} {Γ : CCtx (Head L) n} :
    CDerivable (church Δ (F :: Fs))
      (.typing Γ (.const F.name)
        (CTm.liftClosed (.pi (levelsBelow (.const F.bound)) F.type))) := by
  obtain ⟨level, formed⟩ := familyType_typed (Δ := Δ) admitted
  have known : (church Δ (F :: Fs)).constantType F.name =
      some (.pi (levelsBelow (.const F.bound)) F.type) := if_pos rfl
  exact .const known formed (.tower (.sort _))

/-- **A family is a function on the names of the levels below its bound.** -/
theorem family_typed (admitted : Admitted (F :: Fs)) :
    CDerivable (church Δ (F :: Fs))
      (.typing .nil (.const F.name) (.pi (levelsBelow (.const F.bound)) F.type)) := by
  have typed := family_const_typed (Δ := Δ) admitted (Γ := .nil)
  rwa [CTm.liftClosed_zero] at typed

/-- **A family at the name of a level below its bound is typed** at its type at that name. -/
theorem family_app_typed (admitted : Admitted (F :: Fs)) {e : LevelExpr L}
    (below : LeUnder Δ (.succ e) (.const F.bound)) :
    CDerivable (church Δ (F :: Fs))
      (.typing .nil (.app (.const F.name) (levelName e)) (CTm.inst0 (levelName e) F.type)) :=
  .appElim (family_typed admitted) (lift_bare (levelName_typed below))

/-- The value of the latest family, where it computes, is typed in the extended package. -/
theorem family_body_typed (admitted : Admitted (F :: Fs)) (positive : Δ.Positive)
    {e : LevelExpr L} (fires : F.fires e) (below : LeUnder Δ (.succ e) (.const F.bound)) :
    CDerivable (church Δ (F :: Fs))
      (.typing .nil (F.body e) (CTm.inst0 (levelName e) F.type)) := by
  cases admitted with
  | cons level earlier fresh unused selfFree stable formed instances =>
    exact CDerivable.mono (cons_sub Δ fresh) (instances Δ positive e fires below)

/-- **A family at the name of a level is its value at that level**, wherever it computes. -/
theorem family_at (admitted : Admitted (F :: Fs)) (positive : Δ.Positive) {e : LevelExpr L}
    (fires : F.fires e) (below : LeUnder Δ (.succ e) (.const F.bound)) :
    CDerivable (church Δ (F :: Fs))
      (.equality .nil (.app (.const F.name) (levelName e)) (F.body e)
        (CTm.inst0 (levelName e) F.type)) := by
  have step : CStep (F :: Fs)
      (.app (.const F.name) (levelName e) : CTm (Head L) 0) (F.body e) := by
    have lifted := CStep.family (n := 0) (F := F) (Fs := F :: Fs) (e := e) (.head _) fires
    rwa [CTm.liftClosed_zero] at lifted
  refine .root (premises := [.typing (levelName e) (levelsBelow (.const F.bound))]) step
    (.family (.head _) rfl) (fun premise member => ?_)
    (family_app_typed admitted below) (family_body_typed admitted positive fires below)
  obtain rfl := List.mem_singleton.mp member
  exact lift_bare (levelName_typed below)

/-- **A family at the name of a level is its value there, in every context.** -/
theorem family_at_in (admitted : Admitted (F :: Fs)) (positive : Δ.Positive) {e : LevelExpr L}
    (fires : F.fires e) (below : LeUnder Δ (.succ e) (.const F.bound)) {n : Nat}
    (Γ : CCtx (Head L) n) :
    CDerivable (church Δ (F :: Fs))
      (.equality Γ (.app (.const F.name) (levelName e)) (F.body e).liftClosed
        (CTm.inst0 (levelName e) F.type).liftClosed) :=
  CEqual.rename (ρ := fun i => i.elim0) (family_at admitted positive fires below)
    (fun i => i.elim0)

end Typings

end LevelNames
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
