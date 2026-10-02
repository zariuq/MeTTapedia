import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerInterpretation.LevelFamilies

/-!
# The two sources of families: values at every closed level, and one check

A family over the level names is admitted when its values are typed wherever it computes
(`LevelFamilies`). This file gives the two ways such a family arises.

* **Values at every closed level** (`Family.pointwise`, `admitted_pointwise`). The family is
  given by a closed term for every closed level and computes at the names of closed levels
  only. It is admitted when, for every closed level below the bound, its value has the family's
  type at the name of that level: the rule with one premise for every closed level.
* **One check** (`Family.uniform`, `admitted_uniform`). The family is given by one term with
  the level parameter `0`; its value at a level expression is the term with that expression for
  the parameter, and it computes at the name of every level expression. It is admitted by one
  derivation: under the parameter bounded by the family's bound, the term has the family's type
  at the name of the parameter. Under the parameter the universes are the tower's own, with
  their cumulativity and type formers.

The second is an instance of the first notion of admission, by level substitution: the one
derivation gives the typing of the value at every level expression below the bound, under every
bounds (`admitted_uniform`).

Positive examples, for a limit bound `c`:

* the successor on names, `suc (name e) = name (e + 1)` (`successor_admitted`,
  `successor_at`);
* the next universes, `next (name e) = U_{e+1}`, and the universes at their precise type,
  `universes x : next x` with `universes (name e) = U_e` (`universes_admitted`,
  `universes_at`);
* a family that uses an earlier one at the successor of its parameter, checked once
  (`secondNext_admitted`), and equal to `U_{e+2}` at the name of `e` (`secondNext_at`);
* a family from one check computes under a level parameter: under `l < c`,
  `universes (name l) = U_l` (`universes_at_param`);
* over the notations below `ε₀`: the universes at all the finite levels, and their member at
  the name of `2` (`finiteUniverses_admitted`, `finiteUniverses_at_two`).

Negative examples: a family given by its values at the closed levels does not compute at the
name of a level parameter (`pointwise_not_at_param`); a term with two level parameters is not
determined by the image of the parameter `0` (`not_onlyParamZero`).

Scope: the annotated judgment; one level argument.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
namespace LevelNames

open Presentation Presentation.TypedEquality Presentation.TypedEquality.Annotated
open Presentation.TypedEquality.Impredicative.Domain (termConsts)
open Mettapedia.TypeTheory.UniverseLevel
open LevelBounds (LeUnder EqUnder Admissible unbounded valid_unbounded positive_unbounded)
open LevelTower (oneBound oneBound_zero oneBound_other)

variable {L : Type}

/-! ## Terms and level parameters -/

/-- A term that every level substitution keeps: its heads have no level parameter. -/
def LevelClosed {n : Nat} (t : CTm (Head L) n) : Prop :=
  ∀ σ : Nat → LevelExpr L, t.mapHead (substLevelsHead σ) = t

/-- A term whose level instances are determined by the image of the parameter `0`: it has no
other level parameter. -/
def OnlyParamZero {n : Nat} (t : CTm (Head L) n) : Prop :=
  ∀ σ τ : Nat → LevelExpr L, σ 0 = τ 0 →
    t.mapHead (substLevelsHead σ) = t.mapHead (substLevelsHead τ)

/-- A term without level parameter is determined by the image of the parameter `0`. -/
theorem LevelClosed.onlyParamZero {n : Nat} {t : CTm (Head L) n} (closed : LevelClosed t) :
    OnlyParamZero t :=
  fun σ τ _ => (closed σ).trans (closed τ).symm

/-- Changing heads changes no constant of a term. -/
theorem termConsts_mapHead {H H' : Type} (g : H → H') :
    ∀ {n : Nat} (t : CTm H n), termConsts (t.mapHead g) = termConsts t := by
  intro n t
  induction t with
  | var i => rfl
  | const k => rfl
  | head h => rfl
  | pi A B ihA ihB => simp only [CTm.mapHead, termConsts, ihA, ihB]
  | sigma A B ihA ihB => simp only [CTm.mapHead, termConsts, ihA, ihB]
  | id A a b ihA iha ihb => simp only [CTm.mapHead, termConsts, ihA, iha, ihb]
  | lam A b ihA ihb => simp only [CTm.mapHead, termConsts, ihA, ihb]
  | app f a ihf iha => simp only [CTm.mapHead, termConsts, ihf, iha]
  | pair a b iha ihb => simp only [CTm.mapHead, termConsts, iha, ihb]
  | fst p ih => simp only [CTm.mapHead, termConsts, ih]
  | snd p ih => simp only [CTm.mapHead, termConsts, ih]
  | refl a ih => simp only [CTm.mapHead, termConsts, ih]

/-- The parameter `0` instantiated by an expression is that expression. -/
theorem instantiate_zero (e : LevelExpr L) : LevelExpr.instantiate 0 e 0 = e := by
  show (if (0 : Nat) = 0 then e else .param 0) = e
  exact if_pos rfl

/-- Another parameter is kept. -/
theorem instantiate_other (e : LevelExpr L) {i : Nat} (other : i ≠ 0) :
    LevelExpr.instantiate 0 e i = .param i := by
  show (if i = 0 then e else .param i) = .param i
  exact if_neg other

/-! ## Values at every closed level -/

/-- **The family with given values at the closed levels.** It computes at the names of closed
levels only. -/
def Family.pointwise (name : DeclName) (bound : L) (type : CTm (Head L) 1)
    (value : L → CTm (Head L) 0) : Family L where
  name := name
  bound := bound
  type := type
  fires := fun e => ∃ d, e = .const d
  body := fun e =>
    match e with
    | .const d => value d
    | _ => .head (.tower .legacyGround)

/-- **A family given by its values at the closed levels does not compute at the name of a level
parameter.** -/
theorem pointwise_not_at_param (name : DeclName) (bound : L) (type : CTm (Head L) 1)
    (value : L → CTm (Head L) 0) (i : Nat) :
    ¬ (Family.pointwise name bound type value).fires (.param i) := by
  rintro ⟨d, impossible⟩
  cases impossible

section Pointwise

variable [LevelOrder L] {name : DeclName} {bound : L} {type : CTm (Head L) 1}
  {value : L → CTm (Head L) 0}

/-- A family with closed values and a closed type commutes with level substitution. -/
theorem pointwise_stable (typeClosed : LevelClosed type)
    (valuesClosed : ∀ d, LevelClosed (value d)) :
    (Family.pointwise name bound type value).Stable where
  type_closed := typeClosed
  fires_const := fun d => ⟨d, rfl⟩
  fires_subst := by
    rintro e σ ⟨d, rfl⟩
    exact ⟨d, rfl⟩
  body_subst := by
    rintro e σ ⟨d, rfl⟩
    exact valuesClosed d σ
  body_eval := by
    rintro e ν ⟨d, rfl⟩
    rfl

/-- **The rule with one premise for every closed level**: a family given by its values at the
closed levels is admitted when, at every closed level below the bound, its value has the
family's type at the name of that level. -/
theorem admitted_pointwise {Fs : List (Family L)} (admitted : Admitted Fs) (level : LevelExpr L)
    (fresh : declared Fs name = none)
    (unused : ∀ F' ∈ Fs, ∀ d, d < F'.bound → name ∉ termConsts (F'.body (.const d)))
    (selfFree : ∀ d, d < bound → name ∉ termConsts (value d))
    (typeClosed : LevelClosed type) (valuesClosed : ∀ d, LevelClosed (value d))
    (formed : CDerivable (church (unbounded L) Fs)
      (.typing (.snoc .nil (levelsBelow (.const bound))) type (universeAt level)))
    (instances : ∀ d, d < bound → CDerivable (church (unbounded L) Fs)
      (.typing .nil (value d) (CTm.inst0 (levelName (.const d)) type))) :
    Admitted (Family.pointwise name bound type value :: Fs) := by
  refine .cons level admitted fresh unused selfFree (pointwise_stable typeClosed valuesClosed)
    formed ?_
  rintro Δ positive e ⟨d, rfl⟩ below
  have strict : d < bound := LevelOrder.lt_of_succ_le (below _ positive.valid_bot)
  exact underBounds Δ (instances d strict)

end Pointwise

/-! ## One check -/

/-- **The family of the instances of one term**: its value at a level expression is the term
with that expression for the level parameter `0`. It computes at the name of every level
expression. -/
def Family.uniform (name : DeclName) (bound : L) (type : CTm (Head L) 1)
    (t : CTm (Head L) 0) : Family L where
  name := name
  bound := bound
  type := type
  fires := fun _ => True
  body := fun e => t.mapHead (substLevelsHead (LevelExpr.instantiate 0 e))

section Uniform

variable [LevelOrder L] {name : DeclName} {bound : L} {type : CTm (Head L) 1}
  {t : CTm (Head L) 0}

/-- The family of the instances of a term with the one level parameter `0`, at a closed type,
commutes with level substitution. -/
theorem uniform_stable (typeClosed : LevelClosed type) (only : OnlyParamZero t) :
    (Family.uniform name bound type t).Stable where
  type_closed := typeClosed
  fires_const := fun _ => trivial
  fires_subst := fun _ _ => trivial
  body_subst := by
    intro e σ _
    show (t.mapHead (substLevelsHead (LevelExpr.instantiate 0 e))).mapHead (substLevelsHead σ) =
      t.mapHead (substLevelsHead (LevelExpr.instantiate 0 (e.subst σ)))
    have composed : (fun h => substLevelsHead σ (substLevelsHead (LevelExpr.instantiate 0 e) h)) =
        substLevelsHead (fun i => (LevelExpr.instantiate 0 e i).subst σ) :=
      funext (substLevelsHead_comp σ _)
    rw [CTm.mapHead_comp, composed]
    refine only _ _ ?_
    show (LevelExpr.instantiate 0 e 0).subst σ = LevelExpr.instantiate 0 (e.subst σ) 0
    rw [instantiate_zero, instantiate_zero]
  body_eval := by
    intro e ν _
    show (t.mapHead (substLevelsHead (LevelExpr.instantiate 0 e))).mapHead (evalHead ν) =
      (t.mapHead (substLevelsHead (LevelExpr.instantiate 0 (.const (e.eval ν))))).mapHead
        (evalHead ν)
    have same : (fun h => evalHead ν (substLevelsHead (LevelExpr.instantiate 0 e) h)) =
        fun h => evalHead ν
          (substLevelsHead (LevelExpr.instantiate 0 (.const (e.eval ν))) h) := by
      funext h
      rw [evalHead_substLevelsHead, evalHead_substLevelsHead]
      congr 1
      funext i
      by_cases isZero : i = 0
      · subst isZero
        rw [instantiate_zero, instantiate_zero]
        rfl
      · rw [instantiate_other e isZero, instantiate_other _ isZero]
    rw [CTm.mapHead_comp, CTm.mapHead_comp, same]

/-- **A family is admitted by one check**: one derivation, with the level parameter `0` below
the family's bound, that the term has the family's type at the name of the parameter. -/
theorem admitted_uniform {Fs : List (Family L)} (admitted : Admitted Fs) (level : LevelExpr L)
    (fresh : declared Fs name = none)
    (unused : ∀ F' ∈ Fs, ∀ d, d < F'.bound → name ∉ termConsts (F'.body (.const d)))
    (selfFree : name ∉ termConsts t) (typeClosed : LevelClosed type) (only : OnlyParamZero t)
    (formed : CDerivable (church (unbounded L) Fs)
      (.typing (.snoc .nil (levelsBelow (.const bound))) type (universeAt level)))
    (typed : CDerivable (church (oneBound bound) Fs)
      (.typing .nil t (CTm.inst0 (levelName (.param 0)) type))) :
    Admitted (Family.uniform name bound type t :: Fs) := by
  refine .cons level admitted fresh unused ?_ (uniform_stable typeClosed only) formed ?_
  · intro d _ used
    refine selfFree ?_
    have value : (Family.uniform name bound type t).body (.const d) =
        t.mapHead (substLevelsHead (LevelExpr.instantiate 0 (.const d))) := rfl
    rwa [value, termConsts_mapHead] at used
  · intro Δ _ e _ below
    have admissible : Admissible Δ (oneBound bound) (LevelExpr.instantiate 0 e) :=
      LevelBounds.admissible_instantiate
        (fun i other c known => by
          rw [oneBound_other bound i other] at known
          cases known)
        (fun c known => by
          rw [oneBound_zero] at known
          cases known
          exact below)
    have instance_ := substLevels admitted.stable admissible typed
    have target : (CTm.inst0 (levelName (.param 0)) type).mapHead
        (substLevelsHead (LevelExpr.instantiate 0 e)) = CTm.inst0 (levelName e) type := by
      rw [CTm.mapHead_inst0, typeClosed]
      show CTm.inst0 (levelName (LevelExpr.instantiate 0 e 0)) type = _
      rw [instantiate_zero]
    show CDerivable (church Δ Fs)
      (.typing .nil (t.mapHead (substLevelsHead (LevelExpr.instantiate 0 e)))
        (CTm.inst0 (levelName e) type))
    rw [← target]
    exact instance_

end Uniform

/-! ## Examples -/

section Examples

variable [LevelOrder L] (c : L)

/-- The successor on names: its value under the parameter is the name of the successor. -/
def successorTerm : CTm (Head L) 0 := levelName (.succ (.param 0))

/-- The next universes: the universe above the parameter. -/
def nextTerm : CTm (Head L) 0 := universeAt (.succ (.param 0))

/-- The universes: the universe at the parameter. -/
def universesTerm : CTm (Head L) 0 := universeAt (.param 0)

omit [LevelOrder L] in
theorem successorTerm_only : OnlyParamZero (successorTerm (L := L)) := by
  intro σ τ same
  show levelName (.succ (σ 0)) = levelName (.succ (τ 0))
  rw [same]

omit [LevelOrder L] in
theorem nextTerm_only : OnlyParamZero (nextTerm (L := L)) := by
  intro σ τ same
  show universeAt (.succ (σ 0)) = universeAt (.succ (τ 0))
  rw [same]

omit [LevelOrder L] in
theorem universesTerm_only : OnlyParamZero (universesTerm (L := L)) := by
  intro σ τ same
  show universeAt (σ 0) = universeAt (τ 0)
  rw [same]

omit [LevelOrder L] in
/-- **A term with two level parameters is not determined by the image of the parameter `0`.**
-/
theorem not_onlyParamZero [Nonempty L] :
    ¬ OnlyParamZero (universeAt (.param 1) : CTm (Head L) 0) := by
  intro only
  obtain ⟨d⟩ := ‹Nonempty L›
  have same := only (fun _ => .param 0) (fun i => if i = 0 then .param 0 else .const d) rfl
  have unfolded : (universeAt (.param 0) : CTm (Head L) 0) = universeAt (.const d) := same
  injection unfolded with _ heads
  injection heads with tower
  injection tower with exprs
  cases exprs

variable {suc next universes second : DeclName}

/-- The successor on the names of the levels below a bound. -/
abbrev successorFamily (suc : DeclName) : Family L :=
  Family.uniform suc c (levelsBelow (.const c)) successorTerm

/-- The next universes. -/
abbrev nextFamily (next : DeclName) : Family L := Family.uniform next c (CU c) nextTerm

/-- The universes, at the type of the next universe. -/
abbrev universesFamily (next universes : DeclName) : Family L :=
  Family.uniform universes c (.app (.const next) (.var 0)) universesTerm

/-- The universes two levels up, from the next universes at the successor of the parameter. -/
abbrev secondNextFamily (next second : DeclName) : Family L :=
  Family.uniform second c (CU c) (.app (.const next) (levelName (.succ (.param 0))))

variable {c}

/-- The bounds with one parameter below a level above the least one are positive. -/
theorem oneBound_positive (positive : LevelOrder.bot < c) : (oneBound c).Positive := by
  intro i c' known
  by_cases isZero : i = 0
  · subst isZero
    rw [oneBound_zero] at known
    cases known
    exact positive
  · rw [oneBound_other c i isZero] at known
    cases known

/-- Under a parameter below a limit, the successor of the parameter is below the limit. -/
theorem succ_param_below (limit : LevelOrder.IsLimit c) :
    LeUnder (oneBound c) (.succ (.succ (.param 0))) (.const c) :=
  fun _ valid => LevelOrder.succ_le_of_lt (limit.succ_lt (valid 0 c (oneBound_zero c)))

/-- **The successor on names is admitted by one check**, for a limit bound. -/
theorem successor_admitted (limit : LevelOrder.IsLimit c) :
    Admitted [successorFamily c suc] :=
  admitted_uniform .nil (.const c) rfl (fun _ mem => nomatch mem)
    (fun used => absurd used List.not_mem_nil) (fun _ => rfl) successorTerm_only
    (lift_bare (levelsBelow_typed _)) (lift_bare (levelName_typed (succ_param_below limit)))

/-- **The successor on names at the name of a level is the name of its successor.** -/
theorem successor_at (limit : LevelOrder.IsLimit c) {Δ : LevelBounds L} (positive : Δ.Positive)
    {e : LevelExpr L} (below : LeUnder Δ (.succ e) (.const c)) :
    CDerivable (church Δ [successorFamily c suc])
      (.equality .nil (.app (.const suc) (levelName e)) (levelName (.succ e))
        (levelsBelow (.const c))) := by
  have computed := family_at (successor_admitted (suc := suc) limit) positive
    (e := e) trivial below
  have value : (successorFamily c suc).body e = levelName (.succ e) := by
    show levelName (.succ (LevelExpr.instantiate 0 e 0)) = _
    rw [instantiate_zero]
  rw [value] at computed
  exact computed

/-- **The next universes are admitted by one check**, for a limit bound: under `l < c`, the
universe at `l + 1` is a member of the universe at `c`. -/
theorem next_admitted (limit : LevelOrder.IsLimit c) : Admitted [nextFamily c next] :=
  admitted_uniform .nil (.succ (.const c)) rfl (fun _ mem => nomatch mem)
    (fun used => absurd used List.not_mem_nil) (fun _ => rfl) nextTerm_only
    (lift_bare (universeAt_typed _)) (lift_bare (universeAt_mem (succ_param_below limit)))

/-- **The universes are admitted by one check**, over the next universes: under the parameter,
the universe at `l` is a member of the universe at `l + 1`, which is the next universe at the
name of `l`. -/
theorem universes_admitted (limit : LevelOrder.IsLimit c) (distinct : universes ≠ next) :
    Admitted [universesFamily c next universes, nextFamily c next] := by
  have first := next_admitted (next := next) limit
  have atParam : LeUnder (oneBound c) (.succ (.param 0)) (.const c) :=
    LevelBounds.succ_le_of_lt_bound (oneBound_zero c)
  refine admitted_uniform first (.const c) ?_ ?_ (fun used => absurd used List.not_mem_nil)
    (fun _ => rfl) universesTerm_only
    (.appElim (A := levelsBelow (.const c)) (B := CU c) (family_const_typed first) (.var 0)) ?_
  · show (if universes = next then some (CTm.pi (levelsBelow (.const c)) (CU c)) else none) =
      (none : Option (CTm (Head L) 0))
    rw [if_neg distinct]
  · intro F' mem d _ used
    obtain rfl := List.mem_singleton.mp mem
    exact absurd used List.not_mem_nil
  · have computed := family_at first (oneBound_positive limit.1) (e := .param 0) trivial atParam
    have value : (nextFamily c next).body (.param 0) = universeAt (.succ (.param 0)) := by
      show universeAt (.succ (LevelExpr.instantiate 0 (.param 0) 0)) = _
      rw [instantiate_zero]
    rw [value] at computed
    exact .conv (lift_bare (universeAt_typed _)) (.symm computed) (.tower (.sort _))

/-- **The universes at the name of a level are the universe at that level**, wherever the
level lies below the bound: at closed levels and under level parameters. -/
theorem universes_at (limit : LevelOrder.IsLimit c) (distinct : universes ≠ next)
    {Δ : LevelBounds L} (positive : Δ.Positive) {e : LevelExpr L}
    (below : LeUnder Δ (.succ e) (.const c)) :
    CDerivable (church Δ [universesFamily c next universes, nextFamily c next])
      (.equality .nil (.app (.const universes) (levelName e)) (universeAt e)
        (.app (.const next) (levelName e))) := by
  have computed := family_at (universes_admitted limit distinct) positive (e := e) trivial below
  have value : (universesFamily c next universes).body e = universeAt e := by
    show universeAt (LevelExpr.instantiate 0 e 0) = _
    rw [instantiate_zero]
  rw [value] at computed
  exact computed

/-- **A family from one check computes under a level parameter**: under `l < c`, the universes
at the name of `l` are the universe at `l`. -/
theorem universes_at_param (limit : LevelOrder.IsLimit c) (distinct : universes ≠ next) :
    CDerivable (church (oneBound c) [universesFamily c next universes, nextFamily c next])
      (.equality .nil (.app (.const universes) (levelName (.param 0))) (universeAt (.param 0))
        (.app (.const next) (levelName (.param 0)))) :=
  universes_at limit distinct (oneBound_positive limit.1)
    (LevelBounds.succ_le_of_lt_bound (oneBound_zero c))

/-- **A family that uses an earlier one at the successor of its parameter is admitted by one
check**: under `l < c`, the next universe at the name of `l + 1` is a member of the universe at
`c`. -/
theorem secondNext_admitted (limit : LevelOrder.IsLimit c) (distinct : second ≠ next) :
    Admitted [secondNextFamily c next second, nextFamily c next] := by
  have first := next_admitted (next := next) limit
  refine admitted_uniform first (.succ (.const c)) ?_ ?_ ?_ (fun _ => rfl) ?_
    (lift_bare (universeAt_typed _)) (family_app_typed first (succ_param_below limit))
  · show (if second = next then some (CTm.pi (levelsBelow (.const c)) (CU c)) else none) =
      (none : Option (CTm (Head L) 0))
    rw [if_neg distinct]
  · intro F' mem d _ used
    obtain rfl := List.mem_singleton.mp mem
    exact absurd used List.not_mem_nil
  · intro used
    rcases List.mem_append.mp used with atConst | atName
    · exact distinct (List.mem_singleton.mp atConst)
    · exact absurd atName List.not_mem_nil
  · intro σ τ same
    show CTm.app (.const next) (levelName (.succ (σ 0))) =
      .app (.const next) (levelName (.succ (τ 0)))
    rw [same]

/-- **At the name of a level it is the universe two levels up.** -/
theorem secondNext_at (limit : LevelOrder.IsLimit c) (distinct : second ≠ next) {d : L}
    (below : d < c) :
    CDerivable (church (unbounded L) [secondNextFamily c next second, nextFamily c next])
      (.equality .nil (.app (.const second) (levelName (.const d)))
        (universeAt (.succ (.succ (.const d)))) (CU c)) := by
  have admitted := secondNext_admitted limit distinct
  have first := next_admitted (next := next) limit
  have atLevel : LeUnder (unbounded L) (.succ (.const d)) (.const c) :=
    fun _ _ => LevelOrder.succ_le_of_lt below
  have atSucc : LeUnder (unbounded L) (.succ (.succ (.const d))) (.const c) :=
    fun _ _ => LevelOrder.succ_le_of_lt (limit.succ_lt below)
  have unfolded := family_at admitted positive_unbounded (e := .const d) trivial atLevel
  have value : (secondNextFamily c next second).body (.const d) =
      .app (.const next) (levelName (.succ (.const d))) := by
    show CTm.app (.const next) (levelName (.succ (LevelExpr.instantiate 0 (.const d) 0))) = _
    rw [instantiate_zero]
  rw [value] at unfolded
  have inner := family_at first positive_unbounded (e := .succ (.const d)) trivial atSucc
  have innerValue : (nextFamily c next).body (.succ (.const d)) =
      universeAt (.succ (.succ (.const d))) := by
    show universeAt (.succ (LevelExpr.instantiate 0 (.succ (.const d)) 0)) = _
    rw [instantiate_zero]
  rw [innerValue] at inner
  exact .trans unfolded (lift_cons admitted inner)

end Examples

/-! ### Over the notations below `ε₀` -/

/-- **Over the notations below `ε₀`, the universes at all the finite levels are admitted by
one check** under a level parameter below `ω`. -/
theorem finiteUniverses_admitted :
    Admitted [universesFamily Level.omega (.str .anonymous "nextUniverse")
        (.str .anonymous "universes"),
      nextFamily Level.omega (.str .anonymous "nextUniverse")] :=
  universes_admitted Level.isLimit_omega (by decide)

/-- Over the notations: the member of the family of the finite universes at the name of `2`
is the universe at `2`. -/
theorem finiteUniverses_at_two :
    CDerivable
      (church (unbounded Level)
        [universesFamily Level.omega (.str .anonymous "nextUniverse")
            (.str .anonymous "universes"),
          nextFamily Level.omega (.str .anonymous "nextUniverse")])
      (.equality .nil
        (.app (.const (.str .anonymous "universes")) (levelName (.const (Level.ofNat 2))))
        (universeAt (.const (Level.ofNat 2)))
        (.app (.const (.str .anonymous "nextUniverse")) (levelName (.const (Level.ofNat 2))))) :=
  universes_at Level.isLimit_omega (by decide) positive_unbounded
    (fun _ _ => LevelOrder.succ_le_of_lt (Level.ofNat_lt_omega 2))

end LevelNames
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
