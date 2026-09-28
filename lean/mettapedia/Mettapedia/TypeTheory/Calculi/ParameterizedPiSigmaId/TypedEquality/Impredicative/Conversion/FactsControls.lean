import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Conversion.TowerSound
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Algorithmic.Completeness

/-!
# Controls for the facts about weak-head forms of types

The consequences of the typed equality are stated over the facts about the
weak-head forms of types (`FormFacts`), over the lifting of spine comparisons
(`SpineLift`) and over the completeness of the algorithmic equality
(`AlgorithmicComplete`); their presuppositions hold syntactically. Read on the
universe tower `U₀ : U₁ : …` and on two packages built from it:

* **the tower** has the facts, spine comparisons lift and the algorithmic
  equality is complete (`Tower.spineLift`, `Tower.complete`), and through the
  facts `Π U₀. U₀` and `Π U₀. U₁` are not equal (`Tower.pi_codomains_differ`);
* **the tower with a root step from `U₀` to `U₁`** has no facts: the two
  universes, weak-head forms of equal types, would be one head
  (`Tower.collapse_not_formFacts`); its presuppositions hold all the same
  (`Tower.collapse_presupposed`);
* **the tower with a constant computing to itself** has no facts, its spine
  comparisons do not lift, and its algorithmic equality is not complete: the
  constant is a type that reaches no weak-head form (`Tower.loop_not_formFacts`,
  `Tower.loop_not_spineLift`, `Tower.loop_not_complete`);
* **a head typed by a head that is no universe** has a type that is no type: the
  presuppositions need a level model (`Tower.unleveled_type_not_type`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Conversion

open Normalization

namespace Tower

/-! ## The tower -/

/-- The tower has no root step. -/
theorem roots : RootPreserving rules := fun _ step => nomatch step

/-- The tower has no head equality. -/
theorem heads : HeadPreserving rules := fun same => nomatch same

/-- The cumulativity of the tower is the order of the natural numbers. -/
theorem algebra : CumulativeAlgebra rules where
  trans := Nat.le_trans
  same_left := fun same le => by
    rcases same with rfl | e
    · exact le
    · exact e.elim
  same_right := fun le same => by
    rcases same with rfl | e
    · exact le
    · exact e.elim
  join_least := fun {u v w x} join hu hv => by
    change w = max u v at join
    subst join
    exact max_le hu hv

/-- The tower declares no constant, so every declared constant is semantic for
the algorithmic equality too. -/
theorem algorithmicConstants : SemanticConstants (algorithmicSetting setting) :=
  fun declared _ _ => nomatch declared

/-- **Spine comparisons lift in the tower**, by the one-sided model. -/
theorem spineLift : SpineLift setting :=
  SpineLift.ofSemantic (declarative_laws _ levels) constants roots heads algebra

/-- **The algorithmic equality is complete for the tower**, by the one-sided
model over it. -/
theorem complete : AlgorithmicComplete rules (fun _ => .rigid) :=
  AlgorithmicComplete.ofSemantic (S := setting) (declarative_laws _ levels) constants roots heads
    algebra algorithmicConstants

/-- **`Π U₀. U₀` and `Π U₀. U₁` are not equal**: the facts give injectivity of
dependent function types and of heads. -/
theorem pi_codomains_differ :
    ¬ TypeEq rules (.nil : Ctx Nat 0) (.pi (.head 0) (.head 0)) (.pi (.head 0) (.head 1)) := by
  intro equal
  obtain ⟨-, eB⟩ := TypeEq.pi_injective side.facts equal .nil
  rcases TypeEq.head_injective side.facts eB (.snoc .nil ⟨1, trivial, .headType rfl⟩) with e | e
  · exact absurd e (by decide)
  · exact e

/-! ## A step making two universes equal -/

/-- **The tower with a root step from `U₀` to `U₁` has no facts about the
weak-head forms of its types**: the weak-head forms `U₀` and `U₁` of equal types
would be one head. -/
theorem collapse_not_formFacts (roles : Roles Nat) : ¬ FormFacts collapse roles := by
  intro facts
  rcases TypeEq.head_injective facts ⟨2, trivial, collapse_equal⟩ .nil with e | e
  · exact absurd e (by decide)
  · exact e

/-- The levels of the tower are levels of the package with the collapsing step,
which keeps its universes. -/
def collapseLevels : LevelModel collapse Nat where
  level := levels.level
  successor := levels.successor
  universe_typing := levels.universe_typing
  ground_typing := levels.ground_typing
  cumulative_universe := levels.cumulative_universe
  headEq_level := levels.headEq_level
  join_level := levels.join_level
  join_exists := levels.join_exists
  join_upper := levels.join_upper
  cumulative_refl := levels.cumulative_refl
  headEq_symm := fun e => nomatch e
  headEq_trans := fun e _ => nomatch e
  universe_decided := levels.universe_decided

/-- **The presuppositions hold without the facts**: in the package with the
collapsing step, which has no facts, both sides of the equation of `U₀` with
`U₁` are typed at `U₂`, which is a type. -/
theorem collapse_presupposed :
    Typed collapse (.nil : Ctx Nat 0) (.head 0) (.head 2) ∧
      Typed collapse (.nil : Ctx Nat 0) (.head 1) (.head 2) ∧
        IsType collapse (.nil : Ctx Nat 0) (.head 2) :=
  Derivable.presupposed collapseLevels collapse_equal .nil

/-! ## A head typed by a head that is no universe -/

/-- A universe presentation whose head `0` is typed by the head `1`, which is no
universe and has no type. -/
def unleveled : Rules Nat where
  headTyping h u := h = 0 ∧ u = 1
  isUniverse u := u = 0
  join u v w := w = max u v
  cumulative u v := u = v
  headEq _ _ := False

/-- **Without a level model the type of a typed term need not be a type**: the
head `0` has the type `1`, which is no type. -/
theorem unleveled_type_not_type :
    Typed unleveled (.nil : Ctx Nat 0) (.head 0) (.head 1) ∧
      ¬ IsType unleveled (.nil : Ctx Nat 0) (.head 1) := by
  refine ⟨.headType ⟨rfl, rfl⟩, ?_⟩
  rintro ⟨u, -, typing⟩
  obtain ⟨w, ⟨h, -⟩, -⟩ := Typed.generation typing
  exact absurd h (by decide)

/-! ## A type computing to itself -/

/-- A constant of the lowest universe that computes to itself. -/
def loopName : DeclName := `Conversion.Tower.loop

/-- The step from the looping constant to itself. -/
def loopStep : RootComputation Nat where
  step := fun l r => l = .const loopName ∧ r = .const loopName
  rename := by
    rintro n m ρ l r ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩
  substitute := by
    rintro n m σ l r ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩

/-- The tower with the looping constant, declared in the lowest universe. -/
def loop : Rules Nat :=
  { rules with
    constantType := fun c => if c = loopName then some (.head 0) else none
    computation := loopStep }

/-- The looping constant computes with no argument; every other name is rigid. -/
def loopRoles : Roles Nat := fun c => if c = loopName then .computes 0 .leaf else .rigid

theorem loopRoles_loop : loopRoles loopName = .computes 0 .leaf := if_pos rfl

theorem loopRoles_not_inductive (T : DeclName) (cs : List (DeclName × List (Field Nat))) :
    loopRoles T ≠ .inductive cs := by
  unfold loopRoles
  split <;> exact fun h => nomatch h

/-- The looping step has root shape. -/
theorem loopShape : RootShape loop loopRoles where
  spine := by
    rintro n t u ⟨rfl, rfl⟩
    exact ⟨loopName, 0, .leaf, [], loopRoles_loop, rfl, rfl, .leaf []⟩
  deterministic := by
    rintro n t u u' ⟨rfl, rfl⟩ ⟨-, rfl⟩
    rfl

/-- The levels of the tower are levels of the package with the looping
constant. -/
def loopLevels : LevelModel loop Nat where
  level := levels.level
  successor := levels.successor
  universe_typing := levels.universe_typing
  ground_typing := levels.ground_typing
  cumulative_universe := levels.cumulative_universe
  headEq_level := levels.headEq_level
  join_level := levels.join_level
  join_exists := levels.join_exists
  join_upper := levels.join_upper
  cumulative_refl := levels.cumulative_refl
  headEq_symm := fun e => nomatch e
  headEq_trans := fun e _ => nomatch e
  universe_decided := levels.universe_decided

/-- The normalization setting of the package with the looping constant. -/
def loopSetting : Setting Nat Nat where
  R := loop
  roles := loopRoles
  E := declarative loop
  levels := loopLevels
  shape := loopShape
  constructors := ConstructorsDeclared.of_no_inductive loopRoles_not_inductive

/-- The looping constant is declared in the lowest universe. -/
theorem loop_declared : loop.constantType loopName = some (.head 0) := by
  show (if loopName = loopName then some (Tm.head 0 : Tm Nat 0) else none) = some (.head 0)
  exact if_pos rfl

/-- The looping constant is a type of the lowest universe. -/
theorem loop_typed {n : Nat} {Γ : Ctx Nat n} : Typed loop Γ (.const loopName) (.head 0) :=
  .const (u := 1) loop_declared (.headType rfl) trivial

/-- The looping constant reduces only to itself. -/
theorem loop_reduces {n : Nat} {t : Tm Nat n} (red : WhRed loop loopRoles (.const loopName) t) :
    t = .const loopName := by
  induction red with
  | refl => rfl
  | tail _ step ih =>
      subst ih
      exact WhStep.deterministic loopShape (.root ⟨rfl, rfl⟩) step

/-- The looping constant is no weak-head form of a type. -/
theorem loop_not_typeForm {n : Nat} : ¬ IsTypeForm loopRoles (.const loopName : Tm Nat n) :=
  fun form => IsTypeForm.whnf (S := loopSetting) form _ (.root ⟨rfl, rfl⟩)

/-- **A package with a type computing to itself has no facts about the weak-head
forms of its types**: the looping constant is a type that reaches no weak-head
form. -/
theorem loop_not_formFacts : ¬ FormFacts loop loopRoles := by
  intro facts
  obtain ⟨A', red, form⟩ := facts.typeForm (Γ := .nil) ⟨0, trivial, loop_typed⟩ .nil
  obtain rfl := loop_reduces red.red
  exact loop_not_typeForm form

/-- **In a package with a type computing to itself spine comparisons do not
lift**: a variable of the looping type is compared with itself as a spine in
every world, but not at its type, which reaches no weak-head form. -/
theorem loop_not_spineLift : ¬ SpineLift loopSetting := by
  intro lift
  have formed : CtxFormed loop (.snoc .nil (.const loopName)) := .snoc .nil ⟨0, trivial, loop_typed⟩
  have typed : Typed loop (.snoc .nil (.const loopName)) (.var 0) (.const loopName) := .var 0
  have compared := lift formed (.inl (.var 0)) (.inl (.var 0)) (.refl typed)
    (SpinesEverywhere.var 0)
  cases compared with
  | terms reducedType form _ _ _ =>
      obtain rfl := loop_reduces reducedType.red
      exact loop_not_typeForm form

/-- **In a package with a type computing to itself the algorithmic equality is
not complete**: the looping type is equal to itself in the lowest universe, but
the algorithm compares it with nothing, since it reaches no weak-head form. -/
theorem loop_not_complete : ¬ AlgorithmicComplete loop loopRoles := by
  intro complete
  have compared := complete (Γ := .nil) .nil (.refl loop_typed)
  cases compared with
  | terms reducedType form reduced reduced' comparedW =>
      obtain rfl := WhRed.eq_of_whnf (S := loopSetting) (head_whnf loopShape 0) reducedType.red
      obtain rfl := loop_reduces reduced.red
      obtain rfl := loop_reduces reduced'.red
      cases comparedW with
      | univ _ _ _ comparedTypes =>
          cases comparedTypes with
          | inductiveType role _ => exact loopRoles_not_inductive _ _ role
          | neutralTypes neutral _ _ _ =>
              exact Neutral.whnf loopShape neutral _ (.root ⟨rfl, rfl⟩)
      | spine spineType _ _ _ _ _ =>
          rcases spineType with ⟨_, _, _, e⟩ | neutral | ⟨_, _, _, e⟩ | ⟨_, e, notUniverse⟩
          · cases e
          · exact neutral.not_former.1 0 rfl
          · cases e
          · exact notUniverse trivial

end Tower

end Conversion
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
