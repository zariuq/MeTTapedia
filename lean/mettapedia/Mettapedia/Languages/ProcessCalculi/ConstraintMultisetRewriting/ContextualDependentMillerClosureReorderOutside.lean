import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentMillerClosureReorderControls

/-!
# The reordered store is outside the Miller class

A store leaves `StratifiedMiller` as soon as its first equation's annotations are η-long normal types that differ up
to heads (`not_stratifiedMiller_of_long`): with nothing before it, the identity is a solution of the empty prefix, so
the class asks the two annotations to be equal types, and η-long normal forms reflect the typed βη equality
(`ContextualDependentEtaLong.long_type_unique`).

For the store of `ContextualDependentMillerClosure.ReorderControls`, the residual store after the first round of the
last family starts with the twin at `G A B` and `G B A`: two neutral types of a binary family declared at
`U0 → U0 → U0`, with arguments declared at `U0`, in a different order. Both are η-long (`binaryNeutral_long`), and
they differ up to heads, so the residual store is outside the class (`reorder_leaves_class`), while the store itself is
in it (`reorder_stratifiedMiller`): the class is not closed under R86's in-place step (`inPlace_not_closed`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentMillerClosure

open CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentEtaLong ContextualDependentShortClosure

section Outside

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (complete : AlgorithmicComplete S.R S.roles)

include facts roots heads algebra complete in
/-- **A store leaves the Miller class** when the annotations of its first equation are η-long normal types that
differ up to heads. -/
theorem not_stratifiedMiller_of_long {Θ : Context S.R} {first : Equation (TotalTerm Θ)}
    {rest : EquationStore (TotalTerm Θ)}
    (left : Long S.R S.roles (.type Θ.raw first.1.1.code))
    (right : Long S.R S.roles (.type Θ.raw first.2.1.code))
    (different : ¬ SameUpToHeads S.R first.1.1.code first.2.1.code) :
    ¬ StratifiedMiller S.levels (first :: rest) := by
  intro stratified
  have held := (stratified [] rest first rfl).2 (𝟙 Θ)
    ((models_iff S.levels (𝟙 Θ) []).mpr fun _ member => nomatch member)
  have identity : ∀ t : Tm Head Θ.arity, subst (𝟙 Θ : Θ ⟶ Θ).substitution t = t := subst_ids
  rw [identity, identity] at held
  exact different (long_type_unique facts roots heads algebra complete Θ.formed left right held)

end Outside

/-- The neutral type `F a b` of a variable applied to two variables. -/
def binaryNeutral {Head : Type} {n : Nat} : Tm Head n → Option (Fin n × Fin n × Fin n)
  | .app (.app (.var f) (.var a)) (.var b) => some (f, a, b)
  | _ => none

theorem binaryNeutral_eq {Head : Type} {n : Nat} {t : Tm Head n} {f a b : Fin n}
    (read : binaryNeutral t = some (f, a, b)) : t = .app (.app (.var f) (.var a)) (.var b) := by
  unfold binaryNeutral at read
  split at read
  · simp only [Option.some.injEq, Prod.mk.injEq] at read
    obtain ⟨rfl, rfl, rfl⟩ := read
    rfl
  · cases read

theorem not_same_binary {Head : Type} {R : Rules Head} {n : Nat} {f a b f' a' b' : Fin n}
    (different : ¬ (a = a' ∧ b = b')) :
    ¬ SameUpToHeads R (.app (.app (.var f) (.var a)) (.var b)) (.app (.app (.var f') (.var a')) (.var b')) := by
  intro same
  cases same with
  | app inner last =>
    cases inner with
    | app _ middle =>
      cases middle
      cases last
      exact different ⟨rfl, rfl⟩

namespace ReorderControls

open ContextualDependentWorklist ContextualDependentDynamicFragment
open ContextualDependentPatternFiring.Controls ContextualDependentIntersectionGeneral.InPlaceControls

theorem universe_isType {n : Nat} (Γ : Tower.Ctx n) : IsType Tower.rules Γ (.head (.sort Tower.zero)) :=
  ⟨.sort (.succ Tower.zero), .sort _, .headType (.sort _)⟩

/-- The binary family `U0 → U0 → U0`. -/
def binaryFamily {n : Nat} : Tower.Tm n :=
  .pi (.head (.sort Tower.zero)) (.pi (.head (.sort Tower.zero)) (.head (.sort Tower.zero)))

theorem unary_isType {n : Nat} (Γ : Tower.Ctx n) :
    IsType Tower.rules Γ (.pi (.head (.sort Tower.zero)) (.head (.sort Tower.zero))) :=
  ⟨_, .sort _, .piForm (.headType (.sort _)) (.sort _) (.headType (.sort _)) (.sort _) (.sorts _ _)⟩

/-- A variable declared at `U0` is η-long at `U0`. -/
theorem universeVar_long {n : Nat} {Γ : Tower.Ctx n} (i : Fin n)
    (lookup : Ctx.lookup Γ i = .head (.sort Tower.zero)) :
    Long Tower.rules TowerModel.roles (.term Γ (.var i) (.head (.sort Tower.zero))) := by
  have typed : Typed Tower.rules Γ (.var i) (.head (.sort Tower.zero)) := lookup ▸ Derivable.var i
  have same : TypeEq Tower.rules Γ (.head (.sort Tower.zero)) (Ctx.lookup Γ i) := by
    rw [lookup]
    exact IsType.refl (universe_isType Γ)
  exact .univ (u := .sort Tower.zero) (.sort _) (IsType.refl (universe_isType Γ)) typed
    (.neutralType (.var i same) (.sort _) (IsType.below_refl (universe_isType Γ)))

/-- **A binary family applied to two variables of `U0` is an η-long type.** -/
theorem binaryNeutral_long {n : Nat} {Γ : Tower.Ctx n} (formed : CtxFormed Tower.rules Γ) (f a b : Fin n)
    (family : Ctx.lookup Γ f = binaryFamily) (first : Ctx.lookup Γ a = .head (.sort Tower.zero))
    (second : Ctx.lookup Γ b = .head (.sort Tower.zero)) :
    Long Tower.rules TowerModel.roles (.type Γ (.app (.app (.var f) (.var a)) (.var b))) := by
  have familyType : IsType Tower.rules Γ binaryFamily :=
    family ▸ Typed.isType (S := setting) (Derivable.var f) formed
  have head : Long Tower.rules TowerModel.roles (.spine Γ (.var f) binaryFamily) :=
    .var f (by rw [family]; exact IsType.refl familyType)
  have inner : Long Tower.rules TowerModel.roles (.spine Γ (.app (.var f) (.var a))
      (.pi (.head (.sort Tower.zero)) (.head (.sort Tower.zero)))) :=
    .app head (IsType.refl familyType) (universeVar_long a first) (IsType.refl (unary_isType Γ))
  have outer : Long Tower.rules TowerModel.roles (.spine Γ (.app (.app (.var f) (.var a)) (.var b))
      (.head (.sort Tower.zero))) :=
    .app inner (IsType.refl (unary_isType Γ)) (universeVar_long b second) (IsType.refl (universe_isType Γ))
  exact .neutralType outer (.sort _) (IsType.below_refl (universe_isType Γ))

/-- The annotations `V` and `W` are a binary family applied to two variables of `U0`, in a different order or at
different arguments. -/
def outsideCodes {n : Nat} (Γ : Tower.Ctx n) (V W : Tower.Tm n) : Bool :=
  match binaryNeutral V, binaryNeutral W with
  | some (f, a, b), some (f', a', b') =>
      decide (¬ (a = a' ∧ b = b') ∧ Ctx.lookup Γ f = binaryFamily ∧ Ctx.lookup Γ f' = binaryFamily ∧
        Ctx.lookup Γ a = .head (.sort Tower.zero) ∧ Ctx.lookup Γ b = .head (.sort Tower.zero) ∧
        Ctx.lookup Γ a' = .head (.sort Tower.zero) ∧ Ctx.lookup Γ b' = .head (.sort Tower.zero))
  | _, _ => false

theorem outsideCodes_sound {n : Nat} {Γ : Tower.Ctx n} (formed : CtxFormed Tower.rules Γ) {V W : Tower.Tm n}
    (check : outsideCodes Γ V W = true) :
    Long Tower.rules TowerModel.roles (.type Γ V) ∧ Long Tower.rules TowerModel.roles (.type Γ W) ∧
      ¬ SameUpToHeads Tower.rules V W := by
  unfold outsideCodes at check
  split at check
  · rename_i f a b f' a' b' readV readW
    obtain ⟨different, family, family', first, second, first', second'⟩ := of_decide_eq_true check
    rw [binaryNeutral_eq readV, binaryNeutral_eq readW]
    exact ⟨binaryNeutral_long formed f a b family first second,
      binaryNeutral_long formed f' a' b' family' first' second', not_same_binary different⟩
  · cases check

/-- The first equation of a store has annotations as in `outsideCodes`. -/
def outsideCheck {Θ : Context setting.R} : EquationStore (TotalTerm Θ) → Bool
  | [] => false
  | first :: _ => outsideCodes Θ.raw first.1.1.code first.2.1.code

theorem not_stratifiedMiller_of_check {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)}
    (check : outsideCheck problem = true) : ¬ StratifiedMiller setting.levels problem := by
  match problem, check with
  | first :: rest, check =>
      obtain ⟨left, right, different⟩ := outsideCodes_sound Θ.formed check
      exact not_stratifiedMiller_of_long (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
        TowerModel.algebra TowerModel.complete left right different

/-- After one round of the last family the residual store's first equation has annotations as in `outsideCodes`. -/
noncomputable def outsideAfterOne : Bool :=
  match run inPlaceOnly reorderStore 1 with
  | .cutoff state => outsideCheck state.remaining
  | _ => false

theorem outsideAfterOne_true : outsideAfterOne = true := by decide +kernel

/-- **The residual store after the first round is outside the Miller class.** -/
theorem reorder_leaves_class :
    ∃ state : ContextualDependentUpdate.Update setting.levels reorderStore,
      run inPlaceOnly reorderStore 1 = .cutoff state ∧ ¬ StratifiedMiller setting.levels state.remaining := by
  have key := outsideAfterOne_true
  unfold outsideAfterOne at key
  generalize ran : run inPlaceOnly reorderStore 1 = outcome at key
  cases outcome with
  | cutoff state => exact ⟨state, rfl, not_stratifiedMiller_of_check key⟩
  | solved _ _ => simp at key
  | refuted _ => simp at key
  | stuck _ => simp at key

/-- **`StratifiedMiller` is not closed under the last family's first round**: the store is in the class, and the
residual store after R86's in-place answer is not. -/
theorem inPlace_not_closed :
    StratifiedMiller setting.levels reorderStore ∧
      ∃ state : ContextualDependentUpdate.Update setting.levels reorderStore,
        run inPlaceOnly reorderStore 1 = .cutoff state ∧ ¬ StratifiedMiller setting.levels state.remaining :=
  ⟨reorder_stratifiedMiller, reorder_leaves_class⟩

end ReorderControls
end ContextualDependentMillerClosure
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
