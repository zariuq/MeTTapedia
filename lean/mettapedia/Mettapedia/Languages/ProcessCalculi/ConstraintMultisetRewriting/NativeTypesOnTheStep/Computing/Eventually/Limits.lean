import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Eventually.Instances
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.PartialConstants
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.ExecutableChecking

/-!
# Where a fixed budget fails, and what no budget can do

**No fixed budget suffices** (`normalize_betaTower`, `compare_betaTower`). In every package, whatever its
root evaluator, the normalizer needs one step for each of `j` nested β-redexes of the identity, so a term
with `j` of them is not normalized below budget `j + 1`; the comparison normalizes the type first, so at a
type with `k` such redexes it does not answer at budget `k`. In the vectors package the pair `zero, zero` at
the type `(λ x. x)ᵏ num` is an equality for every `k` and unanswered at budget `k` (`vectors_cliff`), and it
is answered from budget `k + 3` on, with no hypothesis (`vectors_cliff_transient`). The executable
functions take their budget as a parameter; 16 is the budget the tree's examples pass. The kernel
evaluates the member of the family at which budget 16 fails: unanswered at 16, answered at 17
(`cliff16`).

**A looping row: normal forms must exist** (`loop_cliff`). The tower with one small type constant
`loop` and the row `loop ⟶ loop` has a complete root evaluator, `loop` is typed and equal to itself,
and the comparison over the tree's normalizer answers the pair at no budget. Over the normalization
setting of that package, built from its own roles and shape (`loopSetting`, whose declarative
equality has the model's laws, `loopSetting_laws`), three hypotheses of the general theorems fail
together (`loop_cliff_fails_three`): strong normalization of typed terms (`loop_not_typedSN`);
weak-head normalization, for every reducer, since every reduct of `loop` is `loop` and `loop` is
weak-head normal under no roles (`loop_no_whnf_reduct`, `loopSetting_not_whnfEventually`); and
completeness of the algorithmic equality, since `loop = loop : U₀` has no algorithmic derivation
(`loop_not_algorithmicComplete`). So the looping row shows that normal forms must exist, and nothing
more: it does not separate strong normalization from weak-head normalization. In the same package
`λ x. loop` is typed and weak-head normal, and the normalizer never finishes on it
(`loopLam_whnf_unnormalized`); its body has no normal form, so this too shows only that a full
normalizer needs normal forms. Normal forms of a term are not enough for the tree's order of
reduction either: `Detour.detour` is a typed term with a normal form and a weak-head normal form on
which the full normalizer fails at every budget, in a package not shown to meet the hypotheses of
the general theorems. On a qualified package whose typed terms all have weak-head normal forms the
same happens (`Erasing.separation`), so in `qualified_normalize_eventually`, a theorem about the
tree's normalizer, strong normalization cannot be weakened to weak-head normalization
(`Erasing.whnf_not_enough`). That package has one complete root evaluator, and the failure is the
normalizer's traversal: one that steps arguments first reaches the normal form
(`Erasing.argFirst_normalizes`). It does not show that the comparison needs strong normalization; it
shows only that the tree's normalizer is not a reducer meeting the comparison's hypothesis there
(`Erasing.normalizer_not_whnfEventually`).

**The comparison cannot refuse** (`compare_none_of_not_equal`). It returns a certificate or nothing; on two
typed terms that are not equal it returns nothing at every budget, so "not equal" and "ran out" are one
output. In the vectors package the universes `U₀` and `U₁` are typed in `U₂` and not equal
(`u0_ne_u1`), and the comparison returns nothing for them at every budget (`u0_u1_unanswered`).

**The checker's boundary** (`check_fst_pair_none`). The checker synthesizes eliminations and checks
introductions; it has no rule that synthesizes a pair. So the first projection of a pair literal, typed in
the vectors package (`fst_pair_typed`), is accepted at no budget (`fst_pair_never_checked`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.Computing.Eventually

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open ExecutableReduction ExecutableConversion
open TowerVectorsModel (U0 numC zeroC)

/-! ## No fixed budget suffices -/

section Tower

variable {Head : Type}

/-- `j` applications of the identity function around `a`. -/
def betaTower {n : Nat} (a : Tm Head n) : Nat → Tm Head n
  | 0 => a
  | j + 1 => .app (.lam (.var 0)) (betaTower a j)

variable {L : Type} [UniverseLevel.LevelOrder L] (S : Setting Head L) (root : RootEvaluator S.R)

/-- A β-redex is not a root step of any package: root steps start at constant spines. -/
theorem root_betaRedex {n : Nat} (a : Tm Head n) : root (.app (.lam (.var 0)) a) = none := by
  cases h : root (.app (.lam (.var 0)) a) with
  | none => rfl
  | some next =>
      obtain ⟨c, _, _, args, _, same, _, _⟩ := S.shape.spine next.property
      exact absurd same.symm appSpine_const_ne_lam

/-- The normalizer contracts a β-redex of the identity first. -/
theorem step_betaRedex {n : Nat} (a : Tm Head n) :
    (step S.R root (.app (.lam (.var 0)) a)).map Subtype.val = some a := by
  rw [ExecutableReduction.step, root_betaRedex S root a]
  rfl

/-- **A tower of `j` β-redexes is not normalized below budget `j + 1`**, in every package and with every
root evaluator. -/
theorem normalize_betaTower {n : Nat} (a : Tm Head n) :
    ∀ (j fuel : Nat), fuel ≤ j → normalize S.R root fuel (betaTower a j) = none
  | _, 0, _ => rfl
  | 0, _ + 1, le => absurd le (by omega)
  | j + 1, fuel + 1, le => by
      have rest := normalize_betaTower a j fuel (by omega)
      have stepped := step_betaRedex S root (betaTower a j)
      cases h : step S.R root (.app (.lam (.var 0)) (betaTower a j)) with
      | none => rw [h] at stepped; cases stepped
      | some next =>
          rw [h] at stepped
          obtain ⟨v, pv⟩ := next
          simp only [Option.map_some, Option.some.injEq] at stepped
          subst stepped
          show normalize S.R root (fuel + 1) (.app (.lam (.var 0)) (betaTower a j)) = none
          rw [ExecutableReduction.normalize, h]
          simp only [rest]

/-- **A tower of `j` β-redexes around a stopped term is normalized from budget `j + 1` on.** -/
theorem normalize_betaTower_some {n : Nat} (a : Tm Head n) (stopped : step S.R root a = none) :
    ∀ (j extra : Nat), (normalize S.R root (j + 1 + extra) (betaTower a j)).map Subtype.val = some a
  | 0, extra => by
      rw [show 0 + 1 + extra = extra + 1 by omega]
      show (normalize S.R root (extra + 1) a).map Subtype.val = some a
      rw [ExecutableReduction.normalize, stopped]
      rfl
  | j + 1, extra => by
      have rest := normalize_betaTower_some a stopped j extra
      have stepped := step_betaRedex S root (betaTower a j)
      rw [show j + 1 + 1 + extra = (j + 1 + extra) + 1 by omega]
      show (normalize S.R root ((j + 1 + extra) + 1) (.app (.lam (.var 0)) (betaTower a j))).map
        Subtype.val = some a
      cases h : step S.R root (.app (.lam (.var 0)) (betaTower a j)) with
      | none => rw [h] at stepped; cases stepped
      | some next =>
          rw [h] at stepped
          obtain ⟨v, pv⟩ := next
          simp only [Option.map_some, Option.some.injEq] at stepped
          subst stepped
          rw [ExecutableReduction.normalize, h]
          cases later : normalize S.R root (j + 1 + extra) (betaTower a j) with
          | none => rw [later] at rest; cases rest
          | some answer =>
              rw [later] at rest
              simp only [Option.map_some, Option.some.injEq] at rest
              simp only [later, Option.map_some, rest]

/-- A stopped term is its own answer at every positive budget. -/
theorem normalize_stopped {n : Nat} {t : Tm Head n} (stopped : step S.R root t = none) (fuel : Nat) :
    normalize S.R root (fuel + 1) t = some ⟨t, .refl⟩ := by
  rw [ExecutableReduction.normalize, stopped]

variable [DecidableEq Head] [DecidableRel S.R.headEq] [∀ head, Decidable (S.R.isUniverse head)]

/-- **At a type with `k` β-redexes the comparison does not answer at budget `k`.** -/
theorem compare_betaTower {n : Nat} (Γ : Ctx Head n) (t u X : Tm Head n) :
    ∀ k, compare S.R (normalize S.R root) k Γ t u (betaTower X k) = none
  | 0 => by rw [ExecutableConversion.compare]
  | k + 1 => by
      rw [ExecutableConversion.compare, normalize_betaTower S root X (k + 1) (k + 1) le_rfl]
      rfl

end Tower

/-! ## The comparison cannot refuse -/

section Refusal

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable [DecidableEq Head] [DecidableRel S.R.headEq] [∀ head, Decidable (S.R.isUniverse head)]

/-- **On two typed terms that are not equal the comparison returns nothing at every budget**, whatever the
reducer: a certificate is sound. So its single failure output cannot tell "not equal" from "ran out". -/
theorem compare_none_of_not_equal (q : Qualified S) (red : Reducer S.R) {n : Nat} {Γ : Ctx Head n}
    {t u A : Tm Head n} (formed : CtxFormed S.R Γ) (tt : Typed S.R Γ t A) (tu : Typed S.R Γ u A)
    (different : ¬ Equal S.R Γ t u A) (k : Nat) : compare S.R red k Γ t u A = none := by
  cases h : compare S.R red k Γ t u A with
  | none => rfl
  | some certificate =>
      exact absurd (Algorithm.sound q.facts q.roots q.heads q.algebra certificate.down formed tt tu)
        different

end Refusal

/-! ## The checker's boundary -/

section Checker

variable {Head : Type} (R : Rules Head) [DecidableEq Head] [DecidableRel R.headEq]
  [∀ head, Decidable (R.isUniverse head)] [DecidableRel R.cumulative]
  (heads : ExecutableChecking.HeadChoices R) (red : Reducer R)

/-- The checker synthesizes no pair. -/
theorem synth_pair_none {n : Nat} (Γ : Ctx Head n) (a b : Tm Head n) :
    ∀ k, ExecutableChecking.synth R heads red k Γ (.pair a b) = none
  | 0 => rfl
  | _ + 1 => by rw [ExecutableChecking.synth]

/-- The checker synthesizes no projection of a pair literal. -/
theorem synth_fst_pair_none {n : Nat} (Γ : Ctx Head n) (a b : Tm Head n) :
    ∀ k, ExecutableChecking.synth R heads red k Γ (.fst (.pair a b)) = none
  | 0 => rfl
  | k + 1 => by
      rw [ExecutableChecking.synth]
      simp only [Option.bind_eq_bind, synth_pair_none R heads red Γ a b k, Option.bind_none]

/-- **The checker accepts the projection of a pair literal at no budget and no type.** -/
theorem check_fst_pair_none {n : Nat} (Γ : Ctx Head n) (a b A : Tm Head n) :
    ∀ k, ExecutableChecking.check R heads red k Γ (.fst (.pair a b)) A = none
  | 0 => rfl
  | k + 1 => by
      rw [ExecutableChecking.check]
      all_goals first
        | simp only [Option.bind_eq_bind, synth_fst_pair_none R heads red Γ a b k, Option.bind_none]
        | (intros; contradiction)

end Checker

/-! ## The cliff in the vectors package -/

section VectorsCliff

open ProgrammingOnTheStep.IndexedFamilies.Eliminator (level1)
open Vectors (vecS vecReducer vecRoot vecChoices)

/-- The identity on small types, applied: equal to its argument at the small universe. -/
theorem idApp_typeEq {n : Nat} {Γ : Ctx Tower.Head n} {a : Tm Tower.Head n} (typed : Typed vecS.R Γ a U0) :
    Typed vecS.R Γ (.app (.lam (.var 0)) a) U0 ∧ TypeEq vecS.R Γ (.app (.lam (.var 0)) a) a := by
  have tw := TowerVectorsModel.towerLike_rules level1
  have piTyped : Typed vecS.R Γ (.pi U0 U0) (.head (.sort (.max (.succ (.const 0)) (.succ (.const 0))))) :=
    .piForm tw.u0_typed (tw.isUniverse _) tw.u0_typed (tw.isUniverse _) (tw.join _ _)
  have body : Typed vecS.R (.snoc Γ U0) (.var 0) U0 := .var 0
  have lamTyped : Typed vecS.R Γ (.lam (.var 0)) (.pi U0 U0) := .lamIntro piTyped (tw.isUniverse _) body
  exact ⟨.appElim lamTyped typed, _, tw.isUniverse (.const 0), .betaPi piTyped (tw.isUniverse _) body typed⟩

/-- The towers over `num` are small types equal to `num`. -/
theorem towerType_typeEq {n : Nat} {Γ : Ctx Tower.Head n} :
    ∀ k, Typed vecS.R Γ (betaTower numC k) U0 ∧ TypeEq vecS.R Γ numC (betaTower numC k)
  | 0 => ⟨(TowerVectorsModel.vecDeclared_rules level1).num_typed,
      IsType.refl ⟨_, (TowerVectorsModel.towerLike_rules level1).isUniverse (.const 0),
        (TowerVectorsModel.vecDeclared_rules level1).num_typed⟩⟩
  | k + 1 => by
      obtain ⟨typed, equal⟩ := towerType_typeEq (Γ := Γ) k
      obtain ⟨typed', step⟩ := idApp_typeEq typed
      exact ⟨typed', TypeEq.trans vecS.levels equal step.symm⟩

/-- **The family.** For every `k`, `zero` and `zero` are equal at `(λ x. x)ᵏ num`, and the comparison
over the tree's normalizer does not answer them at budget `k`. -/
theorem vectors_cliff (k : Nat) :
    Equal vecS.R .nil zeroC zeroC (betaTower numC k) ∧
      compare vecS.R (vecReducer level1) k .nil zeroC zeroC (betaTower numC k) = none :=
  ⟨.refl (Typed.convType (TowerVectorsModel.vecDeclared_rules level1).zero_typed (towerType_typeEq k).2),
    compare_betaTower vecS (vecRoot level1) .nil zeroC zeroC numC k⟩

/-- The closed terms `num` and `zero` are stopped. -/
theorem step_num : step vecS.R (vecRoot level1) (numC : Tm Tower.Head 0) = none :=
  Option.isNone_iff_eq_none.mp (by decide +kernel)
theorem step_zero : step vecS.R (vecRoot level1) (zeroC : Tm Tower.Head 0) = none :=
  Option.isNone_iff_eq_none.mp (by decide +kernel)

/-- **Exhausted on the family is transient, with no hypothesis**: the pair at `(λ x. x)ᵏ num` is answered
at every budget from `k + 3` on. -/
theorem vectors_cliff_transient (k : Nat) :
    ∃ certificate, ∀ larger, k + 3 ≤ larger →
      compare vecS.R (vecReducer level1) larger .nil zeroC zeroC (betaTower numC k) = some certificate := by
  have typeNormal := normalize_betaTower_some vecS (vecRoot level1) (numC : Tm Tower.Head 0) step_num k 2
  rw [show k + 1 + 2 = k + 2 + 1 by omega] at typeNormal
  cases h : normalize vecS.R (vecRoot level1) (k + 2 + 1) (betaTower numC k) with
  | none => rw [h] at typeNormal; cases typeNormal
  | some result =>
      rw [h] at typeNormal
      obtain ⟨code, path⟩ := result
      simp only [Option.map_some, Option.some.injEq] at typeNormal
      subst typeNormal
      have zeroNormal : normalize vecS.R (vecRoot level1) (k + 1 + 1) (zeroC : Tm Tower.Head 0) =
          some ⟨zeroC, .refl⟩ :=
        normalize_stopped vecS (vecRoot level1) step_zero (k + 1)
      obtain ⟨certificate, computed⟩ :=
        neutral_const vecS.R (vecReducer level1) (fuel := k) (Γ := .nil)
          (TowerVectorsModel.vecDeclared_rules level1).dZero
      obtain ⟨final, finalComputed⟩ :=
        compare_other vecS.R (vecReducer level1) (fuel := k + 2) (Γ := .nil) (left := zeroC) (right := zeroC)
          (NotFormer.const _) h
          (compareNeutral_of vecS.R (vecReducer level1) zeroNormal zeroNormal ⟨_, computed⟩)
      exact ⟨final, fun larger enough => ContextualDependentConversionBudget.compare_success_mono vecS.R
        (vecReducer level1) (normalize_stable (S := vecS) (vecRoot level1)) finalComputed (by omega)⟩

/-- **The member of the family at which budget 16, the budget of the tree's examples, fails**, evaluated
by the kernel: unanswered at 16, answered at 17. -/
theorem cliff16 :
    (compare vecS.R (vecReducer level1) 16 .nil zeroC zeroC (betaTower numC 16)).isSome = false ∧
      (compare vecS.R (vecReducer level1) 17 .nil zeroC zeroC (betaTower numC 16)).isSome = true := by
  decide +kernel

/-! ### Refusal and the checker's boundary in the vectors package -/

/-- The universes `U₀` and `U₁` are typed in `U₂`. -/
theorem u0_u1_typed :
    Typed vecS.R .nil (U0 : Tm Tower.Head 0) (.head (.sort (.succ (.succ (.const 0))))) ∧
      Typed vecS.R .nil (.head (.sort (.succ (.const 0))) : Tm Tower.Head 0)
        (.head (.sort (.succ (.succ (.const 0))))) := by
  have tw := TowerVectorsModel.towerLike_rules level1
  exact ⟨Derivable.cumul tw.u0_typed (tw.cumulative _ _ fun ν => by simp [LevelExpr.eval]),
    .headType (tw.headTyping _)⟩

/-- **`U₀` and `U₁` are not equal.** -/
theorem u0_ne_u1 :
    ¬ Equal vecS.R .nil (U0 : Tm Tower.Head 0) (.head (.sort (.succ (.const 0))))
      (.head (.sort (.succ (.succ (.const 0))))) := by
  intro e
  have tw := TowerVectorsModel.towerLike_rules level1
  have typeEq : TypeEq vecS.R .nil (U0 : Tm Tower.Head 0) (.head (.sort (.succ (.const 0)))) :=
    ⟨_, tw.isUniverse _, e⟩
  obtain ⟨h', same, headSame⟩ :=
    ((Vectors.vq level1).facts.forms typeEq .nil (.inl ⟨_, rfl⟩) (.inl ⟨_, rfl⟩)).head_left
  cases same
  revert headSame
  unfold HeadSame
  decide

/-- **No budget refuses them**: the comparison returns nothing for `U₀` and `U₁` at every budget. -/
theorem u0_u1_unanswered (k : Nat) :
    compare vecS.R (vecReducer level1) k .nil (U0 : Tm Tower.Head 0) (.head (.sort (.succ (.const 0))))
      (.head (.sort (.succ (.succ (.const 0))))) = none :=
  compare_none_of_not_equal (Vectors.vq level1) (vecReducer level1) .nil u0_u1_typed.1 u0_u1_typed.2
    u0_ne_u1 k

/-- **The first projection of a pair literal is typed.** -/
theorem fst_pair_typed : Typed vecS.R .nil (.fst (.pair zeroC zeroC) : Tm Tower.Head 0) numC := by
  have D := TowerVectorsModel.vecDeclared_rules level1
  have sigmaTyped : Typed vecS.R .nil (.sigma numC numC : Tm Tower.Head 0) U0 :=
    D.tower.sigma_small D.num_typed D.num_typed
  exact .fstElim (.pairIntro sigmaTyped (D.tower.isUniverse _) D.zero_typed D.zero_typed)

/-- **The checker never accepts it**, at any budget. -/
theorem fst_pair_never_checked (k : Nat) :
    ExecutableChecking.check vecS.R vecChoices (vecReducer level1) k .nil
      (.fst (.pair zeroC zeroC) : Tm Tower.Head 0) numC = none :=
  check_fst_pair_none vecS.R vecChoices (vecReducer level1) .nil zeroC zeroC numC k

end VectorsCliff

/-! ## A looping row: normal forms must exist -/

section Loop

/-- The name of the looping constant. -/
def loopName : DeclName := .mkSimple "loop"

/-- The tower with one small type constant `loop` and the row `loop ⟶ loop`. -/
def loopTower : Rules Tower.Head :=
  { Tower.rules with
    constantType := fun name => if name = loopName then some (.head (.sort (.const 0))) else none
    computation := loopComputation loopName }

instance loopHeadEqDecidable : DecidableRel loopTower.headEq := fun first second =>
  LevelTower.instDecidableHeadEq first second

instance loopUniverseDecidable (head : Tower.Head) : Decidable (loopTower.isUniverse head) :=
  ExecutableTowerChoices.universeDecidable head

/-- Its root evaluator fires the row. -/
def loopRoot : RootEvaluator loopTower := fun {_} t => match t with
  | .const c => if h : c = loopName then
      some ⟨.const loopName, (show (loopComputation loopName).step (.const c) (.const loopName) from
        ⟨by rw [h], rfl⟩)⟩ else none
  | _ => none

/-- **The root evaluator is complete.** -/
theorem loopRoot_complete : RootComplete loopTower loopRoot := by
  intro n t none' u step
  obtain ⟨rfl, rfl⟩ := (show t = .const loopName ∧ u = .const loopName from step)
  simp [loopRoot] at none'

/-- `loop` is a small type. -/
theorem loop_typed : Typed loopTower .nil (.const loopName) (.head (.sort (.const 0))) := by
  have declared : loopTower.constantType loopName = some (.head (.sort (.const 0))) := by
    simp [loopTower]
  exact .const declared (.headType (LevelTower.HeadTyping.sort _)) (LevelTower.IsUniverse.sort _)

/-- **Strong normalization fails**: `loop` is typed and not strongly normalizing. Weak-head
normalization and algorithmic completeness fail in the same package (`loop_cliff_fails_three`). -/
theorem loop_not_typedSN : ¬ TypedSN loopTower := fun sn =>
  not_sn_of_self_step (.root (show (loopComputation loopName).step (.const loopName) (.const loopName) from
    ⟨rfl, rfl⟩)) (sn .nil loop_typed)

/-- The normalizer never finishes on `loop`. -/
theorem loop_normalize_none : ∀ k, normalize loopTower loopRoot k (.const loopName : Tm Tower.Head 0) = none
  | 0 => rfl
  | k + 1 => by
      rw [ExecutableReduction.normalize]
      have stepped : step loopTower loopRoot (.const loopName : Tm Tower.Head 0) =
          some ⟨.const loopName, .root (show (loopComputation loopName).step (.const loopName)
            (.const loopName) from ⟨rfl, rfl⟩)⟩ := by
        rw [ExecutableReduction.step]
        simp [loopRoot]
      rw [stepped]
      simp only [loop_normalize_none k]

/-- **An equality answered at no budget**: `loop` equals itself at `U₀`, the root evaluator is complete,
and the comparison over the tree's normalizer never answers. In this package strong normalization,
weak-head normalization and algorithmic completeness all fail (`loop_cliff_fails_three`). -/
theorem loop_cliff (k : Nat) :
    Equal loopTower .nil (.const loopName) (.const loopName) (.head (.sort (.const 0))) ∧
      compare loopTower (normalize loopTower loopRoot) k .nil (.const loopName) (.const loopName)
        (.head (.sort (.const 0))) = none := by
  refine ⟨.refl loop_typed, ?_⟩
  cases k with
  | zero => rw [ExecutableConversion.compare]
  | succ k =>
      have headNormal : normalize loopTower loopRoot (k + 1) (.head (.sort (.const 0)) : Tm Tower.Head 0) =
          some ⟨.head (.sort (.const 0)), .refl⟩ := by
        rw [ExecutableReduction.normalize]
        rfl
      rw [ExecutableConversion.compare, headNormal]
      simp only [Option.bind_eq_bind, Option.bind_some]
      rw [dif_pos (show loopTower.isUniverse (.sort (.const 0)) from LevelTower.IsUniverse.sort _)]
      cases k with
      | zero => rw [ExecutableConversion.types]; rfl
      | succ j =>
          rw [ExecutableConversion.types, loop_normalize_none]
          rfl

/-! ### Weak-head normal forms do not give a full normal form -/

/-- A term that the normalizer steps to itself is never normalized. -/
theorem normalize_none_of_self_step {Head : Type} {R : Rules Head} {root : RootEvaluator R} {n : Nat}
    {t : Tm Head n} (self : (step R root t).map Subtype.val = some t) :
    ∀ k, normalize R root k t = none
  | 0 => rfl
  | k + 1 => by
      have rest := normalize_none_of_self_step self k
      cases h : step R root t with
      | none => rw [h] at self; cases self
      | some next =>
          rw [h] at self
          obtain ⟨v, pv⟩ := next
          simp only [Option.map_some, Option.some.injEq] at self
          subst self
          rw [ExecutableReduction.normalize, h]
          simp only [rest]

/-- The roles of the looping package: `loop` computes at arity zero. -/
def loopRoles : Roles Tower.Head := fun name => if name = loopName then .computes 0 .leaf else .rigid

/-- The looping package's root steps occur at `loop`, of arity zero, and are deterministic. -/
theorem loopShape : RootShape loopTower loopRoles where
  spine := by
    intro n t u step
    obtain ⟨rfl, rfl⟩ := (show t = .const loopName ∧ u = .const loopName from step)
    exact ⟨loopName, 0, .leaf, [], by simp [loopRoles], rfl, rfl, .leaf []⟩
  deterministic := by
    intro n t u u' first second
    obtain ⟨_, rfl⟩ := (show t = .const loopName ∧ u = .const loopName from first)
    obtain ⟨_, rfl⟩ := (show t = .const loopName ∧ u' = .const loopName from second)
    rfl

/-- `λ x. loop`. -/
abbrev loopLam : Tm Tower.Head 0 := .lam (.const loopName)

/-- **`λ x. loop` is typed and weak-head normal, and the full normalizer never finishes on it**: a typed
weak-head normal form need not have a full normal form (this one has none, since its body has
none). -/
theorem loopLam_whnf_unnormalized :
    Typed loopTower .nil loopLam (.pi (.head (.sort (.const 0))) (.head (.sort (.const 0)))) ∧
      Whnf loopTower loopRoles loopLam ∧ ∀ k, normalize loopTower loopRoot k loopLam = none := by
  have declared : loopTower.constantType loopName = some (.head (.sort (.const 0))) := by
    simp [loopTower]
  have small : ∀ {m : Nat} {Γ : Ctx Tower.Head m},
      Typed loopTower Γ (.head (.sort (.const 0))) (.head (.sort (.succ (.const 0)))) :=
    .headType (LevelTower.HeadTyping.sort _)
  have piTyped : Typed loopTower .nil (.pi (.head (.sort (.const 0))) (.head (.sort (.const 0))))
      (.head (.sort (.max (.succ (.const 0)) (.succ (.const 0))))) :=
    .piForm small (LevelTower.IsUniverse.sort _) small (LevelTower.IsUniverse.sort _)
      (LevelTower.Join.sorts _ _)
  have body : Typed loopTower (.snoc .nil (.head (.sort (.const 0)))) (.const loopName)
      (.head (.sort (.const 0))) :=
    .const declared (.headType (LevelTower.HeadTyping.sort _)) (LevelTower.IsUniverse.sort _)
  have stepped : (step loopTower loopRoot loopLam).map Subtype.val = some loopLam := by
    rw [ExecutableReduction.step]
    simp [loopRoot, ExecutableReduction.step]
  exact ⟨.lamIntro piTyped (LevelTower.IsUniverse.sort _) body, lam_whnf loopShape _,
    normalize_none_of_self_step stepped⟩

/-! ### Three hypotheses fail together -/

/-- One step from `loop` goes to `loop`. -/
theorem step_from_loop {n : Nat} {u : Tm Tower.Head n}
    (step : StepCore loopTower.computation loopTower.headEq (.const loopName) u) :
    u = .const loopName := by
  cases step with
  | root h => exact (show (loopComputation loopName).step (.const loopName) u from h).2

/-- **Every reduct of `loop` is `loop`.** -/
theorem reducts_of_loop {n : Nat} {u : Tm Tower.Head n}
    (reduces : Relation.ReflTransGen (StepCore loopTower.computation loopTower.headEq)
      (.const loopName) u) : u = .const loopName := by
  induction reduces with
  | refl => rfl
  | tail _ step ih =>
      subst ih
      exact step_from_loop step

/-- **`loop` is weak-head normal under no roles**: its row is a weak-head step whatever the roles. -/
theorem loop_not_whnf (roles : Roles Tower.Head) {n : Nat} :
    ¬ Whnf loopTower roles (.const loopName : Tm Tower.Head n) := fun normal =>
  normal (.const loopName)
    (.root (show (loopComputation loopName).step (.const loopName) (.const loopName) from ⟨rfl, rfl⟩))

/-- **No reduct of `loop` is weak-head normal**, under any roles: whatever a reducer returns for
`loop`, at whatever budget, is not a weak-head normal form. -/
theorem loop_no_whnf_reduct (roles : Roles Tower.Head)
    (r : Result loopTower (.const loopName : Tm Tower.Head 0)) : ¬ Whnf loopTower roles r.val := by
  rw [reducts_of_loop r.property]
  exact loop_not_whnf roles

/-- **No reducer meets the reducer hypothesis `WhnfEventually` of `compare_eventually`**, over every
setting whose rules are the looping package. -/
theorem loop_not_whnfEventually {L : Type} [LevelOrder L] (S : Setting Tower.Head L)
    (rules : S.R = loopTower) (red : Reducer S.R) : ¬ WhnfEventually S red := by
  obtain ⟨R, roles, E, levels, shape, constructors⟩ := S
  change R = loopTower at rules
  subst rules
  intro eventually
  obtain ⟨_, result, normal, -⟩ := eventually CtxFormed.nil loop_typed
  exact loop_no_whnf_reduct roles result normal

/-- The tower's level model, read for the looping package, which keeps the tower's heads. -/
def loopLevels : LevelModel loopTower ℕ where
  level := (TowerModel.levels (fun _ => 0)).level
  successor := (TowerModel.levels (fun _ => 0)).successor
  universe_typing := (TowerModel.levels (fun _ => 0)).universe_typing
  ground_typing := (TowerModel.levels (fun _ => 0)).ground_typing
  cumulative_universe := (TowerModel.levels (fun _ => 0)).cumulative_universe
  headEq_level := (TowerModel.levels (fun _ => 0)).headEq_level
  join_level := (TowerModel.levels (fun _ => 0)).join_level
  join_exists := (TowerModel.levels (fun _ => 0)).join_exists
  join_upper := (TowerModel.levels (fun _ => 0)).join_upper
  cumulative_refl := (TowerModel.levels (fun _ => 0)).cumulative_refl
  headEq_symm := (TowerModel.levels (fun _ => 0)).headEq_symm
  headEq_trans := (TowerModel.levels (fun _ => 0)).headEq_trans
  universe_decided := (TowerModel.levels (fun _ => 0)).universe_decided

/-- The looping roles declare no inductive type, so their constructors are declared vacuously. -/
theorem loopConstructors : ConstructorsDeclared loopRoles where
  arity := by
    intro T _ _ _ role _
    simp only [loopRoles] at role
    split at role <;> cases role
  distinct := by
    intro T _ role
    simp only [loopRoles] at role
    split at role <;> cases role

/-- **The normalization setting of the looping package**, with its own roles and shape. -/
def loopSetting : Setting Tower.Head ℕ where
  R := loopTower
  roles := loopRoles
  E := declarative loopTower
  levels := loopLevels
  shape := loopShape
  constructors := loopConstructors

/-- Its declarative equality has the laws the model asks for. -/
theorem loopSetting_laws : loopSetting.E.Laws loopSetting.R loopSetting.roles :=
  declarative_laws loopRoles loopLevels

/-- **No reducer meets `WhnfEventually` over the looping setting.** -/
theorem loopSetting_not_whnfEventually (red : Reducer loopSetting.R) :
    ¬ WhnfEventually loopSetting red :=
  loop_not_whnfEventually loopSetting rfl red

/-- A spine of a constant that is the constant `loop` is `loop` alone. -/
theorem appSpine_const_eq_loop {n : Nat} {c : DeclName} {args : List (Tm Tower.Head n)}
    (same : appSpine (.const c) args = .const loopName) : c = loopName := by
  rcases appSpine_const_cases c args with spine | ⟨f, a, spine⟩
  · rw [spine] at same
    exact Tm.const.inj same
  · rw [spine] at same
    cases same

/-- The looping roles: `loop` computes at arity zero with the leaf skeleton. -/
theorem loopRoles_loop : loopRoles loopName = .computes 0 .leaf := by
  simp [loopRoles]

/-- Every other name is rigid. -/
theorem loopRoles_other {c : DeclName} (other : c ≠ loopName) : loopRoles c = .rigid := by
  simp [loopRoles, other]

/-- A leaf skeleton focuses on nothing. -/
theorem loop_no_focus_leaf {n : Nat} {args args' : List (Tm Tower.Head n)} {kind : Inspection}
    {a a' : Tm Tower.Head n} : ¬ InspectTree.Focus loopRoles .leaf args args' kind a a' := by
  intro focus
  cases focus

/-- A computing name of the looping roles is `loop`, with the leaf skeleton. -/
theorem loopRoles_computes {c : DeclName} {arity : Nat} {inspect : InspectTree}
    (role : loopRoles c = .computes arity inspect) : c = loopName ∧ inspect = .leaf := by
  by_cases same : c = loopName
  · subst same
    rw [loopRoles_loop] at role
    cases role
    exact ⟨rfl, rfl⟩
  · rw [loopRoles_other same] at role
    cases role

/-- **`loop` is not neutral** under the looping roles. -/
theorem loop_not_neutral {n : Nat} {t : Tm Tower.Head n} (neutral : Neutral loopRoles t) :
    t ≠ .const loopName := by
  cases neutral with
  | var i => exact fun e => by cases e
  | app _ => exact fun e => by cases e
  | fst _ => exact fun e => by cases e
  | snd _ => exact fun e => by cases e
  | rigid args role =>
      intro same
      rw [appSpine_const_eq_loop same, loopRoles_loop] at role
      cases role
  | stuck role _ focus _ _ =>
      intro _
      obtain ⟨-, rfl⟩ := loopRoles_computes role
      exact loop_no_focus_leaf focus

/-- **A weak-head step from `loop` goes to `loop`.** -/
theorem whStep_from_loop {n : Nat} {t u : Tm Tower.Head n} (step : WhStep loopTower loopRoles t u)
    (source : t = .const loopName) : u = .const loopName := by
  cases step with
  | beta _ _ => exact absurd source (fun e => by cases e)
  | fstPair _ _ => exact absurd source (fun e => by cases e)
  | sndPair _ _ => exact absurd source (fun e => by cases e)
  | root h => exact (show (loopComputation loopName).step t u from h).2
  | appFun _ => exact absurd source (fun e => by cases e)
  | fst _ => exact absurd source (fun e => by cases e)
  | snd _ => exact absurd source (fun e => by cases e)
  | scrutinee role _ focus _ =>
      obtain ⟨-, rfl⟩ := loopRoles_computes role
      exact absurd focus loop_no_focus_leaf

/-- **No weak-head step of the looping package leaves a universe head.** -/
theorem loop_no_whStep_head {n : Nat} {t u : Tm Tower.Head n} (step : WhStep loopTower loopRoles t u)
    (h : Tower.Head) : t ≠ .head h := by
  cases step with
  | beta _ _ => exact fun e => by cases e
  | fstPair _ _ => exact fun e => by cases e
  | sndPair _ _ => exact fun e => by cases e
  | root r =>
      intro same
      have e := (show (loopComputation loopName).step t u from r).1
      rw [same] at e
      cases e
  | appFun _ => exact fun e => by cases e
  | fst _ => exact fun e => by cases e
  | snd _ => exact fun e => by cases e
  | scrutinee _ _ _ _ => exact appSpine_const_ne_head

theorem whRed_from_loop {n : Nat} {u : Tm Tower.Head n}
    (red : WhRed loopTower loopRoles (.const loopName) u) : u = .const loopName := by
  induction red with
  | refl => rfl
  | tail _ step ih => exact whStep_from_loop step ih

theorem loop_whRed_from_head {n : Nat} {h : Tower.Head} {u : Tm Tower.Head n}
    (red : WhRed loopTower loopRoles (.head h) u) : u = .head h := by
  induction red with
  | refl => rfl
  | tail _ step ih => exact absurd ih (loop_no_whStep_head step h)

/-- The universe `U₀` is not a spine type of the looping package. -/
theorem loop_not_spineType_u0 {n : Nat} :
    ¬ SpineType loopTower loopRoles (.head (.sort (.const 0)) : Tm Tower.Head n) := by
  rintro (⟨C, a, b, e⟩ | neutral | ⟨T, ctors, _, e⟩ | ⟨h, e, notUniverse⟩)
  · cases e
  · exact neutral.not_former.1 _ rfl
  · cases e
  · cases e
    exact notUniverse (LevelTower.IsUniverse.sort _)

/-- **`loop = loop : U₀` holds and has no algorithmic derivation**, so the algorithmic equality of the
looping package is not complete under its own roles. -/
theorem loop_not_algorithmicComplete : ¬ AlgorithmicComplete loopTower loopRoles := by
  intro complete
  have equal : Equal loopTower .nil (.const loopName) (.const loopName) (.head (.sort (.const 0))) :=
    .refl loop_typed
  have derivation := complete CtxFormed.nil equal
  cases derivation with
  | terms redA _ redT redU rest =>
      have hA := loop_whRed_from_head redA.red
      have hT := whRed_from_loop redT.red
      have hU := whRed_from_loop redU.red
      subst hA hT hU
      cases rest with
      | univ _ _ _ types =>
          cases types with
          | inductiveType role _ =>
              rw [loopRoles_loop] at role
              cases role
          | neutralTypes neutral _ _ _ => exact loop_not_neutral neutral rfl
      | spine spineType _ _ _ _ _ => exact loop_not_spineType_u0 spineType

/-- **In the looping setting three hypotheses of the general theorems fail together**: strong
normalization of typed terms, weak-head normalization for every reducer, and completeness of the
algorithmic equality. The looping row therefore shows that normal forms must exist; it does not
separate strong normalization from weaker hypotheses. -/
theorem loop_cliff_fails_three :
    ¬ TypedSN loopSetting.R ∧ (∀ red : Reducer loopSetting.R, ¬ WhnfEventually loopSetting red) ∧
      ¬ AlgorithmicComplete loopSetting.R loopSetting.roles :=
  ⟨loop_not_typedSN, loopSetting_not_whnfEventually, loop_not_algorithmicComplete⟩

end Loop

end NativeTypesOnTheStep.Computing.Eventually

section Audit
open NativeTypesOnTheStep.Computing.Eventually
#print axioms root_betaRedex
#print axioms normalize_betaTower
#print axioms normalize_betaTower_some
#print axioms compare_betaTower
#print axioms compare_none_of_not_equal
#print axioms check_fst_pair_none
#print axioms towerType_typeEq
#print axioms vectors_cliff
#print axioms vectors_cliff_transient
#print axioms cliff16
#print axioms u0_ne_u1
#print axioms u0_u1_unanswered
#print axioms fst_pair_typed
#print axioms fst_pair_never_checked
#print axioms loopRoot_complete
#print axioms loop_typed
#print axioms loop_not_typedSN
#print axioms loop_normalize_none
#print axioms loop_cliff
#print axioms normalize_none_of_self_step
#print axioms loopShape
#print axioms loopLam_whnf_unnormalized
#print axioms reducts_of_loop
#print axioms loop_no_whnf_reduct
#print axioms loop_not_whnfEventually
#print axioms loopSetting_laws
#print axioms loopSetting_not_whnfEventually
#print axioms loop_not_neutral
#print axioms loop_not_spineType_u0
#print axioms loop_not_algorithmicComplete
#print axioms loop_cliff_fails_three
end Audit

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
