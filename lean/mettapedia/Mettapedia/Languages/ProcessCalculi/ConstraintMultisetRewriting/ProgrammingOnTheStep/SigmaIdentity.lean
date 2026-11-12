import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFullControls

/-!
# Dependent pairs and identity types, on the dependent full step

Programs over the cumulative tower, run by `Interface.DependentFull.step`.

**A dependent pair, taken apart by matching** (`pair_admitted`). Over `A : U0, a : A`, the row
`pair a (refl a) : Σ (x : A). Id A x a` is taken by the pattern `pair y q`, whose telescope
`y : A, q : Id A y a` is dependent; the made row is `q : Id A y a`. The solution sets `y ↦ a`,
`q ↦ refl a`.

**Matching `refl` against a proof identifies its endpoints** (`refl_match_admitted`,
`refl_match_identifies`). Over `A : U0, a b : A, p : Id A a b`, reading the row `p` with the pattern
`refl z` (`z : A` fresh) is admitted: the information `(refl z : Id A z z) ≐ (p : Id A a b)` is
solved by identifying `a` and `b`. At every solution of it, `a` and `b` are equal. This is matching
on the identity type by unification; the learned `a ≐ b` lives in the knowledge, not in the frame.

**An empty identity type** (`empty_uninhabited`, `absurd_match_refused`). `Id U0 Ground (Ground →
Ground)` is a formed type with no closed inhabitant. The frame `p : Id U0 Ground (Ground → Ground)`
is a state of the step (its empty knowledge is solvable), and matching `refl z` against `p` is
refused, since it would equate `Ground` with `Ground → Ground`: the absurd case is refuted by the
unifier, not by a coverage check.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ProgrammingOnTheStep.SigmaIdentity

open _root_.CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open Interface.DependentFull Interface.DependentFull.Controls

/-- `U0`, as a head. -/
abbrev small : Tower.Head := .sort Tower.zero

/-! ## A dependent pair taken apart -/

/-- `a : A`, over `A : U0`. -/
def aType : TypeOver base := xType

/-- The frame `A : U0, a : A`. -/
abbrev pairBase : Context Tower.rules := extend base aType

/-- `Σ (x : A). Id A x a`, over `A : U0, a : A`. -/
def sigmaCode {n : Nat} (A a : Tower.Tm n) : Tower.Tm n :=
  .sigma A (.id (Presentation.rename wk A) (.var 0) (Presentation.rename wk a))

theorem sigma_formed : Typed Tower.rules pairBase.raw (sigmaCode (.var 1) (.var 0)) (.head small) := by
  have A : Typed Tower.rules pairBase.raw (.var 1) (.head small) := Derivable.var (1 : Fin 2)
  have inner : Typed Tower.rules (.snoc pairBase.raw (.var 1)) (.id (.var 2) (.var 0) (.var 1)) (.head small) :=
    .idForm (Derivable.var (2 : Fin 3)) (.sort _) (Derivable.var (0 : Fin 3)) (Derivable.var (1 : Fin 3))
  have collapse : Tower.rules.cumulative (.sort (.max Tower.zero Tower.zero)) small := by
    change LevelTower.Cumulative (.sort (.max Tower.zero Tower.zero)) (.sort Tower.zero)
    intro valuation
    simp [LevelExpr.eval]
  exact .cumul (.sigmaForm A (.sort _) inner (.sort _) (.sorts _ _)) collapse

theorem pair_typed :
    Typed Tower.rules pairBase.raw (.pair (.var 0) (.refl (.var 0))) (sigmaCode (.var 1) (.var 0)) := by
  have reflTyped : Typed Tower.rules pairBase.raw (.refl (.var 0)) (.id (.var 1) (.var 0) (.var 0)) :=
    .reflIntro (Derivable.var (0 : Fin 2))
  exact .pairIntro sigma_formed (.sort _) (Derivable.var (0 : Fin 2)) reflTyped

/-- The row `pair a (refl a) : Σ (x : A). Id A x a`. -/
def pairRow : TotalTerm pairBase :=
  ⟨⟨sigmaCode (.var 1) (.var 0), small, .sort _, sigma_formed⟩, ⟨.pair (.var 0) (.refl (.var 0)), pair_typed⟩⟩

def pairState : State Tower.rules Nat := ⟨pairBase, [], {0}, fun _ => pairRow⟩

/-- `y : A`, over `A : U0, a : A`. -/
def yType : TypeOver pairBase := ⟨.var 1, small, .sort _, Derivable.var (1 : Fin 2)⟩

abbrev withY : Context Tower.rules := extend pairBase yType

/-- `q : Id A y a`, over `A : U0, a : A, y : A`: a helper whose type depends on the helper before it. -/
def qType : TypeOver withY :=
  ⟨.id (.var 2) (.var 0) (.var 1), small, .sort _,
    .idForm (Derivable.var (2 : Fin 3)) (.sort _) (Derivable.var (0 : Fin 3)) (Derivable.var (1 : Fin 3))⟩

abbrev withYQ : Context Tower.rules := extend withY qType

theorem pairPattern_typed :
    Typed Tower.rules withYQ.raw (.pair (.var 1) (.var 0)) (sigmaCode (.var 3) (.var 2)) := by
  have formed : Typed Tower.rules withYQ.raw (sigmaCode (.var 3) (.var 2)) (.head small) := by
    have collapse : Tower.rules.cumulative (.sort (.max Tower.zero Tower.zero)) small := by
      change LevelTower.Cumulative (.sort (.max Tower.zero Tower.zero)) (.sort Tower.zero)
      intro valuation
      simp [LevelExpr.eval]
    exact .cumul (.sigmaForm (Derivable.var (3 : Fin 4)) (.sort _)
      (.idForm (Derivable.var (4 : Fin 5)) (.sort _) (Derivable.var (0 : Fin 5)) (Derivable.var (3 : Fin 5)))
      (.sort _) (.sorts _ _)) collapse
  have second : Typed Tower.rules withYQ.raw (.var 0) (.id (.var 3) (.var 1) (.var 2)) := Derivable.var (0 : Fin 4)
  exact .pairIntro formed (.sort _) (Derivable.var (1 : Fin 4)) second

/-- The pattern `pair y q : Σ (x : A). Id A x a`. -/
def pairPattern : TotalTerm withYQ :=
  ⟨⟨sigmaCode (.var 3) (.var 2), small, .sort _, by
      have collapse : Tower.rules.cumulative (.sort (.max Tower.zero Tower.zero)) small := by
        change LevelTower.Cumulative (.sort (.max Tower.zero Tower.zero)) (.sort Tower.zero)
        intro valuation
        simp [LevelExpr.eval]
      exact .cumul (.sigmaForm (Derivable.var (3 : Fin 4)) (.sort _)
        (.idForm (Derivable.var (4 : Fin 5)) (.sort _) (Derivable.var (0 : Fin 5)) (Derivable.var (3 : Fin 5)))
        (.sort _) (.sorts _ _)) collapse⟩,
    ⟨.pair (.var 1) (.var 0), pairPattern_typed⟩⟩

/-- `Id A y a`, as the made row's type over the rule's frame. -/
def qRowType : TypeOver withYQ :=
  ⟨.id (.var 3) (.var 1) (.var 2), small, .sort _,
    .idForm (Derivable.var (3 : Fin 4)) (.sort _) (Derivable.var (1 : Fin 4)) (Derivable.var (2 : Fin 4))⟩

/-- **Take the pair apart**: take row `0` with `pair y q`, make row `1 : q : Id A y a`. -/
def pairFiring : Firing setting.levels pairState where
  helpers := .cons yType (.cons qType (.nil _))
  taken := [0]
  read := []
  takes := [pairPattern]
  reads := []
  makes := [(1, ⟨qRowType, (.var 0 : Tower.Tm 4)⟩)]
  tells := []
  guards := []
  queries := []

/-- The solution `y ↦ a, q ↦ refl a`, over `A : U0, a : A`. -/
def pairSolution : pairBase ⟶ withYQ :=
  pair (pair (𝟙 pairBase) ⟨.var 0, Derivable.var (0 : Fin 2)⟩) ⟨.refl (.var 0), .reflIntro (Derivable.var (0 : Fin 2))⟩

theorem pairFiring_information : pairFiring.information = [(pairPattern, pairFiring.row 0)] := rfl

theorem pair_identifies : pairPattern.reindex pairSolution = (pairFiring.row 0).reindex pairSolution :=
  totalTerm_ext (TypeOver.ext rfl rfl) rfl

/-- **The dependent pair is taken apart by matching.** -/
theorem pair_admitted : (step setting.levels Nat).Admits pairFiring := by
  refine ⟨⟨List.nodup_singleton _, List.nodup_singleton _, rfl, rfl, fun m member => ?_⟩,
    (enabled_iff pairFiring).mpr ⟨fun o member => ?_, fun _ member => absurd member List.not_mem_nil,
      fun _ _ readToo => absurd readToo List.not_mem_nil, fun o member inside => ?_⟩,
    ⟨pairBase, pairSolution, ?_⟩, ?_⟩
  · obtain rfl := List.mem_singleton.mp member
    exact Derivable.var (0 : Fin 4)
  · obtain rfl := List.mem_singleton.mp member
    exact Finset.mem_singleton_self 0
  · obtain rfl := List.mem_singleton.mp member
    exact absurd (Finset.mem_singleton.mp inside) (by decide)
  · rw [pairFiring_information]
    intro e member
    obtain rfl := List.mem_singleton.mp member
    show (frames setting.levels).E (pairPattern.reindex pairSolution) ((pairFiring.row 0).reindex pairSolution)
    rw [pair_identifies]
    exact ((frames setting.levels).equivalence _).refl _
  · intro b τ _
    exact ⟨fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil⟩

/-- At the solution, the made row `q` reads as `refl a`. -/
theorem pair_answer : subst pairSolution.substitution (.var 0 : Tower.Tm 4) = .refl (.var 0) := rfl

/-! ## Matching `refl` against a proof -/

/-- `b : A`, over `A : U0, a : A`. -/
def bType : TypeOver pairBase := yType

abbrev withB : Context Tower.rules := extend pairBase bType

/-- `p : Id A a b`, over `A : U0, a : A, b : A`. -/
def pType : TypeOver withB :=
  ⟨.id (.var 2) (.var 1) (.var 0), small, .sort _,
    .idForm (Derivable.var (2 : Fin 3)) (.sort _) (Derivable.var (1 : Fin 3)) (Derivable.var (0 : Fin 3))⟩

/-- The frame `A : U0, a : A, b : A, p : Id A a b`. -/
abbrev idFrame : Context Tower.rules := extend withB pType

/-- The row `p : Id A a b`. -/
def pRow : TotalTerm idFrame :=
  ⟨⟨.id (.var 3) (.var 2) (.var 1), small, .sort _,
      .idForm (Derivable.var (3 : Fin 4)) (.sort _) (Derivable.var (2 : Fin 4)) (Derivable.var (1 : Fin 4))⟩,
    ⟨.var 0, Derivable.var (0 : Fin 4)⟩⟩

def idState : State Tower.rules Nat := ⟨idFrame, [], {0}, fun _ => pRow⟩

/-- `z : A`, over the identity frame. -/
def zType : TypeOver idFrame := ⟨.var 3, small, .sort _, Derivable.var (3 : Fin 4)⟩

abbrev withZ : Context Tower.rules := extend idFrame zType

/-- The pattern `refl z : Id A z z`. -/
def reflPattern : TotalTerm withZ :=
  ⟨⟨.id (.var 4) (.var 0) (.var 0), small, .sort _,
      .idForm (Derivable.var (4 : Fin 5)) (.sort _) (Derivable.var (0 : Fin 5)) (Derivable.var (0 : Fin 5))⟩,
    ⟨.refl (.var 0), .reflIntro (Derivable.var (0 : Fin 5))⟩⟩

/-- **Read the proof `p` with the pattern `refl z`.** -/
def reflFiring : Firing setting.levels idState where
  helpers := .cons zType (.nil _)
  taken := []
  read := [0]
  takes := []
  reads := [reflPattern]
  makes := []
  tells := []
  guards := []
  queries := []

theorem reflFiring_information : reflFiring.information = [(reflPattern, reflFiring.row 0)] := rfl

/-- The solution `b ↦ a, p ↦ refl a, z ↦ a`, over `A : U0, a : A`. -/
def reflSolution : pairBase ⟶ withZ :=
  pair (pair (pair (𝟙 pairBase) ⟨.var 0, Derivable.var (0 : Fin 2)⟩)
    ⟨.refl (.var 0), .reflIntro (Derivable.var (0 : Fin 2))⟩) ⟨.var 0, Derivable.var (0 : Fin 2)⟩

theorem refl_identifies : reflPattern.reindex reflSolution = (reflFiring.row 0).reindex reflSolution :=
  totalTerm_ext (TypeOver.ext rfl rfl) rfl

/-- **Matching `refl` against `p` is admitted.** -/
theorem refl_match_admitted : (step setting.levels Nat).Admits reflFiring := by
  refine ⟨⟨List.nodup_nil, List.nodup_nil, rfl, rfl, fun _ member => absurd member List.not_mem_nil⟩,
    (enabled_iff reflFiring).mpr ⟨fun _ member => absurd member List.not_mem_nil, fun o member => ?_,
      fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil⟩,
    ⟨pairBase, reflSolution, ?_⟩, ?_⟩
  · obtain rfl := List.mem_singleton.mp member
    exact Finset.mem_singleton_self 0
  · rw [reflFiring_information]
    intro e member
    obtain rfl := List.mem_singleton.mp member
    show (frames setting.levels).E (reflPattern.reindex reflSolution) ((reflFiring.row 0).reindex reflSolution)
    rw [refl_identifies]
    exact ((frames setting.levels).equivalence _).refl _
  · intro b τ _
    exact ⟨fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil⟩

/-- **At every solution of the match, the endpoints `a` and `b` are equal.** -/
theorem refl_match_identifies {Θ : Context Tower.rules} (τ : Θ ⟶ withZ)
    (solved : (frames setting.levels).Models τ reflFiring.information) :
    Equal Tower.rules Θ.raw (subst τ.substitution (.var 3)) (subst τ.substitution (.var 2))
      (subst τ.substitution (.var 4)) := by
  rw [reflFiring_information] at solved
  obtain ⟨types, -⟩ := (equivalent_iff setting.levels _ _).mp (solved _ (List.mem_singleton_self _))
  obtain ⟨-, toA, toB⟩ := TypeEq.id_injective (TowerModel.facts (L := Nat)) types Θ.formed
  exact .trans (.symm toA) toB

/-! ## An empty identity type -/

/-- `Id U0 Ground (Ground → Ground)`. -/
def emptyId {n : Nat} : Tower.Tm n := .id (.head small) ground arrow

theorem emptyId_formed {n : Nat} (Γ : Tower.Ctx n) :
    Typed Tower.rules Γ emptyId (.head (.sort (.succ Tower.zero))) :=
  .idForm (.headType (.sort _)) (.sort _) (ground_typed Γ) (arrow_typed Γ)

/-- **`Id U0 Ground (Ground → Ground)` has no closed inhabitant**: an η-long closed normal form of it
would be `refl t` with `t` equal to both `Ground` and `Ground → Ground`. -/
theorem empty_uninhabited {t : Tower.Tm 0} : ¬ Typed Tower.rules .nil t emptyId := by
  intro typed
  obtain ⟨v, lv, _⟩ := ContextualDependentEtaLong.long_exists (S := ContextualDependentEtaLong.Controls.setting)
    TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentEtaLong.Controls.rigid TowerModel.complete .nil typed
  cases lv with
  | univ _ e _ _ => exact TypeEq.id_ne_head TowerModel.facts .nil e
  | lam e _ _ _ => exact TypeEq.pi_ne_id TowerModel.facts .nil e.symm
  | pair e _ _ _ => exact TypeEq.sigma_ne_id TowerModel.facts .nil e.symm
  | refl _ typedRefl _ =>
      obtain ⟨A, _, le⟩ := (Typed.generation typedRefl :
        ∃ A, Typed Tower.rules .nil _ A ∧ TypeLe Tower.rules .nil (.id A _ _) emptyId)
      have same := TypeLe.id_eq (S := ContextualDependentEtaLong.Controls.setting) TowerModel.facts le
        ⟨_, .sort _, emptyId_formed _⟩ .nil
      obtain ⟨⟨u, hu, sameA⟩, toGround, toArrow⟩ := TypeEq.id_injective TowerModel.facts same .nil
      exact ground_arrow_clash .nil ⟨small, .sort _, .convEq (.trans (.symm toGround) toArrow) sameA hu⟩
  | neutral ls _ _ _ => exact ContextualDependentClosedBoundary.Controls.closedSpine ls

/-- The frame `p : Id U0 Ground (Ground → Ground)`. -/
abbrev absurdFrame : Context Tower.rules :=
  extend (empty Tower.rules) ⟨emptyId, .sort (.succ Tower.zero), .sort _, emptyId_formed _⟩

/-- **The frame has no closed point**: no closed substitution reaches it. -/
theorem absurdFrame_no_closed_point : ¬ Nonempty (empty Tower.rules ⟶ absurdFrame) :=
  fun ⟨σ⟩ => empty_uninhabited (σ.typed (0 : Fin 1))

/-- The row `p`. -/
def absurdRow : TotalTerm absurdFrame :=
  ⟨⟨emptyId, .sort (.succ Tower.zero), .sort _, emptyId_formed _⟩, ⟨.var 0, Derivable.var (0 : Fin 1)⟩⟩

def absurdState : State Tower.rules Nat := ⟨absurdFrame, [], {0}, fun _ => absurdRow⟩

/-- `z : U0`, over the absurd frame. -/
def zUniverse : TypeOver absurdFrame := smallUniverse _

/-- The pattern `refl z : Id U0 z z`. -/
def absurdPattern : TotalTerm (extend absurdFrame zUniverse) :=
  ⟨⟨.id (.head small) (.var 0) (.var 0), .sort (.succ Tower.zero), .sort _,
      .idForm (.headType (.sort _)) (.sort _) (Derivable.var (0 : Fin 2)) (Derivable.var (0 : Fin 2))⟩,
    ⟨.refl (.var 0), .reflIntro (Derivable.var (0 : Fin 2))⟩⟩

/-- **Read `p` with `refl z`.** -/
def absurdFiring : Firing setting.levels absurdState where
  helpers := .cons zUniverse (.nil _)
  taken := []
  read := [0]
  takes := []
  reads := [absurdPattern]
  makes := []
  tells := []
  guards := []
  queries := []

theorem absurdFiring_information : absurdFiring.information = [(absurdPattern, absurdFiring.row 0)] := rfl

/-- **The absurd match is refused**: a solution would equate `Ground` with `Ground → Ground`. -/
theorem absurd_match_refused : ¬ (step setting.levels Nat).Admits absurdFiring := by
  rintro ⟨-, -, ⟨Δ, σ, solved⟩, -⟩
  rw [absurdFiring_information] at solved
  obtain ⟨types, -⟩ := (equivalent_iff setting.levels _ _).mp (solved _ (List.mem_singleton_self _))
  obtain ⟨-, toGround, toArrow⟩ := TypeEq.id_injective (TowerModel.facts (L := Nat)) types Δ.formed
  exact ground_arrow_clash Δ.formed ⟨small, .sort _, .trans (.symm toGround) toArrow⟩

/-- **Yet the absurd state is a state of the step**: its knowledge, empty, is solvable. -/
theorem absurdState_solvable : (frames setting.levels).Solvable absurdState.knowledge :=
  ⟨absurdFrame, 𝟙 _, Frames.models_nil _⟩

end ProgrammingOnTheStep.SigmaIdentity

#print axioms ProgrammingOnTheStep.SigmaIdentity.pair_admitted
#print axioms ProgrammingOnTheStep.SigmaIdentity.pair_answer
#print axioms ProgrammingOnTheStep.SigmaIdentity.refl_match_admitted
#print axioms ProgrammingOnTheStep.SigmaIdentity.refl_match_identifies
#print axioms ProgrammingOnTheStep.SigmaIdentity.empty_uninhabited
#print axioms ProgrammingOnTheStep.SigmaIdentity.absurdFrame_no_closed_point
#print axioms ProgrammingOnTheStep.SigmaIdentity.absurd_match_refused
#print axioms ProgrammingOnTheStep.SigmaIdentity.absurdState_solvable

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
