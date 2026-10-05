import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.MegalodonHOTG.Sets
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerInterpretation.CandidateSoundness
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerDecidability
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.MegalodonHOTG.SetsModel
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.ReductionValues
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.ConstantFamilies

/-!
# The tower inside the sets has the metatheory of the tower

The rules of the tower inside the sets (`MegalodonHOTG`) are the rules of the tower over the
levels of `L` followed by the natural numbers. The theorems of the tower are stated over an
arbitrary level order, so they hold of it as they stand. This file states them for it:

* every term typed in a formed context is strongly normalizing (`sn`);
* the equality of two terms of a type, and of two types, is decided (`equal_decide`,
  `typeEq_decide`);
* every derivation of the judgment that writes abstractions without their domains is the
  erasure of an annotated derivation (`lifts`, `elaborates`);
* no closed term has the type `Π (X : U₀). X`, relative to cofinally many inaccessible
  cardinals in one universe (`bare_consistent`);
* every step of a typed annotated term, at any position, is an equality at its type
  (`reduces_equal`), and the term keeps its set value along every reduction, in the reading
  of the type of all sets as all the sets of the lower universe (`reduction_keeps_value`).

The last statement reads the type of all sets as one more least closed universe. That reading
does not serve the constants of set theory, whose universe operation needs the set of all
sets to be closed under it (`MegalodonHOTG.SetsModel`, `MegalodonHOTG.SetTheory`).

**Declared constants with no equation** (`withConstants`). Every package over the rules of
the tower has the tower's universe laws (`packageLevels`, `packageAlgebra`,
`packageHeadReading`), and its head equality preserves typing (`package_headPreserving`). A
family of declared constants with no equation has no declared step, so its type formers are
injective and distinct whatever the constants and their types (`constants_formerFacts`).
Hence, for a logic given by constants for its rules of inference, for the constants of a set
theory, for axioms:

* every reduction of a typed term is an equality at its type, and the reduct is typed at it
  (`constants_reduces_equal`, `constants_reduces_typed`);
* in every set model of the family a typed term keeps its value along every reduction
  (`constants_reduction_keeps_value`);
* **every term typed in a formed context is strongly normalizing** (`constants_sn`, and
  `constants_typed_sn` for the rules without the annotations), whatever constants are declared
  and at whatever types: the model of strong normalization of the tower reads every constant
  that never computes as its daimon (`Impredicative.SystemF.noSteps_sn`). No order of the
  declarations is asked for.

**Sizes.** In a package over the rules of the tower whose type formers are injective, a
function type is typed only at universes at or above a universe of its domain (`pi_level`).
So a function type over all the sets is a type of no universe at a level of `L` and is not a
set (`functionsOverSets_not_small`, `functionsOverSets_not_set`), and neither is a function
type over a variable that stands for a set a type of a universe at a level of `L`
(`functionsOverVariable_not_small`).

**An equation between sizes is not admitted** (`not_admitted_of_small_step`): a package in
which a type of a universe at a level of `L` takes a declared step to a function type over
all the sets does not have both injective type formers and declared steps that are equalities
at the types of their left sides. The two are the hypotheses under which steps keep types
(`Annotated.ContextualPreservation`). An equation that unfolds the proofs of a statement
about all sets into the functions on all sets is such a step when the type of the proofs is
a type of the least universe.

Scope: the statements of the first list are about the rules with no declared constant and no
declared equation, and those on declared constants about families with no equation. A package
that declares constants with equations is outside both. Its meaning and its consistency come
from a set model (`SetConstantFamilies`, `MegalodonHOTG.SetTheory`), which asks for values that
satisfy the equations and does not ask the equations to stop. For such a package no strong
normalization is stated here, equality of its terms is not decided by these theorems, and
its steps are not shown to keep types. An equation with no value in the well-founded sets
has no such model either.

Positive example: the identity on the sets, without its domain written, is strongly
normalizing (`setIdentity_sn`). Negative example: with a declared equation the conclusion can
fail; the equation of the streams unfolds again at every step, so a term typed in a formed
context of the stream package is not strongly normalizing (`Streams.iter_typed_not_sn` in
`MegalodonHOTG.Streams`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
namespace MegalodonHOTG

open Presentation Presentation.TypedEquality Presentation.TypedEquality.Annotated
open Presentation.TypedEquality.Normalization (CtxFormed IsType TypeEq LevelModel CumulativeAlgebra
  HeadSame)
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (CofinalInaccessibles)

universe u

variable {L : Type} [LevelOrder L] {n : Nat} {Γ : LevelTower.Ctx (Above L) n}

/-- **Strong normalization**: every term typed in a formed context of the tower inside the
sets is strongly normalizing. -/
theorem sn {t A : LevelTower.Tm (Above L) n} (formed : CtxFormed (rules L) Γ)
    (typed : Typed (rules L) Γ t A) : StrongNormalization.SN (rules L) t :=
  tower_sn formed typed

/-- **The equality of two terms of a type is decided.** -/
theorem equal_decide {t s T : LevelTower.Tm (Above L) n} (formed : CtxFormed (rules L) Γ)
    (typedT : Typed (rules L) Γ t T) (typedS : Typed (rules L) Γ s T) :
    Equal (rules L) Γ t s T ∨ ¬ Equal (rules L) Γ t s T :=
  Normalization.LevelTower.equal_decide formed typedT typedS

/-- **The equality of two types is decided.** -/
theorem typeEq_decide {A B : LevelTower.Tm (Above L) n} (formed : CtxFormed (rules L) Γ)
    (typeA : IsType (rules L) Γ A) (typeB : IsType (rules L) Γ B) :
    TypeEq (rules L) Γ A B ∨ ¬ TypeEq (rules L) Γ A B :=
  Normalization.LevelTower.typeEq_decide formed typeA typeB

/-- **Every derivation lifts to an annotated derivation**: the domain of every abstraction is
reconstructed. -/
theorem lifts {statement : Statement (Head L)} (derivation : Derivable (rules L) statement) :
    Lifts (bare L) statement :=
  tower_lifts derivation

/-- **Every derivation over a formed context elaborates** to an annotated derivation over a
formed annotated context. -/
theorem elaborates {statement : Statement (Head L)} (derivation : Derivable (rules L) statement)
    (formed : statement.CtxFormed (rules L)) :
    ∃ s : CStatement (Head L), s.CtxFormed (bare L) ∧ CDerivable (bare L) s ∧
      s.erase = statement :=
  tower_elaborates derivation formed

/-- **Consistency of the rules**, relative to cofinally many inaccessible cardinals in one
universe: no closed term has the type `Π (X : U₀). X`. -/
theorem bare_consistent (h : CofinalInaccessibles.{u}) (t : LevelTower.Tm (Above L) 0) :
    ¬ Derivable (rules L) (.typing .nil t emptyType.erase) :=
  candidate_consistent h t

/-- Positive example: the identity on the sets, without its domain written, is strongly
normalizing. -/
theorem setIdentity_sn :
    StrongNormalization.SN (rules L)
      ((.lam allSets (.var 0) : CTm (Head L) 0).erase) :=
  sn (Γ := .nil) .nil (setIdentity_typed (P := bare L) (Γ := .nil) contains_rules).erase

/-! ## Annotated terms along reduction -/

section Reduction

open ZFSetInterpretation (universeSet)

variable {Θ : CCtx (Head L) n}

/-- Head equality preserves the typing of annotated terms in every package whose head typing
and head equality are the tower's: equal levels are cumulative both ways. -/
theorem headPreserving {R : Rules (Head L)} (contains : Contains R)
    (typingWithin : ∀ {h u : Head L}, R.headTyping h u → LevelTower.HeadTyping h u)
    (headEqWithin : ∀ {h h' : Head L}, R.headEq h h' → LevelTower.HeadEq h h')
    (P : ChurchRules R) : CHeadPreserving P := by
  intro n Γ h h' A same typing
  obtain ⟨u, headTyping, le⟩ := typing.generation
  have same' := headEqWithin same
  cases typingWithin headTyping with
  | legacyGround =>
      cases h' with
      | legacyGround => exact CTyped.subsume (.headType headTyping) le
      | sort _ => exact same'.elim
  | sort l =>
      cases h' with
      | legacyGround => exact same'.elim
      | sort r =>
          have raise : R.cumulative (.sort (.succ r)) (.sort (.succ l)) :=
            contains.cumulative (u := .sort (.succ r)) (v := .sort (.succ l)) fun ν => by
              show LevelOrder.succ (LevelExpr.eval ν r) ≤ LevelOrder.succ (LevelExpr.eval ν l)
              exact LevelOrder.succ_le_succ (le_of_eq (same' ν).symm)
          exact CTyped.subsume
            (CDerivable.cumul (.headType (contains.headTyping (.sort r))) raise) le

/-- Head equality of the tower inside the sets preserves the typing of annotated terms. -/
theorem bare_headPreserving : CHeadPreserving (bare L) :=
  headPreserving contains_rules id id (bare L)

/-- **Every reduction of a typed annotated term is an equality at its type**, at any position
of the term. -/
theorem reduces_equal {t s T : CTm (Head L) n} (formed : CCtxFormed (bare L) Θ)
    (reduces : CReduces (bare L) t s) (typing : CTyped (bare L) Θ t T) :
    CEqual (bare L) Θ t s T :=
  CReduces.equal towerFormerFacts towerLevels (fun _ step _ => step.elim) bare_headPreserving
    formed reduces typing

variable (small : CofinalInaccessibles.{u}) (large : CofinalInaccessibles.{u + 1})

include small in
/-- **A typed annotated term keeps its set value along every reduction**, in the reading of
the type of all sets as all the sets of the lower universe, relative to cofinally many
inaccessible cardinals in two universes. -/
theorem reduction_keeps_value {ground : ZFSet.{u + 1}} (ν : Nat → Above L)
    (groundTyped : ground ∈ universeSet large ZFSet.omega (LevelOrder.bot : L))
    (consts : DeclName → ZFSet.{u + 1}) {t s T : CTm (Head L) n}
    (formed : CCtxFormed (bare L) Θ) (typing : CTyped (bare L) Θ t T)
    (reduces : CReduces (bare L) t s) (ρ : Env.{u + 1} n)
    (sat : Sat (lowerSetsHeads (L := L) large ground ν) consts Θ ρ) :
    ev (lowerSetsHeads (L := L) large ground ν) consts t ρ =
      ev (lowerSetsHeads (L := L) large ground ν) consts s ρ :=
  reduction_value_eq (lowerSets_setModel small large ν groundTyped consts) towerFormerFacts
    towerLevels (fun _ step _ => step.elim) bare_headPreserving formed typing reduces ρ sat

end Reduction

/-! ## Packages over the rules of the tower -/

section Packages

variable (R₂ : Rules (Head L))

/-- The universe laws of the tower hold of every package over its rules. -/
abbrev packageLevels : LevelModel (Rules.sum (rules L) R₂) (Above L) :=
  Annotated.LevelModel.sum towerLevels R₂

/-- The laws of cumulativity of the tower hold of every package over its rules. -/
theorem packageAlgebra : CumulativeAlgebra (Rules.sum (rules L) R₂) :=
  { Normalization.TowerModel.algebra with }

/-- The tower's reading of the heads, for a package over its rules. -/
def packageHeadReading : HeadReading (Rules.sum (rules L) R₂) := { towerHeadReading with }

variable {R₂}

/-- Head equality preserves typing in every package over the rules of the tower. -/
theorem package_headPreserving (Q : ChurchRules (Rules.sum (rules L) R₂)) : CHeadPreserving Q :=
  headPreserving package_contains id id Q

end Packages

/-! ## Declared constants with no equation -/

section Constants

variable (L) in
/-- **The tower inside the sets with a family of declared constants and no equation.** -/
abbrev withConstants (decls : DeclName → Option (CTm (Head L) 0)) :
    ChurchRules (Rules.sum (rules L) (familyRules (rules L) decls [])) :=
  withFamily (bare L) decls []

variable {decls : DeclName → Option (CTm (Head L) 0)} {Θ : CCtx (Head L) n}

/-- A family with no equation has no declared step. -/
theorem constants_noSteps {l r : CTm (Head L) n} :
    ¬ (withConstants L decls).computation.step l r := by
  rintro (step | step)
  · exact step.elim
  · exact family_no_step_of_no_equation (rules L) step

/-- The declared steps of a family with no equation are equalities: it has none. -/
theorem constants_admitted : CRootAdmitted (withConstants L decls) :=
  fun _ step _ => (constants_noSteps step).elim

/-- **The type formers of a family of declared constants with no equation are injective and
distinct**, whatever the constants and their types. -/
theorem constants_formerFacts : CFormerFacts (withConstants L decls) :=
  CFormerFacts.ofNoSteps constants_noSteps (packageLevels _) (packageHeadReading _)
    tower_groundHeadEq tower_universe

/-- **Every reduction of a term typed over a family of declared constants with no equation is
an equality at its type**, at any position of the term. -/
theorem constants_reduces_equal {t s T : CTm (Head L) n}
    (formed : CCtxFormed (withConstants L decls) Θ) (reduces : CReduces (withConstants L decls) t s)
    (typing : CTyped (withConstants L decls) Θ t T) : CEqual (withConstants L decls) Θ t s T :=
  CReduces.equal constants_formerFacts (packageLevels _) constants_admitted
    (package_headPreserving _) formed reduces typing

/-- The reduct is typed at the type of the term. -/
theorem constants_reduces_typed {t s T : CTm (Head L) n}
    (formed : CCtxFormed (withConstants L decls) Θ) (reduces : CReduces (withConstants L decls) t s)
    (typing : CTyped (withConstants L decls) Θ t T) : CTyped (withConstants L decls) Θ s T :=
  CReduces.typed constants_formerFacts (packageLevels _) constants_admitted
    (package_headPreserving _) formed reduces typing

/-- The rules of a family with no equation have no root step. -/
theorem constants_rules_noSteps {l r : LevelTower.Tm (Above L) n} :
    ¬ (Rules.sum (rules L) (familyRules (rules L) decls [])).computation.step l r := by
  rintro (step | ⟨_, member, _⟩)
  · exact step.elim
  · exact nomatch member

/-- **Strong normalization of declared constants with no equation**, for the rules of the
family: every term typed in a formed context is strongly normalizing, whatever constants the
family declares and at whatever types. -/
theorem constants_typed_sn {t A : LevelTower.Tm (Above L) n}
    (formed : CtxFormed (Rules.sum (rules L) (familyRules (rules L) decls [])) Γ)
    (typed : Typed (Rules.sum (rules L) (familyRules (rules L) decls [])) Γ t A) :
    StrongNormalization.SN (Rules.sum (rules L) (familyRules (rules L) decls [])) t :=
  Impredicative.SystemF.noSteps_sn (R := Rules.sum (rules L) (familyRules (rules L) decls []))
    id id id id id constants_rules_noSteps formed typed

/-- **Strong normalization of declared constants with no equation**: every term typed in a
formed context of the tower inside the sets with a family of declared constants and no
equation is strongly normalizing, whatever the constants and their types. -/
theorem constants_sn {t T : CTm (Head L) n} (formed : CCtxFormed (withConstants L decls) Θ)
    (typing : CTyped (withConstants L decls) Θ t T) :
    StrongNormalization.SN (Rules.sum (rules L) (familyRules (rules L) decls [])) t.erase :=
  constants_typed_sn formed.erase typing.erase

/-- **A term typed over a family of declared constants with no equation keeps its set value
along every reduction**, in every set model of the family. -/
theorem constants_reduction_keeps_value {heads : Head L → ZFSet.{u}}
    {consts : DeclName → ZFSet.{u}} (model : SetModel heads consts (withConstants L decls))
    {t s T : CTm (Head L) n} (formed : CCtxFormed (withConstants L decls) Θ)
    (typing : CTyped (withConstants L decls) Θ t T)
    (reduces : CReduces (withConstants L decls) t s) (ρ : Env.{u} n)
    (sat : Sat heads consts Θ ρ) : ev heads consts t ρ = ev heads consts s ρ :=
  reduction_value_eq model constants_formerFacts (packageLevels _) constants_admitted
    (package_headPreserving _) formed typing reduces ρ sat

end Constants

/-! ## Sizes -/

section Sizes

variable {R₂ : Rules (Head L)} {Q : ChurchRules (Rules.sum (rules L) R₂)} {Θ : CCtx (Head L) n}
  (facts : CFormerFacts Q)

include facts

/-- A universe usable at a universe is at a level at most the other's. -/
theorem universe_level_le (formed : CCtxFormed Q Θ) {w t : Head L}
    (hw : (Rules.sum (rules L) R₂).isUniverse w) (typeT : CIsType Q Θ (.head t))
    (le : CTypeLe Q Θ (.head w) (.head t)) :
    (packageLevels R₂).level w ≤ (packageLevels R₂).level t := by
  obtain ⟨v, _, eT, c⟩ := CBelow.universe_cumulative facts (packageLevels R₂) (packageAlgebra R₂)
    (CTypeLe.toBelow le typeT) formed hw
    (CIsType.refl (CIsType.head_of_universe (packageLevels R₂) hw))
  rw [(HeadSame.level (packageLevels R₂) (CTypeEq.head_injective facts eT formed)).2]
  exact ((packageLevels R₂).cumulative_universe c).2.2

/-- **A function type is typed only at universes at or above a universe of its domain.** -/
theorem pi_level (formed : CCtxFormed Q Θ) {A : CTm (Head L) n} {B : CTm (Head L) (n + 1)}
    {t : Head L} (typing : CTyped Q Θ (.pi A B) (.head t)) :
    ∃ u, (Rules.sum (rules L) R₂).isUniverse u ∧ CTyped Q Θ A (.head u) ∧
      (packageLevels R₂).level u ≤ (packageLevels R₂).level t := by
  obtain ⟨u, v, w, tA, hu, _, _, join, le⟩ := typing.generation
  obtain ⟨hw, levelW⟩ := (packageLevels R₂).join_level join
  exact ⟨u, hu, tA, le_trans ((le_max_left _ _).trans_eq levelW.symm)
    (universe_level_le facts formed hw (CTyped.isType (packageLevels R₂) typing formed) le)⟩

/-- The type of all sets is typed only from the classes up. -/
theorem sets_level (formed : CCtxFormed Q Θ) {u : Head L}
    (hu : (Rules.sum (rules L) R₂).isUniverse u) (typing : CTyped Q Θ allSets (.head u)) :
    (Above.above 1 : Above L) ≤ (packageLevels R₂).level u := by
  obtain ⟨u', headTyping, le⟩ := typing.generation
  cases headTyping with
  | sort _ =>
      exact universe_level_le facts formed (.sort _)
        (CIsType.head_of_universe (packageLevels R₂) hu) le

/-- **A function type over all the sets is typed only from the classes up.** -/
theorem functionsOverSets_level (formed : CCtxFormed Q Θ) {B : CTm (Head L) (n + 1)}
    {t : Head L} (typing : CTyped Q Θ (.pi allSets B) (.head t)) :
    (Above.above 1 : Above L) ≤ (packageLevels R₂).level t := by
  obtain ⟨u, hu, tA, le⟩ := pi_level facts formed typing
  exact le_trans (sets_level facts formed hu tA) le

/-- **A function type over all the sets is a type of no universe at a level of `L`.** -/
theorem functionsOverSets_not_small (formed : CCtxFormed Q Θ) {B : CTm (Head L) (n + 1)}
    (d : L) : ¬ CTyped Q Θ (.pi allSets B) (universeAt d) := fun typing =>
  Above.not_above_le_below 1 d (functionsOverSets_level facts formed typing)

/-- A function type over all the sets is not a set. -/
theorem functionsOverSets_not_set (formed : CCtxFormed Q Θ) {B : CTm (Head L) (n + 1)} :
    ¬ CTyped Q Θ (.pi allSets B) allSets := fun typing =>
  absurd (Above.above_le_above.mp (functionsOverSets_level facts formed typing)) (by decide)

/-- **A function type over a variable that stands for a set is a type of no universe at a
level of `L`**: the bounded quantifier over a set that is not known to be small has the size
of the sets. -/
theorem functionsOverVariable_not_small (formed : CCtxFormed Q Θ) {i : Fin n}
    (isSet : Θ.lookup i = allSets) {B : CTm (Head L) (n + 1)} (d : L) :
    ¬ CTyped Q Θ (.pi (.var i) B) (universeAt d) := fun typing => by
  obtain ⟨u, hu, tA, le⟩ := pi_level facts formed typing
  have declared : CTypeLe Q Θ (Θ.lookup i) (.head u) := tA.generation
  rw [isSet] at declared
  exact Above.not_above_le_below 0 d
    (le_trans (universe_level_le facts formed (.sort _)
      (CIsType.head_of_universe (packageLevels R₂) hu) declared) le)

/-- **An equation between sizes is not admitted.** A package in which a type of a universe at
a level of `L` takes a declared step to a function type over all the sets does not have both
injective type formers and declared steps that are equalities at the types of their left
sides. -/
theorem not_admitted_of_small_step (formed : CCtxFormed Q Θ) {l : CTm (Head L) n}
    {B : CTm (Head L) (n + 1)} {d : L} (typing : CTyped Q Θ l (universeAt d))
    (step : Q.computation.step l (.pi allSets B)) : ¬ CRootAdmitted Q := fun admitted =>
  functionsOverSets_not_small facts formed d
    (CEqual.typed (packageLevels R₂) (admitted formed step typing) formed).2

end Sizes

end MegalodonHOTG
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
