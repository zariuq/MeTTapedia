import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSweepWitnessesCumulative
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFullControls

/-!
# Sets as predicates: comprehension is native, extensionality is not knowledge

A HOL-style reading of sets over the dependent step: a set over `U0` is a predicate `U0 → U0`, and
comprehension is abstraction. Two sets:

* `S = {X | Σ (_ : X). Ground}`, the code `λX. Σ X Ground`;
* `T = {X | Σ (_ : Ground). X}`, the code `λX. Σ Ground X`.

They have the same members in the strongest internal sense: two closed functions swap the
components, `Π X. S-type X → T-type X` and back (`swap_typed`, `swapBack_typed`).

**Extensionality cannot be told** (`extensionality_refused`). A firing that holds both swaps as rows
and tells `S ≐ T` is refused: the knowledge equates terms only up to typed βη conversion, and the
two abstractions are not convertible, since their bodies are different dependent pair types
(`sets_unsolvable`). So the knowledge of the step is intensional. Set extensionality, like any
equality decided by proof, has to be a proposition or a quotient carried by the program, not an
equation of the knowledge.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ProgrammingOnTheStep.SetExtensionality

open _root_.CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open Interface.DependentFull Interface.DependentFull.Controls

abbrev small : Tower.Head := .sort Tower.zero

abbrev U0 {n : Nat} : Tower.Tm n := .head small

theorem collapse : Tower.rules.cumulative (.sort (.max Tower.zero Tower.zero)) small := by
  change LevelTower.Cumulative (.sort (.max Tower.zero Tower.zero)) (.sort Tower.zero)
  intro valuation
  simp [LevelExpr.eval]

/-! ## Two sets -/

/-- `S = λX. Σ (_ : X). Ground`. -/
def sCode {n : Nat} : Tower.Tm n := .lam (.sigma (.var 0) ground)

/-- `T = λX. Σ (_ : Ground). X`. -/
def tCode {n : Nat} : Tower.Tm n := .lam (.sigma ground (.var 1))

/-- Sets over `U0`: `U0 → U0`. -/
def setType {n : Nat} : Tower.Tm n := .pi U0 U0

theorem setType_formed {n : Nat} (Γ : Tower.Ctx n) :
    Typed Tower.rules Γ setType (.head (.sort (.max (.succ Tower.zero) (.succ Tower.zero)))) :=
  .piForm (.headType (.sort _)) (.sort _) (.headType (.sort _)) (.sort _) (.sorts _ _)

theorem s_typed {n : Nat} (Γ : Tower.Ctx n) : Typed Tower.rules Γ sCode setType :=
  .lamIntro (setType_formed Γ) (.sort _)
    (.cumul (.sigmaForm (Derivable.var 0) (.sort _) (ground_typed _) (.sort _) (.sorts _ _)) collapse)

theorem t_typed {n : Nat} (Γ : Tower.Ctx n) : Typed Tower.rules Γ tCode setType :=
  .lamIntro (setType_formed Γ) (.sort _)
    (.cumul (.sigmaForm (ground_typed _) (.sort _) (Derivable.var 1) (.sort _) (.sorts _ _)) collapse)

/-! ## The same members: two swaps -/

/-- `λX. λp. pair (snd p) (fst p)`. -/
def swapCode {n : Nat} : Tower.Tm n := .lam (.lam (.pair (.snd (.var 0)) (.fst (.var 0))))

/-- `Π (X : U0). (Σ (_ : X). Ground) → Σ (_ : Ground). X`. -/
def swapType {n : Nat} : Tower.Tm n := .pi U0 (.pi (.sigma (.var 0) ground) (.sigma ground (.var 2)))

/-- `Π (X : U0). (Σ (_ : Ground). X) → Σ (_ : X). Ground`. -/
def swapBackType {n : Nat} : Tower.Tm n := .pi U0 (.pi (.sigma ground (.var 1)) (.sigma (.var 1) ground))

/-- **`S X` gives `T X`**, for every `X`. -/
theorem swap_typed {n : Nat} (Γ : Tower.Ctx n) : Typed Tower.rules Γ swapCode swapType := by
  have pairs : Typed Tower.rules (.snoc (.snoc Γ U0) (.sigma (.var 0) ground)) (.sigma ground (.var 2)) U0 :=
    .cumul (.sigmaForm (ground_typed _) (.sort _) (Derivable.var 2) (.sort _) (.sorts _ _)) collapse
  have p : Typed Tower.rules (.snoc (.snoc Γ U0) (.sigma (.var 0) ground)) (.var 0) (.sigma (.var 1) ground) :=
    Derivable.var 0
  have body : Typed Tower.rules (.snoc (.snoc Γ U0) (.sigma (.var 0) ground))
      (.pair (.snd (.var 0)) (.fst (.var 0))) (.sigma ground (.var 2)) :=
    .pairIntro pairs (.sort _) (.sndElim p) (.fstElim p)
  have domain : Typed Tower.rules (.snoc Γ U0) (.sigma (.var 0) ground) U0 :=
    .cumul (.sigmaForm (Derivable.var 0) (.sort _) (ground_typed _) (.sort _) (.sorts _ _)) collapse
  have inner : Typed Tower.rules (.snoc Γ U0) (.pi (.sigma (.var 0) ground) (.sigma ground (.var 2))) U0 :=
    .cumul (.piForm domain (.sort _) pairs (.sort _) (.sorts _ _)) collapse
  have outer : Typed Tower.rules Γ swapType (.head (.sort (.max (.succ Tower.zero) Tower.zero))) :=
    .piForm (.headType (.sort _)) (.sort _) inner (.sort _) (.sorts _ _)
  exact .lamIntro outer (.sort _) (.lamIntro inner (.sort _) body)

/-- **`T X` gives `S X`**, for every `X`. -/
theorem swapBack_typed {n : Nat} (Γ : Tower.Ctx n) : Typed Tower.rules Γ swapCode swapBackType := by
  have pairs : Typed Tower.rules (.snoc (.snoc Γ U0) (.sigma ground (.var 1))) (.sigma (.var 1) ground) U0 :=
    .cumul (.sigmaForm (Derivable.var 1) (.sort _) (ground_typed _) (.sort _) (.sorts _ _)) collapse
  have p : Typed Tower.rules (.snoc (.snoc Γ U0) (.sigma ground (.var 1))) (.var 0) (.sigma ground (.var 2)) :=
    Derivable.var 0
  have body : Typed Tower.rules (.snoc (.snoc Γ U0) (.sigma ground (.var 1)))
      (.pair (.snd (.var 0)) (.fst (.var 0))) (.sigma (.var 1) ground) :=
    .pairIntro pairs (.sort _) (.sndElim p) (.fstElim p)
  have domain : Typed Tower.rules (.snoc Γ U0) (.sigma ground (.var 1)) U0 :=
    .cumul (.sigmaForm (ground_typed _) (.sort _) (Derivable.var 1) (.sort _) (.sorts _ _)) collapse
  have inner : Typed Tower.rules (.snoc Γ U0) (.pi (.sigma ground (.var 1)) (.sigma (.var 1) ground)) U0 :=
    .cumul (.piForm domain (.sort _) pairs (.sort _) (.sorts _ _)) collapse
  have outer : Typed Tower.rules Γ swapBackType (.head (.sort (.max (.succ Tower.zero) Tower.zero))) :=
    .piForm (.headType (.sort _)) (.sort _) inner (.sort _) (.sorts _ _)
  exact .lamIntro outer (.sort _) (.lamIntro inner (.sort _) body)

/-! ## Extensionality as a told equation -/

def setOver (Γ : Context Tower.rules) : TypeOver Γ :=
  ⟨setType, .sort (.max (.succ Tower.zero) (.succ Tower.zero)), .sort _, setType_formed _⟩

def sRow (Γ : Context Tower.rules) : TotalTerm Γ := ⟨setOver Γ, ⟨sCode, s_typed _⟩⟩
def tRow (Γ : Context Tower.rules) : TotalTerm Γ := ⟨setOver Γ, ⟨tCode, t_typed _⟩⟩

def swapRow : TotalTerm (empty Tower.rules) :=
  ⟨⟨swapType, .sort (.max (.succ Tower.zero) Tower.zero), .sort _, (by
      have pairs : Typed Tower.rules (.snoc (.snoc .nil U0) (.sigma (.var 0) ground)) (.sigma ground (.var 2)) U0 :=
        .cumul (.sigmaForm (ground_typed _) (.sort _) (Derivable.var 2) (.sort _) (.sorts _ _)) collapse
      have domain : Typed Tower.rules (.snoc .nil U0) (.sigma (.var 0) ground) U0 :=
        .cumul (.sigmaForm (Derivable.var 0) (.sort _) (ground_typed _) (.sort _) (.sorts _ _)) collapse
      exact .piForm (.headType (.sort _)) (.sort _)
        (.cumul (.piForm domain (.sort _) pairs (.sort _) (.sorts _ _)) collapse) (.sort _) (.sorts _ _))⟩,
    ⟨swapCode, swap_typed _⟩⟩

def swapBackRow : TotalTerm (empty Tower.rules) :=
  ⟨⟨swapBackType, .sort (.max (.succ Tower.zero) Tower.zero), .sort _, (by
      have pairs : Typed Tower.rules (.snoc (.snoc .nil U0) (.sigma ground (.var 1))) (.sigma (.var 1) ground) U0 :=
        .cumul (.sigmaForm (Derivable.var 1) (.sort _) (ground_typed _) (.sort _) (.sorts _ _)) collapse
      have domain : Typed Tower.rules (.snoc .nil U0) (.sigma ground (.var 1)) U0 :=
        .cumul (.sigmaForm (ground_typed _) (.sort _) (Derivable.var 1) (.sort _) (.sorts _ _)) collapse
      exact .piForm (.headType (.sort _)) (.sort _)
        (.cumul (.piForm domain (.sort _) pairs (.sort _) (.sorts _ _)) collapse) (.sort _) (.sorts _ _))⟩,
    ⟨swapCode, swapBack_typed _⟩⟩

/-- The state holding the two swaps as rows `0` and `1`. -/
def evidenceState : State Tower.rules Nat :=
  ⟨empty Tower.rules, [], {0, 1}, fun o => if o = 0 then swapRow else swapBackRow⟩

/-- **The extensionality firing**: reading both swaps, tell `S ≐ T`. -/
def extensionalityFiring : Firing setting.levels evidenceState where
  helpers := .nil _
  taken := []
  read := [0, 1]
  takes := []
  reads := [swapRow, swapBackRow]
  makes := []
  tells := [(sRow _, tRow _)]
  guards := []
  queries := []

/-- **The two sets are equal at no solution.** -/
theorem sets_unsolvable {Δ : Context Tower.rules} (σ : Δ ⟶ empty Tower.rules) :
    ¬ (frames setting.levels).Solves σ (sRow _, tRow _) := by
  intro solved
  obtain ⟨-, terms⟩ := (equivalent_iff setting.levels _ _).mp solved
  change Equal Tower.rules Δ.raw (.lam (.sigma (.var 0) ground)) (.lam (.sigma ground (.var 1)))
    (.pi U0 U0) at terms
  have bodies := ContextualDependentUniverseInjective.equal_of_lam
    (S := ContextualDependentEtaLong.Controls.setting) TowerModel.facts Δ.formed terms
  have formed : CtxFormed Tower.rules (.snoc Δ.raw U0) :=
    Δ.formed.snoc ⟨_, LevelTower.IsUniverse.sort _, .headType (LevelTower.HeadTyping.sort _)⟩
  have domains := (TypeEq.sigma_injective (TowerModel.facts (L := Nat)) ⟨small, .sort _, bodies⟩ formed).1
  have neutral : Neutral (TowerModel.roles (L := Nat)) (.var 0 : Tower.Tm (Δ.arity + 1)) := .var 0
  exact (TypeEq.neutral_form (TowerModel.facts (L := Nat)) domains formed neutral
    (.inl ⟨_, rfl⟩)).not_former.1 _ rfl

/-- **Extensionality is refused**, with both swaps present as evidence. -/
theorem extensionality_refused : ¬ (step setting.levels Nat).Admits extensionalityFiring := by
  rintro ⟨-, -, ⟨Δ, σ, solved⟩, -⟩
  exact sets_unsolvable σ (solved _ (List.mem_append_right _ (List.mem_singleton_self _)))

end ProgrammingOnTheStep.SetExtensionality

#print axioms ProgrammingOnTheStep.SetExtensionality.s_typed
#print axioms ProgrammingOnTheStep.SetExtensionality.t_typed
#print axioms ProgrammingOnTheStep.SetExtensionality.swap_typed
#print axioms ProgrammingOnTheStep.SetExtensionality.swapBack_typed
#print axioms ProgrammingOnTheStep.SetExtensionality.sets_unsolvable
#print axioms ProgrammingOnTheStep.SetExtensionality.extensionality_refused

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
