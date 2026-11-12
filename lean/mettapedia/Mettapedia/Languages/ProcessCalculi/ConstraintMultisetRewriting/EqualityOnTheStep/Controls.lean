import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.EqualityOnTheStep.Transport

/-!
# Controls: what does not transport, and why

**A predicate that reads the code of a set is not respected** (`codeReading_not_respected`). The
region "the row's code is literally `S`" holds of `S` and not of `T`, while the evidence for
`setEq S T` exists. Transport is defined only along a classifying substitution into
`Transport.Omega`, whose family is a term of the calculus with a respect term; a predicate on codes is
neither, so the design has no transport for it.

**Inside the language, the identity type reads the code of a set** (`idFamily`): `λR. Id (U0 → U0) R S`
is a family of sets, inhabited at `S` (`idFamily_at_S`) and closed-uninhabited at `T`
(`idSets_uninhabited`, by η-long normal forms). It has **no closed respect term**
(`idFamily_no_respect`): one would carry the evidence and `refl S` to a closed inhabitant of
`Id (U0 → U0) T S`. So the restriction "transport needs a respect term" is necessary: dropping it
would transport the intensional identity type, which is false.

**Absence does not transport** (`absence_does_not_transport`). Over `p : Ground`, a state holding the
evidence for `setEq S T` and the member `(p, λy. y) : T (Ground → Ground)`, and no member of `S`:
the absence of every member of `S (Ground → Ground)` is admitted (`absentS_admitted`), and the absence
of every member of `T (Ground → Ground)` is refused (`absentT_refused`). A rule "absence at `S` and
`S ≈ T` give absence at `T`" would be unsound. The rule that prevents it: queries read through the
**knowledge** only (`Query.reads`), the equality rows are rows, not knowledge, and a transport firing
only makes a row: it takes nothing, tells nothing, guards nothing and asks nothing
(`transportBy_only_makes`). Absence is an observation of the rows present, not a proposition. A
negation `S X → ⊥` is a family, and it has a respect term, by the backward map
(`SetTheory.negRespect_typed`), so non-membership transports where absence does not.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace EqualityOnTheStep.Controls

open _root_.CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open Interface.DependentFull Interface.DependentFull.Controls
open ProgrammingOnTheStep.SetExtensionality (small U0 sCode tCode setType swapCode swapType
  swapBackType setType_formed s_typed t_typed swap_typed swapBack_typed)

/-! ## A predicate on codes -/

/-- The region "the row's code is literally `S`". -/
def codeIsS {Γ : Context Tower.rules} (t : TotalTerm Γ) : Prop := t.2.code = sCode

/-- **Reading the code of a set is not respected by extensional equality.** -/
theorem codeReading_not_respected :
    Typed Tower.rules triple.raw Run.evidenceAt (setEq sCode tCode) ∧
      codeIsS (ProgrammingOnTheStep.SetExtensionality.sRow triple) ∧
      ¬ codeIsS (ProgrammingOnTheStep.SetExtensionality.tRow triple) := by
  refine ⟨Run.evidenceAt_typed, rfl, fun same => ?_⟩
  change (.lam (.sigma ground (.var 1)) : Tower.Tm 3) = .lam (.sigma (.var 0) ground) at same
  cases same

/-! ## The identity type of sets -/

/-- **The identity family of `S`**: `λR. Id (U0 → U0) R S`. -/
def idFamily : Tower.Tm 0 := .lam (.id setType (.var 0) sCode)

theorem idFamily_body : Typed Tower.rules (.snoc .nil setType) (.id setType (.var 0) sCode) (.head large) :=
  .idForm (setType_large _) (.sort _) (Derivable.var 0) (s_typed _)

/-- It is a family of sets. -/
theorem idFamily_typed : Typed Tower.rules .nil idFamily famType :=
  .lamIntro (famType_formed _) (.sort _) idFamily_body

theorem idFamily_at_S_beta : Equal Tower.rules .nil (.app idFamily sCode) (.id setType sCode sCode) (.head large) :=
  Derivable.betaPi (famType_formed _) (.sort _) idFamily_body (s_typed _)

theorem idFamily_at_T_beta : Equal Tower.rules .nil (.app idFamily tCode) (.id setType tCode sCode) (.head large) :=
  Derivable.betaPi (famType_formed _) (.sort _) idFamily_body (t_typed _)

/-- **Inhabited at `S`**: `refl S`. -/
theorem idFamily_at_S : Typed Tower.rules .nil (.refl sCode) (.app idFamily sCode) :=
  .conv (.reflIntro (s_typed _)) (.symm idFamily_at_S_beta) (.sort _)

theorem idSets_formed : Typed Tower.rules .nil (.id setType tCode sCode) (.head large) :=
  .idForm (setType_large _) (.sort _) (t_typed _) (s_typed _)

/-- **`Id (U0 → U0) T S` has no closed inhabitant**: an η-long closed normal form of it would be
`refl R` with `R` equal to both `T` and `S`, and `S` and `T` are equal at no solution. -/
theorem idSets_uninhabited {t : Tower.Tm 0} : ¬ Typed Tower.rules .nil t (.id setType tCode sCode) := by
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
        ∃ A, Typed Tower.rules .nil _ A ∧ TypeLe Tower.rules .nil (.id A _ _) (.id setType tCode sCode))
      have same := TypeLe.id_eq (S := ContextualDependentEtaLong.Controls.setting) TowerModel.facts le
        ⟨_, .sort _, idSets_formed⟩ .nil
      obtain ⟨⟨u, hu, sameA⟩, toT, toS⟩ := TypeEq.id_injective TowerModel.facts same .nil
      have equal : Equal Tower.rules .nil tCode sCode setType := .convEq (.trans (.symm toT) toS) sameA hu
      exact ProgrammingOnTheStep.SetExtensionality.sets_unsolvable (toEmpty (empty Tower.rules))
        ((equivalent_iff setting.levels _ _).mpr ⟨⟨large, .sort _, .refl (setType_large _)⟩, .symm equal⟩)
  | neutral ls _ _ _ => exact ContextualDependentClosedBoundary.Controls.closedSpine ls

/-- **The identity family has no closed respect term.** -/
theorem idFamily_no_respect {r : Tower.Tm 0} : ¬ Typed Tower.rules .nil r (respType idFamily) := by
  intro tr
  have E0 : Typed Tower.rules .nil (evidence swapCode swapCode) (setEq sCode tCode) :=
    evidence_typed (swap_typed _) (swapBack_typed _)
  have carried := Derivable.appElim (Derivable.appElim (Derivable.appElim (Derivable.appElim tr (s_typed _))
    (t_typed _)) E0) idFamily_at_S
  have atT : Typed Tower.rules .nil
      (.app (.app (.app (.app r sCode) tCode) (evidence swapCode swapCode)) (.refl sCode)) (.app idFamily tCode) :=
    carried
  exact idSets_uninhabited (.conv atT idFamily_at_T_beta (.sort _))

/-! ## Absence does not transport -/

/-- `λy. y : Ground → Ground`. -/
theorem identity_typed {n : Nat} (Γ : Tower.Ctx n) : Typed Tower.rules Γ (.lam (.var 0)) arrow :=
  .lamIntro (arrow_typed _) (.sort _) (Derivable.var 0)

/-- `(p, λy. y) : T (Ground → Ground)`, over `p : Ground`. -/
theorem arrowMemberT_typed :
    Typed Tower.rules point.raw (.pair (.var 0) (.lam (.var 0))) (.app tCode arrow) := by
  have formed : Typed Tower.rules point.raw (.sigma ground arrow) U0 :=
    .cumul (.sigmaForm (ground_typed _) (.sort _) (arrow_typed _) (.sort _) (.sorts _ _)) collapse
  have p : Typed Tower.rules point.raw (.var 0) ground := Derivable.var 0
  have normal : Typed Tower.rules point.raw (.pair (.var 0) (.lam (.var 0))) (.sigma ground arrow) :=
    .pairIntro formed (.sort _) p (identity_typed _)
  exact .conv normal (.symm (t_beta (arrow_typed _))) (.sort _)

/-- The evidence row over `p : Ground`. -/
def evidenceRowAtPoint : TotalTerm point :=
  ⟨Run.largeType point (setEq sCode tCode) (setEq_formed (s_typed _) (t_typed _)),
    ⟨evidence swapCode swapCode, evidence_typed (swap_typed _) (swapBack_typed _)⟩⟩

/-- The member of `T (Ground → Ground)`. -/
def arrowMemberT : TotalTerm point :=
  ⟨Run.smallType point (.app tCode arrow) (Run.app_small (t_typed _) (arrow_typed _)),
    ⟨.pair (.var 0) (.lam (.var 0)), arrowMemberT_typed⟩⟩

/-- **The state**: the evidence for `setEq S T` (row `0`) and a member of `T (Ground → Ground)`
(row `1`); no member of `S`. -/
def absenceState : State Tower.rules Nat :=
  ⟨point, [], {0, 1}, fun o => if o = 0 then evidenceRowAtPoint else arrowMemberT⟩

/-- `h : S (Ground → Ground)`. -/
def sHelper : TypeOver point := Run.smallType point (.app sCode arrow) (Run.app_small (s_typed _) (arrow_typed _))

abbrev withSHelper : Context Tower.rules := extend point sHelper

def sPattern : TotalTerm withSHelper :=
  ⟨Run.smallType withSHelper (.app sCode arrow) (Run.app_small (s_typed _) (arrow_typed _)),
    ⟨.var 0, Derivable.var 0⟩⟩

/-- `h : T (Ground → Ground)`. -/
def tHelper : TypeOver point := Run.smallType point (.app tCode arrow) (Run.app_small (t_typed _) (arrow_typed _))

abbrev withTHelper : Context Tower.rules := extend point tHelper

def tPattern : TotalTerm withTHelper :=
  ⟨Run.smallType withTHelper (.app tCode arrow) (Run.app_small (t_typed _) (arrow_typed _)),
    ⟨.var 0, Derivable.var 0⟩⟩

/-- **Ask the absence of every member of `S (Ground → Ground)`.** -/
def absentS : Firing setting.levels absenceState where
  helpers := .cons sHelper (.nil _)
  taken := []
  read := []
  takes := []
  reads := []
  makes := []
  tells := []
  guards := []
  queries := [Query.absent setting.levels Nat sPattern]

/-- **Ask the absence of every member of `T (Ground → Ground)`.** -/
def absentT : Firing setting.levels absenceState where
  helpers := .cons tHelper (.nil _)
  taken := []
  read := []
  takes := []
  reads := []
  makes := []
  tells := []
  guards := []
  queries := [Query.absent setting.levels Nat tPattern]

theorem absentS_information : absentS.information = [] := rfl

theorem absentT_information : absentT.information = [] := rfl

theorem absentS_row (o : Nat) : absentS.row o = (absenceState.label o).reindex (projectionHom point sHelper) :=
  rfl

/-- **The absence of members of `S` is admitted**: no solution equates a member of `S (Ground → Ground)`
with the evidence (a dependent function, not a pair) or with the member of `T (Ground → Ground)`
(`Σ (Ground → Ground) Ground` is not `Σ Ground (Ground → Ground)`). -/
theorem absentS_admitted : (step setting.levels Nat).Admits absentS := by
  refine (admits_iff absentS).mpr ⟨⟨List.nodup_nil, List.nodup_nil, rfl, rfl,
      fun _ member => absurd member List.not_mem_nil⟩,
    ⟨fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil,
      fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil⟩,
    ?_, fun _ _ _ _ member => absurd member List.not_mem_nil, ?_⟩
  · rw [absentS_information]
    exact ⟨withSHelper, 𝟙 _, Frames.models_nil _⟩
  intro q member Θ τ _
  obtain rfl := List.mem_singleton.mp member
  refine (Query.absent_holds_iff _ _ _ τ).mpr fun o present equated => ?_
  have types := equated.1
  have hS : TypeEq Tower.rules Θ.raw (.app sCode arrow) (.sigma arrow ground) :=
    ⟨small, .sort _, s_beta (arrow_typed _)⟩
  change o ∈ ({0, 1} : Finset Nat) at present
  rcases Finset.mem_insert.mp present with rfl | rest
  · change TypeEq Tower.rules Θ.raw (.app sCode arrow) (setEq sCode tCode) at types
    exact TypeEq.pi_ne_sigma (TowerModel.facts (L := Nat)) Θ.formed (types.symm.trans setting.levels hS)
  · obtain rfl := Finset.mem_singleton.mp rest
    change TypeEq Tower.rules Θ.raw (.app sCode arrow) (.app tCode arrow) at types
    have hT : TypeEq Tower.rules Θ.raw (.app tCode arrow) (.sigma ground arrow) :=
      ⟨small, .sort _, t_beta (arrow_typed _)⟩
    have both : TypeEq Tower.rules Θ.raw (.sigma arrow ground) (.sigma ground arrow) :=
      (hS.symm.trans setting.levels types).trans setting.levels hT
    exact ground_arrow_clash Θ.formed
      (TypeEq.sigma_injective (TowerModel.facts (L := Nat)) both Θ.formed).1.symm

/-- `h ↦ (p, λy. y)`. -/
def tWitness : point ⟶ withTHelper := pair (𝟙 point) ⟨.pair (.var 0) (.lam (.var 0)), arrowMemberT_typed⟩

theorem tWitness_identifies :
    tPattern.reindex tWitness = (absentT.row 1).reindex tWitness :=
  totalTerm_ext (TypeOver.ext rfl rfl) rfl

/-- **The absence of members of `T` is refused**: the solution `h ↦ (p, λy. y)` equates the pattern
with row `1`. -/
theorem absentT_refused : ¬ (step setting.levels Nat).Admits absentT := by
  intro admitted
  obtain ⟨-, -, -, -, queries⟩ := (admits_iff absentT).mp admitted
  have solved : (frames setting.levels).Models tWitness absentT.information := by
    rw [absentT_information]
    exact Frames.models_nil _
  have asked := (Query.absent_holds_iff _ _ _ _).mp (queries _ (List.Mem.head _) point tWitness solved)
  refine asked 1 (show (1 : Nat) ∈ ({0, 1} : Finset Nat) by decide) ?_
  show (frames setting.levels).E (tPattern.reindex tWitness) ((absentT.row 1).reindex tWitness)
  rw [tWitness_identifies]
  exact ((frames setting.levels).equivalence _).refl _

/-- **Absence does not transport**: in a state holding the evidence for `setEq S T`, the absence of
members of `S` at `Ground → Ground` is admitted and the absence of members of `T` there is refused. -/
theorem absence_does_not_transport :
    (absenceState.label 0).1.code = setEq sCode tCode ∧ 0 ∈ absenceState.present ∧
      (step setting.levels Nat).Admits absentS ∧ ¬ (step setting.levels Nat).Admits absentT :=
  ⟨rfl, show (0 : Nat) ∈ ({0, 1} : Finset Nat) by decide, absentS_admitted, absentT_refused⟩

/-- **Transport only makes rows**: it takes nothing, tells nothing, guards nothing and asks nothing. -/
theorem transportBy_only_makes (st : State Tower.rules Nat) (i j k : Nat) (σ : st.frame ⟶ Transport.Omega) :
    (Transport.transportBy st i j k σ).taken = [] ∧ (Transport.transportBy st i j k σ).tells = [] ∧
      (Transport.transportBy st i j k σ).guards = [] ∧ (Transport.transportBy st i j k σ).queries = [] :=
  ⟨rfl, rfl, rfl, rfl⟩

end EqualityOnTheStep.Controls

#print axioms EqualityOnTheStep.Controls.codeReading_not_respected
#print axioms EqualityOnTheStep.Controls.idFamily_typed
#print axioms EqualityOnTheStep.Controls.idFamily_at_S
#print axioms EqualityOnTheStep.Controls.idSets_uninhabited
#print axioms EqualityOnTheStep.Controls.idFamily_no_respect
#print axioms EqualityOnTheStep.Controls.absentS_admitted
#print axioms EqualityOnTheStep.Controls.absentT_refused
#print axioms EqualityOnTheStep.Controls.absence_does_not_transport
#print axioms EqualityOnTheStep.Controls.transportBy_only_makes

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
