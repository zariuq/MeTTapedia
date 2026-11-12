import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.MatchAdmission
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFullControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaElimination

/-!
# Raw typing is not closed under agreement: an η-expanded solution types more

Two solutions that agree on every judged term need not type the same raw row. In the cumulative
βη tower the λ of a function carries no domain, and subtyping of function types keeps the domain
fixed. So over the frame `h : Π (x : U₁). U₁`:

* `h` and its η-expansion `λ x. h x` are equal at `Π (x : U₁). U₁` (`etaHom_substEq`), so the identity
  and the substitution `etaHom : h ↦ λ x. h x` agree (`etaHom_agree`), and both are initial solutions of
  the empty store (`eta_initial`);
* the η-expansion is typed at `Π (x : U₀). U₁` (`etaCode_typed_small`): its bound variable is chosen at
  `U₀` and raised to `U₁`;
* `h` is not (`etaRow_not_wellTyped`): `Π (x : U₁). U₁` usable at `Π (x : U₀). U₁` would make the domains
  equal, and `U₁` is not `U₀` (the normalization model's injectivity of function types and of heads).

So the made row `h : Π (x : U₀). U₁` is typed at one of two agreeing solutions and not at the other:
**typing is not closed under agreement** (`etaRow_not_closed`). The row is typed up to agreement and not
typed after the match (`eta_gap`).

**Consequence for the settling step.** A settler's verdict is an initial solution, and initial solutions
are unique only up to agreement. The settler that settles the empty store along `etaHom`
(`etaSettler`, through `Settler.pointed`) makes the settling step admit the firing that makes this row
(`eta_settled_admitted`), whose row is not typed after the match (`settling_not_sound`,
`eta_not_admittedAfterMatch`). The settler that settles the same store along the identity refuses it
(`identity_refuses`), and so does the present step (`never_refuses_eta`): admission depends on the
representative the settler picks (`representative_dependence`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep

open _root_.CategoryTheory Opposite Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open Interface.DependentFull (Make State Firing)
open UnificationWithLevels (Agree InitialSolution EpiOnTerms)

/-! ## Settlers that know one answer, and the empty store -/

section General

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}
variable (levels : LevelModel rules L)

/-- The verdicts on a store, indexed by the frame and the store together. -/
abbrev VerdictAt (p : (Γ : Context rules) × EquationStore (TotalTerm Γ)) : Type := Verdict levels p.2

open Classical in
/-- **A settler that knows one answer**: it settles the store `I₀` along `σ₀` and postpones every other
store. Every settler of this form is lawful: its one verdict is an initial solution. -/
noncomputable def Settler.pointed {Δ₀ M₀ : Context rules} (I₀ : EquationStore (TotalTerm Δ₀))
    (σ₀ : M₀ ⟶ Δ₀) (initial₀ : InitialSolution (frames levels) I₀ σ₀) : Settler levels :=
  fun {Δ} I =>
    if h : (⟨Δ₀, I₀⟩ : (Γ : Context rules) × EquationStore (TotalTerm Γ)) = ⟨Δ, I⟩ then
      (Eq.rec (motive := fun p _ => VerdictAt levels p) (Verdict.settled M₀ σ₀ initial₀) h :
        VerdictAt levels ⟨Δ, I⟩)
    else .postponed

theorem Settler.pointed_self {Δ₀ M₀ : Context rules} (I₀ : EquationStore (TotalTerm Δ₀))
    (σ₀ : M₀ ⟶ Δ₀) (initial₀ : InitialSolution (frames levels) I₀ σ₀) :
    Settler.pointed levels I₀ σ₀ initial₀ I₀ = .settled M₀ σ₀ initial₀ := by
  unfold Settler.pointed
  rw [dif_pos rfl]

/-- **A substitution that agrees with the identity is an initial solution of the empty store.** -/
theorem initial_nil_of_agree {Δ : Context rules} {σ : Δ ⟶ Δ}
    (agree : Agree (frames levels) (𝟙 Δ) σ) :
    InitialSolution (frames levels) ([] : EquationStore (TotalTerm Δ)) σ := by
  have self : ∀ t : TotalTerm Δ, (frames levels).E t ((frames levels).act σ t) := by
    intro t
    have same := agree t
    rwa [show (frames levels).act (𝟙 Δ) t = t from reindex_id t] at same
  refine UnificationWithLevels.Principal.initial
    ⟨Frames.models_nil (X := frames levels) σ, fun Θ τ _ => ⟨τ, fun t => ?_⟩⟩ ?_
  · change (frames levels).E (t.reindex τ) (t.reindex (τ ≫ σ))
    rw [reindex_comp]
    exact (frames levels).preserves τ (self t)
  · intro Θ g h same t
    have left : (frames levels).E ((frames levels).act g t) ((frames levels).act g ((frames levels).act σ t)) :=
      (frames levels).preserves g (self t)
    have right : (frames levels).E ((frames levels).act h ((frames levels).act σ t)) ((frames levels).act h t) :=
      ((frames levels).equivalence Θ).symm ((frames levels).preserves h (self t))
    exact ((frames levels).equivalence Θ).trans left (((frames levels).equivalence Θ).trans (same t) right)

end General

namespace Eta

open Interface.DependentFull.Controls

/-! ## The frame `h : Π (x : U₁). U₁` -/

/-- The universe at level 0. -/
abbrev u0 {n : Nat} : Tower.Tm n := .head (.sort Tower.zero)

/-- The universe at level 1. -/
abbrev u1 {n : Nat} : Tower.Tm n := .head (.sort (.succ Tower.zero))

/-- `Π (x : U₁). U₁` is a type. -/
theorem bigArrow_typed {n : Nat} (Γ : Tower.Ctx n) :
    Typed Tower.rules Γ (.pi u1 u1)
      (.head (.sort (.max (.succ (.succ Tower.zero)) (.succ (.succ Tower.zero))))) :=
  .piForm (.headType (.sort _)) (.sort _) (.headType (.sort _)) (.sort _) (.sorts _ _)

/-- `Π (x : U₀). U₁` is a type. -/
theorem smallArrow_typed {n : Nat} (Γ : Tower.Ctx n) :
    Typed Tower.rules Γ (.pi u0 u1)
      (.head (.sort (.max (.succ Tower.zero) (.succ (.succ Tower.zero))))) :=
  .piForm (.headType (.sort _)) (.sort _) (.headType (.sort _)) (.sort _) (.sorts _ _)

/-- `Π (x : U₁). U₁`, formed over the empty frame. -/
def bigArrow : TypeOver (empty Tower.rules) :=
  ⟨.pi u1 u1, .sort (.max (.succ (.succ Tower.zero)) (.succ (.succ Tower.zero))), .sort _, bigArrow_typed _⟩

/-- **The frame `h : Π (x : U₁). U₁`.** -/
abbrev hFrame : Context Tower.rules := extend (empty Tower.rules) bigArrow

/-- `Π (x : U₀). U₁`, formed over the frame. -/
def smallArrow : TypeOver hFrame :=
  ⟨.pi u0 u1, .sort (.max (.succ Tower.zero) (.succ (.succ Tower.zero))), .sort _, smallArrow_typed _⟩

/-! ## The η-expansion -/

/-- The η-expansion `λ x. h x`. -/
def etaCode : Tower.Tm 1 := .lam (.app (.var 1) (.var 0))

/-- `λ x. h x : Π (x : U₁). U₁`. -/
theorem etaCode_typed_big : Typed Tower.rules hFrame.raw etaCode (.pi u1 u1) :=
  .lamIntro (bigArrow_typed _) (.sort _) (.appElim (A := u1) (B := u1) (.var 1) (.var 0))

/-- **`λ x. h x : Π (x : U₀). U₁`**: the bound variable is chosen at `U₀` and used at `U₁`. -/
theorem etaCode_typed_small : Typed Tower.rules hFrame.raw etaCode (.pi u0 u1) :=
  .lamIntro (smallArrow_typed _) (.sort _)
    (.appElim (A := u1) (B := u1) (.var 1) (.cumul (.var 0) (fun _ => Nat.le_succ _)))

/-- The substitution `h ↦ λ x. h x`. -/
def etaHom : hFrame ⟶ hFrame :=
  pair (toEmpty hFrame) ⟨etaCode, etaCode_typed_big⟩

/-- **`h` and its η-expansion are equal**: the identity and `etaHom` are equal substitutions. -/
theorem etaHom_substEq : homTypedEquality Tower.rules (𝟙 hFrame) etaHom := by
  refine ⟨identityTyped hFrame.raw, fun index => ?_⟩
  fin_cases index
  show Equal Tower.rules hFrame.raw (.var 0) etaCode (.pi u1 u1)
  have beta : Equal Tower.rules (.snoc hFrame.raw u1)
      (.app (.lam (.app (.var 2) (.var 0))) (.var 0)) (.app (.var 1) (.var 0)) u1 :=
    .betaPi (A := u1) (B := u1) (body := .app (.var 2) (.var 0)) (a := .var 0)
      (bigArrow_typed _) (.sort _) (.appElim (A := u1) (B := u1) (.var 2) (.var 0)) (.var 0)
  exact .etaPi (.var 0) etaCode_typed_big (.symm beta)

/-- **The identity and the η-expansion agree** on every judged term. -/
theorem etaHom_agree : Agree (frames setting.levels) (𝟙 hFrame) etaHom :=
  fun t => act_equal_of_substEq setting.levels etaHom_substEq t

/-- **The η-expansion is an initial solution of the empty store**, as the identity is. -/
theorem eta_initial :
    InitialSolution (frames setting.levels) ([] : EquationStore (TotalTerm hFrame)) etaHom :=
  initial_nil_of_agree setting.levels etaHom_agree

theorem identity_initial :
    InitialSolution (frames setting.levels) ([] : EquationStore (TotalTerm hFrame)) (𝟙 hFrame) :=
  initial_nil_of_agree setting.levels (UnificationWithLevels.Agree.refl _)

/-! ## The row `h : Π (x : U₀). U₁` -/

/-- **The made row**: `h` at `Π (x : U₀). U₁`. -/
def etaRow : Make hFrame := ⟨smallArrow, .var 0⟩

/-- **Typed at the η-expansion.** -/
theorem etaRow_typed_at_eta : (etaRow.reindex etaHom).WellTyped := etaCode_typed_small

/-- **Not typed in its frame, that is at the identity**: `Π (x : U₁). U₁` is not usable at
`Π (x : U₀). U₁`, since that would make `U₁` and `U₀` equal types. -/
theorem etaRow_not_wellTyped : ¬ etaRow.WellTyped := by
  intro typed
  have le : TypeLe Tower.rules hFrame.raw (.pi u1 u1) (.pi u0 u1) := Typed.generation typed
  have formed : CtxFormed Tower.rules hFrame.raw := hFrame.formed
  have below : Below Tower.rules hFrame.raw (.pi u1 u1) (.pi u0 u1) :=
    TypeLe.toBelow le ⟨_, .sort _, smallArrow_typed _⟩
  obtain ⟨A', B', eT, eA, -⟩ := Below.pi_source (S := setting) TowerModel.facts below formed
    (IsType.refl ⟨_, .sort _, bigArrow_typed _⟩)
  obtain ⟨eDomain, -⟩ := LevelTower.pi_injective eT formed
  have universes : TypeEq Tower.rules hFrame.raw u1 u0 :=
    TypeEq.trans setting.levels eA eDomain.symm
  rcases LevelTower.head_injective universes formed with same | same
  · cases same
  · exact Nat.succ_ne_zero 0 (same fun _ => 0)

/-- **Typing is not closed under agreement in the βη tower**: the identity and `etaHom` agree and solve
the empty store, the row is typed at `etaHom` and not at the identity. -/
theorem etaRow_not_closed :
    ¬ ClosedUnderAgreement setting.levels ([] : EquationStore (TotalTerm hFrame)) etaRow := by
  intro closed
  have atIdentity := closed hFrame (𝟙 hFrame) etaHom (Frames.models_nil _) etaHom_agree
    ((mem_typing_iff_reindex etaRow etaHom).mpr etaRow_typed_at_eta)
  apply etaRow_not_wellTyped
  have typed := (mem_typing_iff_reindex etaRow (𝟙 hFrame)).mp atIdentity
  rwa [Make.reindex_id'] at typed

/-- **The gap between the two semantic rules is real**: the row is typed up to agreement after the
empty match, and not typed after it. -/
theorem eta_gap :
    TypedUpToAgreement setting.levels ([] : EquationStore (TotalTerm hFrame)) etaRow ∧
      ¬ TypedAfterMatch setting.levels ([] : EquationStore (TotalTerm hFrame)) etaRow :=
  ⟨settled_sound setting.levels (principal_of_initial setting.levels eta_initial) etaRow_typed_at_eta,
    fun typed => etaRow_not_wellTyped ((typedAfterMatch_nil_iff setting.levels etaRow).mp typed)⟩

/-! ## The settling step admits it along the η-expansion -/

/-- Make the helper `h : Π (x : U₁). U₁` and the row `1 : h : Π (x : U₀). U₁`; tell nothing. -/
def etaFiring : Firing setting.levels emptyState where
  helpers := .cons bigArrow (.nil _)
  taken := []
  read := []
  takes := []
  reads := []
  makes := [(1, etaRow)]
  tells := []
  guards := []
  queries := []

theorem etaFiring_information : etaFiring.information = [] := rfl

theorem etaFiring_not_frameTyped : ¬ FrameTyped setting.levels etaFiring :=
  fun typed => etaRow_not_wellTyped (typed (1, etaRow) (List.mem_singleton_self _))

/-- The settler that settles the empty store of `h : Π (x : U₁). U₁` along the η-expansion. -/
noncomputable def etaSettler : Settler setting.levels :=
  Settler.pointed setting.levels ([] : EquationStore (TotalTerm hFrame)) etaHom eta_initial

/-- The settler that settles the same store along the identity. -/
noncomputable def identitySettler : Settler setting.levels :=
  Settler.pointed setting.levels ([] : EquationStore (TotalTerm hFrame)) (𝟙 hFrame) identity_initial

theorem eta_plan : plan setting.levels etaSettler etaFiring = ⟨hFrame, etaHom⟩ := by
  rw [plan_of_not_frameTyped setting.levels etaSettler etaFiring_not_frameTyped]
  show (etaSettler ([] : EquationStore (TotalTerm hFrame))).along = _
  exact congrArg Verdict.along (Settler.pointed_self setting.levels _ etaHom eta_initial)

theorem identity_plan : plan setting.levels identitySettler etaFiring = ⟨hFrame, 𝟙 hFrame⟩ := by
  rw [plan_of_not_frameTyped setting.levels identitySettler etaFiring_not_frameTyped]
  show (identitySettler ([] : EquationStore (TotalTerm hFrame))).along = _
  exact congrArg Verdict.along (Settler.pointed_self setting.levels _ (𝟙 hFrame) identity_initial)

/-- **Settled along the η-expansion, the firing is admitted.** -/
theorem eta_settled_admitted : (settlingStep setting.levels Nat etaSettler).Admits etaFiring := by
  refine ⟨⟨List.nodup_nil, List.nodup_singleton _, rfl, rfl, fun m member => ?_⟩,
    (DependentFull.enabled_iff etaFiring).mpr ⟨fun _ member => absurd member List.not_mem_nil,
      fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil,
      fun o made present => ?_⟩, ⟨hFrame, 𝟙 hFrame, Frames.models_nil _⟩, ?_⟩
  · obtain rfl := List.mem_singleton.mp member
    rw [eta_plan]
    exact etaRow_typed_at_eta
  · have one : o = 1 := List.mem_singleton.mp made
    have zero : o = 0 := Finset.mem_singleton.mp present
    exact absurd (one.symm.trans zero) (by decide)
  · intro _ _ _
    exact ⟨fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil⟩

/-- **The settling step is sound only up to agreement**: with a settler whose verdict is an initial
solution, it admits a firing whose made row is not typed after the match. -/
theorem settling_not_sound :
    (settlingStep setting.levels Nat etaSettler).Admits etaFiring ∧
      ¬ ∀ m ∈ etaFiring.makes, TypedAfterMatch setting.levels etaFiring.information m.2 :=
  ⟨eta_settled_admitted, fun typed => eta_gap.2 (typed (1, etaRow) (List.mem_singleton_self _))⟩

/-- ... and the firing is not admitted after the match. -/
theorem eta_not_admittedAfterMatch : ¬ AdmitsAfterMatch setting.levels etaFiring :=
  fun admitted => eta_gap.2 (admitted.1.2.2.2.2 (1, etaRow) (List.mem_singleton_self _))

/-- **Control: settled along the identity, the same firing is refused.** -/
theorem identity_refuses : ¬ (settlingStep setting.levels Nat identitySettler).Admits etaFiring := by
  rintro ⟨⟨-, -, -, -, typed⟩, -⟩
  have atIdentity := typed (1, etaRow) (List.mem_singleton_self _)
  rw [identity_plan] at atIdentity
  exact etaRow_not_wellTyped atIdentity

/-- **Control: the present step refuses it**, so does the settler that never settles. -/
theorem never_refuses_eta :
    ¬ (settlingStep setting.levels Nat (Settler.never setting.levels)).Admits etaFiring := by
  intro admitted
  obtain ⟨⟨-, -, -, -, typed⟩, -⟩ := (never_admits_iff setting.levels etaFiring).mp admitted
  exact etaRow_not_wellTyped (typed (1, etaRow) (List.mem_singleton_self _))

/-- **Admission of the settling step depends on the representative**: two settlers whose verdicts on
the same store are agreeing initial solutions disagree on the firing. -/
theorem representative_dependence :
    Agree (frames setting.levels) (𝟙 hFrame) etaHom ∧
      (settlingStep setting.levels Nat etaSettler).Admits etaFiring ∧
      ¬ (settlingStep setting.levels Nat identitySettler).Admits etaFiring :=
  ⟨etaHom_agree, eta_settled_admitted, identity_refuses⟩

end Eta

end NativeTypesOnTheStep

#print axioms NativeTypesOnTheStep.Settler.pointed_self
#print axioms NativeTypesOnTheStep.initial_nil_of_agree
#print axioms NativeTypesOnTheStep.Eta.etaCode_typed_small
#print axioms NativeTypesOnTheStep.Eta.etaHom_substEq
#print axioms NativeTypesOnTheStep.Eta.etaHom_agree
#print axioms NativeTypesOnTheStep.Eta.eta_initial
#print axioms NativeTypesOnTheStep.Eta.etaRow_typed_at_eta
#print axioms NativeTypesOnTheStep.Eta.etaRow_not_wellTyped
#print axioms NativeTypesOnTheStep.Eta.etaRow_not_closed
#print axioms NativeTypesOnTheStep.Eta.eta_gap
#print axioms NativeTypesOnTheStep.Eta.eta_settled_admitted
#print axioms NativeTypesOnTheStep.Eta.settling_not_sound
#print axioms NativeTypesOnTheStep.Eta.eta_not_admittedAfterMatch
#print axioms NativeTypesOnTheStep.Eta.identity_refuses
#print axioms NativeTypesOnTheStep.Eta.never_refuses_eta
#print axioms NativeTypesOnTheStep.Eta.representative_dependence

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
