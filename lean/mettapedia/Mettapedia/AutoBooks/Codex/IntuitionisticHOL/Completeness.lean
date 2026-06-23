import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.Hintikka
import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.Soundness

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL

open Mettapedia.Logic.HOL

universe u v w w'

variable {Base : Type u} {Const : Ty Base → Type v}

/-- Frontier object for the future saturation-to-countermodel route. -/
structure CompletenessFrontier (Const : Ty Base → Type v) (Γ : Ctx Base) where
  antecedents : List (Formula Const Γ)
  succedent : Formula Const Γ

/-- Native staged search state connecting the original frontier to the signed
Hintikka-style saturation data currently under construction. -/
structure SaturationSearchState (Const : Ty Base → Type v) (Γ : Ctx Base) where
  frontier : CompletenessFrontier Const Γ
  hintikka : HintikkaSet Const Γ
  agenda : List (LocalBranchTarget Const Γ)

namespace SaturationSearchState

/-- A chosen local branch together with proof that it genuinely resolves the
stated branching target. -/
structure LocalBranchResolution (Const : Ty Base → Type v) (Γ : Ctx Base) where
  target : LocalBranchTarget Const Γ
  step : LocalSaturationStep Const Γ
  admissible : target.AcceptsStep step

namespace LocalBranchResolution

theorem exists_addition (r : LocalBranchResolution Const Γ) :
    ∃ sf : SignedFormula Const Γ, LocalSaturationStep.additions r.step = [sf] := by
  cases r with
  | mk target step admissible =>
      cases target <;> cases step <;>
        simp [LocalBranchTarget.AcceptsStep, LocalBranchTarget.branches,
          LocalSaturationStep.additions] at admissible ⊢

end LocalBranchResolution

/-- An honest local saturation move whose triggering premise is already active
in the current staged Hintikka set. -/
structure TriggeredLocalStep (S : SaturationSearchState Const Γ) where
  step : DeterministicLocalSaturationStep Const Γ
  active : DeterministicLocalSaturationStep.premise step ∈ S.hintikka.formulas

/-- A triggered local saturation move that genuinely contributes at least one
new signed formula to the current staged Hintikka set. -/
structure ProductiveTriggeredLocalStep (S : SaturationSearchState Const Γ) where
  step : DeterministicLocalSaturationStep Const Γ
  active : DeterministicLocalSaturationStep.premise step ∈ S.hintikka.formulas
  fresh : ∃ sf ∈ DeterministicLocalSaturationStep.additions step, sf ∉ S.hintikka.formulas

namespace ProductiveTriggeredLocalStep

/-- Forget productivity and keep only the underlying honest triggered step. -/
def toTriggeredLocalStep {S : SaturationSearchState Const Γ}
    (t : ProductiveTriggeredLocalStep S) : TriggeredLocalStep S :=
  { step := t.step
    active := t.active }

end ProductiveTriggeredLocalStep

/-- A canonical focus on one pending agenda item, exposing the exact prefix and
suffix around the chosen target. -/
structure AgendaFocus (S : SaturationSearchState Const Γ) where
  before : List (LocalBranchTarget Const Γ)
  target : LocalBranchTarget Const Γ
  after : List (LocalBranchTarget Const Γ)
  decompose : S.agenda = before ++ target :: after

namespace AgendaFocus

/-- The agenda remaining after removing the focused target. -/
def remaining {S : SaturationSearchState Const Γ} (f : AgendaFocus S) :
    List (LocalBranchTarget Const Γ) :=
  f.before ++ f.after

theorem target_mem_agenda {S : SaturationSearchState Const Γ} (f : AgendaFocus S) :
    f.target ∈ S.agenda := by
  rw [f.decompose]
  simp

theorem mem_agenda_of_mem_remaining {S : SaturationSearchState Const Γ}
    (f : AgendaFocus S) {b : LocalBranchTarget Const Γ}
    (h : b ∈ f.remaining) :
    b ∈ S.agenda := by
  rw [f.decompose]
  unfold remaining at h
  rcases List.mem_append.mp h with h | h
  · exact List.mem_append.mpr <| Or.inl h
  · exact List.mem_append.mpr <| Or.inr (List.mem_cons_of_mem _ h)

end AgendaFocus

/-- Start the search state from the initial signed frontier of a completeness goal. -/
def initial (F : CompletenessFrontier Const Γ) : SaturationSearchState Const Γ :=
  let H : HintikkaSet Const Γ :=
    { formulas :=
        F.antecedents.map (fun φ => (Sign.trueE, φ)) ++ [(Sign.falseE, F.succedent)] }
  { frontier := F
    hintikka := H
    agenda := H.localBranchTargets }

/-- Apply one local saturation step by adding its prescribed formulas to the
current Hintikka staging list and collecting any newly exposed local branching
obligations. Resolution/removal of agenda entries is deferred to the later
branch-management layer. -/
def applyLocalStep (S : SaturationSearchState Const Γ) (s : LocalSaturationStep Const Γ) :
    SaturationSearchState Const Γ :=
  let H' := S.hintikka.saturateWithStep s
  { frontier := S.frontier
    hintikka := H'
    agenda := S.agenda ++
      (LocalSaturationStep.additions s).foldr
        (fun sf acc => LocalBranchTarget.ofSignedFormula sf ++ acc) [] }

/-- The next local branching target, when any remain in the agenda. -/
def nextAgendaTarget? (S : SaturationSearchState Const Γ) : Option (LocalBranchTarget Const Γ) :=
  S.agenda.head?

/-- A resolution matches the current agenda head when its target is exactly the
next pending local branching obligation. -/
def CanResolveHead (S : SaturationSearchState Const Γ)
    (r : LocalBranchResolution Const Γ) : Prop :=
  S.nextAgendaTarget? = some r.target

/-- A resolution matches a focused agenda item when it resolves exactly that
chosen target. -/
def CanResolveFocus (S : SaturationSearchState Const Γ)
    (f : AgendaFocus S) (r : LocalBranchResolution Const Γ) : Prop :=
  r.target = f.target

/-- Every pending agenda item is justified by a signed formula that is already
visible in the staged Hintikka set. -/
def AgendaVisible (S : SaturationSearchState Const Γ) : Prop :=
  ∀ b ∈ S.agenda, b.premise ∈ S.hintikka.formulas

/-- A productive deterministic saturation move is compatible with the current
closed hull when each added formula avoids its flipped counterpart there. -/
def DeterministicAdditionCompatible (S : SaturationSearchState Const Γ)
    (s : DeterministicLocalSaturationStep Const Γ) : Prop :=
  ∀ {sf : SignedFormula Const Γ},
    sf ∈ DeterministicLocalSaturationStep.additions s →
      SignedFormula.flip sf ∉ S.hintikka.close.formulas

/-- A chosen local branch is compatible with the current closed hull when each
formula it adds avoids its flipped counterpart in the already closed Hintikka
set. For genuine branch resolutions this is a singleton compatibility check. -/
def BranchAdditionCompatible (S : SaturationSearchState Const Γ)
    (r : LocalBranchResolution Const Γ) : Prop :=
  ∀ {sf : SignedFormula Const Γ},
    sf ∈ LocalSaturationStep.additions r.step →
      SignedFormula.flip sf ∉ S.hintikka.close.formulas

theorem deterministicAdditionCompatible_trueAnd_iff
    (S : SaturationSearchState Const Γ)
    {φ ψ : Formula Const Γ} :
    S.DeterministicAdditionCompatible (.trueAnd φ ψ) ↔
      (Sign.falseE, φ) ∉ S.hintikka.close.formulas ∧
        (Sign.falseE, ψ) ∉ S.hintikka.close.formulas := by
  simp [DeterministicAdditionCompatible, DeterministicLocalSaturationStep.additions,
    DeterministicLocalSaturationStep.toLocalSaturationStep, LocalSaturationStep.additions,
    SignedFormula.flip, Sign.flip]
  rfl

theorem deterministicAdditionCompatible_falseOr_iff
    (S : SaturationSearchState Const Γ)
    {φ ψ : Formula Const Γ} :
    S.DeterministicAdditionCompatible (.falseOr φ ψ) ↔
      (Sign.trueE, φ) ∉ S.hintikka.close.formulas ∧
        (Sign.trueE, ψ) ∉ S.hintikka.close.formulas := by
  simp [DeterministicAdditionCompatible, DeterministicLocalSaturationStep.additions,
    DeterministicLocalSaturationStep.toLocalSaturationStep, LocalSaturationStep.additions,
    SignedFormula.flip, Sign.flip]
  rfl

theorem deterministicAdditionCompatible_trueAll_iff
    (S : SaturationSearchState Const Γ)
    {σ : Ty Base} {φ : Formula Const (σ :: Γ)} {t : Term Const Γ σ} :
    S.DeterministicAdditionCompatible (.trueAll φ t) ↔
      (Sign.falseE, instantiate (Base := Base) t φ) ∉ S.hintikka.close.formulas := by
  simp [DeterministicAdditionCompatible, DeterministicLocalSaturationStep.additions,
    DeterministicLocalSaturationStep.toLocalSaturationStep, LocalSaturationStep.additions,
    SignedFormula.flip, Sign.flip]
  rfl

theorem deterministicAdditionCompatible_falseAllWitness_iff
    (S : SaturationSearchState Const Γ)
    {σ : Ty Base} {φ : Formula Const (σ :: Γ)} {t : Term Const Γ σ} :
    S.DeterministicAdditionCompatible (.falseAllWitness φ t) ↔
      (Sign.trueE, instantiate (Base := Base) t φ) ∉ S.hintikka.close.formulas := by
  simp [DeterministicAdditionCompatible, DeterministicLocalSaturationStep.additions,
    DeterministicLocalSaturationStep.toLocalSaturationStep, LocalSaturationStep.additions,
    SignedFormula.flip, Sign.flip]
  rfl

theorem deterministicAdditionCompatible_trueExWitness_iff
    (S : SaturationSearchState Const Γ)
    {σ : Ty Base} {φ : Formula Const (σ :: Γ)} {t : Term Const Γ σ} :
    S.DeterministicAdditionCompatible (.trueExWitness φ t) ↔
      (Sign.falseE, instantiate (Base := Base) t φ) ∉ S.hintikka.close.formulas := by
  simp [DeterministicAdditionCompatible, DeterministicLocalSaturationStep.additions,
    DeterministicLocalSaturationStep.toLocalSaturationStep, LocalSaturationStep.additions,
    SignedFormula.flip, Sign.flip]
  rfl

theorem deterministicAdditionCompatible_falseEx_iff
    (S : SaturationSearchState Const Γ)
    {σ : Ty Base} {φ : Formula Const (σ :: Γ)} {t : Term Const Γ σ} :
    S.DeterministicAdditionCompatible (.falseEx φ t) ↔
      (Sign.trueE, instantiate (Base := Base) t φ) ∉ S.hintikka.close.formulas := by
  simp [DeterministicAdditionCompatible, DeterministicLocalSaturationStep.additions,
    DeterministicLocalSaturationStep.toLocalSaturationStep, LocalSaturationStep.additions,
    SignedFormula.flip, Sign.flip]
  rfl

theorem branchAdditionCompatible_iff_of_singleton_addition
    (S : SaturationSearchState Const Γ)
    {r : LocalBranchResolution Const Γ} {sf : SignedFormula Const Γ}
    (hadd : LocalSaturationStep.additions r.step = [sf]) :
    S.BranchAdditionCompatible r ↔
      SignedFormula.flip sf ∉ S.hintikka.close.formulas := by
  constructor
  · intro hCompat
    exact hCompat (by simp [hadd])
  · intro hFlip sf' hsf'
    have hEq : sf' = sf := by
      simp [hadd] at hsf'
      exact hsf'
    subst hEq
    exact hFlip

theorem deterministicAdditionCompatible_trueAnd
    (S : SaturationSearchState Const Γ)
    {φ ψ : Formula Const Γ}
    (hφ : (Sign.falseE, φ) ∉ S.hintikka.close.formulas)
    (hψ : (Sign.falseE, ψ) ∉ S.hintikka.close.formulas) :
    S.DeterministicAdditionCompatible (.trueAnd φ ψ) :=
  (deterministicAdditionCompatible_trueAnd_iff S).2 ⟨hφ, hψ⟩

theorem deterministicAdditionCompatible_falseOr
    (S : SaturationSearchState Const Γ)
    {φ ψ : Formula Const Γ}
    (hφ : (Sign.trueE, φ) ∉ S.hintikka.close.formulas)
    (hψ : (Sign.trueE, ψ) ∉ S.hintikka.close.formulas) :
    S.DeterministicAdditionCompatible (.falseOr φ ψ) :=
  (deterministicAdditionCompatible_falseOr_iff S).2 ⟨hφ, hψ⟩

theorem deterministicAdditionCompatible_trueAll
    (S : SaturationSearchState Const Γ)
    {σ : Ty Base} {φ : Formula Const (σ :: Γ)} {t : Term Const Γ σ}
    (h :
      (Sign.falseE, instantiate (Base := Base) t φ) ∉ S.hintikka.close.formulas) :
    S.DeterministicAdditionCompatible (.trueAll φ t) :=
  (deterministicAdditionCompatible_trueAll_iff S).2 h

theorem not_deterministicAdditionCompatible_trueAll
    (S : SaturationSearchState Const Γ)
    {σ : Ty Base} {φ : Formula Const (σ :: Γ)} {t : Term Const Γ σ}
    (h :
      (Sign.falseE, instantiate (Base := Base) t φ) ∈ S.hintikka.close.formulas) :
    ¬ S.DeterministicAdditionCompatible (.trueAll φ t) := by
  rw [deterministicAdditionCompatible_trueAll_iff]
  simpa using h

theorem deterministicAdditionCompatible_falseAllWitness
    (S : SaturationSearchState Const Γ)
    {σ : Ty Base} {φ : Formula Const (σ :: Γ)} {t : Term Const Γ σ}
    (h :
      (Sign.trueE, instantiate (Base := Base) t φ) ∉ S.hintikka.close.formulas) :
    S.DeterministicAdditionCompatible (.falseAllWitness φ t) :=
  (deterministicAdditionCompatible_falseAllWitness_iff S).2 h

theorem not_deterministicAdditionCompatible_falseAllWitness
    (S : SaturationSearchState Const Γ)
    {σ : Ty Base} {φ : Formula Const (σ :: Γ)} {t : Term Const Γ σ}
    (h :
      (Sign.trueE, instantiate (Base := Base) t φ) ∈ S.hintikka.close.formulas) :
    ¬ S.DeterministicAdditionCompatible (.falseAllWitness φ t) := by
  rw [deterministicAdditionCompatible_falseAllWitness_iff]
  simpa using h

theorem deterministicAdditionCompatible_trueExWitness
    (S : SaturationSearchState Const Γ)
    {σ : Ty Base} {φ : Formula Const (σ :: Γ)} {t : Term Const Γ σ}
    (h :
      (Sign.falseE, instantiate (Base := Base) t φ) ∉ S.hintikka.close.formulas) :
    S.DeterministicAdditionCompatible (.trueExWitness φ t) :=
  (deterministicAdditionCompatible_trueExWitness_iff S).2 h

theorem not_deterministicAdditionCompatible_trueExWitness
    (S : SaturationSearchState Const Γ)
    {σ : Ty Base} {φ : Formula Const (σ :: Γ)} {t : Term Const Γ σ}
    (h :
      (Sign.falseE, instantiate (Base := Base) t φ) ∈ S.hintikka.close.formulas) :
    ¬ S.DeterministicAdditionCompatible (.trueExWitness φ t) := by
  rw [deterministicAdditionCompatible_trueExWitness_iff]
  simpa using h

theorem deterministicAdditionCompatible_falseEx
    (S : SaturationSearchState Const Γ)
    {σ : Ty Base} {φ : Formula Const (σ :: Γ)} {t : Term Const Γ σ}
    (h :
      (Sign.trueE, instantiate (Base := Base) t φ) ∉ S.hintikka.close.formulas) :
    S.DeterministicAdditionCompatible (.falseEx φ t) :=
  (deterministicAdditionCompatible_falseEx_iff S).2 h

theorem not_deterministicAdditionCompatible_falseEx
    (S : SaturationSearchState Const Γ)
    {σ : Ty Base} {φ : Formula Const (σ :: Γ)} {t : Term Const Γ σ}
    (h :
      (Sign.trueE, instantiate (Base := Base) t φ) ∈ S.hintikka.close.formulas) :
    ¬ S.DeterministicAdditionCompatible (.falseEx φ t) := by
  rw [deterministicAdditionCompatible_falseEx_iff]
  simpa using h

theorem branchAdditionCompatible_falseAndLeft_iff
    (S : SaturationSearchState Const Γ)
    {r : LocalBranchResolution Const Γ} {φ ψ : Formula Const Γ}
    (hstep : r.step = .falseAndLeft φ ψ) :
    S.BranchAdditionCompatible r ↔
      (Sign.trueE, φ) ∉ S.hintikka.close.formulas := by
  rw [branchAdditionCompatible_iff_of_singleton_addition
    (S := S) (r := r) (sf := (Sign.falseE, φ))]
  · simp [SignedFormula.flip, Sign.flip]
    rfl
  · simp [hstep, LocalSaturationStep.additions]

theorem branchAdditionCompatible_falseAndRight_iff
    (S : SaturationSearchState Const Γ)
    {r : LocalBranchResolution Const Γ} {φ ψ : Formula Const Γ}
    (hstep : r.step = .falseAndRight φ ψ) :
    S.BranchAdditionCompatible r ↔
      (Sign.trueE, ψ) ∉ S.hintikka.close.formulas := by
  rw [branchAdditionCompatible_iff_of_singleton_addition
    (S := S) (r := r) (sf := (Sign.falseE, ψ))]
  · simp [SignedFormula.flip, Sign.flip]
    rfl
  · simp [hstep, LocalSaturationStep.additions]

theorem branchAdditionCompatible_trueOrLeft_iff
    (S : SaturationSearchState Const Γ)
    {r : LocalBranchResolution Const Γ} {φ ψ : Formula Const Γ}
    (hstep : r.step = .trueOrLeft φ ψ) :
    S.BranchAdditionCompatible r ↔
      (Sign.falseE, φ) ∉ S.hintikka.close.formulas := by
  rw [branchAdditionCompatible_iff_of_singleton_addition
    (S := S) (r := r) (sf := (Sign.trueE, φ))]
  · simp [SignedFormula.flip, Sign.flip]
    rfl
  · simp [hstep, LocalSaturationStep.additions]

theorem branchAdditionCompatible_trueOrRight_iff
    (S : SaturationSearchState Const Γ)
    {r : LocalBranchResolution Const Γ} {φ ψ : Formula Const Γ}
    (hstep : r.step = .trueOrRight φ ψ) :
    S.BranchAdditionCompatible r ↔
      (Sign.falseE, ψ) ∉ S.hintikka.close.formulas := by
  rw [branchAdditionCompatible_iff_of_singleton_addition
    (S := S) (r := r) (sf := (Sign.trueE, ψ))]
  · simp [SignedFormula.flip, Sign.flip]
    rfl
  · simp [hstep, LocalSaturationStep.additions]

/-- Consume a chosen focused agenda item by removing exactly that target and
appending any newly exposed obligations from the chosen local saturation step. -/
def resolveFocused (S : SaturationSearchState Const Γ)
    (f : AgendaFocus S) (r : LocalBranchResolution Const Γ)
    (_hfocus : S.CanResolveFocus f r) :
    SaturationSearchState Const Γ :=
  let H' := S.hintikka.saturateWithStep r.step
  { frontier := S.frontier
    hintikka := H'
    agenda := f.remaining ++
      (LocalSaturationStep.additions r.step).foldr
        (fun sf acc => LocalBranchTarget.ofSignedFormula sf ++ acc) [] }

/-- A single honest completeness-side search move from the current staged state:
either saturate using an already active local premise, or resolve one chosen
focused branching obligation. -/
inductive SearchStep (S : SaturationSearchState Const Γ) where
  | saturate (t : TriggeredLocalStep S)
  | resolve (f : AgendaFocus S) (r : LocalBranchResolution Const Γ)
      (hfocus : S.CanResolveFocus f r)

namespace SearchStep

/-- The successor state reached by executing one honest local search move. -/
def next {S : SaturationSearchState Const Γ} : SearchStep S → SaturationSearchState Const Γ
  | .saturate t => S.applyLocalStep t.step.toLocalSaturationStep
  | .resolve f r hfocus => S.resolveFocused f r hfocus

end SearchStep

/-- State-to-state transition relation generated by one honest local search move. -/
def SearchTransition (S T : SaturationSearchState Const Γ) : Prop :=
  ∃ a : SearchStep S, a.next = T

/-- Finite reachability in the current local completeness search discipline. -/
abbrev SearchReachable (S T : SaturationSearchState Const Γ) : Prop :=
  Relation.ReflTransGen SearchTransition S T

/-- Consume the current agenda head by applying an admissible local branch
resolution, dropping that head target, and appending any new obligations
exposed by the formulas added in the chosen step. -/
def resolveHead (S : SaturationSearchState Const Γ)
    (r : LocalBranchResolution Const Γ) (_hhead : S.CanResolveHead r) :
    SaturationSearchState Const Γ :=
  let H' := S.hintikka.saturateWithStep r.step
  let remaining :=
    match S.agenda with
    | [] => []
    | _ :: tl => tl
  { frontier := S.frontier
    hintikka := H'
    agenda := remaining ++
      (LocalSaturationStep.additions r.step).foldr
        (fun sf acc => LocalBranchTarget.ofSignedFormula sf ++ acc) [] }

theorem true_mem_initial {F : CompletenessFrontier Const Γ}
    {φ : Formula Const Γ} (h : φ ∈ F.antecedents) :
    (Sign.trueE, φ) ∈ (initial F).hintikka.formulas :=
by
  apply List.mem_append.mpr
  left
  exact List.mem_map.mpr ⟨φ, h, rfl⟩

theorem false_mem_initial (F : CompletenessFrontier Const Γ) :
    (Sign.falseE, F.succedent) ∈ (initial F).hintikka.formulas :=
by
  apply List.mem_append.mpr
  right
  simp

theorem mem_applyLocalStep_of_mem {S : SaturationSearchState Const Γ}
    {s : LocalSaturationStep Const Γ} {sf : SignedFormula Const Γ}
    (h : sf ∈ S.hintikka.formulas) :
    sf ∈ (applyLocalStep S s).hintikka.formulas :=
  HintikkaSet.mem_saturateWithStep_of_mem h

theorem mem_applyLocalStep_of_addition {S : SaturationSearchState Const Γ}
    {s : LocalSaturationStep Const Γ} {sf : SignedFormula Const Γ}
    (h : sf ∈ LocalSaturationStep.additions s) :
    sf ∈ (applyLocalStep S s).hintikka.formulas :=
  HintikkaSet.mem_saturateWithStep_of_addition h

theorem exists_fresh_formula_of_productiveTriggeredLocalStep
    {S : SaturationSearchState Const Γ}
    (t : ProductiveTriggeredLocalStep S) :
    ∃ sf,
      sf ∈ (applyLocalStep S t.step.toLocalSaturationStep).hintikka.formulas ∧
        sf ∉ S.hintikka.formulas := by
  rcases t.fresh with ⟨sf, hsf, hnot⟩
  exact ⟨sf, mem_applyLocalStep_of_addition (by
    simpa [DeterministicLocalSaturationStep.additions] using hsf), hnot⟩

theorem mem_resolveHead_of_mem {S : SaturationSearchState Const Γ}
    {r : LocalBranchResolution Const Γ} {hhead : S.CanResolveHead r}
    {sf : SignedFormula Const Γ}
    (h : sf ∈ S.hintikka.formulas) :
    sf ∈ (resolveHead S r hhead).hintikka.formulas :=
  HintikkaSet.mem_saturateWithStep_of_mem h

theorem mem_resolveHead_of_addition {S : SaturationSearchState Const Γ}
    {r : LocalBranchResolution Const Γ} {hhead : S.CanResolveHead r}
    {sf : SignedFormula Const Γ}
    (h : sf ∈ LocalSaturationStep.additions r.step) :
    sf ∈ (resolveHead S r hhead).hintikka.formulas :=
  HintikkaSet.mem_saturateWithStep_of_addition h

theorem closed_noncontradictory_applyLocalStep_of_deterministicAdditionCompatible
    {S : SaturationSearchState Const Γ}
    (hNoncontradictory : S.hintikka.close.Noncontradictory)
    {s : DeterministicLocalSaturationStep Const Γ}
    (hCompat : S.DeterministicAdditionCompatible s) :
    (applyLocalStep S s.toLocalSaturationStep).hintikka.close.Noncontradictory := by
  simpa [applyLocalStep, HintikkaSet.saturateWithStep, HintikkaSet.insertAll,
    DeterministicLocalSaturationStep.additions] using
    (HintikkaSet.noncontradictory_close_insertAll_of_flip_not_mem
      (H := S.hintikka)
      (Δ := DeterministicLocalSaturationStep.additions s)
      hNoncontradictory
      (hCompat := by
        intro sf hsf
        exact hCompat hsf)
      (hInternal := by
        intro sf hsf
        exact DeterministicLocalSaturationStep.flip_not_mem_additions_of_mem
          (s := s) hsf))

theorem closed_noncontradictory_resolveHead_of_branchAdditionCompatible
    {S : SaturationSearchState Const Γ}
    (hNoncontradictory : S.hintikka.close.Noncontradictory)
    {r : LocalBranchResolution Const Γ} {hhead : S.CanResolveHead r}
    (hCompat : S.BranchAdditionCompatible r) :
    (resolveHead S r hhead).hintikka.close.Noncontradictory := by
  rcases LocalBranchResolution.exists_addition r with ⟨sf, hsf⟩
  have hFlip : SignedFormula.flip sf ∉ S.hintikka.close.formulas := by
    have hMem : sf ∈ LocalSaturationStep.additions r.step := by
      simp [hsf]
    exact hCompat hMem
  simpa [resolveHead, HintikkaSet.saturateWithStep, HintikkaSet.insertAll, hsf] using
    (HintikkaSet.noncontradictory_close_insertAll_singleton_of_flip_not_mem
      (H := S.hintikka) hNoncontradictory (sf := sf) hFlip)

theorem mem_resolveFocused_of_mem {S : SaturationSearchState Const Γ}
    {f : AgendaFocus S} {r : LocalBranchResolution Const Γ}
    {hfocus : S.CanResolveFocus f r} {sf : SignedFormula Const Γ}
    (h : sf ∈ S.hintikka.formulas) :
    sf ∈ (resolveFocused S f r hfocus).hintikka.formulas :=
  HintikkaSet.mem_saturateWithStep_of_mem h

theorem mem_resolveFocused_of_addition {S : SaturationSearchState Const Γ}
    {f : AgendaFocus S} {r : LocalBranchResolution Const Γ}
    {hfocus : S.CanResolveFocus f r} {sf : SignedFormula Const Γ}
    (h : sf ∈ LocalSaturationStep.additions r.step) :
    sf ∈ (resolveFocused S f r hfocus).hintikka.formulas :=
  HintikkaSet.mem_saturateWithStep_of_addition h

theorem agendaVisible_initial (F : CompletenessFrontier Const Γ) :
    (initial F).AgendaVisible := by
  intro b hb
  simpa [initial] using HintikkaSet.premise_mem_of_mem_localBranchTargets hb

theorem agendaVisible_applyLocalStep {S : SaturationSearchState Const Γ}
    (hS : S.AgendaVisible) (s : LocalSaturationStep Const Γ) :
    (applyLocalStep S s).AgendaVisible := by
  intro b hb
  rcases List.mem_append.mp hb with hb | hb
  · exact mem_applyLocalStep_of_mem (hS b hb)
  ·
    have hprem : b.premise ∈ LocalSaturationStep.additions s :=
      LocalBranchTarget.premise_mem_of_mem_targetsFrom hb
    exact mem_applyLocalStep_of_addition hprem

theorem agendaVisible_resolveHead {S : SaturationSearchState Const Γ}
    (hS : S.AgendaVisible)
    {r : LocalBranchResolution Const Γ} {hhead : S.CanResolveHead r} :
    (resolveHead S r hhead).AgendaVisible := by
  intro b hb
  rcases List.mem_append.mp hb with hb | hb
  ·
    have hold : b ∈ S.agenda := by
      cases hAgenda : S.agenda with
      | nil =>
          simp [hAgenda] at hb
      | cons a tl =>
          simp [hAgenda] at hb
          simp [hb]
    exact mem_resolveHead_of_mem (hS b hold)
  ·
    have hprem : b.premise ∈ LocalSaturationStep.additions r.step :=
      LocalBranchTarget.premise_mem_of_mem_targetsFrom hb
    exact mem_resolveHead_of_addition hprem

theorem agendaVisible_resolveFocused {S : SaturationSearchState Const Γ}
    (hS : S.AgendaVisible)
    {f : AgendaFocus S} {r : LocalBranchResolution Const Γ}
    {hfocus : S.CanResolveFocus f r} :
    (resolveFocused S f r hfocus).AgendaVisible := by
  intro b hb
  rcases List.mem_append.mp hb with hb | hb
  · exact mem_resolveFocused_of_mem (hS b (f.mem_agenda_of_mem_remaining hb))
  ·
    have hprem : b.premise ∈ LocalSaturationStep.additions r.step :=
      LocalBranchTarget.premise_mem_of_mem_targetsFrom hb
    exact mem_resolveFocused_of_addition hprem

theorem mem_agenda_of_canResolveHead {S : SaturationSearchState Const Γ}
    {r : LocalBranchResolution Const Γ}
    (hhead : S.CanResolveHead r) :
    r.target ∈ S.agenda := by
  cases hAgenda : S.agenda with
  | nil =>
      simp [CanResolveHead, nextAgendaTarget?, hAgenda] at hhead
  | cons a tl =>
      simp [CanResolveHead, nextAgendaTarget?, hAgenda] at hhead
      simp [hhead]

theorem premise_mem_of_canResolveHead {S : SaturationSearchState Const Γ}
    (hS : S.AgendaVisible)
    {r : LocalBranchResolution Const Γ}
    (hhead : S.CanResolveHead r) :
    r.target.premise ∈ S.hintikka.formulas :=
  hS r.target (mem_agenda_of_canResolveHead hhead)

theorem mem_agenda_of_canResolveFocus {S : SaturationSearchState Const Γ}
    {f : AgendaFocus S} {r : LocalBranchResolution Const Γ}
    (hfocus : S.CanResolveFocus f r) :
    r.target ∈ S.agenda := by
  rw [CanResolveFocus] at hfocus
  simpa [hfocus] using f.target_mem_agenda

theorem premise_mem_of_canResolveFocus {S : SaturationSearchState Const Γ}
    (hS : S.AgendaVisible)
    {f : AgendaFocus S} {r : LocalBranchResolution Const Γ}
    (hfocus : S.CanResolveFocus f r) :
    r.target.premise ∈ S.hintikka.formulas := by
  exact hS r.target (mem_agenda_of_canResolveFocus hfocus)

theorem stepPremise_mem_of_canResolveHead {S : SaturationSearchState Const Γ}
    (hS : S.AgendaVisible)
    {r : LocalBranchResolution Const Γ}
    (hhead : S.CanResolveHead r) :
    LocalSaturationStep.premise r.step ∈ S.hintikka.formulas := by
  have hprem : r.target.premise ∈ S.hintikka.formulas :=
    premise_mem_of_canResolveHead hS hhead
  simpa [LocalBranchTarget.premise_eq_of_acceptsStep r.admissible] using hprem

theorem stepPremise_mem_of_canResolveFocus {S : SaturationSearchState Const Γ}
    (hS : S.AgendaVisible)
    {f : AgendaFocus S} {r : LocalBranchResolution Const Γ}
    (hfocus : S.CanResolveFocus f r) :
    LocalSaturationStep.premise r.step ∈ S.hintikka.formulas := by
  have hprem : r.target.premise ∈ S.hintikka.formulas :=
    premise_mem_of_canResolveFocus hS hfocus
  simpa [LocalBranchTarget.premise_eq_of_acceptsStep r.admissible] using hprem

theorem searchStep_next_agendaVisible {S : SaturationSearchState Const Γ}
    (hS : S.AgendaVisible) (a : SearchStep S) :
    a.next.AgendaVisible := by
  cases a with
  | saturate t =>
      simpa [SearchStep.next] using
        agendaVisible_applyLocalStep hS t.step.toLocalSaturationStep
  | resolve f r hfocus =>
      simpa [SearchStep.next] using agendaVisible_resolveFocused hS (f := f) (r := r)
        (hfocus := hfocus)

theorem searchStep_stepPremise_mem {S : SaturationSearchState Const Γ}
    (hS : S.AgendaVisible) (a : SearchStep S) :
    match a with
    | .saturate t => DeterministicLocalSaturationStep.premise t.step ∈ S.hintikka.formulas
    | .resolve _ r _ => LocalSaturationStep.premise r.step ∈ S.hintikka.formulas := by
  cases a with
  | saturate t =>
      simpa using t.active
  | resolve f r hfocus =>
      simpa using stepPremise_mem_of_canResolveFocus hS (f := f) (r := r) hfocus

theorem searchTransition_of_searchStep {S : SaturationSearchState Const Γ}
    (a : SearchStep S) :
    SearchTransition S a.next :=
  ⟨a, rfl⟩

theorem frontier_eq_of_searchTransition {S T : SaturationSearchState Const Γ}
    (h : SearchTransition S T) :
    T.frontier = S.frontier := by
  rcases h with ⟨a, rfl⟩
  cases a <;> rfl

theorem formula_mem_of_searchTransition {S T : SaturationSearchState Const Γ}
    (h : SearchTransition S T) {sf : SignedFormula Const Γ}
    (hsf : sf ∈ S.hintikka.formulas) :
    sf ∈ T.hintikka.formulas := by
  rcases h with ⟨a, rfl⟩
  cases a with
  | saturate t =>
      exact mem_applyLocalStep_of_mem hsf
  | resolve f r hfocus =>
      exact mem_resolveFocused_of_mem (hfocus := hfocus) hsf

theorem agendaVisible_of_searchTransition {S T : SaturationSearchState Const Γ}
    (hS : S.AgendaVisible) (h : SearchTransition S T) :
    T.AgendaVisible := by
  rcases h with ⟨a, rfl⟩
  exact searchStep_next_agendaVisible hS a

theorem frontier_eq_of_searchReachable {S T : SaturationSearchState Const Γ}
    (h : SearchReachable S T) :
    T.frontier = S.frontier := by
  exact Relation.ReflTransGen.trans_induction_on h
    (fun _ => rfl)
    (fun hstep => frontier_eq_of_searchTransition hstep)
    (fun _ _ ih₁ ih₂ => Eq.trans ih₂ ih₁)

theorem formula_mem_of_searchReachable {S T : SaturationSearchState Const Γ}
    (h : SearchReachable S T) {sf : SignedFormula Const Γ}
    (hsf : sf ∈ S.hintikka.formulas) :
    sf ∈ T.hintikka.formulas := by
  exact Relation.ReflTransGen.trans_induction_on h
    (fun _ => id)
    (fun hstep => formula_mem_of_searchTransition hstep)
    (fun _ _ ih₁ ih₂ => fun hsf => ih₂ (ih₁ hsf))
    hsf

theorem agendaVisible_of_searchReachable {S T : SaturationSearchState Const Γ}
    (h : SearchReachable S T) :
    S.AgendaVisible → T.AgendaVisible := by
  exact Relation.ReflTransGen.trans_induction_on h
    (fun _ => id)
    (fun hstep hS => agendaVisible_of_searchTransition hS hstep)
    (fun _ _ ih₁ ih₂ hS => ih₂ (ih₁ hS))

def headFocus (S : SaturationSearchState Const Γ)
    (r : LocalBranchResolution Const Γ) (hhead : S.CanResolveHead r) :
    AgendaFocus S :=
  match hAgenda : S.agenda with
  | [] =>
      False.elim <| by
        simp [CanResolveHead, nextAgendaTarget?, hAgenda] at hhead
  | a :: tl =>
      have hEq : a = r.target := by
        simp [CanResolveHead, nextAgendaTarget?, hAgenda] at hhead
        exact hhead
      { before := []
        target := r.target
        after := tl
        decompose := by simp [hAgenda, hEq] }

@[simp] theorem headFocus_target (S : SaturationSearchState Const Γ)
    (r : LocalBranchResolution Const Γ) (hhead : S.CanResolveHead r) :
    (headFocus S r hhead).target = r.target := by
  unfold headFocus
  split <;> rename_i heq
  · simp [CanResolveHead, nextAgendaTarget?, heq] at hhead
  · simp

@[simp] theorem headFocus_remaining (S : SaturationSearchState Const Γ)
    (r : LocalBranchResolution Const Γ) (hhead : S.CanResolveHead r) :
    (headFocus S r hhead).remaining =
      match S.agenda with
      | [] => []
      | _ :: tl => tl := by
  unfold headFocus
  split <;> rename_i heq
  · simp [CanResolveHead, nextAgendaTarget?, heq] at hhead
  · simp [AgendaFocus.remaining, heq]

theorem canResolveFocus_headFocus (S : SaturationSearchState Const Γ)
    (r : LocalBranchResolution Const Γ) (hhead : S.CanResolveHead r) :
    S.CanResolveFocus (headFocus S r hhead) r := by
  simp [CanResolveFocus]

def headResolutionStep (S : SaturationSearchState Const Γ)
    (r : LocalBranchResolution Const Γ) (hhead : S.CanResolveHead r) :
    SearchStep S :=
  .resolve (headFocus S r hhead) r (canResolveFocus_headFocus S r hhead)

theorem resolveHead_eq_resolveFocused (S : SaturationSearchState Const Γ)
    (r : LocalBranchResolution Const Γ) (hhead : S.CanResolveHead r) :
    resolveHead S r hhead =
      resolveFocused S (headFocus S r hhead) r (canResolveFocus_headFocus S r hhead) := by
  cases hAgenda : S.agenda with
  | nil =>
      simp [CanResolveHead, nextAgendaTarget?, hAgenda] at hhead
  | cons a tl =>
      simp [resolveHead, resolveFocused, headFocus_remaining, CanResolveHead,
        nextAgendaTarget?, hAgenda] at hhead ⊢

theorem headResolutionStep_next_eq_resolveHead (S : SaturationSearchState Const Γ)
    (r : LocalBranchResolution Const Γ) (hhead : S.CanResolveHead r) :
    (headResolutionStep S r hhead).next = resolveHead S r hhead := by
  simpa [headResolutionStep, SearchStep.next] using
    (resolveHead_eq_resolveFocused S r hhead).symm

theorem headResolutionTransition (S : SaturationSearchState Const Γ)
    (r : LocalBranchResolution Const Γ) (hhead : S.CanResolveHead r) :
    SearchTransition S (resolveHead S r hhead) := by
  refine ⟨headResolutionStep S r hhead, ?_⟩
  exact headResolutionStep_next_eq_resolveHead S r hhead

theorem headResolutionReachable (S : SaturationSearchState Const Γ)
    (r : LocalBranchResolution Const Γ) (hhead : S.CanResolveHead r) :
    SearchReachable S (resolveHead S r hhead) :=
  Relation.ReflTransGen.single (headResolutionTransition S r hhead)

theorem frontier_eq_of_initial_searchReachable {F : CompletenessFrontier Const Γ}
    {T : SaturationSearchState Const Γ}
    (h : SearchReachable (initial F) T) :
    T.frontier = F := by
  simpa [initial] using frontier_eq_of_searchReachable h

theorem true_mem_of_initial_searchReachable {F : CompletenessFrontier Const Γ}
    {T : SaturationSearchState Const Γ}
    (h : SearchReachable (initial F) T)
    {φ : Formula Const Γ} (hφ : φ ∈ F.antecedents) :
    (Sign.trueE, φ) ∈ T.hintikka.formulas :=
  formula_mem_of_searchReachable h (true_mem_initial hφ)

theorem false_mem_of_initial_searchReachable {F : CompletenessFrontier Const Γ}
    {T : SaturationSearchState Const Γ}
    (h : SearchReachable (initial F) T) :
    (Sign.falseE, F.succedent) ∈ T.hintikka.formulas :=
  formula_mem_of_searchReachable h (false_mem_initial F)

/-- A finite honest search run rooted at one fixed initial frontier. -/
structure SearchRun (F : CompletenessFrontier Const Γ) where
  state : SaturationSearchState Const Γ
  reachable : SearchReachable (initial F) state

namespace SearchRun

/-- The trivial run staying at the initial search state. -/
def initial (F : CompletenessFrontier Const Γ) : SearchRun F :=
  { state := SaturationSearchState.initial F
    reachable := Relation.ReflTransGen.refl }

/-- Extend a rooted run by one honest local search step. -/
def step {F : CompletenessFrontier Const Γ} (R : SearchRun F)
    (a : SearchStep R.state) : SearchRun F :=
  { state := a.next
    reachable := Relation.ReflTransGen.trans R.reachable
      (Relation.ReflTransGen.single (searchTransition_of_searchStep a)) }

/-- Extend a rooted run by one triggered local saturation step. -/
def saturate {F : CompletenessFrontier Const Γ} (R : SearchRun F)
    (t : TriggeredLocalStep R.state) : SearchRun F :=
  R.step (.saturate t)

/-- Extend a rooted run by resolving one focused local branching target. -/
def resolveFocused {F : CompletenessFrontier Const Γ} (R : SearchRun F)
    (f : AgendaFocus R.state) (r : LocalBranchResolution Const Γ)
    (hfocus : R.state.CanResolveFocus f r) : SearchRun F :=
  R.step (.resolve f r hfocus)

/-- Extend a rooted run by resolving the current agenda head. -/
def resolveHead {F : CompletenessFrontier Const Γ} (R : SearchRun F)
    (r : LocalBranchResolution Const Γ) (hhead : R.state.CanResolveHead r) :
    SearchRun F :=
  { state := SaturationSearchState.resolveHead R.state r hhead
    reachable := Relation.ReflTransGen.trans R.reachable
      (headResolutionReachable R.state r hhead) }

@[simp] theorem initial_state (F : CompletenessFrontier Const Γ) :
    (initial F).state = SaturationSearchState.initial F :=
  rfl

theorem frontier_eq {F : CompletenessFrontier Const Γ} (R : SearchRun F) :
    R.state.frontier = F :=
  frontier_eq_of_initial_searchReachable R.reachable

theorem agendaVisible {F : CompletenessFrontier Const Γ} (R : SearchRun F) :
    R.state.AgendaVisible :=
  agendaVisible_of_searchReachable R.reachable (agendaVisible_initial F)

theorem formula_mem {F : CompletenessFrontier Const Γ} (R : SearchRun F)
    {sf : SignedFormula Const Γ}
    (hsf : sf ∈ (SaturationSearchState.initial F).hintikka.formulas) :
    sf ∈ R.state.hintikka.formulas :=
  formula_mem_of_searchReachable R.reachable hsf

theorem true_mem {F : CompletenessFrontier Const Γ} (R : SearchRun F)
    {φ : Formula Const Γ} (hφ : φ ∈ F.antecedents) :
    (Sign.trueE, φ) ∈ R.state.hintikka.formulas :=
  true_mem_of_initial_searchReachable R.reachable hφ

theorem false_mem {F : CompletenessFrontier Const Γ} (R : SearchRun F) :
    (Sign.falseE, F.succedent) ∈ R.state.hintikka.formulas :=
  false_mem_of_initial_searchReachable R.reachable

theorem stepPremise_mem {F : CompletenessFrontier Const Γ} (R : SearchRun F)
    (a : SearchStep R.state) :
    match a with
    | .saturate t => DeterministicLocalSaturationStep.premise t.step ∈ R.state.hintikka.formulas
    | .resolve _ r _ => LocalSaturationStep.premise r.step ∈ R.state.hintikka.formulas :=
  by
    cases a with
    | saturate t =>
        simpa using t.active
    | resolve f r hfocus =>
        simpa using stepPremise_mem_of_canResolveFocus R.agendaVisible
          (f := f) (r := r) hfocus

end SearchRun

/-- An explicit honest local-search derivation rooted at one fixed frontier. -/
inductive SearchDerivation (F : CompletenessFrontier Const Γ) :
    SaturationSearchState Const Γ → Type (max u v) where
  | initial :
      SearchDerivation F (SaturationSearchState.initial F)
  | saturate {S : SaturationSearchState Const Γ}
      (D : SearchDerivation F S) (t : TriggeredLocalStep S) :
      SearchDerivation F (S.applyLocalStep t.step.toLocalSaturationStep)
  | resolveFocused {S : SaturationSearchState Const Γ}
      (D : SearchDerivation F S) (f : AgendaFocus S)
      (r : LocalBranchResolution Const Γ) (hfocus : S.CanResolveFocus f r) :
      SearchDerivation F (S.resolveFocused f r hfocus)
  | resolveHead {S : SaturationSearchState Const Γ}
      (D : SearchDerivation F S)
      (r : LocalBranchResolution Const Γ) (hhead : S.CanResolveHead r) :
      SearchDerivation F (S.resolveHead r hhead)

namespace SearchDerivation

/-- Any explicit honest derivation yields a finite honest reachability proof
from the rooted initial frontier state to its endpoint. -/
theorem reachable {F : CompletenessFrontier Const Γ}
    {S : SaturationSearchState Const Γ} (D : SearchDerivation F S) :
    SearchReachable (SaturationSearchState.initial F) S := by
  induction D with
  | initial =>
      exact Relation.ReflTransGen.refl
  | @saturate S D t ih =>
      exact Relation.ReflTransGen.trans ih
        (Relation.ReflTransGen.single
          (searchTransition_of_searchStep (.saturate t)))
  | @resolveFocused S D f r hfocus ih =>
      exact Relation.ReflTransGen.trans ih
        (Relation.ReflTransGen.single
          (searchTransition_of_searchStep (.resolve f r hfocus)))
  | @resolveHead S D r hhead ih =>
      exact Relation.ReflTransGen.trans ih
        (headResolutionReachable S r hhead)

/-- Forget the explicit history and keep the rooted run endpoint together with
its finite honest reachability proof. -/
def toSearchRun {F : CompletenessFrontier Const Γ} {S : SaturationSearchState Const Γ}
    (D : SearchDerivation F S) : SearchRun F :=
  { state := S
    reachable := D.reachable }

@[simp] theorem toSearchRun_state {F : CompletenessFrontier Const Γ}
    {S : SaturationSearchState Const Γ} (D : SearchDerivation F S) :
    D.toSearchRun.state = S :=
  rfl

theorem frontier_eq {F : CompletenessFrontier Const Γ}
    {S : SaturationSearchState Const Γ} (D : SearchDerivation F S) :
    S.frontier = F := by
  simpa [toSearchRun_state] using D.toSearchRun.frontier_eq

theorem agendaVisible {F : CompletenessFrontier Const Γ}
    {S : SaturationSearchState Const Γ} (D : SearchDerivation F S) :
    S.AgendaVisible := by
  simpa [toSearchRun_state] using D.toSearchRun.agendaVisible

theorem formula_mem {F : CompletenessFrontier Const Γ}
    {S : SaturationSearchState Const Γ} (D : SearchDerivation F S)
    {sf : SignedFormula Const Γ}
    (hsf : sf ∈ (SaturationSearchState.initial F).hintikka.formulas) :
    sf ∈ S.hintikka.formulas := by
  simpa [toSearchRun_state] using D.toSearchRun.formula_mem hsf

theorem true_mem {F : CompletenessFrontier Const Γ}
    {S : SaturationSearchState Const Γ} (D : SearchDerivation F S)
    {φ : Formula Const Γ} (hφ : φ ∈ F.antecedents) :
    (Sign.trueE, φ) ∈ S.hintikka.formulas := by
  simpa [toSearchRun_state] using D.toSearchRun.true_mem hφ

theorem false_mem {F : CompletenessFrontier Const Γ}
    {S : SaturationSearchState Const Γ} (D : SearchDerivation F S) :
    (Sign.falseE, F.succedent) ∈ S.hintikka.formulas := by
  simpa [toSearchRun_state] using D.toSearchRun.false_mem

end SearchDerivation

/-- A more disciplined local-search history that only resolves the current
agenda head, removing arbitrary focus choice from branch resolution. -/
inductive HeadSearchDerivation (F : CompletenessFrontier Const Γ) :
    SaturationSearchState Const Γ → Type (max u v) where
  | initial :
      HeadSearchDerivation F (SaturationSearchState.initial F)
  | saturate {S : SaturationSearchState Const Γ}
      (D : HeadSearchDerivation F S) (t : TriggeredLocalStep S) :
      HeadSearchDerivation F (S.applyLocalStep t.step.toLocalSaturationStep)
  | resolveHead {S : SaturationSearchState Const Γ}
      (D : HeadSearchDerivation F S)
      (r : LocalBranchResolution Const Γ) (hhead : S.CanResolveHead r) :
      HeadSearchDerivation F (S.resolveHead r hhead)

namespace HeadSearchDerivation

/-- Any head-driven derivation yields a finite honest reachability proof from
the rooted initial frontier state to its endpoint. -/
theorem reachable {F : CompletenessFrontier Const Γ}
    {S : SaturationSearchState Const Γ} (D : HeadSearchDerivation F S) :
    SearchReachable (SaturationSearchState.initial F) S := by
  induction D with
  | initial =>
      exact Relation.ReflTransGen.refl
  | @saturate S D t ih =>
      exact Relation.ReflTransGen.trans ih
        (Relation.ReflTransGen.single
          (searchTransition_of_searchStep (.saturate t)))
  | @resolveHead S D r hhead ih =>
      exact Relation.ReflTransGen.trans ih
        (headResolutionReachable S r hhead)

/-- Forget the explicit head-driven history and keep the rooted run endpoint. -/
def toSearchRun {F : CompletenessFrontier Const Γ} {S : SaturationSearchState Const Γ}
    (D : HeadSearchDerivation F S) : SearchRun F :=
  { state := S
    reachable := D.reachable }

theorem frontier_eq {F : CompletenessFrontier Const Γ}
    {S : SaturationSearchState Const Γ} (D : HeadSearchDerivation F S) :
    S.frontier = F := by
  change D.toSearchRun.state.frontier = F
  exact D.toSearchRun.frontier_eq

theorem agendaVisible {F : CompletenessFrontier Const Γ}
    {S : SaturationSearchState Const Γ} (D : HeadSearchDerivation F S) :
    S.AgendaVisible := by
  change D.toSearchRun.state.AgendaVisible
  exact D.toSearchRun.agendaVisible

theorem formula_mem {F : CompletenessFrontier Const Γ}
    {S : SaturationSearchState Const Γ} (D : HeadSearchDerivation F S)
    {sf : SignedFormula Const Γ}
    (hsf : sf ∈ (SaturationSearchState.initial F).hintikka.formulas) :
    sf ∈ S.hintikka.formulas := by
  change sf ∈ D.toSearchRun.state.hintikka.formulas
  exact D.toSearchRun.formula_mem hsf

theorem true_mem {F : CompletenessFrontier Const Γ}
    {S : SaturationSearchState Const Γ} (D : HeadSearchDerivation F S)
    {φ : Formula Const Γ} (hφ : φ ∈ F.antecedents) :
    (Sign.trueE, φ) ∈ S.hintikka.formulas := by
  change (Sign.trueE, φ) ∈ D.toSearchRun.state.hintikka.formulas
  exact D.toSearchRun.true_mem hφ

theorem false_mem {F : CompletenessFrontier Const Γ}
    {S : SaturationSearchState Const Γ} (D : HeadSearchDerivation F S) :
    (Sign.falseE, F.succedent) ∈ S.hintikka.formulas := by
  change (Sign.falseE, F.succedent) ∈ D.toSearchRun.state.hintikka.formulas
  exact D.toSearchRun.false_mem

end HeadSearchDerivation

/-- A stricter head-driven search discipline whose saturation steps must be
genuinely productive, i.e. contribute at least one new signed formula. -/
inductive ProductiveHeadSearchDerivation (F : CompletenessFrontier Const Γ) :
    SaturationSearchState Const Γ → Type (max u v) where
  | initial :
      ProductiveHeadSearchDerivation F (SaturationSearchState.initial F)
  | saturate {S : SaturationSearchState Const Γ}
      (D : ProductiveHeadSearchDerivation F S) (t : ProductiveTriggeredLocalStep S) :
      ProductiveHeadSearchDerivation F (S.applyLocalStep t.step.toLocalSaturationStep)
  | resolveHead {S : SaturationSearchState Const Γ}
      (D : ProductiveHeadSearchDerivation F S)
      (r : LocalBranchResolution Const Γ) (hhead : S.CanResolveHead r) :
      ProductiveHeadSearchDerivation F (S.resolveHead r hhead)

namespace ProductiveHeadSearchDerivation

/-- Any productive head-driven derivation yields a finite honest reachability
proof from the rooted initial frontier state to its endpoint. -/
theorem reachable {F : CompletenessFrontier Const Γ}
    {S : SaturationSearchState Const Γ} (D : ProductiveHeadSearchDerivation F S) :
    SearchReachable (SaturationSearchState.initial F) S := by
  induction D with
  | initial =>
      exact Relation.ReflTransGen.refl
  | @saturate S D t ih =>
      exact Relation.ReflTransGen.trans ih
        (Relation.ReflTransGen.single
          (searchTransition_of_searchStep (.saturate t.toTriggeredLocalStep)))
  | @resolveHead S D r hhead ih =>
      exact Relation.ReflTransGen.trans ih
        (headResolutionReachable S r hhead)

/-- Forget the explicit productive head-driven history and keep the rooted run
endpoint. -/
def toSearchRun {F : CompletenessFrontier Const Γ} {S : SaturationSearchState Const Γ}
    (D : ProductiveHeadSearchDerivation F S) : SearchRun F :=
  { state := S
    reachable := D.reachable }

theorem frontier_eq {F : CompletenessFrontier Const Γ}
    {S : SaturationSearchState Const Γ} (D : ProductiveHeadSearchDerivation F S) :
    S.frontier = F := by
  change D.toSearchRun.state.frontier = F
  exact D.toSearchRun.frontier_eq

theorem agendaVisible {F : CompletenessFrontier Const Γ}
    {S : SaturationSearchState Const Γ} (D : ProductiveHeadSearchDerivation F S) :
    S.AgendaVisible := by
  change D.toSearchRun.state.AgendaVisible
  exact D.toSearchRun.agendaVisible

theorem formula_mem {F : CompletenessFrontier Const Γ}
    {S : SaturationSearchState Const Γ} (D : ProductiveHeadSearchDerivation F S)
    {sf : SignedFormula Const Γ}
    (hsf : sf ∈ (SaturationSearchState.initial F).hintikka.formulas) :
    sf ∈ S.hintikka.formulas := by
  change sf ∈ D.toSearchRun.state.hintikka.formulas
  exact D.toSearchRun.formula_mem hsf

theorem true_mem {F : CompletenessFrontier Const Γ}
    {S : SaturationSearchState Const Γ} (D : ProductiveHeadSearchDerivation F S)
    {φ : Formula Const Γ} (hφ : φ ∈ F.antecedents) :
    (Sign.trueE, φ) ∈ S.hintikka.formulas := by
  change (Sign.trueE, φ) ∈ D.toSearchRun.state.hintikka.formulas
  exact D.toSearchRun.true_mem hφ

theorem false_mem {F : CompletenessFrontier Const Γ}
    {S : SaturationSearchState Const Γ} (D : ProductiveHeadSearchDerivation F S) :
    (Sign.falseE, F.succedent) ∈ S.hintikka.formulas := by
  change (Sign.falseE, F.succedent) ∈ D.toSearchRun.state.hintikka.formulas
  exact D.toSearchRun.false_mem

end ProductiveHeadSearchDerivation

/-- A head-priority scheduler: productive saturation is only allowed while the
agenda is empty, and otherwise search proceeds by resolving the current head. -/
inductive HeadPrioritySearchDerivation (F : CompletenessFrontier Const Γ) :
    SaturationSearchState Const Γ → Type (max u v) where
  | initial :
      HeadPrioritySearchDerivation F (SaturationSearchState.initial F)
  | saturate {S : SaturationSearchState Const Γ}
      (D : HeadPrioritySearchDerivation F S) (hIdle : S.agenda = [])
      (t : ProductiveTriggeredLocalStep S) :
      HeadPrioritySearchDerivation F (S.applyLocalStep t.step.toLocalSaturationStep)
  | resolveHead {S : SaturationSearchState Const Γ}
      (D : HeadPrioritySearchDerivation F S)
      (r : LocalBranchResolution Const Γ) (hhead : S.CanResolveHead r) :
      HeadPrioritySearchDerivation F (S.resolveHead r hhead)

namespace HeadPrioritySearchDerivation

/-- Stepwise compatibility data ensuring that every head-priority move adds
only formulas whose flips are absent from the closed hull already built so far. -/
def Compatible {F : CompletenessFrontier Const Γ} :
    {S : SaturationSearchState Const Γ} →
      HeadPrioritySearchDerivation F S → Prop
  | _, .initial => True
  | _, .saturate (S := S) D _ t =>
      Compatible D ∧ S.DeterministicAdditionCompatible t.step
  | _, .resolveHead (S := S) D r _ =>
      Compatible D ∧ S.BranchAdditionCompatible r

theorem compatible_initial {F : CompletenessFrontier Const Γ} :
    Compatible (HeadPrioritySearchDerivation.initial (F := F)) := by
  trivial

theorem compatible_saturate
    {F : CompletenessFrontier Const Γ}
    {S : SaturationSearchState Const Γ}
    (D : HeadPrioritySearchDerivation F S)
    (hIdle : S.agenda = [])
    (t : ProductiveTriggeredLocalStep S)
    (hD : Compatible D)
    (hStep : S.DeterministicAdditionCompatible t.step) :
    Compatible (HeadPrioritySearchDerivation.saturate D hIdle t) :=
  ⟨hD, hStep⟩

theorem compatible_resolveHead
    {F : CompletenessFrontier Const Γ}
    {S : SaturationSearchState Const Γ}
    (D : HeadPrioritySearchDerivation F S)
    (r : LocalBranchResolution Const Γ)
    (hhead : S.CanResolveHead r)
    (hD : Compatible D)
    (hStep : S.BranchAdditionCompatible r) :
    Compatible (HeadPrioritySearchDerivation.resolveHead D r hhead) :=
  ⟨hD, hStep⟩

/-- Any head-priority derivation yields a finite honest reachability proof from
the rooted initial frontier state to its endpoint. -/
theorem reachable {F : CompletenessFrontier Const Γ}
    {S : SaturationSearchState Const Γ} (D : HeadPrioritySearchDerivation F S) :
    SearchReachable (SaturationSearchState.initial F) S := by
  induction D with
  | initial =>
      exact Relation.ReflTransGen.refl
  | @saturate S D hIdle t ih =>
      exact Relation.ReflTransGen.trans ih
        (Relation.ReflTransGen.single
          (searchTransition_of_searchStep (.saturate t.toTriggeredLocalStep)))
  | @resolveHead S D r hhead ih =>
      exact Relation.ReflTransGen.trans ih
        (headResolutionReachable S r hhead)

/-- Forget the explicit head-priority history and keep the rooted run endpoint. -/
def toSearchRun {F : CompletenessFrontier Const Γ} {S : SaturationSearchState Const Γ}
    (D : HeadPrioritySearchDerivation F S) : SearchRun F :=
  { state := S
    reachable := D.reachable }

theorem frontier_eq {F : CompletenessFrontier Const Γ}
    {S : SaturationSearchState Const Γ} (D : HeadPrioritySearchDerivation F S) :
    S.frontier = F := by
  change D.toSearchRun.state.frontier = F
  exact D.toSearchRun.frontier_eq

theorem agendaVisible {F : CompletenessFrontier Const Γ}
    {S : SaturationSearchState Const Γ} (D : HeadPrioritySearchDerivation F S) :
    S.AgendaVisible := by
  change D.toSearchRun.state.AgendaVisible
  exact D.toSearchRun.agendaVisible

theorem formula_mem {F : CompletenessFrontier Const Γ}
    {S : SaturationSearchState Const Γ} (D : HeadPrioritySearchDerivation F S)
    {sf : SignedFormula Const Γ}
    (hsf : sf ∈ (SaturationSearchState.initial F).hintikka.formulas) :
    sf ∈ S.hintikka.formulas := by
  change sf ∈ D.toSearchRun.state.hintikka.formulas
  exact D.toSearchRun.formula_mem hsf

theorem true_mem {F : CompletenessFrontier Const Γ}
    {S : SaturationSearchState Const Γ} (D : HeadPrioritySearchDerivation F S)
    {φ : Formula Const Γ} (hφ : φ ∈ F.antecedents) :
    (Sign.trueE, φ) ∈ S.hintikka.formulas := by
  change (Sign.trueE, φ) ∈ D.toSearchRun.state.hintikka.formulas
  exact D.toSearchRun.true_mem hφ

theorem false_mem {F : CompletenessFrontier Const Γ}
    {S : SaturationSearchState Const Γ} (D : HeadPrioritySearchDerivation F S) :
    (Sign.falseE, F.succedent) ∈ S.hintikka.formulas := by
  change (Sign.falseE, F.succedent) ∈ D.toSearchRun.state.hintikka.formulas
  exact D.toSearchRun.false_mem

theorem closed_noncontradictory {F : CompletenessFrontier Const Γ}
    {S : SaturationSearchState Const Γ} (D : HeadPrioritySearchDerivation F S)
    (hInitial : (SaturationSearchState.initial F).hintikka.close.Noncontradictory)
    (hCompat : D.Compatible) :
    S.hintikka.close.Noncontradictory := by
  induction D with
  | initial =>
      simpa using hInitial
  | @saturate S D hIdle t ih =>
      simp [Compatible] at hCompat
      exact SaturationSearchState.closed_noncontradictory_applyLocalStep_of_deterministicAdditionCompatible
        (S := S) (ih hCompat.1) hCompat.2
  | @resolveHead S D r hhead ih =>
      simp [Compatible] at hCompat
      exact SaturationSearchState.closed_noncontradictory_resolveHead_of_branchAdditionCompatible
        (S := S) (ih hCompat.1) (r := r) (hhead := hhead) hCompat.2

end HeadPrioritySearchDerivation

/-- No genuinely productive local saturation step remains available. -/
def NoProductiveTriggeredStep (S : SaturationSearchState Const Γ) : Prop :=
  ∀ _ : ProductiveTriggeredLocalStep S, False

/-- A terminal local-search state has no pending branch agenda and no productive
saturation step left to apply. -/
def IsTerminal (S : SaturationSearchState Const Γ) : Prop :=
  S.agenda = [] ∧ S.NoProductiveTriggeredStep

theorem locallySaturated_of_noProductiveTriggeredStep
    {S : SaturationSearchState Const Γ}
    (hS : S.NoProductiveTriggeredStep) :
    S.hintikka.LocallySaturated := by
  intro s hprem sf hsf
  by_cases hmem : sf ∈ S.hintikka.formulas
  · exact hmem
  · exfalso
    exact hS
      { step := s
        active := hprem
        fresh := ⟨sf, hsf, hmem⟩ }

theorem locallySaturated_of_isTerminal
    {S : SaturationSearchState Const Γ}
    (hS : S.IsTerminal) :
    S.hintikka.LocallySaturated :=
  locallySaturated_of_noProductiveTriggeredStep hS.2

/-- A head-priority completion packages a frontier-rooted derivation together
with the fact that the resulting local search state is terminal. -/
structure HeadPriorityCompletion (F : CompletenessFrontier Const Γ) where
  state : SaturationSearchState Const Γ
  derivation : HeadPrioritySearchDerivation F state
  terminal : state.IsTerminal
  branchClosed : state.hintikka.BranchClosed

namespace HeadPriorityCompletion

theorem frontier_eq {F : CompletenessFrontier Const Γ}
    (C : HeadPriorityCompletion F) :
    C.state.frontier = F :=
  C.derivation.frontier_eq

theorem agenda_eq_nil {F : CompletenessFrontier Const Γ}
    (C : HeadPriorityCompletion F) :
    C.state.agenda = [] :=
  C.terminal.1

theorem noProductiveTriggeredStep {F : CompletenessFrontier Const Γ}
    (C : HeadPriorityCompletion F) :
    C.state.NoProductiveTriggeredStep :=
  C.terminal.2

theorem agendaVisible {F : CompletenessFrontier Const Γ}
    (C : HeadPriorityCompletion F) :
    C.state.AgendaVisible :=
  C.derivation.agendaVisible

theorem locallySaturated {F : CompletenessFrontier Const Γ}
    (C : HeadPriorityCompletion F) :
    C.state.hintikka.LocallySaturated :=
  locallySaturated_of_isTerminal C.terminal

theorem true_mem {F : CompletenessFrontier Const Γ}
    (C : HeadPriorityCompletion F)
    {φ : Formula Const Γ} (hφ : φ ∈ F.antecedents) :
    (Sign.trueE, φ) ∈ C.state.hintikka.formulas :=
  C.derivation.true_mem hφ

theorem false_mem {F : CompletenessFrontier Const Γ}
    (C : HeadPriorityCompletion F) :
    (Sign.falseE, F.succedent) ∈ C.state.hintikka.formulas :=
  C.derivation.false_mem

theorem closed_noncontradictory_of_compatibleDerivation
    {F : CompletenessFrontier Const Γ}
    (C : HeadPriorityCompletion F)
    (hInitial : (SaturationSearchState.initial F).hintikka.close.Noncontradictory)
    (hCompat : C.derivation.Compatible) :
    C.state.hintikka.close.Noncontradictory :=
  C.derivation.closed_noncontradictory hInitial hCompat

end HeadPriorityCompletion

theorem nextAgendaTarget?_initial_eq_head? (F : CompletenessFrontier Const Γ) :
    (initial F).nextAgendaTarget? = (initial F).agenda.head? :=
  rfl

theorem canResolveHead_iff (S : SaturationSearchState Const Γ)
    (r : LocalBranchResolution Const Γ) :
    S.CanResolveHead r ↔ S.nextAgendaTarget? = some r.target :=
  Iff.rfl

end SaturationSearchState

/-- A world-free local countermodel candidate packages a frontier together with
the current terminal head-priority completion data extracted from the staged
local search. Later completeness work may add the missing world-indexed forcing
structure on top of this object. -/
structure CountermodelCandidate (Const : Ty Base → Type v) (Γ : Ctx Base) where
  frontier : CompletenessFrontier Const Γ
  completion : SaturationSearchState.HeadPriorityCompletion frontier

namespace CountermodelCandidate

/-- The terminal staged search state underlying the current local candidate. -/
def state (C : CountermodelCandidate Const Γ) : SaturationSearchState Const Γ :=
  C.completion.state

/-- The currently accumulated Hintikka-style signed formulas attached to the
local candidate. -/
def hintikka (C : CountermodelCandidate Const Γ) : HintikkaSet Const Γ :=
  C.state.hintikka

theorem frontier_eq (C : CountermodelCandidate Const Γ) :
    C.state.frontier = C.frontier :=
  C.completion.frontier_eq

theorem agenda_eq_nil (C : CountermodelCandidate Const Γ) :
    C.state.agenda = [] :=
  C.completion.agenda_eq_nil

theorem agendaVisible (C : CountermodelCandidate Const Γ) :
    C.state.AgendaVisible :=
  C.completion.agendaVisible

theorem locallySaturated (C : CountermodelCandidate Const Γ) :
    C.hintikka.LocallySaturated :=
  C.completion.locallySaturated

theorem branchClosed (C : CountermodelCandidate Const Γ) :
    C.hintikka.BranchClosed :=
  C.completion.branchClosed

theorem formula_mem (C : CountermodelCandidate Const Γ)
    {sf : SignedFormula Const Γ}
    (hsf : sf ∈ (SaturationSearchState.initial C.frontier).hintikka.formulas) :
    sf ∈ C.hintikka.formulas := by
  simpa [hintikka, state] using C.completion.derivation.formula_mem hsf

theorem true_mem (C : CountermodelCandidate Const Γ)
    {φ : Formula Const Γ} (hφ : φ ∈ C.frontier.antecedents) :
    (Sign.trueE, φ) ∈ C.hintikka.formulas := by
  simpa [hintikka, state] using C.completion.true_mem hφ

theorem false_mem (C : CountermodelCandidate Const Γ) :
    (Sign.falseE, C.frontier.succedent) ∈ C.hintikka.formulas := by
  simpa [hintikka, state] using C.completion.false_mem

theorem exists_resolvingStep_of_premise_mem (C : CountermodelCandidate Const Γ)
    {b : LocalBranchTarget Const Γ}
    (hb : b.premise ∈ C.hintikka.formulas) :
    ∃ s : LocalSaturationStep Const Γ,
      b.AcceptsStep s ∧
      ∀ sf ∈ LocalSaturationStep.additions s, sf ∈ C.hintikka.formulas :=
  HintikkaSet.exists_resolvingStep_of_branchClosed C.branchClosed hb

theorem exists_resolvingStep_of_mem_localBranchTargets
    (C : CountermodelCandidate Const Γ)
    {b : LocalBranchTarget Const Γ}
    (hb : b ∈ C.hintikka.localBranchTargets) :
    ∃ s : LocalSaturationStep Const Γ,
      b.AcceptsStep s ∧
      ∀ sf ∈ LocalSaturationStep.additions s, sf ∈ C.hintikka.formulas :=
  HintikkaSet.exists_resolvingStep_of_mem_localBranchTargets C.branchClosed hb

end CountermodelCandidate

/-- A semantic-facing world-free Hintikka core for a frontier, keeping only the
frontier witness data and the local closure properties needed by the later
induced-model route. -/
structure LocalHintikkaCore (F : CompletenessFrontier Const Γ) where
  hintikka : HintikkaSet Const Γ
  antecedent_true_mem :
    ∀ {φ : Formula Const Γ}, φ ∈ F.antecedents → (Sign.trueE, φ) ∈ hintikka.formulas
  succedent_false_mem : (Sign.falseE, F.succedent) ∈ hintikka.formulas
  locallySaturated : hintikka.LocallySaturated
  branchClosed : hintikka.BranchClosed

namespace LocalHintikkaCore

theorem true_mem {F : CompletenessFrontier Const Γ}
    (C : LocalHintikkaCore F)
    {φ : Formula Const Γ} (hφ : φ ∈ F.antecedents) :
    (Sign.trueE, φ) ∈ C.hintikka.formulas :=
  C.antecedent_true_mem hφ

theorem false_mem {F : CompletenessFrontier Const Γ}
    (C : LocalHintikkaCore F) :
    (Sign.falseE, F.succedent) ∈ C.hintikka.formulas :=
  C.succedent_false_mem

theorem branchTarget_resolvable {F : CompletenessFrontier Const Γ}
    (C : LocalHintikkaCore F)
    {b : LocalBranchTarget Const Γ}
    (hb : b ∈ C.hintikka.localBranchTargets) :
    ∃ s : LocalSaturationStep Const Γ,
      b.AcceptsStep s ∧
      ∀ sf ∈ LocalSaturationStep.additions s, sf ∈ C.hintikka.formulas :=
  HintikkaSet.exists_resolvingStep_of_mem_localBranchTargets C.branchClosed hb

end LocalHintikkaCore

/-- A paper-facing local Hintikka certificate for a frontier packages the
world-free closure properties of the current completeness spine together with
closedness and non-contradiction. This is the semantic target the later
countermodel construction must eventually inhabit. -/
structure LocalHintikkaCertificate (F : CompletenessFrontier Const Γ)
    extends LocalHintikkaCore F where
  closed : hintikka.Closed
  noncontradictory : hintikka.Noncontradictory

namespace LocalHintikkaCertificate

theorem true_mem {F : CompletenessFrontier Const Γ}
    (C : LocalHintikkaCertificate F)
    {φ : Formula Const Γ} (hφ : φ ∈ F.antecedents) :
    (Sign.trueE, φ) ∈ C.hintikka.formulas :=
  C.antecedent_true_mem hφ

theorem false_mem {F : CompletenessFrontier Const Γ}
    (C : LocalHintikkaCertificate F) :
    (Sign.falseE, F.succedent) ∈ C.hintikka.formulas :=
  C.succedent_false_mem

theorem trueTop_mem {F : CompletenessFrontier Const Γ}
    (C : LocalHintikkaCertificate F) :
    (Sign.trueE, (.top : Formula Const Γ)) ∈ C.hintikka.formulas :=
  HintikkaSet.trueTop_mem_of_closed C.closed

theorem falseBot_mem {F : CompletenessFrontier Const Γ}
    (C : LocalHintikkaCertificate F) :
    (Sign.falseE, (.bot : Formula Const Γ)) ∈ C.hintikka.formulas :=
  HintikkaSet.falseBot_mem_of_closed C.closed

theorem antecedent_false_not_mem {F : CompletenessFrontier Const Γ}
    (C : LocalHintikkaCertificate F)
    {φ : Formula Const Γ} (hφ : φ ∈ F.antecedents) :
    (Sign.falseE, φ) ∉ C.hintikka.formulas :=
  HintikkaSet.false_not_mem_of_true_mem_of_noncontradictory
    C.noncontradictory (C.true_mem hφ)

theorem succedent_true_not_mem {F : CompletenessFrontier Const Γ}
    (C : LocalHintikkaCertificate F) :
    (Sign.trueE, F.succedent) ∉ C.hintikka.formulas :=
  HintikkaSet.true_not_mem_of_false_mem_of_noncontradictory
    C.noncontradictory C.false_mem

theorem trueBot_not_mem {F : CompletenessFrontier Const Γ}
    (C : LocalHintikkaCertificate F) :
    (Sign.trueE, (.bot : Formula Const Γ)) ∉ C.hintikka.formulas :=
  HintikkaSet.trueBot_not_mem_of_noncontradictory C.noncontradictory

theorem falseTop_not_mem {F : CompletenessFrontier Const Γ}
    (C : LocalHintikkaCertificate F) :
    (Sign.falseE, (.top : Formula Const Γ)) ∉ C.hintikka.formulas :=
  HintikkaSet.falseTop_not_mem_of_noncontradictory C.noncontradictory

theorem succedent_not_mem_antecedents {F : CompletenessFrontier Const Γ}
    (C : LocalHintikkaCertificate F) :
    F.succedent ∉ F.antecedents := by
  intro hSucc
  exact C.succedent_true_not_mem (C.true_mem hSucc)

theorem branchTarget_resolvable {F : CompletenessFrontier Const Γ}
    (C : LocalHintikkaCertificate F)
    {b : LocalBranchTarget Const Γ}
    (hb : b ∈ C.hintikka.localBranchTargets) :
    ∃ s : LocalSaturationStep Const Γ,
      b.AcceptsStep s ∧
      ∀ sf ∈ LocalSaturationStep.additions s, sf ∈ C.hintikka.formulas :=
  HintikkaSet.exists_resolvingStep_of_mem_localBranchTargets C.branchClosed hb

end LocalHintikkaCertificate

/-- A frontier-indexed local analogue of the paper's consistent Hintikka set:
the local closure core together with closedness and the one-world ICTT
consistency condition. -/
structure LocalConsistentHintikka (F : CompletenessFrontier Const Γ)
    extends LocalHintikkaCore F where
  closed : hintikka.Closed
  consistent : hintikka.ICTTConsistent

namespace LocalConsistentHintikka

theorem not_derivable_succedent {F : CompletenessFrontier Const Γ}
    (C : LocalConsistentHintikka F) :
    ¬ Derivable (Base := Base) (Const := Const) C.hintikka.trueFormulas F.succedent :=
  HintikkaSet.not_derivable_of_false_mem_of_icttConsistent
    C.consistent C.succedent_false_mem

theorem noncontradictory {F : CompletenessFrontier Const Γ}
    (C : LocalConsistentHintikka F) :
    C.hintikka.Noncontradictory :=
  HintikkaSet.noncontradictory_of_closed_icttConsistent
    C.closed C.consistent

/-- Forget consistency and retain the weaker local closed non-contradictory
certificate already used by the current completeness spine. -/
def toLocalHintikkaCertificate {F : CompletenessFrontier Const Γ}
    (C : LocalConsistentHintikka F) :
    LocalHintikkaCertificate F :=
  { toLocalHintikkaCore := C.toLocalHintikkaCore
    closed := C.closed
    noncontradictory := C.noncontradictory }

theorem succedent_not_mem_antecedents {F : CompletenessFrontier Const Γ}
    (C : LocalConsistentHintikka F) :
    F.succedent ∉ F.antecedents :=
  C.toLocalHintikkaCertificate.succedent_not_mem_antecedents

end LocalConsistentHintikka

/-- A semilocal model together with a global environment that agrees with a
local closed non-contradictory Hintikka certificate by sending every staged
true formula to `⊤` and every staged false formula to a strictly non-top truth
value. This is the current semantic consumer of the paper-facing local
Hintikka layer. -/
structure LocalAgreementWitness (M : SemilocalModel Base Const)
    (F : CompletenessFrontier Const Γ) where
  certificate : LocalHintikkaCertificate F
  env : SemilocalModel.Env M Γ
  global : SemilocalModel.IsGlobalEnv M env
  true_top :
    ∀ {φ : Formula Const Γ},
      (Sign.trueE, φ) ∈ certificate.hintikka.formulas →
        SemilocalModel.formulaTruth M env φ = ⊤
  false_ne_top :
    ∀ {φ : Formula Const Γ},
      (Sign.falseE, φ) ∈ certificate.hintikka.formulas →
        SemilocalModel.formulaTruth M env φ ≠ ⊤

namespace LocalAgreementWitness

theorem antecedentTruth_eq_top
    {M : SemilocalModel Base Const} {F : CompletenessFrontier Const Γ}
    (W : LocalAgreementWitness M F) :
    SemilocalModel.antecedentTruth M W.env F.antecedents = ⊤ :=
  SemilocalModel.antecedentTruth_eq_top_of_forall_mem M W.env
    (by
      intro φ hφ
      exact W.true_top (W.certificate.antecedent_true_mem hφ))

theorem succedent_ne_top
    {M : SemilocalModel Base Const} {F : CompletenessFrontier Const Γ}
    (W : LocalAgreementWitness M F) :
    SemilocalModel.formulaTruth M W.env F.succedent ≠ ⊤ :=
  W.false_ne_top W.certificate.succedent_false_mem

/-- Any global environment agreeing with a local closed non-contradictory
certificate already refutes semantic validity of the frontier sequent. -/
theorem not_validSequent
    {M : SemilocalModel Base Const} {F : CompletenessFrontier Const Γ}
    (W : LocalAgreementWitness M F) :
    ¬ SemilocalModel.ValidSequent M F.antecedents F.succedent := by
  intro hValid
  have htopLe :
      (⊤ : M.Omega) ≤ SemilocalModel.formulaTruth M W.env F.succedent := by
    simpa [W.antecedentTruth_eq_top] using hValid W.env W.global
  have htop :
      SemilocalModel.formulaTruth M W.env F.succedent = ⊤ := by
    apply top_unique
    exact htopLe
  exact W.succedent_ne_top htop

/-- Under semilocal soundness, an agreeing semantic witness rules out
derivability of the frontier sequent. -/
theorem not_derivable
    {M : SemilocalModel Base Const} {F : CompletenessFrontier Const Γ}
    (W : LocalAgreementWitness M F)
    (hM : SemilocalModel.SupportsUniformRelativization M) :
    ¬ Derivable (Base := Base) (Const := Const) F.antecedents F.succedent := by
  intro hDer
  exact W.not_validSequent (SemilocalModel.soundness M hM hDer)

end LocalAgreementWitness

/-- The current semilocal analogue of the paper's local model agreeing with a
frontier-facing local Hintikka certificate. This packages existence of the
model together with the already-defined root agreement witness. -/
structure LocalCountermodel (F : CompletenessFrontier Const Γ) where
  model : SemilocalModel.{u, v, w, w'} Base Const
  agreement : LocalAgreementWitness.{u, v, w, w'} model F

namespace LocalCountermodel

def certificate {F : CompletenessFrontier Const Γ}
    (C : LocalCountermodel F) :
    LocalHintikkaCertificate F :=
  C.agreement.certificate

theorem antecedentTruth_eq_top {F : CompletenessFrontier Const Γ}
    (C : LocalCountermodel F) :
    SemilocalModel.antecedentTruth C.model C.agreement.env F.antecedents = ⊤ :=
  C.agreement.antecedentTruth_eq_top

theorem succedent_ne_top {F : CompletenessFrontier Const Γ}
    (C : LocalCountermodel F) :
    SemilocalModel.formulaTruth C.model C.agreement.env F.succedent ≠ ⊤ :=
  C.agreement.succedent_ne_top

theorem not_validSequent {F : CompletenessFrontier Const Γ}
    (C : LocalCountermodel F) :
    ¬ SemilocalModel.ValidSequent C.model F.antecedents F.succedent :=
  C.agreement.not_validSequent

theorem not_derivable {F : CompletenessFrontier Const Γ}
    (C : LocalCountermodel F)
    (hM : SemilocalModel.SupportsUniformRelativization C.model) :
    ¬ Derivable (Base := Base) (Const := Const) F.antecedents F.succedent :=
  C.agreement.not_derivable hM

end LocalCountermodel

/-- A local countermodel whose underlying semilocal model also satisfies the
uniform relativization hypothesis needed by the current soundness theorem. -/
structure SoundLocalCountermodel (F : CompletenessFrontier Const Γ)
    extends LocalCountermodel F where
  supportsUniformRelativization :
    SemilocalModel.SupportsUniformRelativization model

namespace SoundLocalCountermodel

theorem not_validSequent {F : CompletenessFrontier Const Γ}
    (C : SoundLocalCountermodel F) :
    ¬ SemilocalModel.ValidSequent C.model F.antecedents F.succedent :=
  C.toLocalCountermodel.not_validSequent

theorem not_derivable {F : CompletenessFrontier Const Γ}
    (C : SoundLocalCountermodel F) :
    ¬ Derivable (Base := Base) (Const := Const) F.antecedents F.succedent :=
  C.toLocalCountermodel.not_derivable C.supportsUniformRelativization

end SoundLocalCountermodel

namespace LocalAgreementWitness

/-- Package an agreeing witness as the current semilocal countermodel object. -/
def toLocalCountermodel
    {M : SemilocalModel Base Const} {F : CompletenessFrontier Const Γ}
    (W : LocalAgreementWitness M F) :
    LocalCountermodel F :=
  { model := M
    agreement := W }

/-- Package an agreeing witness together with the semilocal soundness hypothesis
as the stronger countermodel object used to refute derivability. -/
def toSoundLocalCountermodel
    {M : SemilocalModel Base Const} {F : CompletenessFrontier Const Γ}
    (W : LocalAgreementWitness M F)
    (hM : SemilocalModel.SupportsUniformRelativization M) :
    SoundLocalCountermodel F :=
  { toLocalCountermodel := W.toLocalCountermodel
    supportsUniformRelativization := hM }

end LocalAgreementWitness

namespace CountermodelCandidate

/-- Forget the staged search derivation details and retain only the current
semantic-facing world-free Hintikka core. -/
def toLocalHintikkaCore (C : CountermodelCandidate Const Γ) :
    LocalHintikkaCore C.frontier :=
  { hintikka := C.hintikka
    antecedent_true_mem := by
      intro φ hφ
      exact C.true_mem hφ
    succedent_false_mem := C.false_mem
    locallySaturated := C.locallySaturated
    branchClosed := C.branchClosed }

/-- Close the candidate's staged Hintikka set by adjoining the paper-mandated
`T ⊤` and `F ⊥` formulas. -/
def closedHintikka (C : CountermodelCandidate Const Γ) : HintikkaSet Const Γ :=
  C.hintikka.close

theorem closedHintikka_noncontradictory_of_compatibleDerivation
    (C : CountermodelCandidate Const Γ)
    (hInitial :
      (SaturationSearchState.initial C.frontier).hintikka.close.Noncontradictory)
    (hCompat : C.completion.derivation.Compatible) :
    C.closedHintikka.Noncontradictory :=
  C.completion.closed_noncontradictory_of_compatibleDerivation hInitial hCompat

theorem closedHintikka_closed
    (C : CountermodelCandidate Const Γ) :
    C.closedHintikka.Closed :=
  HintikkaSet.closed_close C.hintikka

theorem closedHintikka_locallySaturated
    (C : CountermodelCandidate Const Γ) :
    C.closedHintikka.LocallySaturated :=
  HintikkaSet.locallySaturated_close C.locallySaturated

theorem closedHintikka_branchClosed
    (C : CountermodelCandidate Const Γ) :
    C.closedHintikka.BranchClosed :=
  HintikkaSet.branchClosed_close C.branchClosed

theorem closedHintikka_noncontradictory_of_initialResolveHead
    (C : CountermodelCandidate Const Γ)
    {r : SaturationSearchState.LocalBranchResolution Const Γ}
    (hhead : (SaturationSearchState.initial C.frontier).CanResolveHead r)
    (hState :
      C.state = (SaturationSearchState.initial C.frontier).resolveHead r hhead)
    (hInitial :
      (SaturationSearchState.initial C.frontier).hintikka.close.Noncontradictory)
    (hCompat :
      (SaturationSearchState.initial C.frontier).BranchAdditionCompatible r) :
    C.closedHintikka.Noncontradictory := by
  unfold CountermodelCandidate.closedHintikka CountermodelCandidate.hintikka
  rw [hState]
  exact SaturationSearchState.closed_noncontradictory_resolveHead_of_branchAdditionCompatible
    (S := SaturationSearchState.initial C.frontier) hInitial (r := r) (hhead := hhead) hCompat

theorem true_mem_closedHintikka
    (C : CountermodelCandidate Const Γ)
    {φ : Formula Const Γ} (hφ : φ ∈ C.frontier.antecedents) :
    (Sign.trueE, φ) ∈ C.closedHintikka.formulas :=
  HintikkaSet.mem_close_of_mem (C.true_mem hφ)

theorem false_mem_closedHintikka
    (C : CountermodelCandidate Const Γ) :
    (Sign.falseE, C.frontier.succedent) ∈ C.closedHintikka.formulas :=
  HintikkaSet.mem_close_of_mem C.false_mem

/-- The closed-hull search candidate keeps the frontier witness data while
upgrading the staged Hintikka set to a closed one. -/
def toClosedLocalHintikkaCore
    (C : CountermodelCandidate Const Γ) :
    LocalHintikkaCore C.frontier :=
  { hintikka := C.closedHintikka
    antecedent_true_mem := by
      intro φ hφ
      exact C.true_mem_closedHintikka hφ
    succedent_false_mem := C.false_mem_closedHintikka
    locallySaturated := C.closedHintikka_locallySaturated
    branchClosed := C.closedHintikka_branchClosed }

theorem not_derivable_succedent
    (C : CountermodelCandidate Const Γ)
    (hCons : C.hintikka.ICTTConsistent) :
    ¬ Derivable (Base := Base) (Const := Const) C.hintikka.trueFormulas C.frontier.succedent :=
  HintikkaSet.not_derivable_of_false_mem_of_icttConsistent hCons C.false_mem

theorem closed_not_derivable_succedent
    (C : CountermodelCandidate Const Γ)
    (hCons : C.closedHintikka.ICTTConsistent) :
    ¬ Derivable (Base := Base) (Const := Const) C.closedHintikka.trueFormulas C.frontier.succedent :=
  HintikkaSet.not_derivable_of_false_mem_of_icttConsistent hCons C.false_mem_closedHintikka

theorem noncontradictory
    (C : CountermodelCandidate Const Γ)
    (hClosed : C.hintikka.Closed)
    (hCons : C.hintikka.ICTTConsistent) :
    C.hintikka.Noncontradictory :=
  HintikkaSet.noncontradictory_of_closed_icttConsistent hClosed hCons

/-- Upgrade a terminal search candidate to the weaker paper-facing certificate
once closedness and non-contradiction have been established. -/
def toLocalHintikkaCertificate
    (C : CountermodelCandidate Const Γ)
    (hClosed : C.hintikka.Closed)
    (hCons : C.hintikka.ICTTConsistent) :
    LocalHintikkaCertificate C.frontier :=
  { toLocalHintikkaCore := C.toLocalHintikkaCore
    closed := hClosed
    noncontradictory := C.noncontradictory hClosed hCons }

/-- Upgrade a terminal search candidate to the stronger local consistent
Hintikka object once closedness and ICTT-consistency are supplied. -/
def toLocalConsistentHintikka
    (C : CountermodelCandidate Const Γ)
    (hClosed : C.hintikka.Closed)
    (hCons : C.hintikka.ICTTConsistent) :
    LocalConsistentHintikka C.frontier :=
  { toLocalHintikkaCore := C.toLocalHintikkaCore
    closed := hClosed
    consistent := hCons }

/-- Upgrade the closed hull of a terminal search candidate to a local
consistent Hintikka object once ICTT-consistency of that closed hull has been
supplied. -/
def toClosedLocalConsistentHintikka
    (C : CountermodelCandidate Const Γ)
    (hCons : C.closedHintikka.ICTTConsistent) :
    LocalConsistentHintikka C.frontier :=
  { toLocalHintikkaCore := C.toClosedLocalHintikkaCore
    closed := C.closedHintikka_closed
    consistent := hCons }

/-- Upgrade the closed hull of a terminal search candidate directly to the
paper-facing local Hintikka certificate once non-contradiction of that closed
hull has been supplied. -/
def toClosedLocalHintikkaCertificate
    (C : CountermodelCandidate Const Γ)
    (hNoncontradictory : C.closedHintikka.Noncontradictory) :
    LocalHintikkaCertificate C.frontier :=
  { toLocalHintikkaCore := C.toClosedLocalHintikkaCore
    closed := C.closedHintikka_closed
    noncontradictory := hNoncontradictory }

/-- Package a terminal candidate coming from one compatible initial head
resolution directly as a closed non-contradictory certificate. -/
def toClosedLocalHintikkaCertificateOfInitialResolveHead
    (C : CountermodelCandidate Const Γ)
    {r : SaturationSearchState.LocalBranchResolution Const Γ}
    (hhead : (SaturationSearchState.initial C.frontier).CanResolveHead r)
    (hState :
      C.state = (SaturationSearchState.initial C.frontier).resolveHead r hhead)
    (hInitial :
      (SaturationSearchState.initial C.frontier).hintikka.close.Noncontradictory)
    (hCompat :
      (SaturationSearchState.initial C.frontier).BranchAdditionCompatible r) :
    LocalHintikkaCertificate C.frontier :=
  C.toClosedLocalHintikkaCertificate
    (C.closedHintikka_noncontradictory_of_initialResolveHead
      hhead hState hInitial hCompat)

/-- Package a terminal candidate whose whole head-priority derivation is
compatible as a closed non-contradictory certificate. -/
def toClosedLocalHintikkaCertificateOfCompatibleDerivation
    (C : CountermodelCandidate Const Γ)
    (hInitial :
      (SaturationSearchState.initial C.frontier).hintikka.close.Noncontradictory)
    (hCompat : C.completion.derivation.Compatible) :
    LocalHintikkaCertificate C.frontier :=
  C.toClosedLocalHintikkaCertificate
    (C.closedHintikka_noncontradictory_of_compatibleDerivation hInitial hCompat)

/-- Turn a terminal search candidate into an agreement witness once the semantic
agreement data for its staged Hintikka set is available. -/
def toLocalAgreementWitness
    {M : SemilocalModel Base Const}
    (C : CountermodelCandidate Const Γ)
    (hClosed : C.hintikka.Closed)
    (hCons : C.hintikka.ICTTConsistent)
    (env : SemilocalModel.Env M Γ)
    (global : SemilocalModel.IsGlobalEnv M env)
    (true_top :
      ∀ {φ : Formula Const Γ},
        (Sign.trueE, φ) ∈ C.hintikka.formulas →
          SemilocalModel.formulaTruth M env φ = ⊤)
    (false_ne_top :
      ∀ {φ : Formula Const Γ},
        (Sign.falseE, φ) ∈ C.hintikka.formulas →
          SemilocalModel.formulaTruth M env φ ≠ ⊤) :
    LocalAgreementWitness M C.frontier :=
  { certificate := C.toLocalHintikkaCertificate hClosed hCons
    env := env
    global := global
    true_top := by
      intro φ hφ
      simpa [CountermodelCandidate.toLocalHintikkaCertificate,
        CountermodelCandidate.toLocalHintikkaCore] using true_top hφ
    false_ne_top := by
      intro φ hφ
      simpa [CountermodelCandidate.toLocalHintikkaCertificate,
        CountermodelCandidate.toLocalHintikkaCore] using false_ne_top hφ }

/-- Package a terminal search candidate as the current local countermodel object
once the remaining semantic agreement data has been supplied. -/
def toLocalCountermodel
    {M : SemilocalModel Base Const}
    (C : CountermodelCandidate Const Γ)
    (hClosed : C.hintikka.Closed)
    (hCons : C.hintikka.ICTTConsistent)
    (env : SemilocalModel.Env M Γ)
    (global : SemilocalModel.IsGlobalEnv M env)
    (true_top :
      ∀ {φ : Formula Const Γ},
        (Sign.trueE, φ) ∈ C.hintikka.formulas →
          SemilocalModel.formulaTruth M env φ = ⊤)
    (false_ne_top :
      ∀ {φ : Formula Const Γ},
        (Sign.falseE, φ) ∈ C.hintikka.formulas →
          SemilocalModel.formulaTruth M env φ ≠ ⊤) :
    LocalCountermodel C.frontier :=
  (C.toLocalAgreementWitness hClosed hCons env global true_top false_ne_top).toLocalCountermodel

/-- Strengthen the candidate-to-countermodel bridge with the semilocal soundness
hypothesis needed to refute derivability. -/
def toSoundLocalCountermodel
    {M : SemilocalModel Base Const}
    (C : CountermodelCandidate Const Γ)
    (hClosed : C.hintikka.Closed)
    (hCons : C.hintikka.ICTTConsistent)
    (env : SemilocalModel.Env M Γ)
    (global : SemilocalModel.IsGlobalEnv M env)
    (true_top :
      ∀ {φ : Formula Const Γ},
        (Sign.trueE, φ) ∈ C.hintikka.formulas →
          SemilocalModel.formulaTruth M env φ = ⊤)
    (false_ne_top :
      ∀ {φ : Formula Const Γ},
        (Sign.falseE, φ) ∈ C.hintikka.formulas →
          SemilocalModel.formulaTruth M env φ ≠ ⊤)
    (hM : SemilocalModel.SupportsUniformRelativization M) :
    SoundLocalCountermodel C.frontier :=
  (C.toLocalAgreementWitness hClosed hCons env global true_top false_ne_top).toSoundLocalCountermodel hM

/-- Turn the closed hull of a terminal search candidate into an agreement
witness once semantic agreement data and non-contradiction have been provided
for the closed hull. -/
def toClosedLocalAgreementWitnessOfNoncontradictory
    {M : SemilocalModel Base Const}
    (C : CountermodelCandidate Const Γ)
    (hNoncontradictory : C.closedHintikka.Noncontradictory)
    (env : SemilocalModel.Env M Γ)
    (global : SemilocalModel.IsGlobalEnv M env)
    (true_top :
      ∀ {φ : Formula Const Γ},
        (Sign.trueE, φ) ∈ C.closedHintikka.formulas →
          SemilocalModel.formulaTruth M env φ = ⊤)
    (false_ne_top :
      ∀ {φ : Formula Const Γ},
        (Sign.falseE, φ) ∈ C.closedHintikka.formulas →
          SemilocalModel.formulaTruth M env φ ≠ ⊤) :
    LocalAgreementWitness M C.frontier :=
  { certificate := C.toClosedLocalHintikkaCertificate hNoncontradictory
    env := env
    global := global
    true_top := by
      intro φ hφ
      simpa [CountermodelCandidate.toClosedLocalHintikkaCertificate,
        CountermodelCandidate.toClosedLocalHintikkaCore,
        CountermodelCandidate.closedHintikka] using true_top hφ
    false_ne_top := by
      intro φ hφ
      simpa [CountermodelCandidate.toClosedLocalHintikkaCertificate,
        CountermodelCandidate.toClosedLocalHintikkaCore,
        CountermodelCandidate.closedHintikka] using false_ne_top hφ }

/-- Turn the closed hull of a terminal search candidate into an agreement
witness once ICTT-consistency has been established for that closed hull. This
stronger route simply recovers the non-contradiction required by the more
paper-faithful semantic interface. -/
def toClosedLocalAgreementWitness
    {M : SemilocalModel Base Const}
    (C : CountermodelCandidate Const Γ)
    (hCons : C.closedHintikka.ICTTConsistent)
    (env : SemilocalModel.Env M Γ)
    (global : SemilocalModel.IsGlobalEnv M env)
    (true_top :
      ∀ {φ : Formula Const Γ},
        (Sign.trueE, φ) ∈ C.closedHintikka.formulas →
          SemilocalModel.formulaTruth M env φ = ⊤)
    (false_ne_top :
      ∀ {φ : Formula Const Γ},
        (Sign.falseE, φ) ∈ C.closedHintikka.formulas →
          SemilocalModel.formulaTruth M env φ ≠ ⊤) :
    LocalAgreementWitness M C.frontier :=
  C.toClosedLocalAgreementWitnessOfNoncontradictory
    (C.toClosedLocalConsistentHintikka hCons).noncontradictory
    env global true_top false_ne_top

/-- Package the closed hull of a terminal search candidate as the current local
countermodel object once the remaining semantic agreement data and
non-contradiction are available. -/
def toClosedLocalCountermodelOfNoncontradictory
    {M : SemilocalModel Base Const}
    (C : CountermodelCandidate Const Γ)
    (hNoncontradictory : C.closedHintikka.Noncontradictory)
    (env : SemilocalModel.Env M Γ)
    (global : SemilocalModel.IsGlobalEnv M env)
    (true_top :
      ∀ {φ : Formula Const Γ},
        (Sign.trueE, φ) ∈ C.closedHintikka.formulas →
          SemilocalModel.formulaTruth M env φ = ⊤)
    (false_ne_top :
      ∀ {φ : Formula Const Γ},
        (Sign.falseE, φ) ∈ C.closedHintikka.formulas →
          SemilocalModel.formulaTruth M env φ ≠ ⊤) :
    LocalCountermodel C.frontier :=
  (C.toClosedLocalAgreementWitnessOfNoncontradictory
      hNoncontradictory env global true_top false_ne_top).toLocalCountermodel

/-- Package the closed hull of a terminal search candidate as the current local
countermodel object once ICTT-consistency has been established for that closed
hull. -/
def toClosedLocalCountermodel
    {M : SemilocalModel Base Const}
    (C : CountermodelCandidate Const Γ)
    (hCons : C.closedHintikka.ICTTConsistent)
    (env : SemilocalModel.Env M Γ)
    (global : SemilocalModel.IsGlobalEnv M env)
    (true_top :
      ∀ {φ : Formula Const Γ},
        (Sign.trueE, φ) ∈ C.closedHintikka.formulas →
          SemilocalModel.formulaTruth M env φ = ⊤)
    (false_ne_top :
      ∀ {φ : Formula Const Γ},
        (Sign.falseE, φ) ∈ C.closedHintikka.formulas →
          SemilocalModel.formulaTruth M env φ ≠ ⊤) :
    LocalCountermodel C.frontier :=
  C.toClosedLocalCountermodelOfNoncontradictory
    (C.toClosedLocalConsistentHintikka hCons).noncontradictory
    env global true_top false_ne_top

/-- Strengthen the closed-hull candidate-to-countermodel bridge with the
semilocal soundness hypothesis needed to refute derivability once
non-contradiction is available. -/
def toClosedSoundLocalCountermodelOfNoncontradictory
    {M : SemilocalModel Base Const}
    (C : CountermodelCandidate Const Γ)
    (hNoncontradictory : C.closedHintikka.Noncontradictory)
    (env : SemilocalModel.Env M Γ)
    (global : SemilocalModel.IsGlobalEnv M env)
    (true_top :
      ∀ {φ : Formula Const Γ},
        (Sign.trueE, φ) ∈ C.closedHintikka.formulas →
          SemilocalModel.formulaTruth M env φ = ⊤)
    (false_ne_top :
      ∀ {φ : Formula Const Γ},
        (Sign.falseE, φ) ∈ C.closedHintikka.formulas →
          SemilocalModel.formulaTruth M env φ ≠ ⊤)
    (hM : SemilocalModel.SupportsUniformRelativization M) :
    SoundLocalCountermodel C.frontier :=
  (C.toClosedLocalAgreementWitnessOfNoncontradictory
      hNoncontradictory env global true_top false_ne_top).toSoundLocalCountermodel hM

/-- Strengthen the closed-hull candidate-to-countermodel bridge with the
semilocal soundness hypothesis needed to refute derivability once
ICTT-consistency has been established for that closed hull. -/
def toClosedSoundLocalCountermodel
    {M : SemilocalModel Base Const}
    (C : CountermodelCandidate Const Γ)
    (hCons : C.closedHintikka.ICTTConsistent)
    (env : SemilocalModel.Env M Γ)
    (global : SemilocalModel.IsGlobalEnv M env)
    (true_top :
      ∀ {φ : Formula Const Γ},
        (Sign.trueE, φ) ∈ C.closedHintikka.formulas →
          SemilocalModel.formulaTruth M env φ = ⊤)
    (false_ne_top :
      ∀ {φ : Formula Const Γ},
        (Sign.falseE, φ) ∈ C.closedHintikka.formulas →
          SemilocalModel.formulaTruth M env φ ≠ ⊤)
    (hM : SemilocalModel.SupportsUniformRelativization M) :
    SoundLocalCountermodel C.frontier :=
  C.toClosedSoundLocalCountermodelOfNoncontradictory
    (C.toClosedLocalConsistentHintikka hCons).noncontradictory
    env global true_top false_ne_top hM

end CountermodelCandidate

namespace CompletenessFrontier

/-- View a frontier as the underlying sequent-style Hintikka goal. -/
def toHintikkaGoal (F : CompletenessFrontier Const Γ) : HintikkaGoal Const Γ :=
  { antecedents := F.antecedents
    succedent := F.succedent }

/-- Frontier-level side conditions excluding the three immediate contradictions
created when the paper's `T ⊤` and `F ⊥` closure formulas are adjoined to the
initial signed sequent data. -/
def ClosedNonconflicting (F : CompletenessFrontier Const Γ) : Prop :=
  (.bot : Formula Const Γ) ∉ F.antecedents ∧
    F.succedent ≠ (.top : Formula Const Γ) ∧
    F.succedent ∉ F.antecedents

/-- Initial signed data from which a saturation search would start. -/
def initialHintikkaSet (F : CompletenessFrontier Const Γ) : HintikkaSet Const Γ :=
  F.toHintikkaGoal.toHintikkaSet

theorem true_mem_initialHintikkaSet {F : CompletenessFrontier Const Γ}
    {φ : Formula Const Γ} (h : φ ∈ F.antecedents) :
    (Sign.trueE, φ) ∈ F.initialHintikkaSet.formulas := by
  exact HintikkaGoal.true_mem_toHintikkaSet h

theorem false_mem_initialHintikkaSet (F : CompletenessFrontier Const Γ) :
    (Sign.falseE, F.succedent) ∈ F.initialHintikkaSet.formulas := by
  exact HintikkaGoal.false_mem_toHintikkaSet F.toHintikkaGoal

@[simp] theorem trueFormulas_initialHintikkaSet
    (F : CompletenessFrontier Const Γ) :
    F.initialHintikkaSet.trueFormulas = F.antecedents := by
  exact HintikkaGoal.trueFormulas_toHintikkaSet F.toHintikkaGoal

@[simp] theorem falseFormulas_initialHintikkaSet
    (F : CompletenessFrontier Const Γ) :
    F.initialHintikkaSet.falseFormulas = [F.succedent] := by
  exact HintikkaGoal.falseFormulas_toHintikkaSet F.toHintikkaGoal

theorem true_mem_initialClosedHintikka_iff
    (F : CompletenessFrontier Const Γ)
    {φ : Formula Const Γ} :
    (Sign.trueE, φ) ∈ F.initialHintikkaSet.close.formulas ↔
      φ = (.top : Formula Const Γ) ∨ φ ∈ F.antecedents := by
  simp [initialHintikkaSet, toHintikkaGoal, HintikkaGoal.toHintikkaSet,
    HintikkaGoal.signedFormulas, HintikkaSet.close]
  constructor
  · intro h
    rcases List.mem_cons.mp h with hTop | hRest
    · cases hTop
      exact Or.inl rfl
    rcases List.mem_cons.mp hRest with hFalseBot | hTail
    · cases hFalseBot
    rcases List.mem_append.mp hTail with hMap | hSucc
    · rcases List.mem_map.mp hMap with ⟨ψ, hψ, hEq⟩
      cases hEq
      exact Or.inr hψ
    · rcases List.mem_singleton.mp hSucc with hEq
      cases hEq
  · rintro (rfl | hφ)
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ <|
        List.mem_cons_of_mem _ <|
          List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨φ, hφ, rfl⟩))

theorem false_mem_initialClosedHintikka_iff
    (F : CompletenessFrontier Const Γ)
    {φ : Formula Const Γ} :
    (Sign.falseE, φ) ∈ F.initialHintikkaSet.close.formulas ↔
      φ = (.bot : Formula Const Γ) ∨ φ = F.succedent := by
  simp [initialHintikkaSet, toHintikkaGoal, HintikkaGoal.toHintikkaSet,
    HintikkaGoal.signedFormulas, HintikkaSet.close]
  constructor
  · intro h
    rcases List.mem_cons.mp h with hTrueTop | hRest
    · cases hTrueTop
    rcases List.mem_cons.mp hRest with hBot | hTail
    · cases hBot
      exact Or.inl rfl
    rcases List.mem_append.mp hTail with hMap | hSucc
    · rcases List.mem_map.mp hMap with ⟨ψ, _hψ, hEq⟩
      cases hEq
    · rcases List.mem_singleton.mp hSucc with hEq
      cases hEq
      exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact List.mem_cons_of_mem _ List.mem_cons_self
    · exact List.mem_cons_of_mem _ <|
        List.mem_cons_of_mem _ <|
          List.mem_append.mpr (Or.inr (List.mem_singleton_self (Sign.falseE, F.succedent)))

theorem initialHintikkaSet_close_noncontradictory_iff
    (F : CompletenessFrontier Const Γ) :
    F.initialHintikkaSet.close.Noncontradictory ↔ F.ClosedNonconflicting := by
  constructor
  · intro hNoncontradictory
    refine ⟨?_, ?_, ?_⟩
    · intro hBot
      have hTrueBot :
          (Sign.trueE, (.bot : Formula Const Γ)) ∈ F.initialHintikkaSet.close.formulas :=
        (F.true_mem_initialClosedHintikka_iff).2 (Or.inr hBot)
      exact (HintikkaSet.trueBot_not_mem_of_noncontradictory hNoncontradictory) hTrueBot
    · intro hTop
      have hFalseTop :
          (Sign.falseE, (.top : Formula Const Γ)) ∈ F.initialHintikkaSet.close.formulas := by
        exact (F.false_mem_initialClosedHintikka_iff).2 (Or.inr hTop.symm)
      exact (HintikkaSet.falseTop_not_mem_of_noncontradictory hNoncontradictory) hFalseTop
    · intro hSucc
      have hTrueSucc :
          (Sign.trueE, F.succedent) ∈ F.initialHintikkaSet.close.formulas :=
        (F.true_mem_initialClosedHintikka_iff).2 (Or.inr hSucc)
      have hFalseSucc :
          (Sign.falseE, F.succedent) ∈ F.initialHintikkaSet.close.formulas :=
        HintikkaSet.mem_close_of_mem F.false_mem_initialHintikkaSet
      exact
        (HintikkaSet.true_not_mem_of_false_mem_of_noncontradictory
          hNoncontradictory hFalseSucc) hTrueSucc
  · rintro ⟨hNoBot, hSuccNeTop, hSuccNotMem⟩
    intro hContra
    rcases hContra with hConflict | hSpecial
    · rcases hConflict with ⟨φ, hTrue, hFalse⟩
      rcases (F.true_mem_initialClosedHintikka_iff.mp hTrue) with hTop | hAnt
      · subst φ
        rcases (F.false_mem_initialClosedHintikka_iff.mp hFalse) with hBot | hSucc
        · simp at hBot
        · exact hSuccNeTop hSucc.symm
      · rcases (F.false_mem_initialClosedHintikka_iff.mp hFalse) with hBot | hSucc
        · subst φ
          exact hNoBot hAnt
        · subst φ
          exact hSuccNotMem hAnt
    · rcases hSpecial with hTrueBot | hFalseTop
      · rcases (F.true_mem_initialClosedHintikka_iff.mp hTrueBot) with hTop | hBot
        · simp at hTop
        · exact hNoBot hBot
      · rcases (F.false_mem_initialClosedHintikka_iff.mp hFalseTop) with hBot | hSucc
        · simp at hBot
        · exact hSuccNeTop hSucc.symm

theorem initialHintikkaSet_icttConsistent_iff_not_derivable
    (F : CompletenessFrontier Const Γ) :
    F.initialHintikkaSet.ICTTConsistent ↔
      ¬ Derivable (Base := Base) (Const := Const) F.antecedents F.succedent := by
  simpa [initialHintikkaSet, toHintikkaGoal] using
    HintikkaGoal.icttConsistent_toHintikkaSet_iff_not_derivable F.toHintikkaGoal

@[simp] theorem initial_hintikka_eq_initialHintikkaSet
    (F : CompletenessFrontier Const Γ) :
    (SaturationSearchState.initial F).hintikka = F.initialHintikkaSet := by
  rfl

theorem initial_closed_noncontradictory_iff
    (F : CompletenessFrontier Const Γ) :
    (SaturationSearchState.initial F).hintikka.close.Noncontradictory ↔
      F.ClosedNonconflicting := by
  simpa [CompletenessFrontier.initialHintikkaSet] using
    F.initialHintikkaSet_close_noncontradictory_iff

theorem initial_icttConsistent_iff_not_derivable
    (F : CompletenessFrontier Const Γ) :
    (SaturationSearchState.initial F).hintikka.ICTTConsistent ↔
      ¬ Derivable (Base := Base) (Const := Const) F.antecedents F.succedent := by
  simpa [CompletenessFrontier.initialHintikkaSet] using
    F.initialHintikkaSet_icttConsistent_iff_not_derivable

end CompletenessFrontier

namespace SaturationSearchState.HeadPrioritySearchDerivation

theorem closed_noncontradictory_of_closedNonconflicting
    {F : CompletenessFrontier Const Γ}
    {S : SaturationSearchState Const Γ} (D : HeadPrioritySearchDerivation F S)
    (hInitial : F.ClosedNonconflicting)
    (hCompat : D.Compatible) :
    S.hintikka.close.Noncontradictory :=
  D.closed_noncontradictory
    ((CompletenessFrontier.initial_closed_noncontradictory_iff F).2 hInitial)
    hCompat

end SaturationSearchState.HeadPrioritySearchDerivation

namespace SaturationSearchState.HeadPriorityCompletion

theorem closed_noncontradictory_of_closedNonconflicting
    {F : CompletenessFrontier Const Γ}
    (C : HeadPriorityCompletion F)
    (hInitial : F.ClosedNonconflicting)
    (hCompat : C.derivation.Compatible) :
    C.state.hintikka.close.Noncontradictory :=
  C.derivation.closed_noncontradictory_of_closedNonconflicting hInitial hCompat

end SaturationSearchState.HeadPriorityCompletion

/-- A head-priority derivation together with the frontier-side closed-hull sanity
condition and the stepwise compatibility evidence needed to keep its closed
Hintikka hull noncontradictory throughout the run. Unlike
`CertifiedHeadPriorityCompletion`, this structure does not require terminality,
so it can be extended compositionally by further scheduler-approved steps. -/
structure CertifiedHeadPriorityDerivation
    (Const : Ty Base → Type v) (Γ : Ctx Base)
    (F : CompletenessFrontier Const Γ) where
  state : SaturationSearchState Const Γ
  derivation : SaturationSearchState.HeadPrioritySearchDerivation F state
  closedNonconflicting : F.ClosedNonconflicting
  compatible : derivation.Compatible

namespace CertifiedHeadPriorityDerivation

def frontier (_ : CertifiedHeadPriorityDerivation Const Γ F) :
    CompletenessFrontier Const Γ :=
  F

def hintikka (D : CertifiedHeadPriorityDerivation Const Γ F) :
    HintikkaSet Const Γ :=
  D.state.hintikka

def closedHintikka (D : CertifiedHeadPriorityDerivation Const Γ F) :
    HintikkaSet Const Γ :=
  D.hintikka.close

def initial {F : CompletenessFrontier Const Γ}
    (hInitial : F.ClosedNonconflicting) :
    CertifiedHeadPriorityDerivation Const Γ F where
  state := SaturationSearchState.initial F
  derivation := SaturationSearchState.HeadPrioritySearchDerivation.initial
  closedNonconflicting := hInitial
  compatible := SaturationSearchState.HeadPrioritySearchDerivation.compatible_initial

def saturate
    {F : CompletenessFrontier Const Γ}
    (C : CertifiedHeadPriorityDerivation Const Γ F)
    (hIdle : C.state.agenda = [])
    (t : SaturationSearchState.ProductiveTriggeredLocalStep C.state)
    (hCompat : C.state.DeterministicAdditionCompatible t.step) :
    CertifiedHeadPriorityDerivation Const Γ F where
  state := C.state.applyLocalStep t.step.toLocalSaturationStep
  derivation := SaturationSearchState.HeadPrioritySearchDerivation.saturate
    C.derivation hIdle t
  closedNonconflicting := C.closedNonconflicting
  compatible := SaturationSearchState.HeadPrioritySearchDerivation.compatible_saturate
    C.derivation hIdle t C.compatible hCompat

def resolveHead
    {F : CompletenessFrontier Const Γ}
    (C : CertifiedHeadPriorityDerivation Const Γ F)
    (r : SaturationSearchState.LocalBranchResolution Const Γ)
    (hhead : C.state.CanResolveHead r)
    (hCompat : C.state.BranchAdditionCompatible r) :
    CertifiedHeadPriorityDerivation Const Γ F where
  state := C.state.resolveHead r hhead
  derivation := SaturationSearchState.HeadPrioritySearchDerivation.resolveHead
    C.derivation r hhead
  closedNonconflicting := C.closedNonconflicting
  compatible := SaturationSearchState.HeadPrioritySearchDerivation.compatible_resolveHead
    C.derivation r hhead C.compatible hCompat

theorem closedHintikka_noncontradictory
    {F : CompletenessFrontier Const Γ}
    (C : CertifiedHeadPriorityDerivation Const Γ F) :
    C.closedHintikka.Noncontradictory :=
  C.derivation.closed_noncontradictory_of_closedNonconflicting
    C.closedNonconflicting C.compatible

/-- Build a certified derivation from a single scheduler-approved productive
deterministic saturation step taken from the initial search state. -/
def ofInitialSaturate
    {F : CompletenessFrontier Const Γ}
    (hInitial : F.ClosedNonconflicting)
    (hIdle : (SaturationSearchState.initial F).agenda = [])
    (t : SaturationSearchState.ProductiveTriggeredLocalStep
      (SaturationSearchState.initial F))
    (hCompat :
      (SaturationSearchState.initial F).DeterministicAdditionCompatible t.step) :
    CertifiedHeadPriorityDerivation Const Γ F :=
  (initial (Const := Const) (Γ := Γ) hInitial).saturate hIdle t hCompat

/-- Build a certified derivation from a single scheduler-approved head
resolution taken from the initial search state. -/
def ofInitialResolveHead
    {F : CompletenessFrontier Const Γ}
    (hInitial : F.ClosedNonconflicting)
    (r : SaturationSearchState.LocalBranchResolution Const Γ)
    (hhead : (SaturationSearchState.initial F).CanResolveHead r)
    (hCompat :
      (SaturationSearchState.initial F).BranchAdditionCompatible r) :
    CertifiedHeadPriorityDerivation Const Γ F :=
  (initial (Const := Const) (Γ := Γ) hInitial).resolveHead r hhead hCompat

/-- Build a certified derivation from an initial productive deterministic
saturation step followed by a scheduler-approved head resolution. This is the
smallest mixed run needed by the current regression canaries. -/
def ofInitialSaturateThenResolveHead
    {F : CompletenessFrontier Const Γ}
    (hInitial : F.ClosedNonconflicting)
    (hIdle : (SaturationSearchState.initial F).agenda = [])
    (t : SaturationSearchState.ProductiveTriggeredLocalStep
      (SaturationSearchState.initial F))
    (r : SaturationSearchState.LocalBranchResolution Const Γ)
    (hhead :
      (SaturationSearchState.applyLocalStep
        (SaturationSearchState.initial F) t.step.toLocalSaturationStep).CanResolveHead r)
    (hCompat₁ :
      (SaturationSearchState.initial F).DeterministicAdditionCompatible t.step)
    (hCompat₂ :
      (SaturationSearchState.applyLocalStep
        (SaturationSearchState.initial F) t.step.toLocalSaturationStep).BranchAdditionCompatible r) :
    CertifiedHeadPriorityDerivation Const Γ F :=
  ((initial (Const := Const) (Γ := Γ) hInitial).saturate hIdle t hCompat₁).resolveHead
    r hhead hCompat₂

end CertifiedHeadPriorityDerivation

/-- A terminal head-priority completion together with the search-side side
conditions currently needed to upgrade its closed hull into paper-facing
Hintikka and countermodel data. Bundling these obligations here keeps the
certificate layer attached to genuine search completions rather than only to
post hoc countermodel candidates. -/
structure CertifiedHeadPriorityCompletion
    (Const : Ty Base → Type v) (Γ : Ctx Base)
    (F : CompletenessFrontier Const Γ) where
  completion : SaturationSearchState.HeadPriorityCompletion F
  closedNonconflicting : F.ClosedNonconflicting
  compatible : completion.derivation.Compatible

namespace CertifiedHeadPriorityCompletion

def frontier (_ : CertifiedHeadPriorityCompletion Const Γ F) :
    CompletenessFrontier Const Γ :=
  F

def state (C : CertifiedHeadPriorityCompletion Const Γ F) :
    SaturationSearchState Const Γ :=
  C.completion.state

def hintikka (C : CertifiedHeadPriorityCompletion Const Γ F) :
    HintikkaSet Const Γ :=
  C.state.hintikka

def closedHintikka (C : CertifiedHeadPriorityCompletion Const Γ F) :
    HintikkaSet Const Γ :=
  C.hintikka.close

theorem closedHintikka_noncontradictory
    (C : CertifiedHeadPriorityCompletion Const Γ F) :
    C.closedHintikka.Noncontradictory :=
  C.completion.closed_noncontradictory_of_closedNonconflicting
    C.closedNonconflicting C.compatible

def ofCertifiedDerivation
    {F : CompletenessFrontier Const Γ}
    (D : CertifiedHeadPriorityDerivation Const Γ F)
    (terminal : D.state.IsTerminal)
    (branchClosed : D.state.hintikka.BranchClosed) :
    CertifiedHeadPriorityCompletion Const Γ F where
  completion :=
    { state := D.state
      derivation := D.derivation
      terminal := terminal
      branchClosed := branchClosed }
  closedNonconflicting := D.closedNonconflicting
  compatible := D.compatible

/-- Build a certified completion from a single scheduler-approved productive
deterministic saturation step taken from the initial search state. -/
def ofInitialSaturate
    {F : CompletenessFrontier Const Γ}
    (hInitial : F.ClosedNonconflicting)
    (hIdle : (SaturationSearchState.initial F).agenda = [])
    (t : SaturationSearchState.ProductiveTriggeredLocalStep
      (SaturationSearchState.initial F))
    (terminal :
      (SaturationSearchState.applyLocalStep
        (SaturationSearchState.initial F) t.step.toLocalSaturationStep).IsTerminal)
    (branchClosed :
      (SaturationSearchState.applyLocalStep
        (SaturationSearchState.initial F) t.step.toLocalSaturationStep).hintikka.BranchClosed)
    (hCompat :
      (SaturationSearchState.initial F).DeterministicAdditionCompatible t.step) :
    CertifiedHeadPriorityCompletion Const Γ F :=
  ofCertifiedDerivation
    (CertifiedHeadPriorityDerivation.ofInitialSaturate
      (Const := Const) (Γ := Γ) hInitial hIdle t hCompat)
    terminal branchClosed

/-- Build a certified completion from a single scheduler-approved head
resolution taken from the initial search state. -/
def ofInitialResolveHead
    {F : CompletenessFrontier Const Γ}
    (hInitial : F.ClosedNonconflicting)
    (r : SaturationSearchState.LocalBranchResolution Const Γ)
    (hhead : (SaturationSearchState.initial F).CanResolveHead r)
    (terminal :
      ((SaturationSearchState.initial F).resolveHead r hhead).IsTerminal)
    (branchClosed :
      ((SaturationSearchState.initial F).resolveHead r hhead).hintikka.BranchClosed)
    (hCompat :
      (SaturationSearchState.initial F).BranchAdditionCompatible r) :
    CertifiedHeadPriorityCompletion Const Γ F :=
  ofCertifiedDerivation
    (CertifiedHeadPriorityDerivation.ofInitialResolveHead
      (Const := Const) (Γ := Γ) hInitial r hhead hCompat)
    terminal branchClosed

/-- Build a certified completion from an initial productive deterministic
saturation step followed by a scheduler-approved head resolution. This is the
smallest mixed run needed by the current regression canaries. -/
def ofInitialSaturateThenResolveHead
    {F : CompletenessFrontier Const Γ}
    (hInitial : F.ClosedNonconflicting)
    (hIdle : (SaturationSearchState.initial F).agenda = [])
    (t : SaturationSearchState.ProductiveTriggeredLocalStep
      (SaturationSearchState.initial F))
    (r : SaturationSearchState.LocalBranchResolution Const Γ)
    (hhead :
      (SaturationSearchState.applyLocalStep
        (SaturationSearchState.initial F) t.step.toLocalSaturationStep).CanResolveHead r)
    (terminal :
      ((SaturationSearchState.applyLocalStep
          (SaturationSearchState.initial F) t.step.toLocalSaturationStep).resolveHead r hhead).IsTerminal)
    (branchClosed :
      ((SaturationSearchState.applyLocalStep
          (SaturationSearchState.initial F) t.step.toLocalSaturationStep).resolveHead r hhead).hintikka.BranchClosed)
    (hCompat₁ :
      (SaturationSearchState.initial F).DeterministicAdditionCompatible t.step)
    (hCompat₂ :
      (SaturationSearchState.applyLocalStep
        (SaturationSearchState.initial F) t.step.toLocalSaturationStep).BranchAdditionCompatible r) :
    CertifiedHeadPriorityCompletion Const Γ F :=
  ofCertifiedDerivation
    (CertifiedHeadPriorityDerivation.ofInitialSaturateThenResolveHead
      (Const := Const) (Γ := Γ) hInitial hIdle t r hhead hCompat₁ hCompat₂)
    terminal branchClosed

end CertifiedHeadPriorityCompletion

namespace CertifiedHeadPriorityDerivation

def toCertifiedCompletion
    {F : CompletenessFrontier Const Γ}
    (D : CertifiedHeadPriorityDerivation Const Γ F)
    (terminal : D.state.IsTerminal)
    (branchClosed : D.state.hintikka.BranchClosed) :
    CertifiedHeadPriorityCompletion Const Γ F :=
  CertifiedHeadPriorityCompletion.ofCertifiedDerivation D terminal branchClosed

end CertifiedHeadPriorityDerivation

namespace SaturationSearchState.HeadPriorityCompletion

def toCertified
    {F : CompletenessFrontier Const Γ}
    (C : HeadPriorityCompletion F)
    (hInitial : F.ClosedNonconflicting)
    (hCompat : C.derivation.Compatible) :
    CertifiedHeadPriorityCompletion Const Γ F :=
  { completion := C
    closedNonconflicting := hInitial
    compatible := hCompat }

end SaturationSearchState.HeadPriorityCompletion

namespace CountermodelCandidate

theorem closedHintikka_noncontradictory_of_closedNonconflicting
    (C : CountermodelCandidate Const Γ)
    (hInitial : C.frontier.ClosedNonconflicting)
    (hCompat : C.completion.derivation.Compatible) :
    C.closedHintikka.Noncontradictory :=
  C.completion.closed_noncontradictory_of_closedNonconflicting hInitial hCompat

/-- Package a terminal candidate whose whole head-priority derivation is
compatible and whose frontier avoids immediate closed-hull conflicts as a
closed non-contradictory certificate. -/
def toClosedLocalHintikkaCertificateOfClosedNonconflicting
    (C : CountermodelCandidate Const Γ)
    (hInitial : C.frontier.ClosedNonconflicting)
    (hCompat : C.completion.derivation.Compatible) :
    LocalHintikkaCertificate C.frontier :=
  C.toClosedLocalHintikkaCertificate
    (C.closedHintikka_noncontradictory_of_closedNonconflicting hInitial hCompat)

/-- Turn the closed hull of a compatible terminal search candidate into an
agreement witness once semantic agreement data has been provided, assuming the
frontier already avoids the immediate closed-hull conflicts. -/
def toClosedLocalAgreementWitnessOfClosedNonconflicting
    {M : SemilocalModel Base Const}
    (C : CountermodelCandidate Const Γ)
    (hInitial : C.frontier.ClosedNonconflicting)
    (hCompat : C.completion.derivation.Compatible)
    (env : SemilocalModel.Env M Γ)
    (global : SemilocalModel.IsGlobalEnv M env)
    (true_top :
      ∀ {φ : Formula Const Γ},
        (Sign.trueE, φ) ∈ C.closedHintikka.formulas →
          SemilocalModel.formulaTruth M env φ = ⊤)
    (false_ne_top :
      ∀ {φ : Formula Const Γ},
        (Sign.falseE, φ) ∈ C.closedHintikka.formulas →
          SemilocalModel.formulaTruth M env φ ≠ ⊤) :
    LocalAgreementWitness M C.frontier :=
  C.toClosedLocalAgreementWitnessOfNoncontradictory
    (C.closedHintikka_noncontradictory_of_closedNonconflicting hInitial hCompat)
    env global true_top false_ne_top

/-- Package the closed hull of a compatible terminal search candidate as the
current local countermodel object once semantic agreement data has been
provided and the frontier avoids immediate closed-hull conflicts. -/
def toClosedLocalCountermodelOfClosedNonconflicting
    {M : SemilocalModel Base Const}
    (C : CountermodelCandidate Const Γ)
    (hInitial : C.frontier.ClosedNonconflicting)
    (hCompat : C.completion.derivation.Compatible)
    (env : SemilocalModel.Env M Γ)
    (global : SemilocalModel.IsGlobalEnv M env)
    (true_top :
      ∀ {φ : Formula Const Γ},
        (Sign.trueE, φ) ∈ C.closedHintikka.formulas →
          SemilocalModel.formulaTruth M env φ = ⊤)
    (false_ne_top :
      ∀ {φ : Formula Const Γ},
        (Sign.falseE, φ) ∈ C.closedHintikka.formulas →
          SemilocalModel.formulaTruth M env φ ≠ ⊤) :
    LocalCountermodel C.frontier :=
  (C.toClosedLocalAgreementWitnessOfClosedNonconflicting
      hInitial hCompat env global true_top false_ne_top).toLocalCountermodel

/-- Strengthen the compatible closed-hull candidate-to-countermodel bridge with
the semilocal soundness hypothesis needed to refute derivability once the
frontier avoids immediate closed-hull conflicts. -/
def toClosedSoundLocalCountermodelOfClosedNonconflicting
    {M : SemilocalModel Base Const}
    (C : CountermodelCandidate Const Γ)
    (hInitial : C.frontier.ClosedNonconflicting)
    (hCompat : C.completion.derivation.Compatible)
    (env : SemilocalModel.Env M Γ)
    (global : SemilocalModel.IsGlobalEnv M env)
    (true_top :
      ∀ {φ : Formula Const Γ},
        (Sign.trueE, φ) ∈ C.closedHintikka.formulas →
          SemilocalModel.formulaTruth M env φ = ⊤)
    (false_ne_top :
      ∀ {φ : Formula Const Γ},
        (Sign.falseE, φ) ∈ C.closedHintikka.formulas →
          SemilocalModel.formulaTruth M env φ ≠ ⊤)
    (hM : SemilocalModel.SupportsUniformRelativization M) :
    SoundLocalCountermodel C.frontier :=
  (C.toClosedLocalAgreementWitnessOfClosedNonconflicting
      hInitial hCompat env global true_top false_ne_top).toSoundLocalCountermodel hM

end CountermodelCandidate

namespace CertifiedHeadPriorityCompletion

/-- Forget only the extra certification witnesses and keep the underlying
countermodel candidate extracted from the certified completion. -/
def toCountermodelCandidate
    (C : CertifiedHeadPriorityCompletion Const Γ F) :
    CountermodelCandidate Const Γ :=
  { frontier := F
    completion := C.completion }

end CertifiedHeadPriorityCompletion

/-- A terminal world-free candidate together with the certified search-side
side conditions currently needed to turn it into closed Hintikka data and then
into a semilocal countermodel witness. -/
structure CertifiedCountermodelCandidate
    (Const : Ty Base → Type v) (Γ : Ctx Base) where
  candidate : CountermodelCandidate Const Γ
  closedNonconflicting : candidate.frontier.ClosedNonconflicting
  compatible : candidate.completion.derivation.Compatible

namespace CertifiedCountermodelCandidate

def frontier (C : CertifiedCountermodelCandidate Const Γ) :
    CompletenessFrontier Const Γ :=
  C.candidate.frontier

def state (C : CertifiedCountermodelCandidate Const Γ) :
    SaturationSearchState Const Γ :=
  C.candidate.state

def hintikka (C : CertifiedCountermodelCandidate Const Γ) :
    HintikkaSet Const Γ :=
  C.candidate.hintikka

def closedHintikka (C : CertifiedCountermodelCandidate Const Γ) :
    HintikkaSet Const Γ :=
  C.candidate.closedHintikka

theorem closedHintikka_noncontradictory
    (C : CertifiedCountermodelCandidate Const Γ) :
    C.closedHintikka.Noncontradictory :=
  C.candidate.closedHintikka_noncontradictory_of_closedNonconflicting
    C.closedNonconflicting C.compatible

def toClosedLocalHintikkaCertificate
    (C : CertifiedCountermodelCandidate Const Γ) :
    LocalHintikkaCertificate C.frontier :=
  C.candidate.toClosedLocalHintikkaCertificateOfClosedNonconflicting
    C.closedNonconflicting C.compatible

@[simp] theorem toClosedLocalHintikkaCertificate_hintikka
    (C : CertifiedCountermodelCandidate Const Γ) :
    C.toClosedLocalHintikkaCertificate.hintikka = C.closedHintikka :=
  rfl

@[simp] theorem toClosedLocalHintikkaCertificate_formulas
    (C : CertifiedCountermodelCandidate Const Γ) :
    C.toClosedLocalHintikkaCertificate.hintikka.formulas = C.closedHintikka.formulas :=
  rfl

def toClosedLocalAgreementWitness
    {M : SemilocalModel Base Const}
    (C : CertifiedCountermodelCandidate Const Γ)
    (env : SemilocalModel.Env M Γ)
    (global : SemilocalModel.IsGlobalEnv M env)
    (true_top :
      ∀ {φ : Formula Const Γ},
        (Sign.trueE, φ) ∈ C.closedHintikka.formulas →
          SemilocalModel.formulaTruth M env φ = ⊤)
    (false_ne_top :
      ∀ {φ : Formula Const Γ},
        (Sign.falseE, φ) ∈ C.closedHintikka.formulas →
          SemilocalModel.formulaTruth M env φ ≠ ⊤) :
    LocalAgreementWitness M C.frontier :=
  C.candidate.toClosedLocalAgreementWitnessOfClosedNonconflicting
    C.closedNonconflicting C.compatible env global true_top false_ne_top

def toClosedLocalCountermodel
    {M : SemilocalModel Base Const}
    (C : CertifiedCountermodelCandidate Const Γ)
    (env : SemilocalModel.Env M Γ)
    (global : SemilocalModel.IsGlobalEnv M env)
    (true_top :
      ∀ {φ : Formula Const Γ},
        (Sign.trueE, φ) ∈ C.closedHintikka.formulas →
          SemilocalModel.formulaTruth M env φ = ⊤)
    (false_ne_top :
      ∀ {φ : Formula Const Γ},
        (Sign.falseE, φ) ∈ C.closedHintikka.formulas →
          SemilocalModel.formulaTruth M env φ ≠ ⊤) :
    LocalCountermodel C.frontier :=
  C.candidate.toClosedLocalCountermodelOfClosedNonconflicting
    C.closedNonconflicting C.compatible env global true_top false_ne_top

def toClosedSoundLocalCountermodel
    {M : SemilocalModel Base Const}
    (C : CertifiedCountermodelCandidate Const Γ)
    (env : SemilocalModel.Env M Γ)
    (global : SemilocalModel.IsGlobalEnv M env)
    (true_top :
      ∀ {φ : Formula Const Γ},
        (Sign.trueE, φ) ∈ C.closedHintikka.formulas →
          SemilocalModel.formulaTruth M env φ = ⊤)
    (false_ne_top :
      ∀ {φ : Formula Const Γ},
        (Sign.falseE, φ) ∈ C.closedHintikka.formulas →
          SemilocalModel.formulaTruth M env φ ≠ ⊤)
    (hM : SemilocalModel.SupportsUniformRelativization M) :
    SoundLocalCountermodel C.frontier :=
  C.candidate.toClosedSoundLocalCountermodelOfClosedNonconflicting
    C.closedNonconflicting C.compatible env global true_top false_ne_top hM

/-- Repackage a certified countermodel candidate as the corresponding certified
completion so the search-side and semantics-side APIs can be reused directly at
the candidate layer. -/
def toCertifiedCompletion
    (C : CertifiedCountermodelCandidate Const Γ) :
    CertifiedHeadPriorityCompletion Const Γ C.frontier :=
  { completion := C.candidate.completion
    closedNonconflicting := C.closedNonconflicting
    compatible := C.compatible }

@[simp] theorem toCertifiedCompletion_state
    (C : CertifiedCountermodelCandidate Const Γ) :
    C.toCertifiedCompletion.state = C.state :=
  rfl

@[simp] theorem toCertifiedCompletion_hintikka
    (C : CertifiedCountermodelCandidate Const Γ) :
    C.toCertifiedCompletion.hintikka = C.hintikka :=
  rfl

@[simp] theorem toCertifiedCompletion_closedHintikka
    (C : CertifiedCountermodelCandidate Const Γ) :
    C.toCertifiedCompletion.closedHintikka = C.closedHintikka :=
  rfl

end CertifiedCountermodelCandidate

namespace CertifiedHeadPriorityCompletion

/-- Repackage a certified completion as the corresponding certified
countermodel candidate, keeping the same completion data while exposing the
candidate-level bridge API. -/
def toCertifiedCountermodelCandidate
    (C : CertifiedHeadPriorityCompletion Const Γ F) :
    CertifiedCountermodelCandidate Const Γ :=
  { candidate := C.toCountermodelCandidate
    closedNonconflicting := by
      simpa [toCountermodelCandidate] using C.closedNonconflicting
    compatible := by
      simpa [toCountermodelCandidate] using C.compatible }

@[simp] theorem toCertifiedCountermodelCandidate_state
    (C : CertifiedHeadPriorityCompletion Const Γ F) :
    C.toCertifiedCountermodelCandidate.state = C.state :=
  rfl

@[simp] theorem toCertifiedCountermodelCandidate_hintikka
    (C : CertifiedHeadPriorityCompletion Const Γ F) :
    C.toCertifiedCountermodelCandidate.hintikka = C.hintikka :=
  rfl

@[simp] theorem toCertifiedCountermodelCandidate_closedHintikka
    (C : CertifiedHeadPriorityCompletion Const Γ F) :
    C.toCertifiedCountermodelCandidate.closedHintikka = C.closedHintikka :=
  rfl

/-- Forget terminality/branch-closure packaging and view a certified completion
as the underlying certified head-priority derivation. -/
def toCertifiedDerivation
    (C : CertifiedHeadPriorityCompletion Const Γ F) :
    CertifiedHeadPriorityDerivation Const Γ F :=
  { state := C.state
    derivation := C.completion.derivation
    closedNonconflicting := C.closedNonconflicting
    compatible := C.compatible }

@[simp] theorem toCertifiedDerivation_state
    (C : CertifiedHeadPriorityCompletion Const Γ F) :
    C.toCertifiedDerivation.state = C.state :=
  rfl

@[simp] theorem toCertifiedDerivation_hintikka
    (C : CertifiedHeadPriorityCompletion Const Γ F) :
    C.toCertifiedDerivation.hintikka = C.hintikka :=
  rfl

@[simp] theorem toCertifiedDerivation_closedHintikka
    (C : CertifiedHeadPriorityCompletion Const Γ F) :
    C.toCertifiedDerivation.closedHintikka = C.closedHintikka :=
  rfl

def toClosedLocalHintikkaCertificate
    (C : CertifiedHeadPriorityCompletion Const Γ F) :
    LocalHintikkaCertificate F :=
  C.toCertifiedCountermodelCandidate.toClosedLocalHintikkaCertificate

@[simp] theorem toClosedLocalHintikkaCertificate_hintikka
    (C : CertifiedHeadPriorityCompletion Const Γ F) :
    C.toClosedLocalHintikkaCertificate.hintikka = C.closedHintikka :=
  rfl

@[simp] theorem toClosedLocalHintikkaCertificate_formulas
    (C : CertifiedHeadPriorityCompletion Const Γ F) :
    C.toClosedLocalHintikkaCertificate.hintikka.formulas = C.closedHintikka.formulas :=
  rfl

def toClosedLocalAgreementWitness
    {M : SemilocalModel Base Const}
    (C : CertifiedHeadPriorityCompletion Const Γ F)
    (env : SemilocalModel.Env M Γ)
    (global : SemilocalModel.IsGlobalEnv M env)
    (true_top :
      ∀ {φ : Formula Const Γ},
        (Sign.trueE, φ) ∈ C.closedHintikka.formulas →
          SemilocalModel.formulaTruth M env φ = ⊤)
    (false_ne_top :
      ∀ {φ : Formula Const Γ},
        (Sign.falseE, φ) ∈ C.closedHintikka.formulas →
          SemilocalModel.formulaTruth M env φ ≠ ⊤) :
    LocalAgreementWitness M F :=
  C.toCertifiedCountermodelCandidate.toClosedLocalAgreementWitness
    env global true_top false_ne_top

def toClosedLocalCountermodel
    {M : SemilocalModel Base Const}
    (C : CertifiedHeadPriorityCompletion Const Γ F)
    (env : SemilocalModel.Env M Γ)
    (global : SemilocalModel.IsGlobalEnv M env)
    (true_top :
      ∀ {φ : Formula Const Γ},
        (Sign.trueE, φ) ∈ C.closedHintikka.formulas →
          SemilocalModel.formulaTruth M env φ = ⊤)
    (false_ne_top :
      ∀ {φ : Formula Const Γ},
        (Sign.falseE, φ) ∈ C.closedHintikka.formulas →
          SemilocalModel.formulaTruth M env φ ≠ ⊤) :
    LocalCountermodel F :=
  C.toCertifiedCountermodelCandidate.toClosedLocalCountermodel
    env global true_top false_ne_top

theorem exists_closedLocalAgreementWitness_of_exists_semantics
    (C : CertifiedHeadPriorityCompletion Const Γ F)
    (hSem :
      ∃ (M : SemilocalModel.{u, v, w, w'} Base Const) (env : SemilocalModel.Env M Γ),
        SemilocalModel.IsGlobalEnv M env ∧
        (∀ {φ : Formula Const Γ},
            (Sign.trueE, φ) ∈ C.closedHintikka.formulas →
              SemilocalModel.formulaTruth M env φ = ⊤) ∧
        (∀ {φ : Formula Const Γ},
            (Sign.falseE, φ) ∈ C.closedHintikka.formulas →
              SemilocalModel.formulaTruth M env φ ≠ ⊤)) :
    Nonempty (Σ M : SemilocalModel.{u, v, w, w'} Base Const, LocalAgreementWitness M F) := by
  rcases hSem with ⟨M, env, global, true_top, false_ne_top⟩
  exact ⟨⟨M, C.toClosedLocalAgreementWitness (M := M) env global true_top false_ne_top⟩⟩

theorem exists_closedLocalCountermodel_of_exists_semantics
    (C : CertifiedHeadPriorityCompletion Const Γ F)
    (hSem :
      ∃ (M : SemilocalModel.{u, v, w, w'} Base Const) (env : SemilocalModel.Env M Γ),
        SemilocalModel.IsGlobalEnv M env ∧
        (∀ {φ : Formula Const Γ},
            (Sign.trueE, φ) ∈ C.closedHintikka.formulas →
              SemilocalModel.formulaTruth M env φ = ⊤) ∧
        (∀ {φ : Formula Const Γ},
            (Sign.falseE, φ) ∈ C.closedHintikka.formulas →
              SemilocalModel.formulaTruth M env φ ≠ ⊤)) :
    Nonempty (LocalCountermodel.{u, v, w, w'} F) := by
  rcases C.exists_closedLocalAgreementWitness_of_exists_semantics hSem with ⟨⟨_, W⟩⟩
  exact ⟨W.toLocalCountermodel⟩

theorem exists_closedSoundLocalCountermodel_of_exists_semantics
    (C : CertifiedHeadPriorityCompletion Const Γ F)
    (hSem :
      ∃ (M : SemilocalModel.{u, v, w, w'} Base Const) (env : SemilocalModel.Env M Γ),
        SemilocalModel.IsGlobalEnv M env ∧
        (∀ {φ : Formula Const Γ},
            (Sign.trueE, φ) ∈ C.closedHintikka.formulas →
              SemilocalModel.formulaTruth M env φ = ⊤) ∧
        (∀ {φ : Formula Const Γ},
            (Sign.falseE, φ) ∈ C.closedHintikka.formulas →
              SemilocalModel.formulaTruth M env φ ≠ ⊤) ∧
        SemilocalModel.SupportsUniformRelativization M) :
    Nonempty (SoundLocalCountermodel.{u, v, w', w} F) := by
  rcases hSem with ⟨M, env, global, true_top, false_ne_top, hM⟩
  exact ⟨C.toCertifiedCountermodelCandidate.toClosedSoundLocalCountermodel
    (M := M) env global true_top false_ne_top hM⟩

theorem exists_semilocal_truth_counterexample_of_exists_semantics
    (C : CertifiedHeadPriorityCompletion Const Γ F)
    (hSem :
      ∃ (M : SemilocalModel.{u, v, w, w'} Base Const) (env : SemilocalModel.Env M Γ),
        SemilocalModel.IsGlobalEnv M env ∧
        (∀ {φ : Formula Const Γ},
            (Sign.trueE, φ) ∈ C.closedHintikka.formulas →
              SemilocalModel.formulaTruth M env φ = ⊤) ∧
        (∀ {φ : Formula Const Γ},
            (Sign.falseE, φ) ∈ C.closedHintikka.formulas →
              SemilocalModel.formulaTruth M env φ ≠ ⊤) ∧
        SemilocalModel.SupportsUniformRelativization M) :
    ∃ (M : SemilocalModel.{u, v, w, w'} Base Const) (env : SemilocalModel.Env M Γ),
      SemilocalModel.IsGlobalEnv M env ∧
      SemilocalModel.antecedentTruth M env F.antecedents = ⊤ ∧
      SemilocalModel.formulaTruth M env F.succedent ≠ ⊤ ∧
      SemilocalModel.SupportsUniformRelativization M := by
  rcases C.exists_closedSoundLocalCountermodel_of_exists_semantics hSem with ⟨CM⟩
  exact ⟨CM.model, CM.agreement.env, CM.agreement.global,
    CM.agreement.antecedentTruth_eq_top, CM.agreement.succedent_ne_top,
    CM.supportsUniformRelativization⟩

theorem not_derivable_of_exists_semantics
    (C : CertifiedHeadPriorityCompletion Const Γ F)
    (hSem :
      ∃ (M : SemilocalModel.{u, v, w, w'} Base Const) (env : SemilocalModel.Env M Γ),
        SemilocalModel.IsGlobalEnv M env ∧
        (∀ {φ : Formula Const Γ},
            (Sign.trueE, φ) ∈ C.closedHintikka.formulas →
              SemilocalModel.formulaTruth M env φ = ⊤) ∧
        (∀ {φ : Formula Const Γ},
            (Sign.falseE, φ) ∈ C.closedHintikka.formulas →
              SemilocalModel.formulaTruth M env φ ≠ ⊤) ∧
        SemilocalModel.SupportsUniformRelativization M) :
    ¬ Derivable (Base := Base) (Const := Const) F.antecedents F.succedent := by
  rcases C.exists_closedSoundLocalCountermodel_of_exists_semantics hSem with ⟨CM⟩
  exact CM.not_derivable

def toClosedSoundLocalCountermodel
    {M : SemilocalModel Base Const}
    (C : CertifiedHeadPriorityCompletion Const Γ F)
    (env : SemilocalModel.Env M Γ)
    (global : SemilocalModel.IsGlobalEnv M env)
    (true_top :
      ∀ {φ : Formula Const Γ},
        (Sign.trueE, φ) ∈ C.closedHintikka.formulas →
          SemilocalModel.formulaTruth M env φ = ⊤)
    (false_ne_top :
      ∀ {φ : Formula Const Γ},
        (Sign.falseE, φ) ∈ C.closedHintikka.formulas →
          SemilocalModel.formulaTruth M env φ ≠ ⊤)
    (hM : SemilocalModel.SupportsUniformRelativization M) :
    SoundLocalCountermodel F :=
  C.toCertifiedCountermodelCandidate.toClosedSoundLocalCountermodel
    env global true_top false_ne_top hM

end CertifiedHeadPriorityCompletion

namespace SaturationSearchState.HeadPriorityCompletion

theorem exists_closedLocalAgreementWitness_of_exists_semantics
    {F : CompletenessFrontier Const Γ}
    (C : HeadPriorityCompletion F)
    (hInitial : F.ClosedNonconflicting)
    (hCompat : C.derivation.Compatible)
    (hSem :
      ∃ (M : SemilocalModel.{u, v, w, w'} Base Const) (env : SemilocalModel.Env M Γ),
        SemilocalModel.IsGlobalEnv M env ∧
        (∀ {φ : Formula Const Γ},
            (Sign.trueE, φ) ∈ C.state.hintikka.close.formulas →
              SemilocalModel.formulaTruth M env φ = ⊤) ∧
        (∀ {φ : Formula Const Γ},
            (Sign.falseE, φ) ∈ C.state.hintikka.close.formulas →
              SemilocalModel.formulaTruth M env φ ≠ ⊤)) :
    Nonempty (Σ M : SemilocalModel.{u, v, w, w'} Base Const, LocalAgreementWitness M F) := by
  simpa [SaturationSearchState.HeadPriorityCompletion.toCertified,
    CertifiedHeadPriorityCompletion.state,
    CertifiedHeadPriorityCompletion.hintikka,
    CertifiedHeadPriorityCompletion.closedHintikka] using
    (CertifiedHeadPriorityCompletion.exists_closedLocalAgreementWitness_of_exists_semantics
      (C := C.toCertified (Const := Const) (Γ := Γ) hInitial hCompat) hSem)

theorem exists_closedLocalCountermodel_of_exists_semantics
    {F : CompletenessFrontier Const Γ}
    (C : HeadPriorityCompletion F)
    (hInitial : F.ClosedNonconflicting)
    (hCompat : C.derivation.Compatible)
    (hSem :
      ∃ (M : SemilocalModel.{u, v, w, w'} Base Const) (env : SemilocalModel.Env M Γ),
        SemilocalModel.IsGlobalEnv M env ∧
        (∀ {φ : Formula Const Γ},
            (Sign.trueE, φ) ∈ C.state.hintikka.close.formulas →
              SemilocalModel.formulaTruth M env φ = ⊤) ∧
        (∀ {φ : Formula Const Γ},
            (Sign.falseE, φ) ∈ C.state.hintikka.close.formulas →
              SemilocalModel.formulaTruth M env φ ≠ ⊤)) :
    Nonempty (LocalCountermodel.{u, v, w, w'} F) := by
  simpa [SaturationSearchState.HeadPriorityCompletion.toCertified,
    CertifiedHeadPriorityCompletion.state,
    CertifiedHeadPriorityCompletion.hintikka,
    CertifiedHeadPriorityCompletion.closedHintikka] using
    (CertifiedHeadPriorityCompletion.exists_closedLocalCountermodel_of_exists_semantics
      (C := C.toCertified (Const := Const) (Γ := Γ) hInitial hCompat) hSem)

theorem exists_closedSoundLocalCountermodel_of_exists_semantics
    {F : CompletenessFrontier Const Γ}
    (C : HeadPriorityCompletion F)
    (hInitial : F.ClosedNonconflicting)
    (hCompat : C.derivation.Compatible)
    (hSem :
      ∃ (M : SemilocalModel.{u, v, w, w'} Base Const) (env : SemilocalModel.Env M Γ),
        SemilocalModel.IsGlobalEnv M env ∧
        (∀ {φ : Formula Const Γ},
            (Sign.trueE, φ) ∈ C.state.hintikka.close.formulas →
              SemilocalModel.formulaTruth M env φ = ⊤) ∧
        (∀ {φ : Formula Const Γ},
            (Sign.falseE, φ) ∈ C.state.hintikka.close.formulas →
              SemilocalModel.formulaTruth M env φ ≠ ⊤) ∧
        SemilocalModel.SupportsUniformRelativization M) :
    Nonempty (SoundLocalCountermodel.{u, v, w', w} F) := by
  simpa [SaturationSearchState.HeadPriorityCompletion.toCertified,
    CertifiedHeadPriorityCompletion.state,
    CertifiedHeadPriorityCompletion.hintikka,
    CertifiedHeadPriorityCompletion.closedHintikka] using
    (CertifiedHeadPriorityCompletion.exists_closedSoundLocalCountermodel_of_exists_semantics
      (C := C.toCertified (Const := Const) (Γ := Γ) hInitial hCompat) hSem)

theorem exists_semilocal_truth_counterexample_of_exists_semantics
    {F : CompletenessFrontier Const Γ}
    (C : HeadPriorityCompletion F)
    (hInitial : F.ClosedNonconflicting)
    (hCompat : C.derivation.Compatible)
    (hSem :
      ∃ (M : SemilocalModel.{u, v, w, w'} Base Const) (env : SemilocalModel.Env M Γ),
        SemilocalModel.IsGlobalEnv M env ∧
        (∀ {φ : Formula Const Γ},
            (Sign.trueE, φ) ∈ C.state.hintikka.close.formulas →
              SemilocalModel.formulaTruth M env φ = ⊤) ∧
        (∀ {φ : Formula Const Γ},
            (Sign.falseE, φ) ∈ C.state.hintikka.close.formulas →
              SemilocalModel.formulaTruth M env φ ≠ ⊤) ∧
        SemilocalModel.SupportsUniformRelativization M) :
    ∃ (M : SemilocalModel.{u, v, w, w'} Base Const) (env : SemilocalModel.Env M Γ),
      SemilocalModel.IsGlobalEnv M env ∧
      SemilocalModel.antecedentTruth M env F.antecedents = ⊤ ∧
      SemilocalModel.formulaTruth M env F.succedent ≠ ⊤ ∧
      SemilocalModel.SupportsUniformRelativization M := by
  simpa [SaturationSearchState.HeadPriorityCompletion.toCertified,
    CertifiedHeadPriorityCompletion.state,
    CertifiedHeadPriorityCompletion.hintikka,
    CertifiedHeadPriorityCompletion.closedHintikka] using
    (CertifiedHeadPriorityCompletion.exists_semilocal_truth_counterexample_of_exists_semantics
      (C := C.toCertified (Const := Const) (Γ := Γ) hInitial hCompat) hSem)

theorem not_derivable_of_exists_semantics
    {F : CompletenessFrontier Const Γ}
    (C : HeadPriorityCompletion F)
    (hInitial : F.ClosedNonconflicting)
    (hCompat : C.derivation.Compatible)
    (hSem :
      ∃ (M : SemilocalModel.{u, v, w, w'} Base Const) (env : SemilocalModel.Env M Γ),
        SemilocalModel.IsGlobalEnv M env ∧
        (∀ {φ : Formula Const Γ},
            (Sign.trueE, φ) ∈ C.state.hintikka.close.formulas →
              SemilocalModel.formulaTruth M env φ = ⊤) ∧
        (∀ {φ : Formula Const Γ},
            (Sign.falseE, φ) ∈ C.state.hintikka.close.formulas →
              SemilocalModel.formulaTruth M env φ ≠ ⊤) ∧
        SemilocalModel.SupportsUniformRelativization M) :
    ¬ Derivable (Base := Base) (Const := Const) F.antecedents F.succedent := by
  simpa [SaturationSearchState.HeadPriorityCompletion.toCertified,
    CertifiedHeadPriorityCompletion.state,
    CertifiedHeadPriorityCompletion.hintikka,
    CertifiedHeadPriorityCompletion.closedHintikka] using
    (CertifiedHeadPriorityCompletion.not_derivable_of_exists_semantics
      (C := C.toCertified (Const := Const) (Γ := Γ) hInitial hCompat) hSem)

end SaturationSearchState.HeadPriorityCompletion

namespace CertifiedHeadPriorityDerivation

def toCertifiedCountermodelCandidate
    {F : CompletenessFrontier Const Γ}
    (D : CertifiedHeadPriorityDerivation Const Γ F)
    (terminal : D.state.IsTerminal)
    (branchClosed : D.state.hintikka.BranchClosed) :
    CertifiedCountermodelCandidate Const Γ :=
  (D.toCertifiedCompletion terminal branchClosed).toCertifiedCountermodelCandidate

@[simp] theorem toCertifiedCompletion_state
    {F : CompletenessFrontier Const Γ}
    (D : CertifiedHeadPriorityDerivation Const Γ F)
    (terminal : D.state.IsTerminal)
    (branchClosed : D.state.hintikka.BranchClosed) :
    (D.toCertifiedCompletion terminal branchClosed).state = D.state :=
  rfl

@[simp] theorem toCertifiedCompletion_hintikka
    {F : CompletenessFrontier Const Γ}
    (D : CertifiedHeadPriorityDerivation Const Γ F)
    (terminal : D.state.IsTerminal)
    (branchClosed : D.state.hintikka.BranchClosed) :
    (D.toCertifiedCompletion terminal branchClosed).hintikka = D.hintikka :=
  rfl

@[simp] theorem toCertifiedCompletion_closedHintikka
    {F : CompletenessFrontier Const Γ}
    (D : CertifiedHeadPriorityDerivation Const Γ F)
    (terminal : D.state.IsTerminal)
    (branchClosed : D.state.hintikka.BranchClosed) :
    (D.toCertifiedCompletion terminal branchClosed).closedHintikka = D.closedHintikka :=
  rfl

@[simp] theorem toCertifiedCountermodelCandidate_state
    {F : CompletenessFrontier Const Γ}
    (D : CertifiedHeadPriorityDerivation Const Γ F)
    (terminal : D.state.IsTerminal)
    (branchClosed : D.state.hintikka.BranchClosed) :
    (D.toCertifiedCountermodelCandidate terminal branchClosed).state = D.state :=
  rfl

@[simp] theorem toCertifiedCountermodelCandidate_hintikka
    {F : CompletenessFrontier Const Γ}
    (D : CertifiedHeadPriorityDerivation Const Γ F)
    (terminal : D.state.IsTerminal)
    (branchClosed : D.state.hintikka.BranchClosed) :
    (D.toCertifiedCountermodelCandidate terminal branchClosed).hintikka = D.hintikka :=
  rfl

@[simp] theorem toCertifiedCountermodelCandidate_closedHintikka
    {F : CompletenessFrontier Const Γ}
    (D : CertifiedHeadPriorityDerivation Const Γ F)
    (terminal : D.state.IsTerminal)
    (branchClosed : D.state.hintikka.BranchClosed) :
    (D.toCertifiedCountermodelCandidate terminal branchClosed).closedHintikka = D.closedHintikka :=
  rfl

theorem closedHintikka_true_top_of_candidate
    {F : CompletenessFrontier Const Γ}
    {M : SemilocalModel Base Const}
    (D : CertifiedHeadPriorityDerivation Const Γ F)
    (terminal : D.state.IsTerminal)
    (branchClosed : D.state.hintikka.BranchClosed)
    (env : SemilocalModel.Env M Γ)
    (candidate_true_top :
      ∀ {φ : Formula Const Γ},
        (Sign.trueE, φ) ∈
            (D.toCertifiedCountermodelCandidate terminal branchClosed).closedHintikka.formulas →
          SemilocalModel.formulaTruth M env φ = ⊤)
    {φ : Formula Const Γ}
    (hφ : (Sign.trueE, φ) ∈ D.closedHintikka.formulas) :
    SemilocalModel.formulaTruth M env φ = ⊤ :=
  candidate_true_top (by simpa using hφ)

theorem closedHintikka_false_ne_top_of_candidate
    {F : CompletenessFrontier Const Γ}
    {M : SemilocalModel Base Const}
    (D : CertifiedHeadPriorityDerivation Const Γ F)
    (terminal : D.state.IsTerminal)
    (branchClosed : D.state.hintikka.BranchClosed)
    (env : SemilocalModel.Env M Γ)
    (candidate_false_ne_top :
      ∀ {φ : Formula Const Γ},
        (Sign.falseE, φ) ∈
            (D.toCertifiedCountermodelCandidate terminal branchClosed).closedHintikka.formulas →
          SemilocalModel.formulaTruth M env φ ≠ ⊤)
    {φ : Formula Const Γ}
    (hφ : (Sign.falseE, φ) ∈ D.closedHintikka.formulas) :
    SemilocalModel.formulaTruth M env φ ≠ ⊤ :=
  candidate_false_ne_top (by simpa using hφ)

theorem closedHintikka_true_top_of_candidate_classified
    {F : CompletenessFrontier Const Γ}
    {M : SemilocalModel Base Const}
    {P : Formula Const Γ → Prop}
    (D : CertifiedHeadPriorityDerivation Const Γ F)
    (terminal : D.state.IsTerminal)
    (branchClosed : D.state.hintikka.BranchClosed)
    (env : SemilocalModel.Env M Γ)
    (candidate_true_class :
      ∀ {φ : Formula Const Γ},
        (Sign.trueE, φ) ∈
            (D.toCertifiedCountermodelCandidate terminal branchClosed).closedHintikka.formulas →
          P φ)
    (true_top_of_class :
      ∀ {φ : Formula Const Γ},
        P φ →
          SemilocalModel.formulaTruth M env φ = ⊤)
    {φ : Formula Const Γ}
    (hφ : (Sign.trueE, φ) ∈ D.closedHintikka.formulas) :
    SemilocalModel.formulaTruth M env φ = ⊤ :=
  true_top_of_class <|
    candidate_true_class (by simpa using hφ)

theorem closedHintikka_false_ne_top_of_candidate_classified
    {F : CompletenessFrontier Const Γ}
    {M : SemilocalModel Base Const}
    {P : Formula Const Γ → Prop}
    (D : CertifiedHeadPriorityDerivation Const Γ F)
    (terminal : D.state.IsTerminal)
    (branchClosed : D.state.hintikka.BranchClosed)
    (env : SemilocalModel.Env M Γ)
    (candidate_false_class :
      ∀ {φ : Formula Const Γ},
        (Sign.falseE, φ) ∈
            (D.toCertifiedCountermodelCandidate terminal branchClosed).closedHintikka.formulas →
          P φ)
    (false_ne_top_of_class :
      ∀ {φ : Formula Const Γ},
        P φ →
          SemilocalModel.formulaTruth M env φ ≠ ⊤)
    {φ : Formula Const Γ}
    (hφ : (Sign.falseE, φ) ∈ D.closedHintikka.formulas) :
    SemilocalModel.formulaTruth M env φ ≠ ⊤ :=
  false_ne_top_of_class <|
    candidate_false_class (by simpa using hφ)

structure CandidateClosedHintikkaSemantics
    {F : CompletenessFrontier Const Γ}
    {M : SemilocalModel Base Const}
    (D : CertifiedHeadPriorityDerivation Const Γ F)
    (terminal : D.state.IsTerminal)
    (branchClosed : D.state.hintikka.BranchClosed)
    (env : SemilocalModel.Env M Γ) where
  trueClass : Formula Const Γ → Prop
  falseClass : Formula Const Γ → Prop
  candidate_true_class :
    ∀ {φ : Formula Const Γ},
      (Sign.trueE, φ) ∈
          (D.toCertifiedCountermodelCandidate terminal branchClosed).closedHintikka.formulas →
        trueClass φ
  candidate_false_class :
    ∀ {φ : Formula Const Γ},
      (Sign.falseE, φ) ∈
          (D.toCertifiedCountermodelCandidate terminal branchClosed).closedHintikka.formulas →
        falseClass φ
  true_top_of_class :
    ∀ {φ : Formula Const Γ},
      trueClass φ →
        SemilocalModel.formulaTruth M env φ = ⊤
  false_ne_top_of_class :
    ∀ {φ : Formula Const Γ},
      falseClass φ →
        SemilocalModel.formulaTruth M env φ ≠ ⊤

namespace CandidateClosedHintikkaSemantics

theorem closedHintikka_true_top
    {F : CompletenessFrontier Const Γ}
    {M : SemilocalModel Base Const}
    {D : CertifiedHeadPriorityDerivation Const Γ F}
    {terminal : D.state.IsTerminal}
    {branchClosed : D.state.hintikka.BranchClosed}
    {env : SemilocalModel.Env M Γ}
    (S : CandidateClosedHintikkaSemantics D terminal branchClosed env)
    {φ : Formula Const Γ}
    (hφ : (Sign.trueE, φ) ∈ D.closedHintikka.formulas) :
    SemilocalModel.formulaTruth M env φ = ⊤ :=
  D.closedHintikka_true_top_of_candidate_classified
    terminal branchClosed env
    S.candidate_true_class
    S.true_top_of_class
    hφ

theorem closedHintikka_false_ne_top
    {F : CompletenessFrontier Const Γ}
    {M : SemilocalModel Base Const}
    {D : CertifiedHeadPriorityDerivation Const Γ F}
    {terminal : D.state.IsTerminal}
    {branchClosed : D.state.hintikka.BranchClosed}
    {env : SemilocalModel.Env M Γ}
    (S : CandidateClosedHintikkaSemantics D terminal branchClosed env)
    {φ : Formula Const Γ}
    (hφ : (Sign.falseE, φ) ∈ D.closedHintikka.formulas) :
    SemilocalModel.formulaTruth M env φ ≠ ⊤ :=
  D.closedHintikka_false_ne_top_of_candidate_classified
    terminal branchClosed env
    S.candidate_false_class
    S.false_ne_top_of_class
    hφ

end CandidateClosedHintikkaSemantics

def toCandidateClosedHintikkaSemantics
    {F : CompletenessFrontier Const Γ}
    {M : SemilocalModel Base Const}
    (D : CertifiedHeadPriorityDerivation Const Γ F)
    (terminal : D.state.IsTerminal)
    (branchClosed : D.state.hintikka.BranchClosed)
    (env : SemilocalModel.Env M Γ)
    (true_top :
      ∀ {φ : Formula Const Γ},
        (Sign.trueE, φ) ∈ D.closedHintikka.formulas →
          SemilocalModel.formulaTruth M env φ = ⊤)
    (false_ne_top :
      ∀ {φ : Formula Const Γ},
        (Sign.falseE, φ) ∈ D.closedHintikka.formulas →
          SemilocalModel.formulaTruth M env φ ≠ ⊤) :
    CandidateClosedHintikkaSemantics D terminal branchClosed env :=
  { trueClass := fun φ => (Sign.trueE, φ) ∈ D.closedHintikka.formulas
    falseClass := fun φ => (Sign.falseE, φ) ∈ D.closedHintikka.formulas
    candidate_true_class := by
      intro φ hφ
      simpa using hφ
    candidate_false_class := by
      intro φ hφ
      simpa using hφ
    true_top_of_class := by
      intro φ hφ
      exact true_top hφ
    false_ne_top_of_class := by
      intro φ hφ
      exact false_ne_top hφ }

theorem exists_candidateClosedHintikkaSemantics_of_exists_semantics
    {F : CompletenessFrontier Const Γ}
    (D : CertifiedHeadPriorityDerivation Const Γ F)
    (terminal : D.state.IsTerminal)
    (branchClosed : D.state.hintikka.BranchClosed)
    (hSem :
      ∃ (M : SemilocalModel.{u, v, w, w'} Base Const) (env : SemilocalModel.Env M Γ),
        SemilocalModel.IsGlobalEnv M env ∧
        (∀ {φ : Formula Const Γ},
            (Sign.trueE, φ) ∈ D.closedHintikka.formulas →
              SemilocalModel.formulaTruth M env φ = ⊤) ∧
        (∀ {φ : Formula Const Γ},
            (Sign.falseE, φ) ∈ D.closedHintikka.formulas →
              SemilocalModel.formulaTruth M env φ ≠ ⊤)) :
    ∃ (M : SemilocalModel.{u, v, w, w'} Base Const) (env : SemilocalModel.Env M Γ),
      SemilocalModel.IsGlobalEnv M env ∧
      Nonempty (CandidateClosedHintikkaSemantics D terminal branchClosed env) := by
  rcases hSem with ⟨M, env, global, true_top, false_ne_top⟩
  exact ⟨M, env, global,
    ⟨D.toCandidateClosedHintikkaSemantics terminal branchClosed env true_top false_ne_top⟩⟩

def toClosedLocalHintikkaCertificate
    {F : CompletenessFrontier Const Γ}
    (D : CertifiedHeadPriorityDerivation Const Γ F)
    (terminal : D.state.IsTerminal)
    (branchClosed : D.state.hintikka.BranchClosed) :
    LocalHintikkaCertificate F :=
  (D.toCertifiedCompletion terminal branchClosed).toClosedLocalHintikkaCertificate

def toClosedLocalAgreementWitnessOfCandidate
    {F : CompletenessFrontier Const Γ}
    {M : SemilocalModel Base Const}
    (D : CertifiedHeadPriorityDerivation Const Γ F)
    (terminal : D.state.IsTerminal)
    (branchClosed : D.state.hintikka.BranchClosed)
    (env : SemilocalModel.Env M Γ)
    (global : SemilocalModel.IsGlobalEnv M env)
    (candidate_true_top :
      ∀ {φ : Formula Const Γ},
        (Sign.trueE, φ) ∈
            (D.toCertifiedCountermodelCandidate terminal branchClosed).closedHintikka.formulas →
          SemilocalModel.formulaTruth M env φ = ⊤)
    (candidate_false_ne_top :
      ∀ {φ : Formula Const Γ},
        (Sign.falseE, φ) ∈
            (D.toCertifiedCountermodelCandidate terminal branchClosed).closedHintikka.formulas →
          SemilocalModel.formulaTruth M env φ ≠ ⊤) :
    LocalAgreementWitness M F :=
  (D.toCertifiedCompletion terminal branchClosed).toClosedLocalAgreementWitness
    env global
    (fun hφ =>
      D.closedHintikka_true_top_of_candidate
        terminal branchClosed env candidate_true_top hφ)
    (fun hφ =>
      D.closedHintikka_false_ne_top_of_candidate
        terminal branchClosed env candidate_false_ne_top hφ)

def toClosedLocalAgreementWitnessOfCandidateClassified
    {F : CompletenessFrontier Const Γ}
    {M : SemilocalModel Base Const}
    {Ptrue Pfalse : Formula Const Γ → Prop}
    (D : CertifiedHeadPriorityDerivation Const Γ F)
    (terminal : D.state.IsTerminal)
    (branchClosed : D.state.hintikka.BranchClosed)
    (env : SemilocalModel.Env M Γ)
    (global : SemilocalModel.IsGlobalEnv M env)
    (candidate_true_class :
      ∀ {φ : Formula Const Γ},
        (Sign.trueE, φ) ∈
            (D.toCertifiedCountermodelCandidate terminal branchClosed).closedHintikka.formulas →
          Ptrue φ)
    (candidate_false_class :
      ∀ {φ : Formula Const Γ},
        (Sign.falseE, φ) ∈
            (D.toCertifiedCountermodelCandidate terminal branchClosed).closedHintikka.formulas →
          Pfalse φ)
    (true_top_of_class :
      ∀ {φ : Formula Const Γ},
        Ptrue φ →
          SemilocalModel.formulaTruth M env φ = ⊤)
    (false_ne_top_of_class :
      ∀ {φ : Formula Const Γ},
        Pfalse φ →
          SemilocalModel.formulaTruth M env φ ≠ ⊤) :
    LocalAgreementWitness M F :=
  D.toClosedLocalAgreementWitnessOfCandidate
    terminal branchClosed env global
    (fun hφ => true_top_of_class (candidate_true_class hφ))
    (fun hφ => false_ne_top_of_class (candidate_false_class hφ))

def toClosedLocalAgreementWitnessOfSemantics
    {F : CompletenessFrontier Const Γ}
    {M : SemilocalModel Base Const}
    (D : CertifiedHeadPriorityDerivation Const Γ F)
    (terminal : D.state.IsTerminal)
    (branchClosed : D.state.hintikka.BranchClosed)
    (env : SemilocalModel.Env M Γ)
    (global : SemilocalModel.IsGlobalEnv M env)
    (S : CandidateClosedHintikkaSemantics D terminal branchClosed env) :
    LocalAgreementWitness M F :=
  D.toClosedLocalAgreementWitnessOfCandidateClassified
    terminal branchClosed env global
    (Ptrue := S.trueClass)
    (Pfalse := S.falseClass)
    S.candidate_true_class
    S.candidate_false_class
    S.true_top_of_class
    S.false_ne_top_of_class

def toClosedLocalAgreementWitness
    {F : CompletenessFrontier Const Γ}
    {M : SemilocalModel Base Const}
    (D : CertifiedHeadPriorityDerivation Const Γ F)
    (terminal : D.state.IsTerminal)
    (branchClosed : D.state.hintikka.BranchClosed)
    (env : SemilocalModel.Env M Γ)
    (global : SemilocalModel.IsGlobalEnv M env)
    (true_top :
      ∀ {φ : Formula Const Γ},
        (Sign.trueE, φ) ∈ D.closedHintikka.formulas →
          SemilocalModel.formulaTruth M env φ = ⊤)
    (false_ne_top :
      ∀ {φ : Formula Const Γ},
        (Sign.falseE, φ) ∈ D.closedHintikka.formulas →
          SemilocalModel.formulaTruth M env φ ≠ ⊤) :
    LocalAgreementWitness M F :=
  (D.toCertifiedCompletion terminal branchClosed).toClosedLocalAgreementWitness
    env global true_top false_ne_top

def toClosedLocalCountermodel
    {F : CompletenessFrontier Const Γ}
    {M : SemilocalModel Base Const}
    (D : CertifiedHeadPriorityDerivation Const Γ F)
    (terminal : D.state.IsTerminal)
    (branchClosed : D.state.hintikka.BranchClosed)
    (env : SemilocalModel.Env M Γ)
    (global : SemilocalModel.IsGlobalEnv M env)
    (true_top :
      ∀ {φ : Formula Const Γ},
        (Sign.trueE, φ) ∈ D.closedHintikka.formulas →
          SemilocalModel.formulaTruth M env φ = ⊤)
    (false_ne_top :
      ∀ {φ : Formula Const Γ},
        (Sign.falseE, φ) ∈ D.closedHintikka.formulas →
          SemilocalModel.formulaTruth M env φ ≠ ⊤) :
    LocalCountermodel F :=
  (D.toCertifiedCompletion terminal branchClosed).toClosedLocalCountermodel
    env global true_top false_ne_top

theorem exists_closedLocalAgreementWitness_of_exists_semantics
    {F : CompletenessFrontier Const Γ}
    (D : CertifiedHeadPriorityDerivation Const Γ F)
    (terminal : D.state.IsTerminal)
    (branchClosed : D.state.hintikka.BranchClosed)
    (hSem :
      ∃ (M : SemilocalModel.{u, v, w, w'} Base Const) (env : SemilocalModel.Env M Γ),
        SemilocalModel.IsGlobalEnv M env ∧
        (∀ {φ : Formula Const Γ},
            (Sign.trueE, φ) ∈ D.closedHintikka.formulas →
              SemilocalModel.formulaTruth M env φ = ⊤) ∧
        (∀ {φ : Formula Const Γ},
            (Sign.falseE, φ) ∈ D.closedHintikka.formulas →
              SemilocalModel.formulaTruth M env φ ≠ ⊤)) :
    Nonempty (Σ M : SemilocalModel.{u, v, w, w'} Base Const, LocalAgreementWitness M F) := by
  rcases hSem with ⟨M, env, global, true_top, false_ne_top⟩
  exact ⟨⟨M,
    D.toClosedLocalAgreementWitness (M := M)
      terminal branchClosed env global true_top false_ne_top⟩⟩

theorem exists_closedLocalCountermodel_of_exists_semantics
    {F : CompletenessFrontier Const Γ}
    (D : CertifiedHeadPriorityDerivation Const Γ F)
    (terminal : D.state.IsTerminal)
    (branchClosed : D.state.hintikka.BranchClosed)
    (hSem :
      ∃ (M : SemilocalModel.{u, v, w, w'} Base Const) (env : SemilocalModel.Env M Γ),
        SemilocalModel.IsGlobalEnv M env ∧
        (∀ {φ : Formula Const Γ},
            (Sign.trueE, φ) ∈ D.closedHintikka.formulas →
              SemilocalModel.formulaTruth M env φ = ⊤) ∧
        (∀ {φ : Formula Const Γ},
            (Sign.falseE, φ) ∈ D.closedHintikka.formulas →
              SemilocalModel.formulaTruth M env φ ≠ ⊤)) :
    Nonempty (LocalCountermodel.{u, v, w, w'} F) := by
  rcases
      D.exists_closedLocalAgreementWitness_of_exists_semantics
        terminal branchClosed hSem with ⟨⟨_, W⟩⟩
  exact ⟨W.toLocalCountermodel⟩

theorem exists_closedSoundLocalCountermodel_of_exists_semantics
    {F : CompletenessFrontier Const Γ}
    (D : CertifiedHeadPriorityDerivation Const Γ F)
    (terminal : D.state.IsTerminal)
    (branchClosed : D.state.hintikka.BranchClosed)
    (hSem :
      ∃ (M : SemilocalModel.{u, v, w, w'} Base Const) (env : SemilocalModel.Env M Γ),
        SemilocalModel.IsGlobalEnv M env ∧
        (∀ {φ : Formula Const Γ},
            (Sign.trueE, φ) ∈ D.closedHintikka.formulas →
              SemilocalModel.formulaTruth M env φ = ⊤) ∧
        (∀ {φ : Formula Const Γ},
            (Sign.falseE, φ) ∈ D.closedHintikka.formulas →
              SemilocalModel.formulaTruth M env φ ≠ ⊤) ∧
        SemilocalModel.SupportsUniformRelativization M) :
    Nonempty (SoundLocalCountermodel.{u, v, w', w} F) := by
  rcases hSem with ⟨M, env, global, true_top, false_ne_top, hM⟩
  exact ⟨(D.toCertifiedCompletion terminal branchClosed).toCertifiedCountermodelCandidate
    |>.toClosedSoundLocalCountermodel
      (M := M) env global true_top false_ne_top hM⟩

theorem exists_semilocal_truth_counterexample_of_exists_semantics
    {F : CompletenessFrontier Const Γ}
    (D : CertifiedHeadPriorityDerivation Const Γ F)
    (terminal : D.state.IsTerminal)
    (branchClosed : D.state.hintikka.BranchClosed)
    (hSem :
      ∃ (M : SemilocalModel.{u, v, w, w'} Base Const) (env : SemilocalModel.Env M Γ),
        SemilocalModel.IsGlobalEnv M env ∧
        (∀ {φ : Formula Const Γ},
            (Sign.trueE, φ) ∈ D.closedHintikka.formulas →
              SemilocalModel.formulaTruth M env φ = ⊤) ∧
        (∀ {φ : Formula Const Γ},
            (Sign.falseE, φ) ∈ D.closedHintikka.formulas →
              SemilocalModel.formulaTruth M env φ ≠ ⊤) ∧
        SemilocalModel.SupportsUniformRelativization M) :
    ∃ (M : SemilocalModel.{u, v, w, w'} Base Const) (env : SemilocalModel.Env M Γ),
      SemilocalModel.IsGlobalEnv M env ∧
      SemilocalModel.antecedentTruth M env F.antecedents = ⊤ ∧
      SemilocalModel.formulaTruth M env F.succedent ≠ ⊤ ∧
      SemilocalModel.SupportsUniformRelativization M := by
  rcases D.exists_closedSoundLocalCountermodel_of_exists_semantics terminal branchClosed hSem with
    ⟨CM⟩
  exact ⟨CM.model, CM.agreement.env, CM.agreement.global,
    CM.agreement.antecedentTruth_eq_top, CM.agreement.succedent_ne_top,
    CM.supportsUniformRelativization⟩

theorem not_derivable_of_exists_semantics
    {F : CompletenessFrontier Const Γ}
    (D : CertifiedHeadPriorityDerivation Const Γ F)
    (terminal : D.state.IsTerminal)
    (branchClosed : D.state.hintikka.BranchClosed)
    (hSem :
      ∃ (M : SemilocalModel.{u, v, w, w'} Base Const) (env : SemilocalModel.Env M Γ),
        SemilocalModel.IsGlobalEnv M env ∧
        (∀ {φ : Formula Const Γ},
            (Sign.trueE, φ) ∈ D.closedHintikka.formulas →
              SemilocalModel.formulaTruth M env φ = ⊤) ∧
        (∀ {φ : Formula Const Γ},
            (Sign.falseE, φ) ∈ D.closedHintikka.formulas →
              SemilocalModel.formulaTruth M env φ ≠ ⊤) ∧
        SemilocalModel.SupportsUniformRelativization M) :
    ¬ Derivable (Base := Base) (Const := Const) F.antecedents F.succedent := by
  rcases D.exists_closedSoundLocalCountermodel_of_exists_semantics terminal branchClosed hSem with
    ⟨CM⟩
  exact CM.not_derivable

def toClosedLocalCountermodelOfCandidate
    {F : CompletenessFrontier Const Γ}
    {M : SemilocalModel Base Const}
    (D : CertifiedHeadPriorityDerivation Const Γ F)
    (terminal : D.state.IsTerminal)
    (branchClosed : D.state.hintikka.BranchClosed)
    (env : SemilocalModel.Env M Γ)
    (global : SemilocalModel.IsGlobalEnv M env)
    (candidate_true_top :
      ∀ {φ : Formula Const Γ},
        (Sign.trueE, φ) ∈
            (D.toCertifiedCountermodelCandidate terminal branchClosed).closedHintikka.formulas →
          SemilocalModel.formulaTruth M env φ = ⊤)
    (candidate_false_ne_top :
      ∀ {φ : Formula Const Γ},
        (Sign.falseE, φ) ∈
            (D.toCertifiedCountermodelCandidate terminal branchClosed).closedHintikka.formulas →
          SemilocalModel.formulaTruth M env φ ≠ ⊤) :
    LocalCountermodel F :=
  (D.toCertifiedCompletion terminal branchClosed).toClosedLocalCountermodel
    env global
    (fun hφ =>
      D.closedHintikka_true_top_of_candidate
        terminal branchClosed env candidate_true_top hφ)
    (fun hφ =>
      D.closedHintikka_false_ne_top_of_candidate
        terminal branchClosed env candidate_false_ne_top hφ)

def toClosedLocalCountermodelOfCandidateClassified
    {F : CompletenessFrontier Const Γ}
    {M : SemilocalModel Base Const}
    {Ptrue Pfalse : Formula Const Γ → Prop}
    (D : CertifiedHeadPriorityDerivation Const Γ F)
    (terminal : D.state.IsTerminal)
    (branchClosed : D.state.hintikka.BranchClosed)
    (env : SemilocalModel.Env M Γ)
    (global : SemilocalModel.IsGlobalEnv M env)
    (candidate_true_class :
      ∀ {φ : Formula Const Γ},
        (Sign.trueE, φ) ∈
            (D.toCertifiedCountermodelCandidate terminal branchClosed).closedHintikka.formulas →
          Ptrue φ)
    (candidate_false_class :
      ∀ {φ : Formula Const Γ},
        (Sign.falseE, φ) ∈
            (D.toCertifiedCountermodelCandidate terminal branchClosed).closedHintikka.formulas →
          Pfalse φ)
    (true_top_of_class :
      ∀ {φ : Formula Const Γ},
        Ptrue φ →
          SemilocalModel.formulaTruth M env φ = ⊤)
    (false_ne_top_of_class :
      ∀ {φ : Formula Const Γ},
        Pfalse φ →
          SemilocalModel.formulaTruth M env φ ≠ ⊤) :
    LocalCountermodel F :=
  D.toClosedLocalCountermodelOfCandidate
    terminal branchClosed env global
    (fun hφ => true_top_of_class (candidate_true_class hφ))
    (fun hφ => false_ne_top_of_class (candidate_false_class hφ))

def toClosedLocalCountermodelOfSemantics
    {F : CompletenessFrontier Const Γ}
    {M : SemilocalModel Base Const}
    (D : CertifiedHeadPriorityDerivation Const Γ F)
    (terminal : D.state.IsTerminal)
    (branchClosed : D.state.hintikka.BranchClosed)
    (env : SemilocalModel.Env M Γ)
    (global : SemilocalModel.IsGlobalEnv M env)
    (S : CandidateClosedHintikkaSemantics D terminal branchClosed env) :
    LocalCountermodel F :=
  D.toClosedLocalCountermodelOfCandidateClassified
    terminal branchClosed env global
    (Ptrue := S.trueClass)
    (Pfalse := S.falseClass)
    S.candidate_true_class
    S.candidate_false_class
    S.true_top_of_class
    S.false_ne_top_of_class

def toClosedSoundLocalCountermodel
    {F : CompletenessFrontier Const Γ}
    {M : SemilocalModel Base Const}
    (D : CertifiedHeadPriorityDerivation Const Γ F)
    (terminal : D.state.IsTerminal)
    (branchClosed : D.state.hintikka.BranchClosed)
    (env : SemilocalModel.Env M Γ)
    (global : SemilocalModel.IsGlobalEnv M env)
    (true_top :
      ∀ {φ : Formula Const Γ},
        (Sign.trueE, φ) ∈ D.closedHintikka.formulas →
          SemilocalModel.formulaTruth M env φ = ⊤)
    (false_ne_top :
      ∀ {φ : Formula Const Γ},
        (Sign.falseE, φ) ∈ D.closedHintikka.formulas →
          SemilocalModel.formulaTruth M env φ ≠ ⊤)
    (hM : SemilocalModel.SupportsUniformRelativization M) :
    SoundLocalCountermodel F :=
  (D.toCertifiedCompletion terminal branchClosed).toClosedSoundLocalCountermodel
    env global true_top false_ne_top hM

def toClosedSoundLocalCountermodelOfCandidate
    {F : CompletenessFrontier Const Γ}
    {M : SemilocalModel Base Const}
    (D : CertifiedHeadPriorityDerivation Const Γ F)
    (terminal : D.state.IsTerminal)
    (branchClosed : D.state.hintikka.BranchClosed)
    (env : SemilocalModel.Env M Γ)
    (global : SemilocalModel.IsGlobalEnv M env)
    (candidate_true_top :
      ∀ {φ : Formula Const Γ},
        (Sign.trueE, φ) ∈
            (D.toCertifiedCountermodelCandidate terminal branchClosed).closedHintikka.formulas →
          SemilocalModel.formulaTruth M env φ = ⊤)
    (candidate_false_ne_top :
      ∀ {φ : Formula Const Γ},
        (Sign.falseE, φ) ∈
            (D.toCertifiedCountermodelCandidate terminal branchClosed).closedHintikka.formulas →
          SemilocalModel.formulaTruth M env φ ≠ ⊤)
    (hM : SemilocalModel.SupportsUniformRelativization M) :
    SoundLocalCountermodel F :=
  (D.toCertifiedCompletion terminal branchClosed).toClosedSoundLocalCountermodel
    env global
    (fun hφ =>
      D.closedHintikka_true_top_of_candidate
        terminal branchClosed env candidate_true_top hφ)
    (fun hφ =>
      D.closedHintikka_false_ne_top_of_candidate
        terminal branchClosed env candidate_false_ne_top hφ)
    hM

def toClosedSoundLocalCountermodelOfCandidateClassified
    {F : CompletenessFrontier Const Γ}
    {M : SemilocalModel Base Const}
    {Ptrue Pfalse : Formula Const Γ → Prop}
    (D : CertifiedHeadPriorityDerivation Const Γ F)
    (terminal : D.state.IsTerminal)
    (branchClosed : D.state.hintikka.BranchClosed)
    (env : SemilocalModel.Env M Γ)
    (global : SemilocalModel.IsGlobalEnv M env)
    (candidate_true_class :
      ∀ {φ : Formula Const Γ},
        (Sign.trueE, φ) ∈
            (D.toCertifiedCountermodelCandidate terminal branchClosed).closedHintikka.formulas →
          Ptrue φ)
    (candidate_false_class :
      ∀ {φ : Formula Const Γ},
        (Sign.falseE, φ) ∈
            (D.toCertifiedCountermodelCandidate terminal branchClosed).closedHintikka.formulas →
          Pfalse φ)
    (true_top_of_class :
      ∀ {φ : Formula Const Γ},
        Ptrue φ →
          SemilocalModel.formulaTruth M env φ = ⊤)
    (false_ne_top_of_class :
      ∀ {φ : Formula Const Γ},
        Pfalse φ →
          SemilocalModel.formulaTruth M env φ ≠ ⊤)
    (hM : SemilocalModel.SupportsUniformRelativization M) :
    SoundLocalCountermodel F :=
  D.toClosedSoundLocalCountermodelOfCandidate
    terminal branchClosed env global
    (fun hφ => true_top_of_class (candidate_true_class hφ))
    (fun hφ => false_ne_top_of_class (candidate_false_class hφ))
    hM

def toClosedSoundLocalCountermodelOfSemantics
    {F : CompletenessFrontier Const Γ}
    {M : SemilocalModel Base Const}
    (D : CertifiedHeadPriorityDerivation Const Γ F)
    (terminal : D.state.IsTerminal)
    (branchClosed : D.state.hintikka.BranchClosed)
    (env : SemilocalModel.Env M Γ)
    (global : SemilocalModel.IsGlobalEnv M env)
    (S : CandidateClosedHintikkaSemantics D terminal branchClosed env)
    (hM : SemilocalModel.SupportsUniformRelativization M) :
    SoundLocalCountermodel F :=
  D.toClosedSoundLocalCountermodelOfCandidateClassified
    terminal branchClosed env global
    (Ptrue := S.trueClass)
    (Pfalse := S.falseClass)
    S.candidate_true_class
    S.candidate_false_class
    S.true_top_of_class
    S.false_ne_top_of_class
    hM

end CertifiedHeadPriorityDerivation

namespace CertifiedHeadPriorityDerivation

namespace CandidateClosedHintikkaSemantics

def toClosedLocalAgreementWitness
    {F : CompletenessFrontier Const Γ}
    {M : SemilocalModel Base Const}
    {D : CertifiedHeadPriorityDerivation Const Γ F}
    {terminal : D.state.IsTerminal}
    {branchClosed : D.state.hintikka.BranchClosed}
    {env : SemilocalModel.Env M Γ}
    (S : CandidateClosedHintikkaSemantics D terminal branchClosed env)
    (global : SemilocalModel.IsGlobalEnv M env) :
    LocalAgreementWitness M F :=
  D.toClosedLocalAgreementWitnessOfSemantics
    terminal branchClosed env global S

def toClosedLocalCountermodel
    {F : CompletenessFrontier Const Γ}
    {M : SemilocalModel Base Const}
    {D : CertifiedHeadPriorityDerivation Const Γ F}
    {terminal : D.state.IsTerminal}
    {branchClosed : D.state.hintikka.BranchClosed}
    {env : SemilocalModel.Env M Γ}
    (S : CandidateClosedHintikkaSemantics D terminal branchClosed env)
    (global : SemilocalModel.IsGlobalEnv M env) :
    LocalCountermodel F :=
  D.toClosedLocalCountermodelOfSemantics
    terminal branchClosed env global S

def toClosedSoundLocalCountermodel
    {F : CompletenessFrontier Const Γ}
    {M : SemilocalModel Base Const}
    {D : CertifiedHeadPriorityDerivation Const Γ F}
    {terminal : D.state.IsTerminal}
    {branchClosed : D.state.hintikka.BranchClosed}
    {env : SemilocalModel.Env M Γ}
    (S : CandidateClosedHintikkaSemantics D terminal branchClosed env)
    (global : SemilocalModel.IsGlobalEnv M env)
    (hM : SemilocalModel.SupportsUniformRelativization M) :
    SoundLocalCountermodel F :=
  D.toClosedSoundLocalCountermodelOfSemantics
    terminal branchClosed env global S hM

theorem not_validSequent
    {F : CompletenessFrontier Const Γ}
    {M : SemilocalModel Base Const}
    {D : CertifiedHeadPriorityDerivation Const Γ F}
    {terminal : D.state.IsTerminal}
    {branchClosed : D.state.hintikka.BranchClosed}
    {env : SemilocalModel.Env M Γ}
    (S : CandidateClosedHintikkaSemantics D terminal branchClosed env)
    (global : SemilocalModel.IsGlobalEnv M env)
    (hM : SemilocalModel.SupportsUniformRelativization M) :
    ¬ SemilocalModel.ValidSequent M F.antecedents F.succedent :=
  (S.toClosedSoundLocalCountermodel global hM).not_validSequent

theorem not_derivable
    {F : CompletenessFrontier Const Γ}
    {M : SemilocalModel Base Const}
    {D : CertifiedHeadPriorityDerivation Const Γ F}
    {terminal : D.state.IsTerminal}
    {branchClosed : D.state.hintikka.BranchClosed}
    {env : SemilocalModel.Env M Γ}
    (S : CandidateClosedHintikkaSemantics D terminal branchClosed env)
    (global : SemilocalModel.IsGlobalEnv M env)
    (hM : SemilocalModel.SupportsUniformRelativization M) :
    ¬ Derivable (Base := Base) (Const := Const) F.antecedents F.succedent :=
  (S.toClosedSoundLocalCountermodel global hM).not_derivable

end CandidateClosedHintikkaSemantics

end CertifiedHeadPriorityDerivation

namespace CertifiedHeadPriorityCompletion

/-- The semantic packaging already available for terminal certified derivations,
re-indexed at the certified completion layer. -/
abbrev CandidateClosedHintikkaSemantics
    {M : SemilocalModel Base Const}
    (C : CertifiedHeadPriorityCompletion Const Γ F)
    (env : SemilocalModel.Env M Γ) :=
  CertifiedHeadPriorityDerivation.CandidateClosedHintikkaSemantics
    C.toCertifiedDerivation C.completion.terminal C.completion.branchClosed env

/-- Package raw closed-hull semantic agreement data at the certified
completion layer as a reusable candidate semantics object. -/
def toCandidateClosedHintikkaSemantics
    {M : SemilocalModel Base Const}
    (C : CertifiedHeadPriorityCompletion Const Γ F)
    (env : SemilocalModel.Env M Γ)
    (true_top :
      ∀ {φ : Formula Const Γ},
        (Sign.trueE, φ) ∈ C.closedHintikka.formulas →
          SemilocalModel.formulaTruth M env φ = ⊤)
    (false_ne_top :
      ∀ {φ : Formula Const Γ},
        (Sign.falseE, φ) ∈ C.closedHintikka.formulas →
          SemilocalModel.formulaTruth M env φ ≠ ⊤) :
    CandidateClosedHintikkaSemantics C env :=
  CertifiedHeadPriorityDerivation.toCandidateClosedHintikkaSemantics
    (D := C.toCertifiedDerivation)
    (terminal := C.completion.terminal)
    (branchClosed := C.completion.branchClosed)
    env true_top false_ne_top

theorem exists_candidateClosedHintikkaSemantics_of_exists_semantics
    (C : CertifiedHeadPriorityCompletion Const Γ F)
    (hSem :
      ∃ (M : SemilocalModel.{u, v, w, w'} Base Const) (env : SemilocalModel.Env M Γ),
        SemilocalModel.IsGlobalEnv M env ∧
        (∀ {φ : Formula Const Γ},
            (Sign.trueE, φ) ∈ C.closedHintikka.formulas →
              SemilocalModel.formulaTruth M env φ = ⊤) ∧
        (∀ {φ : Formula Const Γ},
            (Sign.falseE, φ) ∈ C.closedHintikka.formulas →
              SemilocalModel.formulaTruth M env φ ≠ ⊤)) :
    ∃ (M : SemilocalModel.{u, v, w, w'} Base Const) (env : SemilocalModel.Env M Γ),
      SemilocalModel.IsGlobalEnv M env ∧
      Nonempty (CandidateClosedHintikkaSemantics C env) := by
  rcases hSem with ⟨M, env, global, true_top, false_ne_top⟩
  exact ⟨M, env, global,
    ⟨C.toCandidateClosedHintikkaSemantics (M := M) env true_top false_ne_top⟩⟩

def toClosedLocalAgreementWitnessOfSemantics
    {M : SemilocalModel Base Const}
    (C : CertifiedHeadPriorityCompletion Const Γ F)
    (env : SemilocalModel.Env M Γ)
    (global : SemilocalModel.IsGlobalEnv M env)
    (S : CandidateClosedHintikkaSemantics C env) :
    LocalAgreementWitness M F :=
  CertifiedHeadPriorityDerivation.CandidateClosedHintikkaSemantics.toClosedLocalAgreementWitness
    (D := C.toCertifiedDerivation)
    (terminal := C.completion.terminal)
    (branchClosed := C.completion.branchClosed)
    (env := env)
    S global

def toClosedLocalCountermodelOfSemantics
    {M : SemilocalModel Base Const}
    (C : CertifiedHeadPriorityCompletion Const Γ F)
    (env : SemilocalModel.Env M Γ)
    (global : SemilocalModel.IsGlobalEnv M env)
    (S : CandidateClosedHintikkaSemantics C env) :
    LocalCountermodel F :=
  CertifiedHeadPriorityDerivation.CandidateClosedHintikkaSemantics.toClosedLocalCountermodel
    (D := C.toCertifiedDerivation)
    (terminal := C.completion.terminal)
    (branchClosed := C.completion.branchClosed)
    (env := env)
    S global

def toClosedSoundLocalCountermodelOfSemantics
    {M : SemilocalModel Base Const}
    (C : CertifiedHeadPriorityCompletion Const Γ F)
    (env : SemilocalModel.Env M Γ)
    (global : SemilocalModel.IsGlobalEnv M env)
    (S : CandidateClosedHintikkaSemantics C env)
    (hM : SemilocalModel.SupportsUniformRelativization M) :
    SoundLocalCountermodel F :=
  CertifiedHeadPriorityDerivation.CandidateClosedHintikkaSemantics.toClosedSoundLocalCountermodel
    (D := C.toCertifiedDerivation)
    (terminal := C.completion.terminal)
    (branchClosed := C.completion.branchClosed)
    (env := env)
    S global hM

def toCandidateClosedHintikkaSemanticsOfClosedLocalAgreementWitness
    {M : SemilocalModel Base Const}
    (C : CertifiedHeadPriorityCompletion Const Γ F)
    (W : LocalAgreementWitness M F)
    (hCert : W.certificate = C.toClosedLocalHintikkaCertificate) :
    CandidateClosedHintikkaSemantics C W.env :=
  C.toCandidateClosedHintikkaSemantics (M := M) W.env
    (by
      intro φ hφ
      exact W.true_top <| by
        simpa [hCert] using hφ)
    (by
      intro φ hφ
      exact W.false_ne_top <| by
        simpa [hCert] using hφ)

@[simp] theorem toClosedLocalAgreementWitnessOfSemantics_certificate
    {M : SemilocalModel Base Const}
    (C : CertifiedHeadPriorityCompletion Const Γ F)
    (env : SemilocalModel.Env M Γ)
    (global : SemilocalModel.IsGlobalEnv M env)
    (S : CandidateClosedHintikkaSemantics C env) :
    (C.toClosedLocalAgreementWitnessOfSemantics env global S).certificate =
      C.toClosedLocalHintikkaCertificate := by
  rfl

theorem exists_closedLocalAgreementWitness_of_exists_candidateClosedHintikkaSemantics
    (C : CertifiedHeadPriorityCompletion Const Γ F)
    (hSem :
      ∃ (M : SemilocalModel.{u, v, w, w'} Base Const) (env : SemilocalModel.Env M Γ),
        SemilocalModel.IsGlobalEnv M env ∧
        Nonempty (CandidateClosedHintikkaSemantics C env)) :
    ∃ (M : SemilocalModel.{u, v, w, w'} Base Const) (W : LocalAgreementWitness M F),
      W.certificate = C.toClosedLocalHintikkaCertificate := by
  rcases hSem with ⟨M, env, global, ⟨S⟩⟩
  exact ⟨M, C.toClosedLocalAgreementWitnessOfSemantics (M := M) env global S, by
    simp⟩

theorem exists_candidateClosedHintikkaSemantics_of_exists_closedLocalAgreementWitness
    (C : CertifiedHeadPriorityCompletion Const Γ F)
    (hW :
      ∃ (M : SemilocalModel.{u, v, w, w'} Base Const) (W : LocalAgreementWitness M F),
        W.certificate = C.toClosedLocalHintikkaCertificate) :
    ∃ (M : SemilocalModel.{u, v, w, w'} Base Const) (env : SemilocalModel.Env M Γ),
      SemilocalModel.IsGlobalEnv M env ∧
      Nonempty (CandidateClosedHintikkaSemantics C env) := by
  rcases hW with ⟨M, W, hCert⟩
  exact ⟨M, W.env, W.global,
    ⟨C.toCandidateClosedHintikkaSemanticsOfClosedLocalAgreementWitness (M := M) W hCert⟩⟩

theorem not_derivable_of_exists_candidateClosedHintikkaSemantics
    (C : CertifiedHeadPriorityCompletion Const Γ F)
    (hSem :
      ∃ (M : SemilocalModel.{u, v, w, w'} Base Const) (env : SemilocalModel.Env M Γ),
        SemilocalModel.IsGlobalEnv M env ∧
        Nonempty (CandidateClosedHintikkaSemantics C env) ∧
        SemilocalModel.SupportsUniformRelativization M) :
    ¬ Derivable (Base := Base) (Const := Const) F.antecedents F.succedent := by
  rcases hSem with ⟨M, env, global, ⟨S⟩, hM⟩
  exact
    CertifiedHeadPriorityDerivation.CandidateClosedHintikkaSemantics.not_derivable
      (D := C.toCertifiedDerivation)
      (terminal := C.completion.terminal)
      (branchClosed := C.completion.branchClosed)
      (env := env)
      S global hM

end CertifiedHeadPriorityCompletion

namespace CertifiedCountermodelCandidate

/-- Candidate-level alias for the reusable closed-hull semantic classification
packaged for certified completions. -/
abbrev CandidateClosedHintikkaSemantics
    {M : SemilocalModel Base Const}
    (C : CertifiedCountermodelCandidate Const Γ)
    (env : SemilocalModel.Env M Γ) :=
  CertifiedHeadPriorityCompletion.CandidateClosedHintikkaSemantics
    (C := C.toCertifiedCompletion) env

/-- Package raw closed-hull semantic agreement data directly at the certified
candidate layer. -/
def toCandidateClosedHintikkaSemantics
    {M : SemilocalModel Base Const}
    (C : CertifiedCountermodelCandidate Const Γ)
    (env : SemilocalModel.Env M Γ)
    (true_top :
      ∀ {φ : Formula Const Γ},
        (Sign.trueE, φ) ∈ C.closedHintikka.formulas →
          SemilocalModel.formulaTruth M env φ = ⊤)
    (false_ne_top :
      ∀ {φ : Formula Const Γ},
        (Sign.falseE, φ) ∈ C.closedHintikka.formulas →
          SemilocalModel.formulaTruth M env φ ≠ ⊤) :
    CandidateClosedHintikkaSemantics C env :=
  C.toCertifiedCompletion.toCandidateClosedHintikkaSemantics env true_top false_ne_top

/-- Recover the closed local agreement witness directly from a certified
candidate-level semantics package. -/
def toClosedLocalAgreementWitnessOfSemantics
    {M : SemilocalModel Base Const}
    (C : CertifiedCountermodelCandidate Const Γ)
    (env : SemilocalModel.Env M Γ)
    (global : SemilocalModel.IsGlobalEnv M env)
    (S : CandidateClosedHintikkaSemantics C env) :
    LocalAgreementWitness M C.frontier :=
  C.toCertifiedCompletion.toClosedLocalAgreementWitnessOfSemantics env global S

/-- Recover the current local countermodel object directly from a certified
candidate-level semantics package. -/
def toClosedLocalCountermodelOfSemantics
    {M : SemilocalModel Base Const}
    (C : CertifiedCountermodelCandidate Const Γ)
    (env : SemilocalModel.Env M Γ)
    (global : SemilocalModel.IsGlobalEnv M env)
    (S : CandidateClosedHintikkaSemantics C env) :
    LocalCountermodel C.frontier :=
  C.toCertifiedCompletion.toClosedLocalCountermodelOfSemantics env global S

/-- Recover the sound local countermodel object directly from a certified
candidate-level semantics package. -/
def toClosedSoundLocalCountermodelOfSemantics
    {M : SemilocalModel Base Const}
    (C : CertifiedCountermodelCandidate Const Γ)
    (env : SemilocalModel.Env M Γ)
    (global : SemilocalModel.IsGlobalEnv M env)
    (S : CandidateClosedHintikkaSemantics C env)
    (hM : SemilocalModel.SupportsUniformRelativization M) :
    SoundLocalCountermodel C.frontier :=
  C.toCertifiedCompletion.toClosedSoundLocalCountermodelOfSemantics env global S hM

/-- Any closed local agreement witness whose certificate matches the certified
candidate canonically induces a candidate-level semantics package. -/
def toCandidateClosedHintikkaSemanticsOfClosedLocalAgreementWitness
    {M : SemilocalModel Base Const}
    (C : CertifiedCountermodelCandidate Const Γ)
    (W : LocalAgreementWitness M C.frontier)
    (hCert : W.certificate = C.toClosedLocalHintikkaCertificate) :
  CandidateClosedHintikkaSemantics C W.env :=
  C.toCertifiedCompletion.toCandidateClosedHintikkaSemanticsOfClosedLocalAgreementWitness
    W (by
      rw [hCert]
      rfl)

@[simp] theorem toClosedLocalAgreementWitnessOfSemantics_certificate
    {M : SemilocalModel Base Const}
    (C : CertifiedCountermodelCandidate Const Γ)
    (env : SemilocalModel.Env M Γ)
    (global : SemilocalModel.IsGlobalEnv M env)
    (S : CandidateClosedHintikkaSemantics C env) :
    (C.toClosedLocalAgreementWitnessOfSemantics env global S).certificate =
      C.toClosedLocalHintikkaCertificate := by
  rfl

theorem exists_candidateClosedHintikkaSemantics_of_exists_semantics
    (C : CertifiedCountermodelCandidate Const Γ)
    (hSem :
      ∃ (M : SemilocalModel.{u, v, w, w'} Base Const) (env : SemilocalModel.Env M Γ),
        SemilocalModel.IsGlobalEnv M env ∧
        (∀ {φ : Formula Const Γ},
            (Sign.trueE, φ) ∈ C.closedHintikka.formulas →
              SemilocalModel.formulaTruth M env φ = ⊤) ∧
        (∀ {φ : Formula Const Γ},
            (Sign.falseE, φ) ∈ C.closedHintikka.formulas →
              SemilocalModel.formulaTruth M env φ ≠ ⊤)) :
    ∃ (M : SemilocalModel.{u, v, w, w'} Base Const) (env : SemilocalModel.Env M Γ),
      SemilocalModel.IsGlobalEnv M env ∧
      Nonempty (CandidateClosedHintikkaSemantics C env) := by
  rcases hSem with ⟨M, env, global, true_top, false_ne_top⟩
  exact ⟨M, env, global,
    ⟨C.toCandidateClosedHintikkaSemantics (M := M) env true_top false_ne_top⟩⟩

theorem exists_closedLocalAgreementWitness_of_exists_candidateClosedHintikkaSemantics
    (C : CertifiedCountermodelCandidate Const Γ)
    (hSem :
      ∃ (M : SemilocalModel.{u, v, w, w'} Base Const) (env : SemilocalModel.Env M Γ),
        SemilocalModel.IsGlobalEnv M env ∧
        Nonempty (CandidateClosedHintikkaSemantics C env)) :
    ∃ (M : SemilocalModel.{u, v, w, w'} Base Const) (W : LocalAgreementWitness M C.frontier),
      W.certificate = C.toClosedLocalHintikkaCertificate := by
  rcases hSem with ⟨M, env, global, ⟨S⟩⟩
  exact ⟨M, C.toClosedLocalAgreementWitnessOfSemantics (M := M) env global S, by
    simp⟩

theorem exists_candidateClosedHintikkaSemantics_of_exists_closedLocalAgreementWitness
    (C : CertifiedCountermodelCandidate Const Γ)
    (hW :
      ∃ (M : SemilocalModel.{u, v, w, w'} Base Const) (W : LocalAgreementWitness M C.frontier),
        W.certificate = C.toClosedLocalHintikkaCertificate) :
    ∃ (M : SemilocalModel.{u, v, w, w'} Base Const) (env : SemilocalModel.Env M Γ),
      SemilocalModel.IsGlobalEnv M env ∧
      Nonempty (CandidateClosedHintikkaSemantics C env) := by
  rcases hW with ⟨M, W, hCert⟩
  exact ⟨M, W.env, W.global,
    ⟨C.toCandidateClosedHintikkaSemanticsOfClosedLocalAgreementWitness (M := M) W hCert⟩⟩

theorem exists_semilocal_truth_counterexample_of_exists_semantics
    (C : CertifiedCountermodelCandidate Const Γ)
    (hSem :
      ∃ (M : SemilocalModel.{u, v, w, w'} Base Const) (env : SemilocalModel.Env M Γ),
        SemilocalModel.IsGlobalEnv M env ∧
        (∀ {φ : Formula Const Γ},
            (Sign.trueE, φ) ∈ C.closedHintikka.formulas →
              SemilocalModel.formulaTruth M env φ = ⊤) ∧
        (∀ {φ : Formula Const Γ},
            (Sign.falseE, φ) ∈ C.closedHintikka.formulas →
              SemilocalModel.formulaTruth M env φ ≠ ⊤) ∧
        SemilocalModel.SupportsUniformRelativization M) :
    ∃ (M : SemilocalModel.{u, v, w, w'} Base Const) (env : SemilocalModel.Env M Γ),
      SemilocalModel.IsGlobalEnv M env ∧
      SemilocalModel.antecedentTruth M env C.frontier.antecedents = ⊤ ∧
      SemilocalModel.formulaTruth M env C.frontier.succedent ≠ ⊤ ∧
      SemilocalModel.SupportsUniformRelativization M := by
  rcases hSem with ⟨M, env, global, true_top, false_ne_top, hM⟩
  let S : CandidateClosedHintikkaSemantics C env :=
    C.toCandidateClosedHintikkaSemantics env true_top false_ne_top
  let CM : SoundLocalCountermodel C.frontier :=
    C.toClosedSoundLocalCountermodelOfSemantics env global S hM
  exact ⟨M, env, global, CM.agreement.antecedentTruth_eq_top,
    CM.agreement.succedent_ne_top, hM⟩

theorem exists_semilocal_truth_counterexample_of_exists_candidateClosedHintikkaSemantics
    (C : CertifiedCountermodelCandidate Const Γ)
    (hSem :
      ∃ (M : SemilocalModel.{u, v, w, w'} Base Const) (env : SemilocalModel.Env M Γ),
        SemilocalModel.IsGlobalEnv M env ∧
        Nonempty (CandidateClosedHintikkaSemantics C env) ∧
        SemilocalModel.SupportsUniformRelativization M) :
    ∃ (M : SemilocalModel.{u, v, w, w'} Base Const) (env : SemilocalModel.Env M Γ),
      SemilocalModel.IsGlobalEnv M env ∧
      SemilocalModel.antecedentTruth M env C.frontier.antecedents = ⊤ ∧
      SemilocalModel.formulaTruth M env C.frontier.succedent ≠ ⊤ ∧
      SemilocalModel.SupportsUniformRelativization M := by
  rcases hSem with ⟨M, env, global, ⟨S⟩, hM⟩
  let CM : SoundLocalCountermodel C.frontier :=
    C.toClosedSoundLocalCountermodelOfSemantics env global S hM
  exact ⟨M, env, global, CM.agreement.antecedentTruth_eq_top,
    CM.agreement.succedent_ne_top, hM⟩

theorem not_derivable_of_exists_candidateClosedHintikkaSemantics
    (C : CertifiedCountermodelCandidate Const Γ)
    (hSem :
      ∃ (M : SemilocalModel.{u, v, w, w'} Base Const) (env : SemilocalModel.Env M Γ),
        SemilocalModel.IsGlobalEnv M env ∧
        Nonempty (CandidateClosedHintikkaSemantics C env) ∧
        SemilocalModel.SupportsUniformRelativization M) :
    ¬ Derivable (Base := Base) (Const := Const) C.frontier.antecedents C.frontier.succedent := by
  rcases hSem with ⟨M, env, global, ⟨S⟩, hM⟩
  exact (C.toClosedSoundLocalCountermodelOfSemantics (M := M) env global S hM).not_derivable

end CertifiedCountermodelCandidate

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL
