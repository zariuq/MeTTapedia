import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.Hintikka
import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.Soundness

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL

open Mettapedia.Logic.HOL

universe u v

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

/-- A chosen local branch is compatible with the current closed hull when each
formula it adds avoids its flipped counterpart in the already closed Hintikka
set. For genuine branch resolutions this is a singleton compatibility check. -/
def BranchAdditionCompatible (S : SaturationSearchState Const Γ)
    (r : LocalBranchResolution Const Γ) : Prop :=
  ∀ {sf : SignedFormula Const Γ},
    sf ∈ LocalSaturationStep.additions r.step →
      SignedFormula.flip sf ∉ S.hintikka.close.formulas

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
  simpa using D.toSearchRun.frontier_eq

theorem agendaVisible {F : CompletenessFrontier Const Γ}
    {S : SaturationSearchState Const Γ} (D : HeadSearchDerivation F S) :
    S.AgendaVisible := by
  simpa using D.toSearchRun.agendaVisible

theorem formula_mem {F : CompletenessFrontier Const Γ}
    {S : SaturationSearchState Const Γ} (D : HeadSearchDerivation F S)
    {sf : SignedFormula Const Γ}
    (hsf : sf ∈ (SaturationSearchState.initial F).hintikka.formulas) :
    sf ∈ S.hintikka.formulas := by
  simpa using D.toSearchRun.formula_mem hsf

theorem true_mem {F : CompletenessFrontier Const Γ}
    {S : SaturationSearchState Const Γ} (D : HeadSearchDerivation F S)
    {φ : Formula Const Γ} (hφ : φ ∈ F.antecedents) :
    (Sign.trueE, φ) ∈ S.hintikka.formulas := by
  simpa using D.toSearchRun.true_mem hφ

theorem false_mem {F : CompletenessFrontier Const Γ}
    {S : SaturationSearchState Const Γ} (D : HeadSearchDerivation F S) :
    (Sign.falseE, F.succedent) ∈ S.hintikka.formulas := by
  simpa using D.toSearchRun.false_mem

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
  simpa using D.toSearchRun.frontier_eq

theorem agendaVisible {F : CompletenessFrontier Const Γ}
    {S : SaturationSearchState Const Γ} (D : ProductiveHeadSearchDerivation F S) :
    S.AgendaVisible := by
  simpa using D.toSearchRun.agendaVisible

theorem formula_mem {F : CompletenessFrontier Const Γ}
    {S : SaturationSearchState Const Γ} (D : ProductiveHeadSearchDerivation F S)
    {sf : SignedFormula Const Γ}
    (hsf : sf ∈ (SaturationSearchState.initial F).hintikka.formulas) :
    sf ∈ S.hintikka.formulas := by
  simpa using D.toSearchRun.formula_mem hsf

theorem true_mem {F : CompletenessFrontier Const Γ}
    {S : SaturationSearchState Const Γ} (D : ProductiveHeadSearchDerivation F S)
    {φ : Formula Const Γ} (hφ : φ ∈ F.antecedents) :
    (Sign.trueE, φ) ∈ S.hintikka.formulas := by
  simpa using D.toSearchRun.true_mem hφ

theorem false_mem {F : CompletenessFrontier Const Γ}
    {S : SaturationSearchState Const Γ} (D : ProductiveHeadSearchDerivation F S) :
    (Sign.falseE, F.succedent) ∈ S.hintikka.formulas := by
  simpa using D.toSearchRun.false_mem

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
  simpa using D.toSearchRun.frontier_eq

theorem agendaVisible {F : CompletenessFrontier Const Γ}
    {S : SaturationSearchState Const Γ} (D : HeadPrioritySearchDerivation F S) :
    S.AgendaVisible := by
  simpa using D.toSearchRun.agendaVisible

theorem formula_mem {F : CompletenessFrontier Const Γ}
    {S : SaturationSearchState Const Γ} (D : HeadPrioritySearchDerivation F S)
    {sf : SignedFormula Const Γ}
    (hsf : sf ∈ (SaturationSearchState.initial F).hintikka.formulas) :
    sf ∈ S.hintikka.formulas := by
  simpa using D.toSearchRun.formula_mem hsf

theorem true_mem {F : CompletenessFrontier Const Γ}
    {S : SaturationSearchState Const Γ} (D : HeadPrioritySearchDerivation F S)
    {φ : Formula Const Γ} (hφ : φ ∈ F.antecedents) :
    (Sign.trueE, φ) ∈ S.hintikka.formulas := by
  simpa using D.toSearchRun.true_mem hφ

theorem false_mem {F : CompletenessFrontier Const Γ}
    {S : SaturationSearchState Const Γ} (D : HeadPrioritySearchDerivation F S) :
    (Sign.falseE, F.succedent) ∈ S.hintikka.formulas := by
  simpa using D.toSearchRun.false_mem

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
  model : SemilocalModel Base Const
  agreement : LocalAgreementWitness model F

namespace LocalCountermodel

def certificate {F : CompletenessFrontier Const Γ}
    (C : LocalCountermodel (Base := Base) (Const := Const) F) :
    LocalHintikkaCertificate F :=
  C.agreement.certificate

theorem antecedentTruth_eq_top {F : CompletenessFrontier Const Γ}
    (C : LocalCountermodel (Base := Base) (Const := Const) F) :
    SemilocalModel.antecedentTruth C.model C.agreement.env F.antecedents = ⊤ :=
  C.agreement.antecedentTruth_eq_top

theorem succedent_ne_top {F : CompletenessFrontier Const Γ}
    (C : LocalCountermodel (Base := Base) (Const := Const) F) :
    SemilocalModel.formulaTruth C.model C.agreement.env F.succedent ≠ ⊤ :=
  C.agreement.succedent_ne_top

theorem not_validSequent {F : CompletenessFrontier Const Γ}
    (C : LocalCountermodel (Base := Base) (Const := Const) F) :
    ¬ SemilocalModel.ValidSequent C.model F.antecedents F.succedent :=
  C.agreement.not_validSequent

theorem not_derivable {F : CompletenessFrontier Const Γ}
    (C : LocalCountermodel (Base := Base) (Const := Const) F)
    (hM : SemilocalModel.SupportsUniformRelativization C.model) :
    ¬ Derivable (Base := Base) (Const := Const) F.antecedents F.succedent :=
  C.agreement.not_derivable hM

end LocalCountermodel

/-- A local countermodel whose underlying semilocal model also satisfies the
uniform relativization hypothesis needed by the current soundness theorem. -/
structure SoundLocalCountermodel (F : CompletenessFrontier Const Γ)
    extends LocalCountermodel (Base := Base) (Const := Const) F where
  supportsUniformRelativization :
    SemilocalModel.SupportsUniformRelativization model

namespace SoundLocalCountermodel

theorem not_validSequent {F : CompletenessFrontier Const Γ}
    (C : SoundLocalCountermodel (Base := Base) (Const := Const) F) :
    ¬ SemilocalModel.ValidSequent C.model F.antecedents F.succedent :=
  C.toLocalCountermodel.not_validSequent

theorem not_derivable {F : CompletenessFrontier Const Γ}
    (C : SoundLocalCountermodel (Base := Base) (Const := Const) F) :
    ¬ Derivable (Base := Base) (Const := Const) F.antecedents F.succedent :=
  C.toLocalCountermodel.not_derivable C.supportsUniformRelativization

end SoundLocalCountermodel

namespace LocalAgreementWitness

/-- Package an agreeing witness as the current semilocal countermodel object. -/
def toLocalCountermodel
    {M : SemilocalModel Base Const} {F : CompletenessFrontier Const Γ}
    (W : LocalAgreementWitness M F) :
    LocalCountermodel (Base := Base) (Const := Const) F :=
  { model := M
    agreement := W }

/-- Package an agreeing witness together with the semilocal soundness hypothesis
as the stronger countermodel object used to refute derivability. -/
def toSoundLocalCountermodel
    {M : SemilocalModel Base Const} {F : CompletenessFrontier Const Γ}
    (W : LocalAgreementWitness M F)
    (hM : SemilocalModel.SupportsUniformRelativization M) :
    SoundLocalCountermodel (Base := Base) (Const := Const) F :=
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
    LocalCountermodel (Base := Base) (Const := Const) C.frontier :=
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
    SoundLocalCountermodel (Base := Base) (Const := Const) C.frontier :=
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
    LocalCountermodel (Base := Base) (Const := Const) C.frontier :=
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
    LocalCountermodel (Base := Base) (Const := Const) C.frontier :=
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
    SoundLocalCountermodel (Base := Base) (Const := Const) C.frontier :=
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
    SoundLocalCountermodel (Base := Base) (Const := Const) C.frontier :=
  C.toClosedSoundLocalCountermodelOfNoncontradictory
    (C.toClosedLocalConsistentHintikka hCons).noncontradictory
    env global true_top false_ne_top hM

end CountermodelCandidate

namespace CompletenessFrontier

/-- View a frontier as the underlying sequent-style Hintikka goal. -/
def toHintikkaGoal (F : CompletenessFrontier Const Γ) : HintikkaGoal Const Γ :=
  { antecedents := F.antecedents
    succedent := F.succedent }

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

theorem initial_icttConsistent_iff_not_derivable
    (F : CompletenessFrontier Const Γ) :
    (SaturationSearchState.initial F).hintikka.ICTTConsistent ↔
      ¬ Derivable (Base := Base) (Const := Const) F.antecedents F.succedent := by
  simpa [CompletenessFrontier.initialHintikkaSet] using
    F.initialHintikkaSet_icttConsistent_iff_not_derivable

end CompletenessFrontier

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL
