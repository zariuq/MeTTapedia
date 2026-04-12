import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.Completeness

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL

/-!
# Completeness Regression

Canaries around the current search-to-countermodel spine. In particular, these
examples record that arbitrary terminal head-priority completion does not by
itself force non-contradiction: a bad branch choice can still end in a
contradictory local candidate.
-/

namespace CompletenessRegression

open Mettapedia.Logic.HOL

inductive BaseSort where
  | atom
  deriving DecidableEq, Repr

def Const : Ty BaseSort → Type := fun _ => PEmpty

def badFrontier : CompletenessFrontier Const [] :=
  { antecedents := [.top]
    succedent := .and .top .top }

def badResolution : SaturationSearchState.LocalBranchResolution Const [] :=
  { target := .falseAnd .top .top
    step := .falseAndLeft .top .top
    admissible := by
      simp [LocalBranchTarget.AcceptsStep, LocalBranchTarget.branches] }

@[simp] theorem badInitialAgenda :
    (SaturationSearchState.initial badFrontier).agenda =
      [LocalBranchTarget.falseAnd (.top : Formula Const []) (.top : Formula Const [])] := by
  simp [SaturationSearchState.initial, badFrontier, HintikkaSet.localBranchTargets,
    LocalBranchTarget.ofSignedFormula]

theorem badCanResolveHead :
    (SaturationSearchState.initial badFrontier).CanResolveHead badResolution := by
  simp [SaturationSearchState.CanResolveHead, SaturationSearchState.nextAgendaTarget?,
    badResolution]

def badState : SaturationSearchState Const [] :=
  { frontier := badFrontier
    hintikka :=
      { formulas :=
          [(Sign.falseE, (.top : Formula Const [])),
            (Sign.trueE, (.top : Formula Const [])),
            (Sign.falseE, (.and (.top : Formula Const []) (.top : Formula Const [])))] }
    agenda := [] }

@[simp] theorem badState_formulas :
    badState.hintikka.formulas =
      [(Sign.falseE, (.top : Formula Const [])),
        (Sign.trueE, (.top : Formula Const [])),
        (Sign.falseE, (.and (.top : Formula Const []) (.top : Formula Const [])))] := by
  rfl

@[simp] theorem badState_agenda : badState.agenda = [] := by
  rfl

theorem mem_badState_formulas {sf : SignedFormula Const []} :
    sf ∈ badState.hintikka.formulas ↔
      sf = (Sign.falseE, (.top : Formula Const [])) ∨
      sf = (Sign.trueE, (.top : Formula Const [])) ∨
      sf = (Sign.falseE, (.and (.top : Formula Const []) (.top : Formula Const []))) := by
  simp [badState_formulas]

theorem badState_eq_resolveHead :
    badState =
      (SaturationSearchState.initial badFrontier).resolveHead
        badResolution badCanResolveHead := by
  rfl

theorem badState_noProductiveTriggeredStep :
    badState.NoProductiveTriggeredStep := by
  intro t
  rcases t with ⟨s, hs, hfresh⟩
  cases s with
  | trueAnd φ ψ =>
      have hs' := mem_badState_formulas.mp hs
      simp [DeterministicLocalSaturationStep.premise, LocalSaturationStep.premise] at hs'
      rcases hs' with h | h | h <;> cases h
  | falseOr φ ψ =>
      have hs' := mem_badState_formulas.mp hs
      simp [DeterministicLocalSaturationStep.premise, LocalSaturationStep.premise] at hs'
      rcases hs' with h | h | h <;> cases h
  | trueAll φ t =>
      have hs' := mem_badState_formulas.mp hs
      simp [DeterministicLocalSaturationStep.premise, LocalSaturationStep.premise] at hs'
      rcases hs' with h | h | h <;> cases h
  | falseAllWitness φ t =>
      have hs' := mem_badState_formulas.mp hs
      simp [DeterministicLocalSaturationStep.premise, LocalSaturationStep.premise] at hs'
      rcases hs' with h | h | h <;> cases h
  | trueExWitness φ t =>
      have hs' := mem_badState_formulas.mp hs
      simp [DeterministicLocalSaturationStep.premise, LocalSaturationStep.premise] at hs'
      rcases hs' with h | h | h <;> cases h
  | falseEx φ t =>
      have hs' := mem_badState_formulas.mp hs
      simp [DeterministicLocalSaturationStep.premise, LocalSaturationStep.premise] at hs'
      rcases hs' with h | h | h <;> cases h

theorem badState_branchClosed :
    badState.hintikka.BranchClosed := by
  intro b
  cases b with
  | falseAnd φ ψ =>
      refine ⟨.falseAndLeft φ ψ, by simp [LocalBranchTarget.AcceptsStep, LocalBranchTarget.branches], ?_⟩
      intro hprem sf hsf
      have hprem' := mem_badState_formulas.mp hprem
      rcases hprem' with h | h | h
      · cases h
      · cases h
      · cases h
        exact (mem_badState_formulas).2 <|
          Or.inl (by simpa [LocalSaturationStep.additions] using hsf)
  | trueOr φ ψ =>
      refine ⟨.trueOrLeft φ ψ, by simp [LocalBranchTarget.AcceptsStep, LocalBranchTarget.branches], ?_⟩
      intro hprem
      have hprem' := mem_badState_formulas.mp hprem
      rcases hprem' with h | h | h <;> cases h

theorem badState_terminal : badState.IsTerminal := by
  exact ⟨badState_agenda, badState_noProductiveTriggeredStep⟩

def badDerivation :
    SaturationSearchState.HeadPrioritySearchDerivation badFrontier badState :=
  by
    simpa [badState_eq_resolveHead] using
      (SaturationSearchState.HeadPrioritySearchDerivation.resolveHead
        (F := badFrontier)
        SaturationSearchState.HeadPrioritySearchDerivation.initial
        badResolution badCanResolveHead)

def badCompletion : SaturationSearchState.HeadPriorityCompletion badFrontier :=
  { state := badState
    derivation := badDerivation
    terminal := badState_terminal
    branchClosed := badState_branchClosed }

def badCandidate : CountermodelCandidate Const [] :=
  { frontier := badFrontier
    completion := badCompletion }

theorem badFrontier_derivable :
    Derivable (Base := BaseSort) (Const := Const)
      badFrontier.antecedents badFrontier.succedent := by
  refine Derivable.andR ?_ ?_
  · exact Derivable.ax (by simp [badFrontier])
  · exact Derivable.ax (by simp [badFrontier])

theorem badInitialHintikka_not_icttConsistent :
    ¬ badFrontier.initialHintikkaSet.ICTTConsistent := by
  rw [CompletenessFrontier.initialHintikkaSet_icttConsistent_iff_not_derivable]
  intro hNot
  exact hNot badFrontier_derivable

theorem badCandidate_closedHintikka_not_icttConsistent :
    ¬ badCandidate.closedHintikka.ICTTConsistent := by
  intro hCons
  have hFalseTop :
      (Sign.falseE, (.top : Formula Const [])) ∈ badCandidate.closedHintikka.formulas := by
    exact HintikkaSet.mem_close_of_mem (by simp [badCandidate, CountermodelCandidate.hintikka,
      CountermodelCandidate.state, badCompletion])
  exact (HintikkaSet.not_derivable_of_false_mem_of_icttConsistent hCons hFalseTop)
    Derivable.topR

theorem badCandidate_closedHintikka_not_noncontradictory :
    ¬ badCandidate.closedHintikka.Noncontradictory := by
  intro h
  have hTrue :
      (Sign.trueE, (.top : Formula Const [])) ∈ badCandidate.closedHintikka.formulas := by
    exact badCandidate.true_mem_closedHintikka (by simp [badCandidate, badFrontier])
  have hFalse :
      (Sign.falseE, (.top : Formula Const [])) ∈ badCandidate.closedHintikka.formulas := by
    exact HintikkaSet.mem_close_of_mem (by simp [badCandidate, CountermodelCandidate.hintikka,
      CountermodelCandidate.state, badCompletion])
  exact h (HintikkaSet.contradictory_of_conflict hTrue hFalse)

theorem not_all_terminal_candidates_noncontradictory :
    ¬ ∀ C : CountermodelCandidate Const [], C.closedHintikka.Noncontradictory := by
  intro h
  exact badCandidate_closedHintikka_not_noncontradictory (h badCandidate)

theorem not_all_terminal_candidates_icttConsistent :
    ¬ ∀ C : CountermodelCandidate Const [], C.closedHintikka.ICTTConsistent := by
  intro h
  exact badCandidate_closedHintikka_not_icttConsistent (h badCandidate)

example :
    badState.IsTerminal :=
  badState_terminal

example :
    ¬ badCandidate.closedHintikka.Noncontradictory :=
  badCandidate_closedHintikka_not_noncontradictory

example :
    ¬ badCandidate.closedHintikka.ICTTConsistent :=
  badCandidate_closedHintikka_not_icttConsistent

/-- Trivial global model used to separate an underivable frontier from a bad
branch choice. -/
def underivableCarrier : Ty BaseSort → Type
  | .prop => Prop
  | .base _ => PUnit
  | .arr σ τ => underivableCarrier σ → underivableCarrier τ

def underivableModel : GlobalModel BaseSort Const where
  toSemilocalModel :=
    { toApplicativeStructure :=
        { Carrier := underivableCarrier
          const := fun c => nomatch c
          app := fun f x => f x
          lam := fun f => f
          beta := by
            intro σ τ f x
            rfl
          eta := by
            intro σ τ f
            rfl }
      Omega := Prop
      frame := inferInstance
      truth := fun p => p
      extent := fun _ => True
      topP := True
      botP := False
      andP := And
      orP := Or
      impP := fun p q => p → q
      eqP := fun x y => x = y
      allP := fun f => ∀ x, f x
      exP := fun f => ∃ x, f x
      truth_top := rfl
      truth_bot := rfl
      truth_and := by
        intro p q
        rfl
      truth_or := by
        intro p q
        rfl
      truth_imp := by
        intro p q
        rfl
      truth_all := by
        intro σ f
        apply propext
        simp
      truth_ex := by
        intro σ f
        apply propext
        simp }
  global := by
    intro τ x
    rfl

def underivableEmptyEnv : GlobalModel.Env underivableModel [] :=
  fun {_τ} v => nomatch v

def underivableFrontier : CompletenessFrontier Const [] :=
  { antecedents := [.top, .or .bot .top]
    succedent := .bot }

theorem underivableFrontier_not_valid :
    ¬ GlobalModel.ValidSequent underivableModel
      underivableFrontier.antecedents underivableFrontier.succedent := by
  intro hvalid
  have h := hvalid underivableEmptyEnv
  simp [GlobalModel.antecedentTruth, GlobalModel.formulaTruth, SemilocalModel.antecedentTruth,
    SemilocalModel.formulaTruth, SemilocalModel.eval, underivableFrontier,
    underivableModel] at h

theorem underivableFrontier_not_derivable :
    ¬ Derivable (Base := BaseSort) (Const := Const)
      underivableFrontier.antecedents underivableFrontier.succedent := by
  intro hDer
  exact underivableFrontier_not_valid (GlobalModel.soundness underivableModel hDer)

theorem underivableInitialHintikka_icttConsistent :
    (SaturationSearchState.initial underivableFrontier).hintikka.ICTTConsistent := by
  rw [CompletenessFrontier.initial_icttConsistent_iff_not_derivable]
  exact underivableFrontier_not_derivable

def underivableResolution : SaturationSearchState.LocalBranchResolution Const [] :=
  { target := .trueOr .bot .top
    step := .trueOrLeft .bot .top
    admissible := by
      simp [LocalBranchTarget.AcceptsStep, LocalBranchTarget.branches] }

@[simp] theorem underivableInitialAgenda :
    (SaturationSearchState.initial underivableFrontier).agenda =
      [LocalBranchTarget.trueOr (.bot : Formula Const []) (.top : Formula Const [])] := by
  simp [SaturationSearchState.initial, underivableFrontier, HintikkaSet.localBranchTargets,
    LocalBranchTarget.ofSignedFormula]

theorem underivableCanResolveHead :
    (SaturationSearchState.initial underivableFrontier).CanResolveHead underivableResolution := by
  simp [SaturationSearchState.CanResolveHead, SaturationSearchState.nextAgendaTarget?,
    underivableResolution]

def goodResolution : SaturationSearchState.LocalBranchResolution Const [] :=
  { target := .trueOr .bot .top
    step := .trueOrRight .bot .top
    admissible := by
      simp [LocalBranchTarget.AcceptsStep, LocalBranchTarget.branches] }

theorem goodCanResolveHead :
    (SaturationSearchState.initial underivableFrontier).CanResolveHead goodResolution := by
  simp [SaturationSearchState.CanResolveHead, SaturationSearchState.nextAgendaTarget?,
    goodResolution]

def goodState : SaturationSearchState Const [] :=
  { frontier := underivableFrontier
    hintikka :=
      { formulas :=
          [(Sign.trueE, (.top : Formula Const [])),
            (Sign.trueE, (.top : Formula Const [])),
            (Sign.trueE, (.or (.bot : Formula Const []) (.top : Formula Const []))),
            (Sign.falseE, (.bot : Formula Const []))] }
    agenda := [] }

@[simp] theorem goodState_formulas :
    goodState.hintikka.formulas =
      [(Sign.trueE, (.top : Formula Const [])),
        (Sign.trueE, (.top : Formula Const [])),
        (Sign.trueE, (.or (.bot : Formula Const []) (.top : Formula Const []))),
        (Sign.falseE, (.bot : Formula Const []))] := by
  rfl

theorem mem_goodState_formulas {sf : SignedFormula Const []} :
    sf ∈ goodState.hintikka.formulas ↔
      sf = (Sign.trueE, (.top : Formula Const [])) ∨
      sf = (Sign.trueE, (.top : Formula Const [])) ∨
      sf = (Sign.trueE, (.or (.bot : Formula Const []) (.top : Formula Const []))) ∨
      sf = (Sign.falseE, (.bot : Formula Const [])) := by
  simp [goodState_formulas]

@[simp] theorem goodState_agenda : goodState.agenda = [] := by
  rfl

theorem goodState_eq_resolveHead :
    goodState =
      (SaturationSearchState.initial underivableFrontier).resolveHead
        goodResolution goodCanResolveHead := by
  rfl

theorem goodState_noProductiveTriggeredStep :
    goodState.NoProductiveTriggeredStep := by
  intro t
  rcases t with ⟨s, hs, hfresh⟩
  cases s with
  | trueAnd φ ψ =>
      have hs' := mem_goodState_formulas.mp hs
      simp [DeterministicLocalSaturationStep.premise, LocalSaturationStep.premise] at hs'
      rcases hs' with h | h | h | h <;> cases h
  | falseOr φ ψ =>
      have hs' := mem_goodState_formulas.mp hs
      simp [DeterministicLocalSaturationStep.premise, LocalSaturationStep.premise] at hs'
      rcases hs' with h | h | h | h <;> cases h
  | trueAll φ t =>
      have hs' := mem_goodState_formulas.mp hs
      simp [DeterministicLocalSaturationStep.premise, LocalSaturationStep.premise] at hs'
      rcases hs' with h | h | h | h <;> cases h
  | falseAllWitness φ t =>
      have hs' := mem_goodState_formulas.mp hs
      simp [DeterministicLocalSaturationStep.premise, LocalSaturationStep.premise] at hs'
      rcases hs' with h | h | h | h <;> cases h
  | trueExWitness φ t =>
      have hs' := mem_goodState_formulas.mp hs
      simp [DeterministicLocalSaturationStep.premise, LocalSaturationStep.premise] at hs'
      rcases hs' with h | h | h | h <;> cases h
  | falseEx φ t =>
      have hs' := mem_goodState_formulas.mp hs
      simp [DeterministicLocalSaturationStep.premise, LocalSaturationStep.premise] at hs'
      rcases hs' with h | h | h | h <;> cases h

theorem goodState_branchClosed :
    goodState.hintikka.BranchClosed := by
  intro b
  cases b with
  | falseAnd φ ψ =>
      refine ⟨.falseAndLeft φ ψ, by simp [LocalBranchTarget.AcceptsStep, LocalBranchTarget.branches], ?_⟩
      intro hprem
      have hprem' := mem_goodState_formulas.mp hprem
      rcases hprem' with h | h | h | h <;> cases h
  | trueOr φ ψ =>
      refine ⟨.trueOrRight φ ψ, by simp [LocalBranchTarget.AcceptsStep, LocalBranchTarget.branches], ?_⟩
      intro hprem sf hsf
      have hprem' := mem_goodState_formulas.mp hprem
      rcases hprem' with h | h | h | h
      · cases h
      · cases h
      · cases h
        exact (mem_goodState_formulas).2 <|
          Or.inl (by simpa [LocalSaturationStep.additions] using hsf)
      · cases h

theorem goodState_terminal : goodState.IsTerminal := by
  exact ⟨goodState_agenda, goodState_noProductiveTriggeredStep⟩

def goodDerivation :
    SaturationSearchState.HeadPrioritySearchDerivation underivableFrontier goodState :=
  by
    simpa [goodState_eq_resolveHead] using
      (SaturationSearchState.HeadPrioritySearchDerivation.resolveHead
        (F := underivableFrontier)
        SaturationSearchState.HeadPrioritySearchDerivation.initial
        goodResolution goodCanResolveHead)

def goodCompletion : SaturationSearchState.HeadPriorityCompletion underivableFrontier :=
  { state := goodState
    derivation := goodDerivation
    terminal := goodState_terminal
    branchClosed := goodState_branchClosed }

def goodCandidate : CountermodelCandidate Const [] :=
  { frontier := underivableFrontier
    completion := goodCompletion }

def underivableState : SaturationSearchState Const [] :=
  { frontier := underivableFrontier
    hintikka :=
      { formulas :=
          [(Sign.trueE, (.bot : Formula Const [])),
            (Sign.trueE, (.top : Formula Const [])),
            (Sign.trueE, (.or (.bot : Formula Const []) (.top : Formula Const []))),
            (Sign.falseE, (.bot : Formula Const []))] }
    agenda := [] }

@[simp] theorem underivableState_formulas :
    underivableState.hintikka.formulas =
      [(Sign.trueE, (.bot : Formula Const [])),
        (Sign.trueE, (.top : Formula Const [])),
        (Sign.trueE, (.or (.bot : Formula Const []) (.top : Formula Const []))),
        (Sign.falseE, (.bot : Formula Const []))] := by
  rfl

theorem mem_underivableState_formulas {sf : SignedFormula Const []} :
    sf ∈ underivableState.hintikka.formulas ↔
      sf = (Sign.trueE, (.bot : Formula Const [])) ∨
      sf = (Sign.trueE, (.top : Formula Const [])) ∨
      sf = (Sign.trueE, (.or (.bot : Formula Const []) (.top : Formula Const []))) ∨
      sf = (Sign.falseE, (.bot : Formula Const [])) := by
  simp [underivableState_formulas]

@[simp] theorem underivableState_agenda : underivableState.agenda = [] := by
  rfl

theorem underivableState_eq_resolveHead :
    underivableState =
      (SaturationSearchState.initial underivableFrontier).resolveHead
        underivableResolution underivableCanResolveHead := by
  rfl

theorem underivableState_noProductiveTriggeredStep :
    underivableState.NoProductiveTriggeredStep := by
  intro t
  rcases t with ⟨s, hs, hfresh⟩
  cases s with
  | trueAnd φ ψ =>
      have hs' := mem_underivableState_formulas.mp hs
      simp [DeterministicLocalSaturationStep.premise, LocalSaturationStep.premise] at hs'
      rcases hs' with h | h | h | h <;> cases h
  | falseOr φ ψ =>
      have hs' := mem_underivableState_formulas.mp hs
      simp [DeterministicLocalSaturationStep.premise, LocalSaturationStep.premise] at hs'
      rcases hs' with h | h | h | h <;> cases h
  | trueAll φ t =>
      have hs' := mem_underivableState_formulas.mp hs
      simp [DeterministicLocalSaturationStep.premise, LocalSaturationStep.premise] at hs'
      rcases hs' with h | h | h | h <;> cases h
  | falseAllWitness φ t =>
      have hs' := mem_underivableState_formulas.mp hs
      simp [DeterministicLocalSaturationStep.premise, LocalSaturationStep.premise] at hs'
      rcases hs' with h | h | h | h <;> cases h
  | trueExWitness φ t =>
      have hs' := mem_underivableState_formulas.mp hs
      simp [DeterministicLocalSaturationStep.premise, LocalSaturationStep.premise] at hs'
      rcases hs' with h | h | h | h <;> cases h
  | falseEx φ t =>
      have hs' := mem_underivableState_formulas.mp hs
      simp [DeterministicLocalSaturationStep.premise, LocalSaturationStep.premise] at hs'
      rcases hs' with h | h | h | h <;> cases h

theorem underivableState_branchClosed :
    underivableState.hintikka.BranchClosed := by
  intro b
  cases b with
  | falseAnd φ ψ =>
      refine ⟨.falseAndLeft φ ψ, by simp [LocalBranchTarget.AcceptsStep, LocalBranchTarget.branches], ?_⟩
      intro hprem
      have hprem' := mem_underivableState_formulas.mp hprem
      rcases hprem' with h | h | h | h <;> cases h
  | trueOr φ ψ =>
      refine ⟨.trueOrLeft φ ψ, by simp [LocalBranchTarget.AcceptsStep, LocalBranchTarget.branches], ?_⟩
      intro hprem sf hsf
      have hprem' := mem_underivableState_formulas.mp hprem
      rcases hprem' with h | h | h | h
      · cases h
      · cases h
      · cases h
        exact (mem_underivableState_formulas).2 <|
          Or.inl (by simpa [LocalSaturationStep.additions] using hsf)
      · cases h

theorem underivableState_terminal : underivableState.IsTerminal := by
  exact ⟨underivableState_agenda, underivableState_noProductiveTriggeredStep⟩

def underivableDerivation :
    SaturationSearchState.HeadPrioritySearchDerivation underivableFrontier underivableState :=
  by
    simpa [underivableState_eq_resolveHead] using
      (SaturationSearchState.HeadPrioritySearchDerivation.resolveHead
        (F := underivableFrontier)
        SaturationSearchState.HeadPrioritySearchDerivation.initial
        underivableResolution underivableCanResolveHead)

def underivableCompletion : SaturationSearchState.HeadPriorityCompletion underivableFrontier :=
  { state := underivableState
    derivation := underivableDerivation
    terminal := underivableState_terminal
    branchClosed := underivableState_branchClosed }

def underivableCandidate : CountermodelCandidate Const [] :=
  { frontier := underivableFrontier
    completion := underivableCompletion }

theorem underivableCandidate_closedHintikka_not_noncontradictory :
    ¬ underivableCandidate.closedHintikka.Noncontradictory := by
  intro h
  have hTrueBot :
      (Sign.trueE, (.bot : Formula Const [])) ∈ underivableCandidate.closedHintikka.formulas := by
    exact HintikkaSet.mem_close_of_mem (by
      simp [underivableCandidate, CountermodelCandidate.hintikka,
        CountermodelCandidate.state, underivableCompletion])
  have hFalseBot :
      (Sign.falseE, (.bot : Formula Const [])) ∈ underivableCandidate.closedHintikka.formulas := by
    exact HintikkaSet.mem_close_of_mem (by
      simp [underivableCandidate, CountermodelCandidate.hintikka,
        CountermodelCandidate.state, underivableCompletion])
  exact h (HintikkaSet.contradictory_of_conflict hTrueBot hFalseBot)

theorem underivableCandidate_closedHintikka_not_icttConsistent :
    ¬ underivableCandidate.closedHintikka.ICTTConsistent := by
  intro hCons
  have hTrueBot :
      (Sign.trueE, (.bot : Formula Const [])) ∈ underivableCandidate.closedHintikka.formulas := by
    exact HintikkaSet.mem_close_of_mem (by
      simp [underivableCandidate, CountermodelCandidate.hintikka,
        CountermodelCandidate.state, underivableCompletion])
  have hFalseBot :
      (Sign.falseE, (.bot : Formula Const [])) ∈ underivableCandidate.closedHintikka.formulas := by
    exact HintikkaSet.mem_close_of_mem (by
      simp [underivableCandidate, CountermodelCandidate.hintikka,
        CountermodelCandidate.state, underivableCompletion])
  exact (HintikkaSet.not_derivable_of_false_mem_of_icttConsistent hCons hFalseBot)
    (HintikkaSet.derivable_of_true_mem hTrueBot)

theorem underivableResolution_breaks_initial_icttConsistent :
    (SaturationSearchState.initial underivableFrontier).hintikka.ICTTConsistent ∧
      ¬ ((SaturationSearchState.initial underivableFrontier).resolveHead
          underivableResolution underivableCanResolveHead).hintikka.close.ICTTConsistent := by
  constructor
  · exact underivableInitialHintikka_icttConsistent
  · simpa [underivableState_eq_resolveHead, CountermodelCandidate.closedHintikka,
      CountermodelCandidate.hintikka, CountermodelCandidate.state, underivableCandidate,
      underivableCompletion] using underivableCandidate_closedHintikka_not_icttConsistent

theorem underivableInitialClosedHintikka_false_mem_iff_bot {φ : Formula Const []} :
    (Sign.falseE, φ) ∈ (SaturationSearchState.initial underivableFrontier).hintikka.close.formulas ↔
      φ = (.bot : Formula Const []) := by
  simp [SaturationSearchState.initial, underivableFrontier, HintikkaSet.close]

theorem underivableInitialClosedHintikka_true_mem_iff
    {φ : Formula Const []} :
    (Sign.trueE, φ) ∈ (SaturationSearchState.initial underivableFrontier).hintikka.close.formulas ↔
      φ = (.top : Formula Const []) ∨
        φ = (.or (.bot : Formula Const []) (.top : Formula Const [])) := by
  simp [SaturationSearchState.initial, underivableFrontier, HintikkaSet.close]

theorem underivableInitialClosedHintikka_trueBot_not_mem :
    (Sign.trueE, (.bot : Formula Const [])) ∉
      (SaturationSearchState.initial underivableFrontier).hintikka.close.formulas := by
  simp [SaturationSearchState.initial, underivableFrontier, HintikkaSet.close]

theorem underivableInitialClosedHintikka_falseTop_not_mem :
    (Sign.falseE, (.top : Formula Const [])) ∉
      (SaturationSearchState.initial underivableFrontier).hintikka.close.formulas := by
  simp [SaturationSearchState.initial, underivableFrontier, HintikkaSet.close]

theorem underivableInitialClosedHintikka_noncontradictory :
    (SaturationSearchState.initial underivableFrontier).hintikka.close.Noncontradictory := by
  intro hContra
  rcases hContra with hConflict | hContra
  · rcases hConflict with ⟨φ, hTrue, hFalse⟩
    have hBot : φ = (.bot : Formula Const []) :=
      underivableInitialClosedHintikka_false_mem_iff_bot.mp hFalse
    subst hBot
    exact underivableInitialClosedHintikka_trueBot_not_mem hTrue
  · rcases hContra with hTrueBot | hFalseTop
    · exact underivableInitialClosedHintikka_trueBot_not_mem hTrueBot
    · exact underivableInitialClosedHintikka_falseTop_not_mem hFalseTop

theorem goodResolution_branchAdditionCompatible :
    (SaturationSearchState.initial underivableFrontier).BranchAdditionCompatible goodResolution := by
  intro sf hsf
  have hEq : sf = (Sign.trueE, (.top : Formula Const [])) := by
    simpa [goodResolution, LocalSaturationStep.additions] using hsf
  subst hEq
  exact underivableInitialClosedHintikka_falseTop_not_mem

theorem underivableResolution_not_branchAdditionCompatible :
    ¬ (SaturationSearchState.initial underivableFrontier).BranchAdditionCompatible
      underivableResolution := by
  intro hCompat
  have hNot : SignedFormula.flip (Sign.trueE, (.bot : Formula Const [])) ∉
      (SaturationSearchState.initial underivableFrontier).hintikka.close.formulas := by
    exact hCompat (by simp [underivableResolution, LocalSaturationStep.additions])
  have hFalseBot :
      (Sign.falseE, (.bot : Formula Const [])) ∈
        (SaturationSearchState.initial underivableFrontier).hintikka.close.formulas := by
    exact HintikkaSet.falseBot_mem_close
      ((SaturationSearchState.initial underivableFrontier).hintikka)
  exact hNot hFalseBot

theorem goodCandidate_closedHintikka_false_mem_iff_bot {φ : Formula Const []} :
    (Sign.falseE, φ) ∈ goodCandidate.closedHintikka.formulas ↔
      φ = (.bot : Formula Const []) := by
  simp [goodCandidate, CountermodelCandidate.closedHintikka, CountermodelCandidate.hintikka,
    CountermodelCandidate.state, goodCompletion, goodState_formulas, HintikkaSet.close]

theorem goodCandidate_closedHintikka_true_mem_iff
    {φ : Formula Const []} :
    (Sign.trueE, φ) ∈ goodCandidate.closedHintikka.formulas ↔
      φ = (.top : Formula Const []) ∨
        φ = (.or (.bot : Formula Const []) (.top : Formula Const [])) := by
  simp [goodCandidate, CountermodelCandidate.closedHintikka, CountermodelCandidate.hintikka,
    CountermodelCandidate.state, goodCompletion, goodState_formulas, HintikkaSet.close]

theorem goodCandidate_closedHintikka_trueBot_not_mem :
    (Sign.trueE, (.bot : Formula Const [])) ∉ goodCandidate.closedHintikka.formulas := by
  simp [goodCandidate, CountermodelCandidate.closedHintikka, CountermodelCandidate.hintikka,
    CountermodelCandidate.state, goodCompletion, goodState_formulas, HintikkaSet.close]

theorem goodCandidate_closedHintikka_falseTop_not_mem :
    (Sign.falseE, (.top : Formula Const [])) ∉ goodCandidate.closedHintikka.formulas := by
  simp [goodCandidate, CountermodelCandidate.closedHintikka, CountermodelCandidate.hintikka,
    CountermodelCandidate.state, goodCompletion, goodState_formulas, HintikkaSet.close]

theorem goodCandidate_closedHintikka_noncontradictory :
    goodCandidate.closedHintikka.Noncontradictory := by
  exact goodCandidate.closedHintikka_noncontradictory_of_initialResolveHead
    goodCanResolveHead
    goodState_eq_resolveHead.symm
    underivableInitialClosedHintikka_noncontradictory
    goodResolution_branchAdditionCompatible

def goodClosedCertificate : LocalHintikkaCertificate underivableFrontier :=
  goodCandidate.toClosedLocalHintikkaCertificateOfInitialResolveHead
    goodCanResolveHead
    goodState_eq_resolveHead.symm
    underivableInitialClosedHintikka_noncontradictory
    goodResolution_branchAdditionCompatible

theorem goodClosed_true_top
    {φ : Formula Const []}
    (hφ : (Sign.trueE, φ) ∈ goodCandidate.closedHintikka.formulas) :
    SemilocalModel.formulaTruth underivableModel.toSemilocalModel underivableEmptyEnv φ = ⊤ := by
  rcases goodCandidate_closedHintikka_true_mem_iff.mp hφ with rfl | rfl
  · simp
  · simp

theorem goodClosed_false_ne_top
    {φ : Formula Const []}
    (hφ : (Sign.falseE, φ) ∈ goodCandidate.closedHintikka.formulas) :
    SemilocalModel.formulaTruth underivableModel.toSemilocalModel underivableEmptyEnv φ ≠ ⊤ := by
  have hBot : φ = (.bot : Formula Const []) :=
    goodCandidate_closedHintikka_false_mem_iff_bot.mp hφ
  subst hBot
  intro h
  simp [underivableModel, SemilocalModel.formulaTruth, SemilocalModel.eval] at h

def goodClosedAgreementWitness :
    LocalAgreementWitness underivableModel.toSemilocalModel underivableFrontier :=
  goodCandidate.toClosedLocalAgreementWitnessOfNoncontradictory
    goodCandidate_closedHintikka_noncontradictory
    underivableEmptyEnv
    (GlobalModel.isGlobalEnv underivableModel underivableEmptyEnv)
    (by
      intro φ hφ
      exact goodClosed_true_top hφ)
    (by
      intro φ hφ
      exact goodClosed_false_ne_top hφ)

def goodClosedCountermodel :
    LocalCountermodel (Base := BaseSort) (Const := Const) underivableFrontier :=
  goodClosedAgreementWitness.toLocalCountermodel

def goodClosedSoundCountermodel :
    SoundLocalCountermodel (Base := BaseSort) (Const := Const) underivableFrontier :=
  goodClosedAgreementWitness.toSoundLocalCountermodel
    (GlobalModel.supportsUniformRelativization underivableModel)

example :
    (SaturationSearchState.initial underivableFrontier).hintikka.ICTTConsistent :=
  underivableInitialHintikka_icttConsistent

example :
    ¬ underivableCandidate.closedHintikka.ICTTConsistent :=
  underivableCandidate_closedHintikka_not_icttConsistent

example :
    goodCandidate.closedHintikka.Noncontradictory :=
  goodCandidate_closedHintikka_noncontradictory

example :
    LocalHintikkaCertificate underivableFrontier :=
  goodClosedCertificate

example :
    LocalCountermodel (Base := BaseSort) (Const := Const) underivableFrontier :=
  goodClosedCountermodel

example :
    ¬ Derivable (Base := BaseSort) (Const := Const)
      underivableFrontier.antecedents underivableFrontier.succedent :=
  goodClosedSoundCountermodel.not_derivable

example :
    (SaturationSearchState.initial underivableFrontier).hintikka.ICTTConsistent ∧
      ¬ ((SaturationSearchState.initial underivableFrontier).resolveHead
          underivableResolution underivableCanResolveHead).hintikka.close.ICTTConsistent :=
  underivableResolution_breaks_initial_icttConsistent

end CompletenessRegression

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL
