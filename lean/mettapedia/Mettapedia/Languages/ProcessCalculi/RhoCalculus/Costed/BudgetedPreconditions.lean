import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed.Bridge
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed.BudgetedRuntime

/-!
# Executable precondition witnesses for budgeted cost-rho

The differential boundary reports the hypotheses used by the runtime bridge.
These checks are executable, while the accompanying theorems connect each
Boolean result to the corresponding proposition.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed

/-- Executable pairwise checking that compares each item with every later
item. -/
def pairwiseCheck {Alpha : Type} (relation : Alpha → Alpha → Bool) :
    List Alpha → Bool
  | [] => true
  | head :: tail => tail.all (relation head) && pairwiseCheck relation tail

theorem pairwiseCheck_true_iff {Alpha : Type}
    (relation : Alpha → Alpha → Bool) (items : List Alpha) :
    pairwiseCheck relation items = true ↔
      items.Pairwise fun left right => relation left right = true := by
  induction items with
  | nil => simp [pairwiseCheck]
  | cons head tail ih =>
      simp [pairwiseCheck, ih, List.pairwise_cons]

/-- Executable counterpart of `KeySorted`. -/
def keySortedCheck {Alpha : Type} (key : Alpha → String)
    (items : List Alpha) : Bool :=
  pairwiseCheck (fun left right => decide (key left ≤ key right)) items

theorem keySortedCheck_true_iff {Alpha : Type} (key : Alpha → String)
    (items : List Alpha) :
    keySortedCheck key items = true ↔ KeySorted key items := by
  simp [keySortedCheck, pairwiseCheck_true_iff, KeySorted]

def RawCostSig.encodingCanonicalCheck (sig : RawCostSig) : Bool :=
  pairwiseCheck (fun left right => decide (left ≤ right)) sig

theorem RawCostSig.encodingCanonicalCheck_true_iff (sig : RawCostSig) :
    sig.encodingCanonicalCheck = true ↔ sig.EncodingCanonical := by
  simp [RawCostSig.encodingCanonicalCheck, pairwiseCheck_true_iff,
    RawCostSig.EncodingCanonical]

def RawCostStack.encodingCanonicalCheck (stack : RawCostStack) : Bool :=
  stack.all RawCostSig.encodingCanonicalCheck

mutual
  def RawCostName.encodingCanonicalCheck : RawCostName → Bool
    | .bvar _ => true
    | .quote term => term.encodingCanonicalCheck
    | .signature sig => sig.encodingCanonicalCheck

  def RawCostProc.encodingCanonicalCheck : RawCostProc → Bool
    | .nil => true
    | .par left right =>
        left.encodingCanonicalCheck && right.encodingCanonicalCheck
    | .send channel payload =>
        channel.encodingCanonicalCheck && payload.encodingCanonicalCheck
    | .recv channel body =>
        channel.encodingCanonicalCheck && body.encodingCanonicalCheck

  def RawCostTerm.encodingCanonicalCheck : RawCostTerm → Bool
    | .nil => true
    | .signed proc sig =>
        proc.encodingCanonicalCheck && sig.encodingCanonicalCheck
    | .par left right =>
        left.encodingCanonicalCheck && right.encodingCanonicalCheck
    | .drop name => name.encodingCanonicalCheck
    | .purse surface stack =>
        surface.encodingCanonicalCheck && stack.encodingCanonicalCheck
end

theorem RawCostStack.encodingCanonicalCheck_true_iff
    (stack : RawCostStack) :
    stack.encodingCanonicalCheck = true ↔ stack.EncodingCanonical := by
  rw [RawCostStack.EncodingCanonical, List.forall_iff_forall_mem]
  simp [RawCostStack.encodingCanonicalCheck,
    RawCostSig.encodingCanonicalCheck_true_iff]

mutual
  theorem RawCostName.encodingCanonicalCheck_true_iff :
      ∀ name : RawCostName,
        name.encodingCanonicalCheck = true ↔ name.EncodingCanonical
    | .bvar _ => by simp [RawCostName.encodingCanonicalCheck,
        RawCostName.EncodingCanonical]
    | .quote term => by
        simp [RawCostName.encodingCanonicalCheck,
          RawCostName.EncodingCanonical,
          RawCostTerm.encodingCanonicalCheck_true_iff term]
    | .signature sig => by
        simp [RawCostName.encodingCanonicalCheck,
          RawCostName.EncodingCanonical,
          RawCostSig.encodingCanonicalCheck_true_iff]

  theorem RawCostProc.encodingCanonicalCheck_true_iff :
      ∀ proc : RawCostProc,
        proc.encodingCanonicalCheck = true ↔ proc.EncodingCanonical
    | .nil => by simp [RawCostProc.encodingCanonicalCheck,
        RawCostProc.EncodingCanonical]
    | .par left right => by
        simp [RawCostProc.encodingCanonicalCheck,
          RawCostProc.EncodingCanonical,
          RawCostProc.encodingCanonicalCheck_true_iff left,
          RawCostProc.encodingCanonicalCheck_true_iff right]
    | .send channel payload => by
        simp [RawCostProc.encodingCanonicalCheck,
          RawCostProc.EncodingCanonical,
          RawCostName.encodingCanonicalCheck_true_iff channel,
          RawCostTerm.encodingCanonicalCheck_true_iff payload]
    | .recv channel body => by
        simp [RawCostProc.encodingCanonicalCheck,
          RawCostProc.EncodingCanonical,
          RawCostName.encodingCanonicalCheck_true_iff channel,
          RawCostTerm.encodingCanonicalCheck_true_iff body]

  theorem RawCostTerm.encodingCanonicalCheck_true_iff :
      ∀ term : RawCostTerm,
        term.encodingCanonicalCheck = true ↔ term.EncodingCanonical
    | .nil => by simp [RawCostTerm.encodingCanonicalCheck,
        RawCostTerm.EncodingCanonical]
    | .signed proc sig => by
        simp [RawCostTerm.encodingCanonicalCheck,
          RawCostTerm.EncodingCanonical,
          RawCostProc.encodingCanonicalCheck_true_iff proc,
          RawCostSig.encodingCanonicalCheck_true_iff]
    | .par left right => by
        simp [RawCostTerm.encodingCanonicalCheck,
          RawCostTerm.EncodingCanonical,
          RawCostTerm.encodingCanonicalCheck_true_iff left,
          RawCostTerm.encodingCanonicalCheck_true_iff right]
    | .drop name => by
        simp [RawCostTerm.encodingCanonicalCheck,
          RawCostTerm.EncodingCanonical,
          RawCostName.encodingCanonicalCheck_true_iff name]
    | .purse surface stack => by
        simp [RawCostTerm.encodingCanonicalCheck,
          RawCostTerm.EncodingCanonical,
          RawCostName.encodingCanonicalCheck_true_iff surface,
          RawCostStack.encodingCanonicalCheck_true_iff]
end

def RawCostTerm.normalizedCheck (term : RawCostTerm) : Bool :=
  term.normalize == term

theorem RawCostTerm.normalizedCheck_true_iff (term : RawCostTerm) :
    term.normalizedCheck = true ↔ term.Normalized := by
  simp [RawCostTerm.normalizedCheck, RawCostTerm.Normalized]

/-- Executable counterpart of the canonical runtime-configuration premise. -/
def RawCostConfig.canonicalCheck (config : RawCostConfig) : Bool :=
  config.all RawCostTerm.normalizedCheck &&
    keySortedCheck RawCostTerm.key config

theorem RawCostConfig.canonicalCheck_true_iff (config : RawCostConfig) :
    config.canonicalCheck = true ↔ config.Canonical := by
  constructor
  · intro checked
    simp only [RawCostConfig.canonicalCheck, Bool.and_eq_true] at checked
    have parts := checked
    refine ⟨?_, (keySortedCheck_true_iff RawCostTerm.key config).mp parts.2⟩
    rw [List.forall_iff_forall_mem]
    simpa [List.all_eq_true, RawCostTerm.normalizedCheck_true_iff]
      using parts.1
  · intro canonical
    simp only [RawCostConfig.canonicalCheck, Bool.and_eq_true]
    refine ⟨?_, (keySortedCheck_true_iff RawCostTerm.key config).mpr
      canonical.ordered⟩
    have components := canonical.components
    rw [List.forall_iff_forall_mem] at components
    simpa [List.all_eq_true, RawCostTerm.normalizedCheck_true_iff]
      using components

def RawCostConfig.encodingCanonicalCheck (config : RawCostConfig) : Bool :=
  config.all RawCostTerm.encodingCanonicalCheck

theorem RawCostConfig.encodingCanonicalCheck_true_iff
    (config : RawCostConfig) :
    config.encodingCanonicalCheck = true ↔
      config.Forall RawCostTerm.EncodingCanonical := by
  rw [List.forall_iff_forall_mem]
  simp [RawCostConfig.encodingCanonicalCheck, List.all_eq_true,
    RawCostTerm.encodingCanonicalCheck_true_iff]

/-- The three executable facts required at the differential theorem boundary. -/
structure RuntimePreconditionChecks where
  wellFormed : Bool
  canonical : Bool
  encodingCanonical : Bool
  deriving Repr, DecidableEq, Lean.ToJson, Lean.FromJson

def runtimePreconditionChecks (term : RawCostTerm) : RuntimePreconditionChecks :=
  { wellFormed := term.wellFormed
    canonical := term.normalizeConfig.canonicalCheck
    encodingCanonical := term.normalizeConfig.encodingCanonicalCheck }

theorem runtimePreconditionChecks_canonical (term : RawCostTerm) :
    (runtimePreconditionChecks term).canonical = true := by
  exact (RawCostConfig.canonicalCheck_true_iff term.normalizeConfig).mpr
    (RawCostTerm.normalizeConfig_canonical term)

theorem runtimePreconditionChecks_encodingCanonical (term : RawCostTerm) :
    (runtimePreconditionChecks term).encodingCanonical = true := by
  exact (RawCostConfig.encodingCanonicalCheck_true_iff
    term.normalizeConfig).mpr
      (RawCostTerm.normalizeConfig_forall_encodingCanonical term)

theorem runtimePreconditionChecks_all_true_iff (term : RawCostTerm) :
    let checks := runtimePreconditionChecks term
    checks.wellFormed = true ∧ checks.canonical = true ∧
      checks.encodingCanonical = true ↔ term.wellFormed = true := by
  simp only
  constructor
  · intro checked
    exact checked.1
  · intro supported
    exact ⟨supported, runtimePreconditionChecks_canonical term,
      runtimePreconditionChecks_encodingCanonical term⟩

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed
