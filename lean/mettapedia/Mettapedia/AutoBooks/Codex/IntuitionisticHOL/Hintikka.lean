import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.Soundness

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL

open Mettapedia.Logic.HOL

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

/-- Signed formulas for the future Hintikka and saturation machinery. -/
inductive Sign where
  | trueE
  | falseE
  deriving DecidableEq, Repr

def SignedFormula (Const : Ty Base → Type v) (Γ : Ctx Base) := Sign × Formula Const Γ

/-- Staging container for local Hintikka data. -/
structure HintikkaSet (Const : Ty Base → Type v) (Γ : Ctx Base) where
  formulas : List (SignedFormula Const Γ)

/-- Paper-facing placeholder for the branch that will feed completeness. -/
structure HintikkaGoal (Const : Ty Base → Type v) (Γ : Ctx Base) where
  antecedents : List (Formula Const Γ)
  succedent : Formula Const Γ

namespace Sign

/-- Switch the polarity of a signed formula. -/
def flip : Sign → Sign
  | .trueE => .falseE
  | .falseE => .trueE

@[simp] theorem flip_flip (s : Sign) : flip (flip s) = s := by
  cases s <;> rfl

end Sign

namespace SignedFormula

/-- Polarity reversal leaves the underlying formula unchanged. -/
def flip (sf : SignedFormula Const Γ) : SignedFormula Const Γ :=
  (Sign.flip sf.1, sf.2)

@[simp] theorem flip_flip (sf : SignedFormula Const Γ) : flip (flip sf) = sf := by
  cases sf
  simp [flip]

theorem flip_ne_self (sf : SignedFormula Const Γ) : flip sf ≠ sf := by
  cases sf with
  | mk s φ =>
      cases s <;> intro h <;> cases h

end SignedFormula

/-- World-free saturation steps for the local connective and quantifier closure
shape of future completeness arguments.

Implication and persistence need a world-indexed forcing layer and are therefore
left to the later stage where that layer is introduced explicitly. -/
inductive LocalSaturationStep (Const : Ty Base → Type v) (Γ : Ctx Base) where
  | trueAnd (φ ψ : Formula Const Γ)
  | falseAndLeft (φ ψ : Formula Const Γ)
  | falseAndRight (φ ψ : Formula Const Γ)
  | trueOrLeft (φ ψ : Formula Const Γ)
  | trueOrRight (φ ψ : Formula Const Γ)
  | falseOr (φ ψ : Formula Const Γ)
  | trueAll {σ : Ty Base} (φ : Formula Const (σ :: Γ)) (t : Term Const Γ σ)
  | falseAllWitness {σ : Ty Base} (φ : Formula Const (σ :: Γ)) (t : Term Const Γ σ)
  | trueExWitness {σ : Ty Base} (φ : Formula Const (σ :: Γ)) (t : Term Const Γ σ)
  | falseEx {σ : Ty Base} (φ : Formula Const (σ :: Γ)) (t : Term Const Γ σ)

namespace LocalSaturationStep

/-- The signed formula whose presence triggers a local saturation obligation. -/
def premise : LocalSaturationStep Const Γ → SignedFormula Const Γ
  | .trueAnd φ ψ => (Sign.trueE, .and φ ψ)
  | .falseAndLeft φ ψ => (Sign.falseE, .and φ ψ)
  | .falseAndRight φ ψ => (Sign.falseE, .and φ ψ)
  | .trueOrLeft φ ψ => (Sign.trueE, .or φ ψ)
  | .trueOrRight φ ψ => (Sign.trueE, .or φ ψ)
  | .falseOr φ ψ => (Sign.falseE, .or φ ψ)
  | .trueAll φ _ => (Sign.trueE, .all φ)
  | .falseAllWitness φ _ => (Sign.falseE, .all φ)
  | .trueExWitness φ _ => (Sign.trueE, .ex φ)
  | .falseEx φ _ => (Sign.falseE, .ex φ)

/-- The signed formulas added in the chosen local branch or witness step. -/
def additions : LocalSaturationStep Const Γ → List (SignedFormula Const Γ)
  | .trueAnd φ ψ => [(Sign.trueE, φ), (Sign.trueE, ψ)]
  | .falseAndLeft φ _ => [(Sign.falseE, φ)]
  | .falseAndRight _ ψ => [(Sign.falseE, ψ)]
  | .trueOrLeft φ _ => [(Sign.trueE, φ)]
  | .trueOrRight _ ψ => [(Sign.trueE, ψ)]
  | .falseOr φ ψ => [(Sign.falseE, φ), (Sign.falseE, ψ)]
  | .trueAll φ t => [(Sign.trueE, instantiate (Base := Base) t φ)]
  | .falseAllWitness φ t => [(Sign.falseE, instantiate (Base := Base) t φ)]
  | .trueExWitness φ t => [(Sign.trueE, instantiate (Base := Base) t φ)]
  | .falseEx φ t => [(Sign.falseE, instantiate (Base := Base) t φ)]

end LocalSaturationStep

/-- The deterministic world-free saturation clauses. Genuine branching choices
remain in `LocalBranchTarget`. -/
inductive DeterministicLocalSaturationStep
    (Const : Ty Base → Type v) (Γ : Ctx Base) where
  | trueAnd (φ ψ : Formula Const Γ)
  | falseOr (φ ψ : Formula Const Γ)
  | trueAll {σ : Ty Base} (φ : Formula Const (σ :: Γ)) (t : Term Const Γ σ)
  | falseAllWitness {σ : Ty Base} (φ : Formula Const (σ :: Γ)) (t : Term Const Γ σ)
  | trueExWitness {σ : Ty Base} (φ : Formula Const (σ :: Γ)) (t : Term Const Γ σ)
  | falseEx {σ : Ty Base} (φ : Formula Const (σ :: Γ)) (t : Term Const Γ σ)

namespace DeterministicLocalSaturationStep

/-- View a deterministic saturation clause as one of the general local
saturation steps. -/
def toLocalSaturationStep :
    DeterministicLocalSaturationStep Const Γ → LocalSaturationStep Const Γ
  | .trueAnd φ ψ => .trueAnd φ ψ
  | .falseOr φ ψ => .falseOr φ ψ
  | .trueAll φ t => .trueAll φ t
  | .falseAllWitness φ t => .falseAllWitness φ t
  | .trueExWitness φ t => .trueExWitness φ t
  | .falseEx φ t => .falseEx φ t

/-- The signed formula whose presence triggers a deterministic saturation
obligation. -/
def premise (s : DeterministicLocalSaturationStep Const Γ) : SignedFormula Const Γ :=
  LocalSaturationStep.premise s.toLocalSaturationStep

/-- The signed formulas added by a deterministic saturation clause. -/
def additions (s : DeterministicLocalSaturationStep Const Γ) :
    List (SignedFormula Const Γ) :=
  LocalSaturationStep.additions s.toLocalSaturationStep

theorem flip_not_mem_additions_of_mem
    {s : DeterministicLocalSaturationStep Const Γ}
    {sf : SignedFormula Const Γ}
    (h : sf ∈ additions s) :
    SignedFormula.flip sf ∉ additions s := by
  cases s with
  | trueAnd φ ψ =>
      simp [additions, toLocalSaturationStep, LocalSaturationStep.additions] at h ⊢
      rcases h with rfl | rfl <;> constructor <;> intro hflip <;> cases hflip
  | falseOr φ ψ =>
      simp [additions, toLocalSaturationStep, LocalSaturationStep.additions] at h ⊢
      rcases h with rfl | rfl <;> constructor <;> intro hflip <;> cases hflip
  | trueAll φ t =>
      simp [additions, toLocalSaturationStep, LocalSaturationStep.additions] at h ⊢
      rcases h with rfl
      intro hflip
      cases hflip
  | falseAllWitness φ t =>
      simp [additions, toLocalSaturationStep, LocalSaturationStep.additions] at h ⊢
      rcases h with rfl
      intro hflip
      cases hflip
  | trueExWitness φ t =>
      simp [additions, toLocalSaturationStep, LocalSaturationStep.additions] at h ⊢
      rcases h with rfl
      intro hflip
      cases hflip
  | falseEx φ t =>
      simp [additions, toLocalSaturationStep, LocalSaturationStep.additions] at h ⊢
      rcases h with rfl
      intro hflip
      cases hflip

end DeterministicLocalSaturationStep

/-! Local branching obligations package the unresolved connective-level work
whose eventual resolution will choose one of several local saturation steps. -/
inductive LocalBranchTarget (Const : Ty Base → Type v) (Γ : Ctx Base) where
  | falseAnd (φ ψ : Formula Const Γ)
  | trueOr (φ ψ : Formula Const Γ)

namespace LocalBranchTarget

/-- The signed formula whose presence spawns this local branching obligation. -/
def premise : LocalBranchTarget Const Γ → SignedFormula Const Γ
  | .falseAnd φ ψ => (Sign.falseE, .and φ ψ)
  | .trueOr φ ψ => (Sign.trueE, .or φ ψ)

/-- The possible local saturation-step resolutions of a branching obligation. -/
def branches : LocalBranchTarget Const Γ → List (LocalSaturationStep Const Γ)
  | .falseAnd φ ψ => [.falseAndLeft φ ψ, .falseAndRight φ ψ]
  | .trueOr φ ψ => [.trueOrLeft φ ψ, .trueOrRight φ ψ]

/-- A local saturation step is admissible for a branching obligation when it is
one of that target's listed branch resolutions. -/
def AcceptsStep (b : LocalBranchTarget Const Γ) (s : LocalSaturationStep Const Γ) : Prop :=
  s ∈ b.branches

theorem premise_eq_of_acceptsStep {b : LocalBranchTarget Const Γ}
    {s : LocalSaturationStep Const Γ}
    (h : b.AcceptsStep s) :
    LocalSaturationStep.premise s = b.premise := by
  cases b <;> cases s <;> simp [AcceptsStep, branches, premise] at h ⊢
  all_goals
    rcases h with ⟨rfl, rfl⟩
    rfl

/-- Extract the connective-level branching obligations suggested by a signed formula. -/
def ofSignedFormula : SignedFormula Const Γ → List (LocalBranchTarget Const Γ)
  | (Sign.falseE, .and φ ψ) => [.falseAnd φ ψ]
  | (Sign.trueE, .or φ ψ) => [.trueOr φ ψ]
  | _ => []

/-- Any branch target emitted from a signed formula keeps that formula as its premise. -/
theorem premise_eq_of_mem_ofSignedFormula {sf : SignedFormula Const Γ}
    {b : LocalBranchTarget Const Γ}
    (h : b ∈ ofSignedFormula sf) :
    b.premise = sf := by
  cases sf with
  | mk s φ =>
      cases s <;> cases φ <;> cases b <;> simp [ofSignedFormula, premise] at h ⊢
      all_goals
        rcases h with ⟨rfl, rfl⟩
        rfl

/-- Any branch target collected from a list of signed formulas points back to one
of the formulas in that list. -/
theorem premise_mem_of_mem_targetsFrom {Δ : List (SignedFormula Const Γ)}
    {b : LocalBranchTarget Const Γ}
    (h : b ∈ Δ.foldr (fun sf acc => ofSignedFormula sf ++ acc) []) :
    b.premise ∈ Δ := by
  induction Δ with
  | nil =>
      simp at h
  | cons sf tl ih =>
      have h' : b ∈ ofSignedFormula sf ++ tl.foldr (fun sf acc => ofSignedFormula sf ++ acc) [] := by
        simpa [List.foldr] using h
      rcases List.mem_append.mp h' with h | h
      · simp [premise_eq_of_mem_ofSignedFormula h]
      · right
        exact ih h

end LocalBranchTarget

namespace HintikkaSet

/-- Add a list of signed formulas to a Hintikka set's staging list. -/
def insertAll (H : HintikkaSet Const Γ) (Δ : List (SignedFormula Const Γ)) :
    HintikkaSet Const Γ :=
  { formulas := Δ ++ H.formulas }

/-- Extend a Hintikka set by the formulas prescribed by a local saturation step. -/
def saturateWithStep (H : HintikkaSet Const Γ) (s : LocalSaturationStep Const Γ) :
    HintikkaSet Const Γ :=
  H.insertAll (LocalSaturationStep.additions s)

/-- Close a world-free Hintikka set by adjoining the always-required `T ⊤` and
`F ⊥` formulas. This matches the paper's remark that any Hintikka set is
contained in a closed one obtained by adding these formulas. -/
def close (H : HintikkaSet Const Γ) : HintikkaSet Const Γ :=
  { formulas :=
      (Sign.trueE, (.top : Formula Const Γ)) ::
      (Sign.falseE, (.bot : Formula Const Γ)) ::
      H.formulas }

/-- The local branching obligations currently visible in a staged Hintikka set. -/
def localBranchTargets (H : HintikkaSet Const Γ) : List (LocalBranchTarget Const Γ) :=
  H.formulas.foldr (fun sf acc => LocalBranchTarget.ofSignedFormula sf ++ acc) []

/-- Every visible local branching obligation in a staged Hintikka set arises
from a formula already present in that set. -/
theorem premise_mem_of_mem_localBranchTargets {H : HintikkaSet Const Γ}
    {b : LocalBranchTarget Const Γ}
    (h : b ∈ H.localBranchTargets) :
    b.premise ∈ H.formulas := by
  exact LocalBranchTarget.premise_mem_of_mem_targetsFrom h

@[simp] theorem mem_insertAll_left {H : HintikkaSet Const Γ}
    {Δ : List (SignedFormula Const Γ)} {sf : SignedFormula Const Γ}
    (h : sf ∈ Δ) :
    sf ∈ (H.insertAll Δ).formulas := by
  exact List.mem_append.mpr <| Or.inl h

@[simp] theorem mem_insertAll_right {H : HintikkaSet Const Γ}
    {Δ : List (SignedFormula Const Γ)} {sf : SignedFormula Const Γ}
    (h : sf ∈ H.formulas) :
    sf ∈ (H.insertAll Δ).formulas := by
  exact List.mem_append.mpr <| Or.inr h

@[simp] theorem mem_saturateWithStep_of_mem {H : HintikkaSet Const Γ}
    {s : LocalSaturationStep Const Γ} {sf : SignedFormula Const Γ}
    (h : sf ∈ H.formulas) :
    sf ∈ (H.saturateWithStep s).formulas :=
  mem_insertAll_right h

@[simp] theorem mem_saturateWithStep_of_addition {H : HintikkaSet Const Γ}
    {s : LocalSaturationStep Const Γ} {sf : SignedFormula Const Γ}
    (h : sf ∈ LocalSaturationStep.additions s) :
    sf ∈ (H.saturateWithStep s).formulas :=
  mem_insertAll_left h

@[simp] theorem mem_close_of_mem {H : HintikkaSet Const Γ}
    {sf : SignedFormula Const Γ}
    (h : sf ∈ H.formulas) :
    sf ∈ H.close.formulas := by
  simp [close, h]

@[simp] theorem trueTop_mem_close (H : HintikkaSet Const Γ) :
    (Sign.trueE, (.top : Formula Const Γ)) ∈ H.close.formulas := by
  unfold close
  exact List.mem_cons_self

@[simp] theorem falseBot_mem_close (H : HintikkaSet Const Γ) :
    (Sign.falseE, (.bot : Formula Const Γ)) ∈ H.close.formulas := by
  unfold close
  exact List.mem_cons_of_mem _ List.mem_cons_self

theorem mem_close_insertAll_singleton_iff {H : HintikkaSet Const Γ}
    {added sf : SignedFormula Const Γ} :
    sf ∈ (H.insertAll [added]).close.formulas ↔
      sf = added ∨ sf ∈ H.close.formulas := by
  simp [close, insertAll, or_assoc, or_comm]

theorem mem_close_insertAll_iff {H : HintikkaSet Const Γ}
    {Δ : List (SignedFormula Const Γ)} {sf : SignedFormula Const Γ} :
    sf ∈ (H.insertAll Δ).close.formulas ↔
      sf ∈ Δ ∨ sf ∈ H.close.formulas := by
  simp [close, insertAll, or_assoc, or_comm]

theorem premise_mem_of_mem_close {H : HintikkaSet Const Γ}
    {s : LocalSaturationStep Const Γ}
    (h : LocalSaturationStep.premise s ∈ H.close.formulas) :
    LocalSaturationStep.premise s ∈ H.formulas := by
  cases s <;> simp [close, LocalSaturationStep.premise] at h ⊢
  all_goals
    rcases h with h | h
    · cases h
    · rcases h with h | h
      · cases h
      · exact h

/-- A Hintikka set supports a local saturation step when it contains all formulas
required by that branch or witness once the triggering premise is present. -/
def SupportsLocalStep (H : HintikkaSet Const Γ)
    (s : DeterministicLocalSaturationStep Const Γ) : Prop :=
  DeterministicLocalSaturationStep.premise s ∈ H.formulas →
    ∀ sf ∈ DeterministicLocalSaturationStep.additions s, sf ∈ H.formulas

/-- A Hintikka set supports a branching target when at least one admissible
local resolution step is already supported whenever the target premise is
present. -/
def SupportsBranchTarget (H : HintikkaSet Const Γ) (b : LocalBranchTarget Const Γ) : Prop :=
  ∃ s : LocalSaturationStep Const Γ, b.AcceptsStep s ∧
    (LocalSaturationStep.premise s ∈ H.formulas →
      ∀ sf ∈ LocalSaturationStep.additions s, sf ∈ H.formulas)

/-- World-free branching closure saying that every local branching obligation
admits some supported local resolution. -/
def BranchClosed (H : HintikkaSet Const Γ) : Prop :=
  ∀ b : LocalBranchTarget Const Γ, H.SupportsBranchTarget b

/-- World-free contradiction for the current signed Hintikka staging layer. -/
def Contradictory (H : HintikkaSet Const Γ) : Prop :=
  (∃ φ : Formula Const Γ,
      (Sign.trueE, φ) ∈ H.formulas ∧ (Sign.falseE, φ) ∈ H.formulas) ∨
    (Sign.trueE, (.bot : Formula Const Γ)) ∈ H.formulas ∨
    (Sign.falseE, (.top : Formula Const Γ)) ∈ H.formulas

/-- World-free non-contradiction for the current signed Hintikka staging layer. -/
def Noncontradictory (H : HintikkaSet Const Γ) : Prop :=
  ¬ H.Contradictory

/-- The minimal closure clause from the paper forcing truth of `⊤` and falsity
of `⊥` in the current world-free signed staging layer. -/
def Closed (H : HintikkaSet Const Γ) : Prop :=
  (Sign.trueE, (.top : Formula Const Γ)) ∈ H.formulas ∧
    (Sign.falseE, (.bot : Formula Const Γ)) ∈ H.formulas

/-- The unsigned formulas currently staged as true in the local world-free
Hintikka layer. -/
def trueFormulas (H : HintikkaSet Const Γ) : List (Formula Const Γ) :=
  H.formulas.filterMap fun
    | (Sign.trueE, φ) => some φ
    | (Sign.falseE, _) => none

/-- The unsigned formulas currently staged as false in the local world-free
Hintikka layer. -/
def falseFormulas (H : HintikkaSet Const Γ) : List (Formula Const Γ) :=
  H.formulas.filterMap fun
    | (Sign.falseE, φ) => some φ
    | (Sign.trueE, _) => none

/-- Local one-world analogue of Definition 5.5 from the paper: every staged
false formula avoids derivability from the staged true formulas. -/
def ICTTConsistent (H : HintikkaSet Const Γ) : Prop :=
  ∀ {φ : Formula Const Γ},
    φ ∈ H.falseFormulas →
      ¬ Derivable (Base := Base) (Const := Const) H.trueFormulas φ

/-- The world-free fragment of saturation closure used before introducing a
world-indexed forcing layer for implication and persistence. -/
def LocallySaturated (H : HintikkaSet Const Γ) : Prop :=
  ∀ s : DeterministicLocalSaturationStep Const Γ, H.SupportsLocalStep s

theorem mem_of_localStep {H : HintikkaSet Const Γ}
    (hH : H.LocallySaturated) (s : DeterministicLocalSaturationStep Const Γ)
    (hprem : DeterministicLocalSaturationStep.premise s ∈ H.formulas)
    {sf : SignedFormula Const Γ}
    (hsf : sf ∈ DeterministicLocalSaturationStep.additions s) :
    sf ∈ H.formulas :=
  hH s hprem sf hsf

theorem exists_resolvingStep_of_supportsBranchTarget {H : HintikkaSet Const Γ}
    {b : LocalBranchTarget Const Γ}
    (hH : H.SupportsBranchTarget b)
    (hprem : b.premise ∈ H.formulas) :
    ∃ s : LocalSaturationStep Const Γ,
      b.AcceptsStep s ∧
      ∀ sf ∈ LocalSaturationStep.additions s, sf ∈ H.formulas := by
  rcases hH with ⟨s, hs, hsupp⟩
  have hsPrem : LocalSaturationStep.premise s ∈ H.formulas := by
    simpa [LocalBranchTarget.premise_eq_of_acceptsStep hs] using hprem
  exact ⟨s, hs, hsupp hsPrem⟩

theorem exists_resolvingStep_of_branchClosed {H : HintikkaSet Const Γ}
    (hH : H.BranchClosed)
    {b : LocalBranchTarget Const Γ}
    (hprem : b.premise ∈ H.formulas) :
    ∃ s : LocalSaturationStep Const Γ,
      b.AcceptsStep s ∧
      ∀ sf ∈ LocalSaturationStep.additions s, sf ∈ H.formulas :=
  exists_resolvingStep_of_supportsBranchTarget (hH b) hprem

theorem exists_resolvingStep_of_mem_localBranchTargets {H : HintikkaSet Const Γ}
    (hH : H.BranchClosed)
    {b : LocalBranchTarget Const Γ}
    (hb : b ∈ H.localBranchTargets) :
    ∃ s : LocalSaturationStep Const Γ,
      b.AcceptsStep s ∧
      ∀ sf ∈ LocalSaturationStep.additions s, sf ∈ H.formulas :=
  exists_resolvingStep_of_branchClosed hH
    (premise_mem_of_mem_localBranchTargets hb)

theorem trueAnd_mem_of_locallySaturated {H : HintikkaSet Const Γ}
    (hH : H.LocallySaturated)
    {φ ψ : Formula Const Γ}
    (h : (Sign.trueE, .and φ ψ) ∈ H.formulas) :
    (Sign.trueE, φ) ∈ H.formulas ∧ (Sign.trueE, ψ) ∈ H.formulas := by
  have hsupp := hH (.trueAnd φ ψ)
  have hprem : DeterministicLocalSaturationStep.premise (.trueAnd φ ψ) ∈ H.formulas := by
    change (Sign.trueE, .and φ ψ) ∈ H.formulas
    exact h
  constructor
  · exact hsupp hprem _ (by
      simp [DeterministicLocalSaturationStep.additions,
        DeterministicLocalSaturationStep.toLocalSaturationStep, LocalSaturationStep.additions])
  · exact hsupp hprem _ (by
      simp [DeterministicLocalSaturationStep.additions,
        DeterministicLocalSaturationStep.toLocalSaturationStep, LocalSaturationStep.additions])

theorem falseAnd_mem_of_branchClosed {H : HintikkaSet Const Γ}
    (hH : H.BranchClosed)
    {φ ψ : Formula Const Γ}
    (h : (Sign.falseE, .and φ ψ) ∈ H.formulas) :
    (Sign.falseE, φ) ∈ H.formulas ∨ (Sign.falseE, ψ) ∈ H.formulas := by
  rcases exists_resolvingStep_of_branchClosed hH
      (b := .falseAnd φ ψ) (by
        change (Sign.falseE, .and φ ψ) ∈ H.formulas
        exact h) with
    ⟨s, hs, hsupp⟩
  have hs' : s = .falseAndLeft φ ψ ∨ s = .falseAndRight φ ψ := by
    simpa [LocalBranchTarget.AcceptsStep, LocalBranchTarget.branches] using hs
  rcases hs' with rfl | rfl
  · left
    exact hsupp _ (by simp [LocalSaturationStep.additions])
  · right
    exact hsupp _ (by simp [LocalSaturationStep.additions])

theorem trueOr_mem_of_branchClosed {H : HintikkaSet Const Γ}
    (hH : H.BranchClosed)
    {φ ψ : Formula Const Γ}
    (h : (Sign.trueE, .or φ ψ) ∈ H.formulas) :
    (Sign.trueE, φ) ∈ H.formulas ∨ (Sign.trueE, ψ) ∈ H.formulas := by
  rcases exists_resolvingStep_of_branchClosed hH
      (b := .trueOr φ ψ) (by
        change (Sign.trueE, .or φ ψ) ∈ H.formulas
        exact h) with
    ⟨s, hs, hsupp⟩
  have hs' : s = .trueOrLeft φ ψ ∨ s = .trueOrRight φ ψ := by
    simpa [LocalBranchTarget.AcceptsStep, LocalBranchTarget.branches] using hs
  rcases hs' with rfl | rfl
  · left
    exact hsupp _ (by simp [LocalSaturationStep.additions])
  · right
    exact hsupp _ (by simp [LocalSaturationStep.additions])

theorem falseOr_mem_of_locallySaturated {H : HintikkaSet Const Γ}
    (hH : H.LocallySaturated)
    {φ ψ : Formula Const Γ}
    (h : (Sign.falseE, .or φ ψ) ∈ H.formulas) :
    (Sign.falseE, φ) ∈ H.formulas ∧ (Sign.falseE, ψ) ∈ H.formulas := by
  have hsupp := hH (.falseOr φ ψ)
  have hprem : DeterministicLocalSaturationStep.premise (.falseOr φ ψ) ∈ H.formulas := by
    change (Sign.falseE, .or φ ψ) ∈ H.formulas
    exact h
  constructor
  · exact hsupp hprem _ (by
      simp [DeterministicLocalSaturationStep.additions,
        DeterministicLocalSaturationStep.toLocalSaturationStep, LocalSaturationStep.additions])
  · exact hsupp hprem _ (by
      simp [DeterministicLocalSaturationStep.additions,
        DeterministicLocalSaturationStep.toLocalSaturationStep, LocalSaturationStep.additions])

theorem trueAll_mem_of_locallySaturated {H : HintikkaSet Const Γ}
    (hH : H.LocallySaturated)
    {σ : Ty Base} {φ : Formula Const (σ :: Γ)}
    (h : (Sign.trueE, .all φ) ∈ H.formulas)
    (t : Term Const Γ σ) :
    (Sign.trueE, instantiate (Base := Base) t φ) ∈ H.formulas := by
  have hprem : DeterministicLocalSaturationStep.premise (.trueAll φ t) ∈ H.formulas := by
    change (Sign.trueE, .all φ) ∈ H.formulas
    exact h
  exact hH (.trueAll φ t)
    hprem
    _ (by
      simp [DeterministicLocalSaturationStep.additions,
        DeterministicLocalSaturationStep.toLocalSaturationStep, LocalSaturationStep.additions])

theorem falseAll_mem_of_locallySaturated {H : HintikkaSet Const Γ}
    (hH : H.LocallySaturated)
    {σ : Ty Base} {φ : Formula Const (σ :: Γ)}
    (h : (Sign.falseE, .all φ) ∈ H.formulas)
    (t : Term Const Γ σ) :
    (Sign.falseE, instantiate (Base := Base) t φ) ∈ H.formulas := by
  have hprem : DeterministicLocalSaturationStep.premise (.falseAllWitness φ t) ∈ H.formulas := by
    change (Sign.falseE, .all φ) ∈ H.formulas
    exact h
  exact hH (.falseAllWitness φ t)
    hprem
    _ (by
      simp [DeterministicLocalSaturationStep.additions,
        DeterministicLocalSaturationStep.toLocalSaturationStep, LocalSaturationStep.additions])

theorem trueEx_mem_of_locallySaturated {H : HintikkaSet Const Γ}
    (hH : H.LocallySaturated)
    {σ : Ty Base} {φ : Formula Const (σ :: Γ)}
    (h : (Sign.trueE, .ex φ) ∈ H.formulas)
    (t : Term Const Γ σ) :
    (Sign.trueE, instantiate (Base := Base) t φ) ∈ H.formulas := by
  have hprem : DeterministicLocalSaturationStep.premise (.trueExWitness φ t) ∈ H.formulas := by
    change (Sign.trueE, .ex φ) ∈ H.formulas
    exact h
  exact hH (.trueExWitness φ t)
    hprem
    _ (by
      simp [DeterministicLocalSaturationStep.additions,
        DeterministicLocalSaturationStep.toLocalSaturationStep, LocalSaturationStep.additions])

theorem falseEx_mem_of_locallySaturated {H : HintikkaSet Const Γ}
    (hH : H.LocallySaturated)
    {σ : Ty Base} {φ : Formula Const (σ :: Γ)}
    (h : (Sign.falseE, .ex φ) ∈ H.formulas)
    (t : Term Const Γ σ) :
    (Sign.falseE, instantiate (Base := Base) t φ) ∈ H.formulas := by
  have hprem : DeterministicLocalSaturationStep.premise (.falseEx φ t) ∈ H.formulas := by
    change (Sign.falseE, .ex φ) ∈ H.formulas
    exact h
  exact hH (.falseEx φ t)
    hprem
    _ (by
      simp [DeterministicLocalSaturationStep.additions,
        DeterministicLocalSaturationStep.toLocalSaturationStep, LocalSaturationStep.additions])

theorem contradictory_of_conflict {H : HintikkaSet Const Γ}
    {φ : Formula Const Γ}
    (hTrue : (Sign.trueE, φ) ∈ H.formulas)
    (hFalse : (Sign.falseE, φ) ∈ H.formulas) :
    H.Contradictory :=
  Or.inl ⟨φ, hTrue, hFalse⟩

theorem contradictory_of_trueBot {H : HintikkaSet Const Γ}
    (h : (Sign.trueE, (.bot : Formula Const Γ)) ∈ H.formulas) :
    H.Contradictory :=
  Or.inr <| Or.inl h

theorem contradictory_of_falseTop {H : HintikkaSet Const Γ}
    (h : (Sign.falseE, (.top : Formula Const Γ)) ∈ H.formulas) :
    H.Contradictory :=
  Or.inr <| Or.inr h

theorem true_mem_trueFormulas {H : HintikkaSet Const Γ}
    {φ : Formula Const Γ}
    (h : (Sign.trueE, φ) ∈ H.formulas) :
    φ ∈ H.trueFormulas := by
  unfold trueFormulas
  exact List.mem_filterMap.mpr ⟨(Sign.trueE, φ), h, rfl⟩

theorem false_mem_falseFormulas {H : HintikkaSet Const Γ}
    {φ : Formula Const Γ}
    (h : (Sign.falseE, φ) ∈ H.formulas) :
    φ ∈ H.falseFormulas := by
  unfold falseFormulas
  exact List.mem_filterMap.mpr ⟨(Sign.falseE, φ), h, rfl⟩

theorem derivable_of_true_mem {H : HintikkaSet Const Γ}
    {φ : Formula Const Γ}
    (h : (Sign.trueE, φ) ∈ H.formulas) :
    Derivable (Base := Base) (Const := Const) H.trueFormulas φ :=
  Derivable.ax (true_mem_trueFormulas h)

theorem not_derivable_of_false_mem_of_icttConsistent {H : HintikkaSet Const Γ}
    (hH : H.ICTTConsistent)
    {φ : Formula Const Γ}
    (h : (Sign.falseE, φ) ∈ H.formulas) :
    ¬ Derivable (Base := Base) (Const := Const) H.trueFormulas φ :=
  hH (false_mem_falseFormulas h)

theorem trueTop_mem_of_closed {H : HintikkaSet Const Γ}
    (hH : H.Closed) :
    (Sign.trueE, (.top : Formula Const Γ)) ∈ H.formulas :=
  hH.1

theorem falseBot_mem_of_closed {H : HintikkaSet Const Γ}
    (hH : H.Closed) :
    (Sign.falseE, (.bot : Formula Const Γ)) ∈ H.formulas :=
  hH.2

theorem closed_close (H : HintikkaSet Const Γ) :
    H.close.Closed := by
  constructor
  · exact trueTop_mem_close H
  · exact falseBot_mem_close H

theorem false_not_mem_of_true_mem_of_noncontradictory {H : HintikkaSet Const Γ}
    (hH : H.Noncontradictory)
    {φ : Formula Const Γ}
    (hTrue : (Sign.trueE, φ) ∈ H.formulas) :
    (Sign.falseE, φ) ∉ H.formulas := by
  intro hFalse
  exact hH (contradictory_of_conflict hTrue hFalse)

theorem true_not_mem_of_false_mem_of_noncontradictory {H : HintikkaSet Const Γ}
    (hH : H.Noncontradictory)
    {φ : Formula Const Γ}
    (hFalse : (Sign.falseE, φ) ∈ H.formulas) :
    (Sign.trueE, φ) ∉ H.formulas := by
  intro hTrue
  exact hH (contradictory_of_conflict hTrue hFalse)

theorem trueBot_not_mem_of_noncontradictory {H : HintikkaSet Const Γ}
    (hH : H.Noncontradictory) :
    (Sign.trueE, (.bot : Formula Const Γ)) ∉ H.formulas := by
  intro hBot
  exact hH (contradictory_of_trueBot hBot)

theorem falseTop_not_mem_of_noncontradictory {H : HintikkaSet Const Γ}
    (hH : H.Noncontradictory) :
    (Sign.falseE, (.top : Formula Const Γ)) ∉ H.formulas := by
  intro hTop
  exact hH (contradictory_of_falseTop hTop)

theorem noncontradictory_close_insertAll_singleton_of_flip_not_mem
    {H : HintikkaSet Const Γ}
    (hH : H.close.Noncontradictory)
    {sf : SignedFormula Const Γ}
    (hFlip : SignedFormula.flip sf ∉ H.close.formulas) :
    (H.insertAll [sf]).close.Noncontradictory := by
  intro hContra
  rcases hContra with hConflict | hContra
  · rcases hConflict with ⟨φ, hTrue, hFalse⟩
    by_cases hTrueEq : (Sign.trueE, φ) = sf
    · have hFlipNew : SignedFormula.flip sf ∈ (H.insertAll [sf]).close.formulas := by
        cases hTrueEq
        change (Sign.falseE, φ) ∈ (H.insertAll [(Sign.trueE, φ)]).close.formulas
        exact hFalse
      rcases (mem_close_insertAll_singleton_iff.mp hFlipNew) with hEq | hOld
      · exact SignedFormula.flip_ne_self sf hEq
      · exact hFlip hOld
    · by_cases hFalseEq : (Sign.falseE, φ) = sf
      · have hFlipNew : SignedFormula.flip sf ∈ (H.insertAll [sf]).close.formulas := by
          cases hFalseEq
          change (Sign.trueE, φ) ∈ (H.insertAll [(Sign.falseE, φ)]).close.formulas
          exact hTrue
        rcases (mem_close_insertAll_singleton_iff.mp hFlipNew) with hEq | hOld
        · exact SignedFormula.flip_ne_self sf hEq
        · exact hFlip hOld
      · have hTrueOld : (Sign.trueE, φ) ∈ H.close.formulas := by
          rcases (mem_close_insertAll_singleton_iff.mp hTrue) with hEq | hOld
          · exact False.elim (hTrueEq hEq)
          · exact hOld
        have hFalseOld : (Sign.falseE, φ) ∈ H.close.formulas := by
          rcases (mem_close_insertAll_singleton_iff.mp hFalse) with hEq | hOld
          · exact False.elim (hFalseEq hEq)
          · exact hOld
        exact hH (contradictory_of_conflict hTrueOld hFalseOld)
  · rcases hContra with hTrueBot | hFalseTop
    · rcases (mem_close_insertAll_singleton_iff.mp hTrueBot) with hEq | hOld
      · have hFlipOld : SignedFormula.flip sf ∈ H.close.formulas := by
          cases hEq
          change (Sign.falseE, (.bot : Formula Const Γ)) ∈ H.close.formulas
          exact falseBot_mem_close H
        exact hFlip hFlipOld
      · exact hH (contradictory_of_trueBot hOld)
    · rcases (mem_close_insertAll_singleton_iff.mp hFalseTop) with hEq | hOld
      · have hFlipOld : SignedFormula.flip sf ∈ H.close.formulas := by
          cases hEq
          change (Sign.trueE, (.top : Formula Const Γ)) ∈ H.close.formulas
          exact trueTop_mem_close H
        exact hFlip hFlipOld
      · exact hH (contradictory_of_falseTop hOld)

theorem noncontradictory_close_insertAll_of_flip_not_mem
    {H : HintikkaSet Const Γ} {Δ : List (SignedFormula Const Γ)}
    (hH : H.close.Noncontradictory)
    (hCompat :
      ∀ {sf : SignedFormula Const Γ},
        sf ∈ Δ → SignedFormula.flip sf ∉ H.close.formulas)
    (hInternal :
      ∀ {sf : SignedFormula Const Γ},
        sf ∈ Δ → SignedFormula.flip sf ∉ Δ) :
    (H.insertAll Δ).close.Noncontradictory := by
  intro hContra
  rcases hContra with hConflict | hContra
  · rcases hConflict with ⟨φ, hTrue, hFalse⟩
    rcases mem_close_insertAll_iff.mp hTrue with hTrueNew | hTrueOld
    · rcases mem_close_insertAll_iff.mp hFalse with hFalseNew | hFalseOld
      · exact (hInternal hTrueNew) (by simpa [SignedFormula.flip, Sign.flip] using hFalseNew)
      · exact (hCompat hTrueNew) (by simpa [SignedFormula.flip, Sign.flip] using hFalseOld)
    · rcases mem_close_insertAll_iff.mp hFalse with hFalseNew | hFalseOld
      · exact (hCompat hFalseNew) (by simpa [SignedFormula.flip, Sign.flip] using hTrueOld)
      · exact hH (contradictory_of_conflict hTrueOld hFalseOld)
  · rcases hContra with hTrueBot | hFalseTop
    · rcases mem_close_insertAll_iff.mp hTrueBot with hTrueBotNew | hTrueBotOld
      · exact (hCompat hTrueBotNew) (by
          change (Sign.falseE, (.bot : Formula Const Γ)) ∈ H.close.formulas
          exact falseBot_mem_close H)
      · exact hH (contradictory_of_trueBot hTrueBotOld)
    · rcases mem_close_insertAll_iff.mp hFalseTop with hFalseTopNew | hFalseTopOld
      · exact (hCompat hFalseTopNew) (by
          change (Sign.trueE, (.top : Formula Const Γ)) ∈ H.close.formulas
          exact trueTop_mem_close H)
      · exact hH (contradictory_of_falseTop hFalseTopOld)

theorem noncontradictory_of_closed_icttConsistent {H : HintikkaSet Const Γ}
    (hClosed : H.Closed)
    (hCons : H.ICTTConsistent) :
    H.Noncontradictory := by
  intro hContra
  rcases hContra with hConflict | hContra
  · rcases hConflict with ⟨φ, hTrue, hFalse⟩
    exact (not_derivable_of_false_mem_of_icttConsistent hCons hFalse)
      (derivable_of_true_mem hTrue)
  · rcases hContra with hTrueBot | hFalseTop
    · exact (not_derivable_of_false_mem_of_icttConsistent hCons
        (falseBot_mem_of_closed hClosed))
        (derivable_of_true_mem hTrueBot)
    · exact (not_derivable_of_false_mem_of_icttConsistent hCons hFalseTop)
        Derivable.topR

theorem locallySaturated_close {H : HintikkaSet Const Γ}
    (hH : H.LocallySaturated) :
    H.close.LocallySaturated := by
  intro s hprem sf hsf
  exact mem_close_of_mem <|
    hH s (by
      simpa [DeterministicLocalSaturationStep.premise] using
        (premise_mem_of_mem_close (s := s.toLocalSaturationStep) hprem))
      sf (by simpa [DeterministicLocalSaturationStep.additions] using hsf)

theorem supportsBranchTarget_close {H : HintikkaSet Const Γ}
    {b : LocalBranchTarget Const Γ}
    (hH : H.SupportsBranchTarget b) :
    H.close.SupportsBranchTarget b := by
  rcases hH with ⟨s, hs, hsupp⟩
  refine ⟨s, hs, ?_⟩
  intro hprem sf hsf
  have hprem' : LocalSaturationStep.premise s ∈ H.close.formulas := by
    simpa [LocalBranchTarget.premise_eq_of_acceptsStep hs] using hprem
  have hprem'' : LocalSaturationStep.premise s ∈ H.formulas := by
    exact premise_mem_of_mem_close (s := s) hprem'
  exact mem_close_of_mem <|
    hsupp hprem'' sf hsf

theorem branchClosed_close {H : HintikkaSet Const Γ}
    (hH : H.BranchClosed) :
    H.close.BranchClosed := by
  intro b
  exact supportsBranchTarget_close (hH b)

end HintikkaSet

namespace HintikkaGoal

/-- Initial signed frontier attached to a sequent goal. -/
def signedFormulas (g : HintikkaGoal Const Γ) : List (SignedFormula Const Γ) :=
  g.antecedents.map (fun φ => (Sign.trueE, φ)) ++ [(Sign.falseE, g.succedent)]

/-- Initial Hintikka set obtained from a goal sequent. -/
def toHintikkaSet (g : HintikkaGoal Const Γ) : HintikkaSet Const Γ :=
  { formulas := g.signedFormulas }

theorem true_mem_signedFormulas {g : HintikkaGoal Const Γ} {φ : Formula Const Γ}
    (h : φ ∈ g.antecedents) :
    (Sign.trueE, φ) ∈ g.signedFormulas := by
  apply List.mem_append.mpr
  left
  exact List.mem_map.mpr ⟨φ, h, rfl⟩

theorem false_mem_signedFormulas (g : HintikkaGoal Const Γ) :
    (Sign.falseE, g.succedent) ∈ g.signedFormulas := by
  apply List.mem_append.mpr
  right
  simp

theorem true_mem_toHintikkaSet {g : HintikkaGoal Const Γ} {φ : Formula Const Γ}
    (h : φ ∈ g.antecedents) :
    (Sign.trueE, φ) ∈ g.toHintikkaSet.formulas :=
  true_mem_signedFormulas h

theorem false_mem_toHintikkaSet (g : HintikkaGoal Const Γ) :
    (Sign.falseE, g.succedent) ∈ g.toHintikkaSet.formulas :=
  false_mem_signedFormulas g

@[simp] theorem trueFormulas_toHintikkaSet (g : HintikkaGoal Const Γ) :
    g.toHintikkaSet.trueFormulas = g.antecedents := by
  cases g with
  | mk antecedents succedent =>
      induction antecedents with
      | nil =>
          rfl
      | cons φ Δ ih =>
          have htail :
              ({ antecedents := Δ, succedent := succedent } :
                HintikkaGoal Const Γ).toHintikkaSet.trueFormulas = Δ := ih
          change φ ::
              ({ antecedents := Δ, succedent := succedent } :
                HintikkaGoal Const Γ).toHintikkaSet.trueFormulas = φ :: Δ
          rw [htail]

@[simp] theorem falseFormulas_toHintikkaSet (g : HintikkaGoal Const Γ) :
    g.toHintikkaSet.falseFormulas = [g.succedent] := by
  cases g with
  | mk antecedents succedent =>
      induction antecedents with
      | nil =>
          rfl
      | cons φ Δ ih =>
          have htail :
              ({ antecedents := Δ, succedent := succedent } :
                HintikkaGoal Const Γ).toHintikkaSet.falseFormulas = [succedent] := ih
          change
              ({ antecedents := Δ, succedent := succedent } :
                HintikkaGoal Const Γ).toHintikkaSet.falseFormulas = [succedent]
          exact htail

theorem icttConsistent_toHintikkaSet_iff_not_derivable (g : HintikkaGoal Const Γ) :
    g.toHintikkaSet.ICTTConsistent ↔
      ¬ Derivable (Base := Base) (Const := Const) g.antecedents g.succedent := by
  simp [HintikkaSet.ICTTConsistent]

end HintikkaGoal

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL
