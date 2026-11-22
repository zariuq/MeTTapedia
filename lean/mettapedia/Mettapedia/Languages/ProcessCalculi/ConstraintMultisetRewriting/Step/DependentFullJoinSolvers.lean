import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFullJoinFull
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentNormalizingSolver
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPermutation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentFragmentFiringPi

/-!
# The fibre join through R86's and R90's solvers

R93 read R77's pattern and full solvers rule by rule and found that every progressing round keeps
translated telescopes. This file does the same for the later solvers: R86's normalizing and permuting
solvers, and R90's identity and Π solvers (whose fallback is R90's fragment round).

**Translated telescopes are chains of sort constants** (`SortChains`). A raw telescope whose every
declaration is a Π-chain of sort constants, read from the signature's sorts, is the telescope of a
list frame (`translated_of_sortChains`), and conversely (`sortChains_of_translated`).

**The rules, one by one:**
* the distinct-locals refutation and the rigid round (`rigidRound_translated`): the rigid round
  progresses only through R77's full round;
* **context normalization** (`contextStep_translated`, `prepare_translated`): a chain has no redex,
  so the normalized telescope is the telescope itself. This needs the root evaluator to be silent on
  chains (`ChainsSilent`); the evaluator without root steps is (`chainsSilent_none`). A root step on
  a sort constant would rewrite a translated declaration out of the image;
* **rotation** (`rotateRaw_sortChains`, `rotateRule_translated`): renaming, strengthening and
  weakening keep chains, so a rotated translated telescope is the telescope of the permuted list
  frame;
* **decomposition** of a local application, an identity type or a Π type (`decomposeSearch_translated`,
  `idDecomposeSearch_translated`, `piDecomposeSearch_translated`): the store is replaced by an
  equivalent one at the same frame, and the pattern rule then removes the newest declaration.

So every one of these solvers keeps translated telescopes (`normalizing_keeps_translated`,
`permuting_keeps_translated`, `fragment_keeps_translated`, `identity_keeps_translated`,
`pi_keeps_translated`), and each one's decision on a translated store is a decision in the fibre
(`decidedInFibre_of_keeps` and its five instances). No rule of these solvers leaves the image.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
namespace DependentFull

open _root_.CategoryTheory
open Mettapedia.OSLF
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentFibre Translation
open ContextualDependentUpdate

/-! ## Telescopes of sort chains -/

section Chains

variable {Head : Type} {sig : Binding.Signature} (names : BindingSignatureEmbedding.Names sig)

/-- **A telescope of sort chains**: every declaration is the closed type `Π Γ. s` of a metavariable
arity, as a chain of sort constants. -/
inductive SortChains : {n : Nat} → Ctx Head n → Prop
  | nil : SortChains .nil
  | snoc {n : Nat} {raw : Ctx Head n} (a : Binding.MetaArity sig) : SortChains raw →
      SortChains (.snoc raw (constChain (a.1.reverse.map names.sort) (names.sort a.2)))

theorem sortChains_metaCtx : ∀ N : List (Binding.MetaArity sig), SortChains names (metaCtx (Head := Head) names N)
  | [] => .nil
  | a :: N => by
      show SortChains names (.snoc (metaCtx names N) (liftClosed (BindingSignatureEmbedding.bindingType names a.1 a.2)))
      rw [liftClosed_bindingType]
      exact .snoc a (sortChains_metaCtx N)

end Chains

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (church : ConversionCoherence.ChurchRosser S.R)
variable {sig : Binding.Signature} (names : BindingSignatureEmbedding.Names sig)
  (realization : BindingSignatureEmbedding.Realization names S.R)

/-- **A telescope of sort chains is translated.** -/
theorem translated_of_sortChains {n : Nat} {raw : Ctx Head n} (chains : SortChains names raw) :
    ∀ formed : CtxFormed S.R raw,
      Translated facts roots heads church names realization ⟨n, raw, formed⟩ := by
  induction chains with
  | nil => intro formed; exact ⟨[], rfl⟩
  | @snoc n raw a chains ih =>
      intro formed
      obtain ⟨N, same⟩ := ih (ContextualDependentWorklist.formedPrefix formed)
      have arity : n = N.length := congrArg Context.arity same
      subst arity
      have raws : raw = metaCtx names N := eq_of_heq (congr_arg_heq Context.raw same)
      subst raws
      refine ⟨a :: N, ContextualDependentWorklist.context_eq ?_ _ _⟩
      show Ctx.snoc (metaCtx names N) (constChain (a.1.reverse.map names.sort) (names.sort a.2)) =
        Ctx.snoc (metaCtx names N) (liftClosed (BindingSignatureEmbedding.bindingType names a.1 a.2))
      rw [liftClosed_bindingType]

/-- **A translated telescope is a telescope of sort chains.** -/
theorem sortChains_of_translated {Γ : Context S.R}
    (translated : Translated facts roots heads church names realization Γ) : SortChains names Γ.raw := by
  obtain ⟨N, rfl⟩ := translated
  exact sortChains_metaCtx names N

/-! ## Chains have no redex -/

/-- **A root evaluator silent on chains** fires on no chain of constants. -/
def ChainsSilent (root : ExecutableReduction.RootEvaluator S.R) : Prop :=
  ∀ {n : Nat} (cs : List DeclName) (result : DeclName), root (constChain (Head := Head) (n := n) cs result) = none

/-- The evaluator without root steps is silent on chains. -/
theorem chainsSilent_none : ChainsSilent (S := S) (fun _ => none) := fun _ _ => rfl

theorem step_const_none {root : ExecutableReduction.RootEvaluator S.R} (silent : ChainsSilent root)
    {n : Nat} (c : DeclName) : ExecutableReduction.step S.R root (.const c : Tm Head n) = none := by
  have quiet : root (.const c : Tm Head n) = none := silent [] c
  unfold ExecutableReduction.step
  rw [quiet]

theorem step_chain_none {root : ExecutableReduction.RootEvaluator S.R} (silent : ChainsSilent root)
    (cs : List DeclName) (result : DeclName) :
    ∀ {n : Nat}, ExecutableReduction.step S.R root (constChain (Head := Head) (n := n) cs result) = none := by
  induction cs with
  | nil => intro n; exact step_const_none silent result
  | cons c cs ih =>
      intro n
      have quiet : root (.pi (.const c) (constChain cs result) : Tm Head n) = none := silent (c :: cs) result
      have domain : ExecutableReduction.step S.R root (.const c : Tm Head n) = none := step_const_none silent c
      have body := ih (n := n + 1)
      show ExecutableReduction.step S.R root (.pi (.const c) (constChain cs result)) = none
      rw [ExecutableReduction.step, quiet]
      simp only [domain, body]

theorem normalize_chain {root : ExecutableReduction.RootEvaluator S.R} (silent : ChainsSilent root)
    {fuel n : Nat} {cs : List DeclName} {result : DeclName}
    {reduced : ExecutableReduction.Result S.R (constChain (Head := Head) (n := n) cs result)}
    (computed : ExecutableReduction.normalize S.R root fuel (constChain cs result) = some reduced) :
    reduced.val = constChain cs result := by
  cases fuel with
  | zero => simp [ExecutableReduction.normalize] at computed
  | succ fuel =>
      simp only [ExecutableReduction.normalize, step_chain_none silent] at computed
      cases computed
      rfl

section Rules

variable [DecidableEq Head] [DecidableRel S.R.headEq]
  [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
variable (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles) (algebra : CumulativeAlgebra S.R)
  (declared : DeclaredTypesFormed S.R)
  (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)
  (root : ExecutableReduction.RootEvaluator S.R)
  (rootComplete : ∀ {n : Nat} (term : Tm Head n), root term = none → ∀ target, ¬ S.R.computation.step term target)
  (normalizes : ∀ {Θ : Context S.R} {type : TypeOver Θ} (term : Term Θ type),
    ∃ code : Tm Head Θ.arity, ContextualDependentNormalChecking.Normal (S := S) code ∧
      Equal S.R Θ.raw term.code code type.code)
  (certifyNormal : ∀ {n : Nat} (term : Tm Head n),
    Option (PLift (ContextualDependentNormalChecking.Normal (S := S) term)))
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)

/-! ## Context normalization keeps translated telescopes -/

omit [DecidableEq Head] [DecidableRel S.R.headEq] [∀ head, Decidable (S.R.isUniverse head)]
  [DecidableRel S.R.cumulative] in
include facts roots heads in
/-- **Normalizing a telescope of chains returns it unchanged.** -/
theorem contextNormalize_raw (silent : ChainsSilent root) (fuel : Nat) {n : Nat} {raw : Ctx Head n}
    (chains : SortChains names raw) :
    ∀ (formed : CtxFormed S.R raw) {result : ContextualDependentContextNormalization.Normalized (S := S) raw},
      ContextualDependentContextNormalization.normalize root rootComplete facts roots heads fuel raw formed =
        some result → result.raw = raw := by
  induction chains with
  | nil =>
      intro formed result computed
      simp only [ContextualDependentContextNormalization.normalize] at computed
      cases computed
      rfl
  | @snoc n raw a chains ih =>
      intro formed result computed
      simp only [ContextualDependentContextNormalization.normalize] at computed
      cases priorRun : ContextualDependentContextNormalization.normalize root rootComplete facts roots heads fuel raw
          (ContextualDependentWorklist.formedPrefix formed) with
      | none =>
          rw [priorRun] at computed
          cases computed
      | some prior =>
          rw [priorRun] at computed
          dsimp only at computed
          split at computed
          · cases computed
          · rename_i reduced reducedRun
            cases computed
            show Ctx.snoc prior.raw reduced.val = _
            rw [ih _ priorRun, normalize_chain silent reducedRun]

omit [DecidableEq Head] [DecidableRel S.R.headEq] [∀ head, Decidable (S.R.isUniverse head)]
  [DecidableRel S.R.cumulative] in
/-- **Context normalization keeps translated telescopes.** -/
theorem contextStep_translated (silent : ChainsSilent root) (fuel : Nat) {Θ : Context S.R}
    (problem : EquationStore (TotalTerm Θ))
    (translated : Translated facts roots heads church names realization Θ) :
    Translated facts roots heads church names realization
      (ContextualDependentNormalizing.contextStep root rootComplete facts roots heads fuel problem).target := by
  unfold ContextualDependentNormalizing.contextStep
  split
  · exact translated
  · rename_i normalized computed
    have chains := sortChains_of_translated facts roots heads church names realization translated
    have same := contextNormalize_raw facts roots heads names root rootComplete silent fuel chains Θ.formed computed
    show Translated facts roots heads church names realization ⟨Θ.arity, normalized.raw, normalized.formed⟩
    rw [← same] at chains
    exact translated_of_sortChains facts roots heads church names realization chains normalized.formed

omit [DecidableEq Head] [DecidableRel S.R.headEq] [∀ head, Decidable (S.R.isUniverse head)]
  [DecidableRel S.R.cumulative] in
/-- **Preparation keeps translated telescopes.** -/
theorem prepare_translated (silent : ChainsSilent root) (fuel : Nat) {Θ : Context S.R}
    (problem : EquationStore (TotalTerm Θ))
    (translated : Translated facts roots heads church names realization Θ) :
    Translated facts roots heads church names realization
      (ContextualDependentNormalizing.prepare root rootComplete facts roots heads fuel problem).target :=
  contextStep_translated facts roots heads church names realization root rootComplete silent fuel problem translated

/-! ## The pattern rule and the rigid round -/

/-- **A solved pattern rule ends at a translated telescope.** -/
theorem patternRule_translated (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ))
    {update : Update S.levels problem} {smaller : update.target.arity < Θ.arity}
    (solved : ContextualDependentPatternSolver.patternRule rigid facts complete roots heads algebra declared choices
      reducer root normalizes certifyNormal fuel problem = some (.solved update smaller))
    (translated : Translated facts roots heads church names realization Θ) :
    Translated facts roots heads church names realization update.target := by
  obtain ⟨view, same⟩ := patternRule_target facts roots heads rigid complete algebra declared choices reducer root
    normalizes certifyNormal fuel problem solved
  rw [same]
  exact translated_base facts roots heads church names realization view translated

/-- **The rigid round keeps translated telescopes**: it progresses only through R77's full round. -/
theorem rigidRound_translated (fuel : Nat) {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}
    {update : Update S.levels problem}
    {smaller : ContextualDependentWorklist.Below (ContextualDependentWorklist.size update.remaining)
      (ContextualDependentWorklist.size problem)}
    (progressed : ContextualDependentRigidDecomposition.rigidRound rigid complete facts roots heads algebra declared
      choices reducer root normalizes certifyNormal headTypingUnique fuel problem = .progress update smaller)
    (translated : Translated facts roots heads church names realization Γ) :
    Translated facts roots heads church names realization update.target := by
  unfold ContextualDependentRigidDecomposition.rigidRound at progressed
  split at progressed
  · cases progressed
  · exact full_keeps_translated facts roots heads church names realization rigid complete algebra declared choices
      reducer root normalizes certifyNormal headTypingUnique fuel progressed translated

/-! ## The normalizing solver -/

/-- **R86's normalizing solver keeps translated telescopes.** -/
theorem normalizing_keeps_translated (silent : ChainsSilent root) (fuel : Nat) :
    KeepsFrames (ContextualDependentNormalizing.normalizingSolver rigid complete facts roots heads algebra declared
      choices reducer root rootComplete normalizes certifyNormal headTypingUnique fuel)
      (Translated facts roots heads church names realization) := by
  intro Γ problem update smaller progressed translated
  change ContextualDependentNormalizing.normalizingRound rigid complete facts roots heads algebra declared choices
    reducer root rootComplete normalizes certifyNormal headTypingUnique fuel problem = .progress update smaller
    at progressed
  unfold ContextualDependentNormalizing.normalizingRound at progressed
  split at progressed
  · rename_i inner innerSmaller computed
    cases progressed
    have kept := rigidRound_translated facts roots heads church names realization rigid complete algebra declared
      choices reducer root normalizes certifyNormal headTypingUnique fuel computed
      (prepare_translated facts roots heads church names realization root rootComplete silent fuel problem translated)
    exact kept
  · cases progressed
  · cases progressed

/-! ## Rotation -/

omit [DecidableEq Head] [DecidableRel S.R.headEq] [∀ head, Decidable (S.R.isUniverse head)]
  [DecidableRel S.R.cumulative] in
/-- **Rotating a telescope of chains gives a telescope of chains**: the moved chain is weakened, the
later chain renamed and strengthened, and each stays the same chain. -/
theorem rotateRaw_sortChains : ∀ (depth : Nat) {n : Nat} {raw raw' : Ctx Head n}, SortChains names raw →
    ContextualDependentPermutation.rotateRaw raw depth = some raw' → SortChains names raw'
  | 0, _, _, _, chains, computed => by
      simp only [ContextualDependentPermutation.rotateRaw, Option.some.injEq] at computed
      subst computed
      exact chains
  | _ + 1, _, .nil, _, _, computed => by
      simp [ContextualDependentPermutation.rotateRaw] at computed
  | depth + 1, _, .snoc earlier later, raw', chains, computed => by
      cases chains with
      | snoc a earlierChains =>
          simp only [ContextualDependentPermutation.rotateRaw] at computed
          cases rotatedRun : ContextualDependentPermutation.rotateRaw earlier depth with
          | none =>
              rw [rotatedRun] at computed
              cases computed
          | some rotated =>
              rw [rotatedRun] at computed
              have rotatedChains := rotateRaw_sortChains depth earlierChains rotatedRun
              cases rotatedChains with
              | nil => simp at computed
              | snoc b belowChains =>
                  simp only [rename_chain, invert_chain, Option.map_some, Option.some.injEq] at computed
                  subst computed
                  exact .snoc b (.snoc a belowChains)

/-- **A solved rotation at one depth ends at a translated telescope.** -/
theorem rotateAt_translated (fuel depth : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ))
    {update : Update S.levels problem} {smaller : update.target.arity < Θ.arity}
    (solved : ContextualDependentPermutation.rotateAt rigid complete facts roots heads algebra declared choices reducer
      root normalizes certifyNormal fuel depth problem = some (.solved update smaller))
    (translated : Translated facts roots heads church names realization Θ) :
    Translated facts roots heads church names realization update.target := by
  unfold ContextualDependentPermutation.rotateAt at solved
  split at solved
  · cases solved
  · rename_i raw rotatedRun
    have chains := rotateRaw_sortChains names depth
      (sortChains_of_translated facts roots heads church names realization translated) rotatedRun
    split at solved
    · cases solved
    · split at solved
      · split at solved
        · split at solved
          · try dsimp only at solved
            split at solved
            · rename_i inner innerSmaller computed
              cases solved
              have kept := patternRule_translated facts roots heads church names realization rigid complete
                algebra declared choices reducer root normalizes certifyNormal fuel _ computed
                (translated_of_sortChains facts roots heads church names realization chains _)
              exact kept
            · cases solved
            · cases solved
          · cases solved
        · cases solved
      · cases solved

/-- **A solved rotation search ends at a translated telescope.** -/
theorem rotateSearch_translated (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ))
    (translated : Translated facts roots heads church names realization Θ) :
    ∀ (depths : List Nat) {update : Update S.levels problem} {smaller : update.target.arity < Θ.arity},
      ContextualDependentPermutation.rotateSearch rigid complete facts roots heads algebra declared choices reducer
        root normalizes certifyNormal fuel problem depths = some (.solved update smaller) →
      Translated facts roots heads church names realization update.target
  | [], _, _, solved => by simp [ContextualDependentPermutation.rotateSearch] at solved
  | depth :: rest, update, smaller, solved => by
      simp only [ContextualDependentPermutation.rotateSearch] at solved
      split at solved
      · rename_i found computed
        cases solved
        exact rotateAt_translated facts roots heads church names realization rigid complete algebra declared choices
          reducer root normalizes certifyNormal fuel depth problem computed translated
      · exact rotateSearch_translated fuel problem translated rest solved

/-- **The rotation rule keeps translated telescopes.** -/
theorem rotateRule_translated (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ))
    {update : Update S.levels problem} {smaller : update.target.arity < Θ.arity}
    (solved : ContextualDependentPermutation.rotateRule rigid complete facts roots heads algebra declared choices
      reducer root normalizes certifyNormal fuel problem = some (.solved update smaller))
    (translated : Translated facts roots heads church names realization Θ) :
    Translated facts roots heads church names realization update.target :=
  rotateSearch_translated facts roots heads church names realization rigid complete algebra declared choices reducer
    root normalizes certifyNormal fuel problem translated _ solved

/-- **R86's permuting solver keeps translated telescopes.** -/
theorem permuting_keeps_translated (fuel : Nat) :
    KeepsFrames (ContextualDependentPermutation.permutingSolver rigid complete facts roots heads algebra declared
      choices reducer root normalizes certifyNormal headTypingUnique fuel)
      (Translated facts roots heads church names realization) := by
  intro Γ problem update smaller progressed translated
  change ContextualDependentPermutation.permutingRound rigid complete facts roots heads algebra declared choices
    reducer root normalizes certifyNormal headTypingUnique fuel problem = .progress update smaller at progressed
  unfold ContextualDependentPermutation.permutingRound at progressed
  split at progressed
  · split at progressed
    · rename_i inner innerSmaller computed
      cases progressed
      exact rotateRule_translated facts roots heads church names realization rigid complete algebra declared choices
        reducer root normalizes certifyNormal fuel problem computed translated
    · cases progressed
    · cases progressed
  · rename_i inner innerSmaller computed
    cases progressed
    exact rigidRound_translated facts roots heads church names realization rigid complete algebra declared choices
      reducer root normalizes certifyNormal headTypingUnique fuel computed translated
  · cases progressed

/-! ## Decomposition -/

/-- **A solved decomposition of one equation ends at a translated telescope**: the equation is
replaced by an equivalent one at the same frame, and the pattern rule removes the newest
declaration. -/
theorem decomposeEquation_translated (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ))
    (rest : EquationStore (TotalTerm Θ)) {update : Update S.levels (equation :: rest)}
    {smaller : update.target.arity < Θ.arity}
    (solved : ContextualDependentRigidDecomposition.decomposeEquation rigid facts complete roots heads algebra declared
      choices reducer root normalizes certifyNormal fuel equation rest = some (.solved update smaller))
    (translated : Translated facts roots heads church names realization Θ) :
    Translated facts roots heads church names realization update.target := by
  unfold ContextualDependentRigidDecomposition.decomposeEquation at solved
  split at solved
  · cases solved
  · split at solved
    · cases solved
    · split at solved
      · cases solved
      · try dsimp only at solved
        split at solved
        · cases solved
        · split at solved
          · rename_i inner innerSmaller computed
            cases solved
            have kept := patternRule_translated facts roots heads church names realization rigid complete algebra
              declared choices reducer root normalizes certifyNormal fuel _ computed translated
            exact kept
          · cases solved
          · cases solved

theorem decomposeSearch_translated (fuel : Nat) {Θ : Context S.R}
    (translated : Translated facts roots heads church names realization Θ) :
    ∀ (problem : EquationStore (TotalTerm Θ)) {update : Update S.levels problem}
      {smaller : update.target.arity < Θ.arity},
      ContextualDependentRigidDecomposition.decomposeSearch rigid facts complete roots heads algebra declared choices
        reducer root normalizes certifyNormal fuel problem = some (.solved update smaller) →
      Translated facts roots heads church names realization update.target
  | [], _, _, solved => by simp [ContextualDependentRigidDecomposition.decomposeSearch] at solved
  | equation :: rest, update, smaller, solved => by
      simp only [ContextualDependentRigidDecomposition.decomposeSearch] at solved
      split at solved
      · rename_i found computed
        cases solved
        exact decomposeEquation_translated facts roots heads church names realization rigid complete algebra declared
          choices reducer root normalizes certifyNormal fuel equation rest computed translated
      · obtain ⟨found, computed, kept⟩ := Option.map_eq_some_iff.mp solved
        cases found with
        | solved inner innerSmaller =>
            cases kept
            exact decomposeSearch_translated fuel translated rest computed
        | refuted _ => cases kept

/-- **The decomposition round keeps translated telescopes.** -/
theorem decomposeRound_translated (fuel : Nat) {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}
    {update : Update S.levels problem}
    {smaller : ContextualDependentWorklist.Below (ContextualDependentWorklist.size update.remaining)
      (ContextualDependentWorklist.size problem)}
    (progressed : ContextualDependentRigidDecomposition.decomposeRound rigid facts complete roots heads algebra declared
      choices reducer root normalizes certifyNormal headTypingUnique fuel problem = .progress update smaller)
    (translated : Translated facts roots heads church names realization Γ) :
    Translated facts roots heads church names realization update.target := by
  unfold ContextualDependentRigidDecomposition.decomposeRound at progressed
  split at progressed
  · rename_i inner innerSmaller computed
    cases progressed
    exact decomposeSearch_translated facts roots heads church names realization rigid complete algebra declared
      choices reducer root normalizes certifyNormal fuel translated problem computed
  · cases progressed
  · exact rigidRound_translated facts roots heads church names realization rigid complete algebra declared choices
      reducer root normalizes certifyNormal headTypingUnique fuel progressed translated

theorem idDecomposeEquation_translated (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ))
    (rest : EquationStore (TotalTerm Θ)) {update : Update S.levels (equation :: rest)}
    {smaller : update.target.arity < Θ.arity}
    (solved : ContextualDependentFragment.idDecomposeEquation facts roots heads algebra declared choices reducer rigid
      complete root normalizes certifyNormal fuel equation rest = some (.solved update smaller))
    (translated : Translated facts roots heads church names realization Θ) :
    Translated facts roots heads church names realization update.target := by
  unfold ContextualDependentFragment.idDecomposeEquation at solved
  split at solved
  · cases solved
  · split at solved
    · cases solved
    · split at solved
      · try dsimp only at solved
        split at solved
        · cases solved
        · split at solved
          · rename_i inner innerSmaller computed
            cases solved
            have kept := patternRule_translated facts roots heads church names realization rigid complete algebra
              declared choices reducer root normalizes certifyNormal fuel _ computed translated
            exact kept
          · cases solved
          · cases solved
      · cases solved

theorem idDecomposeSearch_translated (fuel : Nat) {Θ : Context S.R}
    (translated : Translated facts roots heads church names realization Θ) :
    ∀ (problem : EquationStore (TotalTerm Θ)) {update : Update S.levels problem}
      {smaller : update.target.arity < Θ.arity},
      ContextualDependentFragment.idDecomposeSearch facts roots heads algebra declared choices reducer rigid complete
        root normalizes certifyNormal fuel problem = some (.solved update smaller) →
      Translated facts roots heads church names realization update.target
  | [], _, _, solved => by simp [ContextualDependentFragment.idDecomposeSearch] at solved
  | equation :: rest, update, smaller, solved => by
      simp only [ContextualDependentFragment.idDecomposeSearch] at solved
      split at solved
      · rename_i found computed
        cases solved
        exact idDecomposeEquation_translated facts roots heads church names realization rigid complete algebra
          declared choices reducer root normalizes certifyNormal fuel equation rest computed translated
      · obtain ⟨found, computed, kept⟩ := Option.map_eq_some_iff.mp solved
        cases found with
        | solved inner innerSmaller =>
            cases kept
            exact idDecomposeSearch_translated fuel translated rest computed
        | refuted _ => cases kept

theorem piDecomposeEquation_translated (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ))
    (rest : EquationStore (TotalTerm Θ)) {update : Update S.levels (equation :: rest)}
    {smaller : update.target.arity < Θ.arity}
    (solved : ContextualDependentFragment.piDecomposeEquation facts roots heads algebra declared choices reducer rigid
      complete root normalizes certifyNormal fuel equation rest = some (.solved update smaller))
    (translated : Translated facts roots heads church names realization Θ) :
    Translated facts roots heads church names realization update.target := by
  unfold ContextualDependentFragment.piDecomposeEquation at solved
  split at solved
  · cases solved
  · split at solved
    · cases solved
    · split at solved
      · cases solved
      · try dsimp only at solved
        split at solved
        · cases solved
        · split at solved
          · rename_i inner innerSmaller computed
            cases solved
            have kept := patternRule_translated facts roots heads church names realization rigid complete algebra
              declared choices reducer root normalizes certifyNormal fuel _ computed translated
            exact kept
          · cases solved
          · cases solved

theorem piDecomposeSearch_translated (fuel : Nat) {Θ : Context S.R}
    (translated : Translated facts roots heads church names realization Θ) :
    ∀ (problem : EquationStore (TotalTerm Θ)) {update : Update S.levels problem}
      {smaller : update.target.arity < Θ.arity},
      ContextualDependentFragment.piDecomposeSearch facts roots heads algebra declared choices reducer rigid complete
        root normalizes certifyNormal fuel problem = some (.solved update smaller) →
      Translated facts roots heads church names realization update.target
  | [], _, _, solved => by simp [ContextualDependentFragment.piDecomposeSearch] at solved
  | equation :: rest, update, smaller, solved => by
      simp only [ContextualDependentFragment.piDecomposeSearch] at solved
      split at solved
      · rename_i found computed
        cases solved
        exact piDecomposeEquation_translated facts roots heads church names realization rigid complete algebra
          declared choices reducer root normalizes certifyNormal fuel equation rest computed translated
      · obtain ⟨found, computed, kept⟩ := Option.map_eq_some_iff.mp solved
        cases found with
        | solved inner innerSmaller =>
            cases kept
            exact piDecomposeSearch_translated fuel translated rest computed
        | refuted _ => cases kept

/-! ## R90's fragment, identity and Π rounds -/

/-- **The fragment round keeps translated telescopes.** -/
theorem fragment_keeps_translated (silent : ChainsSilent root) (fuel : Nat) :
    KeepsFrames (ContextualDependentFragment.fragmentSolver rigid facts complete roots heads algebra declared choices
      reducer root rootComplete normalizes certifyNormal headTypingUnique fuel)
      (Translated facts roots heads church names realization) := by
  intro Γ problem update smaller progressed translated
  change ContextualDependentFragment.fragmentRound rigid facts complete roots heads algebra declared choices reducer
    root rootComplete normalizes certifyNormal headTypingUnique fuel problem = .progress update smaller at progressed
  have prepared := prepare_translated facts roots heads church names realization root rootComplete silent fuel problem
    translated
  unfold ContextualDependentFragment.fragmentRound at progressed
  split at progressed
  · rename_i inner innerSmaller computed
    cases progressed
    have kept := decomposeRound_translated facts roots heads church names realization rigid complete algebra declared
      choices reducer root normalizes certifyNormal headTypingUnique fuel computed prepared
    exact kept
  · cases progressed
  · split at progressed
    · rename_i inner innerSmaller computed
      cases progressed
      have kept := rotateRule_translated facts roots heads church names realization rigid complete algebra declared
        choices reducer root normalizes certifyNormal fuel _ computed prepared
      exact kept
    · cases progressed
    · cases progressed

/-- **R90's identity round keeps translated telescopes.** -/
theorem identity_keeps_translated (silent : ChainsSilent root) (fuel : Nat) :
    KeepsFrames (ContextualDependentFragment.identitySolver facts roots heads algebra declared choices reducer rigid
      complete root normalizes certifyNormal headTypingUnique rootComplete fuel)
      (Translated facts roots heads church names realization) := by
  intro Γ problem update smaller progressed translated
  change ContextualDependentFragment.identityRound facts roots heads algebra declared choices reducer rigid complete
    root normalizes certifyNormal headTypingUnique rootComplete fuel problem = .progress update smaller at progressed
  have prepared := prepare_translated facts roots heads church names realization root rootComplete silent fuel problem
    translated
  unfold ContextualDependentFragment.identityRound at progressed
  split at progressed
  · rename_i inner innerSmaller computed
    cases progressed
    have kept := idDecomposeSearch_translated facts roots heads church names realization rigid complete algebra
      declared choices reducer root normalizes certifyNormal fuel prepared _ computed
    exact kept
  · cases progressed
  · exact fragment_keeps_translated facts roots heads church names realization rigid complete algebra declared choices
      reducer root rootComplete normalizes certifyNormal headTypingUnique silent fuel progressed translated

/-- **R90's Π round keeps translated telescopes.** -/
theorem pi_keeps_translated (silent : ChainsSilent root) (fuel : Nat) :
    KeepsFrames (ContextualDependentFragment.piSolver facts roots heads algebra declared choices reducer rigid
      complete root normalizes certifyNormal headTypingUnique rootComplete fuel)
      (Translated facts roots heads church names realization) := by
  intro Γ problem update smaller progressed translated
  change ContextualDependentFragment.piRound facts roots heads algebra declared choices reducer rigid complete
    root normalizes certifyNormal headTypingUnique rootComplete fuel problem = .progress update smaller at progressed
  have prepared := prepare_translated facts roots heads church names realization root rootComplete silent fuel problem
    translated
  unfold ContextualDependentFragment.piRound at progressed
  split at progressed
  · rename_i inner innerSmaller computed
    cases progressed
    have kept := piDecomposeSearch_translated facts roots heads church names realization rigid complete algebra
      declared choices reducer root normalizes certifyNormal fuel prepared _ computed
    exact kept
  · cases progressed
  · exact identity_keeps_translated facts roots heads church names realization rigid complete algebra declared choices
      reducer root rootComplete normalizes certifyNormal headTypingUnique silent fuel progressed translated

end Rules

/-! ## Decisions in the fibre -/

/-- **A solver that keeps translated telescopes decides in the fibre wherever it decides.** -/
theorem decidedInFibre_of_keeps (solver : ContextualDependentWorklist.Solver S.levels)
    (keeps : KeepsFrames solver (Translated facts roots heads church names realization))
    {M : List (Binding.MetaArity sig)} (K : EquationStore (Binding.ContextualFamily.Observation sig M.get))
    (fuel : Nat)
    (decided : (ContextualDependentWorklist.run solver ((fibre facts roots heads church names realization).store K)
      fuel).Decided) :
    DecidedInFibre facts roots heads church names realization K := by
  generalize computed : ContextualDependentWorklist.run solver
    ((fibre facts roots heads church names realization).store K) fuel = outcome at decided
  cases outcome with
  | solved state finished =>
      have principal := ContextualDependentWorklist.drive_solved_principal _ computed
      obtain ⟨N, same⟩ := drive_solved_target _ keeps fuel _
        (translated_obj facts roots heads church names realization M) computed
      have landing : ∀ (T : Context S.R) (answer : T ⟶ (fibre facts roots heads church names realization).obj M),
          T = (fibre facts roots heads church names realization).obj N →
          (frames S.levels).Principal ((fibre facts roots heads church names realization).store K) answer →
          DecidedInFibre facts roots heads church names realization K := by
        intro T answer same principal
        subst same
        exact .inl ⟨N, answer, principal⟩
      exact landing _ state.answer same principal
  | refuted absent => exact .inr absent
  | stuck _ => exact False.elim decided
  | cutoff _ => exact False.elim decided

section Instances

variable [DecidableEq Head] [DecidableRel S.R.headEq]
  [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
variable (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles) (algebra : CumulativeAlgebra S.R)
  (declared : DeclaredTypesFormed S.R)
  (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)
  (root : ExecutableReduction.RootEvaluator S.R)
  (rootComplete : ∀ {n : Nat} (term : Tm Head n), root term = none → ∀ target, ¬ S.R.computation.step term target)
  (normalizes : ∀ {Θ : Context S.R} {type : TypeOver Θ} (term : Term Θ type),
    ∃ code : Tm Head Θ.arity, ContextualDependentNormalChecking.Normal (S := S) code ∧
      Equal S.R Θ.raw term.code code type.code)
  (certifyNormal : ∀ {n : Nat} (term : Tm Head n),
    Option (PLift (ContextualDependentNormalChecking.Normal (S := S) term)))
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)
  {M : List (Binding.MetaArity sig)} (K : EquationStore (Binding.ContextualFamily.Observation sig M.get))
  (rounds fuel : Nat)

/-- **R86's normalizing solver decides in the fibre.** -/
theorem decidedInFibre_of_normalizing (silent : ChainsSilent root)
    (decided : (ContextualDependentWorklist.run (ContextualDependentNormalizing.normalizingSolver rigid complete facts
      roots heads algebra declared choices reducer root rootComplete normalizes certifyNormal headTypingUnique rounds)
      ((fibre facts roots heads church names realization).store K) fuel).Decided) :
    DecidedInFibre facts roots heads church names realization K :=
  decidedInFibre_of_keeps facts roots heads church names realization _
    (normalizing_keeps_translated facts roots heads church names realization rigid complete algebra declared choices
      reducer root rootComplete normalizes certifyNormal headTypingUnique silent rounds) K fuel decided

/-- **R86's permuting solver decides in the fibre.** -/
theorem decidedInFibre_of_permuting
    (decided : (ContextualDependentWorklist.run (ContextualDependentPermutation.permutingSolver rigid complete facts
      roots heads algebra declared choices reducer root normalizes certifyNormal headTypingUnique rounds)
      ((fibre facts roots heads church names realization).store K) fuel).Decided) :
    DecidedInFibre facts roots heads church names realization K :=
  decidedInFibre_of_keeps facts roots heads church names realization _
    (permuting_keeps_translated facts roots heads church names realization rigid complete algebra declared choices
      reducer root normalizes certifyNormal headTypingUnique rounds) K fuel decided

/-- **R90's fragment solver decides in the fibre.** -/
theorem decidedInFibre_of_fragment (silent : ChainsSilent root)
    (decided : (ContextualDependentWorklist.run (ContextualDependentFragment.fragmentSolver rigid facts complete roots
      heads algebra declared choices reducer root rootComplete normalizes certifyNormal headTypingUnique rounds)
      ((fibre facts roots heads church names realization).store K) fuel).Decided) :
    DecidedInFibre facts roots heads church names realization K :=
  decidedInFibre_of_keeps facts roots heads church names realization _
    (fragment_keeps_translated facts roots heads church names realization rigid complete algebra declared choices
      reducer root rootComplete normalizes certifyNormal headTypingUnique silent rounds) K fuel decided

/-- **R90's identity solver decides in the fibre.** -/
theorem decidedInFibre_of_identity (silent : ChainsSilent root)
    (decided : (ContextualDependentWorklist.run (ContextualDependentFragment.identitySolver facts roots heads algebra
      declared choices reducer rigid complete root normalizes certifyNormal headTypingUnique rootComplete rounds)
      ((fibre facts roots heads church names realization).store K) fuel).Decided) :
    DecidedInFibre facts roots heads church names realization K :=
  decidedInFibre_of_keeps facts roots heads church names realization _
    (identity_keeps_translated facts roots heads church names realization rigid complete algebra declared choices
      reducer root rootComplete normalizes certifyNormal headTypingUnique silent rounds) K fuel decided

/-- **R90's Π solver decides in the fibre.** -/
theorem decidedInFibre_of_pi (silent : ChainsSilent root)
    (decided : (ContextualDependentWorklist.run (ContextualDependentFragment.piSolver facts roots heads algebra
      declared choices reducer rigid complete root normalizes certifyNormal headTypingUnique rootComplete rounds)
      ((fibre facts roots heads church names realization).store K) fuel).Decided) :
    DecidedInFibre facts roots heads church names realization K :=
  decidedInFibre_of_keeps facts roots heads church names realization _
    (pi_keeps_translated facts roots heads church names realization rigid complete algebra declared choices
      reducer root rootComplete normalizes certifyNormal headTypingUnique silent rounds) K fuel decided

end Instances

end DependentFull

#print axioms DependentFull.sortChains_metaCtx
#print axioms DependentFull.translated_of_sortChains
#print axioms DependentFull.sortChains_of_translated
#print axioms DependentFull.chainsSilent_none
#print axioms DependentFull.step_chain_none
#print axioms DependentFull.contextNormalize_raw
#print axioms DependentFull.contextStep_translated
#print axioms DependentFull.prepare_translated
#print axioms DependentFull.patternRule_translated
#print axioms DependentFull.rigidRound_translated
#print axioms DependentFull.normalizing_keeps_translated
#print axioms DependentFull.rotateRaw_sortChains
#print axioms DependentFull.rotateAt_translated
#print axioms DependentFull.rotateRule_translated
#print axioms DependentFull.permuting_keeps_translated
#print axioms DependentFull.decomposeEquation_translated
#print axioms DependentFull.decomposeRound_translated
#print axioms DependentFull.idDecomposeSearch_translated
#print axioms DependentFull.piDecomposeSearch_translated
#print axioms DependentFull.fragment_keeps_translated
#print axioms DependentFull.identity_keeps_translated
#print axioms DependentFull.pi_keeps_translated
#print axioms DependentFull.decidedInFibre_of_keeps
#print axioms DependentFull.decidedInFibre_of_normalizing
#print axioms DependentFull.decidedInFibre_of_permuting
#print axioms DependentFull.decidedInFibre_of_fragment
#print axioms DependentFull.decidedInFibre_of_identity
#print axioms DependentFull.decidedInFibre_of_pi

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
