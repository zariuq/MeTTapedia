import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNamedPatternImages
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBindingPatternImages
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualRigidPatterns
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualProblemMapping
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameSaturation

/-!
# Structural patterns survive actual solver choices and runs

Every root constructor supplies pattern assignment images and a pattern
residual. A flexible-pair input supplies the injective occurrence maps needed
by its computed pullback; the root case carries no preservation assumption.
Located choices map their actual retained prefix and suffix. Rigid
normalization and recursive frame changes then preserve the same fragment
through the executable driver.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSolverPatterns

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual
open ContextualPatternFragment
open ContextualSolverCases
open ContextualFrameUpdate

variable {S : Signature} {V : Type} {source : V → MetaArity S}

theorem singleton_patterns (equation : Equation (Observation S source))
    (first : Pattern S source equation.1.2.2) (second : Pattern S source equation.2.2.2) :
    ProblemPattern [equation] := by
  intro pair member
  have same := List.mem_singleton.mp member
  subst pair
  exact ⟨first, second⟩

variable [DecidableEq V]

theorem root_preserves {equation : Equation (Observation S source)} (selected : RootCase S source equation) :
    Pattern S source equation.1.2.2 → Pattern S source equation.2.2.2 →
      (∀ identity, Pattern S selected.perform.declaration (selected.perform.answer identity)) ∧
        ProblemPattern selected.perform.remaining := by
  induction selected with
  | reflexive term =>
      intro _ _
      exact ⟨fun identity => generator_pattern identity, fun _ member => False.elim (List.not_mem_nil member)⟩
  | binding recovered =>
      intro first second
      exact ⟨ContextualBindingPatternImages.case_images recovered first second,
        fun _ member => False.elim (List.not_mem_nil member)⟩
  | imitation identity rho operator fields =>
      intro first second
      have images := ContextualNamedPatternImages.imitation_images identity rho operator fields []
      refine ⟨images, ?_⟩
      dsimp only [RootCase.perform, ContextualNamedImitation.apply, id]
      rw [ContextualProblemMapping.composition]
      apply map_patterns _ images
      exact singleton_patterns _ first second
  | selfPair identity left right different =>
      intro _ _
      refine ⟨ContextualNamedPatternImages.self_images identity left right [], ?_⟩
      simp only [RootCase.perform, ContextualNamedSelfPair.apply, id, mapProblem, List.map_nil]
      exact fun _ member => False.elim (List.not_mem_nil member)
  | flexPair first second different sorts left right =>
      intro leftPattern rightPattern
      have leftInjective := (ContextualSolverPatternImages.renamed_generator_pattern_iff first left).mp leftPattern
      have rightInjective := (ContextualSolverPatternImages.renamed_generator_pattern_iff second right).mp rightPattern
      refine ⟨ContextualNamedPatternImages.flex_images first second different sorts left right
        leftInjective rightInjective [], ?_⟩
      simp only [RootCase.perform, ContextualNamedFlexPair.apply, ContextualHeterogeneousFlexPair.apply,
        id, mapProblem, List.map_nil]
      exact fun _ member => False.elim (List.not_mem_nil member)
  | reverse original earlier =>
      intro first second
      exact earlier second first

theorem choice_preserves {problem : Problem source} (selected : Choice problem) (patterned : ProblemPattern problem) :
    (∀ identity, Pattern S selected.perform.declaration (selected.perform.answer identity)) ∧
      ProblemPattern selected.perform.remaining := by
  rcases selected with ⟨before, equation, root, after, split⟩
  subst problem
  have both := patterned equation (List.mem_append_right _ List.mem_cons_self)
  obtain ⟨images, remaining⟩ := root_preserves root both.1 both.2
  refine ⟨images, ?_⟩
  change ProblemPattern (mapProblem root.perform.answer before ++
    (root.perform.remaining ++ mapProblem root.perform.answer after))
  apply (ContextualRigidPatterns.append_patterns _ _).mpr
  constructor
  · exact map_patterns _ images before fun pair member => patterned pair (List.mem_append_left _ member)
  · apply (ContextualRigidPatterns.append_patterns _ _).mpr
    exact ⟨remaining, map_patterns _ images after fun pair member =>
      patterned pair (List.mem_append_right _ (List.mem_cons_of_mem _ member))⟩

theorem computed_preserves [DecidableEq S.Srt] [∀ sort, DecidableEq (S.Op sort)]
    {problem : Problem source} {update : Update problem}
    (computed : ContextualFrameWorklist.choose problem = some update) (patterned : ProblemPattern problem) :
    (∀ identity, Pattern S update.declaration (update.answer identity)) ∧ ProblemPattern update.remaining := by
  unfold ContextualFrameWorklist.choose at computed
  obtain ⟨selected, _, rfl⟩ := Option.map_eq_some_iff.mp computed
  exact choice_preserves selected patterned

variable [DecidableEq S.Srt] [∀ sort, DecidableEq (S.Op sort)]

theorem run_preserves (fuel : Nat) :
    ∀ {Names : Type} [DecidableEq Names] (declaration : Names → MetaArity S)
      (problem : Problem declaration), ProblemPattern problem →
      ∀ {update : Update problem}, ContextualFrameWorklist.run fuel declaration problem = .residual update →
        ProblemPattern update.remaining := by
  induction fuel with
  | zero =>
      intro Names equality declaration problem patterned update computed
      simp only [ContextualFrameWorklist.run, ContextualFrameWorklist.runWithRefuter] at computed
      have same := ContextualFrameWorklist.Result.residual.inj computed
      cases same
      exact patterned
  | succ fuel earlier =>
      intro Names equality declaration problem patterned update computed
      simp only [ContextualFrameWorklist.run, ContextualFrameWorklist.runWithRefuter,
        ContextualFrameWorklist.normalizationUpdate] at computed
      split at computed
      · cases computed
      · rename_i remaining normalized
        have normalizedPattern := ContextualRigidPatterns.normalization_patterns problem patterned normalized
        split at computed
        · cases computed
        · split at computed
          · have same := ContextualFrameWorklist.Result.residual.inj computed
            cases same
            exact normalizedPattern
          · rename_i chosen selected
            have chosenPattern := (computed_preserves selected normalizedPattern).2
            let _ := chosen.equality
            dsimp only [ContextualFrameUpdate.Update.then] at computed
            simp only [ContextualFrameWorklist.Result.after] at computed
            split at computed
            · rename_i last tail
              have lastPattern := earlier chosen.declaration chosen.remaining chosenPattern tail
              have same := ContextualFrameWorklist.Result.residual.inj computed
              cases same
              exact lastPattern
            · cases computed

theorem saturates_patterns {Next : Type} (next : Next → MetaArity S) (problem : Problem source)
    (patterned : ProblemPattern problem) (candidate : Assignment source next) (solved : Models candidate problem) :
    ∃ (fuel : Nat) (update : Update problem),
      ContextualFrameWorklist.run fuel source problem = .residual update ∧
        (letI := update.equality
         ContextualFrameWorklist.choose (S := S) (source := update.declaration) update.remaining = none) ∧
        ProblemPattern update.remaining ∧
        ∃ residual : Assignment update.declaration next, Models residual update.remaining ∧
          ∀ identity, candidate identity = instantiate residual (update.answer identity) := by
  obtain ⟨fuel, update, computed, noChoice, factors⟩ :=
    ContextualFrameSaturation.saturates_preserving_every_solution next problem candidate solved
  exact ⟨fuel, update, computed, noChoice, run_preserves fuel source problem patterned computed, factors⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSolverPatterns
