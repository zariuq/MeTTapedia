import Mettapedia.GSLT.LanguageDef.BoundPrefixProjectionControls

/-!
# Integrated contextual slot matching controls

These exercise the actual matcher, not only its recovered-body helper. The
signature is derived from the authored occurrence-control LanguageDef.
-/

namespace Mettapedia.GSLT.LanguageDef.ScopedMatchingControls

open Mettapedia.OSLF.Binding Mettapedia.OSLF.MeTTaIL.Syntax
open MetaDependencyControls ScopedMatcherDependencyBoundary PartialRenamingControls
open PartialRenamingInstantiationControls VariableArgumentRecognitionControls
open BoundPrefixProjectionControls
open WellSorted.OccurrenceControls (a b)

set_option autoImplicit false

noncomputable local instance operatorEquality (sort : signature.Srt) :
    DecidableEq (signature.Op sort) := Classical.decEq _

def nestedSlot : Args (withMetas signature nestedDeclarations)
    [([a, a], .arrow a a)] [a, b] :=
  .cons (.op (.inr (.mk nestedIndex)) subsetWithOrdinary) .nil

def nestedSlotTarget : Args signature [([a, a], .arrow a a)] [] :=
  .cons nestedSelected .nil

theorem nested_slot_records_actual_body :
    smatchA (emptyMAcc : MAcc signature nestedDeclarations [a, b]) nestedSlot nestedSlotTarget =
      some (setMeta emptyMAcc nestedIndex nestedBody) := by
  unfold nestedSlot nestedSlotTarget
  rw [smatchA_recovered_slot _ nestedIndex subsetWithOrdinary nestedSelected .nil .nil nestedBody (by rfl)]
  simp only [emptyMAcc, smatchA, smatchAtA_nil]

theorem nested_slot_checks_existing_body :
    smatchA (setMeta (emptyMAcc : MAcc signature nestedDeclarations [a, b]) nestedIndex nestedBody)
      nestedSlot nestedSlotTarget = some (setMeta emptyMAcc nestedIndex nestedBody) := by
  unfold nestedSlot nestedSlotTarget
  rw [smatchA_recovered_slot _ nestedIndex subsetWithOrdinary nestedSelected .nil .nil nestedBody (by rfl)]
  simp only [setMeta_self, smatchA, smatchAtA_nil, ↓reduceIte]

theorem nested_slot_rejects_conflicting_body :
    smatchA (setMeta (emptyMAcc : MAcc signature nestedDeclarations [a, b]) nestedIndex locallyBoundResult)
      nestedSlot nestedSlotTarget = none := by
  unfold nestedSlot nestedSlotTarget
  rw [smatchA_recovered_slot _ nestedIndex subsetWithOrdinary nestedSelected .nil .nil nestedBody (by rfl)]
  simp only [setMeta_self]
  rw [if_neg]
  intro equality
  have mismatch := congrArg BindingSyntax.erase equality
  cases mismatch

theorem nested_slot_rejects_unselected_reference :
    smatchA (emptyMAcc : MAcc signature nestedDeclarations [a, b]) nestedSlot
      (.cons nestedUnsupported .nil) = none := by
  unfold nestedSlot
  exact smatchA_rejected_slot _ nestedIndex subsetWithOrdinary nestedUnsupported .nil .nil (by rfl)

theorem local_binder_remains_local :
    smatchA (emptyMAcc : MAcc signature nestedDeclarations [a, b]) nestedSlot
      (.cons locallyBoundSource .nil) = some (setMeta emptyMAcc nestedIndex locallyBoundResult) := by
  unfold nestedSlot
  rw [smatchA_recovered_slot _ nestedIndex subsetWithOrdinary locallyBoundSource .nil .nil
    locallyBoundResult (by rfl)]
  simp only [emptyMAcc, smatchA, smatchAtA_nil]

theorem ordinary_rule_variable_not_promoted :
    smatchA (emptyMAcc : MAcc signature nestedDeclarations [a, b])
      (.cons (.op (.inr (.mk nestedIndex)) ordinarySameSort) .nil)
      nestedSlotTarget = none := by
  unfold nestedSlotTarget
  exact smatchA_rejected_slot _ nestedIndex ordinarySameSort nestedSelected .nil .nil (by rfl)

theorem permuted_slot_records_actual_body :
    smatchA (emptyMAcc : MAcc signature binaryDeclarations [a, b])
      (.cons (.op (.inr (.mk binaryIndex)) permutationWithOrdinary) .nil)
      (.cons (.var (.succ .zero) : Term signature ([a, a] ++ []) a) .nil) =
      some (setMeta emptyMAcc binaryIndex (.var .zero)) := by
  rw [smatchA_recovered_slot _ binaryIndex permutationWithOrdinary
    (.var (.succ .zero) : Term signature ([a, a] ++ []) a) .nil .nil (.var .zero) (by rfl)]
  simp only [emptyMAcc, smatchA, smatchAtA_nil]

abbrev mixedDeclarations : List (MetaArity signature) := [([a, b], b)]
abbrev mixedIndex : Fin mixedDeclarations.length := ⟨0, by decide⟩

def mixedSlotArgs : Args (withMetas signature mixedDeclarations)
    [([], a), ([], b)] ([b, a, b] ++ [a, b]) :=
  .cons (.var (.succ .zero)) (.cons (.var .zero) .nil)

theorem mixed_sort_slot_records_actual_body :
    smatchA (emptyMAcc : MAcc signature mixedDeclarations [a, b])
      (.cons (.op (.inr (.mk mixedIndex)) mixedSlotArgs) .nil)
      (.cons (.var .zero : Term signature ([b, a, b] ++ []) b) .nil) =
      some (setMeta emptyMAcc mixedIndex (.var (.succ .zero))) := by
  rw [smatchA_recovered_slot _ mixedIndex mixedSlotArgs
    (.var .zero : Term signature ([b, a, b] ++ []) b) .nil .nil (.var (.succ .zero)) (by rfl)]
  simp only [emptyMAcc, smatchA, smatchAtA_nil]

theorem diagonal_slot_declined :
    smatchA (emptyMAcc : MAcc signature binaryDeclarations [a, b])
      (.cons (.op (.inr (.mk binaryIndex)) diagonalWithOrdinary) .nil)
      (.cons (.var .zero : Term signature ([a] ++ []) a) .nil) = none :=
  smatchA_rejected_slot _ binaryIndex diagonalWithOrdinary
    (.var .zero : Term signature ([a] ++ []) a) .nil .nil (by rfl)

/-- The integrated rejection is a profile boundary, not an unsolvability result. -/
theorem diagonal_declined_but_instantiable :
    smatchA (emptyMAcc : MAcc signature binaryDeclarations [a, b])
      (.cons (.op (.inr (.mk binaryIndex)) diagonalWithOrdinary) .nil)
      (.cons (.var .zero : Term signature ([a] ++ []) a) .nil) = none ∧
    instantiate firstBody (.op (.inr (.mk binaryIndex)) diagonalWithOrdinary) =
      (.var .zero : Term signature ([a] ++ [a, b]) a) :=
  ⟨diagonal_slot_declined, rfl⟩

/-- An empty declared dependency context beneath a binder accepts a genuinely
closed body; the ambient binder does not become a required permission. -/
theorem closed_dependency_beneath_binder :
    smatchA (emptyMAcc : MAcc signature declarations [a, b])
      (.cons (.op (.inr (.mk closedIndex)) .nil)
        (.nil : Args (withMetas signature declarations) [] [a, b]))
      (.cons (constant : Term signature ([a] ++ []) a) .nil) =
      some (setMeta emptyMAcc closedIndex constant) := by
  rw [smatchA_recovered_slot _ closedIndex .nil
    (constant : Term signature ([a] ++ []) a) .nil .nil constant (by rfl)]
  simp only [emptyMAcc, smatchA, smatchAtA_nil]

/-- The original global soundness theorem applies to the actual successful
extended match and every assignment realizing its retained accumulator. -/
theorem nested_match_sound_for_every_extension
    (sigma : Sub signature [a, b] [])
    (assignment : (i : Fin nestedDeclarations.length) →
      Term signature (nestedDeclarations.get i).1 (nestedDeclarations.get i).2)
    (realizes : MExtends sigma assignment (setMeta emptyMAcc nestedIndex nestedBody)) :
    bindArgs sigma (instantiateArgs assignment nestedSlot) = nestedSlotTarget :=
  smatchA_sound emptyMAcc _ nestedSlot nestedSlotTarget nested_slot_records_actual_body
    sigma assignment realizes

/-- A rule variable beneath an ambient binder may receive a closed lambda;
the lambda's own newly introduced variable is not an ambient dependency. -/
theorem ordinary_nested_closed_body :
    smatchAtT (S := signature) [a] (emptyMAcc : MAcc signature declarations [.arrow a a])
      (.var (.succ .zero))
      (.op (BindingSyntax.Operator.lambda a a) (.cons (.var .zero) .nil)) =
      some { (emptyMAcc : MAcc signature declarations [.arrow a a]) with
        vars := updatePSub emptyPSub .zero identityTarget } := by
  rw [smatchAtT.eq_def (S := signature)]
  rfl

/-- The same rule variable cannot capture the surrounding binder. -/
theorem ordinary_nested_ambient_reference_rejected :
    smatchAtT (S := signature) [a] (emptyMAcc : MAcc signature declarations [.arrow a a])
      (.var (.succ .zero))
      (.op (BindingSyntax.Operator.lambda a a) (.cons (.var (.succ .zero)) .nil)) = none := by
  rw [smatchAtT.eq_def (S := signature)]
  rfl

theorem bound_reference_is_rigid :
    smatchAtT (S := signature) [a, a] (emptyMAcc : MAcc signature declarations [a])
      (.var (.succ .zero)) (.var (.succ .zero)) = some emptyMAcc := by
  rw [smatchAtT.eq_def (S := signature)]
  rfl

theorem bound_reference_cannot_switch_same_sort_positions :
    smatchAtT (S := signature) [a, a] (emptyMAcc : MAcc signature declarations [a])
      (.var (.succ .zero)) (.var .zero) = none := by
  rw [smatchAtT.eq_def (S := signature)]
  rfl

def repeatedMetaDepths : Args (withMetas signature declarations)
    [([a], a), ([a, a], a)] [] :=
  .cons (metaVar dependentIndex)
    (.cons (rename oldArgument (metaVar dependentIndex)) .nil)

/-- One declared dependency remains the same body at two ambient depths. -/
theorem repeated_meta_at_different_depths :
    smatchA (emptyMAcc : MAcc signature declarations []) repeatedMetaDepths
      (.cons (.var .zero) (.cons (.var (.succ .zero)) .nil)) =
        some (setMeta emptyMAcc dependentIndex (.var .zero)) := by
  unfold repeatedMetaDepths
  simp only [metaVar, rename]
  rw [smatchA_recovered_slot (S := signature) (b := a) (rest := []) _ dependentIndex _ _ _ _ (.var .zero) (by rfl)]
  simp only [emptyMAcc]
  rw [smatchA_recovered_slot (S := signature) (b := a) (rest := [a]) _ dependentIndex _ _ _ _ (.var .zero) (by rfl)]
  simp only [setMeta_self, ↓reduceIte, smatchA, smatchAtA_nil]

/-- Keeping the same result sort does not authorize capture at the deeper use. -/
theorem repeated_meta_rejects_new_binder_capture :
    smatchA (emptyMAcc : MAcc signature declarations []) repeatedMetaDepths
      (.cons (.var .zero) (.cons (.var .zero) .nil)) = none := by
  unfold repeatedMetaDepths
  simp only [metaVar, rename]
  rw [smatchA_recovered_slot (S := signature) (b := a) (rest := []) _ dependentIndex _ _ _ _ (.var .zero) (by rfl)]
  simp only [emptyMAcc]
  exact smatchA_rejected_slot _ dependentIndex _ _ .nil .nil (by rfl)

/-- This is a substitution witness independent of the matcher computation. -/
theorem repeated_meta_actual_instantiation :
    instantiateArgs usesArgument repeatedMetaDepths =
      (.cons (.var .zero) (.cons (.var (.succ .zero)) .nil) :
        Args signature [([a], a), ([a, a], a)] []) := rfl

def repeatedOrdinaryDepths : Args (withMetas signature declarations)
    [([], a), ([a], a)] [a] :=
  .cons (.var .zero) (.cons (.var (.succ .zero)) .nil)

theorem repeated_ordinary_at_different_depths :
    smatchA (emptyMAcc : MAcc signature declarations [a]) repeatedOrdinaryDepths
      (.cons constant (.cons constant .nil)) =
      some { (emptyMAcc : MAcc signature declarations [a]) with
        vars := updatePSub emptyPSub .zero constant } := by
  unfold repeatedOrdinaryDepths
  rw [smatchA_cons (S := signature)]
  rw [smatchAtT.eq_def (S := signature)]
  dsimp [splitVar, emptyMAcc, emptyPSub, strengthenT, strengthenA, constant]
  rw [smatchA_cons (S := signature)]
  rw [smatchAtT.eq_def (S := signature)]
  dsimp only
  unfold splitVar
  unfold splitVar
  simp [strengthenT, strengthenA, updatePSub_self, smatchA, smatchAtA_nil]

theorem repeated_ordinary_rejects_capture :
    smatchA (emptyMAcc : MAcc signature declarations [a]) repeatedOrdinaryDepths
      (.cons constant (.cons (.var .zero) .nil)) = none := by
  unfold repeatedOrdinaryDepths
  rw [smatchA_cons (S := signature)]
  rw [smatchAtT.eq_def (S := signature)]
  dsimp [splitVar, emptyMAcc, emptyPSub, strengthenT, strengthenA, constant]
  rw [smatchA_cons (S := signature)]
  rw [smatchAtT.eq_def (S := signature)]
  rfl

/-- The profile is checked on the nested pattern without reference to a target. -/
theorem nested_pattern_supported :
    MatchingSupportedT [] nestedPattern := by
  unfold nestedPattern
  rw [MatchingSupportedT.eq_def (S := signature)]
  dsimp only
  rw [MatchingSupportedA.eq_def (S := signature)]
  dsimp only [castTermCtx]
  constructor
  · rw [MatchingSupportedT.eq_def (S := signature)]
    dsimp only
    rw [MatchingSupportedA.eq_def (S := signature)]
    dsimp only [castTermCtx]
    constructor
    · simp only [metaVar, rename]
      rw [MatchingSupportedT.eq_def (S := signature)]
      dsimp only
      refine ⟨renameArgs oldArgument (idArgs (S := signature) (M := declarations) [a]), ?_, ?_⟩
      · rfl
      · exact ⟨_, rfl⟩
    · rw [MatchingSupportedA.eq_def (S := signature)]
      trivial
  · rw [MatchingSupportedA.eq_def (S := signature)]
    trivial

def emptyClosing : Sub signature [] [] := fun _ impossible => nomatch impossible

theorem nested_completeness_retains_actual_assignment :
    ∃ acc', smatchT (emptyMAcc : MAcc signature declarations []) nestedPattern nestedTarget = some acc' ∧
      MExtends emptyClosing usesArgument acc' := by
  apply smatchT_complete emptyMAcc nestedPattern nestedTarget nested_pattern_supported
    emptyClosing usesArgument (MExtends.empty _ _)
  rw [nested_instantiation]
  rfl

theorem repeated_meta_pattern_supported :
    MatchingSupportedA [] repeatedMetaDepths := by
  unfold repeatedMetaDepths
  rw [MatchingSupportedA.eq_def (S := signature)]
  dsimp only [castTermCtx]
  constructor
  · simp only [metaVar]
    rw [MatchingSupportedT.eq_def (S := signature)]
    dsimp only
    exact ⟨idArgs (S := signature) (M := declarations) [a], rfl, _, rfl⟩
  · rw [MatchingSupportedA.eq_def (S := signature)]
    dsimp only [castTermCtx]
    constructor
    · simp only [metaVar, rename]
      rw [MatchingSupportedT.eq_def (S := signature)]
      dsimp only
      exact ⟨renameArgs oldArgument (idArgs (S := signature) (M := declarations) [a]), rfl, _, rfl⟩
    · rw [MatchingSupportedA.eq_def (S := signature)]
      trivial

theorem repeated_meta_completeness_retains_actual_assignment :
    ∃ acc', smatchA (emptyMAcc : MAcc signature declarations []) repeatedMetaDepths
      (.cons (.var .zero) (.cons (.var (.succ .zero)) .nil)) = some acc' ∧
        MExtends emptyClosing usesArgument acc' := by
  apply smatchA_complete emptyMAcc repeatedMetaDepths _ repeated_meta_pattern_supported
    emptyClosing usesArgument (MExtends.empty _ _)
  rw [repeated_meta_actual_instantiation]
  rfl

/-- Repeated dependency arguments are outside this injective profile, even
though the independent diagonal instantiation witness remains available. -/
theorem diagonal_pattern_not_supported :
    ¬ MatchingSupportedT (S := signature) (M := binaryDeclarations) (Γ := [a, b]) [a]
      (Term.op (.inr (.mk binaryIndex)) diagonalWithOrdinary) := by
  rw [MatchingSupportedT.eq_def (S := signature)]
  dsimp only
  rintro ⟨projected, projection, selected, recognized⟩
  have projectedEq : projected = diagonalArgs := by
    exact (Option.some.inj projection).symm
  subst projected
  have declined : recognizeVariableArguments (S := withMetas signature binaryDeclarations)
      (dependencies := [a, a]) diagonalArgs = none := rfl
  rw [declined] at recognized
  cases recognized

end Mettapedia.GSLT.LanguageDef.ScopedMatchingControls
