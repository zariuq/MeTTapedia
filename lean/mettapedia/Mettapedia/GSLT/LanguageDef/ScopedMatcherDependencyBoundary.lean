import Mettapedia.GSLT.LanguageDef.MetaDependencyBoundaryControls
import Mettapedia.OSLF.Syntax.ScopedMatching

/-!
# The scoped matcher's contextual-dependency boundary

All schemas and targets use the existing LanguageDef-derived signature.
Actual matching results are compared with actual instantiation witnesses.
These controls exercise whole-slot, subset and permuted dependencies, while
including recursive rigid operators beneath accumulated binders.
-/

namespace Mettapedia.GSLT.LanguageDef.ScopedMatcherDependencyBoundary

open Mettapedia.OSLF.Binding Mettapedia.OSLF.MeTTaIL.Syntax
open BindingSyntax MetaDependencyControls
open WellSorted.OccurrenceControls (a)

set_option autoImplicit false

/-- The matcher is parameterized by equality on base operators. These controls
reason about that algorithm with classical equality; they do not supply a
new executable operator-equality implementation. -/
noncomputable local instance operatorEquality (sort : signature.Srt) :
    DecidableEq (signature.Op sort) := Classical.decEq _

def prefixPattern : Term (withMetas signature declarations) [] (.arrow a a) :=
  .op (.inl (.lambda a a)) (.cons (metaVar dependentIndex) .nil)

def identityTarget : Term signature [] (.arrow a a) :=
  .op (.lambda a a) (.cons (.var .zero) .nil)

def subsetPattern : Term (withMetas signature declarations) []
    (.arrow (.multiBinder a) a) :=
  .op (.inl (.multiLambda a a 2))
    (.cons (rename oldArgument (metaVar dependentIndex)) .nil)

def subsetTarget : Term signature [] (.arrow (.multiBinder a) a) :=
  .op (.multiLambda a a 2) (.cons (.var (.succ .zero)) .nil)

abbrev binaryDeclarations : List (MetaArity signature) := [([a, a], a)]
abbrev binaryIndex : Fin binaryDeclarations.length := ⟨0, by decide⟩

def firstBody : (i : Fin binaryDeclarations.length) →
    Term signature (binaryDeclarations.get i).1 (binaryDeclarations.get i).2 := by
  intro i
  exact Fin.cases (.var .zero) (fun impossible => Fin.elim0 impossible) i

def swapArguments : Ren signature [a, a] [a, a] := fun _ position => by
  cases position with
  | zero => exact .succ .zero
  | succ inner =>
      cases inner with
      | zero => exact .zero
      | succ impossible => exact nomatch impossible

def permutedPattern : Term (withMetas signature binaryDeclarations) []
    (.arrow (.multiBinder a) a) :=
  .op (.inl (.multiLambda a a 2))
    (.cons (rename swapArguments (metaVar binaryIndex)) .nil)

def nestedPattern : Term (withMetas signature declarations) [] (.arrow a (.arrow a a)) :=
  .op (.inl (.lambda a (.arrow a a)))
    (.cons (.op (.inl (.lambda a a))
      (.cons (rename oldArgument (metaVar dependentIndex)) .nil)) .nil)

def nestedTarget : Term signature [] (.arrow a (.arrow a a)) :=
  .op (.lambda a (.arrow a a))
    (.cons (.op (.lambda a a) (.cons (.var (.succ .zero)) .nil)) .nil)

/-- The current whole-slot prefix solver genuinely records a body. -/
theorem prefix_match_succeeds :
    (smatchT (emptyMAcc : MAcc signature declarations []) prefixPattern identityTarget).isSome =
      true := by
  unfold smatchT prefixPattern identityTarget
  rw [smatchAtT.eq_def (S := signature)]
  simp only [↓reduceDIte]
  rw [smatchAtA.eq_def (S := signature)]
  simp only [castTermCtx]
  simp only [metaVar]
  rw [smatchAtT.eq_def (S := signature)]
  change (smatchAtA [] (setMeta (emptyMAcc : MAcc signature declarations []) dependentIndex (.var .zero)) .nil .nil).isSome = true
  rw [smatchAtA.eq_def (S := signature)]
  rfl

theorem prefix_instantiation : instantiate usesArgument prefixPattern = identityTarget := rfl

/-- Strict subsets of the slot's bound variables now recover their bodies. -/
theorem subset_match_succeeds :
    (smatchT (emptyMAcc : MAcc signature declarations []) subsetPattern subsetTarget).isSome = true := by
  unfold smatchT subsetPattern subsetTarget
  rw [smatchAtT.eq_def (S := signature)]
  simp only [↓reduceDIte]
  rw [smatchAtA.eq_def (S := signature)]
  simp only [castTermCtx]
  simp only [metaVar, rename]
  rw [smatchAtT.eq_def (S := signature)]
  change (smatchAtA [] (setMeta (emptyMAcc : MAcc signature declarations []) dependentIndex (.var .zero)) .nil .nil).isSome = true
  rw [smatchAtA.eq_def (S := signature)]
  rfl

theorem subset_instantiation : instantiate usesArgument subsetPattern = subsetTarget := rfl

/-- A typed injective permutation is accepted without reordering its body. -/
theorem permuted_match_succeeds :
    (smatchT (emptyMAcc : MAcc signature binaryDeclarations []) permutedPattern subsetTarget).isSome =
      true := by
  unfold smatchT permutedPattern subsetTarget
  rw [smatchAtT.eq_def (S := signature)]
  simp only [↓reduceDIte]
  rw [smatchAtA.eq_def (S := signature)]
  simp only [castTermCtx]
  simp only [metaVar, rename]
  rw [smatchAtT.eq_def (S := signature)]
  change (smatchAtA [] (setMeta (emptyMAcc : MAcc signature binaryDeclarations []) binaryIndex (.var .zero)) .nil .nil).isSome = true
  rw [smatchAtA.eq_def (S := signature)]
  rfl

theorem permuted_instantiation : instantiate firstBody permutedPattern = subsetTarget := rfl

/-- Rigid nested operators recurse under all accumulated binders. -/
theorem nested_match_succeeds :
    (smatchT (emptyMAcc : MAcc signature declarations []) nestedPattern nestedTarget).isSome = true := by
  unfold smatchT nestedPattern nestedTarget
  rw [smatchAtT.eq_def (S := signature)]
  simp only [↓reduceDIte]
  rw [smatchAtA.eq_def (S := signature)]
  simp only [castTermCtx]
  rw [smatchAtT.eq_def (S := signature)]
  simp only [↓reduceDIte]
  rw [smatchAtA.eq_def (S := signature)]
  simp only [castTermCtx]
  simp only [metaVar, rename]
  rw [smatchAtT.eq_def (S := signature)]
  dsimp only
  have recovered : recoverBoundVariableBody (S := signature) (M := declarations) (bs := [a, a]) (Γ := [])
      (renameArgs oldArgument (idArgs (S := signature) (M := declarations) [a]))
      (.var (.succ .zero) : Term signature ([a, a] ++ []) a) =
        some (.var .zero) := rfl
  dsimp [declarations, dependentIndex] at recovered ⊢
  rw [recovered]
  dsimp only [emptyMAcc]
  rw [smatchAtA.eq_def (S := signature)]
  dsimp only
  rw [smatchAtA.eq_def (S := signature)]
  rfl

theorem nested_instantiation : instantiate usesArgument nestedPattern = nestedTarget := rfl

/-- Both matching and actual instantiation agree on this subset case. -/
theorem subset_matching_and_instantiation :
    (∃ body : (i : Fin declarations.length) →
        Term signature (declarations.get i).1 (declarations.get i).2,
      instantiate body subsetPattern = subsetTarget) ∧
      (smatchT (emptyMAcc : MAcc signature declarations []) subsetPattern subsetTarget).isSome = true :=
  ⟨⟨usesArgument, subset_instantiation⟩, subset_match_succeeds⟩

theorem permuted_matching_and_instantiation :
    (∃ body : (i : Fin binaryDeclarations.length) →
        Term signature (binaryDeclarations.get i).1 (binaryDeclarations.get i).2,
      instantiate body permutedPattern = subsetTarget) ∧
      (smatchT (emptyMAcc : MAcc signature binaryDeclarations []) permutedPattern subsetTarget).isSome = true :=
  ⟨⟨firstBody, permuted_instantiation⟩, permuted_match_succeeds⟩

theorem nested_matching_and_instantiation :
    (∃ body : (i : Fin declarations.length) →
        Term signature (declarations.get i).1 (declarations.get i).2,
      instantiate body nestedPattern = nestedTarget) ∧
      (smatchT (emptyMAcc : MAcc signature declarations []) nestedPattern nestedTarget).isSome = true :=
  ⟨⟨usesArgument, nested_instantiation⟩, nested_match_succeeds⟩

def wrongTarget : Term signature [] (.arrow a a) :=
  .op (.lambda a a) (.cons constant .nil)

theorem rigid_wrong_target_declined :
    smatchT (emptyMAcc : MAcc signature declarations []) (embed identityTarget) wrongTarget = none := by
  unfold smatchT identityTarget wrongTarget
  simp only [embed, embedArgs]
  rw [smatchAtT.eq_def (S := signature)]
  simp only [↓reduceDIte]
  rw [smatchAtA.eq_def (S := signature)]
  simp only [castTermCtx]
  rw [smatchAtT.eq_def (S := signature)]
  unfold splitVar
  simp [constant]

theorem rigid_wrong_target_has_no_instantiation :
    ¬ ∃ body : (i : Fin declarations.length) →
        Term signature (declarations.get i).1 (declarations.get i).2,
      instantiate body (embed identityTarget) = wrongTarget := by
  rintro ⟨body, equality⟩
  rw [instantiate_embed] at equality
  have erased := congrArg erase equality
  cases erased

def nestedCapturedTarget : Term signature [] (.arrow a (.arrow a a)) :=
  .op (.lambda a (.arrow a a))
    (.cons (.op (.lambda a a) (.cons (.var .zero) .nil)) .nil)

/-- Recursive matching does not turn the newest binder into an old dependency. -/
theorem nested_new_binder_capture_declined :
    smatchT (emptyMAcc : MAcc signature declarations []) nestedPattern nestedCapturedTarget = none := by
  unfold smatchT nestedPattern nestedCapturedTarget
  rw [smatchAtT.eq_def (S := signature)]
  simp only [↓reduceDIte]
  rw [smatchAtA.eq_def (S := signature)]
  simp only [castTermCtx]
  rw [smatchAtT.eq_def (S := signature)]
  simp only [↓reduceDIte]
  rw [smatchAtA.eq_def (S := signature)]
  simp only [castTermCtx, metaVar, rename]
  rw [smatchAtT.eq_def (S := signature)]
  dsimp only
  have rejected : recoverBoundVariableBody (S := signature) (M := declarations)
      (bs := [a, a]) (Γ := [])
      (renameArgs oldArgument (idArgs (S := signature) (M := declarations) [a]))
      (.var .zero : Term signature ([a, a] ++ []) a) = none := rfl
  dsimp [declarations, dependentIndex] at rejected ⊢
  rw [rejected]

theorem nested_argument_instantiation_does_not_capture :
    instantiate usesArgument nestedPattern ≠ nestedCapturedTarget := by
  rw [nested_instantiation]
  intro equality
  have mismatch := congrArg erase equality
  cases mismatch

end Mettapedia.GSLT.LanguageDef.ScopedMatcherDependencyBoundary
