import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryProviderBuilt

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

/-- A rigid pattern is its own parallel-contents block: splicing leaves it
alone and unit filtering keeps it. -/
theorem claude_parallelContents_singleton_of_rigid
    (declaration : ReflectivePresentationDecl) {pattern : Pattern}
    (notUnit : pattern ≠ .apply declaration.parallelUnitConstructor [])
    (notParallel : ∀ nested,
      pattern ≠ .collection declaration.parallelCollection nested none) :
    parallelContents declaration [pattern] = [pattern] := by
  unfold parallelContents
  rw [List.flatMap_cons, List.flatMap_nil, List.append_nil,
    parallelSplice_eq_singleton_of_not_parallel declaration pattern notParallel]
  simp [notUnit]

/-- **Two rigid contributors cannot survive a singleton collapse.**

Each contributes exactly one block to the spliced contents, so the contents
list has length at least two — but a singleton collapse pins it at one. -/
theorem claude_two_rigid_contributors_absurd
    (declaration : ReflectivePresentationDecl) {result : Pattern}
    (notUnit : result ≠ .apply declaration.parallelUnitConstructor [])
    (notParallel : ∀ nested,
      result ≠ .collection declaration.parallelCollection nested none)
    {before middle after : List Pattern} {first second : Pattern}
    (firstCanon : canonicalize declaration first = result)
    (secondCanon : canonicalize declaration second = result)
    (contentsEq : parallelContents declaration
        ((before ++ first :: middle ++ second :: after).map
          (canonicalize declaration)) = [result]) :
    False := by
  have block := claude_parallelContents_singleton_of_rigid declaration notUnit
    notParallel
  have expand : (before ++ first :: middle ++ second :: after).map
      (canonicalize declaration) =
      before.map (canonicalize declaration) ++ [result] ++
        (middle.map (canonicalize declaration) ++ [result] ++
          after.map (canonicalize declaration)) := by
    simp [firstCanon, secondCanon]
  rw [expand] at contentsEq
  rw [parallelContents_append, parallelContents_append,
    parallelContents_append, parallelContents_append, block] at contentsEq
  have lengths := congrArg List.length contentsEq
  simp only [List.length_append, List.length_cons, List.length_nil] at lengths
  omega

/-- **The residual of GAP B'-a, closed.**

Two distinct elements of a collapsing bare parallel cannot both canonicalize
to the surviving singleton: split the element list at each of them and the
spliced contents carries two blocks where the collapse allows one. -/
theorem claude_sibling_unit_residual
    (declaration : ReflectivePresentationDecl) {result : Pattern}
    (notUnit : result ≠ .apply declaration.parallelUnitConstructor [])
    (notParallel : ∀ nested,
      result ≠ .collection declaration.parallelCollection nested none)
    {elements pre post : List Pattern} {active other : Pattern}
    (elementsSplit : elements = pre ++ other :: post)
    (activeInContexts : active ∈ pre ∨ active ∈ post)
    (activeCanon : canonicalize declaration active = result)
    (otherResult : canonicalize declaration other = result)
    (contentsEq : parallelContents declaration
        (elements.map (canonicalize declaration)) = [result]) :
    False := by
  subst elementsSplit
  rcases activeInContexts with activeInPre | activeInPost
  · obtain ⟨beforeActive, afterActive, preSplit⟩ :=
      List.mem_iff_append.mp activeInPre
    subst preSplit
    refine claude_two_rigid_contributors_absurd declaration notUnit notParallel
      (before := beforeActive) (first := active)
      (middle := afterActive) (second := other) (after := post)
      activeCanon otherResult ?_
    simpa using contentsEq
  · obtain ⟨beforeActive, afterActive, postSplit⟩ :=
      List.mem_iff_append.mp activeInPost
    subst postSplit
    refine claude_two_rigid_contributors_absurd declaration notUnit notParallel
      (before := pre) (first := other)
      (middle := beforeActive) (second := active) (after := afterActive)
      otherResult activeCanon ?_
    simpa using contentsEq

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
