import Mettapedia.GSLT.LanguageDef.Gauthier.CanonicalPatternSchema
import Mettapedia.GSLT.LanguageDef.Gauthier.AlignmentEvidence

/-!
# Causal source support for role-indexed program patterns

Pattern matching is ordinary first-order instantiation.  Evidence support is
not the number of matching rows or binding occurrences: it is the finite set
of causal source roots represented by certified matches.  This module reuses
the established `MoreGeneral`, lineage-certificate, and source-root semantics.
-/

namespace Mettapedia.GSLT.LanguageDef.GauthierPatternSupport

open Mettapedia.GSLT.LanguageDef.GauthierE1
open Mettapedia.GSLT.LanguageDef.GauthierRoleAntiUnification
open Mettapedia.GSLT.LanguageDef.GauthierAlignmentEvidence
open Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery

/-- A concrete program matches a pattern when one total hole substitution
instantiates the entire pattern to that program.  Repeated holes therefore
must receive the same concrete subtree. -/
def Matches (pattern : Pattern) (program : Prog) : Prop :=
  ∃ substitution : TermSubstitution,
    instantiate substitution pattern = program

mutual

/-- Term instantiation after pattern instantiation is substitution
composition. -/
theorem instantiate_instantiatePattern
    (termSubstitution : TermSubstitution)
    (patternSubstitution : PatternSubstitution) (pattern : Pattern) :
    instantiate termSubstitution
        (instantiatePattern patternSubstitution pattern) =
      instantiate
        (fun key => instantiate termSubstitution (patternSubstitution key))
        pattern := by
  exact Pattern.rec
    (motive_1 := fun pattern =>
      instantiate termSubstitution
          (instantiatePattern patternSubstitution pattern) =
        instantiate
          (fun key => instantiate termSubstitution (patternSubstitution key))
          pattern)
    (motive_2 := fun patterns =>
      (patterns.map (instantiatePattern patternSubstitution)).map
          (instantiate termSubstitution) =
        patterns.map
          (instantiate
            (fun key => instantiate termSubstitution
              (patternSubstitution key))))
    (fun _ => by simp [instantiatePattern, instantiate])
    (fun _ _ childrenResult => by
      simpa [instantiatePattern, instantiate] using childrenResult)
    (by rfl)
    (fun _ _ headResult tailResult => by
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨headResult, tailResult⟩)
    pattern

end


/-- Both inputs of an LGG match the computed pattern. -/
theorem lgg_matches_left (sig : Signature σ) (role : HoleRole)
    (left right : Prog) : Matches (lgg sig role left right) left :=
  ⟨leftSubstitution, instantiate_left_lgg sig role left right⟩

/-- Both inputs of an LGG match the computed pattern. -/
theorem lgg_matches_right (sig : Signature σ) (role : HoleRole)
    (left right : Prog) : Matches (lgg sig role left right) right :=
  ⟨rightSubstitution, instantiate_right_lgg sig role left right⟩

/-- Matching is monotone toward more general patterns. -/
theorem matches_mono_moreGeneral {general specific : Pattern}
    {program : Prog} (order : MoreGeneral general specific)
    (matching : Matches specific program) : Matches general program := by
  obtain ⟨patternSubstitution, specializes⟩ := order
  obtain ⟨termSubstitution, realizes⟩ := matching
  refine ⟨fun key =>
    instantiate termSubstitution (patternSubstitution key), ?_⟩
  rw [← instantiate_instantiatePattern, specializes, realizes]

/-- Reusing one hole in two positions is a real equality constraint. -/
theorem repeated_hole_rejects_distinct_children :
    ¬ Matches (.node 3 [.hole repeatedKey, .hole repeatedKey])
      (.node 3 [zero, one]) := by
  rintro ⟨substitution, equal⟩
  simp only [instantiate, Prog.node.injEq, true_and] at equal
  have first := congrArg (fun children => children[0]?) equal
  have second := congrArg (fun children => children[1]?) equal
  simp only [List.getElem?_cons_zero, List.getElem?_cons_succ] at first second
  have zero_eq_one : zero = one := Option.some.inj (first.symm.trans second)
  simp [zero, one] at zero_eq_one

/-! ## Source-root support -/

/-- An observed program with audit lineage, structural occurrence path, and
authenticated causal root. -/
structure ProgramObservation where
  program : Prog
  sourceLineage : Nat
  structuralPath : List Nat
  sourceRoot : Nat

/-- A root supports a pattern in a corpus when at least one observation from
that root matches.  source-row multiplicity is deliberately existential. -/
def RootSupports (corpus : List ProgramObservation)
    (pattern : Pattern) (root : Nat) : Prop :=
  ∃ observation ∈ corpus,
    observation.sourceRoot = root ∧ Matches pattern observation.program

/-- Set-valued causal support of a pattern. -/
def supportSet (corpus : List ProgramObservation) (pattern : Pattern) :
    Set Nat :=
  { root | RootSupports corpus pattern root }

/-- Pattern specialization cannot create support.  Equivalently, support is
anti-monotone along the specialization order. -/
theorem supportSet_anti_mono {general specific : Pattern}
    (order : MoreGeneral general specific) (corpus : List ProgramObservation) :
    supportSet corpus specific ⊆ supportSet corpus general := by
  intro root supported
  obtain ⟨observation, in_corpus, root_eq, matching⟩ := supported
  exact ⟨observation, in_corpus, root_eq,
    matches_mono_moreGeneral order matching⟩

/-- A match certificate carries the substitution witness together with the
authenticated observation used for finite evidence accounting. -/
structure SourceMatch (pattern : Pattern) where
  observation : ProgramObservation
  matching : Matches pattern observation.program

/-- Finite causal support is the set of source roots, not the number of rows. -/
def supportRoots {pattern : Pattern} (matchingRows : List (SourceMatch pattern)) :
    Finset Nat :=
  (matchingRows.map fun matched => matched.observation.sourceRoot).toFinset

/-- The deliberately unsafe comparator counts every matching row. -/
def rawMatchCount {pattern : Pattern}
    (matchingRows : List (SourceMatch pattern)) : Nat := matchingRows.length

/-- Repeating an identical certified match cannot inflate causal support. -/
theorem supportRoots_duplicate {pattern : Pattern}
    (matched : SourceMatch pattern) (rest : List (SourceMatch pattern)) :
    supportRoots (matched :: matched :: rest) =
      supportRoots (matched :: rest) := by
  simp [supportRoots]

/-- Different source rows, paths, or descendant lineages from one root still
contribute one support unit. -/
theorem supportRoots_same_root {pattern : Pattern}
    (first second : SourceMatch pattern)
    (sameRoot : first.observation.sourceRoot =
      second.observation.sourceRoot) :
    supportRoots [first, second] = supportRoots [first] := by
  simp [supportRoots, sameRoot]

/-- In particular, two occurrences of one shared DAG source cannot inflate
support merely because their structural paths differ. -/
theorem shared_dag_occurrences_support_once {pattern : Pattern}
    (program : Prog) (matching : Matches pattern program)
    (sourceLineage sourceRoot : Nat) (firstPath secondPath : List Nat) :
    let first : SourceMatch pattern :=
      ⟨⟨program, sourceLineage, firstPath, sourceRoot⟩, matching⟩
    let second : SourceMatch pattern :=
      ⟨⟨program, sourceLineage, secondPath, sourceRoot⟩, matching⟩
    supportRoots [first, second] = supportRoots [first] := by
  simp [supportRoots]

/-- Build a source match whose causal root is supplied by the existing
lineage-manifest certificate. -/
def sourceMatchOfManifest {World Lineage : Type*}
    {graph : LineageDAG Nat World Lineage}
    (certificate : SourceClassCertificate graph)
    {pattern : Pattern} (program : Prog) (source : Nat)
    (structuralPath : List Nat) (matching : Matches pattern program) :
    SourceMatch pattern :=
  ⟨⟨program, source, structuralPath, certificate.classOf source⟩, matching⟩

/-- Descendant rows with a common ancestor share a manifest source class and
therefore contribute one support unit. -/
theorem common_ancestor_matches_support_once
    {World Lineage : Type*} {graph : LineageDAG Nat World Lineage}
    (certificate : SourceClassCertificate graph)
    {left right : Nat}
    (common : ∃ ancestor,
      graph.AncestorOrSelf ancestor left ∧
        graph.AncestorOrSelf ancestor right)
    {pattern : Pattern} (leftProgram rightProgram : Prog)
    (leftPath rightPath : List Nat)
    (leftMatches : Matches pattern leftProgram)
    (rightMatches : Matches pattern rightProgram) :
    supportRoots
        [sourceMatchOfManifest certificate leftProgram left leftPath leftMatches,
         sourceMatchOfManifest certificate rightProgram right rightPath rightMatches] =
      supportRoots
        [sourceMatchOfManifest certificate leftProgram left leftPath leftMatches] := by
  apply supportRoots_same_root
  exact certificate.commonAncestor_same common

/-- Genuinely independent roots add exactly one support unit each. -/
theorem independent_roots_add {pattern : Pattern}
    (first second : SourceMatch pattern)
    (different : first.observation.sourceRoot ≠
      second.observation.sourceRoot) :
    (supportRoots [first, second]).card = 2 := by
  simp [supportRoots, different]

/-! ## Raw-row inflation counterexample -/

def rootHolePattern : Pattern := .hole repeatedKey

def zeroRootMatch : SourceMatch rootHolePattern where
  observation := ⟨zero, 10, [0], 7⟩
  matching := by
    refine ⟨fun _ => zero, ?_⟩
    simp [rootHolePattern, instantiate]

def oneRootMatch : SourceMatch rootHolePattern where
  observation := ⟨one, 11, [1], 7⟩
  matching := by
    refine ⟨fun _ => one, ?_⟩
    simp [rootHolePattern, instantiate]

/-- Counting raw matching rows reports two while causal-root support correctly
reports one.  This is the minimal binding-multiplicity inflation witness. -/
theorem raw_match_count_inflates_same_root :
    rawMatchCount [zeroRootMatch, oneRootMatch] = 2 ∧
      (supportRoots [zeroRootMatch, oneRootMatch]).card = 1 := by
  constructor
  · rfl
  · simp [supportRoots, zeroRootMatch, oneRootMatch]

#print axioms instantiate_instantiatePattern
#print axioms lgg_matches_left
#print axioms lgg_matches_right
#print axioms matches_mono_moreGeneral
#print axioms repeated_hole_rejects_distinct_children
#print axioms supportSet_anti_mono
#print axioms supportRoots_duplicate
#print axioms supportRoots_same_root
#print axioms shared_dag_occurrences_support_once
#print axioms common_ancestor_matches_support_once
#print axioms independent_roots_add
#print axioms raw_match_count_inflates_same_root

end Mettapedia.GSLT.LanguageDef.GauthierPatternSupport
