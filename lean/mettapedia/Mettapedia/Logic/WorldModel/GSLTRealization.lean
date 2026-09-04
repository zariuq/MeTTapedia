import Mettapedia.Logic.WorldModel.Basic
import Mettapedia.GSLT.Core.GSLT

/-!
# Exact GSLT realizations of world-model interfaces

A world-model realization separates a semantic world from its physical
carrier.  Revision and extraction must commute with the semantic operations.
An exact query GSLT then exposes extraction as behavior: every query has a
path to its semantic answer, and every covered terminal answer reflects that
same meaning.

This is coalgebraic operational structure.  It is deliberately distinct from
`CoGSLTLayer`, which is the existing base-indexed authored-extension
interface; a realization may later inhabit such a layer without identifying
the two notions.
-/

namespace Mettapedia.Logic.WorldModel.GSLTRealization

open Mettapedia.GSLT

set_option autoImplicit false

/-- A concrete carrier implementing an independently defined world model. -/
structure Realization (Semantic Concrete Query Value : Type)
    [WorldModel Semantic Query Value] where
  denote : Concrete → Semantic
  empty : Concrete
  revise : Concrete → Concrete → Concrete
  extract : Concrete → Query → Value
  empty_sound : denote empty = WorldModel.empty Query Value
  revise_sound : ∀ first second,
    denote (revise first second) =
      WorldModel.revise Query Value (denote first) (denote second)
  extract_sound : ∀ concrete query,
    extract concrete query = WorldModel.extract (denote concrete) query

/-- The concrete operations themselves form a minimal world model. -/
@[reducible] def Realization.toWorldModel
    {Semantic Concrete Query Value : Type}
    [WorldModel Semantic Query Value]
    (realization : Realization Semantic Concrete Query Value) :
    WorldModel Concrete Query Value where
  revise := realization.revise
  empty := realization.empty
  extract := realization.extract

/-- A representation refinement preserves semantic worlds and the authored
revision structure. -/
structure Refinement
    {Semantic Source Target Query Value : Type}
    [WorldModel Semantic Query Value]
    (source : Realization Semantic Source Query Value)
    (target : Realization Semantic Target Query Value) where
  map : Source → Target
  denote_commutes : ∀ state, target.denote (map state) = source.denote state
  map_empty : map source.empty = target.empty
  map_revise : ∀ first second,
    map (source.revise first second) =
      target.revise (map first) (map second)

/-- Extraction is forced to commute once both realizations have one semantic
authority. -/
theorem Refinement.extract_preserved
    {Semantic Source Target Query Value : Type}
    [WorldModel Semantic Query Value]
    {source : Realization Semantic Source Query Value}
    {target : Realization Semantic Target Query Value}
    (refinement : Refinement source target)
    (state : Source) (query : Query) :
    target.extract (refinement.map state) query = source.extract state query := by
  rw [target.extract_sound, source.extract_sound, refinement.denote_commutes]

/-- A query realization gives the world-model observer an exact operational
presentation.  `request` contains only the concrete state and query.  Answers
are reached by paths, are normal, reflect their semantic value, and cover all
normal forms reachable from a request. -/
structure ExactQueryGSLT
    {Semantic Concrete Query Value : Type}
    [WorldModel Semantic Query Value]
    (realization : Realization Semantic Concrete Query Value) where
  theory : GSLT
  request : Concrete → Query → theory.Term
  answer : Concrete → Value → theory.Term
  executePath : ∀ concrete query,
    theory.RewritePath (request concrete query)
      (answer concrete (realization.extract concrete query))
  answer_normal : ∀ concrete value,
    theory.IsNormalForm (answer concrete value)
  answer_reflect : ∀ concrete query value,
    theory.RewritePath (request concrete query) (answer concrete value) →
      value = realization.extract concrete query
  covered_normal : ∀ concrete query terminal,
    theory.RewritePath (request concrete query) terminal →
      theory.IsNormalForm terminal →
        ∃ value, terminal = answer concrete value

/-- A covered normal form is exactly the semantic world-model observation. -/
theorem ExactQueryGSLT.covered_terminal_exact
    {Semantic Concrete Query Value : Type}
    [WorldModel Semantic Query Value]
    {realization : Realization Semantic Concrete Query Value}
    (machine : ExactQueryGSLT realization)
    (concrete : Concrete) (query : Query) (terminal : machine.theory.Term)
    (path : machine.theory.RewritePath
      (machine.request concrete query) terminal)
    (normal : machine.theory.IsNormalForm terminal) :
    terminal = machine.answer concrete (realization.extract concrete query) := by
  obtain ⟨value, rfl⟩ := machine.covered_normal concrete query terminal path normal
  rw [machine.answer_reflect concrete query value path]

/-- Positive existence half of the exact behavioral contract. -/
theorem ExactQueryGSLT.semantic_answer_reachable
    {Semantic Concrete Query Value : Type}
    [WorldModel Semantic Query Value]
    {realization : Realization Semantic Concrete Query Value}
    (machine : ExactQueryGSLT realization)
    (concrete : Concrete) (query : Query) :
    Nonempty (machine.theory.RewritePath
        (machine.request concrete query)
        (machine.answer concrete (WorldModel.extract
          (realization.denote concrete) query))) := by
  rw [← realization.extract_sound]
  exact ⟨machine.executePath concrete query⟩

#print axioms Refinement.extract_preserved
#print axioms ExactQueryGSLT.covered_terminal_exact
#print axioms ExactQueryGSLT.semantic_answer_reachable

end Mettapedia.Logic.WorldModel.GSLTRealization
