import Mettapedia.Languages.TransitionSystem.Contexts

/-!
# Extending a transition table at one state

A larger table lists the states and moves of a smaller one.  Its inclusion is
a map of theories and preserves transitions.  It does not reflect them when
the larger table adds a move out of a state of the smaller one.

The inclusion is nevertheless a morphism of theories, for every probe, when
the added moves out of old states all leave one state, the pivot, and the
pivot is recognised by its successors in the smaller table: it has a
successor that can move and one that cannot, and it is the only state that
does.  Then whatever a probe relates to the pivot is the pivot itself, unless
the probe has stopped observing, and in both cases the added move is
answered.

So bisimilarity is preserved along a map that adds behaviour.  What such a
map does to traces is a separate matter, taken up where a pivot extension is
exhibited.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.TransitionSystem

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.Contexts
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep

namespace Table

/-- The state can move. -/
def Steppable (table : Table) (label : String) : Prop :=
  ∃ move ∈ table.moves, move.2.1 = label

instance (table : Table) (label : String) : Decidable (table.Steppable label) := by
  unfold Steppable
  infer_instance

/-- The larger table extends the smaller one at a pivot. -/
structure PivotExtension (small large : Table) (pivot : String) : Prop where
  /-- The larger table lists the states of the smaller one... -/
  states : ∀ label ∈ small.states, label ∈ large.states
  /-- ...and its moves. -/
  moves : ∀ move ∈ small.moves, move ∈ large.moves
  /-- A move of the larger table out of a state of the smaller one is a move
  of the smaller one, or leaves the pivot. -/
  conservative : ∀ move ∈ large.moves, move.2.1 ∈ small.states →
    move ∈ small.moves ∨ move.2.1 = pivot
  /-- In the smaller table the pivot has a successor that can move... -/
  toSteppable : ∃ move ∈ small.moves, move.2.1 = pivot ∧ small.Steppable move.2.2
  /-- ...and one that cannot... -/
  toStuck : ∃ move ∈ small.moves, move.2.1 = pivot ∧ ¬ small.Steppable move.2.2
  /-- ...and it is the only state with both. -/
  unique : ∀ first ∈ small.moves, ∀ second ∈ small.moves, first.2.1 = second.2.1 →
    small.Steppable first.2.2 → ¬ small.Steppable second.2.2 → first.2.1 = pivot

variable {small large : Table} {pivot : String}
  (smallFormed : small.WellFormed) (largeFormed : large.WellFormed)
  (extension : PivotExtension small large pivot)

/-- The inclusion of the smaller table, as a map of declarations. -/
def inclusion : StructuralMorphism (validated smallFormed) (validated largeFormed) where
  symbols := LanguageDefSymbolMap.id
  mapsTypes := by
    intro declaration membership
    rw [mapTypeDecl_id]
    exact membership
  mapsTerms := by
    intro rule membership
    rw [mapGrammarRule_id]
    obtain ⟨label, listed, rfl⟩ := List.mem_map.mp membership
    exact List.mem_map_of_mem (extension.states label listed)
  mapsEquations := by
    intro equation membership
    cases membership
  mapsRewrites := by
    intro rewrite membership
    rw [mapRewriteRule_id]
    obtain ⟨move, moveMember, rfl⟩ := List.mem_map.mp membership
    exact List.mem_map_of_mem (extension.moves move moveMember)

/-- The inclusion as a map of theories. -/
def inclusionMap : ContextMap (theory smallFormed) (theory largeFormed) :=
  structuralContextMap base (inclusion smallFormed largeFormed extension)
    (preservesEquations_of_equationFree base _ small.isEquationFree)

/-- The image of a term has the pattern of the term. -/
theorem inclusionMap_term_val {interface : Interface} (term : Term small.language interface) :
    ((inclusionMap smallFormed largeFormed extension).term term).1 = term.1 :=
  mapPattern_id term.1

/-- Placing the image of a term in the image of a label gives the pattern of
the placed term. -/
theorem apply_image {origin result : Interface}
    (label : (theory smallFormed).Label origin result) (term : Term small.language origin) :
    ((theory largeFormed).apply ((inclusionMap smallFormed largeFormed extension).context label)
        ((inclusionMap smallFormed largeFormed extension).term term)).1 =
      ((theory smallFormed).apply label term).1 := by
  have filled := congrArg Subtype.val
    (Term.map_fill (inclusion smallFormed largeFormed extension) label fun _ => term)
  exact filled.symm.trans (mapPattern_id _)

/-- **The inclusion preserves transitions.** -/
theorem inclusionMap_preservesTransitions :
    (inclusionMap smallFormed largeFormed extension).PreservesTransitions :=
  structuralContextMap_preservesTransitions base (inclusion smallFormed largeFormed extension)
    (preservesEquations_of_equationFree base _ small.isEquationFree)
    (preservesSteps_of_equationFree base _ small.isEquationFree large.isEquationFree (by
      intro pattern next step
      change Step base large.language (mapPattern LanguageDefSymbolMap.id pattern)
        (mapPattern LanguageDefSymbolMap.id next)
      rw [mapPattern_id, mapPattern_id]
      obtain ⟨move, moveMember, rfl, rfl⟩ := small.step_iff.mp step
      exact large.step_iff.mpr ⟨move, extension.moves move moveMember, rfl, rfl⟩))

/-! ## The relation that the inclusion carries a bisimulation to -/

/-- No carried observer out of the index labels a transition: the probe has
stopped observing there. -/
def Inert (probe : (theory smallFormed).Probe) (index : probe.Index) : Prop :=
  ∀ {target : probe.Index} (observer : probe.Observer index target)
    (term : (theory largeFormed).Term
      ((inclusionMap smallFormed largeFormed extension).interface (probe.interface index)))
    (next : (theory largeFormed).Term
      ((inclusionMap smallFormed largeFormed extension).interface (probe.interface target))),
    ¬ (theory largeFormed).Transition term
      (((inclusionMap smallFormed largeFormed extension).push probe).label observer) next

/-- Two terms of the larger table are related at an index when they are
equal, or are the images of two terms that the probe finds bisimilar, or the
probe has stopped observing at the index. -/
def Related (probe : (theory smallFormed).Probe) (index : probe.Index)
    (first second : (theory largeFormed).Term
      ((inclusionMap smallFormed largeFormed extension).interface (probe.interface index))) :
    Prop :=
  first = second ∨
    (∃ left right : Term small.language (probe.interface index), probe.Bisimilar left right ∧
      first = (inclusionMap smallFormed largeFormed extension).term left ∧
      second = (inclusionMap smallFormed largeFormed extension).term right) ∨
    Inert smallFormed largeFormed extension probe index

theorem related_symm {probe : (theory smallFormed).Probe} {index : probe.Index}
    {first second : (theory largeFormed).Term
      ((inclusionMap smallFormed largeFormed extension).interface (probe.interface index))}
    (related : Related smallFormed largeFormed extension probe index first second) :
    Related smallFormed largeFormed extension probe index second first := by
  rcases related with same | ⟨left, right, bisimilar, rfl, rfl⟩ | inert
  · exact Or.inl same.symm
  · exact Or.inr (Or.inl ⟨right, left, ContextTheory.Probe.bisimilar_symm bisimilar, rfl, rfl⟩)
  · exact Or.inr (Or.inr inert)

/-- **A transition of the first of two related terms is answered by the
second.** -/
theorem related_forward {probe : (theory smallFormed).Probe} {source target : probe.Index}
    {first second : (theory largeFormed).Term
      ((inclusionMap smallFormed largeFormed extension).interface (probe.interface source))}
    (related : Related smallFormed largeFormed extension probe source first second)
    (observer : probe.Observer source target)
    {next : (theory largeFormed).Term
      ((inclusionMap smallFormed largeFormed extension).interface (probe.interface target))}
    (transition : (theory largeFormed).Transition first
      (((inclusionMap smallFormed largeFormed extension).push probe).label observer) next) :
    ∃ answer, (theory largeFormed).Transition second
        (((inclusionMap smallFormed largeFormed extension).push probe).label observer) answer ∧
      Related smallFormed largeFormed extension probe target next answer := by
  rcases related with same | ⟨left, right, bisimilar, rfl, rfl⟩ | inert
  · subst same
    exact ⟨next, transition, Or.inl rfl⟩
  · obtain ⟨relation, ⟨forward, backward⟩, pair⟩ := bisimilar
    obtain ⟨identityLarge, move, moveMember, sourceShape, targetShape⟩ :=
      (transition_iff largeFormed _).mp transition
    have leftShape : left.1 = state move.2.1 :=
      (inclusionMap_term_val smallFormed largeFormed extension left).symm.trans sourceShape
    have placed : ((theory smallFormed).apply (probe.label observer) left).1 = state move.2.1 :=
      (apply_image smallFormed largeFormed extension (probe.label observer) left).symm.trans
        ((identityLarge _).trans sourceShape)
    have identitySmall := label_identity_of_state smallFormed (probe.label observer) placed
    obtain ⟨ofStates, sourceListed⟩ :=
      interface_of_state ((theory smallFormed).apply (probe.label observer) left) placed
    rcases extension.conservative move moveMember sourceListed with smallMove | atPivot
    · -- a move of the smaller table: the probe's own bisimulation answers it
      let reduct : Term small.language (probe.interface target) :=
        stateTerm ofStates (smallFormed.2.2 move smallMove).2
      have step : (theory smallFormed).Transition left (probe.label observer) reduct :=
        (transition_iff smallFormed _).mpr ⟨identitySmall, move, smallMove, leftShape, rfl⟩
      obtain ⟨answer, answerStep, answerRelated⟩ := forward pair observer step
      have same : next = (inclusionMap smallFormed largeFormed extension).term reduct :=
        Subtype.ext (targetShape.trans
          (inclusionMap_term_val smallFormed largeFormed extension reduct).symm)
      refine ⟨(inclusionMap smallFormed largeFormed extension).term answer,
        inclusionMap_preservesTransitions smallFormed largeFormed extension _ answerStep, ?_⟩
      rw [same]
      exact Or.inr (Or.inl ⟨reduct, answer, ⟨relation, ⟨forward, backward⟩, answerRelated⟩,
        rfl, rfl⟩)
    · -- a move out of the pivot
      obtain ⟨up, upMember, upSource, upSteppable⟩ := extension.toSteppable
      obtain ⟨down, downMember, downSource, downStuck⟩ := extension.toStuck
      have leftPivot : left.1 = state pivot := by rw [leftShape, atPivot]
      let upTerm : Term small.language (probe.interface target) :=
        stateTerm ofStates (smallFormed.2.2 up upMember).2
      let downTerm : Term small.language (probe.interface target) :=
        stateTerm ofStates (smallFormed.2.2 down downMember).2
      have upStep : (theory smallFormed).Transition left (probe.label observer) upTerm :=
        (transition_iff smallFormed _).mpr
          ⟨identitySmall, up, upMember, leftPivot.trans (by rw [upSource]), rfl⟩
      have downStep : (theory smallFormed).Transition left (probe.label observer) downTerm :=
        (transition_iff smallFormed _).mpr
          ⟨identitySmall, down, downMember, leftPivot.trans (by rw [downSource]), rfl⟩
      obtain ⟨upAnswer, upAnswerStep, upRelated⟩ := forward pair observer upStep
      obtain ⟨downAnswer, downAnswerStep, downRelated⟩ := forward pair observer downStep
      by_cases inert : Inert smallFormed largeFormed extension probe target
      · -- the probe has stopped observing: any move answers
        exact ⟨(inclusionMap smallFormed largeFormed extension).term upAnswer,
          inclusionMap_preservesTransitions smallFormed largeFormed extension _ upAnswerStep,
          Or.inr (Or.inr inert)⟩
      · -- the probe still observes: the second term is the pivot too
        obtain ⟨final, second, witness, witnessNext, witnessStep⟩ :
            ∃ (final : probe.Index) (second : probe.Observer target final)
              (witness : (theory largeFormed).Term
                ((inclusionMap smallFormed largeFormed extension).interface
                  (probe.interface target)))
              (witnessNext : (theory largeFormed).Term
                ((inclusionMap smallFormed largeFormed extension).interface
                  (probe.interface final))),
              (theory largeFormed).Transition witness
                (((inclusionMap smallFormed largeFormed extension).push probe).label second)
                witnessNext := by
          by_contra none
          exact inert fun {final} second witness witnessNext witnessStep =>
            none ⟨final, second, witness, witnessNext, witnessStep⟩
        obtain ⟨identityFinalLarge, -⟩ := (transition_iff largeFormed _).mp witnessStep
        have identityFinal : ∀ term : Term small.language (probe.interface target),
            ((theory smallFormed).apply (probe.label second) term).1 = term.1 := by
          intro term
          exact (apply_image smallFormed largeFormed extension (probe.label second) term).symm.trans
            ((identityFinalLarge _).trans
              (inclusionMap_term_val smallFormed largeFormed extension term))
        have finalStates : (probe.interface final).type = .base "Proc" :=
          (interface_of_state ((theory smallFormed).apply (probe.label second) upTerm)
            (identityFinal upTerm)).1
        -- the answer to the move up can move
        obtain ⟨further, furtherMember, furtherSource⟩ := upSteppable
        let furtherTerm : Term small.language (probe.interface final) :=
          stateTerm finalStates (smallFormed.2.2 further furtherMember).2
        have furtherStep : (theory smallFormed).Transition upTerm (probe.label second)
            furtherTerm :=
          (transition_iff smallFormed _).mpr
            ⟨identityFinal, further, furtherMember, (congrArg state furtherSource).symm, rfl⟩
        obtain ⟨_, upAnswerMoves, -⟩ := forward upRelated second furtherStep
        obtain ⟨-, upMove, upMoveMember, upAnswerShape, -⟩ :=
          (transition_iff smallFormed _).mp upAnswerMoves
        -- the answer to the move down cannot
        have downAnswerStuck : ∀ candidate ∈ small.moves,
            downAnswer.1 ≠ state candidate.2.1 := by
          intro candidate candidateMember shape
          let reached : Term small.language (probe.interface final) :=
            stateTerm finalStates (smallFormed.2.2 candidate candidateMember).2
          have moves : (theory smallFormed).Transition downAnswer (probe.label second) reached :=
            (transition_iff smallFormed _).mpr
              ⟨identityFinal, candidate, candidateMember, shape, rfl⟩
          obtain ⟨_, downMoves, -⟩ := backward downRelated second moves
          obtain ⟨-, other, otherMember, otherShape, -⟩ :=
            (transition_iff smallFormed _).mp downMoves
          exact downStuck ⟨other, otherMember, (state_injective otherShape).symm⟩
        -- so the second term has a successor that moves and one that does not
        obtain ⟨-, firstMove, firstMember, rightShape, upAnswerTarget⟩ :=
          (transition_iff smallFormed _).mp upAnswerStep
        obtain ⟨-, secondMove, secondMember, rightShape', downAnswerTarget⟩ :=
          (transition_iff smallFormed _).mp downAnswerStep
        have sameSource : firstMove.2.1 = secondMove.2.1 :=
          state_injective (rightShape.symm.trans rightShape')
        have firstSteppable : small.Steppable firstMove.2.2 :=
          ⟨upMove, upMoveMember, state_injective (upAnswerShape.symm.trans upAnswerTarget)⟩
        have secondStuck : ¬ small.Steppable secondMove.2.2 := by
          rintro ⟨candidate, candidateMember, candidateSource⟩
          exact downAnswerStuck candidate candidateMember
            (downAnswerTarget.trans (by rw [candidateSource]))
        have rightPivot : firstMove.2.1 = pivot :=
          extension.unique firstMove firstMember secondMove secondMember sameSource
            firstSteppable secondStuck
        have answered : (theory largeFormed).Transition
            ((inclusionMap smallFormed largeFormed extension).term right)
            (((inclusionMap smallFormed largeFormed extension).push probe).label observer) next :=
          (transition_iff largeFormed _).mpr ⟨identityLarge, move, moveMember,
            (inclusionMap_term_val smallFormed largeFormed extension right).trans
              (rightShape.trans (by rw [rightPivot, atPivot])), targetShape⟩
        exact ⟨next, answered, Or.inl rfl⟩
  · exact absurd transition (inert observer _ _)

/-- The relation is a bisimulation as the carried probe sees it. -/
theorem related_isBisimulation (probe : (theory smallFormed).Probe) :
    ((inclusionMap smallFormed largeFormed extension).push probe).IsBisimulation
      (Related smallFormed largeFormed extension probe) :=
  ⟨fun related _ observer _ transition =>
      related_forward smallFormed largeFormed extension related observer transition,
    fun related _ observer _ transition => by
      obtain ⟨answer, step, answerRelated⟩ := related_forward smallFormed largeFormed extension
        (related_symm smallFormed largeFormed extension related) observer transition
      exact ⟨answer, step, related_symm smallFormed largeFormed extension answerRelated⟩⟩

/-- **The inclusion into a pivot extension is a morphism of theories**: what
every probe of the smaller table finds bisimilar, the carried probe finds
bisimilar in the larger table, although the larger table has moves the
smaller one lacks. -/
def inclusionMorphism : ContextMorphism (theory smallFormed) (theory largeFormed) where
  toContextMap := inclusionMap smallFormed largeFormed extension
  transitions := inclusionMap_preservesTransitions smallFormed largeFormed extension
  preserves := fun probe _ left right bisimilar =>
    ⟨Related smallFormed largeFormed extension probe,
      related_isBisimulation smallFormed largeFormed extension probe,
      Or.inr (Or.inl ⟨left, right, bisimilar, rfl, rfl⟩)⟩

end Table

end Mettapedia.Languages.TransitionSystem
