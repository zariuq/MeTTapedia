import Mettapedia.GSLT.Contexts.TransitionProfile
import Mettapedia.Logic.Relation.Normalization

/-!
# What a hosting map carries back from the host

A hosting map preserves and reflects transitions and reflects the static
equivalence.  Three properties of the reduction of the host therefore hold of
the reduction of every theory it hosts.  Read the other way, each is an
obstruction: a theory without the property has no hosting map into a theory
with it.

* **Confluence up to the static equivalence** (`ConfluentUpTo`,
  `ContextMap.Hosting.confluentUpTo`).  A theory in which one term reduces to
  two normal terms that are apart is hosted by no confluent theory
  (`ContextMap.not_hosting_of_branch`).
* **Termination** (`Terminating`, `ContextMap.terminating_of_preserves`).
  Preserving transitions is enough.  A theory with a cyclic reduction has no
  transition-preserving map into a terminating theory
  (`ContextMap.not_preserves_of_cycle`).
* **Closure of reduction under contexts** (`ContextClosed`,
  `ContextMap.Hosting.contextClosed`).  A theory in which some context
  disables a step of its hole is hosted by no theory whose reduction is closed
  under contexts.

The properties are stated for one theory and for all its interfaces; nothing
is assumed about how the theory is presented.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT

open Mettapedia.Logic.Relation (IsNormal)

universe u

namespace ContextTheory

variable (theory : ContextTheory.{u})

/-- Reduction at one interface: finitely many steps. -/
abbrev Reaches {interface : theory.Interface} (term final : theory.Term interface) : Prop :=
  Relation.ReflTransGen (theory.rewrites (interface := interface)) term final

/-- **Confluence up to the static equivalence**: two reducts of one term
reduce to equivalent terms. -/
def ConfluentUpTo : Prop :=
  ∀ {interface : theory.Interface} (source left right : theory.Term interface),
    theory.Reaches source left → theory.Reaches source right →
      ∃ leftEnd rightEnd, theory.Reaches left leftEnd ∧ theory.Reaches right rightEnd ∧
        (theory.equations interface).r leftEnd rightEnd

/-- **Termination**: there is no infinite reduction sequence. -/
def Terminating : Prop :=
  ∀ interface : theory.Interface,
    WellFounded fun next term : theory.Term interface => theory.rewrites term next

/-- **Reduction is closed under contexts**: a step of the hole gives a
reduction of the whole, up to the static equivalence. -/
def ContextClosed : Prop :=
  ∀ {origin result : theory.Interface} (label : theory.Label origin result)
    {term next : theory.Term origin}, theory.rewrites term next →
      ∃ whole, theory.Reaches (theory.apply label term) whole ∧
        (theory.equations result).r whole (theory.apply label next)

end ContextTheory

/-- An accessible element is not related to itself. -/
theorem not_rel_self_of_acc {α : Type u} {relation : α → α → Prop} {element : α}
    (accessible : Acc relation element) : ¬ relation element element := by
  induction accessible with
  | intro element _ ih => exact fun cycle => ih element cycle cycle

namespace ContextMap

variable {source target : ContextTheory.{u}} (map : ContextMap source target)

/-- A map that preserves steps preserves reduction. -/
theorem reaches_of_preserves (preserves : map.PreservesRewrites) {interface : source.Interface}
    {term final : source.Term interface} (reaches : source.Reaches term final) :
    target.Reaches (map.term term) (map.term final) := by
  induction reaches with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (preserves step)

/-- A map that reflects steps reflects reduction, up to the static
equivalence of the target at both ends. -/
theorem reaches_reflect (reflects : map.ReflectsRewrites) {interface : source.Interface}
    {term : source.Term interface} {image final : target.Term (map.interface interface)}
    (start : (target.equations _).r image (map.term term)) (reaches : target.Reaches image final) :
    ∃ sourceFinal, source.Reaches term sourceFinal ∧
      (target.equations _).r final (map.term sourceFinal) := by
  induction reaches with
  | refl => exact ⟨term, .refl, start⟩
  | tail _ step ih =>
      obtain ⟨middle, sourceReaches, related⟩ := ih
      obtain ⟨answer, answerStep, answerRelated⟩ := target.rewrites_resp_left related step
      obtain ⟨sourceNext, sourceStep, lifted⟩ := reflects answerStep
      exact ⟨sourceNext, sourceReaches.tail sourceStep,
        (target.equations _).iseqv.trans answerRelated lifted⟩

/-- **A hosting map carries confluence back**: a theory hosted by a confluent
theory is confluent. -/
theorem Hosting.confluentUpTo (hosting : map.Hosting) (confluent : target.ConfluentUpTo) :
    source.ConfluentUpTo := by
  intro interface origin left right leftReaches rightReaches
  have preserves : map.PreservesRewrites := map.preservesRewrites_of_transitions hosting.preserves
  have reflects : map.ReflectsRewrites := map.reflectsRewrites_of_transitions hosting.reflects
  obtain ⟨leftEnd, rightEnd, leftJoin, rightJoin, joined⟩ :=
    confluent (map.term origin) (map.term left) (map.term right)
      (map.reaches_of_preserves preserves leftReaches)
      (map.reaches_of_preserves preserves rightReaches)
  obtain ⟨leftSource, leftSourceReaches, leftRelated⟩ :=
    map.reaches_reflect reflects ((target.equations _).iseqv.refl _) leftJoin
  obtain ⟨rightSource, rightSourceReaches, rightRelated⟩ :=
    map.reaches_reflect reflects ((target.equations _).iseqv.refl _) rightJoin
  refine ⟨leftSource, rightSource, leftSourceReaches, rightSourceReaches, ?_⟩
  apply map.reflectsEquations_of_faithful hosting.faithful
  exact (target.equations _).iseqv.trans ((target.equations _).iseqv.symm leftRelated)
    ((target.equations _).iseqv.trans joined rightRelated)

/-- **No confluent theory hosts a theory with a branch**: a term with two
steps to normal terms that are apart. -/
theorem not_hosting_of_branch {interface : source.Interface}
    {term first second : source.Term interface}
    (firstStep : source.rewrites term first) (secondStep : source.rewrites term second)
    (firstNormal : IsNormal source.rewrites first) (secondNormal : IsNormal source.rewrites second)
    (apart : ¬ (source.equations interface).r first second)
    (confluent : target.ConfluentUpTo) : ¬ map.Hosting := by
  intro hosting
  obtain ⟨firstEnd, secondEnd, firstReaches, secondReaches, joined⟩ :=
    Hosting.confluentUpTo map hosting confluent term first second (.single firstStep) (.single secondStep)
  rw [firstNormal.reflTransGen_eq firstReaches, secondNormal.reflTransGen_eq secondReaches]
    at joined
  exact apart joined

/-- **A map that preserves transitions carries termination back.** -/
theorem terminating_of_preserves (preserves : map.PreservesTransitions)
    (terminating : target.Terminating) : source.Terminating := by
  intro interface
  have steps : map.PreservesRewrites := map.preservesRewrites_of_transitions preserves
  exact Subrelation.wf
    (r := InvImage
      (fun next term : target.Term (map.interface interface) => target.rewrites term next)
      map.term)
    (fun step => steps step) (InvImage.wf _ (terminating _))

/-- **No terminating theory receives a transition-preserving map from a
theory with a cyclic reduction.** -/
theorem not_preserves_of_cycle {interface : source.Interface} {term : source.Term interface}
    (cycle : Relation.TransGen source.rewrites term term) (terminating : target.Terminating) :
    ¬ map.PreservesTransitions := by
  intro preserves
  have wellFounded := map.terminating_of_preserves preserves terminating interface
  have reversed : Relation.TransGen
      (fun next term : source.Term interface => source.rewrites term next) term term :=
    Relation.transGen_swap.mpr cycle
  exact not_rel_self_of_acc (wellFounded.transGen.apply term) reversed

/-- **A hosting map carries closure of reduction under contexts back.** -/
theorem Hosting.contextClosed (hosting : map.Hosting) (closed : target.ContextClosed) :
    source.ContextClosed := by
  intro origin result label term next step
  have preserves : map.PreservesRewrites := map.preservesRewrites_of_transitions hosting.preserves
  have reflects : map.ReflectsRewrites := map.reflectsRewrites_of_transitions hosting.reflects
  obtain ⟨whole, wholeReaches, wholeRelated⟩ := closed (map.context label) (preserves step)
  obtain ⟨sourceWhole, sourceReaches, lifted⟩ := map.reaches_reflect reflects
    ((target.equations _).iseqv.symm (map.apply_equivariant label term)) wholeReaches
  refine ⟨sourceWhole, sourceReaches, ?_⟩
  apply map.reflectsEquations_of_faithful hosting.faithful
  exact (target.equations _).iseqv.trans ((target.equations _).iseqv.symm lifted)
    ((target.equations _).iseqv.trans wholeRelated
      ((target.equations _).iseqv.symm (map.apply_equivariant label next)))

/-- **No context-closed theory hosts a theory in which a context disables a
step of its hole.** -/
theorem not_hosting_of_disabled {origin result : source.Interface}
    (label : source.Label origin result) {term next : source.Term origin}
    (step : source.rewrites term next)
    (disabled : ∀ whole, source.Reaches (source.apply label term) whole →
      ¬ (source.equations result).r whole (source.apply label next))
    (closed : target.ContextClosed) : ¬ map.Hosting := by
  intro hosting
  obtain ⟨whole, reaches, related⟩ := Hosting.contextClosed map hosting closed label step
  exact disabled whole reaches related

end ContextMap

#print axioms ContextMap.Hosting.confluentUpTo
#print axioms ContextMap.not_hosting_of_branch
#print axioms ContextMap.terminating_of_preserves
#print axioms ContextMap.not_preserves_of_cycle
#print axioms ContextMap.Hosting.contextClosed
#print axioms ContextMap.not_hosting_of_disabled

end Mettapedia.GSLT
