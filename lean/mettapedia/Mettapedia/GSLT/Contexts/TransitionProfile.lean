import Mettapedia.GSLT.Contexts.ContextMorphism
import Mathlib.Logic.Relation

/-!
# Reduction profiles for context theories

The static context action and the selected reduction relation are independent
parts of a context theory. A profile can count a nonempty finite computation
as one transition while retaining the same terms, equations and contexts.

The nonempty profile uses Mathlib's transitive closure. It does not count
inaction as a step. Transport into this profile proves finite operational
simulation; it does not by itself prove backward lifting, bisimilarity
preservation, divergence reflection or preservation of execution cost.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT

universe u

namespace ContextTheory

variable (theory : ContextTheory.{u})

/-- Change the operational relation while retaining the static context
theory. The replacement must respect its existing equations on both sides. -/
def withRewrites
    (relation : {interface : theory.Interface} → theory.Term interface →
      theory.Term interface → Prop)
    (left : ∀ {interface : theory.Interface} {term term' next : theory.Term interface},
      (theory.equations interface).r term term' → relation term next →
        ∃ next', relation term' next' ∧ (theory.equations interface).r next next')
    (right : ∀ {interface : theory.Interface} {term next next' : theory.Term interface},
      relation term next → (theory.equations interface).r next next' → relation term next') :
    ContextTheory.{u} :=
  { theory with rewrites := relation, rewrites_resp_left := left, rewrites_resp_right := right }

/-- Equation compatibility on both sides gives transport with the same
target term, rather than requiring a fresh representative at each use. -/
theorem rewrites_of_equations_left {interface : theory.Interface}
    {term term' next : theory.Term interface}
    (equivalent : (theory.equations interface).r term term')
    (step : theory.rewrites term next) : theory.rewrites term' next := by
  obtain ⟨next', transported, same⟩ := theory.rewrites_resp_left equivalent step
  exact theory.rewrites_resp_right transported ((theory.equations _).iseqv.symm same)

theorem nonemptyReduction_resp_left {interface : theory.Interface}
    {term term' next : theory.Term interface}
    (equivalent : (theory.equations interface).r term term')
    (steps : Relation.TransGen theory.rewrites term next) :
    Relation.TransGen theory.rewrites term' next := by
  obtain ⟨middle, first, rest⟩ := Relation.TransGen.head'_iff.mp steps
  exact Relation.TransGen.head' (theory.rewrites_of_equations_left equivalent first) rest

theorem nonemptyReduction_resp_right {interface : theory.Interface}
    {term next next' : theory.Term interface}
    (steps : Relation.TransGen theory.rewrites term next)
    (equivalent : (theory.equations interface).r next next') :
    Relation.TransGen theory.rewrites term next' := by
  obtain ⟨middle, first, last⟩ := Relation.TransGen.tail'_iff.mp steps
  exact Relation.TransGen.tail' first (theory.rewrites_resp_right last equivalent)

/-- One profile transition performs at least one original reduction. The
profile shares every static context operation with the original theory. -/
def nonemptyReduction : ContextTheory.{u} :=
  theory.withRewrites (fun {interface} => Relation.TransGen (@theory.rewrites interface))
    (by
      intro interface term term' next equivalent steps
      exact ⟨next, theory.nonemptyReduction_resp_left equivalent steps,
        (theory.equations _).iseqv.refl _⟩)
    (by
      intro interface term next next' steps equivalent
      exact theory.nonemptyReduction_resp_right steps equivalent)

@[simp] theorem nonemptyReduction_rewrites_iff {interface : theory.Interface}
    (term next : theory.Term interface) :
    theory.nonemptyReduction.rewrites term next ↔ Relation.TransGen theory.rewrites term next :=
  Iff.rfl

/-- A primitive step is a nonempty computation. -/
theorem nonemptyReduction_of_step {interface : theory.Interface}
    {term next : theory.Term interface} (step : theory.rewrites term next) :
    theory.nonemptyReduction.rewrites term next :=
  Relation.TransGen.single step

/-- Profile transitions compose through a genuine intermediate term. -/
theorem nonemptyReduction_trans {interface : theory.Interface}
    {term middle next : theory.Term interface}
    (first : theory.nonemptyReduction.rewrites term middle)
    (second : theory.nonemptyReduction.rewrites middle next) :
    theory.nonemptyReduction.rewrites term next :=
  first.trans second

end ContextTheory

namespace ContextMap

variable {source target : ContextTheory.{u}} (map : ContextMap source target)

/-- Primitive reductions transport under the term map. Equivariance then
provides the corresponding law at every translated context label. -/
def PreservesRewrites : Prop :=
  ∀ {interface : source.Interface} {term next : source.Term interface},
    source.rewrites term next → target.rewrites (map.term term) (map.term next)

theorem preservesRewrites_of_transitions (preserves : map.PreservesTransitions) :
    map.PreservesRewrites := by
  intro interface term next step
  have transition : source.Transition term (source.identity interface) next := by
    simpa only [ContextTheory.Transition, source.apply_identity] using step
  exact target.rewrites_of_equations_left (map.context_identity_on_image term)
    (preserves _ transition)

theorem preservesTransitions_of_rewrites (preserves : map.PreservesRewrites) :
    map.PreservesTransitions := by
  intro origin result label term next transition
  exact target.rewrites_of_equations_left (map.apply_equivariant label term)
    (preserves transition)

theorem preservesTransitions_iff_rewrites :
    map.PreservesTransitions ↔ map.PreservesRewrites :=
  ⟨map.preservesRewrites_of_transitions, map.preservesTransitions_of_rewrites⟩

/-- Backward lifting of primitive image reductions, retaining the target
equation relating the response to its lifted source representative. -/
def ReflectsRewrites : Prop :=
  ∀ {interface : source.Interface} {term : source.Term interface}
    {next : target.Term (map.interface interface)},
    target.rewrites (map.term term) next →
      ∃ sourceNext, source.rewrites term sourceNext ∧
        (target.equations _).r next (map.term sourceNext)

theorem reflectsRewrites_of_transitions (reflects : map.ReflectsTransitions) :
    map.ReflectsRewrites := by
  intro interface term next step
  have transition : target.Transition (map.term term)
      (map.context (source.identity interface)) next :=
    target.rewrites_of_equations_left
      ((target.equations _).iseqv.symm (map.context_identity_on_image term)) step
  obtain ⟨sourceNext, lifted, equivalent⟩ := reflects _ transition
  refine ⟨sourceNext, ?_, equivalent⟩
  simpa only [ContextTheory.Transition, source.apply_identity] using lifted

theorem reflectsTransitions_of_rewrites (reflects : map.ReflectsRewrites) :
    map.ReflectsTransitions := by
  intro origin result label term next transition
  exact reflects (target.rewrites_of_equations_left
    ((target.equations _).iseqv.symm (map.apply_equivariant label term)) transition)

theorem reflectsTransitions_iff_rewrites :
    map.ReflectsTransitions ↔ map.ReflectsRewrites :=
  ⟨map.reflectsRewrites_of_transitions, map.reflectsTransitions_of_rewrites⟩

/-- A static context map is independent of whether primitive reductions or
nonempty finite computations are selected as the operational profile. -/
def atNonemptyReduction : ContextMap source.nonemptyReduction target.nonemptyReduction where
  interface := map.interface
  term := map.term
  context := map.context
  term_resp := map.term_resp
  equivariant := map.equivariant

/-- A simulation that sends each primitive source reduction to a nonempty
target computation extends to all nonempty source computations. -/
theorem preservesNonemptyReduction
    (simulates : ∀ {interface : source.Interface} {term next : source.Term interface},
      source.rewrites term next → target.nonemptyReduction.rewrites (map.term term) (map.term next))
    {interface : source.Interface} {term next : source.Term interface}
    (steps : source.nonemptyReduction.rewrites term next) :
    target.nonemptyReduction.rewrites (map.term term) (map.term next) :=
  Relation.TransGen.lift' map.term (fun _ _ step => simulates step) term next steps

/-- Primitive transition transport also transports transitions of the
nonempty computation profile. No reflection law is inferred. -/
theorem atNonemptyReduction_preservesTransitions (preserves : map.PreservesTransitions) :
    map.atNonemptyReduction.PreservesTransitions := by
  apply map.atNonemptyReduction.preservesTransitions_of_rewrites
  intro interface term next steps
  exact map.preservesNonemptyReduction
    (fun step => target.nonemptyReduction_of_step (map.preservesRewrites_of_transitions preserves step))
    steps

end ContextMap

end Mettapedia.GSLT
