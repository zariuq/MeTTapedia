import Mettapedia.GSLT.Contexts.ImageObservation
import Mettapedia.GSLT.Contexts.TransitionProfile

/-!
# A theory given by its terms alone, as a theory presented through its contexts

A theory given by its terms, its static equivalence and its reduction
(`GSLT`) has a least presentation through contexts: the only contexts are the
hole and the terms (`GSLT.termsAlone`).  A context with holes uses each hole
once, so a context with one hole is the hole, and a context with no hole is a
term.

For such a theory the labels say nothing.  Every label acts as the identity
(`termsAlone_apply`), a transition labelled by a context is a step, and what
the full probe sees is reduction bisimilarity (`termsAlone_bisimilar_iff`).

A map out of it into any theory is given by a map on terms that respects the
static equivalence (`ContextMap.ofTerms`): the hole goes to the hole and a
term to its image.  It is hosting exactly when the map on terms reflects the
static equivalence and preserves and reflects steps
(`ContextMap.ofTerms_hosting_iff`).  This is the form in which a simulation
stated on terms alone becomes a statement in the category of theories; it
adds no context to the source.
-/

set_option autoImplicit false
set_option linter.dupNamespace false

namespace Mettapedia.GSLT

universe u

/-- The contexts of a theory given by its terms alone: the hole, when there
is exactly one, and the terms, when there is none. -/
inductive TermsContext (Carrier : Type u) (arity : Type) : Type u where
  | hole (position : arity) (only : ∀ other : arity, other = position)
  | constant (term : Carrier) (empty : IsEmpty arity)

namespace TermsContext

variable {Carrier : Type u} {arity newArity : Type}

/-- Fill the hole, if there is one. -/
def fill (filling : arity → Carrier) : TermsContext Carrier arity → Carrier
  | .hole position _ => filling position
  | .constant term _ => term

/-- Rename the holes along a surjection. -/
def relabel (rename : arity → newArity) (surjective : Function.Surjective rename) :
    TermsContext Carrier arity → TermsContext Carrier newArity
  | .hole position only =>
      .hole (rename position) fun other => by
        obtain ⟨origin, rfl⟩ := surjective other
        rw [only origin]
  | .constant term empty =>
      .constant term ⟨fun other => by
        obtain ⟨origin, rfl⟩ := surjective other
        exact empty.false origin⟩

theorem fill_relabel (rename : arity → newArity) (surjective : Function.Surjective rename)
    (context : TermsContext Carrier arity) (filling : newArity → Carrier) :
    (context.relabel rename surjective).fill filling = context.fill fun index =>
      filling (rename index) := by
  cases context <;> rfl

/-- When there is one hole, the leaves beneath it are all the leaves. -/
theorem leaf_surjective {innerArity : arity → Type} {position : arity}
    (only : ∀ other : arity, other = position) :
    Function.Surjective fun leaf : innerArity position =>
      (⟨position, leaf⟩ : Σ index, innerArity index) := by
  rintro ⟨index, leaf⟩
  obtain rfl := only index
  exact ⟨leaf, rfl⟩

/-- Plug a family of contexts into the holes of a context. -/
def plug {innerArity : arity → Type} (context : TermsContext Carrier arity)
    (inner : (index : arity) → TermsContext Carrier (innerArity index)) :
    TermsContext Carrier (Σ index, innerArity index) :=
  match context with
  | .hole position only =>
      (inner position).relabel (fun leaf => ⟨position, leaf⟩) (leaf_surjective only)
  | .constant term empty => .constant term ⟨fun leaf => empty.false leaf.1⟩

theorem fill_plug {innerArity : arity → Type} (context : TermsContext Carrier arity)
    (inner : (index : arity) → TermsContext Carrier (innerArity index))
    (filling : (Σ index, innerArity index) → Carrier) :
    (context.plug inner).fill filling =
      context.fill fun index => (inner index).fill fun leaf => filling ⟨index, leaf⟩ := by
  cases context with
  | hole position only =>
      exact fill_relabel (fun leaf => (⟨position, leaf⟩ : Σ index, innerArity index))
        (leaf_surjective only) (inner position) filling
  | constant term empty => rfl

end TermsContext

/-- **A theory given by its terms alone, presented through its contexts.** -/
def GSLT.termsAlone (theory : GSLT.{u}) : ContextTheory.{u} where
  Interface := PUnit
  Term := fun _ => theory.Term
  equations := fun _ => theory.equations
  rewrites := theory.rewrites
  rewrites_resp_left := theory.rewrites_resp_left
  rewrites_resp_right := theory.rewrites_resp_right
  Context := fun {arity} _ _ => TermsContext theory.Term arity
  fill := fun context filling => context.fill filling
  fill_resp := fun context _ _ equivalent => by
    cases context with
    | hole position only => exact equivalent position
    | constant term empty => exact theory.equations.iseqv.refl term
  identity := fun _ => .hole () fun _ => rfl
  fill_identity := fun _ _ => rfl
  plug := fun context inner => context.plug inner
  fill_plug := fun context inner filling => context.fill_plug inner filling
  relabel := fun rename bijective context => context.relabel rename bijective.2
  fill_relabel := fun rename bijective context filling =>
    context.fill_relabel rename bijective.2 filling
  constant := fun term => .constant term ⟨fun impossible => impossible.elim⟩
  fill_constant := fun _ _ => rfl

namespace GSLT

variable (theory : GSLT.{u})

/-- **Every label of a theory given by its terms alone acts as the
identity.** -/
theorem termsAlone_apply (label : theory.termsAlone.Label PUnit.unit PUnit.unit)
    (term : theory.Term) : theory.termsAlone.apply label term = term := by
  cases label with
  | hole position only => rfl
  | constant value empty => exact (empty.false ()).elim

/-- A transition labelled by a context is a step. -/
theorem termsAlone_transition_iff (label : theory.termsAlone.Label PUnit.unit PUnit.unit)
    {term next : theory.Term} :
    theory.termsAlone.Transition (source := PUnit.unit) term label next ↔
      theory.rewrites term next := by
  show theory.rewrites (theory.termsAlone.apply label term) next ↔ _
  rw [termsAlone_apply]

/-- **What the full probe sees is reduction bisimilarity.** -/
theorem termsAlone_bisimilar_iff {left right : theory.Term} :
    theory.termsAlone.fullProbe.Bisimilar (index := PUnit.unit) left right ↔
      theory.Bisimilar left right := by
  constructor
  · intro bisimilar
    exact ContextTheory.bisimilar_toGSLT (theory := theory.termsAlone) bisimilar
  · rintro ⟨relation, ⟨forward, backward⟩, related⟩
    refine ⟨fun _ first second => relation first second, ⟨?_, ?_⟩, related⟩
    · intro _ first second pair _ observer next transition
      obtain ⟨next', step, nextRelated⟩ :=
        forward pair ((theory.termsAlone_transition_iff observer).mp transition)
      exact ⟨next', (theory.termsAlone_transition_iff observer).mpr step, nextRelated⟩
    · intro _ first second pair _ observer next' transition
      obtain ⟨next, step, nextRelated⟩ :=
        backward pair ((theory.termsAlone_transition_iff observer).mp transition)
      exact ⟨next, (theory.termsAlone_transition_iff observer).mpr step, nextRelated⟩

end GSLT

namespace ContextMap

variable {source : GSLT.{u}} {target : ContextTheory.{u}}

/-- The image of a context of a theory given by its terms alone: the hole
goes to the hole, a term to its image. -/
def termsImage (point : target.Interface) (term : source.Term → target.Term point) {arity : Type}
    (context : TermsContext source.Term arity) : target.Context (fun _ : arity => point) point :=
  match context with
  | .hole position only =>
      target.relabel (fun _ : Unit => position)
        ⟨fun _ _ _ => rfl, fun other => ⟨(), (only other).symm⟩⟩ (target.identity point)
  | .constant value empty =>
      target.relabel (fun impossible : Empty => impossible.elim)
        ⟨fun impossible => impossible.elim, fun other => (empty.false other).elim⟩
        (target.constant (term value))

theorem fill_termsImage (point : target.Interface) (term : source.Term → target.Term point)
    {arity : Type} (context : TermsContext source.Term arity) (filling : arity → source.Term) :
    target.fill (termsImage point term context) (fun index => term (filling index)) =
      term (context.fill filling) := by
  cases context with
  | hole position only =>
      exact (target.fill_relabel (holes := fun _ : arity => point) (fun _ : Unit => position)
        ⟨fun _ _ _ => rfl, fun other => ⟨(), (only other).symm⟩⟩ (target.identity point)
        fun index => term (filling index)).trans (target.fill_identity point _)
  | constant value empty =>
      exact (target.fill_relabel (holes := fun _ : arity => point)
        (fun impossible : Empty => impossible.elim)
        ⟨fun impossible => impossible.elim, fun other => (empty.false other).elim⟩
        (target.constant (term value)) fun index => term (filling index)).trans
        (target.fill_constant (term value) _)

/-- Equal terms are equivalent. -/
theorem equations_of_eq {interface : target.Interface} {first second : target.Term interface}
    (same : first = second) : (target.equations interface).r first second :=
  same ▸ (target.equations interface).iseqv.refl first

/-- **A map on terms that respects the static equivalence is a map of
theories out of a theory given by its terms alone.** -/
def ofTerms (point : target.Interface) (term : source.Term → target.Term point)
    (term_resp : ∀ {first second : source.Term}, source.equations.r first second →
      (target.equations point).r (term first) (term second)) :
    ContextMap source.termsAlone target where
  interface := fun _ => point
  term := term
  context := fun context => termsImage point term context
  term_resp := term_resp
  equivariant := fun context filling =>
    equations_of_eq (fill_termsImage point term context filling).symm

/-- **The map is hosting exactly when the map on terms reflects the static
equivalence and preserves and reflects steps.** -/
theorem ofTerms_hosting_iff (point : target.Interface) (term : source.Term → target.Term point)
    (term_resp : ∀ {first second : source.Term}, source.equations.r first second →
      (target.equations point).r (term first) (term second)) :
    (ofTerms point term term_resp).Hosting ↔
      (∀ first second : source.Term, (target.equations point).r (term first) (term second) →
        source.equations.r first second) ∧
      (∀ first next : source.Term, source.rewrites first next →
        target.rewrites (term first) (term next)) ∧
      ∀ (first : source.Term) (next : target.Term point), target.rewrites (term first) next →
        ∃ sourceNext, source.rewrites first sourceNext ∧
          (target.equations point).r next (term sourceNext) := by
  rw [hosting_iff, (ofTerms point term term_resp).preservesTransitions_iff_rewrites,
    (ofTerms point term term_resp).reflectsTransitions_iff_rewrites]
  constructor
  · rintro ⟨reflectsEquations, preserves, reflects⟩
    exact ⟨fun _ _ equivalent => reflectsEquations (origin := PUnit.unit) equivalent,
      fun _ _ step => preserves (interface := PUnit.unit) step,
      fun _ _ step => reflects (interface := PUnit.unit) step⟩
  · rintro ⟨reflectsEquations, preserves, reflects⟩
    exact ⟨fun equivalent => reflectsEquations _ _ equivalent, fun step => preserves _ _ step,
      fun step => reflects _ _ step⟩

end ContextMap

#print axioms GSLT.termsAlone
#print axioms GSLT.termsAlone_bisimilar_iff
#print axioms ContextMap.ofTerms
#print axioms ContextMap.ofTerms_hosting_iff

end Mettapedia.GSLT
