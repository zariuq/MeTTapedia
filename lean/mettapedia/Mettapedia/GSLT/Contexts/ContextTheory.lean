import Mettapedia.GSLT.Core.GSLT
import Mathlib.Logic.Function.Basic

/-!
# Theories presented through their contexts

A theory presents a symmetric multicategory of contexts.  Its objects are
interfaces.  A context has holes, each of an interface, and a result
interface; its holes are named by an arbitrary index type, so that plugging a
family of contexts into the holes of a context needs no arithmetic on
positions.  Contexts act on terms by filling, and a term is a context with no
hole.

The laws of a symmetric multicategory are stated through that action: the
action of a plugged context is the composite of the actions, the identity
context acts as the identity, and renaming the holes along a bijection
permutes the arguments.  Two contexts are compared by their action, up to the
static equivalence of the theory.

A context with one hole is a label.  The transition `term --label--> next`
says that placing the term in the context enables the step.  Bisimilarity is
taken over these transitions, relative to a class of observing contexts; when
the class is closed under composition, bisimilarity is preserved by every
observing context.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT

universe u

/-- A theory presented through its contexts. -/
structure ContextTheory where
  /-- What a hole or a result is: a sort, with whatever else is recorded. -/
  Interface : Type u
  /-- The terms of an interface. -/
  Term : Interface → Type u
  /-- The static equivalence. -/
  equations : (interface : Interface) → Setoid (Term interface)
  /-- One-step reduction. -/
  rewrites : {interface : Interface} → Term interface → Term interface → Prop
  rewrites_resp_left : ∀ {interface : Interface} {term term' next : Term interface},
    (equations interface).r term term' → rewrites term next →
      ∃ next', rewrites term' next' ∧ (equations interface).r next next'
  rewrites_resp_right : ∀ {interface : Interface} {term next next' : Term interface},
    rewrites term next → (equations interface).r next next' → rewrites term next'
  /-- Contexts with holes of the given interfaces and a result interface. -/
  Context : {arity : Type} → (arity → Interface) → Interface → Type u
  /-- A context acts on terms: fill every hole. -/
  fill : {arity : Type} → {holes : arity → Interface} → {result : Interface} →
    Context holes result → ((index : arity) → Term (holes index)) → Term result
  fill_resp : ∀ {arity : Type} {holes : arity → Interface} {result : Interface}
    (context : Context holes result) {first second : (index : arity) → Term (holes index)},
    (∀ index, (equations (holes index)).r (first index) (second index)) →
      (equations result).r (fill context first) (fill context second)
  /-- The context that is a hole. -/
  identity : (interface : Interface) → Context (fun _ : Unit => interface) interface
  fill_identity : ∀ (interface : Interface) (filling : Unit → Term interface),
    fill (identity interface) filling = filling ()
  /-- Plug a family of contexts into the holes of a context. -/
  plug : {arity : Type} → {holes : arity → Interface} → {result : Interface} →
    {innerArity : arity → Type} →
    {innerHoles : (index : arity) → innerArity index → Interface} →
    Context holes result → ((index : arity) → Context (innerHoles index) (holes index)) →
      Context (fun position : Σ index, innerArity index => innerHoles position.1 position.2)
        result
  fill_plug : ∀ {arity : Type} {holes : arity → Interface} {result : Interface}
    {innerArity : arity → Type} {innerHoles : (index : arity) → innerArity index → Interface}
    (context : Context holes result)
    (inner : (index : arity) → Context (innerHoles index) (holes index))
    (filling : (position : Σ index, innerArity index) →
      Term (innerHoles position.1 position.2)),
    fill (plug context inner) filling =
      fill context fun index => fill (inner index) fun position => filling ⟨index, position⟩
  /-- Rename the holes along a bijection. -/
  relabel : {arity newArity : Type} → {holes : newArity → Interface} → {result : Interface} →
    (rename : arity → newArity) → Function.Bijective rename →
    Context (fun index => holes (rename index)) result → Context holes result
  fill_relabel : ∀ {arity newArity : Type} {holes : newArity → Interface} {result : Interface}
    (rename : arity → newArity) (bijective : Function.Bijective rename)
    (context : Context (fun index => holes (rename index)) result)
    (filling : (index : newArity) → Term (holes index)),
    fill (relabel rename bijective context) filling =
      fill context fun index => filling (rename index)
  /-- A term is a context with no hole. -/
  constant : {holes : Empty → Interface} → {result : Interface} → Term result →
    Context holes result
  fill_constant : ∀ {holes : Empty → Interface} {result : Interface} (term : Term result)
    (filling : (index : Empty) → Term (holes index)),
    fill (constant (holes := holes) term) filling = term

namespace ContextTheory

variable (theory : ContextTheory.{u})

/-- The theory at one interface, as a GSLT. -/
def gslt (interface : theory.Interface) : GSLT where
  Term := theory.Term interface
  equations := theory.equations interface
  rewrites := theory.rewrites
  rewrites_resp_left := theory.rewrites_resp_left
  rewrites_resp_right := theory.rewrites_resp_right

/-! ## Comparing contexts by their action -/

/-- Two contexts are equivalent when they agree, up to the static
equivalence, on every filling. -/
def ContextEquiv {arity : Type} {holes : arity → theory.Interface}
    {result : theory.Interface} (first second : theory.Context holes result) : Prop :=
  ∀ filling, (theory.equations result).r (theory.fill first filling)
    (theory.fill second filling)

theorem contextEquiv_refl {arity : Type} {holes : arity → theory.Interface}
    {result : theory.Interface} (context : theory.Context holes result) :
    theory.ContextEquiv context context :=
  fun _ => (theory.equations result).iseqv.refl _

theorem contextEquiv_symm {arity : Type} {holes : arity → theory.Interface}
    {result : theory.Interface} {first second : theory.Context holes result}
    (equivalent : theory.ContextEquiv first second) : theory.ContextEquiv second first :=
  fun filling => (theory.equations result).iseqv.symm (equivalent filling)

theorem contextEquiv_trans {arity : Type} {holes : arity → theory.Interface}
    {result : theory.Interface} {first second third : theory.Context holes result}
    (firstSecond : theory.ContextEquiv first second)
    (secondThird : theory.ContextEquiv second third) : theory.ContextEquiv first third :=
  fun filling => (theory.equations result).iseqv.trans (firstSecond filling)
    (secondThird filling)

/-- The comparison of contexts by their action is an equivalence relation. -/
def contextSetoid {arity : Type} (holes : arity → theory.Interface)
    (result : theory.Interface) : Setoid (theory.Context holes result) where
  r := theory.ContextEquiv
  iseqv := ⟨theory.contextEquiv_refl, theory.contextEquiv_symm, theory.contextEquiv_trans⟩

/-! ## The laws of a symmetric multicategory, read through the action -/

/-- Plugging holes into every hole of a context does not change its
action. -/
theorem fill_plug_identity {arity : Type} {holes : arity → theory.Interface}
    {result : theory.Interface} (context : theory.Context holes result)
    (filling : (position : Σ _ : arity, Unit) → theory.Term (holes position.1)) :
    theory.fill (theory.plug context fun index => theory.identity (holes index)) filling =
      theory.fill context fun index => filling ⟨index, ()⟩ := by
  rw [theory.fill_plug]
  congr 1
  funext index
  exact theory.fill_identity _ _

/-- Plugging a context into a hole gives a context with the same action. -/
theorem fill_identity_plug {arity : Type} {holes : arity → theory.Interface}
    {result : theory.Interface} (context : theory.Context holes result)
    (filling : (position : Σ _ : Unit, arity) → theory.Term (holes position.2)) :
    theory.fill (theory.plug (theory.identity result) fun _ => context) filling =
      theory.fill context fun index => filling ⟨(), index⟩ := by
  rw [theory.fill_plug, theory.fill_identity]

/-- **Plugging is associative**: plugging twice acts as plugging the plugged
family. -/
theorem fill_plug_plug {arity : Type} {holes : arity → theory.Interface}
    {result : theory.Interface} {middleArity : arity → Type}
    {middleHoles : (index : arity) → middleArity index → theory.Interface}
    {innerArity : (index : arity) → middleArity index → Type}
    {innerHoles : (index : arity) → (middle : middleArity index) →
      innerArity index middle → theory.Interface}
    (context : theory.Context holes result)
    (middle : (index : arity) → theory.Context (middleHoles index) (holes index))
    (inner : (index : arity) → (position : middleArity index) →
      theory.Context (innerHoles index position) (middleHoles index position))
    (filling : (index : arity) → (position : middleArity index) →
      (leaf : innerArity index position) → theory.Term (innerHoles index position leaf)) :
    theory.fill
        (theory.plug (theory.plug context middle) fun position =>
          inner position.1 position.2)
        (fun leaf => filling leaf.1.1 leaf.1.2 leaf.2) =
      theory.fill
        (theory.plug context fun index =>
          theory.plug (middle index) fun position => inner index position)
        (fun leaf => filling leaf.1 leaf.2.1 leaf.2.2) := by
  simp only [theory.fill_plug]

/-- Renaming twice acts as renaming along the composite. -/
theorem fill_relabel_relabel {arity middleArity newArity : Type}
    {holes : newArity → theory.Interface} {result : theory.Interface}
    (first : arity → middleArity) (firstBijective : Function.Bijective first)
    (second : middleArity → newArity) (secondBijective : Function.Bijective second)
    (context : theory.Context (fun index => holes (second (first index))) result)
    (filling : (index : newArity) → theory.Term (holes index)) :
    theory.fill
        (theory.relabel second secondBijective (theory.relabel first firstBijective context))
        filling =
      theory.fill
        (theory.relabel (fun index => second (first index))
          (secondBijective.comp firstBijective) context)
        filling := by
  simp only [theory.fill_relabel]

/-- **Terms are the contexts with no hole.**  A context with no hole acts as
the constant context of the term it fills to. -/
theorem constant_fill_equiv {holes : Empty → theory.Interface} {result : theory.Interface}
    (context : theory.Context holes result) :
    theory.ContextEquiv (theory.constant (theory.fill context fun index => index.elim))
      context := by
  intro filling
  rw [theory.fill_constant]
  have same : (fun index : Empty => (index.elim : theory.Term (holes index))) = filling :=
    funext fun index => index.elim
  rw [same]
  exact (theory.equations result).iseqv.refl _

/-! ## Labels -/

/-- A label: a context with one hole. -/
abbrev Label (source target : theory.Interface) :=
  theory.Context (fun _ : Unit => source) target

/-- Place a term in a label. -/
def apply {source target : theory.Interface} (label : theory.Label source target)
    (term : theory.Term source) : theory.Term target :=
  theory.fill label fun _ => term

theorem sigma_unit_bijective : Function.Bijective (fun _ : (Σ _ : Unit, Unit) => ()) :=
  ⟨fun first second _ => by
      rcases first with ⟨⟨⟩, ⟨⟩⟩
      rcases second with ⟨⟨⟩, ⟨⟩⟩
      rfl,
    fun _ => ⟨⟨(), ()⟩, rfl⟩⟩

/-- Labels compose: the outer label around the inner. -/
def compose {first second third : theory.Interface} (outer : theory.Label second third)
    (inner : theory.Label first second) : theory.Label first third :=
  theory.relabel (fun _ : (Σ _ : Unit, Unit) => ()) sigma_unit_bijective
    (theory.plug outer fun _ => inner)

@[simp] theorem apply_identity {interface : theory.Interface}
    (term : theory.Term interface) : theory.apply (theory.identity interface) term = term :=
  theory.fill_identity interface _

@[simp] theorem apply_compose {first second third : theory.Interface}
    (outer : theory.Label second third) (inner : theory.Label first second)
    (term : theory.Term first) :
    theory.apply (theory.compose outer inner) term =
      theory.apply outer (theory.apply inner term) := by
  simp only [apply, compose, theory.fill_relabel, theory.fill_plug]

theorem apply_resp {source target : theory.Interface} (label : theory.Label source target)
    {first second : theory.Term source}
    (equivalent : (theory.equations source).r first second) :
    (theory.equations target).r (theory.apply label first) (theory.apply label second) :=
  theory.fill_resp label fun _ => equivalent

/-! ## Transitions labelled by contexts -/

/-- **Placing the term in the context enables the step.** -/
def Transition {source target : theory.Interface} (term : theory.Term source)
    (label : theory.Label source target) (next : theory.Term target) : Prop :=
  theory.rewrites (theory.apply label term) next

/-- A transition labelled by the hole is a step. -/
theorem transition_identity_iff {interface : theory.Interface}
    {term next : theory.Term interface} :
    theory.Transition term (theory.identity interface) next ↔ theory.rewrites term next := by
  rw [Transition, apply_identity]

/-! ## Probes -/

/-- **A probe**: a family of observing contexts.  The observers are indexed,
each index stands for an interface, and an observer between two indices is a
label between their interfaces.  The index need not be the interface itself:
the observers of one theory, carried into another, remain indexed by the
interfaces they came from. -/
structure Probe where
  Index : Type u
  interface : Index → theory.Interface
  Observer : Index → Index → Type u
  label : {source target : Index} → Observer source target →
    theory.Label (interface source) (interface target)

/-- Every context with one hole observes. -/
def fullProbe : theory.Probe where
  Index := theory.Interface
  interface := id
  Observer := fun source target => theory.Label source target
  label := fun observer => observer

/-- Only the hole observes: the probe that sees reduction and nothing else. -/
def reductionProbe : theory.Probe where
  Index := theory.Interface
  interface := id
  Observer := fun source target => ULift (PLift (source = target))
  label := fun {source _} same => same.down.down ▸ theory.identity source

variable {theory}

/-- A probe is closed when it has the holes and composes, up to the action
on terms. -/
structure Probe.Closed (probe : theory.Probe) : Prop where
  identity : ∀ index, ∃ observer : probe.Observer index index,
    ∀ term, theory.apply (probe.label observer) term = term
  compose : ∀ {first second third : probe.Index} (outer : probe.Observer second third)
    (inner : probe.Observer first second), ∃ observer : probe.Observer first third,
      ∀ term, theory.apply (probe.label observer) term =
        theory.apply (probe.label outer) (theory.apply (probe.label inner) term)

variable (theory) in
theorem fullProbe_closed : theory.fullProbe.Closed :=
  ⟨fun index => ⟨theory.identity index, theory.apply_identity⟩,
    fun outer inner => ⟨theory.compose outer inner, theory.apply_compose outer inner⟩⟩

/-- A family of relations, one per index, closed under the transitions that
the observers label, in both directions. -/
def Probe.IsBisimulation (probe : theory.Probe)
    (relation : (index : probe.Index) → theory.Term (probe.interface index) →
      theory.Term (probe.interface index) → Prop) : Prop :=
  (∀ {source : probe.Index} {left right : theory.Term (probe.interface source)},
    relation source left right →
      ∀ {target : probe.Index} (observer : probe.Observer source target)
        {next : theory.Term (probe.interface target)},
        theory.Transition left (probe.label observer) next →
          ∃ next', theory.Transition right (probe.label observer) next' ∧
            relation target next next') ∧
  (∀ {source : probe.Index} {left right : theory.Term (probe.interface source)},
    relation source left right →
      ∀ {target : probe.Index} (observer : probe.Observer source target)
        {next' : theory.Term (probe.interface target)},
        theory.Transition right (probe.label observer) next' →
          ∃ next, theory.Transition left (probe.label observer) next ∧
            relation target next next')

/-- **Bisimilarity as a probe sees it**: over the transitions that the
observers of the probe label. -/
def Probe.Bisimilar (probe : theory.Probe) {index : probe.Index}
    (left right : theory.Term (probe.interface index)) : Prop :=
  ∃ relation, probe.IsBisimulation relation ∧ relation index left right

namespace Probe

variable (probe : theory.Probe)

theorem bisimilar_of_equations {index : probe.Index}
    {left right : theory.Term (probe.interface index)}
    (equivalent : (theory.equations (probe.interface index)).r left right) :
    probe.Bisimilar left right := by
  refine ⟨fun index => (theory.equations (probe.interface index)).r, ⟨?_, ?_⟩, equivalent⟩
  · intro source left right related target observer next transition
    exact theory.rewrites_resp_left (theory.apply_resp _ related) transition
  · intro source left right related target observer next' transition
    obtain ⟨next, step, nextRelated⟩ := theory.rewrites_resp_left
      (theory.apply_resp _ ((theory.equations _).iseqv.symm related)) transition
    exact ⟨next, step, (theory.equations _).iseqv.symm nextRelated⟩

theorem bisimilar_refl {index : probe.Index} (term : theory.Term (probe.interface index)) :
    probe.Bisimilar term term :=
  probe.bisimilar_of_equations ((theory.equations _).iseqv.refl term)

variable {probe}

theorem bisimilar_symm {index : probe.Index}
    {left right : theory.Term (probe.interface index)}
    (bisimilar : probe.Bisimilar left right) : probe.Bisimilar right left := by
  obtain ⟨relation, ⟨forward, backward⟩, related⟩ := bisimilar
  refine ⟨fun index first second => relation index second first, ⟨?_, ?_⟩, related⟩
  · intro source left right flipped target observer next transition
    exact backward flipped observer transition
  · intro source left right flipped target observer next' transition
    exact forward flipped observer transition

theorem bisimilar_trans {index : probe.Index}
    {left middle right : theory.Term (probe.interface index)}
    (first : probe.Bisimilar left middle) (second : probe.Bisimilar middle right) :
    probe.Bisimilar left right := by
  obtain ⟨firstRelation, ⟨firstForward, firstBackward⟩, firstRelated⟩ := first
  obtain ⟨secondRelation, ⟨secondForward, secondBackward⟩, secondRelated⟩ := second
  refine ⟨fun index a c => ∃ b, firstRelation index a b ∧ secondRelation index b c,
    ⟨?_, ?_⟩, middle, firstRelated, secondRelated⟩
  · rintro source a c ⟨b, ab, bc⟩ target observer next transition
    obtain ⟨middleNext, middleStep, firstNext⟩ := firstForward ab observer transition
    obtain ⟨rightNext, rightStep, secondNext⟩ := secondForward bc observer middleStep
    exact ⟨rightNext, rightStep, middleNext, firstNext, secondNext⟩
  · rintro source a c ⟨b, ab, bc⟩ target observer next' transition
    obtain ⟨middleNext, middleStep, secondNext⟩ := secondBackward bc observer transition
    obtain ⟨leftNext, leftStep, firstNext⟩ := firstBackward ab observer middleStep
    exact ⟨leftNext, leftStep, middleNext, firstNext, secondNext⟩

/-- Bisimilarity as a probe sees it is closed under the static equivalence
on both sides. -/
theorem bisimilar_of_equations_of_equations {index : probe.Index}
    {left left' right right' : theory.Term (probe.interface index)}
    (leftEquivalent : (theory.equations _).r left' left)
    (bisimilar : probe.Bisimilar left right)
    (rightEquivalent : (theory.equations _).r right right') :
    probe.Bisimilar left' right' :=
  bisimilar_trans (probe.bisimilar_of_equations leftEquivalent)
    (bisimilar_trans bisimilar (probe.bisimilar_of_equations rightEquivalent))

/-- **Fewer observers, coarser bisimilarity.**  For a probe whose observers
are among another's at the same interfaces, bisimilarity as the larger probe
sees it implies bisimilarity as the smaller one does. -/
theorem Bisimilar.restrict {large : theory.Probe}
    (keep : {source target : large.Index} → large.Observer source target → Prop)
    {index : large.Index} {left right : theory.Term (large.interface index)}
    (bisimilar : large.Bisimilar left right) :
    Probe.Bisimilar
      { Index := large.Index
        interface := large.interface
        Observer := fun source target => {observer : large.Observer source target // keep observer}
        label := fun observer => large.label observer.1 } left right := by
  obtain ⟨relation, ⟨forward, backward⟩, related⟩ := bisimilar
  refine ⟨relation, ⟨?_, ?_⟩, related⟩
  · intro source left right pair target observer next transition
    exact forward pair observer.1 transition
  · intro source left right pair target observer next' transition
    exact backward pair observer.1 transition

/-- **Bisimilarity is a congruence** for a closed probe: every observer
preserves it. -/
theorem Bisimilar.apply (closed : probe.Closed) {source target : probe.Index}
    {left right : theory.Term (probe.interface source)}
    (bisimilar : probe.Bisimilar left right) (observer : probe.Observer source target) :
    probe.Bisimilar (theory.apply (probe.label observer) left)
      (theory.apply (probe.label observer) right) := by
  refine ⟨fun index first second =>
    ∃ (origin : probe.Index) (around : probe.Observer origin index)
      (a b : theory.Term (probe.interface origin)), probe.Bisimilar a b ∧
        first = theory.apply (probe.label around) a ∧
        second = theory.apply (probe.label around) b,
    ⟨?_, ?_⟩, source, observer, left, right, bisimilar, rfl, rfl⟩
  · rintro middle first second ⟨origin, around, a, b, related, rfl, rfl⟩ final outer next
      transition
    obtain ⟨relation, ⟨forward, backward⟩, pair⟩ := related
    obtain ⟨composite, composes⟩ := closed.compose outer around
    obtain ⟨hole, holes⟩ := closed.identity final
    have lifted : theory.Transition a (probe.label composite) next := by
      rw [ContextTheory.Transition, composes]
      exact transition
    obtain ⟨next', step, nextRelated⟩ := forward pair composite lifted
    refine ⟨next', ?_, final, hole, next, next',
      ⟨relation, ⟨forward, backward⟩, nextRelated⟩, (holes next).symm, (holes next').symm⟩
    rw [ContextTheory.Transition, composes] at step
    exact step
  · rintro middle first second ⟨origin, around, a, b, related, rfl, rfl⟩ final outer next'
      transition
    obtain ⟨relation, ⟨forward, backward⟩, pair⟩ := related
    obtain ⟨composite, composes⟩ := closed.compose outer around
    obtain ⟨hole, holes⟩ := closed.identity final
    have lifted : theory.Transition b (probe.label composite) next' := by
      rw [ContextTheory.Transition, composes]
      exact transition
    obtain ⟨next, step, nextRelated⟩ := backward pair composite lifted
    refine ⟨next, ?_, final, hole, next, next',
      ⟨relation, ⟨forward, backward⟩, nextRelated⟩, (holes next).symm, (holes next').symm⟩
    rw [ContextTheory.Transition, composes] at step
    exact step

end Probe

/-- **What the full probe sees refines reduction bisimilarity.**  Terms that
are bisimilar over all context-labelled transitions are bisimilar in the
theory at their interface. -/
theorem bisimilar_toGSLT {interface : theory.Interface}
    {left right : theory.Term interface}
    (bisimilar : theory.fullProbe.Bisimilar (index := interface) left right) :
    (theory.gslt interface).Bisimilar left right := by
  refine ⟨fun first second => theory.fullProbe.Bisimilar (index := interface) first second,
    ⟨?_, ?_⟩, bisimilar⟩
  · rintro first second ⟨relation, ⟨forward, backward⟩, pair⟩ next step
    obtain ⟨next', step', nextRelated⟩ := forward pair (theory.identity interface)
      ((theory.transition_identity_iff).mpr step)
    exact ⟨next', (theory.transition_identity_iff).mp step',
      relation, ⟨forward, backward⟩, nextRelated⟩
  · rintro first second ⟨relation, ⟨forward, backward⟩, pair⟩ next' step
    obtain ⟨next, step', nextRelated⟩ := backward pair (theory.identity interface)
      ((theory.transition_identity_iff).mpr step)
    exact ⟨next, (theory.transition_identity_iff).mp step',
      relation, ⟨forward, backward⟩, nextRelated⟩

/-- **The probe whose only observers are the holes sees reduction
bisimilarity**, no more and no less. -/
theorem reductionProbe_bisimilar_iff {interface : theory.Interface}
    {left right : theory.Term interface} :
    theory.reductionProbe.Bisimilar (index := interface) left right ↔
      (theory.gslt interface).Bisimilar left right := by
  constructor
  · intro bisimilar
    refine ⟨fun first second =>
      theory.reductionProbe.Bisimilar (index := interface) first second, ⟨?_, ?_⟩, bisimilar⟩
    · rintro first second ⟨relation, ⟨forward, backward⟩, pair⟩ next step
      obtain ⟨next', step', nextRelated⟩ :=
        forward pair (target := interface) ⟨⟨rfl⟩⟩ ((theory.transition_identity_iff).mpr step)
      exact ⟨next', (theory.transition_identity_iff).mp step',
        relation, ⟨forward, backward⟩, nextRelated⟩
    · rintro first second ⟨relation, ⟨forward, backward⟩, pair⟩ next' step
      obtain ⟨next, step', nextRelated⟩ :=
        backward pair (target := interface) ⟨⟨rfl⟩⟩ ((theory.transition_identity_iff).mpr step)
      exact ⟨next, (theory.transition_identity_iff).mp step',
        relation, ⟨forward, backward⟩, nextRelated⟩
  · intro bisimilar
    refine ⟨fun index first second => (theory.gslt index).Bisimilar first second,
      ⟨?_, ?_⟩, bisimilar⟩
    · rintro source first second ⟨relation, ⟨forward, backward⟩, pair⟩ target ⟨⟨same⟩⟩ next
        transition
      cases same
      obtain ⟨next', step', nextRelated⟩ :=
        forward pair ((theory.transition_identity_iff).mp transition)
      exact ⟨next', (theory.transition_identity_iff).mpr step',
        relation, ⟨forward, backward⟩, nextRelated⟩
    · rintro source first second ⟨relation, ⟨forward, backward⟩, pair⟩ target ⟨⟨same⟩⟩ next'
        transition
      cases same
      obtain ⟨next, step', nextRelated⟩ :=
        backward pair ((theory.transition_identity_iff).mp transition)
      exact ⟨next, (theory.transition_identity_iff).mpr step',
        relation, ⟨forward, backward⟩, nextRelated⟩

end ContextTheory

end Mettapedia.GSLT
