import Mettapedia.GSLT.Contexts.ContextMorphism

/-!
# The constant map

Under the naive definition, a morphism of theories is a map on terms that
preserves bisimilarity.  Every constant map is one: the image of any two
terms is one term, which is bisimilar to itself.  So there is a morphism from
any theory to any theory that has a term, and the category orders nothing.

A constant map on terms defines a static map in the sense of pairs, as soon as
every context of the source is assigned a context of the target that absorbs
the chosen term.  Its images are bisimilar for every probe, for the same reason.
What excludes it is the first non-degeneracy condition: it is not hosting,
as soon as the source has two inequivalent terms at one interface.
-/

set_option autoImplicit false
set_option linter.dupNamespace false

open CategoryTheory

namespace Mettapedia.GSLT

/-- **The constant map is a morphism under the naive definition.** -/
def GSLT.Morphism.constant (source target : GSLT) (term : target.Term) :
    GSLT.Morphism source target where
  toFun := fun _ => term
  preserves_bisim := fun _ => target.bisimilar_refl term

/-- **The naive category orders nothing**: there is a morphism from any
theory to any theory that has a term. -/
theorem GSLT.nonempty_hom (source target : GSLT) (inhabited : Nonempty target.Term) :
    Nonempty (source ⟶ target) :=
  inhabited.elim fun term => ⟨GSLT.Morphism.constant source target term⟩

/-- Any two theories with a term have morphisms both ways under the naive
definition. -/
theorem GSLT.nonempty_hom_both (first second : GSLT) (firstInhabited : Nonempty first.Term)
    (secondInhabited : Nonempty second.Term) :
    Nonempty (first ⟶ second) ∧ Nonempty (second ⟶ first) :=
  ⟨GSLT.nonempty_hom first second secondInhabited, GSLT.nonempty_hom second first firstInhabited⟩

universe u

variable {source target : ContextTheory.{u}}

/-- A constant static map of theories.  Every term goes to one
term of the target, and every context to a context that absorbs that term. -/
def ContextMap.constant (point : target.Interface) (value : target.Term point)
    (absorb : {arity : Type} → {holes : arity → source.Interface} →
      {result : source.Interface} → source.Context holes result →
        target.Context (fun _ : arity => point) point)
    (absorbs : ∀ {arity : Type} {holes : arity → source.Interface} {result : source.Interface}
      (context : source.Context holes result),
      (target.equations point).r (target.fill (absorb context) fun _ => value) value) :
    ContextMap source target where
  interface := fun _ => point
  term := fun _ => value
  context := absorb
  term_resp := fun _ => (target.equations point).iseqv.refl value
  equivariant := fun context _ => (target.equations point).iseqv.symm (absorbs context)

/-- **The constant map fails hosting**, as soon as the source has two
inequivalent terms at one interface. -/
theorem ContextMap.constant_not_hosting (point : target.Interface)
    (value : target.Term point)
    (absorb : {arity : Type} → {holes : arity → source.Interface} →
      {result : source.Interface} → source.Context holes result →
        target.Context (fun _ : arity => point) point)
    (absorbs : ∀ {arity : Type} {holes : arity → source.Interface} {result : source.Interface}
      (context : source.Context holes result),
      (target.equations point).r (target.fill (absorb context) fun _ => value) value)
    {origin : source.Interface} {first second : source.Term origin}
    (distinct : ¬ (source.equations origin).r first second) :
    ¬ (ContextMap.constant point value absorb absorbs).Hosting :=
  ContextMap.not_hosting_of_identifies _ distinct ((target.equations point).iseqv.refl value)

/-- Every two images of a constant map are bisimilar, independently of the
source's transitions.  This fact alone does not give transition transport. -/
theorem ContextMap.constant_bisimilar (point : target.Interface) (value : target.Term point)
    (absorb : {arity : Type} → {holes : arity → source.Interface} →
      {result : source.Interface} → source.Context holes result →
        target.Context (fun _ : arity => point) point)
    (absorbs : ∀ {arity : Type} {holes : arity → source.Interface} {result : source.Interface}
      (context : source.Context holes result),
      (target.equations point).r (target.fill (absorb context) fun _ => value) value)
    (probe : source.Probe) {index : probe.Index}
    (left right : source.Term (probe.interface index)) :
    ((ContextMap.constant point value absorb absorbs).push probe).Bisimilar
      (index := index) ((ContextMap.constant point value absorb absorbs).term left)
      ((ContextMap.constant point value absorb absorbs).term right) :=
  ContextTheory.Probe.bisimilar_refl (index := index)
    ((ContextMap.constant point value absorb absorbs).push probe) value

/-- A constant map can carry a source step only if its target value has a
self-transition.  Preservation of bisimilarity supplies no such transition. -/
theorem ContextMap.constant_requires_self_transition
    (point : target.Interface) (value : target.Term point)
    (absorb : {arity : Type} → {holes : arity → source.Interface} →
      {result : source.Interface} → source.Context holes result →
        target.Context (fun _ : arity => point) point)
    (absorbs : ∀ {arity : Type} {holes : arity → source.Interface} {result : source.Interface}
      (context : source.Context holes result),
      (target.equations point).r (target.fill (absorb context) fun _ => value) value)
    (preserves : (ContextMap.constant point value absorb absorbs).PreservesTransitions)
    {origin result : source.Interface} (label : source.Label origin result)
    {term : source.Term origin} {next : source.Term result}
    (step : source.Transition term label next) : target.rewrites value value := by
  have carried := preserves label step
  obtain ⟨answer, answerStep, answerEq⟩ := target.rewrites_resp_left (absorbs label) carried
  exact target.rewrites_resp_right answerStep ((target.equations _).iseqv.symm answerEq)

end Mettapedia.GSLT
