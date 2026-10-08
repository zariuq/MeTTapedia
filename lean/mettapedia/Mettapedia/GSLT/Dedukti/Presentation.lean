import Mettapedia.GSLT.Dedukti.Typing
import Mettapedia.GSLT.Contexts.HostingInvariants

/-!
# The λΠ-calculus modulo rewriting as a theory presented through its contexts

A theory of the λΠ-calculus modulo has two presentations as a triple
`(T, E, R)`, and they are different objects of the category of theories.

* `rewritingTheory theory`: the static equivalence is identity of terms and
  the reduction is one step of beta or of a declared rule.  This is the
  calculus as something that runs.
* `conversionTheory theory`: the static equivalence is the declared
  conversion and there is no reduction.  This is the calculus as its type
  checker sees it: a computation is not an event, and a term is not kept
  apart from its reducts.

A third presentation, with the declared conversion as static equivalence and
the steps as reduction, does not exist: reduction would have to be closed
under the static equivalence, and a redex is convertible to its normal form,
which has no step (`conv_not_static_for_step`).

The identity on terms is a map from the first to the second (`silence`).  It
is never hosting when the theory has a step (`silence_not_hosting`): it sends
a transition to none and identifies a redex with its contractum.

Contexts are terms with named holes (`TermContext`).  A hole may occur several
times, beneath binders, or not at all; filling is textual.  The existing
one-hole contexts of `LFContextualBetaEta` are the contexts in which the hole
occurs once (`TermContext.ofContext`).

`HoleSyntax` is the common shape of a syntax with holes; `HoleSyntax.theory`
builds a theory with one interface from it, a static equivalence that filling
respects, and a reduction.  It is used again for the source of a translation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dedukti

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFTyping (lift subst subst0)
open Mettapedia.GSLT.LanguageDef.LFContextualBetaEta (Context)
open Mettapedia.Logic.Relation (Confluent IsNormal)

/-! ## Syntax with holes -/

/-- A syntax with named holes over a carrier of terms: contexts, filling,
plugging contexts into contexts, the hole, and the context with no hole. -/
structure HoleSyntax (Carrier : Type) where
  Hole : Type → Type
  fill : {slots : Type} → (slots → Carrier) → Hole slots → Carrier
  bind : {slots inner : Type} → (slots → Hole inner) → Hole slots → Hole inner
  hole : {slots : Type} → slots → Hole slots
  constant : {slots : Type} → Carrier → Hole slots
  fill_bind : ∀ {slots inner : Type} (filling : inner → Carrier) (plugged : slots → Hole inner)
    (context : Hole slots),
    fill filling (bind plugged context) = fill (fun slot => fill filling (plugged slot)) context
  fill_hole : ∀ {slots : Type} (filling : slots → Carrier) (slot : slots),
    fill filling (hole slot) = filling slot
  fill_constant : ∀ {slots : Type} (filling : slots → Carrier) (term : Carrier),
    fill filling (constant term) = term

/-- **The theory of a syntax with holes**, with one interface. -/
def HoleSyntax.theory {Carrier : Type} (shape : HoleSyntax Carrier) (equations : Setoid Carrier)
    (rewrites : Carrier → Carrier → Prop)
    (fill_resp : ∀ {slots : Type} (context : shape.Hole slots) {first second : slots → Carrier},
      (∀ slot, equations.r (first slot) (second slot)) →
        equations.r (shape.fill first context) (shape.fill second context))
    (left : ∀ {term term' next : Carrier}, equations.r term term' → rewrites term next →
      ∃ next', rewrites term' next' ∧ equations.r next next')
    (right : ∀ {term next next' : Carrier}, rewrites term next → equations.r next next' →
      rewrites term next') : ContextTheory.{0} where
  Interface := Unit
  Term := fun _ => Carrier
  equations := fun _ => equations
  rewrites := rewrites
  rewrites_resp_left := left
  rewrites_resp_right := right
  Context := fun {arity} _ _ => shape.Hole arity
  fill := fun context filling => shape.fill filling context
  fill_resp := fun context _ _ related => fill_resp context related
  identity := fun _ => shape.hole ()
  fill_identity := fun _ filling => shape.fill_hole filling ()
  plug := fun {_ _ _ innerArity _} context inner =>
    shape.bind (fun index => shape.bind
      (fun position => shape.hole (⟨index, position⟩ : Σ index, innerArity index)) (inner index))
      context
  fill_plug := fun context inner filling => by
    rw [shape.fill_bind]
    congr 1
    funext index
    rw [shape.fill_bind]
    congr 1
    funext position
    exact shape.fill_hole filling _
  relabel := fun rename _ context => shape.bind (fun index => shape.hole (rename index)) context
  fill_relabel := fun rename _ context filling => by
    rw [shape.fill_bind]
    congr 1
    funext index
    exact shape.fill_hole filling _
  constant := fun term => shape.constant term
  fill_constant := fun term filling => shape.fill_constant filling term

/-! ## Terms with holes -/

/-- A λΠ term with named holes. -/
inductive TermContext (slots : Type) : Type where
  | hole : slots → TermContext slots
  | srt : Srt → TermContext slots
  | con : String → TermContext slots
  | var : Nat → TermContext slots
  | pi : TermContext slots → TermContext slots → TermContext slots
  | lam : TermContext slots → TermContext slots → TermContext slots
  | app : TermContext slots → TermContext slots → TermContext slots

namespace TermContext

variable {slots inner : Type}

/-- Fill the holes with terms.  Filling is textual: a hole beneath a binder
captures. -/
def fill (filling : slots → Term) : TermContext slots → Term
  | .hole slot => filling slot
  | .srt sort => .srt sort
  | .con name => .con name
  | .var index => .var index
  | .pi domain body => .pi (domain.fill filling) (body.fill filling)
  | .lam domain body => .lam (domain.fill filling) (body.fill filling)
  | .app function argument => .app (function.fill filling) (argument.fill filling)

/-- Plug contexts into the holes. -/
def bind (plugged : slots → TermContext inner) : TermContext slots → TermContext inner
  | .hole slot => plugged slot
  | .srt sort => .srt sort
  | .con name => .con name
  | .var index => .var index
  | .pi domain body => .pi (domain.bind plugged) (body.bind plugged)
  | .lam domain body => .lam (domain.bind plugged) (body.bind plugged)
  | .app function argument => .app (function.bind plugged) (argument.bind plugged)

/-- A term, as a context with no hole. -/
def ofTerm : Term → TermContext slots
  | .srt sort => .srt sort
  | .con name => .con name
  | .var index => .var index
  | .pi domain body => .pi (ofTerm domain) (ofTerm body)
  | .lam domain body => .lam (ofTerm domain) (ofTerm body)
  | .app function argument => .app (ofTerm function) (ofTerm argument)

theorem fill_bind (filling : inner → Term) (plugged : slots → TermContext inner)
    (context : TermContext slots) :
    (context.bind plugged).fill filling = context.fill fun slot => (plugged slot).fill filling := by
  induction context with
  | hole slot => rfl
  | srt sort => rfl
  | con name => rfl
  | var index => rfl
  | pi domain body ihDomain ihBody => simp [bind, fill, ihDomain, ihBody]
  | lam domain body ihDomain ihBody => simp [bind, fill, ihDomain, ihBody]
  | app function argument ihFunction ihArgument => simp [bind, fill, ihFunction, ihArgument]

theorem fill_ofTerm (filling : slots → Term) (term : Term) :
    (ofTerm term : TermContext slots).fill filling = term := by
  induction term with
  | srt sort => rfl
  | con name => rfl
  | var index => rfl
  | pi domain body ihDomain ihBody => simp [ofTerm, fill, ihDomain, ihBody]
  | lam domain body ihDomain ihBody => simp [ofTerm, fill, ihDomain, ihBody]
  | app function argument ihFunction ihArgument => simp [ofTerm, fill, ihFunction, ihArgument]

/-- An existing one-hole context, as a context whose hole occurs once. -/
def ofContext : Context → TermContext Unit
  | .hole => .hole ()
  | .piDomain rest body => .pi (ofContext rest) (ofTerm body)
  | .piBody domain rest => .pi (ofTerm domain) (ofContext rest)
  | .lamDomain rest body => .lam (ofContext rest) (ofTerm body)
  | .lamBody domain rest => .lam (ofTerm domain) (ofContext rest)
  | .appFunction rest argument => .app (ofContext rest) (ofTerm argument)
  | .appArgument function rest => .app (ofTerm function) (ofContext rest)

/-- Filling the context of a one-hole context is plugging it. -/
theorem fill_ofContext (context : Context) (term : Term) :
    (ofContext context).fill (fun _ => term) = context.plug term := by
  induction context with
  | hole => rfl
  | piDomain rest body ih => simp [ofContext, fill, Context.plug, ih, fill_ofTerm]
  | piBody domain rest ih => simp [ofContext, fill, Context.plug, ih, fill_ofTerm]
  | lamDomain rest body ih => simp [ofContext, fill, Context.plug, ih, fill_ofTerm]
  | lamBody domain rest ih => simp [ofContext, fill, Context.plug, ih, fill_ofTerm]
  | appFunction rest argument ih => simp [ofContext, fill, Context.plug, ih, fill_ofTerm]
  | appArgument function rest ih => simp [ofContext, fill, Context.plug, ih, fill_ofTerm]

end TermContext

/-- The λΠ terms as a syntax with holes. -/
def termShape : HoleSyntax Term where
  Hole := TermContext
  fill := TermContext.fill
  bind := TermContext.bind
  hole := TermContext.hole
  constant := TermContext.ofTerm
  fill_bind := TermContext.fill_bind
  fill_hole := fun _ _ => rfl
  fill_constant := TermContext.fill_ofTerm

variable {theory : Theory}

/-- Conversion is a congruence for every context. -/
theorem Conv.fill {slots : Type} (context : TermContext slots) {first second : slots → Term}
    (convertible : ∀ slot, Conv theory (first slot) (second slot)) :
    Conv theory (context.fill first) (context.fill second) := by
  induction context with
  | hole slot => exact convertible slot
  | srt sort => exact .refl _
  | con name => exact .refl _
  | var index => exact .refl _
  | pi domain body ihDomain ihBody => exact Conv.pi ihDomain ihBody
  | lam domain body ihDomain ihBody => exact Conv.lam ihDomain ihBody
  | app function argument ihFunction ihArgument => exact Conv.app ihFunction ihArgument

/-- Reduction is closed under every context. -/
theorem Reduces.fill {slots : Type} (context : TermContext slots) {first second : slots → Term}
    (reduces : ∀ slot, Reduces theory (first slot) (second slot)) :
    Reduces theory (context.fill first) (context.fill second) := by
  induction context with
  | hole slot => exact reduces slot
  | srt sort => exact .refl
  | con name => exact .refl
  | var index => exact .refl
  | pi domain body ihDomain ihBody => exact Reduces.pi ihDomain ihBody
  | lam domain body ihDomain ihBody => exact Reduces.lam ihDomain ihBody
  | app function argument ihFunction ihArgument => exact Reduces.app ihFunction ihArgument

/-! ## The two presentations -/

/-- **The calculus as it runs**: terms compared by identity, reduced by one
step of beta or of a declared rule. -/
def rewritingTheory (theory : Theory) : ContextTheory.{0} :=
  termShape.theory ⟨Eq, ⟨fun _ => rfl, fun same => same.symm, fun first second => first.trans second⟩⟩
    (Step theory)
    (fun context _ _ same => congrArg (fun filling => TermContext.fill filling context) (funext same))
    (fun same step => ⟨_, same ▸ step, rfl⟩)
    (fun step same => same ▸ step)

/-- **The calculus as its type checker sees it**: terms compared by the
declared conversion, and no reduction. -/
def conversionTheory (theory : Theory) : ContextTheory.{0} :=
  termShape.theory ⟨Conv theory, Relation.EqvGen.is_equivalence _⟩ (fun _ _ => False)
    (fun context _ _ convertible => Conv.fill context convertible)
    (fun _ step => step.elim)
    (fun step _ => step)

@[simp] theorem rewritingTheory_rewrites {source target : Term} :
    (rewritingTheory theory).rewrites (interface := ()) source target ↔ Step theory source target :=
  Iff.rfl

@[simp] theorem rewritingTheory_equations {left right : Term} :
    ((rewritingTheory theory).equations ()).r left right ↔ left = right :=
  Iff.rfl

@[simp] theorem conversionTheory_equations {left right : Term} :
    ((conversionTheory theory).equations ()).r left right ↔ Conv theory left right :=
  Iff.rfl

/-- **A confluent calculus is a confluent theory.** -/
theorem rewritingTheory_confluentUpTo (confluent : Confluent (Step theory)) :
    (rewritingTheory theory).ConfluentUpTo := by
  intro _ source left right leftReaches rightReaches
  obtain ⟨common, leftJoin, rightJoin⟩ := confluent source left right leftReaches rightReaches
  exact ⟨common, common, leftJoin, rightJoin, rfl⟩

/-- **The reduction of the calculus is closed under contexts**, for every
theory: a context cannot withdraw a rule. -/
theorem rewritingTheory_contextClosed (theory : Theory) : (rewritingTheory theory).ContextClosed := by
  intro _ _ label term next step
  exact ⟨_, Reduces.fill label fun _ => Relation.ReflTransGen.single step, rfl⟩

/-- **The declared conversion cannot be the static equivalence of the steps.**
Reduction would have to be closed under it; a redex is convertible to its
contractum, and a sort has no step. -/
theorem conv_not_static_for_step (headed : theory.Headed) :
    ¬ ∀ term term' next : Term, Conv theory term term' → Step theory term next →
      ∃ next', Step theory term' next' ∧ Conv theory next next' := by
  intro closed
  have step : Step theory (.app (.lam (.srt .type) (.var 0)) (.srt .kind)) (.srt .kind) :=
    Step.root (.beta (.srt .type) (.var 0) (.srt .kind))
  obtain ⟨next', impossible, _⟩ := closed _ (.srt .kind) _ (.rel _ _ step) step
  exact srt_normal headed .kind _ impossible

/-! ## Forgetting the computation -/

/-- **The identity on terms, from the calculus as it runs to the calculus as
its checker sees it.** -/
def silence (theory : Theory) : ContextMap (rewritingTheory theory) (conversionTheory theory) where
  interface := fun _ => ()
  term := fun term => term
  context := fun context => context
  term_resp := fun same => Conv.of_eq same
  equivariant := fun _ _ => Relation.EqvGen.refl _

/-- **Forgetting the computation is not hosting**, as soon as the theory has
one step: the step is sent to no transition. -/
theorem silence_not_preserves {source target : Term} (step : Step theory source target) :
    ¬ (silence theory).PreservesTransitions := by
  intro preserves
  have transition : (rewritingTheory theory).Transition (source := ()) source
      ((rewritingTheory theory).identity ()) target := step
  exact preserves _ transition

theorem silence_not_hosting {source target : Term} (step : Step theory source target) :
    ¬ (silence theory).Hosting :=
  fun hosting => silence_not_preserves step hosting.preserves

/-- It also identifies terms that were apart: a redex and its contractum. -/
theorem silence_identifies {source target : Term} (step : Step theory source target) :
    ((conversionTheory theory).equations ()).r ((silence theory).term (origin := ()) source)
      ((silence theory).term (origin := ()) target) :=
  .rel _ _ step

/-- In the calculus as its checker sees it nothing reduces, so every term is
normal. -/
theorem conversionTheory_normal (term : Term) :
    IsNormal ((conversionTheory theory).rewrites (interface := ())) term :=
  fun _ step => step

/-- The calculus as its checker sees it is confluent and terminating, for
every theory: both properties are about reduction, and it has none. -/
theorem conversionTheory_confluentUpTo (theory : Theory) : (conversionTheory theory).ConfluentUpTo := by
  intro _ source left right leftReaches rightReaches
  have leftSame := (conversionTheory_normal (theory := theory) source).reflTransGen_eq leftReaches
  have rightSame := (conversionTheory_normal (theory := theory) source).reflTransGen_eq rightReaches
  subst leftSame
  subst rightSame
  exact ⟨_, _, .refl, .refl, Relation.EqvGen.refl _⟩

theorem conversionTheory_terminating (theory : Theory) : (conversionTheory theory).Terminating :=
  fun _ => ⟨fun term => ⟨term, fun _ step => step.elim⟩⟩

#print axioms HoleSyntax.theory
#print axioms rewritingTheory
#print axioms conversionTheory
#print axioms rewritingTheory_confluentUpTo
#print axioms rewritingTheory_contextClosed
#print axioms conv_not_static_for_step
#print axioms silence_not_hosting

end Mettapedia.GSLT.Dedukti
