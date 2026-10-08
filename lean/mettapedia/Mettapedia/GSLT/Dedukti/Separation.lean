import Mettapedia.GSLT.Dedukti.CousineauDowekMorphism
import Mettapedia.TypeTheory.MaterialSets.Hypersets.AntiFoundation

/-!
# What separates evaluation by directed rules from the λΠ-calculus modulo

The λΠ-calculus modulo compares terms by the equivalence that its rewrite
rules generate, and it asks of every theory that reduction be confluent and,
on typed terms, terminating.  A language whose evaluation is by directed
rules, with several results, a mutable space of rules, and cyclic values,
asks none of this.  Each difference is stated here as a property of theories
that a hosting map carries back from its target
(`Mettapedia/GSLT/Contexts/HostingInvariants.lean`), with a witness on each
side.  The witnesses are small theories with the named feature.  They are not
a formalization of any one evaluator.

## Several results

`withChoice theory` adds to a theory a binary symbol with the two rules
`choose x y ⟶ x` and `choose x y ⟶ y`.

* Read as a calculus that runs, the extension is conservative: on the terms
  without the new symbol it has exactly the steps of the theory, and the
  inclusion is hosting (`includeAvoiding_hosting`).
* It is hosted by no confluent theory (`withChoice_not_hosted_by_confluent`):
  not by a calculus that runs under its confluence requirement, and not by any
  calculus as its checker sees it (`withChoice_not_hosted_by_conversion`).
  So the theory and its extension are different degrees of the hosting
  preorder (`choice_strictly_above`).
* Read as a calculus compared by conversion, the extension identifies every
  two terms (`withChoice_conv_all`), and typing collapses: a term of one type
  has every type (`withChoice_typing_collapse`).  Several results and
  conversion by rewriting cannot be had together.

## A mutable space

`spaceTheory` is a model with two instructions that add and retract one rule
and a call that succeeds while the rule is present.  Its reduction is not
closed under contexts: the retracting context disables a step of its hole
(`space_call_disabled`).  The reduction of every theory of the λΠ-calculus
modulo is closed under contexts, since no context can withdraw a rule, so
none hosts it (`space_not_hosted_by_rewriting`).

## Cyclic values

A reading of hypersets as terms that sends membership to nonempty reduction
cannot send the hyperset `Ω = {Ω}` to a term from which every reduction is
finite (`no_terminating_reading_of_membership`).  The hypersets are the
existing ones, with their existing `quineAtom`.

## Evidence of computation

In the calculus as it runs, a step is a transition.  In the calculus as its
checker sees it, a term and its reduct are one term, and the typing judgment
records no trace of a conversion: one term has two types that differ by a
rule (`silent_conversion`).  The map between the two presentations is never
hosting when there is a step (`silence_not_hosting`, in `Presentation`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dedukti

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFTyping (lift subst subst0 Ctx)
open Mettapedia.GSLT.LanguageDef.LFProfile (Profile ProductRule)
open Mettapedia.GSLT.LanguageDef.LFContextualBetaEta (Context)
open Mettapedia.Logic.Relation (Confluent IsNormal)
open Mettapedia.TypeTheory.MaterialSets.Hypersets (HSet)

/-! ## Several results -/

/-- The name of the choice symbol. -/
def chooseName : String := "choose"

/-- `choose a b`. -/
def choose (left right : Term) : Term := .app (.app (.con chooseName) left) right

/-- `choose x y ⟶ x`. -/
def chooseLeft : RewriteRule := ⟨choose (.var 1) (.var 0), .var 1⟩

/-- `choose x y ⟶ y`. -/
def chooseRight : RewriteRule := ⟨choose (.var 1) (.var 0), .var 0⟩

/-- **A theory with a choice between two results.** -/
def withChoice (theory : Theory) : Theory where
  constType := theory.constType
  body := theory.body
  rule := fun rule => theory.rule rule ∨ rule = chooseLeft ∨ rule = chooseRight

variable {theory : Theory}

theorem withChoice_extends (theory : Theory) : theory.Extends (withChoice theory) :=
  ⟨fun _ _ same => same, fun _ _ same => same, fun _ member => Or.inl member⟩

theorem withChoice_headed (headed : theory.Headed) : (withChoice theory).Headed := by
  rintro rule (member | rfl | rfl)
  · exact headed rule member
  · exact ⟨chooseName, rfl⟩
  · exact ⟨chooseName, rfl⟩

theorem step_choose_left (theory : Theory) (left right : Term) :
    Step (withChoice theory) (choose left right) left := by
  have root := RootStep.rule (theory := withChoice theory) (rule := chooseLeft)
    (fun index => if index = 0 then right else left) (Or.inr (Or.inl rfl))
  simpa [chooseLeft, choose, inst, instantiate, lift_zero] using Step.root root

theorem step_choose_right (theory : Theory) (left right : Term) :
    Step (withChoice theory) (choose left right) right := by
  have root := RootStep.rule (theory := withChoice theory) (rule := chooseRight)
    (fun index => if index = 0 then right else left) (Or.inr (Or.inr rfl))
  simpa [chooseRight, choose, inst, instantiate, lift_zero] using Step.root root

/-- **Compared by conversion, a theory with choice identifies every two
terms.** -/
theorem withChoice_conv_all (theory : Theory) (left right : Term) :
    Conv (withChoice theory) left right :=
  .trans _ _ _ (.symm _ _ (.rel _ _ (step_choose_left theory left right)))
    (.rel _ _ (step_choose_right theory left right))

/-- **Typing collapses**: in a theory with choice a term of one type has every
type. -/
theorem withChoice_typing_collapse {profile : Profile} {context : Ctx} {term type other : Term}
    {sort : Srt} (typed : HasType profile (withChoice theory) context term type)
    (formed : HasType profile (withChoice theory) context other (.srt sort)) :
    HasType profile (withChoice theory) context term other :=
  .conv typed (withChoice_conv_all theory type other) formed

/-- A theory with choice is not confluent. -/
theorem withChoice_not_confluent (headed : theory.Headed) :
    ¬ Confluent (Step (withChoice theory)) := by
  intro confluent
  have joinable := confluent (choose (.srt .type) (.srt .kind)) (.srt .type) (.srt .kind)
    (.single (step_choose_left theory _ _)) (.single (step_choose_right theory _ _))
  exact not_joinable_of_normal (srt_normal (withChoice_headed headed) .type)
    (srt_normal (withChoice_headed headed) .kind) (by decide) joinable

/-- **No confluent theory hosts a theory with choice**, read as a calculus
that runs. -/
theorem withChoice_not_hosted_by_confluent (headed : theory.Headed) {target : ContextTheory.{0}}
    (confluent : target.ConfluentUpTo)
    (map : ContextMap (rewritingTheory (withChoice theory)) target) : ¬ map.Hosting :=
  map.not_hosting_of_branch (interface := ()) (term := choose (.srt .type) (.srt .kind))
    (first := .srt .type) (second := .srt .kind)
    (step_choose_left theory _ _) (step_choose_right theory _ _)
    (srt_normal (withChoice_headed headed) .type) (srt_normal (withChoice_headed headed) .kind)
    (fun same => by cases same) confluent

/-- In particular no calculus that runs under the confluence requirement
hosts it. -/
theorem withChoice_not_hosted_by_rewriting (headed : theory.Headed) {host : Theory}
    (confluent : Confluent (Step host))
    (map : ContextMap (rewritingTheory (withChoice theory)) (rewritingTheory host)) :
    ¬ map.Hosting :=
  withChoice_not_hosted_by_confluent headed (rewritingTheory_confluentUpTo confluent) map

/-- Nor does any calculus as its checker sees it, with no hypothesis on the
host. -/
theorem withChoice_not_hosted_by_conversion (headed : theory.Headed) (host : Theory)
    (map : ContextMap (rewritingTheory (withChoice theory)) (conversionTheory host)) :
    ¬ map.Hosting :=
  withChoice_not_hosted_by_confluent headed (conversionTheory_confluentUpTo host) map

/-! ### The theory inside its extension -/

/-- A constant does not occur in a term. -/
def Avoids (name : String) : Term → Prop
  | .con other => other ≠ name
  | .srt _ => True
  | .var _ => True
  | .pi domain body => Avoids name domain ∧ Avoids name body
  | .lam domain body => Avoids name domain ∧ Avoids name body
  | .app function argument => Avoids name function ∧ Avoids name argument

theorem Avoids.lift {name : String} {term : Term} (avoids : Avoids name term) :
    ∀ amount cutoff : Nat, Avoids name (lift amount cutoff term) := by
  induction term with
  | var index => intro amount cutoff; trivial
  | srt sort => intro amount cutoff; trivial
  | con other => intro amount cutoff; exact avoids
  | pi domain body ihDomain ihBody =>
      intro amount cutoff; exact ⟨ihDomain avoids.1 _ _, ihBody avoids.2 _ _⟩
  | lam domain body ihDomain ihBody =>
      intro amount cutoff; exact ⟨ihDomain avoids.1 _ _, ihBody avoids.2 _ _⟩
  | app function argument ihFunction ihArgument =>
      intro amount cutoff; exact ⟨ihFunction avoids.1 _ _, ihArgument avoids.2 _ _⟩

theorem Avoids.subst {name : String} {term : Term} (avoids : Avoids name term) :
    ∀ (target : Nat) {replacement : Term}, Avoids name replacement →
      Avoids name (subst target replacement term) := by
  induction term with
  | var index =>
      intro target replacement replaced
      simp only [LFTyping.subst]
      split
      · exact replaced
      · split <;> trivial
  | srt sort => intro target replacement _; trivial
  | con other => intro target replacement _; exact avoids
  | pi domain body ihDomain ihBody =>
      intro target replacement replaced
      exact ⟨ihDomain avoids.1 _ replaced, ihBody avoids.2 _ (replaced.lift 1 0)⟩
  | lam domain body ihDomain ihBody =>
      intro target replacement replaced
      exact ⟨ihDomain avoids.1 _ replaced, ihBody avoids.2 _ (replaced.lift 1 0)⟩
  | app function argument ihFunction ihArgument =>
      intro target replacement replaced
      exact ⟨ihFunction avoids.1 _ replaced, ihArgument avoids.2 _ replaced⟩

theorem Avoids.of_plug {name : String} (context : Context) {term : Term}
    (avoids : Avoids name (context.plug term)) : Avoids name term := by
  induction context with
  | hole => exact avoids
  | piDomain rest body ih => exact ih avoids.1
  | piBody domain rest ih => exact ih avoids.2
  | lamDomain rest body ih => exact ih avoids.1
  | lamBody domain rest ih => exact ih avoids.2
  | appFunction rest argument ih => exact ih avoids.1
  | appArgument function rest ih => exact ih avoids.2

theorem Avoids.plug {name : String} (context : Context) {term other : Term}
    (avoids : Avoids name (context.plug term)) (replaced : Avoids name other) :
    Avoids name (context.plug other) := by
  induction context with
  | hole => exact replaced
  | piDomain rest body ih => exact ⟨ih avoids.1, avoids.2⟩
  | piBody domain rest ih => exact ⟨avoids.1, ih avoids.2⟩
  | lamDomain rest body ih => exact ⟨ih avoids.1, avoids.2⟩
  | lamBody domain rest ih => exact ⟨avoids.1, ih avoids.2⟩
  | appFunction rest argument ih => exact ⟨ih avoids.1, avoids.2⟩
  | appArgument function rest ih => exact ⟨avoids.1, ih avoids.2⟩

/-- A constant does not occur in a context. -/
def TermContext.Avoids (name : String) {slots : Type} : TermContext slots → Prop
  | .hole _ => True
  | .con other => other ≠ name
  | .srt _ => True
  | .var _ => True
  | .pi domain body => Avoids name domain ∧ Avoids name body
  | .lam domain body => Avoids name domain ∧ Avoids name body
  | .app function argument => Avoids name function ∧ Avoids name argument

theorem TermContext.avoids_fill {name : String} {slots : Type} {context : TermContext slots}
    (avoids : context.Avoids name) {filling : slots → Term}
    (fillings : ∀ slot, Dedukti.Avoids name (filling slot)) :
    Dedukti.Avoids name (context.fill filling) := by
  induction context with
  | hole slot => exact fillings slot
  | srt sort => trivial
  | con other => exact avoids
  | var index => trivial
  | pi domain body ihDomain ihBody => exact ⟨ihDomain avoids.1, ihBody avoids.2⟩
  | lam domain body ihDomain ihBody => exact ⟨ihDomain avoids.1, ihBody avoids.2⟩
  | app function argument ihFunction ihArgument => exact ⟨ihFunction avoids.1, ihArgument avoids.2⟩

theorem TermContext.avoids_bind {name : String} {slots inner : Type} {context : TermContext slots}
    (avoids : context.Avoids name) {plugged : slots → TermContext inner}
    (pluggings : ∀ slot, (plugged slot).Avoids name) : (context.bind plugged).Avoids name := by
  induction context with
  | hole slot => exact pluggings slot
  | srt sort => trivial
  | con other => exact avoids
  | var index => trivial
  | pi domain body ihDomain ihBody => exact ⟨ihDomain avoids.1, ihBody avoids.2⟩
  | lam domain body ihDomain ihBody => exact ⟨ihDomain avoids.1, ihBody avoids.2⟩
  | app function argument ihFunction ihArgument => exact ⟨ihFunction avoids.1, ihArgument avoids.2⟩

theorem TermContext.avoids_ofTerm {name : String} {slots : Type} {term : Term}
    (avoids : Dedukti.Avoids name term) : (TermContext.ofTerm term : TermContext slots).Avoids name := by
  induction term with
  | var index => trivial
  | srt sort => trivial
  | con other => exact avoids
  | pi domain body ihDomain ihBody => exact ⟨ihDomain avoids.1, ihBody avoids.2⟩
  | lam domain body ihDomain ihBody => exact ⟨ihDomain avoids.1, ihBody avoids.2⟩
  | app function argument ihFunction ihArgument => exact ⟨ihFunction avoids.1, ihArgument avoids.2⟩

/-- The terms in which a constant does not occur, as a syntax with holes. -/
def avoidingShape (name : String) : HoleSyntax {term : Term // Avoids name term} where
  Hole := fun slots => {context : TermContext slots // context.Avoids name}
  fill := fun filling context =>
    ⟨context.1.fill fun slot => (filling slot).1,
      TermContext.avoids_fill context.2 fun slot => (filling slot).2⟩
  bind := fun plugged context =>
    ⟨context.1.bind fun slot => (plugged slot).1,
      TermContext.avoids_bind context.2 fun slot => (plugged slot).2⟩
  hole := fun slot => ⟨.hole slot, trivial⟩
  constant := fun term => ⟨TermContext.ofTerm term.1, TermContext.avoids_ofTerm term.2⟩
  fill_bind := fun _ _ context => Subtype.ext (TermContext.fill_bind _ _ context.1)
  fill_hole := fun _ _ => rfl
  fill_constant := fun _ term => Subtype.ext (TermContext.fill_ofTerm _ term.1)

/-- **A calculus as it runs, on the terms in which a constant does not
occur.** -/
def rewritingTheoryAvoiding (name : String) (theory : Theory) : ContextTheory.{0} :=
  (avoidingShape name).theory
    ⟨Eq, ⟨fun _ => rfl, fun same => same.symm, fun first second => first.trans second⟩⟩
    (fun source target => Step theory source.1 target.1)
    (fun context _ _ same =>
      congrArg (fun filling => (avoidingShape name).fill filling context) (funext same))
    (fun same step => ⟨_, same ▸ step, rfl⟩)
    (fun step same => same ▸ step)

/-- The steps of a theory keep a constant out of a term. -/
def Theory.PreservesAvoiding (theory : Theory) (name : String) : Prop :=
  ∀ source target : Term, Avoids name source → Step theory source target → Avoids name target

/-- Beta introduces no constant. -/
theorem empty_preservesAvoiding (name : String) : Theory.empty.PreservesAvoiding name := by
  intro source target avoids step
  cases step with
  | inContext context root =>
      refine Avoids.plug context avoids ?_
      have inner := Avoids.of_plug context avoids
      cases root with
      | beta domain body argument => exact Avoids.subst inner.1.2 0 inner.2
      | delta defined => cases defined
      | rule assignment member => exact member.elim

/-- On a term without the choice symbol, a step of the extension is a step of
the theory. -/
theorem step_of_avoiding {source target : Term} (avoids : Avoids chooseName source)
    (step : Step (withChoice theory) source target) : Step theory source target := by
  cases step with
  | inContext context root =>
      have inner := Avoids.of_plug context avoids
      refine .inContext context ?_
      cases root with
      | beta domain body argument => exact .beta domain body argument
      | delta defined => exact .delta defined
      | rule assignment member =>
          rcases member with member | rfl | rfl
          · exact .rule assignment member
          · exact absurd rfl inner.1.1
          · exact absurd rfl inner.1.1

/-- The inclusion of a theory into its extension by choice. -/
def includeAvoiding (theory : Theory) :
    ContextMap (rewritingTheoryAvoiding chooseName theory) (rewritingTheory (withChoice theory)) where
  interface := fun _ => ()
  term := fun term => term.1
  context := fun context => context.1
  term_resp := fun same => congrArg Subtype.val same
  equivariant := fun _ _ => rfl

/-- **The extension by choice hosts the theory**: on the terms without the
new symbol nothing is identified, no step is lost and none is added. -/
theorem includeAvoiding_hosting (closed : theory.PreservesAvoiding chooseName) :
    (includeAvoiding theory).Hosting := by
  rw [ContextMap.hosting_iff]
  refine ⟨fun same => Subtype.ext same, ?_, ?_⟩
  · intro _ _ label term next step
    exact Step.mono (withChoice_extends theory) step
  · intro _ _ label term next step
    have avoids : Avoids chooseName (label.1.fill fun _ => term.1) :=
      TermContext.avoids_fill label.2 fun _ => term.2
    have inside := step_of_avoiding avoids step
    exact ⟨⟨next, closed _ _ avoids inside⟩, inside, rfl⟩

/-- A confluent calculus is confluent on the terms without a constant, when
its steps keep the constant out. -/
theorem rewritingTheoryAvoiding_confluentUpTo {name : String}
    (closed : theory.PreservesAvoiding name) (confluent : Confluent (Step theory)) :
    (rewritingTheoryAvoiding name theory).ConfluentUpTo := by
  intro _ source left right leftReaches rightReaches
  have forget : ∀ {first second : {term : Term // Avoids name term}},
      (rewritingTheoryAvoiding name theory).Reaches (interface := ()) first second →
        Reduces theory first.1 second.1 := by
    intro first second reaches
    induction reaches with
    | refl => exact .refl
    | tail _ step ih => exact ih.tail step
  have recover : ∀ (first : {term : Term // Avoids name term}) {final : Term},
      Reduces theory first.1 final → ∃ avoids : Avoids name final,
        (rewritingTheoryAvoiding name theory).Reaches (interface := ()) first ⟨final, avoids⟩ := by
    intro first final reduces
    induction reduces with
    | refl => exact ⟨first.2, .refl⟩
    | tail _ step ih =>
        obtain ⟨avoids, reaches⟩ := ih
        exact ⟨closed _ _ avoids step, reaches.tail step⟩
  obtain ⟨common, leftJoin, rightJoin⟩ :=
    confluent source.1 left.1 right.1 (forget leftReaches) (forget rightReaches)
  obtain ⟨avoids, leftFinal⟩ := recover left leftJoin
  obtain ⟨_, rightFinal⟩ := recover right rightJoin
  exact ⟨⟨common, avoids⟩, ⟨common, avoids⟩, leftFinal, rightFinal, rfl⟩

/-- **Different degrees of the hosting preorder.**  For a confluent theory
whose rules are headed by constants and whose steps do not introduce the
choice symbol: its extension by choice hosts it, and it does not host the
extension. -/
theorem choice_strictly_above (headed : theory.Headed)
    (closed : theory.PreservesAvoiding chooseName) (confluent : Confluent (Step theory)) :
    (∃ map : ContextMap (rewritingTheoryAvoiding chooseName theory)
        (rewritingTheory (withChoice theory)), map.Hosting) ∧
      ¬ ∃ map : ContextMap (rewritingTheory (withChoice theory))
        (rewritingTheoryAvoiding chooseName theory), map.Hosting :=
  ⟨⟨includeAvoiding theory, includeAvoiding_hosting closed⟩, fun ⟨map, hosting⟩ =>
    withChoice_not_hosted_by_confluent headed
      (rewritingTheoryAvoiding_confluentUpTo closed confluent) map hosting⟩

/-! ## A mutable space -/

/-- Programs over a space that holds at most one rule. -/
inductive SpaceProgram where
  /-- A call that the rule answers. -/
  | call
  /-- The answer. -/
  | done
  /-- Add the rule, then continue. -/
  | add : SpaceProgram → SpaceProgram
  /-- Retract the rule, then continue. -/
  | retract : SpaceProgram → SpaceProgram
  deriving DecidableEq, Repr

/-- A configuration: whether the rule is in the space, and the program. -/
structure SpaceConfig where
  present : Bool
  program : SpaceProgram
  deriving DecidableEq, Repr

/-- One step of evaluation against the space. -/
inductive SpaceStep : SpaceConfig → SpaceConfig → Prop where
  | add (present : Bool) (rest : SpaceProgram) : SpaceStep ⟨present, .add rest⟩ ⟨true, rest⟩
  | retract (present : Bool) (rest : SpaceProgram) :
      SpaceStep ⟨present, .retract rest⟩ ⟨false, rest⟩
  | call : SpaceStep ⟨true, .call⟩ ⟨true, .done⟩

/-- A context: a hole, a configuration, or an instruction in front of a
context. -/
inductive SpaceContext (slots : Type) : Type where
  | hole : slots → SpaceContext slots
  | constant : SpaceConfig → SpaceContext slots
  | add : SpaceContext slots → SpaceContext slots
  | retract : SpaceContext slots → SpaceContext slots

namespace SpaceContext

variable {slots inner : Type}

/-- Fill the holes: an instruction is put in front of the program and the
space is kept. -/
def fill (filling : slots → SpaceConfig) : SpaceContext slots → SpaceConfig
  | .hole slot => filling slot
  | .constant config => config
  | .add rest => ⟨(fill filling rest).present, .add (fill filling rest).program⟩
  | .retract rest => ⟨(fill filling rest).present, .retract (fill filling rest).program⟩

/-- Plug contexts into the holes. -/
def bind (plugged : slots → SpaceContext inner) : SpaceContext slots → SpaceContext inner
  | .hole slot => plugged slot
  | .constant config => .constant config
  | .add rest => .add (bind plugged rest)
  | .retract rest => .retract (bind plugged rest)

theorem fill_bind (filling : inner → SpaceConfig) (plugged : slots → SpaceContext inner)
    (context : SpaceContext slots) :
    fill filling (bind plugged context) = fill (fun slot => fill filling (plugged slot)) context := by
  induction context with
  | hole slot => rfl
  | constant config => rfl
  | add rest ih => simp [bind, fill, ih]
  | retract rest ih => simp [bind, fill, ih]

end SpaceContext

/-- The configurations as a syntax with holes. -/
def spaceShape : HoleSyntax SpaceConfig where
  Hole := SpaceContext
  fill := SpaceContext.fill
  bind := SpaceContext.bind
  hole := SpaceContext.hole
  constant := SpaceContext.constant
  fill_bind := SpaceContext.fill_bind
  fill_hole := fun _ _ => rfl
  fill_constant := fun _ _ => rfl

/-- **Evaluation against a mutable space**, as a theory. -/
def spaceTheory : ContextTheory.{0} :=
  spaceShape.theory ⟨Eq, ⟨fun _ => rfl, fun same => same.symm, fun first second => first.trans second⟩⟩
    SpaceStep
    (fun context _ _ same => congrArg (fun filling => SpaceContext.fill filling context) (funext same))
    (fun same step => ⟨_, same ▸ step, rfl⟩)
    (fun step same => same ▸ step)

/-- The context that retracts the rule before running its hole. -/
def retracting : spaceTheory.Label () () := SpaceContext.retract (.hole ())

theorem space_call_steps : spaceTheory.rewrites (interface := ()) ⟨true, .call⟩ ⟨true, .done⟩ :=
  SpaceStep.call

/-- Everything that the retracted call reaches: itself, and the call with the
rule gone. -/
theorem space_retracted_reaches {final : SpaceConfig}
    (reaches : Relation.ReflTransGen SpaceStep ⟨true, .retract .call⟩ final) :
    final = ⟨true, .retract .call⟩ ∨ final = ⟨false, .call⟩ := by
  induction reaches with
  | refl => exact Or.inl rfl
  | tail _ step ih =>
      rcases ih with rfl | rfl
      · cases step
        exact Or.inr rfl
      · cases step

/-- **A context disables a step of its hole**: the call steps, and after the
retracting context it never reaches the retracted answer. -/
theorem space_call_disabled (final : SpaceConfig)
    (reaches : spaceTheory.Reaches (interface := ())
      (spaceTheory.apply retracting ⟨true, .call⟩) final) :
    ¬ (spaceTheory.equations ()).r final (spaceTheory.apply retracting ⟨true, .done⟩) := by
  intro same
  have shape : final = ⟨true, .retract .done⟩ := same
  rcases space_retracted_reaches reaches with other | other
  · rw [other] at shape
    cases shape
  · rw [other] at shape
    cases shape

/-- The reduction of the space is not closed under contexts. -/
theorem spaceTheory_not_contextClosed : ¬ spaceTheory.ContextClosed := by
  intro closed
  obtain ⟨whole, reaches, related⟩ := closed retracting space_call_steps
  exact space_call_disabled whole reaches related

/-- **No theory whose reduction is closed under contexts hosts the space.** -/
theorem space_not_hosted_by_contextClosed {target : ContextTheory.{0}}
    (closed : target.ContextClosed) (map : ContextMap spaceTheory target) : ¬ map.Hosting :=
  map.not_hosting_of_disabled retracting space_call_steps space_call_disabled closed

/-- In particular no theory of the λΠ-calculus modulo, read as a calculus
that runs, hosts it: with no hypothesis on the theory. -/
theorem space_not_hosted_by_rewriting (host : Theory)
    (map : ContextMap spaceTheory (rewritingTheory host)) : ¬ map.Hosting :=
  space_not_hosted_by_contextClosed (rewritingTheory_contextClosed host) map

/-! ## Cyclic values -/

/-- **No reading of hypersets as terms that sends membership to nonempty
reduction lands `Ω` on a term from which every reduction is finite.** -/
theorem no_terminating_reading_of_membership (theory : Theory) (read : HSet.{0} → Term)
    (carries : ∀ whole part : HSet.{0}, part ∈ whole →
      Relation.TransGen (Step theory) (read whole) (read part)) :
    ¬ Acc (fun next term => Step theory term next) (read HSet.quineAtom) := by
  intro terminates
  have cycle := carries HSet.quineAtom HSet.quineAtom HSet.quineAtom_mem_self
  exact not_rel_self_of_acc (acc_transGen terminates) (Relation.transGen_swap.mpr cycle)

/-- The same for a typed reading into a theory that terminates on typed
terms: where termination is used. -/
theorem no_typed_reading_of_membership {profile : Profile} (theory : Theory)
    (terminates : ∀ (context : Ctx) (term type : Term), HasType profile theory context term type →
      Acc (fun next term => Step theory term next) term)
    (read : HSet.{0} → Term)
    (carries : ∀ whole part : HSet.{0}, part ∈ whole →
      Relation.TransGen (Step theory) (read whole) (read part)) (context : Ctx) (type : Term) :
    ¬ HasType profile theory context (read HSet.quineAtom) type :=
  fun typed => no_terminating_reading_of_membership theory read carries
    (terminates context _ type typed)

/-! ## Evidence of computation -/

/-- **Conversion leaves no trace in the term**: one term has two types that
differ by a declared rule. -/
theorem silent_conversion :
    ∃ (context : Ctx) (term first second : Term), first ≠ second ∧
      LambdaPiModulo Example.withRule context term first ∧
      LambdaPiModulo Example.withRule context term second :=
  ⟨[.con "Q", .con "P"], .var 1, .con "P", .pi (.con "Q") (.con "Q"), by decide, .var rfl,
    .conv (.var rfl) Example.conv_P (Example.type_arrow _)⟩

#print axioms withChoice_conv_all
#print axioms withChoice_typing_collapse
#print axioms withChoice_not_confluent
#print axioms withChoice_not_hosted_by_confluent
#print axioms withChoice_not_hosted_by_conversion
#print axioms includeAvoiding_hosting
#print axioms choice_strictly_above
#print axioms space_call_disabled
#print axioms space_not_hosted_by_rewriting
#print axioms no_terminating_reading_of_membership
#print axioms silent_conversion

end Mettapedia.GSLT.Dedukti
