import Mettapedia.GSLT.Dedukti.Interpretation

/-!
# Pure type systems in a sort-annotated presentation

The source of the Cousineau–Dowek embedding is a pure type system.  Its
translation reads, at each product `Π x : A. B`, the sorts of `A`, of `B` and
of the product, and at each abstraction the sort of its domain ("where `s1`
is the type of `A`", Definition 7 of their paper).  Those sorts are data of
the typing derivation, not of the raw term.

This module presents a pure type system so that the data is in the syntax.

* `PTerm`: terms whose products carry their rule `(s1, s2, s3)` and whose
  abstractions carry the sort of their domain.  Erasing the annotations gives
  an existing raw λΠ term (`PTerm.erase`).
* `Derives profile`: the typing rules, with two forms of judgment.
  `type A s` says that `A` is a type of sort `s`; `term t A s` says that `t`
  has type `A`, a type of sort `s`.  A context entry records the sort of its
  type.  The application rule carries the formation of the product it
  eliminates, and the two forms are exchanged where the sort itself has a
  sort (`ofTerm`, `toTerm`).

The specification of the system is an existing `LFProfile.Profile`: the two
sorts, the axioms and the product rules.  It covers the simply typed lambda
calculus, λΠ, and the calculus of constructions.

What is proved here about the presentation: every derivation erases to a
derivation of the pure type system on raw terms (`Derives.erase`), that is, of
`HasType profile Theory.empty`.

What is not proved: the converse.  That every derivation on raw terms is the
erasure of a sorted one needs correctness of types and, for the annotations to
be determined by the raw term, uniqueness of types; the latter holds for
functional systems.  Those are the hypotheses under which the published
translation is a function of the raw term.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dedukti

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFTyping (Ctx ctxLookup ctxLookupAux)
open Mettapedia.GSLT.LanguageDef.LFProfile (Profile ProductRule)

/-- The existing lookup of a variable is the entry at its index, lifted over
the entries in front of it. -/
theorem ctxLookupAux_eq_getElem? :
    ∀ (context : Ctx) (depth index : Nat),
      ctxLookupAux depth context index =
        (context[index]?).map (LFTyping.lift (depth + index + 1) 0) := by
  intro context
  induction context with
  | nil => intro depth index; simp [ctxLookupAux]
  | cons head tail ih =>
      intro depth index
      cases index with
      | zero => simp [ctxLookupAux]
      | succ index =>
          have shifted : depth + 1 + index + 1 = depth + (index + 1) + 1 := by omega
          simp [ctxLookupAux, ih, shifted]

theorem ctxLookup_eq_getElem? (context : Ctx) (index : Nat) :
    ctxLookup context index = (context[index]?).map (LFTyping.lift (index + 1) 0) := by
  have general := ctxLookupAux_eq_getElem? context 0 index
  simpa [ctxLookup] using general

/-- Terms of a pure type system, with the sorts that its typing assigns
written at the binders. -/
inductive PTerm where
  | var : Nat → PTerm
  | sort : Srt → PTerm
  | pi : ProductRule → PTerm → PTerm → PTerm
  | lam : Srt → PTerm → PTerm → PTerm
  | app : PTerm → PTerm → PTerm
  deriving DecidableEq, Repr

namespace PTerm

/-- Lift the free variables at or above a cutoff. -/
def lift (amount cutoff : Nat) : PTerm → PTerm
  | .var index => .var (if index < cutoff then index else index + amount)
  | .sort level => .sort level
  | .pi rule domain body => .pi rule (lift amount cutoff domain) (lift amount (cutoff + 1) body)
  | .lam level domain body => .lam level (lift amount cutoff domain) (lift amount (cutoff + 1) body)
  | .app function argument => .app (lift amount cutoff function) (lift amount cutoff argument)

/-- Substitute for one variable. -/
def subst (target : Nat) (replacement : PTerm) : PTerm → PTerm
  | .var index =>
      if index = target then replacement
      else if target < index then .var (index - 1)
      else .var index
  | .sort level => .sort level
  | .pi rule domain body =>
      .pi rule (subst target replacement domain) (subst (target + 1) (lift 1 0 replacement) body)
  | .lam level domain body =>
      .lam level (subst target replacement domain) (subst (target + 1) (lift 1 0 replacement) body)
  | .app function argument =>
      .app (subst target replacement function) (subst target replacement argument)

/-- Substitute for the innermost variable. -/
def subst0 (argument body : PTerm) : PTerm := subst 0 argument body

/-- Erase the annotations. -/
def erase : PTerm → Term
  | .var index => .var index
  | .sort level => .srt level
  | .pi _ domain body => .pi (erase domain) (erase body)
  | .lam _ domain body => .lam (erase domain) (erase body)
  | .app function argument => .app (erase function) (erase argument)

theorem erase_lift (term : PTerm) :
    ∀ amount cutoff : Nat, (lift amount cutoff term).erase = LFTyping.lift amount cutoff term.erase := by
  induction term with
  | var index => intro amount cutoff; rfl
  | sort level => intro amount cutoff; rfl
  | pi rule domain body ihDomain ihBody =>
      intro amount cutoff; simp [lift, erase, LFTyping.lift, ihDomain, ihBody]
  | lam level domain body ihDomain ihBody =>
      intro amount cutoff; simp [lift, erase, LFTyping.lift, ihDomain, ihBody]
  | app function argument ihFunction ihArgument =>
      intro amount cutoff; simp [lift, erase, LFTyping.lift, ihFunction, ihArgument]

theorem erase_subst (term : PTerm) :
    ∀ (target : Nat) (replacement : PTerm),
      (subst target replacement term).erase = LFTyping.subst target replacement.erase term.erase := by
  induction term with
  | var index =>
      intro target replacement
      simp only [subst, erase, LFTyping.subst]
      split
      · rfl
      · split <;> rfl
  | sort level => intro target replacement; rfl
  | pi rule domain body ihDomain ihBody =>
      intro target replacement
      simp [subst, erase, LFTyping.subst, ihDomain, ihBody, erase_lift]
  | lam level domain body ihDomain ihBody =>
      intro target replacement
      simp [subst, erase, LFTyping.subst, ihDomain, ihBody, erase_lift]
  | app function argument ihFunction ihArgument =>
      intro target replacement
      simp [subst, erase, LFTyping.subst, ihFunction, ihArgument]

theorem erase_subst0 (argument body : PTerm) :
    (subst0 argument body).erase = LFTyping.subst0 argument.erase body.erase :=
  erase_subst body 0 argument

/-- One beta step, anywhere in a term. -/
inductive Step : PTerm → PTerm → Prop where
  | beta (level : Srt) (domain body argument : PTerm) :
      Step (.app (.lam level domain body) argument) (subst0 argument body)
  | piDomain {rule : ProductRule} {domain domain' body : PTerm} :
      Step domain domain' → Step (.pi rule domain body) (.pi rule domain' body)
  | piBody {rule : ProductRule} {domain body body' : PTerm} :
      Step body body' → Step (.pi rule domain body) (.pi rule domain body')
  | lamDomain {level : Srt} {domain domain' body : PTerm} :
      Step domain domain' → Step (.lam level domain body) (.lam level domain' body)
  | lamBody {level : Srt} {domain body body' : PTerm} :
      Step body body' → Step (.lam level domain body) (.lam level domain body')
  | appFunction {function function' argument : PTerm} :
      Step function function' → Step (.app function argument) (.app function' argument)
  | appArgument {function argument argument' : PTerm} :
      Step argument argument' → Step (.app function argument) (.app function argument')

/-- Beta conversion of annotated terms. -/
abbrev Conv : PTerm → PTerm → Prop := Relation.EqvGen Step

/-- Erasure sends a step to a step of the raw calculus. -/
theorem erase_step {source target : PTerm} (step : Step source target) :
    Dedukti.Step Theory.empty source.erase target.erase := by
  induction step with
  | beta level domain body argument =>
      rw [erase_subst0]
      exact Step.root (.beta _ _ _)
  | piDomain _ ih => exact ih.plug (.piDomain .hole _)
  | piBody _ ih => exact ih.plug (.piBody _ .hole)
  | lamDomain _ ih => exact ih.plug (.lamDomain .hole _)
  | lamBody _ ih => exact ih.plug (.lamBody _ .hole)
  | appFunction _ ih => exact ih.plug (.appFunction .hole _)
  | appArgument _ ih => exact ih.plug (.appArgument _ .hole)

/-- Erasure sends conversion to conversion of the raw calculus. -/
theorem erase_conv {source target : PTerm} (convertible : Conv source target) :
    Dedukti.Conv Theory.empty source.erase target.erase := by
  induction convertible with
  | rel _ _ step => exact .rel _ _ (erase_step step)
  | refl _ => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ihFirst ihSecond => exact .trans _ _ _ ihFirst ihSecond

/-- An operation that carries steps to steps carries conversion to
conversion. -/
theorem Conv.map {operation : PTerm → PTerm}
    (steps : ∀ {source target : PTerm}, Step source target → Step (operation source) (operation target))
    {source target : PTerm} (convertible : Conv source target) :
    Conv (operation source) (operation target) := by
  induction convertible with
  | rel _ _ step => exact .rel _ _ (steps step)
  | refl _ => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ihFirst ihSecond => exact .trans _ _ _ ihFirst ihSecond

theorem Conv.pi {rule : ProductRule} {domain domain' body body' : PTerm}
    (domains : Conv domain domain') (bodies : Conv body body') :
    Conv (.pi rule domain body) (.pi rule domain' body') :=
  .trans _ _ _ (Conv.map (operation := fun term => .pi rule term body) .piDomain domains)
    (Conv.map (operation := fun term => .pi rule domain' term) .piBody bodies)

theorem Conv.lam {level : Srt} {domain domain' body body' : PTerm}
    (domains : Conv domain domain') (bodies : Conv body body') :
    Conv (.lam level domain body) (.lam level domain' body') :=
  .trans _ _ _ (Conv.map (operation := fun term => .lam level term body) .lamDomain domains)
    (Conv.map (operation := fun term => .lam level domain' term) .lamBody bodies)

theorem Conv.app {function function' argument argument' : PTerm}
    (functions : Conv function function') (arguments : Conv argument argument') :
    Conv (.app function argument) (.app function' argument') :=
  .trans _ _ _ (Conv.map (operation := fun term => .app term argument) .appFunction functions)
    (Conv.map (operation := fun term => .app function' term) .appArgument arguments)

end PTerm

/-! ## The typing rules -/

/-- The two forms of judgment. -/
inductive Judgment where
  /-- `A` is a type of sort `s`. -/
  | type (subject : PTerm) (sort : Srt)
  /-- `t` has type `A`, a type of sort `s`. -/
  | term (subject type : PTerm) (sort : Srt)

/-- A context: each entry is a type with its sort. -/
abbrev SortedCtx : Type := List (PTerm × Srt)

/-- The type and sort of a variable. -/
def lookupSorted (context : SortedCtx) (index : Nat) : Option (PTerm × Srt) :=
  (context[index]?).map fun entry => (PTerm.lift (index + 1) 0 entry.1, entry.2)

/-- **The typing rules of a pure type system**, in the sorted presentation. -/
inductive Derives (profile : Profile) : SortedCtx → Judgment → Prop where
  | sort {context : SortedCtx} {source target : Srt} :
      profile.sortAxiom source = some target →
      Derives profile context (.type (.sort source) target)
  | pi {context : SortedCtx} {domain body : PTerm} {domainSort codomainSort resultSort : Srt} :
      Derives profile context (.type domain domainSort) →
      Derives profile ((domain, domainSort) :: context) (.type body codomainSort) →
      (⟨domainSort, codomainSort, resultSort⟩ : ProductRule) ∈ profile.products →
      Derives profile context
        (.type (.pi ⟨domainSort, codomainSort, resultSort⟩ domain body) resultSort)
  | ofTerm {context : SortedCtx} {subject : PTerm} {sort above : Srt} :
      Derives profile context (.term subject (.sort sort) above) →
      profile.sortAxiom sort = some above →
      Derives profile context (.type subject sort)
  | toTerm {context : SortedCtx} {subject : PTerm} {sort above : Srt} :
      Derives profile context (.type subject sort) →
      profile.sortAxiom sort = some above →
      Derives profile context (.term subject (.sort sort) above)
  | var {context : SortedCtx} {index : Nat} {type : PTerm} {sort : Srt} :
      lookupSorted context index = some (type, sort) →
      Derives profile context (.term (.var index) type sort)
  | lam {context : SortedCtx} {domain body bodyType : PTerm}
      {domainSort codomainSort resultSort : Srt} :
      Derives profile context (.type domain domainSort) →
      Derives profile ((domain, domainSort) :: context) (.type bodyType codomainSort) →
      (⟨domainSort, codomainSort, resultSort⟩ : ProductRule) ∈ profile.products →
      Derives profile ((domain, domainSort) :: context) (.term body bodyType codomainSort) →
      Derives profile context
        (.term (.lam domainSort domain body)
          (.pi ⟨domainSort, codomainSort, resultSort⟩ domain bodyType) resultSort)
  | app {context : SortedCtx} {function argument domain bodyType : PTerm}
      {domainSort codomainSort resultSort : Srt} :
      Derives profile context (.type domain domainSort) →
      Derives profile ((domain, domainSort) :: context) (.type bodyType codomainSort) →
      (⟨domainSort, codomainSort, resultSort⟩ : ProductRule) ∈ profile.products →
      Derives profile context
        (.term function (.pi ⟨domainSort, codomainSort, resultSort⟩ domain bodyType) resultSort) →
      Derives profile context (.term argument domain domainSort) →
      Derives profile context
        (.term (.app function argument) (PTerm.subst0 argument bodyType) codomainSort)
  | conv {context : SortedCtx} {subject source target : PTerm} {sort : Srt} :
      Derives profile context (.term subject source sort) →
      PTerm.Conv source target →
      Derives profile context (.type target sort) →
      Derives profile context (.term subject target sort)

/-! ## Erasure to the raw system -/

/-- The raw context of a sorted context. -/
def eraseCtx (context : SortedCtx) : Ctx := context.map fun entry => entry.1.erase

/-- The raw term and type of a judgment. -/
def Judgment.erased : Judgment → Term × Term
  | .type subject level => (subject.erase, .srt level)
  | .term subject classifier _ => (subject.erase, classifier.erase)

theorem ctxLookup_eraseCtx {context : SortedCtx} {index : Nat} {type : PTerm} {sort : Srt}
    (found : lookupSorted context index = some (type, sort)) :
    ctxLookup (eraseCtx context) index = some type.erase := by
  rw [ctxLookup_eq_getElem?]
  unfold lookupSorted at found
  unfold eraseCtx
  rw [List.getElem?_map]
  cases entry : context[index]? with
  | none => rw [entry] at found; cases found
  | some value =>
      rw [entry] at found
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at found
      obtain ⟨rfl, _⟩ := found
      simp [PTerm.erase_lift]

/-- **A sorted derivation erases to a derivation of the pure type system on
raw terms.** -/
theorem Derives.erase {profile : Profile} {context : SortedCtx} {judgment : Judgment}
    (derivation : Derives profile context judgment) :
    HasType profile Theory.empty (eraseCtx context) judgment.erased.1 judgment.erased.2 := by
  induction derivation with
  | sort axiomHolds => exact .sort axiomHolds
  | pi _ _ rule ihDomain ihBody => exact .pi ihDomain ihBody rule
  | ofTerm _ _ ih => exact ih
  | toTerm _ _ ih => exact ih
  | var found => exact .var (ctxLookup_eraseCtx found)
  | lam _ _ rule _ ihDomain ihBodyType ihBody => exact .lam ihDomain ihBodyType rule ihBody
  | app _ _ _ _ _ _ _ ihFunction ihArgument =>
      simp only [Judgment.erased, PTerm.erase_subst0]
      exact .app ihFunction ihArgument
  | conv _ convertible _ ihTerm ihTarget =>
      exact .conv ihTerm (PTerm.erase_conv convertible) ihTarget

/-- The subject of a judgment. -/
def Judgment.subject : Judgment → PTerm
  | .type subject _ => subject
  | .term subject _ _ => subject

/-- The annotation of a product that a derivation has as its subject is a
rule of the system. -/
theorem Derives.pi_rule_mem {profile : Profile} {context : SortedCtx} {judgment : Judgment}
    (derivation : Derives profile context judgment) :
    ∀ {rule : ProductRule} {domain body : PTerm}, judgment.subject = .pi rule domain body →
      rule ∈ profile.products := by
  induction derivation with
  | sort _ => intro rule domain body same; cases same
  | pi _ _ member _ _ => intro rule domain body same; cases same; exact member
  | ofTerm _ _ ih => exact ih
  | toTerm _ _ ih => exact ih
  | var _ => intro rule domain body same; cases same
  | lam _ _ _ _ _ _ _ => intro rule domain body same; cases same
  | app _ _ _ _ _ _ _ _ _ => intro rule domain body same; cases same
  | conv _ _ _ ihTerm _ => exact ihTerm

/-! ## Three systems -/

/-- The product rule of polymorphism: a product over a kind of types is a
type. -/
def kindTypeType : ProductRule := ⟨.kind, .type, .type⟩

/-- The simply typed lambda calculus: one rule. -/
def simplyTyped : Profile where
  sortAxiom := LFProfile.typeAxiom
  products := [LFProfile.typeTypeType]

/-- The calculus of constructions: four rules. -/
def constructions : Profile where
  sortAxiom := LFProfile.typeAxiom
  products := [LFProfile.typeTypeType, LFProfile.typeKindKind, kindTypeType, LFProfile.kindKindKind]

namespace Example

/-- The polymorphic identity `λ X : Type. λ x : X. x`. -/
def polymorphicIdentity : PTerm := .lam .kind (.sort .type) (.lam .type (.var 0) (.var 0))

/-- Its type `Π X : Type. X → X`. -/
def polymorphicIdentityType : PTerm :=
  .pi kindTypeType (.sort .type) (.pi LFProfile.typeTypeType (.var 0) (.var 1))

theorem variable_is_type :
    Derives constructions [(.sort .type, .kind)] (.type (.var 0) .type) :=
  .ofTerm (.var rfl) rfl

theorem outer_variable_is_type :
    Derives constructions [(.var 0, .type), (.sort .type, .kind)] (.type (.var 1) .type) :=
  .ofTerm (.var rfl) rfl

/-- **Positive**: the polymorphic identity is typed in the calculus of
constructions. -/
theorem polymorphicIdentity_typed :
    Derives constructions [] (.term polymorphicIdentity polymorphicIdentityType .type) := by
  have inner : Derives constructions [(.sort .type, .kind)]
      (.term (.lam .type (.var 0) (.var 0)) (.pi LFProfile.typeTypeType (.var 0) (.var 1)) .type) :=
    .lam variable_is_type outer_variable_is_type (by decide) (.var rfl)
  exact .lam (.sort rfl) (.pi variable_is_type outer_variable_is_type (by decide)) (by decide) inner

/-- **Negative**: its type is not a type of the simply typed lambda calculus,
which has no product over a kind. -/
theorem polymorphicIdentityType_not_simplyTyped (context : SortedCtx) (sort : Srt) :
    ¬ Derives simplyTyped context (.type polymorphicIdentityType sort) := by
  intro derivation
  have member := derivation.pi_rule_mem (rule := kindTypeType) rfl
  revert member
  decide

end Example

#print axioms PTerm.erase_subst
#print axioms PTerm.erase_conv
#print axioms Derives.erase
#print axioms Derives.pi_rule_mem
#print axioms Example.polymorphicIdentity_typed
#print axioms Example.polymorphicIdentityType_not_simplyTyped

end Mettapedia.GSLT.Dedukti
