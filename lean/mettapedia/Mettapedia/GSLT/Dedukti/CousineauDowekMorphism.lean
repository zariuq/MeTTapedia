import Mettapedia.GSLT.Dedukti.CousineauDowek

/-!
# The Cousineau–Dowek embedding as a map of theories

The embedding is placed in the category of theories presented through their
contexts, with source a pure type system and target the λΠ-calculus modulo its
theory.  What it is depends on what the two theories are taken to be.

## The calculi as their checkers see them: conversion, no reduction

* On the sort-annotated syntax, compared by beta conversion of annotated
  terms, the translation is a map of theories for every pure type system
  (`cdMap`).  The annotated syntax is free, so a fold out of it is defined
  without condition.
* The pure type system itself compares raw terms.  `rawTheory profile` has the
  validly annotated terms as representatives and beta conversion of their
  erasures as static equivalence.  The translation is a map out of it exactly
  when it respects that equivalence (`respectsErasure_iff`):
  `RespectsErasure profile` says that two validly annotated terms with
  convertible erasures have convertible translations.  That is the condition
  under which the fold descends from the free syntax to the presented one.
* When it does, the map is **hosting** (`cdRawMap_hosting`): the translation
  reflects conversion, by the back translation.  No further hypothesis.
* The condition holds for the simply typed lambda calculus
  (`simplyTyped_respectsErasure`, `simplyTyped_hosting`): with one product
  rule the annotation is determined by the raw term.
* It fails for a system with two rules for one pair of sorts, under confluence
  of the target (`nonFunctional_not_respectsErasure`): one raw product has two
  annotations and two translations with different heads.  For functional
  systems the condition is uniqueness of types; it is not proved here.

## The calculi as they run: identity, one-step reduction

The translation is a map of theories (`cdRunMap`) that

* does not preserve single steps (`cdRunMap_not_preserves`): a step in the
  domain of a product is two steps of the target;
* does not reflect single steps (`cdRunMap_not_reflects`): the target can
  reduce one of the two copies of a domain, reaching a term that is the
  translation of nothing (`halfReduced_not_image`);
* preserves nonempty reductions (`cdRunMap_simulates`).

So soundness of the embedding is hosting at the level of conversion, and a
simulation, not hosting, at the level of single steps.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dedukti

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFTyping (lift subst subst0)
open Mettapedia.GSLT.LanguageDef.LFProfile (Profile ProductRule)
open Mettapedia.GSLT.LanguageDef.LFContextualBetaEta (Context)
open Mettapedia.Logic.Relation (Confluent IsNormal)

/-! ## Annotated terms with holes -/

/-- An annotated term with named holes. -/
inductive PContext (slots : Type) : Type where
  | hole : slots → PContext slots
  | var : Nat → PContext slots
  | sort : Srt → PContext slots
  | pi : ProductRule → PContext slots → PContext slots → PContext slots
  | lam : Srt → PContext slots → PContext slots → PContext slots
  | app : PContext slots → PContext slots → PContext slots

namespace PContext

variable {slots inner : Type}

/-- Fill the holes with terms. -/
def fill (filling : slots → PTerm) : PContext slots → PTerm
  | .hole slot => filling slot
  | .var index => .var index
  | .sort level => .sort level
  | .pi rule domain body => .pi rule (fill filling domain) (fill filling body)
  | .lam level domain body => .lam level (fill filling domain) (fill filling body)
  | .app function argument => .app (fill filling function) (fill filling argument)

/-- Plug contexts into the holes. -/
def bind (plugged : slots → PContext inner) : PContext slots → PContext inner
  | .hole slot => plugged slot
  | .var index => .var index
  | .sort level => .sort level
  | .pi rule domain body => .pi rule (bind plugged domain) (bind plugged body)
  | .lam level domain body => .lam level (bind plugged domain) (bind plugged body)
  | .app function argument => .app (bind plugged function) (bind plugged argument)

/-- A term, as a context with no hole. -/
def ofTerm : PTerm → PContext slots
  | .var index => .var index
  | .sort level => .sort level
  | .pi rule domain body => .pi rule (ofTerm domain) (ofTerm body)
  | .lam level domain body => .lam level (ofTerm domain) (ofTerm body)
  | .app function argument => .app (ofTerm function) (ofTerm argument)

theorem fill_bind (filling : inner → PTerm) (plugged : slots → PContext inner)
    (context : PContext slots) :
    fill filling (bind plugged context) = fill (fun slot => fill filling (plugged slot)) context := by
  induction context with
  | hole slot => rfl
  | var index => rfl
  | sort level => rfl
  | pi rule domain body ihDomain ihBody => simp [bind, fill, ihDomain, ihBody]
  | lam level domain body ihDomain ihBody => simp [bind, fill, ihDomain, ihBody]
  | app function argument ihFunction ihArgument => simp [bind, fill, ihFunction, ihArgument]

theorem fill_ofTerm (filling : slots → PTerm) (term : PTerm) :
    fill filling (ofTerm term : PContext slots) = term := by
  induction term with
  | var index => rfl
  | sort level => rfl
  | pi rule domain body ihDomain ihBody => simp [ofTerm, fill, ihDomain, ihBody]
  | lam level domain body ihDomain ihBody => simp [ofTerm, fill, ihDomain, ihBody]
  | app function argument ihFunction ihArgument => simp [ofTerm, fill, ihFunction, ihArgument]

/-- The translation of a context: holes stay holes. -/
def translate : PContext slots → TermContext slots
  | .hole slot => .hole slot
  | .var index => .var index
  | .sort level => .con (Symbol.code level).name
  | .pi rule domain body =>
      .app (.app (.con (Symbol.prod rule).name) (translate domain))
        (.lam (.app (.con (Symbol.decode rule.domain).name) (translate domain)) (translate body))
  | .lam level domain body =>
      .lam (.app (.con (Symbol.decode level).name) (translate domain)) (translate body)
  | .app function argument => .app (translate function) (translate argument)

theorem translate_fill (context : PContext slots) (filling : slots → PTerm) :
    Dedukti.translate (fill filling context) =
      (translate context).fill fun slot => Dedukti.translate (filling slot) := by
  induction context with
  | hole slot => rfl
  | var index => rfl
  | sort level => rfl
  | pi rule domain body ihDomain ihBody =>
      simp [fill, translate, Dedukti.translate, TermContext.fill, prodCode, El, ihDomain, ihBody]
  | lam level domain body ihDomain ihBody =>
      simp [fill, translate, Dedukti.translate, TermContext.fill, El, ihDomain, ihBody]
  | app function argument ihFunction ihArgument =>
      simp [fill, translate, Dedukti.translate, TermContext.fill, ihFunction, ihArgument]

/-- The erasure of a context. -/
def erase : PContext slots → TermContext slots
  | .hole slot => .hole slot
  | .var index => .var index
  | .sort level => .srt level
  | .pi _ domain body => .pi (erase domain) (erase body)
  | .lam _ domain body => .lam (erase domain) (erase body)
  | .app function argument => .app (erase function) (erase argument)

theorem erase_fill (context : PContext slots) (filling : slots → PTerm) :
    (fill filling context).erase = (erase context).fill fun slot => (filling slot).erase := by
  induction context with
  | hole slot => rfl
  | var index => rfl
  | sort level => rfl
  | pi rule domain body ihDomain ihBody =>
      simp [fill, erase, PTerm.erase, TermContext.fill, ihDomain, ihBody]
  | lam level domain body ihDomain ihBody =>
      simp [fill, erase, PTerm.erase, TermContext.fill, ihDomain, ihBody]
  | app function argument ihFunction ihArgument =>
      simp [fill, erase, PTerm.erase, TermContext.fill, ihFunction, ihArgument]

end PContext

/-- Beta conversion of annotated terms is a congruence for every context. -/
theorem PTerm.Conv.fill {slots : Type} (context : PContext slots) {first second : slots → PTerm}
    (convertible : ∀ slot, PTerm.Conv (first slot) (second slot)) :
    PTerm.Conv (context.fill first) (context.fill second) := by
  induction context with
  | hole slot => exact convertible slot
  | var index => exact .refl _
  | sort level => exact .refl _
  | pi rule domain body ihDomain ihBody => exact PTerm.Conv.pi ihDomain ihBody
  | lam level domain body ihDomain ihBody => exact PTerm.Conv.lam ihDomain ihBody
  | app function argument ihFunction ihArgument => exact PTerm.Conv.app ihFunction ihArgument

/-- The annotated terms as a syntax with holes. -/
def ptermShape : HoleSyntax PTerm where
  Hole := PContext
  fill := PContext.fill
  bind := PContext.bind
  hole := PContext.hole
  constant := PContext.ofTerm
  fill_bind := PContext.fill_bind
  fill_hole := fun _ _ => rfl
  fill_constant := PContext.fill_ofTerm

/-! ## The free syntax: the translation is a map without condition -/

/-- The annotated terms, compared by beta conversion of annotated terms. -/
def annotatedTheory : ContextTheory.{0} :=
  ptermShape.theory ⟨PTerm.Conv, Relation.EqvGen.is_equivalence _⟩ (fun _ _ => False)
    (fun context _ _ convertible => PTerm.Conv.fill context convertible)
    (fun _ step => step.elim)
    (fun step _ => step)

/-- **The embedding on the annotated syntax**, as a map of theories. -/
def cdMap (profile : Profile) :
    ContextMap annotatedTheory (conversionTheory (cdTheory profile)) where
  interface := fun _ => ()
  term := fun term => translate term
  context := fun context => PContext.translate context
  term_resp := fun convertible => translate_conv profile convertible
  equivariant := fun context filling => Conv.of_eq (PContext.translate_fill context filling)

/-- The map reflects conversion up to the erasure of the annotations. -/
theorem cdMap_reflects_erasure (profile : Profile) {first second : PTerm}
    (convertible : ((conversionTheory (cdTheory profile)).equations ()).r
      ((cdMap profile).term (origin := ()) first) ((cdMap profile).term (origin := ()) second)) :
    Conv Theory.empty first.erase second.erase :=
  translate_reflects profile convertible

/-! ## The presented syntax: raw terms, with valid annotations as representatives -/

/-- Every annotation is one that the system has: a product carries a rule, an
abstraction the domain sort of a rule. -/
def PTerm.Valid (profile : Profile) : PTerm → Prop
  | .var _ => True
  | .sort _ => True
  | .pi rule domain body => rule ∈ profile.products ∧ Valid profile domain ∧ Valid profile body
  | .lam level domain body =>
      (∃ rule ∈ profile.products, rule.domain = level) ∧ Valid profile domain ∧ Valid profile body
  | .app function argument => Valid profile function ∧ Valid profile argument

/-- Validity of the annotations of a context. -/
def PContext.Valid (profile : Profile) {slots : Type} : PContext slots → Prop
  | .hole _ => True
  | .var _ => True
  | .sort _ => True
  | .pi rule domain body => rule ∈ profile.products ∧ Valid profile domain ∧ Valid profile body
  | .lam level domain body =>
      (∃ rule ∈ profile.products, rule.domain = level) ∧ Valid profile domain ∧ Valid profile body
  | .app function argument => Valid profile function ∧ Valid profile argument

theorem PContext.valid_fill {profile : Profile} {slots : Type} {context : PContext slots}
    (valid : context.Valid profile) {filling : slots → PTerm}
    (fillings : ∀ slot, (filling slot).Valid profile) : (context.fill filling).Valid profile := by
  induction context with
  | hole slot => exact fillings slot
  | var index => trivial
  | sort level => trivial
  | pi rule domain body ihDomain ihBody => exact ⟨valid.1, ihDomain valid.2.1, ihBody valid.2.2⟩
  | lam level domain body ihDomain ihBody => exact ⟨valid.1, ihDomain valid.2.1, ihBody valid.2.2⟩
  | app function argument ihFunction ihArgument => exact ⟨ihFunction valid.1, ihArgument valid.2⟩

theorem PContext.valid_bind {profile : Profile} {slots inner : Type} {context : PContext slots}
    (valid : context.Valid profile) {plugged : slots → PContext inner}
    (pluggings : ∀ slot, (plugged slot).Valid profile) : (context.bind plugged).Valid profile := by
  induction context with
  | hole slot => exact pluggings slot
  | var index => trivial
  | sort level => trivial
  | pi rule domain body ihDomain ihBody => exact ⟨valid.1, ihDomain valid.2.1, ihBody valid.2.2⟩
  | lam level domain body ihDomain ihBody => exact ⟨valid.1, ihDomain valid.2.1, ihBody valid.2.2⟩
  | app function argument ihFunction ihArgument => exact ⟨ihFunction valid.1, ihArgument valid.2⟩

theorem PContext.valid_ofTerm {profile : Profile} {slots : Type} {term : PTerm}
    (valid : term.Valid profile) : (PContext.ofTerm term : PContext slots).Valid profile := by
  induction term with
  | var index => trivial
  | sort level => trivial
  | pi rule domain body ihDomain ihBody => exact ⟨valid.1, ihDomain valid.2.1, ihBody valid.2.2⟩
  | lam level domain body ihDomain ihBody => exact ⟨valid.1, ihDomain valid.2.1, ihBody valid.2.2⟩
  | app function argument ihFunction ihArgument => exact ⟨ihFunction valid.1, ihArgument valid.2⟩

/-- The validly annotated terms of a system. -/
abbrev ValidTerm (profile : Profile) : Type := {term : PTerm // term.Valid profile}

/-- The validly annotated terms as a syntax with holes. -/
def validShape (profile : Profile) : HoleSyntax (ValidTerm profile) where
  Hole := fun slots => {context : PContext slots // context.Valid profile}
  fill := fun filling context =>
    ⟨context.1.fill fun slot => (filling slot).1,
      PContext.valid_fill context.2 fun slot => (filling slot).2⟩
  bind := fun plugged context =>
    ⟨context.1.bind fun slot => (plugged slot).1,
      PContext.valid_bind context.2 fun slot => (plugged slot).2⟩
  hole := fun slot => ⟨.hole slot, trivial⟩
  constant := fun term => ⟨PContext.ofTerm term.1, PContext.valid_ofTerm term.2⟩
  fill_bind := fun _ _ context => Subtype.ext (PContext.fill_bind _ _ context.1)
  fill_hole := fun _ _ => rfl
  fill_constant := fun _ term => Subtype.ext (PContext.fill_ofTerm _ term.1)

/-- Two annotated terms whose erasures are beta convertible. -/
def ErasedConv (first second : PTerm) : Prop := Conv Theory.empty first.erase second.erase

/-- **The pure type system on raw terms**, at conversion: the validly
annotated terms, compared by beta conversion of their erasures. -/
def rawTheory (profile : Profile) : ContextTheory.{0} :=
  (validShape profile).theory
    ⟨fun first second => ErasedConv first.1 second.1,
      ⟨fun _ => .refl _, fun related => .symm _ _ related,
        fun first second => .trans _ _ _ first second⟩⟩
    (fun _ _ => False)
    (fun context first second related => by
      change Conv Theory.empty (context.1.fill fun slot => (first slot).1).erase
        (context.1.fill fun slot => (second slot).1).erase
      rw [PContext.erase_fill, PContext.erase_fill]
      exact Conv.fill _ related)
    (fun _ step => step.elim)
    (fun step _ => step)

/-- **The condition for the fold to descend**: validly annotated terms with
convertible erasures have convertible translations. -/
def RespectsErasure (profile : Profile) : Prop :=
  ∀ first second : ValidTerm profile, ErasedConv first.1 second.1 →
    Conv (cdTheory profile) (translate first.1) (translate second.1)

variable {profile : Profile}

/-- **The embedding out of the pure type system on raw terms**, under the
condition. -/
def cdRawMap (respects : RespectsErasure profile) :
    ContextMap (rawTheory profile) (conversionTheory (cdTheory profile)) where
  interface := fun _ => ()
  term := fun term => translate term.1
  context := fun context => PContext.translate context.1
  term_resp := fun {_ first second} related => respects first second related
  equivariant := fun context filling =>
    Conv.of_eq (PContext.translate_fill context.1 fun slot => (filling slot).1)

/-- **Soundness is hosting**: the embedding out of the pure type system on raw
terms identifies no two terms that were apart. -/
theorem cdRawMap_hosting (respects : RespectsErasure profile) : (cdRawMap respects).Hosting := by
  rw [ContextMap.hosting_iff]
  refine ⟨?_, ?_, ?_⟩
  · intro _ first second convertible
    exact translate_reflects profile convertible
  · intro _ _ _ _ _ step
    exact step.elim
  · intro _ _ _ _ _ step
    exact step.elim

/-- **The translation is a map out of the presented syntax exactly when it
respects the presenting equivalence.** -/
theorem respectsErasure_iff :
    RespectsErasure profile ↔
      ∃ map : ContextMap (rawTheory profile) (conversionTheory (cdTheory profile)),
        ∀ term : ValidTerm profile, map.term (origin := ()) term = translate term.1 := by
  constructor
  · intro respects
    exact ⟨cdRawMap respects, fun _ => rfl⟩
  · rintro ⟨map, agrees⟩ first second related
    have image := map.term_resp (origin := ()) (first := first) (second := second) related
    rw [agrees, agrees] at image
    exact image

/-! ## Positive: the simply typed lambda calculus -/

/-- The annotation of a raw term of a system with the one rule
`(Type, Type, Type)`. -/
def annotate : Term → PTerm
  | .var index => .var index
  | .srt level => .sort level
  | .con _ => .sort .type
  | .pi domain body => .pi LFProfile.typeTypeType (annotate domain) (annotate body)
  | .lam domain body => .lam .type (annotate domain) (annotate body)
  | .app function argument => .app (annotate function) (annotate argument)

theorem annotate_lift (term : Term) :
    ∀ amount cutoff : Nat, annotate (lift amount cutoff term) = PTerm.lift amount cutoff (annotate term) := by
  induction term with
  | var index => intro amount cutoff; rfl
  | srt level => intro amount cutoff; rfl
  | con name => intro amount cutoff; rfl
  | pi domain body ihDomain ihBody =>
      intro amount cutoff; simp [lift, annotate, PTerm.lift, ihDomain, ihBody]
  | lam domain body ihDomain ihBody =>
      intro amount cutoff; simp [lift, annotate, PTerm.lift, ihDomain, ihBody]
  | app function argument ihFunction ihArgument =>
      intro amount cutoff; simp [lift, annotate, PTerm.lift, ihFunction, ihArgument]

theorem annotate_subst (term : Term) :
    ∀ (target : Nat) (replacement : Term), annotate (subst target replacement term) =
      PTerm.subst target (annotate replacement) (annotate term) := by
  induction term with
  | var index =>
      intro target replacement
      by_cases same : index = target
      · simp [subst, annotate, PTerm.subst, same]
      · by_cases above : target < index
        · simp [subst, annotate, PTerm.subst, same, above]
        · simp [subst, annotate, PTerm.subst, same, above]
  | srt level => intro target replacement; rfl
  | con name => intro target replacement; rfl
  | pi domain body ihDomain ihBody =>
      intro target replacement
      simp [subst, annotate, PTerm.subst, ihDomain, ihBody, annotate_lift]
  | lam domain body ihDomain ihBody =>
      intro target replacement
      simp [subst, annotate, PTerm.subst, ihDomain, ihBody, annotate_lift]
  | app function argument ihFunction ihArgument =>
      intro target replacement
      simp [subst, annotate, PTerm.subst, ihFunction, ihArgument]

theorem annotate_step {source target : Term} (step : Step Theory.empty source target) :
    PTerm.Step (annotate source) (annotate target) := by
  cases step with
  | @inContext context redex contractum root =>
      have atRoot : PTerm.Step (annotate redex) (annotate contractum) := by
        cases root with
        | beta domain body argument =>
            have same : annotate (subst0 argument body) =
                PTerm.subst0 (annotate argument) (annotate body) := annotate_subst body 0 argument
            rw [same]
            exact .beta _ _ _ _
        | delta defined => cases defined
        | rule assignment member => exact member.elim
      induction context with
      | hole => exact atRoot
      | piDomain rest body ih => exact .piDomain ih
      | piBody domain rest ih => exact .piBody ih
      | lamDomain rest body ih => exact .lamDomain ih
      | lamBody domain rest ih => exact .lamBody ih
      | appFunction rest argument ih => exact .appFunction ih
      | appArgument function rest ih => exact .appArgument ih

theorem annotate_conv {source target : Term} (convertible : Conv Theory.empty source target) :
    PTerm.Conv (annotate source) (annotate target) := by
  induction convertible with
  | rel _ _ step => exact .rel _ _ (annotate_step step)
  | refl _ => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ihFirst ihSecond => exact .trans _ _ _ ihFirst ihSecond

/-- With one rule the annotation is determined by the raw term. -/
theorem annotate_erase {term : PTerm} (valid : term.Valid simplyTyped) :
    annotate term.erase = term := by
  induction term with
  | var index => rfl
  | sort level => rfl
  | pi rule domain body ihDomain ihBody =>
      have same : rule = LFProfile.typeTypeType := List.mem_singleton.mp valid.1
      simp [PTerm.erase, annotate, same, ihDomain valid.2.1, ihBody valid.2.2]
  | lam level domain body ihDomain ihBody =>
      obtain ⟨rule, member, domainSort⟩ := valid.1
      have same : rule = LFProfile.typeTypeType := List.mem_singleton.mp member
      have isType : level = .type := by rw [← domainSort, same]; rfl
      simp [PTerm.erase, annotate, isType, ihDomain valid.2.1, ihBody valid.2.2]
  | app function argument ihFunction ihArgument =>
      simp [PTerm.erase, annotate, ihFunction valid.1, ihArgument valid.2]

/-- **For the simply typed lambda calculus the fold descends to raw terms.** -/
theorem simplyTyped_respectsErasure : RespectsErasure simplyTyped := by
  intro first second related
  have annotated := annotate_conv related
  rw [annotate_erase first.2, annotate_erase second.2] at annotated
  exact translate_conv simplyTyped annotated

/-- **The embedding of the simply typed lambda calculus is hosting**, with no
hypothesis. -/
theorem simplyTyped_hosting : (cdRawMap simplyTyped_respectsErasure).Hosting :=
  cdRawMap_hosting simplyTyped_respectsErasure

/-! ## Negative: two rules for one pair of sorts -/

/-- A product of two types that is a kind. -/
def typeTypeKind : ProductRule := ⟨.type, .type, .kind⟩

/-- A system that is not functional: a product of two types is a type and is
a kind. -/
def nonFunctional : Profile where
  sortAxiom := LFProfile.typeAxiom
  products := [LFProfile.typeTypeType, typeTypeKind]

/-- The raw product `Π x : Type. Type`, with a chosen annotation. -/
def smallProduct (rule : ProductRule) : PTerm := .pi rule (.sort .type) (.sort .type)

/-- No rule of the embedding rewrites a product code, and it has no
definition. -/
theorem cdTheory_not_defines_prod (profile : Profile) (rule : ProductRule) :
    ¬ (cdTheory profile).Defines (Symbol.prod rule).name := by
  rintro (defined | ⟨declared, member, head⟩)
  · exact defined rfl
  · cases member with
    | @code source target _ =>
        have same : (Symbol.decode target).name = (Symbol.prod rule).name := Option.some.inj head
        exact absurd (Symbol.name_injective same) (by simp)
    | @prod other _ =>
        have same : (Symbol.decode other.result).name = (Symbol.prod rule).name :=
          Option.some.inj head
        exact absurd (Symbol.name_injective same) (by simp)

/-- The two annotations of one raw product have translations with no common
reduct. -/
theorem smallProduct_not_joinable (profile : Profile) :
    ¬ Joinable (cdTheory profile) (translate (smallProduct LFProfile.typeTypeType))
      (translate (smallProduct typeTypeKind)) :=
  not_joinable_of_heads (cdTheory_headed profile)
    (cdTheory_not_defines_prod profile LFProfile.typeTypeType)
    (cdTheory_not_defines_prod profile typeTypeKind) (by decide) rfl rfl

/-- **Where confluence is used**: for a system that is not functional the
fold does not descend to raw terms. -/
theorem nonFunctional_not_respectsErasure
    (confluent : Confluent (Step (cdTheory nonFunctional))) : ¬ RespectsErasure nonFunctional := by
  intro respects
  have convertible := respects
    ⟨smallProduct LFProfile.typeTypeType, ⟨by decide, trivial, trivial⟩⟩
    ⟨smallProduct typeTypeKind, ⟨by decide, trivial, trivial⟩⟩ (.refl _)
  exact smallProduct_not_joinable nonFunctional ((conv_iff_joinable confluent).mp convertible)

/-! ## The calculi as they run -/

/-- The annotated terms, compared by identity and reduced by beta. -/
def annotatedRunTheory : ContextTheory.{0} :=
  ptermShape.theory ⟨Eq, ⟨fun _ => rfl, fun same => same.symm, fun first second => first.trans second⟩⟩
    PTerm.Step
    (fun context _ _ same => congrArg (fun filling => PContext.fill filling context) (funext same))
    (fun same step => ⟨_, same ▸ step, rfl⟩)
    (fun step same => same ▸ step)

/-- **The embedding between the calculi as they run.** -/
def cdRunMap (profile : Profile) :
    ContextMap annotatedRunTheory (rewritingTheory (cdTheory profile)) where
  interface := fun _ => ()
  term := fun term => translate term
  context := fun context => PContext.translate context
  term_resp := fun same => congrArg translate same
  equivariant := fun context filling => PContext.translate_fill context filling

/-- The redex `(λ x : Type. x) Type`. -/
def redexDomain : PTerm := .app (.lam .kind (.sort .type) (.var 0)) (.sort .type)

/-- A product whose domain is a redex. -/
def stepSource (rule : ProductRule) : PTerm := .pi rule redexDomain (.sort .type)

/-- The same product with its domain reduced. -/
def stepTarget (rule : ProductRule) : PTerm := .pi rule (.sort .type) (.sort .type)

theorem stepSource_step (rule : ProductRule) : PTerm.Step (stepSource rule) (stepTarget rule) :=
  .piDomain (.beta .kind (.sort .type) (.var 0) (.sort .type))

/-- **The translation of one step is not one step.** -/
theorem translate_not_step (profile : Profile) (rule : ProductRule) :
    ¬ Step (cdTheory profile) (translate (stepSource rule)) (translate (stepTarget rule)) := by
  intro step
  rcases step.app_inv with root | ⟨function', inner, same⟩ | ⟨argument', inner, same⟩
  · exact RootStep.not_of_rigid (cdTheory_headed profile) (cdTheory_not_defines_prod profile rule)
      rfl root
  · simp [translate, stepTarget, redexDomain, prodCode, El, sortCode] at same
  · simp [translate, stepTarget, redexDomain, prodCode, El, sortCode] at same

/-- The translation of the product with a redex domain, after the target has
reduced one of the two copies of that domain. -/
def halfReduced (rule : ProductRule) : Term :=
  prodCode rule (sortCode .type) (.lam (El rule.domain (translate redexDomain)) (sortCode .type))

theorem step_halfReduced (profile : Profile) (rule : ProductRule) :
    Step (cdTheory profile) (translate (stepSource rule)) (halfReduced rule) :=
  Step.inContext
    (.appFunction (.appArgument (.con (Symbol.prod rule).name) .hole)
      (.lam (El rule.domain (translate redexDomain)) (sortCode .type)))
    (.beta (El .kind (sortCode .type)) (.var 0) (sortCode .type))

/-- **The half-reduced term is the translation of no term.** -/
theorem halfReduced_not_image (rule : ProductRule) (term : PTerm) :
    translate term ≠ halfReduced rule := by
  intro same
  cases term with
  | var index => simp [translate, halfReduced, prodCode] at same
  | sort level => simp [translate, halfReduced, prodCode, sortCode] at same
  | lam level domain body => simp [translate, halfReduced, prodCode] at same
  | pi other domain body =>
      simp only [translate, halfReduced, prodCode, El, Term.app.injEq, Term.lam.injEq] at same
      obtain ⟨⟨_, first⟩, ⟨_, second⟩, _⟩ := same
      rw [first] at second
      simp [sortCode, translate, redexDomain] at second
  | app function argument =>
      cases function with
      | app inner middle =>
          simp only [translate, halfReduced, prodCode, Term.app.injEq] at same
          obtain ⟨⟨head, _⟩, _⟩ := same
          cases inner with
          | sort level => exact absurd (Symbol.name_injective (Term.con.inj head)) (by simp)
          | var index => simp [translate] at head
          | pi other domain body => simp [translate, prodCode] at head
          | lam level domain body => simp [translate] at head
          | app deeper deepest => simp [translate] at head
      | var index => simp [translate, halfReduced, prodCode] at same
      | sort level => simp [translate, halfReduced, prodCode, sortCode] at same
      | pi other domain body => simp [translate, halfReduced, prodCode] at same
      | lam level domain body => simp [translate, halfReduced, prodCode] at same

/-- **The embedding does not preserve single steps.** -/
theorem cdRunMap_not_preserves (profile : Profile) : ¬ (cdRunMap profile).PreservesTransitions := by
  intro preserves
  have steps : (cdRunMap profile).PreservesRewrites :=
    (cdRunMap profile).preservesRewrites_of_transitions preserves
  exact translate_not_step profile LFProfile.typeTypeType
    (steps (interface := ()) (stepSource_step LFProfile.typeTypeType))

/-- **The embedding does not reflect single steps.** -/
theorem cdRunMap_not_reflects (profile : Profile) : ¬ (cdRunMap profile).ReflectsTransitions := by
  intro reflects
  have steps : (cdRunMap profile).ReflectsRewrites :=
    (cdRunMap profile).reflectsRewrites_of_transitions reflects
  obtain ⟨next, _, same⟩ := steps (interface := ()) (term := stepSource LFProfile.typeTypeType)
    (step_halfReduced profile LFProfile.typeTypeType)
  exact halfReduced_not_image LFProfile.typeTypeType next same.symm

/-- So it is not hosting between the calculi as they run. -/
theorem cdRunMap_not_hosting (profile : Profile) : ¬ (cdRunMap profile).Hosting :=
  fun hosting => cdRunMap_not_preserves profile hosting.preserves

/-- **The embedding preserves nonempty reductions.** -/
theorem cdRunMap_simulates (profile : Profile) :
    (cdRunMap profile).atNonemptyReduction.PreservesTransitions := by
  apply (cdRunMap profile).atNonemptyReduction.preservesTransitions_of_rewrites
  intro _ term next steps
  exact (cdRunMap profile).preservesNonemptyReduction
    (fun step => translate_transGen profile step) steps

#print axioms cdMap
#print axioms cdMap_reflects_erasure
#print axioms cdRawMap_hosting
#print axioms respectsErasure_iff
#print axioms simplyTyped_respectsErasure
#print axioms simplyTyped_hosting
#print axioms nonFunctional_not_respectsErasure
#print axioms translate_not_step
#print axioms halfReduced_not_image
#print axioms cdRunMap_not_preserves
#print axioms cdRunMap_not_reflects
#print axioms cdRunMap_simulates

end Mettapedia.GSLT.Dedukti
