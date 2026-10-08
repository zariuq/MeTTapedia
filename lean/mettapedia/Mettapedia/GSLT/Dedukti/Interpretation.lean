import Mettapedia.GSLT.Dedukti.Presentation

/-!
# Structural theory morphisms: interpreting constants by closed terms

An interpretation gives each constant a closed term, and extends to all terms
by leaving every other constructor in place (`interpret`).  It is the fold out
of the term syntax determined by its values on the constants, so it commutes
with lifting, with substitution and with the instantiation of pattern
variables (`interpret_lift`, `interpret_subst`, `interpret_instantiate`).
Closedness of the images is what these three laws need; an image with a free
variable fails them (`Controls.open_image_breaks_substitution`).

An interpretation is a morphism from one theory to another when it meets two
obligations.

* `Interpretation.Respects`: the image of every definition and of every
  instance of a declared rule is a conversion of the target.  This is the
  obligation that a checker of the target does not discharge by checking the
  images of the constants: it is about the rules.  Under it, conversion is
  preserved (`Interpretation.conv`), and the interpretation is a map of
  theories between the two calculi as their checkers see them
  (`Interpretation.contextMap`).
* `Interpretation.Typed`: the image of every constant has the image of its
  type, in every context.  With the first obligation, typing is preserved
  (`Interpretation.hasType`).

Interpretations compose, and so do both obligations
(`Interpretation.comp`, `Interpretation.Respects.comp`,
`Interpretation.Typed.comp`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dedukti

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFTyping (lift subst subst0 Ctx ctxLookup ctxLookupAux)
open Mettapedia.GSLT.LanguageDef.LFProfile (Profile ProductRule)
open Mettapedia.GSLT.LanguageDef.LFContextualBetaEta (Context)

/-- Replace every constant by its meaning. -/
def interpret (meaning : String → Term) : Term → Term
  | .con name => meaning name
  | .srt sort => .srt sort
  | .var index => .var index
  | .pi domain body => .pi (interpret meaning domain) (interpret meaning body)
  | .lam domain body => .lam (interpret meaning domain) (interpret meaning body)
  | .app function argument => .app (interpret meaning function) (interpret meaning argument)

/-- An interpretation of constants by closed terms. -/
structure Interpretation where
  meaning : String → Term
  closed : ∀ name, Closed (meaning name)

namespace Interpretation

variable (interpretation : Interpretation)

/-- The action of an interpretation on terms. -/
abbrev apply (term : Term) : Term := interpret interpretation.meaning term

theorem apply_lift (term : Term) :
    ∀ amount cutoff : Nat, interpretation.apply (lift amount cutoff term) =
      lift amount cutoff (interpretation.apply term) := by
  induction term with
  | var index => intro amount cutoff; simp only [lift, apply, interpret]
  | srt sort => intro amount cutoff; rfl
  | con name => intro amount cutoff; exact ((interpretation.closed name).lift amount cutoff).symm
  | pi domain body ihDomain ihBody =>
      intro amount cutoff
      simp only [lift, apply, interpret] at ihDomain ihBody ⊢
      rw [ihDomain, ihBody]
  | lam domain body ihDomain ihBody =>
      intro amount cutoff
      simp only [lift, apply, interpret] at ihDomain ihBody ⊢
      rw [ihDomain, ihBody]
  | app function argument ihFunction ihArgument =>
      intro amount cutoff
      simp only [lift, apply, interpret] at ihFunction ihArgument ⊢
      rw [ihFunction, ihArgument]

theorem apply_subst (term : Term) :
    ∀ (target : Nat) (replacement : Term), interpretation.apply (subst target replacement term) =
      subst target (interpretation.apply replacement) (interpretation.apply term) := by
  induction term with
  | var index =>
      intro target replacement
      simp only [subst, apply, interpret]
      split
      · rfl
      · split <;> rfl
  | srt sort => intro target replacement; rfl
  | con name =>
      intro target replacement
      exact ((interpretation.closed name).subst target _).symm
  | pi domain body ihDomain ihBody =>
      intro target replacement
      have lifted := interpretation.apply_lift replacement 1 0
      simp only [subst, apply, interpret] at ihDomain ihBody lifted ⊢
      rw [ihDomain, ihBody, lifted]
  | lam domain body ihDomain ihBody =>
      intro target replacement
      have lifted := interpretation.apply_lift replacement 1 0
      simp only [subst, apply, interpret] at ihDomain ihBody lifted ⊢
      rw [ihDomain, ihBody, lifted]
  | app function argument ihFunction ihArgument =>
      intro target replacement
      simp only [subst, apply, interpret] at ihFunction ihArgument ⊢
      rw [ihFunction, ihArgument]

theorem apply_subst0 (argument body : Term) :
    interpretation.apply (subst0 argument body) =
      subst0 (interpretation.apply argument) (interpretation.apply body) :=
  interpretation.apply_subst body 0 argument

theorem apply_instantiate (assignment : Nat → Term) (term : Term) :
    ∀ depth : Nat, interpretation.apply (instantiate assignment depth term) =
      instantiate (fun index => interpretation.apply (assignment index)) depth
        (interpretation.apply term) := by
  induction term with
  | var index =>
      intro depth
      simp only [instantiate, apply, interpret]
      split
      · rfl
      · exact interpretation.apply_lift _ _ _
  | srt sort => intro depth; rfl
  | con name =>
      intro depth
      exact (instantiate_of_wellScoped (interpretation.closed name) _ (Nat.zero_le depth)).symm
  | pi domain body ihDomain ihBody =>
      intro depth
      simp only [instantiate, apply, interpret] at ihDomain ihBody ⊢
      rw [ihDomain, ihBody]
  | lam domain body ihDomain ihBody =>
      intro depth
      simp only [instantiate, apply, interpret] at ihDomain ihBody ⊢
      rw [ihDomain, ihBody]
  | app function argument ihFunction ihArgument =>
      intro depth
      simp only [instantiate, apply, interpret] at ihFunction ihArgument ⊢
      rw [ihFunction, ihArgument]

/-- An interpretation keeps closed terms closed, at every depth. -/
theorem apply_wellScoped {term : Term} {depth : Nat} (wellScoped : WellScoped depth term) :
    WellScoped depth (interpretation.apply term) := by
  induction wellScoped with
  | srt => exact .srt
  | con => exact (interpretation.closed _).mono (Nat.zero_le _)
  | var bound => exact .var bound
  | pi _ _ ihDomain ihBody => exact .pi ihDomain ihBody
  | lam _ _ ihDomain ihBody => exact .lam ihDomain ihBody
  | app _ _ ihFunction ihArgument => exact .app ihFunction ihArgument

/-! ## The obligation on rules -/

/-- **The obligation on rules**: the image of every definition and of every
instance of a declared rule of the source is a conversion of the target. -/
structure Respects (source target : Theory) : Prop where
  body : ∀ name term, source.body name = some term →
    Conv target (interpretation.meaning name) (interpretation.apply term)
  rule : ∀ rule, source.rule rule → ∀ assignment : Nat → Term,
    Conv target (interpretation.apply (inst assignment rule.lhs))
      (interpretation.apply (inst assignment rule.rhs))

variable {interpretation} {source target : Theory}

/-- Conversion of the images is carried through every position. -/
theorem conv_plug (context : Context) {first second : Term}
    (convertible : Conv target (interpretation.apply first) (interpretation.apply second)) :
    Conv target (interpretation.apply (context.plug first))
      (interpretation.apply (context.plug second)) := by
  induction context with
  | hole => exact convertible
  | piDomain rest body ih => exact Conv.pi ih (.refl _)
  | piBody domain rest ih => exact Conv.pi (.refl _) ih
  | lamDomain rest body ih => exact Conv.lam ih (.refl _)
  | lamBody domain rest ih => exact Conv.lam (.refl _) ih
  | appFunction rest argument ih => exact Conv.app ih (.refl _)
  | appArgument function rest ih => exact Conv.app (.refl _) ih

theorem Respects.step (respects : interpretation.Respects source target) {first second : Term}
    (step : Step source first second) :
    Conv target (interpretation.apply first) (interpretation.apply second) := by
  cases step with
  | inContext context root =>
      apply conv_plug
      cases root with
      | beta domain body argument =>
          rw [interpretation.apply_subst0]
          exact Conv.beta _ _ _
      | delta defined => exact respects.body _ _ defined
      | rule assignment member => exact respects.rule _ member assignment

/-- **An interpretation that meets the obligation on rules preserves
conversion.** -/
theorem Respects.conv (respects : interpretation.Respects source target) {first second : Term}
    (convertible : Conv source first second) :
    Conv target (interpretation.apply first) (interpretation.apply second) := by
  induction convertible with
  | rel _ _ step => exact respects.step step
  | refl _ => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ihFirst ihSecond => exact .trans _ _ _ ihFirst ihSecond

/-! ## The obligation on constants -/

variable (interpretation) in
/-- **The obligation on constants**: the image of every constant has the image
of its declared type, in the image of every context. -/
structure Typed (profile : Profile) (source target : Theory) : Prop where
  constType : ∀ name type, source.constType name = some type → ∀ context : Ctx,
    HasType profile target (context.map interpretation.apply) (interpretation.meaning name)
      (interpretation.apply type)

theorem ctxLookupAux_map (operation : Term → Term)
    (commutes : ∀ term amount, operation (lift amount 0 term) = lift amount 0 (operation term)) :
    ∀ (context : Ctx) (depth index : Nat),
      ctxLookupAux depth (context.map operation) index =
        (ctxLookupAux depth context index).map operation := by
  intro context
  induction context with
  | nil => intro depth index; simp [ctxLookupAux]
  | cons head tail ih =>
      intro depth index
      cases index with
      | zero => simp [ctxLookupAux, commutes]
      | succ index => simpa [ctxLookupAux] using ih (depth + 1) index

theorem ctxLookup_map (operation : Term → Term)
    (commutes : ∀ term amount, operation (lift amount 0 term) = lift amount 0 (operation term))
    (context : Ctx) (index : Nat) :
    ctxLookup (context.map operation) index = (ctxLookup context index).map operation :=
  ctxLookupAux_map operation commutes context 0 index

/-- **An interpretation that meets both obligations preserves typing.** -/
theorem Respects.hasType {profile : Profile} (respects : interpretation.Respects source target)
    (typed : interpretation.Typed profile source target) {context : Ctx} {term type : Term}
    (derivation : HasType profile source context term type) :
    HasType profile target (context.map interpretation.apply) (interpretation.apply term)
      (interpretation.apply type) := by
  induction derivation with
  | sort axiomHolds => exact .sort axiomHolds
  | @var context index type found =>
      refine .var ?_
      rw [ctxLookup_map interpretation.apply
        (fun term amount => interpretation.apply_lift term amount 0), found]
      rfl
  | con declared => exact typed.constType _ _ declared _
  | pi _ _ rule ihDomain ihBody => exact .pi ihDomain ihBody rule
  | lam _ _ rule _ ihDomain ihBodyType ihBody => exact .lam ihDomain ihBodyType rule ihBody
  | app _ _ ihFunction ihArgument =>
      rw [interpretation.apply_subst0]
      exact .app ihFunction ihArgument
  | conv _ convertible _ ihTerm ihTarget => exact .conv ihTerm (respects.conv convertible) ihTarget

/-! ## Composition -/

/-- The identity interpretation. -/
def id : Interpretation where
  meaning := fun name => .con name
  closed := fun _ => .con

theorem id_apply (term : Term) : Interpretation.id.apply term = term := by
  induction term with
  | var index => rfl
  | srt sort => rfl
  | con name => rfl
  | pi domain body ihDomain ihBody =>
      simp only [apply, interpret] at ihDomain ihBody ⊢
      rw [ihDomain, ihBody]
  | lam domain body ihDomain ihBody =>
      simp only [apply, interpret] at ihDomain ihBody ⊢
      rw [ihDomain, ihBody]
  | app function argument ihFunction ihArgument =>
      simp only [apply, interpret] at ihFunction ihArgument ⊢
      rw [ihFunction, ihArgument]

/-- The composite of two interpretations: interpret the meanings of the first
by the second. -/
def comp (second first : Interpretation) : Interpretation where
  meaning := fun name => second.apply (first.meaning name)
  closed := fun name => second.apply_wellScoped (first.closed name)

theorem comp_apply (second first : Interpretation) (term : Term) :
    (second.comp first).apply term = second.apply (first.apply term) := by
  induction term with
  | var index => rfl
  | srt sort => rfl
  | con name => rfl
  | pi domain body ihDomain ihBody =>
      simp only [apply, interpret] at ihDomain ihBody ⊢
      rw [ihDomain, ihBody]
  | lam domain body ihDomain ihBody =>
      simp only [apply, interpret] at ihDomain ihBody ⊢
      rw [ihDomain, ihBody]
  | app function argument ihFunction ihArgument =>
      simp only [apply, interpret] at ihFunction ihArgument ⊢
      rw [ihFunction, ihArgument]

theorem Respects.id (theory : Theory) : Interpretation.id.Respects theory theory where
  body := fun name term defined => by
    rw [id_apply]
    exact .rel _ _ (Step.root (.delta defined))
  rule := fun rule member assignment => by
    rw [id_apply, id_apply]
    exact Conv.rule member assignment

/-- **The obligation on rules composes.** -/
theorem Respects.comp {first second : Interpretation} {lower middle upper : Theory}
    (secondRespects : second.Respects middle upper) (firstRespects : first.Respects lower middle) :
    (second.comp first).Respects lower upper where
  body := fun name term defined => by
    rw [comp_apply]
    exact secondRespects.conv (firstRespects.body name term defined)
  rule := fun rule member assignment => by
    rw [comp_apply, comp_apply]
    exact secondRespects.conv (firstRespects.rule rule member assignment)

/-- **The obligation on constants composes**, given the obligation on rules
for the second interpretation. -/
theorem Typed.comp {profile : Profile} {first second : Interpretation} {lower middle upper : Theory}
    (secondRespects : second.Respects middle upper) (secondTyped : second.Typed profile middle upper)
    (firstTyped : first.Typed profile lower middle) :
    (second.comp first).Typed profile lower upper where
  constType := fun name type declared context => by
    have image := secondRespects.hasType secondTyped (firstTyped.constType name type declared context)
    have contexts : context.map (second.comp first).apply =
        (context.map first.apply).map second.apply := by
      rw [List.map_map]
      exact List.map_congr_left fun term _ => comp_apply second first term
    rw [contexts, comp_apply]
    exact image

/-! ## An interpretation as a map of theories -/

/-- The action of an interpretation on contexts: holes stay holes. -/
def onContext (meaning : String → Term) {slots : Type} : TermContext slots → TermContext slots
  | .hole slot => .hole slot
  | .srt sort => .srt sort
  | .con name => TermContext.ofTerm (meaning name)
  | .var index => .var index
  | .pi domain body => .pi (onContext meaning domain) (onContext meaning body)
  | .lam domain body => .lam (onContext meaning domain) (onContext meaning body)
  | .app function argument => .app (onContext meaning function) (onContext meaning argument)

theorem apply_fill (interpretation : Interpretation) {slots : Type} (context : TermContext slots)
    (filling : slots → Term) :
    interpretation.apply (context.fill filling) =
      (onContext interpretation.meaning context).fill fun slot => interpretation.apply (filling slot) := by
  induction context with
  | hole slot => rfl
  | srt sort => rfl
  | con name => exact (TermContext.fill_ofTerm _ _).symm
  | var index => rfl
  | pi domain body ihDomain ihBody =>
      simp only [TermContext.fill, onContext, apply, interpret] at ihDomain ihBody ⊢
      rw [ihDomain, ihBody]
  | lam domain body ihDomain ihBody =>
      simp only [TermContext.fill, onContext, apply, interpret] at ihDomain ihBody ⊢
      rw [ihDomain, ihBody]
  | app function argument ihFunction ihArgument =>
      simp only [TermContext.fill, onContext, apply, interpret] at ihFunction ihArgument ⊢
      rw [ihFunction, ihArgument]

/-- **An interpretation that meets the obligation on rules is a map of
theories**, between the two calculi as their checkers see them. -/
def contextMap (interpretation : Interpretation) {source target : Theory}
    (respects : interpretation.Respects source target) :
    ContextMap (conversionTheory source) (conversionTheory target) where
  interface := fun _ => ()
  term := fun term => interpretation.apply term
  context := fun context => onContext interpretation.meaning context
  term_resp := fun convertible => respects.conv convertible
  equivariant := fun context filling => Conv.of_eq (interpretation.apply_fill context filling)

end Interpretation

#print axioms Interpretation.apply_subst
#print axioms Interpretation.apply_instantiate
#print axioms Interpretation.Respects.conv
#print axioms Interpretation.Respects.hasType
#print axioms Interpretation.Respects.comp
#print axioms Interpretation.Typed.comp
#print axioms Interpretation.contextMap

end Mettapedia.GSLT.Dedukti
