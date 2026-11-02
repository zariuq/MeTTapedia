import Mettapedia.OSLF.MeTTaIL.ReferenceStepEquations
import Mettapedia.GSLT.LanguageDef.SortedEquationInstance
import Mettapedia.GSLT.LanguageDef.WellSortedOccurrenceReplacement
import Mettapedia.GSLT.LanguageDef.BagNormalFormTyping

/-!
# Equation disciplines of the reference relation

An authored equation declares, in its type context, the sort each schema variable ranges over. The reference
relation's equations (`ReferenceStep.AuthoredEquation`) match a side of the equation with the ordinary pattern matcher
and do not read that context, so a variable declared to be a name may be bound to a process. That is the **syntax
theory** of the equations. The disciplines below read the context, each in its own way, and live beside it:

- `raw`: every binding is admitted; the syntax theory (`disciplinedEquation_raw_iff`);
- `sorted`: each declared variable is bound to a pattern of its declared type in some context, as the derived
  collection laws already require of their elements. A variable occurring under a binder of the term may still be
  bound to that binder's variable;
- `fresh`: sorted, and **scoped values** (`ScopedValues`): a variable that the instantiated side uses outside a binder
  the matched side captured it under is bound to a closed pattern. The scoped instantiation lifts a value used deeper
  than it was captured but does not lower one used shallower, so without this a bound variable of the value would
  change binder: `λy. Lam (λx. App x x)` would be an η-instance of `λy. y`. With it, the η-law `Lam (λx. App F x) = F`
  reads its side condition, `x` not free in `F`;
- `closed`: each declared variable is bound to a closed object of its declared type, with scoped values.

A closed binding is fresh, a fresh binding is sorted, and a sorted binding is admitted raw (`BindingsAdmitted.mono`,
`ScopeAdmitted.mono`), so the disciplined equivalences are contained in one another (`DisciplinedEquivalent.mono`,
`DisciplinedEquivalent.toEquivalent`). In an
equation-free language every discipline is equality (`disciplinedEquivalent_iff_eq_of_isEquationFree`). The closed
discipline is the one the generated equation theory already states (`EquationSemantics.SortedBindings`,
`bindingsAdmitted_closed_iff`). The disciplines differ only on authored equations: a language whose equations are all
derived from its declarations reads them alike under each (`disciplinedStep_iff_of_equations_nil`).

**The typed interpretation** reads an equation as a judgment `Γ ⊢ s ≡ t : T` (`TypedStep`, `TypedEquivalent`): one
admitted instance between two object terms of the same type in the same context. Typing a whole term types each of its
occurrences in the binder context there (`WellSorted.hasType_typedAt`), so the instance is read at the sort and the
binder context of the place it rewrites, as the binding disciplines above cannot: they see a binding without its place.
Frames that keep types carry the judgment (`TypedEquivalent.fill`), in particular every typed occurrence of base type
(`TypedEquivalent.congr`), and it is contained in the discipline it interprets (`TypedEquivalent.toDisciplined`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.ReferenceStep

open Syntax Match Engine
open Mettapedia.GSLT.LanguageDef.WellSorted (HasType FreeTypeContext isObjectPattern)
open Mettapedia.GSLT.LanguageDef.EquationSemantics (DerivedInstance)
open Mettapedia.OSLF.MeTTaIL.DerivedContexts (OneHoleContext)

/-- **How an equation's instances read its type context.** -/
inductive EquationDiscipline where
  /-- Every binding is admitted: the syntax theory. -/
  | raw
  /-- Each declared variable is bound to a pattern of its declared type in some context. -/
  | sorted
  /-- Sorted, with scoped values: no bound variable of a value changes binder. -/
  | fresh
  /-- Each declared variable is bound to a closed object of its declared type, with scoped values. -/
  | closed
  deriving DecidableEq, Repr

/-- The inclusion order of the disciplines: closed, then fresh, then sorted, then raw. -/
def EquationDiscipline.rank : EquationDiscipline → ℕ
  | .closed => 0
  | .fresh => 1
  | .sorted => 2
  | .raw => 3

/-- **The bindings a discipline admits** for an equation's type context. -/
def BindingsAdmitted (language : LanguageDef) : EquationDiscipline → List (String × TypeExpr) → Bindings → Prop
  | .raw, _, _ => True
  | .sorted, typeContext, bindings | .fresh, typeContext, bindings => ∀ name type, (name, type) ∈ typeContext →
      ∃ free bound, HasType language free bound (applyBindings bindings (.fvar name)) type
  | .closed, typeContext, bindings => ∀ name type, (name, type) ∈ typeContext →
      isObjectPattern (applyBindings bindings (.fvar name)) = true ∧
        HasType language FreeTypeContext.empty [] (applyBindings bindings (.fvar name)) type

/-- **A stricter discipline admits fewer bindings.** -/
theorem BindingsAdmitted.mono {language : LanguageDef} :
    ∀ {strict loose : EquationDiscipline}, strict.rank ≤ loose.rank →
      ∀ {typeContext : List (String × TypeExpr)} {bindings : Bindings},
        BindingsAdmitted language strict typeContext bindings → BindingsAdmitted language loose typeContext bindings
  | _, .raw, _, _, _, _ => trivial
  | .raw, .sorted, order, _, _, _ => absurd order (by decide)
  | .sorted, .sorted, _, _, _, admitted => admitted
  | .fresh, .sorted, _, _, _, admitted => admitted
  | .closed, .sorted, _, _, _, admitted => fun name type member =>
    ⟨FreeTypeContext.empty, [], (admitted name type member).2⟩
  | .raw, .fresh, order, _, _, _ => absurd order (by decide)
  | .sorted, .fresh, order, _, _, _ => absurd order (by decide)
  | .fresh, .fresh, _, _, _, admitted => admitted
  | .closed, .fresh, _, _, _, admitted => fun name type member =>
    ⟨FreeTypeContext.empty, [], (admitted name type member).2⟩
  | .raw, .closed, order, _, _, _ => absurd order (by decide)
  | .sorted, .closed, order, _, _, _ => absurd order (by decide)
  | .fresh, .closed, order, _, _, _ => absurd order (by decide)
  | .closed, .closed, _, _, _, admitted => admitted

/-! ## Scoped values -/

mutual
/-- The depths, under the binders of a pattern, at which it uses a metavariable. -/
def useDepths (name : String) : ℕ → Pattern → List ℕ
  | depth, .fvar other => if other == name then [depth] else []
  | _, .bvar _ => []
  | depth, .apply _ arguments => useDepthsList name depth arguments
  | depth, .lambda _ body => useDepths name (depth + 1) body
  | depth, .multiLambda arity _ body => useDepths name (depth + arity) body
  | depth, .subst body replacement => useDepths name (depth + 1) body ++ useDepths name depth replacement
  | depth, .collection _ elements rest =>
    useDepthsList name depth elements ++ (if rest == some name then [depth] else [])

/-- The depths at which a list of patterns uses a metavariable. -/
def useDepthsList (name : String) : ℕ → List Pattern → List ℕ
  | _, [] => []
  | depth, pattern :: patterns => useDepths name depth pattern ++ useDepthsList name depth patterns
end

/-- **Scoped values**: a metavariable that the instantiated side uses at fewer binders than the matched side captured
it under is bound to a closed pattern, so that the scoped instantiation, which lifts values used deeper but does not
lower values used shallower, changes the binder of no bound variable. -/
def ScopedValues (matched instantiated : Pattern) (bindings : Bindings) : Prop :=
  ∀ name captured, captureDepth name 0 matched = some captured → (∃ used ∈ useDepths name 0 instantiated, used < captured) →
    (applyBindings bindings (.fvar name)).isWellScopedAt 0 = true

/-- **What a discipline asks of the scope of an instance**: scoped values for the fresh and closed disciplines. -/
def EquationDiscipline.ScopeAdmitted : EquationDiscipline → Pattern → Pattern → Bindings → Prop
  | .raw, _, _, _ | .sorted, _, _, _ => True
  | .fresh, matched, instantiated, bindings | .closed, matched, instantiated, bindings =>
    ScopedValues matched instantiated bindings

/-- **A stricter discipline asks more of the scope.** -/
theorem EquationDiscipline.ScopeAdmitted.mono :
    ∀ {strict loose : EquationDiscipline}, strict.rank ≤ loose.rank →
      ∀ {matched instantiated : Pattern} {bindings : Bindings},
        strict.ScopeAdmitted matched instantiated bindings → loose.ScopeAdmitted matched instantiated bindings
  | _, .raw, _, _, _, _, _ | _, .sorted, _, _, _, _, _ => trivial
  | .raw, .fresh, order, _, _, _, _ | .sorted, .fresh, order, _, _, _, _
  | .raw, .closed, order, _, _, _, _ | .sorted, .closed, order, _, _, _, _
  | .fresh, .closed, order, _, _, _, _ => absurd order (by decide)
  | .fresh, .fresh, _, _, _, _, admitted | .closed, .fresh, _, _, _, _, admitted
  | .closed, .closed, _, _, _, _, admitted => admitted

variable (relEnv : RelationEnv) (language : LanguageDef)

/-- **A disciplined equation instance**: an authored instance whose bindings the discipline admits. -/
inductive DisciplinedEquation (discipline : EquationDiscipline) : Pattern → Pattern → Prop
  | forward {equation : Equation} {source : Pattern} {initial final : Bindings} {witnesses : List Witness} :
      equation ∈ language.equations → readsRaw equation = true →
      initial ∈ matchPattern equation.left source →
      PremisesValid relEnv language (captureSitesOf equation.left equation.premises) initial equation.premises
        witnesses final →
      BindingsAdmitted language discipline equation.typeContext final →
      discipline.ScopeAdmitted (captureSitesOf equation.left equation.premises) equation.right final →
      DisciplinedEquation discipline source
        (applyBindingsScoped (captureSitesOf equation.left equation.premises) final 0 equation.right)
  | reverse {equation : Equation} {source : Pattern} {initial final : Bindings} {witnesses : List Witness} :
      equation ∈ language.equations → readsRaw equation = true →
      initial ∈ matchPattern equation.right source →
      PremisesValid relEnv language (captureSitesOf equation.right equation.premises) initial equation.premises
        witnesses final →
      BindingsAdmitted language discipline equation.typeContext final →
      discipline.ScopeAdmitted (captureSitesOf equation.right equation.premises) equation.left final →
      DisciplinedEquation discipline source
        (applyBindingsScoped (captureSitesOf equation.right equation.premises) final 0 equation.left)
  /-- An equation with binders declaring its binding dependencies, read through the declaration. The scoped route checks scope
  but infers no sorts, so only the raw discipline admits it. -/
  | declared {equation : Equation} {orientation : ScopedEquationExecution.Orientation} {ambient : ℕ}
      {source target : Pattern} :
      discipline = .raw → equation ∈ language.equations → readsRaw equation = false →
      target ∈ ScopedEquationExecution.applyEquationAt language ambient equation orientation source →
      DisciplinedEquation discipline source target
  /-- A declared equation with premises, its premises witnessed over the closed captures; again only the raw
  discipline admits it. -/
  | premised {equation : Equation} {orientation : ScopedEquationExecution.Orientation} {ambient : ℕ}
      {witnesses : List Witness} {source target : Pattern} :
      discipline = .raw → equation ∈ language.equations → readsRaw equation = false → equation.premises ≠ [] →
      DeclaredPremised relEnv language equation orientation ambient witnesses source target →
      DisciplinedEquation discipline source target

/-- One generator under a discipline: a disciplined authored instance, or a derived collection law. -/
def DisciplinedGenerator (discipline : EquationDiscipline) (source target : Pattern) : Prop :=
  DisciplinedEquation relEnv language discipline source target ∨ DerivedInstance language source target

/-- One disciplined generator in a one-hole context. -/
inductive DisciplinedStep (discipline : EquationDiscipline) : Pattern → Pattern → Prop
  | inContext (context : OneHoleContext) {redex contractum : Pattern} :
      DisciplinedGenerator relEnv language discipline redex contractum →
      DisciplinedStep discipline (context.fill redex) (context.fill contractum)

/-- **Equivalence modulo the equations under a discipline.** -/
def DisciplinedEquivalent (discipline : EquationDiscipline) : Pattern → Pattern → Prop :=
  Relation.EqvGen (DisciplinedStep relEnv language discipline)

/-- **The reference relation modulo the equations under a discipline.** -/
def DisciplinedStepModulo (discipline : EquationDiscipline) (source target : Pattern) : Prop :=
  ∃ redex contractum, DisciplinedEquivalent relEnv language discipline source redex ∧
    Step relEnv language redex contractum ∧ DisciplinedEquivalent relEnv language discipline contractum target

variable {relEnv language}

/-! ## The disciplines among themselves -/

theorem DisciplinedEquation.mono {strict loose : EquationDiscipline} (order : strict.rank ≤ loose.rank)
    {source target : Pattern} (instance_ : DisciplinedEquation relEnv language strict source target) :
    DisciplinedEquation relEnv language loose source target := by
  cases instance_ with
  | forward member undeclared matched valid admitted scope =>
    exact .forward member undeclared matched valid (BindingsAdmitted.mono order admitted)
      (EquationDiscipline.ScopeAdmitted.mono order scope)
  | reverse member undeclared matched valid admitted scope =>
    exact .reverse member undeclared matched valid (BindingsAdmitted.mono order admitted)
      (EquationDiscipline.ScopeAdmitted.mono order scope)
  | declared raw member notRaw produced =>
    subst raw
    cases loose <;> first | exact .declared rfl member notRaw produced | exact absurd order (by decide)
  | premised raw member notRaw premised declaredPremised =>
    subst raw
    cases loose <;> first
      | exact .premised rfl member notRaw premised declaredPremised
      | exact absurd order (by decide)

theorem DisciplinedStep.mono {strict loose : EquationDiscipline} (order : strict.rank ≤ loose.rank)
    {source target : Pattern} (step : DisciplinedStep relEnv language strict source target) :
    DisciplinedStep relEnv language loose source target := by
  cases step with
  | inContext context generator => exact .inContext context (generator.imp (DisciplinedEquation.mono order) id)

/-- **A stricter discipline relates fewer terms.** -/
theorem DisciplinedEquivalent.mono {strict loose : EquationDiscipline} (order : strict.rank ≤ loose.rank)
    {source target : Pattern} (equivalent : DisciplinedEquivalent relEnv language strict source target) :
    DisciplinedEquivalent relEnv language loose source target :=
  Relation.EqvGen.mono (fun _ _ step => DisciplinedStep.mono order step) _ _ equivalent

/-! ## The raw discipline is the syntax theory -/

theorem disciplinedEquation_raw_iff {source target : Pattern} :
    DisciplinedEquation relEnv language .raw source target ↔ AuthoredEquation relEnv language source target := by
  constructor
  · intro instance_
    cases instance_ with
    | forward member undeclared matched valid _ _ => exact .forward member undeclared matched valid
    | reverse member undeclared matched valid _ _ => exact .reverse member undeclared matched valid
    | declared _ member notRaw produced => exact .declared member notRaw produced
    | premised _ member notRaw premised declaredPremised => exact .premised member notRaw premised declaredPremised
  · intro authored
    cases authored with
    | forward member undeclared matched valid => exact .forward member undeclared matched valid trivial trivial
    | reverse member undeclared matched valid => exact .reverse member undeclared matched valid trivial trivial
    | declared member notRaw produced => exact .declared rfl member notRaw produced
    | premised member notRaw premised declaredPremised => exact .premised rfl member notRaw premised declaredPremised

theorem disciplinedStep_raw_iff {source target : Pattern} :
    DisciplinedStep relEnv language .raw source target ↔ EquationStep relEnv language source target := by
  constructor
  · intro step
    cases step with
    | inContext context generator =>
      exact .inContext context (generator.imp disciplinedEquation_raw_iff.mp id)
  · intro step
    cases step with
    | inContext context generator =>
      exact .inContext context (generator.imp disciplinedEquation_raw_iff.mpr id)

theorem disciplinedEquivalent_raw_iff {source target : Pattern} :
    DisciplinedEquivalent relEnv language .raw source target ↔ Equivalent relEnv language source target :=
  ⟨fun equivalent => Relation.EqvGen.mono (fun _ _ step => disciplinedStep_raw_iff.mp step) _ _ equivalent,
    fun equivalent => Relation.EqvGen.mono (fun _ _ step => disciplinedStep_raw_iff.mpr step) _ _ equivalent⟩

/-- **Every disciplined equivalence is contained in the syntax theory.** -/
theorem DisciplinedEquivalent.toEquivalent {discipline : EquationDiscipline} {source target : Pattern}
    (equivalent : DisciplinedEquivalent relEnv language discipline source target) :
    Equivalent relEnv language source target :=
  disciplinedEquivalent_raw_iff.mp (equivalent.mono (by cases discipline <;> decide))

/-- **In an equation-free language every discipline is equality.** -/
theorem disciplinedEquivalent_iff_eq_of_isEquationFree (free : language.isEquationFree = true)
    {discipline : EquationDiscipline} {first second : Pattern} :
    DisciplinedEquivalent relEnv language discipline first second ↔ first = second :=
  ⟨fun equivalent => (equivalent_iff_eq_of_isEquationFree free).mp equivalent.toEquivalent,
    fun same => same ▸ Relation.EqvGen.refl _⟩

/-- **The closed discipline is the generated theory's sorted bindings.** -/
theorem bindingsAdmitted_closed_iff {language : LanguageDef} {typeContext : List (String × TypeExpr)}
    {bindings : Bindings} :
    BindingsAdmitted language .closed typeContext bindings ↔
      Mettapedia.GSLT.LanguageDef.EquationSemantics.SortedBindings language typeContext bindings :=
  Iff.rfl

/-- **The disciplines differ only on authored equations.** -/
theorem disciplinedStep_iff_of_equations_nil (none_ : language.equations = []) {first second : EquationDiscipline}
    {source target : Pattern} :
    DisciplinedStep relEnv language first source target ↔ DisciplinedStep relEnv language second source target := by
  have derived : ∀ {discipline : EquationDiscipline} {redex contractum : Pattern},
      DisciplinedGenerator relEnv language discipline redex contractum ↔ DerivedInstance language redex contractum := by
    intro discipline redex contractum
    refine ⟨fun generator => generator.elim (fun instance_ => ?_) id, Or.inr⟩
    cases instance_ with
    | forward member => rw [none_] at member; cases member
    | reverse member => rw [none_] at member; cases member
    | declared _ member _ => rw [none_] at member; cases member
    | premised _ member _ _ _ => rw [none_] at member; cases member
  constructor
  · rintro ⟨context, generator⟩
    exact .inContext context (derived.mpr (derived.mp generator))
  · rintro ⟨context, generator⟩
    exact .inContext context (derived.mpr (derived.mp generator))

/-! ## The typed interpretation -/

variable (language) in
/-- **A formed term** of a type in a context: an object term of that type meeting a formation condition, such as the
scope policy of a reflective language (`fun _ => True` for typing alone). -/
structure Formed (free : FreeTypeContext) (bound : List TypeExpr) (type : TypeExpr) (formed : Pattern → Prop)
    (term : Pattern) : Prop where
  object : isObjectPattern term = true
  typed : HasType language free bound term type
  formed : formed term

variable (relEnv language) in
/-- **A typed equation step**, the judgment `Γ ⊢ s ≡ t : T` for one instance: two formed terms of type `type` in the
context `(free, bound)`, related by one step of the discipline. -/
def TypedStep (discipline : EquationDiscipline) (free : FreeTypeContext) (bound : List TypeExpr) (type : TypeExpr)
    (formed : Pattern → Prop) (source target : Pattern) : Prop :=
  Formed language free bound type formed source ∧ Formed language free bound type formed target ∧
    DisciplinedStep relEnv language discipline source target

variable (relEnv language) in
/-- **Typed equivalence**: the judgment `Γ ⊢ s ≡ t : T`, through formed terms of that type. -/
def TypedEquivalent (discipline : EquationDiscipline) (free : FreeTypeContext) (bound : List TypeExpr)
    (type : TypeExpr) (formed : Pattern → Prop) : Pattern → Pattern → Prop :=
  Relation.EqvGen (TypedStep relEnv language discipline free bound type formed)

variable {discipline : EquationDiscipline} {free : FreeTypeContext} {bound : List TypeExpr} {type : TypeExpr}
  {formed : Pattern → Prop}

theorem TypedEquivalent.equivalence :
    Equivalence (TypedEquivalent relEnv language discipline free bound type formed) :=
  Relation.EqvGen.is_equivalence _

theorem TypedStep.symm {source target : Pattern}
    (step : TypedStep relEnv language discipline free bound type formed source target) :
    TypedEquivalent relEnv language discipline free bound type formed target source :=
  .symm _ _ (.rel _ _ step)

/-- **Typed equivalence is contained in the discipline it interprets.** -/
theorem TypedEquivalent.toDisciplined {source target : Pattern}
    (equivalent : TypedEquivalent relEnv language discipline free bound type formed source target) :
    DisciplinedEquivalent relEnv language discipline source target :=
  Relation.EqvGen.mono (fun _ _ step => step.2.2) _ _ equivalent

theorem TypedEquivalent.mono {strict loose : EquationDiscipline} (order : strict.rank ≤ loose.rank)
    {source target : Pattern} (equivalent : TypedEquivalent relEnv language strict free bound type formed source target) :
    TypedEquivalent relEnv language loose free bound type formed source target :=
  Relation.EqvGen.mono (fun _ _ step => ⟨step.1, step.2.1, step.2.2.mono order⟩) _ _ equivalent

/-- **A weaker formation condition relates more terms.** -/
theorem TypedEquivalent.weaken {weaker : Pattern → Prop} (implies : ∀ term, formed term → weaker term)
    {source target : Pattern} (equivalent : TypedEquivalent relEnv language discipline free bound type formed source target) :
    TypedEquivalent relEnv language discipline free bound type weaker source target :=
  Relation.EqvGen.mono (fun _ _ step => ⟨⟨step.1.object, step.1.typed, implies _ step.1.formed⟩,
    ⟨step.2.1.object, step.2.1.typed, implies _ step.2.1.formed⟩, step.2.2⟩) _ _ equivalent

/-- **The ends of a typed equivalence are equal or formed.** -/
theorem TypedEquivalent.ends {source target : Pattern}
    (equivalent : TypedEquivalent relEnv language discipline free bound type formed source target) :
    source = target ∨
      (Formed language free bound type formed source ∧ Formed language free bound type formed target) := by
  induction equivalent with
  | rel _ _ step => exact .inr ⟨step.1, step.2.1⟩
  | refl => exact .inl rfl
  | symm _ _ _ ih => exact ih.elim (fun same => .inl same.symm) (fun both => .inr ⟨both.2, both.1⟩)
  | trans _ _ _ _ _ first second =>
    rcases first with rfl | first
    · exact second
    · rcases second with rfl | second
      · exact .inr first
      · exact .inr ⟨first.1, second.2⟩

/-- A typed equivalence from a formed term ends at a formed term. -/
theorem TypedEquivalent.formed_right {source target : Pattern}
    (equivalent : TypedEquivalent relEnv language discipline free bound type formed source target)
    (sourceFormed : Formed language free bound type formed source) :
    Formed language free bound type formed target :=
  equivalent.ends.elim (fun same => same ▸ sourceFormed) (·.2)

/-- **Congruence**: a frame that takes formed terms to formed terms carries the judgment, from the binder context
and formation condition of its hole to its own. -/
theorem TypedEquivalent.fill (context : OneHoleContext) {innerBound : List TypeExpr} {innerType : TypeExpr}
    {innerFormed : Pattern → Prop}
    (frame : ∀ term, Formed language free innerBound innerType innerFormed term →
      Formed language free bound type formed (context.fill term))
    {source target : Pattern}
    (equivalent : TypedEquivalent relEnv language discipline free innerBound innerType innerFormed source target) :
    TypedEquivalent relEnv language discipline free bound type formed (context.fill source) (context.fill target) := by
  induction equivalent with
  | rel _ _ step =>
    obtain ⟨sourceFormed, targetFormed, inner⟩ := step
    refine .rel _ _ ⟨frame _ sourceFormed, frame _ targetFormed, ?_⟩
    cases inner with
    | inContext innerContext generator =>
      rw [← OneHoleContext.fill_comp, ← OneHoleContext.fill_comp]
      exact .inContext _ generator
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ first second => exact .trans _ _ _ first second

/-- **A term of base type has no binder form**, so replacing it keeps every parameter representation an occurrence
requires. -/
theorem representationCompatible_of_base {free : FreeTypeContext} {bound : List TypeExpr} {source : Pattern}
    {sort : String} (typed : HasType language free bound source (.base sort)) (target : Pattern) :
    Mettapedia.GSLT.LanguageDef.WellSorted.RepresentationCompatible source target := by
  intro context parameter represented
  cases context with
  | hole =>
    cases parameter with
    | simple => trivial
    | abstractionNamed =>
      cases source <;> simp_all [Mettapedia.GSLT.LanguageDef.WellSorted.MatchesParameterRepresentation,
        OneHoleContext.fill]
      cases typed
    | multiAbstractionNamed =>
      cases source <;> simp_all [Mettapedia.GSLT.LanguageDef.WellSorted.MatchesParameterRepresentation,
        OneHoleContext.fill]
      cases typed
  | lambda binder _ =>
    cases binder <;> cases parameter <;>
      simp_all [Mettapedia.GSLT.LanguageDef.WellSorted.MatchesParameterRepresentation, OneHoleContext.fill]
  | multiLambda _ binders _ =>
    cases binders <;> cases parameter <;>
      simp_all [Mettapedia.GSLT.LanguageDef.WellSorted.MatchesParameterRepresentation, OneHoleContext.fill]
  | _ => cases parameter <;>
      simp_all [Mettapedia.GSLT.LanguageDef.WellSorted.MatchesParameterRepresentation, OneHoleContext.fill]

/-- **Congruence at a typed occurrence of base type**: a typed equivalence at the occurrence, in its binder context,
is one of the whole term, when the frame keeps the formation condition. -/
theorem TypedEquivalent.congr {context : OneHoleContext} {focusBound : List TypeExpr} {sort : String}
    {focusFormed : Pattern → Prop} {source target : Pattern}
    (selected : Mettapedia.GSLT.LanguageDef.WellSorted.TypedAt language free source context bound type focusBound
      (.base sort))
    (object : isObjectPattern (context.fill source) = true)
    (formedFrame : ∀ term, focusFormed term → formed (context.fill term))
    (equivalent : TypedEquivalent relEnv language discipline free focusBound (.base sort) focusFormed source target) :
    TypedEquivalent relEnv language discipline free bound type formed (context.fill source) (context.fill target) :=
  TypedEquivalent.fill context (fun term termFormed =>
    ⟨Mettapedia.GSLT.LanguageDef.BagNormalForm.isObjectPattern_fill_replace context object
        (fun _ => termFormed.object),
      selected.replace (representationCompatible_of_base selected.focus_typed term) termFormed.typed,
      formedFrame term termFormed.formed⟩) equivalent

end Mettapedia.OSLF.MeTTaIL.ReferenceStep
