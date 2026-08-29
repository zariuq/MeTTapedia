import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.TypedSubstitution

/-!
# Generic generation for cumulative presentation judgments

Typing rules determine a principal result before the two deliberately
non-syntax-directed tail rules are used.  Conversion may replace that result
by a definitionally equal type, while cumulativity may raise a universe head.
`TypeAdjustment` records precisely those directed changes.

The generation theorems are presentation-independent: they apply to every
choice of universe heads, declarations, and root computation.  In particular,
they are not a checker and do not assume normalization or confluence.  They
expose the additional injectivity/coherence results that a fragment authority
must earn before it can invert an adjustment.
-/

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation

/-! ## Directed result-type adjustment -/

/-- The exact closure of the two tail rules of `HasType`.  Conversion is
symmetric internally, but universe lifting remains directed. -/
inductive TypeAdjustment (rules : Rules Head) :
    Tm Head n → Tm Head n → Prop where
  | refl (type : Tm Head n) : TypeAdjustment rules type type
  | conversion {source target : Tm Head n} :
      Conv rules.headEq source target rules.computation →
      TypeAdjustment rules source target
  | cumulative {source target : Head} :
      rules.cumulative source target →
      TypeAdjustment rules (.head source) (.head target)
  | trans {source middle target : Tm Head n} :
      TypeAdjustment rules source middle →
      TypeAdjustment rules middle target →
      TypeAdjustment rules source target

namespace TypeAdjustment

theorem trans_assoc {rules : Rules Head}
    {first second third fourth : Tm Head n}
    (firstSecond : TypeAdjustment rules first second)
    (secondThird : TypeAdjustment rules second third)
    (thirdFourth : TypeAdjustment rules third fourth) :
    TypeAdjustment rules first fourth :=
  .trans firstSecond (.trans secondThird thirdFourth)

/-- Renaming preserves every directed adjustment. -/
theorem rename {rules : Rules Head} {source target : Tm Head n}
    (adjustment : TypeAdjustment rules source target) (rho : Ren n m) :
    TypeAdjustment rules (Presentation.rename rho source)
      (Presentation.rename rho target) := by
  induction adjustment with
  | refl type => exact .refl _
  | conversion conversion =>
      exact .conversion (conversion.renameTerms rho)
  | cumulative order => exact .cumulative order
  | trans first second ihFirst ihSecond => exact .trans ihFirst ihSecond

/-- Substitution preserves every directed adjustment. -/
theorem substitute {rules : Rules Head} {source target : Tm Head n}
    (adjustment : TypeAdjustment rules source target)
    (substitution : Sub Head n m) :
    TypeAdjustment rules (Presentation.subst substitution source)
      (Presentation.subst substitution target) := by
  induction adjustment with
  | refl type => exact .refl _
  | conversion conversion =>
      exact .conversion (conversion.substitute substitution)
  | cumulative order => exact .cumulative order
  | trans first second ihFirst ihSecond => exact .trans ihFirst ihSecond

end TypeAdjustment

/-! ## The conversion boundary needed by Pi-valued generation -/

/-- The two constructor-separation laws needed to turn a directed typing
adjustment ending at a dependent-function type back into conversion evidence.

This is intentionally smaller than normalization, confluence, or a general
conversion decision procedure.  A presentation may obtain it from any
conversion metatheory that proves Pi injectivity and prevents a Pi type from
being convertible to a universe head. -/
structure PiConversionBoundary (rules : Rules Head) : Prop where
  components {n : Nat} {domain₁ domain₂ : Tm Head n}
      {codomain₁ codomain₂ : Tm Head (n + 1)} :
    Conv rules.headEq (.pi domain₁ codomain₁)
        (.pi domain₂ codomain₂) rules.computation →
      Conv rules.headEq domain₁ domain₂ rules.computation ∧
      Conv rules.headEq codomain₁ codomain₂ rules.computation
  headDisjoint {n : Nat} {domain : Tm Head n}
      {codomain : Tm Head (n + 1)} {head : Head} :
    ¬ Conv rules.headEq (.pi domain codomain) (.head head) rules.computation

/-- Negative control: a presentation that collapses a dependent-function
type into a universe head cannot possess the Pi conversion boundary. -/
theorem noPiConversionBoundaryOfHeadCollapse
    {rules : Rules Head} {domain : Tm Head n}
    {codomain : Tm Head (n + 1)} {head : Head}
    (collapse :
      Conv rules.headEq (.pi domain codomain) (.head head)
        rules.computation) :
    ¬ PiConversionBoundary rules := by
  intro boundary
  exact boundary.headDisjoint collapse

/-- A type belongs to the Pi conversion class when it converts to some
dependent-function type.  This is a support predicate only; it retains no
chosen normalization procedure. -/
def PiConvertible (rules : Rules Head) (type : Tm Head n) : Prop :=
  ∃ domain codomain,
    Conv rules.headEq type (.pi domain codomain) rules.computation

/-- Directed cumulativity cannot occur on a path whose target is in a Pi
conversion class, provided Pi types and universe heads are disjoint.
Consequently the complete adjustment is already conversion evidence. -/
theorem TypeAdjustment.toConvOfPiConvertibleTarget
    {rules : Rules Head} (boundary : PiConversionBoundary rules)
    {source target : Tm Head n}
    (adjustment : TypeAdjustment rules source target) :
    PiConvertible rules target →
      Conv rules.headEq source target rules.computation := by
  induction adjustment with
  | refl type =>
      intro _targetPi
      exact Relation.EqvGen.refl _
  | conversion conversion =>
      intro _targetPi
      exact conversion
  | @cumulative sourceHead targetHead order =>
      intro targetPi
      rcases targetPi with ⟨domain, codomain, conversion⟩
      exact False.elim
        (boundary.headDisjoint
          (Relation.EqvGen.symm _ _ conversion))
  | @trans source middle target first second ihFirst ihSecond =>
      intro targetPi
      have secondConversion :
          Conv rules.headEq middle target rules.computation :=
        ihSecond targetPi
      rcases targetPi with ⟨domain, codomain, targetConversion⟩
      have middlePi : PiConvertible rules middle :=
        ⟨domain, codomain,
          Relation.EqvGen.trans _ _ _ secondConversion targetConversion⟩
      exact Relation.EqvGen.trans _ _ _
        (ihFirst middlePi) secondConversion

/-- Specialization of `toConvOfPiConvertibleTarget` to a syntactically
displayed Pi target. -/
theorem TypeAdjustment.toConvOfPiTarget
    {rules : Rules Head} (boundary : PiConversionBoundary rules)
    {source domain : Tm Head n} {codomain : Tm Head (n + 1)}
    (adjustment : TypeAdjustment rules source (.pi domain codomain)) :
    Conv rules.headEq source (.pi domain codomain) rules.computation :=
  adjustment.toConvOfPiConvertibleTarget boundary
    ⟨domain, codomain, Relation.EqvGen.refl _⟩

/-! ## Replaying an adjustment as typing -/

/-- A typing derivation may be transported along exactly the directed changes
recorded by `TypeAdjustment`. -/
theorem HasType.adjust {rules : Rules Head} {context : Ctx Head n}
    {term source target : Tm Head n}
    (typing : HasType rules context term source)
    (adjustment : TypeAdjustment rules source target) :
    HasType rules context term target := by
  induction adjustment with
  | refl type => exact typing
  | conversion conversion => exact .conv typing conversion
  | cumulative order => exact .cumul typing order
  | trans first second ihFirst ihSecond => exact ihSecond (ihFirst typing)

/-! ## Subject-shape generation -/

private theorem appGenerationAux {rules : Rules Head}
    {context : Ctx Head n} {term displayedType : Tm Head n}
    (typing : HasType rules context term displayedType) :
    ∀ {function argument : Tm Head n}, term = .app function argument →
      ∃ domain codomain,
        HasType rules context function (.pi domain codomain) ∧
        HasType rules context argument domain ∧
        TypeAdjustment rules (inst0 argument codomain) displayedType := by
  induction typing with
  | headType =>
      intro function argument equality
      cases equality
  | var =>
      intro function argument equality
      cases equality
  | const =>
      intro function argument equality
      cases equality
  | piForm =>
      intro function argument equality
      cases equality
  | sigmaForm =>
      intro function argument equality
      cases equality
  | lamIntro =>
      intro function argument equality
      cases equality
  | appElim functionTyping argumentTyping _ _ =>
      intro function argument equality
      cases equality
      exact ⟨_, _, functionTyping, argumentTyping, .refl _⟩
  | pairIntro =>
      intro function argument equality
      cases equality
  | fstElim =>
      intro function argument equality
      cases equality
  | sndElim =>
      intro function argument equality
      cases equality
  | idForm =>
      intro function argument equality
      cases equality
  | reflIntro =>
      intro function argument equality
      cases equality
  | cumul prior order ih =>
      intro function argument equality
      rcases ih equality with
        ⟨domain, codomain, functionTyping, argumentTyping, adjustment⟩
      exact ⟨domain, codomain, functionTyping, argumentTyping,
        .trans adjustment (.cumulative order)⟩
  | conv prior conversion ih =>
      intro function argument equality
      rcases ih equality with
        ⟨domain, codomain, functionTyping, argumentTyping, adjustment⟩
      exact ⟨domain, codomain, functionTyping, argumentTyping,
        .trans adjustment (.conversion conversion)⟩

/-- Every application typing exposes a function typing, an argument typing,
and the complete directed adjustment from the principal application result
to the displayed type. -/
theorem HasType.appGeneration {rules : Rules Head}
    {context : Ctx Head n} {function argument displayedType : Tm Head n}
    (typing : HasType rules context (.app function argument) displayedType) :
    ∃ domain codomain,
      HasType rules context function (.pi domain codomain) ∧
      HasType rules context argument domain ∧
      TypeAdjustment rules (inst0 argument codomain) displayedType :=
  appGenerationAux typing rfl

/-- Pairwise Pi alignment propagates across one application.  The function
term supplies alignment of its two observed Pi typings; generation exposes
the two result adjustments.  Pi-target conversion removes any impossible
cumulative detour, after which component injectivity finishes the proof.

No principal type, normalization function, or executable checker is assumed. -/
theorem HasType.applicationPiAlignment
    {rules : Rules Head} (boundary : PiConversionBoundary rules)
    {context : Ctx Head n} {function argument : Tm Head n}
    {domain₁ domain₂ : Tm Head n}
    {codomain₁ codomain₂ : Tm Head (n + 1)}
    (functionAlignment :
      ∀ {functionDomain₁ functionDomain₂ : Tm Head n}
          {functionCodomain₁ functionCodomain₂ : Tm Head (n + 1)},
        HasType rules context function
            (.pi functionDomain₁ functionCodomain₁) →
        HasType rules context function
            (.pi functionDomain₂ functionCodomain₂) →
          Conv rules.headEq functionDomain₁ functionDomain₂
              rules.computation ∧
            Conv rules.headEq functionCodomain₁ functionCodomain₂
              rules.computation)
    (first : HasType rules context (.app function argument)
      (.pi domain₁ codomain₁))
    (second : HasType rules context (.app function argument)
      (.pi domain₂ codomain₂)) :
    Conv rules.headEq domain₁ domain₂ rules.computation ∧
      Conv rules.headEq codomain₁ codomain₂ rules.computation := by
  rcases first.appGeneration with
    ⟨functionDomain₁, functionCodomain₁, firstFunction,
      _firstArgument, firstAdjustment⟩
  rcases second.appGeneration with
    ⟨functionDomain₂, functionCodomain₂, secondFunction,
      _secondArgument, secondAdjustment⟩
  have functionComponents :=
    functionAlignment firstFunction secondFunction
  have resultComponents :
      Conv rules.headEq
        (inst0 argument functionCodomain₁)
        (inst0 argument functionCodomain₂) rules.computation :=
    functionComponents.2.substitute (subst0 argument)
  have firstConversion := firstAdjustment.toConvOfPiTarget boundary
  have secondConversion := secondAdjustment.toConvOfPiTarget boundary
  have displayedConversion :
      Conv rules.headEq (.pi domain₁ codomain₁)
        (.pi domain₂ codomain₂) rules.computation :=
    Relation.EqvGen.trans _ _ _
      (Relation.EqvGen.symm _ _ firstConversion)
      (Relation.EqvGen.trans _ _ _ resultComponents secondConversion)
  exact boundary.components displayedConversion

/-! ## Principal application inversion under conversion coherence -/

/-- The exact fragment-level coherence needed to compare two dependent
function typings of the same term.  This is deliberately weaker than global
uniqueness of typing, which is false in a cumulative theory: a universe-valued
term may inhabit several ordered universe heads.  A fragment earns this
structure from its conversion metatheory (normally confluence plus `Pi`
injectivity); the declarative judgment does not assume it globally. -/
structure PiTypingCoherence (rules : Rules Head) : Prop where
  compare {n : Nat} {context : Ctx Head n} {term : Tm Head n}
      {domain₁ domain₂ : Tm Head n}
      {codomain₁ codomain₂ : Tm Head (n + 1)} :
    HasType rules context term (.pi domain₁ codomain₁) →
    HasType rules context term (.pi domain₂ codomain₂) →
    Conv rules.headEq (.pi domain₁ codomain₁)
      (.pi domain₂ codomain₂) rules.computation
  components {n : Nat} {domain₁ domain₂ : Tm Head n}
      {codomain₁ codomain₂ : Tm Head (n + 1)} :
    Conv rules.headEq (.pi domain₁ codomain₁)
        (.pi domain₂ codomain₂) rules.computation →
      Conv rules.headEq domain₁ domain₂ rules.computation ∧
      Conv rules.headEq codomain₁ codomain₂ rules.computation

/-- The fragment-scoped form actually needed by an executable authority.
Instead of demanding uniqueness for every typable function in the calculus,
it aligns the two Pi typings only for a named family of recognized function
spines.  The component conversions are returned together, so consumers never
need a stronger global injectivity premise than their fragment uses. -/
structure PiTypingAlignmentOn (rules : Rules Head)
    (Recognized : (n : Nat) → Tm Head n → Prop) : Prop where
  align {n : Nat} {context : Ctx Head n} {term : Tm Head n}
      {domain₁ domain₂ : Tm Head n}
      {codomain₁ codomain₂ : Tm Head (n + 1)} :
    Recognized n term →
    HasType rules context term (.pi domain₁ codomain₁) →
    HasType rules context term (.pi domain₂ codomain₂) →
      Conv rules.headEq domain₁ domain₂ rules.computation ∧
      Conv rules.headEq codomain₁ codomain₂ rules.computation

/-- Global coherence restricts to every recognized fragment. -/
def PiTypingCoherence.toAlignmentOn
    {Head : Type} {rules : Rules Head}
    (coherence : PiTypingCoherence rules)
    (Recognized : (n : Nat) → Tm Head n → Prop) :
    PiTypingAlignmentOn (Head := Head) rules Recognized where
  align := by
    intro n context term domain₁ domain₂ codomain₁ codomain₂
      _recognized first second
    exact coherence.components (coherence.compare first second)

/-- Application inversion needs only fragment-scoped Pi alignment. -/
theorem HasType.appAgainstPrincipalOn {rules : Rules Head}
    {Recognized : (n : Nat) → Tm Head n → Prop}
    (alignment : PiTypingAlignmentOn (Head := Head) rules Recognized)
    {context : Ctx Head n} {function argument : Tm Head n}
    {domain : Tm Head n} {codomain : Tm Head (n + 1)}
    {displayedType : Tm Head n}
    (recognized : Recognized n function)
    (principalFunction :
      HasType rules context function (.pi domain codomain))
    (observedApplication :
      HasType rules context (.app function argument) displayedType) :
    HasType rules context argument domain ∧
      HasType rules context (.app function argument)
        (inst0 argument codomain) ∧
      TypeAdjustment rules (inst0 argument codomain) displayedType := by
  rcases observedApplication.appGeneration with
    ⟨observedDomain, observedCodomain, observedFunction,
      observedArgument, observedAdjustment⟩
  have componentConversions :=
    alignment.align recognized principalFunction observedFunction
  have principalArgument : HasType rules context argument domain :=
    .conv observedArgument
      (Relation.EqvGen.symm _ _ componentConversions.1)
  have principalApplication :
      HasType rules context (.app function argument)
        (inst0 argument codomain) :=
    .appElim principalFunction principalArgument
  have resultConversion :
      Conv rules.headEq (inst0 argument codomain)
        (inst0 argument observedCodomain) rules.computation :=
    componentConversions.2.substitute (subst0 argument)
  exact
    ⟨principalArgument, principalApplication,
      .trans (.conversion resultConversion) observedAdjustment⟩

/-- Invert an observed application against an independently established
principal dependent-function typing.  The argument is reconstructed at the
principal domain, the application is replayed at its principal result, and
every conversion/cumulative tail in the observed derivation is retained as a
directed adjustment to the displayed result.

This is the reusable seam needed by schema-driven computation authority: it
does not normalize, decide conversion, or postulate a global checker. -/
theorem HasType.appAgainstPrincipal {rules : Rules Head}
    (coherence : PiTypingCoherence rules)
    {context : Ctx Head n} {function argument : Tm Head n}
    {domain : Tm Head n} {codomain : Tm Head (n + 1)}
    {displayedType : Tm Head n}
    (principalFunction :
      HasType rules context function (.pi domain codomain))
    (observedApplication :
      HasType rules context (.app function argument) displayedType) :
    HasType rules context argument domain ∧
      HasType rules context (.app function argument)
        (inst0 argument codomain) ∧
      TypeAdjustment rules (inst0 argument codomain) displayedType :=
  HasType.appAgainstPrincipalOn
    (coherence.toAlignmentOn (fun _n _term => True)) True.intro
    principalFunction observedApplication

private theorem constantGenerationAux {rules : Rules Head}
    {context : Ctx Head n} {term displayedType : Tm Head n}
    (typing : HasType rules context term displayedType) :
    ∀ {name : DeclName}, term = .const name →
      ∃ declaredType : Tm Head 0,
        rules.constantType name = some declaredType ∧
        TypeAdjustment rules (liftClosed declaredType) displayedType := by
  induction typing with
  | headType =>
      intro name equality
      cases equality
  | var =>
      intro name equality
      cases equality
  | const lookup =>
      intro name equality
      cases equality
      exact ⟨_, lookup, .refl _⟩
  | piForm =>
      intro name equality
      cases equality
  | sigmaForm =>
      intro name equality
      cases equality
  | lamIntro =>
      intro name equality
      cases equality
  | appElim =>
      intro name equality
      cases equality
  | pairIntro =>
      intro name equality
      cases equality
  | fstElim =>
      intro name equality
      cases equality
  | sndElim =>
      intro name equality
      cases equality
  | idForm =>
      intro name equality
      cases equality
  | reflIntro =>
      intro name equality
      cases equality
  | cumul prior order ih =>
      intro name equality
      rcases ih equality with ⟨declaredType, lookup, adjustment⟩
      exact ⟨declaredType, lookup,
        .trans adjustment (.cumulative order)⟩
  | conv prior conversion ih =>
      intro name equality
      rcases ih equality with ⟨declaredType, lookup, adjustment⟩
      exact ⟨declaredType, lookup,
        .trans adjustment (.conversion conversion)⟩

/-- A constant typing exposes the actual declaration and records every later
conversion or universe lift instead of pretending its displayed type is
definitionally the declaration type. -/
theorem HasType.constantGeneration {rules : Rules Head}
    {context : Ctx Head n} {name : DeclName} {displayedType : Tm Head n}
    (typing : HasType rules context (.const name) displayedType) :
    ∃ declaredType : Tm Head 0,
      rules.constantType name = some declaredType ∧
      TypeAdjustment rules (liftClosed declaredType) displayedType :=
  constantGenerationAux typing rfl

/-- Two Pi-valued typings of the same declared constant align whenever the
presentation has earned the Pi conversion boundary.  Declaration lookup is
functional, and Pi-target adjustments cannot conceal a cumulative detour. -/
theorem HasType.constantPiAlignment
    {rules : Rules Head} (boundary : PiConversionBoundary rules)
    {context : Ctx Head n} {name : DeclName}
    {domain₁ domain₂ : Tm Head n}
    {codomain₁ codomain₂ : Tm Head (n + 1)}
    (first : HasType rules context (.const name) (.pi domain₁ codomain₁))
    (second : HasType rules context (.const name) (.pi domain₂ codomain₂)) :
    Conv rules.headEq domain₁ domain₂ rules.computation ∧
      Conv rules.headEq codomain₁ codomain₂ rules.computation := by
  rcases first.constantGeneration with
    ⟨firstDeclared, firstLookup, firstAdjustment⟩
  rcases second.constantGeneration with
    ⟨secondDeclared, secondLookup, secondAdjustment⟩
  have declarationEquality : firstDeclared = secondDeclared := by
    have someEquality :
        (some firstDeclared : Option (Tm Head 0)) = some secondDeclared :=
      firstLookup.symm.trans secondLookup
    exact Option.some.inj someEquality
  subst secondDeclared
  have firstConversion := firstAdjustment.toConvOfPiTarget boundary
  have secondConversion := secondAdjustment.toConvOfPiTarget boundary
  have displayedConversion :
      Conv rules.headEq (.pi domain₁ codomain₁)
        (.pi domain₂ codomain₂) rules.computation :=
    Relation.EqvGen.trans _ _ _
      (Relation.EqvGen.symm _ _ firstConversion) secondConversion
  exact boundary.components displayedConversion

/-- The declaration lookup support of constant generation. -/
theorem HasType.constantDeclared {rules : Rules Head}
    {context : Ctx Head n} {name : DeclName} {displayedType : Tm Head n}
    (typing : HasType rules context (.const name) displayedType) :
    ∃ declaredType : Tm Head 0,
      rules.constantType name = some declaredType := by
  rcases typing.constantGeneration with ⟨declaredType, lookup, _⟩
  exact ⟨declaredType, lookup⟩

/-! ## Negative controls -/

/-- No tail conversion or cumulative rule can type an application whose
function has no dependent-function typing. -/
theorem HasType.appImpossibleWithoutFunction {rules : Rules Head}
    {context : Ctx Head n} {function argument displayedType : Tm Head n}
    (missing : ∀ domain codomain,
      ¬ HasType rules context function (.pi domain codomain)) :
    ¬ HasType rules context (.app function argument) displayedType := by
  intro typing
  rcases typing.appGeneration with
    ⟨domain, codomain, functionTyping, _, _⟩
  exact missing domain codomain functionTyping

/-- Conversion and cumulativity cannot conjure a missing global declaration. -/
theorem HasType.constantImpossibleWhenMissing {rules : Rules Head}
    {context : Ctx Head n} {name : DeclName} {displayedType : Tm Head n}
    (missing : rules.constantType name = none) :
    ¬ HasType rules context (.const name) displayedType := by
  intro typing
  rcases typing.constantDeclared with ⟨declaredType, lookup⟩
  rw [missing] at lookup
  cases lookup

/-! ## Axiom audit -/

#print axioms TypeAdjustment.rename
#print axioms TypeAdjustment.substitute
#print axioms noPiConversionBoundaryOfHeadCollapse
#print axioms TypeAdjustment.toConvOfPiConvertibleTarget
#print axioms TypeAdjustment.toConvOfPiTarget
#print axioms HasType.adjust
#print axioms HasType.appGeneration
#print axioms HasType.applicationPiAlignment
#print axioms PiTypingCoherence.toAlignmentOn
#print axioms HasType.appAgainstPrincipalOn
#print axioms HasType.appAgainstPrincipal
#print axioms HasType.constantGeneration
#print axioms HasType.constantPiAlignment
#print axioms HasType.appImpossibleWithoutFunction
#print axioms HasType.constantImpossibleWhenMissing

end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
