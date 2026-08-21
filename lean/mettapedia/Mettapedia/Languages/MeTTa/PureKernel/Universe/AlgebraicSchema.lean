import Mettapedia.Languages.MeTTa.PureKernel.Universe.ConversionCoherence

/-!
# Open algebraic schemas and their metavariable geometry

This module studies open rewrite equations independently of any particular
universe tower, datatype, or execution engine.  A schema variable may occur
under binders; `variableMultiplicity` therefore follows a free variable
through a binder by shifting its de Bruijn index.

Left-linearity is recorded here because it is a property of the presented
equation, not of a checker or reduction strategy.  Later confluence arguments
can state exactly whether they use it.  Non-left-linear schemas remain valid
schemas; they simply require a residual theory that preserves the coherence
of repeated metavariable occurrences.
-/

namespace Mettapedia.Languages.MeTTa.PureKernel.Universe.Presentation
namespace AlgebraicSchema

/-- A family of open algebraic rewrite schemas.  Its arity is the number of
metavariables in the schema, represented by ordinary open-term variables.
This is the logical support layer; proof-relevant root evidence remains in
`ProofRelevantRootComputation`. -/
abbrev SchemaFamily (Head : Type) :=
  {arity : Nat} → Tm Head arity → Tm Head arity → Prop

/-- Number of free occurrences of one open-term variable.  Entering a binder
shifts the tracked variable, so bound variable zero is never confused with a
schema metavariable. -/
def variableMultiplicity (index : Fin n) : Tm Head n → Nat
  | .var candidate => if candidate = index then 1 else 0
  | .const _ => 0
  | .head _ => 0
  | .pi domain codomain =>
      variableMultiplicity index domain +
        variableMultiplicity index.succ codomain
  | .sigma domain codomain =>
      variableMultiplicity index domain +
        variableMultiplicity index.succ codomain
  | .id type left right =>
      variableMultiplicity index type +
        variableMultiplicity index left +
        variableMultiplicity index right
  | .lam body => variableMultiplicity index.succ body
  | .app function argument =>
      variableMultiplicity index function +
        variableMultiplicity index argument
  | .pair first second =>
      variableMultiplicity index first +
        variableMultiplicity index second
  | .fst pair => variableMultiplicity index pair
  | .snd pair => variableMultiplicity index pair
  | .refl term => variableMultiplicity index term

/-- A term is left-linear when every one of its open variables occurs at most
once.  The name refers to its eventual role as the left side of a schema. -/
def LeftLinear (term : Tm Head n) : Prop :=
  ∀ index, variableMultiplicity index term ≤ 1

/-- A schema family is left-linear when every selected left side is. -/
def LeftLinearFamily (schema : SchemaFamily Head) : Prop :=
  ∀ {arity : Nat} {left right : Tm Head arity},
    schema left right → LeftLinear left

/-- Proof-relevant witness that a particular schema variable is repeated. -/
def RepeatedAt (term : Tm Head n) (index : Fin n) : Prop :=
  2 ≤ variableMultiplicity index term

/-- A repeated variable is a direct obstruction to left-linearity. -/
theorem not_leftLinear_of_repeatedAt
    {term : Tm Head n} {index : Fin n}
    (repeated : RepeatedAt term index) : ¬ LeftLinear term := by
  unfold RepeatedAt at repeated
  intro linear
  unfold LeftLinear at linear
  have atMostOne := linear index
  omega

/-! ## Occurrence-separated presentations

A non-left-linear equation can carry strictly more informative presentation
data than its contracted surface form.  The skeleton below gives every
left-hand occurrence its own metavariable; `contraction` records which of
those occurrence variables denote the same authored variable.  Contracting
the skeleton recovers both endpoints exactly.

This structure is geometry, not reduction authority.  In particular it does
not decide whether a runtime may match the separated skeleton directly.  Such
an operational use additionally needs a coherence discipline for the fibres
of `contraction` (syntactic equality, typed conversion, or richer residual
evidence). -/

/-- An occurrence-separated presentation of one possibly non-left-linear
rule.  The informative skeleton lives over its own occurrence telescope;
renaming along `contraction` recovers the authored rule exactly. -/
structure OccurrenceSeparatedRule
    (authoredLeft authoredRight : Tm Head authoredArity) where
  occurrenceArity : Nat
  skeletonLeft : Tm Head occurrenceArity
  skeletonRight : Tm Head occurrenceArity
  contraction : Ren occurrenceArity authoredArity
  contractsLeft :
    Presentation.rename contraction skeletonLeft = authoredLeft
  contractsRight :
    Presentation.rename contraction skeletonRight = authoredRight
  separatedLeft : LeftLinear skeletonLeft

namespace OccurrenceSeparatedRule

/-- A contraction is split when every authored metavariable has a chosen
occurrence representative.  This is kept separate from occurrence
separation: a presentation may legitimately omit an unused authored
variable, while exact factorization of arbitrary substitutions needs a
section. -/
structure SplitContraction
    {authoredLeft authoredRight : Tm Head authoredArity}
    (presentation : OccurrenceSeparatedRule authoredLeft authoredRight) where
  representative : Ren authoredArity presentation.occurrenceArity
  rightInverse : ∀ authored,
    presentation.contraction (representative authored) = authored

/-- An authored substitution expands to the occurrence telescope by giving
every separated occurrence the term selected by its authored variable. -/
def expandSubstitution
    {authoredLeft authoredRight : Tm Head authoredArity}
    (presentation : OccurrenceSeparatedRule authoredLeft authoredRight)
    (substitution : Sub Head authoredArity ambient) :
    Sub Head presentation.occurrenceArity ambient :=
  fun occurrence => substitution (presentation.contraction occurrence)

/-- Evidence that a separated occurrence assignment respects a relation on
every fibre of the contraction.  The relation may live in `Prop` (for
convertibility support) or in `Type` (for proof-relevant conversion receipts),
so the informative theorem is not forced through a truth-value quotient. -/
abbrev FibreEvidence
    {authoredLeft authoredRight : Tm Head authoredArity}
    (presentation : OccurrenceSeparatedRule authoredLeft authoredRight)
    (Related : Tm Head ambient → Tm Head ambient → Sort u)
    (substitution : Sub Head presentation.occurrenceArity ambient) : Sort u :=
  ∀ left right,
    presentation.contraction left = presentation.contraction right →
      Related (substitution left) (substitution right)

/-- A relation is stable under the open-term operations precisely when
pointwise-related substitutions send every open term to related instances.
This packages all constructor congruence laws in their reusable substitution
form. -/
abbrev SubstitutionCompatible
    (Related : Tm Head ambient → Tm Head ambient → Sort u) : Sort u :=
  ∀ {arity : Nat} (term : Tm Head arity)
      (left right : Sub Head arity ambient),
    (∀ index, Related (left index) (right index)) →
      Related (Presentation.subst left term) (Presentation.subst right term)

/-- Equality is substitution-compatible, providing the exact diagonal as the
smallest coherence relation. -/
def equalitySubstitutionCompatible :
    SubstitutionCompatible
      (Head := Head) (ambient := ambient) (fun left right => left = right) := by
  intro arity term left right pointwise
  exact congrArg (fun substitution => Presentation.subst substitution term)
    (funext pointwise)

/-- Declarative conversion is substitution-compatible for every presentation.
This is proved from the conversion constructors and their congruence laws; it
does not assume normalization, confluence, or a checker. -/
def conversionSubstitutionCompatible
    (headEq : Head → Head → Prop)
    (rootRules : RootComputation Head) :
    SubstitutionCompatible
      (ambient := ambient)
      (fun left right => Conv headEq left right rootRules) := by
  intro arity term left right pointwise
  exact Conv.substitutePointwise pointwise term

/-- Exact syntactic coherence is the equality-valued instance of the more
informative fibre-evidence interface. -/
abbrev FibreCoherent
    {authoredLeft authoredRight : Tm Head authoredArity}
    (presentation : OccurrenceSeparatedRule authoredLeft authoredRight)
    (substitution : Sub Head presentation.occurrenceArity ambient) : Prop :=
  presentation.FibreEvidence (fun left right => left = right) substitution

/-- Every expansion of an authored substitution is fibre-coherent. -/
theorem expandSubstitution_coherent
    {authoredLeft authoredRight : Tm Head authoredArity}
    (presentation : OccurrenceSeparatedRule authoredLeft authoredRight)
    (substitution : Sub Head authoredArity ambient) :
    presentation.FibreCoherent
      (presentation.expandSubstitution substitution) := by
  intro left right equality
  exact congrArg substitution equality

namespace SplitContraction

/-- Read an authored substitution from the chosen occurrence representatives. -/
def contractSubstitution
    {authoredLeft authoredRight : Tm Head authoredArity}
    {presentation : OccurrenceSeparatedRule authoredLeft authoredRight}
  (split : presentation.SplitContraction)
    (substitution : Sub Head presentation.occurrenceArity ambient) :
    Sub Head authoredArity ambient :=
  fun authored => substitution (split.representative authored)

/-- Contracting an expanded authored substitution is the identity. -/
theorem contract_expand
    {authoredLeft authoredRight : Tm Head authoredArity}
    {presentation : OccurrenceSeparatedRule authoredLeft authoredRight}
    (split : presentation.SplitContraction)
    (substitution : Sub Head authoredArity ambient) :
    split.contractSubstitution
        (presentation.expandSubstitution substitution) = substitution := by
  funext authored
  exact congrArg substitution (split.rightInverse authored)

/-- Coherence is precisely what makes expansion after contraction the
identity on an occurrence substitution. -/
theorem expand_contract_of_coherent
    {authoredLeft authoredRight : Tm Head authoredArity}
    {presentation : OccurrenceSeparatedRule authoredLeft authoredRight}
    (split : presentation.SplitContraction)
    {substitution : Sub Head presentation.occurrenceArity ambient}
    (coherent : presentation.FibreCoherent substitution) :
    presentation.expandSubstitution
        (split.contractSubstitution substitution) = substitution := by
  funext occurrence
  apply coherent (split.representative (presentation.contraction occurrence))
    occurrence
  exact split.rightInverse (presentation.contraction occurrence)

/-- Universal property of the contraction: coherent occurrence assignments
are exactly the image of authored assignments. -/
theorem coherent_iff_exists_expansion
    {authoredLeft authoredRight : Tm Head authoredArity}
    {presentation : OccurrenceSeparatedRule authoredLeft authoredRight}
    (split : presentation.SplitContraction)
    (substitution : Sub Head presentation.occurrenceArity ambient) :
    presentation.FibreCoherent substitution ↔
      ∃ authoredSubstitution : Sub Head authoredArity ambient,
        presentation.expandSubstitution authoredSubstitution = substitution := by
  constructor
  · intro coherent
    exact ⟨split.contractSubstitution substitution,
      split.expand_contract_of_coherent coherent⟩
  · rintro ⟨authoredSubstitution, rfl⟩
    exact presentation.expandSubstitution_coherent authoredSubstitution

/-- Relational universal property of a split contraction.  Fibre evidence
relates every separated occurrence to the expansion of the authored
substitution read from the chosen representatives.  When `Related` carries
derivations in `Type`, this function preserves those derivations. -/
def occurrenceEvidenceToExpansion
    {authoredLeft authoredRight : Tm Head authoredArity}
    {presentation : OccurrenceSeparatedRule authoredLeft authoredRight}
    (split : presentation.SplitContraction)
    (Related : Tm Head ambient → Tm Head ambient → Sort u)
    {substitution : Sub Head presentation.occurrenceArity ambient}
    (evidence : presentation.FibreEvidence Related substitution) :
    ∀ occurrence,
      Related (substitution occurrence)
        (presentation.expandSubstitution
          (split.contractSubstitution substitution) occurrence) := by
  intro occurrence
  change Related (substitution occurrence)
    (substitution
      (split.representative (presentation.contraction occurrence)))
  apply evidence occurrence
    (split.representative (presentation.contraction occurrence))
  exact (split.rightInverse (presentation.contraction occurrence)).symm

end SplitContraction

/-- Substitution after occurrence expansion recovers the exact authored left
instance.  No quotient or endpoint-only comparison is involved. -/
theorem subst_skeletonLeft
    {authoredLeft authoredRight : Tm Head authoredArity}
    (presentation : OccurrenceSeparatedRule authoredLeft authoredRight)
    (substitution : Sub Head authoredArity ambient) :
    Presentation.subst (presentation.expandSubstitution substitution)
        presentation.skeletonLeft =
      Presentation.subst substitution authoredLeft := by
  calc
    Presentation.subst (presentation.expandSubstitution substitution)
        presentation.skeletonLeft =
        Presentation.subst
          (fun occurrence => substitution
            (presentation.contraction occurrence))
          presentation.skeletonLeft := rfl
    _ = Presentation.subst substitution
          (Presentation.rename presentation.contraction
            presentation.skeletonLeft) :=
      (Presentation.subst_rename substitution presentation.contraction
        presentation.skeletonLeft).symm
    _ = Presentation.subst substitution authoredLeft :=
      congrArg (Presentation.subst substitution) presentation.contractsLeft

/-- The same exact recovery holds for the right endpoint. -/
theorem subst_skeletonRight
    {authoredLeft authoredRight : Tm Head authoredArity}
    (presentation : OccurrenceSeparatedRule authoredLeft authoredRight)
    (substitution : Sub Head authoredArity ambient) :
    Presentation.subst (presentation.expandSubstitution substitution)
        presentation.skeletonRight =
      Presentation.subst substitution authoredRight := by
  calc
    Presentation.subst (presentation.expandSubstitution substitution)
        presentation.skeletonRight =
        Presentation.subst
          (fun occurrence => substitution
            (presentation.contraction occurrence))
          presentation.skeletonRight := rfl
    _ = Presentation.subst substitution
          (Presentation.rename presentation.contraction
            presentation.skeletonRight) :=
      (Presentation.subst_rename substitution presentation.contraction
        presentation.skeletonRight).symm
    _ = Presentation.subst substitution authoredRight :=
      congrArg (Presentation.subst substitution) presentation.contractsRight

namespace SplitContraction

/-- A coherent occurrence assignment factors through the contraction on the
left endpoint.  This is the converse direction to `subst_skeletonLeft`: it
shows that occurrence separation adds presentation data, not new coherent
instances. -/
theorem subst_skeletonLeft_of_coherent
    {authoredLeft authoredRight : Tm Head authoredArity}
    {presentation : OccurrenceSeparatedRule authoredLeft authoredRight}
    (split : presentation.SplitContraction)
    {substitution : Sub Head presentation.occurrenceArity ambient}
    (coherent : presentation.FibreCoherent substitution) :
    Presentation.subst substitution presentation.skeletonLeft =
      Presentation.subst (split.contractSubstitution substitution)
        authoredLeft := by
  calc
    Presentation.subst substitution presentation.skeletonLeft =
        Presentation.subst
          (presentation.expandSubstitution
            (split.contractSubstitution substitution))
          presentation.skeletonLeft :=
      congrArg
        (fun selected => Presentation.subst selected
          presentation.skeletonLeft)
        (split.expand_contract_of_coherent coherent).symm
    _ = Presentation.subst (split.contractSubstitution substitution)
          authoredLeft :=
      presentation.subst_skeletonLeft
        (split.contractSubstitution substitution)

/-- The same factorization theorem holds on the right endpoint. -/
theorem subst_skeletonRight_of_coherent
    {authoredLeft authoredRight : Tm Head authoredArity}
    {presentation : OccurrenceSeparatedRule authoredLeft authoredRight}
    (split : presentation.SplitContraction)
    {substitution : Sub Head presentation.occurrenceArity ambient}
    (coherent : presentation.FibreCoherent substitution) :
    Presentation.subst substitution presentation.skeletonRight =
      Presentation.subst (split.contractSubstitution substitution)
        authoredRight := by
  calc
    Presentation.subst substitution presentation.skeletonRight =
        Presentation.subst
          (presentation.expandSubstitution
            (split.contractSubstitution substitution))
          presentation.skeletonRight :=
      congrArg
        (fun selected => Presentation.subst selected
          presentation.skeletonRight)
        (split.expand_contract_of_coherent coherent).symm
    _ = Presentation.subst (split.contractSubstitution substitution)
          authoredRight :=
      presentation.subst_skeletonRight
        (split.contractSubstitution substitution)

/-- Relation-valued endpoint factorization on the left.  A compatible
coherence relation need not identify separated occurrences definitionally;
it transports their evidence through the whole open schema and relates the
result to the contracted authored instance. -/
def skeletonLeftEvidenceToAuthored
    {authoredLeft authoredRight : Tm Head authoredArity}
    {presentation : OccurrenceSeparatedRule authoredLeft authoredRight}
    (split : presentation.SplitContraction)
    (Related : Tm Head ambient → Tm Head ambient → Sort u)
    (compatible : SubstitutionCompatible Related)
    {substitution : Sub Head presentation.occurrenceArity ambient}
    (evidence : presentation.FibreEvidence Related substitution) :
    Related
      (Presentation.subst substitution presentation.skeletonLeft)
      (Presentation.subst (split.contractSubstitution substitution)
        authoredLeft) := by
  have endpointEvidence := compatible presentation.skeletonLeft substitution
    (presentation.expandSubstitution
      (split.contractSubstitution substitution))
    (split.occurrenceEvidenceToExpansion Related evidence)
  rw [presentation.subst_skeletonLeft
    (split.contractSubstitution substitution)] at endpointEvidence
  exact endpointEvidence

/-- Relation-valued endpoint factorization on the right. -/
def skeletonRightEvidenceToAuthored
    {authoredLeft authoredRight : Tm Head authoredArity}
    {presentation : OccurrenceSeparatedRule authoredLeft authoredRight}
    (split : presentation.SplitContraction)
    (Related : Tm Head ambient → Tm Head ambient → Sort u)
    (compatible : SubstitutionCompatible Related)
    {substitution : Sub Head presentation.occurrenceArity ambient}
    (evidence : presentation.FibreEvidence Related substitution) :
    Related
      (Presentation.subst substitution presentation.skeletonRight)
      (Presentation.subst (split.contractSubstitution substitution)
        authoredRight) := by
  have endpointEvidence := compatible presentation.skeletonRight substitution
    (presentation.expandSubstitution
      (split.contractSubstitution substitution))
    (split.occurrenceEvidenceToExpansion Related evidence)
  rw [presentation.subst_skeletonRight
    (split.contractSubstitution substitution)] at endpointEvidence
  exact endpointEvidence

/-- Conversion-coherent occurrence assignments produce a left endpoint
convertible to the exact authored instance selected by the representatives. -/
theorem skeletonLeft_conv_toAuthored
    {authoredLeft authoredRight : Tm Head authoredArity}
    {presentation : OccurrenceSeparatedRule authoredLeft authoredRight}
    (split : presentation.SplitContraction)
    (headEq : Head → Head → Prop)
    (rootRules : RootComputation Head)
    {substitution : Sub Head presentation.occurrenceArity ambient}
    (evidence : presentation.FibreEvidence
      (fun left right => Conv headEq left right rootRules) substitution) :
    Conv headEq
      (Presentation.subst substitution presentation.skeletonLeft)
      (Presentation.subst (split.contractSubstitution substitution)
        authoredLeft)
      rootRules :=
  split.skeletonLeftEvidenceToAuthored
    (fun left right => Conv headEq left right rootRules)
    (conversionSubstitutionCompatible headEq rootRules) evidence

/-- The corresponding conversion factorization for the right endpoint. -/
theorem skeletonRight_conv_toAuthored
    {authoredLeft authoredRight : Tm Head authoredArity}
    {presentation : OccurrenceSeparatedRule authoredLeft authoredRight}
    (split : presentation.SplitContraction)
    (headEq : Head → Head → Prop)
    (rootRules : RootComputation Head)
    {substitution : Sub Head presentation.occurrenceArity ambient}
    (evidence : presentation.FibreEvidence
      (fun left right => Conv headEq left right rootRules) substitution) :
    Conv headEq
      (Presentation.subst substitution presentation.skeletonRight)
      (Presentation.subst (split.contractSubstitution substitution)
        authoredRight)
      rootRules :=
  split.skeletonRightEvidenceToAuthored
    (fun left right => Conv headEq left right rootRules)
    (conversionSubstitutionCompatible headEq rootRules) evidence

/-- A conversion-coherent occurrence instance is admissible in the authored
conversion theory whenever its contracted instance is an authorized root
step.  This is a conservativity theorem: it licenses reasoning through the
informative occurrence presentation without adding the unrestricted
left-linear skeleton to root computation. -/
theorem occurrenceInstance_conv_of_fibreEvidence
    {authoredLeft authoredRight : Tm Head authoredArity}
    {presentation : OccurrenceSeparatedRule authoredLeft authoredRight}
    (split : presentation.SplitContraction)
    (headEq : Head → Head → Prop)
    (rootRules : RootComputation Head)
    {substitution : Sub Head presentation.occurrenceArity ambient}
    (evidence : presentation.FibreEvidence
      (fun left right => Conv headEq left right rootRules) substitution)
    (authorized : rootRules.step
      (Presentation.subst (split.contractSubstitution substitution)
        authoredLeft)
      (Presentation.subst (split.contractSubstitution substitution)
        authoredRight)) :
    Conv headEq
      (Presentation.subst substitution presentation.skeletonLeft)
      (Presentation.subst substitution presentation.skeletonRight)
      rootRules :=
  .trans _ _ _
    (split.skeletonLeft_conv_toAuthored headEq rootRules evidence)
    (.trans _ _ _
      (.rel _ _ (Step.root authorized))
      (.symm _ _
        (split.skeletonRight_conv_toAuthored headEq rootRules evidence)))

end SplitContraction

/-- An ordinary instance of the authored equation. -/
def AuthoredInstance
    {authoredLeft authoredRight : Tm Head authoredArity}
    (_presentation : OccurrenceSeparatedRule authoredLeft authoredRight)
    (source target : Tm Head ambient) : Prop :=
  ∃ substitution : Sub Head authoredArity ambient,
    Presentation.subst substitution authoredLeft = source ∧
    Presentation.subst substitution authoredRight = target

/-- An occurrence-skeleton instance whose separated copies satisfy the exact
fibre equations recorded by the contraction. -/
def CoherentOccurrenceInstance
    {authoredLeft authoredRight : Tm Head authoredArity}
    (presentation : OccurrenceSeparatedRule authoredLeft authoredRight)
    (source target : Tm Head ambient) : Prop :=
  ∃ substitution : Sub Head presentation.occurrenceArity ambient,
    presentation.FibreCoherent substitution ∧
    Presentation.subst substitution presentation.skeletonLeft = source ∧
    Presentation.subst substitution presentation.skeletonRight = target

/-- Exact-image theorem: for a split contraction, authored instances are
precisely coherent occurrence-skeleton instances.  Thus left-linearization is
an informative presentation refinement with an explicit diagonal condition,
not a widening of the rule relation. -/
theorem coherentOccurrenceInstance_iff_authoredInstance
    {authoredLeft authoredRight : Tm Head authoredArity}
    {presentation : OccurrenceSeparatedRule authoredLeft authoredRight}
    (split : presentation.SplitContraction)
    (source target : Tm Head ambient) :
    presentation.CoherentOccurrenceInstance source target ↔
      presentation.AuthoredInstance source target := by
  constructor
  · rintro ⟨substitution, coherent, leftEndpoint, rightEndpoint⟩
    refine ⟨split.contractSubstitution substitution, ?_, ?_⟩
    · exact (split.subst_skeletonLeft_of_coherent coherent).symm.trans
        leftEndpoint
    · exact (split.subst_skeletonRight_of_coherent coherent).symm.trans
        rightEndpoint
  · rintro ⟨substitution, leftEndpoint, rightEndpoint⟩
    refine ⟨presentation.expandSubstitution substitution,
      presentation.expandSubstitution_coherent substitution, ?_, ?_⟩
    · exact (presentation.subst_skeletonLeft substitution).trans leftEndpoint
    · exact (presentation.subst_skeletonRight substitution).trans rightEndpoint

end OccurrenceSeparatedRule

/-- Every logical schema has an occurrence-separated presentation.  The
support layer exposes inhabitation; named presentation data (or the separate
proof-relevant root-evidence layer) retains the actual receipt. -/
abbrev OccurrenceSeparatedFamily (schema : SchemaFamily Head) :=
  ∀ {arity : Nat} {left right : Tm Head arity},
    schema left right → Nonempty (OccurrenceSeparatedRule left right)

namespace Canary

/-- Positive control: an ordinary two-metavariable application pattern is
left-linear. -/
def linearApplication : Tm Unit 2 :=
  .app (.var 1) (.var 0)

theorem linearApplication_leftLinear : LeftLinear linearApplication := by
  intro index
  refine Fin.cases ?_ (fun tail => Fin.cases ?_ (fun impossible =>
    Fin.elim0 impossible) tail) index
  · decide
  · decide

/-- Negative control: sharing a metavariable in both application positions is
detectably non-left-linear. -/
def repeatedApplication : Tm Unit 1 :=
  .app (.var 0) (.var 0)

theorem repeatedApplication_repeated :
    RepeatedAt repeatedApplication 0 := by
  change 2 ≤ 2
  exact Nat.le_refl 2

theorem repeatedApplication_not_leftLinear :
    ¬ LeftLinear repeatedApplication :=
  not_leftLinear_of_repeatedAt repeatedApplication_repeated

/-- Positive control: an already-linear rule has an occurrence presentation
whose contraction is the identity. -/
def linearApplicationSeparation :
    OccurrenceSeparatedRule linearApplication (.var 0) where
  occurrenceArity := 2
  skeletonLeft := linearApplication
  skeletonRight := .var 0
  contraction := idRen
  contractsLeft := by decide
  contractsRight := by decide
  separatedLeft := linearApplication_leftLinear

def linearApplicationSplit :
    linearApplicationSeparation.SplitContraction where
  representative := idRen
  rightInverse := by intro authored; rfl

theorem linearApplicationSeparation_injective :
    Function.Injective linearApplicationSeparation.contraction := by
  intro left right equality
  exact equality

/-- The repeated application is recovered from a two-occurrence linear
skeleton by identifying both occurrence variables. -/
def repeatedApplicationSeparation :
    OccurrenceSeparatedRule repeatedApplication (.var 0) where
  occurrenceArity := 2
  skeletonLeft := linearApplication
  skeletonRight := .var 0
  contraction := fun _ => 0
  contractsLeft := by decide
  contractsRight := by decide
  separatedLeft := linearApplication_leftLinear

def repeatedApplicationSplit :
    repeatedApplicationSeparation.SplitContraction where
  representative := by
    change Ren 1 2
    exact fun _ => 0
  rightInverse := by
    intro authored
    change (0 : Fin 1) = authored
    exact (Fin.eq_zero authored).symm

/-- A concrete assignment that gives the two copies of the repeated
metavariable different terms. -/
def repeatedApplicationMismatchedSubstitution : Sub Unit 2 2 :=
  ![.var 0, .var 1]

/-- Negative control: merely matching the left-linear skeleton does not
supply the diagonal evidence required by the authored nonlinear rule. -/
theorem repeatedApplicationMismatched_not_coherent :
    ¬ repeatedApplicationSeparation.FibreCoherent
      repeatedApplicationMismatchedSubstitution := by
  intro coherent
  have termEquality := coherent (0 : Fin 2) (1 : Fin 2) rfl
  have indexEquality : (0 : Fin 2) = 1 := Tm.var.inj termEquality
  exact Fin.zero_ne_one indexEquality

/-- Negative control: duplication is carried by a genuinely non-injective
contraction; it has not disappeared behind the left-linear skeleton. -/
theorem repeatedApplicationSeparation_not_injective :
    ¬ Function.Injective repeatedApplicationSeparation.contraction := by
  intro injective
  have equality : (0 : Fin 2) = 1 := injective rfl
  exact Fin.zero_ne_one equality

/-- Every ordinary instance of the repeated authored rule is exactly an
instance of its occurrence-separated skeleton. -/
theorem repeatedApplicationSeparation_exactInstance
    (substitution : Sub Unit 1 ambient) :
    Presentation.subst
        (repeatedApplicationSeparation.expandSubstitution substitution)
        repeatedApplicationSeparation.skeletonLeft =
      Presentation.subst substitution repeatedApplication ∧
    Presentation.subst
        (repeatedApplicationSeparation.expandSubstitution substitution)
        repeatedApplicationSeparation.skeletonRight =
      Presentation.subst substitution (.var 0) :=
  ⟨repeatedApplicationSeparation.subst_skeletonLeft substitution,
    repeatedApplicationSeparation.subst_skeletonRight substitution⟩

end Canary

/-! ## Axiom audit -/

#print axioms not_leftLinear_of_repeatedAt
#print axioms Canary.linearApplication_leftLinear
#print axioms Canary.repeatedApplication_repeated
#print axioms Canary.repeatedApplication_not_leftLinear
#print axioms OccurrenceSeparatedRule.subst_skeletonLeft
#print axioms OccurrenceSeparatedRule.subst_skeletonRight
#print axioms OccurrenceSeparatedRule.expandSubstitution_coherent
#print axioms OccurrenceSeparatedRule.SplitContraction.contract_expand
#print axioms OccurrenceSeparatedRule.SplitContraction.expand_contract_of_coherent
#print axioms OccurrenceSeparatedRule.SplitContraction.coherent_iff_exists_expansion
#print axioms OccurrenceSeparatedRule.equalitySubstitutionCompatible
#print axioms OccurrenceSeparatedRule.conversionSubstitutionCompatible
#print axioms OccurrenceSeparatedRule.SplitContraction.occurrenceEvidenceToExpansion
#print axioms OccurrenceSeparatedRule.SplitContraction.subst_skeletonLeft_of_coherent
#print axioms OccurrenceSeparatedRule.SplitContraction.subst_skeletonRight_of_coherent
#print axioms OccurrenceSeparatedRule.SplitContraction.skeletonLeftEvidenceToAuthored
#print axioms OccurrenceSeparatedRule.SplitContraction.skeletonRightEvidenceToAuthored
#print axioms OccurrenceSeparatedRule.SplitContraction.skeletonLeft_conv_toAuthored
#print axioms OccurrenceSeparatedRule.SplitContraction.skeletonRight_conv_toAuthored
#print axioms OccurrenceSeparatedRule.SplitContraction.occurrenceInstance_conv_of_fibreEvidence
#print axioms OccurrenceSeparatedRule.coherentOccurrenceInstance_iff_authoredInstance
#print axioms Canary.linearApplicationSeparation_injective
#print axioms Canary.repeatedApplicationSeparation_not_injective
#print axioms Canary.repeatedApplicationSeparation_exactInstance
#print axioms Canary.repeatedApplicationMismatched_not_coherent

end AlgebraicSchema
end Mettapedia.Languages.MeTTa.PureKernel.Universe.Presentation
