import Mettapedia.GSLT.Parsing.PlainBnfSemanticAdmission
import Mettapedia.GSLT.Parsing.PlainBnfLexicalInhabitation
import Mathlib.Order.FixedPoints
import Mathlib.Tactic

/-!
# Independent graph semantics for admitted plain BNF

This module states reachability, productivity, and nullability directly over
the structured plain-BNF document.  The meanings are least fixed points of
monotone operators.  They neither execute nor inspect the authored graph
analysis GSLT, so they can serve as its independent specification.

Inhabited lexical references are productive leaves but are not nullable. Grammar
references are graph edges.  Literal strings are always productive and are
nullable exactly when empty.  Source order belongs to a later enumeration
theorem; these sets state the order-independent mathematical result.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.PlainBnfGraphSemantics

open Mettapedia.GSLT.Parsing.PlainBnfStructuredDenotation
open Mettapedia.GSLT.Parsing.PlainBnfSemanticAdmission

/-! ## Reference classification -/

def LexicalName (authority : GrammarAuthority) (name : String) : Prop :=
  name ∈ authority.lexicalDeclarations.map (·.referenceName)

/-- Productivity needs an accepted scalar, not just a declaration name. -/
def LexicalProductive (authority : GrammarAuthority) (name : String) : Prop :=
  ∃ declaration ∈ authority.lexicalDeclarations,
    declaration.referenceName = name ∧
      PlainBnfLexicalInhabitation.InhabitedClass
        (denoteLexicalClass declaration).kind

/-- Scalar admission discharges the gap checker's preconditions. This is a
semantic checker theorem, not yet a realization theorem for authored rules. -/
theorem lexical_inhabitation_check_exact (declaration : LexicalDeclaration)
    (valid : MatcherWellFormed declaration.matcher) :
    PlainBnfLexicalInhabitation.checkInhabitedByGaps
        (denoteLexicalClass declaration).kind = true ↔
      PlainBnfLexicalInhabitation.InhabitedClass
        (denoteLexicalClass declaration).kind := by
  cases declaration with
  | mk name className matcher label origin =>
    cases matcher with
    | points scalars =>
      exact PlainBnfLexicalInhabitation.checkInhabitedByGaps_iff (.points scalars)
        (PlainBnfLexicalInhabitation.inventoryValid_of_scalarListWellFormed scalars valid)
        (PlainBnfLexicalInhabitation.sorted_and_valid_of_scalarListWellFormed scalars valid).1
    | except excluded =>
      rcases valid with empty | wellFormed
      · subst excluded
        exact PlainBnfLexicalInhabitation.checkInhabitedByGaps_iff (.except [])
          PlainBnfLexicalInhabitation.empty_inventory_valid (by simp)
      · exact PlainBnfLexicalInhabitation.checkInhabitedByGaps_iff (.except excluded)
          (PlainBnfLexicalInhabitation.inventoryValid_of_scalarListWellFormed excluded wellFormed)
          (PlainBnfLexicalInhabitation.sorted_and_valid_of_scalarListWellFormed excluded wellFormed).1

def GrammarEdge (document : Document) (authority : GrammarAuthority)
    (source target : String) : Prop :=
  ∃ occurrence ∈ referenceOccurrences document,
    occurrence.owner = source /\ occurrence.name = target /\
      ¬ LexicalName authority target

instance (authority : GrammarAuthority) (name : String) :
    Decidable (LexicalName authority name) := by
  unfold LexicalName
  infer_instance

instance (document : Document) (authority : GrammarAuthority)
    (source target : String) :
    Decidable (GrammarEdge document authority source target) := by
  unfold GrammarEdge
  infer_instance

/-! ## Reachability -/

def reachableStep (document : Document) (authority : GrammarAuthority)
    (current : Set String) : Set String :=
  fun name =>
    name = authority.startName \/ name ∈ current \/
      ∃ source, source ∈ current /\
        GrammarEdge document authority source name

theorem reachableStep_monotone (document : Document)
    (authority : GrammarAuthority) :
    Monotone (reachableStep document authority) := by
  intro left right included name membership
  rcases membership with start | old | ⟨source, sourceIn, edge⟩
  · exact Or.inl start
  · exact Or.inr (Or.inl (included old))
  · exact Or.inr (Or.inr ⟨source, included sourceIn, edge⟩)

def reachableOperator (document : Document) (authority : GrammarAuthority) :
    Set String →o Set String where
  toFun := reachableStep document authority
  monotone' := reachableStep_monotone document authority

def Reachable (document : Document) (authority : GrammarAuthority) :
    Set String :=
  (reachableOperator document authority).lfp

theorem reachable_fixed (document : Document)
    (authority : GrammarAuthority) :
    reachableStep document authority (Reachable document authority) =
      Reachable document authority :=
  (reachableOperator document authority).map_lfp

theorem start_reachable (document : Document) (authority : GrammarAuthority) :
    authority.startName ∈ Reachable document authority := by
  rw [← reachable_fixed]
  exact Or.inl rfl

theorem reachable_of_edge (document : Document)
    (authority : GrammarAuthority) {source target : String}
    (sourceReachable : source ∈ Reachable document authority)
    (edge : GrammarEdge document authority source target) :
    target ∈ Reachable document authority := by
  rw [← reachable_fixed]
  exact Or.inr (Or.inr ⟨source, sourceReachable, edge⟩)

/-- Universal property: `Reachable` is contained in every set that contains
the start symbol and is closed under grammar-reference edges. -/
theorem reachable_le_of_closed (document : Document)
    (authority : GrammarAuthority) (candidate : Set String)
    (start : authority.startName ∈ candidate)
    (closed : ∀ source target, source ∈ candidate ->
      GrammarEdge document authority source target -> target ∈ candidate) :
    Reachable document authority ⊆ candidate := by
  apply (reachableOperator document authority).lfp_le
  intro name membership
  rcases membership with atStart | old | ⟨source, sourceIn, edge⟩
  · exact atStart ▸ start
  · exact old
  · exact closed source name sourceIn edge

/-! ## Productivity and nullability predicates -/

def ElementProductive (current : Set String)
    (authority : GrammarAuthority) : Element -> Prop
  | .literal _ _ => True
  | .reference name _ => name ∈ current \/ LexicalProductive authority name

def AlternativeProductive (current : Set String)
    (authority : GrammarAuthority) (alternative : Alternative) : Prop :=
  ∀ element ∈ alternative.elements,
    ElementProductive current authority element

def ExpressionProductive (current : Set String)
    (authority : GrammarAuthority) (expression : Expression) : Prop :=
  ∃ alternative ∈ expression.alternatives,
    AlternativeProductive current authority alternative

def ElementNullable (current : Set String) : Element -> Prop
  | .literal text _ => text = ""
  | .reference name _ => name ∈ current

def AlternativeNullable (current : Set String)
    (alternative : Alternative) : Prop :=
  ∀ element ∈ alternative.elements, ElementNullable current element

def ExpressionNullable (current : Set String)
    (expression : Expression) : Prop :=
  ∃ alternative ∈ expression.alternatives,
    AlternativeNullable current alternative

theorem elementProductive_mono {left right : Set String}
    (included : left ⊆ right) (authority : GrammarAuthority)
    {element : Element} :
    ElementProductive left authority element ->
      ElementProductive right authority element := by
  cases element with
  | literal text span => simp [ElementProductive]
  | reference name span =>
      intro productive
      rcases productive with grammar | lexical
      · exact Or.inl (included grammar)
      · exact Or.inr lexical

theorem alternativeProductive_mono {left right : Set String}
    (included : left ⊆ right) (authority : GrammarAuthority)
    {alternative : Alternative} :
    AlternativeProductive left authority alternative ->
      AlternativeProductive right authority alternative := by
  unfold AlternativeProductive
  intro productive element membership
  exact elementProductive_mono included authority
    (productive element membership)

theorem expressionProductive_mono {left right : Set String}
    (included : left ⊆ right) (authority : GrammarAuthority)
    {expression : Expression} :
    ExpressionProductive left authority expression ->
      ExpressionProductive right authority expression := by
  rintro ⟨alternative, membership, productive⟩
  exact ⟨alternative, membership,
    alternativeProductive_mono included authority productive⟩

theorem elementNullable_mono {left right : Set String}
    (included : left ⊆ right) {element : Element} :
    ElementNullable left element -> ElementNullable right element := by
  cases element with
  | literal text span => exact id
  | reference name span =>
      simp only [ElementNullable]
      intro membership
      exact included membership

theorem alternativeNullable_mono {left right : Set String}
    (included : left ⊆ right) {alternative : Alternative} :
    AlternativeNullable left alternative ->
      AlternativeNullable right alternative := by
  unfold AlternativeNullable
  intro nullable element membership
  exact elementNullable_mono included (nullable element membership)

theorem expressionNullable_mono {left right : Set String}
    (included : left ⊆ right) {expression : Expression} :
    ExpressionNullable left expression -> ExpressionNullable right expression := by
  rintro ⟨alternative, membership, nullable⟩
  exact ⟨alternative, membership,
    alternativeNullable_mono included nullable⟩

/-! ## Least productive and nullable name sets -/

def productiveStep (document : Document) (authority : GrammarAuthority)
    (current : Set String) : Set String :=
  fun name => name ∈ current \/
    ∃ occurrence ∈ ruleOccurrences document,
      occurrence.name = name /\
        ExpressionProductive current authority occurrence.expression

def nullableStep (document : Document) (current : Set String) : Set String :=
  fun name => name ∈ current \/
    ∃ occurrence ∈ ruleOccurrences document,
      occurrence.name = name /\ ExpressionNullable current occurrence.expression

theorem productiveStep_monotone (document : Document)
    (authority : GrammarAuthority) :
    Monotone (productiveStep document authority) := by
  intro left right included name membership
  rcases membership with old | ⟨occurrence, inDocument, named, productive⟩
  · exact Or.inl (included old)
  · exact Or.inr ⟨occurrence, inDocument, named,
      expressionProductive_mono included authority productive⟩

theorem nullableStep_monotone (document : Document) :
    Monotone (nullableStep document) := by
  intro left right included name membership
  rcases membership with old | ⟨occurrence, inDocument, named, nullable⟩
  · exact Or.inl (included old)
  · exact Or.inr ⟨occurrence, inDocument, named,
      expressionNullable_mono included nullable⟩

def productiveOperator (document : Document) (authority : GrammarAuthority) :
    Set String →o Set String where
  toFun := productiveStep document authority
  monotone' := productiveStep_monotone document authority

def nullableOperator (document : Document) : Set String →o Set String where
  toFun := nullableStep document
  monotone' := nullableStep_monotone document

def Productive (document : Document) (authority : GrammarAuthority) :
    Set String :=
  (productiveOperator document authority).lfp

def Nullable (document : Document) : Set String :=
  (nullableOperator document).lfp

theorem productive_fixed (document : Document)
    (authority : GrammarAuthority) :
    productiveStep document authority (Productive document authority) =
      Productive document authority :=
  (productiveOperator document authority).map_lfp

theorem nullable_fixed (document : Document) :
    nullableStep document (Nullable document) = Nullable document :=
  (nullableOperator document).map_lfp

theorem productive_of_expression (document : Document)
    (authority : GrammarAuthority) (occurrence : RuleOccurrence)
    (membership : occurrence ∈ ruleOccurrences document)
    (productive : ExpressionProductive (Productive document authority)
      authority occurrence.expression) :
    occurrence.name ∈ Productive document authority := by
  rw [← productive_fixed]
  exact Or.inr ⟨occurrence, membership, rfl, productive⟩

theorem nullable_of_expression (document : Document)
    (occurrence : RuleOccurrence)
    (membership : occurrence ∈ ruleOccurrences document)
    (nullable : ExpressionNullable (Nullable document)
      occurrence.expression) :
    occurrence.name ∈ Nullable document := by
  rw [← nullable_fixed]
  exact Or.inr ⟨occurrence, membership, rfl, nullable⟩

/-- Universal property of productivity: any set closed under productive rule
expressions contains the least productive set. -/
theorem productive_le_of_closed (document : Document)
    (authority : GrammarAuthority) (candidate : Set String)
    (closed : ∀ occurrence ∈ ruleOccurrences document,
      ExpressionProductive candidate authority occurrence.expression ->
        occurrence.name ∈ candidate) :
    Productive document authority ⊆ candidate := by
  apply (productiveOperator document authority).lfp_le
  intro name membership
  rcases membership with old | ⟨occurrence, inDocument, named, productive⟩
  · exact old
  · exact named ▸ closed occurrence inDocument productive

/-- Universal property of nullability: any set closed under nullable rule
expressions contains the least nullable set. -/
theorem nullable_le_of_closed (document : Document) (candidate : Set String)
    (closed : ∀ occurrence ∈ ruleOccurrences document,
      ExpressionNullable candidate occurrence.expression ->
        occurrence.name ∈ candidate) :
    Nullable document ⊆ candidate := by
  apply (nullableOperator document).lfp_le
  intro name membership
  rcases membership with old | ⟨occurrence, inDocument, named, nullable⟩
  · exact old
  · exact named ▸ closed occurrence inDocument nullable

/-! ## Semantic discriminators -/

theorem literal_is_productive (current : Set String)
    (authority : GrammarAuthority) (text : String) (span : SourceSpan) :
    ElementProductive current authority (.literal text span) :=
  trivial

theorem nonempty_literal_is_not_nullable (current : Set String)
    {text : String} (nonempty : text ≠ "") (span : SourceSpan) :
    ¬ ElementNullable current (.literal text span) := by
  simpa [ElementNullable] using nonempty

theorem lexical_reference_is_productive (current : Set String)
    (authority : GrammarAuthority) {name : String}
    (lexical : LexicalProductive authority name) (span : SourceSpan) :
    ElementProductive current authority (.reference name span) :=
  Or.inr lexical

theorem lexical_membership_does_not_make_nullable
    (current : Set String) (authority : GrammarAuthority) {name : String}
    (_lexical : LexicalName authority name) (absent : name ∉ current)
    (span : SourceSpan) :
    ¬ ElementNullable current (.reference name span) := by
  simpa [ElementNullable] using absent

private def exampleSpan : SourceSpan := { start := 0, stop := 0 }

private def exclusionDeclaration (excluded : List Nat) : LexicalDeclaration :=
  { referenceName := "scalar", className := "ScalarClass"
    matcher := .except excluded, ruleLabel := "scalar-rule"
    origin := { authority := "lexical-test", occurrence := 0 } }

private def exclusionAuthority (excluded : List Nat) : GrammarAuthority :=
  { startName := "s", lexicalDeclarations := [exclusionDeclaration excluded] }

theorem empty_exclusion_reference_is_productive :
    ElementProductive ∅ (exclusionAuthority [])
      (.reference "scalar" exampleSpan) := by
  apply Or.inr
  refine ⟨exclusionDeclaration [], by simp [exclusionAuthority], rfl, ?_⟩
  exact PlainBnfLexicalInhabitation.empty_exclusion_is_inhabited

private theorem exclusion_is_declared_but_unproductive (excluded : List Nat)
    (wellFormed : PlainBnfLexicalScalarSemantics.ScalarListWellFormed
      (excluded.map Int.ofNat))
    (uninhabited : ¬ PlainBnfLexicalInhabitation.InhabitedClass (.except excluded)) :
    MatcherWellFormed (.except excluded) ∧
      LexicalName (exclusionAuthority excluded) "scalar" ∧
      ¬ ElementProductive ∅ (exclusionAuthority excluded)
        (.reference "scalar" exampleSpan) := by
  refine ⟨Or.inr wellFormed,
    by simp [LexicalName, exclusionAuthority, exclusionDeclaration], ?_⟩
  intro productive
  rcases productive with impossible | ⟨declaration, membership, _, inhabited⟩
  · exact impossible
  · simp only [exclusionAuthority, List.mem_singleton] at membership
    subst declaration
    exact uninhabited inhabited

/-- A valid declaration can denote an empty class. Its name must not be
used as a productive base case for the grammar fixed point. -/
theorem declared_lexical_reference_can_be_unproductive :
    ∃ excluded : List Nat,
    MatcherWellFormed (.except excluded) ∧
      LexicalName (exclusionAuthority excluded) "scalar" ∧
      ¬ ElementProductive ∅ (exclusionAuthority excluded)
        (.reference "scalar" exampleSpan) := by
  obtain ⟨excluded, wellFormed, uninhabited⟩ :=
    PlainBnfLexicalInhabitation.well_formed_exclusion_can_be_uninhabited
  exact ⟨excluded, exclusion_is_declared_but_unproductive excluded wellFormed uninhabited⟩

private def emptyAlternative : Alternative :=
  { elements := [], span := exampleSpan }

private def epsilonExpression : Expression :=
  { alternatives := [emptyAlternative], span := exampleSpan }

private def epsilonDocument : Document :=
  { entries := [.rule "s" epsilonExpression exampleSpan]
    span := exampleSpan }

private def emptyAuthority : GrammarAuthority :=
  { startName := "s", lexicalDeclarations := [] }

private def epsilonOccurrence : RuleOccurrence :=
  { entryIndex := 0
    name := "s"
    expression := epsilonExpression
    span := exampleSpan }

/-- Positive control: an explicit empty alternative belongs to both least
fixed points. -/
theorem epsilon_rule_is_productive_and_nullable :
    "s" ∈ Productive epsilonDocument emptyAuthority /\
      "s" ∈ Nullable epsilonDocument := by
  constructor
  · apply productive_of_expression epsilonDocument emptyAuthority
      epsilonOccurrence
    · simp [ruleOccurrences, ruleOccurrencesFrom, epsilonDocument,
        epsilonOccurrence]
    · refine ⟨emptyAlternative, by decide +kernel, ?_⟩
      unfold AlternativeProductive
      intro element membership
      change element ∈ [] at membership
      exact False.elim (List.not_mem_nil membership)
  · apply nullable_of_expression epsilonDocument epsilonOccurrence
    · simp [ruleOccurrences, ruleOccurrencesFrom, epsilonDocument,
        epsilonOccurrence]
    · refine ⟨emptyAlternative, by decide +kernel, ?_⟩
      unfold AlternativeNullable
      intro element membership
      change element ∈ [] at membership
      exact False.elim (List.not_mem_nil membership)

private def selfReferenceAlternative : Alternative :=
  { elements := [.reference "s" exampleSpan], span := exampleSpan }

private def selfReferenceExpression : Expression :=
  { alternatives := [selfReferenceAlternative], span := exampleSpan }

private def ungroundedCycleDocument : Document :=
  { entries := [.rule "s" selfReferenceExpression exampleSpan]
    span := exampleSpan }

/-- Negative control: a bare self-cycle has no productive or nullable base
case, so least-fixed-point semantics does not admit it by circular reasoning. -/
theorem ungrounded_cycle_is_neither_productive_nor_nullable :
    "s" ∉ Productive ungroundedCycleDocument emptyAuthority /\
      "s" ∉ Nullable ungroundedCycleDocument := by
  have productiveEmpty :
      Productive ungroundedCycleDocument emptyAuthority ⊆
        (∅ : Set String) := by
    apply productive_le_of_closed
    intro occurrence membership productive
    simp [ungroundedCycleDocument, ruleOccurrences, ruleOccurrencesFrom] at membership
    subst occurrence
    simp [ExpressionProductive, selfReferenceExpression,
      AlternativeProductive, selfReferenceAlternative,
      ElementProductive, LexicalProductive, emptyAuthority] at productive
  have nullableEmpty :
      Nullable ungroundedCycleDocument ⊆ (∅ : Set String) := by
    apply nullable_le_of_closed
    intro occurrence membership nullable
    simp [ungroundedCycleDocument, ruleOccurrences, ruleOccurrencesFrom] at membership
    subst occurrence
    simp [ExpressionNullable, selfReferenceExpression,
      AlternativeNullable, selfReferenceAlternative,
      ElementNullable] at nullable
  constructor
  · intro membership
    exact (productiveEmpty membership)
  · intro membership
    exact (nullableEmpty membership)

#print axioms reachable_fixed
#print axioms start_reachable
#print axioms reachable_of_edge
#print axioms reachable_le_of_closed
#print axioms productive_fixed
#print axioms nullable_fixed
#print axioms productive_of_expression
#print axioms nullable_of_expression
#print axioms productive_le_of_closed
#print axioms nullable_le_of_closed
#print axioms nonempty_literal_is_not_nullable
#print axioms lexical_membership_does_not_make_nullable
#print axioms epsilon_rule_is_productive_and_nullable
#print axioms ungrounded_cycle_is_neither_productive_nor_nullable
#print axioms empty_exclusion_reference_is_productive
#print axioms declared_lexical_reference_can_be_unproductive
#print axioms lexical_inhabitation_check_exact

end Mettapedia.GSLT.Parsing.PlainBnfGraphSemantics
