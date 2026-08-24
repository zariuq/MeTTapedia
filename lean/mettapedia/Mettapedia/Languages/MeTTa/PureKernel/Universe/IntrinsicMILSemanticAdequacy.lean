import Mettapedia.Languages.MeTTa.PureKernel.Universe.IntrinsicMILHypothesis

/-!
# Semantic adequacy of intrinsic hypothesis programs

The native family `Hyp S P source target` and the proof-relevant relational
semantics meet here.  A `Program` is structural evidence that a tower term is
built from the native primitive and chain constructors for one typed
vocabulary quotation.  It has two independent projections:

* a tower typing derivation;
* a proof-relevant relation assembled from primitive meanings and relational
  composition.

The exact-image theorem characterizes precisely the terms produced by
quotation.  Reflection stops at existence: relational denotation need not
identify a proof program uniquely, as the collision counterexample shows.
-/

namespace Mettapedia.Languages.MeTTa.PureKernel.Universe
namespace IntrinsicMILSemanticAdequacy

open RelationalInternalLanguage
open Presentation

universe uSort uCarrier uPrimitive

/-! ## The structural semantic image -/

set_option linter.unusedVariables false in
/-- Structural evidence that a tower term is an intrinsic hypothesis program
for a particular typed vocabulary quotation. -/
inductive Program
    {vocabulary : MILSchemaElaboration.Semantic.Vocabulary.{uSort, uCarrier,
      uPrimitive}}
    {context : Tower.Ctx n}
    (quotation : IntrinsicMILHypothesis.TypedVocabularyQuotation vocabulary
      context) :
    {source target : vocabulary.SortCode} → Tower.Tm n →
      Type (max (max uSort uCarrier) uPrimitive) where
  | primitive {source target : vocabulary.SortCode}
      (symbol : vocabulary.Primitive source target) :
      Program quotation (source := source) (target := target)
        (IntrinsicMILHypothesis.primitiveApp quotation.sorts quotation.primitives
          (quotation.sortCode source) (quotation.sortCode target)
          (quotation.primitiveCode symbol))
  | chain {source middle target : vocabulary.SortCode}
      {earlierTerm laterTerm : Tower.Tm n}
      (earlier : Program quotation (source := source) (target := middle)
        earlierTerm)
      (later : Program quotation (source := middle) (target := target)
        laterTerm) :
      Program quotation (source := source) (target := target)
        (IntrinsicMILHypothesis.chainApp quotation.sorts quotation.primitives
          (quotation.sortCode source) (quotation.sortCode middle)
          (quotation.sortCode target) earlierTerm laterTerm)

namespace Program

/-- Recover the semantic hypothesis tree represented by structural program
evidence. -/
def toHypothesis
    {vocabulary : MILSchemaElaboration.Semantic.Vocabulary}
    {context : Tower.Ctx n}
    {quotation : IntrinsicMILHypothesis.TypedVocabularyQuotation vocabulary
      context}
    {source target : vocabulary.SortCode} {term : Tower.Tm n} :
    Program quotation (source := source) (target := target) term →
      MILSchemaElaboration.Semantic.Hypothesis vocabulary source target
  | .primitive symbol => .primitive symbol
  | .chain earlier later => .chain earlier.toHypothesis later.toHypothesis

/-- Interpret the structural program directly as a proof-relevant relation. -/
def denotation
    {vocabulary : MILSchemaElaboration.Semantic.Vocabulary}
    {context : Tower.Ctx n}
    {quotation : IntrinsicMILHypothesis.TypedVocabularyQuotation vocabulary
      context}
    {source target : vocabulary.SortCode} {term : Tower.Tm n} :
    Program quotation (source := source) (target := target) term →
      RelationalInternalLanguage.Semantic.Rel
        (vocabulary.Carrier source) (vocabulary.Carrier target)
  | .primitive symbol => vocabulary.meaning symbol
  | .chain earlier later =>
      RelationalInternalLanguage.Semantic.Rel.Chain
        earlier.denotation later.denotation

/-- Structural program evidence independently reconstructs a native tower
typing derivation at exactly the indexed endpoints. -/
theorem hasType
    {vocabulary : MILSchemaElaboration.Semantic.Vocabulary}
    {context : Tower.Ctx n}
    {quotation : IntrinsicMILHypothesis.TypedVocabularyQuotation vocabulary
      context}
    {source target : vocabulary.SortCode} {term : Tower.Tm n}
    (program : Program quotation (source := source) (target := target) term) :
    IntrinsicMILHypothesis.HasType context term
      (IntrinsicMILHypothesis.hypothesisApp quotation.sorts quotation.primitives
        (quotation.sortCode source) (quotation.sortCode target)) := by
  induction program with
  | primitive symbol =>
      exact IntrinsicMILHypothesis.primitiveApp_hasType quotation.sortsTyping
        quotation.primitivesTyping (quotation.sortCodeTyping _)
        (quotation.sortCodeTyping _) (quotation.primitiveCodeTyping symbol)
  | chain earlier later earlierTyping laterTyping =>
      exact IntrinsicMILHypothesis.chainApp_hasType quotation.sortsTyping
        quotation.primitivesTyping (quotation.sortCodeTyping _)
        (quotation.sortCodeTyping _) (quotation.sortCodeTyping _)
        earlierTyping laterTyping

/-- Quotation produces structural program evidence, not merely a raw term. -/
def ofHypothesis
    {vocabulary : MILSchemaElaboration.Semantic.Vocabulary}
    {context : Tower.Ctx n}
    (quotation : IntrinsicMILHypothesis.TypedVocabularyQuotation vocabulary
      context) :
    {source target : vocabulary.SortCode} →
      (hypothesis : MILSchemaElaboration.Semantic.Hypothesis vocabulary source
        target) →
      Program quotation (source := source) (target := target)
        (IntrinsicMILHypothesis.quoteHypothesis quotation hypothesis)
  | _, _, .primitive symbol => .primitive symbol
  | _, _, .chain earlier later =>
      .chain (ofHypothesis quotation earlier) (ofHypothesis quotation later)

@[simp] theorem toHypothesis_ofHypothesis
    {vocabulary : MILSchemaElaboration.Semantic.Vocabulary}
    {context : Tower.Ctx n}
    (quotation : IntrinsicMILHypothesis.TypedVocabularyQuotation vocabulary
      context)
    {source target : vocabulary.SortCode}
    (hypothesis : MILSchemaElaboration.Semantic.Hypothesis vocabulary source
      target) :
    (ofHypothesis quotation hypothesis).toHypothesis = hypothesis := by
  induction hypothesis with
  | primitive symbol => rfl
  | chain earlier later earlierHypothesis laterHypothesis =>
      simp only [ofHypothesis, toHypothesis, earlierHypothesis, laterHypothesis]

/-- Structural evidence reflects back into the exact quotation image. -/
theorem quote_toHypothesis
    {vocabulary : MILSchemaElaboration.Semantic.Vocabulary}
    {context : Tower.Ctx n}
    {quotation : IntrinsicMILHypothesis.TypedVocabularyQuotation vocabulary
      context}
    {source target : vocabulary.SortCode} {term : Tower.Tm n}
    (program : Program quotation (source := source) (target := target) term) :
    IntrinsicMILHypothesis.quoteHypothesis quotation program.toHypothesis =
      term := by
  induction program with
  | primitive symbol => rfl
  | chain earlier later earlierHypothesis laterHypothesis =>
      simp only [toHypothesis, IntrinsicMILHypothesis.quoteHypothesis_chain,
        earlierHypothesis, laterHypothesis]

/-- The direct structural semantics agrees with the independently defined
semantic-hypothesis interpretation. -/
theorem denotation_eq_toHypothesis
    {vocabulary : MILSchemaElaboration.Semantic.Vocabulary}
    {context : Tower.Ctx n}
    {quotation : IntrinsicMILHypothesis.TypedVocabularyQuotation vocabulary
      context}
    {source target : vocabulary.SortCode} {term : Tower.Tm n}
    (program : Program quotation (source := source) (target := target) term) :
    program.denotation = program.toHypothesis.denote := by
  induction program with
  | primitive symbol => rfl
  | chain earlier later earlierHypothesis laterHypothesis =>
      simp only [denotation, toHypothesis,
        MILSchemaElaboration.Semantic.Hypothesis.denote_chain,
        earlierHypothesis, laterHypothesis]

/-- The agreement preserves every inhabitant of every evidence fibre, not
only relational support or endpoint reachability. -/
def evidenceEquiv
    {vocabulary : MILSchemaElaboration.Semantic.Vocabulary}
    {context : Tower.Ctx n}
    {quotation : IntrinsicMILHypothesis.TypedVocabularyQuotation vocabulary
      context}
    {source target : vocabulary.SortCode} {term : Tower.Tm n}
    (program : Program quotation (source := source) (target := target) term)
    (input : vocabulary.Carrier source)
    (output : vocabulary.Carrier target) :
    program.denotation.evidence input output ≃
      program.toHypothesis.denote.evidence input output :=
  Equiv.cast (congrArg (fun relation => relation.evidence input output)
    program.denotation_eq_toHypothesis)

/-- Native chaining exposes the exact intermediate carrier value and both
premise derivations. -/
def chainEvidenceEquiv
    {vocabulary : MILSchemaElaboration.Semantic.Vocabulary}
    {context : Tower.Ctx n}
    {quotation : IntrinsicMILHypothesis.TypedVocabularyQuotation vocabulary
      context}
    {source middle target : vocabulary.SortCode}
    {earlierTerm laterTerm : Tower.Tm n}
    (earlier : Program quotation (source := source) (target := middle)
      earlierTerm)
    (later : Program quotation (source := middle) (target := target)
      laterTerm)
    (input : vocabulary.Carrier source)
    (output : vocabulary.Carrier target) :
    (Program.chain earlier later).denotation.evidence input output ≃
      (Sigma fun intermediate : vocabulary.Carrier middle =>
        earlier.denotation.evidence input intermediate ×
          later.denotation.evidence intermediate output) :=
  Equiv.refl _

end Program

/-! ## Representability as a downstream compilation license -/

/-- A vocabulary is directly compilable only when each primitive relation
has independently earned a representation as a function graph. -/
structure PrimitiveRepresentations
    (vocabulary : MILSchemaElaboration.Semantic.Vocabulary) where
  represent : ∀ {source target : vocabulary.SortCode}
      (symbol : vocabulary.Primitive source target),
    RelationalInternalLanguage.Semantic.Rel.Representation
      (vocabulary.meaning symbol)

/-- Represented primitives make every structurally typed hypothesis program
representable.  The semantic relation remains primary; this merely derives a
direct execution map for the represented fragment. -/
def Program.representation
    {vocabulary : MILSchemaElaboration.Semantic.Vocabulary}
    {context : Tower.Ctx n}
    {quotation : IntrinsicMILHypothesis.TypedVocabularyQuotation vocabulary
      context}
    (primitiveRepresentations : PrimitiveRepresentations vocabulary) :
    {source target : vocabulary.SortCode} → {term : Tower.Tm n} →
      (program : Program quotation (source := source) (target := target) term) →
      RelationalInternalLanguage.Semantic.Rel.Representation
        program.denotation
  | _, _, _, .primitive symbol => primitiveRepresentations.represent symbol
  | _, _, _, .chain earlier later =>
      RelationalInternalLanguage.Semantic.Rel.chainRepresentation
        (earlier.representation primitiveRepresentations)
        (later.representation primitiveRepresentations)

/-- The compiled map for a chain is definitionally ordinary function
composition, but only after both subprograms have earned representations. -/
@[simp] theorem Program.representation_chain_map
    {vocabulary : MILSchemaElaboration.Semantic.Vocabulary}
    {context : Tower.Ctx n}
    {quotation : IntrinsicMILHypothesis.TypedVocabularyQuotation vocabulary
      context}
    (primitiveRepresentations : PrimitiveRepresentations vocabulary)
    {source middle target : vocabulary.SortCode}
    {earlierTerm laterTerm : Tower.Tm n}
    (earlier : Program quotation (source := source) (target := middle)
      earlierTerm)
    (later : Program quotation (source := middle) (target := target)
      laterTerm) :
    ((Program.chain earlier later).representation
      primitiveRepresentations).map =
      (later.representation primitiveRepresentations).map ∘
        (earlier.representation primitiveRepresentations).map :=
  rfl

/-! ## Exact image and strongest true reflection -/

def InExactImage
    {vocabulary : MILSchemaElaboration.Semantic.Vocabulary}
    {context : Tower.Ctx n}
    (quotation : IntrinsicMILHypothesis.TypedVocabularyQuotation vocabulary
      context)
    {source target : vocabulary.SortCode} (term : Tower.Tm n) : Prop :=
  Nonempty (Program quotation (source := source) (target := target) term)

theorem quote_inExactImage
    {vocabulary : MILSchemaElaboration.Semantic.Vocabulary}
    {context : Tower.Ctx n}
    (quotation : IntrinsicMILHypothesis.TypedVocabularyQuotation vocabulary
      context)
    {source target : vocabulary.SortCode}
    (hypothesis : MILSchemaElaboration.Semantic.Hypothesis vocabulary source
      target) :
    InExactImage quotation (source := source) (target := target)
      (IntrinsicMILHypothesis.quoteHypothesis quotation hypothesis) :=
  ⟨Program.ofHypothesis quotation hypothesis⟩

/-- A term is in the structural image exactly when it is the quotation of a
typed semantic hypothesis.  No uniqueness is claimed. -/
theorem inExactImage_iff
    {vocabulary : MILSchemaElaboration.Semantic.Vocabulary}
    {context : Tower.Ctx n}
    (quotation : IntrinsicMILHypothesis.TypedVocabularyQuotation vocabulary
      context)
    {source target : vocabulary.SortCode} (term : Tower.Tm n) :
    InExactImage quotation (source := source) (target := target) term ↔
      ∃ hypothesis : MILSchemaElaboration.Semantic.Hypothesis vocabulary source
          target,
        IntrinsicMILHypothesis.quoteHypothesis quotation hypothesis = term := by
  constructor
  · rintro ⟨program⟩
    exact ⟨program.toHypothesis, program.quote_toHypothesis⟩
  · rintro ⟨hypothesis, rfl⟩
    exact quote_inExactImage quotation hypothesis

/-- Structural exact-image evidence carries an intrinsic typing derivation. -/
theorem exactImage_hasType
    {vocabulary : MILSchemaElaboration.Semantic.Vocabulary}
    {context : Tower.Ctx n}
    (quotation : IntrinsicMILHypothesis.TypedVocabularyQuotation vocabulary
      context)
    {source target : vocabulary.SortCode} {term : Tower.Tm n}
    (program : Program quotation (source := source) (target := target) term) :
    IntrinsicMILHypothesis.HasType context term
      (IntrinsicMILHypothesis.hypothesisApp quotation.sorts quotation.primitives
        (quotation.sortCode source) (quotation.sortCode target)) := by
  exact program.hasType

/-- Open variables and other ambient inhabitants are outside the constructor
image.  Typing and being an authored/quoted hypothesis are intentionally
different properties. -/
theorem variable_not_inExactImage
    {vocabulary : MILSchemaElaboration.Semantic.Vocabulary}
    {context : Tower.Ctx n}
    (quotation : IntrinsicMILHypothesis.TypedVocabularyQuotation vocabulary
      context)
    {source target : vocabulary.SortCode} (index : Fin n) :
    ¬ InExactImage quotation (source := source) (target := target) (.var index) := by
  rintro ⟨program⟩
  cases program

/-! ## Denotational non-reflection canary -/

namespace CollisionCanary

inductive Primitive : Unit → Unit → Type where
  | left : Primitive () ()
  | right : Primitive () ()

def meaning : {source target : Unit} → Primitive source target →
    RelationalInternalLanguage.Semantic.Rel Unit Unit
  | _, _, .left => RelationalInternalLanguage.Semantic.Rel.graph id
  | _, _, .right => RelationalInternalLanguage.Semantic.Rel.graph id

def vocabulary : MILSchemaElaboration.Semantic.Vocabulary where
  SortCode := Unit
  Carrier := fun _ => Unit
  Primitive := Primitive
  meaning := meaning

def left : MILSchemaElaboration.Semantic.Hypothesis vocabulary () () :=
  .primitive .left
def right : MILSchemaElaboration.Semantic.Hypothesis vocabulary () () :=
  .primitive .right

def isRight :
    MILSchemaElaboration.Semantic.Hypothesis vocabulary () () → Bool
  | .primitive .right => true
  | _ => false

theorem programs_distinct : left ≠ right := by
  intro equality
  have tagged := congrArg isRight equality
  simp [left, right, isRight] at tagged

theorem denotations_equal : left.denote = right.denote :=
  rfl

/-- Relational meaning is intentionally not a complete invariant of authored
proof programs.  Consequently the exact-image theorem above reflects an
inhabitant, not a unique syntax tree. -/
theorem no_global_denotation_reflection :
    ¬ ∀ (earlier later : MILSchemaElaboration.Semantic.Hypothesis vocabulary
        () ()),
      earlier.denote = later.denote → earlier = later := by
  intro reflection
  exact programs_distinct (reflection left right denotations_equal)

end CollisionCanary

/-! ## Negative control for compilation authority -/

namespace NondeterministicCanary

inductive ObjectSort where
  | input
  | output
deriving DecidableEq

def Carrier : ObjectSort → Type
  | .input => Unit
  | .output => Bool

inductive Primitive : ObjectSort → ObjectSort → Type where
  | choose : Primitive .input .output

def meaning : {source target : ObjectSort} → Primitive source target →
    RelationalInternalLanguage.Semantic.Rel (Carrier source) (Carrier target)
  | _, _, .choose => RelationalInternalLanguage.Semantic.Canary.choice

def vocabulary : MILSchemaElaboration.Semantic.Vocabulary where
  SortCode := ObjectSort
  Carrier := Carrier
  Primitive := Primitive
  meaning := meaning

theorem primitive_executes_both :
    Nonempty ((vocabulary.meaning Primitive.choose).evidence () false) ∧
      Nonempty ((vocabulary.meaning Primitive.choose).evidence () true) :=
  RelationalInternalLanguage.Semantic.Canary.choice_executes_both

/-- Raw nondeterministic execution survives, but no direct-map license can be
constructed for the vocabulary. -/
theorem no_primitiveRepresentations :
    ¬ Nonempty (PrimitiveRepresentations vocabulary) := by
  rintro ⟨representations⟩
  exact RelationalInternalLanguage.Semantic.Canary.choice_not_representable
    ⟨representations.represent Primitive.choose⟩

end NondeterministicCanary

#print axioms Program.hasType
#print axioms Program.quote_toHypothesis
#print axioms Program.denotation_eq_toHypothesis
#print axioms Program.evidenceEquiv
#print axioms Program.chainEvidenceEquiv
#print axioms Program.representation
#print axioms Program.representation_chain_map
#print axioms inExactImage_iff
#print axioms variable_not_inExactImage
#print axioms CollisionCanary.no_global_denotation_reflection
#print axioms NondeterministicCanary.no_primitiveRepresentations

end IntrinsicMILSemanticAdequacy
end Mettapedia.Languages.MeTTa.PureKernel.Universe
