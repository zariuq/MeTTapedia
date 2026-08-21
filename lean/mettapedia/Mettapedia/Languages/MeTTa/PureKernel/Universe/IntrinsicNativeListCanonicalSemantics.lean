import Mettapedia.Languages.MeTTa.PureKernel.Universe.IntrinsicNativeListRelator

/-!
# Canonical semantics for intrinsic native Lists

The polynomial List and its proof-relevant relator give the reusable
mathematical semantics.  The intrinsic declarations give raw Prime syntax and
typing rules.  This module proves their exact meeting point on the canonical
constructor fragment, without postulating a model of arbitrary raw syntax.

The construction deliberately reuses Lean's ordinary `List` spine and the
existing `ListExample.ListRel`; it introduces no competing List or relator.
A canonical element is an actual raw Prime term paired with a typing
derivation.  A canonical relation witness is likewise an actual evidence term
paired with its typing derivation.  Folding these spines through the intrinsic
constructors produces raw List and `mapRel` terms, and the resulting typing
derivations are proved recursively.

The same spines are exactly equivalent to the polynomial semantic List and
its proof-relevant relational lifting.  This is fragment adequacy: it covers
all finite constructor spines and retains every head witness.  It is not a
claim that every well-typed raw term is canonical, nor a semantic-CwF
interpretation or initiality theorem for the whole Prime calculus.
-/

namespace Mettapedia.Languages.MeTTa.PureKernel.Universe
namespace NativeIndexedFamilies
namespace IntrinsicCanonicalSemantics

open Presentation
open Mettapedia.TypeTheory.IndexedPolynomial

/-! ## Typed raw fibres -/

/-- An actual raw Prime term in one fixed typing fibre. -/
structure TypedTerm {n : Nat} (context : Tower.Ctx n)
    (type : Tower.Tm n) where
  term : Tower.Tm n
  typing : Presentation.HasType IntrinsicRelator.rules context term type

namespace TypedTerm

@[ext]
theorem ext {n : Nat} {context : Tower.Ctx n} {type : Tower.Tm n}
    {first second : TypedTerm context type}
    (terms : first.term = second.term) : first = second := by
  cases first
  cases second
  cases terms
  rfl

end TypedTerm

/-- Canonical intrinsic Lists are finite spines of genuinely typed raw
elements.  The ordinary spine is reused rather than redeclared. -/
abbrev CanonicalList {n : Nat} (context : Tower.Ctx n)
    (element : Tower.Tm n) :=
  List (TypedTerm context element)

/-- Fold a canonical typed spine into the actual intrinsic List
constructors. -/
def encodeList {n : Nat} {context : Tower.Ctx n}
    (element : Tower.Tm n) : CanonicalList context element → Tower.Tm n
  | [] => Intrinsic.nilApp element
  | head :: tail =>
      Intrinsic.consApp element head.term (encodeList element tail)

@[simp] theorem encodeList_nil {n : Nat} {context : Tower.Ctx n}
    (element : Tower.Tm n) :
    encodeList (context := context) element [] = Intrinsic.nilApp element :=
  rfl

@[simp] theorem encodeList_cons {n : Nat} {context : Tower.Ctx n}
    (element : Tower.Tm n) (head : TypedTerm context element)
    (tail : CanonicalList context element) :
    encodeList element (head :: tail) =
      Intrinsic.consApp element head.term (encodeList element tail) :=
  rfl

private def applicationFunction {n : Nat} : Tower.Tm n → Tower.Tm n
  | .app function _argument => function
  | other => other

private def applicationArgument {n : Nat} : Tower.Tm n → Option (Tower.Tm n)
  | .app _function argument => some argument
  | _ => none

/-- Raw constructor encoding loses no canonical List-spine information. -/
theorem encodeList_injective {n : Nat} {context : Tower.Ctx n}
    (element : Tower.Tm n) :
    Function.Injective (encodeList (context := context) element) := by
  intro first
  induction first with
  | nil =>
      intro second equality
      cases second with
      | nil => rfl
      | cons head tail =>
          have spineEquality := congrArg
            IntrinsicRelator.applicationSpineLength equality
          simp [encodeList, Intrinsic.nilApp, Intrinsic.consApp,
            IntrinsicRelator.applicationSpineLength] at spineEquality
  | cons firstHead firstTail hypothesis =>
      intro second equality
      cases second with
      | nil =>
          have spineEquality := congrArg
            IntrinsicRelator.applicationSpineLength equality
          simp [encodeList, Intrinsic.nilApp, Intrinsic.consApp,
            IntrinsicRelator.applicationSpineLength] at spineEquality
      | cons secondHead secondTail =>
          have tailTerms := congrArg applicationArgument equality
          have tailEquality :
              encodeList element firstTail = encodeList element secondTail := by
            simpa [encodeList, Intrinsic.consApp, applicationArgument] using
              tailTerms
          have functionTerms := congrArg applicationFunction equality
          have headTerms := congrArg applicationArgument functionTerms
          have headEquality : firstHead.term = secondHead.term := by
            simpa [encodeList, Intrinsic.consApp, applicationFunction,
              applicationArgument] using headTerms
          have headsEqual : firstHead = secondHead :=
            TypedTerm.ext headEquality
          have tailsEqual : firstTail = secondTail := hypothesis tailEquality
          cases headsEqual
          cases tailsEqual
          rfl

/-- Canonical List encoding is intrinsically well typed. -/
theorem encodeList_hasType {n : Nat} {context : Tower.Ctx n}
    {element : Tower.Tm n}
    (elementTyping : Presentation.HasType IntrinsicRelator.rules context
      element (sortTm Intrinsic.elementLevel)) :
    ∀ list : CanonicalList context element,
      Presentation.HasType IntrinsicRelator.rules context
        (encodeList element list) (Intrinsic.listApp element)
  | [] => IntrinsicRelator.nilApp_hasType elementTyping
  | head :: tail =>
      IntrinsicRelator.consApp_hasType elementTyping head.typing
        (encodeList_hasType elementTyping tail)

/-! ## Exact polynomial List interpretation -/

/-- Interpret the canonical spine in the reusable polynomial List model. -/
def interpretList {n : Nat} {context : Tower.Ctx n}
    {element : Tower.Tm n} :
    CanonicalList context element → Semantic.List (TypedTerm context element) :=
  ListExample.ofList

@[simp] theorem interpretList_nil {n : Nat} {context : Tower.Ctx n}
    {element : Tower.Tm n} :
    interpretList ([] : CanonicalList context element) = Semantic.nil :=
  rfl

@[simp] theorem interpretList_cons {n : Nat} {context : Tower.Ctx n}
    {element : Tower.Tm n} (head : TypedTerm context element)
    (tail : CanonicalList context element) :
    interpretList (head :: tail) =
      Semantic.cons head (interpretList tail) :=
  rfl

/-- Canonical typed spines and the polynomial List carry exactly the same
data. -/
noncomputable def canonicalListEquiv {n : Nat} (context : Tower.Ctx n)
    (element : Tower.Tm n) :
    CanonicalList context element ≃ Semantic.List (TypedTerm context element) :=
  (Semantic.listRepresentation (TypedTerm context element)).symm

@[simp] theorem canonicalListEquiv_apply {n : Nat}
    (context : Tower.Ctx n) (element : Tower.Tm n)
    (list : CanonicalList context element) :
    canonicalListEquiv context element list = interpretList list := by
  rfl

/-! ## Typed relation-evidence fibres -/

/-- An actual raw evidence term inhabiting the relation at two typed raw
endpoints. -/
structure TypedRelationEvidence {n : Nat} {context : Tower.Ctx n}
    {source target : Tower.Tm n} (relation : Tower.Tm n)
    (sourceTerm : TypedTerm context source)
    (targetTerm : TypedTerm context target) where
  term : Tower.Tm n
  typing : Presentation.HasType IntrinsicRelator.rules context term
    (.app (.app relation sourceTerm.term) targetTerm.term)

namespace TypedRelationEvidence

@[ext]
theorem ext {n : Nat} {context : Tower.Ctx n}
    {source target relation : Tower.Tm n}
    {sourceTerm : TypedTerm context source}
    {targetTerm : TypedTerm context target}
    {first second : TypedRelationEvidence relation sourceTerm targetTerm}
    (terms : first.term = second.term) : first = second := by
  cases first
  cases second
  cases terms
  rfl

end TypedRelationEvidence

/-- The proof-relevant semantic relation whose inhabitants are precisely
typed raw evidence terms. -/
def typedRelation {n : Nat} {context : Tower.Ctx n}
    {source target : Tower.Tm n} (relation : Tower.Tm n) :
    Semantic.PrimeRel (TypedTerm context source) (TypedTerm context target)
    where
  evidence := TypedRelationEvidence relation

/-- Canonical intrinsic `mapRel` evidence reuses the general proof-relevant
list relator.  Every element witness remains present in the spine. -/
abbrev CanonicalMapRel {n : Nat} {context : Tower.Ctx n}
    {source target : Tower.Tm n} (relation : Tower.Tm n)
    (sourceList : CanonicalList context source)
    (targetList : CanonicalList context target) :=
  ListExample.ListRel (TypedRelationEvidence relation) sourceList targetList

/-! ## Encoding relational evidence into intrinsic syntax -/

/-- Fold a canonical proof spine into the actual intrinsic `mapRel`
constructors. -/
def encodeMapRel {n : Nat} {context : Tower.Ctx n}
    {source target relation : Tower.Tm n} :
    {sourceList : CanonicalList context source} →
    {targetList : CanonicalList context target} →
    CanonicalMapRel relation sourceList targetList → Tower.Tm n
  | [], [], .nil => IntrinsicRelator.nilRelApp source target relation
  | sourceHead :: sourceTail, targetHead :: targetTail,
      .cons headEvidence tailEvidence =>
      IntrinsicRelator.consRelApp source target relation
        sourceHead.term targetHead.term
        (encodeList (context := context) source sourceTail)
        (encodeList (context := context) target targetTail)
        headEvidence.term (encodeMapRel tailEvidence)

/-- Encoding a canonical proof spine produces a term in the corresponding
intrinsic `mapRel` fibre. -/
theorem encodeMapRel_hasType {n : Nat} {context : Tower.Ctx n}
    {source target relation : Tower.Tm n}
    (sourceTyping : Presentation.HasType IntrinsicRelator.rules context source
      (sortTm Intrinsic.elementLevel))
    (targetTyping : Presentation.HasType IntrinsicRelator.rules context target
      (sortTm Intrinsic.elementLevel))
    (relationTyping : Presentation.HasType IntrinsicRelator.rules context
      relation
      (.pi source (.pi (Presentation.rename wk target)
        (sortTm Intrinsic.motiveLevel)))) :
    {sourceList : CanonicalList context source} →
    {targetList : CanonicalList context target} →
    (evidence : CanonicalMapRel relation sourceList targetList) →
      Presentation.HasType IntrinsicRelator.rules context
        (encodeMapRel evidence)
        (IntrinsicRelator.mapRelApp source target relation
          (encodeList source sourceList) (encodeList target targetList))
  | [], [], .nil => by
      exact IntrinsicRelator.nilRelApp_hasType sourceTyping targetTyping
        relationTyping
  | sourceHead :: sourceTail, targetHead :: targetTail,
      .cons headEvidence tailEvidence => by
      exact IntrinsicRelator.consRelApp_hasType sourceTyping targetTyping
        relationTyping sourceHead.typing targetHead.typing
        (encodeList_hasType sourceTyping sourceTail)
        (encodeList_hasType targetTyping targetTail)
        headEvidence.typing
        (encodeMapRel_hasType sourceTyping targetTyping relationTyping
          tailEvidence)

/-- Raw constructor encoding also loses no canonical relational-evidence
spine.  In particular, evidence multiplicity cannot disappear merely by
entering intrinsic syntax. -/
theorem encodeMapRel_injective {n : Nat} {context : Tower.Ctx n}
    {source target relation : Tower.Tm n}
    (sourceList : CanonicalList context source)
    (targetList : CanonicalList context target) :
    Function.Injective
      (@encodeMapRel n context source target relation sourceList targetList) := by
  intro first
  induction first with
  | nil =>
      intro second _equality
      cases second
      rfl
  | cons firstHead firstTail hypothesis =>
      intro second equality
      cases second with
      | cons secondHead secondTail =>
          have tailTerms := congrArg applicationArgument equality
          have tailEquality :
              encodeMapRel firstTail = encodeMapRel secondTail := by
            simpa [encodeMapRel, IntrinsicRelator.consRelApp,
              applicationArgument] using tailTerms
          have functionTerms := congrArg applicationFunction equality
          have headTerms := congrArg applicationArgument functionTerms
          have headEquality : firstHead.term = secondHead.term := by
            simpa [encodeMapRel, IntrinsicRelator.consRelApp,
              applicationFunction, applicationArgument] using headTerms
          have headsEqual : firstHead = secondHead :=
            TypedRelationEvidence.ext headEquality
          have tailsEqual : firstTail = secondTail := hypothesis tailEquality
          cases headsEqual
          cases tailsEqual
          rfl

/-! ## Exact semantic correspondence -/

/-- Interpreting both canonical List spines reduces semantic `mapRel`
evidence to the very same `ListRel` proof spine. -/
theorem interpretedMapRel_eq_canonical {n : Nat}
    {context : Tower.Ctx n} {source target relation : Tower.Tm n}
    (sourceList : CanonicalList context source)
    (targetList : CanonicalList context target) :
    (Semantic.mapRel (typedRelation relation)).evidence
        (interpretList sourceList) (interpretList targetList) =
      CanonicalMapRel relation sourceList targetList := by
  change ListExample.ListRel (TypedRelationEvidence relation)
      (ListExample.toList (ListExample.ofList sourceList))
      (ListExample.toList (ListExample.ofList targetList)) =
    ListExample.ListRel (TypedRelationEvidence relation)
      sourceList targetList
  simp

/-- Canonical intrinsic proof spines and semantic polynomial `mapRel`
evidence are exactly equivalent, not merely equisupported. -/
noncomputable def canonicalMapRelEquiv {n : Nat}
    {context : Tower.Ctx n} {source target relation : Tower.Tm n}
    (sourceList : CanonicalList context source)
    (targetList : CanonicalList context target) :
    CanonicalMapRel relation sourceList targetList ≃
      (Semantic.mapRel (typedRelation relation)).evidence
        (interpretList sourceList) (interpretList targetList) :=
  Equiv.cast (interpretedMapRel_eq_canonical sourceList targetList).symm

/-! ## Earned functional specialization -/

/-- Evidence that one intrinsic relation fibre has a functional semantic
realization on typed raw endpoints.  This is additional structure: arbitrary
proof-relevant relations need not provide it. -/
structure FunctionalEvidenceRealization {n : Nat}
    {context : Tower.Ctx n} {source target : Tower.Tm n}
    (relation : Tower.Tm n) where
  action : TypedTerm context source → TypedTerm context target
  evidenceEquiv : ∀ sourceTerm targetTerm,
    TypedRelationEvidence relation sourceTerm targetTerm ≃
      ListExample.Graph action sourceTerm targetTerm

/-- A pointwise functional realization lifts through every canonical List
spine, then agrees exactly with the graph of ordinary List map.  Thus
functional map is earned from the proof-relevant relation rather than chosen
as its definition. -/
noncomputable def canonicalMapRel_graph_equiv_graph_map {n : Nat}
    {context : Tower.Ctx n} {source target relation : Tower.Tm n}
    (realization : FunctionalEvidenceRealization
      (context := context) (source := source) (target := target) relation)
    (sourceList : CanonicalList context source)
    (targetList : CanonicalList context target) :
    CanonicalMapRel relation sourceList targetList ≃
      ListExample.Graph (List.map realization.action)
        sourceList targetList :=
  (ListExample.ListRel.evidenceEquiv realization.evidenceEquiv
    sourceList targetList).trans
      (ListExample.listRel_graph_equiv_graph_map realization.action
        sourceList targetList)

/-! ## Evidence-retention controls -/

/-- The empty constructor supplies a canonical relational witness for every
well-formed relation, and its raw encoding is the genuine intrinsic
constructor. -/
def canonicalNilEvidence {n : Nat} {context : Tower.Ctx n}
    {source target relation : Tower.Tm n} :
    CanonicalMapRel (source := source) (target := target) relation
      ([] : CanonicalList context source)
      ([] : CanonicalList context target) :=
  .nil

@[simp] theorem encodeMapRel_canonicalNil {n : Nat}
    {context : Tower.Ctx n} {source target relation : Tower.Tm n} :
    encodeMapRel
        (canonicalNilEvidence (context := context)
          (source := source) (target := target) (relation := relation)) =
      IntrinsicRelator.nilRelApp source target relation :=
  rfl

/-- Distinct raw head-evidence terms remain distinct after relational cons
encoding.  The proof spine is not quotiented to endpoint truth. -/
theorem encodedCons_ne_of_headTerm_ne {n : Nat}
    {context : Tower.Ctx n} {source target relation : Tower.Tm n}
    {sourceHead : TypedTerm context source}
    {targetHead : TypedTerm context target}
    {sourceTail : CanonicalList context source}
    {targetTail : CanonicalList context target}
    (firstHead secondHead :
      TypedRelationEvidence relation sourceHead targetHead)
    (tailEvidence : CanonicalMapRel relation sourceTail targetTail)
    (different : firstHead.term ≠ secondHead.term) :
    encodeMapRel
        (ListExample.ListRel.cons firstHead tailEvidence) ≠
      encodeMapRel
        (ListExample.ListRel.cons secondHead tailEvidence) := by
  intro equality
  apply different
  simp only [encodeMapRel, IntrinsicRelator.consRelApp] at equality
  have functionEquality := congrArg
    (fun term => match term with
      | .app function _argument => function
      | other => other)
    equality
  have headEquality := congrArg
    (fun term => match term with
      | .app _function argument => some argument
      | _ => none)
    functionEquality
  simpa using headEquality

/-- If the element-evidence fibre is empty, no singleton `mapRel` evidence
can be manufactured. -/
theorem singletonMapRel_isEmpty {n : Nat}
    {context : Tower.Ctx n} {source target relation : Tower.Tm n}
    (sourceHead : TypedTerm context source)
    (targetHead : TypedTerm context target)
    (emptyHead : IsEmpty
      (TypedRelationEvidence relation sourceHead targetHead)) :
    IsEmpty (CanonicalMapRel relation [sourceHead] [targetHead]) where
  false := by
    intro evidence
    cases evidence with
    | cons headEvidence _ => exact emptyHead.false headEvidence

/-! ## Axiom audit -/

#print axioms encodeList_hasType
#print axioms encodeList_injective
#print axioms canonicalListEquiv
#print axioms encodeMapRel_hasType
#print axioms encodeMapRel_injective
#print axioms canonicalMapRelEquiv
#print axioms canonicalMapRel_graph_equiv_graph_map
#print axioms encodedCons_ne_of_headTerm_ne
#print axioms singletonMapRel_isEmpty

end IntrinsicCanonicalSemantics
end NativeIndexedFamilies
end Mettapedia.Languages.MeTTa.PureKernel.Universe
