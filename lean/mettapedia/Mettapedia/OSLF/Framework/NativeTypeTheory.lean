import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.GSLT.Core.NonFactorization

/-!
# Native types: the type theory a language already has

OSLF derives a language's behavioural modalities from its own reduction
relation — `langDiamond` and `langBox` in `TypeSynthesis`, with their Galois
connection falling out automatically.  What that leaves unsaid is the
*spatial* half: the types that come from the term grammar rather than from
reduction, and how the two combine.

This module takes the first step of OSLF → native type theory by naming that
combined type language and giving it a semantics, and then answering the
question the language-purity work needs:

> Which typing judgments are *derived* from a `LanguageDef`, and which are
> genuinely authored information?

The answer is a construction rather than a judgement call.

* **Native types are derived.**  `satisfies_congr` shows the whole semantics
  depends on the language **only through its step relation** — spatial
  formers from the constructors, modal formers from reduction, nothing else.
  So a native type is a *view* of the core fields, never extension data.

* **Authored typing is not.**  `authored_typing_not_determined_by_language`
  exhibits two different typing relations over one and the same language.
  Typing therefore does not factor through the `LanguageDef`, which is
  exactly what makes an authored type system genuine new information rather
  than a redundant restatement.

Those two together are the derivable/residual boundary the extension
architecture needs, and they are the reason a proof calculus belongs in a
fibre over the core rather than inside it: the part that *is* determined is
already available without being stored, and the part that is stored is
provably not determined.
-/

namespace Mettapedia.OSLF.Framework.NativeTypeTheory

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.GSLT.Core.NonFactorization

/-! ## The native type language

Spatial formers name a constructor and constrain its arguments; modal formers
reuse the operators OSLF already derives; the rest is ordinary propositional
structure. -/

/-- A type of the native theory of some language. -/
inductive NativeType where
  /-- Every term. -/
  | top
  /-- No term. -/
  | bot
  /-- Both. -/
  | and (left right : NativeType)
  /-- Either. -/
  | or (left right : NativeType)
  /-- **Spatial**: headed by a named constructor, with typed arguments. -/
  | headed (constructor : String) (arguments : List NativeType)
  /-- **Behavioural**: some successor satisfies the inner type. -/
  | diamond (inner : NativeType)
  /-- **Behavioural**: every predecessor satisfies the inner type. -/
  | box (inner : NativeType)
deriving Repr

mutual

/-- Native inhabitation over an explicit reduction span.  This is the
interpretation-independent core: syntactic, reflective, logic-backed, and
other lawful rule interpretations can all supply their own span without
changing the native type language. -/
def satisfiesOver (span : ReductionSpan Pattern) : NativeType → Pattern → Prop
  | .top, _ => True
  | .bot, _ => False
  | .and left right, pattern =>
      satisfiesOver span left pattern ∧ satisfiesOver span right pattern
  | .or left right, pattern =>
      satisfiesOver span left pattern ∨ satisfiesOver span right pattern
  | .headed constructor arguments, pattern =>
      ∃ children : List Pattern,
        pattern = .apply constructor children ∧
          satisfiesAllOver span arguments children
  | .diamond inner, pattern =>
      derivedDiamond span (satisfiesOver span inner) pattern
  | .box inner, pattern =>
      derivedBox span (satisfiesOver span inner) pattern

/-- Pointwise inhabitation of an argument vector. -/
def satisfiesAllOver (span : ReductionSpan Pattern) :
    List NativeType → List Pattern → Prop
  | [], [] => True
  | argument :: arguments, child :: children =>
      satisfiesOver span argument child ∧
        satisfiesAllOver span arguments children
  | _, _ => False

end

/-- Native inhabitation for a language under an explicit relation
environment.  The environment is part of the interpreted reduction span; it
is not stored as a second native-type authority. -/
def satisfiesUsing (relEnv : MeTTaIL.Engine.RelationEnv)
    (lang : LanguageDef) : NativeType → Pattern → Prop :=
  satisfiesOver (langSpanUsing relEnv lang)

/-- Pointwise native inhabitation under an explicit relation environment. -/
def satisfiesAllUsing (relEnv : MeTTaIL.Engine.RelationEnv)
    (lang : LanguageDef) : List NativeType → List Pattern → Prop :=
  satisfiesAllOver (langSpanUsing relEnv lang)

/-- What it means for a pattern to inhabit a native type under the default
empty relation environment. -/
def satisfies (lang : LanguageDef) : NativeType → Pattern → Prop :=
  satisfiesUsing MeTTaIL.Engine.RelationEnv.empty lang

/-- Pointwise default inhabitation of an argument vector. -/
def satisfiesAll (lang : LanguageDef) : List NativeType → List Pattern → Prop :=
  satisfiesAllUsing MeTTaIL.Engine.RelationEnv.empty lang

/-! ## Proof-relevant certificates for the finitary native fragment

`top`, conjunction, disjunction, spatial heads, and `diamond` have finite
positive witnesses.  A diamond certificate retains the exact reduction edge
and the certificate for its target.  There is deliberately no constructor for
`bot` or `box`: arbitrary predecessor-universality requires a separate finite
enumeration, invariant, or coinductive certificate rather than an unchecked
claim. -/

mutual

/-- A finite positive certificate for native inhabitation. -/
inductive Certificate (span : ReductionSpan Pattern) :
    NativeType → Pattern → Type where
  | top (pattern : Pattern) : Certificate span .top pattern
  | and {left right pattern}
      (leftEvidence : Certificate span left pattern)
      (rightEvidence : Certificate span right pattern) :
      Certificate span (.and left right) pattern
  | orLeft {left right pattern}
      (evidence : Certificate span left pattern) :
      Certificate span (.or left right) pattern
  | orRight {left right pattern}
      (evidence : Certificate span right pattern) :
      Certificate span (.or left right) pattern
  | headed (constructor : String) (arguments : List NativeType)
      (pattern : Pattern) (children : List Pattern)
      (shape : pattern = .apply constructor children)
      (childrenEvidence : CertificateAll span arguments children) :
      Certificate span (.headed constructor arguments) pattern
  | diamond {inner source}
      (edge : span.Edge)
      (sourceEq : span.source edge = source)
      (targetEvidence : Certificate span inner (span.target edge)) :
      Certificate span (.diamond inner) source

/-- Pointwise finite certificates for a spatial argument vector. -/
inductive CertificateAll (span : ReductionSpan Pattern) :
    List NativeType → List Pattern → Type where
  | nil : CertificateAll span [] []
  | cons {argument arguments child children}
      (head : Certificate span argument child)
      (tail : CertificateAll span arguments children) :
      CertificateAll span (argument :: arguments) (child :: children)

end

mutual

/-- Every finite native certificate denotes true native inhabitation. -/
theorem Certificate.sound {span : ReductionSpan Pattern} :
    ∀ {nativeType pattern}, Certificate span nativeType pattern →
      satisfiesOver span nativeType pattern
  | _, _, .top _ => trivial
  | _, _, .and leftEvidence rightEvidence =>
      ⟨leftEvidence.sound, rightEvidence.sound⟩
  | _, _, .orLeft evidence => Or.inl evidence.sound
  | _, _, .orRight evidence => Or.inr evidence.sound
  | _, _, .headed _ _ _ children shape childrenEvidence =>
      ⟨children, shape, childrenEvidence.sound⟩
  | _, _, .diamond edge sourceEq targetEvidence => by
      exact ⟨edge, sourceEq, targetEvidence.sound⟩

/-- Pointwise certificate soundness. -/
theorem CertificateAll.sound {span : ReductionSpan Pattern} :
    ∀ {arguments children}, CertificateAll span arguments children →
      satisfiesAllOver span arguments children
  | _, _, .nil => trivial
  | _, _, .cons head tail => ⟨head.sound, tail.sound⟩

end

/-- `bot` has no positive native certificate. -/
theorem bot_not_certifiable (span : ReductionSpan Pattern) (pattern : Pattern) :
    IsEmpty (Certificate span .bot pattern) :=
  ⟨fun evidence => nomatch evidence⟩

/-- `box` is intentionally outside the finite positive certificate fragment.
Its admission requires a separately checked completeness witness. -/
theorem box_not_certifiable (span : ReductionSpan Pattern)
    (inner : NativeType) (pattern : Pattern) :
    IsEmpty (Certificate span (.box inner) pattern) :=
  ⟨fun evidence => nomatch evidence⟩

mutual

/-- Executable membership in the finite positive-certificate fragment.  `bot`
is part of the syntax (and has no inhabitants); `box` is rejected because its
universal predecessor obligation needs additional completeness evidence. -/
def NativeType.finitelyCertifiable : NativeType → Bool
  | .top | .bot => true
  | .and left right | .or left right =>
      left.finitelyCertifiable && right.finitelyCertifiable
  | .headed _ arguments => nativeTypesFinitelyCertifiable arguments
  | .diamond inner => inner.finitelyCertifiable
  | .box _ => false

def nativeTypesFinitelyCertifiable : List NativeType → Bool
  | [] => true
  | nativeType :: nativeTypes =>
      nativeType.finitelyCertifiable &&
        nativeTypesFinitelyCertifiable nativeTypes

end

mutual

/-- Completeness of finite positive certificates on their admitted fragment. -/
theorem Certificate.complete {span : ReductionSpan Pattern} :
    ∀ (nativeType : NativeType) (pattern : Pattern),
      nativeType.finitelyCertifiable = true →
      satisfiesOver span nativeType pattern →
      Nonempty (Certificate span nativeType pattern)
  | .top, pattern, _, _ => ⟨.top pattern⟩
  | .bot, _, _, inhabited => False.elim inhabited
  | .and left right, pattern, supported, inhabited => by
      simp only [NativeType.finitelyCertifiable, Bool.and_eq_true] at supported
      obtain ⟨leftEvidence⟩ :=
        Certificate.complete left pattern supported.1 inhabited.1
      obtain ⟨rightEvidence⟩ :=
        Certificate.complete right pattern supported.2 inhabited.2
      exact ⟨.and leftEvidence rightEvidence⟩
  | .or left right, pattern, supported, inhabited => by
      simp only [NativeType.finitelyCertifiable, Bool.and_eq_true] at supported
      rcases inhabited with leftInhabited | rightInhabited
      · obtain ⟨evidence⟩ :=
          Certificate.complete left pattern supported.1 leftInhabited
        exact ⟨.orLeft evidence⟩
      · obtain ⟨evidence⟩ :=
          Certificate.complete right pattern supported.2 rightInhabited
        exact ⟨.orRight evidence⟩
  | .headed constructor arguments, pattern, supported, inhabited => by
      obtain ⟨children, shape, childrenInhabited⟩ := inhabited
      obtain ⟨childrenEvidence⟩ :=
        CertificateAll.complete arguments children supported childrenInhabited
      exact ⟨.headed constructor arguments pattern children shape
        childrenEvidence⟩
  | .diamond inner, source, supported, inhabited => by
      obtain ⟨edge, sourceEq, targetInhabited⟩ := inhabited
      obtain ⟨targetEvidence⟩ :=
        Certificate.complete inner (span.target edge) supported targetInhabited
      exact ⟨.diamond edge sourceEq targetEvidence⟩
  | .box _, _, supported, _ => by
      simp [NativeType.finitelyCertifiable] at supported

/-- Pointwise completeness for finite spatial argument vectors. -/
theorem CertificateAll.complete {span : ReductionSpan Pattern} :
    ∀ (arguments : List NativeType) (children : List Pattern),
      nativeTypesFinitelyCertifiable arguments = true →
      satisfiesAllOver span arguments children →
      Nonempty (CertificateAll span arguments children)
  | [], [], _, _ => ⟨.nil⟩
  | [], _ :: _, _, inhabited => False.elim inhabited
  | _ :: _, [], _, inhabited => False.elim inhabited
  | argument :: arguments, child :: children, supported, inhabited => by
      simp only [nativeTypesFinitelyCertifiable, Bool.and_eq_true] at supported
      obtain ⟨headEvidence⟩ :=
        Certificate.complete argument child supported.1 inhabited.1
      obtain ⟨tailEvidence⟩ :=
        CertificateAll.complete arguments children supported.2 inhabited.2
      exact ⟨.cons headEvidence tailEvidence⟩

end


/-! ### Multiplicity boundary of propositional native modalities -/

private def oneEdgeSpan (source target : Pattern) : ReductionSpan Pattern where
  Edge := Unit
  source := fun _ => source
  target := fun _ => target

private def twoEdgeSpan (source target : Pattern) : ReductionSpan Pattern where
  Edge := Bool
  source := fun _ => source
  target := fun _ => target

/-- Native diamond sees existence, not how many occurrence edges witness it.
An exact-bag executor must therefore retain multiplicity separately rather
than treating native satisfaction as its result carrier. -/
theorem diamond_forgets_edge_multiplicity (source target : Pattern) :
    satisfiesOver (oneEdgeSpan source target) (.diamond .top) source ↔
      satisfiesOver (twoEdgeSpan source target) (.diamond .top) source := by
  simp [satisfiesOver, derivedDiamond, di, pb, oneEdgeSpan, twoEdgeSpan]

/-- The two spans identified by the diamond observation genuinely contain
different numbers of occurrence edges. -/
theorem diamond_equal_but_edge_counts_differ (source target : Pattern) :
    (satisfiesOver (oneEdgeSpan source target) (.diamond .top) source ↔
      satisfiesOver (twoEdgeSpan source target) (.diamond .top) source) ∧
      Fintype.card Unit ≠ Fintype.card Bool := by
  exact ⟨diamond_forgets_edge_multiplicity source target, by decide⟩

/-! ## Spatial keys usable by compilers -/

/-- The constructor and arity visible in a spatial native type. -/
structure HeadSignature where
  constructor : String
  arity : Nat
deriving Repr, DecidableEq

/-- Extract a dispatch key from the outermost spatial type.  Compound and
behavioural types are not guessed through: an optimizer may fall back when no
exact outer head is available. -/
def NativeType.headSignature? : NativeType → Option HeadSignature
  | .headed constructor arguments => some ⟨constructor, arguments.length⟩
  | _ => none

/-- Extract the same key directly from an application pattern. -/
def patternHeadSignature? : Pattern → Option HeadSignature
  | .apply constructor arguments => some ⟨constructor, arguments.length⟩
  | _ => none

/-- Satisfaction of a spatial type supplies an exact constructor/arity key.
This is the no-false-negative fact needed by a head-indexed compiler. -/
theorem patternHeadSignature_of_satisfiesOver_headed
    (span : ReductionSpan Pattern) (constructor : String)
    (arguments : List NativeType) (pattern : Pattern)
    (inhabited : satisfiesOver span (.headed constructor arguments) pattern) :
    patternHeadSignature? pattern =
      some ⟨constructor, arguments.length⟩ := by
  rcases inhabited with ⟨children, rfl, childrenInhabited⟩
  have sameLength : children.length = arguments.length := by
    induction arguments generalizing children with
    | nil =>
        cases children <;> simp_all [satisfiesAllOver]
    | cons argument arguments inductionHypothesis =>
        cases children with
        | nil => simp [satisfiesAllOver] at childrenInhabited
        | cons child children =>
            simp only [satisfiesAllOver] at childrenInhabited
            simp [inductionHypothesis children childrenInhabited.2]
  simp [patternHeadSignature?, sameLength]

/-! ## The spatial fragment is generated by the term grammar -/

/-- Every declared constructor yields a native type: the terms headed by it,
with unconstrained arguments.  This is the sense in which the spatial half of
the theory is *read off* the language rather than written. -/
def constructorTypes (lang : LanguageDef) : List NativeType :=
  lang.terms.map fun rule =>
    NativeType.headed rule.label (rule.params.map fun _ => NativeType.top)

/-- **The spatial fragment factors through `terms`.**  Two languages with the
same constructors generate the same spatial types, so nothing else about a
language contributes to them. -/
theorem constructorTypes_factors_through_terms {first second : LanguageDef}
    (sameTerms : first.terms = second.terms) :
    constructorTypes first = constructorTypes second := by
  simp [constructorTypes, sameTerms]

/-- Stated as a factorization in the criterion's own vocabulary. -/
theorem constructorTypes_factors : Factors LanguageDef.terms constructorTypes :=
  ⟨fun terms => terms.map fun rule =>
      NativeType.headed rule.label (rule.params.map fun _ => NativeType.top),
    fun _ => rfl⟩

/-! ## The whole theory depends only on the step relation

The modal half is delegated to `langDiamond`/`langBox`, which are derived
from reduction.  So the entire semantics is a function of the reduction
relation together with the constructors — and of nothing else a language
carries. -/

/-- **Native inhabitation is determined by the step relation.**  Two languages
whose derived reductions agree assign every native type the same meaning.
Since `langDiamond` and `langBox` are themselves derived, this says the native
theory adds no information to the language: it is a view. -/
theorem satisfies_congr {first second : LanguageDef}
    (sameStep : langSpan first = langSpan second) :
    ∀ (nativeType : NativeType) (pattern : Pattern),
      satisfies first nativeType pattern ↔ satisfies second nativeType pattern := by
  intro nativeType pattern
  change satisfiesOver (langSpan first) nativeType pattern ↔
    satisfiesOver (langSpan second) nativeType pattern
  rw [sameStep]

theorem satisfiesAll_congr {first second : LanguageDef}
    (sameStep : langSpan first = langSpan second) :
    ∀ (arguments : List NativeType) (children : List Pattern),
      satisfiesAll first arguments children ↔ satisfiesAll second arguments children := by
  intro arguments children
  change satisfiesAllOver (langSpan first) arguments children ↔
    satisfiesAllOver (langSpan second) arguments children
  rw [sameStep]

/-! ## Authored typing is not determined by the language

The complementary half, and the reason a proof calculus is genuine extension
data rather than a redundant restatement. -/

/-- A typing relation over a fixed language: which terms have which types. -/
abbrev AuthoredTyping := Pattern → Pattern → Prop

/-- Two authored typings over one language. -/
def permissiveTyping : AuthoredTyping := fun _ _ => True

def restrictiveTyping : AuthoredTyping := fun _ _ => False

theorem authored_typings_differ : permissiveTyping ≠ restrictiveTyping := by
  intro equal
  have applied : permissiveTyping (.apply "x" []) (.apply "T" []) =
      restrictiveTyping (.apply "x" []) (.apply "T" []) := by rw [equal]
  simp [permissiveTyping, restrictiveTyping] at applied

/-- Pairing a typing with the language it is authored over. -/
abbrev TypedLanguage := LanguageDef × AuthoredTyping

/-- Two typed languages sharing one language and differing in their typing. -/
def authoredFiber (lang : LanguageDef) :
    NonTrivialFiber (fun typed : TypedLanguage => typed.1) (fun typed => typed.2) where
  left := (lang, permissiveTyping)
  right := (lang, restrictiveTyping)
  sameShadow := rfl
  differentValue := authored_typings_differ

/-- **Authored typing does not factor through the language.**  So a type
system written by a user is genuine new information: no function of the
`LanguageDef` recovers it, and it therefore belongs in a fibre over the core
rather than inside it. -/
theorem authored_typing_not_determined_by_language (lang : LanguageDef) :
    ¬ Factors (fun typed : TypedLanguage => typed.1) (fun typed => typed.2) :=
  (authoredFiber lang).not_factors

/-- **The boundary, stated once.**  What the native theory says is derived —
determined by the constructors and the step relation.  What a user authors is
not.  The first needs no storage; the second is exactly what an extension
must carry. -/
theorem derived_and_authored_boundary (lang : LanguageDef) :
    Factors LanguageDef.terms constructorTypes ∧
      ¬ Factors (fun typed : TypedLanguage => typed.1) (fun typed => typed.2) :=
  ⟨constructorTypes_factors, authored_typing_not_determined_by_language lang⟩

end Mettapedia.OSLF.Framework.NativeTypeTheory
