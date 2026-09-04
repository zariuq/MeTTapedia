import Mettapedia.Computability.ReflectiveCode
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefDSL
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.PureCanonicalSection
import Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution

/-!
# The rho quote/drop boundary is relational and substitution-scoped

Pure rho and a total contextual-code interface have different law shapes.
Pure rho validates the name equation `quote (drop name) ≡ name` through
structural congruence.  It does not execute a free `drop (quote process)`.
The beta-shaped exposure instead occurs when communication substitution
actually replaces the dropped bound name by a quotation.  A separately named
execution extension may also add a free execution rule.

This module instantiates the general reflective-code capability theory on the
live rho `Pattern` carrier.  It proves:

* quote and drop preserve structural congruence;
* the static name eta law holds on the structural quotient;
* process beta fails even on that quotient for the free-drop witness;
* pure rho has no free operational beta for that witness;
* communication substitution has an exact, provenance-scoped beta law; and
* the explicit execution extension adds precisely the missing witness step.

Consequently rho reflection is not silently treated as a total modal splice.
Connecting it to contextual code requires a selected operational or quotient
adequacy theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.ReflectiveCodeBoundary

open Mettapedia.Computability.ReflectiveCode
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Extended

/-- The raw rho quotation/drop constructors, before any equation or
operational rule is imposed. -/
def rawInterface : Interface Pattern Pattern where
  quote := fun process => .apply "NQuote" [process]
  drop := fun quotedName => .apply "PDrop" [quotedName]

/-- Structural congruence as a setoid on the shared raw carrier.  The two
semantic sorts remain governed by rho's typing discipline; this setoid only
records the common structural relation used by quote and drop. -/
def structuralSetoid : Setoid Pattern where
  r := StructuralCongruence
  iseqv :=
    { refl := StructuralCongruence.refl
      symm := fun relation => StructuralCongruence.symm _ _ relation
      trans := fun first second => StructuralCongruence.trans _ _ _ first second }

/-- Structural congruence is preserved by every unary application
constructor. -/
theorem unary_congruence (constructor : String) {left right : Pattern}
    (related : StructuralCongruence left right) :
    StructuralCongruence (.apply constructor [left])
      (.apply constructor [right]) := by
  refine StructuralCongruence.apply_cong constructor [left] [right] rfl ?_
  intro index leftBound rightBound
  simp only [List.length_cons, List.length_nil] at leftBound rightBound
  have indexZero : index = 0 := by omega
  subst index
  simpa using related

/-- Both reflective constructors descend to the structural quotient. -/
def structuralCompatibility :
    Interface.QuotientCompatibility rawInterface structuralSetoid
      structuralSetoid where
  quote_respects := by
    intro left right related
    change StructuralCongruence left right at related
    change StructuralCongruence (.apply "NQuote" [left])
      (.apply "NQuote" [right])
    exact unary_congruence "NQuote" related
  drop_respects := by
    intro left right related
    change StructuralCongruence left right at related
    change StructuralCongruence (.apply "PDrop" [left])
      (.apply "PDrop" [right])
    exact unary_congruence "PDrop" related

/-- Pure rho's quote/drop equation is name eta relative to structural
congruence. -/
theorem structural_eta :
    rawInterface.EtaAlong structuralSetoid.r := by
  intro quotedName
  change StructuralCongruence
    (.apply "NQuote" [.apply "PDrop" [quotedName]]) quotedName
  exact StructuralCongruence.quote_drop quotedName

/-- Therefore quote-after-drop is literally the identity on the structural
quotient, even though it is not raw-syntax equality. -/
theorem quotient_eta :
    Function.RightInverse structuralCompatibility.quotientDrop
      structuralCompatibility.quotientQuote :=
  Interface.QuotientCompatibility.quotient_eta rawInterface
    structuralCompatibility structural_eta

/-- The name eta equation is not literal raw-syntax equality. -/
theorem raw_static_eta_fails : ¬ rawInterface.StaticEta := by
  intro eta
  have impossible := eta (.fvar "name")
  simp [rawInterface] at impossible

/-- The free dropped quotation and its proposed target are both in the pure
rho carrier. -/
theorem freeDropWitness_hashSetFree : HashSetFree freeDropWitness := by
  simp [freeDropWitness, HashSetFree, HashSetFreeList]

theorem freeDropTarget_hashSetFree : HashSetFree freeDropTarget := by
  simp [freeDropTarget, HashSetFree, HashSetFreeList]

/-- Process beta is absent even modulo pure structural congruence.  Thus the
name-eta quotient section is not an equivalence of process and name carriers. -/
theorem free_drop_not_structurally_beta :
    ¬ StructuralCongruence freeDropWitness freeDropTarget := by
  intro congruent
  have canonicalEqual :=
    (structuralCongruence_iff_canonicalize_eq
      freeDropWitness_hashSetFree freeDropTarget_hashSetFree).mp congruent
  simp [freeDropWitness, freeDropTarget, canonicalize, canonicalizeList,
    normalizeQuote] at canonicalEqual

/-- There is no structural process-beta law for every raw rho process. -/
theorem structural_beta_fails :
    ¬ rawInterface.BetaAlong structuralSetoid.r := by
  intro beta
  apply free_drop_not_structurally_beta
  have witness := beta freeDropTarget
  change StructuralCongruence freeDropWitness freeDropTarget at witness
  exact witness

/-- The declared rho reflective signature used by the generic substitution
compiler. -/
abbrev declaration : ReflectivePresentationDecl :=
  rhoReflectivePresentation.toReflectivePresentationDecl

/-- Communication-substitution beta: a dropped bound name is exposed exactly
when this substitution supplied a quotation. -/
theorem communication_substitution_beta (process : Pattern) :
    substituteReflective declaration 0 (rawInterface.quote process)
        (rawInterface.drop (.bvar 0)) = process := by
  simp [rawInterface, declaration, substituteReflective,
    substituteNameMark, normalizeReflective, rhoReflectivePresentation]

/-- A free dropped quotation remains inert under the same substitution; the
beta law is provenance-scoped rather than a raw constructor equation. -/
theorem free_drop_remains_inert_under_substitution :
    substituteReflective declaration 0
        (rawInterface.quote freeDropTarget)
        (rawInterface.drop (rawInterface.quote freeDropTarget)) =
      rawInterface.drop (rawInterface.quote freeDropTarget) := by
  rfl

/-- Literal quotation is opaque to communication substitution. -/
theorem literal_quote_is_substitution_opaque :
    substituteReflective declaration 0
        (rawInterface.quote freeDropTarget)
        (rawInterface.quote
          (.apply "POutput" [.bvar 0, freeDropTarget])) =
      rawInterface.quote
        (.apply "POutput" [.bvar 0, freeDropTarget]) := by
  rfl

/-- Pure rho rejects free process beta operationally, while the explicitly
named execution extension admits exactly the material witness. -/
theorem pure_vs_execution_extension :
    (forall target, ¬ langReduces rhoCalc freeDropWitness target) /\
      langReduces rhoCalcExecExt freeDropWitness freeDropTarget :=
  freeDrop_pure_vs_execExt

/-- The three law scopes coexist and remain distinct: static name eta,
communication-substitution beta, and optional free execution. -/
theorem reflection_scope_matrix :
    rawInterface.EtaAlong structuralSetoid.r /\
      (forall process,
        substituteReflective declaration 0 (rawInterface.quote process)
            (rawInterface.drop (.bvar 0)) = process) /\
      (forall target, ¬ langReduces rhoCalc freeDropWitness target) /\
      langReduces rhoCalcExecExt freeDropWitness freeDropTarget /\
      ¬ rawInterface.BetaAlong structuralSetoid.r := by
  exact ⟨structural_eta, communication_substitution_beta,
    pure_vs_execution_extension.1, pure_vs_execution_extension.2,
    structural_beta_fails⟩

#print axioms unary_congruence
#print axioms quotient_eta
#print axioms raw_static_eta_fails
#print axioms free_drop_not_structurally_beta
#print axioms structural_beta_fails
#print axioms communication_substitution_beta
#print axioms free_drop_remains_inert_under_substitution
#print axioms literal_quote_is_substitution_opaque
#print axioms pure_vs_execution_extension
#print axioms reflection_scope_matrix

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.ReflectiveCodeBoundary
