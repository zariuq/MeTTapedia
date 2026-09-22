import Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Regular.ContextNormalization
import Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Regular.TypeConversionSemantics

/-!
# Normal telescope transport in the regular syntactic category

Normalizing a formed telescope changes its type entries while retaining
variable positions and every substitution image. Typed identity substitutions
give a natural isomorphism from the original context category to this
normalization functor. Source types and terms transport coherently and their
normal forms are unchanged. This is not a quotient of terms by conversion.
-/

namespace Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Regular.SyntacticCwf

open Syntax Substitution Regular
open _root_.CategoryTheory
open Mettapedia.TypeTheory

def normalizedContext (Γ : Context) : Context :=
  ⟨Γ.length, (normalizeContext Γ.raw Γ.regular).context,
    (normalizeContext Γ.raw Γ.regular).conversion.target_regular⟩

/-- Reassign the same image terms to the two computed normal telescopes. -/
def normalizedContextSub {Γ Δ : Context} (σ : Hom Γ Δ) :
    Hom (normalizedContext Γ) (normalizedContext Δ) :=
  ⟨σ.val, (normalizeContext Δ.raw Δ.regular).conversion.transportMorphism
    (normalizeContext Γ.raw Γ.regular).conversion σ.property⟩

def contextNormalizationFunctor : cwf.base.Context ⥤ cwf.base.Context where
  obj Γ := ⟨normalizedContext Γ.val⟩
  map σ := normalizedContextSub σ
  map_id _ := Subtype.ext rfl
  map_comp _ _ := Subtype.ext rfl

/-- The inverse maps retain all variables; their typing follows from the
entrywise conversion theorem, not from equality of the context syntax. -/
def contextNormalizationIso (Γ : Context) :
    CwfYoneda.context cwf Γ ≅ CwfYoneda.context cwf (normalizedContext Γ) where
  hom := ⟨ids, (normalizeContext Γ.raw Γ.regular).conversion.symm.identityMorphism⟩
  inv := ⟨ids, (normalizeContext Γ.raw Γ.regular).conversion.identityMorphism⟩
  hom_inv_id := Subtype.ext rfl
  inv_hom_id := Subtype.ext rfl

/-- All context substitutions commute with canonical telescope transport. -/
def contextNormalizationNaturalIso :
    𝟭 cwf.base.Context ≅ contextNormalizationFunctor :=
  NatIso.ofComponents (fun Γ => contextNormalizationIso Γ.val) (by
    intro Γ Δ σ
    apply Subtype.ext
    funext i
    exact (subst_ids (σ.val i)).symm)

/-- Yoneda carries the source comparison to its actual semantic contexts. -/
def representedContextNormalizationIso (Γ : Context) :
    CwfYoneda.contextFace cwf Γ ≅ CwfYoneda.contextFace cwf (normalizedContext Γ) :=
  yoneda.mapIso (contextNormalizationIso Γ)

/-- Transport preserves type code while changing its context derivation. -/
def typeInNormalizedContext {Γ : Context} (A : Ty Γ) : Ty (normalizedContext Γ) :=
  ⟨A.val, (normalizeContext Γ.raw Γ.regular).conversion.transport A.property⟩

def termInNormalizedContext {Γ : Context} {A : Ty Γ} (term : Tm Γ A) :
    Tm (normalizedContext Γ) (typeInNormalizedContext A) :=
  ⟨term.val, (normalizeContext Γ.raw Γ.regular).conversion.transport term.property⟩

theorem typeInNormalizedContext_substitution {Γ Δ : Context} (A : Ty Δ) (σ : Hom Γ Δ) :
    typeInNormalizedContext (typeSub A σ) =
      typeSub (typeInNormalizedContext A) (normalizedContextSub σ) := rfl

theorem termInNormalizedContext_substitution {Γ Δ : Context} {A : Ty Δ}
    (term : Tm Δ A) (σ : Hom Γ Δ) :
    termInNormalizedContext (termSub term σ) =
      termSub (termInNormalizedContext term) (normalizedContextSub σ) := rfl

/-- Normalization depends on the actual program, not the context-conversion
proof used to establish that the program is regular. -/
theorem normalizeTerm_context_transport {Γ : Context} {A : Ty Γ} (term : Tm Γ A) :
    normalizeTerm (termInNormalizedContext term) =
      termInNormalizedContext (normalizeTerm term) := rfl

/-! ## Dependent entries after a converted prefix -/

def betaPrefix : Context := extend sampleContext betaIndexedType
def reducedPrefix : Context := extend sampleContext dependentIdentityFamily

theorem betaPrefix_converts : RegularCtxConversion betaPrefix.raw reducedPrefix.raw :=
  .snoc (.refl sampleContext.regular) betaIndexedType.property
    dependentIdentityFamily.property betaIndexedType_converts

/-- The third entry refers to the immediately preceding proof variable,
whose declared type contains the beta redex. -/
def laterProofType : Ty betaPrefix :=
  identityType (typeSub betaIndexedType (weaken betaIndexedType))
    (lastTerm betaIndexedType) (lastTerm betaIndexedType)

def laterProofTypeInReducedPrefix : Ty reducedPrefix :=
  ⟨laterProofType.val, betaPrefix_converts.transport laterProofType.property⟩

def betaTelescope : Context := extend betaPrefix laterProofType
def reducedTelescope : Context := extend reducedPrefix laterProofTypeInReducedPrefix

theorem dependent_telescope_converts :
    RegularCtxConversion betaTelescope.raw reducedTelescope.raw :=
  betaPrefix_converts.extend_same laterProofType.property

/-- A nontrivial converted prefix remains compatible with its dependent
suffix. The original contexts stay distinct; their computed forms coincide. -/
theorem dependent_telescope_normal_forms :
    betaTelescope.raw ≠ reducedTelescope.raw ∧
      (normalizedContext betaTelescope).raw = (normalizedContext reducedTelescope).raw := by
  constructor
  · intro equal
    cases equal
  · exact (normalizeContext_eq_iff betaTelescope.regular reducedTelescope.regular).2
      dependent_telescope_converts

theorem dependent_telescope_decision :
    decideContextConversion betaTelescope.regular reducedTelescope.regular = true :=
  (decideContextConversion_correct _ _).2 dependent_telescope_converts

/-- Converting earlier declarations retains the newest dependent variable
and its entire type, not merely a count of context entries. -/
theorem dependent_telescope_retains_variable :
    RegularHasType reducedTelescope.raw (lastTerm laterProofType).val
      (typeSub laterProofType (weaken laterProofType)).val :=
  dependent_telescope_converts.transport (lastTerm laterProofType).property

private def functionAssumption : Context :=
  extend empty (piType (smallSort empty) (smallSort sampleContext))

private theorem sampleContext_normal : ContextNormal sampleContext.raw :=
  .snoc .nil (u0_redNormal 0)

private theorem functionAssumption_normal : ContextNormal functionAssumption.raw := by
  refine .snoc .nil ?_
  intro target step
  cases step with
  | congPiDom impossible => exact u0_redNormal 0 _ impossible
  | congPiCod impossible => exact u0_redNormal 1 _ impossible

/-- Equal lengths are insufficient: a small-type assumption and a function
assumption remain different canonical contexts. -/
theorem different_context_types_rejected :
    decideContextConversion sampleContext.regular functionAssumption.regular = false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  have converted := (decideContextConversion_correct _ _).1 accepted
  have equal := converted.eq_of_normal sampleContext_normal functionAssumption_normal
  cases equal

/-- Malformed upper-sort assumptions cannot enter the conversion relation,
even when both sides contain the same malformed syntax. -/
theorem malformed_context_not_convertible :
    ¬ RegularCtxConversion (Context.Ctx.snoc .nil .u1) (Context.Ctx.snoc .nil .u1) := by
  intro converted
  exact no_regular_u1_term converted.source_regular.head_formed

#print axioms contextNormalizationNaturalIso
#print axioms representedContextNormalizationIso
#print axioms termInNormalizedContext_substitution
#print axioms normalizeTerm_context_transport
#print axioms dependent_telescope_normal_forms
#print axioms dependent_telescope_decision
#print axioms dependent_telescope_retains_variable
#print axioms different_context_types_rejected
#print axioms malformed_context_not_convertible

end Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Regular.SyntacticCwf
