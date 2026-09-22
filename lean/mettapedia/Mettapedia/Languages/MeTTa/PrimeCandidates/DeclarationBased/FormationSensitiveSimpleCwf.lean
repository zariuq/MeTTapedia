import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveCwf
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveSimpleFragment
import Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.CwfMorphism
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveQuotientInterpretation
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeQuotientInterpretationControls

/-!
# The simply typed fragment in the formed cumulative CwF

The existing term and substitution translation is a strict CwF morphism
into the formation-sensitive source, not just the permissive source. Its
erasure agrees with the previous translation on contexts, types, terms and
substitutions. No second translation algorithm or typing authority is used.

The existing normalizer and conversion decision are connected to the actual
formed conversion fibres. Equality there is decided on the translated simple
image, including under further simple substitutions. This does not normalize
arbitrary dependent terms, reflect all target inhabitants, or identify raw
source code with its normal form.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
namespace FormationSensitiveSimpleCwf

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.IntrinsicSTT Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.TowerDTT
open Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.SubstitutionTranslation FormationSensitiveSimpleFragment
open Presentation

variable {Γ Δ Θ : List Ty} {A : Ty}

def mapContext (Γ : List Ty) : FormationSensitiveContextual.Context Tower.rules :=
  ⟨Γ.length, eraseContext Γ, eraseContext_formed Γ⟩

def simpleType (context : FormationSensitiveContextual.Context Tower.rules) (A : Ty) :
    FormationSensitiveContextual.TypeOver context :=
  ⟨eraseTypeAt context.arity A, .sort (levelOf A), .sort (levelOf A),
    eraseTypeAt_formed A context.raw⟩

def mapTerm (term : Term Γ A) :
    FormationSensitiveContextual.Term (mapContext Γ) (simpleType (mapContext Γ) A) :=
  ⟨eraseTerm term, eraseTerm_typed term⟩

def mapSubstitution (σ : Substitution Δ Γ) :
    FormationSensitiveContextual.Hom (mapContext Γ) (mapContext Δ) :=
  ⟨eraseSubstitution σ, eraseSubstitution_typed σ⟩

def contextFunctor : syntacticCwfWithTerminal.toCwf.base.Context ⥤
    (FormationSensitiveContextual.asCwfWithTerminal Tower.rules).toCwf.base.Context where
  obj context := ⟨mapContext context.val⟩
  map := mapSubstitution
  map_id context := FormationSensitiveContextual.Hom.ext (eraseSubstitution_variables context.val)
  map_comp earlier later := FormationSensitiveContextual.Hom.ext
    (Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.CwfMorphism.eraseSubstitution_comp later earlier)

theorem simpleType_reindex {source target : FormationSensitiveContextual.Context Tower.rules}
    (σ : FormationSensitiveContextual.Hom source target) (A : Ty) :
    (simpleType target A).reindex σ = simpleType source A :=
  FormationSensitiveContextual.TypeOver.ext (eraseTypeAt_subst A σ.substitution) rfl

def familyMorphism : CwfFamilyMorphism syntacticCwfWithTerminal.toCwf
    (FormationSensitiveContextual.asCwf Tower.rules) where
  base := contextFunctor
  family := {
    app := fun context => {
      onIndex := simpleType (mapContext context.unop.val)
      onFibre := fun _ => mapTerm }
    naturality := by
      intro source target σ
      apply IndexedFamily.Hom.ext
      · funext A
        exact (simpleType_reindex (mapSubstitution σ.unop) A).symm
      · intro A term
        apply FormationSensitiveContextual.Term.heq_of_type_eq_of_code_eq
        · exact (simpleType_reindex (mapSubstitution σ.unop) A).symm
        · exact eraseTerm_substitute σ.unop term }

/-- The simple fragment preserves the entire substitution/comprehension
structure in the formed candidate, with no reverse use of typing erasure. -/
def strictMorphism : StrictCwfMorphism syntacticCwfWithTerminal
    (FormationSensitiveContextual.asCwfWithTerminal Tower.rules) where
  toFamilyMorphism := familyMorphism
  empty_preserved := rfl
  extension_preserved _ _ := rfl
  projection_preserved context type := by
    change List Ty at context
    change Ty at type
    apply FormationSensitiveContextual.Hom.ext
    change eraseSubstitution (fun v => Term.var (Var.succ v)) =
      subComp ids projection
    rw [subComp_ids_left]
    funext index
    rw [← eraseVar_typedVarAt context index, eraseSubstitution_apply]
    rfl
  variable_preserved context type := by
    change List Ty at context
    change Ty at type
    apply FormationSensitiveContextual.Term.heq_of_type_eq_of_code_eq
    · apply FormationSensitiveContextual.TypeOver.ext
      · change eraseTypeAt (type :: context).length type =
          subst ids (subst projection (eraseTypeAt context.length type))
        rw [eraseTypeAt_subst, eraseTypeAt_subst]
        rfl
      · rfl
    · rfl

/-- Erasing formation evidence after translating agrees with the earlier
context functor, on every context and substitution. -/
theorem forget_contextFunctor :
    contextFunctor ⋙ FormationSensitiveContextual.forgetBase Tower.rules =
      Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.CwfMorphism.contextFunctor := rfl

theorem forget_type (context : List Ty) (A : Ty) :
    (simpleType (mapContext context) A).toRaw =
      Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.CwfMorphism.simpleType (Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.CwfMorphism.mapContext context) A := rfl

theorem forget_term (term : Term Γ A) :
    (mapTerm term).toRaw = Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.CwfMorphism.mapTerm term := rfl

/-! ## Executable normalization and the conversion-valued interpretation -/

def interpreted (term : Term Γ A) : FormationSensitiveContextual.TermFibre
    (FormationSensitiveContextual.QType.mk (simpleType (mapContext Γ) A)) :=
  FormationSensitiveContextual.TermFibre.mk (mapTerm term)

/-- Semantic equality is exactly beta conversion on this admitted image;
the unrestricted target conversion path is allowed to leave the image. -/
theorem interpreted_eq_iff (left right : Term Γ A) :
    interpreted left = interpreted right ↔ BetaConv left right :=
  (FormationSensitiveContextual.TermFibre.mk_eq_iff (mapTerm left) (mapTerm right)).trans
    (Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.ConversionDecision.towerConv_iff_betaConv left right)

theorem normalization_preserves_interpretation (term : Term Γ A) :
    interpreted (Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.Normalization.normalize term).normalForm = interpreted term :=
  (interpreted_eq_iff _ _).mpr (Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.Normalization.normalize_convert term).symm

/-- This uses the existing executable decision procedure, not an existence
statement about a supplied conversion certificate. -/
theorem decision_iff_interpreted_eq (left right : Term Γ A) :
    Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.ConversionDecision.decideConversion left right = true ↔
      interpreted left = interpreted right :=
  (Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.ConversionDecision.decideConversion_correct left right).trans
    (interpreted_eq_iff left right).symm

/-- The actual target substitution has the original translated source as
its input; the family is transported using the existing simple-type law. -/
theorem mapTerm_substitution (term : Term Γ A) (σ : Substitution Γ Δ) :
    ((mapTerm term).reindex (mapSubstitution σ)).cast
        (simpleType_reindex (mapSubstitution σ) A) =
      mapTerm (term.substitute σ) := by
  apply FormationSensitiveContextual.Term.ext
  rw [FormationSensitiveContextual.Term.cast_code]
  exact (eraseTerm_substitute σ term).symm

/-- Normalize, substitute, and normalize again: the result is the same
formed source term as substituting first and normalizing. New redexes from
the substitution are evaluated, not erased by an invalid strict law. -/
theorem normalize_substitution (term : Term Γ A) (σ : Substitution Γ Δ) :
    mapTerm (Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.Normalization.normalize
      ((Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.Normalization.normalize term).normalForm.substitute σ)).normalForm =
    mapTerm (Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.Normalization.normalize (term.substitute σ)).normalForm :=
  congrArg mapTerm (Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.ConversionDecision.normalize_substitute term σ)

namespace Controls

open Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.ConversionDecision

/-- The older function remains free underneath the argument's lambda. -/
def forwardedFunction {Γ : List Ty} :
    Term (.arr .atom .atom :: Γ) (.arr .atom .atom) :=
  .lam (.app (.var (.succ .zero)) (.var .zero))

/-- The nested closure used by the runtime contract, with `x` and `y`
represented by independent typed variables. -/
def nestedFunctionResult : Term [.atom, .atom] .atom :=
  .app
    (.app
      (.lam (.app (.lam FormationSensitiveSimpleFragment.Examples.twiceBody)
        forwardedFunction))
      (.lam (.var (.succ (.succ .zero)))))
    (.var .zero)

/-- Five actual beta steps suffice; the unused argument need not be
normalized to establish the captured result. -/
theorem nested_function_reduces :
    Relation.ReflTransGen BetaStep nestedFunctionResult (.var (.succ .zero)) := by
  refine .head (.appLeft (.beta _ _)) ?_
  refine .head (.appLeft (.beta _ _)) ?_
  refine .head (.beta _ _) ?_
  refine .head (.beta _ _) ?_
  exact .single (.beta _ _)

theorem nested_function_returns_older_value :
    Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.ConversionDecision.decideConversion nestedFunctionResult
      (.var (.succ .zero)) = true :=
  (decideConversion_correct _ _).mpr
    (Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.Normalization.steps_convert nested_function_reduces)

theorem nested_function_does_not_capture_argument :
    interpreted nestedFunctionResult ≠ interpreted (.var .zero) := by
  have result := (decision_iff_interpreted_eq _ _).mp nested_function_returns_older_value
  intro captures
  have equal := result.symm.trans captures
  have accepts := (decision_iff_interpreted_eq _ _).mpr equal.symm
  rw [rejects_distinct_variables] at accepts
  cases accepts

/-- Distinct intrinsic derivations discarded by erasure are still admitted
and agree in the formed conversion observation. This is positive evidence
for the actual normalization-based decision, not assumed extensionality. -/
theorem discarded_identities_observation :
    interpreted Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.ErasureBoundary.discardAtomicIdentity =
      interpreted Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.ErasureBoundary.discardFunctionIdentity :=
  (decision_iff_interpreted_eq _ _).mp accepts_discarded_identities

/-- Extensional eta agreement does not collapse the candidate's beta-only
conversion observation, even at an admitted function type. -/
theorem eta_observations_distinct : interpreted etaVariable ≠ interpreted etaExpansion :=
  fun equal => eta_not_betaConvertible ((interpreted_eq_iff _ _).mp equal)

theorem distinct_variables :
    interpreted (Term.var (Var.zero : Var [.atom, .atom] .atom)) ≠
      interpreted (Term.var (Var.succ Var.zero)) := by
  intro equal
  have accepted := (decision_iff_interpreted_eq _ _).mpr equal
  have refused := Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.ConversionDecision.rejects_distinct_variables
  rw [refused] at accepted
  cases accepted

end Controls

#print axioms strictMorphism
#print axioms interpreted_eq_iff
#print axioms decision_iff_interpreted_eq
#print axioms normalize_substitution
#print axioms Controls.discarded_identities_observation
#print axioms Controls.nested_function_reduces
#print axioms Controls.nested_function_returns_older_value
#print axioms Controls.nested_function_does_not_capture_argument
#print axioms Controls.eta_observations_distinct

end FormationSensitiveSimpleCwf
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
