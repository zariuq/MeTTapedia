import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mettapedia.TypeTheory.CwfTarskiUniverse
import Mettapedia.TypeTheory.ExactCodeModalityModel
import Mettapedia.TypeTheory.ModalCwfFibre

/-!
# A common dependent and exact-code model, with its universe boundary

The exact-code multimodal families model has an ordinary dependent CwF at
its unique mode.  That one semantic object jointly supports dependent
products, dependent sums, contextual identity elimination, a
substitution-stable finite Tarski universe, and nonidentity quotation and
splicing with beta and eta.

The finite universe is not closed under dependent products: its only codes
decode to the empty, unit, and Boolean types, whereas the Boolean function
space has four elements.  This negative theorem is important.  It prevents
the compatibility witness from being misread as a model of a cumulative or
Pi/Sigma-closed universe hierarchy.

The module compares semantic capabilities.  It does not select a calculus,
an equality policy, a conversion algorithm, or a product language.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DependentExactCodeCommonModel

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.ContextualProductComparison
open Mettapedia.TypeTheory.ContextualSumComparison
open Mettapedia.TypeTheory.ContextualIdentityTypes
open Mettapedia.TypeTheory.CwfTarskiUniverse
open Mettapedia.TypeTheory.ContextualCode
open Mettapedia.TypeTheory.ExactCodeModalityModel

/-- The ordinary contextual theory visible at the exact-code model's mode. -/
abbrev ordinaryCwf : Cwf.{1, 0, 1, 0} :=
  ModalCwfFibre.fibreCwf cwf laws coherence ()

/-- Forgetting the modalities leaves precisely the ordinary set-families
CwF at the same universe level. -/
theorem ordinaryCwf_is_setFamilies : ordinaryCwf = familiesCwf.{0} :=
  rfl

/-- The finite Tarski universe inherited from the modal model. -/
def finiteTarski : TarskiUniverse ordinaryCwf where
  univ := fun context => cwf.univ (mode := ()) context
  el := fun code => cwf.el (mode := ()) code

/-- Its decoding operation commutes with ordinary contextual substitution. -/
def finiteTarskiSubstitutionStable : finiteTarski.SubstitutionStable where
  univ_sub _ := rfl
  el_sub _ _ := rfl

/-- All listed capabilities inhabit one semantic object.  In particular,
the code component is not an identity modality: its one-step arrow and
grade are nonzero and quotation changes representation. -/
structure SupportedCapabilities where
  products : DependentProductBeta ordinaryCwf
  sums : DependentSumBeta ordinaryCwf
  identityFormation : IdentityFormation ordinaryCwf
  identityReflexivity : IdentityReflexivity ordinaryCwf identityFormation
  identityElimination :
    IdentityEliminationBeta ordinaryCwf identityFormation identityReflexivity
  tarski : TarskiUniverse ordinaryCwf
  tarskiStable : tarski.SubstitutionStable
  codeBeta : SelectedQuoteSpliceBeta modes cwf laws
    selected quotation splicing
  codeEta : SelectedQuoteSpliceEta modes cwf laws
    selected quotation splicing
  codeArrowNonidentity : oneStep ≠ modes.id ()
  codeGradeNonzero : grading.gradeOf oneStep ≠ grading.unit

/-- The concrete compatibility witness. -/
def supportedCapabilities : SupportedCapabilities where
  products := familiesProducts
  sums := familiesSums
  identityFormation := Families.identityFormation
  identityReflexivity := Families.identityReflexivity
  identityElimination := Families.identityElimination
  tarski := finiteTarski
  tarskiStable := finiteTarskiSubstitutionStable
  codeBeta := beta
  codeEta := eta
  codeArrowNonidentity := oneStep_not_identity
  codeGradeNonzero := oneStep_grade_nonzero

/-! ## The finite-universe obstruction -/

def unitContext : ordinaryCwf.Ctx := PUnit

def boolCode : ordinaryCwf.Tm unitContext (finiteTarski.univ unitContext) :=
  fun _ => SmallCode.bool

def constantBoolCode : ordinaryCwf.Tm
    (ordinaryCwf.ext unitContext (finiteTarski.el boolCode))
  (finiteTarski.univ
      (ordinaryCwf.ext unitContext (finiteTarski.el boolCode))) :=
  fun _ => SmallCode.bool

/-- No code in the finite universe decodes to the Boolean function space. -/
theorem no_code_decodes_bool_function
    (code : SmallCode) :
    SmallCode.decode code ≠ (Bool → Bool) := by
  intro sameType
  cases code with
  | empty =>
      change Empty = (Bool → Bool) at sameType
      have sameCardinality := Fintype.card_congr' sameType
      norm_num at sameCardinality
  | unit =>
      change PUnit = (Bool → Bool) at sameType
      have sameCardinality := Fintype.card_congr' sameType
      norm_num at sameCardinality
  | bool =>
      change Bool = (Bool → Bool) at sameType
      have sameCardinality := Fintype.card_congr' sameType
      norm_num at sameCardinality

/-- No code in the finite universe decodes to the Boolean dependent pair. -/
theorem no_code_decodes_bool_sigma
    (code : SmallCode) :
    SmallCode.decode code ≠ (Sigma fun _ : Bool => Bool) := by
  intro sameType
  cases code with
  | empty =>
      change Empty = (Sigma fun _ : Bool => Bool) at sameType
      have sameCardinality := Fintype.card_congr' sameType
      norm_num at sameCardinality
  | unit =>
      change PUnit = (Sigma fun _ : Bool => Bool) at sameType
      have sameCardinality := Fintype.card_congr' sameType
      norm_num at sameCardinality
  | bool =>
      change Bool = (Sigma fun _ : Bool => Bool) at sameType
      have sameCardinality := Fintype.card_congr' sameType
      norm_num at sameCardinality

/-- The selected finite Tarski universe is not strictly closed under the
ambient dependent-product operation. -/
theorem finiteTarski_not_piClosed :
    ¬ Nonempty (finiteTarski.PiClosed familiesProducts) := by
  rintro ⟨closed⟩
  have decodedProduct := congrFun
    (closed.el_piCode boolCode constantBoolCode) PUnit.unit
  exact no_code_decodes_bool_function
    (closed.piCode boolCode constantBoolCode PUnit.unit) decodedProduct

/-- The same finite universe is not strictly closed under the ambient
dependent-sum operation. -/
theorem finiteTarski_not_sigmaClosed :
    ¬ Nonempty (finiteTarski.SigmaClosed familiesSums) := by
  rintro ⟨closed⟩
  have decodedSum := congrFun
    (closed.el_sigmaCode boolCode constantBoolCode) PUnit.unit
  exact no_code_decodes_bool_sigma
    (closed.sigmaCode boolCode constantBoolCode PUnit.unit) decodedSum

/-- Positive and negative boundaries for the same model: dependency,
identity elimination, exact code, and a stable finite universe coexist, but
Pi-closed universe structure does not follow. -/
theorem exact_supported_bundle_and_strict_universe_boundary :
    Nonempty SupportedCapabilities ∧
      ¬ Nonempty (finiteTarski.PiClosed familiesProducts) ∧
      ¬ Nonempty (finiteTarski.SigmaClosed familiesSums) :=
  ⟨⟨supportedCapabilities⟩, finiteTarski_not_piClosed,
    finiteTarski_not_sigmaClosed⟩

#print axioms ordinaryCwf_is_setFamilies
#print axioms finiteTarskiSubstitutionStable
#print axioms supportedCapabilities
#print axioms no_code_decodes_bool_function
#print axioms no_code_decodes_bool_sigma
#print axioms finiteTarski_not_piClosed
#print axioms finiteTarski_not_sigmaClosed
#print axioms exact_supported_bundle_and_strict_universe_boundary

end Mettapedia.TypeTheory.DependentExactCodeCommonModel
