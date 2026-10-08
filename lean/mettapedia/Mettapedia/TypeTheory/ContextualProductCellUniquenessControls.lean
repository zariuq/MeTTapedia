import Mettapedia.TypeTheory.ContextualProductCellUniqueness
import Mettapedia.TypeTheory.ContextualLogicalMorphismControls

/-!
# Complete product evaluation and its separate eta obligation

The positive profile has varying finite domains and codomains and an
actual noninjective type decoder. The negative profile adds a Boolean to
each complete function. Every local beta and strict substitution law holds,
yet flipping that Boolean is invisible to generic application and evaluation.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualProductCellUniquenessControls

open CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open ContextualTypeOperations ContextualPiEta ContextualProductCellUniqueness
open ContextualSumComprehensionControls (varyingDomain varyingCodomain)

theorem family_eta : PiEta Families.products.{0} Families.products_substitution.1 := by
  intro Γ A B function
  funext γ argument
  rfl

theorem supplied_evaluation_readout (n : Nat)
    (function : (argument : varyingDomain n) → varyingCodomain ⟨n, argument⟩)
    (argument : varyingDomain n) :
    evaluation Families.products Families.products_substitution.1
      varyingDomain varyingCodomain ⟨⟨n, function⟩, argument⟩ =
        ⟨⟨n, argument⟩, function argument⟩ := rfl

/-- Every complete candidate endomorphism satisfying the actual three
readings is detected on the genuinely varying product context. -/
theorem varying_complete_readings_detect (component argumentComponent)
    (base : (familiesCwf.{0}).compS
      ((familiesCwf.{0}).wk (Families.products.pi varyingDomain varyingCodomain)) component =
      (familiesCwf.{0}).wk (Families.products.pi varyingDomain varyingCodomain))
    (argumentBase : (familiesCwf.{0}).compS
      ((familiesCwf.{0}).wk ((familiesCwf.{0}).tySub varyingDomain
        ((familiesCwf.{0}).wk (Families.products.pi varyingDomain varyingCodomain)))) argumentComponent =
      (familiesCwf.{0}).compS component
        ((familiesCwf.{0}).wk ((familiesCwf.{0}).tySub varyingDomain
          ((familiesCwf.{0}).wk (Families.products.pi varyingDomain varyingCodomain)))))
    (argument : (familiesCwf.{0}).compS
      (TypeOver.extensionSubstitution
        ((familiesCwf.{0}).wk (Families.products.pi varyingDomain varyingCodomain)) varyingDomain)
      argumentComponent = TypeOver.extensionSubstitution
        ((familiesCwf.{0}).wk (Families.products.pi varyingDomain varyingCodomain)) varyingDomain)
    (evaluated : (familiesCwf.{0}).compS
      (evaluation Families.products Families.products_substitution.1 varyingDomain varyingCodomain)
      argumentComponent =
      evaluation Families.products Families.products_substitution.1 varyingDomain varyingCodomain) :
    component = (familiesCwf.{0}).idS _ :=
  evaluation_joint_cancel Families.products Families.products_substitution family_eta
    varyingDomain varyingCodomain component argumentComponent base argumentBase argument evaluated

theorem marked_formation : StrictPiFormationSubstitution
    (ContextualMarkedTypes.products Families.products.{0}) := by
  intro Γ Δ σ A B
  rfl

/-- The local identity propagation applies to the real type decoder,
including its supplied marked presentations and arbitrary natural cells. -/
theorem marked_product_component_forced
    (cell : ContextualLogicalMorphismControls.forget.toFamilyMorphism.base ⟶
      ContextualLogicalMorphismControls.forget.toFamilyMorphism.base)
    (baseFixed : cell.app ⟨Nat⟩ = 𝟙 _)
    (domainFixed : cell.app ⟨ContextualLogicalMorphismControls.sourceModel.toCwf.ext
      Nat ContextualLogicalMorphismControls.A⟩ = 𝟙 _)
    (codomainFixed : cell.app ⟨ContextualLogicalMorphismControls.sourceModel.toCwf.ext
      (ContextualLogicalMorphismControls.sourceModel.toCwf.ext
        Nat ContextualLogicalMorphismControls.A) ContextualLogicalMorphismControls.B⟩ = 𝟙 _) :
    cell.app ⟨ContextualLogicalMorphismControls.sourceModel.toCwf.ext Nat
      ((ContextualMarkedTypes.products Families.products).pi
        ContextualLogicalMorphismControls.A ContextualLogicalMorphismControls.B)⟩ = 𝟙 _ :=
  product_fixed ContextualLogicalMorphismControls.forget cell
    (ContextualMarkedTypes.products Families.products) Families.products marked_formation
    Families.products_substitution family_eta ContextualLogicalMorphismControls.local_products_preserved
    ContextualLogicalMorphismControls.A ContextualLogicalMorphismControls.B
    baseFixed domainFixed codomainFixed

theorem marked_decoder_has_actual_collision :
    (⟨varyingDomain, true⟩ : ContextualLogicalMorphismControls.sourceModel.toCwf.Ty Nat) ≠
      ⟨varyingDomain, false⟩ ∧
    ContextualLogicalMorphismControls.forget.toFamilyMorphism.mapType
      (⟨varyingDomain, true⟩ : ContextualLogicalMorphismControls.sourceModel.toCwf.Ty Nat) =
    ContextualLogicalMorphismControls.forget.toFamilyMorphism.mapType
      (⟨varyingDomain, false⟩ : ContextualLogicalMorphismControls.sourceModel.toCwf.Ty Nat) :=
  ContextualLogicalMorphismControls.presentation_collision

def hiddenProducts : PiOperations (familiesCwf.{0}) where
  pi A B γ := ((argument : A γ) → B ⟨γ, argument⟩) × Bool
  lam body γ := (fun argument => body ⟨γ, argument⟩, false)
  app function argument γ := (function γ).1 (argument γ)

theorem hidden_beta : PiBeta hiddenProducts := fun _ _ => rfl

theorem hidden_substitution : StrictPiSubstitution hiddenProducts := by
  refine ⟨?_, ?_, ?_⟩
  · intro Γ Δ σ A B
    rfl
  · intro Γ Δ σ A B body
    rfl
  · intro Γ Δ σ A B function argument reindexed same
    cases eq_of_heq same
    rfl

def suppliedHidden (mark : Bool) :
    (familiesCwf.{0}).Tm Nat (hiddenProducts.pi varyingDomain varyingCodomain) :=
  fun n => (fun _ => ⟨n, by change n < n + _ + 1; omega⟩, mark)

theorem hidden_functions_differ : suppliedHidden false ≠ suppliedHidden true := by
  intro same
  exact Bool.noConfusion (congrArg (fun function => (function 0).2) same)

theorem hidden_generic_application_agrees :
    genericSection hiddenProducts hidden_substitution.1 (suppliedHidden false) =
      genericSection hiddenProducts hidden_substitution.1 (suppliedHidden true) := by
  funext point
  rfl

theorem hidden_eta_fails : ¬ PiEta hiddenProducts hidden_substitution.1 := by
  intro eta
  exact Bool.noConfusion (congrArg (fun function => (function 0).2) (eta (suppliedHidden true)))

abbrev hiddenContext := (familiesCwf.{0}).ext Nat
  (hiddenProducts.pi varyingDomain varyingCodomain)

abbrev hiddenArgumentContext := (familiesCwf.{0}).ext hiddenContext
  ((familiesCwf.{0}).tySub varyingDomain
    ((familiesCwf.{0}).wk (hiddenProducts.pi varyingDomain varyingCodomain)))

def hiddenFlip (point : hiddenContext) : hiddenContext :=
  ⟨point.1, (point.2.1, !point.2.2)⟩

def hiddenArgumentFlip (point : hiddenArgumentContext) : hiddenArgumentContext :=
  ⟨hiddenFlip point.1, point.2⟩

/-- The full actual evaluator ignores the hidden Boolean, even though its
context endomorphism and every supplied argument are inhabited. -/
theorem hidden_all_readouts_hold :
    (familiesCwf.{0}).compS
      ((familiesCwf.{0}).wk (hiddenProducts.pi varyingDomain varyingCodomain)) hiddenFlip =
      (familiesCwf.{0}).wk (hiddenProducts.pi varyingDomain varyingCodomain) ∧
    (familiesCwf.{0}).compS
      ((familiesCwf.{0}).wk ((familiesCwf.{0}).tySub varyingDomain
        ((familiesCwf.{0}).wk (hiddenProducts.pi varyingDomain varyingCodomain)))) hiddenArgumentFlip =
      (familiesCwf.{0}).compS hiddenFlip
        ((familiesCwf.{0}).wk ((familiesCwf.{0}).tySub varyingDomain
          ((familiesCwf.{0}).wk (hiddenProducts.pi varyingDomain varyingCodomain)))) ∧
    (familiesCwf.{0}).compS (TypeOver.extensionSubstitution
      ((familiesCwf.{0}).wk (hiddenProducts.pi varyingDomain varyingCodomain)) varyingDomain)
      hiddenArgumentFlip = TypeOver.extensionSubstitution
        ((familiesCwf.{0}).wk (hiddenProducts.pi varyingDomain varyingCodomain)) varyingDomain ∧
    (familiesCwf.{0}).compS
      (evaluation hiddenProducts hidden_substitution.1 varyingDomain varyingCodomain) hiddenArgumentFlip =
      evaluation hiddenProducts hidden_substitution.1 varyingDomain varyingCodomain :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem hidden_component_is_not_identity : hiddenFlip ≠ (familiesCwf.{0}).idS hiddenContext := by
  intro same
  have marks := congrArg (fun component => (component ⟨0, suppliedHidden true 0⟩).2.2) same
  exact Bool.noConfusion marks

end Mettapedia.TypeTheory.ContextualProductCellUniquenessControls
