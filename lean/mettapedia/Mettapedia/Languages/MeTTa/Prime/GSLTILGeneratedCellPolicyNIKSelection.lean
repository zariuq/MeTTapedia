import Mettapedia.GSLT.LanguageDef.GSLTILGeneratedCellReflection
import Mettapedia.Languages.MeTTa.Prime.NIKPolicyFamilyCapabilitySelection

/-!
# Observation-relative NIK selection for generated GSLT-IL cells

Reflection of complete proof history and support for a declared observation
family are related but not identical capabilities.

* A split primitive-generator interpretation reconstructs every complete
  source cell, so it supports every dependent policy family over that cell
  fibre.
* Any structural interpretation supports policies that depend only on
  constructor shape, even when it intentionally identifies primitive
  receipts.
* A primitive collision excludes the interpretation from every request whose
  policy family distinguishes those receipts.

This is the observation-relative form of maximal-native selection.  A lossy
face is neither globally accepted nor globally rejected: it remains eligible
exactly for policy requests proved insensitive to its loss.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Prime.GSLTILGeneratedCellPolicyNIKSelection

open Mettapedia.GSLT.Core
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.GSLT.Ultrainfinite.GeneratedTwoCellReflection
open Mettapedia.GSLT.LanguageDef.MaximalNativeCalculus
open Mettapedia.Languages.MeTTa.Prime.NIKPolicyFamilyCapabilitySelection

universe uObject uStep uSourceGenerator uTargetGenerator uPolicy uResult

variable {Object : Type uObject}
variable {Step : Object → Object → Type uStep}
variable {SourceGenerator : {source target : Object} →
  Route Step source target → Route Step source target →
    Type uSourceGenerator}
variable {TargetGenerator : {source target : Object} →
  Route Step source target → Route Step source target →
    Type uTargetGenerator}

/-! ## Policy support earned from cell reflection -/

/-- A split generator face supplies executable runners for every dependent
policy family on one complete source-cell fibre. -/
def realizationOfGeneratorRetraction
    (retraction : GeneratorRetraction
      Step SourceGenerator TargetGenerator)
    {source target : Object} {first second : Route Step source target}
    (family : PolicyFamily.{_, uPolicy, uResult}
      (GeneratedTwoCell SourceGenerator first second)) :
    family.ReadoutRealization
      (mapGenerators retraction.forward :
        GeneratedTwoCell SourceGenerator first second →
          GeneratedTwoCell TargetGenerator first second) where
  run := fun policy targetCell =>
    family.decide policy
      (mapGenerators retraction.backward targetCell)
  agrees := by
    intro policy cell
    exact congrArg (family.decide policy) (retraction.retract_map cell)

/-- Consequently every policy family is supported by a split complete-cell
readout. -/
theorem supportsEveryFamily_of_generatorRetraction
    (retraction : GeneratorRetraction
      Step SourceGenerator TargetGenerator)
    {source target : Object} {first second : Route Step source target}
    (family : PolicyFamily.{_, uPolicy, uResult}
      (GeneratedTwoCell SourceGenerator first second)) :
    family.SupportsReadout
      (mapGenerators retraction.forward :
        GeneratedTwoCell SourceGenerator first second →
          GeneratedTwoCell TargetGenerator first second) :=
  ⟨realizationOfGeneratorRetraction retraction family⟩

/-- A policy that distinguishes two collided primitive receipts excludes that
face from the corresponding policy request. -/
theorem not_supportsFamily_of_generator_collision
    (onGenerator : ∀ {source target} {first second : Route Step source target},
      SourceGenerator first second → TargetGenerator first second)
    {source target : Object} {first second : Route Step source target}
    {left right : SourceGenerator first second}
    (collision : onGenerator left = onGenerator right)
    (family : PolicyFamily.{_, uPolicy, uResult}
      (GeneratedTwoCell SourceGenerator first second))
    (policy : family.Policy)
    (differentDecision :
      family.decide policy
          (GeneratedTwoCell.generator (Generator := SourceGenerator) left) ≠
        family.decide policy
          (GeneratedTwoCell.generator (Generator := SourceGenerator) right)) :
    ¬ family.SupportsReadout
      (mapGenerators onGenerator :
        GeneratedTwoCell SourceGenerator first second →
          GeneratedTwoCell TargetGenerator first second) := by
  have sameReadout :
      mapGenerators onGenerator
          (GeneratedTwoCell.generator (Generator := SourceGenerator) left) =
        mapGenerators onGenerator
          (GeneratedTwoCell.generator (Generator := SourceGenerator) right) := by
    rw [mapGenerators_generator, mapGenerators_generator, collision]
  exact family.not_supportsReadout_of_policy_collision
    (mapGenerators onGenerator) sameReadout policy differentDecision

/-! ## A nontrivial policy supported by every structural cell map -/

/-- Number of retained raw cell constructors.  It observes structural history
but deliberately ignores the identity of primitive generator evidence. -/
def constructorCount
    {Generator : {source target : Object} →
      Route Step source target → Route Step source target → Type*} :
    {source target : Object} → {first second : Route Step source target} →
      GeneratedTwoCell Generator first second → Nat
  | _, _, _, _, .refl _ => 1
  | _, _, _, _, .generator _ => 1
  | _, _, _, _, .vertical earlier later =>
      constructorCount earlier + constructorCount later + 1
  | _, _, _, _, .whiskerLeft _ cell => constructorCount cell + 1
  | _, _, _, _, .whiskerRight _ cell => constructorCount cell + 1

/-- Structural generator mapping preserves constructor count without needing
reflection of generator identity. -/
@[simp] theorem constructorCount_mapGenerators
    (onGenerator : ∀ {source target} {first second : Route Step source target},
      SourceGenerator first second → TargetGenerator first second)
    {source target : Object} {first second : Route Step source target}
    (cell : GeneratedTwoCell SourceGenerator first second) :
    constructorCount (mapGenerators onGenerator cell) =
      constructorCount cell := by
  induction cell with
  | refl => rfl
  | generator => rfl
  | vertical earlier later earlierIH laterIH =>
      simp only [mapGenerators, constructorCount,
        earlierIH, laterIH]
  | whiskerLeft prior cell cellIH =>
      simp only [mapGenerators, constructorCount, cellIH]
  | whiskerRight suffix cell cellIH =>
      simp only [mapGenerators, constructorCount, cellIH]

inductive StructuralPolicy where
  | constructorCount
deriving DecidableEq

/-- The one-policy family observing structural constructor count. -/
def structuralFamily
    {source target : Object} {first second : Route Step source target} :
    PolicyFamily (GeneratedTwoCell SourceGenerator first second) where
  Policy := StructuralPolicy
  Result := fun _ => Nat
  decide := fun _ => constructorCount

/-- Every structural generator interpretation supports constructor count,
including interpretations that collide primitive receipts. -/
def structuralRealization
    (onGenerator : ∀ {source target} {first second : Route Step source target},
      SourceGenerator first second → TargetGenerator first second)
    {source target : Object} {first second : Route Step source target} :
    (structuralFamily
      (SourceGenerator := SourceGenerator)
      (first := first) (second := second)).ReadoutRealization
      (mapGenerators onGenerator :
        GeneratedTwoCell SourceGenerator first second →
          GeneratedTwoCell TargetGenerator first second) where
  run := fun _ targetCell => constructorCount targetCell
  agrees := fun _ cell => constructorCount_mapGenerators onGenerator cell

theorem structuralFamily_supported
    (onGenerator : ∀ {source target} {first second : Route Step source target},
      SourceGenerator first second → TargetGenerator first second)
    {source target : Object} {first second : Route Step source target} :
    (structuralFamily
      (SourceGenerator := SourceGenerator)
      (first := first) (second := second)).SupportsReadout
      (mapGenerators onGenerator :
        GeneratedTwoCell SourceGenerator first second →
          GeneratedTwoCell TargetGenerator first second) :=
  ⟨structuralRealization onGenerator⟩

/-! ## Observation-relative collision canary -/

namespace Canary

open Mettapedia.GSLT.Ultrainfinite.GeneratedTwoCellUniversal.Canary
open Mettapedia.GSLT.Ultrainfinite.GeneratedTwoCellReflection.Canary

abbrev SourceCell :=
  GeneratedTwoCell DuplicateOptimizationGenerator detourRoute directRoute

abbrev TargetCell :=
  GeneratedTwoCell OptimizationGenerator detourRoute directRoute

/-- The proof-sensitive readout recognizes the first authored receipt while
retaining all other cell shapes as the negative case. -/
def isFirstReceipt : SourceCell → Bool
  | .generator .first => true
  | _ => false

inductive Policy where
  | shape
  | receipt
deriving DecidableEq

/-- A heterogeneous family combining a structural statistic and an authored
receipt-sensitive answer. -/
def policies : PolicyFamily SourceCell where
  Policy := Policy
  Result := fun
    | .shape => Nat
    | .receipt => Bool
  decide := fun
    | .shape => constructorCount
    | .receipt => isFirstReceipt

inductive ShapeRequest where
  | shape
deriving DecidableEq

def shapeFamily : PolicyFamily SourceCell :=
  policies.reindex (fun _ : ShapeRequest => Policy.shape)

/-- The colliding face remains useful for the structural request. -/
theorem collapsed_supports_shapeFamily :
    shapeFamily.SupportsReadout
      (mapGenerators collapseDuplicate :
        SourceCell → TargetCell) := by
  refine ⟨{
    run := fun _ targetCell => constructorCount targetCell
    agrees := ?_ }⟩
  intro policy cell
  cases policy
  exact constructorCount_mapGenerators collapseDuplicate cell

/-- The same face is inadmissible for the full family because it identifies
the two authored receipts that the receipt policy distinguishes. -/
theorem collapsed_refuses_fullPolicyFamily :
    ¬ policies.SupportsReadout
      (mapGenerators collapseDuplicate :
        SourceCell → TargetCell) := by
  exact not_supportsFamily_of_generator_collision
    (Object := Node)
    (Step := Edge)
    (SourceGenerator := DuplicateOptimizationGenerator)
    (TargetGenerator := OptimizationGenerator)
    collapseDuplicate
    (left := DuplicateOptimizationGenerator.first)
    (right := DuplicateOptimizationGenerator.second)
    rfl policies Policy.receipt (by
      simp [policies, isFirstReceipt])

def identityRetraction :
    GeneratorRetraction Edge
      DuplicateOptimizationGenerator DuplicateOptimizationGenerator where
  forward := fun evidence => evidence
  backward := fun evidence => evidence
  leftInverse := by
    intro source target first second evidence
    rfl

/-- Retaining the complete cell supports both the structural and
receipt-sensitive policies. -/
theorem retained_supports_fullPolicyFamily :
    policies.SupportsReadout
      (mapGenerators identityRetraction.forward :
        SourceCell → SourceCell) :=
  supportsEveryFamily_of_generatorRetraction identityRetraction policies

/-- Loss is judged relative to the declared consumer family: the collapsed
face is accepted for shape and refused for receipt-sensitive use, while the
retained face supports both. -/
theorem lossiness_is_policy_relative :
    shapeFamily.SupportsReadout
        (mapGenerators collapseDuplicate :
          SourceCell → TargetCell) ∧
      ¬ policies.SupportsReadout
        (mapGenerators collapseDuplicate :
          SourceCell → TargetCell) ∧
      policies.SupportsReadout
        (mapGenerators identityRetraction.forward :
          SourceCell → SourceCell) :=
  ⟨collapsed_supports_shapeFamily,
    collapsed_refuses_fullPolicyFamily,
    retained_supports_fullPolicyFamily⟩

/-! ## The same distinction as an exact NIK capability request -/

/-- A common result carrier lets NIK compare a collapsed structural face and
the complete proof-relevant face inside one semantic request fibre. -/
abbrev CellReadout := TargetCell ⊕ SourceCell

def sourceObject : AdmissionObject where
  Carrier := SourceCell
  Meaning := fun cell => 0 < constructorCount cell

def readoutObject : AdmissionObject where
  Carrier := CellReadout
  Meaning := fun
    | .inl cell => 0 < constructorCount cell
    | .inr cell => 0 < constructorCount cell

def collapsedOperation : sourceObject ⟶ readoutObject where
  run := fun cell => Sum.inl (mapGenerators collapseDuplicate cell)
  preserves := by
    intro cell meaningful
    change 0 < constructorCount (mapGenerators collapseDuplicate cell)
    rw [constructorCount_mapGenerators]
    exact meaningful

def retainedOperation : sourceObject ⟶ readoutObject where
  run := Sum.inr
  preserves := fun _ meaningful => meaningful

inductive CellCapability where
  | structural
  | receiptIdentity
deriving DecidableEq

def nativeSupports (index : Fin 2) : CellCapability → Prop
  | .structural => True
  | .receiptIdentity => index = 1

/-- The retained face is strictly above the collapsed face because it exposes
one more native capability.  Both operations are already admitted semantic
arrows before selection. -/
def cellFamily :
    RecognizedFamily (Fin 2) sourceObject readoutObject where
  package
    | ⟨0, _⟩ => collapsedOperation
    | ⟨1, _⟩ => retainedOperation
  Capability := CellCapability
  supports := nativeSupports
  supports_mono := by
    intro weaker stronger related capability supported
    fin_cases weaker <;> fin_cases stronger <;> cases capability <;>
      simp [nativeSupports] at related supported ⊢
  strict_support_gain := by
    intro weaker stronger strict
    fin_cases weaker <;> fin_cases stronger
    · simp at strict
    · exact ⟨.receiptIdentity, by simp [nativeSupports], by
        simp [nativeSupports]⟩
    · simp at strict
    · simp at strict
  recognized := Finset.univ
  licensed := Finset.univ
  licensed_subset_recognized := Finset.Subset.rfl
  licensed_nonempty := Finset.univ_nonempty

def cellReadout : Fin 2 → SourceCell → CellReadout
  | ⟨0, _⟩ => collapsedOperation.run
  | ⟨1, _⟩ => retainedOperation.run

/-- Shape is supported by both faces; receipt identity only by the complete
face. -/
def cellSupports (index : Fin 2) (policy : Policy) : Prop :=
  policy = .shape ∨ index = 1

def cellRunner (index : Fin 2) (policy : Policy)
    (_support : cellSupports index policy) :
    CellReadout → policies.Result policy :=
  match policy with
  | .shape => fun
      | .inl cell => constructorCount cell
      | .inr cell => constructorCount cell
  | .receipt => fun
      | .inl _ => false
      | .inr cell => isFirstReceipt cell

theorem cellRunner_agrees (index : Fin 2) (policy : Policy)
    (support : cellSupports index policy) (cell : SourceCell) :
    cellRunner index policy support (cellReadout index cell) =
      policies.decide policy cell := by
  fin_cases index <;> cases policy
  · exact constructorCount_mapGenerators collapseDuplicate cell
  · simp [cellSupports] at support
  · rfl
  · rfl

theorem cellSupports_mono {weaker stronger : Fin 2}
    (related : weaker ≤ stronger) (policy : Policy)
    (supported : cellSupports weaker policy) :
    cellSupports stronger policy := by
  fin_cases weaker <;> fin_cases stronger <;> cases policy <;>
    simp [cellSupports] at related supported ⊢

def cellCatalog : PolicyReadoutCatalog (Fin 2) SourceCell policies where
  Key := fun _ => CellReadout
  readout := cellReadout
  Supports := cellSupports
  runner := cellRunner
  agrees := cellRunner_agrees
  supports_mono := cellSupports_mono

/-- Before an observation request is declared, both admitted faces remain
eligible. -/
def neutralNativeRequest : cellFamily.CapabilityRequest where
  required := ∅
  candidates := Finset.univ
  candidates_exact := by
    intro candidate
    constructor
    · intro _member
      refine ⟨by simp [cellFamily], ?_⟩
      intro capability required
      simp at required
    · intro _data
      simp
  candidates_nonempty := Finset.univ_nonempty

/-- A structural request retains both native faces. -/
def shapeRequest :
    PolicyCapabilityRequest cellCatalog neutralNativeRequest where
  requiredPolicies := {Policy.shape}
  candidates := Finset.univ
  candidates_exact := by
    intro candidate
    constructor
    · intro _member
      refine ⟨by simp [neutralNativeRequest], ?_⟩
      intro policy required
      change cellSupports candidate policy
      left
      exact Set.mem_singleton_iff.mp required
    · intro _data
      simp
  candidates_nonempty := Finset.univ_nonempty

/-- A receipt-sensitive request cuts the exact fibre down to the complete
proof-relevant face. -/
def receiptRequest :
    PolicyCapabilityRequest cellCatalog neutralNativeRequest where
  requiredPolicies := {Policy.receipt}
  candidates := {(1 : Fin 2)}
  candidates_exact := by
    intro candidate
    fin_cases candidate
    · constructor
      · intro impossible
        simp at impossible
      · rintro ⟨_nativeMember, supportsReceipt⟩
        have supported := supportsReceipt Policy.receipt (by rfl)
        simp [cellCatalog, cellSupports] at supported
    · constructor
      · intro _member
        refine ⟨by simp [neutralNativeRequest], ?_⟩
        intro policy _required
        change cellSupports (1 : Fin 2) policy
        exact Or.inr rfl
      · intro _data
        simp
  candidates_nonempty := by simp

theorem collapsed_is_shape_candidate :
    (0 : Fin 2) ∈ shapeRequest.candidates := by simp [shapeRequest]

theorem collapsed_is_not_receipt_candidate :
    (0 : Fin 2) ∉ receiptRequest.candidates := by simp [receiptRequest]

theorem retained_is_receipt_candidate :
    (1 : Fin 2) ∈ receiptRequest.candidates := by simp [receiptRequest]

/-- The receipt request has the complete face as its strongest native
realization. -/
def receiptSelection :
    receiptRequest.toCapabilityRequest.StrongestNativeCalculusPrinciple :=
  ⟨(1 : Fin 2), by
    constructor
    · simp [RecognizedFamily.CapabilityRequest.restrictedFamily,
        PolicyCapabilityRequest.toCapabilityRequest, receiptRequest]
    · intro candidate candidateMember
      fin_cases candidate
      · simp [RecognizedFamily.CapabilityRequest.restrictedFamily,
          PolicyCapabilityRequest.toCapabilityRequest,
          receiptRequest] at candidateMember
      · exact le_rfl⟩

/-- NIK selection retains an executable realization of the exact requested
dependent policy vector. -/
theorem selected_receipt_refines_requestedVector :
    NonFactorization.Factors
      (cellCatalog.readout receiptSelection.1)
      receiptRequest.requestedFamily.vector :=
  (receiptRequest.strongestRealization receiptSelection).vectorFactors

/-- Selection executes the originally admitted complete operation; it does
not insert a checker or reconstruct erased receipt identity. -/
theorem selected_receipt_operation_is_retained (cell : SourceCell) :
    (receiptRequest.toCapabilityRequest.strongestOperation
        receiptSelection).run cell = Sum.inr cell :=
  rfl

end Canary

/-! ## Axiom audit -/

#print axioms realizationOfGeneratorRetraction
#print axioms supportsEveryFamily_of_generatorRetraction
#print axioms not_supportsFamily_of_generator_collision
#print axioms constructorCount_mapGenerators
#print axioms structuralFamily_supported
#print axioms Canary.collapsed_supports_shapeFamily
#print axioms Canary.collapsed_refuses_fullPolicyFamily
#print axioms Canary.retained_supports_fullPolicyFamily
#print axioms Canary.lossiness_is_policy_relative
#print axioms Canary.cellRunner_agrees
#print axioms Canary.receiptRequest
#print axioms Canary.selected_receipt_refines_requestedVector
#print axioms Canary.selected_receipt_operation_is_retained

end Mettapedia.Languages.MeTTa.Prime.GSLTILGeneratedCellPolicyNIKSelection
