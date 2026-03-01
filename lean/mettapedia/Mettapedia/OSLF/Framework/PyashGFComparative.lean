import Mettapedia.OSLF.Framework.PyashGF
import Mettapedia.OSLF.Framework.PyashGFInventory
import Mettapedia.OSLF.Framework.PyashGFEnglishFragment

/-!
# Pyash vs English Comparative Claims (Focused GF Corpus)

Focused comparative claims over the current PyashGF bridge and lexical inventories.
These are lightweight theorem-level claims intended for canary-level regression checks.
-/

namespace Mettapedia.OSLF.Framework.PyashGFComparative

open Mettapedia.OSLF.Framework.PyashGF
open Mettapedia.OSLF.Framework.PyashGFInventory
open Mettapedia.OSLF.Framework.PyashGFEnglishFragment

/-- Comparative advantage claim: Pyash has explicit `def` mood lexicalization
    in the observed be-word inventory, while English-head inventory does not. -/
def pyashDefMoodLexicalAdvantage : Prop :=
  pyashBeWordInventory.contains "def" = true ∧
    pyashEnglishHeadInventory.contains "def" = false

theorem pyashDefMoodLexicalAdvantage_true : pyashDefMoodLexicalAdvantage := by
  show pyashBeWordInventory.contains "def" = true ∧
    pyashEnglishHeadInventory.contains "def" = false
  decide

/-- Comparative advantage claim: the focused Pyash GF bridge is deterministic
    as a partial function from GF clause nodes to OSLF states. -/
def pyashClauseMappingDeterministic : Prop :=
  ∀ clause s₁ s₂,
    pyashGFClauseToState? clause = some s₁ →
    pyashGFClauseToState? clause = some s₂ →
    s₁ = s₂

theorem pyashClauseMappingDeterministic_true : pyashClauseMappingDeterministic := by
  intro clause s₁ s₂ h₁ h₂
  simpa [h₁] using h₂

/-- Comparative weaker-path claim: English-head inventory currently carries an
    explicit copula head (`be`) that is not present in the Pyash be-word list. -/
def pyashCopulaHeadWeakerPath : Prop :=
  pyashEnglishHeadInventory.contains "be" = true ∧
    pyashBeWordInventory.contains "be" = false

theorem pyashCopulaHeadWeakerPath_true : pyashCopulaHeadWeakerPath := by
  show pyashEnglishHeadInventory.contains "be" = true ∧
    pyashBeWordInventory.contains "be" = false
  decide

/-- Executable boolean canary for `def`-mood lexical advantage. -/
def pyashDefMoodLexicalAdvantageBool : Bool :=
  pyashBeWordInventory.contains "def" && !(pyashEnglishHeadInventory.contains "def")

theorem pyashDefMoodLexicalAdvantageBool_true :
    pyashDefMoodLexicalAdvantageBool = true := by
  decide

/-- Executable boolean canary for deterministic clause mapping.
    The proposition itself is proved in `pyashClauseMappingDeterministic_true`. -/
def pyashClauseMappingDeterministicBool : Bool := true

theorem pyashClauseMappingDeterministicBool_true :
    pyashClauseMappingDeterministicBool = true := by
  rfl

/-- Executable boolean canary for explicit copula weaker-path claim. -/
def pyashCopulaHeadWeakerPathBool : Bool :=
  pyashEnglishHeadInventory.contains "be" && !(pyashBeWordInventory.contains "be")

theorem pyashCopulaHeadWeakerPathBool_true :
    pyashCopulaHeadWeakerPathBool = true := by
  decide

/-- Executable canary for controlled-English WDF semantic coverage bundle. -/
def pyashEnglishWDFSemanticCoverageBool : Bool :=
  pyashEnglishSemanticCoverageCanaries.all (fun row => row.2)

theorem pyashEnglishWDFSemanticCoverageBool_true :
    pyashEnglishWDFSemanticCoverageBool = true := by
  simpa [pyashEnglishWDFSemanticCoverageBool] using
    pyashEnglishSemanticCoverageCanaries_all_true

/-- The semantic English inventory supports every clause in the controlled WDF list. -/
def pyashEnglishSemanticInventorySupportsAllClauses : Prop :=
  ∀ c ∈ pyashEnglishWDFAll,
    ∃ mood head,
      head ∈ pyashEnglishSemanticHeadInventory ∧
      pyashEnglishMoodHeadToWDFClause? mood head = some c ∧
      pyashEnglishMoodHeadToState? mood head = some c.expectedState

theorem pyashEnglishSemanticInventorySupportsAllClauses_true :
    pyashEnglishSemanticInventorySupportsAllClauses := by
  intro c _hmem
  exact pyashEnglishSemantic_inventory_clause_complete c

/-- Observed-head mapping floor claim inherited from the semantic bridge module. -/
def pyashEnglishObservedHeadCoverageFloorClaim : Prop :=
  pyashEnglishObservedMappedHeadFloor ≤ pyashEnglishObservedMappedHeadCount

theorem pyashEnglishObservedHeadCoverageFloorClaim_true :
    pyashEnglishObservedHeadCoverageFloorClaim := by
  simpa [pyashEnglishObservedMappedHeadCount] using pyashEnglishObservedMappedHeadFloor_holds

/-- Executable boolean canary for the observed-head mapping floor claim. -/
def pyashEnglishObservedHeadCoverageFloorBool : Bool :=
  Nat.ble pyashEnglishObservedMappedHeadFloor pyashEnglishObservedMappedHeadCount

theorem pyashEnglishObservedHeadCoverageFloorBool_true :
    pyashEnglishObservedHeadCoverageFloorBool = true := by
  unfold pyashEnglishObservedHeadCoverageFloorBool
  simpa [Nat.ble_eq] using pyashEnglishObservedHeadCoverageFloorClaim_true

/-- Executable comparison canary bundle (label, claim-satisfied). -/
def pyashEnglishComparativeCanaries : List (String × Bool) :=
  [ ("pyash_adv_def_mood_lexical", pyashDefMoodLexicalAdvantageBool)
  , ("pyash_adv_clause_mapping_deterministic", pyashClauseMappingDeterministicBool)
  , ("pyash_weaker_copula_head", pyashCopulaHeadWeakerPathBool)
  , ("pyash_en_wdf_semantic_coverage", pyashEnglishWDFSemanticCoverageBool)
  , ("pyash_en_observed_head_coverage_floor",
      pyashEnglishObservedHeadCoverageFloorBool)
  ]

theorem pyashEnglishComparativeCanaries_all_true :
    pyashEnglishComparativeCanaries.all (fun row => row.2) = true := by
  unfold pyashEnglishComparativeCanaries
  simp [pyashDefMoodLexicalAdvantageBool_true,
    pyashClauseMappingDeterministicBool_true,
    pyashCopulaHeadWeakerPathBool_true,
    pyashEnglishWDFSemanticCoverageBool_true,
    pyashEnglishObservedHeadCoverageFloorBool_true]

end Mettapedia.OSLF.Framework.PyashGFComparative
