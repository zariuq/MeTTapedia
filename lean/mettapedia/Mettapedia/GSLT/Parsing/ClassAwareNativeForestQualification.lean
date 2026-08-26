import Mettapedia.GSLT.Parsing.ClassAwareNativeForestFamilyCompleteness
import Mettapedia.GSLT.Parsing.ClassAwareNativeForestIdentityWire
import Mettapedia.GSLT.Parsing.ClassAwareParserPackEnumeration

/-!
# Resolved exact qualification for a native ParserPack forest

This module composes the two independent native-forest qualification inputs.
A physical identity snapshot must resolve uniquely against the supplied
authored target plan, and the resulting inventory must make every exported
native choice an exact semantic family.  This native-internal exactness does
not by itself prove that the backend exported every valid ParserPack
derivation; `RootParserComplete` records that separate backward-lift
obligation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.ClassAwareNativeForestQualification

open Mettapedia.GSLT.Parsing.ClassAwareNativeForestContract
open Mettapedia.GSLT.Parsing.ClassAwareNativeForestFamilyCompleteness
open Mettapedia.GSLT.Parsing.ClassAwareNativeForestFamilyWitness
open Mettapedia.GSLT.Parsing.ClassAwareNativeForestIdentityInventory
open Mettapedia.GSLT.Parsing.ClassAwareNativeForestIdentityWire
open Mettapedia.GSLT.Parsing.ClassAwarePackedForest
open Mettapedia.GSLT.Parsing.ClassAwareParserPackCertificate
open Mettapedia.GSLT.Parsing.ClassAwareParserPackCorrespondence
open Mettapedia.GSLT.Parsing.ClassAwareParserPackEnumeration
open Mettapedia.GSLT.Parsing.LanguageDefSyntaxCompiler
open Mettapedia.GSLT.Parsing.ParserProfileSemantics
open Mettapedia.GSLT.Parsing.PresentationExprSemantics

/-- One executable gate for semantic identity resolution and exact finite
family representation. The identity packet has no authority when resolution
against the supplied target plan fails. -/
def validateResolvedExactFamilyRepresentation
    (snapshot : Snapshot) (view : ForestView)
    (profile : ParserProfileLayer) (plan : CompiledParserPackPlan) : Bool :=
  match snapshot.resolveInventory? plan with
  | none => false
  | some inventory =>
      validateExactFamilyRepresentation view inventory profile plan

/-- Acceptance supplies both the exact resolved inventory and the two-sided
representation theorem for every exported native choice.  ParserPack-wide
completeness remains the separate `RootParserComplete` premise below. -/
theorem validateResolvedExactFamilyRepresentation_sound
    {snapshot : Snapshot} {view : ForestView}
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    (accepted :
      validateResolvedExactFamilyRepresentation snapshot view profile plan =
        true) :
    ∃ inventory : Inventory,
      snapshot.resolveInventory? plan = some inventory ∧
        ∃ inputs : RootedFamilyDecodingInputs view inventory profile plan,
          Represents view inventory.toTable profile view.codepoints
            (decodedForest inputs.families
              (enumerateFamilyWitnesses view)) := by
  unfold validateResolvedExactFamilyRepresentation at accepted
  generalize resolved : snapshot.resolveInventory? plan = result at accepted
  cases result with
  | none => simp at accepted
  | some inventory =>
      refine ⟨inventory, rfl, ?_⟩
      exact validateExactFamilyRepresentation_sound accepted

/-! ## Completeness relative to the authored ParserPack

`Represents` is deliberately exact about the supplied native arrays: every
exported family is meaningful, and every physical choice is decoded.  A
backend can nevertheless omit an authored ParserPack alternative.  The
following second premise is what turns native self-representation into full
proof-fibre hosting.
-/

/-- Every whole-input ParserPack derivation has its exact certificate rooted
and unfolded in the flattened forest represented by the native arrays. -/
def RootParserComplete
    (target : Forest) (profile : ParserProfileLayer)
    (plan : CompiledParserPackPlan) (input : List Nat) : Prop :=
  ∀ tree : CST,
    Complete target profile plan input plan.lexical.startSort
      0 input.length tree

/-- Full native ParserPack qualification keeps native representation and
guest-calculus completeness as independent fields.  Neither digests nor
agreement between two backends can manufacture the second field. -/
structure ParserCompleteRepresentation
    (view : ForestView) (inventory : Inventory)
    (profile : ParserProfileLayer) (plan : CompiledParserPackPlan)
    (target : Forest) : Prop where
  represents :
    Represents view inventory.toTable profile view.codepoints target
  parserComplete :
    RootParserComplete target profile plan view.codepoints

/-- Executable unfolding check for one finite certificate. -/
def rootUnfolds? (target : Forest) (resultSort : String)
    (certificate : Certificate) : Bool :=
  decide (certificateKey resultSort certificate ∈ target.roots) &&
    (certificateFamilies resultSort certificate).all fun family =>
      decide (family ∈ target.families)

theorem rootUnfolds?_eq_true_iff
    (target : Forest) (resultSort : String)
    (certificate : Certificate) :
    rootUnfolds? target resultSort certificate = true ↔
      RootUnfolds target resultSort certificate := by
  simp [rootUnfolds?, RootUnfolds, Unfolds, List.all_eq_true]

/-- An independent finite catalogue contains replayable root certificates and
is complete for every authored ParserPack derivation.  How the catalogue is
constructed is intentionally left open: an exhaustive reference parser may
provide it, whereas the native forest being qualified may not certify itself. -/
structure RootCertificateCatalogue
    (profile : ParserProfileLayer) (plan : CompiledParserPackPlan)
    (input : List Nat) : Type where
  entries : List (Certificate × CST)
  replay : ∀ entry, entry ∈ entries →
    Nonempty (Replays profile plan input entry.1
      plan.lexical.startSort 0 input.length entry.2)
  complete : ∀ (tree : CST)
      (derivation : ParserPackRootDerives profile plan input tree),
    (Certificate.ofDerivation derivation, tree) ∈ entries

/-- The independent height-bounded reference enumerator supplies a finite
catalogue once the authored plan/input semantics proves a root height bound.
No native forest participates in this construction. -/
def RootCertificateCatalogue.ofHeightBound
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {input : List Nat} {fuel : Nat}
    (bounded : RootHeightBound profile plan input fuel) :
    RootCertificateCatalogue profile plan input := {
  entries := rootCatalogueRows fuel profile plan input
  replay := fun _ member => rootCatalogueRows_replay member
  complete := fun tree derivation =>
    rootCatalogueRows_complete bounded tree derivation
}

/-- Compare a forest with every certificate occurrence in a finite catalogue.
The CST is retained in the catalogue identity even though unfolding depends
only on the certificate. -/
def validateCatalogueRowsCoverage
    (target : Forest) (resultSort : String)
    (entries : List (Certificate × CST)) : Bool :=
  entries.all fun entry => rootUnfolds? target resultSort entry.1

def validateCatalogueCoverage
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {input : List Nat}
    (target : Forest)
    (catalogue : RootCertificateCatalogue profile plan input) : Bool :=
  validateCatalogueRowsCoverage target plan.lexical.startSort
    catalogue.entries

/-- Coverage of an independently complete catalogue supplies precisely the
missing ParserPack backward lift. -/
theorem validateCatalogueCoverage_sound
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {input : List Nat} {target : Forest}
    (catalogue : RootCertificateCatalogue profile plan input)
    (accepted : validateCatalogueCoverage target catalogue = true) :
    RootParserComplete target profile plan input := by
  intro tree derivation
  have member := catalogue.complete tree derivation
  have covered := (List.all_eq_true.mp accepted)
    (Certificate.ofDerivation derivation, tree) member
  exact (rootUnfolds?_eq_true_iff target plan.lexical.startSort _).mp covered

/-- Assemble full native qualification only after the independent catalogue
coverage gate has closed. -/
def ParserCompleteRepresentation.ofCatalogue
    {view : ForestView} {inventory : Inventory}
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {target : Forest}
    (represents :
      Represents view inventory.toTable profile view.codepoints target)
    (catalogue :
      RootCertificateCatalogue profile plan view.codepoints)
    (accepted : validateCatalogueCoverage target catalogue = true) :
    ParserCompleteRepresentation view inventory profile plan target := {
  represents
  parserComplete := validateCatalogueCoverage_sound catalogue accepted
}

/-- A fully qualified native representation has exactly the authored
ParserPack proof fibre at each whole-input CST observation. -/
noncomputable def ParserCompleteRepresentation.rootDerivationEquiv
    {view : ForestView} {inventory : Inventory}
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {target : Forest}
    (qualification :
      ParserCompleteRepresentation view inventory profile plan target)
    (tree : CST) :
    ParserPackRootDerives profile plan view.codepoints tree ≃
      NativePackedFibre view inventory.toTable profile plan view.codepoints
        plan.lexical.startSort 0 view.codepoints.length tree :=
  nativeDerivationEquiv qualification.represents
    (qualification.parserComplete tree)

/-- Source-plan compilation and fully qualified native execution compose
without quotienting the CST or certificate occurrence fibre. -/
noncomputable def ParserCompleteRepresentation.sourceRootDerivationEquiv
    {literalScalars? : String → Option (List Nat)}
    {profile : ParserProfileLayer} {rules : List CompiledRule}
    {plan : CompiledParserPackPlan} {view : ForestView}
    {inventory : Inventory} {target : Forest}
    (agreement :
      ParserPackPlanAgreement literalScalars? profile rules plan)
    (qualification :
      ParserCompleteRepresentation view inventory profile plan target)
    (tree : CST) :
    SourcePlanRootDerives literalScalars? profile rules
        view.codepoints tree ≃
      NativePackedFibre view inventory.toTable profile plan view.codepoints
        plan.lexical.startSort 0 view.codepoints.length tree :=
  (sourcePlanRootDerivationEquiv agreement tree).trans
    (qualification.rootDerivationEquiv tree)

/-! ## Omission canary -/

private def omissionProfile : ParserProfileLayer := {
  name := "ParserCompletenessOmissionCanary"
  startSort := "Value"
  classes := []
  states := []
}

private def omissionPlan : CompiledParserPackPlan := {
  lexical := {
    profileName := "ParserCompletenessOmissionCanary"
    startSort := "Value"
    classes := []
    productions := [
      { label := "value-left", resultSort := "Value",
        matcher := .char 65, childSlots := [0] },
      { label := "value-right", resultSort := "Value",
        matcher := .char 65, childSlots := [0] }
    ]
  }
  structural := []
}

private def omissionLeftCertificate : Certificate :=
  .lexical 0 (.char 65) 0 1

private def omissionForest : Forest :=
  pack [("Value", omissionLeftCertificate)]

private def omissionRightCertificate : Certificate :=
  .lexical 1 (.char 65) 0 1

private def omissionRightTree : CST :=
  .node "value-right" 0 1 [.terminal [65] 0 1]

private def omissionCatalogueRows : List (Certificate × CST) := [
  (omissionLeftCertificate,
    .node "value-left" 0 1 [.terminal [65] 0 1]),
  (omissionRightCertificate, omissionRightTree)
]

private def omissionFullForest : Forest :=
  pack [
    ("Value", omissionLeftCertificate),
    ("Value", omissionRightCertificate)
  ]

private theorem omissionRootHeightBound :
    RootHeightBound omissionProfile omissionPlan [65] 1 := by
  intro tree derivation
  cases derivation with
  | lexical => rfl
  | structural position valid _ _ _ =>
      simp [omissionPlan] at valid

private def omissionCatalogue :
    RootCertificateCatalogue omissionProfile omissionPlan [65] :=
  RootCertificateCatalogue.ofHeightBound omissionRootHeightBound

private def omissionRightDerivation :
    ParserPackDerivesAt omissionProfile omissionPlan [65]
      "Value" 0 1
      (.node "value-right" 0 1 [.terminal [65] 0 1]) := by
  apply ParserPackDerivesAt.lexical 1 (by decide)
  · rfl
  · rfl
  · rfl
  · exact ⟨.char rfl, rfl⟩

private theorem omissionRightDerivation_certificate :
    Certificate.ofDerivation omissionRightDerivation =
      omissionRightCertificate := by
  rfl

/-- Positive executable control: packing both independently catalogued
alternatives covers both exact physical production occurrences. -/
theorem complete_catalogue_rows_are_covered :
    validateCatalogueRowsCoverage omissionFullForest "Value"
      omissionCatalogueRows = true := by
  decide

/-- Negative executable control: a semantically valid forest containing only
the left alternative fails coverage of the independently catalogued right
alternative. -/
theorem omitted_catalogue_row_is_rejected :
    validateCatalogueRowsCoverage omissionForest "Value"
      omissionCatalogueRows = false := by
  decide

/-- The complete forest passes the actual independent height-bounded
ParserPack catalogue, not merely a hand-written list of expected rows. -/
theorem complete_enumerated_catalogue_is_covered :
    validateCatalogueCoverage omissionFullForest omissionCatalogue = true := by
  decide

/-- The same independently generated catalogue rejects the forest that drops
the second physical production occurrence. -/
theorem omitted_enumerated_catalogue_is_rejected :
    validateCatalogueCoverage omissionForest omissionCatalogue = false := by
  decide

/-- Negative control: retaining one valid alternative does not establish
ParserPack completeness when another physical production occurrence accepts
the same input. -/
theorem one_valid_unfolding_does_not_imply_root_completeness :
    RootUnfolds omissionForest "Value" omissionLeftCertificate ∧
      ¬ RootParserComplete omissionForest omissionProfile omissionPlan [65] := by
  constructor
  · exact member_pack_rootUnfolds (certificates :=
      [("Value", omissionLeftCertificate)]) (by simp)
  · intro complete
    have rightUnfolds := complete
      omissionRightTree
      omissionRightDerivation
    have rightFamily := rightUnfolds.2
      (certificateFamily "Value"
        (Certificate.ofDerivation omissionRightDerivation))
      (by
        change certificateFamily "Value"
            (Certificate.ofDerivation omissionRightDerivation) ∈
          certificateFamilies "Value"
            (Certificate.ofDerivation omissionRightDerivation)
        rw [omissionRightDerivation_certificate]
        change certificateFamily "Value" omissionRightCertificate ∈
          [certificateFamily "Value" omissionRightCertificate]
        simp)
    rw [omissionRightDerivation_certificate] at rightFamily
    change certificateFamily "Value" omissionRightCertificate ∈
      [certificateFamily "Value" omissionLeftCertificate] at rightFamily
    simp only [List.mem_singleton] at rightFamily
    have productionEqual := congrArg Family.production rightFamily
    change ProductionRef.lexical 1 = ProductionRef.lexical 0 at productionEqual
    have impossible : (1 : Nat) = 0 :=
      ProductionRef.lexical.inj productionEqual
    omega

end Mettapedia.GSLT.Parsing.ClassAwareNativeForestQualification
