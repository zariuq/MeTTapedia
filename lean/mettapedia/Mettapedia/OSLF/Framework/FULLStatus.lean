import Mettapedia.OSLF.Framework.CategoryBridge
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.Framework.ConstructorCategory
import Mettapedia.OSLF.MeTTaIL.DeclReducesWithPremises
import Mettapedia.GSLT.Topos.PredicateFibration
import Mettapedia.OSLF.Framework.ToposReduction
import Mettapedia.OSLF.Framework.BeckChevalleyOSLF

/-!
# OSLF FULL Status Tracker

Machine-readable tracker for what is already formalized versus what is still
missing for a full presheaf-topos/native-type-theory OSLF lift.

This module is intentionally concrete: every entry includes a code reference
string so status reports can link back to Lean artifacts directly.
-/

namespace Mettapedia.OSLF.Framework.FULLStatus

/-- Current completion state for a FULL-OSLF milestone. -/
inductive MilestoneStatus where
  | done
  | inProgress
  | missing
  deriving DecidableEq, Repr

/-- One traceability row in the FULL-OSLF tracker. -/
structure Milestone where
  area : String
  title : String
  status : MilestoneStatus
  codeRef : String
  note : String
  deriving Repr

/-- Central FULL-OSLF status table.

    `status = done` means the artifact is formalized in Lean.
    `status = inProgress` means interface/hook exists but full theorem is pending.
    `status = missing` means no complete implementation/theorem yet. -/
def tracker : List Milestone :=
  [ { area := "OSLF Core"
      title := "LanguageDef → RewriteSystem → OSLF pipeline"
      status := .done
      codeRef := "Mettapedia/OSLF/Framework/TypeSynthesis.lean: langOSLF"
      note := "Generic synthesis and automatic modal Galois connection are in place." }
  , { area := "Premise Semantics"
      title := "Premise-aware executable/declarative equivalence"
      status := .done
      codeRef := "Mettapedia/OSLF/MeTTaIL/DeclReducesWithPremises.lean: engineWithPremisesUsing_sound/complete"
      note := "Engine path with premises has soundness/completeness bridge." }
  , { area := "Category Lift"
      title := "Sort base no longer hard-coded to Discrete"
      status := .inProgress
      codeRef := "Mettapedia/OSLF/Framework/CategoryBridge.lean: SortCategoryInterface, lambdaTheorySortInterface, typeSortsLambdaInterface"
      note := "Interface + concrete λ-theory-backed interface are defined; language-specific presheaf semantics still pending." }
  , { area := "Category Lift"
      title := "Predication over interface-selected base category"
      status := .inProgress
      codeRef := "Mettapedia/OSLF/Framework/CategoryBridge.lean: predFibrationUsing, oslf_fibrationUsing, typeSortsPredFibrationViaLambdaInterface"
      note := "Generic fibration constructors exist and are exercised in a non-default λ-theory-backed use-site." }
  , { area := "Presheaf Topos"
      title := "Internal Ω/sieve-based subobject semantics"
      status := .inProgress
      codeRef := "Mettapedia/GSLT/Topos/SubobjectClassifier.lean: presheafSubobjectRepresentableByOmega / presheafCategoryHasClassifierConstructive"
      note := "Constructive Ω/sieve representability and classifier are formalized; base-semantics wiring into CategoryBridge remains." }
  , { area := "Reduction-as-Subobject"
      title := "Internal reduction graph with premises in topos"
      status := .inProgress
      codeRef := "Mettapedia/OSLF/Framework/ToposReduction.lean: reductionGraphObjUsing / reductionGraphUsing_edge_endpoints_iff / langDiamondUsing_iff_exists_graphStep / langBoxUsing_iff_forall_graphIncoming"
      note := "Premise-aware one-step reduction is packaged as a reusable graph object abstraction over presheaves, with endpoint and modal (`◇`,`□`) graph-compatibility bridges." }
  , { area := "Beck-Chevalley"
      title := "Full substitution square in lifted base"
      status := .inProgress
      codeRef := "Mettapedia/OSLF/Framework/BeckChevalleyOSLF.lean: presheafPrimary_beckChevalley_transport / commDi_diamond_graphObj_square"
      note := "OSLF layer now includes an explicit graph-object substitution/rewrite square theorem (`commDi_diamond_graphObj_square`) over `ReductionGraphObj`, alongside presheaf Beck-Chevalley transport." }
  ]

/-- Count milestones with a given status. -/
def countBy (s : MilestoneStatus) : Nat :=
  (tracker.filter (fun m => m.status = s)).length

/-- Remaining FULL-OSLF milestones (in-progress + missing). -/
def remaining : List Milestone :=
  tracker.filter (fun m => m.status ≠ .done)

/-- Quick sanity check: we do have tracked unfinished work. -/
theorem remaining_nonempty : remaining ≠ [] := by
  simp [remaining, tracker]

/-! ## Code-Reference Anchors

These checks tie tracker statements to concrete constants in the codebase.
-/

#check @Mettapedia.OSLF.Framework.TypeSynthesis.langOSLF
#check @Mettapedia.OSLF.MeTTaIL.DeclReducesWithPremises.engineWithPremisesUsing_sound
#check @Mettapedia.OSLF.MeTTaIL.DeclReducesWithPremises.engineWithPremisesUsing_complete
#check @Mettapedia.OSLF.Framework.CategoryBridge.SortCategoryInterface
#check @Mettapedia.OSLF.Framework.CategoryBridge.lambdaTheorySortInterface
#check @Mettapedia.OSLF.Framework.CategoryBridge.predFibrationUsing
#check @Mettapedia.OSLF.Framework.CategoryBridge.oslf_fibrationUsing
#check @Mettapedia.GSLT.Topos.beckChevalleyCondition_presheafChangeOfBase
#check @Mettapedia.OSLF.Framework.BeckChevalleyOSLF.presheafPrimary_beckChevalley_transport
#check @Mettapedia.OSLF.Framework.BeckChevalleyOSLF.langDiamondUsing_graph_transport
#check @Mettapedia.OSLF.Framework.BeckChevalleyOSLF.commDi_diamond_graph_step_iff
#check @Mettapedia.OSLF.Framework.BeckChevalleyOSLF.commDi_diamond_graphObj_square
#check @Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
#check @Mettapedia.OSLF.Framework.ToposReduction.reductionGraphObjUsing
#check @Mettapedia.OSLF.Framework.ToposReduction.reductionSubfunctorUsing
#check @Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing_edge_endpoints_iff
#check @Mettapedia.OSLF.Framework.ToposReduction.langDiamondUsing_iff_exists_graphStep
#check @Mettapedia.OSLF.Framework.ToposReduction.langBoxUsing_iff_forall_graphIncoming
#check @Mettapedia.OSLF.Framework.ToposReduction.langDiamondUsing_iff_exists_internalStep
#check @Mettapedia.OSLF.Framework.ToposReduction.langBoxUsing_iff_forall_internalStep

end Mettapedia.OSLF.Framework.FULLStatus
