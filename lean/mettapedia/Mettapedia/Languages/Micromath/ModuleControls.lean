import Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
import Mettapedia.OSLF.MeTTaIL.Engine
import Mettapedia.GSLT.LanguageDef.CollectionReadRelation
import Mettapedia.Languages.Micromath.Kernel

/-!
# Selected Micromath module rewrites use reusable proof premises

These controls execute the authored module's actual rewrite rule. Micromath
allows two premise references to name the same checked theorem. The authored
module now expresses these as collection-membership premises, interpreted by
the ordinary premise-aware engine and the pure collection reader. The earlier
distinct-consuming encoding is retained only as a negative mutation.

These controls check actual module execution, not arbitrary-input adequacy,
fresh definitions, trusted store initialization or a native implementation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Micromath.ModuleControls

open Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
open scoped Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
open Mettapedia.OSLF.MeTTaIL.Syntax

#module_file "../../../../../metta/gslt/module/MicromathKernel.module"
#module_roundtrip MicromathKernel

def authored : LanguageDef := MicromathKernel.language.toOption.get (by decide)
def sub1 : RewriteRule := authored.rewrites[3]'(by decide)
#guard sub1.name == "Sub1"
def sub2 : RewriteRule := authored.rewrites[4]'(by decide)
#guard sub2.name == "Sub2"

def x : Pattern := .apply "X" []
def y : Pattern := .apply "Y" []
def eq (out f left right : Pattern) : Pattern := .apply "EQ" [out, f, left, right]
def store (claims : List Pattern) : Pattern := .apply "Store" [.collection .hashSet claims none]

def main : Claim := projectionSecond 1 0
def side : Claim := projectionFirst 1 0
def conclusion : Claim := projectionSecond 0 1

theorem repeated_references_are_a_valid_kernel_step :
    substitute1? main main side side = some conclusion := by decide

theorem main_holds {D : Type} (interpret : Assignment D) (projects : Projects interpret) :
    Holds interpret main := projectionSecond_holds interpret projects 1 0

theorem side_holds {D : Type} (interpret : Assignment D) (projects : Projects interpret) :
    Holds interpret side := projectionFirst_holds interpret projects 1 0

def representedMain : Pattern := eq x y y x
def representedSide : Pattern := eq y x y x
def representedConclusion : Pattern := eq y y x y

def fourDistinctRows : Pattern :=
  store [eq x x y x, eq x y x y, eq x x x y, eq y x x y]

/-- The former resource pattern removes a different member at each premise.
The rule retains the authored field equations but mutates reads into takes. -/
def consumingMutation : RewriteRule := { sub1 with
  premises := []
  left := .apply "Store" [.collection .hashSet
    [eq (.fvar "x") (.fvar "t") (.fvar "u") (.fvar "w"),
     eq (.fvar "u1") (.fvar "u") (.fvar "a") (.fvar "b"),
     eq (.fvar "w1") (.fvar "w") (.fvar "a") (.fvar "b"),
     eq (.fvar "x1") (.fvar "x") (.fvar "a") (.fvar "b")] (some "rest")]
  right := .apply "Store" [.collection .hashSet
    [eq (.fvar "x") (.fvar "t") (.fvar "u") (.fvar "w"),
     eq (.fvar "u1") (.fvar "u") (.fvar "a") (.fvar "b"),
     eq (.fvar "w1") (.fvar "w") (.fvar "a") (.fvar "b"),
     eq (.fvar "x1") (.fvar "x") (.fvar "a") (.fvar "b"),
     eq (.fvar "x1") (.fvar "t") (.fvar "u1") (.fvar "w1")] (some "rest")] }

/-- Mutation of only the collection tag reconstructs the former bag/set
mismatch while preserving the actual module's field patterns. -/
def bagKindMutation : RewriteRule := { consumingMutation with
  left := match consumingMutation.left with
    | .apply head [.collection _ claims rest] => .apply head [.collection .hashBag claims rest]
    | other => other }

/-- The conclusion is genuinely new, so refusing this selected inference
cannot be dismissed merely as omitting a no-op. -/
theorem conclusion_not_already_present :
    representedConclusion ∉ [representedMain, representedSide] := by decide

/-- The older matcher can handle distinct rows; its failure on reuse was not
caused by an unrecognized constructor or a wrong collection kind. -/
theorem consuming_mutation_accepts_four_distinct_rows :
    (Mettapedia.OSLF.MeTTaIL.Match.applyRule consumingMutation
      fourDistinctRows).isEmpty = false := by
  cbv

set_option maxHeartbeats 4000000 in
theorem actual_engine_accepts_four_distinct_rows :
    (Mettapedia.OSLF.MeTTaIL.Engine.applyRuleWithPremisesUsing
      Mettapedia.GSLT.LanguageDef.CollectionReadRelation.environment authored sub1
      fourDistinctRows).isEmpty = false := by
  cbv

theorem bag_kind_mutation_refuses_the_same_rows :
    Mettapedia.OSLF.MeTTaIL.Match.applyRule bagKindMutation fourDistinctRows = [] := by
  cbv

theorem consuming_matcher_refuses_repeated_premise_references :
    Mettapedia.OSLF.MeTTaIL.Match.applyRule consumingMutation
      (store [representedMain, representedSide]) = [] := by
  cbv

/-- The mutation fails through the engine too, not only its pattern matcher. -/
theorem consuming_engine_refuses_repeated_premise_references :
    Mettapedia.OSLF.MeTTaIL.Engine.applyRuleWithPremises authored consumingMutation
      (store [representedMain, representedSide]) = [] := by
  cbv

def run (rule : RewriteRule) (claims : List Pattern) : List Pattern :=
  Mettapedia.OSLF.MeTTaIL.Engine.applyRuleWithPremisesUsing
    Mettapedia.GSLT.LanguageDef.CollectionReadRelation.environment authored rule (store claims)

set_option maxHeartbeats 4000000 in
theorem actual_sub1_reuses_proofs_and_preserves_the_store :
    (run sub1 [representedMain, representedSide]).contains
      (store [representedConclusion, representedMain, representedSide]) = true := by cbv

theorem sub2_repeated_references_are_a_valid_kernel_step :
    substitute2? main main side conclusion = some side := by decide

set_option maxHeartbeats 4000000 in
theorem actual_sub2_reuses_proofs_and_preserves_the_store :
    (run sub2 [representedMain, representedSide, representedConclusion]).contains
      (store [representedSide, representedMain, representedSide, representedConclusion]) = true := by cbv

set_option maxHeartbeats 4000000 in
theorem missing_side_premise_is_not_invented : run sub1 [representedMain] = [] := by cbv

theorem empty_library_has_no_inference : run sub1 [] = [] ∧ run sub2 [] = [] := by cbv

theorem default_engine_without_read_service_declines :
    Mettapedia.OSLF.MeTTaIL.Engine.applyRuleWithPremises authored sub1
      (store [representedMain, representedSide]) = [] := by cbv

#print axioms repeated_references_are_a_valid_kernel_step
#print axioms main_holds
#print axioms side_holds
#print axioms conclusion_not_already_present
#print axioms consuming_mutation_accepts_four_distinct_rows
#print axioms actual_engine_accepts_four_distinct_rows
#print axioms bag_kind_mutation_refuses_the_same_rows
#print axioms consuming_matcher_refuses_repeated_premise_references
#print axioms consuming_engine_refuses_repeated_premise_references
#print axioms actual_sub1_reuses_proofs_and_preserves_the_store
#print axioms sub2_repeated_references_are_a_valid_kernel_step
#print axioms actual_sub2_reuses_proofs_and_preserves_the_store
#print axioms missing_side_premise_is_not_invented
#print axioms empty_library_has_no_inference
#print axioms default_engine_without_read_service_declines

end Mettapedia.Languages.Micromath.ModuleControls
