import Mettapedia.GSLT.Parsing.ClassAwareGroundedChart
import Mettapedia.GSLT.Parsing.ClassAwareChartIndex

/-! Consequence-driven reference-chart construction. A budget limits work;
only an independently checked fixed point supplies parser completeness.
The completed chart is pruned after saturation, before native coverage is
compared, so irrelevant local families are not required in the native forest. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.ClassAwareChartClosure

open ClassAwarePackedForest ClassAwarePackedForestSaturation
open ClassAwareNativeForestQualification ClassAwareParserPackCorrespondence
open ClassAwareParserPackCertificate ParserProfileSemantics

def rootKey (plan : CompiledParserPackPlan) (input : List Nat) : NodeKey :=
  ⟨plan.lexical.startSort, 0, input.length⟩

def fullForest (plan : CompiledParserPackPlan) (input : List Nat) (families : List Family) : Forest :=
  ⟨[rootKey plan input], families⟩

def step (profile : ParserProfileLayer) (plan : CompiledParserPackPlan) (input : List Nat)
    (families : List Family) : List Family :=
  Mettapedia.Util.LinearHash.eraseDupsFast (families ++ expectedLexicalFamilies profile plan input ++
    ClassAwareChartIndex.structuralFamilies (fullForest plan input families) profile plan input)

theorem step_contains (profile : ParserProfileLayer) (plan : CompiledParserPackPlan)
    (input : List Nat) (families : List Family) : families ⊆ step profile plan input families := by
  intro family member
  simp only [step, Mettapedia.Util.LinearHash.eraseDupsFast_eq, List.mem_eraseDups, List.mem_append]
  exact Or.inl (Or.inl member)

theorem fixed_saturated {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {input : List Nat} {families : List Family}
    (fixed : step profile plan input families = families) :
    RuleSaturated (fullForest plan input families) profile plan input := by
  apply validateRuleSaturation_sound
  simp only [validateRuleSaturation, fullForest, rootKey, List.mem_singleton,
    decide_true, Bool.true_and, List.all_eq_true, Bool.and_eq_true]
  constructor
  · intro family member
    rw [← fixed]
    simp only [step, Mettapedia.Util.LinearHash.eraseDupsFast_eq, ClassAwareChartIndex.structuralFamilies_exact,
      List.mem_eraseDups, List.mem_append, decide_eq_true_eq]
    exact Or.inl (Or.inr member)
  · intro family member
    rw [← fixed]
    simp only [step, Mettapedia.Util.LinearHash.eraseDupsFast_eq, ClassAwareChartIndex.structuralFamilies_exact,
      List.mem_eraseDups, List.mem_append, decide_eq_true_eq]
    exact Or.inr member

/-- Whole-input roots are published only when a family at that key exists.
The internal saturation checker may use the root key even for rejected text. -/
def recognizedForest (plan : CompiledParserPackPlan) (input : List Nat) (families : List Family) : Forest :=
  { roots := if rootKey plan input ∈ families.map Family.parent then [rootKey plan input] else []
    families }

theorem recognized_complete {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {input : List Nat} {families : List Family}
    (saturated : RuleSaturated (fullForest plan input families) profile plan input) :
    RootParserComplete (recognizedForest plan input families) profile plan input := by
  intro tree derivation
  have unfolds := saturated.derivation_unfolds derivation (Nat.le_refl _)
  have familyPresent := unfolds _ (certificateFamily_mem_certificateFamilies _ _)
  have keyEq : certificateKey plan.lexical.startSort (Certificate.ofDerivation derivation) = rootKey plan input := by
    cases derivation <;> rfl
  have parentEq : (certificateFamily plan.lexical.startSort (Certificate.ofDerivation derivation)).parent =
      rootKey plan input := by
    cases derivation <;> rfl
  have recognized : rootKey plan input ∈ families.map Family.parent :=
    List.mem_map.mpr ⟨_, familyPresent, parentEq⟩
  exact ⟨by simp [recognizedForest, recognized, keyEq], unfolds⟩

/-- A stopped construction is pending. Returning a forest requires an actual
fixed-point equality, independently of the supplied round budget. -/
def finish? (profile : ParserProfileLayer) (plan : CompiledParserPackPlan) (input : List Nat) :
    Nat → List Family → Option Forest
  | 0, _ => none
  | rounds + 1, families =>
      let next := step profile plan input families
      if next == families then
        some (ClassAwareGroundedChart.rootReachableForest (recognizedForest plan input families))
      else finish? profile plan input rounds next

theorem finish?_complete {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {input : List Nat} (rounds : Nat) (families : List Family) (forest : Forest)
    (finished : finish? profile plan input rounds families = some forest) :
    RootParserComplete forest profile plan input := by
  induction rounds generalizing families with
  | zero => cases finished
  | succ rounds ih =>
    simp only [finish?] at finished
    split at finished
    · rename_i fixed
      cases Option.some.inj finished
      exact ClassAwareGroundedChart.rootReachable_complete
        (recognized_complete (fixed_saturated (by simpa only [beq_iff_eq] using fixed)))
    · exact ih _ finished

def reference? (profile : ParserProfileLayer) (plan : CompiledParserPackPlan) (input : List Nat)
    (rounds : Nat) : Option Forest := finish? profile plan input rounds []

theorem reference?_complete {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {input : List Nat} {rounds : Nat} {forest : Forest}
    (finished : reference? profile plan input rounds = some forest) :
    RootParserComplete forest profile plan input := finish?_complete rounds [] forest finished

end Mettapedia.GSLT.Parsing.ClassAwareChartClosure
