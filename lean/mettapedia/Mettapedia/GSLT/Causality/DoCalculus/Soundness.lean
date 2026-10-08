import Mettapedia.GSLT.Causality.DoCalculus.Distinctions
import Mettapedia.GSLT.Causality.DoCalculus.ExchangeDelete
import Mettapedia.GSLT.Causality.DoCalculus.LanguageDef
import Mettapedia.GSLT.Core.NonFactorization

/-!
# Soundness of the do-calculus fragment

Each expression denotes a g-formula mass in a finite Markovian model. A
do-free expression reads only the observational joint.

Rule 2 preserves that denotation when every parent of the exchanged set lies
in the conditioned set. Rule 3 preserves it when every edge out of the deleted
set lands in the intervention. Those are the theorems already proved for the
g-formula. The surface rules in `LanguageDef` also carry a d-separation
premise. The implication from that premise alone, for Pearl's full rule 2 and
full rule 3, is not proved here.

Pearl's rule 2 in full is: `P(y | do(x), do(z), w) = P(y | do(x), z, w)`
whenever `Y` and `Z` are d-separated by `X, W` in the graph with the arrows
into `X` and the arrows out of `Z` deleted. Pearl's rule 3 in full is:
`P(y | do(x), do(z), w) = P(y | do(x), w)` whenever `Y` and `Z` are
d-separated by `X, W` in the graph with the arrows into `X` and into `Z(W)`
deleted, where `Z(W)` is the subset of `Z` with no descendant in `W` after
the arrows into `X` are deleted.

The identification fragment tries those two proved branches and refuses
otherwise. Success produces a do-free expression of equal denotation. The
converse, that every identifiable query is found, is Shpitser–Pearl's
Theorem 7 and is not proved for this fragment. The bow is a query the
fragment refuses, and no do-free expression denotes its effect in every
compatible model.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.DoCalculus

open Mettapedia.ProbabilityTheory.BayesianNetworks
open BayesianNetwork
open DirectedGraph
open Mettapedia.GSLT.Core.NonFactorization
open scoped BigOperators ENNReal

variable {V : Type}
variable [Fintype V] [DecidableEq V]
variable (graph : DirectedGraph V)
variable [DecidableRel graph.edges]
variable (hAcyclic : graph.IsAcyclic)
variable {β : Type} [Fintype β] [DecidableEq β] [MeasurableSpace β]

/-! ## Expressions -/

/-- A g-formula expression. `cond` is one conditional mass. `sum` sums the
body over the values of a vertex block, extending the anchor on that block. -/
inductive MassExpr (V : Type) where
  | slice (intervention fixed : Finset V)
  | cond (intervention numerator denominator : Finset V)
  | mul (left right : MassExpr V)
  | div (numerator denominator : MassExpr V)
  | sum (bound : Finset V) (body : MassExpr V)
  deriving DecidableEq

/-- An expression is do-free when no branch intervenes. -/
def doFree : MassExpr V → Bool
  | .slice intervention _ => decide (intervention = ∅)
  | .cond intervention _ _ => decide (intervention = ∅)
  | .mul left right => doFree left && doFree right
  | .div numerator denominator => doFree numerator && doFree denominator
  | .sum _ body => doFree body

/-- Replace the coordinates in `bound` and keep the anchor off that block. -/
def extendAnchor (bound : Finset V) (inn : {v // v ∈ bound} → β) (anchor : V → β) :
    V → β :=
  glue bound inn (fun outside => anchor outside.1)

/-- Depth of an expression. A conditional is one step above the two slices it
reads, so the denotation can call those slices. -/
def massExprDepth : MassExpr V → Nat
  | .slice _ _ => 0
  | .cond _ _ _ => 1
  | .mul left right => massExprDepth left + massExprDepth right + 1
  | .div numerator denominator =>
      massExprDepth numerator + massExprDepth denominator + 1
  | .sum _ body => massExprDepth body + 1

noncomputable def gDenote
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (anchor : V → β) (expr : MassExpr V) : ℝ≥0∞ :=
  match expr with
  | .slice intervention fixed =>
      truncSlice graph hAcyclic cpt (doFinset intervention anchor) fixed anchor
  | .cond intervention numerator denominator =>
      gDenote cpt anchor (.slice intervention numerator) /
        gDenote cpt anchor (.slice intervention denominator)
  | .mul left right => gDenote cpt anchor left * gDenote cpt anchor right
  | .div numerator denominator =>
      gDenote cpt anchor numerator / gDenote cpt anchor denominator
  | .sum bound body =>
      ∑ inn : {v // v ∈ bound} → β,
        gDenote cpt (extendAnchor bound inn anchor) body
termination_by massExprDepth expr
decreasing_by
  all_goals (simp only [massExprDepth]; omega)

/-- The same expression read from an arbitrary joint, with interventions ignored.
On a do-free expression this agrees with `gDenote`. -/
noncomputable def denoteJoint (anchor : V → β) (joint : (V → β) → ℝ≥0∞)
    (expr : MassExpr V) : ℝ≥0∞ :=
  match expr with
  | .slice _ fixed =>
      ∑ f, if agreesOn fixed anchor f = true then joint f else 0
  | .cond _ numerator denominator =>
      denoteJoint anchor joint (.slice ∅ numerator) /
        denoteJoint anchor joint (.slice ∅ denominator)
  | .mul left right =>
      denoteJoint anchor joint left * denoteJoint anchor joint right
  | .div numerator denominator =>
      denoteJoint anchor joint numerator / denoteJoint anchor joint denominator
  | .sum bound body =>
      ∑ inn : {v // v ∈ bound} → β,
        denoteJoint (extendAnchor bound inn anchor) joint body
termination_by massExprDepth expr
decreasing_by
  all_goals (simp only [massExprDepth]; omega)

omit [Fintype V] [Fintype β] [DecidableEq β] [MeasurableSpace β] in
lemma doFinset_empty (anchor : V → β) :
    doFinset (∅ : Finset V) anchor = fun _ => none := by
  funext vertex
  simp [doFinset]

lemma slice_eq_joint
    (fixed : Finset V)
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (anchor : V → β) :
    gDenote graph hAcyclic cpt anchor (.slice ∅ fixed) =
      denoteJoint anchor (fun f => cpt.jointWeight f) (.slice ∅ fixed) := by
  simp only [gDenote, denoteJoint, truncSlice, doFinset_empty]
  refine Finset.sum_congr rfl fun f _ => ?_
  congr 1

theorem denote_eq_joint
    (expr : MassExpr V) (hfree : doFree expr = true)
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (anchor : V → β) :
    gDenote graph hAcyclic cpt anchor expr =
      denoteJoint anchor (fun f => cpt.jointWeight f) expr := by
  induction expr generalizing anchor with
  | slice intervention fixed =>
      simp only [doFree, decide_eq_true_eq] at hfree
      subst hfree
      exact slice_eq_joint graph hAcyclic fixed cpt anchor
  | cond intervention numerator denominator =>
      simp only [doFree, decide_eq_true_eq] at hfree
      subst hfree
      rw [gDenote.eq_2, denoteJoint.eq_2,
        slice_eq_joint graph hAcyclic numerator cpt anchor,
        slice_eq_joint graph hAcyclic denominator cpt anchor]
  | mul left right leftIh rightIh =>
      simp only [doFree, Bool.and_eq_true] at hfree
      simp only [gDenote, denoteJoint]
      rw [leftIh hfree.1, rightIh hfree.2]
  | div numerator denominator numeratorIh denominatorIh =>
      simp only [doFree, Bool.and_eq_true] at hfree
      simp only [gDenote, denoteJoint]
      rw [numeratorIh hfree.1, denominatorIh hfree.2]
  | sum bound body bodyIh =>
      simp only [doFree] at hfree
      simp only [gDenote, denoteJoint]
      refine Finset.sum_congr rfl fun inn _ => ?_
      exact bodyIh hfree (extendAnchor bound inn anchor)

/-- A do-free denotation is a function of the observational joint. -/
theorem doFree_factors_through_joint
    (expr : MassExpr V) (hfree : doFree expr = true) (anchor : V → β) :
    Factors (fun cpt : (network (β := β) graph hAcyclic).DiscreteCPT => cpt.jointWeight)
      (fun cpt => gDenote graph hAcyclic cpt anchor expr) := by
  refine ⟨fun joint => denoteJoint anchor joint expr, fun cpt => ?_⟩
  exact (denote_eq_joint graph hAcyclic expr hfree cpt anchor).symm

/-! ## Probability algebra -/

lemma ennreal_div_mul_div (a b c : ℝ≥0∞) (hb0 : b ≠ 0) (hbTop : b ≠ ⊤) :
    (a / b) * (b / c) = a / c := by
  rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul,
    mul_comm (b⁻¹ * a) (c⁻¹ * b), mul_assoc, ← mul_assoc b b⁻¹ a,
    ENNReal.mul_inv_cancel hb0 hbTop, one_mul]

lemma ennreal_div_div_same (a b c : ℝ≥0∞) (hb0 : b ≠ 0) (hbTop : b ≠ ⊤) :
    (a / b) / (c / b) = a / c := by
  rw [ENNReal.div_eq_inv_mul, ENNReal.inv_div (Or.inl hbTop) (Or.inl hb0), mul_comm]
  exact ennreal_div_mul_div a b c hb0 hbTop

lemma sum_div_const {ι : Type} (s : Finset ι) (f : ι → ℝ≥0∞) (c : ℝ≥0∞) :
    ∑ i ∈ s, f i / c = (∑ i ∈ s, f i) / c := by
  simp_rw [ENNReal.div_eq_inv_mul]
  rw [← Finset.mul_sum]

/-- Removing an empty intervention leaves the observational ratio of the joint. -/
theorem empty_do_is_observational
    (numerator denominator : Finset V)
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (anchor : V → β) :
    gDenote graph hAcyclic cpt anchor (.cond ∅ numerator denominator) =
      denoteJoint anchor (fun f => cpt.jointWeight f)
        (.cond ∅ numerator denominator) :=
  denote_eq_joint graph hAcyclic (.cond ∅ numerator denominator) (by simp [doFree]) cpt anchor

/-- The chain rule: the joint conditional is the product of the two successive
conditionals, when the middle slice is positive and finite. -/
theorem chain_sound
    (intervention left right conditioning : Finset V)
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (anchor : V → β)
    (hmiddle : truncSlice graph hAcyclic cpt (doFinset intervention anchor)
      (intervention ∪ right ∪ conditioning) anchor ≠ 0) :
    gDenote graph hAcyclic cpt anchor
        (.cond intervention
          (intervention ∪ left ∪ right ∪ conditioning)
          (intervention ∪ conditioning)) =
      gDenote graph hAcyclic cpt anchor
          (.cond intervention
            (intervention ∪ left ∪ right ∪ conditioning)
            (intervention ∪ right ∪ conditioning)) *
        gDenote graph hAcyclic cpt anchor
          (.cond intervention
            (intervention ∪ right ∪ conditioning)
            (intervention ∪ conditioning)) := by
  simp only [gDenote]
  have hmiddleTop := truncSlice_ne_top graph hAcyclic cpt (doFinset intervention anchor)
    (intervention ∪ right ∪ conditioning) anchor
  exact (ennreal_div_mul_div _ _ _ hmiddle hmiddleTop).symm

/-- Bayes' rule for the same slices, when each conditioning slice that is
divided by is positive and finite. -/
theorem bayes_sound
    (intervention left right conditioning : Finset V)
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (anchor : V → β)
    (hleft : truncSlice graph hAcyclic cpt (doFinset intervention anchor)
      (intervention ∪ left ∪ conditioning) anchor ≠ 0)
    (hbase : truncSlice graph hAcyclic cpt (doFinset intervention anchor)
      (intervention ∪ conditioning) anchor ≠ 0) :
    gDenote graph hAcyclic cpt anchor
        (.cond intervention
          (intervention ∪ left ∪ right ∪ conditioning)
          (intervention ∪ right ∪ conditioning)) =
      gDenote graph hAcyclic cpt anchor
        (.div
          (.mul
            (.cond intervention
              (intervention ∪ left ∪ right ∪ conditioning)
              (intervention ∪ left ∪ conditioning))
            (.cond intervention
              (intervention ∪ left ∪ conditioning)
              (intervention ∪ conditioning)))
          (.cond intervention
            (intervention ∪ right ∪ conditioning)
            (intervention ∪ conditioning))) := by
  simp only [gDenote]
  have hleftTop := truncSlice_ne_top graph hAcyclic cpt (doFinset intervention anchor)
    (intervention ∪ left ∪ conditioning) anchor
  have hbaseTop := truncSlice_ne_top graph hAcyclic cpt (doFinset intervention anchor)
    (intervention ∪ conditioning) anchor
  have hchain := ennreal_div_mul_div
    (truncSlice graph hAcyclic cpt (doFinset intervention anchor)
      (intervention ∪ left ∪ right ∪ conditioning) anchor)
    (truncSlice graph hAcyclic cpt (doFinset intervention anchor)
      (intervention ∪ left ∪ conditioning) anchor)
    (truncSlice graph hAcyclic cpt (doFinset intervention anchor)
      (intervention ∪ conditioning) anchor)
    hleft hleftTop
  rw [hchain]
  exact (ennreal_div_div_same _ _ _ hbase hbaseTop).symm

/-! ## Marginalization -/

omit [Fintype β] [MeasurableSpace β] in
lemma agreesOn_union {left right : Finset V} {anchor assignment : V → β} :
    agreesOn (left ∪ right) anchor assignment = true ↔
      agreesOn left anchor assignment = true ∧
        agreesOn right anchor assignment = true := by
  simp only [agreesOn_eq_true_iff, Finset.mem_union]
  constructor
  · intro hagree
    exact ⟨fun vertex hmember => hagree vertex (Or.inl hmember),
      fun vertex hmember => hagree vertex (Or.inr hmember)⟩
  · intro hagree vertex hmember
    rcases hmember with hleft | hright
    · exact hagree.1 vertex hleft
    · exact hagree.2 vertex hright

omit [Fintype β] [MeasurableSpace β] in
lemma agreesOn_extend_bound
    (bound : Finset V) (inn : {v // v ∈ bound} → β) (anchor assignment : V → β) :
    agreesOn bound (extendAnchor bound inn anchor) assignment = true ↔
      inn = innOf bound assignment := by
  rw [agreesOn_eq_true_iff]
  constructor
  · intro hagree
    funext vertex
    have hvalue := hagree vertex.1 vertex.2
    simpa [extendAnchor, glue, innOf, vertex.2] using hvalue.symm
  · intro hagree vertex hmember
    simp [extendAnchor, glue, innOf, hmember, hagree]

omit [Fintype β] [MeasurableSpace β] in
lemma agreesOn_extend_fixed
    {fixed bound : Finset V} (hdisj : Disjoint fixed bound)
    (inn : {v // v ∈ bound} → β) (anchor assignment : V → β) :
    agreesOn fixed (extendAnchor bound inn anchor) assignment =
      agreesOn fixed anchor assignment := by
  unfold agreesOn
  rw [decide_eq_decide]
  constructor
  · intro hagree vertex hmember
    have houtside : vertex ∉ bound := Finset.disjoint_left.mp hdisj hmember
    have hglue : extendAnchor bound inn anchor vertex = anchor vertex := by
      simp [extendAnchor, glue, houtside]
    exact (hagree vertex hmember).trans hglue
  · intro hagree vertex hmember
    have houtside : vertex ∉ bound := Finset.disjoint_left.mp hdisj hmember
    have hglue : extendAnchor bound inn anchor vertex = anchor vertex := by
      simp [extendAnchor, glue, houtside]
    exact (hagree vertex hmember).trans hglue.symm

omit [Fintype β] [MeasurableSpace β] in
lemma agrees_union_extend
    {fixed bound : Finset V} (hdisj : Disjoint fixed bound)
    (inn : {v // v ∈ bound} → β) (anchor assignment : V → β) :
    agreesOn (fixed ∪ bound) (extendAnchor bound inn anchor) assignment = true ↔
      agreesOn fixed anchor assignment = true ∧ inn = innOf bound assignment := by
  rw [agreesOn_union]
  constructor
  · intro hagree
    have hfixedEq := agreesOn_extend_fixed hdisj inn anchor assignment
    have hfixed : agreesOn fixed anchor assignment = true := by
      rw [← hfixedEq]
      exact hagree.1
    exact ⟨hfixed, (agreesOn_extend_bound bound inn anchor assignment).1 hagree.2⟩
  · intro hagree
    refine ⟨?_, (agreesOn_extend_bound bound inn anchor assignment).2 hagree.2⟩
    rw [agreesOn_extend_fixed hdisj inn anchor assignment]
    exact hagree.1

omit [Fintype V] [Fintype β] [DecidableEq β] [MeasurableSpace β] in
lemma doFinset_extend
    {intervention bound : Finset V} (hdisj : Disjoint intervention bound)
    (inn : {v // v ∈ bound} → β) (anchor : V → β) :
    doFinset intervention (extendAnchor bound inn anchor) = doFinset intervention anchor := by
  funext vertex
  simp only [doFinset]
  by_cases hmember : vertex ∈ intervention
  · have houtside : vertex ∉ bound := Finset.disjoint_left.mp hdisj hmember
    simp [hmember, extendAnchor, glue, houtside]
  · simp [hmember]

lemma truncSlice_extend_off
    {fixed bound : Finset V} (hdisj : Disjoint fixed bound)
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (assignment : V → Option β) (anchor : V → β)
    (inn : {v // v ∈ bound} → β) :
    truncSlice graph hAcyclic cpt assignment fixed (extendAnchor bound inn anchor) =
      truncSlice graph hAcyclic cpt assignment fixed anchor := by
  unfold truncSlice
  refine Finset.sum_congr rfl fun assignmentRow _ => ?_
  rw [agreesOn_extend_fixed hdisj inn anchor assignmentRow]

lemma slice_sum_extensions
    {fixed bound : Finset V} (hdisj : Disjoint fixed bound)
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (assignment : V → Option β) (anchor : V → β) :
    ∑ inn : {v // v ∈ bound} → β,
        truncSlice graph hAcyclic cpt assignment (fixed ∪ bound)
          (extendAnchor bound inn anchor) =
      truncSlice graph hAcyclic cpt assignment fixed anchor := by
  unfold truncSlice
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun assignmentRow _ => ?_
  by_cases hfixed : agreesOn fixed anchor assignmentRow = true
  · conv_rhs => rw [if_pos hfixed]
    have hinner : ∀ inn : {v // v ∈ bound} → β,
        (if agreesOn (fixed ∪ bound) (extendAnchor bound inn anchor) assignmentRow = true then
          truncatedWeight graph hAcyclic cpt assignment assignmentRow else 0) =
        if inn = innOf bound assignmentRow then
          truncatedWeight graph hAcyclic cpt assignment assignmentRow else 0 := by
      intro inn
      by_cases hinn : inn = innOf bound assignmentRow
      · have hagree :
            agreesOn (fixed ∪ bound) (extendAnchor bound inn anchor) assignmentRow = true :=
          (agrees_union_extend hdisj inn anchor assignmentRow).2 ⟨hfixed, hinn⟩
        exact (if_pos hagree).trans (if_pos hinn).symm
      · have hnot :
            agreesOn (fixed ∪ bound) (extendAnchor bound inn anchor) assignmentRow ≠ true := by
          intro htrue
          exact hinn ((agrees_union_extend hdisj inn anchor assignmentRow).1 htrue).2
        exact (if_neg hnot).trans (if_neg hinn).symm
    simp_rw [hinner]
    exact Fintype.sum_ite_eq' (innOf bound assignmentRow)
      (fun _ => truncatedWeight graph hAcyclic cpt assignment assignmentRow)
  · conv_rhs => rw [if_neg hfixed]
    refine Finset.sum_eq_zero fun inn _ => ?_
    have hnot :
        agreesOn (fixed ∪ bound) (extendAnchor bound inn anchor) assignmentRow ≠ true := by
      intro htrue
      exact hfixed ((agrees_union_extend hdisj inn anchor assignmentRow).1 htrue).1
    exact if_neg hnot

/-- Summing out a block disjoint from the intervention and from the remaining
event leaves the marginal conditional. -/
theorem marginal_sound
    {intervention outcome bound conditioning : Finset V}
    (hintervention : Disjoint bound intervention)
    (houtcome : Disjoint bound outcome)
    (hconditioning : Disjoint bound conditioning)
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (anchor : V → β) :
    gDenote graph hAcyclic cpt anchor
        (.sum bound
          (.cond intervention
            (intervention ∪ outcome ∪ bound ∪ conditioning)
            (intervention ∪ conditioning))) =
      gDenote graph hAcyclic cpt anchor
        (.cond intervention
          (intervention ∪ outcome ∪ conditioning)
          (intervention ∪ conditioning)) := by
  have hrest : Disjoint bound (intervention ∪ outcome ∪ conditioning) := by
    rw [Finset.disjoint_union_right, Finset.disjoint_union_right]
    exact ⟨⟨hintervention, houtcome⟩, hconditioning⟩
  have hfixed : Disjoint (intervention ∪ outcome ∪ conditioning) bound := hrest.symm
  have hassign : ∀ inn : {v // v ∈ bound} → β,
      doFinset intervention (extendAnchor bound inn anchor) =
        doFinset intervention anchor :=
    fun inn => doFinset_extend (hintervention.symm) inn anchor
  have hdenDisj : Disjoint (intervention ∪ conditioning) bound := by
    rw [Finset.disjoint_union_left]
    exact ⟨hintervention.symm, hconditioning.symm⟩
  have hden : ∀ inn : {v // v ∈ bound} → β,
      truncSlice graph hAcyclic cpt
          (doFinset intervention (extendAnchor bound inn anchor))
          (intervention ∪ conditioning)
          (extendAnchor bound inn anchor) =
        truncSlice graph hAcyclic cpt (doFinset intervention anchor)
          (intervention ∪ conditioning) anchor := by
    intro inn
    rw [hassign inn]
    exact truncSlice_extend_off graph hAcyclic hdenDisj cpt
      (doFinset intervention anchor) anchor inn
  simp only [gDenote]
  simp_rw [hden, hassign, sum_div_const]
  have hnum := slice_sum_extensions graph hAcyclic hfixed cpt
    (doFinset intervention anchor) anchor
  have hset : intervention ∪ outcome ∪ conditioning ∪ bound =
      intervention ∪ outcome ∪ bound ∪ conditioning := by
    ext vertex
    simp only [Finset.mem_union]
    tauto
  rw [← hset, hnum]

/-! ## Rules 2 and 3 on the proved branches -/

/-- Rule 2 under the parent condition. The d-separation premise of `rule2Rule`
is not the hypothesis used here. -/
theorem rule2_parent_sound
    {intervention exchanged outcome conditioning : Finset V}
    (hdisj : Disjoint intervention exchanged)
    (hparents : ∀ vertex ∈ exchanged, ∀ parent, graph.edges parent vertex →
      parent ∈ intervention ∪ exchanged ∪ conditioning)
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (anchor : V → β)
    (hagree : ∀ vertex ∈ exchanged, anchor vertex = anchor vertex)
    (hpos : truncSlice graph hAcyclic cpt (doFinset intervention anchor)
      (intervention ∪ exchanged ∪ conditioning) anchor ≠ 0) :
    gDenote graph hAcyclic cpt anchor
        (.cond (intervention ∪ exchanged)
          (intervention ∪ outcome ∪ exchanged ∪ conditioning)
          (intervention ∪ exchanged ∪ conditioning)) =
      gDenote graph hAcyclic cpt anchor
        (.cond intervention
          (intervention ∪ outcome ∪ exchanged ∪ conditioning)
          (intervention ∪ exchanged ∪ conditioning)) := by
  simp only [gDenote]
  have hmerge : mergeAssign intervention anchor anchor = anchor := by
    funext vertex
    unfold mergeAssign
    split_ifs
    · rfl
    · rfl
  have hrule := rule2_of_parents (X := intervention) (Y := outcome) (Z := exchanged)
    (W := conditioning) graph hAcyclic hdisj hparents cpt anchor anchor anchor hagree hpos
  rw [hmerge] at hrule
  exact hrule

/-- Rule 3 when the deleted set has no child outside the intervention. -/
theorem rule3_no_external_child_sound
    [Inhabited β]
    {intervention deleted outcome conditioning : Finset V}
    (hintervention : Disjoint intervention deleted)
    (houtcome : Disjoint outcome deleted)
    (hconditioning : Disjoint conditioning deleted)
    (houtside : ∀ source ∈ deleted, ∀ target, graph.edges source target →
      target ∈ intervention ∪ deleted)
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (anchor : V → β)
    (hpos : truncSlice graph hAcyclic cpt (doFinset intervention anchor)
      (intervention ∪ conditioning) anchor ≠ 0) :
    gDenote graph hAcyclic cpt anchor
        (.cond (intervention ∪ deleted)
          (intervention ∪ outcome ∪ conditioning)
          (intervention ∪ conditioning)) =
      gDenote graph hAcyclic cpt anchor
        (.cond intervention
          (intervention ∪ outcome ∪ conditioning)
          (intervention ∪ conditioning)) := by
  simp only [gDenote]
  have hmerge : mergeAssign intervention anchor anchor = anchor := by
    funext vertex
    unfold mergeAssign
    split_ifs
    · rfl
    · rfl
  have hrule := (rule3_cond_of_no_external_child (X := intervention) (Y := outcome)
    (Z := deleted) (W := conditioning) graph hAcyclic hintervention houtcome
    hconditioning houtside cpt anchor anchor anchor hpos).1
  rw [hmerge] at hrule
  exact hrule

/-! ## A fragment of the identification strategy -/

inductive IdAnswer (V : Type) where
  | doFree (expr : MassExpr V)
  | refuse
  deriving DecidableEq

def parentsIn (bound intervention conditioning : Finset V) : Bool :=
  decide (∀ vertex ∈ bound, ∀ parent, graph.edges parent vertex →
    parent ∈ intervention ∪ bound ∪ conditioning)

def noOutsideChild (bound intervention : Finset V) : Bool :=
  decide (∀ source ∈ bound, ∀ target, graph.edges source target →
    target ∈ intervention ∪ bound)

def deleteOK (outcome bound conditioning : Finset V) : Bool :=
  noOutsideChild graph bound ∅ && decide (Disjoint outcome bound) &&
    decide (Disjoint conditioning bound)

def exchangeSource (outcome bound conditioning : Finset V) : MassExpr V :=
  .cond bound (outcome ∪ bound ∪ conditioning) (bound ∪ conditioning)

def exchangeResult (outcome bound conditioning : Finset V) : MassExpr V :=
  .cond ∅ (outcome ∪ bound ∪ conditioning) (bound ∪ conditioning)

def deleteSource (outcome bound conditioning : Finset V) : MassExpr V :=
  .cond bound (outcome ∪ conditioning) conditioning

def deleteResult (outcome conditioning : Finset V) : MassExpr V :=
  .cond ∅ (outcome ∪ conditioning) conditioning

/-- Try the parent exchange with an empty outer intervention, then the
no-outside-child deletion, and refuse when neither branch applies. -/
def idFragment (outcome bound conditioning : Finset V) : IdAnswer V :=
  if parentsIn graph bound ∅ conditioning then
    .doFree (exchangeResult outcome bound conditioning)
  else if deleteOK graph outcome bound conditioning then
    .doFree (deleteResult outcome conditioning)
  else
    .refuse

omit [Fintype V] in
theorem exchange_result_doFree (outcome bound conditioning : Finset V) :
    doFree (exchangeResult outcome bound conditioning) = true := by
  simp [exchangeResult, doFree]

omit [Fintype V] in
theorem delete_result_doFree (outcome conditioning : Finset V) :
    doFree (deleteResult outcome conditioning) = true := by
  simp [deleteResult, doFree]

theorem id_exchange_sound
    (outcome bound conditioning : Finset V)
    (hparents : parentsIn graph bound ∅ conditioning = true)
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (anchor : V → β)
    (hpos : truncSlice graph hAcyclic cpt (doFinset (∅ : Finset V) anchor)
      (bound ∪ conditioning) anchor ≠ 0) :
    idFragment graph outcome bound conditioning =
        .doFree (exchangeResult outcome bound conditioning) ∧
      gDenote graph hAcyclic cpt anchor (exchangeSource outcome bound conditioning) =
        gDenote graph hAcyclic cpt anchor
          (exchangeResult outcome bound conditioning) := by
  refine ⟨by simp [idFragment, hparents], ?_⟩
  have hcovered : ∀ vertex ∈ bound, ∀ parent, graph.edges parent vertex →
      parent ∈ (∅ : Finset V) ∪ bound ∪ conditioning := by
    rw [parentsIn, decide_eq_true_eq] at hparents
    exact hparents
  have hposRule : truncSlice graph hAcyclic cpt (doFinset (∅ : Finset V) anchor)
      ((∅ : Finset V) ∪ bound ∪ conditioning) anchor ≠ 0 := by
    simpa [Finset.empty_union] using hpos
  have hrule := rule2_parent_sound (intervention := (∅ : Finset V)) (exchanged := bound)
    (outcome := outcome) (conditioning := conditioning) graph hAcyclic
    (Finset.disjoint_empty_left bound) hcovered cpt anchor (fun _ _ => rfl) hposRule
  simpa [exchangeSource, exchangeResult, Finset.empty_union] using hrule

theorem id_delete_sound
    [Inhabited β]
    (outcome bound conditioning : Finset V)
    (hparents : parentsIn graph bound ∅ conditioning = false)
    (hdelete : deleteOK graph outcome bound conditioning = true)
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (anchor : V → β)
    (hpos : truncSlice graph hAcyclic cpt (doFinset (∅ : Finset V) anchor)
      conditioning anchor ≠ 0) :
    idFragment graph outcome bound conditioning =
        .doFree (deleteResult outcome conditioning) ∧
      gDenote graph hAcyclic cpt anchor (deleteSource outcome bound conditioning) =
        gDenote graph hAcyclic cpt anchor (deleteResult outcome conditioning) := by
  refine ⟨by simp [idFragment, hparents, hdelete], ?_⟩
  have hparts : (noOutsideChild graph bound ∅ = true ∧ Disjoint outcome bound) ∧
      Disjoint conditioning bound := by
    simp only [deleteOK, Bool.and_eq_true, decide_eq_true_eq] at hdelete
    exact hdelete
  have houtside : ∀ source ∈ bound, ∀ target, graph.edges source target →
      target ∈ (∅ : Finset V) ∪ bound := by
    have hchild : noOutsideChild graph bound ∅ = true := hparts.1.1
    rw [noOutsideChild, decide_eq_true_eq] at hchild
    exact hchild
  have hposRule : truncSlice graph hAcyclic cpt (doFinset (∅ : Finset V) anchor)
      ((∅ : Finset V) ∪ conditioning) anchor ≠ 0 := by
    simpa [Finset.empty_union] using hpos
  have hrule := rule3_no_external_child_sound (intervention := (∅ : Finset V))
    (deleted := bound) (outcome := outcome) (conditioning := conditioning)
    graph hAcyclic (Finset.disjoint_empty_left bound) hparts.1.2 hparts.2
    houtside cpt anchor hposRule
  simpa [deleteSource, deleteResult, Finset.empty_union] using hrule

/-! ## The bow has no do-free normal form -/

theorem bow_id_refuses :
    idFragment bowGraph {Bow.y} {Bow.x} (∅ : Finset Bow) = .refuse := by
  decide

/-- A do-free expression cannot denote `P(Y = true | do(X = true))` on every
bow table. The two tables are one observational joint and two effects, which
is the non-trivial fibre `bowFiber`. -/
theorem bow_has_no_do_free_form
    (expr : MassExpr Bow) (anchor : Bow → Bool)
    (hfree : doFree expr = true)
    (hdenote : ∀ cpt : (network (β := Bool) bowGraph bowAcyclic).DiscreteCPT,
      gDenote bowGraph bowAcyclic cpt anchor expr = bowQuery cpt) :
    False := by
  have hfactor := doFree_factors_through_joint bowGraph bowAcyclic expr hfree anchor
  have hidentified : Factors bowShadow bowQuery := by
    rcases hfactor with ⟨recover, hrecover⟩
    refine ⟨recover, fun cpt => ?_⟩
    rw [← hdenote cpt]
    exact hrecover cpt
  exact bow_query_not_identified hidentified

/-! ## Back-door and front-door, checked against the g-formula -/

theorem backDoor_factors (treatment outcome : V) (treatmentValue outcomeValue : β) :
    Factors
      (fun cpt : PositiveAt graph hAcyclic treatment treatmentValue => cpt.1.jointWeight)
      (fun cpt => interventionalMass graph hAcyclic cpt.1 treatment outcome
        treatmentValue outcomeValue) :=
  parent_adjustment_identified graph hAcyclic treatment outcome treatmentValue outcomeValue

theorem backDoor_matches_adjustment
    (treatment outcome : V) (treatmentValue outcomeValue : β)
    (cpt : PositiveAt graph hAcyclic treatment treatmentValue) :
    interventionalMass graph hAcyclic cpt.1 treatment outcome
        treatmentValue outcomeValue =
      adjustOfJoint graph treatment outcome treatmentValue outcomeValue
        cpt.1.jointWeight := by
  rw [parentAdjustment graph hAcyclic cpt.1 treatment outcome treatmentValue outcomeValue cpt.2]
  unfold parentMass
  rfl

theorem frontDoor_factors (treatmentValue outcomeValue : β) :
    Factors
      (fun cpt : FrontPositive treatmentValue => cpt.1.jointWeight)
      (fun cpt => doMass cpt.1 treatmentValue outcomeValue) :=
  front_door_identified treatmentValue outcomeValue

theorem frontDoor_matches_formula
    (treatmentValue outcomeValue : β)
    (cpt : (network (β := β) smokeGraph smokeAcyclic).DiscreteCPT)
    (hsmoking : obs cpt (fun assignment => assignment .s = treatmentValue) ≠ 0)
    (htar : ∀ smoking tar, pt cpt smoking tar ≠ 0) :
    doMass cpt treatmentValue outcomeValue =
      frontDoorOf treatmentValue outcomeValue cpt.jointWeight := by
  rw [frontDoor cpt treatmentValue outcomeValue hsmoking htar]
  simp only [obs_eq_smokeMass]
  rfl

omit [Fintype β] in
/-- Doing one set and then a disjoint set is the g-formula of the union, in
either order. -/
theorem two_interventions_agree
    {intervention exchanged : Finset V} (hdisj : Disjoint intervention exchanged)
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (valueIntervention valueExchanged configuration : V → β) :
    (intervenedFinsetCPT (deleteIncoming graph intervention)
        (deleteIncoming_acyclic graph hAcyclic intervention)
        (intervenedFinsetCPT graph hAcyclic cpt intervention valueIntervention)
        exchanged valueExchanged).jointWeight configuration =
      (intervenedFinsetCPT (deleteIncoming graph exchanged)
          (deleteIncoming_acyclic graph hAcyclic exchanged)
          (intervenedFinsetCPT graph hAcyclic cpt exchanged valueExchanged)
          intervention valueIntervention).jointWeight configuration ∧
      (intervenedFinsetCPT (deleteIncoming graph intervention)
          (deleteIncoming_acyclic graph hAcyclic intervention)
          (intervenedFinsetCPT graph hAcyclic cpt intervention valueIntervention)
          exchanged valueExchanged).jointWeight configuration =
        (intervenedFinsetCPT graph hAcyclic cpt (intervention ∪ exchanged)
          (mergeAssign intervention valueIntervention valueExchanged)).jointWeight
          configuration :=
  do_then_do_comm_eq_union graph hAcyclic hdisj cpt valueIntervention valueExchanged
    configuration

end Mettapedia.GSLT.Causality.DoCalculus
