import Mettapedia.GSLT.LanguageDef.ProofGSLTOpenChecker

/-!
# Raw substitution of open proof trees

Open derivations substitute by `bind`.  This module supplies the matching
operation on the untrusted wire representation: replacing each premise
citation by a raw proof.  Erasure is a homomorphism from typed `bind` to raw
substitution, which is what lets chronological DAG composition state its
expansion theorem entirely at the artifact level.

Substitution against an environment list leaves out-of-range citations
unchanged, so the operation is total and the rule-count accounting below is
exact without side conditions: an out-of-range citation contributes zero
because the untouched citation has zero rule nodes.
-/

namespace Mettapedia.GSLT.LanguageDef.ProofGSLT

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker

namespace RawOpenProof

mutual

/-- Replace each premise citation by the proof at its position.  Citations
outside the environment remain citations. -/
def substitute (environment : List RawOpenProof) : RawOpenProof → RawOpenProof
  | .premise index => environment.getD index (.premise index)
  | .node ruleInstance children =>
      .node ruleInstance (substituteList environment children)

/-- Pointwise substitution into ordered children. -/
def substituteList (environment : List RawOpenProof) :
    List RawOpenProof → List RawOpenProof
  | [] => []
  | proof :: proofs =>
      substitute environment proof :: substituteList environment proofs

end

@[simp] theorem substitute_premise (environment : List RawOpenProof)
    (index : Nat) :
    substitute environment (.premise index) =
      environment.getD index (.premise index) := by
  rw [substitute]

@[simp] theorem substitute_node (environment : List RawOpenProof)
    (ruleInstance : RuleInstance) (children : List RawOpenProof) :
    substitute environment (.node ruleInstance children) =
      .node ruleInstance (substituteList environment children) := by
  rw [substitute]

@[simp] theorem substituteList_nil (environment : List RawOpenProof) :
    substituteList environment [] = [] := by
  rw [substituteList]

@[simp] theorem substituteList_cons (environment : List RawOpenProof)
    (proof : RawOpenProof) (proofs : List RawOpenProof) :
    substituteList environment (proof :: proofs) =
      substitute environment proof :: substituteList environment proofs := by
  rw [substituteList]

mutual

/-- Substitution by the empty environment is the identity. -/
theorem substitute_nil (proof : RawOpenProof) :
    substitute [] proof = proof := by
  cases proof with
  | premise index => simp [List.getD]
  | node ruleInstance children => simp [substituteList_nil' children]

/-- Pointwise identity of empty-environment substitution. -/
theorem substituteList_nil' (proofs : List RawOpenProof) :
    substituteList [] proofs = proofs := by
  cases proofs with
  | nil => simp
  | cons proof proofs => simp [substitute_nil proof, substituteList_nil' proofs]

end

mutual

/-- Number of citations of one premise position in an open proof tree. -/
def premiseCitations (index : Nat) : RawOpenProof → Nat
  | .premise cited => if cited = index then 1 else 0
  | .node _ children => premiseCitationsList index children

/-- Total citations of one premise position across ordered children. -/
def premiseCitationsList (index : Nat) : List RawOpenProof → Nat
  | [] => 0
  | proof :: proofs =>
      premiseCitations index proof + premiseCitationsList index proofs

end

@[simp] theorem premiseCitations_premise (index cited : Nat) :
    premiseCitations index (.premise cited) =
      if cited = index then 1 else 0 := by
  rw [premiseCitations]

@[simp] theorem premiseCitations_node (index : Nat)
    (ruleInstance : RuleInstance) (children : List RawOpenProof) :
    premiseCitations index (.node ruleInstance children) =
      premiseCitationsList index children := by
  rw [premiseCitations]

@[simp] theorem premiseCitationsList_nil (index : Nat) :
    premiseCitationsList index [] = 0 := by
  rw [premiseCitationsList]

@[simp] theorem premiseCitationsList_cons (index : Nat)
    (proof : RawOpenProof) (proofs : List RawOpenProof) :
    premiseCitationsList index (proof :: proofs) =
      premiseCitations index proof + premiseCitationsList index proofs := by
  rw [premiseCitationsList]

/-- Ordered-children rule count as a plain sum. -/
theorem ruleCount_node (ruleInstance : RuleInstance)
    (children : List RawOpenProof) :
    ruleCount (.node ruleInstance children) =
      (children.map ruleCount).sum + 1 := by
  have foldGeneral : ∀ (proofs : List RawOpenProof) (start : Nat),
      proofs.foldl (fun total child => total + child.ruleCount) start =
        start + (proofs.map ruleCount).sum := by
    intro proofs
    induction proofs with
    | nil => intro start; simp
    | cons proof proofs inductionHypothesis =>
        intro start
        simp [inductionHypothesis, Nat.add_assoc]
  rw [ruleCount, foldGeneral]
  simp

/-- The rule-node weight an environment contributes at one cited position. -/
def environmentWeight (environment : List RawOpenProof) (index : Nat) : Nat :=
  ((environment.getD index (.premise index))).ruleCount

/-- Total rule-node weight of a proof's citations into an environment. -/
def citationWeight (environment : List RawOpenProof)
    (proof : RawOpenProof) : Nat :=
  ((List.range environment.length).map
    (fun index =>
      premiseCitations index proof * environmentWeight environment index)).sum

/-- Total citation weight across ordered children. -/
def citationWeightList (environment : List RawOpenProof)
    (proofs : List RawOpenProof) : Nat :=
  ((List.range environment.length).map
    (fun index =>
      premiseCitationsList index proofs *
        environmentWeight environment index)).sum

theorem citationWeightList_nil (environment : List RawOpenProof) :
    citationWeightList environment [] = 0 := by
  simp [citationWeightList]

private theorem sum_map_add_mul (indices : List Nat)
    (first second weight : Nat → Nat) :
    (indices.map (fun index =>
      (first index + second index) * weight index)).sum =
      (indices.map (fun index => first index * weight index)).sum +
        (indices.map (fun index => second index * weight index)).sum := by
  induction indices with
  | nil => simp
  | cons head tail inductionHypothesis =>
      simp only [List.map_cons, List.sum_cons, inductionHypothesis]
      rw [Nat.add_mul]
      omega

private theorem sum_map_zero (indices : List Nat) (values : Nat → Nat)
    (zero : ∀ index ∈ indices, values index = 0) :
    (indices.map values).sum = 0 := by
  induction indices with
  | nil => simp
  | cons head tail inductionHypothesis =>
      simp only [List.map_cons, List.sum_cons]
      rw [zero head (by simp),
        inductionHypothesis
          (fun index mem => zero index (List.mem_cons_of_mem head mem))]

private theorem sum_map_single (indices : List Nat) (target : Nat)
    (weight : Nat → Nat) (nodup : indices.Nodup) (mem : target ∈ indices) :
    (indices.map (fun index =>
      (if target = index then 1 else 0) * weight index)).sum =
      weight target := by
  induction indices with
  | nil => simp at mem
  | cons head tail inductionHypothesis =>
      rcases List.mem_cons.mp mem with equal | inTail
      · subst equal
        simp only [List.map_cons, List.sum_cons]
        have tailZero : (tail.map (fun index =>
            (if target = index then 1 else 0) * weight index)).sum = 0 := by
          apply sum_map_zero
          intro index memIndex
          have notEqual : target ≠ index := by
            intro equal
            have inTail : target ∈ tail := by rw [equal]; exact memIndex
            exact (List.nodup_cons.mp nodup).1 inTail
          simp [notEqual]
        rw [tailZero]
        simp only [if_true]
        omega
      · have notEqual : target ≠ head := by
          intro equal
          have selfInTail : head ∈ tail := by rw [← equal]; exact inTail
          exact (List.nodup_cons.mp nodup).1 selfInTail
        simp only [List.map_cons, List.sum_cons, if_neg notEqual,
          Nat.zero_mul, Nat.zero_add]
        exact inductionHypothesis (List.nodup_cons.mp nodup).2 inTail

theorem citationWeightList_cons (environment : List RawOpenProof)
    (proof : RawOpenProof) (proofs : List RawOpenProof) :
    citationWeightList environment (proof :: proofs) =
      citationWeight environment proof +
        citationWeightList environment proofs := by
  unfold citationWeightList citationWeight
  simp only [premiseCitationsList_cons]
  exact sum_map_add_mul (List.range environment.length) _ _ _

/-- A premise citation weighs exactly the rule count of the environment
proof at its position; out-of-range citations weigh zero on both sides. -/
theorem citationWeight_premise (environment : List RawOpenProof)
    (index : Nat) :
    citationWeight environment (.premise index) =
      environmentWeight environment index := by
  unfold citationWeight
  simp only [premiseCitations_premise]
  by_cases bound : index < environment.length
  · exact sum_map_single (List.range environment.length) index
      (environmentWeight environment) List.nodup_range
      (List.mem_range.mpr bound)
  · have envZero : environmentWeight environment index = 0 := by
      have outOfRange : environment[index]? = none :=
        List.getElem?_eq_none (by omega)
      simp [environmentWeight, List.getD_eq_getElem?_getD, outOfRange,
        ruleCount]
    rw [envZero]
    apply sum_map_zero
    intro position positionMem
    have notEqual : index ≠ position := by
      intro equal
      exact bound (equal ▸ List.mem_range.mp positionMem)
    simp [notEqual]

mutual

/-- Exact rule-count accounting for substitution: the substituted tree has
the original rule nodes plus, for every premise position, its citation count
times the rule count of the substituted proof. -/
theorem substitute_ruleCount (environment : List RawOpenProof)
    (proof : RawOpenProof) :
    (substitute environment proof).ruleCount =
      proof.ruleCount + citationWeight environment proof := by
  cases proof with
  | premise index =>
      simp [substitute_premise, citationWeight_premise, ruleCount,
        environmentWeight, List.getD_eq_getElem?_getD]
  | node ruleInstance children =>
      simp only [substitute_node, ruleCount_node]
      rw [substituteList_ruleCount environment children]
      have citationsEqual : citationWeight environment
          (.node ruleInstance children) =
            citationWeightList environment children := by
        unfold citationWeight citationWeightList
        simp
      omega

/-- Ordered-children analogue of the substitution rule-count law. -/
theorem substituteList_ruleCount (environment : List RawOpenProof)
    (proofs : List RawOpenProof) :
    ((substituteList environment proofs).map ruleCount).sum =
      (proofs.map ruleCount).sum + citationWeightList environment proofs := by
  cases proofs with
  | nil => simp [citationWeightList_nil]
  | cons proof proofs =>
      simp only [substituteList_cons, List.map_cons, List.sum_cons]
      rw [substitute_ruleCount environment proof,
        substituteList_ruleCount environment proofs,
        citationWeightList_cons]
      omega

end

end RawOpenProof

/-! ## Erasure is a homomorphism from typed plugging to raw substitution -/

namespace OpenDerivationList

/-- Erasure preserves ordered length. -/
theorem length_eraseOpen {presentation : ValidatedPresentation}
    {context goals : List Pattern}
    (derivations : OpenDerivationList presentation context goals) :
    derivations.eraseOpen.length = goals.length := by
  cases derivations with
  | nil => rfl
  | cons head tail =>
      simp [OpenDerivationList.eraseOpen, length_eraseOpen tail]

/-- Positional lookup of an erased environment is erasure of the typed
lookup. -/
theorem eraseOpen_getD {presentation : ValidatedPresentation}
    {context goals : List Pattern}
    (derivations : OpenDerivationList presentation context goals)
    (index : Fin goals.length) (fallback : RawOpenProof) :
    derivations.eraseOpen.getD index.val fallback =
      (derivations.get index).eraseOpen := by
  cases derivations with
  | nil => exact Fin.elim0 index
  | cons head tail =>
      refine Fin.cases ?_ (fun tailIndex => ?_) index
      · rfl
      · simpa [OpenDerivationList.eraseOpen, OpenDerivationList.get] using
          eraseOpen_getD tail tailIndex fallback

end OpenDerivationList

mutual

/-- Erasing a plugged derivation is raw substitution of the erasures. -/
theorem OpenDerivation.eraseOpen_bind
    {presentation : ValidatedPresentation}
    {sourceContext targetContext : List Pattern} {goal : Pattern}
    (derivation : OpenDerivation presentation sourceContext goal)
    (environment :
      OpenDerivationList presentation targetContext sourceContext) :
    (derivation.bind environment).eraseOpen =
      RawOpenProof.substitute environment.eraseOpen derivation.eraseOpen := by
  cases derivation with
  | assumption index =>
      simp only [OpenDerivation.bind, OpenDerivation.eraseOpen,
        RawOpenProof.substitute_premise]
      exact (OpenDerivationList.eraseOpen_getD environment index _).symm
  | byRule ruleInstance application children =>
      simp only [OpenDerivation.bind, OpenDerivation.eraseOpen,
        RawOpenProof.substitute_node]
      rw [OpenDerivationList.eraseOpen_bind children environment]

/-- Pointwise erasure/plugging exchange for ordered children. -/
theorem OpenDerivationList.eraseOpen_bind
    {presentation : ValidatedPresentation}
    {sourceContext targetContext goals : List Pattern}
    (derivations : OpenDerivationList presentation sourceContext goals)
    (environment :
      OpenDerivationList presentation targetContext sourceContext) :
    (derivations.bind environment).eraseOpen =
      RawOpenProof.substituteList environment.eraseOpen
        derivations.eraseOpen := by
  cases derivations with
  | nil => rfl
  | cons head tail =>
      simp only [OpenDerivationList.bind, OpenDerivationList.eraseOpen,
        RawOpenProof.substituteList_cons]
      rw [OpenDerivation.eraseOpen_bind head environment,
        OpenDerivationList.eraseOpen_bind tail environment]

end

end Mettapedia.GSLT.LanguageDef.ProofGSLT
