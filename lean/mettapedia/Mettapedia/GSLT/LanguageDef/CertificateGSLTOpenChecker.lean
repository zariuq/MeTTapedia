import Mettapedia.GSLT.LanguageDef.CertificateGSLTIndexed

/-!
# Executable checking of open proof templates

`OpenDerivation` is the trusted Type-valued calculus of premise holes and rule
applications.  This module supplies its untrusted wire representation and a
fuel-free checker.  Successful checking reconstructs an open derivation with
exactly the submitted tree; erasing any typed open derivation is accepted.

Premise references are natural-number positions in the ordered context.  A
reference outside that context fails closed.  Equal judgments at different
positions remain distinguishable because their positions remain in the raw
artifact.
-/

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLT

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker

/-- Untrusted open proof tree.  `premise i` cites the `i`th premise occurrence;
`node` applies one ordinary presentation rule. -/
inductive RawOpenProof where
  | premise (index : Nat)
  | node (ruleInstance : RuleInstance) (children : List RawOpenProof)
deriving Repr

/-- Primitive rule-node count of the expanded open proof tree. -/
def RawOpenProof.ruleCount : RawOpenProof → Nat
  | .premise _ => 0
  | .node _ children => children.foldl (fun total child =>
      total + child.ruleCount) 0 + 1

mutual

/-- Fuel-free checker for one open proof tree. -/
def checkOpenRaw (presentation : ValidatedPresentation)
    (context : List Pattern) : Pattern → RawOpenProof → Bool
  | goal, .premise index =>
      match context[index]? with
      | none => false
      | some premise => decide (premise = goal)
  | goal, .node ruleInstance children =>
      match instantiateRule? presentation ruleInstance with
      | none => false
      | some (premises, conclusion) =>
          decide (conclusion = goal) &&
            checkOpenRawChildren presentation context premises children
termination_by _ proof => sizeOf proof

/-- Ordered-child checker for open proof trees. -/
def checkOpenRawChildren (presentation : ValidatedPresentation)
    (context : List Pattern) :
    List Pattern → List RawOpenProof → Bool
  | [], [] => true
  | premise :: premises, child :: children =>
      checkOpenRaw presentation context premise child &&
        checkOpenRawChildren presentation context premises children
  | _, _ => false
termination_by _ children => sizeOf children

end

mutual

/-- Erase a typed open derivation to the executable wire tree. -/
def OpenDerivation.eraseOpen
    {presentation : ValidatedPresentation} {context : List Pattern}
    {goal : Pattern} :
    OpenDerivation presentation context goal → RawOpenProof
  | .assumption index => .premise index.val
  | .byRule ruleInstance _ children =>
      .node ruleInstance children.eraseOpen

/-- Pointwise open-proof erasure. -/
def OpenDerivationList.eraseOpen
    {presentation : ValidatedPresentation} {context goals : List Pattern} :
    OpenDerivationList presentation context goals → List RawOpenProof
  | .nil => []
  | .cons head tail => head.eraseOpen :: tail.eraseOpen

end

mutual

/-- Erasure of every typed open derivation is accepted. -/
theorem checkOpenRaw_erase
    {presentation : ValidatedPresentation} {context : List Pattern}
    {goal : Pattern}
    (derivation : OpenDerivation presentation context goal) :
    checkOpenRaw presentation context goal derivation.eraseOpen = true := by
  cases derivation with
  | assumption index =>
      simp [OpenDerivation.eraseOpen, checkOpenRaw]
  | byRule ruleInstance application children =>
      have instantiated :=
        instantiateRule?_eq_some_iff_application.mpr application
      simp [OpenDerivation.eraseOpen, checkOpenRaw, instantiated,
        checkOpenRawChildren_erase children]

/-- Ordered erasures are accepted against their ordered judgment vector. -/
theorem checkOpenRawChildren_erase
    {presentation : ValidatedPresentation} {context goals : List Pattern}
    (derivations : OpenDerivationList presentation context goals) :
    checkOpenRawChildren presentation context goals derivations.eraseOpen =
      true := by
  cases derivations with
  | nil => simp [OpenDerivationList.eraseOpen, checkOpenRawChildren]
  | cons head tail =>
      simp [OpenDerivationList.eraseOpen, checkOpenRawChildren,
        checkOpenRaw_erase head, checkOpenRawChildren_erase tail]

end

mutual

/-- Successful raw-template checking reconstructs a typed open derivation
with exactly the submitted erasure. -/
theorem checkOpenRaw_exact_derivation
    {presentation : ValidatedPresentation} {context : List Pattern}
    {goal : Pattern} {proof : RawOpenProof}
    (checked : checkOpenRaw presentation context goal proof = true) :
    ∃ derivation : OpenDerivation presentation context goal,
      derivation.eraseOpen = proof := by
  cases proof with
  | premise index =>
      simp only [checkOpenRaw] at checked
      cases lookup : context[index]? with
      | none => simp [lookup] at checked
      | some premise =>
          simp only [lookup, decide_eq_true_eq] at checked
          have lookupFacts := List.getElem?_eq_some_iff.mp lookup
          have bound : index < context.length := lookupFacts.1
          have value : context.get ⟨index, bound⟩ = premise := lookupFacts.2
          subst goal
          rw [← value]
          exact ⟨.assumption ⟨index, bound⟩, rfl⟩
  | node ruleInstance children =>
      simp only [checkOpenRaw] at checked
      cases instantiated : instantiateRule? presentation ruleInstance with
      | none => simp [instantiated] at checked
      | some result =>
          rcases result with ⟨premises, conclusion⟩
          simp only [instantiated, Bool.and_eq_true, decide_eq_true_eq] at checked
          rcases checked with ⟨conclusionShape, childrenChecked⟩
          subst goal
          have application :
              RuleApplication presentation ruleInstance premises conclusion :=
            instantiateRule?_eq_some_iff_application.mp instantiated
          rcases checkOpenRawChildren_exact_derivations childrenChecked with
            ⟨derivations, erased⟩
          exact ⟨.byRule ruleInstance application derivations, by
            simp [OpenDerivation.eraseOpen, erased]⟩
termination_by sizeOf proof

/-- Successful ordered-child checking reconstructs exact typed children. -/
theorem checkOpenRawChildren_exact_derivations
    {presentation : ValidatedPresentation} {context : List Pattern}
    {goals : List Pattern} {proofs : List RawOpenProof}
    (checked :
      checkOpenRawChildren presentation context goals proofs = true) :
    ∃ derivations : OpenDerivationList presentation context goals,
      derivations.eraseOpen = proofs := by
  cases goals with
  | nil =>
      cases proofs with
      | nil => exact ⟨.nil, rfl⟩
      | cons proof proofs => simp [checkOpenRawChildren] at checked
  | cons goal goals =>
      cases proofs with
      | nil => simp [checkOpenRawChildren] at checked
      | cons proof proofs =>
          simp only [checkOpenRawChildren, Bool.and_eq_true] at checked
          rcases checkOpenRaw_exact_derivation checked.1 with
            ⟨head, headErased⟩
          rcases checkOpenRawChildren_exact_derivations checked.2 with
            ⟨tail, tailErased⟩
          exact ⟨.cons head tail, by
            simp [OpenDerivationList.eraseOpen, headErased, tailErased]⟩
termination_by sizeOf proofs

end

/-- Native accepted open-proof subtype. -/
def CheckedOpenProof (object : Object) (context : List Pattern)
    (goal : Pattern) :=
  { proof : RawOpenProof //
    checkOpenRaw object.presentation context goal proof = true }

/-- Checked open evidence and typed open derivations are extensionally
equivalent at the existence boundary. -/
theorem checkedOpenProof_nonempty_iff_openDerivation
    {object : Object} {context : List Pattern} {goal : Pattern} :
    Nonempty (CheckedOpenProof object context goal) ↔
      Nonempty (OpenDerivation object.presentation context goal) := by
  constructor
  · rintro ⟨⟨proof, checked⟩⟩
    rcases checkOpenRaw_exact_derivation checked with ⟨derivation, _⟩
    exact ⟨derivation⟩
  · rintro ⟨derivation⟩
    exact ⟨⟨derivation.eraseOpen, checkOpenRaw_erase derivation⟩⟩

end Mettapedia.GSLT.LanguageDef.CertificateGSLT
