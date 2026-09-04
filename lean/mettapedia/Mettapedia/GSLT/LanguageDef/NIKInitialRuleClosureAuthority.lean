import Mettapedia.GSLT.LanguageDef.NIKMetalogic
import Mettapedia.OSLF.Framework.InitialModalSchema

/-!
# Least rule closure as a NIK authority

`InitialModalSchema` separates two free constructions: raw formulas are the
free algebra for the OSLF formula signature, while derivability is the least
predicate closed under a specified rule relation.  This module connects the
second construction to NIK without identifying replay with meaning.

A qualified rule system supplies four independent pieces:

* a specified rule relation;
* an executable and exact rule-instance witness;
* a semantic predicate on judgments;
* a proof that every specified rule preserves that predicate.

The resulting NIK theory uses least rule closure as proof scope and the
supplied predicate as meaning.  Its certificates are finite witnessed
derivation trees.  Thus the same construction covers schematic-substitution
and hypothetical-judgment disciplines while retaining their different syntax
and rule witnesses.

The examples below are deliberately fragments exhibiting the MM0/Metamath and
Isabelle/Pure styles.  They are not implementations of either full framework.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NIKInitialRuleClosureAuthority

open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.Logic
open Mettapedia.OSLF.Framework.InitialModalSchema
open Mettapedia.OSLF.Formula
open Mettapedia.OSLF.MeTTaIL.Syntax

universe u v

/-! ## Generic qualified rule systems -/

/-- A specified rule system with an exact executable instance witness and an
independently supplied semantic interpretation. -/
structure QualifiedRuleSystem (Judgment : Type u) : Type (max (u + 1) (v + 1)) where
  rules : List Judgment -> Judgment -> Prop
  witness : RuleWitness.{u, v} rules
  Meaning : Judgment -> Prop
  rules_sound : forall premises conclusion,
    rules premises conclusion ->
      (forall premise, premise ∈ premises -> Meaning premise) ->
        Meaning conclusion

namespace QualifiedRuleSystem

variable {Judgment : Type u}

/-- Least generated derivability is proof scope; semantic meaning is supplied
separately and contains that scope by rule soundness. -/
def theory (ruleSystem : QualifiedRuleSystem.{u, v} Judgment) :
    TheoryFamily Unit where
  Signature := Unit
  signatureOf := fun _kind => ()
  Claim := fun _kind => Judgment
  Scope := fun _kind => Derives ruleSystem.rules
  Meaning := fun _kind => ruleSystem.Meaning
  scope_sound := by
    intro _kind claim derivation
    exact Derives.least ruleSystem.Meaning ruleSystem.rules_sound derivation

/-- The native proof object is the witnessed derivation tree itself.  Its
judgment is structural validity plus equality of the root conclusion. -/
def evidenceDiscipline (ruleSystem : QualifiedRuleSystem.{u, v} Judgment) :
    EvidenceDiscipline (theory ruleSystem) where
  ProofObject := fun _kind => Derivation Judgment ruleSystem.witness.W
  Proves := fun _kind derivation claim =>
    derivation.valid ruleSystem.witness = true ∧ derivation.concl = claim
  scope_iff_proof := by
    intro _kind claim
    constructor
    · intro inScope
      exact Derives.exists_derivation ruleSystem.witness inScope
    · rintro ⟨derivation, valid, concludes⟩
      exact concludes ▸ Derivation.valid_sound ruleSystem.witness derivation valid

/-- The profile-blind finite replay checker.  Semantic meaning is absent from
its inputs and from its computation. -/
def checker [DecidableEq Judgment]
    (ruleSystem : QualifiedRuleSystem.{u, v} Judgment) :=
  replayChecker ruleSystem.witness

/-- Finite replay is an exact NIK authority for least rule closure. -/
def contract [DecidableEq Judgment]
    (ruleSystem : QualifiedRuleSystem.{u, v} Judgment) :
    AuthorityContract (theory ruleSystem) where
  Certificate := fun _kind => Derivation Judgment ruleSystem.witness.W
  checker := fun _kind => checker ruleSystem
  scopeAuthority := fun _kind => replayChecker_authority ruleSystem.witness

/-- The replay boundary preserves the whole accepted derivation fibre.  The
proof is not merely theorem-existence equivalence: both directions retain the
same witnessed derivation tree. -/
def certificateEquivalence [DecidableEq Judgment]
    (ruleSystem : QualifiedRuleSystem.{u, v} Judgment) :
    CertificateEquivalence
      (checker ruleSystem)
      ((evidenceDiscipline ruleSystem).proofSystem ()) where
  fibreEquiv := fun claim =>
    { toFun := fun accepted =>
        ⟨accepted.1, by
          change accepted.1.valid ruleSystem.witness = true ∧
            accepted.1.concl = claim
          simpa [checker, replayChecker] using accepted.2⟩
      invFun := fun native =>
        ⟨native.1, by
          have judged : native.1.valid ruleSystem.witness = true ∧
              native.1.concl = claim := by
            simpa [evidenceDiscipline, EvidenceDiscipline.proofSystem] using native.2
          simpa [checker, replayChecker, Bool.and_eq_true] using judged⟩
      left_inv := by
        intro accepted
        apply Subtype.ext
        rfl
      right_inv := by
        intro native
        apply Subtype.ext
        rfl }

/-- The qualified rule system therefore supplies both an ordinary exact
scope contract and the stronger native proof-fibre boundary. -/
def proofCarryingAuthority [DecidableEq Judgment]
    (ruleSystem : QualifiedRuleSystem.{u, v} Judgment) :
    ProofCarryingAuthority (evidenceDiscipline ruleSystem) where
  Certificate := fun _kind => Derivation Judgment ruleSystem.witness.W
  checker := fun _kind => checker ruleSystem
  certificateBoundary := fun _kind => certificateEquivalence ruleSystem

/-- Acceptance projects through leastness to the independently supplied
meaning predicate. -/
theorem accepted_meaning [DecidableEq Judgment]
    (ruleSystem : QualifiedRuleSystem.{u, v} Judgment)
    (claim : Judgment)
    (certificate : Derivation Judgment ruleSystem.witness.W)
    (accepted :
      ((contract ruleSystem).checker ()).check claim certificate = true) :
    ruleSystem.Meaning claim :=
  ((contract ruleSystem).projection ()).sound claim certificate accepted

/-- Scope is exactly inhabitation of the structural derivation fibre, not an
existence claim manufactured from semantic meaning. -/
theorem scope_iff_structural_derivation
    (ruleSystem : QualifiedRuleSystem.{u, v} Judgment)
    (claim : Judgment) :
    (theory ruleSystem).Scope () claim <->
      ∃ derivation : Derivation Judgment ruleSystem.witness.W,
        derivation.valid ruleSystem.witness = true ∧
          derivation.concl = claim :=
  (evidenceDiscipline ruleSystem).scope_iff_proof () claim

/-- A claim outside least derivability scope is rejected by every certificate,
regardless of which semantic profile is attached to the same replay checker. -/
theorem outside_scope_has_no_certificate [DecidableEq Judgment]
    (ruleSystem : QualifiedRuleSystem.{u, v} Judgment)
    (claim : Judgment)
    (outsideScope : ¬ Derives ruleSystem.rules claim) :
    ¬ ∃ certificate : Derivation Judgment ruleSystem.witness.W,
      ((contract ruleSystem).checker ()).check claim certificate = true := by
  rintro ⟨certificate, accepted⟩
  exact outsideScope
    ((contract ruleSystem).scopeAuthority () |>.sound claim certificate accepted)

end QualifiedRuleSystem

/-! ## Schematic-substitution fragment -/

namespace SchematicFragment

open SchematicCanary

/-- Validity in every OSLF relational model.  This is independent of the
schematic replay checker. -/
def Meaning (formula : OSLFFormula) : Prop :=
  forall (reduction : Pattern -> Pattern -> Prop) (atoms : AtomSem) (state : Pattern),
    sem reduction atoms formula state

/-- Modus ponens and Hilbert K preserve validity under arbitrary atom
substitution in every relational model. -/
theorem rules_sound : forall premises conclusion,
    rules premises conclusion ->
      (forall premise, premise ∈ premises -> Meaning premise) ->
        Meaning conclusion := by
  rintro premises conclusion ⟨schema, member, substitution, rfl, rfl⟩
    premisesMeaning reduction atoms state
  simp only [axioms, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl
  · have antecedent := premisesMeaning
      (substAtoms substitution (.atom "A")) (by simp) reduction atoms state
    have implication := premisesMeaning
      (substAtoms substitution (.imp (.atom "A") (.atom "B")))
      (by simp) reduction atoms state
    simp only [substAtoms, sem] at antecedent implication ⊢
    exact implication antecedent
  · simp only [substAtoms, sem]
    intro antecedent _ignored
    exact antecedent

def ruleSystem : QualifiedRuleSystem OSLFFormula where
  rules := rules
  witness := witness
  Meaning := Meaning
  rules_sound := rules_sound

def theory := ruleSystem.theory

def contract := ruleSystem.contract

/-- Positive control: the existing schematic K certificate crosses the NIK
authority boundary unchanged. -/
theorem k_certificate_accepted :
    (contract.checker ()).check kInstance kCertificate = true :=
  kCertificate_accepted

theorem k_instance_meaning : Meaning kInstance :=
  ruleSystem.accepted_meaning kInstance kCertificate k_certificate_accepted

/-- Negative control: no certificate establishes bottom. -/
theorem no_certificate_accepts_bottom :
    ¬ ∃ certificate, (contract.checker ()).check OSLFFormula.bot certificate = true :=
  ruleSystem.outside_scope_has_no_certificate OSLFFormula.bot bot_not_derivable

end SchematicFragment

/-! ## Hypothetical-judgment fragment -/

namespace HypotheticalFragment

open HypotheticalCanary

def ruleSystem : QualifiedRuleSystem (Hyp String) where
  rules := rules
  witness := witness
  Meaning := Valid
  rules_sound := rules_valid

def theory := ruleSystem.theory

def contract := ruleSystem.contract

/-- Positive control: implication identity crosses the NIK authority boundary
as an ordinary witnessed hypothetical derivation. -/
theorem identity_accepted :
    (contract.checker ()).check ([], .imp a a) identityCertificate = true :=
  HypotheticalCanary.identity_accepted

theorem identity_meaning : Valid ([], .imp a a) :=
  ruleSystem.accepted_meaning ([], .imp a a) identityCertificate
    identity_accepted

/-- A bare atom is false in the all-false valuation, independently of replay. -/
theorem atom_not_meaning : ¬ Valid ([], a) := by
  intro meaningful
  exact meaningful (fun _atom => False) (by simp)

/-- Negative control: no certificate establishes the invalid bare atom. -/
theorem no_certificate_accepts_atom :
    ¬ ∃ certificate, (contract.checker ()).check ([], a) certificate = true :=
  ruleSystem.outside_scope_has_no_certificate ([], a) atom_not_derivable

end HypotheticalFragment

#print axioms QualifiedRuleSystem.accepted_meaning
#print axioms QualifiedRuleSystem.scope_iff_structural_derivation
#print axioms QualifiedRuleSystem.outside_scope_has_no_certificate
#print axioms QualifiedRuleSystem.certificateEquivalence
#print axioms QualifiedRuleSystem.proofCarryingAuthority
#print axioms SchematicFragment.k_instance_meaning
#print axioms SchematicFragment.no_certificate_accepts_bottom
#print axioms HypotheticalFragment.identity_meaning
#print axioms HypotheticalFragment.atom_not_meaning
#print axioms HypotheticalFragment.no_certificate_accepts_atom

end Mettapedia.GSLT.LanguageDef.NIKInitialRuleClosureAuthority
