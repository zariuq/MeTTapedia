import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ArtifactComparison
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.IdentityEquality.Linking

/-!
# The identity profile in the kernel's spelling

The runtime stores rules and prints terms in the kernel's spelling.  This
module writes the identity profile's additions in that spelling, each checked
against its term in the calculus:

* the equation decoder at `num`, as a stored rule of the proof family;
* the realizations of the three assumptions of `zero-add`;
* linking: replacing the assumption constants of the runtime's own proof term
  of `zero-add`, as `set:native-proof` returned it, by the realizations gives
  the spelling of the linked proof;
* the same for the runtime's proof of symmetry at `num → num`, expanded by the
  proof library from `pf:sym`, and for its proof of congruence of the power
  set, expanded from `pf:cong`: each term is the compiler's output from the
  source proof, and linking it gives the linked proof.

Every spelled term reads back as its term, so a runtime that stores this rule
and links these realizations computes on the objects of the formal profile.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.IdentityEquality.KernelSpelling

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation
open CertifiedTransformProgram.ArtifactComparison (KTerm KRule capturedTerm)
open CertifiedTransformProgram.IdentityEquality.Realizations
open CertifiedTransformProgram.IdentityEquality.Translation

/-! ## Linking in the kernel's spelling -/

/-- Drop the domains of lambdas. -/
def erase : KTerm → KTerm
  | .app function argument => .app (erase function) (erase argument)
  | .lamTyped _ body => .lamBare (erase body)
  | .lamBare body => .lamBare (erase body)
  | .pi domain codomain => .pi (erase domain) (erase codomain)
  | .sigma domain codomain => .sigma (erase domain) (erase codomain)
  | .ident carrier left right => .ident (erase carrier) (erase left) (erase right)
  | .refl term => .refl (erase term)
  | .pair first second => .pair (erase first) (erase second)
  | .fst package => .fst (erase package)
  | .snd package => .snd (erase package)
  | term => term

/-- Replace declared constants by closed terms. -/
def expand (bodies : String → Option KTerm) : KTerm → KTerm
  | .declConst name => (bodies name).getD (.declConst name)
  | .app function argument => .app (expand bodies function) (expand bodies argument)
  | .lamTyped domain body => .lamTyped (expand bodies domain) (expand bodies body)
  | .lamBare body => .lamBare (expand bodies body)
  | .pi domain codomain => .pi (expand bodies domain) (expand bodies codomain)
  | .sigma domain codomain => .sigma (expand bodies domain) (expand bodies codomain)
  | .ident carrier left right =>
      .ident (expand bodies carrier) (expand bodies left) (expand bodies right)
  | .refl term => .refl (expand bodies term)
  | .pair first second => .pair (expand bodies first) (expand bodies second)
  | .fst package => .fst (expand bodies package)
  | .snd package => .snd (expand bodies package)
  | term => term

/-! ## The realizations -/

def reflText : String := "(Lam (Refl (idx 0)))"

def substText : String :=
  "(Lam (Lam (Lam (Lam (Lam (App (App (App (App (App (App (DeclConst id:eliminate) (DeclConst num)) (idx 3)) (Lam (Lam (App (DeclConst __cetta_holds_df87b3cd8ab4b6383b1d0591) (App (idx 6) (idx 1)))))) (idx 0)) (idx 2)) (idx 1)))))))"

def inductionText : String :=
  "(Lam (Lam (Lam (Lam (App (App (App (App (DeclConst num-rec) (Lam (App (DeclConst __cetta_holds_df87b3cd8ab4b6383b1d0591) (App (idx 4) (idx 0))))) (idx 2)) (idx 1)) (idx 0))))))"

theorem reflRealization_text :
    (KTerm.ofTm reflRealization).map KTerm.render = some reflText := by rfl

set_option maxRecDepth 100000 in
theorem substRealization_text :
    (KTerm.ofTm substRealization).map KTerm.render = some substText := by rfl

set_option maxRecDepth 100000 in
theorem inductionRealization_text :
    (KTerm.ofTm inductionRealization).map KTerm.render = some inductionText := by rfl

/-- The assumption constants of the runtime's proof term of `zero-add`, with
their realizations in the kernel's spelling. -/
def linkingTable : String → Option KTerm
  | "__cetta_proof_edb893c30879ea3547bf6b13" => KTerm.ofTm inductionRealization
  | "__cetta_proof_3e526d1816b34ee602df380a" => KTerm.ofTm reflRealization
  | "__cetta_proof_7b7ae677596090a0fb1c398d" => KTerm.ofTm substRealization
  | _ => none

/-- Linking the runtime's own proof term, with its lambda domains dropped, gives
the spelling of the linked proof. -/
theorem captured_links :
    KTerm.ofTm linkedZeroAdd = some (expand linkingTable (erase capturedTerm)) := by rfl

def linkedText : String :=
  "(App (App (App (Lam (Lam (Lam (Lam (App (App (App (App (DeclConst num-rec) (Lam (App (DeclConst __cetta_holds_df87b3cd8ab4b6383b1d0591) (App (idx 4) (idx 0))))) (idx 2)) (idx 1)) (idx 0)))))) (Lam (App (App (DeclConst eq@num) (App (App (DeclConst add) (DeclConst zero)) (idx 0))) (idx 0)))) (App (Lam (Refl (idx 0))) (DeclConst zero))) (Lam (Lam (App (App (App (App (App (Lam (Lam (Lam (Lam (Lam (App (App (App (App (App (App (DeclConst id:eliminate) (DeclConst num)) (idx 3)) (Lam (Lam (App (DeclConst __cetta_holds_df87b3cd8ab4b6383b1d0591) (App (idx 6) (idx 1)))))) (idx 0)) (idx 2)) (idx 1))))))) (Lam (App (App (DeclConst eq@num) (App (DeclConst suc) (App (App (DeclConst add) (DeclConst zero)) (idx 2)))) (App (DeclConst suc) (idx 0))))) (App (App (DeclConst add) (DeclConst zero)) (idx 1))) (idx 1)) (idx 0)) (App (Lam (Refl (idx 0))) (App (DeclConst suc) (App (App (DeclConst add) (DeclConst zero)) (idx 1))))))))"

set_option maxRecDepth 100000 in
theorem linkedZeroAdd_text : (KTerm.ofTm linkedZeroAdd).map KTerm.render = some linkedText := by
  rfl

/-- The spelled linked proof reads back as the linked proof. -/
theorem linkedZeroAdd_reads :
    (expand linkingTable (erase capturedTerm)).toTmAt 0 = some linkedZeroAdd :=
  KTerm.toTm_ofTm linkedZeroAdd captured_links

/-! ## The equation decoder -/

/-- `Holds (eq@num x y) = Id num x y`, as a stored rule of the proof family. -/
def equationRule : KRule where
  head := "__cetta_holds_df87b3cd8ab4b6383b1d0591"
  arity := 1
  patterns := [.app (.app (.declConst "eq@num") (.pvar 0)) (.pvar 1)]
  rhs := .ident (.declConst "num") (.pvar 0) (.pvar 1)

def equationRuleText : String :=
  "(PrimeRule __cetta_holds_df87b3cd8ab4b6383b1d0591 1 ((App (App (DeclConst eq@num) (PVar 0)) (PVar 1))) (Id (DeclConst num) (PVar 0) (PVar 1)))"

set_option maxRecDepth 100000 in
theorem equationRule_text : equationRule.render "PrimeRule" = equationRuleText := by rfl

/-- The stored rule is the profile's equation decoder at `num`. -/
theorem equationRule_toEquation :
    equationRule.toEquation =
      some ⟨2, (Metatheory.equationLeft SetProfile.numTy, Metatheory.equationRight SetProfile.numTy)⟩ := by
  rfl

/-! ## Symmetry at `num → num` -/

/-- `num → num` in the kernel's spelling. -/
def functionsSpelled : KTerm := .pi (.declConst "num") (.declConst "num")

/-- The term `set:native-proof fun-sym` returned. -/
def capturedSymmetry : KTerm :=
  .lamTyped functionsSpelled (.lamTyped functionsSpelled (.lamTyped
    (.app (.declConst "__cetta_holds_df87b3cd8ab4b6383b1d0591")
      (.app (.app (.declConst "eq@(Pi num num)") (.idx 1)) (.idx 0)))
    (.app
      (.app (.app (.app (.app (.declConst "__cetta_proof_39b13fb31936e8bfd301615d")
        (.lamTyped functionsSpelled (.app (.app (.declConst "eq@(Pi num num)") (.idx 0)) (.idx 3))))
        (.idx 2)) (.idx 1)) (.idx 0))
      (.app (.declConst "__cetta_proof_9176030980c5f7f182d46601") (.idx 2)))))

def capturedSymmetryText : String :=
  "(Lam (Pi (DeclConst num) (DeclConst num)) (Lam (Pi (DeclConst num) (DeclConst num)) (Lam (App (DeclConst __cetta_holds_df87b3cd8ab4b6383b1d0591) (App (App (DeclConst eq@(Pi num num)) (idx 1)) (idx 0))) (App (App (App (App (App (DeclConst __cetta_proof_39b13fb31936e8bfd301615d) (Lam (Pi (DeclConst num) (DeclConst num)) (App (App (DeclConst eq@(Pi num num)) (idx 0)) (idx 3)))) (idx 2)) (idx 1)) (idx 0)) (App (DeclConst __cetta_proof_9176030980c5f7f182d46601) (idx 2))))))"

set_option maxRecDepth 100000 in
theorem capturedSymmetry_text : capturedSymmetry.render = capturedSymmetryText := by rfl

/-- The runtime's constants for `refl@fun` and `subst@fun`, in the order of the
source proof's assumptions. -/
def symmetryConstants : Fin 2 → Tower.Tm 0 :=
  ![.const (.mkSimple "__cetta_proof_9176030980c5f7f182d46601"),
    .const (.mkSimple "__cetta_proof_39b13fb31936e8bfd301615d")]

/-- With lambda domains dropped, the runtime's term is the compiler's output from
the source proof of symmetry, with the runtime's constants as hypotheses. -/
theorem capturedSymmetry_erases :
    capturedSymmetry.toTmAt 0 =
      HOLNativeGenericProofCompiler.Modulo.compileModulo SetProfile.signature
        (Linking.symmetryProof Linking.functions) Fin.elim0 symmetryConstants := by
  rfl

/-- The runtime's constants with their realizations in the kernel's spelling. -/
def symmetryTable : String → Option KTerm
  | "__cetta_proof_9176030980c5f7f182d46601" => KTerm.ofTm reflRealization
  | "__cetta_proof_39b13fb31936e8bfd301615d" =>
      KTerm.ofTm (Carriers.substRealizationAt Linking.functions)
  | _ => none

/-- Substitution at `num → num`: identity elimination at the function carrier. -/
def substFunctionsText : String :=
  "(Lam (Lam (Lam (Lam (Lam (App (App (App (App (App (App (DeclConst id:eliminate) (Pi (DeclConst num) (DeclConst num))) (idx 3)) (Lam (Lam (App (DeclConst __cetta_holds_df87b3cd8ab4b6383b1d0591) (App (idx 6) (idx 1)))))) (idx 0)) (idx 2)) (idx 1)))))))"

set_option maxRecDepth 100000 in
theorem substFunctions_text :
    (KTerm.ofTm (Carriers.substRealizationAt Linking.functions)).map KTerm.render =
      some substFunctionsText := by
  rfl

/-- Linking the runtime's term gives the linked symmetry proof. -/
theorem capturedSymmetry_links :
    KTerm.ofTm Linking.linkedSymmetry = some (expand symmetryTable (erase capturedSymmetry)) := by
  rfl

theorem linkedSymmetry_reads :
    (expand symmetryTable (erase capturedSymmetry)).toTmAt 0 = some Linking.linkedSymmetry :=
  KTerm.toTm_ofTm Linking.linkedSymmetry capturedSymmetry_links

/-! ## Congruence of the power set -/

/-- The term `set:native-proof power-cong` returned. -/
def capturedCongruence : KTerm :=
  .lamTyped (.declConst "set") (.lamTyped (.declConst "set") (.lamTyped
    (.app (.declConst "__cetta_holds_df87b3cd8ab4b6383b1d0591")
      (.app (.app (.declConst "eq@set") (.idx 1)) (.idx 0)))
    (.app
      (.app (.app (.app (.app (.declConst "__cetta_proof_355c44f012c7df9e6abfaf30")
        (.lamTyped (.declConst "set") (.app (.app (.declConst "eq@set")
          (.app (.declConst "Power") (.idx 3))) (.app (.declConst "Power") (.idx 0)))))
        (.idx 2)) (.idx 1)) (.idx 0))
      (.app (.declConst "__cetta_proof_1f581f338b62ac4adc3b0911")
        (.app (.declConst "Power") (.idx 2))))))

def capturedCongruenceText : String :=
  "(Lam (DeclConst set) (Lam (DeclConst set) (Lam (App (DeclConst __cetta_holds_df87b3cd8ab4b6383b1d0591) (App (App (DeclConst eq@set) (idx 1)) (idx 0))) (App (App (App (App (App (DeclConst __cetta_proof_355c44f012c7df9e6abfaf30) (Lam (DeclConst set) (App (App (DeclConst eq@set) (App (DeclConst Power) (idx 3))) (App (DeclConst Power) (idx 0))))) (idx 2)) (idx 1)) (idx 0)) (App (DeclConst __cetta_proof_1f581f338b62ac4adc3b0911) (App (DeclConst Power) (idx 2)))))))"

set_option maxRecDepth 100000 in
theorem capturedCongruence_text : capturedCongruence.render = capturedCongruenceText := by rfl

/-- The runtime's constants for `refl@set` and `subst@set`. -/
def congruenceConstants : Fin 2 → Tower.Tm 0 :=
  ![.const (.mkSimple "__cetta_proof_1f581f338b62ac4adc3b0911"),
    .const (.mkSimple "__cetta_proof_355c44f012c7df9e6abfaf30")]

theorem capturedCongruence_erases :
    capturedCongruence.toTmAt 0 =
      HOLNativeGenericProofCompiler.Modulo.compileModulo SetProfile.signature
        Linking.congruenceProof Fin.elim0 congruenceConstants := by
  rfl

def congruenceTable : String → Option KTerm
  | "__cetta_proof_1f581f338b62ac4adc3b0911" => KTerm.ofTm reflRealization
  | "__cetta_proof_355c44f012c7df9e6abfaf30" =>
      KTerm.ofTm (Carriers.substRealizationAt Linking.sets)
  | _ => none

theorem capturedCongruence_links :
    KTerm.ofTm Linking.linkedCongruence =
      some (expand congruenceTable (erase capturedCongruence)) := by
  rfl

#print axioms captured_links
#print axioms capturedCongruence_erases
#print axioms capturedCongruence_links
#print axioms capturedSymmetry_erases
#print axioms capturedSymmetry_links
#print axioms linkedZeroAdd_text
#print axioms linkedZeroAdd_reads
#print axioms equationRule_toEquation

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.IdentityEquality.KernelSpelling
