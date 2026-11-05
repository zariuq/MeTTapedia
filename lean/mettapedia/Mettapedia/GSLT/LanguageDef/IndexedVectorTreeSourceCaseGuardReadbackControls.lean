import Mettapedia.GSLT.LanguageDef.IndexedVectorTreeSourceCaseGuardReadback

/-!
# Source case-guard readback at a permuted symbolic environment

Answer and family predicates remain independent variables. The target orders
all seven parameters differently from the original source and supplies beta-
wrapped case functions. The exact source guards still read back to the
declared products. Requests dropping the method's All argument or changing
the result-evidence carrier are refused by the actual complete-context reader.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.IndexedVectorTreeSourceCaseGuardReadbackControls
open Mettapedia.Logic Mettapedia.Logic.HOL
open IndexedVectorTreeSourceCaseGuardReadback
open Native

abbrev context : Ctx Base :=
  [E ⇒ .prop,E ⇒ .prop,Source.motiveCarrier,E ⇒ E,N ⇒ V ⇒ E,Source.solvedCaseCarrier,Source.branchCaseCarrier]

private def variableAt (type : Ty Base) (position : Fin context.length)
    (same : context.get position = type) : Var context type := same ▸ Var.ofFin context position

def answer : Term Const context (E ⇒ .prop) := .var (variableAt _ ⟨0,by decide +kernel⟩ (by decide +kernel))
def family : Term Const context (E ⇒ .prop) := .var (variableAt _ ⟨1,by decide +kernel⟩ (by decide +kernel))
def motive : Term Const context Source.motiveCarrier := .var (variableAt _ ⟨2,by decide +kernel⟩ (by decide +kernel))
def solved : Term Const context (E ⇒ E) := .var (variableAt _ ⟨3,by decide +kernel⟩ (by decide +kernel))
def branch : Term Const context (N ⇒ V ⇒ E) := .var (variableAt _ ⟨4,by decide +kernel⟩ (by decide +kernel))
def solvedCase : Term Const context Source.solvedCaseCarrier :=
  .app (.lam (.var .vz)) (.var (variableAt _ ⟨5,by decide +kernel⟩ (by decide +kernel)))
def branchCase : Term Const context Source.branchCaseCarrier :=
  .app (.lam (.var .vz)) (.var (variableAt _ ⟨6,by decide +kernel⟩ (by decide +kernel)))

theorem distinct_predicate_variables : answer ≠ family := by intro same; cases same

theorem permuted_solved_guard :
    HOL.subst (Install.rawImages answer family motive solved branch solvedCase branchCase)
      (Source.ambientContext.telescope.guard solvedCaseVariable) =
      .app (solvedCaseGuardFor answer motive solved) solvedCase :=
  rawSolvedCaseGuard answer family motive solved branch solvedCase branchCase

theorem permuted_branch_guard :
    HOL.subst (Install.rawImages answer family motive solved branch solvedCase branchCase)
      (Source.ambientContext.telescope.guard branchCaseVariable) =
      .app (branchCaseGuardFor family motive branch) branchCase :=
  rawBranchCaseGuard answer family motive solved branch solvedCase branchCase

theorem raised_branch_guard :
    HOL.subst (Subst.ofRename (Rename.weaken (σ := N))) (branchCaseGuardFor family motive branch) =
      branchCaseGuardFor (weaken family) (weaken motive) (weaken branch) := by
  simpa only [subst_ofRename,weaken] using
    branchCaseGuardFor_subst (Subst.ofRename (Rename.weaken (σ := N))) family motive branch

def droppedAllMethodTarget : Ctx Base :=
  [W,V,N,N ⇒ V ⇒ W,Source.solvedCaseCarrier,N ⇒ V ⇒ E,E ⇒ E,Source.motiveCarrier,E ⇒ .prop,E ⇒ .prop]

theorem missing_original_all_method_argument_refused :
    (IndexedVectorTreeNativeSourceReading.readComplete? 1 droppedAllMethodTarget).isSome = false := by
  decide +kernel

def changedEvidenceTarget : Ctx Base :=
  [W,V,N,Source.branchCaseCarrier,Source.solvedCaseCarrier,N ⇒ V ⇒ E,E ⇒ E,E ⇒ E ⇒ .prop,E ⇒ .prop,E ⇒ .prop]

theorem changed_motive_evidence_carrier_refused :
    (IndexedVectorTreeNativeSourceReading.readComplete? 1 changedEvidenceTarget).isSome = false := by
  decide +kernel

#print axioms permuted_solved_guard
#print axioms permuted_branch_guard
#print axioms raised_branch_guard
#print axioms missing_original_all_method_argument_refused
#print axioms changed_motive_evidence_carrier_refused

end Mettapedia.GSLT.LanguageDef.IndexedVectorTreeSourceCaseGuardReadbackControls
