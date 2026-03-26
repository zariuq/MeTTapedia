import Mettapedia.Languages.Metamath.MMLean4Bridge
import Mettapedia.Languages.Metamath.GroundedSemantics

/-!
# Metamath Acceptance Equivalence Scaffold

This module exposes local aliases for implementation acceptance and
spec provability, then reuses `mm-lean4`'s proved biconditional directly.
-/

namespace Mettapedia.Languages.Metamath.AcceptanceEquivalence

open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.GroundedSemantics

/-- Implementation acceptance predicate (parser/checker side). -/
def ImplAccepts (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula) : Prop :=
  ∃ (proof : Array String) (prFinal : Metamath.Verify.ProofState) (f' : Metamath.Verify.Formula),
    proof.foldlM (fun pr step => Metamath.Verify.DB.stepNormal (checkBytesDB bytes) pr step)
      ⟨⟨0, 0⟩, label, f, (checkBytesDB bytes).frame, #[], #[], Metamath.Verify.ProofTokenParser.normal⟩ =
        Except.ok prFinal ∧
      prFinal.stack.size = 1 ∧
      prFinal.stack[0]? = some f' ∧
      Metamath.Kernel.toExpr f' = Metamath.Kernel.toExpr f

/-- Spec acceptance predicate (declarative side). -/
def SpecAccepts (bytes : ByteArray) (f : Metamath.Verify.Formula) : Prop :=
  ∃ (Γ : Metamath.Spec.Database) (fr : Metamath.Spec.Frame),
    Metamath.Kernel.toDatabase (checkBytesDB bytes) = some Γ ∧
      Metamath.Kernel.toFrame (checkBytesDB bytes) (checkBytesDB bytes).frame = some fr ∧
      Metamath.Spec.Provable Γ fr (Metamath.Kernel.toExpr f)

theorem implAccepts_iff_specAccepts
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula)
    (hSuccess : (checkBytesDB bytes).error? = none) :
    ImplAccepts bytes label f ↔ SpecAccepts bytes f := by
  simpa [ImplAccepts, SpecAccepts, checkBytesDB] using
    parserAcceptance_iff_specProvable bytes label f hSuccess

end Mettapedia.Languages.Metamath.AcceptanceEquivalence
