import Mettapedia.Logic.LP.FunctionFree
import Mettapedia.Logic.LP.FunctionFreeEvaluation
import CertifyingDatalog.Datalog.Grounding
import CertifyingDatalog.Datalog.Basic
import Mathlib.Data.List.OfFn

/-!
# Bridge: LP Function-Free ↔ CertifyingDatalog (Real Import)

CertifyingDatalog (Tantow et al., ITP 2025) is now a lake dependency.
We prove a direct equivalence between our LP `GroundAtom` (Fin-indexed)
and CDL's `GroundAtom` (List-based) via the signature projection
`LPSignature → Signature`.

## Structure

1. `LPSignature.toCDLSig`: project our signature to CDL's (drop `functionSymbols`).
2. `LP.GroundAtom.toCDL` / `CDL.GroundAtom.toLP`: conversions.
3. `LP.GroundAtom.equivCDL`: the `≃` equivalence with kernel-checked round-trips.

## LLM note
Use `List.ofFn` / `List.getElem_ofFn` for Fin↔List bridges.

## References

- Tantow et al., *Certifying Datalog Reasoning in Lean 4*, ITP 2025
  Source: `Mettapedia/external/CertifyingDatalog/`
-/

namespace Mettapedia.Logic.LP

/-! ## Section 1: Signature projection -/

/-- Project an `LPSignature` to CertifyingDatalog's `Signature`
    by dropping the `functionSymbols` field. -/
@[reducible] def LPSignature.toCDLSig (σ : LPSignature) : Signature where
  constants       := σ.constants
  vars            := σ.vars
  relationSymbols := σ.relationSymbols
  relationArity   := σ.relationArity

/-! ## Section 2: Conversions (requires function-free signature) -/

variable {σ : LPSignature} [hFF : IsEmpty σ.functionSymbols]

/-- Convert an LP `GroundAtom` to CertifyingDatalog's `GroundAtom`.
    Uses `List.ofFn` for a clean Fin→List conversion. -/
def GroundAtom.toCDL (ga : GroundAtom σ) : _root_.GroundAtom (LPSignature.toCDLSig σ) where
  symbol     := ga.symbol
  atom_terms := List.ofFn (fun i => (ga.args i).toConst)
  term_length := by simp [List.length_ofFn, LPSignature.toCDLSig]

/-- Convert CertifyingDatalog's `GroundAtom` to an LP `GroundAtom`. -/
def GroundAtom.ofCDL (cga : _root_.GroundAtom (LPSignature.toCDLSig σ)) : GroundAtom σ where
  symbol := cga.symbol
  args   := fun i => .ofConst (cga.atom_terms[i.val]'(cga.term_length ▸ i.isLt))

/-! ## Section 3: Round-trip properties -/

/-- CDL → LP → CDL round-trip: atom_terms are preserved. -/
theorem GroundAtom.ofCDL_toCDL (cga : _root_.GroundAtom (LPSignature.toCDLSig σ)) :
    (GroundAtom.ofCDL cga).toCDL = cga := by
  cases cga with | mk sym terms hlen =>
  simp only [GroundAtom.ofCDL, GroundAtom.toCDL, _root_.GroundAtom.mk.injEq, true_and]
  apply List.ext_getElem
  · simp [List.length_ofFn, hlen]
  · intro i h1 h2
    simp [List.getElem_ofFn, GroundTerm.toConst_ofConst]

/-- LP → CDL → LP round-trip: args are preserved. -/
theorem GroundAtom.toCDL_ofCDL (ga : GroundAtom σ) :
    GroundAtom.ofCDL ga.toCDL = ga := by
  have h : (GroundAtom.ofCDL ga.toCDL).args = ga.args := by
    funext i
    simp [GroundAtom.toCDL, GroundAtom.ofCDL, List.getElem_ofFn,
          GroundTerm.ofConst_toConst]
  cases ga
  simp only [toCDL, ofCDL] at h ⊢
  congr

/-- The equivalence between LP `GroundAtom` and CertifyingDatalog's `GroundAtom`.
    This is a real cross-library bridge — both sides are the actual types from
    their respective libraries. -/
def GroundAtom.equivCDL : GroundAtom σ ≃ _root_.GroundAtom (LPSignature.toCDLSig σ) where
  toFun    := GroundAtom.toCDL
  invFun   := GroundAtom.ofCDL
  left_inv := GroundAtom.toCDL_ofCDL
  right_inv := GroundAtom.ofCDL_toCDL

end Mettapedia.Logic.LP
