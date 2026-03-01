import Mettapedia.Logic.LP.FunctionFree
import Mettapedia.Logic.LP.FunctionFreeEvaluation
import Mathlib.Data.List.OfFn

/-!
# Bridge: LP Function-Free ↔ CertifyingDatalog-style Types

CertifyingDatalog (Tantow et al., ITP 2025) uses List-based ground atoms.
Our LP kernel uses Fin-indexed ground atoms. When `IsEmpty σ.functionSymbols`,
the two representations are isomorphic.

CertifyingDatalog is NOT a lake dependency (to avoid toolchain coupling).
We mirror their type structure and prove the bridge.

## LLM note: Use `List.ofFn` / `List.getElem_ofFn` for clean Fin↔List bridges.
Avoid `ext` on GroundAtom (HEq) and CDLGroundAtom (getElem?) — use structural proofs.

## References

- Tantow et al., *Certifying Datalog Reasoning in Lean 4*, ITP 2025
-/

namespace Mettapedia.Logic.LP

/-! ## Section 1: CDL-style Ground Atom (List-based) -/

/-- A CertifyingDatalog-style ground atom: relation symbol + list of constant args. -/
structure CDLGroundAtom (σ : LPSignature) where
  /-- The predicate symbol. -/
  symbol     : σ.relationSymbols
  /-- Constant arguments as a list. -/
  atom_terms : List σ.constants
  /-- The list length matches the relation's arity. -/
  term_length : atom_terms.length = σ.relationArity symbol

/-! ## Section 2: Conversions -/

variable {σ : LPSignature} [hFF : IsEmpty σ.functionSymbols]

/-- Convert an LP `GroundAtom` to CDL-style `CDLGroundAtom`.
    Uses `List.ofFn` for a clean Fin→List conversion. -/
def GroundAtom.toCDL (ga : GroundAtom σ) : CDLGroundAtom σ where
  symbol     := ga.symbol
  atom_terms := List.ofFn (fun i => (ga.args i).toConst)
  term_length := by simp [List.length_ofFn]

/-- Convert a CDL-style `CDLGroundAtom` to LP `GroundAtom`. -/
def CDLGroundAtom.toLP (cga : CDLGroundAtom σ) : GroundAtom σ where
  symbol := cga.symbol
  args   := fun i => .ofConst (cga.atom_terms[i.val]'(cga.term_length.symm ▸ i.isLt))

/-! ## Section 3: Round-trip properties -/

/-- CDL → LP → CDL round-trip: atom_terms are preserved. -/
theorem CDLGroundAtom.toLP_toCDL (cga : CDLGroundAtom σ) :
    cga.toLP.toCDL = cga := by
  cases cga with | mk sym terms hlen =>
  simp only [CDLGroundAtom.toLP, GroundAtom.toCDL, CDLGroundAtom.mk.injEq, true_and]
  apply List.ext_getElem
  · simp [List.length_ofFn, hlen]
  · intro i h1 h2
    simp [List.getElem_ofFn, GroundTerm.toConst_ofConst]

/-- LP → CDL → LP round-trip: args are preserved. -/
theorem GroundAtom.toCDL_toLP (ga : GroundAtom σ) :
    ga.toCDL.toLP = ga := by
  have h : ga.toCDL.toLP.args = ga.args := by
    funext i
    simp [GroundAtom.toCDL, CDLGroundAtom.toLP, List.getElem_ofFn,
          GroundTerm.ofConst_toConst]
  cases ga
  simp only [toCDL, CDLGroundAtom.toLP] at h ⊢
  congr

/-- The equivalence between LP `GroundAtom` and CDL-style `CDLGroundAtom`. -/
def GroundAtom.equivCDL : GroundAtom σ ≃ CDLGroundAtom σ where
  toFun    := GroundAtom.toCDL
  invFun   := CDLGroundAtom.toLP
  left_inv := GroundAtom.toCDL_toLP
  right_inv := CDLGroundAtom.toLP_toCDL

end Mettapedia.Logic.LP
