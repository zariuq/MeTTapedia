import Mettapedia.Languages.VibeITP.Spec.Kernel

/-!
# Vibe-ITP specification: derivability

The logic of the kernel as an inductive relation.  A theory records the
allocated symbols, the admitted axiom statements, and the admitted definitions.
Theorem statements are closed terms; free-variable symbols in a statement are
schematic and may be instantiated.

The execution primitive `THM_JIT` is deliberately absent.  It runs supplied
machine code and is outside this specification; a checker run that reaches it
is classified by the protocol, not by this relation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Spec

/-- An admitted definition: its fresh constant, parameters, and closed body. -/
structure Definition where
  symbol : SymId
  fvars : List SymId
  value : Term
deriving Repr

/-- A theory: allocated symbols with their data, axiom statements admitted
before proof processing, and definitions admitted at any time. -/
structure Theory where
  sig : Sig
  axioms : List Term
  definitions : List Definition

/-- Derivability in a theory.  Implications and equations use the kernel's
built-in `impl` and `eq` constants; modus ponens compares terms syntactically,
with symbols compared by allocation identity. -/
inductive Derives (T : Theory) : Term → Prop where
  | axiom {φ : Term} :
      φ ∈ T.axioms → Derives T φ
  | definition {d : Definition} :
      d ∈ T.definitions →
        Derives T (definitionStatement T.sig d.symbol d.fvars d.value)
  | modusPonens {a b : Term} :
      Derives T (.impl a b) → Derives T a → Derives T b
  | instantiate {φ ψ value : Term} {F : SymId} :
      Derives T φ → WellFormed T.sig value = true →
        instantiateStatement T.sig F value φ = some ψ → Derives T ψ
  | litIsNat {n : Nat} :
      n < wordBound → Derives T (litIsNatStatement n)
  | litLt {a b : Nat} :
      a < b → b < wordBound → Derives T (litLtStatement a b)
  | litAdd {a b : Nat} :
      a < wordBound → b < wordBound → Derives T (litAddStatement a b)
  | litMul {a b : Nat} :
      a < wordBound → b < wordBound → Derives T (litMulStatement a b)
  | litDiv {a b : Nat} :
      a < wordBound → b < wordBound → b ≠ 0 → Derives T (litDivStatement a b)
  | litLength {bytes : List UInt8} :
      WellFormed T.sig (.lit bytes) = true → Derives T (litLengthStatement bytes)
  | litGet {bytes : List UInt8} {index : Nat} :
      WellFormed T.sig (.lit bytes) = true → index < bytes.length →
        Derives T (litGetStatement bytes index)

end Mettapedia.Languages.VibeITP.Spec
