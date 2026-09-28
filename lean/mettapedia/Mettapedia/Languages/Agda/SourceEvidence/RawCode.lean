import Mettapedia.Languages.Agda.StaticSpecification.Judgments
import Mathlib.Logic.Encodable.Basic

/-!
Finite, unindexed codes for the frozen finite-Set/relevant-Pi source syntax.
The decoder checks every de Bruijn bound and distinguishes binding from
non-binding abstractions. This is serialization of syntax, not evaluation.
Natural-number serialization is provided separately by NumeralCode.
No presentation-generated rule is imported.
-/

namespace Mettapedia.Languages.Agda.SourceEvidence.Codec
open Mettapedia.Languages.Agda.StaticSpecification

inductive Code where
  | atom : Nat → Code
  | pair : Code → Code → Code
  deriving DecidableEq, Repr

namespace Code

@[simp, match_pattern] def list : List Code → Code
  | [] => .atom 0
  | x :: xs => .pair x (list xs)

/-- Parameters and ordered premises are separate finite code lists. -/
@[simp, match_pattern] def node (tag : Nat) (parameters premises : List Code) : Code :=
  .pair (.atom tag) (.pair (list parameters) (list premises))

end Code

mutual
  def encodeTerm : Term n → Code
    | .var i => .pair (.atom 0) (.atom i.val)
    | .lam b => .pair (.atom 1) (encodeAbs b)
    | .pi a b => .pair (.atom 2) (.pair (encodeTy a) (encodeTyAbs b))
    | .sort k => .pair (.atom 3) (.atom k)
    | .elim f e => .pair (.atom 4) (.pair (encodeTerm f) (encodeElim e))
  def encodeAbs : Abs n → Code
    | .bind b => .pair (.atom 0) (encodeTerm b)
    | .noBind b => .pair (.atom 1) (encodeTerm b)
  def encodeTy : Ty n → Code
    | .el k a => .pair (.atom k) (encodeTerm a)
  def encodeTyAbs : TyAbs n → Code
    | .bind b => .pair (.atom 0) (encodeTy b)
    | .noBind b => .pair (.atom 1) (encodeTy b)
  def encodeElim : Elim n → Code
    | .apply a => .pair (.atom 0) (encodeTerm a)
end

mutual
  def decodeTerm (n : Nat) : Code → Option (Term n)
    | .pair (.atom 0) (.atom i) => if h : i < n then some (.var ⟨i, h⟩) else none
    | .pair (.atom 1) b => .lam <$> decodeAbs n b
    | .pair (.atom 2) (.pair a b) => do return .pi (← decodeTy n a) (← decodeTyAbs n b)
    | .pair (.atom 3) (.atom k) => some (.sort k)
    | .pair (.atom 4) (.pair f e) => do return .elim (← decodeTerm n f) (← decodeElim n e)
    | _ => none
  def decodeAbs (n : Nat) : Code → Option (Abs n)
    | .pair (.atom 0) b => .bind <$> decodeTerm (n + 1) b
    | .pair (.atom 1) b => .noBind <$> decodeTerm n b
    | _ => none
  def decodeTy (n : Nat) : Code → Option (Ty n)
    | .pair (.atom k) a => .el k <$> decodeTerm n a
    | _ => none
  def decodeTyAbs (n : Nat) : Code → Option (TyAbs n)
    | .pair (.atom 0) b => .bind <$> decodeTy (n + 1) b
    | .pair (.atom 1) b => .noBind <$> decodeTy n b
    | _ => none
  def decodeElim (n : Nat) : Code → Option (Elim n)
    | .pair (.atom 0) a => .apply <$> decodeTerm n a
    | _ => none
end

mutual
  @[simp] theorem decode_encodeTerm (t : Term n) : decodeTerm n (encodeTerm t) = some t := by
    match t with
    | .var i => simp [encodeTerm, decodeTerm]
    | .lam b => simp [encodeTerm, decodeTerm, decode_encodeAbs b]
    | .pi a b => simp [encodeTerm, decodeTerm, decode_encodeTy a,
        decode_encodeTyAbs b]
    | .sort k => rfl
    | .elim f e => simp [encodeTerm, decodeTerm, decode_encodeTerm f,
        decode_encodeElim e]
  @[simp] theorem decode_encodeAbs (b : Abs n) : decodeAbs n (encodeAbs b) = some b := by
    match b with
    | .bind t => simp [encodeAbs, decodeAbs, decode_encodeTerm t]
    | .noBind t => simp [encodeAbs, decodeAbs, decode_encodeTerm t]
  @[simp] theorem decode_encodeTy (a : Ty n) : decodeTy n (encodeTy a) = some a := by
    match a with
    | .el k t => simp [encodeTy, decodeTy, decode_encodeTerm t]
  @[simp] theorem decode_encodeTyAbs (b : TyAbs n) : decodeTyAbs n (encodeTyAbs b) = some b := by
    match b with
    | .bind a => simp [encodeTyAbs, decodeTyAbs, decode_encodeTy a]
    | .noBind a => simp [encodeTyAbs, decodeTyAbs, decode_encodeTy a]
  @[simp] theorem decode_encodeElim (e : Elim n) : decodeElim n (encodeElim e) = some e := by
    match e with
    | .apply t => simp [encodeElim, decodeElim, decode_encodeTerm t]
end

def encodeContext : RawContext n → Code
  | .nil => .atom 0
  | .snoc Γ a => .pair (encodeContext Γ) (encodeTy a)

def decodeContext : (n : Nat) → Code → Option (RawContext n)
  | 0, .atom 0 => some .nil
  | n + 1, .pair Γ a => do return .snoc (← decodeContext n Γ) (← decodeTy n a)
  | _, _ => none

@[simp] theorem decode_encodeContext (Γ : RawContext n) :
    decodeContext n (encodeContext Γ) = some Γ := by
  induction Γ with
  | nil => rfl
  | snoc Γ a ih => simp [encodeContext, decodeContext, ih]

end Mettapedia.Languages.Agda.SourceEvidence.Codec
