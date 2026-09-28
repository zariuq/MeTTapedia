import Mettapedia.Languages.Agda.SourceEvidence.RawCode

/-! Scope-checked endpoints for the five frozen source judgment families. -/

namespace Mettapedia.Languages.Agda.SourceEvidence.Codec
open Mettapedia.Languages.Agda.StaticSpecification

inductive Judgment where
  | context {n : Nat} : RawContext n → Judgment
  | formation {n : Nat} : RawContext n → Ty n → Judgment
  | typing {n : Nat} : RawContext n → Term n → Ty n → Judgment
  | typeEquality {n : Nat} : RawContext n → Ty n → Ty n → Judgment
  | termEquality {n : Nat} : RawContext n → Term n → Term n → Ty n → Judgment

def Evidence : Judgment → Type
  | .context Γ => FormCtx Γ
  | .formation Γ a => FormTy Γ a
  | .typing Γ t a => Typing Γ t a
  | .typeEquality Γ a b => TypeEq Γ a b
  | .termEquality Γ t u a => TermEq Γ t u a

def encodeJudgment : Judgment → Code
  | @Judgment.context n Γ => .node 0 [.atom n, encodeContext Γ] []
  | @Judgment.formation n Γ a => .node 1 [.atom n, encodeContext Γ, encodeTy a] []
  | @Judgment.typing n Γ t a => .node 2 [.atom n, encodeContext Γ, encodeTerm t, encodeTy a] []
  | @Judgment.typeEquality n Γ a b => .node 3 [.atom n, encodeContext Γ, encodeTy a, encodeTy b] []
  | @Judgment.termEquality n Γ t u a =>
      .node 4 [.atom n, encodeContext Γ, encodeTerm t, encodeTerm u, encodeTy a] []

def decodeJudgment : Code → Option Judgment
  | .node 0 [.atom n, Γ] [] => do return .context (← decodeContext n Γ)
  | .node 1 [.atom n, Γ, a] [] => do return .formation (← decodeContext n Γ) (← decodeTy n a)
  | .node 2 [.atom n, Γ, t, a] [] => do
      return .typing (← decodeContext n Γ) (← decodeTerm n t) (← decodeTy n a)
  | .node 3 [.atom n, Γ, a, b] [] => do
      return .typeEquality (← decodeContext n Γ) (← decodeTy n a) (← decodeTy n b)
  | .node 4 [.atom n, Γ, t, u, a] [] => do
      return .termEquality (← decodeContext n Γ) (← decodeTerm n t)
        (← decodeTerm n u) (← decodeTy n a)
  | _ => none

@[simp] theorem decode_encodeJudgment (j : Judgment) :
    decodeJudgment (encodeJudgment j) = some j := by
  cases j <;> simp [encodeJudgment, decodeJudgment]

theorem encodeJudgment_injective : Function.Injective encodeJudgment := by
  intro a b h
  have := congrArg decodeJudgment h
  simpa using this

instance : DecidableEq Judgment := encodeJudgment_injective.decidableEq

/-- The dependent package retains the actual Type-valued source proof. -/
abbrev Packed := (j : Judgment) × Evidence j

/-- Only a checked equality of complete indices permits evidence transport. -/
def fit (expected : Judgment) (packet : Packed) : Option (Evidence expected) :=
  if h : packet.1 = expected then some (h ▸ packet.2) else none

@[simp] theorem fit_same (j : Judgment) (d : Evidence j) : fit j ⟨j, d⟩ = some d := by
  simp [fit]

theorem fit_wrong {expected : Judgment} {packet : Packed} (h : packet.1 ≠ expected) :
    fit expected packet = none := by simp [fit, h]

end Mettapedia.Languages.Agda.SourceEvidence.Codec
