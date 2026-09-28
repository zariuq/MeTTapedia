import Mettapedia.OSLF.Syntax.BindingWireCodec
import Mettapedia.OSLF.Syntax.BindingTelescopeSubstitution

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.OSLF.Binding Mettapedia.OSLF.Binding.Telescope

variable {S : Signature} [DecidableEq S.Srt]
variable (operator : Codec (Σ s : S.Srt, S.Op s)) (b k : S.Srt)

def putContext : {n : Nat} → RawContext S b k n → Data
  | _, .nil => .atom 0
  | _, .snoc prior code => .pair (putContext prior) (putTerm operator code)

def getContext : Data → Option (Sigma (RawContext S b k))
  | .atom 0 => some ⟨0, .nil⟩
  | .pair prior code => do
      let ⟨n, context⟩ ← getContext prior
      let A ← getTerm operator (scope b n) k code
      return ⟨n + 1, .snoc context A⟩
  | _ => none

theorem get_putContext {n : Nat} (context : RawContext S b k n) :
    getContext operator b k (putContext operator b k context) = some ⟨n, context⟩ := by
  induction context with
  | nil => rfl
  | snoc prior code ih =>
      simp only [putContext, getContext, ih, Bind.bind, Option.bind, get_putTerm]
      rfl

def context : Codec (Sigma (RawContext S b k)) where
  put value := putContext operator b k value.2
  get := getContext operator b k
  get_put value := get_putContext operator b k value.2

def contextAt (n : Nat) : Codec (RawContext S b k n) :=
  (context operator b k).mapped (fun Γ => ⟨n, Γ⟩)
    (fun ⟨m, Γ⟩ => if h : m = n then some (h ▸ Γ) else none)
    (fun _ => by simp only [dite_true])

def putSub (m : Nat) : (n : Nat) → RawSub S b n m → Data
  | 0, _ => .atom 0
  | n + 1, σ => .pair (putSub m n (split σ).1) (putTerm operator (split σ).2)

def getSub (m : Nat) : (n : Nat) → Data → Option (RawSub S b n m)
  | 0, .atom 0 => some (emptySub b m)
  | n + 1, .pair prior newest => do
      return pair (← getSub m n prior) (← getTerm operator (scope b m) b newest)
  | _, _ => none

theorem get_putSub (m n : Nat) (σ : RawSub S b n m) :
    getSub operator b m n (putSub operator b m n σ) = some σ := by
  induction n with
  | zero => exact congrArg some (emptySub_unique σ).symm
  | succ n ih =>
      simp only [putSub, getSub, ih, Bind.bind, Option.bind, get_putTerm, pair_split]
      rfl

def substitution (n m : Nat) : Codec (RawSub S b n m) :=
  ⟨putSub operator b m n, getSub operator b m n, get_putSub operator b m n⟩

end Mettapedia.OSLF.Binding.WireCodec
