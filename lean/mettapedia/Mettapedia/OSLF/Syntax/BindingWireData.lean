import Mathlib.Logic.Equiv.Defs

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.WireCodec

inductive Data where
  | atom (value : Nat)
  | pair (first second : Data)
  deriving DecidableEq, Repr

structure Codec (α : Type) where
  put : α → Data
  get : Data → Option α
  get_put : ∀ value, get (put value) = some value

namespace Codec

variable {α β : Type}

theorem put_injective (codec : Codec α) : Function.Injective codec.put := by
  intro a b same
  have decoded := congrArg codec.get same
  rw [codec.get_put, codec.get_put] at decoded
  exact Option.some.inj decoded

def decEq (codec : Codec α) : DecidableEq α :=
  fun a b => decidable_of_iff (codec.put a = codec.put b) codec.put_injective.eq_iff

def nat : Codec Nat where
  put := .atom
  get | .atom n => some n | _ => none
  get_put _ := rfl

def prod (first : Codec α) (second : Codec β) : Codec (α × β) where
  put value := .pair (first.put value.1) (second.put value.2)
  get | .pair a b => do return (← first.get a, ← second.get b) | _ => none
  get_put value := by simp only [first.get_put, second.get_put]; rfl

def mapped (base : Codec α) (put : β → α) (get : α → Option β)
    (roundtrip : ∀ value, get (put value) = some value) : Codec β where
  put value := base.put (put value)
  get wire := (base.get wire).bind get
  get_put value := by rw [base.get_put]; exact roundtrip value

def ofEquiv (base : Codec α) (equiv : β ≃ α) : Codec β :=
  base.mapped equiv (some ∘ equiv.symm) (fun value => congrArg some (equiv.left_inv value))

def sigma {β : α → Type} (index : Codec α) (fiber : ∀ a, Codec (β a)) : Codec (Sigma β) where
  put value := .pair (index.put value.1) ((fiber value.1).put value.2)
  get
    | .pair first second => do
        let a ← index.get first
        return ⟨a, ← (fiber a).get second⟩
    | _ => none
  get_put value := by
    simp only [index.get_put, Bind.bind, Option.bind, (fiber value.1).get_put]
    rfl

def fin (n : Nat) : Codec (Fin n) :=
  nat.mapped Fin.val (fun i => if h : i < n then some ⟨i, h⟩ else none)
    (fun i => by simp only [i.isLt, dite_true])

/-- Accept only the representation emitted by this encoder. The initial
decoder must already reconstruct the represented value. -/
def canonicalGet (codec : Codec α) (wire : Data) : Option α := do
  let value ← codec.get wire
  if codec.put value = wire then some value else none

theorem canonicalGet_put (codec : Codec α) (value : α) :
    codec.canonicalGet (codec.put value) = some value := by
  simp only [canonicalGet, codec.get_put, Bind.bind, Option.bind, ite_true]

theorem put_of_canonicalGet (codec : Codec α) (wire : Data) (value : α)
    (accepted : codec.canonicalGet wire = some value) : codec.put value = wire := by
  cases decoded : codec.get wire with
  | none => simp only [canonicalGet, decoded, Bind.bind, Option.bind] at accepted; cases accepted
  | some result =>
      by_cases same : codec.put result = wire
      · simp only [canonicalGet, decoded, Bind.bind, Option.bind, if_pos same, Option.some.injEq] at accepted
        cases accepted
        exact same
      · simp only [canonicalGet, decoded, Bind.bind, Option.bind, if_neg same] at accepted
        cases accepted

def putList (element : Codec α) : List α → Data
  | [] => .atom 0
  | head :: tail => .pair (element.put head) (putList element tail)

def getList (element : Codec α) : Data → Option (List α)
  | .atom 0 => some []
  | .pair head tail => do return (← element.get head) :: (← getList element tail)
  | _ => none

theorem get_putList (element : Codec α) : ∀ values, getList element (putList element values) = some values
  | [] => rfl
  | head :: tail => by simp only [putList, getList, element.get_put, get_putList element tail]; rfl

def list (element : Codec α) : Codec (List α) := ⟨putList element, getList element, get_putList element⟩

def char : Codec Char :=
  nat.mapped Char.toNat
    (fun n => if (Char.ofNat n).toNat = n then some (Char.ofNat n) else none)
    (fun c => by simp only [Char.ofNat_toNat, ite_true])

end Codec
end Mettapedia.OSLF.Binding.WireCodec
