import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.WrittenDomains

/-!
# Scope recovery for the native dependent term grammar

The native kernel receives indices as numbers. Its syntax prefilter traverses
both the written domain and body of an annotated lambda, while traversing the
body of a bare lambda under one binder. `Raw` exposes that constructor grammar
independently of scope. `decode` recovers the existing scoped `ATm` grammar.

The scope test accepts exactly the terms that decode, and successful decoding
has an exact inverse. Renaming and substitution below operate on raw indices;
their agreement with the independently defined scoped operations is proved.
These are symbolic syntax contracts. Allocation, integer bounds and the C
implementation are separate refinement obligations.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace NativeSyntax

inductive Raw (Head : Type) where
  | var (index : Nat)
  | const (name : DeclName)
  | head (value : Head)
  | pi (domain body : Raw Head)
  | sigma (domain body : Raw Head)
  | id (carrier left right : Raw Head)
  | lamBare (body : Raw Head)
  | lamTyped (domain body : Raw Head)
  | app (function argument : Raw Head)
  | pair (first second : Raw Head)
  | fst (pair : Raw Head)
  | snd (pair : Raw Head)
  | refl (subject : Raw Head)
  deriving DecidableEq, Repr

variable {Head : Type}

def encode : {n : Nat} → ATm Head n → Raw Head
  | _, .var index => .var index.val
  | _, .const name => .const name
  | _, .head value => .head value
  | _, .pi domain body => .pi (encode domain) (encode body)
  | _, .sigma domain body => .sigma (encode domain) (encode body)
  | _, .id carrier left right => .id (encode carrier) (encode left) (encode right)
  | _, .lamBare body => .lamBare (encode body)
  | _, .lamTyped domain body => .lamTyped (encode domain) (encode body)
  | _, .app function argument => .app (encode function) (encode argument)
  | _, .pair first second => .pair (encode first) (encode second)
  | _, .fst pair => .fst (encode pair)
  | _, .snd pair => .snd (encode pair)
  | _, .refl subject => .refl (encode subject)

def decode (n : Nat) : Raw Head → Option (ATm Head n)
  | .var index => if bound : index < n then some (.var ⟨index, bound⟩) else none
  | .const name => some (.const name)
  | .head value => some (.head value)
  | .pi domain body => do return .pi (← decode n domain) (← decode (n+1) body)
  | .sigma domain body => do return .sigma (← decode n domain) (← decode (n+1) body)
  | .id carrier left right => do return .id (← decode n carrier) (← decode n left) (← decode n right)
  | .lamBare body => ATm.lamBare <$> decode (n+1) body
  | .lamTyped domain body => do return .lamTyped (← decode n domain) (← decode (n+1) body)
  | .app function argument => do return .app (← decode n function) (← decode n argument)
  | .pair first second => do return .pair (← decode n first) (← decode n second)
  | .fst pair => ATm.fst <$> decode n pair
  | .snd pair => ATm.snd <$> decode n pair
  | .refl subject => ATm.refl <$> decode n subject

def checkScope (n : Nat) : Raw Head → Bool
  | .var index => decide (index < n)
  | .const _ | .head _ => true
  | .pi domain body | .sigma domain body | .lamTyped domain body =>
      checkScope n domain && checkScope (n+1) body
  | .id carrier left right => checkScope n carrier && checkScope n left && checkScope n right
  | .lamBare body => checkScope (n+1) body
  | .app first second | .pair first second => checkScope n first && checkScope n second
  | .fst pair | .snd pair | .refl pair => checkScope n pair

@[simp] theorem decode_encode {n : Nat} (term : ATm Head n) :
    decode n (encode term) = some term := by
  induction term <;> simp_all [encode, decode]

theorem encode_decode {n : Nat} {raw : Raw Head} {term : ATm Head n}
    (decoded : decode n raw = some term) : encode term = raw := by
  induction raw generalizing n with
  | var index =>
      simp only [decode] at decoded
      split at decoded
      · cases decoded; rfl
      · cases decoded
  | const name => cases decoded; rfl
  | head value => cases decoded; rfl
  | pi domain body ihDomain ihBody =>
      cases hA : decode (n) domain <;> cases hB : decode (n+1) body <;>
        simp [decode, hA, hB] at decoded
      subst term
      simp only [encode, ihDomain hA, ihBody hB]
  | sigma domain body ihDomain ihBody =>
      cases hA : decode (n) domain <;> cases hB : decode (n+1) body <;>
        simp [decode, hA, hB] at decoded
      subst term
      simp only [encode, ihDomain hA, ihBody hB]
  | id carrier left right ihCarrier ihLeft ihRight =>
      cases hA : decode (n) carrier <;> cases ha : decode (n) left <;> cases hb : decode (n) right <;>
        simp [decode, hA, ha, hb] at decoded
      subst term
      simp only [encode, ihCarrier hA, ihLeft ha, ihRight hb]
  | lamBare body ih =>
      cases hb : decode (n+1) body <;>
        simp [decode, hb] at decoded
      subst term
      simp only [encode, ih hb]
  | lamTyped domain body ihDomain ihBody =>
      cases hA : decode (n) domain <;> cases hB : decode (n+1) body <;>
        simp [decode, hA, hB] at decoded
      subst term
      simp only [encode, ihDomain hA, ihBody hB]
  | app function argument ihFunction ihArgument =>
      cases hf : decode (n) function <;> cases ha : decode (n) argument <;>
        simp [decode, hf, ha] at decoded
      subst term
      simp only [encode, ihFunction hf, ihArgument ha]
  | pair first second ihFirst ihSecond =>
      cases ha : decode (n) first <;> cases hb : decode (n) second <;>
        simp [decode, ha, hb] at decoded
      subst term
      simp only [encode, ihFirst ha, ihSecond hb]
  | fst pair ih =>
      cases hp : decode (n) pair <;>
        simp [decode, hp] at decoded
      subst term
      simp only [encode, ih hp]
  | snd pair ih =>
      cases hp : decode (n) pair <;>
        simp [decode, hp] at decoded
      subst term
      simp only [encode, ih hp]
  | refl subject ih =>
      cases ha : decode (n) subject <;>
        simp [decode, ha] at decoded
      subst term
      simp only [encode, ih ha]

theorem encode_injective {n : Nat} : Function.Injective (@encode Head n) := by
  intro first second same
  have decoded := congrArg (decode n) same
  simpa only [decode_encode, Option.some.injEq] using decoded

theorem decode_isSome {n : Nat} (raw : Raw Head) :
    (decode n raw).isSome = checkScope n raw := by
  induction raw generalizing n with
  | var index => simp only [decode, checkScope]; split <;> simp_all
  | const name => rfl
  | head value => rfl
  | pi domain body ihDomain ihBody =>
      simp only [decode, checkScope, ← ihDomain (n := n), ← ihBody (n := n+1)]
      cases decode (n) domain <;> cases decode (n+1) body <;> rfl
  | sigma domain body ihDomain ihBody =>
      simp only [decode, checkScope, ← ihDomain (n := n), ← ihBody (n := n+1)]
      cases decode (n) domain <;> cases decode (n+1) body <;> rfl
  | id carrier left right ihCarrier ihLeft ihRight =>
      simp only [decode, checkScope, ← ihCarrier (n := n), ← ihLeft (n := n), ← ihRight (n := n)]
      cases decode (n) carrier <;> cases decode (n) left <;> cases decode (n) right <;> rfl
  | lamBare body ih =>
      simp only [decode, checkScope, ← ih (n := n+1)]
      cases decode (n+1) body <;> rfl
  | lamTyped domain body ihDomain ihBody =>
      simp only [decode, checkScope, ← ihDomain (n := n), ← ihBody (n := n+1)]
      cases decode (n) domain <;> cases decode (n+1) body <;> rfl
  | app function argument ihFunction ihArgument =>
      simp only [decode, checkScope, ← ihFunction (n := n), ← ihArgument (n := n)]
      cases decode (n) function <;> cases decode (n) argument <;> rfl
  | pair first second ihFirst ihSecond =>
      simp only [decode, checkScope, ← ihFirst (n := n), ← ihSecond (n := n)]
      cases decode (n) first <;> cases decode (n) second <;> rfl
  | fst pair ih =>
      simp only [decode, checkScope, ← ih (n := n)]
      cases decode (n) pair <;> rfl
  | snd pair ih =>
      simp only [decode, checkScope, ← ih (n := n)]
      cases decode (n) pair <;> rfl
  | refl subject ih =>
      simp only [decode, checkScope, ← ih (n := n)]
      cases decode (n) subject <;> rfl

theorem scoped_iff_decoded {n : Nat} {raw : Raw Head} :
    checkScope n raw = true ↔ ∃ term : ATm Head n, decode n raw = some term := by
  rw [← decode_isSome]
  cases decode n raw <;> simp

theorem scoped_iff_encoded {n : Nat} {raw : Raw Head} :
    checkScope n raw = true ↔ ∃ term : ATm Head n, encode term = raw := by
  rw [scoped_iff_decoded]
  exact ⟨fun ⟨term, checked⟩ => ⟨term, encode_decode checked⟩,
    fun ⟨term, same⟩ => ⟨term, same ▸ decode_encode term⟩⟩

def liftRenRaw (ρ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | index+1 => ρ index + 1

def renameRaw (ρ : Nat → Nat) : Raw Head → Raw Head
  | .var index => .var (ρ index)
  | .const name => .const name
  | .head value => .head value
  | .pi domain body => .pi (renameRaw ρ domain) (renameRaw (liftRenRaw ρ) body)
  | .sigma domain body => .sigma (renameRaw ρ domain) (renameRaw (liftRenRaw ρ) body)
  | .id carrier left right => .id (renameRaw ρ carrier) (renameRaw ρ left) (renameRaw ρ right)
  | .lamBare body => .lamBare (renameRaw (liftRenRaw ρ) body)
  | .lamTyped domain body => .lamTyped (renameRaw ρ domain) (renameRaw (liftRenRaw ρ) body)
  | .app function argument => .app (renameRaw ρ function) (renameRaw ρ argument)
  | .pair first second => .pair (renameRaw ρ first) (renameRaw ρ second)
  | .fst pair => .fst (renameRaw ρ pair)
  | .snd pair => .snd (renameRaw ρ pair)
  | .refl subject => .refl (renameRaw ρ subject)

theorem liftRenRaw_agrees {n m : Nat} {ρ : Ren n m} {raw : Nat → Nat}
    (agree : ∀ index : Fin n, raw index.val = (ρ index).val) :
    ∀ index : Fin (n+1), liftRenRaw raw index.val = (liftRen ρ index).val := by
  intro index
  refine Fin.cases ?_ (fun outer => ?_) index
  · rfl
  · simpa only [liftRenRaw, liftRen, Fin.cases_succ, Fin.val_succ] using
      congrArg Nat.succ (agree outer)

theorem encode_rename {n m : Nat} (ρ : Ren n m) (raw : Nat → Nat)
    (agree : ∀ index : Fin n, raw index.val = (ρ index).val) (term : ATm Head n) :
    encode (term.rename ρ) = renameRaw raw (encode term) := by
  induction term generalizing m raw with
  | var index => simp [ATm.rename, encode, renameRaw, agree]
  | const name => rfl
  | head value => rfl
  | pi domain body ihDomain ihBody =>
      simp only [ATm.rename, encode, renameRaw, ihDomain ρ raw agree,
        ihBody (liftRen ρ) (liftRenRaw raw) (liftRenRaw_agrees agree)]
  | sigma domain body ihDomain ihBody =>
      simp only [ATm.rename, encode, renameRaw, ihDomain ρ raw agree,
        ihBody (liftRen ρ) (liftRenRaw raw) (liftRenRaw_agrees agree)]
  | id carrier left right ihCarrier ihLeft ihRight =>
      simp only [ATm.rename, encode, renameRaw, ihCarrier ρ raw agree,
        ihLeft ρ raw agree, ihRight ρ raw agree]
  | lamBare body ih =>
      simp only [ATm.rename, encode, renameRaw,
        ih (liftRen ρ) (liftRenRaw raw) (liftRenRaw_agrees agree)]
  | lamTyped domain body ihDomain ihBody =>
      simp only [ATm.rename, encode, renameRaw, ihDomain ρ raw agree,
        ihBody (liftRen ρ) (liftRenRaw raw) (liftRenRaw_agrees agree)]
  | app function argument ihFunction ihArgument =>
      simp only [ATm.rename, encode, renameRaw, ihFunction ρ raw agree, ihArgument ρ raw agree]
  | pair first second ihFirst ihSecond =>
      simp only [ATm.rename, encode, renameRaw, ihFirst ρ raw agree, ihSecond ρ raw agree]
  | fst pair ih => simp only [ATm.rename, encode, renameRaw, ih ρ raw agree]
  | snd pair ih => simp only [ATm.rename, encode, renameRaw, ih ρ raw agree]
  | refl subject ih => simp only [ATm.rename, encode, renameRaw, ih ρ raw agree]

end NativeSyntax
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
