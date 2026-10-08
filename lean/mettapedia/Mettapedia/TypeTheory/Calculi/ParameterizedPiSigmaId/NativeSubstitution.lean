import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.NativeSyntax

/-!
# Raw native shifting and binder substitution

`shift` and `substituteZero` follow the native index algorithms: shifting skips
indices below the cutoff; substitution preserves the inner binders, shifts an
inserted argument past them, and decrements the remaining outer indices.
Their definitions traverse the raw constructor tree, independently of the
scoped operations. The comparison theorems apply to every scoped term and to
arbitrary substitutions, including dependent types and written lambda domains.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace NativeSyntax

variable {Head : Type}

theorem liftRenRaw_id : liftRenRaw id = id := by
  funext index
  cases index <;> rfl

theorem renameRaw_id (term : Raw Head) : renameRaw id term = term := by
  induction term <;> simp_all only [renameRaw, liftRenRaw_id, id_eq]

theorem liftRenRaw_comp (first second : Nat → Nat) :
    (fun index => liftRenRaw second (liftRenRaw first index)) =
      liftRenRaw (fun index => second (first index)) := by
  funext index
  cases index <;> rfl

theorem renameRaw_comp (first second : Nat → Nat) (term : Raw Head) :
    renameRaw second (renameRaw first term) =
      renameRaw (fun index => second (first index)) term := by
  induction term generalizing first second <;>
    simp_all only [renameRaw, ← liftRenRaw_comp]

def shiftIndex (amount cutoff index : Nat) : Nat :=
  if index < cutoff then index else index + amount

def shift (amount cutoff : Nat) : Raw Head → Raw Head
  | .var index => .var (shiftIndex amount cutoff index)
  | .const name => .const name
  | .head value => .head value
  | .pi domain body => .pi (shift amount cutoff domain) (shift amount (cutoff+1) body)
  | .sigma domain body => .sigma (shift amount cutoff domain) (shift amount (cutoff+1) body)
  | .id carrier left right =>
      .id (shift amount cutoff carrier) (shift amount cutoff left) (shift amount cutoff right)
  | .lamBare body => .lamBare (shift amount (cutoff+1) body)
  | .lamTyped domain body =>
      .lamTyped (shift amount cutoff domain) (shift amount (cutoff+1) body)
  | .app function argument => .app (shift amount cutoff function) (shift amount cutoff argument)
  | .pair first second => .pair (shift amount cutoff first) (shift amount cutoff second)
  | .fst pair => .fst (shift amount cutoff pair)
  | .snd pair => .snd (shift amount cutoff pair)
  | .refl subject => .refl (shift amount cutoff subject)

theorem liftRenRaw_shiftIndex (amount cutoff : Nat) :
    liftRenRaw (shiftIndex amount cutoff) = shiftIndex amount (cutoff+1) := by
  funext index
  cases index with
  | zero => simp [liftRenRaw, shiftIndex]
  | succ index =>
      simp only [liftRenRaw, shiftIndex]
      split <;> split <;> omega

theorem shift_eq_renameRaw (amount cutoff : Nat) (term : Raw Head) :
    shift amount cutoff term = renameRaw (shiftIndex amount cutoff) term := by
  induction term generalizing cutoff <;>
    simp_all only [shift, renameRaw, liftRenRaw_shiftIndex]

theorem shift_zero_comp (first second : Nat) (term : Raw Head) :
    shift second 0 (shift first 0 term) = shift (first+second) 0 term := by
  simp only [shift_eq_renameRaw, renameRaw_comp]
  congr 1
  funext index
  simp only [shiftIndex, Nat.not_lt_zero, ↓reduceIte]
  omega

def weakenRen {n : Nat} (amount : Nat) : Ren n (n+amount) :=
  fun index => ⟨index.val + amount, by omega⟩

theorem shift_encode {n : Nat} (amount : Nat) (term : ATm Head n) :
    shift amount 0 (encode term) = encode (term.rename (weakenRen amount)) := by
  rw [shift_eq_renameRaw]
  symm
  apply encode_rename
  intro index
  simp [shiftIndex, weakenRen]

theorem shift_decodes {n : Nat} (amount : Nat) (term : ATm Head n) :
    decode (n+amount) (shift amount 0 (encode term)) =
      some (term.rename (weakenRen amount)) := by
  rw [shift_encode, decode_encode]

def liftSubRaw (substitution : Nat → Raw Head) : Nat → Raw Head
  | 0 => .var 0
  | index+1 => renameRaw Nat.succ (substitution index)

def substRaw (substitution : Nat → Raw Head) : Raw Head → Raw Head
  | .var index => substitution index
  | .const name => .const name
  | .head value => .head value
  | .pi domain body => .pi (substRaw substitution domain) (substRaw (liftSubRaw substitution) body)
  | .sigma domain body =>
      .sigma (substRaw substitution domain) (substRaw (liftSubRaw substitution) body)
  | .id carrier left right =>
      .id (substRaw substitution carrier) (substRaw substitution left) (substRaw substitution right)
  | .lamBare body => .lamBare (substRaw (liftSubRaw substitution) body)
  | .lamTyped domain body =>
      .lamTyped (substRaw substitution domain) (substRaw (liftSubRaw substitution) body)
  | .app function argument => .app (substRaw substitution function) (substRaw substitution argument)
  | .pair first second => .pair (substRaw substitution first) (substRaw substitution second)
  | .fst pair => .fst (substRaw substitution pair)
  | .snd pair => .snd (substRaw substitution pair)
  | .refl subject => .refl (substRaw substitution subject)

theorem liftSubRaw_agrees {n m : Nat} {σ : ATm.ASub Head n m}
    {raw : Nat → Raw Head} (agree : ∀ index : Fin n, raw index.val = encode (σ index)) :
    ∀ index : Fin (n+1), liftSubRaw raw index.val = encode (ATm.liftSub σ index) := by
  intro index
  refine Fin.cases ?_ (fun outer => ?_) index
  · rfl
  · simp only [liftSubRaw, ATm.liftSub, Fin.cases_succ, Fin.val_succ, agree outer]
    symm
    exact encode_rename wk Nat.succ (fun _ => rfl) (σ outer)

theorem encode_subst {n m : Nat} (σ : ATm.ASub Head n m) (raw : Nat → Raw Head)
    (agree : ∀ index : Fin n, raw index.val = encode (σ index)) (term : ATm Head n) :
    encode (term.subst σ) = substRaw raw (encode term) := by
  induction term generalizing m raw with
  | var index => simp [ATm.subst, encode, substRaw, agree]
  | const name => rfl
  | head value => rfl
  | pi domain body ihDomain ihBody =>
      simp only [ATm.subst, encode, substRaw, ihDomain σ raw agree,
        ihBody (ATm.liftSub σ) (liftSubRaw raw) (liftSubRaw_agrees agree)]
  | sigma domain body ihDomain ihBody =>
      simp only [ATm.subst, encode, substRaw, ihDomain σ raw agree,
        ihBody (ATm.liftSub σ) (liftSubRaw raw) (liftSubRaw_agrees agree)]
  | id carrier left right ihCarrier ihLeft ihRight =>
      simp only [ATm.subst, encode, substRaw, ihCarrier σ raw agree,
        ihLeft σ raw agree, ihRight σ raw agree]
  | lamBare body ih =>
      simp only [ATm.subst, encode, substRaw,
        ih (ATm.liftSub σ) (liftSubRaw raw) (liftSubRaw_agrees agree)]
  | lamTyped domain body ihDomain ihBody =>
      simp only [ATm.subst, encode, substRaw, ihDomain σ raw agree,
        ihBody (ATm.liftSub σ) (liftSubRaw raw) (liftSubRaw_agrees agree)]
  | app function argument ihFunction ihArgument =>
      simp only [ATm.subst, encode, substRaw, ihFunction σ raw agree, ihArgument σ raw agree]
  | pair first second ihFirst ihSecond =>
      simp only [ATm.subst, encode, substRaw, ihFirst σ raw agree, ihSecond σ raw agree]
  | fst pair ih => simp only [ATm.subst, encode, substRaw, ih σ raw agree]
  | snd pair ih => simp only [ATm.subst, encode, substRaw, ih σ raw agree]
  | refl subject ih => simp only [ATm.subst, encode, substRaw, ih σ raw agree]

def substituteZero (argument : Raw Head) (depth : Nat) : Raw Head → Raw Head
  | .var index =>
      if index < depth then .var index
      else if index = depth then shift depth 0 argument else .var (index-1)
  | .const name => .const name
  | .head value => .head value
  | .pi domain body =>
      .pi (substituteZero argument depth domain) (substituteZero argument (depth+1) body)
  | .sigma domain body =>
      .sigma (substituteZero argument depth domain) (substituteZero argument (depth+1) body)
  | .id carrier left right => .id (substituteZero argument depth carrier)
      (substituteZero argument depth left) (substituteZero argument depth right)
  | .lamBare body => .lamBare (substituteZero argument (depth+1) body)
  | .lamTyped domain body =>
      .lamTyped (substituteZero argument depth domain) (substituteZero argument (depth+1) body)
  | .app function value =>
      .app (substituteZero argument depth function) (substituteZero argument depth value)
  | .pair first second =>
      .pair (substituteZero argument depth first) (substituteZero argument depth second)
  | .fst pair => .fst (substituteZero argument depth pair)
  | .snd pair => .snd (substituteZero argument depth pair)
  | .refl subject => .refl (substituteZero argument depth subject)

def zeroSub (argument : Raw Head) (depth index : Nat) : Raw Head :=
  if index < depth then .var index
  else if index = depth then shift depth 0 argument else .var (index-1)

theorem renameRaw_succ (term : Raw Head) :
    renameRaw Nat.succ term = shift 1 0 term := by
  rw [shift_eq_renameRaw]
  congr 1

theorem liftSubRaw_zeroSub (argument : Raw Head) (depth : Nat) :
    liftSubRaw (zeroSub argument depth) = zeroSub argument (depth+1) := by
  funext index
  cases index with
  | zero => simp [liftSubRaw, zeroSub]
  | succ index =>
      by_cases inner : index < depth
      · simp [liftSubRaw, zeroSub, inner, show index+1 < depth+1 by omega, renameRaw]
      · by_cases same : index = depth
        · subst index
          simp [liftSubRaw, zeroSub, renameRaw_succ, shift_zero_comp]
        · have outer : depth < index := by omega
          simp [liftSubRaw, zeroSub, inner, same, show ¬ index+1 < depth+1 by omega,
            renameRaw]
          omega

theorem substituteZero_eq_substRaw (argument term : Raw Head) (depth : Nat) :
    substituteZero argument depth term = substRaw (zeroSub argument depth) term := by
  induction term generalizing depth <;>
    simp_all only [substituteZero, substRaw, zeroSub, liftSubRaw_zeroSub]

theorem substituteZero_encode {n : Nat} (argument : ATm Head n) (body : ATm Head (n+1)) :
    substituteZero (encode argument) 0 (encode body) = encode (ATm.inst0 argument body) := by
  rw [substituteZero_eq_substRaw]
  symm
  apply encode_subst
  intro index
  refine Fin.cases ?_ (fun outer => ?_) index
  · simp only [zeroSub, Nat.not_lt_zero, ↓reduceIte, shift_eq_renameRaw]
    have identity : shiftIndex 0 0 = id := by funext i; simp [shiftIndex]
    rw [identity]
    exact renameRaw_id (encode argument)
  · simp [zeroSub, ATm.subst0, encode]

theorem substituteZero_decodes {n : Nat} (argument : ATm Head n) (body : ATm Head (n+1)) :
    decode n (substituteZero (encode argument) 0 (encode body)) =
      some (ATm.inst0 argument body) := by
  rw [substituteZero_encode, decode_encode]

end NativeSyntax
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
