import Mettapedia.Computability.KolmogorovComplexity.ConditionalProgramModel
import Mathlib.Computability.Primrec.List
import Mathlib.Data.Nat.Bits

/-!
# The exact dense natural-word codec on the shared foundations

The encoding and inverse follow IcTheory's `BitString.toNatExact` and
`BitString.ofNatExact`. Their mathematical reconstruction and computability
arguments are reused here; the independent-interpreter bridge proves the
explicit correspondence. Leading zero bits are retained, and every natural
has an exact word preimage. These laws do not assert a machine-time bound.
-/

set_option autoImplicit false

namespace KolmogorovComplexity.NaturalWordEncoding

def encode : List Bool → Nat
  | [] => 0
  | false :: word => 2 * encode word + 1
  | true :: word => 2 * encode word + 2

def decode : Nat → List Bool
  | 0 => []
  | n + 1 => n.bodd :: decode n.div2
termination_by n => n
decreasing_by
  simp_wf
  simpa [Nat.div2_val] using Nat.lt_succ_of_le (Nat.div_le_self n 2)

theorem encode_decode (n : Nat) : encode (decode n) = n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => simp [decode, encode]
      | succ n =>
          rw [decode]
          have smaller : n.div2 < n + 1 := by
            simpa [Nat.div2_val] using Nat.lt_succ_of_le (Nat.div_le_self n 2)
          have previous := ih n.div2 smaller
          cases parity : n.bodd
          · simp only [encode, previous]
            have value : n = 2 * n.div2 := by
              simpa [Nat.bit_val, parity] using (Nat.bit_bodd_div2 n).symm
            omega
          · simp only [encode, previous]
            have value : n = 2 * n.div2 + 1 := by
              simpa [Nat.bit_val, parity] using (Nat.bit_bodd_div2 n).symm
            omega

theorem decode_encode (word : List Bool) : decode (encode word) = word := by
  induction word with
  | nil => simp [decode, encode]
  | cons bit word ih =>
      cases bit with
      | false => rw [encode, decode]; simp [Nat.div2_bit0, ih]
      | true => rw [encode, decode]; simp [ih]

theorem encode_primrec : Primrec encode := by
  have step : Primrec₂ fun (_word : List Bool) (state : Bool × Nat) =>
      cond state.1 (2 * state.2 + 2) (2 * state.2 + 1) := by
    refine Primrec.cond (hc := ?_) (hf := ?_) (hg := ?_)
    · exact Primrec.fst.comp Primrec.snd
    · exact Primrec.nat_add.comp
        (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.snd.comp Primrec.snd)) (Primrec.const 2)
    · exact Primrec.nat_add.comp
        (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.snd.comp Primrec.snd)) (Primrec.const 1)
  refine (Primrec.list_foldr (hf := Primrec.id) (hg := Primrec.const 0) step).of_eq ?_
  intro word
  induction word with
  | nil => rfl
  | cons bit word ih => cases bit <;> simpa [encode] using ih

theorem decode_primrec : Primrec decode := by
  have casesRecursive : Primrec₂ fun (_unit : Unit) (previous : List (List Bool)) =>
      match previous with
      | [] => some []
      | _ :: tail => Option.map (List.cons (Nat.bodd tail.length)) (previous[tail.length.div2]?) := by
    have empty : Primrec (fun (_input : Unit × List (List Bool)) => some ([] : List Bool)) := Primrec.const _
    have step : Primrec₂ fun (input : Unit × List (List Bool)) (cell : List Bool × List (List Bool)) =>
        Option.map (List.cons (Nat.bodd cell.2.length)) (input.2[cell.2.length.div2]?) := by
      exact Primrec.option_map
        (hf := Primrec.list_getElem?.comp (Primrec.snd.comp Primrec.fst)
          (Primrec.nat_div2.comp (Primrec.list_length.comp (Primrec.snd.comp Primrec.snd))))
        (hg := (Primrec.list_cons.comp
          (Primrec.nat_bodd.comp
            (Primrec.list_length.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))) Primrec.snd).to₂)
    refine ((Primrec.list_casesOn
      (f := fun input : Unit × List (List Bool) => input.2) Primrec.snd empty step).to₂).of_eq ?_
    intro context previous
    cases previous <;> rfl
  have recurrence : Primrec₂ fun (_unit : Unit) (previous : List (List Bool)) =>
      match previous.length with
      | 0 => some []
      | n + 1 => Option.map (List.cons (Nat.bodd n)) (previous[n.div2]?) := by
    refine casesRecursive.of_eq ?_
    intro context previous
    cases previous <;> rfl
  have recursive : Primrec₂ (fun (_unit : Unit) n => decode n) := by
    refine Primrec.nat_strong_rec (f := fun (_unit : Unit) n => decode n) recurrence ?_
    intro context n
    cases n with
    | zero => simp [decode]
    | succ n =>
        have smaller : n.div2 < n + 1 := by
          simpa [Nat.div2_val] using Nat.lt_succ_of_le (Nat.div_le_self n 2)
        have lookup : ((List.range (n + 1)).map decode)[n.div2]? = some (decode n.div2) := by
          rw [List.getElem?_map, List.getElem?_range smaller]
          simp
        simpa [decode, List.length_range] using congrArg (Option.map (List.cons (Nat.bodd n))) lookup
  simpa using recursive.comp (Primrec.const Unit.unit) Primrec.id

def codec : NaturalWordCodec where
  encode := encode
  decode := decode
  decode_encode := decode_encode
  encode_decode := encode_decode
  encode_computable := encode_primrec.to_comp
  decode_computable := decode_primrec.to_comp

end KolmogorovComplexity.NaturalWordEncoding
