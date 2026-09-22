import Mathlib.Computability.PartrecCode
import Mathlib.Computability.TuringMachine.Config

/-!
# A primitive-recursive encoding of `Turing.ToPartrec.Code`

Mathlib encodes `Nat.Partrec.Code` and proves its constructors and its recursor
primitive recursive, but gives no encoding of `Turing.ToPartrec.Code`.  The two
types have the same shape except that `Nat.Partrec.Code` has one more nullary
constructor, `right`.  This module transports Mathlib's encoding along that
shape:

* `toPartrecCode` sends `zero', succ, tail, cons, comp, case, fix` to
  `zero, succ, left, pair, comp, prec, rfind'` — a syntactic embedding that does
  not preserve evaluation and is not meant to;
* its image is exactly the codes that never use `right` (`WithoutRight`), a
  primitive-recursive predicate;
* `Turing.ToPartrec.Code` is equivalent to that subtype, and so inherits a
  `Primcodable` instance from Mathlib's.

Every constructor of `Turing.ToPartrec.Code`, and the constant-list code
`constCode`, is then primitive recursive for this encoding.  No second encoding of
codes is written: the numbers are Mathlib's.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.ToPartrecCodeEncoding

open Primrec

/-- The syntactic embedding into Mathlib's code type. -/
def toPartrecCode : Turing.ToPartrec.Code → Nat.Partrec.Code
  | .zero' => .zero
  | .succ => .succ
  | .tail => .left
  | .cons f fs => .pair (toPartrecCode f) (toPartrecCode fs)
  | .comp f g => .comp (toPartrecCode f) (toPartrecCode g)
  | .case f g => .prec (toPartrecCode f) (toPartrecCode g)
  | .fix f => .rfind' (toPartrecCode f)

/-- Its left inverse; `right`, outside the image, goes to `zero'`. -/
def ofPartrecCode : Nat.Partrec.Code → Turing.ToPartrec.Code
  | .zero => .zero'
  | .succ => .succ
  | .left => .tail
  | .right => .zero'
  | .pair f g => .cons (ofPartrecCode f) (ofPartrecCode g)
  | .comp f g => .comp (ofPartrecCode f) (ofPartrecCode g)
  | .prec f g => .case (ofPartrecCode f) (ofPartrecCode g)
  | .rfind' f => .fix (ofPartrecCode f)

/-- Whether a code never uses `right`. -/
def WithoutRight : Nat.Partrec.Code → Bool
  | .zero | .succ | .left => true
  | .right => false
  | .pair f g | .comp f g | .prec f g => WithoutRight f && WithoutRight g
  | .rfind' f => WithoutRight f

theorem ofPartrecCode_toPartrecCode (c : Turing.ToPartrec.Code) :
    ofPartrecCode (toPartrecCode c) = c := by
  induction c <;> simp [toPartrecCode, ofPartrecCode, *]

theorem withoutRight_toPartrecCode (c : Turing.ToPartrec.Code) :
    WithoutRight (toPartrecCode c) = true := by
  induction c <;> simp [toPartrecCode, WithoutRight, *]

theorem toPartrecCode_ofPartrecCode {d : Nat.Partrec.Code} (without : WithoutRight d = true) :
    toPartrecCode (ofPartrecCode d) = d := by
  induction d <;> simp_all [toPartrecCode, ofPartrecCode, WithoutRight]

/-- The image is exactly the codes without `right`: `right` itself is not hit. -/
theorem right_not_in_image (c : Turing.ToPartrec.Code) : toPartrecCode c ≠ .right := by
  cases c <;> simp [toPartrecCode]

theorem withoutRight_eq_recOn (d : Nat.Partrec.Code) :
    WithoutRight d =
      Nat.Partrec.Code.recOn d true true true false (fun _ _ left right => left && right)
        (fun _ _ left right => left && right) (fun _ _ left right => left && right)
        (fun _ inner => inner) := by
  induction d <;> simp [WithoutRight, *]

theorem withoutRight_primrec : Primrec WithoutRight := by
  have recursion := Nat.Partrec.Code.primrec_recOn (α := Nat.Partrec.Code) (σ := Bool)
    Primrec.id (Primrec.const true) (Primrec.const true) (Primrec.const true)
    (Primrec.const false)
    (pr := fun _ _ _ left right => left && right)
    (Primrec.and.comp (fst.comp (snd.comp (snd.comp snd))) (snd.comp (snd.comp (snd.comp snd))))
    (co := fun _ _ _ left right => left && right)
    (Primrec.and.comp (fst.comp (snd.comp (snd.comp snd))) (snd.comp (snd.comp (snd.comp snd))))
    (pc := fun _ _ _ left right => left && right)
    (Primrec.and.comp (fst.comp (snd.comp (snd.comp snd))) (snd.comp (snd.comp (snd.comp snd))))
    (rf := fun _ _ inner => inner) (snd.comp snd)
  exact recursion.of_eq fun d => (withoutRight_eq_recOn d).symm

theorem withoutRight_primrecPred : PrimrecPred fun d => WithoutRight d = true :=
  ⟨inferInstance, withoutRight_primrec.of_eq fun d => by simp⟩

instance primcodableWithoutRight :
    Primcodable {d : Nat.Partrec.Code // WithoutRight d = true} :=
  Primcodable.subtype withoutRight_primrecPred

/-- `Turing.ToPartrec.Code` is Mathlib's codes without `right`. -/
def equivWithoutRight : Turing.ToPartrec.Code ≃ {d : Nat.Partrec.Code // WithoutRight d = true} where
  toFun c := ⟨toPartrecCode c, withoutRight_toPartrecCode c⟩
  invFun d := ofPartrecCode d.1
  left_inv := ofPartrecCode_toPartrecCode
  right_inv d := Subtype.ext (toPartrecCode_ofPartrecCode d.2)

instance : Primcodable Turing.ToPartrec.Code :=
  Primcodable.ofEquiv _ equivWithoutRight

theorem toPartrecCode_primrec : Primrec toPartrecCode :=
  subtype_val.comp (of_equiv (e := equivWithoutRight))

theorem primrec_of_toPartrecCode {α : Type} [Primcodable α] {f : α → Turing.ToPartrec.Code}
    (hf : Primrec fun a => toPartrecCode (f a)) : Primrec f :=
  (of_equiv_iff equivWithoutRight).mp
    (subtype_val_iff.mp (show Primrec fun a => (equivWithoutRight (f a)).1 from hf))

theorem primrec₂_cons : Primrec₂ Turing.ToPartrec.Code.cons :=
  primrec_of_toPartrecCode <| Nat.Partrec.Code.primrec₂_pair.comp
    (toPartrecCode_primrec.comp fst) (toPartrecCode_primrec.comp snd)

theorem primrec₂_comp : Primrec₂ Turing.ToPartrec.Code.comp :=
  primrec_of_toPartrecCode <| Nat.Partrec.Code.primrec₂_comp.comp
    (toPartrecCode_primrec.comp fst) (toPartrecCode_primrec.comp snd)

theorem primrec₂_case : Primrec₂ Turing.ToPartrec.Code.case :=
  primrec_of_toPartrecCode <| Nat.Partrec.Code.primrec₂_prec.comp
    (toPartrecCode_primrec.comp fst) (toPartrecCode_primrec.comp snd)

theorem primrec_fix : Primrec Turing.ToPartrec.Code.fix :=
  primrec_of_toPartrecCode <| Nat.Partrec.Code.primrec_rfind'.comp toPartrecCode_primrec

/-- The code producing the one-element list `[n]` on every input. -/
def constCode (n : ℕ) : Turing.ToPartrec.Code :=
  (Turing.ToPartrec.Code.comp .succ)^[n] Turing.ToPartrec.Code.zero

@[simp] theorem constCode_eval (n : ℕ) (v : List ℕ) : (constCode n).eval v = pure [n] := by
  induction n with
  | zero => simp [constCode]
  | succ n ih =>
      have unfold : constCode (n + 1) = Turing.ToPartrec.Code.comp .succ (constCode n) :=
        Function.iterate_succ_apply' _ _ _
      rw [unfold]
      simp [ih]

theorem constCode_primrec : Primrec constCode :=
  Primrec.nat_iterate Primrec.id (Primrec.const _)
    (primrec₂_comp.comp (Primrec.const _) snd).to₂

/-! ## Controls -/

/-- The encoding separates codes that the embedding separates. -/
example : Encodable.encode (Turing.ToPartrec.Code.zero') ≠
    Encodable.encode (Turing.ToPartrec.Code.succ) := by
  intro same
  exact absurd (Encodable.encode_injective same) (by decide)

/-- And `right` is outside the image, so the subtype is proper. -/
example : WithoutRight .right = false := rfl

#print axioms withoutRight_primrec
#print axioms primrec₂_cons
#print axioms primrec₂_comp
#print axioms primrec_fix
#print axioms constCode_primrec

end Mettapedia.Computability.ToPartrecCodeEncoding
