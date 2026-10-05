import Mettapedia.Languages.VibeITP.Presentation.LiteralProgram
import Mettapedia.Languages.VibeITP.Presentation.SoundTheorems

/-!
# Authored literal encoding and ordered byte lookup

Number construction executes one-byte selection or the full eight-byte
little-endian recursion. Byte lookup traverses the submitted byte list in
order. These helpers compute data; the literal inference guards authorize
the corresponding statements separately.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation.ComputationalLiterals

open ComputationalData ComputationalShift ComputationalInference
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => literalProgram
local notation "A" => literalEquations
local notation "H" => productDivisionHost

theorem literal_add (left right : Nat) :
    Applies P H "nik:nat-add" [natural left, natural right] (natural (left + right)) :=
  .primitive (by decide +kernel) (naturalArithmeticHost_add left right)

theorem literal_lt (left right : Nat) :
    Applies P H "nik:nat-lt" [natural left, natural right] (boolean (decide (left < right))) :=
  .primitive (by decide +kernel) (naturalArithmeticHost_lt left right)

theorem literal_zero (value : Nat) :
    Applies P H "nik:nat-zero" [natural value] (boolean (decide (value = 0))) := by
  apply Applies.primitive (by decide +kernel)
  rw [productDivisionHost_prior _ _ (by rfl)]
  by_cases zero : value = 0 <;> simpa [zero, boolean] using computationalHost_zero value

theorem literal_pred (value : Nat) :
    Applies P H "nik:nat-pred" [natural value] (natural value.pred) :=
  .primitive (by decide +kernel) (computationalHost_pred value)

theorem literal_mul (left right : Nat) :
    Applies P H "nik:nat-mul" [natural left, natural right] (natural (left * right)) :=
  .primitive (by decide +kernel) (productDivisionHost_mul left right)

theorem literal_div (left right : Nat) (nonzero : right ≠ 0) :
    Applies P H "nik:nat-div" [natural left, natural right] (natural (left / right)) :=
  .primitive (by decide +kernel) (productDivisionHost_div left right nonzero)

theorem literal_mod (left right : Nat) (nonzero : right ≠ 0) :
    Applies P H "nik:nat-mod" [natural left, natural right] (natural (left % right)) :=
  .primitive (by decide +kernel) (productDivisionHost_mod left right nonzero)

theorem literal_view (items : List Term) :
    Applies P H "nik:list-view" [.list items] (listView items) :=
  .primitive (by decide +kernel) (computationalHost_list_view items)

theorem literal_cons (first : Term) (rest : List Term) :
    Applies P H "nik:list-cons" [first, .list rest] (.list (first :: rest)) :=
  .primitive (by decide +kernel) (computationalHost_list_cons first rest)

theorem literal_some (value : Term) :
    Applies P H "Some" [value] (.expr [.sym "Some", value]) :=
  .constructor (by decide +kernel) (by rfl)

theorem literal_lit (bytes : List UInt8) :
    Applies P H "Vibe:Lit" [.list (bytes.map encodeByte)] (encode (.lit bytes)) :=
  .constructor (by decide +kernel) (by rfl)

theorem literal_app (symbol : Spec.SymId) (arguments : List Spec.Term) :
    Applies P H "Vibe:App" [encodeSymbol symbol, .list (encodeTerms arguments)]
      (encode (.app symbol arguments)) :=
  .constructor (by decide +kernel) (by rfl)

theorem literal_natural_evaluates (environment : Env) (value : Nat) :
    Evaluates P H environment (natural value) (natural value) :=
  (natural_passive P H value).evaluates environment

theorem literal_symbol_evaluates (environment : Env) (symbol : Spec.SymId) :
    Evaluates P H environment (encodeSymbol symbol) (encodeSymbol symbol) :=
  (encodedSymbol_passive P H symbol).evaluates environment

theorem literal_encoded_evaluates (environment : Env) (value : Spec.Term) :
    Evaluates P H environment (encode value) (encode value) :=
  (encoded_passive literalProgram_dataSeparated value).evaluates environment

theorem littleEndian_computes (width value : Nat) :
    Applies P H "vibe:little-endian" [natural width, natural value]
      (.list ((Spec.leBytes width value).map encodeByte)) := by
  induction width generalizing value with
  | zero =>
      refine literal_equation (equation := A[3])
        (environment := [("width", natural 0), ("n", natural value)])
        (by decide +kernel) (by rfl) (by rfl) ?_
      refine Evaluates.call (values := [.sym "True", natural 0, natural value]) (by simp [Special])
        (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))) ?_
      · exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (literal_zero 0)
      · exact ⟨1, by rw [literal_apply _ (by decide +kernel)]; rfl⟩
  | succ width ih =>
      refine literal_equation (equation := A[3])
        (environment := [("width", natural (width + 1)), ("n", natural value)])
        (by decide +kernel) (by rfl) (by rfl) ?_
      refine Evaluates.call (values := [.sym "False", natural (width + 1), natural value]) (by simp [Special])
        (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))) ?_
      · exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (literal_zero (width + 1))
      · refine literal_equation (equation := A[5])
          (environment := [("width", natural (width + 1)), ("n", natural value)])
          (by decide +kernel) (by rfl) (by rfl) ?_
        have firstByte : encodeByte (UInt8.ofNat (value % 256)) = natural (value % 256) := by
          rw [encodeByte, uint8_toNat_ofNat_mod]
        simp only [Spec.leBytes, List.map_cons, firstByte]
        refine Evaluates.call (values := [natural (value % 256),
            .list ((Spec.leBytes width (value / 256)).map encodeByte)]) (by simp [Special])
          (.cons ?_ (.cons ?_ .nil)) (literal_cons _ _)
        · exact Evaluates.call (by simp [Special])
            (.cons (.variable (by rfl)) (.cons (literal_natural_evaluates _ _) .nil))
            (literal_mod value 256 (by decide))
        · refine Evaluates.call (values := [natural width, natural (value / 256)]) (by simp [Special])
            (.cons ?_ (.cons ?_ .nil)) (ih (value / 256))
          · exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (literal_pred (width + 1))
          · exact Evaluates.call (by simp [Special])
              (.cons (.variable (by rfl)) (.cons (literal_natural_evaluates _ _) .nil))
              (literal_div value 256 (by decide))

theorem numberBytes_computes (value : Nat) :
    Applies P H "vibe:number-bytes" [natural value] (.list ((Spec.natLiteral value).map encodeByte)) := by
  refine literal_equation (equation := A[0]) (environment := [("n", natural value)])
    (by decide +kernel) (by rfl) (by rfl) ?_
  refine Evaluates.call (values := [boolean (decide (value < 256)), natural value]) (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) .nil)) ?_
  · exact Evaluates.call (by simp [Special])
      (.cons (.variable (by rfl)) (.cons (literal_natural_evaluates _ _) .nil)) (literal_lt value 256)
  · by_cases small : value < 256
    · have byte : (UInt8.ofNat value).toNat = value := by
        simp only [UInt8.toNat_ofNat', Nat.reducePow]
        exact Nat.mod_eq_of_lt small
      simp only [small, decide_true, boolean, Spec.natLiteral, if_true, List.map_cons, List.map_nil,
        encodeByte, byte]
      refine literal_equation (equation := A[1]) (environment := [("n", natural value)])
        (by decide +kernel) (by rfl) (by rfl) ?_
      exact ⟨2, by rfl⟩
    · simp only [small, decide_false, boolean, Spec.natLiteral, if_false]
      refine literal_equation (equation := A[2]) (environment := [("n", natural value)])
        (by decide +kernel) (by rfl) (by rfl) ?_
      exact Evaluates.call (by simp [Special])
        (.cons (literal_natural_evaluates _ _) (.cons (.variable (by rfl)) .nil))
        (littleEndian_computes 8 value)

theorem numberLiteral_computes (value : Nat) :
    Applies P H "vibe:number-literal" [natural value] (encode (Spec.Term.natLit value)) := by
  refine literal_equation (equation := A[6]) (environment := [("n", natural value)])
    (by decide +kernel) (by rfl) (by rfl) ?_
  exact Evaluates.call (by simp [Special])
    (.cons (Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil)
      (numberBytes_computes value)) .nil) (literal_lit _)

def encodeByteResult : Option UInt8 → Term
  | none => .sym "None"
  | some byte => .expr [.sym "Some", encodeByte byte]

private theorem byte_start (bytes : List UInt8) (index : Nat) (result : Term)
    (next : Applies P H "vibe:byte-view" [listView (bytes.map encodeByte), natural index] result) :
    Applies P H "vibe:byte-at" [.list (bytes.map encodeByte), natural index] result := by
  refine literal_equation (equation := A[7])
    (environment := [("bytes", .list (bytes.map encodeByte)), ("index", natural index)])
    (by decide +kernel) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) .nil)) next
  exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (literal_view _)

theorem byteAt_computes (bytes : List UInt8) (index : Nat) :
    Applies P H "vibe:byte-at" [.list (bytes.map encodeByte), natural index]
      (encodeByteResult bytes[index]?) := by
  induction bytes generalizing index with
  | nil =>
      apply byte_start
      exact ⟨1, by rw [literal_apply _ (by decide +kernel)]; rfl⟩
  | cons first rest ih =>
      apply byte_start
      refine literal_equation (equation := A[9])
        (environment := [("first", encodeByte first), ("rest", .list (rest.map encodeByte)),
          ("index", natural index)]) (by decide +kernel) (by rfl) (by rfl) ?_
      refine Evaluates.call (values := [boolean (decide (index = 0)), encodeByte first,
          .list (rest.map encodeByte), natural index]) (by simp [Special])
        (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
          (.cons (.variable (by rfl)) .nil)))) ?_
      · exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (literal_zero index)
      · cases index with
        | zero =>
            refine literal_equation (equation := A[10])
              (environment := [("first", encodeByte first), ("rest", .list (rest.map encodeByte)),
                ("index", natural 0)]) (by decide +kernel) (by rfl) (by rfl) ?_
            exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (literal_some _)
        | succ index =>
            refine literal_equation (equation := A[11])
              (environment := [("first", encodeByte first), ("rest", .list (rest.map encodeByte)),
                ("index", natural (index + 1))]) (by decide +kernel) (by rfl) (by rfl) ?_
            refine Evaluates.call (values := [.list (rest.map encodeByte), natural index]) (by simp [Special])
              (.cons (.variable (by rfl)) (.cons ?_ .nil)) (ih index)
            exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (literal_pred (index + 1))

theorem byteAt_in_range (bytes : List UInt8) (index : Nat) (bound : index < bytes.length) :
    Applies P H "vibe:byte-at" [.list (bytes.map encodeByte), natural index]
      (.expr [.sym "Some", encodeByte (bytes.getD index 0)]) := by
  have same : bytes[index]? = some (bytes.getD index 0) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem bound, Option.getD_some]
  simpa only [same, encodeByteResult] using byteAt_computes bytes index

theorem byteAt_out_of_range (bytes : List UInt8) (index : Nat) (bound : bytes.length ≤ index) :
    Applies P H "vibe:byte-at" [.list (bytes.map encodeByte), natural index] (.sym "None") := by
  simpa only [List.getElem?_eq_none bound, encodeByteResult] using byteAt_computes bytes index

end Mettapedia.Languages.VibeITP.Presentation.ComputationalLiterals
