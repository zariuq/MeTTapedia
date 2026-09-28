import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ValueSide.Algebra
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Consistency.Coherence

/-!
# The reading of codes over a realizer algebra

The candidate reading over a realizer algebra (`algebraReading`) means an
implication by the function space `arrow`, a quantifier at a carrier by
Girard's clause over the meanings of the carrier (`piOver` from `Real`, the
realizers of each meaning, to the family's candidate at it), and an equation
by the identity candidate of the equality of the two meanings. The types that
decode the codes are realized by these clauses by the laws of the algebra
alone, without reading any membership:

* **C1.** Girard's clause of a constant domain and codomain over a nonempty
  index is the function space (`Laws.piOver_const`);
* **C2.** Girard's clause over any index whose elements each carry a meaning,
  realized and sent as that meaning is, and which carries every meaning, is
  Girard's clause over the meanings: this is the law `piOver_congr`, applied
  in `carrierPi_real` to the valid arguments of a carrier's pack;
* **C3.** the identity candidate reads its proposition up to equivalence
  (`ident_congr`).

C2 is applied with the fact that every meaning of a carrier is the meaning of
a term at a world reached by a morphism: a fresh generic, or a closed
representative of a data value (`Carrier.realizedAt`).

The value of a data function applied to an argument is the function's value
at the argument's value (`appGen_dataValue`, `appData_dataValue`), and the
realizers of the value of a term of the numbers are those of its shape
(`Laws.numValReal_dataValue`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace ValueSide

open Normalization
open Consistency (Kind Carrier Reading World Morph Read DataEq DataSetting dataValue close)
open Realizability (HasShape appGen appData toQ)
open StrongNormalization (NumShape)

variable {Head : Type}

/-! ## The laws of Girard's clause and of the identity candidate -/

namespace RealizerAlgebra

variable {A : RealizerAlgebra Head}

/-- **C1.** Girard's clause with a constant domain and codomain over a nonempty
index is the function space. -/
theorem Laws.piOver_const (alg : A.Laws) {ι : Type} (nonempty : Nonempty ι) (X Y : A.Cand) :
    A.piOver (fun _ : ι => X) (fun _ => Y) = A.arrow X Y :=
  alg.piOver_congr _ _ _ _ (fun _ => ⟨(), rfl, rfl⟩) fun _ =>
    let ⟨i⟩ := nonempty
    ⟨i, rfl, rfl⟩

/-- **C3.** The identity candidate reads its proposition up to equivalence. -/
theorem ident_congr (A : RealizerAlgebra Head) {P Q : Prop} (h : P ↔ Q) :
    A.ident P = A.ident Q :=
  congrArg A.ident (propext h)

end RealizerAlgebra

/-! ## Meanings are realized -/

/-- Every meaning at a carrier is the meaning of a term at a world reached by a
morphism: a fresh generic, or a closed representative of a data value. -/
theorem Carrier.realizedAt {S : Reading Head} {k : Kind} (K : Carrier k) (v : K.V S) {n : Nat}
    (ξ : World S n) :
    ∃ (m : Nat) (ξ' : World S m) (ρ : Ren n m) (a : Tm Head m),
      Morph ξ ξ' ρ ∧ Read S ξ' a K v := by
  cases k with
  | gen =>
      exact ⟨n + 1, ξ.snoc ⟨K, v⟩, wk, .var 0, Morph.wk ξ ⟨K, v⟩, Consistency.Read.generic' _ rfl⟩
  | data =>
      obtain ⟨s, related, rfl⟩ := Consistency.dataValue_surjective v
      exact ⟨n, ξ, idRen, liftClosed s, Morph.id ξ,
        Consistency.Carrier.read_representative related⟩

/-! ## Values of data functions at arguments -/

section Values

variable {S : DataSetting Head} {P : Type}

/-- Terms that are equal have one value. -/
theorem dataValue_eq_of_eq {D : Carrier .data} {n : Nat} {t t' : Tm Head n} (e : t = t')
    (rel : DataEq S D t t) (rel' : DataEq S D t' t') :
    dataValue (P := P) S D t rel = dataValue S D t' rel' := by
  subst e
  rfl

/-- The value of a data function from a generic carrier, applied after a
renaming to any term, is the function's value. -/
theorem appGen_dataValue {K : Carrier .gen} {B : Carrier .data} {n m : Nat} {f : Tm Head n}
    (rel : DataEq S (.arr K B) f f) (ρ : Ren n m) (x : Tm Head m)
    (relApp : DataEq S B (.app (Presentation.rename ρ f) x) (.app (Presentation.rename ρ f) x)) :
    dataValue (P := P) S B (.app (Presentation.rename ρ f) x) relApp =
      appGen (P := P) (dataValue (P := P) S (.arr K B) f rel) := by
  have rel0 : DataEq S B (.app (Presentation.rename wk f) (.var 0))
      (.app (Presentation.rename wk f) (.var 0)) := rel
  have left : Presentation.subst (consSub x (renSub ρ))
      (.app (Presentation.rename wk f) (.var 0)) = .app (Presentation.rename ρ f) x := by
    simp only [Presentation.subst, subst_consSub_rename_wk, consSub_zero, subst_renSub]
  have right : Presentation.subst (liftSub (fun _ => (.const S.zero : Tm Head 0)))
      (.app (Presentation.rename wk f) (.var 0)) =
        .app (Presentation.rename wk (close S f)) (.var 0) := by
    simp only [Presentation.subst, subst_liftSub_wk, close]
    rfl
  have hl := (dataValue_eq_of_eq (P := P) left.symm relApp (by rw [left]; exact relApp)).trans
    (Consistency.dataValue_subst rel0 _ _)
  have hr := (dataValue_eq_of_eq (P := P) right.symm (DataEq.closure (D := .arr K B) rel)
    (by rw [right]; exact DataEq.closure (D := .arr K B) rel)).trans
      (Consistency.dataValue_subst rel0 _ _)
  rw [hl]
  exact hr.symm

/-- A value of a data carrier is the class of the closure of the term. -/
theorem toQ_dataValue {D : Carrier .data} {n : Nat} {t : Tm Head n} (rel : DataEq S D t t) :
    toQ (dataValue (P := P) S D t rel) = Quot.mk _ ⟨close S t, rel.closure⟩ := by
  match D, rel with
  | .num, _ => rfl
  | @Carrier.arr _ .data _ _, _ => rfl

/-- The value of a data function between data carriers, applied after a
renaming to a related argument, is the function's value at the argument's
value. -/
theorem appData_dataValue {K B : Carrier .data} {n m : Nat} {f : Tm Head n}
    (rel : DataEq S (.arr K B) f f) (ρ : Ren n m) {x : Tm Head m} (relX : DataEq S K x x)
    (relApp : DataEq S B (.app (Presentation.rename ρ f) x) (.app (Presentation.rename ρ f) x)) :
    dataValue (P := P) S B (.app (Presentation.rename ρ f) x) relApp =
      appData (dataValue (P := P) S (.arr K B) f rel) (dataValue S K x relX) := by
  have closed : close S (.app (Presentation.rename ρ f) x) = .app (close S f) (close S x) := by
    simp only [close, Presentation.subst, subst_rename]
  have relClosed : DataEq S B (.app (close S f) (close S x)) (.app (close S f) (close S x)) :=
    Realizability.DataEq.app_closed (S := S) (A := K) (B := B)
      (DataEq.closure (D := .arr K B) rel) relX.closure
  have hr : appData (P := P) (dataValue (P := P) S (.arr K B) f rel) (dataValue S K x relX) =
      dataValue S B (.app (close S f) (close S x)) relClosed := by
    change Quot.lift _ _ (toQ (dataValue (P := P) S K x relX)) = _
    rw [toQ_dataValue relX]
  rw [hr, ← Consistency.dataValue_close relApp relApp.closure]
  exact dataValue_eq_of_eq closed _ _

end Values

/-! ## Realizers of the values of the numbers -/

/-- The realizers of the value of a term of the numbers are the realizers of the
term's shape: every representative of the value has that shape. -/
theorem RealizerAlgebra.Laws.numValReal_dataValue {A : RealizerAlgebra Head} (alg : A.Laws)
    {S : Consistency.Setting Head} {star : DeclName} (laws : S.Laws)
    (rigid : S.roles star = .rigid) (num : DeclName) {n : Nat} {a : Tm Head n}
    (rel : DataEq (S.shapes star) .num a a) {s : NumShape} (shape : HasShape S star a s) :
    A.numValReal S star num (dataValue (P := A.Cand) (S.shapes star) .num a rel) =
      A.numReal num S.zero S.suc s := by
  have closed : HasShape S star (close (S.shapes star) a) s := shape.subst _
  refine alg.meet_const _ _ (fun i => ?_)
    ⟨⟨s, ⟨close (S.shapes star) a, rel.closure⟩, rfl, closed⟩⟩
  obtain ⟨s', r, same, shape'⟩ := i
  obtain ⟨s'', h₁, h₂⟩ := Consistency.Q.exact (laws.shapes rigid) same
  obtain rfl := HasShape.deterministic laws rigid shape' h₁
  obtain rfl := HasShape.deterministic laws rigid h₂ closed
  rfl

end ValueSide
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
