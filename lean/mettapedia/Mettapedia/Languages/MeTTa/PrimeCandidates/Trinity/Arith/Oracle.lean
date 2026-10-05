import Mathlib.Data.Num.Lemmas
import Mettapedia.GSLT.LanguageDef.OracleRealization
import Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Arith.Binary

/-!
# Native binary arithmetic as a specified oracle

`Arith.Binary` declares the positive binary numbers and their sum and product by written
equations, so that nothing about them is trusted. A runtime may instead compute a closed call
`padd x y` or `pmul x y` natively, with its big integers. This module says where the trust
that this needs is placed, in the discipline shared by every oracle library
(`GSLT.LanguageDef.OracleExtension`, `GSLT.LanguageDef.OracleRealization`):

* **the library** (`library`): the two typed entries `padd : pos → pos → pos` and
  `pmul : pos → pos → pos`, admitted over the language of the binary numerals
  (`arithLanguage`), whose terms are `one`, `bit0 p` and `bit1 p`;
* **its meaning** (`meaning`): the declared semantics, read through the value maps of
  `Arith.Binary`. A call relates its two numeral arguments to the numeral whose value is the
  value of the declared call in the set model of the binary package (`den` is the value of a
  closed numeral there, `pv` the value map); read as sets instead, the numeral denotes the
  declared call itself (`value_eq_iff`);
* **the backend model** (`natModel`): Lean's natural numbers as the model of the runtime's
  big integers. The model reads the two numerals as numbers, adds or multiplies them, and
  writes the result back as a numeral;
* **the realization meets the meaning** (`realization_meets`), from the homomorphism theorems
  of `Arith.Binary` (`pv_padd`, `pmul_value'`) and the injectivity of the value map on the
  positive numbers of the model (`pv_injOn`), which holds because every such number is the
  value of exactly one numeral (`den_surjective`, `den_injective`).

**Conservativity at closed redexes.** When the declared equations compute a numeral `z` for
`padd x y` (a derivation of `padd x y ≡ z : pos` in the judgment of the binary package), the
model of the backend returns exactly `z` (`conservative_padd`, `conservative_pmul`; in the
model, `conservative_of_meets` for every realization that meets the meaning). The proof goes
through the set model, so it holds relative to `CofinalInaccessibles`, as the set model does.

**Where the trust is placed.** `realization_meets` is a statement about the model. That the
compiled backend computes what the model computes is not proved here: the theorems about the
running code carry it as an explicit hypothesis. `compiled_conservative` assumes
`compiledAgrees`, that the compiled backend returns on every call what the model returns;
`compiled_answer_eq` assumes only `compiledSound`, that every answer it does return is the
model's, which is what a backend that declines some calls (64-bit words) needs. Each is a
hypothesis, never an axiom, and it is the only trust the runtime's oracle adds.

**The three faces.** The operational face gains a native step; its meaning is taken from the
extensional face, the set model of the admitted package; and the intensional face, the
judgment, enters through conservativity: a derivation of the judgment and the backend give
the same numeral.

Positive example: `1 + 1` is `2` in the model (`natModel_one_plus_one`), and the declared
equations of `padd` derive `padd one one ≡ bit0 one` (`padd_one_one_rule`), which the
backend returns (`backend_one_plus_one`).

Negative example: a backend whose addition is off by one at `2^64` (`offByOneModel`) returns
`2^64 + 1` for `(2^64 - 1) + 1`; it does not meet the meaning (`offByOne_not_meets`), and
conservativity fails under it (`offByOne_not_conservative`).

Not here: the comparison, the subtraction, the division, the greatest common divisor and the
fractions of the runtime's oracle. `Arith.Binary` gives them no declarations and no value
map, so they have no meaning in this discipline yet; their native computation is trusted
with tests only.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Arith.Oracle

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.OracleExtension
open Mettapedia.GSLT.LanguageDef.OracleRealization
open Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Arith.Binary
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram
open ExecutableModel ExecutableModel.CodeModel
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
open Presentation Presentation.TypedEquality Presentation.TypedEquality.Annotated

/-! ## The numerals -/

/-- A positive numeral as a closed term of the binary package. -/
def term : PosNum → CTm Tower.Head 0
  | .one => pone
  | .bit0 p => pbit0 (term p)
  | .bit1 p => pbit1 (term p)

/-- A positive numeral as a pattern of the numeral language. -/
def pattern : PosNum → Pattern
  | .one => .apply "one" []
  | .bit0 p => .apply "bit0" [pattern p]
  | .bit1 p => .apply "bit1" [pattern p]

/-- Reading a pattern as a positive numeral: `none` for anything else. -/
def read : Pattern → Option PosNum
  | .apply "one" [] => some .one
  | .apply "bit0" [p] => (read p).map .bit0
  | .apply "bit1" [p] => (read p).map .bit1
  | _ => none

@[simp] theorem read_pattern : ∀ p : PosNum, read (pattern p) = some p
  | .one => rfl
  | .bit0 p => by simp [pattern, read, read_pattern p]
  | .bit1 p => by simp [pattern, read, read_pattern p]

theorem pattern_injective : Function.Injective pattern := by
  intro p q same
  have := congrArg read same
  simpa using this

/-- A pattern that reads as a numeral is that numeral's pattern. -/
theorem eq_pattern_of_read {q : Pattern} {p : PosNum} (returned : read q = some p) :
    q = pattern p := by
  induction q using read.induct generalizing p with
  | case1 =>
      simp only [read, Option.some.injEq] at returned
      subst returned
      rfl
  | case2 q ih =>
      simp only [read, Option.map_eq_some_iff] at returned
      obtain ⟨r, readR, rfl⟩ := returned
      rw [ih readR]
      rfl
  | case3 q ih =>
      simp only [read, Option.map_eq_some_iff] at returned
      obtain ⟨r, readR, rfl⟩ := returned
      rw [ih readR]
      rfl
  | case4 q notOne notBit0 notBit1 =>
      rw [read.eq_4 q notOne notBit0 notBit1] at returned
      cases returned

theorem ofNatSucc_cast : ∀ k : ℕ, ((PosNum.ofNatSucc k : PosNum) : ℕ) = k + 1
  | 0 => rfl
  | k + 1 => by rw [PosNum.ofNatSucc, PosNum.succ_to_nat, ofNatSucc_cast k]

/-- The numeral `PosNum.ofNat n` writes `n`, for a positive `n`. -/
theorem ofNat_cast {n : ℕ} (positive : 0 < n) : ((PosNum.ofNat n : PosNum) : ℕ) = n := by
  rw [PosNum.ofNat, ofNatSucc_cast, Nat.pred_eq_sub_one]
  omega

/-! ## The library, its realization and the model of the backend -/

/-- The sort of the positive numbers. -/
def posType : TypeExpr := .base "pos"

private def numeralCtor (label : String) (fields : List String) : GrammarRule where
  label := label
  category := "pos"
  params := fields.map fun field => .simple field posType
  syntaxPattern := [.terminal label]

/-- **The numeral language**: the sort `pos` and its three constructors. -/
def arithLanguage : LanguageDef where
  name := "prime-binary-arithmetic"
  types := ["pos"]
  terms := [numeralCtor "one" [], numeralCtor "bit0" ["p"], numeralCtor "bit1" ["p"]]
  equations := []
  rewrites := []

/-- The sum of two positive numbers, as a typed entry. -/
def paddDecl : OracleDecl := ⟨"padd", [posType, posType], posType⟩

/-- The product of two positive numbers, as a typed entry. -/
def pmulDecl : OracleDecl := ⟨"pmul", [posType, posType], posType⟩

/-- **The admitted library**: the sum and the product, over the numeral language. -/
def library : AdmittedLibrary arithLanguage :=
  ⟨[paddDecl, pmulDecl], by decide⟩

def paddAdmitted : Admitted library := ⟨paddDecl, by decide⟩
def pmulAdmitted : Admitted library := ⟨pmulDecl, by decide⟩

/-- The operations of the backend: big-integer addition and multiplication. -/
inductive NativeOp where
  | add
  | mul
  deriving DecidableEq

/-- What a backend operation computes on numbers. -/
def NativeOp.eval : NativeOp → ℕ → ℕ → ℕ
  | .add, a, b => a + b
  | .mul, a, b => a * b

theorem NativeOp.eval_pos (op : NativeOp) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    0 < op.eval a b := by
  cases op
  · exact Nat.add_pos_left ha b
  · exact Nat.mul_pos ha hb

/-- The backend operation of an entry. -/
def opOf (declaration : OracleDecl) : NativeOp :=
  if declaration = paddDecl then .add else .mul

/-- Each admitted entry is realized by its backend operation. -/
def realization : NativeRealization arithLanguage library NativeOp where
  implementation declaration := opOf declaration.1

/-- **The model of the backend**: Lean's natural numbers as the model of the runtime's big
integers. The two numerals are read as numbers, the operation is computed on `ℕ`, and the
result is written back as a numeral. -/
def natModel : BackendModel NativeOp where
  run op arguments :=
    match arguments with
    | [first, second] =>
        match read first, read second with
        | some a, some b => some (pattern (PosNum.ofNat (op.eval a b)))
        | _, _ => none
    | _ => none

theorem natModel_run (op : NativeOp) (x y : PosNum) :
    natModel.run op [pattern x, pattern y] = some (pattern (PosNum.ofNat (op.eval x y))) := by
  simp [natModel]

/-- Positive example: in the model, `1 + 1` is `2`. -/
theorem natModel_one_plus_one :
    natModel.run .add [pattern .one, pattern .one] = some (pattern (.bit0 .one)) := by
  decide

/-! ## The meaning: the declared semantics in the set model -/

section Model

open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (CofinalInaccessibles)
open ZFSetTraceProducts (traceApp)

universe u

variable (h : CofinalInaccessibles.{u})

/-- The declared constant of an entry. -/
def declared (declaration : OracleDecl) : DeclName :=
  if declaration = paddDecl then paddN else pmulN

/-- **The value of a closed numeral** in the set model of the binary package. -/
noncomputable def den (p : PosNum) : ZFSet.{u} :=
  ev (objHeads h) (val h) (term p) Fin.elim0

theorem den_one : den h .one = val h oneN := rfl
theorem den_bit0 (p : PosNum) : den h (.bit0 p) = ap1 h bit0N (den h p) := rfl
theorem den_bit1 (p : PosNum) : den h (.bit1 p) = ap1 h bit1N (den h p) := rfl

theorem den_mem : ∀ p : PosNum, den h p ∈ val h posN
  | .one => one_mem h
  | .bit0 p => bit0_mem h (den_mem p)
  | .bit1 p => bit1_mem h (den_mem p)

/-- The value map of `Arith.Binary` reads a numeral as the number it writes. -/
theorem pv_den : ∀ p : PosNum, pv h (den h p) = (p : ℕ)
  | .one => by rw [den_one, pv_one, PosNum.cast_one']
  | .bit0 p => by rw [den_bit0, pv_bit0 h (den_mem h p), pv_den p, PosNum.cast_bit0]
  | .bit1 p => by rw [den_bit1, pv_bit1 h (den_mem h p), pv_den p, PosNum.cast_bit1]

/-- **Distinct numerals have distinct values.** -/
theorem den_injective : Function.Injective (den h) := by
  intro p q same
  have values := congrArg (pv h) same
  rw [pv_den, pv_den] at values
  exact PosNum.to_nat_inj.mp values

/-- **Every positive number of the model is the value of a numeral**, by induction on the
set of positive numbers. -/
theorem den_surjective : ∀ s ∈ val h posN, ∃ p : PosNum, den h p = s := by
  refine pos_induct h ?_ ?_ ?_
  · exact ⟨.one, rfl⟩
  · rintro a _ ⟨p, rfl⟩
    exact ⟨.bit0 p, rfl⟩
  · rintro a _ ⟨p, rfl⟩
    exact ⟨.bit1 p, rfl⟩

/-- **The value map is injective on the positive numbers of the model.** -/
theorem pv_injOn {s t : ZFSet.{u}} (hs : s ∈ val h posN) (ht : t ∈ val h posN)
    (same : pv h s = pv h t) : s = t := by
  obtain ⟨p, rfl⟩ := den_surjective h s hs
  obtain ⟨q, rfl⟩ := den_surjective h t ht
  rw [pv_den, pv_den] at same
  rw [PosNum.to_nat_inj.mp same]

theorem declared_mem (declaration : OracleDecl) {s t : ZFSet.{u}} (hs : s ∈ val h posN)
    (ht : t ∈ val h posN) : ap2 h (declared declaration) s t ∈ val h posN := by
  unfold declared
  split
  · exact padd_mem h hs ht
  · exact pmul_mem h hs ht

/-- The value of a declared call is the backend operation on the values: `pv_padd` for the
sum, `pmul_value'` for the product. -/
theorem pv_declared (declaration : OracleDecl) {s t : ZFSet.{u}} (hs : s ∈ val h posN)
    (ht : t ∈ val h posN) :
    pv h (ap2 h (declared declaration) s t) = (opOf declaration).eval (pv h s) (pv h t) := by
  unfold declared opOf
  split
  · exact pv_padd h hs ht
  · exact pmul_value' h s hs t ht

/-- **The meaning of the library**, the declared semantics read through the value maps of
`Arith.Binary`: a call relates its two numeral arguments to the numeral whose value is the
value of the declared call in the set model of the binary package. -/
def meaning : Meaning library where
  relates declaration arguments result :=
    ∃ x y z : PosNum, arguments = [pattern x, pattern y] ∧ result = pattern z ∧
      pv h (den h z) = pv h (ap2 h (declared declaration.1) (den h x) (den h y))

/-- Read through the value map or as sets, the meaning is the same: the numeral denotes the
declared call itself. -/
theorem value_eq_iff (declaration : OracleDecl) (x y z : PosNum) :
    pv h (den h z) = pv h (ap2 h (declared declaration) (den h x) (den h y)) ↔
      den h z = ap2 h (declared declaration) (den h x) (den h y) :=
  ⟨pv_injOn h (den_mem h z) (declared_mem h declaration (den_mem h x) (den_mem h y)),
    congrArg (pv h)⟩

/-- The numeral the model returns has, in the set model, the value of the declared call. -/
theorem den_ofNat_eval (declaration : OracleDecl) (x y : PosNum) :
    den h (PosNum.ofNat ((opOf declaration).eval x y)) =
      ap2 h (declared declaration) (den h x) (den h y) := by
  apply pv_injOn h (den_mem h _) (declared_mem h declaration (den_mem h x) (den_mem h y))
  rw [pv_den, pv_declared h declaration (den_mem h x) (den_mem h y), pv_den, pv_den,
    ofNat_cast ((opOf declaration).eval_pos (PosNum.to_nat_pos x) (PosNum.to_nat_pos y))]

/-- **The realization meets the meaning in the model of `ℕ`.** The model returns exactly the
numerals the declared semantics relates, on every admitted entry. -/
theorem realization_meets : Meets realization natModel (meaning h) := by
  intro declaration arguments result
  change natModel.run (opOf declaration.1) arguments = some result ↔ _
  constructor
  · intro returned
    match arguments, returned with
    | [first, second], returned =>
        simp only [natModel] at returned
        cases readFirst : read first with
        | none => simp [readFirst] at returned
        | some x =>
            cases readSecond : read second with
            | none => simp [readFirst, readSecond] at returned
            | some y =>
                simp only [readFirst, readSecond, Option.some.injEq] at returned
                exact ⟨x, y, PosNum.ofNat ((opOf declaration.1).eval x y),
                  by rw [eq_pattern_of_read readFirst, eq_pattern_of_read readSecond],
                  returned.symm,
                  (value_eq_iff h declaration.1 x y _).mpr (den_ofNat_eval h declaration.1 x y)⟩
  · rintro ⟨x, y, z, rfl, rfl, valued⟩
    rw [natModel_run]
    congr 2
    apply den_injective h
    rw [(value_eq_iff h declaration.1 x y z).mp valued, den_ofNat_eval]

/-! ## Conservativity at closed redexes -/

/-- **Conservativity at closed redexes, in the model**: whenever the declared call at the
numerals `x` and `y` has, in the set model, the value of the numeral `z`, the backend returns
`z`. -/
def Conservative {Backend : Type*} (implementation : NativeRealization arithLanguage library Backend)
    (model : BackendModel Backend) : Prop :=
  ∀ (declaration : Admitted library) (x y z : PosNum),
    den h z = ap2 h (declared declaration.1) (den h x) (den h y) →
      model.run (implementation.implementation declaration) [pattern x, pattern y] =
        some (pattern z)

/-- Every realization that meets the meaning is conservative. -/
theorem conservative_of_meets {Backend : Type*}
    {implementation : NativeRealization arithLanguage library Backend}
    {model : BackendModel Backend} (meets : Meets implementation model (meaning h)) :
    Conservative h implementation model :=
  fun declaration x y z valued => (meets declaration _ _).mpr
    ⟨x, y, z, rfl, rfl, (value_eq_iff h declaration.1 x y z).mpr valued⟩

theorem natModel_conservative : Conservative h realization natModel :=
  conservative_of_meets h (realization_meets h)

/-- **A derivation of the judgment fixes the value**: if the declared equations derive
`f x y ≡ z : pos` in the binary package, the set model gives the call the value of `z`. -/
theorem den_of_computes {f : DeclName} {x y z : PosNum}
    (computes : CEqual binary .nil (call2 f (term x) (term y)) (term z) cpos) :
    den h z = ap2 h f (den h x) (den h y) :=
  (rule0 h computes).symm

include h in
/-- **Conservativity at closed redexes for the sum.** If the declared equations of `padd`
derive `padd x y ≡ z : pos` for closed numerals, the model of the backend returns `z`. -/
theorem conservative_padd {x y z : PosNum}
    (computes : CEqual binary .nil (call2 paddN (term x) (term y)) (term z) cpos) :
    natModel.run (realization.implementation paddAdmitted) [pattern x, pattern y] =
      some (pattern z) :=
  natModel_conservative h paddAdmitted x y z (den_of_computes h computes)

include h in
/-- **Conservativity at closed redexes for the product.** -/
theorem conservative_pmul {x y z : PosNum}
    (computes : CEqual binary .nil (call2 pmulN (term x) (term y)) (term z) cpos) :
    natModel.run (realization.implementation pmulAdmitted) [pattern x, pattern y] =
      some (pattern z) :=
  natModel_conservative h pmulAdmitted x y z (den_of_computes h computes)

include h in
/-- **The running code, under its one hypothesis.** `compiled` is what the runtime's compiled
backend returns on a call. The theorem depends on `compiledAgrees`: the compiled backend
returns, on every call, what the model of `ℕ` returns. That hypothesis is the trust placed in
the backend (the big-integer library and the code that reads and writes numerals); it is not
proved here and it is not an axiom. Under it, the runtime returns the numeral the declared
equations compute. -/
theorem compiled_conservative (compiled : NativeOp → List Pattern → Option Pattern)
    (compiledAgrees : ∀ op arguments, compiled op arguments = natModel.run op arguments)
    (declaration : Admitted library) {x y z : PosNum}
    (computes : CEqual binary .nil (call2 (declared declaration.1) (term x) (term y)) (term z)
      cpos) :
    compiled (realization.implementation declaration) [pattern x, pattern y] =
      some (pattern z) := by
  rw [compiledAgrees]
  exact natModel_conservative h declaration x y z (den_of_computes h computes)

include h in
/-- **A backend that may decline, under its one hypothesis.** A backend that answers only
some calls, such as one computing with 64-bit words, needs less: `compiledSound` says that
every answer it returns is the answer of the model of `ℕ`. Under it, every answer it returns
is the numeral the declared equations compute; declining costs nothing but speed. -/
theorem compiled_answer_eq (compiled : NativeOp → List Pattern → Option Pattern)
    (compiledSound : ∀ op arguments answer,
      compiled op arguments = some answer → natModel.run op arguments = some answer)
    (declaration : Admitted library) {x y z : PosNum} {answer : Pattern}
    (returned : compiled (realization.implementation declaration) [pattern x, pattern y] =
      some answer)
    (computes : CEqual binary .nil (call2 (declared declaration.1) (term x) (term y)) (term z)
      cpos) :
    answer = pattern z := by
  have conservative := natModel_conservative h declaration x y z (den_of_computes h computes)
  rw [compiledSound _ _ _ returned] at conservative
  exact Option.some.inj conservative

/-- Positive example: the declared equations derive `padd one one ≡ bit0 one`, through
`padd`, `padd-nat`, `nsucc-pos` and `psucc`. -/
theorem padd_one_one_rule :
    CEqual binary .nil (call2 paddN (term .one) (term .one)) (term (.bit0 .one)) cpos :=
  .trans (paddEq_rule bOne bOne)
    (.trans (paddNatOne_rule (bNpos bOne)) (.trans (nsuccPosPos_rule bOne) psuccOne_rule))

include h in
/-- Positive example: the backend returns that numeral, as conservativity says. -/
theorem backend_one_plus_one :
    natModel.run (realization.implementation paddAdmitted) [pattern .one, pattern .one] =
      some (pattern (.bit0 .one)) :=
  conservative_padd h padd_one_one_rule

/-! ## Negative example: a backend off by one at a large value -/

/-- `2^(k+1) - 1`, written with `k + 1` ones. -/
def allOnes : ℕ → PosNum
  | 0 => .one
  | k + 1 => .bit1 (allOnes k)

theorem allOnes_cast : ∀ k : ℕ, ((allOnes k : PosNum) : ℕ) + 1 = 2 ^ (k + 1)
  | 0 => rfl
  | k + 1 => by
      rw [allOnes, PosNum.cast_bit1, pow_succ, ← allOnes_cast k]
      ring

/-- The value at which the faulty backend errs: `2^64`. -/
def large : ℕ := 2 ^ 64

/-- `2^64 - 1`, sixty-four ones. -/
def belowLarge : PosNum := allOnes 63

theorem belowLarge_succ : (belowLarge : ℕ) + 1 = large := allOnes_cast 63

theorem large_pos : 0 < large := by
  unfold large
  positivity

/-- **A backend whose addition is off by one at `2^64`**: it returns `2^64 + 1` where the sum
is `2^64`, and agrees with `natModel` everywhere else. -/
def offByOneModel : BackendModel NativeOp where
  run op arguments :=
    match op, arguments with
    | .add, [first, second] =>
        match read first, read second with
        | some a, some b =>
            some (pattern (PosNum.ofNat (if (a : ℕ) + b = large then large + 1 else a + b)))
        | _, _ => none
    | _, _ => natModel.run op arguments

theorem opOf_padd : opOf paddDecl = .add := if_pos rfl

theorem offByOne_returns :
    offByOneModel.run (realization.implementation paddAdmitted)
        [pattern belowLarge, pattern .one] =
      some (pattern (PosNum.ofNat (large + 1))) := by
  have sum : (belowLarge : ℕ) + ((PosNum.one : PosNum) : ℕ) = large := by
    rw [PosNum.cast_one']
    exact belowLarge_succ
  change offByOneModel.run (opOf paddDecl) [pattern belowLarge, pattern .one] = _
  rw [opOf_padd]
  simp only [offByOneModel, read_pattern]
  rw [if_pos sum]

/-- **The faulty backend does not meet the meaning**: it returns `2^64 + 1` for
`(2^64 - 1) + 1`, which the declared semantics does not relate to that call. -/
theorem offByOne_not_meets : ¬ Meets realization offByOneModel (meaning h) := by
  apply not_meets_of_wrong_result (declaration := paddAdmitted) offByOne_returns
  rintro ⟨x, y, z, same, sameResult, valued⟩
  simp only [List.cons.injEq, and_true] at same
  have xEq := pattern_injective same.1
  have yEq := pattern_injective same.2
  have zEq := pattern_injective sameResult
  subst xEq yEq
  have values := valued
  rw [pv_den, pv_declared h _ (den_mem h _) (den_mem h _), pv_den, pv_den, ← zEq,
    ofNat_cast (Nat.succ_pos large)] at values
  change large + 1 = (opOf paddDecl).eval belowLarge (PosNum.one : ℕ) at values
  rw [opOf_padd] at values
  change large + 1 = (belowLarge : ℕ) + ((PosNum.one : PosNum) : ℕ) at values
  rw [PosNum.cast_one', belowLarge_succ] at values
  omega

/-- **Under the faulty backend, conservativity fails**: the declared semantics gives
`(2^64 - 1) + 1` the value of the numeral `2^64`, and the backend does not return it. -/
theorem offByOne_not_conservative : ¬ Conservative h realization offByOneModel := by
  intro conservative
  have eval : (opOf paddDecl).eval belowLarge (PosNum.one : ℕ) = large := by
    rw [opOf_padd]
    change (belowLarge : ℕ) + ((PosNum.one : PosNum) : ℕ) = large
    rw [PosNum.cast_one']
    exact belowLarge_succ
  have valued : den h (PosNum.ofNat large) =
      ap2 h (declared paddAdmitted.1) (den h belowLarge) (den h .one) := by
    have := den_ofNat_eval h paddDecl belowLarge .one
    rw [eval] at this
    exact this
  have returned := conservative paddAdmitted belowLarge .one (PosNum.ofNat large) valued
  rw [offByOne_returns, Option.some.injEq] at returned
  have values := congrArg (fun p => (read p).map (fun n : PosNum => (n : ℕ))) returned
  simp only [read_pattern, Option.map_some, Option.some.injEq] at values
  rw [ofNat_cast (Nat.succ_pos large), ofNat_cast large_pos] at values
  omega

end Model


end Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Arith.Oracle
