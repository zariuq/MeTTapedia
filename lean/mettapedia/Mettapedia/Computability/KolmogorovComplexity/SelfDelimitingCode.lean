import Mettapedia.Computability.KolmogorovComplexity.Prefix

/-!
# Self-delimiting codes with logarithmic overhead

Reusable binary self-delimiting codes, used by the algorithmic-containment
theory for *program-side* data whose overhead must be logarithmic:

* `e1encode x = replicate |x| true ++ [false] ++ x` — the unary header code,
  `|e1encode x| = 2|x| + 1`.
* `e2encode x = e1encode (binaryBits |x|) ++ x` — binary length header,
  `|e2encode x| ≤ |x| + 2 * Nat.log 2 (|x| + 1) + 3`.

Both families are proved prefix-free and injective, decoders round-trip even
in context (`e1decode (e1encode x ++ rest) = some (x, rest)`), which yields the
prefix-freeness proofs by a single decode comparison.

The `E1`/`E2` terminology follows Franz, Antonenko, and Soletskyi, *A Theory
of Incremental Compression* (2021), and is shared with the `ic-theory` Lean
formalization lineage.  This module supplies Mettapedia's proof-relevant
decoder, primitive-recursive, and contextual-suffix interfaces for those
codes.

The negative control `unary_overhead_exceeds_e2` shows that the project-wide
unary code `machinePrefix` (overhead `n + 1`) has linear rather than
logarithmic overhead: its excess over the `e2` header exceeds every fixed
margin for some sufficiently large `n`.  Program-side encodings (e.g. the `q = E2(t) ++ p`
parameter in the algorithmic-containment construction) must therefore use
`e2encode`, never `machinePrefix`.  Condition-side pairing pays no program
length and is unaffected.

All proofs are kernel-checked and introduce no additional axioms.
-/

namespace KolmogorovComplexity

open scoped Classical

/-! ## Binary representation of naturals -/

/-- Big-endian binary representation of `n`.  The digits of `0` are `[]`,
which decodes back to `0` by `Nat.ofDigits`. -/
def binaryBits (n : Nat) : BinString :=
  (Nat.digits 2 n).reverse.map fun d => decide (d = 1)

/-- Binary digits in base two are primitive recursive.  The strong-recursion
table stores the already computed digit lists below `n`; the `n / 2` entry is
there whenever `n` is positive. -/
theorem digitsTwo_primrec : Primrec (Nat.digits 2) := by
  let step : Unit → List (List Nat) → Option (List Nat) :=
    fun _ previous =>
      some (if previous.length = 0 then [] else
        previous.length % 2 :: previous[previous.length / 2]?.getD [])
  have hStep : Primrec₂ step := by
    apply Primrec₂.mk
    have hLength : Primrec fun input : Unit × List (List Nat) =>
        input.2.length :=
      Primrec.list_length.comp Primrec.snd
    have hIndex : Primrec fun input : Unit × List (List Nat) =>
        input.2.length / 2 :=
      Primrec.nat_div.comp hLength (Primrec.const 2)
    have hSelected : Primrec fun input : Unit × List (List Nat) =>
        input.2[input.2.length / 2]? :=
      Primrec.list_getElem?.comp Primrec.snd hIndex
    have hTail : Primrec fun input : Unit × List (List Nat) =>
        input.2[input.2.length / 2]?.getD [] :=
      Primrec.option_getD.comp hSelected (Primrec.const [])
    have hDigit : Primrec fun input : Unit × List (List Nat) =>
        input.2.length % 2 :=
      Primrec.nat_mod.comp hLength (Primrec.const 2)
    have hCons : Primrec fun input : Unit × List (List Nat) =>
        input.2.length % 2 :: input.2[input.2.length / 2]?.getD [] :=
      Primrec.list_cons.comp hDigit hTail
    have hZero : PrimrecPred fun input : Unit × List (List Nat) =>
        input.2.length = 0 :=
      Primrec.eq.comp hLength (Primrec.const 0)
    exact (Primrec.option_some.comp
      (Primrec.ite hZero (Primrec.const []) hCons)).of_eq fun input => by
        simp [step]
  have hStrong : Primrec₂ fun (_ : Unit) n => Nat.digits 2 n := by
    apply Primrec.nat_strong_rec (fun (_ : Unit) n => Nat.digits 2 n) hStep
    intro _ n
    simp only [step, List.length_map, List.length_range]
    by_cases hn : n = 0
    · subst n
      simp
    · have hdiv : n / 2 < n :=
        Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by omega)
      have hDigits : Nat.digits 2 n =
          n % 2 :: Nat.digits 2 (n / 2) :=
        Nat.digits_eq_cons_digits_div (b := 2) (n := n) (by omega) hn
      rw [if_neg hn]
      simpa [hdiv] using hDigits.symm
  exact hStrong.comp (Primrec.const ()) Primrec.id

/-- The canonical big-endian bit representation is primitive recursive. -/
theorem binaryBits_primrec : Primrec binaryBits := by
  have hBit : Primrec fun d : Nat => decide (d = 1) :=
    (Primrec.beq.comp Primrec.id (Primrec.const 1)).of_eq fun d => by
      apply Bool.eq_iff_iff.mpr
      simp
  have hMapped : Primrec fun digits : List Nat =>
      digits.map fun d => decide (d = 1) :=
    Primrec.list_map Primrec.id (hBit.comp₂ Primrec₂.right)
  exact hMapped.comp (Primrec.list_reverse.comp digitsTwo_primrec)

/-- Interpret a big-endian bit string as a natural number. -/
def ofBinaryBits (bits : BinString) : Nat :=
  Nat.ofDigits 2 (bits.reverse.map fun bit => if bit then 1 else 0)

/-- Interpreting a finite binary word as a natural number is primitive
recursive. -/
theorem ofBinaryBits_primrec : Primrec ofBinaryBits := by
  let bitValue : Bool → Nat := fun bit => if bit then 1 else 0
  have hBitValue : Primrec bitValue := Primrec.dom_bool bitValue
  have hDigits : Primrec fun bits : BinString =>
      bits.reverse.map bitValue :=
    Primrec.list_map Primrec.list_reverse
      (hBitValue.comp₂ Primrec₂.right)
  have hStep : Primrec₂ fun (_bits : BinString) (state : Nat × Nat) =>
      state.1 + 2 * state.2 :=
    Primrec.nat_add.comp₂
      (Primrec.fst.comp₂ Primrec₂.right)
      (Primrec.nat_mul.comp₂ (Primrec₂.const 2)
        (Primrec.snd.comp₂ Primrec₂.right))
  have hFold : Primrec fun bits : BinString =>
      (bits.reverse.map bitValue).foldr
        (fun digit state => digit + 2 * state) 0 :=
    Primrec.list_foldr hDigits (Primrec.const 0) hStep
  exact hFold.of_eq fun bits => by
    unfold ofBinaryBits bitValue
    exact (Nat.ofDigits_eq_foldr 2 _).symm

/-- The bit-string representation round-trips through the numeric decoder. -/
theorem ofBinaryBits_binaryBits (n : Nat) : ofBinaryBits (binaryBits n) = n := by
  have h1 : (binaryBits n).reverse =
      (Nat.digits 2 n).map fun d => decide (d = 1) := by
    unfold binaryBits
    rw [← List.map_reverse, List.reverse_reverse]
  have hpoint : ∀ d ∈ Nat.digits 2 n,
      ((fun bit => if bit then 1 else 0) ∘ fun d => decide (d = 1)) d = d := by
    intro d hd
    have hd2 : d < 2 := Nat.digits_lt_base (by norm_num) hd
    interval_cases d <;> simp
  show Nat.ofDigits 2 ((binaryBits n).reverse.map fun bit => if bit then 1 else 0) = n
  rw [h1, List.map_map, List.map_congr_left hpoint, List.map_id',
    Nat.ofDigits_digits]

theorem binaryBits_injective : Function.Injective binaryBits := by
  intro m n h
  have hm := ofBinaryBits_binaryBits m
  have hn := ofBinaryBits_binaryBits n
  rw [← hm, ← hn, h]

theorem binaryBits_length (n : Nat) :
    (binaryBits n).length ≤ Nat.log 2 n + 1 := by
  by_cases hn : n = 0
  · subst hn
    simp [binaryBits]
  · have hlen := Nat.length_digits 2 n (by norm_num) hn
    simp [binaryBits, hlen]

/-! ## The first code `e1encode` (unary length header) -/

/-- First self-delimiting code: `1^|x| 0 x`. -/
def e1encode (x : BinString) : BinString :=
  List.replicate x.length true ++ [false] ++ x

/-- Count the leading `true` bits; return the count and the remainder. -/
def countLeadingTrues : BinString → Nat × BinString
  | [] => (0, [])
  | true :: rest =>
      let (n, tail) := countLeadingTrues rest
      (n + 1, tail)
  | false :: rest => (0, false :: rest)

/-- One step of the leading-`true` counter. -/
theorem countLeadingTrues_true (tail : BinString) :
    countLeadingTrues (true :: tail) =
      (let (n, rest) := countLeadingTrues tail; (n + 1, rest)) :=
  rfl

/-- A successful leading-`true` count determines the corresponding input
decomposition. -/
theorem countLeadingTrues_decompose {input : BinString} {n : Nat}
    {rest : BinString} (h : countLeadingTrues input = (n, rest)) :
    input = List.replicate n true ++ rest := by
  induction input generalizing n rest with
  | nil =>
      simp [countLeadingTrues] at h
      obtain ⟨rfl, rfl⟩ := h
      simp
  | cons bit tail ih =>
      cases bit with
      | false =>
          simp [countLeadingTrues] at h
          obtain ⟨rfl, rfl⟩ := h
          simp
      | true =>
          rw [countLeadingTrues_true] at h
          generalize htail : countLeadingTrues tail = result at h
          obtain ⟨k, rest'⟩ := result
          injection h with hn hrest
          subst n
          subst rest
          have decomposition := ih htail
          simpa [List.replicate_succ, List.append_assoc] using
            congrArg (List.cons true) decomposition

theorem countLeadingTrues_replicate (n : Nat) (rest : BinString) :
    countLeadingTrues (List.replicate n true ++ (false :: rest)) =
      (n, false :: rest) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.replicate_succ]
      show countLeadingTrues (true :: (List.replicate n true ++ (false :: rest))) =
        (n + 1, false :: rest)
      simp only [countLeadingTrues]
      rw [ih]

/-- Decode a leading unary-header payload, returning the payload and the
suffix after it. -/
def e1decode (w : BinString) : Option (BinString × BinString) :=
  match countLeadingTrues w with
  | (n, false :: body) =>
      if n ≤ body.length then some (body.take n, body.drop n) else none
  | _ => none

/-- An extensionally equal presentation of `e1decode` expressed through the
primitive-recursive list operations `takeWhile` and `dropWhile`.  Keeping this
presentation separate lets the semantic decoder remain simple while exposing
an executable proof interface. -/
def e1decodeEffective (w : BinString) : Option (BinString × BinString) :=
  let headerLength := (w.takeWhile fun bit => bit).length
  match w.dropWhile fun bit => bit with
  | false :: body =>
      if headerLength ≤ body.length then
        some (body.take headerLength, body.drop headerLength)
      else none
  | _ => none

/-- The recursive leading-run computation agrees with the standard
`takeWhile`/`dropWhile` decomposition. -/
theorem countLeadingTrues_eq_takeWhile_dropWhile (w : BinString) :
    countLeadingTrues w =
      ((w.takeWhile fun bit => bit).length,
        w.dropWhile fun bit => bit) := by
  induction w with
  | nil => rfl
  | cons bit tail tail_ih =>
      cases bit with
      | false => rfl
      | true =>
          rw [countLeadingTrues_true, List.takeWhile_cons, List.dropWhile_cons]
          simp only [↓reduceIte, List.length_cons]
          rw [tail_ih]

theorem e1decodeEffective_eq_e1decode (w : BinString) :
    e1decodeEffective w = e1decode w := by
  unfold e1decodeEffective e1decode
  rw [countLeadingTrues_eq_takeWhile_dropWhile]
  generalize List.dropWhile (fun bit : Bool => bit) w = rest
  cases rest with
  | nil => rfl
  | cons bit body => cases bit <;> rfl

/-- The self-delimiting header decoder is primitive recursive. -/
theorem e1decodeEffective_primrec : Primrec e1decodeEffective := by
  let isTrue : Bool → Bool := fun bit => bit
  let headerLength : BinString → Nat := fun w => (w.takeWhile isTrue).length
  let remainder : BinString → BinString := fun w => w.dropWhile isTrue
  have hIsTrue : Primrec isTrue := Primrec.id
  have hHeaderLength : Primrec headerLength :=
    Primrec.list_length.comp (Primrec.list_takeWhile hIsTrue)
  have hRemainder : Primrec remainder := Primrec.list_dropWhile hIsTrue
  have hBody : Primrec₂ fun (_w : BinString)
      (fields : Bool × BinString) => fields.2 :=
    Primrec.snd.comp₂ Primrec₂.right
  have hLengthCondition : PrimrecRel fun (w : BinString)
      (fields : Bool × BinString) => headerLength w ≤ fields.2.length :=
    Primrec.nat_le.comp₂
      (hHeaderLength.comp₂ Primrec₂.left)
      (Primrec.list_length.comp₂ hBody)
  have hTake : Primrec₂ fun (w : BinString)
      (fields : Bool × BinString) => fields.2.take (headerLength w) :=
    Primrec.list_take.comp₂
      (hHeaderLength.comp₂ Primrec₂.left) hBody
  have hDrop : Primrec₂ fun (w : BinString)
      (fields : Bool × BinString) => fields.2.drop (headerLength w) :=
    Primrec.list_drop.comp₂
      (hHeaderLength.comp₂ Primrec₂.left) hBody
  have hDecoded : Primrec₂ fun (w : BinString)
      (fields : Bool × BinString) =>
        some (fields.2.take (headerLength w),
          fields.2.drop (headerLength w)) :=
    Primrec.option_some.comp₂ (Primrec₂.pair.comp₂ hTake hDrop)
  have hFalseBranch : Primrec₂ fun (w : BinString)
      (fields : Bool × BinString) =>
        if headerLength w ≤ fields.2.length then
          some (fields.2.take (headerLength w),
            fields.2.drop (headerLength w))
        else none :=
    Primrec.ite hLengthCondition hDecoded (Primrec₂.const none)
  have hConsBranch : Primrec₂ fun (w : BinString)
      (fields : Bool × BinString) =>
        bif fields.1 then none else
          if headerLength w ≤ fields.2.length then
            some (fields.2.take (headerLength w),
              fields.2.drop (headerLength w))
          else none :=
    Primrec.cond
      (Primrec.fst.comp₂ Primrec₂.right)
      (Primrec₂.const none) hFalseBranch
  have hConstructed := Primrec.list_casesOn hRemainder
    (Primrec.const (none : Option (BinString × BinString))) hConsBranch
  exact hConstructed.of_eq fun w => by
    unfold e1decodeEffective headerLength remainder isTrue
    cases hRest : List.dropWhile (fun bit : Bool => bit) w with
    | nil => rfl
    | cons bit body => cases bit <;> rfl

theorem e1decode_primrec : Primrec e1decode :=
  e1decodeEffective_primrec.of_eq e1decodeEffective_eq_e1decode

/-- `e1decode` reduces whenever the leading-run decomposition is available. -/
theorem e1decode_eq_of_countLeadingTrues (w : BinString) (n : Nat) (rest : BinString)
    (h : countLeadingTrues w = (n, false :: rest)) :
    e1decode w =
      if n ≤ rest.length then some (rest.take n, rest.drop n) else none := by
  unfold e1decode
  rw [h]

theorem e1decode_e1encode_append (x : BinString) (rest : BinString) :
    e1decode (e1encode x ++ rest) = some (x, rest) := by
  have hcount : countLeadingTrues (e1encode x ++ rest) =
      (x.length, false :: (x ++ rest)) := by
    simp only [e1encode, List.append_assoc, List.singleton_append]
    exact countLeadingTrues_replicate _ _
  rw [e1decode_eq_of_countLeadingTrues _ _ _ hcount]
  rw [if_pos (by simp)]
  rw [List.take_left, List.drop_left]

/-- Every successful `e1decode` reconstructs the original input as the encoded
head followed by the returned suffix. -/
theorem e1decode_decompose {input head rest : BinString}
    (h : e1decode input = some (head, rest)) :
    input = e1encode head ++ rest := by
  unfold e1decode at h
  generalize hcount : countLeadingTrues input = result at h
  obtain ⟨n, tail⟩ := result
  cases tail with
  | nil => simp at h
  | cons bit body =>
      cases bit with
      | true => simp at h
      | false =>
          by_cases hn : n ≤ body.length
          · change (if n ≤ body.length then
                some (body.take n, body.drop n) else none) =
                some (head, rest) at h
            rw [if_pos hn] at h
            have fields : (body.take n, body.drop n) = (head, rest) :=
              Option.some.inj h
            have hhead : body.take n = head := congrArg Prod.fst fields
            have hrest : body.drop n = rest := congrArg Prod.snd fields
            have inputDecomposition := countLeadingTrues_decompose hcount
            rw [inputDecomposition, ← hhead, ← hrest]
            have hlength : (body.take n).length = n := by
              rw [List.length_take, min_eq_left hn]
            simp [e1encode, List.append_assoc, hlength]
          · change (if n ≤ body.length then
                some (body.take n, body.drop n) else none) =
                some (head, rest) at h
            rw [if_neg hn] at h
            simp at h

/-- Appending a suffix after a successfully decoded input leaves its head
unchanged and appends to the returned tail. -/
theorem e1decode_append_of_success {input head rest : BinString}
    (h : e1decode input = some (head, rest)) (suffix : BinString) :
    e1decode (input ++ suffix) = some (head, rest ++ suffix) := by
  rw [e1decode_decompose h, List.append_assoc]
  exact e1decode_e1encode_append head (rest ++ suffix)

theorem e1encode_prefix {x y : BinString} (h : e1encode x <+: e1encode y) :
    x = y := by
  obtain ⟨s, hs⟩ := h
  have hy := e1decode_e1encode_append y []
  rw [List.append_nil] at hy
  have hx := e1decode_e1encode_append x s
  rw [← hs, hx] at hy
  have hpair : (x, s) = (y, []) := Option.some.inj hy
  exact congrArg Prod.fst hpair

theorem e1encode_injective : Function.Injective e1encode := by
  intro x y h
  exact e1encode_prefix ⟨[], by rw [h, List.append_nil]⟩

/-- The `e1encode` image is prefix-free: a code lemma usable with the Kraft
inequality machinery. -/
theorem e1_prefixFree : PrefixFree (Set.range e1encode) := by
  intro s hs t ht hne hpref
  obtain ⟨x, rfl⟩ := hs
  obtain ⟨y, rfl⟩ := ht
  have hxy := e1encode_prefix hpref
  exact hne (by rw [hxy])

theorem e1encode_length (x : BinString) :
    (e1encode x).length = 2 * x.length + 1 := by
  simp [e1encode]
  omega

/-! ## The second code `e2encode` (binary length header, logarithmic overhead) -/

/-- Second self-delimiting code: `e1encode (binaryBits |x|) ++ x`. -/
def e2encode (x : BinString) : BinString :=
  e1encode (binaryBits x.length) ++ x

/-- Decode a leading binary-header payload. -/
def e2decode (w : BinString) : Option (BinString × BinString) :=
  match e1decode w with
  | none => none
  | some (headerBits, rest) =>
      let n := ofBinaryBits headerBits
      if n ≤ rest.length then some (rest.take n, rest.drop n) else none

/-- Decoding a binary-length self-delimiting field is primitive recursive. -/
theorem e2decode_primrec : Primrec e2decode := by
  have hBranch : Primrec₂ fun (_w : BinString)
      (fields : BinString × BinString) =>
      let n := ofBinaryBits fields.1
      if n ≤ fields.2.length then
        some (fields.2.take n, fields.2.drop n)
      else none := by
    apply Primrec₂.mk
    have hLength : Primrec fun input : BinString × (BinString × BinString) =>
        ofBinaryBits input.2.1 :=
      ofBinaryBits_primrec.comp (Primrec.fst.comp Primrec.snd)
    have hBody : Primrec fun input : BinString × (BinString × BinString) =>
        input.2.2 :=
      Primrec.snd.comp Primrec.snd
    have hCondition : PrimrecPred fun input : BinString × (BinString × BinString) =>
        ofBinaryBits input.2.1 ≤ input.2.2.length :=
      Primrec.nat_le.comp hLength (Primrec.list_length.comp hBody)
    have hTake : Primrec fun input : BinString × (BinString × BinString) =>
        input.2.2.take (ofBinaryBits input.2.1) :=
      Primrec.list_take.comp hLength hBody
    have hDrop : Primrec fun input : BinString × (BinString × BinString) =>
        input.2.2.drop (ofBinaryBits input.2.1) :=
      Primrec.list_drop.comp hLength hBody
    exact Primrec.ite hCondition
      (Primrec.option_some.comp (hTake.pair hDrop))
      (Primrec.const none)
  exact (Primrec.option_bind e1decode_primrec hBranch).of_eq fun w => by
    unfold e2decode
    cases e1decode w <;> rfl

theorem e2decode_e2encode_append (x : BinString) (rest : BinString) :
    e2decode (e2encode x ++ rest) = some (x, rest) := by
  simp only [e2decode, e2encode, List.append_assoc, e1decode_e1encode_append,
    ofBinaryBits_binaryBits]
  rw [if_pos (by simp)]
  rw [List.take_left, List.drop_left]

/-- Appending a suffix after a successfully decoded `e2` field leaves its
payload unchanged and appends to the returned tail. -/
theorem e2decode_append_of_success {input head rest : BinString}
    (h : e2decode input = some (head, rest)) (suffix : BinString) :
    e2decode (input ++ suffix) = some (head, rest ++ suffix) := by
  unfold e2decode at h ⊢
  cases hHeader : e1decode input with
  | none => simp [hHeader] at h
  | some fields =>
      obtain ⟨headerBits, body⟩ := fields
      simp only [hHeader] at h
      let n := ofBinaryBits headerBits
      change (if n ≤ body.length then
        some (body.take n, body.drop n) else none) = some (head, rest) at h
      by_cases hn : n ≤ body.length
      · rw [if_pos hn] at h
        have decoded : (body.take n, body.drop n) = (head, rest) :=
          Option.some.inj h
        have hHead : body.take n = head := congrArg Prod.fst decoded
        have hRest : body.drop n = rest := congrArg Prod.snd decoded
        rw [e1decode_append_of_success hHeader suffix]
        change (if n ≤ (body ++ suffix).length then
          some ((body ++ suffix).take n, (body ++ suffix).drop n) else none) =
            some (head, rest ++ suffix)
        have hn' : n ≤ (body ++ suffix).length := by
          simpa using le_trans hn (Nat.le_add_right body.length suffix.length)
        rw [if_pos hn', List.take_append_of_le_length hn,
          List.drop_append_of_le_length hn, hHead, hRest]
      · rw [if_neg hn] at h
        simp at h

/-- The payload returned by a successful `e2` decode cannot be longer than
the complete encoded input. -/
theorem e2decode_head_length_le {input head rest : BinString}
    (h : e2decode input = some (head, rest)) :
    head.length ≤ input.length := by
  unfold e2decode at h
  cases hHeader : e1decode input with
  | none => simp [hHeader] at h
  | some fields =>
      obtain ⟨headerBits, body⟩ := fields
      simp only [hHeader] at h
      let n := ofBinaryBits headerBits
      change (if n ≤ body.length then
        some (body.take n, body.drop n) else none) = some (head, rest) at h
      by_cases hn : n ≤ body.length
      · rw [if_pos hn] at h
        have decoded : (body.take n, body.drop n) = (head, rest) :=
          Option.some.inj h
        have hHead : body.take n = head := congrArg Prod.fst decoded
        have hHeadLength : head.length = n := by
          rw [← hHead, List.length_take, min_eq_left hn]
        have hDecompose := e1decode_decompose hHeader
        have hBodyLength : body.length ≤ input.length := by
          rw [hDecompose]
          simp
        omega
      · rw [if_neg hn] at h
        simp at h

theorem e2encode_prefix {x y : BinString} (h : e2encode x <+: e2encode y) :
    x = y := by
  obtain ⟨s, hs⟩ := h
  have hy := e2decode_e2encode_append y []
  rw [List.append_nil] at hy
  have hx := e2decode_e2encode_append x s
  rw [← hs, hx] at hy
  have hpair : (x, s) = (y, []) := Option.some.inj hy
  exact congrArg Prod.fst hpair

theorem e2encode_injective : Function.Injective e2encode := by
  intro x y h
  exact e2encode_prefix ⟨[], by rw [h, List.append_nil]⟩

/-- The `e2encode` image is prefix-free. -/
theorem e2_prefixFree : PrefixFree (Set.range e2encode) := by
  intro s hs t ht hne hpref
  obtain ⟨x, rfl⟩ := hs
  obtain ⟨y, rfl⟩ := ht
  have hxy := e2encode_prefix hpref
  exact hne (by rw [hxy])

/-- Exact length formula for `e2encode`. -/
theorem e2encode_length (x : BinString) :
    (e2encode x).length = x.length + 2 * (binaryBits x.length).length + 1 := by
  simp [e2encode, e1encode_length]
  omega

/-- Logarithmic overhead: `|E2(x)| ≤ |x| + 2 * log₂(|x| + 1) + 3`, stated with
`Nat.log` and a uniform additive constant.  Small inputs are covered:
`binaryBits 0 = []` contributes `0 ≤ log 2 1 + 1`. -/
theorem e2encode_length_le_log (x : BinString) :
    (e2encode x).length ≤ x.length + 2 * Nat.log 2 (x.length + 1) + 3 := by
  rw [e2encode_length]
  have h1 := binaryBits_length (x.length)
  have h2 : Nat.log 2 (x.length) ≤ Nat.log 2 (x.length + 1) :=
    Nat.log_mono_right (Nat.le_succ x.length)
  omega

/-! ## A reusable head-and-tail pairing -/

/-- Pair a self-delimited head with an unmodified tail.  This is the exact
shape used whenever a decoder must recover one finite payload and leave the
remaining program or residual bits untouched. -/
def e2pair (head tail : BinString) : BinString :=
  e2encode head ++ tail

theorem e2decode_e2pair (head tail : BinString) :
    e2decode (e2pair head tail) = some (head, tail) := by
  simpa [e2pair] using e2decode_e2encode_append head tail

theorem e2pair_injective :
    Function.Injective (Function.uncurry e2pair) := by
  rintro ⟨head, tail⟩ ⟨head', tail'⟩ h
  change e2pair head tail = e2pair head' tail' at h
  have hdecode : some (head, tail) = some (head', tail') := by
    calc
      some (head, tail) = e2decode (e2pair head tail) :=
        (e2decode_e2pair head tail).symm
      _ = e2decode (e2pair head' tail') := congrArg e2decode h
      _ = some (head', tail') := e2decode_e2pair head' tail'
  exact Option.some.inj hdecode

theorem e2pair_length (head tail : BinString) :
    (e2pair head tail).length =
      head.length + 2 * (binaryBits head.length).length + 1 + tail.length := by
  simp [e2pair, e2encode_length, List.length_append]

theorem e2pair_length_le_log (head tail : BinString) :
    (e2pair head tail).length ≤
      head.length + 2 * Nat.log 2 (head.length + 1) + 3 + tail.length := by
  unfold e2pair
  rw [List.length_append]
  exact Nat.add_le_add_right (e2encode_length_le_log head) tail.length

/-- Three fields encoded by nesting the reusable head-and-tail pairing.  Both
the first and the combined first-two fields are self-delimited; the final tail
is left unchanged. -/
def e2triple (first second third : BinString) : BinString :=
  e2pair (e2pair first second) third

/-- Decode all three fields of `e2triple`. -/
def e2decodeTriple (input : BinString) : Option (BinString × BinString × BinString) :=
  match e2decode input with
  | none => none
  | some (firstTwo, third) =>
      match e2decode firstTwo with
      | none => none
      | some (first, second) => some (first, second, third)

theorem e2decodeTriple_e2triple (first second third : BinString) :
    e2decodeTriple (e2triple first second third) = some (first, second, third) := by
  simp [e2decodeTriple, e2triple, e2decode_e2pair]

theorem e2triple_injective :
    Function.Injective (fun fields : BinString × BinString × BinString =>
      e2triple fields.1 fields.2.1 fields.2.2) := by
  intro left right h
  have hdecode := congrArg e2decodeTriple h
  simpa only [e2decodeTriple_e2triple, Option.some.injEq] using hdecode

theorem e2triple_length (first second third : BinString) :
    (e2triple first second third).length =
      (e2pair first second).length +
        2 * (binaryBits (e2pair first second).length).length + 1 + third.length := by
  exact e2pair_length (e2pair first second) third

theorem e2triple_length_le_log (first second third : BinString) :
    (e2triple first second third).length ≤
      (e2pair first second).length +
        2 * Nat.log 2 ((e2pair first second).length + 1) + 3 + third.length := by
  exact e2pair_length_le_log (e2pair first second) third

/-! ## Negative control: the unary `machinePrefix` has linear overhead -/

theorem machinePrefix_length (n : Nat) : (machinePrefix n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [machinePrefix, ih]

/-- For every additive margin `k`, some length `n` exists at which the unary
header overhead `n + 1` (`machinePrefix`) exceeds the `e2encode` header bound
`2 * Nat.log 2 (n + 1) + 3` by at least `k`.  Hence the unary code cannot
witness logarithmic-overhead bounds such as the containment slack in the
implication-as-containment theorem. -/
theorem unary_overhead_exceeds_e2 (k : Nat) :
    ∃ n, 2 * Nat.log 2 (n + 1) + 3 + k ≤ n + 1 := by
  refine ⟨2 ^ (k + 4), ?_⟩
  have hsplit : 2 ^ (k + 4) = 16 * 2 ^ k := by
    rw [show k + 4 = 4 + k from by omega, pow_add]
    ring
  have h16 : 16 * (k + 1) ≤ 16 * 2 ^ k := by
    have h := Nat.lt_pow_self (a := 2) (n := k) (by norm_num)
    omega
  have hlog : Nat.log 2 (2 ^ (k + 4) + 1) ≤ k + 5 := by
    have hle : 2 ^ (k + 4) + 1 ≤ 2 ^ (k + 5) := by
      have hge1 : 1 ≤ 2 ^ (k + 4) := Nat.one_le_pow _ _ (by norm_num)
      have hdouble : 2 ^ (k + 5) = 2 ^ (k + 4) * 2 := by
        convert pow_succ 2 (k + 4) using 2
      rw [hdouble]; omega
    calc Nat.log 2 (2 ^ (k + 4) + 1) ≤ Nat.log 2 (2 ^ (k + 5)) :=
          Nat.log_mono_right hle
      _ = k + 5 := Nat.log_pow (by norm_num) _
  rw [hsplit] at hlog ⊢
  omega

#print axioms digitsTwo_primrec
#print axioms binaryBits_primrec
#print axioms ofBinaryBits_binaryBits
#print axioms e1_prefixFree
#print axioms e2decode_primrec
#print axioms e2decode_append_of_success
#print axioms e2decode_head_length_le
#print axioms e2_prefixFree
#print axioms e2encode_length_le_log
#print axioms e2pair_injective
#print axioms e2pair_length_le_log
#print axioms e2triple_injective
#print axioms e2triple_length_le_log
#print axioms unary_overhead_exceeds_e2

end KolmogorovComplexity
