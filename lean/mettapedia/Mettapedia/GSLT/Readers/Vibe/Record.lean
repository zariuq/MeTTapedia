import Mettapedia.GSLT.Readers.Vibe.Correspondence
import Mettapedia.GSLT.Readers.Megalodon.RecordUnique

/-!
# Reading Vibe's encoding of an instruction gives back that instruction

`Correspondence.lean` proves that the readers' binary check accepts exactly the derivations of the
`.module` rows whose tokens spell the input and whose counts hold. This file ties those rows to Vibe
itself: it states Vibe's checker instructions (`Instr`, the 27 opcodes of `binary_spec.md`, with
THM_INSTANTIATE_N's symbols and values as pairs), Vibe's encoding of each (`Instr.encode`, as
`write_uint`/`writeUint` write words: the shortest encoding), and proves that the binary check
accepts Vibe's encoding of every instruction, with that instruction's own tree, at the instruction's
sort (`Instr.reads`); and the same for files before and after `--proofs` (`File.reads`).

An instruction's row is a list of leaves, each a token sort and an `Op`: the opcode byte, a word, a
count, a counted list of words, or counted raw bytes (`Instr.ops`). Vibe's encoding is the leaves'
bytes in order (`Instr.encode_ops`). Words are bounded by 2^64, as Vibe's `uint64_t`, and literal
bytes by 256 (`Instr.Bounded`).

The value-free shape of every row (its label, its sort, the token sorts of its leaves and their
kinds) is decided once for all 27 rows (`shapes_ok`); the values enter only through the generic facts
about words, lists and bytes in `BinaryTokens`.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.Readers.Vibe.Record

open Mettapedia.GSLT.Readers.SLR
open Mettapedia.GSLT.Readers.TreeCheck
open Mettapedia.GSLT.Readers.TokenProfile (ByteSet)
open Mettapedia.GSLT.Readers.BinaryTokens
open Mettapedia.GSLT.Readers.Vibe
open Mettapedia.GSLT.Readers.Vibe.Correspondence
open Mettapedia.GSLT.Readers.Megalodon.Record (printItems_tok printItems_nil printTree_node)

/-! ## Vibe's checker instructions -/

/-- One instruction of `check.c`, its operands in stream order (`binary_spec.md`). Slots are named
by role; THM_INSTANTIATE_N's symbols and values are given as pairs, so the two lists its one count
governs have one length. -/
inductive Instr where
  | fvarNew (arity dst : Nat)
  | constNew (binders : List Nat) (dst : Nat)
  | symbolSwap (i j : Nat)
  | symbolFree (i : Nat)
  | termNewBVar (index dst : Nat)
  | termNewLiteral (bytes : List Nat) (dst : Nat)
  | termNewApp (symbol : Nat) (args : List Nat) (dst : Nat)
  | termSwap (i j : Nat)
  | termFree (i : Nat)
  | addAxiom (statement dst : Nat)
  | thmExchange (thm term : Nat)
  | thmFree (i : Nat)
  | thmSwap (i j : Nat)
  | challengeAdd (statement dst : Nat)
  | challengeSatisfy (challenge thm : Nat)
  | modusPonens (impl premise dst : Nat)
  | thmInstantiate (thm fvar value dst : Nat)
  | defineConst (fvars hints : List Nat) (value dstSymbol dstThm : Nat)
  | litIsNat (n dst : Nat)
  | litLt (a b dst : Nat)
  | litAdd (a b dst : Nat)
  | litMul (a b dst : Nat)
  | litDiv (a b dst : Nat)
  | litLength (term dst : Nat)
  | litGet (term index dst : Nat)
  | jit (safe dst dstTerm : Nat)
  | thmInstantiateN (thm : Nat) (pairs : List (Nat × Nat)) (dst : Nat)
  deriving DecidableEq, Repr

/-- A word as Vibe's encoders write it (`write_uint` in check.c, `writeUint` in
binary_export.cpp): the shortest encoding with 247 as the largest one-byte value. -/
abbrev W (v : Nat) : List Nat := encodeWord 247 v

abbrev Ws (vs : List Nat) : List Nat := encodeWords 247 vs

/-- Vibe's encoding of an instruction: the opcode byte, then the operands as `binary_spec.md` lays
them out (a literal's bytes raw after their count). -/
def Instr.encode : Instr → List Nat
  | .fvarNew a d => 0 :: W a ++ W d
  | .constNew bs d => 1 :: W bs.length ++ Ws bs ++ W d
  | .symbolSwap i j => 2 :: W i ++ W j
  | .symbolFree i => 3 :: W i
  | .termNewBVar k d => 4 :: W k ++ W d
  | .termNewLiteral bs d => 5 :: W bs.length ++ bs ++ W d
  | .termNewApp f args d => 6 :: W f ++ W args.length ++ Ws args ++ W d
  | .termSwap i j => 7 :: W i ++ W j
  | .termFree i => 8 :: W i
  | .addAxiom t d => 9 :: W t ++ W d
  | .thmExchange h t => 10 :: W h ++ W t
  | .thmFree i => 11 :: W i
  | .thmSwap i j => 12 :: W i ++ W j
  | .challengeAdd t d => 13 :: W t ++ W d
  | .challengeSatisfy c h => 14 :: W c ++ W h
  | .modusPonens a b d => 15 :: W a ++ W b ++ W d
  | .thmInstantiate h f v d => 16 :: W h ++ W f ++ W v ++ W d
  | .defineConst fs hs v ds dt => 17 :: W fs.length ++ Ws fs ++ W hs.length ++ Ws hs ++ W v ++ W ds ++ W dt
  | .litIsNat n d => 18 :: W n ++ W d
  | .litLt a b d => 19 :: W a ++ W b ++ W d
  | .litAdd a b d => 20 :: W a ++ W b ++ W d
  | .litMul a b d => 21 :: W a ++ W b ++ W d
  | .litDiv a b d => 22 :: W a ++ W b ++ W d
  | .litLength t d => 23 :: W t ++ W d
  | .litGet t k d => 24 :: W t ++ W k ++ W d
  | .jit h d o => 25 :: W h ++ W d ++ W o
  | .thmInstantiateN h ps d =>
      26 :: W ps.length ++ W h ++ Ws (ps.map Prod.fst) ++ Ws (ps.map Prod.snd) ++ W d

/-! ## The leaves of an instruction's row -/

/-- One leaf: the opcode byte, a word, a count, a counted list of words, counted raw bytes. -/
inductive Op where
  | byte (k : Nat)
  | word (v : Nat)
  | count (n : Nat)
  | words (vs : List Nat)
  | raw (bs : List Nat)
  deriving DecidableEq, Repr

namespace Op

def bytes : Op → List Nat
  | byte k => [k]
  | word v => W v
  | count n => W n
  | words vs => Ws vs
  | raw bs => bs

/-- The token kind a leaf is read with. -/
def kind : Op → Kind
  | byte k => .byte (.points [k])
  | word _ => .word
  | count _ => .count
  | words _ => .words
  | raw _ => .bytes

/-- The bounds of Vibe's encoders: words are 64-bit, bytes are bytes. -/
def Ok : Op → Prop
  | byte k => k < 256
  | word v => v < 2 ^ 64
  | count n => n < 2 ^ 64
  | words vs => ∀ v ∈ vs, v < 2 ^ 64
  | raw bs => ∀ b ∈ bs, b < 256

end Op

/-- The counts of a row: a count sets the register; a list or bytes leaf has as many units as the
register says. -/
def countsOK : Option Nat → List Op → Bool
  | _, [] => true
  | _, .count n :: ops => countsOK (some n) ops
  | reg, .words vs :: ops => reg == some vs.length && countsOK reg ops
  | reg, .raw bs :: ops => reg == some bs.length && countsOK reg ops
  | reg, _ :: ops => countsOK reg ops

/-- An instruction's row: its label, its sort, and its leaves (token sort and leaf) in order. -/
def Instr.row : Instr → String × String × List (String × Op)
  | .fvarNew a d => ("fvar_new", "instr", [("op0", .byte 0), ("u_nat", .word a), ("u_dst_sym", .word d)])
  | .constNew bs d => ("const_new", "instr",
      [("op1", .byte 1), ("u_count", .count bs.length), ("u_nats", .words bs), ("u_dst_sym", .word d)])
  | .symbolSwap i j => ("symbol_swap", "instr", [("op2", .byte 2), ("u_sym", .word i), ("u_sym", .word j)])
  | .symbolFree i => ("symbol_free", "instr", [("op3", .byte 3), ("u_sym", .word i)])
  | .termNewBVar k d => ("term_new_bvar", "instr",
      [("op4", .byte 4), ("u_nat", .word k), ("u_dst_term", .word d)])
  | .termNewLiteral bs d => ("term_new_literal", "instr",
      [("op5", .byte 5), ("u_count", .count bs.length), ("u_bytes", .raw bs), ("u_dst_term", .word d)])
  | .termNewApp f args d => ("term_new_app", "instr",
      [("op6", .byte 6), ("u_sym", .word f), ("u_count", .count args.length), ("u_terms", .words args),
        ("u_dst_term", .word d)])
  | .termSwap i j => ("term_swap", "instr", [("op7", .byte 7), ("u_term", .word i), ("u_term", .word j)])
  | .termFree i => ("term_free", "instr", [("op8", .byte 8), ("u_term", .word i)])
  | .addAxiom t d => ("add_axiom", "setup_instr", [("op9", .byte 9), ("u_term", .word t), ("u_dst_thm", .word d)])
  | .thmExchange h t => ("thm_exchange", "instr", [("op10", .byte 10), ("u_thm", .word h), ("u_term", .word t)])
  | .thmFree i => ("thm_free", "instr", [("op11", .byte 11), ("u_thm", .word i)])
  | .thmSwap i j => ("thm_swap", "instr", [("op12", .byte 12), ("u_thm", .word i), ("u_thm", .word j)])
  | .challengeAdd t d => ("challenge_add", "instr",
      [("op13", .byte 13), ("u_term", .word t), ("u_dst_chal", .word d)])
  | .challengeSatisfy c h => ("challenge_satisfy", "proof_instr",
      [("op14", .byte 14), ("u_chal", .word c), ("u_thm", .word h)])
  | .modusPonens a b d => ("modus_ponens", "proof_instr",
      [("op15", .byte 15), ("u_thm", .word a), ("u_thm", .word b), ("u_dst_thm", .word d)])
  | .thmInstantiate h f v d => ("thm_instantiate", "proof_instr",
      [("op16", .byte 16), ("u_thm", .word h), ("u_sym", .word f), ("u_term", .word v), ("u_dst_thm", .word d)])
  | .defineConst fs hs v ds dt => ("define_const", "instr",
      [("op17", .byte 17), ("u_count", .count fs.length), ("u_syms", .words fs),
        ("u_count", .count hs.length), ("u_nats", .words hs), ("u_term", .word v),
        ("u_dst_sym", .word ds), ("u_dst_thm", .word dt)])
  | .litIsNat n d => ("thm_lit_is_nat", "proof_instr", [("op18", .byte 18), ("u_nat", .word n), ("u_dst_thm", .word d)])
  | .litLt a b d => ("thm_lit_lt", "proof_instr",
      [("op19", .byte 19), ("u_nat", .word a), ("u_nat", .word b), ("u_dst_thm", .word d)])
  | .litAdd a b d => ("thm_lit_add", "proof_instr",
      [("op20", .byte 20), ("u_nat", .word a), ("u_nat", .word b), ("u_dst_thm", .word d)])
  | .litMul a b d => ("thm_lit_mul", "proof_instr",
      [("op21", .byte 21), ("u_nat", .word a), ("u_nat", .word b), ("u_dst_thm", .word d)])
  | .litDiv a b d => ("thm_lit_div", "proof_instr",
      [("op22", .byte 22), ("u_nat", .word a), ("u_nat", .word b), ("u_dst_thm", .word d)])
  | .litLength t d => ("thm_lit_length", "proof_instr", [("op23", .byte 23), ("u_term", .word t), ("u_dst_thm", .word d)])
  | .litGet t k d => ("thm_lit_get", "proof_instr",
      [("op24", .byte 24), ("u_term", .word t), ("u_nat", .word k), ("u_dst_thm", .word d)])
  | .jit h d o => ("thm_jit", "proof_instr",
      [("op25", .byte 25), ("u_thm", .word h), ("u_dst_thm", .word d), ("u_dst_term", .word o)])
  | .thmInstantiateN h ps d => ("thm_instantiate_n", "proof_instr",
      [("op26", .byte 26), ("u_count", .count ps.length), ("u_thm", .word h),
        ("u_syms", .words (ps.map Prod.fst)), ("u_terms", .words (ps.map Prod.snd)), ("u_dst_thm", .word d)])

def Instr.label (i : Instr) : String := i.row.1
def Instr.sort (i : Instr) : String := i.row.2.1
def Instr.ops (i : Instr) : List (String × Op) := i.row.2.2

def leafOf (q : String × Op) : Tree := .leaf q.1 (strOf q.2.bytes)

/-- The tree of an instruction: its row's label over its leaves. -/
def Instr.tree (i : Instr) : Tree := .node i.label (i.ops.map leafOf)

/-- Every operand within Vibe's bounds. -/
def Instr.Bounded (i : Instr) : Prop := ∀ q ∈ i.ops, q.2.Ok

/-- Vibe's encoding is the leaves' bytes in order. -/
theorem Instr.encode_ops (i : Instr) : i.encode = i.ops.flatMap (fun q => q.2.bytes) := by
  cases i <;> simp [Instr.encode, Instr.ops, Instr.row, Op.bytes]

/-- The counts of every row hold by construction. -/
theorem Instr.counts_ok (i : Instr) : countsOK none (i.ops.map Prod.snd) = true := by
  cases i <;> simp [Instr.ops, Instr.row, Record.countsOK]

/-! ## The shapes of the rows, decided once -/

/-- The value-free shape of an instruction's row: label, sort, and each leaf's token sort and kind. -/
def Instr.shape (i : Instr) : String × String × List (String × Kind) :=
  (i.label, i.sort, i.ops.map fun q => (q.1, q.2.kind))

/-- The 27 shapes. -/
def shapes : List (String × String × List (String × Kind)) :=
  [ ("fvar_new", "instr", [("op0", .byte (.points [0])), ("u_nat", .word), ("u_dst_sym", .word)]),
    ("const_new", "instr", [("op1", .byte (.points [1])), ("u_count", .count), ("u_nats", .words), ("u_dst_sym", .word)]),
    ("symbol_swap", "instr", [("op2", .byte (.points [2])), ("u_sym", .word), ("u_sym", .word)]),
    ("symbol_free", "instr", [("op3", .byte (.points [3])), ("u_sym", .word)]),
    ("term_new_bvar", "instr", [("op4", .byte (.points [4])), ("u_nat", .word), ("u_dst_term", .word)]),
    ("term_new_literal", "instr", [("op5", .byte (.points [5])), ("u_count", .count), ("u_bytes", .bytes), ("u_dst_term", .word)]),
    ("term_new_app", "instr", [("op6", .byte (.points [6])), ("u_sym", .word), ("u_count", .count), ("u_terms", .words), ("u_dst_term", .word)]),
    ("term_swap", "instr", [("op7", .byte (.points [7])), ("u_term", .word), ("u_term", .word)]),
    ("term_free", "instr", [("op8", .byte (.points [8])), ("u_term", .word)]),
    ("add_axiom", "setup_instr", [("op9", .byte (.points [9])), ("u_term", .word), ("u_dst_thm", .word)]),
    ("thm_exchange", "instr", [("op10", .byte (.points [10])), ("u_thm", .word), ("u_term", .word)]),
    ("thm_free", "instr", [("op11", .byte (.points [11])), ("u_thm", .word)]),
    ("thm_swap", "instr", [("op12", .byte (.points [12])), ("u_thm", .word), ("u_thm", .word)]),
    ("challenge_add", "instr", [("op13", .byte (.points [13])), ("u_term", .word), ("u_dst_chal", .word)]),
    ("challenge_satisfy", "proof_instr", [("op14", .byte (.points [14])), ("u_chal", .word), ("u_thm", .word)]),
    ("modus_ponens", "proof_instr", [("op15", .byte (.points [15])), ("u_thm", .word), ("u_thm", .word), ("u_dst_thm", .word)]),
    ("thm_instantiate", "proof_instr", [("op16", .byte (.points [16])), ("u_thm", .word), ("u_sym", .word), ("u_term", .word), ("u_dst_thm", .word)]),
    ("define_const", "instr", [("op17", .byte (.points [17])), ("u_count", .count), ("u_syms", .words), ("u_count", .count), ("u_nats", .words), ("u_term", .word), ("u_dst_sym", .word), ("u_dst_thm", .word)]),
    ("thm_lit_is_nat", "proof_instr", [("op18", .byte (.points [18])), ("u_nat", .word), ("u_dst_thm", .word)]),
    ("thm_lit_lt", "proof_instr", [("op19", .byte (.points [19])), ("u_nat", .word), ("u_nat", .word), ("u_dst_thm", .word)]),
    ("thm_lit_add", "proof_instr", [("op20", .byte (.points [20])), ("u_nat", .word), ("u_nat", .word), ("u_dst_thm", .word)]),
    ("thm_lit_mul", "proof_instr", [("op21", .byte (.points [21])), ("u_nat", .word), ("u_nat", .word), ("u_dst_thm", .word)]),
    ("thm_lit_div", "proof_instr", [("op22", .byte (.points [22])), ("u_nat", .word), ("u_nat", .word), ("u_dst_thm", .word)]),
    ("thm_lit_length", "proof_instr", [("op23", .byte (.points [23])), ("u_term", .word), ("u_dst_thm", .word)]),
    ("thm_lit_get", "proof_instr", [("op24", .byte (.points [24])), ("u_term", .word), ("u_nat", .word), ("u_dst_thm", .word)]),
    ("thm_jit", "proof_instr", [("op25", .byte (.points [25])), ("u_thm", .word), ("u_dst_thm", .word), ("u_dst_term", .word)]),
    ("thm_instantiate_n", "proof_instr", [("op26", .byte (.points [26])), ("u_count", .count), ("u_thm", .word), ("u_syms", .words), ("u_terms", .words), ("u_dst_thm", .word)]) ]

theorem Instr.shape_mem (i : Instr) : i.shape ∈ shapes := by
  cases i <;> simp [Instr.shape, Instr.label, Instr.sort, Instr.ops, Instr.row, Op.kind, shapes]

/-- Every shape is a row of the `.module`: its production is the label's, flat (every item a token
sort), at the shape's sort; and each leaf's token sort has the shape's kind. -/
theorem shapes_ok : ∀ sh ∈ shapes,
    G.prodOf? sh.1 = some ⟨sh.1, sh.2.1, sh.2.2.map fun q => Sym.tok q.1⟩ ∧
      ∀ q ∈ sh.2.2, profile.kindOf? q.1 = some q.2 ∧ G.tokenSorts.contains q.1 = true := by
  decide +kernel

theorem profile_inline : profile.inline = 247 := by decide +kernel

/-! ## Words, lists and bytes within Vibe's bounds -/

theorem W_lt (v : Nat) (hv : v < 2 ^ 64) : ∀ b ∈ W v, b < 256 := by
  intro b hb
  simp only [W, encodeWord] at hb
  split at hb
  · simp at hb; omega
  · have hlen : (Nat.digits 256 v).length ≤ 8 :=
      (Nat.digits_length_le_iff (by norm_num) v).mpr (by norm_num at hv ⊢; omega)
    simp only [List.mem_cons] at hb
    rcases hb with rfl | hb
    · omega
    · exact digits_lt v b hb

theorem W_bound (v : Nat) (hv : v < 2 ^ 64) : v < 256 ^ (255 - 247) := by
  norm_num at hv ⊢; omega

theorem Op.bytes_lt (o : Op) (h : o.Ok) : ∀ b ∈ o.bytes, b < 256 := by
  cases o with
  | byte k => intro b hb; simp [Op.bytes] at hb; simp [Op.Ok] at h; omega
  | word v => exact W_lt v h
  | count n => exact W_lt n h
  | words vs =>
    intro b hb
    simp only [Op.bytes, Ws, encodeWords, List.mem_flatMap] at hb
    obtain ⟨v, hv, hbv⟩ := hb
    exact W_lt v (h v hv) b hbv
  | raw bs => exact h

/-- A leaf within the bounds is a token of its kind, the counts aside. -/
theorem Op.member (o : Op) (h : o.Ok) : o.kind.member 247 o.bytes = true := by
  cases o with
  | byte k => simp [Op.kind, Op.bytes, Kind.member, ByteSet.contains, ByteSet.members]
  | word v => exact isWord_encode 247 v (by norm_num) (W_bound v h)
  | count n => exact isWord_encode 247 n (by norm_num) (W_bound n h)
  | words vs =>
    simp only [Op.kind, Op.bytes, Kind.member, Ws]
    rw [splitWords?_encode 247 (by norm_num) vs (fun v hv => W_bound v (h v hv))]
    rfl
  | raw bs => rfl

theorem bytesOf_leaf (o : Op) (h : o.Ok) : bytesOf (strOf o.bytes) = o.bytes :=
  bytesOf_strOf o.bytes (o.bytes_lt h)

/-- A leaf of a row is a token of its sort. -/
theorem inSort_leaf (c : String) (o : Op) (hk : profile.kindOf? c = some o.kind) (h : o.Ok) :
    G.inSort c (strOf o.bytes) = true := by
  show profile.inSort c (strOf o.bytes) = true
  simp only [Profile.inSort, bytesOf_leaf o h, hk, profile_inline, o.member h, Bool.and_true]
  simpa using o.bytes_lt h

/-! ## A flat row prints back to its leaves -/

theorem printItems_leaves (ops : List (String × Op))
    (hops : ∀ q ∈ ops, profile.kindOf? q.1 = some q.2.kind ∧ G.tokenSorts.contains q.1 = true)
    (hb : ∀ q ∈ ops, q.2.Ok) :
    printItems G (ops.map fun q => Sym.tok q.1) (ops.map leafOf) =
      some (ops.map fun q => strOf q.2.bytes) := by
  induction ops with
  | nil => exact printItems_nil G
  | cons q ops ih =>
    have hq := hops q List.mem_cons_self
    have htail := ih (fun q' h' => hops q' (List.mem_cons_of_mem _ h'))
      (fun q' h' => hb q' (List.mem_cons_of_mem _ h'))
    show printItems G (Sym.tok q.1 :: ops.map fun q => Sym.tok q.1)
        (Tree.leaf q.1 (strOf q.2.bytes) :: ops.map leafOf) =
      some (strOf q.2.bytes :: ops.map fun q => strOf q.2.bytes)
    rw [printItems_tok G q.1 (strOf q.2.bytes) _ _ hq.2
      (inSort_leaf q.1 q.2 hq.1 (hb q List.mem_cons_self)), htail]
    rfl

/-- The counts of a flat row's leaves hold when the row's counts do. -/
theorem countsKids_leaves (ops : List (String × Op))
    (hops : ∀ q ∈ ops, profile.kindOf? q.1 = some q.2.kind) (hb : ∀ q ∈ ops, q.2.Ok) :
    ∀ reg, countsOK reg (ops.map Prod.snd) = true → countsKids profile reg (ops.map leafOf) = true := by
  induction ops with
  | nil => intro _ _; simp [countsKids]
  | cons q ops ih =>
    intro reg hc
    have hk := hops q List.mem_cons_self
    have hq := hb q List.mem_cons_self
    have ih' := ih (fun q' h' => hops q' (List.mem_cons_of_mem _ h'))
      (fun q' h' => hb q' (List.mem_cons_of_mem _ h'))
    obtain ⟨c, o⟩ := q
    simp only [List.map_cons, leafOf] at hc ⊢
    cases o with
    | byte k =>
      simp only [Op.kind] at hk
      simp only [countsKids, hk]
      exact ih' reg (by simpa [countsOK] using hc)
    | word v =>
      simp only [Op.kind] at hk
      simp only [countsKids, hk]
      exact ih' reg (by simpa [countsOK] using hc)
    | count n =>
      simp only [Op.kind] at hk
      simp only [countsKids, hk, bytesOf_leaf (.count n) hq]
      simp only [Op.bytes, W, wordValue_encode]
      exact ih' (some n) (by simpa [countsOK] using hc)
    | words vs =>
      simp only [Op.kind] at hk
      simp only [countsOK, Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨rfl, hc⟩ := hc
      simp only [countsKids, hk, bytesOf_leaf (.words vs) hq]
      simp only [Op.bytes, Ws, profile_inline]
      rw [splitWords?_encode 247 (by norm_num) vs (fun v hv => W_bound v (hq v hv))]
      simp only [Option.isSome_some, Option.map_some, beq_self_eq_true, Bool.and_self,
        Bool.true_and]
      exact ih' _ hc
    | raw bs =>
      simp only [Op.kind] at hk
      simp only [countsOK, Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨rfl, hc⟩ := hc
      simp only [countsKids, hk, bytesOf_leaf (.raw bs) hq]
      simp only [Op.bytes, Option.isSome_some, beq_self_eq_true, Bool.and_self, Bool.true_and]
      exact ih' _ hc

theorem joinBytes_leaves (ops : List (String × Op)) (hb : ∀ q ∈ ops, q.2.Ok) :
    joinBytes (ops.map fun q => strOf q.2.bytes) = ops.flatMap fun q => q.2.bytes := by
  induction ops with
  | nil => rfl
  | cons q ops ih =>
    simp only [List.map_cons, joinBytes, List.flatMap_cons] at ih ⊢
    rw [bytesOf_leaf q.2 (hb q List.mem_cons_self), ih (fun q' h' => hb q' (List.mem_cons_of_mem _ h'))]

/-! ## Completeness: Vibe's encoding of an instruction is read as that instruction -/

/-- The binary check accepts Vibe's encoding of every instruction within Vibe's bounds, with the
instruction's own tree, at the instruction's sort. -/
theorem Instr.reads (i : Instr) (hb : i.Bounded) : readB G profile i.sort i.encode i.tree = true := by
  obtain ⟨hprod, hleaves⟩ := shapes_ok i.shape i.shape_mem
  have hops : ∀ q ∈ i.ops, profile.kindOf? q.1 = some q.2.kind ∧ G.tokenSorts.contains q.1 = true := by
    intro q hq
    exact hleaves (q.1, q.2.kind) (List.mem_map.mpr ⟨q, hq, rfl⟩)
  have hrhs : (i.shape.2.2.map fun q => Sym.tok q.1) = i.ops.map fun q => Sym.tok q.1 := by
    simp [Instr.shape]
  simp only [Instr.shape] at hprod hrhs
  rw [hrhs] at hprod
  unfold readB Instr.tree
  rw [printTree_node G i.label (i.ops.map leafOf) _ hprod, printItems_leaves i.ops hops hb]
  simp only [Option.map_some, beq_self_eq_true, Bool.true_and, Bool.and_eq_true, beq_iff_eq]
  refine ⟨?_, ?_⟩
  · rw [joinBytes_leaves i.ops hb, Instr.encode_ops]
  · exact countsKids_leaves i.ops (fun q hq => (hops q hq).1) hb none i.counts_ok

/-! ## Files -/

/-- A file's kind: before `--proofs` (setup) or after it (proof). -/
inductive Role where
  | setup
  | proof
  deriving DecidableEq, Repr

def Role.fileSort : Role → String
  | .setup => "setup_file"
  | .proof => "proof_file"

/-- The row of the file spine that holds an instruction of a sort, in a file of a role. -/
def spineLabel : Role → String → Option String
  | .setup, "instr" => some "setup_common"
  | .setup, "setup_instr" => some "setup_only"
  | .proof, "instr" => some "proof_common"
  | .proof, "proof_instr" => some "proof_only"
  | _, _ => none

def Role.endLabel : Role → String
  | .setup => "setup_end"
  | .proof => "proof_end"

/-- An instruction may stand in a file of the role (check.c's stage rules). -/
def Role.allows (r : Role) (i : Instr) : Bool := (spineLabel r i.sort).isSome

/-- The tree of a file: the instructions on the right-recursive spine of the role's rows. -/
def fileTree (r : Role) : List Instr → Tree
  | [] => .node r.endLabel []
  | i :: is => .node ((spineLabel r i.sort).getD "") [i.tree, fileTree r is]

def encodeFile (is : List Instr) : List Nat := is.flatMap Instr.encode

theorem spine_rows : ∀ r ∈ [Role.setup, Role.proof], ∀ s ∈ ["instr", "setup_instr", "proof_instr"],
    ∀ l, spineLabel r s = some l → G.prodOf? l = some ⟨l, r.fileSort, [.nt s, .nt r.fileSort]⟩ := by
  decide +kernel

theorem end_rows : ∀ r ∈ [Role.setup, Role.proof], G.prodOf? r.endLabel = some ⟨r.endLabel, r.fileSort, []⟩ := by
  decide +kernel

theorem Instr.sort_mem (i : Instr) : i.sort ∈ ["instr", "setup_instr", "proof_instr"] := by
  cases i <;> simp [Instr.sort, Instr.row]

theorem Instr.counts_tree (i : Instr) (hb : i.Bounded) : BinaryTokens.countsTree profile i.tree = true := by
  obtain ⟨-, hleaves⟩ := shapes_ok i.shape i.shape_mem
  have hops : ∀ q ∈ i.ops, profile.kindOf? q.1 = some q.2.kind := by
    intro q hq
    exact (hleaves (q.1, q.2.kind) (List.mem_map.mpr ⟨q, hq, rfl⟩)).1
  simp only [Instr.tree, BinaryTokens.countsTree]
  exact countsKids_leaves i.ops hops hb none i.counts_ok

theorem Instr.prints (i : Instr) (hb : i.Bounded) :
    printTree G i.tree = some (i.sort, i.ops.map fun q => strOf q.2.bytes) := by
  obtain ⟨hprod, hleaves⟩ := shapes_ok i.shape i.shape_mem
  have hops : ∀ q ∈ i.ops, profile.kindOf? q.1 = some q.2.kind ∧ G.tokenSorts.contains q.1 = true := by
    intro q hq
    exact hleaves (q.1, q.2.kind) (List.mem_map.mpr ⟨q, hq, rfl⟩)
  have hrhs : (i.shape.2.2.map fun q => Sym.tok q.1) = i.ops.map fun q => Sym.tok q.1 := by
    simp [Instr.shape]
  simp only [Instr.shape] at hprod hrhs
  rw [hrhs] at hprod
  unfold Instr.tree
  rw [printTree_node G i.label (i.ops.map leafOf) _ hprod, printItems_leaves i.ops hops hb]
  rfl

/-- The tokens a file's tree prints. -/
def fileToks (is : List Instr) : List String := is.flatMap fun i => i.ops.map fun q => strOf q.2.bytes

theorem fileTree_prints (r : Role) :
    ∀ (is : List Instr), (∀ i ∈ is, i.Bounded ∧ r.allows i = true) →
      printTree G (fileTree r is) = some (r.fileSort, fileToks is)
  | [], _ => by
    have h := end_rows r (by cases r <;> simp)
    simp only [fileTree, fileToks, List.flatMap_nil]
    rw [printTree_node G r.endLabel [] _ h, printItems_nil]
    rfl
  | i :: is, h => by
    obtain ⟨hb, ha⟩ := h i List.mem_cons_self
    obtain ⟨l, hl⟩ := Option.isSome_iff_exists.mp ha
    have hrow := spine_rows r (by cases r <;> simp) i.sort i.sort_mem l hl
    have ih := fileTree_prints r is (fun j hj => h j (List.mem_cons_of_mem _ hj))
    simp only [fileTree, hl, Option.getD_some]
    rw [printTree_node G l _ _ hrow]
    obtain ⟨ilb, iks, hit⟩ : ∃ ilb iks, i.tree = .node ilb iks := ⟨_, _, rfl⟩
    obtain ⟨flb, fks, hft⟩ : ∃ flb fks, fileTree r is = .node flb fks := by
      cases is with
      | nil => exact ⟨_, _, rfl⟩
      | cons j js => exact ⟨_, _, rfl⟩
    have hpi := i.prints hb
    rw [hit] at hpi
    rw [hft] at ih
    rw [hit, hft, Megalodon.Record.printItems_nt G i.sort _ ilb iks _ _ hpi,
      Megalodon.Record.printItems_nt G r.fileSort _ flb fks _ _ ih, printItems_nil]
    simp [fileToks]

theorem fileTree_counts (r : Role) :
    ∀ (is : List Instr), (∀ i ∈ is, i.Bounded) → BinaryTokens.countsTree profile (fileTree r is) = true
  | [], _ => by simp [fileTree, BinaryTokens.countsTree, countsKids]
  | i :: is, h => by
    have hi := i.counts_tree (h i List.mem_cons_self)
    have ih := fileTree_counts r is (fun j hj => h j (List.mem_cons_of_mem _ hj))
    obtain ⟨ilb, iks, hit⟩ : ∃ ilb iks, i.tree = .node ilb iks := ⟨_, _, rfl⟩
    obtain ⟨flb, fks, hft⟩ : ∃ flb fks, fileTree r is = .node flb fks := by
      cases is with
      | nil => exact ⟨_, _, rfl⟩
      | cons j js => exact ⟨_, _, rfl⟩
    rw [hit] at hi
    rw [hft] at ih
    simp only [fileTree]
    rw [hit, hft]
    simp only [BinaryTokens.countsTree, countsKids] at hi ih ⊢
    simp [hi, ih]

theorem joinBytes_fileToks (is : List Instr) (hb : ∀ i ∈ is, i.Bounded) :
    joinBytes (fileToks is) = encodeFile is := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    have h1 := joinBytes_leaves i.ops (hb i List.mem_cons_self)
    simp only [fileToks, List.flatMap_cons, encodeFile] at ih ⊢
    simp only [joinBytes, List.flatMap_append] at ih h1 ⊢
    rw [h1, ih (fun j hj => hb j (List.mem_cons_of_mem _ hj)), ← Instr.encode_ops]

/-- The binary check accepts Vibe's encoding of every file whose instructions are within Vibe's
bounds and allowed in the file's role, with the file's own tree. -/
theorem File.reads (r : Role) (is : List Instr) (h : ∀ i ∈ is, i.Bounded ∧ r.allows i = true) :
    readB G profile r.fileSort (encodeFile is) (fileTree r is) = true := by
  unfold readB
  rw [fileTree_prints r is h]
  simp only [beq_self_eq_true, Bool.true_and, Bool.and_eq_true, beq_iff_eq]
  exact ⟨joinBytes_fileToks is (fun i hi => (h i hi).1), fileTree_counts r is (fun i hi => (h i hi).1)⟩

end Mettapedia.GSLT.Readers.Vibe.Record
