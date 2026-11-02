import Mettapedia.GSLT.Readers.Vibe.Record

/-!
# Vibe's encoding of an instruction, or of a file, has exactly one reading

`Record.lean` proves that the binary check accepts Vibe's encoding of every instruction and file
with its own tree. This file proves that it is the only tree: a checked tree at an instruction sort
whose bytes, followed by anything, are Vibe's encoding of an instruction followed by anything, is that
instruction's tree, covers exactly its bytes, and has its sort (`Instr.reading_unique`); and a checked
tree of a whole file of a role is the file's tree (`File.reading_is_tree`). So the tree an engine
returns for Vibe's own output, once checked, is the object Vibe encoded, whatever the untrusted parse
and the untrusted scanner did.

The argument: every row at an instruction sort is flat and begins with a one-byte opcode sort, and no
two rows share an opcode (`rows_are_shapes`, `shapes_opcode`, `shapes_by_opcode`); a checked tree's
leaves are a valid reading of its row (`rowValid_of_tree`), and so are the leaves of Vibe's encoding
(`rowValid_of_ops`); the scanner reads a row as a function (`BinaryTokens.row_unique`).
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
open Mettapedia.GSLT.Readers.Megalodon.Record (prodOf_mem printTree_node_inv printTree_leaf_inv
  printItems_nil_inv printItems_tok_inv printItems_nt_inv)

/-! ## Facts about the rows, decided -/

def instrSorts : List String := ["instr", "setup_instr", "proof_instr"]

/-- Every row at an instruction sort is one of the 27 shapes. -/
theorem rows_are_shapes : ∀ p ∈ G.prods, p.lhs ∈ instrSorts →
    ∃ sh ∈ shapes, p.label = sh.1 ∧ p.lhs = sh.2.1 ∧ p.rhs = sh.2.2.map fun q => Sym.tok q.1 := by
  decide +kernel

/-- The opcode a shape begins with. -/
def shapeOpcode (sh : String × String × List (String × Kind)) : Option Nat :=
  match sh.2.2 with
  | (_, .byte (.points [k])) :: _ => some k
  | _ => none

theorem shapes_have_opcode : ∀ sh ∈ shapes, (shapeOpcode sh).isSome = true := by
  decide +kernel

theorem shapeOpcode_spec (sh : String × String × List (String × Kind)) (k : Nat)
    (h : shapeOpcode sh = some k) : ∃ c rest, sh.2.2 = (c, .byte (.points [k])) :: rest := by
  unfold shapeOpcode at h
  split at h
  · rename_i c k' rest heq
    simp only [Option.some.injEq] at h
    subst h
    exact ⟨c, rest, heq⟩
  · simp at h

theorem shapes_opcode (sh : String × String × List (String × Kind)) (hsh : sh ∈ shapes) :
    ∃ c k rest, sh.2.2 = (c, .byte (.points [k])) :: rest := by
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp (shapes_have_opcode sh hsh)
  obtain ⟨c, rest, h⟩ := shapeOpcode_spec sh k hk
  exact ⟨c, k, rest, h⟩

theorem shapes_by_opcode : ∀ sh1 ∈ shapes, ∀ sh2 ∈ shapes, shapeOpcode sh1 = shapeOpcode sh2 →
    sh1 = sh2 := by
  decide +kernel

theorem instrSorts_not_tokens : ∀ s ∈ instrSorts, G.tokenSorts.contains s = false := by
  decide +kernel

theorem Instr.encode_head (i : Instr) : i.encode.head? = shapeOpcode i.shape := by
  cases i <;> rfl

theorem Instr.sort_instr (i : Instr) : i.sort ∈ instrSorts := by
  cases i <;> simp [Instr.sort, Instr.row, instrSorts]

/-! ## Strings and bytes -/

theorem strOf_bytesOf (x : String) : strOf (bytesOf x) = x := by
  simp only [strOf, bytesOf, List.map_map]
  have : (Char.ofNat ∘ Char.toNat) = id := by funext c; exact Char.ofNat_toNat c
  rw [this, List.map_id, String.ofList_toList]

/-! ## A flat row's printing, inverted -/

/-- A flat row's items print back exactly when the children are leaves of the row's token sorts,
in order, each a token of its sort. -/
theorem printItems_flat_inv (cs : List String) :
    ∀ (kids : List Tree) (toks : List String), printItems G (cs.map Sym.tok) kids = some toks →
      ∃ ps : List (String × String), ps.map Prod.fst = cs ∧ kids = ps.map (fun p => .leaf p.1 p.2) ∧
        toks = ps.map Prod.snd ∧ ∀ p ∈ ps, G.inSort p.1 p.2 = true := by
  induction cs with
  | nil =>
    intro kids toks h
    obtain ⟨rfl, rfl⟩ := printItems_nil_inv G kids toks h
    exact ⟨[], rfl, rfl, rfl, by simp⟩
  | cons c cs ih =>
    intro kids toks h
    obtain ⟨x, kids', u', rfl, hx, h', rfl⟩ := printItems_tok_inv G c _ kids toks h
    obtain ⟨ps, hps, rfl, rfl, hin⟩ := ih kids' u' h'
    refine ⟨(c, x) :: ps, by simp [hps], rfl, rfl, ?_⟩
    intro p hp
    simp only [List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact hx
    · exact hin p hp

/-! ## Valid readings of a row -/

/-- The kind of a token sort (bytes when the profile declares none; a token of such a sort is never
in its sort). -/
def kindD (c : String) : Kind := (profile.kindOf? c).getD .bytes

theorem kindOf_of_inSort (c x : String) (h : G.inSort c x = true) :
    profile.kindOf? c = some (kindD c) := by
  have h' : profile.inSort c x = true := h
  unfold Profile.inSort at h'
  cases hk : profile.kindOf? c with
  | none => simp [hk] at h'
  | some k => simp [kindD, hk]

/-- The leaves of a checked flat node are a valid reading of its row. -/
theorem rowValid_of_leaves : ∀ (ps : List (String × String)) (reg : Option Nat),
    (∀ p ∈ ps, G.inSort p.1 p.2 = true) →
    countsKids profile reg (ps.map fun p => .leaf p.1 p.2) = true →
    rowValid 247 reg (ps.map fun p => kindD p.1) (ps.map fun p => bytesOf p.2) = true
  | [], _, _, _ => by simp [rowValid]
  | (c, x) :: ps, reg, hin, hc => by
    have hcx := hin (c, x) List.mem_cons_self
    have hk := kindOf_of_inSort c x hcx
    have hrest : ∀ p ∈ ps, G.inSort p.1 p.2 = true := fun p hp => hin p (List.mem_cons_of_mem _ hp)
    have hmem : (kindD c).member 247 (bytesOf x) = true := by
      have h' : profile.inSort c x = true := hcx
      simp only [Profile.inSort, hk, profile_inline, Bool.and_eq_true] at h'
      exact h'.2
    simp only [List.map_cons, rowValid, Bool.and_eq_true]
    simp only [List.map_cons] at hc
    generalize hkd : kindD c = k at hk hmem
    cases k with
    | byte set =>
      simp only [countsKids, hk] at hc
      exact ⟨hmem, rowValid_of_leaves ps reg hrest hc⟩
    | word =>
      simp only [countsKids, hk] at hc
      exact ⟨hmem, rowValid_of_leaves ps reg hrest hc⟩
    | count =>
      simp only [countsKids, hk] at hc
      exact ⟨hmem, rowValid_of_leaves ps _ hrest hc⟩
    | words =>
      simp only [countsKids, hk, profile_inline, Bool.and_eq_true] at hc
      obtain ⟨hw, hc⟩ := hc
      refine ⟨?_, rowValid_of_leaves ps reg hrest hc⟩
      simpa [tokValid] using hw
    | bytes =>
      simp only [countsKids, hk, Bool.and_eq_true] at hc
      obtain ⟨hw, hc⟩ := hc
      refine ⟨?_, rowValid_of_leaves ps reg hrest hc⟩
      simpa [tokValid] using hw

/-- Vibe's encoding of a row is a valid reading of it. -/
theorem rowValid_of_ops : ∀ (ops : List Op) (reg : Option Nat), (∀ o ∈ ops, o.Ok) →
    countsOK reg ops = true → rowValid 247 reg (ops.map Op.kind) (ops.map Op.bytes) = true
  | [], _, _, _ => by simp [rowValid]
  | o :: ops, reg, hb, hc => by
    have ho := hb o List.mem_cons_self
    have hb' : ∀ o' ∈ ops, o'.Ok := fun o' h' => hb o' (List.mem_cons_of_mem _ h')
    have hm := o.member ho
    simp only [List.map_cons, rowValid, Bool.and_eq_true]
    cases o with
    | byte k =>
      exact ⟨hm, rowValid_of_ops ops reg hb' (by simpa [countsOK] using hc)⟩
    | word v =>
      exact ⟨hm, rowValid_of_ops ops reg hb' (by simpa [countsOK] using hc)⟩
    | count n =>
      refine ⟨hm, ?_⟩
      simp only [Op.kind, Op.bytes, Kind.nextReg, W, wordValue_encode]
      exact rowValid_of_ops ops (some n) hb' (by simpa [countsOK] using hc)
    | words vs =>
      simp only [countsOK, Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨rfl, hc⟩ := hc
      refine ⟨?_, rowValid_of_ops ops _ hb' hc⟩
      simp only [tokValid, Op.kind, Op.bytes, Ws]
      rw [splitWords?_encode 247 (by norm_num) vs (fun v hv => W_bound v (ho v hv))]
      simp
    | raw bs =>
      simp only [countsOK, Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨rfl, hc⟩ := hc
      exact ⟨by simp [tokValid, Op.kind, Op.bytes], rowValid_of_ops ops _ hb' hc⟩

/-! ## Unique reading of an instruction -/

/-- The first token of a valid reading of a row that begins with a one-byte sort is that byte. -/
theorem rowValid_head (k : Nat) (ks : List Kind) (reg : Option Nat) (toks : List (List Nat))
    (hks : ks.head? = some (.byte (.points [k]))) (h : rowValid 247 reg ks toks = true) :
    toks.flatten.head? = some k := by
  cases ks with
  | nil => simp at hks
  | cons c rest =>
    simp only [List.head?_cons, Option.some.injEq] at hks
    subst hks
    cases toks with
    | nil => simp [rowValid] at h
    | cons tok toks =>
      simp only [rowValid, Bool.and_eq_true] at h
      obtain ⟨ht, -⟩ := h
      cases tok with
      | nil => simp [tokValid, Kind.member] at ht
      | cons b bs =>
        cases bs with
        | nil =>
          simp [tokValid, Kind.member, ByteSet.contains, ByteSet.members] at ht
          simp [ht]
        | cons _ _ => simp [tokValid, Kind.member] at ht

theorem joinBytes_pairs (ps : List (String × String)) :
    joinBytes (ps.map Prod.snd) = (ps.map fun p => bytesOf p.2).flatten := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [List.map_cons, joinBytes, List.flatMap_cons, List.flatten_cons] at ih ⊢; rw [ih]

theorem flatMap_ops (qs : List (String × Op)) :
    qs.flatMap (fun q => q.2.bytes) = ((qs.map Prod.snd).map Op.bytes).flatten := by
  induction qs with
  | nil => rfl
  | cons q qs ih => simp only [List.flatMap_cons, List.map_cons, List.flatten_cons, ih]

theorem leaves_eq : ∀ (ps : List (String × String)) (qs : List (String × Op)),
    ps.map Prod.fst = qs.map Prod.fst →
    ps.map (fun p => bytesOf p.2) = (qs.map Prod.snd).map Op.bytes →
    ps.map (fun p => Tree.leaf p.1 p.2) = qs.map leafOf
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | p :: ps, q :: qs, h1, h2 => by
    simp only [List.map_cons, List.cons.injEq] at h1 h2 ⊢
    refine ⟨?_, leaves_eq ps qs h1.2 h2.2⟩
    simp only [leafOf, h1.1]
    rw [← h2.1, strOf_bytesOf]

/-- **Unique reading.** A checked tree at an instruction sort whose bytes, followed by anything, are
Vibe's encoding of an instruction followed by anything, is that instruction's tree, at its sort, and
covers exactly its bytes. -/
theorem Instr.reading_unique (i : Instr) (hb : i.Bounded) (s : String) (hs : s ∈ instrSorts)
    (t : Tree) (bs r r' : List Nat) (h : readB G profile s bs t = true)
    (he : bs ++ r = i.encode ++ r') : t = i.tree ∧ s = i.sort ∧ bs = i.encode ∧ r = r' := by
  obtain ⟨toks, hd, hj, hc⟩ := (readB_iff s bs t).mp h
  have hp := (printTree_iff G wellFormed t s toks).mpr hd
  cases t with
  | leaf c x =>
    obtain ⟨rfl, hcs⟩ := printTree_leaf_inv G c x s toks hp
    rw [instrSorts_not_tokens s hs] at hcs
    cases hcs
  | node l kids =>
    obtain ⟨p, hq, hl, hi⟩ := printTree_node_inv G l kids s toks hp
    obtain ⟨hmem, hlab⟩ := prodOf_mem G l p hq
    obtain ⟨sh, hsh, hshl, hshs, hshr⟩ := rows_are_shapes p hmem (by rw [hl]; exact hs)
    rw [hshr] at hi
    have hi' : printItems G ((sh.2.2.map Prod.fst).map Sym.tok) kids = some toks := by
      rw [List.map_map]; exact hi
    obtain ⟨ps, hps, rfl, rfl, hin⟩ := printItems_flat_inv (sh.2.2.map Prod.fst) kids _ hi'
    obtain ⟨-, hkinds⟩ := shapes_ok sh hsh
    have hcounts : countsKids profile none (ps.map fun p => .leaf p.1 p.2) = true := by
      simpa [BinaryTokens.countsTree] using hc
    have hvalid := rowValid_of_leaves ps none hin hcounts
    -- the kinds of the leaves are the shape's
    have hkd : (ps.map fun p => kindD p.1) = sh.2.2.map Prod.snd := by
      have e : (ps.map fun p => kindD p.1) = (ps.map Prod.fst).map kindD := by simp
      rw [e, hps, List.map_map]
      apply List.map_congr_left
      intro q hq
      have := (hkinds q hq).1
      simp [kindD, this]
    rw [hkd] at hvalid
    -- the opcode decides the shape
    obtain ⟨c0, k0, rest0, hsh0⟩ := shapes_opcode sh hsh
    have hhead : (ps.map fun p => bytesOf p.2).flatten.head? = some k0 :=
      rowValid_head k0 _ none _ (by rw [hsh0]; rfl) hvalid
    have hbs : bs = (ps.map fun p => bytesOf p.2).flatten := by rw [← hj, joinBytes_pairs]
    have henc : i.encode = ((i.ops.map Prod.snd).map Op.bytes).flatten := by
      rw [Instr.encode_ops, flatMap_ops]
    have hop : shapeOpcode sh = shapeOpcode i.shape := by
      rw [← Instr.encode_head]
      obtain ⟨c1, k1, r1, hr1⟩ := shapes_opcode i.shape i.shape_mem
      have hih : i.encode.head? = some k1 := by
        rw [Instr.encode_head]; simp [shapeOpcode, hr1]
      have h1 : (bs ++ r).head? = some k0 := by
        rw [hbs, List.head?_append, hhead]; rfl
      have h2 : (i.encode ++ r').head? = some k1 := by
        rw [List.head?_append, hih]; rfl
      rw [he, h2] at h1
      rw [hih, h1]
      simp [shapeOpcode, hsh0]
    have hsheq := shapes_by_opcode sh hsh i.shape i.shape_mem hop
    subst hsheq
    have hkinds_eq : (i.shape.2.2.map Prod.snd) = (i.ops.map Prod.snd).map Op.kind := by
      simp [Instr.shape]
    rw [hkinds_eq] at hvalid
    have hivalid := rowValid_of_ops (i.ops.map Prod.snd) none (fun o ho => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ho; exact hb q hq) i.counts_ok
    rw [hbs, henc] at he
    obtain ⟨hpb, hr⟩ := row_unique 247 _ none _ _ r r' hvalid hivalid he
    have hfst : ps.map Prod.fst = i.ops.map Prod.fst := by rw [hps]; simp [Instr.shape]
    refine ⟨?_, ?_, ?_, hr⟩
    · have hl' : l = i.label := by rw [← hlab, hshl]; rfl
      rw [hl']
      simp only [Instr.tree]
      rw [leaves_eq ps i.ops hfst hpb]
    · rw [← hl, hshs]; rfl
    · rw [hbs, henc, hpb]

/-- The tree an engine returns for Vibe's encoding of an instruction, once checked at the
instruction's sort, is that instruction's tree. -/
theorem Instr.reading_is_tree (i : Instr) (hb : i.Bounded) (t : Tree)
    (h : readB G profile i.sort i.encode t = true) : t = i.tree :=
  (i.reading_unique hb i.sort i.sort_instr t i.encode [] [] h rfl).1

/-- What a checked tree at an instruction sort is: a row's label over leaves whose bytes are a valid
reading of the row. -/
theorem instr_reading_shape (s : String) (hs : s ∈ instrSorts) (t : Tree) (bs : List Nat)
    (h : readB G profile s bs t = true) :
    ∃ sh ∈ shapes, ∃ ps : List (String × String),
      t = .node sh.1 (ps.map fun p => .leaf p.1 p.2) ∧ s = sh.2.1 ∧
      bs = (ps.map fun p => bytesOf p.2).flatten ∧
      rowValid 247 none (sh.2.2.map Prod.snd) (ps.map fun p => bytesOf p.2) = true := by
  obtain ⟨toks, hd, hj, hc⟩ := (readB_iff s bs t).mp h
  have hp := (printTree_iff G wellFormed t s toks).mpr hd
  cases t with
  | leaf c x =>
    obtain ⟨rfl, hcs⟩ := printTree_leaf_inv G c x s toks hp
    rw [instrSorts_not_tokens s hs] at hcs
    cases hcs
  | node l kids =>
    obtain ⟨p, hq, hl, hi⟩ := printTree_node_inv G l kids s toks hp
    obtain ⟨hmem, hlab⟩ := prodOf_mem G l p hq
    obtain ⟨sh, hsh, hshl, hshs, hshr⟩ := rows_are_shapes p hmem (by rw [hl]; exact hs)
    rw [hshr] at hi
    have hi' : printItems G ((sh.2.2.map Prod.fst).map Sym.tok) kids = some toks := by
      rw [List.map_map]; exact hi
    obtain ⟨ps, hps, rfl, rfl, hin⟩ := printItems_flat_inv (sh.2.2.map Prod.fst) kids _ hi'
    obtain ⟨-, hkinds⟩ := shapes_ok sh hsh
    have hcounts : countsKids profile none (ps.map fun p => .leaf p.1 p.2) = true := by
      simpa [BinaryTokens.countsTree] using hc
    have hvalid := rowValid_of_leaves ps none hin hcounts
    have hkd : (ps.map fun p => kindD p.1) = sh.2.2.map Prod.snd := by
      have e : (ps.map fun p => kindD p.1) = (ps.map Prod.fst).map kindD := by simp
      rw [e, hps, List.map_map]
      apply List.map_congr_left
      intro q hq
      have := (hkinds q hq).1
      simp [kindD, this]
    rw [hkd] at hvalid
    refine ⟨sh, hsh, ps, ?_, by rw [← hl, hshs], by rw [← hj, joinBytes_pairs], hvalid⟩
    rw [← hlab, hshl]

/-- A checked tree at an instruction sort covers at least one byte (its opcode). -/
theorem instr_reading_nonempty (s : String) (hs : s ∈ instrSorts) (t : Tree) (bs : List Nat)
    (h : readB G profile s bs t = true) : bs ≠ [] := by
  obtain ⟨sh, hsh, ps, -, -, hbs, hvalid⟩ := instr_reading_shape s hs t bs h
  obtain ⟨c0, k0, rest0, hsh0⟩ := shapes_opcode sh hsh
  have hhead := rowValid_head k0 _ none _ (by rw [hsh0]; rfl) hvalid
  intro he
  rw [← hbs, he] at hhead
  simp at hhead

theorem Instr.encode_ne_nil (i : Instr) : i.encode ≠ [] := by
  cases i <;> simp [Instr.encode]

/-! ## Unique reading of a file -/

/-- The rows of the file sorts: the end of a file, or one instruction and the rest of the file. -/
theorem file_rows : ∀ r ∈ [Role.setup, Role.proof], ∀ p ∈ G.prods, p.lhs = r.fileSort →
    (p.label = r.endLabel ∧ p.rhs = []) ∨
      ∃ s ∈ instrSorts, spineLabel r s = some p.label ∧ p.rhs = [.nt s, .nt r.fileSort] := by
  decide +kernel

theorem fileSort_not_token (r : Role) : G.tokenSorts.contains r.fileSort = false := by
  cases r <;> decide +kernel

/-- **Unique reading of a file.** A checked tree of a whole file of a role, whose bytes are Vibe's
encoding of an instruction list, is the file tree of that list. -/
theorem File.reading_is_tree (r : Role) :
    ∀ (is : List Instr), (∀ i ∈ is, i.Bounded) →
      ∀ (t : Tree), readB G profile r.fileSort (encodeFile is) t = true → t = fileTree r is := by
  intro is
  induction is with
  | nil =>
    intro _ t h
    obtain ⟨toks, hd, hj, hc⟩ := (readB_iff _ _ t).mp h
    have hp := (printTree_iff G wellFormed t _ toks).mpr hd
    cases t with
    | leaf c x =>
      obtain ⟨hcs, htok⟩ := printTree_leaf_inv G c x _ toks hp
      rw [← hcs, fileSort_not_token] at htok
      cases htok
    | node l kids =>
      obtain ⟨p, hq, hl, hi⟩ := printTree_node_inv G l kids _ toks hp
      obtain ⟨hmem, hlab⟩ := prodOf_mem G l p hq
      rcases file_rows r (by cases r <;> simp) p hmem hl with ⟨hend, hrhs⟩ | ⟨s, hs, hsp, hrhs⟩
      · rw [hrhs] at hi
        obtain ⟨rfl, rfl⟩ := printItems_nil_inv G kids toks hi
        simp only [fileTree]
        rw [← hlab, hend]
      · rw [hrhs] at hi
        obtain ⟨k1, kids', u1, u', rfl, hk1, hi', rfl⟩ := printItems_nt_inv G s _ kids _ hi
        obtain ⟨k2, kids'', u2, u'', rfl, hk2, hi'', rfl⟩ := printItems_nt_inv G _ _ kids' _ hi'
        obtain ⟨rfl, rfl⟩ := printItems_nil_inv G kids'' u'' hi''
        -- the instruction's bytes are a prefix of the empty encoding: impossible
        have hc1 : BinaryTokens.countsTree profile k1 = true := by
          cases k1 with
          | leaf c x =>
            obtain ⟨rfl, htok⟩ := printTree_leaf_inv G c x _ _ hk1
            rw [instrSorts_not_tokens _ hs] at htok; cases htok
          | node _ _ =>
            cases k2 with
            | leaf c x =>
              obtain ⟨hcs, htok⟩ := printTree_leaf_inv G c x _ _ hk2
              rw [← hcs, fileSort_not_token] at htok; cases htok
            | node _ _ => simp_all [BinaryTokens.countsTree, countsKids]
        have hr1 : readB G profile s (joinBytes u1) k1 = true := by
          unfold readB; rw [hk1]; simp [hc1]
        have hne := instr_reading_nonempty s hs k1 _ hr1
        apply absurd hj
        simp only [joinBytes, List.append_nil, List.flatMap_append, encodeFile, List.flatMap_nil]
        intro h0
        apply hne
        simp only [joinBytes]
        exact List.eq_nil_of_append_eq_nil h0 |>.1
  | cons i is ih =>
    intro hb t h
    have hbi := hb i List.mem_cons_self
    have hbs : ∀ j ∈ is, j.Bounded := fun j hj => hb j (List.mem_cons_of_mem _ hj)
    obtain ⟨toks, hd, hj, hc⟩ := (readB_iff _ _ t).mp h
    have hp := (printTree_iff G wellFormed t _ toks).mpr hd
    cases t with
    | leaf c x =>
      obtain ⟨hcs, htok⟩ := printTree_leaf_inv G c x _ toks hp
      rw [← hcs, fileSort_not_token] at htok
      cases htok
    | node l kids =>
      obtain ⟨p, hq, hl, hi⟩ := printTree_node_inv G l kids _ toks hp
      obtain ⟨hmem, hlab⟩ := prodOf_mem G l p hq
      rcases file_rows r (by cases r <;> simp) p hmem hl with ⟨hend, hrhs⟩ | ⟨s, hs, hsp, hrhs⟩
      · rw [hrhs] at hi
        obtain ⟨rfl, rfl⟩ := printItems_nil_inv G kids toks hi
        exfalso
        have : encodeFile (i :: is) = [] := by rw [← hj]; rfl
        simp only [encodeFile, List.flatMap_cons] at this
        exact i.encode_ne_nil (List.eq_nil_of_append_eq_nil this).1
      · rw [hrhs] at hi
        obtain ⟨k1, kids', u1, u', rfl, hk1, hi', rfl⟩ := printItems_nt_inv G s _ kids _ hi
        obtain ⟨k2, kids'', u2, u'', rfl, hk2, hi'', rfl⟩ := printItems_nt_inv G _ _ kids' _ hi'
        obtain ⟨rfl, rfl⟩ := printItems_nil_inv G kids'' u'' hi''
        have hcc : BinaryTokens.countsTree profile k1 = true ∧ BinaryTokens.countsTree profile k2 = true := by
          cases k1 with
          | leaf c x =>
            obtain ⟨rfl, htok⟩ := printTree_leaf_inv G c x _ _ hk1
            rw [instrSorts_not_tokens _ hs] at htok; cases htok
          | node _ _ =>
            cases k2 with
            | leaf c x =>
              obtain ⟨hcs, htok⟩ := printTree_leaf_inv G c x _ _ hk2
              rw [← hcs, fileSort_not_token] at htok; cases htok
            | node _ _ => simp_all [BinaryTokens.countsTree, countsKids]
        have hr1 : readB G profile s (joinBytes u1) k1 = true := by
          unfold readB; rw [hk1]; simp [hcc.1]
        have hr2 : readB G profile r.fileSort (joinBytes u2) k2 = true := by
          unfold readB; rw [hk2]; simp [hcc.2]
        have hsplit : joinBytes u1 ++ joinBytes u2 = i.encode ++ encodeFile is := by
          have e : joinBytes (u1 ++ (u2 ++ [])) = joinBytes u1 ++ joinBytes u2 := by
            simp [joinBytes, List.flatMap_append]
          rw [← e, hj]
          simp [encodeFile]
        obtain ⟨ht1, hs1, -, hrest⟩ :=
          i.reading_unique hbi s hs k1 (joinBytes u1) (joinBytes u2) (encodeFile is) hr1 hsplit
        rw [hrest] at hr2
        have ht2 := ih hbs k2 hr2
        subst ht1; subst ht2; subst hs1
        simp only [fileTree]
        congr
        rw [← hlab, hsp]; rfl

end Mettapedia.GSLT.Readers.Vibe.Record
