import MeTTailCore.MeTTaIL.Syntax
import MeTTailCore.MeTTaSyntax.Spec

/-! # Source Syntax ↔ Core Round-Trip

Defines `SExpr` (the parsed S-expression AST), encoding/decoding functions
parameterized by `AtomEncodingSpec`, and round-trip correctness proofs for
the syntax-representable subset.

The key property: `decode spec (encode spec sexpr) = some sexpr` for
well-formed source-syntax atoms.
-/

namespace MeTTailCore.MeTTaSyntax

open MeTTailCore.MeTTaIL.Syntax (Pattern)

-- ═══════════════════════════════════════════════════════════════════════
-- Source S-expression AST
-- ═══════════════════════════════════════════════════════════════════════

/-- Parsed S-expression, before lowering to core runtime terms. -/
inductive SExpr where
  | atom : String → SExpr
  | list : List SExpr → SExpr
deriving Repr, BEq

-- DecidableEq requires manual instance for recursive inductive
mutual
private def decEqSExpr : (a b : SExpr) → Decidable (a = b)
  | .atom s₁, .atom s₂ =>
    if h : s₁ = s₂ then isTrue (by subst h; rfl)
    else isFalse (by intro h'; cases h'; exact h rfl)
  | .list l₁, .list l₂ =>
    match decEqSExprList l₁ l₂ with
    | isTrue h => isTrue (by subst h; rfl)
    | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
  | .atom _, .list _ => isFalse (by intro h; cases h)
  | .list _, .atom _ => isFalse (by intro h; cases h)

private def decEqSExprList : (a b : List SExpr) → Decidable (a = b)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (by intro h; cases h)
  | _ :: _, [] => isFalse (by intro h; cases h)
  | a :: as, b :: bs =>
    match decEqSExpr a b, decEqSExprList as bs with
    | isTrue ha, isTrue hb => isTrue (by subst ha; subst hb; rfl)
    | isFalse ha, _ => isFalse (by intro h; cases h; exact ha rfl)
    | _, isFalse hb => isFalse (by intro h; cases h; exact hb rfl)
end

instance : DecidableEq SExpr := decEqSExpr

-- ═══════════════════════════════════════════════════════════════════════
-- Source-syntax atom classification
-- ═══════════════════════════════════════════════════════════════════════

/-- Classification of a source-syntax atom token. -/
inductive AtomKind where
  | variable : String → AtomKind
  | intLit : Int → AtomKind
  | stringLit : String → AtomKind
  | operatorAlias : String → AtomKind
  | symbol : String → AtomKind
deriving Repr, DecidableEq, BEq

/-- Classify a source-syntax atom token given the encoding spec. -/
def classifyAtom (spec : AtomEncodingSpec) (tok : String) : AtomKind :=
  -- Check operator aliases first
  match spec.operatorAliases.find? (·.sourceSymbol == tok) with
  | some alias => .operatorAlias alias.constructorLabel
  | none =>
    -- Variable?
    if tok.length > 1 && tok.toList.head? == some '$' then
      .variable (tok.drop 1).toString
    -- String literal?
    else if tok.length ≥ 2 && tok.toList.head? == some '"' && tok.back == '"' then
      .stringLit (tok.drop 1 |>.dropEnd 1).toString
    -- Integer literal?
    else match tok.toInt? with
      | some n => .intLit n
      | none => .symbol tok

-- ═══════════════════════════════════════════════════════════════════════
-- Encoding: SExpr → Pattern
-- ═══════════════════════════════════════════════════════════════════════

/-- Encode an integer as a constructor-safe token pattern. -/
def encodeIntToken (enc : IntEncoding) (n : Int) : Pattern :=
  match enc with
  | .prefixed tok neg =>
    let s := if n < 0 then tok ++ neg ++ toString (Int.natAbs n)
             else tok ++ toString (Int.natAbs n)
    .apply s []

/-- Encode a byte as two hex characters. -/
private def byteToHex (b : UInt8) : String :=
  let hexChar (n : UInt8) : Char :=
    if n < 10 then Char.ofNat (48 + n.toNat) -- '0' + n
    else Char.ofNat (87 + n.toNat) -- 'a' + (n - 10)
  String.ofList [hexChar (b / 16), hexChar (b % 16)]

/-- Encode a string's UTF-8 bytes as a hex string. -/
private def encodeHexBytes (s : String) : String :=
  s.toUTF8.foldl (fun acc b => acc ++ byteToHex b) ""

/-- Parse a single hex digit character to its numeric value. -/
private def hexVal (c : Char) : Option UInt8 :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat).toUInt8
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10).toUInt8
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10).toUInt8
  else none

/-- Decode a hex string back to a UTF-8 string. -/
private def decodeHexBytes (hex : String) : Option String :=
  let chars := hex.toList
  let rec go : List Char → List UInt8 → Option (List UInt8)
    | [], acc => some acc.reverse
    | [_], _ => none  -- odd length
    | c1 :: c2 :: rest, acc =>
      match hexVal c1, hexVal c2 with
      | some h, some l => go rest ((h * 16 + l) :: acc)
      | _, _ => none
  match go chars [] with
  | some bytes => String.fromUTF8? ⟨bytes.toArray⟩
  | none => none

/-- Encode a string as a constructor-safe token pattern. -/
def encodeStringToken (enc : StringEncoding) (s : String) : Pattern :=
  match enc with
  | .prefixed tok => .apply (tok ++ s) []
  | .hexPrefixed tok => .apply (tok ++ encodeHexBytes s) []

/-- Wrap a symbol name as a Pattern leaf. -/
def encodeSymbolName (name : String) : Pattern :=
  .apply name []

mutual
/-- Encode a source S-expression into a core Pattern. -/
def encode (spec : AtomEncodingSpec) : SExpr → Pattern
  | .atom tok =>
    match classifyAtom spec tok with
    | .operatorAlias ctor => .apply ctor []
    | .variable name =>
      if spec.variableWrapsName then
        .apply spec.variableWrapper [.apply spec.symbolWrapper [encodeSymbolName name]]
      else
        .apply spec.variableWrapper [encodeSymbolName name]
    | .intLit n => .apply spec.intWrapper [encodeIntToken spec.intEncoding n]
    | .stringLit s => .apply spec.stringWrapper [encodeStringToken spec.stringEncoding s]
    | .symbol name => .apply spec.symbolWrapper [encodeSymbolName name]
  | .list [] => .apply spec.exprNil []
  | .list (x :: xs) =>
    .apply spec.exprCons [encode spec x, encodeExprTail spec xs]
termination_by s => sizeOf s
decreasing_by all_goals simp_wf; omega

/-- Fold remaining list elements into an ExprCons/ExprNil chain. -/
def encodeExprTail (spec : AtomEncodingSpec) : List SExpr → Pattern
  | [] => .apply spec.exprNil []
  | x :: xs => .apply spec.exprCons [encode spec x, encodeExprTail spec xs]
termination_by items => sizeOf items
decreasing_by all_goals simp_wf; omega
end

-- ═══════════════════════════════════════════════════════════════════════
-- Decoding: Pattern → Option SExpr  (partial, source-syntax subset only)
-- ═══════════════════════════════════════════════════════════════════════

/-- Decode an integer token pattern back to an Int. -/
def decodeIntToken (enc : IntEncoding) (tok : String) : Option Int :=
  match enc with
  | .prefixed pre neg =>
    if tok.startsWith pre then
      let rest := (tok.drop pre.length).toString
      if rest.startsWith neg then
        ((rest.drop neg.length).toString).toNat?.map (fun n => -(n : Int))
      else
        rest.toNat?.map (fun n => (n : Int))
    else none

/-- Decode a string token pattern back to a String. -/
def decodeStringToken (enc : StringEncoding) (tok : String) : Option String :=
  match enc with
  | .prefixed pre =>
    if tok.startsWith pre then some (tok.drop pre.length).toString
    else none
  | .hexPrefixed pre =>
    if tok.startsWith pre then decodeHexBytes (tok.drop pre.length).toString
    else none

/-- Decode a core Pattern back to a source S-expression, if syntax-representable. -/
def decode (spec : AtomEncodingSpec) : Pattern → Option SExpr
  | .apply ctor [] =>
    -- Nullary operator alias?
    match spec.operatorAliases.find? (·.constructorLabel == ctor) with
    | some alias => some (.atom alias.sourceSymbol)
    | none =>
      if ctor == spec.exprNil then some (.list [])
      else none
  | .apply ctor [.apply name []] =>
    if ctor == spec.symbolWrapper then some (.atom name)
    else if ctor == spec.intWrapper then
      (decodeIntToken spec.intEncoding name).map (fun n => .atom (toString n))
    else if ctor == spec.stringWrapper then
      (decodeStringToken spec.stringEncoding name).map (fun s => .atom ("\"" ++ s ++ "\""))
    else if ctor == spec.variableWrapper && !spec.variableWrapsName then
      some (.atom ("$" ++ name))
    else none
  | .apply ctor [inner] =>
    if ctor == spec.variableWrapper && spec.variableWrapsName then
      match inner with
      | .apply sw [.apply name []] =>
        if sw == spec.symbolWrapper then some (.atom ("$" ++ name)) else none
      | _ => none
    else none
  | .apply ctor [hd, tl] =>
    if ctor == spec.exprCons then
      match decode spec hd, decodeExprCons spec tl with
      | some shd, some stl => some (.list (shd :: stl))
      | _, _ => none
    else
      match spec.sugarForms.find? (fun sf => sf.2.1 == ctor && sf.2.2 == 2) with
      | some (head, _, _) =>
        match decode spec hd, decode spec tl with
        | some s1, some s2 => some (.list [.atom head, s1, s2])
        | _, _ => none
      | none => none
  | _ => none
where
  /-- Decode a cons-list tail structurally. -/
  decodeExprCons (spec : AtomEncodingSpec) : Pattern → Option (List SExpr)
    | .apply ctor [] =>
      if ctor == spec.exprNil then some [] else none
    | .apply ctor [hd, tl] =>
      if ctor == spec.exprCons then
        match decode spec hd, decodeExprCons spec tl with
        | some shd, some stl => some (shd :: stl)
        | _, _ => none
      else none
    | _ => none

-- ═══════════════════════════════════════════════════════════════════════
-- Spec consistency
-- ═══════════════════════════════════════════════════════════════════════

/-- Spec-internal consistency conditions required for the round-trip. -/
structure SpecConsistent (spec : AtomEncodingSpec) : Prop where
  /-- All wrapper names are mutually distinct -/
  sym_ne_int : spec.symbolWrapper ≠ spec.intWrapper
  sym_ne_str : spec.symbolWrapper ≠ spec.stringWrapper
  sym_ne_var : spec.symbolWrapper ≠ spec.variableWrapper
  int_ne_str : spec.intWrapper ≠ spec.stringWrapper
  int_ne_var : spec.intWrapper ≠ spec.variableWrapper
  str_ne_var : spec.stringWrapper ≠ spec.variableWrapper
  /-- exprNil is not an operator alias constructor -/
  exprNil_not_alias : spec.operatorAliases.find?
    (·.constructorLabel == spec.exprNil) = none
  /-- Operator alias constructor labels roundtrip via find? -/
  alias_ctor_roundtrip : ∀ a ∈ spec.operatorAliases,
    spec.operatorAliases.find? (·.constructorLabel == a.constructorLabel) = some a

-- ═══════════════════════════════════════════════════════════════════════
-- Well-formedness: source-syntax atoms that roundtrip correctly
-- ═══════════════════════════════════════════════════════════════════════

/-- Extract the token string from a Pattern leaf. -/
def extractPatternLeaf : Pattern → Option String
  | .apply s [] => some s
  | _ => none

/-- A source-syntax atom is "well-formed" for encoding purposes:
    - symbols don't collide with spec constructor names
    - integer/string token representations roundtrip correctly
    - variables and operator aliases are always well-formed -/
def wellFormedAtom (spec : AtomEncodingSpec) : SExpr → Prop
  | .atom tok =>
    match classifyAtom spec tok with
    | .symbol name =>
      name ≠ spec.exprNil ∧ name ≠ spec.exprCons
      ∧ name ∉ spec.operatorAliases.map (·.constructorLabel)
    | .intLit n =>
      tok = toString n ∧
      match extractPatternLeaf (encodeIntToken spec.intEncoding n) with
      | some itok => decodeIntToken spec.intEncoding itok = some n
      | none => False
    | .stringLit s =>
      tok = "\"" ++ s ++ "\"" ∧
      match extractPatternLeaf (encodeStringToken spec.stringEncoding s) with
      | some stok => decodeStringToken spec.stringEncoding stok = some s
      | none => False
    | .variable name => tok = "$" ++ name
    | .operatorAlias _ => True
  | .list items => ∀ item ∈ items, wellFormedAtom spec item

-- ═══════════════════════════════════════════════════════════════════════
-- Round-trip proof
-- ═══════════════════════════════════════════════════════════════════════

private theorem find?_not_mem_map {l : List OperatorAlias} {name : String}
    (h : name ∉ l.map (·.constructorLabel)) :
    l.find? (·.constructorLabel == name) = none := by
  induction l with
  | nil => simp [List.find?]
  | cons hd tl ih =>
    simp only [List.map, List.mem_cons, not_or] at h
    obtain ⟨hne, hmem⟩ := h
    simp only [List.find?]
    have hbeq : (hd.constructorLabel == name) = false := by
      rw [beq_eq_false_iff_ne]; exact Ne.symm hne
    simp [hbeq, ih hmem]

private theorem decode_encodeExprTail (spec : AtomEncodingSpec)
    (_hsc : SpecConsistent spec)
    (items : List SExpr)
    (hwf : ∀ item ∈ items, wellFormedAtom spec item)
    (ih : ∀ item ∈ items, decode spec (encode spec item) = some item) :
    decode.decodeExprCons spec (encodeExprTail spec items) = some items := by
  induction items with
  | nil => simp [encodeExprTail, decode.decodeExprCons]
  | cons x xs ih_list =>
    simp [encodeExprTail, decode.decodeExprCons]
    have hx := ih x List.mem_cons_self
    have hxs := ih_list
      (fun item hmem => hwf item (List.mem_cons_of_mem x hmem))
      (fun item hmem => ih item (List.mem_cons_of_mem x hmem))
    rw [hx, hxs]

/-- Main round-trip theorem: decoding an encoded well-formed source-syntax atom
    recovers the original, given a consistent encoding spec. -/
theorem decode_encode (spec : AtomEncodingSpec)
    (hsc : SpecConsistent spec)
    (sexpr : SExpr) (hwf : wellFormedAtom spec sexpr) :
    decode spec (encode spec sexpr) = some sexpr := by
  match sexpr, hwf with
  | .atom tok, hwf =>
    simp only [encode]
    generalize hc : classifyAtom spec tok = kind
    match kind with
    | .symbol name =>
      -- encode gives .apply symbolWrapper [.apply name []]
      -- decode matches .apply ctor [.apply name' []] branch
      simp only [encodeSymbolName, decode]
      -- Need: name = tok (from classifyAtom returning .symbol tok)
      -- The decode checks symbolWrapper first → true
      -- wellFormedAtom ensures name ∉ operator alias constructors
      simp only [wellFormedAtom, hc] at hwf
      have hnt : name = tok := by
        unfold classifyAtom at hc
        split at hc
        · cases hc
        · split at hc
          · cases hc
          · split at hc
            · cases hc
            · split at hc
              · cases hc
              · exact (AtomKind.symbol.inj hc).symm
      subst hnt
      rw [if_pos (beq_self_eq_true _)]
    | .variable name =>
      simp only [wellFormedAtom, hc] at hwf
      subst hwf
      cases hv : spec.variableWrapsName
      · -- variableWrapsName = false
        simp only [hv, Bool.false_eq_true, ite_false, encodeSymbolName, decode]
        rw [if_neg (fun h => hsc.sym_ne_var.symm (beq_iff_eq.mp h))]
        rw [if_neg (fun h => hsc.int_ne_var.symm (beq_iff_eq.mp h))]
        rw [if_neg (fun h => hsc.str_ne_var.symm (beq_iff_eq.mp h))]
        simp
      · -- variableWrapsName = true
        simp only [hv, ite_true, encodeSymbolName, decode]
        simp
    | .intLit n =>
      simp only [wellFormedAtom, hc] at hwf
      obtain ⟨htok, hwf_rt⟩ := hwf
      subst htok
      match hie : spec.intEncoding with
      | .prefixed pre neg =>
        simp only [encodeIntToken, hie, decode, extractPatternLeaf] at hwf_rt ⊢
        rw [if_neg (fun h => hsc.sym_ne_int.symm (beq_iff_eq.mp h))]
        rw [if_pos (beq_self_eq_true _)]
        rw [hwf_rt]
        rfl
    | .stringLit s =>
      simp only [wellFormedAtom, hc] at hwf
      obtain ⟨htok, hwf_rt⟩ := hwf
      subst htok
      match hse : spec.stringEncoding with
      | .prefixed pre =>
        simp only [encodeStringToken, hse, decode, extractPatternLeaf] at hwf_rt ⊢
        rw [if_neg (fun h => hsc.sym_ne_str.symm (beq_iff_eq.mp h))]
        rw [if_neg (fun h => hsc.int_ne_str.symm (beq_iff_eq.mp h))]
        rw [if_pos (beq_self_eq_true _)]
        simp [hwf_rt]
      | .hexPrefixed pre =>
        simp only [encodeStringToken, hse, decode, extractPatternLeaf] at hwf_rt ⊢
        rw [if_neg (fun h => hsc.sym_ne_str.symm (beq_iff_eq.mp h))]
        rw [if_neg (fun h => hsc.int_ne_str.symm (beq_iff_eq.mp h))]
        rw [if_pos (beq_self_eq_true _)]
        simp [hwf_rt]
    | .operatorAlias ctor =>
      -- Extract alias info from classifyAtom
      have ha : ∃ alias, spec.operatorAliases.find? (·.sourceSymbol == tok) = some alias ∧
          ctor = alias.constructorLabel := by
        unfold classifyAtom at hc
        split at hc
        · rename_i alias hf
          exact ⟨alias, hf, by injection hc with h; exact h.symm⟩
        · split at hc
          · cases hc
          · split at hc
            · cases hc
            · split at hc
              · cases hc
              · cases hc
      obtain ⟨alias, hf, hctor⟩ := ha
      subst hctor
      have hmem := List.mem_of_find?_eq_some hf
      have hsurf := List.find?_some hf
      simp only [decode]
      rw [hsc.alias_ctor_roundtrip alias hmem]
      simp [beq_iff_eq.mp hsurf]
  | .list [], hwf =>
    simp only [encode, decode]
    rw [hsc.exprNil_not_alias]
    simp
  | .list (x :: xs), hwf =>
    simp only [encode, decode]
    simp only [wellFormedAtom] at hwf
    have hwf_items : ∀ item ∈ (x :: xs), wellFormedAtom spec item := hwf
    have ih_all : ∀ item ∈ (x :: xs), decode spec (encode spec item) = some item := by
      intro item hmem
      exact decode_encode spec hsc item (hwf_items item hmem)
    have hx := ih_all x List.mem_cons_self
    have htl := decode_encodeExprTail spec hsc xs
      (fun item hmem => hwf_items item (List.mem_cons_of_mem x hmem))
      (fun item hmem => ih_all item (List.mem_cons_of_mem x hmem))
    simp [hx, htl]
termination_by sizeOf sexpr
decreasing_by
  simp_wf
  have hsz := List.sizeOf_lt_of_mem hmem
  have hcons : sizeOf (x :: xs) = 1 + sizeOf x + sizeOf xs := List.cons.sizeOf_spec x xs
  omega

end MeTTailCore.MeTTaSyntax
