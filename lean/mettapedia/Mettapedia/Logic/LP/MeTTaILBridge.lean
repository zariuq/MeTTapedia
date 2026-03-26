import Mettapedia.Logic.LP.Semantics
import Mettapedia.Logic.LP.RangeRestriction
import Mettapedia.OSLF.MeTTaIL.DeclReduces
import Mettapedia.OSLF.MeTTaIL.MatchSpec
import Mettapedia.Languages.ProcessCalculi.MORK.MeTTaILBridge
import Mathlib.Data.Matrix.Basic

/-!
# LP ↔ MeTTaIL Bridge: Grounding OSLF in LP Semantics

Connects MeTTaIL's declarative reduction relation (`DeclReduces`) to the least
Herbrand model of a logic program (`LP.leastHerbrandModel`).

## Signature Design

`mettailLPSig` uses `functionSymbols := Unit` — a **single binary pairing function**.
Every `Term.app () ts` expects `ts : Fin 2 → _`, so `![a,b]` elaboration is
uniform and sidesteps variable-arity type-inference failures.

Patterns are encoded as binary pair-spine trees:
  `.fvar x     → var x`           (LP variable — clause parameterization)
  `.bvar n     → const "bv:n"`    (ground token)
  `.apply f as → pair("f_f", spine(as))`
  `.lambda b   → pair("lambda", enc(b))`
  etc.

## Fragment restriction

`morkTranslatable` (same as MORK bridge): no `.subst`, no rest-variable collections.

## Scope: lp_complete_topRule

The main theorem, `lp_complete_topRule`, covers DeclReduces.topRule steps.
Preconditions:
- `hmt_rl`, `hmt_rr`: both rule sides are morkTranslatable
- `hbs_lhs`: `applyBindings bs r.left = p` (matchPattern correctness for the LHS;
  this follows from the yet-to-be-proven `matchPattern_correct` theorem which
  establishes that pattern matching is a left-inverse of `applyBindings`)
- `hbs_rhs`: `applyBindings bs r.right = q` (given directly by DeclReduces.topRule)

`congElem` (sub-collection rewriting) is excluded: it requires LP clauses indexed
by (rule, collection-index, collection-length), which is future work.

`lp_sound` is deferred: clauses are not range-restricted (LP variables in heads but
not in the empty body), so `leastHerbrandModel` over-approximates `DeclReduces`.

## LLM Notes

- `abbrev mettailLPSig` with `functionArity := fun _ => 2` makes `![a, b]` typecheck
  for `Fin (mettailLPSig.functionArity ()) → T` (definitional transparency via abbrev).
- `pairTerm = Term.app () ![a, b]`; `pairGround = GroundTerm.app () ![a, b]`.
  Using `![a, b]` (Matrix.cons) instead of `fun i => by fin_cases i; exact a; exact b`
  gives a definitionally transparent function that `simp` can reduce with
  `Matrix.cons_val_zero` and `Matrix.cons_val_one`.
- `groundTerm_pairTerm` (marked @[simp]): unfolds pairTerm/pairGround + groundTerm.
- Commutation proved by `mutual theorem` with `termination_by sizeOf p` and `sizeOf ps`.
- `lp_complete_topRule` uses `leastHerbrandModel_clause` after building groundAtom = encodeReduces.
-/

namespace Mettapedia.Logic.LP.MeTTaILBridge

open Mettapedia.Logic.LP

/-! ## MeTTaIL type aliases -/

private abbrev ILPat  := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern
private abbrev ILCT   := Mettapedia.OSLF.MeTTaIL.Syntax.CollType
private abbrev ILRule := Mettapedia.OSLF.MeTTaIL.Syntax.RewriteRule
private abbrev ILLang := Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef
private abbrev ILBind := Mettapedia.OSLF.MeTTaIL.Match.Bindings

private abbrev ilApplyBindings : ILBind → ILPat → ILPat :=
  Mettapedia.OSLF.MeTTaIL.Match.applyBindings

/-! ## LP Signature (single binary pairing function) -/

/-- LP signature for MeTTaIL pattern encoding.
    `functionSymbols := Unit` means one binary pair function: `functionArity () = 2`.
    With `abbrev`, `mettailLPSig.functionArity () = 2` is definitionally transparent,
    so `![a, b] : Fin (mettailLPSig.functionArity ()) → T` typechecks. -/
abbrev mettailLPSig : LPSignature where
  vars            := String
  constants       := String
  functionSymbols := Unit
  functionArity   := fun _ => 2
  relationSymbols := Unit
  relationArity   := fun _ => 2

private example : mettailLPSig.functionArity () = 2 := rfl
private example : mettailLPSig.relationArity () = 2 := rfl

/-! ## Pair combinators (using Matrix.cons for definitional transparency) -/

/-- Pair two LP Terms using the single binary pairing function.
    Uses `![a, b]` (Matrix.cons) for a definitionally transparent finite function. -/
def pairTerm (a b : Term mettailLPSig) : Term mettailLPSig :=
  Term.app () ![a, b]

/-- Pair two LP GroundTerms. -/
def pairGround (a b : GroundTerm mettailLPSig) : GroundTerm mettailLPSig :=
  GroundTerm.app () ![a, b]

/-! ## groundTerm distributes over pairTerm -/

/-- Applying a grounding distributes over `pairTerm`:
    `g (pair a b) = pair' (g a) (g b)`. Marked @[simp] for use in commutation proofs. -/
@[simp]
theorem groundTerm_pairTerm (g : Grounding mettailLPSig)
    (a b : Term mettailLPSig) :
    g.groundTerm (pairTerm a b) = pairGround (g.groundTerm a) (g.groundTerm b) := by
  have hargs :
      (fun i : Fin 2 => g.groundTerm (![a, b] i)) =
      ![g.groundTerm a, g.groundTerm b] := by
    funext i
    have hi01 : i = 0 ∨ i = 1 := by
      by_cases hi0 : i = 0
      · exact Or.inl hi0
      · exact Or.inr (Fin.eq_one_of_ne_zero i hi0)
    rcases hi01 with hi | hi
    · subst hi
      simp [Matrix.cons_val_zero]
    · subst hi
      simp [Matrix.cons_val_one]
  simp [pairTerm, pairGround, Grounding.groundTerm, hargs]

/-! ## Collection type tag -/

def mettailCtStr : ILCT → String
  | .vec     => "Vec"
  | .hashBag => "Bag"
  | .hashSet => "Set"

/-! ## Pattern → LP Term encoding -/

mutual
/-- Encode a MeTTaIL Pattern as an LP Term. `.fvar x` becomes the LP variable `x`. -/
def patternToLPTerm (p : ILPat) : Term mettailLPSig :=
  match p with
  | .fvar x             => Term.var x
  | .bvar n             => Term.const s!"bv:{n}"
  | .apply c args       => pairTerm (Term.const s!"f_{c}") (patternListToLPSpine args)
  | .lambda _nm body        => pairTerm (Term.const "lambda") (patternToLPTerm body)
  | .multiLambda n _nms body => pairTerm (Term.const s!"mlam_{n}") (patternToLPTerm body)
  | .subst body repl    => pairTerm (pairTerm (Term.const "subst") (patternToLPTerm body))
                                    (patternToLPTerm repl)
  | .collection ct elems none  => pairTerm (Term.const s!"coll_{mettailCtStr ct}")
                                             (patternListToLPSpine elems)
  | .collection _ _ (some _)   => Term.const "coll_rest"

/-- Encode a list of patterns as a right-spine LP term: `[a,b,c] ↦ pair(a, pair(b, pair(c, nil)))`. -/
def patternListToLPSpine (ps : List ILPat) : Term mettailLPSig :=
  match ps with
  | []        => Term.const "nil"
  | p :: rest => pairTerm (patternToLPTerm p) (patternListToLPSpine rest)
end

/-! ## Pattern → LP GroundTerm encoding (all .fvar as constants) -/

mutual
/-- Encode a MeTTaIL Pattern as an LP GroundTerm. `.fvar x → const "fv:x"` (always ground). -/
def patternToLPGroundTerm (p : ILPat) : GroundTerm mettailLPSig :=
  match p with
  | .fvar x             => GroundTerm.const s!"fv:{x}"
  | .bvar n             => GroundTerm.const s!"bv:{n}"
  | .apply c args       => pairGround (GroundTerm.const s!"f_{c}") (patternListToLPGroundSpine args)
  | .lambda _nm body        => pairGround (GroundTerm.const "lambda") (patternToLPGroundTerm body)
  | .multiLambda n _nms body => pairGround (GroundTerm.const s!"mlam_{n}") (patternToLPGroundTerm body)
  | .subst body repl    => pairGround (pairGround (GroundTerm.const "subst") (patternToLPGroundTerm body))
                                      (patternToLPGroundTerm repl)
  | .collection ct elems none  => pairGround (GroundTerm.const s!"coll_{mettailCtStr ct}")
                                              (patternListToLPGroundSpine elems)
  | .collection _ _ (some _)   => GroundTerm.const "coll_rest"

/-- Ground cons-spine encoding. -/
def patternListToLPGroundSpine (ps : List ILPat) : GroundTerm mettailLPSig :=
  match ps with
  | []        => GroundTerm.const "nil"
  | p :: rest => pairGround (patternToLPGroundTerm p) (patternListToLPGroundSpine rest)
end

/-! ## Grounding from Bindings -/

/-- Convert MeTTaIL Bindings to an LP Grounding. -/
def bindingsToGrounding (bs : ILBind) : Grounding mettailLPSig :=
  fun v => match bs.find? (·.1 == v) with
    | some (_, val) => patternToLPGroundTerm val
    | none          => GroundTerm.const s!"fv:{v}"

/-! ## LP Encoding of Reduction -/

/-- Ground atom encoding `p ⟶ q`. -/
def encodeReduces (p q : ILPat) : GroundAtom mettailLPSig where
  symbol := ()
  args   := ![patternToLPGroundTerm p, patternToLPGroundTerm q]

/-- LP atom constructor for `reduces(lhs, rhs)` at term level. -/
def reducesAtomTerm (lhs rhs : Term mettailLPSig) : Atom mettailLPSig where
  symbol := ()
  args   := ![lhs, rhs]

/-- LP term constructor for collection payloads. -/
def collectionTerm (ct : ILCT) (payload : Term mettailLPSig) : Term mettailLPSig :=
  pairTerm (Term.const s!"coll_{mettailCtStr ct}") payload

/-- Congruence clause (head position):
    reduces(coll(pair(x,xs)), coll(pair(y,xs))) :- reduces(x,y). -/
def collectionCongHeadClause (ct : ILCT) : Clause mettailLPSig where
  head := reducesAtomTerm
    (collectionTerm ct (pairTerm (Term.var "x") (Term.var "xs")))
    (collectionTerm ct (pairTerm (Term.var "y") (Term.var "xs")))
  body := [reducesAtomTerm (Term.var "x") (Term.var "y")]

/-- Congruence clause (tail recursion):
    reduces(coll(pair(x,xs)), coll(pair(x,ys))) :- reduces(coll(xs), coll(ys)). -/
def collectionCongTailClause (ct : ILCT) : Clause mettailLPSig where
  head := reducesAtomTerm
    (collectionTerm ct (pairTerm (Term.var "x") (Term.var "xs")))
    (collectionTerm ct (pairTerm (Term.var "x") (Term.var "ys")))
  body := [reducesAtomTerm (collectionTerm ct (Term.var "xs"))
                          (collectionTerm ct (Term.var "ys"))]

/-- All congruence clauses generated from enabled collection kinds. -/
def congruenceClauses (lang : ILLang) : Program mettailLPSig :=
  lang.congruenceCollections.foldr
    (fun ct acc => [collectionCongHeadClause ct, collectionCongTailClause ct] ++ acc)
    []

/-- Encode a rewrite rule as an LP clause `reduces(enc(lhs), enc(rhs)) :- []`.
    LP variables in the head (from `.fvar x` in pattern) are grounded by `bindingsToGrounding`. -/
def rewriteRuleToLPClause (r : ILRule) : Clause mettailLPSig where
  head.symbol := ()
  head.args   := ![patternToLPTerm r.left, patternToLPTerm r.right]
  body        := []

/-- Compile a LanguageDef to an LP KnowledgeBase. -/
def languageDefToLPKB (lang : ILLang) : KnowledgeBase mettailLPSig where
  prog := lang.rewrites.map rewriteRuleToLPClause ++ congruenceClauses lang
  db   := ∅

/-! ## Commutation Lemma -/

open Mettapedia.Languages.ProcessCalculi.MORK (morkTranslatable morkTranslatableList)

/- The commutation theorem: grounding an LP term equals encoding the bound pattern.

    `g.groundTerm (patternToLPTerm p) = patternToLPGroundTerm (applyBindings g p)`
    for morkTranslatable p. Proved by mutual well-founded recursion on sizeOf. -/
mutual
private theorem commute_pat (bs : ILBind) (p : ILPat) (hmt : morkTranslatable p = true) :
    (bindingsToGrounding bs).groundTerm (patternToLPTerm p) =
    patternToLPGroundTerm (ilApplyBindings bs p) := by
  match p with
  | .fvar x =>
    simp only [patternToLPTerm, Grounding.groundTerm, bindingsToGrounding,
               ilApplyBindings, Mettapedia.OSLF.MeTTaIL.Match.applyBindings]
    cases hfind : bs.find? (fun p => p.1 == x) with
    | some pv =>
      simp
    | none =>
      simp [patternToLPGroundTerm]
  | .bvar n =>
    simp [patternToLPTerm, Grounding.groundTerm, ilApplyBindings,
          Mettapedia.OSLF.MeTTaIL.Match.applyBindings, patternToLPGroundTerm]
  | .apply c args =>
    simp only [morkTranslatable] at hmt
    simp only [patternToLPTerm, ilApplyBindings, Mettapedia.OSLF.MeTTaIL.Match.applyBindings,
               patternToLPGroundTerm, groundTerm_pairTerm, Grounding.groundTerm]
    congr 1
    exact commute_list bs args hmt
  | .lambda _nm body =>
    simp only [morkTranslatable] at hmt
    simp only [patternToLPTerm, ilApplyBindings, Mettapedia.OSLF.MeTTaIL.Match.applyBindings,
               patternToLPGroundTerm, groundTerm_pairTerm, Grounding.groundTerm]
    exact congrArg (pairGround (GroundTerm.const "lambda")) (commute_pat bs body hmt)
  | .multiLambda n _ body =>
    simp only [morkTranslatable] at hmt
    simp only [patternToLPTerm, ilApplyBindings, Mettapedia.OSLF.MeTTaIL.Match.applyBindings,
               patternToLPGroundTerm, groundTerm_pairTerm, Grounding.groundTerm]
    exact congrArg (pairGround (GroundTerm.const s!"mlam_{n}")) (commute_pat bs body hmt)
  | .subst _ _ =>
    simp [morkTranslatable] at hmt
  | .collection ct elems none =>
    simp only [morkTranslatable] at hmt
    simp only [patternToLPTerm, ilApplyBindings, Mettapedia.OSLF.MeTTaIL.Match.applyBindings,
               patternToLPGroundTerm, groundTerm_pairTerm, Grounding.groundTerm, List.append_nil]
    exact congrArg (pairGround (GroundTerm.const s!"coll_{mettailCtStr ct}"))
      (commute_list bs elems hmt)
  | .collection _ _ (some _) =>
    simp [morkTranslatable] at hmt
termination_by sizeOf p

/-- List version of the commutation theorem. -/
private theorem commute_list (bs : ILBind) (ps : List ILPat) (hmt : morkTranslatableList ps = true) :
    (bindingsToGrounding bs).groundTerm (patternListToLPSpine ps) =
    patternListToLPGroundSpine (ps.map (ilApplyBindings bs)) := by
  match ps with
  | [] => simp [patternListToLPSpine, patternListToLPGroundSpine, Grounding.groundTerm]
  | p :: rest =>
    simp only [morkTranslatableList, Bool.and_eq_true] at hmt
    simp only [patternListToLPSpine, patternListToLPGroundSpine, List.map,
               groundTerm_pairTerm]
    congr 1
    · exact commute_pat bs p hmt.1
    · exact commute_list bs rest hmt.2
termination_by sizeOf ps
end

theorem groundTerm_commutes_applyBindings (bs : ILBind) (p : ILPat)
    (hmt : morkTranslatable p = true) :
    (bindingsToGrounding bs).groundTerm (patternToLPTerm p) =
    patternToLPGroundTerm (ilApplyBindings bs p) :=
  commute_pat bs p hmt

/-! ## Main Completeness Theorem (topRule fragment) -/

open Mettapedia.OSLF.MeTTaIL.DeclReductions (DeclReduces)

/-- **LP Completeness — topRule fragment**.

    If a rewrite rule `r` with empty premises fires on `p` to produce `q`
    (i.e., `applyBindings bs r.left = p` and `applyBindings bs r.right = q`),
    and both sides of `r` are morkTranslatable, then the encoded step
    `encodeReduces p q` belongs to the least Herbrand model of the compiled LP.

    **Preconditions**:
    - `hmt_rl`, `hmt_rr`: rule sides are morkTranslatable (needed for commutation)
    - `hbs_lhs`: `applyBindings bs r.left = p` — the "pattern matching is correct" property
      (this is the fundamental correctness of MeTTaIL's `matchPattern`, which says that
       if `bs ∈ matchPattern r.left p` then `applyBindings bs r.left = p`; once the
       theorem `matchPattern_correct` is proven in MatchSpec.lean, `hbs_lhs` follows)
    - `hbs_rhs`: `applyBindings bs r.right = q` (given directly by DeclReduces.topRule)

    **`congElem` note**: Sub-collection rewriting (DeclReduces.congElem) requires LP
    clauses indexed by (rule, collection-index, collection-length) and is not covered here.

    **`lp_sound` note**: The LP clauses are not range-restricted (LP variables appear in
    clause heads but not in the empty body), so `leastHerbrandModel` over-approximates
    `DeclReduces`. The `lp_sound` direction is deferred pending range-restriction. -/
theorem lp_complete_topRule {lang : ILLang} {p q : ILPat}
    (r : ILRule)
    (hr_mem : r ∈ lang.rewrites)
    (_hr_prem : r.premises = [])
    (hmt_rl : morkTranslatable r.left = true)
    (hmt_rr : morkTranslatable r.right = true)
    (bs : ILBind)
    (hbs_lhs : Mettapedia.OSLF.MeTTaIL.Match.applyBindings bs r.left = p)
    (hbs_rhs : Mettapedia.OSLF.MeTTaIL.Match.applyBindings bs r.right = q) :
    encodeReduces p q ∈ leastHerbrandModel (languageDefToLPKB lang) := by
  -- The clause for r is in the KB
  have hc_mem : rewriteRuleToLPClause r ∈ (languageDefToLPKB lang).prog :=
    List.mem_append.mpr <| Or.inl <| List.mem_map.mpr ⟨r, hr_mem, rfl⟩
  -- Body is empty: vacuously satisfied — (rewriteRuleToLPClause r).body = [] by def
  have hbody : ∀ b ∈ (rewriteRuleToLPClause r).body,
      (bindingsToGrounding bs).groundAtom b ∈ leastHerbrandModel (languageDefToLPKB lang) := by
    intro b hb
    simp [rewriteRuleToLPClause] at hb
  -- LHS commutation: groundTerm enc(r.left) = patternToLPGroundTerm p
  have hlhs : (bindingsToGrounding bs).groundTerm (patternToLPTerm r.left) =
              patternToLPGroundTerm p := by
    rw [groundTerm_commutes_applyBindings bs r.left hmt_rl]
    exact congrArg patternToLPGroundTerm hbs_lhs
  -- RHS commutation: groundTerm enc(r.right) = patternToLPGroundTerm q
  have hrhs : (bindingsToGrounding bs).groundTerm (patternToLPTerm r.right) =
              patternToLPGroundTerm q := by
    rw [groundTerm_commutes_applyBindings bs r.right hmt_rr]
    exact congrArg patternToLPGroundTerm hbs_rhs
  -- Grounded head equals encodeReduces p q
  -- Both atoms have symbol = () so args : Fin 2 → GroundTerm on both sides.
  -- We provide the type explicitly to heq_of_eq to help the unifier.
  have hhead : (bindingsToGrounding bs).groundAtom (rewriteRuleToLPClause r).head =
               encodeReduces p q :=
    GroundAtom.ext rfl (by
      refine @heq_of_eq (Fin 2 → GroundTerm mettailLPSig) _ _ ?_
      funext i
      have hi01 : i = 0 ∨ i = 1 := by
        by_cases hi0 : i = 0
        · exact Or.inl hi0
        · exact Or.inr (Fin.eq_one_of_ne_zero i hi0)
      rcases hi01 with hi | hi
      · subst hi
        simpa [Grounding.groundAtom, rewriteRuleToLPClause, encodeReduces,
          Matrix.cons_val_zero, Matrix.head_cons] using hlhs
      · subst hi
        simpa [Grounding.groundAtom, rewriteRuleToLPClause, encodeReduces,
          Matrix.cons_val_one, Matrix.head_fin_const] using hrhs)
  -- `hhead` is g.groundAtom c.head = encodeReduces p q, exactly what T_P_LP requires.
  -- Build membership directly in T_P_LP then use the fixpoint equation.
  have hmem : encodeReduces p q ∈
      T_P_LP (languageDefToLPKB lang) (leastHerbrandModel (languageDefToLPKB lang)) := by
    simp only [T_P_LP, Set.mem_union, Set.mem_setOf_eq]
    exact Or.inr ⟨rewriteRuleToLPClause r, bindingsToGrounding bs, hc_mem, hhead, hbody⟩
  rwa [leastHerbrandModel_fixpoint] at hmem

/-! ## Congruence completeness (collection context closure) -/

private lemma mem_congruenceClauses_head_of_mem {cts : List ILCT} {ct : ILCT}
    (hct : ct ∈ cts) :
    collectionCongHeadClause ct ∈
      cts.foldr (fun c acc => [collectionCongHeadClause c, collectionCongTailClause c] ++ acc) [] := by
  induction cts with
  | nil =>
    cases hct
  | cons c cs ih =>
    simp only [List.mem_cons] at hct
    simp only [List.foldr]
    cases hct with
    | inl hc =>
      subst hc
      simp [List.mem_cons]
    | inr hcs =>
      exact List.mem_append.mpr (Or.inr (ih hcs))

private lemma mem_congruenceClauses_tail_of_mem {cts : List ILCT} {ct : ILCT}
    (hct : ct ∈ cts) :
    collectionCongTailClause ct ∈
      cts.foldr (fun c acc => [collectionCongHeadClause c, collectionCongTailClause c] ++ acc) [] := by
  induction cts with
  | nil =>
    cases hct
  | cons c cs ih =>
    simp only [List.mem_cons] at hct
    simp only [List.foldr]
    cases hct with
    | inl hc =>
      subst hc
      simp [List.mem_cons]
    | inr hcs =>
      exact List.mem_append.mpr (Or.inr (ih hcs))

private lemma collectionCongHeadClause_mem_prog {lang : ILLang} {ct : ILCT}
    (hct : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef.allowsCongruenceIn lang ct) :
    collectionCongHeadClause ct ∈ (languageDefToLPKB lang).prog := by
  have hct_mem : ct ∈ lang.congruenceCollections := hct
  have hcong : collectionCongHeadClause ct ∈ congruenceClauses lang := by
    unfold congruenceClauses
    exact mem_congruenceClauses_head_of_mem hct_mem
  exact List.mem_append.mpr (Or.inr hcong)

private lemma collectionCongTailClause_mem_prog {lang : ILLang} {ct : ILCT}
    (hct : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef.allowsCongruenceIn lang ct) :
    collectionCongTailClause ct ∈ (languageDefToLPKB lang).prog := by
  have hct_mem : ct ∈ lang.congruenceCollections := hct
  have hcong : collectionCongTailClause ct ∈ congruenceClauses lang := by
    unfold congruenceClauses
    exact mem_congruenceClauses_tail_of_mem hct_mem
  exact List.mem_append.mpr (Or.inr hcong)

/-- If one element in a collection reduces, the whole collection reduces (rest = none),
    using LP context-closure clauses. -/
private theorem lp_complete_congElem_none {lang : ILLang} {ct : ILCT}
    (hct : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef.allowsCongruenceIn lang ct)
    {elems : List ILPat} {i : Nat} (hi : i < elems.length) {q' : ILPat}
    (hinner : encodeReduces elems[i] q' ∈ leastHerbrandModel (languageDefToLPKB lang)) :
    encodeReduces (.collection ct elems none) (.collection ct (elems.set i q') none)
      ∈ leastHerbrandModel (languageDefToLPKB lang) := by
  induction elems generalizing i with
  | nil =>
    cases hi
  | cons e rest ih =>
    cases i with
    | zero =>
      have hinner0 : encodeReduces e q' ∈ leastHerbrandModel (languageDefToLPKB lang) := by
        simpa using hinner
      let g : Grounding mettailLPSig := fun v =>
        if v = "x" then patternToLPGroundTerm e
        else if v = "y" then patternToLPGroundTerm q'
        else if v = "xs" then patternListToLPGroundSpine rest
        else GroundTerm.const "unused"
      have hbody :
          ∀ b ∈ (collectionCongHeadClause ct).body,
            g.groundAtom b ∈ leastHerbrandModel (languageDefToLPKB lang) := by
        intro b hb
        simp [collectionCongHeadClause, reducesAtomTerm] at hb
        rcases hb with rfl
        have hbody_eq :
            g.groundAtom (reducesAtomTerm (Term.var "x") (Term.var "y")) =
              encodeReduces e q' := by
          refine GroundAtom.ext rfl (by
            refine @heq_of_eq (Fin 2 → GroundTerm mettailLPSig) _ _ ?_
            funext j
            have hj01 : j = 0 ∨ j = 1 := by
              by_cases hj0 : j = 0
              · exact Or.inl hj0
              · exact Or.inr (Fin.eq_one_of_ne_zero j hj0)
            rcases hj01 with hj | hj
            · subst hj
              have h_gx : g "x" = patternToLPGroundTerm e := rfl
              simp only [Grounding.groundAtom, Grounding.groundTerm, reducesAtomTerm, encodeReduces,
                Matrix.cons_val_zero, h_gx]
            · subst hj
              have h_gy : g "y" = patternToLPGroundTerm q' := rfl
              simp only [Grounding.groundAtom, Grounding.groundTerm, reducesAtomTerm, encodeReduces,
                Matrix.cons_val_one, Matrix.cons_val_zero, h_gy])
        have hbody_mem :
            g.groundAtom (reducesAtomTerm (Term.var "x") (Term.var "y")) ∈
              leastHerbrandModel (languageDefToLPKB lang) := by
          rw [hbody_eq]
          exact hinner0
        exact hbody_mem
      have hmem :
          g.groundAtom (collectionCongHeadClause ct).head ∈
            leastHerbrandModel (languageDefToLPKB lang) := by
        exact leastHerbrandModel_clause (languageDefToLPKB lang)
          (collectionCongHeadClause ct) (collectionCongHeadClause_mem_prog hct) g hbody
      have hhead_eq :
          g.groundAtom (collectionCongHeadClause ct).head =
            encodeReduces (.collection ct (e :: rest) none)
              (.collection ct (q' :: rest) none) := by
        refine GroundAtom.ext rfl (by
          refine @heq_of_eq (Fin 2 → GroundTerm mettailLPSig) _ _ ?_
          funext j
          have hj01 : j = 0 ∨ j = 1 := by
            by_cases hj0 : j = 0
            · exact Or.inl hj0
            · exact Or.inr (Fin.eq_one_of_ne_zero j hj0)
          rcases hj01 with hj | hj
          · subst hj
            have h_gx : g "x" = patternToLPGroundTerm e := rfl
            have h_gxs : g "xs" = patternListToLPGroundSpine rest := rfl
            simp only [Grounding.groundAtom, Grounding.groundTerm, groundTerm_pairTerm,
              collectionCongHeadClause, collectionTerm, reducesAtomTerm, encodeReduces,
              patternToLPGroundTerm, patternListToLPGroundSpine, Matrix.cons_val_zero,
              h_gx, h_gxs]
          · subst hj
            have h_gy : g "y" = patternToLPGroundTerm q' := rfl
            have h_gxs : g "xs" = patternListToLPGroundSpine rest := rfl
            simp only [Grounding.groundAtom, Grounding.groundTerm, groundTerm_pairTerm,
              collectionCongHeadClause, collectionTerm, reducesAtomTerm, encodeReduces,
              patternToLPGroundTerm, patternListToLPGroundSpine, Matrix.cons_val_one,
              Matrix.cons_val_zero, h_gy, h_gxs])
      simpa [hhead_eq] using hmem
    | succ i =>
      have hi' : i < rest.length := by simpa using hi
      have hinner' : encodeReduces rest[i] q' ∈ leastHerbrandModel (languageDefToLPKB lang) := by
        simpa using hinner
      have htail :
          encodeReduces (.collection ct rest none) (.collection ct (rest.set i q') none) ∈
            leastHerbrandModel (languageDefToLPKB lang) :=
        ih hi' hinner'
      let g : Grounding mettailLPSig := fun v =>
        if v = "x" then patternToLPGroundTerm e
        else if v = "xs" then patternListToLPGroundSpine rest
        else if v = "ys" then patternListToLPGroundSpine (rest.set i q')
        else GroundTerm.const "unused"
      have hbody :
          ∀ b ∈ (collectionCongTailClause ct).body,
            g.groundAtom b ∈ leastHerbrandModel (languageDefToLPKB lang) := by
        intro b hb
        simp [collectionCongTailClause, reducesAtomTerm] at hb
        rcases hb with rfl
        have hbody_eq :
            g.groundAtom
                (reducesAtomTerm (collectionTerm ct (Term.var "xs"))
                  (collectionTerm ct (Term.var "ys"))) =
              encodeReduces (.collection ct rest none)
                (.collection ct (rest.set i q') none) := by
          refine GroundAtom.ext rfl (by
            refine @heq_of_eq (Fin 2 → GroundTerm mettailLPSig) _ _ ?_
            funext j
            have hj01 : j = 0 ∨ j = 1 := by
              by_cases hj0 : j = 0
              · exact Or.inl hj0
              · exact Or.inr (Fin.eq_one_of_ne_zero j hj0)
            rcases hj01 with hj | hj
            · subst hj
              have h_gxs : g "xs" = patternListToLPGroundSpine rest := rfl
              simp only [Grounding.groundAtom, Grounding.groundTerm, groundTerm_pairTerm,
                reducesAtomTerm, collectionTerm, encodeReduces, patternToLPGroundTerm,
                Matrix.cons_val_zero, h_gxs]
            · subst hj
              have h_gys : g "ys" = patternListToLPGroundSpine (rest.set i q') := rfl
              simp only [Grounding.groundAtom, Grounding.groundTerm, groundTerm_pairTerm,
                reducesAtomTerm, collectionTerm, encodeReduces, patternToLPGroundTerm,
                Matrix.cons_val_one, Matrix.cons_val_zero, h_gys])
        have hbody_mem :
            g.groundAtom
                (reducesAtomTerm (collectionTerm ct (Term.var "xs"))
                  (collectionTerm ct (Term.var "ys"))) ∈
              leastHerbrandModel (languageDefToLPKB lang) := by
          rw [hbody_eq]
          exact htail
        exact hbody_mem
      have hmem :
          g.groundAtom (collectionCongTailClause ct).head ∈
            leastHerbrandModel (languageDefToLPKB lang) := by
        exact leastHerbrandModel_clause (languageDefToLPKB lang)
          (collectionCongTailClause ct) (collectionCongTailClause_mem_prog hct) g hbody
      have hhead_eq :
          g.groundAtom (collectionCongTailClause ct).head =
            encodeReduces (.collection ct (e :: rest) none)
              (.collection ct (e :: rest.set i q') none) := by
        refine GroundAtom.ext rfl (by
          refine @heq_of_eq (Fin 2 → GroundTerm mettailLPSig) _ _ ?_
          funext j
          have hj01 : j = 0 ∨ j = 1 := by
            by_cases hj0 : j = 0
            · exact Or.inl hj0
            · exact Or.inr (Fin.eq_one_of_ne_zero j hj0)
          rcases hj01 with hj | hj
          · subst hj
            have h_gx : g "x" = patternToLPGroundTerm e := rfl
            have h_gxs : g "xs" = patternListToLPGroundSpine rest := rfl
            simp only [Grounding.groundAtom, Grounding.groundTerm, groundTerm_pairTerm,
              collectionCongTailClause, collectionTerm, reducesAtomTerm, encodeReduces,
              patternToLPGroundTerm, patternListToLPGroundSpine, Matrix.cons_val_zero,
              h_gx, h_gxs]
          · subst hj
            have h_gx : g "x" = patternToLPGroundTerm e := rfl
            have h_gys : g "ys" = patternListToLPGroundSpine (rest.set i q') := rfl
            simp only [Grounding.groundAtom, Grounding.groundTerm, groundTerm_pairTerm,
              collectionCongTailClause, collectionTerm, reducesAtomTerm, encodeReduces,
              patternToLPGroundTerm, patternListToLPGroundSpine, Matrix.cons_val_one,
              Matrix.cons_val_zero, h_gx, h_gys])
      simpa [hhead_eq] using hmem

/-! ## Regression checks: focused commutation cases -/

/-- Regression: `.lambda` pattern commutes with LP grounding/applyBindings translation. -/
theorem regression_commute_lambda (bs : ILBind) :
    (bindingsToGrounding bs).groundTerm
        (patternToLPTerm (.lambda none (.apply "f" [.fvar "x", .bvar 0]))) =
    patternToLPGroundTerm
      (ilApplyBindings bs (.lambda none (.apply "f" [.fvar "x", .bvar 0]))) := by
  have hmt : morkTranslatable (.lambda none (.apply "f" [.fvar "x", .bvar 0])) = true := by
    simp [morkTranslatable, morkTranslatableList]
  simpa using
    groundTerm_commutes_applyBindings bs
      (.lambda none (.apply "f" [.fvar "x", .bvar 0])) hmt

/-- Regression: `.multiLambda` pattern commutes with LP grounding/applyBindings translation. -/
theorem regression_commute_multiLambda (bs : ILBind) :
    (bindingsToGrounding bs).groundTerm
      (patternToLPTerm (.multiLambda 2 [] (.apply "g" [.fvar "x"]))) =
    patternToLPGroundTerm
      (ilApplyBindings bs (.multiLambda 2 [] (.apply "g" [.fvar "x"]))) := by
  have hmt : morkTranslatable (.multiLambda 2 [] (.apply "g" [.fvar "x"])) = true := by
    simp [morkTranslatable, morkTranslatableList]
  simpa using
    groundTerm_commutes_applyBindings bs
      (.multiLambda 2 [] (.apply "g" [.fvar "x"])) hmt

/-- Regression: `.collection _ _ none` pattern commutes with LP grounding/applyBindings translation. -/
theorem regression_commute_collection_none (bs : ILBind) :
    (bindingsToGrounding bs).groundTerm
      (patternToLPTerm (.collection .vec [.fvar "x", .bvar 1, .lambda none (.fvar "y")] none)) =
    patternToLPGroundTerm
      (ilApplyBindings bs (.collection .vec [.fvar "x", .bvar 1, .lambda none (.fvar "y")] none)) := by
  have hmt :
      morkTranslatable (.collection .vec [.fvar "x", .bvar 1, .lambda none (.fvar "y")] none) = true := by
    simp [morkTranslatable, morkTranslatableList]
  simpa using
    groundTerm_commutes_applyBindings bs
      (.collection .vec [.fvar "x", .bvar 1, .lambda none (.fvar "y")] none) hmt

/-- Negative sanity check: rest-variable collections are outside the translatable fragment. -/
theorem regression_nonTranslatable_collection_some :
    morkTranslatable (.collection .vec [.fvar "x"] (some "rest")) = false := by
  simp [morkTranslatable]

/-! ## Corollary: DeclReduces.topRule → lp_complete

Fragment restriction: rule LHS must be `isMatchCorrect` (no `.subst`, no `.collection`).
This ensures `matchPattern_correct` gives `applyBindings bs r.left = p`. -/

/-- A rule is LP-translatable: both sides are mork-translatable, and the LHS
    is match-correct (so `matchPattern_correct` recovers the matched term). -/
def lpTranslatable (r : Mettapedia.OSLF.MeTTaIL.Syntax.RewriteRule) : Bool :=
  morkTranslatable r.left && morkTranslatable r.right &&
  Mettapedia.OSLF.MeTTaIL.Match.Pattern.isMatchCorrect r.left

/-- Full `lp_complete` on the translatable term fragment:
    `DeclReduces` in the `lpTranslatable` rule fragment implies the encoded
    reduces atom is in the least Herbrand model.

    `hp_trans` restricts the source term to `morkTranslatable`, which excludes
    `.collection _ _ (some _)` and allows congruence lifting through the LP
    context-closure clauses. -/
theorem lp_complete {lang : ILLang} {p q : ILPat}
    (h : DeclReduces lang p q)
    (hmt_all : ∀ r ∈ lang.rewrites, lpTranslatable r = true)
    (hp_trans : morkTranslatable p = true) :
    encodeReduces p q ∈ leastHerbrandModel (languageDefToLPKB lang) := by
  cases h with
  | topRule r hr hprem bs hbs hrhs =>
    have hmt := hmt_all r hr
    simp only [lpTranslatable, Bool.and_eq_true] at hmt
    obtain ⟨⟨hmt_l, hmt_r⟩, hmc⟩ := hmt
    have hbs_lhs := Mettapedia.OSLF.MeTTaIL.MatchSpec.matchPattern_correct hbs hmc
    exact lp_complete_topRule r hr hprem hmt_l hmt_r bs hbs_lhs hrhs
  | @congElem elems ct rest hct i hi r hr hprem bs hbs q' hq =>
    have hmt := hmt_all r hr
    simp only [lpTranslatable, Bool.and_eq_true] at hmt
    obtain ⟨⟨hmt_l, hmt_r⟩, hmc⟩ := hmt
    have hbs_lhs : Mettapedia.OSLF.MeTTaIL.Match.applyBindings bs r.left = elems[i] :=
      Mettapedia.OSLF.MeTTaIL.MatchSpec.matchPattern_correct hbs hmc
    have hinner : encodeReduces elems[i] q' ∈ leastHerbrandModel (languageDefToLPKB lang) :=
      lp_complete_topRule r hr hprem hmt_l hmt_r bs hbs_lhs hq
    have hrest_none : rest = none := by
      cases rest with
      | none => rfl
      | some _ =>
        simp [morkTranslatable] at hp_trans
    subst hrest_none
    exact lp_complete_congElem_none hct hi hinner

/-! ## Canary theorems: congruence clause grounding equivalence -/

/-- Canary: head congruence clause grounds to expected encodeReduces for head replacement. -/
theorem canary_congHead_grounding (ct : ILCT) (e q' : ILPat) (rest : List ILPat) :
    let g : Grounding mettailLPSig := fun v =>
      if v = "x" then patternToLPGroundTerm e
      else if v = "y" then patternToLPGroundTerm q'
      else if v = "xs" then patternListToLPGroundSpine rest
      else GroundTerm.const "unused"
    g.groundAtom (collectionCongHeadClause ct).head =
      encodeReduces (.collection ct (e :: rest) none)
        (.collection ct (q' :: rest) none) := by
  let g : Grounding mettailLPSig := fun v =>
    if v = "x" then patternToLPGroundTerm e
    else if v = "y" then patternToLPGroundTerm q'
    else if v = "xs" then patternListToLPGroundSpine rest
    else GroundTerm.const "unused"
  show g.groundAtom (collectionCongHeadClause ct).head = _
  have h_gx : g "x" = patternToLPGroundTerm e := rfl
  have h_gy : g "y" = patternToLPGroundTerm q' := rfl
  have h_gxs : g "xs" = patternListToLPGroundSpine rest := rfl
  exact GroundAtom.ext rfl (by
    refine @heq_of_eq (Fin 2 → GroundTerm mettailLPSig) _ _ ?_
    funext j
    have hj01 : j = 0 ∨ j = 1 := by
      by_cases hj0 : j = 0
      · exact Or.inl hj0
      · exact Or.inr (Fin.eq_one_of_ne_zero j hj0)
    rcases hj01 with hj | hj
    · subst hj
      simp only [Grounding.groundAtom, Grounding.groundTerm, groundTerm_pairTerm,
        collectionCongHeadClause, collectionTerm, reducesAtomTerm, encodeReduces,
        patternToLPGroundTerm, patternListToLPGroundSpine, Matrix.cons_val_zero,
        h_gx, h_gxs]
    · subst hj
      simp only [Grounding.groundAtom, Grounding.groundTerm, groundTerm_pairTerm,
        collectionCongHeadClause, collectionTerm, reducesAtomTerm, encodeReduces,
        patternToLPGroundTerm, patternListToLPGroundSpine, Matrix.cons_val_one,
        Matrix.cons_val_zero, h_gy, h_gxs])

/-- Canary: tail congruence clause grounds to expected encodeReduces for tail replacement. -/
theorem canary_congTail_grounding (ct : ILCT) (e : ILPat) (rest rest' : List ILPat) :
    let g : Grounding mettailLPSig := fun v =>
      if v = "x" then patternToLPGroundTerm e
      else if v = "xs" then patternListToLPGroundSpine rest
      else if v = "ys" then patternListToLPGroundSpine rest'
      else GroundTerm.const "unused"
    g.groundAtom (collectionCongTailClause ct).head =
      encodeReduces (.collection ct (e :: rest) none)
        (.collection ct (e :: rest') none) := by
  let g : Grounding mettailLPSig := fun v =>
    if v = "x" then patternToLPGroundTerm e
    else if v = "xs" then patternListToLPGroundSpine rest
    else if v = "ys" then patternListToLPGroundSpine rest'
    else GroundTerm.const "unused"
  show g.groundAtom (collectionCongTailClause ct).head = _
  have h_gx : g "x" = patternToLPGroundTerm e := rfl
  have h_gxs : g "xs" = patternListToLPGroundSpine rest := rfl
  have h_gys : g "ys" = patternListToLPGroundSpine rest' := rfl
  exact GroundAtom.ext rfl (by
    refine @heq_of_eq (Fin 2 → GroundTerm mettailLPSig) _ _ ?_
    funext j
    have hj01 : j = 0 ∨ j = 1 := by
      by_cases hj0 : j = 0
      · exact Or.inl hj0
      · exact Or.inr (Fin.eq_one_of_ne_zero j hj0)
    rcases hj01 with hj | hj
    · subst hj
      simp only [Grounding.groundAtom, Grounding.groundTerm, groundTerm_pairTerm,
        collectionCongTailClause, collectionTerm, reducesAtomTerm, encodeReduces,
        patternToLPGroundTerm, patternListToLPGroundSpine, Matrix.cons_val_zero,
        h_gx, h_gxs]
    · subst hj
      simp only [Grounding.groundAtom, Grounding.groundTerm, groundTerm_pairTerm,
        collectionCongTailClause, collectionTerm, reducesAtomTerm, encodeReduces,
        patternToLPGroundTerm, patternListToLPGroundSpine, Matrix.cons_val_one,
        Matrix.cons_val_zero, h_gx, h_gys])

/-! ## LP Soundness (Rewrite-Only Fragment)

The full `languageDefToLPKB` includes congruence clauses (non-unit body), so
`RangeRestriction.lhm_unit_mem_iff` does not apply directly to it.

For the **rewrite-only** sub-KB (no congruence clauses), all clauses are unit
(`rewriteRuleToLPClause` sets `body = []`), so the LHM characterization gives
clean LP soundness:

  `encodeReduces p q ∈ lhm(rewriteOnlyKB) → ∃ r ∈ rewrites, ∃ g, g.groundAtom c.head = encodeReduces p q`

This closes the LP soundness gap for the pure rewrite fragment.
The congruence extension remains future work (requires non-unit soundness). -/

/-- KB built from only the rewrite-rule unit clauses, without congruence clauses. -/
def rewriteOnlyKB (lang : ILLang) : KnowledgeBase mettailLPSig where
  prog := lang.rewrites.map rewriteRuleToLPClause
  db   := ∅

/-- `rewriteOnlyKB` is a unit KB: empty db and all clauses have empty body. -/
theorem rewriteOnlyKB_isUnit (lang : ILLang) :
    (rewriteOnlyKB lang).isUnit := by
  refine ⟨rfl, ?_⟩
  intro c hc
  simp only [rewriteOnlyKB, List.mem_map] at hc
  obtain ⟨r, _, rfl⟩ := hc
  simp [Clause.isUnit, rewriteRuleToLPClause]

/-- **LP Soundness — rewrite-only fragment**.

    If `encodeReduces p q` is in the least Herbrand model of the rewrite-only KB
    (no congruence clauses), then there exists a rewrite rule `r ∈ lang.rewrites`
    and a grounding `g` such that `g` instantiates the compiled clause of `r` to
    exactly `encodeReduces p q`.

    This is the LP soundness direction for unit programs: every element of the
    LHM is directly witnessed by a single clause instantiation (no chaining needed).

    **Scope**: applies to `rewriteOnlyKB`, not `languageDefToLPKB` (which includes
    non-unit congruence clauses). The congruence soundness direction is future work. -/
theorem lp_sound_rewriteOnly {lang : ILLang} {p q : ILPat}
    (h : encodeReduces p q ∈ leastHerbrandModel (rewriteOnlyKB lang)) :
    ∃ r ∈ lang.rewrites, ∃ g : Grounding mettailLPSig,
        g.groundAtom (rewriteRuleToLPClause r).head = encodeReduces p q := by
  have hunit := rewriteOnlyKB_isUnit lang
  obtain ⟨c, hc, g, hg⟩ := lhm_unit_mem_witness (rewriteOnlyKB lang) hunit _ h
  simp only [rewriteOnlyKB, List.mem_map] at hc
  obtain ⟨r, hr, rfl⟩ := hc
  exact ⟨r, hr, g, hg⟩

/-- Completeness of `rewriteOnlyKB`: if a rewrite rule fires, the encoded step
    is in the LHM of the rewrite-only KB.

    This is the complement of `lp_sound_rewriteOnly` and follows from `lhm_unit_mem_of_clause`.
    Together they give: `encodeReduces p q ∈ LHM(rewriteOnlyKB) ↔ ∃ r, g, rule-instantiation`. -/
theorem lp_complete_rewriteOnly {lang : ILLang} (r : ILRule)
    (hr : r ∈ lang.rewrites) (g : Grounding mettailLPSig) :
    g.groundAtom (rewriteRuleToLPClause r).head ∈
      leastHerbrandModel (rewriteOnlyKB lang) :=
  lhm_unit_mem_of_clause (rewriteOnlyKB lang) (rewriteOnlyKB_isUnit lang)
    (rewriteRuleToLPClause r)
    (List.mem_map.mpr ⟨r, hr, rfl⟩) g

end Mettapedia.Logic.LP.MeTTaILBridge
