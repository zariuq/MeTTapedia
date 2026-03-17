import Mettapedia.Languages.GF.VisibleLayer
import Mettapedia.Languages.GF.VisibleLayerGFInstance
import Mettapedia.OSLF.QuantifiedFormula2

/-!
# Store → Logical Form: Assembling QFormula2 from Grammar State

This module converts a `GrammarState` (term + semantic store) into a
`QFormula2` — the evidence-valued logical form of a sentence.

## Pipeline position

```
  GF tree → Pattern → V1-V4 → GrammarState → [THIS MODULE] → QFormula2 → BinaryEvidence
```

The store records meaning-bearing decisions (V1 quantifier intro, V2 scope
choice), and the term has NP positions replaced with `⊛NPVar(q)` placeholders.
This module reads both to assemble the quantified logical form.

## Design

1. `detToQuantBinder`: Maps determiner patterns (every_Det → ∀, someSg_Det → ∃)
2. `restrToFormula`: Maps restrictor patterns to QFormula2 predicates
3. `termToBody`: Extracts the predication from the NP-replaced term
4. `wrapQuantifier`: Wraps body in ∀q. restr(q) → body or ∃q. restr(q) ∧ body
5. `storeToQFormula2`: Full assembly given scope-ordered quantifier list
-/

namespace Mettapedia.Languages.GF.StoreToLogicalForm

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.QuantifiedFormula2
open Mettapedia.Languages.GF.VisibleLayer
open Mettapedia.Languages.GF.VisibleLayerGFInstance

/-! ## 1. Determiner → Quantifier Binder -/

/-- Is this determiner universal (every, all) or existential (a, some, the)?
    Returns `true` for universal. -/
def isUniversalDet (det : Pattern) : Bool :=
  match det with
  | .fvar "every_Det" => true
  | .fvar "all_Det"   => true
  | _ => false

/-- Map a determiner pattern to a quantifier binder (∀ or ∃). -/
def detToQuantBinder (det : Pattern) : String → QFormula2 → QFormula2 :=
  if isUniversalDet det then QFormula2.qforall else QFormula2.qexists

example : detToQuantBinder (.fvar "every_Det") = QFormula2.qforall := by
  simp [detToQuantBinder, isUniversalDet]

example : detToQuantBinder (.fvar "someSg_Det") = QFormula2.qexists := by
  simp [detToQuantBinder, isUniversalDet]

/-! ## 2. Restrictor → Predicate Formula -/

/-- Extract the noun name from a restrictor pattern.
    `UseN(man_N)` → `"man_N"`, fallback to `"unknown"`. -/
def extractNounName (restr : Pattern) : String :=
  match restr with
  | .apply "UseN" [.fvar nounName] => nounName
  | .fvar nounName => nounName
  | _ => "unknown_restr"

/-- Map a restrictor pattern to a predicate formula on a variable.
    `UseN(man_N)` + `"q1"` → `qatom ⟨"man_N", [var "q1"]⟩` -/
def restrToFormula (restr : Pattern) (q : String) : QFormula2 :=
  .qatom ⟨extractNounName restr, [.var q]⟩

example : restrToFormula (.apply "UseN" [.fvar "man_N"]) "q1" =
    .qatom ⟨"man_N", [.var "q1"]⟩ := by
  simp [restrToFormula, extractNounName]

/-! ## 3. Term → Body Formula -/

/-- Extract the body formula from a term with ⊛NPVar placeholders.

    Directly pattern-matches the common GF sentence structures:
    - Intransitive: `PredVP(⊛NPVar(q), UseV(v))` → `v(q)`
    - Transitive: `PredVP(⊛NPVar(q1), ComplSlash(SlashV2a(v), ⊛NPVar(q2)))` → `v(q1, q2)` -/
def termToBody (term : Pattern) : QFormula2 :=
  match term with
  -- Intransitive: PredVP(⊛NPVar(q1), UseV(walk_V)) → walk_V(q1)
  | .apply "PredVP" [.apply "⊛NPVar" [.apply q []], .apply "UseV" [.fvar v]] =>
    .qatom ⟨v, [.var q]⟩
  -- Transitive: PredVP(⊛NPVar(q1), ComplSlash(SlashV2a(v), ⊛NPVar(q2))) → v(q1, q2)
  | .apply "PredVP" [.apply "⊛NPVar" [.apply q1 []],
      .apply "ComplSlash" [.apply "SlashV2a" [.fvar v],
                           .apply "⊛NPVar" [.apply q2 []]]] =>
    .qatom ⟨v, [.var q1, .var q2]⟩
  -- Copula: PredVP(⊛NPVar(q), UseComp(CompAP(PositA(adj)))) → adj(q)
  | .apply "PredVP" [.apply "⊛NPVar" [.apply q []],
      .apply "UseComp" [.apply "CompAP" [.apply "PositA" [.fvar adj]]]] =>
    .qatom ⟨adj, [.var q]⟩
  -- Passive: PredVP(⊛NPVar(q), PassV2(v)) → v_passive(q)
  | .apply "PredVP" [.apply "⊛NPVar" [.apply q []], .apply "PassV2" [.fvar v]] =>
    .qatom ⟨v ++ "_passive", [.var q]⟩
  -- Ditransitive: PredVP(⊛NPVar(q1), ComplSlash(Slash2V3(v, ⊛NPVar(q2)), ⊛NPVar(q3))) → v(q1,q2,q3)
  | .apply "PredVP" [.apply "⊛NPVar" [.apply q1 []],
      .apply "ComplSlash" [.apply "Slash2V3" [.fvar v, .apply "⊛NPVar" [.apply q2 []]],
                           .apply "⊛NPVar" [.apply q3 []]]] =>
    .qatom ⟨v, [.var q1, .var q2, .var q3]⟩
  -- Ditransitive (indirect-first): PredVP(⊛NPVar(q1), ComplSlash(Slash3V3(v, ⊛NPVar(q3)), ⊛NPVar(q2)))
  --   → v(q1, q2, q3) with q3 = indirect object saturated first
  | .apply "PredVP" [.apply "⊛NPVar" [.apply q1 []],
      .apply "ComplSlash" [.apply "Slash3V3" [.fvar v, .apply "⊛NPVar" [.apply q3 []]],
                           .apply "⊛NPVar" [.apply q2 []]]] =>
    .qatom ⟨v, [.var q1, .var q2, .var q3]⟩
  -- Copula NP: PredVP(⊛NPVar(q1), UseComp(CompNP(⊛NPVar(q2)))) → copula(q1, q2)
  | .apply "PredVP" [.apply "⊛NPVar" [.apply q1 []],
      .apply "UseComp" [.apply "CompNP" [.apply "⊛NPVar" [.apply q2 []]]]] =>
    .qatom ⟨"copula", [.var q1, .var q2]⟩
  -- Adverbial VP: PredVP(⊛NPVar(q), AdvVP(UseV(v), _)) → v(q)
  --   Adverb ignored; captures "q walks quickly", "q runs in the park", etc.
  | .apply "PredVP" [.apply "⊛NPVar" [.apply q []], .apply "AdvVP" [.apply "UseV" [.fvar v], _]] =>
    .qatom ⟨v, [.var q]⟩
  | _ => .top  -- fallback for other structures

/-! ## 4. Quantifier Wrapping -/

/-- Wrap a quantifier around a body formula.
    - Universal: `∀q. restr(q) → body`
    - Existential: `∃q. restr(q) ∧ body` -/
def wrapQuantifier (det restr : Pattern) (q : String) (body : QFormula2) : QFormula2 :=
  let restrF := restrToFormula restr q
  if isUniversalDet det then
    .qforall q (.qimp restrF body)
  else
    .qexists q (.qand restrF body)

-- ∀q1. man_N(q1) → body
example : wrapQuantifier (.fvar "every_Det") (.apply "UseN" [.fvar "man_N"])
    "q1" .top =
    .qforall "q1" (.qimp (.qatom ⟨"man_N", [.var "q1"]⟩) .top) := by
  simp [wrapQuantifier, isUniversalDet, restrToFormula, extractNounName]

-- ∃q2. woman_N(q2) ∧ body
example : wrapQuantifier (.fvar "someSg_Det") (.apply "UseN" [.fvar "woman_N"])
    "q2" .top =
    .qexists "q2" (.qand (.qatom ⟨"woman_N", [.var "q2"]⟩) .top) := by
  simp [wrapQuantifier, isUniversalDet, restrToFormula, extractNounName]

/-! ## 5. Full Assembly -/

/-- A quantifier entry: handle name, determiner pattern, restrictor pattern. -/
abbrev QuantEntry := String × Pattern × Pattern

/-- Assemble a QFormula2 from an ordered list of quantifier entries and a body.
    Outermost quantifier comes first in the list. -/
def assembleFromQuants (quants : List QuantEntry) (body : QFormula2) : QFormula2 :=
  quants.foldr (fun ⟨q, det, restr⟩ acc => wrapQuantifier det restr q acc) body

/-- Assemble a QFormula2 from a grammar state with explicitly ordered quantifiers.

    This is the computable core: given a scope-ordered list of quantifier entries
    (outermost first) and a grammar state, produce the logical form.

    Callers provide the quantifier ordering; this function handles body extraction
    and quantifier wrapping. -/
def storeToQFormula2_ordered (quants : List QuantEntry) (s : GrammarState) : QFormula2 :=
  assembleFromQuants quants (termToBody s.term)

/-! ## 6. Concrete Assembly Helpers

For worked examples, we provide computable helpers that extract quantifier entries
from concrete stores without going through `Multiset.toList` (which is noncomputable). -/

/-- Single-quantifier extraction from a store known to have exactly one quant atom. -/
def singleQuantEntry (q : String) (det restr : Pattern) : List QuantEntry := [(q, det, restr)]

/-- Two-quantifier extraction with explicit scope ordering.
    `outerFirst = true` means q1 scopes over q2. -/
def twoQuantEntries (q1 : String) (d1 r1 : Pattern)
    (q2 : String) (d2 r2 : Pattern) (outerFirst : Bool) : List QuantEntry :=
  if outerFirst then [(q1, d1, r1), (q2, d2, r2)]
  else [(q2, d2, r2), (q1, d1, r1)]

/-! ## 7. Closedness

Closedness is verified concretely for each example assembly. The key insight:
`wrapQuantifier det restr q body` binds `q`, so if `body`'s only free variable
is `q` and the restrictor introduces no new free variables, the result is closed. -/

/-- Concrete closedness: "every man walks" formula is closed. -/
example : closedQF2
    (wrapQuantifier (.fvar "every_Det") (.apply "UseN" [.fvar "man_N"]) "q1"
      (.qatom ⟨"walk_V", [.var "q1"]⟩)) := by
  simp [closedQF2, wrapQuantifier, isUniversalDet, restrToFormula, extractNounName,
        freeVarsQF2, freeVarsAtom, freeVarsTerms, freeVarsTerm]

/-- Concrete closedness: "a woman" existential wrapping is closed
    when body only mentions q2. -/
example : closedQF2
    (wrapQuantifier (.fvar "someSg_Det") (.apply "UseN" [.fvar "woman_N"]) "q2"
      (.qatom ⟨"love_V2", [.var "q2"]⟩)) := by
  simp [closedQF2, wrapQuantifier, isUniversalDet, restrToFormula, extractNounName,
        freeVarsQF2, freeVarsAtom, freeVarsTerms, freeVarsTerm]

/-! ## 8. termToBody Verification -/

/-- Copula: "the cat is big" → PredVP(⊛NPVar(q1), UseComp(CompAP(PositA(big_A)))) → big_A(q1) -/
example : termToBody
    (.apply "PredVP" [npVar "q1",
      .apply "UseComp" [.apply "CompAP" [.apply "PositA" [.fvar "big_A"]]]]) =
    .qatom ⟨"big_A", [.var "q1"]⟩ := rfl

/-- Passive: "the book is read" → PredVP(⊛NPVar(q1), PassV2(read_V2)) → read_V2_passive(q1) -/
example : termToBody
    (.apply "PredVP" [npVar "q1", .apply "PassV2" [.fvar "read_V2"]]) =
    .qatom ⟨"read_V2_passive", [.var "q1"]⟩ := rfl

/-- Ditransitive: "q1 gives q2 to q3" →
    PredVP(⊛NPVar(q1), ComplSlash(Slash2V3(give_V3, ⊛NPVar(q2)), ⊛NPVar(q3))) → give_V3(q1,q2,q3) -/
example : termToBody
    (.apply "PredVP" [npVar "q1",
      .apply "ComplSlash" [.apply "Slash2V3" [.fvar "give_V3", npVar "q2"],
                           npVar "q3"]]) =
    .qatom ⟨"give_V3", [.var "q1", .var "q2", .var "q3"]⟩ := rfl

/-- Ditransitive (indirect-first): "q1 sends q2 to q3" via Slash3V3 →
    PredVP(⊛NPVar(q1), ComplSlash(Slash3V3(send_V3, ⊛NPVar(q3)), ⊛NPVar(q2))) → send_V3(q1,q2,q3) -/
example : termToBody
    (.apply "PredVP" [npVar "q1",
      .apply "ComplSlash" [.apply "Slash3V3" [.fvar "send_V3", npVar "q3"],
                           npVar "q2"]]) =
    .qatom ⟨"send_V3", [.var "q1", .var "q2", .var "q3"]⟩ := rfl

/-- Copula NP: "John is a teacher" →
    PredVP(⊛NPVar(q1), UseComp(CompNP(⊛NPVar(q2)))) → copula(q1, q2) -/
example : termToBody
    (.apply "PredVP" [npVar "q1",
      .apply "UseComp" [.apply "CompNP" [npVar "q2"]]]) =
    .qatom ⟨"copula", [.var "q1", .var "q2"]⟩ := rfl

/-- Adverbial VP: "every man walks quickly" →
    PredVP(⊛NPVar(q1), AdvVP(UseV(walk_V), PositAdvAdj(quick_A))) → walk_V(q1) -/
example : termToBody
    (.apply "PredVP" [npVar "q1",
      .apply "AdvVP" [.apply "UseV" [.fvar "walk_V"],
                      .apply "PositAdvAdj" [.fvar "quick_A"]]]) =
    .qatom ⟨"walk_V", [.var "q1"]⟩ := rfl

/-! ## 9. Auto-Assembly from Store

Noncomputable extraction of quantifier entries from a multiset store.
The key definition `storeToQFormula2` composes extraction + scope ordering
+ body extraction + quantifier wrapping into a single pipeline. -/

/-- Extract all quantifier entries from a store (order depends on `Multiset.toList`). -/
noncomputable def extractQuantEntries (store : Multiset StoreAtom) : List QuantEntry :=
  store.toList.filterMap fun a => match a with
    | .quant q det restr => some (q, det, restr)
    | _ => none

/-- Scope ordering relation on quantifier entries: `e1` precedes `e2` if
    `scope e1.name e2.name ∈ store`. -/
def scopeRel (store : Multiset StoreAtom) : QuantEntry → QuantEntry → Prop :=
  fun ⟨q1, _, _⟩ ⟨q2, _, _⟩ => StoreAtom.scope q1 q2 ∈ store

instance scopeRel_decidable (store : Multiset StoreAtom) : DecidableRel (scopeRel store) :=
  fun ⟨q1, _, _⟩ ⟨q2, _, _⟩ => inferInstanceAs (Decidable (StoreAtom.scope q1 q2 ∈ store))

/-- Sort quantifier entries by scope atoms: if `scope q1 q2 ∈ store`,
    then `q1` comes before `q2` (outermost first). -/
noncomputable def scopeOrderedQuants (store : Multiset StoreAtom) : List QuantEntry :=
  (extractQuantEntries store).insertionSort (scopeRel store)

/-- Full noncomputable pipeline: extract quantifiers, order by scope, assemble formula. -/
noncomputable def storeToQFormula2 (s : GrammarState) : QFormula2 :=
  assembleFromQuants (scopeOrderedQuants s.store) (termToBody s.term)

/-! ## 10. Specification Theorems

These theorems verify that `scopeOrderedQuants` agrees with manual helpers
on concrete store shapes. We reason about `Multiset` membership without
unfolding the noncomputable `toList`. -/

/-- For a singleton quant store, `extractQuantEntries` yields exactly one entry. -/
theorem extractQuantEntries_singleton (q : String) (det restr : Pattern) :
    extractQuantEntries {StoreAtom.quant q det restr} = [(q, det, restr)] := by
  simp [extractQuantEntries, Multiset.toList_singleton]

/-- For a singleton quant store, scope ordering is trivial (one element). -/
theorem scopeOrderedQuants_singleton (q : String) (det restr : Pattern) :
    scopeOrderedQuants {StoreAtom.quant q det restr} = [(q, det, restr)] := by
  simp [scopeOrderedQuants, extractQuantEntries_singleton]

/-- Single-quantifier specification: `storeToQFormula2` agrees with `singleQuantEntry`
    when the store has exactly one quant atom (plus any non-quant atoms). -/
theorem storeToQFormula2_single_spec
    (q : String) (det restr : Pattern) (term : Pattern) :
    let s : GrammarState := ⟨term, {StoreAtom.quant q det restr}⟩
    storeToQFormula2 s = storeToQFormula2_ordered (singleQuantEntry q det restr) s := by
  simp only [storeToQFormula2, storeToQFormula2_ordered, singleQuantEntry]
  rw [scopeOrderedQuants_singleton]

/-! ## 11. Two-Quantifier Specification -/

/-- Helper: `toList` of a multiset gives a permutation of any concrete representative. -/
private theorem toList_perm_of_coe {α : Type*} (l : List α) :
    (↑l : Multiset α).toList.Perm l :=
  Multiset.coe_eq_coe.mp (Multiset.coe_toList _)

/-- Helper: a permutation of a 2-element list must be one of two orderings. -/
private theorem perm_two_cases {α : Type*} [DecidableEq α] (a b x y : α)
    (h : [x, y].Perm [a, b]) :
    (x = a ∧ y = b) ∨ (x = b ∧ y = a) := by
  have hx : x ∈ [a, b] := h.subset (by simp)
  have hy : y ∈ [a, b] := h.subset (by simp)
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx hy
  by_cases hxa : x = a
  · subst hxa
    by_cases hyb : y = b
    · exact Or.inl ⟨rfl, hyb⟩
    · have hya := hy.resolve_right hyb; subst hya
      have hc := h.count_eq b; simp [List.count_cons, List.count_nil] at hc
      exact Or.inl ⟨rfl, hc⟩
  · have hxb := hx.resolve_left hxa; subst hxb
    by_cases hya : y = a
    · exact Or.inr ⟨rfl, hya⟩
    · have hyb := hy.resolve_left hya; subst hyb
      have hc := h.count_eq a; simp [List.count_cons, List.count_nil] at hc
      exact Or.inr ⟨rfl, hc⟩

/-- For a store with two quant atoms and one scope atom, `extractQuantEntries`
    yields a permutation of the two entries. -/
theorem extractQuantEntries_two (q1 : String) (d1 r1 : Pattern)
    (q2 : String) (d2 r2 : Pattern) :
    let store := ({StoreAtom.quant q1 d1 r1, StoreAtom.quant q2 d2 r2,
                   StoreAtom.scope q1 q2} : Multiset StoreAtom)
    (extractQuantEntries store).Perm [(q1, d1, r1), (q2, d2, r2)] := by
  show (Multiset.toList _).filterMap _ |>.Perm _
  have hperm := toList_perm_of_coe [StoreAtom.quant q1 d1 r1,
    StoreAtom.quant q2 d2 r2, StoreAtom.scope q1 q2]
  have hfm := hperm.filterMap (fun a => match a with
    | .quant q det restr => some (q, det, restr) | _ => none)
  simp only [List.filterMap_cons, List.filterMap_nil] at hfm
  exact hfm

/-- Two-quantifier specification: `scopeOrderedQuants` with `scope q1 q2` in the store
    produces `[(q1, d1, r1), (q2, d2, r2)]` (surface scope, q1 outermost).

    Requires: `scope q1 q2 ∈ store` and `scope q2 q1 ∉ store`. -/
theorem scopeOrderedQuants_two_surface_spec
    (q1 : String) (d1 r1 : Pattern) (q2 : String) (d2 r2 : Pattern)
    (hscope : StoreAtom.scope q1 q2 ∈
      ({StoreAtom.quant q1 d1 r1, StoreAtom.quant q2 d2 r2,
        StoreAtom.scope q1 q2} : Multiset StoreAtom))
    (hno_rev : StoreAtom.scope q2 q1 ∉
      ({StoreAtom.quant q1 d1 r1, StoreAtom.quant q2 d2 r2,
        StoreAtom.scope q1 q2} : Multiset StoreAtom)) :
    let store := ({StoreAtom.quant q1 d1 r1, StoreAtom.quant q2 d2 r2,
                   StoreAtom.scope q1 q2} : Multiset StoreAtom)
    scopeOrderedQuants store = [(q1, d1, r1), (q2, d2, r2)] := by
  intro store
  simp only [scopeOrderedQuants]
  have hperm := extractQuantEntries_two q1 d1 r1 q2 d2 r2
  have hlen : (extractQuantEntries store).length = 2 := hperm.length_eq ▸ rfl
  obtain ⟨e1, e2, heq⟩ : ∃ e1 e2, extractQuantEntries store = [e1, e2] := by
    match extractQuantEntries store, hlen with | [e1, e2], _ => exact ⟨e1, e2, rfl⟩
  rw [heq]
  have hperm2 : [e1, e2].Perm [(q1, d1, r1), (q2, d2, r2)] := heq ▸ hperm
  rcases perm_two_cases _ _ _ _ hperm2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- e1 = (q1,...), e2 = (q2,...): scope q1 q2 ∈ store → sorted already
    subst h1; subst h2
    unfold List.insertionSort
    simp only [List.foldr_cons, List.foldr_nil, List.orderedInsert]
    rw [if_pos (show scopeRel store (q1, d1, r1) (q2, d2, r2) from hscope)]
  · -- e1 = (q2,...), e2 = (q1,...): ¬scope q2 q1 ∈ store → swap
    subst h1; subst h2
    unfold List.insertionSort
    simp only [List.foldr_cons, List.foldr_nil, List.orderedInsert]
    rw [if_neg (show ¬ scopeRel store (q2, d2, r2) (q1, d1, r1) from hno_rev)]

end Mettapedia.Languages.GF.StoreToLogicalForm
