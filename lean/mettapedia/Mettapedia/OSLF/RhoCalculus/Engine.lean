import Mettapedia.OSLF.RhoCalculus.Reduction
import Mettapedia.OSLF.MeTTaIL.Substitution

/-!
# Executable ρ-Calculus Rewrite Engine (Locally Nameless)

An executable (computable) rewrite engine for the ρ-calculus, proven sound
with respect to the propositional `Reduces` relation from `Reduction.lean`.

## Architecture

The engine handles three reduction rules:
- **COMM**: `{n!(q) | for(<-n){p} | ...rest} ⇝ {commSubst p q | ...rest}`
- **DROP**: `*(@p) ⇝ p`
- **PAR**: recursive reduction inside parallel compositions

In locally nameless, input patterns are `PInput [n, lambda body]` where
BVar 0 is the bound variable. No binder name is stored or matched.

## References

- Meredith & Radestock, "A Reflective Higher-Order Calculus"
- mettail-rust: `macros/src/logic/rules.rs`
-/

namespace Mettapedia.OSLF.RhoCalculus.Engine

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.RhoCalculus.Reduction

/-! ## COMM Redex Detection -/

/-- Extract an output on channel `n`: match `POutput [n, q]` and return `(n, q)`. -/
def matchOutput (p : Pattern) : Option (Pattern × Pattern) :=
  match p with
  | .apply "POutput" [n, q] => some (n, q)
  | _ => none

/-- Extract an input on channel `n`: match `PInput [n, lambda body]`
    and return `(n, body)`. In locally nameless, no binder name is stored. -/
def matchInput (p : Pattern) : Option (Pattern × Pattern) :=
  match p with
  | .apply "PInput" [n, .lambda body] => some (n, body)
  | _ => none

/-- Try to find a COMM partner for an output `(n, q)` in a list of elements.
    Returns `(index, body)` if an input on the same channel is found. -/
def findInputPartner (n : Pattern) (elems : List Pattern) : List (Nat × Pattern) :=
  elems.zipIdx.filterMap fun (elem, i) =>
    match matchInput elem with
    | some (n', body) => if n == n' then some (i, body) else none
    | none => none

/-- Find all COMM reducts in a bag.

    For each output `n!(q)` at position `i`, and each input `for(<-n){p}` at
    position `j` (with `i ≠ j`), produce the reduct `{commSubst p q | rest}`.
-/
def findAllComm (elems : List Pattern) : List Pattern :=
  (elems.zipIdx.map fun (elem, i) =>
    match matchOutput elem with
    | none => []
    | some (n, q) =>
      let withoutOutput := elems.eraseIdx i
      let partners := findInputPartner n withoutOutput
      partners.map fun (j, body) =>
        let rest := withoutOutput.eraseIdx j
        .collection .hashBag ([commSubst body q] ++ rest) none).flatten

/-! ## DROP Redex Detection -/

/-- Match a DROP redex: `*(@p)` = `PDrop [NQuote [p]]`. Returns the inner process. -/
def matchDrop (p : Pattern) : Option Pattern :=
  match p with
  | .apply "PDrop" [.apply "NQuote" [inner]] => some inner
  | _ => none

/-! ## One-Step Reduction -/

/-- Reduce all elements of a list, returning `(index, reduct)` pairs. -/
private def reduceElemsAux (reduceStep : Pattern → List Pattern)
    (elems : List Pattern) : List (Nat × Pattern) :=
  (elems.zipIdx.map fun (elem, i) =>
    (reduceStep elem).map fun r => (i, r)).flatten

/-- Specification of `reduceElemsAux`: if `(idx, elem')` is in the result,
    then `idx` is a valid index and `elem'` is a reduct of `elems[idx]`. -/
private theorem reduceElemsAux_spec {f : Pattern → List Pattern} {elems : List Pattern}
    {idx : Nat} {elem' : Pattern}
    (h : (idx, elem') ∈ reduceElemsAux f elems) :
    ∃ (_ : idx < elems.length), elem' ∈ f (elems[idx]) := by
  unfold reduceElemsAux at h
  rw [List.mem_flatten] at h
  obtain ⟨sublist, hsl_mem, h_in_sl⟩ := h
  rw [List.mem_map] at hsl_mem
  obtain ⟨⟨elem, i⟩, hzip, rfl⟩ := hsl_mem
  rw [List.mem_map] at h_in_sl
  obtain ⟨r, hr_mem, hprod⟩ := h_in_sl
  simp only [Prod.mk.injEq] at hprod
  obtain ⟨rfl, rfl⟩ := hprod
  have hzi := List.mem_zipIdx hzip
  obtain ⟨_, hi_lt, helem_eq⟩ := hzi
  simp at hi_lt helem_eq
  exact ⟨hi_lt, helem_eq ▸ hr_mem⟩

/-- Compute all one-step reducts of a pattern. -/
def reduceStep (p : Pattern) (fuel : Nat := 100) : List Pattern :=
  match fuel with
  | 0 => []
  | fuel + 1 =>
    match p with
    | .collection .hashBag elems none =>
      let commReducts := findAllComm elems
      let parReducts := reduceElemsAux (reduceStep · fuel) elems |>.map fun (i, elem') =>
        .collection .hashBag (elems.set i elem') none
      commReducts ++ parReducts
    | .collection .hashSet elems none =>
      reduceElemsAux (reduceStep · fuel) elems |>.map fun (i, elem') =>
        .collection .hashSet (elems.set i elem') none
    | .apply "PDrop" [.apply "NQuote" [inner]] =>
      [inner]
    | _ => []

/-- Reduce to normal form using a deterministic strategy (pick first reduct). -/
def reduceToNormalForm (p : Pattern) (fuel : Nat := 1000) : Pattern :=
  match fuel with
  | 0 => p
  | fuel + 1 =>
    match reduceStep p with
    | [] => p
    | q :: _ => reduceToNormalForm q fuel

/-- Reduce exhaustively: collect all reachable normal forms (BFS with fuel). -/
def reduceAll (p : Pattern) (fuel : Nat := 100) : List Pattern :=
  go [p] [] fuel
where
  go (worklist done : List Pattern) (fuel : Nat) : List Pattern :=
    match fuel with
    | 0 => done ++ worklist
    | fuel + 1 =>
      match worklist with
      | [] => done
      | p :: rest =>
        match reduceStep p with
        | [] => go rest (p :: done) fuel
        | reducts => go (reducts ++ rest) done fuel

/-! ## Soundness -/

/-- matchOutput specification -/
private theorem matchOutput_spec {p n q : Pattern}
    (h : matchOutput p = some (n, q)) : p = .apply "POutput" [n, q] := by
  unfold matchOutput at h; split at h <;> simp_all

/-- matchInput specification (locally nameless: returns channel and body, no binder name) -/
private theorem matchInput_spec {p : Pattern} {n : Pattern} {body : Pattern}
    (h : matchInput p = some (n, body)) : p = .apply "PInput" [n, .lambda body] := by
  unfold matchInput at h; split at h <;> simp_all

/-- findInputPartner specification -/
private theorem findInputPartner_spec {n : Pattern} {elems : List Pattern}
    {j : Nat} {body : Pattern}
    (h : (j, body) ∈ findInputPartner n elems) :
    ∃ (hj : j < elems.length), elems[j] = .apply "PInput" [n, .lambda body] := by
  unfold findInputPartner at h
  rw [List.mem_filterMap] at h
  obtain ⟨⟨elem, k⟩, hmem, hfilt⟩ := h
  have hzip := List.mem_zipIdx hmem
  obtain ⟨_, hk_len, helem_eq⟩ := hzip
  simp only at hfilt
  split at hfilt
  · next n' body' heq_mi =>
    split at hfilt
    · next hbeq =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hfilt
      obtain ⟨hj_eq, hbody_eq⟩ := hfilt
      subst hj_eq; subst hbody_eq
      rw [beq_iff_eq] at hbeq
      subst hbeq
      have hk_lt : k < elems.length := by omega
      have helem_eq' : elem = elems[k] := by simp at helem_eq; exact helem_eq
      refine ⟨hk_lt, ?_⟩
      rw [← helem_eq']
      exact matchInput_spec heq_mi
    · simp at hfilt
  · simp at hfilt

/-- Helper: extracting two elements at positions i,j from a list gives a permutation. -/
private theorem perm_extract_two (elems : List Pattern) (i : Nat) (j : Nat)
    (hi : i < elems.length)
    (hj : j < (elems.eraseIdx i).length) :
    elems.Perm ([elems[i], (elems.eraseIdx i)[j]] ++ (elems.eraseIdx i).eraseIdx j) := by
  have h1 := (List.getElem_cons_eraseIdx_perm hi).symm
  have h2 := (List.getElem_cons_eraseIdx_perm hj).symm
  exact h1.trans (h2.cons _)

open StructuralCongruence in
/-- COMM soundness at specific positions -/
private theorem comm_at_positions (elems : List Pattern) (i : Nat) (j : Nat)
    (n q : Pattern) (body : Pattern)
    (hi : i < elems.length)
    (hj : j < (elems.eraseIdx i).length)
    (hout : elems[i] = .apply "POutput" [n, q])
    (hinp : (elems.eraseIdx i)[j] = .apply "PInput" [n, .lambda body]) :
    Nonempty (Reduces (.collection .hashBag elems none)
      (.collection .hashBag ([commSubst body q] ++ (elems.eraseIdx i).eraseIdx j) none)) := by
  have hperm := perm_extract_two elems i j hi hj
  rw [hout, hinp] at hperm
  have hsc1 := StructuralCongruence.par_perm elems _ hperm
  have hcomm := @Reduces.comm n q body ((elems.eraseIdx i).eraseIdx j)
  exact ⟨Reduces.equiv hsc1 hcomm (StructuralCongruence.refl _)⟩

/-- findAllComm specification -/
private theorem findAllComm_spec {elems : List Pattern} {r : Pattern}
    (hr : r ∈ findAllComm elems) :
    ∃ (i : Nat) (hi : i < elems.length) (j : Nat) (hj : j < (elems.eraseIdx i).length)
      (n q : Pattern) (body : Pattern),
      elems[i] = .apply "POutput" [n, q] ∧
      (elems.eraseIdx i)[j] = .apply "PInput" [n, .lambda body] ∧
      r = .collection .hashBag ([commSubst body q] ++ (elems.eraseIdx i).eraseIdx j) none := by
  unfold findAllComm at hr
  rw [List.mem_flatten] at hr
  obtain ⟨sublist, hsl_mem, hr_in_sl⟩ := hr
  rw [List.mem_map] at hsl_mem
  obtain ⟨⟨elem, i⟩, hzip, rfl⟩ := hsl_mem
  have hzi := List.mem_zipIdx hzip
  obtain ⟨_, hi_lt, helem_eq⟩ := hzi
  simp at hi_lt helem_eq
  simp only at hr_in_sl
  split at hr_in_sl
  · simp at hr_in_sl
  · next n q hmatch =>
    rw [List.mem_map] at hr_in_sl
    obtain ⟨⟨j, body⟩, hpartner, rfl⟩ := hr_in_sl
    refine ⟨i, hi_lt, j, ?_, n, q, body, ?_, ?_, rfl⟩
    · exact (findInputPartner_spec hpartner).choose
    · rw [helem_eq] at hmatch; exact matchOutput_spec hmatch
    · exact (findInputPartner_spec hpartner).choose_spec

/-- Soundness of `findAllComm` -/
private theorem findAllComm_sound (elems : List Pattern)
    (r : Pattern) (hr : r ∈ findAllComm elems) :
    Nonempty (Reduces (.collection .hashBag elems none) r) := by
  obtain ⟨i, hi, j, hj, n, q, body, hout, hinp, rfl⟩ := findAllComm_spec hr
  exact comm_at_positions elems i j n q body hi hj hout hinp

/-- Soundness of `reduceStep`: every reduct is a valid `Reduces`. -/
theorem reduceStep_sound (p q : Pattern) (fuel : Nat)
    (h : q ∈ reduceStep p fuel) : Nonempty (p ⇝ q) := by
  match fuel, p with
  | 0, _ => simp [reduceStep] at h
  | _ + 1, .apply "PDrop" [.apply "NQuote" [inner]] =>
    simp [reduceStep] at h
    exact h ▸ ⟨Reduces.drop⟩
  | fuel + 1, .collection .hashBag elems none =>
    simp only [reduceStep, List.mem_append] at h
    rcases h with hcomm | hpar
    · exact findAllComm_sound elems q hcomm
    · simp only [List.mem_map] at hpar
      obtain ⟨⟨idx, elem'⟩, hmem_aux, hq_eq⟩ := hpar
      subst hq_eq
      obtain ⟨hidx, helem_mem⟩ := reduceElemsAux_spec hmem_aux
      have hred := reduceStep_sound (elems[idx]) elem' fuel helem_mem
      obtain ⟨hred⟩ := hred
      have hdecomp : elems = elems.take idx ++ [elems[idx]] ++ elems.drop (idx + 1) := by
        simp [List.take_append_drop]
      have hset : elems.set idx elem' = elems.take idx ++ [elem'] ++ elems.drop (idx + 1) := by
        simp [List.set_eq_take_append_cons_drop, hidx]
      have h := Reduces.par_any (before := elems.take idx) (after := elems.drop (idx + 1)) hred
      rw [← hdecomp, ← hset] at h
      exact ⟨h⟩
  | fuel + 1, .collection .hashSet elems none =>
    simp only [reduceStep, List.mem_map] at h
    obtain ⟨⟨idx, elem'⟩, hmem_aux, hq_eq⟩ := h
    subst hq_eq
    obtain ⟨hidx, helem_mem⟩ := reduceElemsAux_spec hmem_aux
    have hred := reduceStep_sound (elems[idx]) elem' fuel helem_mem
    obtain ⟨hred⟩ := hred
    have hdecomp : elems = elems.take idx ++ [elems[idx]] ++ elems.drop (idx + 1) := by
      simp [List.take_append_drop]
    have hset : elems.set idx elem' = elems.take idx ++ [elem'] ++ elems.drop (idx + 1) := by
      simp [List.set_eq_take_append_cons_drop, hidx]
    have h := Reduces.par_set_any (before := elems.take idx) (after := elems.drop (idx + 1)) hred
    rw [← hdecomp, ← hset] at h
    exact ⟨h⟩
  | _ + 1, .bvar _ => simp [reduceStep] at h
  | _ + 1, .fvar _ => simp [reduceStep] at h
  | _ + 1, .lambda _ => simp [reduceStep] at h
  | _ + 1, .multiLambda _ _ => simp [reduceStep] at h
  | _ + 1, .subst _ _ => simp [reduceStep] at h
  | _ + 1, .collection _ _ (some _) => simp [reduceStep] at h
  | _ + 1, .collection .vec _ none => simp [reduceStep] at h
  | n + 1, .apply c args =>
    simp only [reduceStep] at h
    split at h
    · exact absurd ‹Pattern.apply c args = _› (by intro h; cases h)
    · exact absurd ‹Pattern.apply c args = _› (by intro h; cases h)
    · next inner heq =>
      have := Pattern.apply.inj heq
      obtain ⟨rfl, rfl⟩ := this
      simp only [List.mem_singleton] at h
      exact h ▸ ⟨Reduces.drop⟩
    · simp at h

/-! ## Pretty Printing -/

/-- Simple string representation of a Pattern for debugging. -/
partial def patternToString : Pattern → String
  | .fvar name => name
  | .bvar n => s!"#{n}"
  | .apply "PZero" [] => "0"
  | .apply "PDrop" [n] =>
    let ns := patternToString n
    s!"*({ns})"
  | .apply "NQuote" [p] =>
    let ps := patternToString p
    s!"@({ps})"
  | .apply "POutput" [n, q] =>
    let ns := patternToString n
    let qs := patternToString q
    s!"{ns}!({qs})"
  | .apply "PInput" [n, .lambda body] =>
    let ns := patternToString n
    let bs := patternToString body
    ns ++ "?" ++ "." ++ "{" ++ bs ++ "}"
  | .apply c args =>
    let argsStr := args.map patternToString |>.intersperse ", " |> String.join
    s!"{c}({argsStr})"
  | .lambda body =>
    let bs := patternToString body
    "λ." ++ bs
  | .multiLambda n body =>
    let bs := patternToString body
    "λ[" ++ toString n ++ "]." ++ bs
  | .subst body repl =>
    let bs := patternToString body
    let rs := patternToString repl
    bs ++ "[" ++ rs ++ "/0]"
  | .collection ct elems rest =>
    let sep := match ct with | .hashBag => " | " | .hashSet => ", " | .vec => "; "
    let elemsStr := elems.map patternToString |>.intersperse sep |> String.join
    let restStr : String := match rest with
      | some rp => sep ++ "..." ++ rp
      | none => ""
    "{" ++ elemsStr ++ restStr ++ "}"

instance : ToString Pattern := ⟨patternToString⟩

/-! ## Executable Tests -/

-- Helper: create common patterns
private def pzero : Pattern := .apply "PZero" []
private def pdrop (n : Pattern) : Pattern := .apply "PDrop" [n]
private def nquote (p : Pattern) : Pattern := .apply "NQuote" [p]
private def poutput (n q : Pattern) : Pattern := .apply "POutput" [n, q]
private def pinput (n : Pattern) (body : Pattern) : Pattern :=
  .apply "PInput" [n, .lambda body]
private def ppar (elems : List Pattern) : Pattern :=
  .collection .hashBag elems none

-- Test 1: COMM — x!(0) | for(<-x){#0} should reduce
-- In LN, the input body has BVar 0 for the bound variable
#eval! do
  let x := Pattern.fvar "x"
  let term := ppar [poutput x pzero, pinput x (.bvar 0)]
  let reducts := reduceStep term
  IO.println s!"COMM test: {term}"
  IO.println s!"  reducts ({reducts.length}):"
  for r in reducts do
    IO.println s!"    → {r}"

-- Test 2: DROP — *(@0) should reduce to 0
#eval! do
  let term := pdrop (nquote pzero)
  let reducts := reduceStep term
  IO.println s!"DROP test: {term}"
  IO.println s!"  reducts ({reducts.length}):"
  for r in reducts do
    IO.println s!"    → {r}"

-- Test 3: Race — two inputs competing
#eval! do
  let x := Pattern.fvar "x"
  let term := ppar [
    poutput x pzero,
    pinput x (.bvar 0),            -- for(<-x){#0} : identity input
    pinput x (pdrop (.bvar 0))     -- for(<-x){*(#0)} : deref input
  ]
  let reducts := reduceStep term
  IO.println s!"Race test: {term}"
  IO.println s!"  reducts ({reducts.length}):"
  for r in reducts do
    IO.println s!"    → {r}"

-- Test 4: Normal form — 0 has no reducts
#eval! do
  let reducts := reduceStep pzero
  IO.println s!"Normal form test: 0"
  IO.println s!"  reducts ({reducts.length}): {if reducts.isEmpty then "none (normal form)" else "unexpected!"}"

-- Test 5: Nested PAR — reduction inside a bag element
#eval! do
  let term := ppar [pdrop (nquote pzero), poutput (.fvar "x") pzero]
  let reducts := reduceStep term
  IO.println s!"Nested PAR test: {term}"
  IO.println s!"  reducts ({reducts.length}):"
  for r in reducts do
    IO.println s!"    → {r}"

-- Test 6: Multi-step — reduce to normal form
#eval! do
  let x := Pattern.fvar "x"
  let term := ppar [poutput x (pdrop (nquote pzero)), pinput x (pdrop (.bvar 0))]
  IO.println s!"Multi-step test: {term}"
  let result := reduceToNormalForm term
  IO.println s!"  normal form: {result}"

end Mettapedia.OSLF.RhoCalculus.Engine
