import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.SemanticSubstitution
import Mettapedia.OSLF.MeTTaIL.Substitution

/-!
# Executable ρ-Calculus Rewrite Engine (Locally Nameless)

An executable (computable) rewrite engine for the ρ-calculus, proven sound
with respect to the propositional `Reduces` relation from `Reduction.lean`.

## Architecture

The engine handles the paper-faithful core one-step semantics:
- **COMM**: `{n!(q) | for(<-n){p} | ...rest} ⇝ {semanticCommSubst p q | ...rest}`
- **PAR**: recursive reduction inside parallel compositions

In locally nameless, input patterns are `PInput [n, lambda body]` where
BVar 0 is the bound variable. No binder name is stored or matched.

## References

- Meredith & Radestock, "A Reflective Higher-Order Calculus"
- mettail-rust: `macros/src/logic/rules.rs`
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Engine

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction

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
  | .apply "PInput" [n, .lambda none body] => some (n, body)
  | _ => none

/-- Try to find a COMM partner for an output `(n, q)` in a list of elements.
    Returns `(index, body)` if an input on the same channel is found. -/
def findInputPartner (n : Pattern) (elems : List Pattern) : List (Nat × Pattern) :=
  elems.zipIdx.filterMap fun (elem, i) =>
    match matchInput elem with
    | some (n', body) =>
      if semanticNormalizeName n == semanticNormalizeName n' then
        some (i, body)
      else
        none
    | none => none

/-- Find all COMM reducts in a bag.

    For each output `n!(q)` at position `i`, and each input `for(<-n){p}` at
    position `j` (with `i ≠ j`), produce the reduct `{semanticCommSubst p q | rest}`.
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
        .collection .hashBag ([semanticCommSubst body q] ++ rest) none).flatten

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

/-- Completeness companion to `reduceElemsAux_spec`: any reduct of `elems[idx]`
    appears in the indexed auxiliary frontier. -/
private theorem reduceElemsAux_mem {f : Pattern → List Pattern} {elems : List Pattern}
    {idx : Nat} {elem' : Pattern}
    (hidx : idx < elems.length)
    (h : elem' ∈ f (elems[idx])) :
    (idx, elem') ∈ reduceElemsAux f elems := by
  unfold reduceElemsAux
  rw [List.mem_flatten]
  refine ⟨(f (elems[idx])).map (fun r => (idx, r)), ?_, ?_⟩
  · rw [List.mem_map]
    refine ⟨(elems[idx], idx), ?_, rfl⟩
    rw [List.mk_mem_zipIdx_iff_getElem?]
    simp [List.getElem?_eq_getElem hidx]
  · rw [List.mem_map]
    exact ⟨elem', h, rfl⟩

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
    | _ => []

/-- Executable irreducibility canary for the empty bag. -/
theorem emptyBag_reduceStep_nil (fuel : Nat) :
    reduceStep (.collection .hashBag [] none) fuel = [] := by
  cases fuel with
  | zero => simp [reduceStep]
  | succ n =>
    simp [reduceStep, findAllComm, reduceElemsAux]

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
    (h : matchInput p = some (n, body)) : p = .apply "PInput" [n, .lambda none body] := by
  unfold matchInput at h; split at h <;> simp_all

/-- findInputPartner specification -/
private theorem findInputPartner_spec {n : Pattern} {elems : List Pattern}
    {j : Nat} {body : Pattern}
    (h : (j, body) ∈ findInputPartner n elems) :
    ∃ (n' : Pattern) (hj : j < elems.length),
      elems[j] = .apply "PInput" [n', .lambda none body] ∧
      semanticNormalizeName n = semanticNormalizeName n' := by
  unfold findInputPartner at h
  rw [List.mem_filterMap] at h
  obtain ⟨⟨elem, k⟩, hmem, hfilt⟩ := h
  have hzip := List.mem_zipIdx hmem
  obtain ⟨_, hk_len, helem_eq⟩ := hzip
  simp only at hfilt
  cases hmi : matchInput elem with
  | none =>
      simp [hmi] at hfilt
  | some pair =>
      rcases pair with ⟨n', body'⟩
      simp [hmi] at hfilt
      obtain ⟨hbeq, hj_eq, hbody_eq⟩ := hfilt
      subst hj_eq
      subst hbody_eq
      have hk_lt : k < elems.length := by omega
      have helem_eq' : elem = elems[k] := by
        simp at helem_eq
        exact helem_eq
      refine ⟨n', hk_lt, ?_, hbeq⟩
      rw [← helem_eq']
      exact matchInput_spec hmi

/-- Helper: extracting two elements at positions i,j from a list gives a permutation. -/
private theorem perm_extract_two (elems : List Pattern) (i : Nat) (j : Nat)
    (hi : i < elems.length)
    (hj : j < (elems.eraseIdx i).length) :
    elems.Perm ([elems[i], (elems.eraseIdx i)[j]] ++ (elems.eraseIdx i).eraseIdx j) := by
  have h1 := (List.getElem_cons_eraseIdx_perm hi).symm
  have h2 := (List.getElem_cons_eraseIdx_perm hj).symm
  exact h1.trans (h2.cons _)

private theorem struct_output_cong_channel {n n' q : Pattern}
    (hn : StructuralCongruence n n') :
    StructuralCongruence (.apply "POutput" [n, q]) (.apply "POutput" [n', q]) := by
  refine StructuralCongruence.apply_cong "POutput" [n, q] [n', q] rfl ?_
  intro i h₁ h₂
  have hi_lt : i < 2 := by simpa using h₁
  have hi : i = 0 ∨ i = 1 := by omega
  cases hi with
  | inl hi0 =>
      subst hi0
      simpa using hn
  | inr hi1 =>
      subst hi1
      simpa using StructuralCongruence.refl q

private theorem struct_input_cong_channel {n n' body : Pattern}
    (hn : StructuralCongruence n n') :
    StructuralCongruence
      (.apply "PInput" [n, .lambda none body])
      (.apply "PInput" [n', .lambda none body]) := by
  refine StructuralCongruence.apply_cong "PInput"
    [n, .lambda none body] [n', .lambda none body] rfl ?_
  intro i h₁ h₂
  have hi_lt : i < 2 := by simpa using h₁
  have hi : i = 0 ∨ i = 1 := by omega
  cases hi with
  | inl hi0 =>
      subst hi0
      simpa using hn
  | inr hi1 =>
      subst hi1
      simpa using StructuralCongruence.refl (.lambda none body)

private theorem par_cong_cons_cons_tail
    {a₁ a₂ b₁ b₂ : Pattern} {rest : List Pattern}
    (ha : StructuralCongruence a₁ a₂)
    (hb : StructuralCongruence b₁ b₂) :
    StructuralCongruence
      (.collection .hashBag ([a₁, b₁] ++ rest) none)
      (.collection .hashBag ([a₂, b₂] ++ rest) none) := by
  refine StructuralCongruence.par_cong _ _ rfl ?_
  intro i h₁ h₂
  cases i with
  | zero =>
      simpa using ha
  | succ i =>
      cases i with
      | zero =>
          simpa using hb
      | succ i =>
          have h₁' : i < rest.length := by simpa using h₁
          have h₂' : i < rest.length := by simpa using h₂
          simpa using StructuralCongruence.refl (rest.get ⟨i, h₁'⟩)

private theorem struct_cong_par_head
    {p p' : Pattern} {rest : List Pattern}
    (hp : StructuralCongruence p p') :
    StructuralCongruence
      (.collection .hashBag (p :: rest) none)
      (.collection .hashBag (p' :: rest) none) := by
  refine StructuralCongruence.par_cong _ _ rfl ?_
  intro i h₁ h₂
  cases i with
  | zero =>
      simpa using hp
  | succ i =>
      have h₁' : i < rest.length := by simpa using h₁
      have h₂' : i < rest.length := by simpa using h₂
      simpa using StructuralCongruence.refl (rest.get ⟨i, h₁'⟩)

private theorem struct_cong_par_any
    {before after : List Pattern} {p p' : Pattern}
    (hp : StructuralCongruence p p') :
    StructuralCongruence
      (.collection .hashBag (before ++ [p] ++ after) none)
      (.collection .hashBag (before ++ [p'] ++ after) none) := by
  have hpermLeft :
      (before ++ [p] ++ after).Perm (p :: (before ++ after)) := by
    simp
  have hpermRight :
      (before ++ [p'] ++ after).Perm (p' :: (before ++ after)) := by
    simp
  exact StructuralCongruence.trans _ _ _
    (StructuralCongruence.par_perm _ _ hpermLeft)
    (StructuralCongruence.trans _ _ _
      (struct_cong_par_head hp)
      (StructuralCongruence.symm _ _ (StructuralCongruence.par_perm _ _ hpermRight)))

private theorem struct_cong_set_head
    {p p' : Pattern} {rest : List Pattern}
    (hp : StructuralCongruence p p') :
    StructuralCongruence
      (.collection .hashSet (p :: rest) none)
      (.collection .hashSet (p' :: rest) none) := by
  refine StructuralCongruence.set_cong _ _ rfl ?_
  intro i h₁ h₂
  cases i with
  | zero =>
      simpa using hp
  | succ i =>
      have h₁' : i < rest.length := by simpa using h₁
      have h₂' : i < rest.length := by simpa using h₂
      simpa using StructuralCongruence.refl (rest.get ⟨i, h₁'⟩)

private theorem struct_cong_set_any
    {before after : List Pattern} {p p' : Pattern}
    (hp : StructuralCongruence p p') :
    StructuralCongruence
      (.collection .hashSet (before ++ [p] ++ after) none)
      (.collection .hashSet (before ++ [p'] ++ after) none) := by
  have hpermLeft :
      (before ++ [p] ++ after).Perm (p :: (before ++ after)) := by
    simp
  have hpermRight :
      (before ++ [p'] ++ after).Perm (p' :: (before ++ after)) := by
    simp
  exact StructuralCongruence.trans _ _ _
    (StructuralCongruence.set_perm _ _ hpermLeft)
    (StructuralCongruence.trans _ _ _
      (struct_cong_set_head hp)
      (StructuralCongruence.symm _ _ (StructuralCongruence.set_perm _ _ hpermRight)))

private theorem reduceStep_mem_par_any
    {before after : List Pattern} {p q : Pattern} {fuel : Nat}
    (h : q ∈ reduceStep p fuel) :
    .collection .hashBag (before ++ [q] ++ after) none ∈
      reduceStep (.collection .hashBag (before ++ [p] ++ after) none) (fuel + 1) := by
  have hidx : before.length < (before ++ [p] ++ after).length := by
    simp
  have haux :
      (before.length, q) ∈
        reduceElemsAux (reduceStep · fuel) (before ++ [p] ++ after) :=
    reduceElemsAux_mem hidx (by simpa using h)
  have hset :
      (before ++ [p] ++ after).set before.length q = before ++ [q] ++ after := by
    simp [List.set_eq_take_append_cons_drop]
  simp only [reduceStep, List.mem_append]
  right
  rw [List.mem_map]
  exact ⟨(before.length, q), haux, by simp⟩

private theorem reduceStep_mem_par_set_any
    {before after : List Pattern} {p q : Pattern} {fuel : Nat}
    (h : q ∈ reduceStep p fuel) :
    .collection .hashSet (before ++ [q] ++ after) none ∈
      reduceStep (.collection .hashSet (before ++ [p] ++ after) none) (fuel + 1) := by
  have hidx : before.length < (before ++ [p] ++ after).length := by
    simp
  have haux :
      (before.length, q) ∈
        reduceElemsAux (reduceStep · fuel) (before ++ [p] ++ after) :=
    reduceElemsAux_mem hidx (by simpa using h)
  have hset :
      (before ++ [p] ++ after).set before.length q = before ++ [q] ++ after := by
    simp [List.set_eq_take_append_cons_drop]
  simp only [reduceStep]
  rw [List.mem_map]
  exact ⟨(before.length, q), haux, by simp⟩

open StructuralCongruence in
/-- COMM soundness at specific positions -/
private theorem comm_at_positions (elems : List Pattern) (i : Nat) (j : Nat)
    (nOut q nIn : Pattern) (body : Pattern)
    (hi : i < elems.length)
    (hj : j < (elems.eraseIdx i).length)
    (hout : elems[i] = .apply "POutput" [nOut, q])
    (hinp : (elems.eraseIdx i)[j] = .apply "PInput" [nIn, .lambda none body])
    (hchan : semanticNormalizeName nOut = semanticNormalizeName nIn) :
    Nonempty (Reduces (.collection .hashBag elems none)
      (.collection .hashBag ([semanticCommSubst body q] ++ (elems.eraseIdx i).eraseIdx j) none)) := by
  have hperm := perm_extract_two elems i j hi hj
  rw [hout, hinp] at hperm
  let n := semanticNormalizeName nOut
  have hOutNorm :
      StructuralCongruence (.apply "POutput" [nOut, q]) (.apply "POutput" [n, q]) :=
    by
      simpa [n] using
        struct_output_cong_channel
          (StructuralCongruence.symm _ _ (semanticNormalizeName_sound_struct (n := nOut)))
  have hInNorm :
      StructuralCongruence (.apply "PInput" [nIn, .lambda none body])
        (.apply "PInput" [n, .lambda none body]) := by
    simpa [n, hchan] using
      struct_input_cong_channel
        (StructuralCongruence.symm _ _ (semanticNormalizeName_sound_struct (n := nIn)))
  have hsc1 : StructuralCongruence
      (.collection .hashBag elems none)
      (.collection .hashBag
        ([.apply "POutput" [n, q], .apply "PInput" [n, .lambda none body]]
          ++ (elems.eraseIdx i).eraseIdx j) none) := by
    exact StructuralCongruence.trans _ _ _
      (StructuralCongruence.par_perm elems _ hperm)
      (par_cong_cons_cons_tail hOutNorm hInNorm)
  have hcomm := @Reduces.comm n q body ((elems.eraseIdx i).eraseIdx j)
  exact ⟨Reduces.equiv hsc1 hcomm (StructuralCongruence.refl _)⟩

/-- findAllComm specification -/
private theorem findAllComm_spec {elems : List Pattern} {r : Pattern}
    (hr : r ∈ findAllComm elems) :
    ∃ (i : Nat) (hi : i < elems.length) (j : Nat) (hj : j < (elems.eraseIdx i).length)
      (nOut q nIn : Pattern) (body : Pattern),
      elems[i] = .apply "POutput" [nOut, q] ∧
      (elems.eraseIdx i)[j] = .apply "PInput" [nIn, .lambda none body] ∧
      semanticNormalizeName nOut = semanticNormalizeName nIn ∧
      r = .collection .hashBag ([semanticCommSubst body q] ++ (elems.eraseIdx i).eraseIdx j) none := by
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
    obtain ⟨nIn, hj, hinp, hnorm⟩ := findInputPartner_spec hpartner
    refine ⟨i, hi_lt, j, hj, n, q, nIn, body, ?_, hinp, hnorm, rfl⟩
    · rw [helem_eq] at hmatch; exact matchOutput_spec hmatch

/-- Soundness of `findAllComm` -/
private theorem findAllComm_sound (elems : List Pattern)
    (r : Pattern) (hr : r ∈ findAllComm elems) :
    Nonempty (Reduces (.collection .hashBag elems none) r) := by
  obtain ⟨i, hi, j, hj, nOut, q, nIn, body, hout, hinp, hchan, rfl⟩ := findAllComm_spec hr
  exact comm_at_positions elems i j nOut q nIn body hi hj hout hinp hchan

/-- Soundness of `reduceStep`: every reduct is a valid `Reduces`. -/
theorem reduceStep_sound (p q : Pattern) (fuel : Nat)
    (h : q ∈ reduceStep p fuel) : Nonempty (p ⇝ q) := by
  match fuel, p with
  | 0, _ => simp [reduceStep] at h
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
  | _ + 1, .lambda _ _ => simp [reduceStep] at h
  | _ + 1, .multiLambda _ _ _ => simp [reduceStep] at h
  | _ + 1, .subst _ _ => simp [reduceStep] at h
  | _ + 1, .collection _ _ (some _) => simp [reduceStep] at h
  | _ + 1, .collection .vec _ none => simp [reduceStep] at h
  | n + 1, .apply c args =>
    simp only [reduceStep] at h
    simp at h

/-- Completeness for a top-level COMM redex: if the send and receive channels
    agree after semantic name normalization, the executable one-step frontier
    contains the expected COMM residual. This matches the live C runtime's
    normalized-name scheduler behavior. -/
theorem comm_head_mem_reduceStep
    {nOut q nIn body : Pattern} {rest : List Pattern}
    (hchan : semanticNormalizeName nOut = semanticNormalizeName nIn) :
    .collection .hashBag ([semanticCommSubst body q] ++ rest) none ∈
      reduceStep
        (.collection .hashBag
          ([.apply "POutput" [nOut, q],
            .apply "PInput" [nIn, .lambda none body]] ++ rest) none)
        1 := by
  simp [reduceStep, findAllComm, findInputPartner, matchOutput, matchInput, hchan]

/-- Structural fuel bound for quotient-exact one-step completeness.

    This is the honest amount of executable lookahead needed for a specific
    semantic one-step derivation: COMM needs one step, and every descent under
    bag/set structure adds one layer of recursive fuel. Structural-congruence
    shells themselves do not increase the bound. -/
def reduceStepCompletenessFuel {p q : Pattern} (h : p ⇝ q) : Nat :=
  match h with
  | .comm => 1
  | .equiv _ hmid _ => reduceStepCompletenessFuel hmid
  | .par hmid => reduceStepCompletenessFuel hmid + 1
  | .par_any hmid => reduceStepCompletenessFuel hmid + 1
  | .par_set hmid => reduceStepCompletenessFuel hmid + 1
  | .par_set_any hmid => reduceStepCompletenessFuel hmid + 1

/-- Quotient-exact completeness with an explicit proof-structural fuel bound. -/
theorem reduceStep_complete_up_to_struct_bounded
    {p q : Pattern} (h : p ⇝ q) :
    ∃ p' q',
      StructuralCongruence p' p ∧
      q' ∈ reduceStep p' (reduceStepCompletenessFuel h) ∧
      StructuralCongruence q' q := by
  induction h with
  | @comm n payload body rest =>
      refine ⟨
        .collection .hashBag
          ([.apply "POutput" [n, payload],
            .apply "PInput" [n, .lambda none body]] ++ rest) none,
        .collection .hashBag ([semanticCommSubst body payload] ++ rest) none,
        StructuralCongruence.refl _,
        ?_,
        StructuralCongruence.refl _⟩
      simpa [reduceStepCompletenessFuel] using
        comm_head_mem_reduceStep
          (nOut := n) (q := payload) (nIn := n) (body := body) (rest := rest) rfl
  | @equiv p pMid q qMid hsrc hmid htgt ih =>
      rcases ih with ⟨pRep, qRep, hpRep, hmem, hqRep⟩
      refine ⟨pRep, qRep, ?_, ?_, ?_⟩
      · exact StructuralCongruence.trans _ _ _ hpRep (StructuralCongruence.symm _ _ hsrc)
      · simpa [reduceStepCompletenessFuel] using hmem
      · exact StructuralCongruence.trans _ _ _ hqRep htgt
  | @par p q rest hstep ih =>
      rcases ih with ⟨pRep, qRep, hpRep, hmem, hqRep⟩
      refine ⟨
        .collection .hashBag (pRep :: rest) none,
        .collection .hashBag (qRep :: rest) none,
        struct_cong_par_head hpRep,
        ?_,
        struct_cong_par_head hqRep⟩
      simpa [reduceStepCompletenessFuel] using
        reduceStep_mem_par_any (before := []) (after := rest) hmem
  | @par_any p q before after hstep ih =>
      rcases ih with ⟨pRep, qRep, hpRep, hmem, hqRep⟩
      refine ⟨
        .collection .hashBag (before ++ [pRep] ++ after) none,
        .collection .hashBag (before ++ [qRep] ++ after) none,
        struct_cong_par_any hpRep,
        ?_,
        struct_cong_par_any hqRep⟩
      simpa [reduceStepCompletenessFuel] using
        reduceStep_mem_par_any (before := before) (after := after) hmem
  | @par_set p q rest hstep ih =>
      rcases ih with ⟨pRep, qRep, hpRep, hmem, hqRep⟩
      refine ⟨
        .collection .hashSet (pRep :: rest) none,
        .collection .hashSet (qRep :: rest) none,
        struct_cong_set_head hpRep,
        ?_,
        struct_cong_set_head hqRep⟩
      simpa [reduceStepCompletenessFuel] using
        reduceStep_mem_par_set_any (before := []) (after := rest) hmem
  | @par_set_any p q before after hstep ih =>
      rcases ih with ⟨pRep, qRep, hpRep, hmem, hqRep⟩
      refine ⟨
        .collection .hashSet (before ++ [pRep] ++ after) none,
        .collection .hashSet (before ++ [qRep] ++ after) none,
        struct_cong_set_any hpRep,
        ?_,
        struct_cong_set_any hqRep⟩
      simpa [reduceStepCompletenessFuel] using
        reduceStep_mem_par_set_any (before := before) (after := after) hmem

/-- Quotient-exact completeness for executable one-step reduction: every
    semantic one-step reduct is represented by an executable one-step reduct
    of some structurally congruent source representative, with a structurally
    congruent target representative. -/
theorem reduceStep_complete_up_to_struct
    {p q : Pattern} (h : p ⇝ q) :
    ∃ p' fuel q',
      StructuralCongruence p' p ∧
      q' ∈ reduceStep p' fuel ∧
      StructuralCongruence q' q := by
  rcases reduceStep_complete_up_to_struct_bounded h with ⟨p', q', hsrc, hmem, htgt⟩
  exact ⟨p', reduceStepCompletenessFuel h, q', hsrc, hmem, htgt⟩

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
  | .apply "PInput" [n, .lambda none body] =>
    let ns := patternToString n
    let bs := patternToString body
    ns ++ "?" ++ "." ++ "{" ++ bs ++ "}"
  | .apply c args =>
    let argsStr := args.map patternToString |>.intersperse ", " |> String.join
    s!"{c}({argsStr})"
  | .lambda _ body =>
    let bs := patternToString body
    "λ." ++ bs
  | .multiLambda n _ body =>
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
  .apply "PInput" [n, .lambda none body]
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

-- Test 2: Free DROP is inert in the paper-faithful core relation
#eval! do
  let term := pdrop (nquote pzero)
  let reducts := reduceStep term
  IO.println s!"Free DROP test: {term}"
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

-- Test 5: Nested PAR with inert free drop
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

/-! ### Boundary witnesses, proved

The race and chaining behaviours exercised by the `#eval` tests above, pinned as kernel-checked
theorems.  They are the operational echoes of the abstract no-go theorems
`contention_requires_choice` and `chaining_not_single_round` in `RhometaReduction.lean`: choice
between alternative COMM pairings and multi-round causal chaining are real behaviours of the
executable semantics, not artifacts of the abstract model. -/

/-- One send on `x`, two competing receivers: the contention witness. -/
private def raceWitness : Pattern :=
  ppar [poutput (Pattern.fvar "x") pzero,
        pinput (Pattern.fvar "x") (.bvar 0),
        pinput (Pattern.fvar "x") (pdrop (.bvar 0))]

/-- **Contention is operationally real**: the race witness has exactly two one-step reducts, and
they are distinct — two alternative pairings consume the same linear send, so a one-round
semantics must choose. -/
theorem raceWitness_two_distinct_reducts :
    (reduceStep raceWitness 4).length = 2 ∧ (reduceStep raceWitness 4).Nodup := by
  decide

/-- `send c a | recv c x. send d x | recv d y. 0`: the chaining witness — the `d`-COMM is enabled
only after the `c`-COMM fires. -/
private def chainWitness : Pattern :=
  ppar [poutput (Pattern.fvar "c") (nquote pzero),
        pinput (Pattern.fvar "c") (poutput (Pattern.fvar "d") (.bvar 0)),
        pinput (Pattern.fvar "d") pzero]

/-- **Chaining is operationally real, half 1**: no one-step reduct of the chaining witness is
quiescent — one round cannot finish it. -/
theorem chainWitness_no_one_step_quiescence :
    (reduceStep chainWitness 6).all (fun q => !(reduceStep q 6).isEmpty) = true := by
  decide

/-- **Chaining is operationally real, half 2**: a quiescent state IS reachable in two rounds —
sequential closure reaches what no single round can. -/
theorem chainWitness_two_step_quiescence :
    (reduceStep chainWitness 6).any
      (fun q => (reduceStep q 6).any (fun v => (reduceStep v 6).isEmpty)) = true := by
  decide

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Engine
