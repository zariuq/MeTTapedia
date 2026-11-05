import Mathlib.Data.List.Basic

/-! Raw source regions are lexical carriers, independent of a guest grammar.
The first closing fence determines the boundary; quotes and backslashes in
the body retain their literal meaning. This specification does not assert
correspondence of a native UTF-8 implementation or authorize guest execution. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.RawSourceRegion

def closing (depth : Nat) : List Char := '"' :: List.replicate depth '#'
def opening (depth : Nat) : List Char := 'r' :: List.replicate depth '#' ++ ['"']

def scanBody (depth : Nat) : List Char → Option (List Char × List Char)
  | [] => none
  | c :: cs =>
    if (closing depth).isPrefixOf (c :: cs) then
      some ([], (c :: cs).drop (depth + 1))
    else (scanBody depth cs).map fun result => (c :: result.1, result.2)

/-- A lexical boundary: no earlier position may be a closing fence. -/
inductive FirstClosing (depth : Nat) : List Char → List Char → List Char → Prop
  | stop (rest : List Char) : FirstClosing depth (closing depth ++ rest) [] rest
  | pass (c : Char) (input body rest : List Char)
      (notClosing : ¬ (closing depth).IsPrefix (c :: input))
      (later : FirstClosing depth input body rest) :
      FirstClosing depth (c :: input) (c :: body) rest

theorem FirstClosing.reconstruct {depth : Nat} {input body rest : List Char}
    (boundary : FirstClosing depth input body rest) :
    input = body ++ closing depth ++ rest := by
  induction boundary with
  | stop => rfl
  | pass c input body rest _ _ ih => simp [ih]

theorem scanBody_sound (depth : Nat) (input body rest : List Char)
    (read : scanBody depth input = some (body, rest)) :
    FirstClosing depth input body rest := by
  induction input generalizing body rest with
  | nil => simp [scanBody] at read
  | cons c cs ih =>
    simp only [scanBody] at read
    split at read
    next starts =>
      obtain ⟨tail, eq⟩ := List.isPrefixOf_iff_prefix.mp starts
      have dropped : (c :: cs).drop (depth + 1) = tail := by
        rw [← eq]
        simp [closing]
      simp only [dropped, Option.some.injEq, Prod.mk.injEq] at read
      rcases read with ⟨rfl, rfl⟩
      rw [← eq]
      exact .stop _
    next noPrefix =>
      cases found : scanBody depth cs with
      | none => simp [found] at read
      | some result =>
        rcases result with ⟨bs, tail⟩
        simp only [found, Option.map_some, Option.some.injEq, Prod.mk.injEq] at read
        rcases read with ⟨rfl, rfl⟩
        exact .pass c cs bs tail (by simpa using noPrefix) (ih bs tail found)

theorem scanBody_complete {depth : Nat} {input body rest : List Char}
    (boundary : FirstClosing depth input body rest) :
    scanBody depth input = some (body, rest) := by
  induction boundary with
  | stop rest => simp [closing, scanBody]
  | pass c input body rest notClosing _ ih =>
    have noPrefix : (closing depth).isPrefixOf (c :: input) = false := by
      exact Bool.eq_false_iff.mpr (fun h => notClosing (List.isPrefixOf_iff_prefix.mp h))
    simp [scanBody, noPrefix, ih]

theorem scanBody_iff (depth : Nat) (input body rest : List Char) :
    scanBody depth input = some (body, rest) ↔ FirstClosing depth input body rest :=
  ⟨scanBody_sound depth input body rest, scanBody_complete⟩

theorem scanBody_reconstruct {depth : Nat} {input body rest : List Char}
    (read : scanBody depth input = some (body, rest)) :
    input = body ++ closing depth ++ rest :=
  (scanBody_sound depth input body rest read).reconstruct

/-- Returned guest source and trailing host source are unique at this fence. -/
theorem boundary_unique {depth : Nat} {input first rest₁ second rest₂ : List Char}
    (one : FirstClosing depth input first rest₁)
    (two : FirstClosing depth input second rest₂) : first = second ∧ rest₁ = rest₂ := by
  have eq := (scanBody_complete one).symm.trans (scanBody_complete two)
  simpa using eq

private theorem hashes_hit_quote (body rest : List Char) (depth : Nat)
    (longer : body.length < depth) :
    (List.replicate depth '#').isPrefixOf (body ++ '"' :: rest) = false := by
  induction body generalizing depth with
  | nil =>
    cases depth with
    | zero => simp at longer
    | succ n => simp [List.replicate_succ, List.isPrefixOf_cons_cons]
  | cons c cs ih =>
    cases depth with
    | zero => simp at longer
    | succ n =>
      have shorter : cs.length < n := by simpa using longer
      simp [List.replicate_succ, List.isPrefixOf_cons_cons, ih n shorter]

/-- There is a finite safe fence for every body, even if it contains quoted
source regions itself. No guest-language parser is needed to find one. -/
theorem boundary_of_length (body rest : List Char) (depth : Nat)
    (longer : body.length < depth) :
    FirstClosing depth (body ++ closing depth ++ rest) body rest := by
  induction body with
  | nil => exact .stop rest
  | cons c cs ih =>
    have shorter : cs.length < depth := by simpa using Nat.lt_of_succ_lt longer
    apply FirstClosing.pass c (cs ++ closing depth ++ rest) cs rest
    · intro starts
      have yes := List.isPrefixOf_iff_prefix.mpr starts
      have no := hashes_hit_quote cs (List.replicate depth '#' ++ rest) depth shorter
      simp [closing, List.isPrefixOf_cons_cons, no] at yes
    · exact ih shorter

theorem scanBody_roundtrip (body rest : List Char) (depth : Nat)
    (longer : body.length < depth) :
    scanBody depth (body ++ closing depth ++ rest) = some (body, rest) :=
  scanBody_complete (boundary_of_length body rest depth longer)

theorem every_body_encodable (body rest : List Char) :
    ∃ depth, 0 < depth ∧ scanBody depth (body ++ closing depth ++ rest) = some (body, rest) :=
  ⟨body.length + 1, by omega, scanBody_roundtrip body rest _ (by omega)⟩

example : scanBody 1 "a\\n\"#tail".toList = some ("a\\n".toList, "tail".toList) := by decide +kernel
example : scanBody 2 "a\"#b\"##tail".toList = some ("a\"#b".toList, "tail".toList) := by decide +kernel
example : scanBody 2 "a\"#".toList = none := by decide +kernel
example : scanBody 1 "\"##".toList = some ([], ['#']) := by decide +kernel
example : scanBody 1 "\r\n  λ\"#".toList = some ("\r\n  λ".toList, []) := by decide +kernel

#print axioms scanBody_iff
#print axioms boundary_unique
#print axioms every_body_encodable

end Mettapedia.GSLT.Parsing.RawSourceRegion
