import Mettapedia.Languages.MeTTa.Translation.HEPeTTaTranslateCore

/-!
# Validated HE↔PeTTa Roundtrip Theorems

Late validated-fragment and stable-common roundtrip proofs extracted from
`HEPeTTaTranslate.lean` so they can be checked separately under tighter
resource limits.
-/

namespace Mettapedia.Languages.MeTTa.Translation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-!
The old universal theorem

```
Translatable a → Translatable (translatePeTTa a s).1
```

is no longer honest once `foldall` is executable. A source such as
`(foldall $f goal init)` is syntactically translatable, but lowers to an HE term
whose reducer position is not pattern-translatable unless `$f` is restricted to a
first-order callable fragment. The validated PeTTa-side theorem therefore appears
later, after the first-order reducer predicate is defined.
-/

/-! ## Roundtrip: HE → PeTTa → HE idempotence

The roundtrip `translatePeTTa ∘ translateHE` does NOT recover the original term.
It produces the PeTTa-normalized form:
- `(chain E V B)` → `(let V E B)` (head rename, not reversed)
- `(nop X)` → `(let $fresh X ())` (administrative let, not reversed)
- `(function (return X))` → `X` (unwrap, not reversed)

But the roundtrip is **idempotent**: after one HE→PeTTa pass, the result is
already in PeTTa normal form, so `translateHE (translatePeTTa (translateHE a s).1 s').1 s''`
produces the same PeTTa normal form as `translateHE a s`.

More precisely: `translateHE` is idempotent on PeTTa-normal terms, because
PeTTa-normal terms have no `chain`, `nop`, `collapse-bind`, `superpose-bind`,
`atom-subst`, or `function/return` heads — so `translateHE` is identity on them. -/

/-- A term is in **PeTTa normal form**: no HE-specific constructs that
    `translateHE` would rewrite. `translateHE` is identity on such terms. -/
def isPeTTaNormal : Atom → Bool
  | .expression (.symbol "chain" :: _) => false
  | .expression [.symbol "collapse-bind", _] => false
  | .expression [.symbol "superpose-bind", _] => false
  | .expression (.symbol "switch" :: _ :: _) => false
  | .expression (.symbol "switch-minimal" :: _ :: _) => false
  | .expression [.symbol "atom-subst", _, _, _] => false
  | .expression [.symbol "nop", _] => false
  | .expression [.symbol "function", .expression [.symbol "return", _]] => false
  | _ => true

/-- `translateHE` is identity on PeTTa-normal atoms (non-expression case). -/
theorem translateHE_id_var (v : String) (s : Nat) :
    translateHE (.var v) s = (.var v, s) := rfl

theorem translateHE_id_symbol (nm : String) (s : Nat) :
    translateHE (.symbol nm) s = (.symbol nm, s) := rfl

set_option maxHeartbeats 800000


mutual

theorem validatedPeTTaSource_of_headSource_aux
    (a : Atom) (h : isValidatedPeTTaHeadSource a = true) :
    isValidatedPeTTaSource a = true := by
  cases a with
  | var _ => simp [isValidatedPeTTaHeadSource, isValidatedPeTTaSource]
  | symbol c =>
      by_cases hchain : c = "chain"
      · subst hchain
        simp [isValidatedPeTTaHeadSource] at h
      · by_cases hcollapse : c = "collapse-bind"
        · subst hcollapse
          simp [isValidatedPeTTaHeadSource] at h
        · by_cases hsuperpose : c = "superpose-bind"
          · subst hsuperpose
            simp [isValidatedPeTTaHeadSource] at h
          · by_cases hswitch : c = "switch"
            · subst hswitch
              simp [isValidatedPeTTaHeadSource] at h
            · by_cases hswitchm : c = "switch-minimal"
              · subst hswitchm
                simp [isValidatedPeTTaHeadSource] at h
              · by_cases hatomsubst : c = "atom-subst"
                · subst hatomsubst
                  simp [isValidatedPeTTaHeadSource] at h
                · by_cases hnop : c = "nop"
                  · subst hnop
                    simp [isValidatedPeTTaHeadSource] at h
                  · by_cases hfunction : c = "function"
                    · subst hfunction
                      simp [isValidatedPeTTaHeadSource] at h
                    · by_cases hprogn : c = "progn"
                      · subst hprogn
                        simp [isValidatedPeTTaHeadSource] at h
                      · by_cases hprog1 : c = "prog1"
                        · subst hprog1
                          simp [isValidatedPeTTaHeadSource] at h
                        · by_cases hfoldall : c = "foldall"
                          · subst hfoldall
                            simp [isValidatedPeTTaHeadSource] at h
                          · by_cases hlt : c = "@<"
                            · subst hlt
                              simp [isValidatedPeTTaHeadSource] at h
                            · by_cases hgt : c = "@>"
                              · subst hgt
                                simp [isValidatedPeTTaHeadSource] at h
                              · simp [isValidatedPeTTaHeadSource, isValidatedPeTTaSource,
                                  hchain, hcollapse, hsuperpose, hswitch, hswitchm,
                                  hatomsubst, hnop, hfunction, hprogn, hprog1,
                                  hfoldall, hlt, hgt] at h ⊢
  | grounded _ => simp [isValidatedPeTTaHeadSource, isValidatedPeTTaSource]
  | expression es =>
      cases es with
      | nil => simp [isValidatedPeTTaHeadSource, isValidatedPeTTaSource]
      | cons hd args =>
          cases hd with
          | symbol c =>
              by_cases hprogn : c = "progn"
              · subst hprogn
                have hargs : isValidatedPeTTaPrognHeadArgs args = true := by
                  simpa [isValidatedPeTTaHeadSource] using h
                simpa [isValidatedPeTTaSource] using
                  validatedPeTTaList_of_prognHeadArgs_aux args hargs
              · by_cases hprog1 : c = "prog1"
                · subst hprog1
                  have hargs : isValidatedPeTTaProg1HeadArgs args = true := by
                    simpa [isValidatedPeTTaHeadSource, hprogn] using h
                  simpa [isValidatedPeTTaSource] using
                    validatedPeTTaList_of_prog1HeadArgs_aux args hargs
                · by_cases hfoldall : c = "foldall"
                  · subst hfoldall
                    cases args with
                    | nil =>
                        simp [isValidatedPeTTaHeadSource, isValidatedPeTTaSource, hprogn, hprog1] at h
                    | cons agg rest =>
                        cases rest with
                        | nil =>
                            simp [isValidatedPeTTaHeadSource, isValidatedPeTTaSource, hprogn, hprog1] at h
                        | cons goal rest =>
                            cases rest with
                            | nil =>
                                simp [isValidatedPeTTaHeadSource, isValidatedPeTTaSource, hprogn, hprog1] at h
                            | cons init rest =>
                                cases rest with
                                | nil =>
                                    simpa [isValidatedPeTTaHeadSource, isValidatedPeTTaSource,
                                      hprogn, hprog1]
                                      using h
                                | cons _ _ =>
                                    simp [isValidatedPeTTaHeadSource, isValidatedPeTTaSource,
                                      hprogn, hprog1] at h
                  · by_cases hlt : c = "@<"
                    · subst hlt
                      cases args with
                      | nil =>
                          simp [isValidatedPeTTaHeadSource, isValidatedPeTTaSource,
                            hprogn, hprog1, hfoldall] at h
                      | cons a rest =>
                          cases rest with
                          | nil =>
                              simp [isValidatedPeTTaHeadSource, isValidatedPeTTaSource,
                                hprogn, hprog1, hfoldall] at h
                          | cons b rest =>
                              cases rest with
                              | nil =>
                                  simpa [isValidatedPeTTaHeadSource, isValidatedPeTTaSource,
                                    hprogn, hprog1, hfoldall] using h
                              | cons _ _ =>
                                  simp [isValidatedPeTTaHeadSource, isValidatedPeTTaSource,
                                    hprogn, hprog1, hfoldall] at h
                    · by_cases hgt : c = "@>"
                      · subst hgt
                        cases args with
                        | nil =>
                            simp [isValidatedPeTTaHeadSource, isValidatedPeTTaSource,
                              hprogn, hprog1, hfoldall, hlt] at h
                        | cons a rest =>
                            cases rest with
                            | nil =>
                                simp [isValidatedPeTTaHeadSource, isValidatedPeTTaSource,
                                  hprogn, hprog1, hfoldall, hlt] at h
                            | cons b rest =>
                                cases rest with
                                | nil =>
                                    simpa [isValidatedPeTTaHeadSource, isValidatedPeTTaSource,
                                      hprogn, hprog1, hfoldall, hlt] using h
                                | cons _ _ =>
                                    simp [isValidatedPeTTaHeadSource, isValidatedPeTTaSource,
                                      hprogn, hprog1, hfoldall, hlt] at h
                      · simpa [isValidatedPeTTaHeadSource, isValidatedPeTTaSource,
                          hprogn, hprog1, hfoldall, hlt, hgt] using h
          | var _ => simpa [isValidatedPeTTaHeadSource] using h
          | grounded _ => simpa [isValidatedPeTTaHeadSource] using h
          | expression _ => simpa [isValidatedPeTTaHeadSource] using h

private theorem validatedPeTTaList_of_prognHeadArgs_aux
    (args : List Atom) (h : isValidatedPeTTaPrognHeadArgs args = true) :
    isValidatedPeTTaList args = true := by
  cases args with
  | nil => simp [isValidatedPeTTaPrognHeadArgs, isValidatedPeTTaList]
  | cons x xs =>
      cases xs with
      | nil =>
          have hx : isValidatedPeTTaSource x = true := by
            exact validatedPeTTaSource_of_headSource_aux x (by simpa [isValidatedPeTTaPrognHeadArgs] using h)
          simp [isValidatedPeTTaList, hx]
      | cons y ys =>
          simp [isValidatedPeTTaPrognHeadArgs, Bool.and_eq_true] at h
          have htail : isValidatedPeTTaList (y :: ys) = true :=
            validatedPeTTaList_of_prognHeadArgs_aux (y :: ys) h.2
          simpa [isValidatedPeTTaList, h.1] using htail

private theorem validatedPeTTaList_of_prog1HeadArgs_aux
    (args : List Atom) (h : isValidatedPeTTaProg1HeadArgs args = true) :
    isValidatedPeTTaList args = true := by
  cases args with
  | nil => simp [isValidatedPeTTaProg1HeadArgs, isValidatedPeTTaList]
  | cons x xs =>
      cases xs with
      | nil =>
          have hx : isValidatedPeTTaSource x = true := by
            exact validatedPeTTaSource_of_headSource_aux x (by simpa [isValidatedPeTTaProg1HeadArgs] using h)
          simp [isValidatedPeTTaList, hx]
      | cons y ys =>
          simp [isValidatedPeTTaProg1HeadArgs, isValidatedPeTTaList, Bool.and_eq_true] at h ⊢
          have hx : isValidatedPeTTaSource x = true :=
            validatedPeTTaSource_of_headSource_aux x h.1
          exact ⟨hx, h.2⟩
end

theorem headSourcePeTTaSymbol_notForbidden_aux
    (c : String) (h : isValidatedPeTTaHeadSource (.symbol c) = true) :
    isForbiddenHeadSymbol (.symbol c) = false := by
  by_cases hchain : c = "chain"
  · subst hchain
    simp [isValidatedPeTTaHeadSource] at h
  · by_cases hcollapse : c = "collapse-bind"
    · subst hcollapse
      simp [isValidatedPeTTaHeadSource] at h
    · by_cases hsuperpose : c = "superpose-bind"
      · subst hsuperpose
        simp [isValidatedPeTTaHeadSource] at h
      · by_cases hswitch : c = "switch"
        · subst hswitch
          simp [isValidatedPeTTaHeadSource] at h
        · by_cases hswitchm : c = "switch-minimal"
          · subst hswitchm
            simp [isValidatedPeTTaHeadSource] at h
          · by_cases hatomsubst : c = "atom-subst"
            · subst hatomsubst
              simp [isValidatedPeTTaHeadSource] at h
            · by_cases hnop : c = "nop"
              · subst hnop
                simp [isValidatedPeTTaHeadSource] at h
              · by_cases hfunction : c = "function"
                · subst hfunction
                  simp [isValidatedPeTTaHeadSource] at h
                · by_cases hprogn : c = "progn"
                  · subst hprogn
                    simp [isValidatedPeTTaHeadSource] at h
                  · by_cases hprog1 : c = "prog1"
                    · subst hprog1
                      simp [isValidatedPeTTaHeadSource] at h
                    · by_cases hfoldall : c = "foldall"
                      · subst hfoldall
                        simp [isValidatedPeTTaHeadSource] at h
                      · by_cases hlt : c = "@<"
                        · subst hlt
                          simp [isValidatedPeTTaHeadSource] at h
                        · by_cases hgt : c = "@>"
                          · subst hgt
                            simp [isValidatedPeTTaHeadSource] at h
                          · simp [isForbiddenHeadSymbol, hchain, hcollapse, hsuperpose,
                              hswitch, hswitchm, hatomsubst, hnop, hfunction, hprogn,
                              hprog1, hfoldall, hlt, hgt]



end Mettapedia.Languages.MeTTa.Translation
