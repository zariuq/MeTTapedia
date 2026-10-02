import Mettapedia.GSLT.LanguageDef.RegexRequests

/-!
# Finite-depth completeness of regex requests

Increasing the premise budget preserves every successful result. Every
well-formed structural request succeeds at some finite budget. The budget
counts derivation depth, not elapsed time or a machine-cost bound.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RegexAuthoredComparison

open Mettapedia.Computability.RegularLanguages

/-- One more level of ordered rule premises cannot change a successful result. -/
theorem boundedResult_step {fuel : Nat} {request : Request} {result : Result request}
    (success : boundedResult fuel request = some result) :
    boundedResult (fuel + 1) request = some result := by
  induction fuel generalizing request result with
  | zero => cases success
  | succ fuel ih =>
    cases request with
    | disjoin left right => exact success
    | conjoin left right => exact success
    | nullable p =>
      cases p with
      | zero => exact success
      | epsilon => exact success
      | char atom => exact success
      | star p => exact success
      | plus p q =>
        obtain ⟨left, hl, rest⟩ := Option.bind_eq_some_iff.mp success
        obtain ⟨right, hr, hout⟩ := Option.bind_eq_some_iff.mp rest
        simp only [boundedResult, ih hl, ih hr]
        exact ih hout
      | comp p q =>
        obtain ⟨left, hl, rest⟩ := Option.bind_eq_some_iff.mp success
        obtain ⟨right, hr, hout⟩ := Option.bind_eq_some_iff.mp rest
        simp only [boundedResult, ih hl, ih hr]
        exact ih hout
    | derivative a p =>
      cases p with
      | zero => exact success
      | epsilon => exact success
      | char atom => cases atom <;> exact success
      | plus p q =>
        obtain ⟨dp, hp, rest⟩ := Option.bind_eq_some_iff.mp success
        obtain ⟨dq, hq, hout⟩ := Option.bind_eq_some_iff.mp rest
        simp only [boundedResult, ih hp, ih hq]
        exact hout
      | comp p q =>
        obtain ⟨empty, hn, rest⟩ := Option.bind_eq_some_iff.mp success
        obtain ⟨dp, hp, hout⟩ := Option.bind_eq_some_iff.mp rest
        simp only [boundedResult, ih hn, ih hp]
        cases empty with
        | false => exact hout
        | true =>
          obtain ⟨dq, hq, hresult⟩ := Option.bind_eq_some_iff.mp hout
          simp only [ih hq]
          exact hresult
      | star p =>
        obtain ⟨dp, hp, hout⟩ := Option.bind_eq_some_iff.mp success
        simp only [boundedResult, ih hp]
        exact hout
    | matchWord p input =>
      cases input with
      | nil => exact ih success
      | cons a rest =>
        obtain ⟨next, hnext, hout⟩ := Option.bind_eq_some_iff.mp success
        simp only [boundedResult, ih hnext]
        exact ih hout

/-- Success is monotone in the premise budget; the result itself stays fixed. -/
theorem boundedResult_mono {small large : Nat} (increasing : small ≤ large)
    {request : Request} {result : Result request}
    (success : boundedResult small request = some result) :
    boundedResult large request = some result := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le increasing
  clear increasing
  induction extra with
  | zero => exact success
  | succ extra ih => exact boundedResult_step ih

private theorem nullable_eventual (p : Regex String) :
    ∃ fuel, boundedResult fuel (.nullable p) = some p.matchEpsilon := by
  induction p with
  | zero => exact ⟨1, rfl⟩
  | epsilon => exact ⟨1, rfl⟩
  | char atom => exact ⟨1, rfl⟩
  | star p ih => exact ⟨1, rfl⟩
  | plus p q hp hq =>
    obtain ⟨fp, hp⟩ := hp
    obtain ⟨fq, hq⟩ := hq
    have left := boundedResult_mono (large := fp + fq + 1) (by omega) hp
    have right := boundedResult_mono (large := fp + fq + 1) (by omega) hq
    exact ⟨fp + fq + 1 + 1, by
      simp only [boundedResult, left, right]
      rfl⟩
  | comp p q hp hq =>
    obtain ⟨fp, hp⟩ := hp
    obtain ⟨fq, hq⟩ := hq
    have left := boundedResult_mono (large := fp + fq + 1) (by omega) hp
    have right := boundedResult_mono (large := fp + fq + 1) (by omega) hq
    exact ⟨fp + fq + 1 + 1, by
      simp only [boundedResult, left, right]
      rfl⟩

private theorem derivative_eventual (a : String) (p : Regex String) :
    ∃ fuel, boundedResult fuel (.derivative a p) = some (derivative a p) := by
  induction p with
  | zero => exact ⟨1, rfl⟩
  | epsilon => exact ⟨1, rfl⟩
  | char atom =>
    cases atom with
    | literal expected =>
      exact ⟨1, by simp [boundedResult, derivative, Atom.accepts]⟩
    | any => exact ⟨1, rfl⟩
  | plus p q hp hq =>
    obtain ⟨fp, hp⟩ := hp
    obtain ⟨fq, hq⟩ := hq
    have left := boundedResult_mono (large := fp + fq + 1) (by omega) hp
    have right := boundedResult_mono (large := fp + fq + 1) (by omega) hq
    exact ⟨fp + fq + 1 + 1, by
      simp only [boundedResult, left, right]
      rfl⟩
  | comp p q hp hq =>
    obtain ⟨fn, hn⟩ := nullable_eventual p
    obtain ⟨fp, hp⟩ := hp
    obtain ⟨fq, hq⟩ := hq
    have empty := boundedResult_mono (large := fn + fp + fq + 1) (by omega) hn
    have left := boundedResult_mono (large := fn + fp + fq + 1) (by omega) hp
    have right := boundedResult_mono (large := fn + fp + fq + 1) (by omega) hq
    exact ⟨fn + fp + fq + 1 + 1, by
      simp only [boundedResult, empty, left]
      cases hn : p.matchEpsilon <;> simp only [hn, Bool.false_eq_true, if_false, if_true,
        right, derivative] <;> rfl⟩
  | star p hp =>
    obtain ⟨fp, hp⟩ := hp
    exact ⟨fp + 1, by
      simp only [boundedResult, hp]
      rfl⟩

private theorem match_eventual (p : Regex String) (input : List String) :
    ∃ fuel, boundedResult fuel (.matchWord p input) = some (fullMatch p input) := by
  induction input generalizing p with
  | nil =>
    obtain ⟨fuel, h⟩ := nullable_eventual p
    exact ⟨fuel + 1, h⟩
  | cons a rest ih =>
    obtain ⟨fd, hd⟩ := derivative_eventual a p
    obtain ⟨fr, hr⟩ := ih (derivative a p)
    have first := boundedResult_mono (large := fd + fr) (by omega) hd
    have later := boundedResult_mono (large := fd + fr) (by omega) hr
    exact ⟨fd + fr + 1, by
      simp only [boundedResult, first]
      exact later⟩

/-- Every structural request has a finite derivation budget producing its actual result. -/
theorem boundedResult_eventual (request : Request) :
    ∃ fuel, boundedResult fuel request = some (referenceResult request) := by
  cases request with
  | disjoin left right => exact ⟨1, rfl⟩
  | conjoin left right => exact ⟨1, rfl⟩
  | nullable p => exact nullable_eventual p
  | derivative a p => exact derivative_eventual a p
  | matchWord p input => exact match_eventual p input

/-- Finite budgets characterize all and only the independently derived results. -/
theorem evidence_iff_boundedResult (request : Request) (result : Result request) :
    Nonempty (Evidence request result) ↔ ∃ fuel, boundedResult fuel request = some result := by
  constructor
  · rintro ⟨event⟩
    obtain ⟨fuel, success⟩ := boundedResult_eventual request
    exact ⟨fuel, success.trans (congrArg some (evidence_sound request result event))⟩
  · rintro ⟨fuel, success⟩
    have same := boundedResult_sound success
    exact ⟨same ▸ completeEvidence request⟩

end Mettapedia.GSLT.LanguageDef.RegexAuthoredComparison
