import Mettapedia.GSLT.LanguageDef.RegexTheory

/-!
# Typed requests and authored regex observations

An admitted request uses the checked regex constructor image and native string
letters. Its meaning retains a derivation of the structural rule graph. The
comparison with authored contextual reduction is stated over this image;
malformed raw terms are not silently treated as well-typed requests.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RegexAuthoredComparison

open Mettapedia.Computability.RegularLanguages
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.ContextualStep


/-- Input judgments, without duplicating regular-expression syntax. -/
inductive Request where
  | disjoin : Bool → Bool → Request
  | conjoin : Bool → Bool → Request
  | nullable : Regex String → Request
  | derivative : String → Regex String → Request
  | matchWord : Regex String → List String → Request

abbrev Result : Request → Type
  | .disjoin _ _ => Bool
  | .conjoin _ _ => Bool
  | .nullable _ => Bool
  | .derivative _ _ => Regex String
  | .matchWord _ _ => Bool

def Evidence : (request : Request) → Result request → Type
  | .disjoin left right, result => RegexDerivatives.Disjoin left right result
  | .conjoin left right, result => RegexDerivatives.Conjoin left right result
  | .nullable p, result => RegexDerivatives.Nullable p result
  | .derivative a p, result => RegexDerivatives.Derivative a p result
  | .matchWord p input, result => RegexDerivatives.Match p input result

def encodeRequest : Request → Pattern
  | .disjoin left right => RegexTheory.disjoin (RegexTheory.boolean left) (RegexTheory.boolean right)
  | .conjoin left right => RegexTheory.conjoin (RegexTheory.boolean left) (RegexTheory.boolean right)
  | .nullable p => RegexTheory.nullable (RegexTheory.encode p)
  | .derivative a p => RegexTheory.derivative (RegexTheory.scalar a) (RegexTheory.encode p)
  | .matchWord p input => RegexTheory.matchRequest (RegexTheory.encode p) (RegexTheory.word input)

def encodeResult : (request : Request) → Result request → Pattern
  | .disjoin _ _, result => RegexTheory.boolean result
  | .conjoin _ _, result => RegexTheory.boolean result
  | .nullable _, result => RegexTheory.boolean result
  | .derivative _ _, result => RegexTheory.encode result
  | .matchWord _ _, result => RegexTheory.boolean result

/-- The terminal observation retains a typed structural derivation. -/
def RootMeaning (request : Request) (output : Pattern) : Prop :=
  ∃ result : Result request, output = encodeResult request result ∧ Nonempty (Evidence request result)

def referenceResult : (request : Request) → Result request
  | .disjoin left right => left || right
  | .conjoin left right => left && right
  | .nullable p => p.matchEpsilon
  | .derivative a p => derivative a p
  | .matchWord p input => fullMatch p input

def completeEvidence : (request : Request) → Evidence request (referenceResult request)
  | .disjoin left right => RegexDerivatives.Disjoin.complete left right
  | .conjoin left right => RegexDerivatives.Conjoin.complete left right
  | .nullable p => RegexDerivatives.Nullable.complete p
  | .derivative a p => RegexDerivatives.Derivative.complete a p
  | .matchWord p input => RegexDerivatives.Match.complete p input

theorem evidence_sound (request : Request) (result : Result request)
    (event : Evidence request result) : referenceResult request = result := by
  cases request with
  | disjoin left right => exact event.sound
  | conjoin left right => exact event.sound
  | nullable p => exact event.sound
  | derivative a p => exact event.sound
  | matchWord p input => exact event.sound

theorem rootMeaning_iff_reference (request : Request) (output : Pattern) :
    RootMeaning request output ↔ output = encodeResult request (referenceResult request) := by
  constructor
  · rintro ⟨result, houtput, ⟨event⟩⟩
    exact houtput.trans (congrArg (encodeResult request) (evidence_sound request result event).symm)
  · intro h
    exact ⟨referenceResult request, h, ⟨completeEvidence request⟩⟩

/-- Finite-depth evaluation of the independent structural judgments. Each
recursive rule premise consumes one level, exactly as in `ContextualStep`. -/
def boundedResult : (fuel : Nat) → (request : Request) → Option (Result request)
  | 0, _ => none
  | _ + 1, .disjoin left right => some (left || right)
  | _ + 1, .conjoin left right => some (left && right)
  | _ + 1, .nullable .zero => some false
  | _ + 1, .nullable .epsilon => some true
  | _ + 1, .nullable (.char _) => some false
  | fuel + 1, .nullable (.plus p q) => do
      let left ← boundedResult fuel (.nullable p)
      let right ← boundedResult fuel (.nullable q)
      boundedResult fuel (.disjoin left right)
  | fuel + 1, .nullable (.comp p q) => do
      let left ← boundedResult fuel (.nullable p)
      let right ← boundedResult fuel (.nullable q)
      boundedResult fuel (.conjoin left right)
  | _ + 1, .nullable (.star _) => some true
  | _ + 1, .derivative _ .zero => some 0
  | _ + 1, .derivative _ .epsilon => some 0
  | _ + 1, .derivative a (.char (.literal expected)) => some (if expected = a then 1 else 0)
  | _ + 1, .derivative _ (.char .any) => some 1
  | fuel + 1, .derivative a (.plus p q) => do
      let dp ← boundedResult fuel (.derivative a p)
      let dq ← boundedResult fuel (.derivative a q)
      return dp + dq
  | fuel + 1, .derivative a (.comp p q) => do
      let empty ← boundedResult fuel (.nullable p)
      let dp ← boundedResult fuel (.derivative a p)
      if empty then do
        let dq ← boundedResult fuel (.derivative a q)
        return dp * q + dq
      else return dp * q
  | fuel + 1, .derivative a (.star p) => do
      let dp ← boundedResult fuel (.derivative a p)
      return dp * p.star
  | fuel + 1, .matchWord p [] => boundedResult fuel (.nullable p)
  | fuel + 1, .matchWord p (a :: rest) => do
      let next ← boundedResult fuel (.derivative a p)
      boundedResult fuel (.matchWord next rest)

theorem boundedResult_sound {fuel : Nat} {request : Request} {result : Result request}
    (success : boundedResult fuel request = some result) : referenceResult request = result := by
  induction fuel generalizing request result with
  | zero => simp [boundedResult] at success
  | succ fuel ih =>
    cases request with
    | disjoin left right => exact Option.some.inj success
    | conjoin left right => exact Option.some.inj success
    | nullable p =>
      cases p with
      | zero => exact Option.some.inj success
      | epsilon => exact Option.some.inj success
      | char atom => exact Option.some.inj success
      | star p => exact Option.some.inj success
      | plus p q =>
        obtain ⟨left, hl, rest⟩ := Option.bind_eq_some_iff.mp success
        have hleft := ih hl
        obtain ⟨right, hr, hout⟩ := Option.bind_eq_some_iff.mp rest
        have hright := ih hr
        have combined := ih hout
        change (p.matchEpsilon || q.matchEpsilon) = result
        change p.matchEpsilon = left at hleft
        change q.matchEpsilon = right at hright
        exact (congrArg₂ Bool.or hleft hright).trans combined
      | comp p q =>
        obtain ⟨left, hl, rest⟩ := Option.bind_eq_some_iff.mp success
        obtain ⟨right, hr, hout⟩ := Option.bind_eq_some_iff.mp rest
        have hleft := ih hl
        have hright := ih hr
        have combined := ih hout
        change (p.matchEpsilon && q.matchEpsilon) = result
        change p.matchEpsilon = left at hleft
        change q.matchEpsilon = right at hright
        exact (congrArg₂ Bool.and hleft hright).trans combined
    | derivative a p =>
      cases p with
      | zero => exact Option.some.inj success
      | epsilon => exact Option.some.inj success
      | char atom =>
        cases atom with
        | literal expected =>
          simpa [referenceResult, derivative, Atom.accepts, boundedResult] using success
        | any => exact Option.some.inj success
      | plus p q =>
        obtain ⟨dp, hp, rest⟩ := Option.bind_eq_some_iff.mp success
        obtain ⟨dq, hq, hout⟩ := Option.bind_eq_some_iff.mp rest
        have hdp := ih hp
        have hdq := ih hq
        have hresult : dp + dq = result := Option.some.inj hout
        change derivative a p + derivative a q = result
        exact (congrArg₂ (fun x y : Regex String => x + y) hdp hdq).trans hresult
      | comp p q =>
        obtain ⟨empty, hempty, rest⟩ := Option.bind_eq_some_iff.mp success
        obtain ⟨dp, hp, hout⟩ := Option.bind_eq_some_iff.mp rest
        have hn : p.matchEpsilon = empty := ih hempty
        have hdp : derivative a p = dp := ih hp
        cases empty with
        | false =>
          have hresult : dp * q = result := Option.some.inj hout
          change derivative a (.comp p q) = result
          simpa only [derivative, hn, Bool.false_eq_true, if_false, hdp] using hresult
        | true =>
          obtain ⟨dq, hq, hout⟩ := Option.bind_eq_some_iff.mp hout
          have hdq : derivative a q = dq := ih hq
          have hresult : dp * q + dq = result := Option.some.inj hout
          change derivative a (.comp p q) = result
          simpa only [derivative, hn, ite_true, hdp, hdq] using hresult
      | star p =>
        obtain ⟨dp, hp, hout⟩ := Option.bind_eq_some_iff.mp success
        have hdp : derivative a p = dp := ih hp
        have hresult : dp * p.star = result := Option.some.inj hout
        change derivative a (.star p) = result
        simpa only [derivative, hdp] using hresult
    | matchWord p input =>
      cases input with
      | nil =>
          change boundedResult fuel (.nullable p) = some result at success
          exact ih (request := .nullable p) success
      | cons a rest =>
        obtain ⟨next, hnext, hout⟩ := Option.bind_eq_some_iff.mp success
        have hd : derivative a p = next := ih hnext
        have hr : fullMatch next rest = result := ih hout
        change fullMatch (derivative a p) rest = result
        simpa only [hd] using hr

end Mettapedia.GSLT.LanguageDef.RegexAuthoredComparison
