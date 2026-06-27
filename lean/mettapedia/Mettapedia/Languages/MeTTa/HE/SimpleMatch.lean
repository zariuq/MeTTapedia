import Mettapedia.Languages.MeTTa.HE.Types

/-!
# HE legacy one-way matcher

The coarse `simpleMatch` surface is the historical one-way matcher used by the
older HE equation-query path and several control-form helpers. It is kept as a
shared primitive so the faithful `matchAtoms` / `mergeBindings` layer can reuse
the same atom utilities without forcing a module cycle through `Space.lean`.

`simpleMatch` is deliberately **not** the authoritative HE query matcher for
equations; G3 moves that public query surface onto `matchAtoms`.
-/

namespace Mettapedia.Languages.MeTTa.HE

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-- Simple one-way pattern matching: does `pattern` match `target`?
    Variables in `pattern` bind to subterms of `target`.
    Returns resulting bindings on success.
    Ref: legacy equation-query helper, still used by several control forms. -/
def simpleMatch (pattern target : Atom) (b : Bindings) (fuel : Nat) : Option Bindings :=
  match fuel with
  | 0 => none
  | n + 1 =>
    match pattern with
    | .var v =>
      match b.lookup v with
      | some existing => if existing == target then some b else none
      | none => some (b.assign v target)
    | .symbol s =>
      match target with
      | .symbol t => if s == t then some b else none
      | _ => none
    | .grounded g =>
      match target with
      | .grounded h => if g == h then some b else none
      | _ => none
    | .expression ps =>
      match target with
      | .expression ts =>
        if ps.length != ts.length then none
        else simpleMatchList ps ts b n
      | _ => none
where
  simpleMatchList : List Atom → List Atom → Bindings → Nat → Option Bindings
    | [], [], b, _ => some b
    | p :: ps, t :: ts, b, fuel =>
      match simpleMatch p t b fuel with
      | some b' => simpleMatchList ps ts b' fuel
      | none => none
    | _, _, _, _ => none

end Mettapedia.Languages.MeTTa.HE
