/-
# GF Concrete Syntax

Concrete syntax maps abstract trees to strings in a specific language.
This includes:
- Parameterized linearization (case, number, gender, etc.)
- String operations (concatenation, inflection)
- Parameter tables
- Language-specific morphology

## References
- GF Tutorial: http://www.grammaticalframework.org/
- ResCze.gf: ~/claude/gf-rgl/src/czech/ResCze.gf (Czech resource)
-/

import Mettapedia.Languages.GF.Core
import Mettapedia.Languages.GF.Abstract

namespace Mettapedia.Languages.GF.Concrete

open Core

/-! ## Parameter Tables

Morphological parameters (case, number, gender) are indexed by enums.
Linearization looks up the appropriate form based on context.
-/

/-- Inflection table: maps parameters to forms -/
structure InflectionTable (Params : Type) [DecidableEq Params] where
  table : Params → String

namespace InflectionTable

/-- Lookup form for given parameters -/
def lookup {Params : Type} [DecidableEq Params]
    (t : InflectionTable Params) (p : Params) : String :=
  t.table p

end InflectionTable

/-! ## Morphophonology

Phonological rules that apply during linearization.
-/

namespace Morphophonology

/-- Vowel shortening (Czech: á→a, é→e, í→i, ó→o, ú/ů→u, ý→y)
    Used in many Czech declension patterns -/
def shortenVowel (c : Char) : Char :=
  match c with
  | 'á' => 'a'
  | 'é' => 'e'
  | 'í' => 'i'
  | 'ó' => 'o'
  | 'ú' => 'u'
  | 'ů' => 'u'
  | 'ý' => 'y'
  | _ => c

/-- Apply vowel shortening to last long vowel in string
    Example: "pán" → "pan", "žena" → "žena" (no long vowels) -/
def shortenLastVowel (s : String) : String :=
  let chars := s.toList
  -- Scan from right to left to find the last long vowel
  let rec go : List Char → List Char → List Char
    | [], acc => acc  -- No long vowel found, return unchanged
    | c :: cs, acc =>
        let c' := shortenVowel c
        if c' != c then
          -- Found long vowel to shorten
          cs ++ [c'] ++ acc
        else
          go cs (c :: acc)
  String.ofList (go chars.reverse [])

end Morphophonology

end Mettapedia.Languages.GF.Concrete
