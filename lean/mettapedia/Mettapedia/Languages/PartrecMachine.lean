import Mettapedia.Languages.PartrecMachine.LanguageDef
import Mettapedia.Languages.PartrecMachine.Adequacy
import Mettapedia.Languages.PartrecMachine.Realization
import Mettapedia.Languages.PartrecMachine.Rice
import Mettapedia.Languages.PartrecMachine.BoundedReduction

/-!
# The partial-recursive machine as an authored language

Mathlib's `Turing.ToPartrec` machine authored as a `LanguageDef`; adequacy of its
reduction against Mathlib's machine, and Mathlib's machine realized in the theory
generated from it; Rice's theorem for sets of its programs, read off that
reduction; and the bounded-reduction escape.
-/
