import Mettapedia.SetTheory.CarveOuts.Sheaves.Sections
import Mettapedia.SetTheory.CarveOuts.Sheaves.Naturals
import Mettapedia.SetTheory.CarveOuts.Sheaves.PowerClasses
import Mettapedia.SetTheory.CarveOuts.Sheaves.Representability
import Mettapedia.SetTheory.CarveOuts.Sheaves.CantorPowers

/-!
# Power classes, natural numbers and representability for sheaves on a space

* `Sections`: gluing and separation on covers; finite limits, monos and subobjects read on
  sections.
* `Naturals`: the natural numbers object is unique up to isomorphism; in sheaves it is the sheaf
  of locally constant natural numbers, and it is small (axiom (I)).
* `PowerClasses`: the sheaf of small local families of sections, with membership; it classifies
  small relations (axiom (P1)).
* `Representability`: with values in a universe above the small fibres, membership in the power
  class of a generic sheaf is a universal small map (axiom (R)); with values in a universe whose
  types are all small, (R) fails by Cantor's theorem.
* `CantorPowers`: sheaves on Cantor space one universe up satisfy the small-map axioms
  (S1)–(S5), (P1), (I) and (R); sheaves on Cantor space with values in `Type` do not.

These constructions use host choice. The ambient categorical structure, indexed final
coalgebra, and interpretation of its material set axioms are separate obligations.
-/
