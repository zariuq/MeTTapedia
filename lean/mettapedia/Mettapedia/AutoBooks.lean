/-
# AutoBooks — Autoformalization of Mathematical Textbooks

A formalization of three foundational textbooks in Lean 4 + Mathlib,
as part of the QED project to formalize all possible mathematical knowledge.

## Books Formalized

1. **Seven Sketches in Compositionality** — Fong & Spivak (2018)
   Applied category theory: preorders, monoidal categories, enrichment,
   profunctors, props, operads, sheaves, toposes.

2. **Categorical Logic and Type Theory** — Jacobs (1999)
   Fibrations, simple type theory, equational/first-order/higher-order logic,
   effective topos, internal categories, polymorphism, advanced fibrations.

3. **Modal Homotopy Type Theory** — Corfield (2020)
   Dependent types, homotopy types, modal types (cohesion),
   spatial types, differential cohesion.
-/

-- Live AutoBooks surface
import Mettapedia.AutoBooks.Codex.Henkin1950
import Mettapedia.AutoBooks.Codex.SevenSketches
import Mettapedia.AutoBooks.Codex.Jacobs
import Mettapedia.AutoBooks.Codex.ModalHoTT

-- Archived exploratory work lives under `Mettapedia/AutoBooks/_archive`.
-- The native Codex intuitionistic branch is currently under active repair and
-- is intentionally kept out of this umbrella until it is green again.
