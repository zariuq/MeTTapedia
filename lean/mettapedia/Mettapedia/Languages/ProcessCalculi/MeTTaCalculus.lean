import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Syntax
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Premises
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.StructuralCongruence
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Reduction
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.SpaceChannelBoundary
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.SpaceInteraction
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.CausalInteraction
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.GSLTInteraction
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Adequacy
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Interoperability
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.PaperMap
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regression

/-!
# Process Calculi: MeTTa-Calculus

Language-focused facade for the symmetric reflective MeTTa-calculus.

This module is intentionally small and shares:

- `MeTTaIL.Pattern` as the process/term substrate
- generic premise-aware rewriting (`OSLF.MeTTaIL.Engine`)
- generic reflexive-transitive closure (`ProcessCalculi.Common.Star`)

Source alignment: the F1R3FLY MeTTa-calculus manuscript,
`metta-calculus.core.tex`.
-/
