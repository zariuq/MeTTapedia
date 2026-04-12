import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.Types
import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.Terms
import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.Sequent
import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.HeytingAlgebra
import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.ApplicativeStructure
import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.Models
import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.Soundness
import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.LowerBoundExtensionRegression
import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.Hintikka
import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.Completeness
import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.CompletenessRegression
import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SourceMap

/-!
# Intuitionistic HOL in Codex

Fresh archive-free staging area for the DeMarco-Lipton proof spine.

This umbrella intentionally exposes only the native files under
`Mettapedia/AutoBooks/Codex/IntuitionisticHOL`:

- `Types`, `Terms`, `Sequent`: syntax and cut-free sequent calculus.
- `HeytingAlgebra`, `ApplicativeStructure`, `Models`: semantic interfaces.
- `Soundness`: the first native soundness layer, currently proved for the
  global-model specialization of the paper semantics.
- `Hintikka`, `Completeness`: staging modules for the next completeness work.
- `SourceMap`: precise paper-to-code bookkeeping.

No file in this umbrella imports `Mettapedia/Logic/HOL/_archive`.
-/
