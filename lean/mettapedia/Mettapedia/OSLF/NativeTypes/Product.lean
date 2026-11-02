import Mettapedia.OSLF.NativeTypes.Product.Query
import Mettapedia.OSLF.NativeTypes.Product.Export
import Mettapedia.OSLF.NativeTypes.Product.AcceptanceRows
import Mettapedia.OSLF.NativeTypes.Product.CertifiedForms
import Mettapedia.OSLF.NativeTypes.Product.LanguageRows
import Mettapedia.OSLF.NativeTypes.Product.FormerRows
import Mettapedia.OSLF.NativeTypes.Product.ReaderParityControls
import Mettapedia.OSLF.NativeTypes.Product.FileRoundTrip

/-!
# Executable OSLF as a product

- `Query`: the command-line front door: terms, types, labels and formulas as S-expressions, read and printed; settings
  (premise fuel, the bound of the finder's hint search); canonical forms for languages with bags; answers resumed across
  budgets; matrix rows checked against expected answers. Answers are asked of the language with its fitting scoped
  steps as congruences, and hold of the language read from the file (`answerWith_proved`, `answerWith_refuted`).
- `Export`: languages as `.module` files, each row as it is: anonymous binders and substitutions as such, and rows
  that declare their binding with the binder names whose reduction is the declaration.
- `AcceptanceRows`: the acceptance matrix's rows as the executable's matrix, each reading back from its text.
- `CertifiedForms`: canonical forms proved for one language (π, ambients, ρ, the grids modulo `A = B` and
  `Wrap x = x`), used for that language, along decidable language equality.
- `FileRoundTrip`: each language with certified forms, written as a file and read as the executable reads it, is
  that language.
- `LanguageRows`: the tree's instance languages (λ, TinyML, a Petri net, Peano arithmetic in λΠ modulo, π, CCS,
  ambients, ρ) asked as the executable asks them, every one written to the executable's matrix and run from its file.
- `FormerRows`: the matrix grown to formers × languages: every former a language's signature supports, at its sample
  terms, with the library's answers, and the coverage of each former by proved and refuted rows.

The executable itself is `lake exe oslf` (`Product.Main`).
-/
