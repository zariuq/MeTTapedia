# Historical contract and determinism calculus

These six modules preserve the earlier runtime/static contract study. They model
newtypes, unions, retained contracts and a determinism-grade analysis. Their
theorems apply to the definitions here; they are not a specification or a verified
implementation of the current runtime predicate-typing candidate.

Their module and declaration namespace is now
`Mettapedia.Languages.MeTTa.PeTTa.Legacy.ContractTyping`. The mathematical
definitions and proof bodies are preserved, apart from the namespace/import
relocation.

Use `Mettapedia.Logic.ConstraintTypes` for the generic foundation and
`Mettapedia.Languages.MeTTa.PeTTa.RuntimeTyping` for the current call protocol.
Neither imports this historical calculus.
