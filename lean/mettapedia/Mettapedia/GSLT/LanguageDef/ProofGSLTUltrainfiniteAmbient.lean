import Mettapedia.GSLT.LanguageDef.ProofGSLTUltrainfiniteInstances

/-!
# Compatibility import for the former ProofGSLT-local ambient layer

The ambient-first definitions now live at their correct abstraction level in
`Mettapedia.GSLT.Core.Ultrainfinite`.  ProofGSLT-specific instances live in
`ProofGSLTUltrainfiniteInstances`.

This module intentionally declares nothing.  It remains as an import bridge
while downstream work moves to the two correctly named modules; it does not
preserve a second copy of the theory or an alias vocabulary.
-/
