import Mettapedia.Languages.MeTTa.TensorDSL.Syntax
import Mettapedia.Languages.MeTTa.TensorDSL.Valence
import Mettapedia.Languages.MeTTa.TensorDSL.Reduction
import Mettapedia.Languages.MeTTa.TensorDSL.Lowering
import Mettapedia.Languages.MeTTa.TensorDSL.Properties

/-!
# MeTTa Tensor DSL (Optional Profile)

Optional, isolated tensor-index profile:
- foundational syntax
- valence and canonicalization algebra
- reduction/equality rules
- lowering into MeTTaIL patterns
- theorem obligations

This file is intentionally not imported by `Mettapedia.Languages.MeTTa` yet.

Provenance:
- Original implementation in this repository.
- Index notation UX inspiration reference:
  https://github.com/rebcabin/RelativityToolkit/releases/tag/v1.5.1
-/
