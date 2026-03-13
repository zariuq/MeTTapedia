import Mettapedia.Logic.HOL.Syntax.Type
import Mettapedia.Logic.HOL.Syntax.Term
import Mettapedia.Logic.HOL.Syntax.Subst
import Mettapedia.Logic.HOL.Syntax.Closed
import Mettapedia.Logic.HOL.Semantics.Henkin
import Mettapedia.Logic.HOL.Semantics.Extensionality
import Mettapedia.Logic.HOL.Semantics.SetBased
import Mettapedia.Logic.HOL.Probabilistic
import Mettapedia.Logic.HOL.Derivation
import Mettapedia.Logic.HOL.Soundness
import Mettapedia.Logic.HOL.Embedding.FirstOrder
import Mettapedia.Logic.HOL.WorldModel
import Mettapedia.Logic.HOL.WorldModelCompleteness
import Mettapedia.Logic.HOL.LogicalInduction

/-!
# Real Higher-Order Logic

Public entrypoint for the real Church-style HOL layer:

- intrinsically typed syntax,
- Henkin semantics,
- direct set-based grounding into Henkin models,
- infinitary semantic probability over measurable indexed model spaces,
- hierarchical and infinite-order semantic probability over measures on those
  indexed model spaces,
- a small natural-deduction core with soundness,
- first-order embedding,
- and the world-model bridge over pointed Henkin models.
- a logical-induction-ready dynamic belief layer over closed HOL formulas.
-/
