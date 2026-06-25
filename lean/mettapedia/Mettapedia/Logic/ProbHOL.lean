import Mettapedia.Logic.HOL.Probabilistic
import Mettapedia.Logic.HOL.LogicalInduction

/-!
# ProbHOL

This module is the deliberately modest top-level wrapper for probabilistic
reasoning about closed HOL formulas.

It now re-exports two distinct but compatible layers:

- the infinitary-first semantic `ProbHOL` layer over measurable indexed spaces
  of pointed Henkin models, and
- the hierarchical / infinite-order semantic layer obtained by placing
  uncertainty over measures on those model spaces, and
- the logical-induction-ready dynamic belief/process layer over coded closed
  HOL formulas.

Following Garrabrant, Benson-Tilsen, Critch, Soares, and Taylor,
*Logical Induction*, arXiv:1609.03543v5 (2020), the second layer is explicitly
time-indexed and deductive-process-parametric.

Important boundary:

- canonical HOL truth remains in `Mettapedia/Logic/HOL/`,
- the static HOL↔WM truth lens remains in `Mettapedia/PLN/Bridges/HOL/PLNWorldModelHOLCore.lean`,
- semantic probability over HOL formulas now lives in
  `Mettapedia/Logic/HOL/Probabilistic/`,
- hierarchical and infinite-order semantic `ProbHOL` is built there via
  Kyburg-style flattening over model-space measures,
- PLN-facing empirical, benchmark, belief, and regression bridges live under
  `Mettapedia/PLN/Bridges/HOL/`,
- and this file still does **not** claim the fully fused dynamic theory of
  logical-induction belief processes over semantic probabilities of Henkin-model
  events.

So `ProbHOL` is now the compact top-level wrapper for:

- semantic probability of HOL formulas, and
- hierarchical and infinite-order semantic uncertainty about HOL formulas, and
- LI-ready belief dynamics about HOL formulas,

while keeping those two layers explicitly distinct.
-/
