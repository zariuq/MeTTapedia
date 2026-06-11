import Mettapedia.Logic.Metaphysics.SiderNihilism
import Mettapedia.Logic.Metaphysics.MonadicSecondOrder
import Mettapedia.Logic.Metaphysics.UltrainfinitismTwoSemantics
import Mettapedia.Logic.Metaphysics.DedekindCategoricity
import Mettapedia.Logic.Metaphysics.UltrainfinitismCore

/-!
# Metaphysics: formal philosophy in Mettapedia

Formalized metaphysical arguments and their semantic infrastructure:

* `SiderNihilism` — Sider's modal argument against mereological nihilism (valid;
  premises 2–3 are theorems; premise 1 fails in the unrestricted space of mereologies).
* `MonadicSecondOrder` — monadic second-order logic over the Boolean-algebra signature
  with relativized (standard/Henkin) semantics.
* `UltrainfinitismTwoSemantics` — the ultrainfinitist core theory is satisfiable under
  standard and all-Henkin semantics by the same gunky witness; the free-ultrafilter
  axiom is Henkin-absolute and equivalent to atomlessness.
* `DedekindCategoricity` — full second-order induction pins ℕ (the contrast pole).
* `UltrainfinitismCore` — relative truth `UltraTrue`, principal collapse, the
  precise/open dial with its envelope theorems and dichotomy, free-vs-principal
  separation, and Łoś transfer (`ultraTrue_iff_uprod`, `ultrapower_elementary`).
-/
