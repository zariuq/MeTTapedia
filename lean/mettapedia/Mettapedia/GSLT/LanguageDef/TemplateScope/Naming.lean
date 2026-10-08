import Mettapedia.GSLT.LanguageDef.TemplateScope.Dropping
import Mettapedia.GSLT.LanguageDef.TemplateScope.Defunctionalization
import Mettapedia.GSLT.LanguageDef.TemplateScope.DefunTransform
import Mettapedia.GSLT.LanguageDef.TemplateScope.DefinitionFaces

/-!
# Template scope: naming across lambdas, equations and definitions

* `TemplateScope.Dropping` — lambda dropping, the inverse of lambda lifting:
  `run_dropped_call` (dropping preserves the bag of results with final stores),
  `dropArgs_lifted` and `lifted_dropArgs` (the two round trips),
  `liftedShape_iff` (lifting and dropping are inverse bijections between
  hygienic lambdas and equations of lifted shape).
* `TemplateScope.Defunctionalization` — Reynolds' defunctionalization on the
  model: every lambda a first-order closure, every application a dispatch to
  the closure's apply rule, which is the lambda's lifted equation
  (`dropArgs_eqn`).  `run_defun`: the evaluator and the target machine agree
  at every fuel on definedness, related results and identical stores;
  `answerBag_defun`: equal lambda-free answer bags.  `closures_are_data`:
  `let` and the matcher take a closure apart, never a lambda.
* `TemplateScope.DefunTransform` — the transformation `defun` and the rules
  `defunRule`: `rel_defun` (a term and its defunctionalization are related),
  `answerBag_defunctionalized` (the transformed program has the same answer
  bags), `defun_corpus` (the corpus targets are `defun` of their sources).
* `TemplateScope.DefinitionFaces` — a definition `f x := t` read
  operationally (the equation), by δβ definitional equality, and in Henkin
  models (a conservative extension, semantically and by derivations), with
  `three_faces` linking the readings on a first-order fragment.

This module only imports the four; it adds no declarations.
-/
