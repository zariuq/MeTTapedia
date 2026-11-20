import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerSyntax
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerSyntaxDeclarations
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerSyntaxRecursion
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerSyntaxEval
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerSyntaxLimit
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerSyntaxControls

/-!
# Typed syntax in the verified model: well-typed expressions indexed by their type

* `TowerSyntax`: the package. The Booleans, the object types `ty` (`tnum`, `tbool`), the untyped
  expressions `raw` (a simple inductive type: literals, Boolean literals, addition, conditional, zero
  test), the computed equations `is-num`, `is-bool` of the index, the value type `val`, the typing
  relation `typed : raw → ty → U0` by recursion on the expression, the transports `at-num`, `at-bool`
  and the recursion principle `syntax-rec`, with their rules and stages.
* `TowerSyntaxDeclarations`: every inductive type and every family by recursion is declared, stage
  by stage, each over the stage before it.
* `TowerSyntaxRecursion`: the transports and the recursion principle are declared; every model
  hypothesis of the package holds (`constants`, `facts`, `roots`, `heads`, `algebra`).
* `TowerSyntaxEval`: `exp t = Σ (r : raw). typed r t` with the constructors `lit`, `blit`, `add`,
  `ite`, `iszero` typed, the recursion principle typed with a computation rule on each constructor at
  open arguments, the interpreter `eval : exp t → val t`, and `eval (add (lit 2) (lit 3)) ≡ 5` by
  conversion. Controls: the constructors differ, an ill-indexed literal is rejected, the family is not
  constantly a unit, the recursion is stuck on a variable expression, and two typing proofs of one
  untyped expression give two different elements.
* `TowerSyntaxLimit`: a recursive family on the index alone is free of itself at a nullary index, so a
  constructor at the index of its own arguments needs an earlier self-referential carrier; the naive
  self-referential right-hand side is typed in no stage that does not declare it.
* `TowerSyntaxControls`: the type former `exp` is injective at every index, open ones included; two
  typing proofs of one untyped expression give elements equal in the identity type, not by conversion.
-/
