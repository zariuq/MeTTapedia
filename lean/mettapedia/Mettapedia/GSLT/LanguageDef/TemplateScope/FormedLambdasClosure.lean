import Mettapedia.GSLT.LanguageDef.TemplateScope.FormedLambdas

/-!
# The closure-part row

`formed_lambdas` row closure-part. A lambda written whole captures `$n`.
A lambda formed later applies that closure. Formation does not decide `$n`
again. The answer bag is `(Pair 1 5)`, the same bag as `written_captures`.
The closure cell is spelling `y`: the spelling inductive has no `g`.
-/

namespace Mettapedia.GSLT.LanguageDef.TemplateScope.FormedLambdas

open Mettapedia.GSLT.LanguageDef.TemplateScope

/-- `(let $g (lam w (Pair w $n)) (let $f (form z ($g z)) (let $n 5 ($f 1))))`. -/
def closurePart : A :=
  lt .y (lm .w (pair (pr .w) (sv .n)))
    (lt .f (fm .z (ap (sv .y) (pr .z)))
      (lt .n (k .n5) (ap (sv .f) (k .n1))))

/-- `formed_lambdas`, row closure-part. -/
theorem closure_part : bag cfgM closurePart = some [captured] := by
  decide

theorem closure_part_not_empty : bag cfgM closurePart ≠ some [] := by
  rw [closure_part]
  decide

end Mettapedia.GSLT.LanguageDef.TemplateScope.FormedLambdas
