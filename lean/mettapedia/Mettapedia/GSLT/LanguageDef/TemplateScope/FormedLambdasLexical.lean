import Mettapedia.GSLT.LanguageDef.TemplateScope.FormedLambdas
import Mettapedia.GSLT.LanguageDef.TemplateScope.FormedLambdasNestSteps
import Mettapedia.GSLT.LanguageDef.TemplateScope.FormedLambdasCapturesSteps
import Mettapedia.GSLT.LanguageDef.TemplateScope.FormedLambdasWrittenSteps
import Mettapedia.GSLT.LanguageDef.TemplateScope.FormedLambdasNewSteps
import Mettapedia.GSLT.LanguageDef.TemplateScope.FormedLambdasSameSteps
import Mettapedia.GSLT.LanguageDef.TemplateScope.FormedLambdasEscapingSteps

namespace Mettapedia.GSLT.LanguageDef.TemplateScope.FormedLambdas

open Mettapedia.GSLT.LanguageDef.TemplateScope

/-!
Lexical-fresh bags are `answersCfg` of the shipped elaborator.
Each proof rewrites `step` and lifts the run with `run_mono`.
-/

theorem formed_captures_LF : bag cfgLF formedCaptures = some [pairT g1 g2] :=
  formedCaptures_bag

theorem written_owns_LF : bag cfgLF writtenOwns = some [pairT g1 g2] :=
  writtenOwns_bag

theorem formed_new_owns_LF : bag cfgLF formedNew = some [pairT g1 g2] :=
  formedNew_bag

theorem pattern_same_name_outside : bag cfgLF sameOut = some [pairT g1 g2] :=
  sameOut_bag

theorem escaping_distinct_bag :
    bag cfgLF escapingDistinct =
      some [pairT (pairT (.sym .n1) (.sym .n7)) (pairT (.sym .n2) (.sym .n8))] :=
  escapingDistinct_bag

theorem formed_captures_LF_not_empty : bag cfgLF formedCaptures ≠ some [] := by
  rw [formed_captures_LF]
  intro h
  injection h with h
  injection h

-- Rule M answers the empty bag. Lexical fresh answers the pair.

theorem formed_M_differs_from_LF :
    bag cfgM formedCaptures ≠ bag cfgLF formedCaptures := by
  rw [formed_captures_M, formed_captures_LF]
  intro h
  injection h with h
  injection h

/-- `lexical_default`, row written. The same program as `pattern_written`. -/
theorem lexical_default_written : bag cfgLF writtenOwns = some [pairT g1 g2] :=
  written_owns_LF

/-- `lexical_default`, row cons-atom. The same program as the four pattern heads. -/
theorem lexical_default_cons : bag cfgLF formedCaptures = some [pairT g1 g2] :=
  formed_captures_LF

/-- `lexical_pattern_activations`, row written. -/
theorem pattern_written : bag cfgLF writtenOwns = some [pairT g1 g2] :=
  written_owns_LF

/-- `lexical_pattern_activations`: cons, union, substitution head, and beta head. -/
theorem pattern_cons : bag cfgLF formedCaptures = some [pairT g1 g2] :=
  formed_captures_LF

theorem pattern_union : bag cfgLF formedCaptures = some [pairT g1 g2] :=
  formed_captures_LF

theorem pattern_head : bag cfgLF formedCaptures = some [pairT g1 g2] :=
  formed_captures_LF

theorem pattern_beta : bag cfgLF formedCaptures = some [pairT g1 g2] :=
  formed_captures_LF

/-- `lexical_pattern_activations`, row explicit-new. -/
theorem pattern_explicit_new : bag cfgLF formedNew = some [pairT g1 g2] :=
  formed_new_owns_LF

theorem lexical_default_nest : bag cfgLF nest = some [.sym .n7] := by
  decide

theorem lexical_default_pair : bag cfgLF pairLets = some [pairT (.sym .n8) (.sym .n7)] := by
  decide

/-- The route prints this fresh slot as `$y#1`. -/
theorem lexical_default_new_inner :
    bag cfgLF newInner = some [.var (.inst [2, 1, 2] (.src ([2, 0], .y)))] := by
  decide

theorem pattern_outer_source : bag cfgLF nest = some [.sym .n7] := lexical_default_nest

theorem pattern_shadow : bag cfgLF shadow = some [pairT (.sym .n2) (.sym .n1)] := by
  decide

theorem pattern_rhs_outside : bag cfgLF rhsOut = some [pairT (.sym .n1) (.sym .n1)] := by
  decide

theorem pattern_repeated_refusal : bag cfgLF repeated = some [] := by
  decide

theorem pattern_repeated_not_wrong : bag cfgLF repeated ≠ some [.sym .wrong] := by
  rw [pattern_repeated_refusal]
  decide

theorem escaping_bag : bag cfgLF escaping = some [pairT (.sym .n1) (.sym .n2)] := by
  decide

end Mettapedia.GSLT.LanguageDef.TemplateScope.FormedLambdas
