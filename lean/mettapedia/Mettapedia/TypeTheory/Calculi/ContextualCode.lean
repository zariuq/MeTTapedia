import Mettapedia.TypeTheory.Calculi.ContextualCode.Syntax
import Mettapedia.TypeTheory.Calculi.ContextualCode.Reduction
import Mettapedia.TypeTheory.Calculi.ContextualCode.Confluence
import Mettapedia.TypeTheory.Calculi.ContextualCode.Embedding
import Mettapedia.TypeTheory.Calculi.ContextualCode.Matching
import Mettapedia.TypeTheory.Calculi.ContextualCode.Controls
import Mettapedia.TypeTheory.Calculi.ContextualCode.Surface
import Mettapedia.TypeTheory.Calculi.ContextualCode.Destructuring
import Mettapedia.TypeTheory.Calculi.ContextualCode.Freshness

/-!
# Contextual code

The sealed-code calculus with templates: code with parameters bound inside it.
`cquote k M` is closed in every outer variable and binds `k` parameters; a
sealed name is the case `k = 0`. Code is made only by `lift`, which evaluates
and seals; the bracket `T[x := A]` is derived from it. Matching inspects code
with patterns whose holes are filled by closed code, so the variables bound
inside code are rigid for matching.

* `Term.subst_subst`, `Pat.fill_bind`, `Pat.fill_rename`, `Pat.fill_injective`,
  `Pat.mentions_fill`: the laws of substitution and of filling holes; holes
  never capture a variable of the code.
* `Step.subst`, `church_rosser`, `template_unique`, `name_unique`: reduction is
  stable under substitution and confluent, so a program has at most one
  template and one name.
* `instAll_iff`: the bracket names exactly the normal form of the code filled
  as written; `instAll_asWritten`: the two agree when that code is normal.
* `step_embed`, `step_of_embed`, `normal_embed`, `normal_of_embed`: the
  sealed-code calculus is the fragment without parameters and matching.
* `issue579_no_match`, `issue579_hole_stuck`, `issue579_subst`: a parameter is
  rigid for matching and for substitution.
* `leakyLet_incoherent`, `leakyLet_disagrees`, `leakyQuote_incoherent`,
  `bothBrackets_incoherent`: a `let` that enters quotations, a quotation that
  substitution enters, and a bracket with two meanings each give one program
  two results.
* `Surface.resolve_perm`, `Surface.alpha_quote`: reading names commutes with
  renaming them, so α-equivalent quotations are one template.
* `openFirst_closeSym`, `closeSym_openFirst`, `run_rawBody`,
  `openFresh_equivariant`, `openFresh_capture`: two readings of taking a
  binder apart.
* `no_self_code`: no program reaches its own name.
-/

namespace Mettapedia.TypeTheory.Calculi.ContextualCode

#print axioms Term.subst_subst
#print axioms Pat.fill_injective
#print axioms Pat.mentions_fill
#print axioms Pat.fill_bind
#print axioms Pat.fill_rename
#print axioms Step.subst
#print axioms Normal.no_step
#print axioms steps_appsN_lamN
#print axioms instAll_name
#print axioms instAll_asWritten
#print axioms lift_reaches_normal
#print axioms church_rosser
#print axioms normal_form_unique
#print axioms template_unique
#print axioms name_unique
#print axioms instAll_iff
#print axioms embed_subst
#print axioms step_embed
#print axioms step_of_embed
#print axioms normal_embed
#print axioms normal_of_embed
#print axioms hole_never_binds
#print axioms issue579_subst
#print axioms issue579_no_match
#print axioms issue579_match
#print axioms issue579_hole_stuck
#print axioms issue579_hole_takes_name
#print axioms parts_example
#print axioms show_constant_body
#print axioms show_bound_body_stuck
#print axioms leakyLet_disagrees
#print axioms leakyLet_incoherent
#print axioms letAsBeta_name_unique
#print axioms leakyQuote_incoherent
#print axioms bothBrackets_incoherent
#print axioms derivedBracket_not_asWritten
#print axioms Surface.resolve_perm
#print axioms Surface.alpha_quote
#print axioms alpha_example
#print axioms alpha_example_by_swap
#print axioms lambda_names_quote
#print axioms lambda_names_reference
#print axioms lambda_names_pair
#print axioms lambda_names_passed_name
#print axioms lam_dollar_quote
#print axioms let_dollar_quote
#print axioms let_dollar_quote_not_five
#print axioms hygiene_example
#print axioms hygiene_not_captured
#print axioms bracket_example
#print axioms pair_bracket_all
#print axioms pair_bracket_twice
#print axioms openFirst_closeSym
#print axioms closeSym_openFirst
#print axioms run_rawBody
#print axioms rawBody_bracket
#print axioms close_openFresh
#print axioms openFresh_equivariant
#print axioms openFresh_capture
#print axioms close_fresh_is_raw
#print axioms bounded_steps
#print axioms no_self_code
#print axioms fresh_of_size_le

end Mettapedia.TypeTheory.Calculi.ContextualCode
