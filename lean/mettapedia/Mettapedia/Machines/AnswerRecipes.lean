import Mettapedia.Machines.AnswerRecipes.Recipes
import Mettapedia.Machines.AnswerRecipes.TierBoundary

/-!
# Answer recipes and the compiled tier's boundary

A cached answer is replayed, and a compiled tier passes answers in and out, without
changing what any variable is.  Each variable of an answer is the caller's, a retained
identity, or the answer's own; caller variables follow the caller, retained identities
stay exactly, and the answer's own variables are fresh in every replay and every export.

* `Recipes`: recipes (the solved input and the output abstracted together by slot kind)
  and replays; `replay_recipe` (a replay is a local variant of the renamed answer) and
  `replay_agrees` (for every variant-invariant execution, replays agree with the uncached
  execution of the renamed call, answer by answer); controls for aliasing, independence,
  retained identities, the caller's identity and the input-output link; negative controls
  for a recipe without the retained kind, one that keeps answer variables, separate
  instantiation, a non-injective supply, and a key that renames a caller variable onto a
  retained identity.
* `TierBoundary`: one table keyed by identity across every route (`cellOf_injective`),
  kinds joined over arrivals (`kindOf_importAll_perm`, `kindOf_importAll_own_iff`),
  exports by kind (`exportTerm_localVariant`, `exportTerm_own_vars`, `exports_disjoint`),
  the end-to-end law `replay_through_tier`, and the tier's current shapes against it
  (`enterFirst_order_dependent`, `split_cells`, `hostOwn_loses_retained`,
  `hostRetained_shares`).

**What the tier's import and export must do, per kind.**
* *Import*, every route (the call's arguments, a host goal's answers, a stored value):
  look the identity up among the call's cells and the cursor's table first; one identity
  has one cell; a known identity joins what the new arrival knows.  A stored value's
  variable arrives as retained; a host answer's variable arrives as the answer's own
  only when its producer introduced it for that answer (a replay's fresh variables, a
  host goal's new variables), and as retained otherwise.
* *Export*, an answer or a host goal's arguments: a caller cell as the caller's
  variable, a retained cell as its identity, an answer-local cell as a variable fresh to
  that export; a collection's copy freshens every cell.
* *Record and replay*: abstract the solved input and the output together; slot the
  call's variables as caller slots, keep the identities from before the call as
  retained, slot the rest as the answer's own; key the call by its variables up to a
  renaming that fixes the retained identities; replay with one fresh supply for the
  whole record.
-/
