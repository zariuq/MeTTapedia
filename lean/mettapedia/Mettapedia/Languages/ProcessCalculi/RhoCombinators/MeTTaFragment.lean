/-
# The MeTTa consumer: the whole presentation passes, and what it costs

The lane needs a MeTTa fragment as the consumer of a name-free combinator
target. The expectation going in was a carve-out — some sub-language where
stored continuations and nested binders make the target pay, cut out with the
equation-freeness and collection-declaration predicates.

The census says otherwise, and the result is sharper than a carve-out.

## The census

Applying the admissibility condition to `mettaHE`:

```
    term constructors    52 of 52 positionally assemblable
    rewrite rules        58 of 58 assemblable
                          0 pattern binders
                          0 open collection tails
```

Contrast the authored rho presentation, which fails at both levels: `PPar` is
variadic and `PInput` binds; `Comm` binds *and* is variadic, and `ParCong` is
variadic.

**Why MeTTa passes is the point, and it is the discipline note made into
data.** MeTTa's binding is not a term-level binder and not a λ-binder in its
patterns: it is *metavariable* binding. A rule's left side matches and binds its
metavariables, and the right side uses them. So the two structural obstructions
that block rho — a binding parameter and a variadic position — simply do not
occur, at either level.

## What that does and does not establish

It establishes that the **code-constructor side transfers completely**: the
family is determined, one constructor per term constructor, and the compiled
cost of any pattern is the sum of its node arities plus one, which
`atomCount_assemble_eq_sum_arities` proves is the compiler's actual output.

It does **not** establish that the published translation transfers. That claim
is exactly what the lane's discipline forbids assuming, and the census is the
reason it must not be assumed rather than a reason it may be: what remains after
the structural obstructions are gone is metavariable *routing*, and a
metavariable occurring `n` times needs a distributor rather than a gate. The
router discipline is built (`Gate.lean`'s `distributor` and `broadcast`, the
five occurrence kinds in `Encoding.lean`), and that it is adequate for
metavariable binding in general is **not proved here**.

## The cost

What can be computed now is what that routing would cost, and it is bounded and
linear per rule rather than an estimate:

```
    metavariable occurrences in right-hand sides    211
    total routing + construction cost               572 atoms
    largest single rule                              17 atoms
```

`routingCost` charges one atom per metavariable occurrence — the distributor
edge that delivers it — plus the arity sum of the constructed nodes, plus the
forwarder. Summed over all 58 rules that is 572; no rule exceeds 17.
-/
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.Admissibility
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.SkeletonExtraction
import Mettapedia.Languages.MeTTa.HE.HELanguageDef

set_option autoImplicit false
set_option maxRecDepth 8000

namespace Mettapedia.Languages.ProcessCalculi.RhoCombinators

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.MeTTa.HE.LanguageDef (mettaHE)

/-! ## The structural census -/

/-- **Every MeTTa term constructor is positionally assemblable.**  No binding
parameter, no variadic parameter, in any of the 52. -/
theorem mettaHE_terms_all_assemblable :
    mettaHE.terms.all positionallyAssemblable = true := by decide

theorem mettaHE_terms_count : mettaHE.terms.length = 52 := by decide

/-- **Every MeTTa rewrite rule is assemblable.**  No pattern binder, no open
collection tail, in any of the 58. -/
theorem mettaHE_rules_all_assemblable :
    mettaHE.rewrites.all ruleAssemblable = true := by decide

theorem mettaHE_rules_count : mettaHE.rewrites.length = 58 := by decide

/-- No rule of the MeTTa presentation binds: its binding is metavariable
binding, which is matched and substituted rather than scoped. -/
theorem mettaHE_no_pattern_binders :
    mettaHE.rewrites.all
        (fun rule => !patternBinds rule.left && !patternBinds rule.right) = true := by
  decide

/-- No rule of the MeTTa presentation has a variadic position. -/
theorem mettaHE_no_open_tails :
    mettaHE.rewrites.all
        (fun rule => !patternVariadic rule.left && !patternVariadic rule.right)
      = true := by decide

/-! ## The routing cost -/

mutual

/-- How many metavariable occurrences a pattern has.  Each one is a distributor
edge in the compiled rule: the matched name has to arrive at every occurrence. -/
def fvarOccurrences : Pattern → ℕ
  | .bvar _ => 0
  | .fvar _ => 1
  | .apply _ arguments => fvarOccurrencesList arguments
  | .lambda _ body => fvarOccurrences body
  | .multiLambda _ _ body => fvarOccurrences body
  | .subst target replacement =>
      fvarOccurrences target + fvarOccurrences replacement
  | .collection _ elements _ => fvarOccurrencesList elements

def fvarOccurrencesList : List Pattern → ℕ
  | [] => 0
  | pattern :: rest => fvarOccurrences pattern + fvarOccurrencesList rest

end

mutual

/-- The arity sum of a pattern's constructed nodes: the same measure the arity
law charges, applied to a pattern rather than a one-hole context. -/
def patternWeight : Pattern → ℕ
  | .bvar _ => 0
  | .fvar _ => 0
  | .apply _ arguments => arguments.length + patternWeightList arguments
  | .lambda _ body => patternWeight body
  | .multiLambda _ _ body => patternWeight body
  | .subst target replacement => patternWeight target + patternWeight replacement
  | .collection _ elements _ => elements.length + patternWeightList elements

def patternWeightList : List Pattern → ℕ
  | [] => 0
  | pattern :: rest => patternWeight pattern + patternWeightList rest

end

/-- What compiling a rule's right-hand side costs: one atom per metavariable
occurrence to route it, the arity sum of the nodes to build it, and one
forwarder. -/
def routingCost (rule : RewriteRule) : ℕ :=
  fvarOccurrences rule.right + patternWeight rule.right + 1

/-- **The metavariable census.**  The whole presentation routes 211
occurrences. -/
theorem mettaHE_fvar_occurrences :
    (mettaHE.rewrites.map fun rule => fvarOccurrences rule.right).sum = 211 := by
  decide

/-- **The cost census.**  Compiling every rule of the MeTTa presentation costs
572 atoms in total. -/
theorem mettaHE_total_routing_cost :
    (mettaHE.rewrites.map routingCost).sum = 572 := by decide

/-- **No rule is expensive.**  The largest single rule compiles to 17 atoms, so
the cost is bounded per rule and not merely linear in aggregate. -/
theorem mettaHE_max_routing_cost :
    (mettaHE.rewrites.map routingCost).foldl max 0 = 17 := by decide

/-- Every rule's cost is at most the maximum, stated the way a bound is used. -/
theorem mettaHE_routing_cost_le :
    mettaHE.rewrites.all (fun rule => routingCost rule ≤ 17) = true := by decide

/-! ## Which rules the linear case covers

`rightHandSide_preserved` needs the right-hand side's metavariables to be
distinct.  That is decidable on the authored rules, and it separates them
exactly.
-/

/-- **Fifty-four of the fifty-eight rules have distinct metavariables in their
right-hand side**, so `rightHandSide_preserved` applies to them with its
distinctness hypothesis discharged. -/
theorem mettaHE_distinct_metavariable_rules :
    (mettaHE.rewrites.filter (fun rule => (patternFvars rule.right).Nodup)).length
      = 54 := by decide

/-- **And the four exceptions are these.**  Each repeats a metavariable in its
right-hand side, which is the case the duplicator composition handles. -/
theorem mettaHE_repeating_rules :
    (mettaHE.rewrites.filter
        (fun rule => !(patternFvars rule.right).Nodup)).map RewriteRule.name
      = ["IF_Start", "IA_Start_Typed", "IA_Start_Undef", "MC_Assert_Start"] := by
  decide

end Mettapedia.Languages.ProcessCalculi.RhoCombinators
