/-
# The minimal label, and why the backward half was the work

The draft's first open question asks for the minimal-label form of its
correctness result, and says which half is owed:

> the forward half descends for free and the backward half is what is owed.

The forward half is `label_le_redex`, already proved: every least label consists
of parallel partners that, together with the soup, complete a single rule
instance — so a label is never larger than one redex. It descends from the bag
construction because a label is one leg of an idem-pushout square.

The backward half asks the opposite: that the label is not merely *bounded* by
the redex but is *the least* one, and this file supplies it in the sharpest
available form. The label is not just minimal — it is **determined**:

```
    label = components ri.redexTerm - source
```

`label_eq_redex_sub_source`. The redex minus what the soup already supplies,
with nothing left to choose. `label_determined` is the consequence a minimality
statement is usually phrased as: two transitions of the same soup by the same
rule instance carry the same label, and reach the same target.

## Why it comes out determined rather than merely minimal

The bag characterisation gives two facts about a transition — that the soup and
the label together make the redex beside a context, and that the label and that
context share nothing. Counting one atom at a time, those two force the
question. If the soup already supplies as many copies of an atom as the redex
needs, the label supplies none and the context takes the surplus; if it supplies
fewer, the context takes none and the label supplies the shortfall. Neither case
leaves a choice, so the label is a difference rather than a minimum.

The disjointness hypothesis is doing all the work, and it is exactly the
condition `isIdemPushout_bag_iff` identifies with leastness. So "least label" and
"the label is the redex minus the soup" are the same statement, which is the
reason the backward half is available at all.

## The observer restriction

Everything here is parameterized by an admissibility predicate on rule
instances, as the labelled-transition development already was. So the
minimal-label form holds in particular when the observers are restricted to the
image of the translation, which `inTranslationImage` defines now that
`translate` exists. `minimal_label_in_translation_image` is that instantiation.
-/
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.ReactiveSystem
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.Translation

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCombinators

open CategoryTheory
open Mettapedia.GSLT.RedexRelativeCongruence (ReactionRule ActIPO)
open Mettapedia.GSLT.BagRelativePushout (bag)
open Comb

/-! ## The label is a difference -/

/-- **The least label is the redex minus what the soup already supplies.**  The
two facts the bag characterisation gives — that soup and label together make the
redex beside a context, and that label and context share nothing — leave no
choice at any atom. -/
theorem label_eq_redex_sub_source {label source context : Multiset Comb}
    {ri : RuleInstance}
    (hsrc : source + label = components ri.redexTerm + context)
    (hdisj : label ∩ context = 0) :
    label = components ri.redexTerm - source := by
  refine Multiset.ext' fun atom => ?_
  have counts := congrArg (Multiset.count atom) hsrc
  have shared := congrArg (Multiset.count atom) hdisj
  simp only [Multiset.count_add, Multiset.count_inter, Multiset.count_zero] at counts shared
  simp only [Multiset.count_sub]
  omega

/-- **The label and the residual context are both determined.** -/
theorem context_eq_source_sub_redex {label source context : Multiset Comb}
    {ri : RuleInstance}
    (hsrc : source + label = components ri.redexTerm + context)
    (hdisj : label ∩ context = 0) :
    context = source - components ri.redexTerm := by
  refine Multiset.ext' fun atom => ?_
  have counts := congrArg (Multiset.count atom) hsrc
  have shared := congrArg (Multiset.count atom) hdisj
  simp only [Multiset.count_add, Multiset.count_inter, Multiset.count_zero] at counts shared
  simp only [Multiset.count_sub]
  omega

/-- **The minimal-label form.**  A transition's label is the redex minus the
soup, so it is the least label enabling that rule instance and there is no other
one. -/
theorem actIPO_label_eq_difference (admissible : RuleInstance → Prop)
    {label source target : Multiset Comb}
    (step : ActIPO (rulesWhere admissible) (bag label) (bag source) (bag target)) :
    ∃ ri, ri.Valid ∧ admissible ri ∧
      label = components ri.redexTerm - source ∧
      target = components ri.reactumTerm + (source - components ri.redexTerm) := by
  obtain ⟨ri, hvalid, hadm, context, hsrc, hdisj, htgt⟩ :=
    (actIPO_bag_iff admissible label source target).mp step
  refine ⟨ri, hvalid, hadm, label_eq_redex_sub_source hsrc hdisj, ?_⟩
  rw [htgt, context_eq_source_sub_redex hsrc hdisj]

/-- **Two transitions of the same soup by the same rule carry the same label and
reach the same target.**  This is the uniqueness a minimality claim is usually
phrased as, and it follows because the label is a difference. -/
theorem label_determined (_admissible : RuleInstance → Prop)
    {source label₁ label₂ target₁ target₂ : Multiset Comb} {ri : RuleInstance}
    {context₁ context₂ : Multiset Comb}
    (hsrc₁ : source + label₁ = components ri.redexTerm + context₁)
    (hdisj₁ : label₁ ∩ context₁ = 0)
    (htgt₁ : target₁ = components ri.reactumTerm + context₁)
    (hsrc₂ : source + label₂ = components ri.redexTerm + context₂)
    (hdisj₂ : label₂ ∩ context₂ = 0)
    (htgt₂ : target₂ = components ri.reactumTerm + context₂) :
    label₁ = label₂ ∧ target₁ = target₂ := by
  refine ⟨?_, ?_⟩
  · rw [label_eq_redex_sub_source hsrc₁ hdisj₁,
      label_eq_redex_sub_source hsrc₂ hdisj₂]
  · rw [htgt₁, htgt₂, context_eq_source_sub_redex hsrc₁ hdisj₁,
      context_eq_source_sub_redex hsrc₂ hdisj₂]

/-! ## Restricting the observers to the translation's image -/

/-- The rule instances a translated program can actually exhibit: those whose
redex sits inside the compilation of some source term.  This is the observer
class the correctness result restricts to, and it is definable now that the
translation exists. -/
def inTranslationImage (s : Comb) : RuleInstance → Prop :=
  fun ri => ∃ (proxies : List Comb) (p : Src) (offset : ℕ),
    components ri.redexTerm ≤ components (translate s proxies p offset)

/-- **The minimal-label form holds under the restricted observer class.**  The
labelled-transition development was parameterized by an admissibility predicate
from the start, so restricting the observers to the translation's image is an
instantiation rather than a separate theorem. -/
theorem minimal_label_in_translation_image (s : Comb)
    {label source target : Multiset Comb}
    (step : ActIPO (rulesWhere (inTranslationImage s)) (bag label) (bag source)
      (bag target)) :
    ∃ ri, ri.Valid ∧ inTranslationImage s ri ∧
      label = components ri.redexTerm - source ∧
      target = components ri.reactumTerm + (source - components ri.redexTerm) :=
  actIPO_label_eq_difference (inTranslationImage s) step

/-- The restriction is not vacuous: every rule instance whose redex is the whole
compilation of some source term is admitted. -/
theorem inTranslationImage_of_translate (s : Comb) (proxies : List Comb)
    (p : Src) (offset : ℕ) (ri : RuleInstance)
    (h : ri.redexTerm = translate s proxies p offset) :
    inTranslationImage s ri :=
  ⟨proxies, p, offset, by rw [h]⟩

end Mettapedia.Languages.ProcessCalculi.RhoCombinators
