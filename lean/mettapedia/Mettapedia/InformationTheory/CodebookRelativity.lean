import Mettapedia.Computability.KolmogorovComplexity.Basic
import Mathlib.Data.Countable.Basic

/-!
# Codebook relativity of strict description-length selection

A prefix codebook is representation data attached to a hypothesis type.  A
selector is representation-invariant only when changing that data cannot
change its pairwise preference.  Reindexing one codebook by a transposition
therefore gives a general obstruction: any selector that strictly prefers the
shorter codeword reverses its ranking whenever two unequal lengths are
swapped.

The obstruction is not a finiteness phenomenon.  A concrete unary codebook on
`Nat` supplies a countably infinite witness.  Conversely, finite binary strings
cannot encode an uncountable hypothesis class injectively.  This separates
three issues which are often conflated:

* finite prior approximation by code lengths;
* representation dependence of strict shorter-is-better selection;
* existence of a finite-string codebook at all.

The no-go does not apply to semantic or ontological criteria that ignore the
codebook.  `liftRelation` and `liftRelation_codebookInvariant` state that
positive control explicitly.

Reference: M. T. Bennett, *The Wrong Razor*, Proposition A.5, Corollary A.9,
and Remark A.10 in the complete-proofs appendix (2026).  The transposition
theorem below strengthens Corollary A.9 from a two-element example to every
codebook containing two distinct lengths; the infinite and uncountable
results are extensions proved here.
-/

set_option autoImplicit false

namespace Mettapedia.InformationTheory.CodebookRelativity

universe uHypothesis uValue

/-- A binary prefix codebook for a hypothesis type.  Distinct hypotheses must
not have codewords in the prefix relation in either ordered direction. -/
structure PrefixCodebook (Hypothesis : Type uHypothesis) where
  encode : Hypothesis → List Bool
  prefixFree : ∀ {left right}, left ≠ right →
    ¬ encode left <+: encode right

namespace PrefixCodebook

variable {Hypothesis : Type uHypothesis}

/-- Prefix-freeness entails injectivity of the encoder. -/
theorem injective (codebook : PrefixCodebook Hypothesis) :
    Function.Injective codebook.encode := by
  intro left right equalCode
  by_contra different
  exact codebook.prefixFree different (by simp [equalCode])

/-- Codeword length in a declared codebook. -/
def length (codebook : PrefixCodebook Hypothesis)
    (hypothesis : Hypothesis) : Nat :=
  (codebook.encode hypothesis).length

/-- Reindex a codebook along a semantic equivalence.  The hypotheses and
their meanings are unchanged; only codeword assignment changes. -/
def reindex (codebook : PrefixCodebook Hypothesis)
    (equiv : Hypothesis ≃ Hypothesis) : PrefixCodebook Hypothesis where
  encode := codebook.encode ∘ equiv
  prefixFree := by
    intro left right different
    exact codebook.prefixFree (equiv.injective.ne different)

@[simp]
theorem encode_reindex (codebook : PrefixCodebook Hypothesis)
    (equiv : Hypothesis ≃ Hypothesis) (hypothesis : Hypothesis) :
    (codebook.reindex equiv).encode hypothesis =
      codebook.encode (equiv hypothesis) :=
  rfl

@[simp]
theorem length_reindex (codebook : PrefixCodebook Hypothesis)
    (equiv : Hypothesis ≃ Hypothesis) (hypothesis : Hypothesis) :
    (codebook.reindex equiv).length hypothesis =
      codebook.length (equiv hypothesis) :=
  rfl

end PrefixCodebook

/-! ## Selectors and invariance -/

/-- A codebook-indexed pairwise selection relation. -/
abbrev Selector (Hypothesis : Type uHypothesis) :=
  PrefixCodebook Hypothesis → Hypothesis → Hypothesis → Prop

/-- The selector uses the ordinary shorter-is-better ordering nontrivially:
every strict length comparison induces a strict preference. -/
def StrictlyPrefersShorter {Hypothesis : Type uHypothesis}
    (selector : Selector Hypothesis) : Prop :=
  ∀ (codebook : PrefixCodebook Hypothesis) {shorter longer},
    codebook.length shorter < codebook.length longer →
      selector codebook shorter longer ∧
        ¬ selector codebook longer shorter

/-- Changing a codebook never changes the selector's pairwise judgment. -/
def CodebookInvariant {Hypothesis : Type uHypothesis}
    (selector : Selector Hypothesis) : Prop :=
  ∀ (first second : PrefixCodebook Hypothesis) (left right : Hypothesis),
    selector first left right ↔ selector second left right

/-- A semantic relation can be viewed as a selector which ignores codebook
data. -/
def liftRelation {Hypothesis : Type uHypothesis}
    (relation : Hypothesis → Hypothesis → Prop) : Selector Hypothesis :=
  fun _ ↦ relation

/-- Any genuinely codebook-independent relation is representation-invariant. -/
theorem liftRelation_codebookInvariant
    {Hypothesis : Type uHypothesis}
    (relation : Hypothesis → Hypothesis → Prop) :
    CodebookInvariant (liftRelation relation) := by
  intro first second left right
  rfl

/-- Swapping unequal codeword lengths reverses every nontrivial
shorter-is-better selector.  No finiteness assumption is used. -/
theorem not_codebookInvariant_of_unequal_lengths
    {Hypothesis : Type uHypothesis}
    (selector : Selector Hypothesis)
    (usesLength : StrictlyPrefersShorter selector)
    (codebook : PrefixCodebook Hypothesis)
    {shorter longer : Hypothesis}
    (lengthLess : codebook.length shorter < codebook.length longer) :
    ¬ CodebookInvariant selector := by
  classical
  intro invariant
  let swapped := codebook.reindex (Equiv.swap shorter longer)
  have preferred := (usesLength codebook lengthLess).1
  have reversedLengths : swapped.length longer < swapped.length shorter := by
    simpa [swapped] using lengthLess
  have reversed := usesLength swapped reversedLengths
  exact reversed.2 ((invariant codebook swapped shorter longer).mp preferred)

/-! ## Countably infinite positive witness -/

open KolmogorovComplexity

/-- The existing self-delimiting unary machine prefix is prefix-free when used
as a codebook on natural-number hypotheses. -/
def natCodebook : PrefixCodebook Nat where
  encode := machinePrefix
  prefixFree := by
    intro left right different isPrefix
    obtain ⟨suffix, codeEq⟩ := isPrefix
    have decoded : some (left, suffix) = some (right, []) := by
      calc
        some (left, suffix) =
            decodeMachinePrefix (machinePrefix left ++ suffix) := by
              symm
              exact decodeMachinePrefix_machinePrefix left suffix
        _ = decodeMachinePrefix (machinePrefix right) := by rw [codeEq]
        _ = some (right, []) := by
          simpa using decodeMachinePrefix_machinePrefix right []
    exact different (by simpa using congrArg (fun value ↦ value.map Prod.fst) decoded)

@[simp]
theorem natCodebook_length_zero : natCodebook.length 0 = 1 := rfl

@[simp]
theorem natCodebook_length_one : natCodebook.length 1 = 2 := rfl

/-- The unary self-delimiting code has exactly one delimiter beyond its
natural-number index. -/
@[simp]
theorem natCodebook_length (index : Nat) :
    natCodebook.length index = index + 1 := by
  change (machinePrefix index).length = index + 1
  induction index with
  | zero => rfl
  | succ index inductionHypothesis =>
      simp [machinePrefix, inductionHypothesis, Nat.add_assoc]

/-- Bennett's ranking-reversal obstruction already occurs on a countably
infinite hypothesis class. -/
theorem nat_not_codebookInvariant
    (selector : Selector Nat)
    (usesLength : StrictlyPrefersShorter selector) :
    ¬ CodebookInvariant selector :=
  not_codebookInvariant_of_unequal_lengths selector usesLength natCodebook
    (by decide : natCodebook.length 0 < natCodebook.length 1)

/-! ## Uncountable obstruction -/

/-- No uncountable hypothesis class has an injective finite-binary-string
codebook.  A finite-string description-length selector therefore cannot even
range over every member of such a class. -/
theorem no_prefixCodebook_of_uncountable
    (Hypothesis : Type uHypothesis) [Uncountable Hypothesis] :
    IsEmpty (PrefixCodebook Hypothesis) :=
  ⟨fun codebook ↦
    not_injective_uncountable_countable codebook.encode codebook.injective⟩

end Mettapedia.InformationTheory.CodebookRelativity

#print axioms Mettapedia.InformationTheory.CodebookRelativity.not_codebookInvariant_of_unequal_lengths
#print axioms Mettapedia.InformationTheory.CodebookRelativity.nat_not_codebookInvariant
#print axioms Mettapedia.InformationTheory.CodebookRelativity.no_prefixCodebook_of_uncountable
