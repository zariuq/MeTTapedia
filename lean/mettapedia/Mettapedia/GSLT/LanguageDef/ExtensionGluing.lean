import Mettapedia.GSLT.LanguageDef.ExtensionComposition

/-!
# Gluing admitted proof calculi

`ExtensionComposition` settles the authored half: extension languages compose,
and the composite's restriction to each side is that side's elaborator.  It also
shows the authored half is the only half that composes unconditionally —
`admission_not_closed_under_composition` merges two admitted calculi into a
rejected one.

This module closes the remaining law.  Under the overlap condition `Compatible`
— disjoint judgment heads, disjoint rule identifiers, at most one rooted
conversion authority — two calculi admitted against one term language merge to a
calculus admitted against that same language, and the merge is exactly the
partial monoid's.

That is `gluing_of_compatible`.  The resulting architecture is a fibration over
the core with a gluing law on compatible pairs.  It is not yet a descent theory:
that would additionally require a notion of cover and coherent higher overlaps.

## How it reduces

Every clause of admission is either pointwise, and so transfers by splitting a
list quantifier across `++`, or it is one of two genuinely global conditions:

* **freedom from duplicate names**, which is `Nodup` on the concatenation and
  therefore needs exactly the disjointness `Compatible` supplies;
* **unambiguous judgment lookup**, which selects on an exact head and arity and
  demands a unique match — so head-disjointness is precisely what makes a lookup
  on the merged declaration list agree with the lookup on the side that declared
  it.

The first is `eraseDups_length_iff_nodup`, proved here because admission spells
duplicate-freedom as a length comparison rather than as `Nodup`.  The second is
`lookupJudgment_merge_left` and its mirror.
-/

namespace Mettapedia.GSLT.LanguageDef.ExtensionGluing

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef.Extension
open Mettapedia.GSLT.LanguageDef.InferenceExtension
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.ExtensionComposition
open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## Duplicate-freedom as a length comparison

Admission compares `eraseDups.length` against `length`.  That is `Nodup` in
disguise, and the disguise has to come off before disjointness can be used. -/

private theorem eraseDups_sublist {α : Type _} [BEq α] [LawfulBEq α] :
    ∀ values : List α, values.eraseDups.Sublist values
  | [] => by simp
  | value :: values => by
      rw [List.eraseDups_cons]
      exact List.Sublist.cons_cons value
        ((eraseDups_sublist (values.filter fun other => !other == value)).trans
          List.filter_sublist)
  termination_by values => values.length
  decreasing_by
    have shorter := List.length_filter_le (fun other => !other == value) values
    simp only [List.length_cons]
    omega

private theorem nodup_eraseDups {α : Type _} [BEq α] [LawfulBEq α] :
    ∀ values : List α, values.eraseDups.Nodup
  | [] => by simp
  | value :: values => by
      rw [List.eraseDups_cons]
      refine List.nodup_cons.mpr
        ⟨?_, nodup_eraseDups (values.filter fun other => !other == value)⟩
      intro member
      rw [List.mem_eraseDups, List.mem_filter] at member
      simp at member
  termination_by values => values.length
  decreasing_by
    have shorter := List.length_filter_le (fun other => !other == value) values
    simp only [List.length_cons]
    omega

private theorem eraseDups_of_nodup {α : Type _} [BEq α] [LawfulBEq α] :
    ∀ {values : List α}, values.Nodup → values.eraseDups = values
  | [], _ => by simp
  | value :: values, nodup => by
      rw [List.eraseDups_cons]
      obtain ⟨absent, tailNodup⟩ := List.nodup_cons.mp nodup
      have filterAll : (values.filter fun other => !other == value) = values := by
        rw [List.filter_eq_self]
        intro other member
        simp only [Bool.not_eq_eq_eq_not, Bool.not_true, beq_eq_false_iff_ne, ne_eq]
        intro equal
        exact absent (equal ▸ member)
      rw [filterAll, eraseDups_of_nodup tailNodup]
  termination_by values => values.length
  decreasing_by
    simp only [List.length_cons]
    omega

/-- Admission's duplicate-freedom test is `Nodup`. -/
theorem eraseDups_length_iff_nodup {α : Type _} [BEq α] [LawfulBEq α]
    (values : List α) :
    (values.eraseDups.length == values.length) = true ↔ values.Nodup := by
  constructor
  · intro lengths
    have equal : values.eraseDups = values :=
      (eraseDups_sublist values).eq_of_length (by simpa using lengths)
    exact equal ▸ nodup_eraseDups values
  · intro nodup
    simp [eraseDups_of_nodup nodup]

/-- Disjoint duplicate-free name lists concatenate to a duplicate-free list. -/
theorem eraseDups_length_append {α : Type _} [BEq α] [LawfulBEq α]
    {first second : List α}
    (firstFree : (first.eraseDups.length == first.length) = true)
    (secondFree : (second.eraseDups.length == second.length) = true)
    (disjoint : ∀ value ∈ first, value ∉ second) :
    ((first ++ second).eraseDups.length == (first ++ second).length) = true := by
  rw [eraseDups_length_iff_nodup] at firstFree secondFree ⊢
  refine List.nodup_append.mpr ⟨firstFree, secondFree, ?_⟩
  intro value member other otherMember equal
  subst equal
  exact disjoint value member otherMember

/-! ## The merge -/

/-- The merged calculus.  Declaration order is authored order, left before
right; conversion authority is whichever side declared one. -/
def mergeOf (first second : ProofCalculus) : ProofCalculus where
  judgments := first.judgments ++ second.judgments
  rules := first.rules ++ second.rules
  conversion := second.conversion <|> first.conversion

/-- Compatible calculi merge, and the merge is the partial monoid's. -/
theorem append_eq_mergeOf {first second : ProofCalculus}
    (compatible : Compatible first second) :
    proofCalculusMonoid.op first second = some (mergeOf first second) := by
  cases compatible.conversion with
  | inl firstNone =>
      cases hsecond : second.conversion <;>
        simp [proofCalculusMonoid, ProofCalculus.append?, mergeOf,
          firstNone, hsecond]
  | inr secondNone =>
      cases hfirst : first.conversion <;>
        simp [proofCalculusMonoid, ProofCalculus.append?, mergeOf,
          hfirst, secondNone]

/-- Merging is associative, unconditionally.  Declaration lists concatenate and
conversion authority resolves by the same left-biased choice however the merge
is bracketed. -/
theorem mergeOf_assoc (first second third : ProofCalculus) :
    mergeOf first (mergeOf second third) = mergeOf (mergeOf first second) third := by
  cases hfirst : first.conversion <;> cases hsecond : second.conversion <;>
    cases hthird : third.conversion <;>
    simp [mergeOf, hfirst, hsecond, hthird, List.append_assoc]

@[simp] theorem mergeOf_empty_left (calculus : ProofCalculus) :
    mergeOf .empty calculus = calculus := by
  cases calculus with
  | mk judgments rules conversion =>
      cases conversion <;> simp [mergeOf, ProofCalculus.empty]

@[simp] theorem mergeOf_empty_right (calculus : ProofCalculus) :
    mergeOf calculus .empty = calculus := by
  cases calculus with
  | mk judgments rules conversion =>
      cases conversion <;> simp [mergeOf, ProofCalculus.empty]

/-! ## Stacked extension

A layer that uses judgments introduced by an earlier layer is not admitted on
its own, so `Compatible` cannot describe it.  What describes it is admission
*relative to* an accumulated base — and stacking such layers is then exactly
associativity of the merge, with no further condition. -/

/-- An increment is admitted over a base when the two together are admitted. -/
def AdmittedOver (language : LanguageDef) (base increment : ProofCalculus) : Prop :=
  (Presentation.mk language (mergeOf base increment)).isValidV2 = true

/-- **Layers stack.**  A layer admitted over a base, followed by a layer
admitted over that extended base, is one increment admitted over the original
base.  Nothing is assumed about how the two layers interact: a later layer may
freely use judgments the earlier one introduced. -/
theorem admittedOver_stack {language : LanguageDef}
    {base first second : ProofCalculus}
    (secondAdmitted : AdmittedOver language (mergeOf base first) second) :
    AdmittedOver language base (mergeOf first second) := by
  unfold AdmittedOver at secondAdmitted ⊢
  rw [mergeOf_assoc]
  exact secondAdmitted

/-- Admission over the empty base is ordinary admission. -/
theorem admittedOver_empty (language : LanguageDef) (calculus : ProofCalculus) :
    AdmittedOver language .empty calculus ↔
      (Presentation.mk language calculus).isValidV2 = true := by
  unfold AdmittedOver
  rw [mergeOf_empty_left]

@[simp] theorem mergeOf_judgments (first second : ProofCalculus) :
    (mergeOf first second).judgments = first.judgments ++ second.judgments :=
  rfl

@[simp] theorem mergeOf_rules (first second : ProofCalculus) :
    (mergeOf first second).rules = first.rules ++ second.rules :=
  rfl

/-! ## Judgment lookup transports across a disjoint merge -/

/-- A head that is declared nowhere in a list selects nothing from it. -/
private theorem judgmentFilter_eq_nil {judgments : List JudgmentDecl}
    {head : String} {arity : Nat}
    (absent : head ∉ judgments.map JudgmentDecl.head) :
    (judgments.filter fun declaration =>
      declaration.head == head && declaration.arity == arity) = [] := by
  rw [List.filter_eq_nil_iff]
  intro declaration member matching
  simp only [Bool.and_eq_true, beq_iff_eq] at matching
  exact absent (matching.1 ▸ List.mem_map_of_mem member)

/-- A successful lookup names a declared head. -/
theorem mem_judgmentHeads_of_lookup {presentation : Presentation}
    {head : String} {arity : Nat}
    (found : (presentation.lookupJudgment? head arity).isSome = true) :
    head ∈ presentation.judgments.map JudgmentDecl.head := by
  by_contra absent
  rw [Presentation.lookupJudgment?, judgmentFilter_eq_nil absent] at found
  simp at found

/-- **Lookup transports from the left.**  A head the right side never declares
resolves in the merge exactly as it resolved on the left. -/
theorem lookupJudgment_merge_left (language : LanguageDef)
    (first second : ProofCalculus) {head : String} {arity : Nat}
    (absent : head ∉ second.judgments.map JudgmentDecl.head) :
    (Presentation.mk language (mergeOf first second)).lookupJudgment? head arity =
      (Presentation.mk language first).lookupJudgment? head arity := by
  show (match ((mergeOf first second).judgments.filter fun declaration =>
      declaration.head == head && declaration.arity == arity) with
    | [declaration] => some declaration
    | _ => none) = _
  rw [mergeOf_judgments, List.filter_append, judgmentFilter_eq_nil absent,
    List.append_nil]
  rfl

/-- **Lookup transports from the right**, symmetrically. -/
theorem lookupJudgment_merge_right (language : LanguageDef)
    (first second : ProofCalculus) {head : String} {arity : Nat}
    (absent : head ∉ first.judgments.map JudgmentDecl.head) :
    (Presentation.mk language (mergeOf first second)).lookupJudgment? head arity =
      (Presentation.mk language second).lookupJudgment? head arity := by
  show (match ((mergeOf first second).judgments.filter fun declaration =>
      declaration.head == head && declaration.arity == arity) with
    | [declaration] => some declaration
    | _ => none) = _
  rw [mergeOf_judgments, List.filter_append, judgmentFilter_eq_nil absent,
    List.nil_append]
  rfl

/-! ## Rule validity transports -/

/-- A rule's judgment shape survives the merge when the other side declares no
head that this rule uses. -/
private theorem judgmentSchemaValid_merge_left (language : LanguageDef)
    (first second : ProofCalculus)
    (disjoint : ∀ head ∈ first.judgments.map JudgmentDecl.head,
      head ∉ second.judgments.map JudgmentDecl.head)
    {pattern : Pattern}
    (valid : (Presentation.mk language first).judgmentSchemaValid pattern = true) :
    (Presentation.mk language (mergeOf first second)).judgmentSchemaValid pattern
      = true := by
  cases pattern with
  | apply head arguments =>
      simp only [Presentation.judgmentSchemaValid, Bool.and_eq_true] at valid ⊢
      refine ⟨?_, valid.2⟩
      rw [lookupJudgment_merge_left language first second
        (disjoint head (mem_judgmentHeads_of_lookup valid.1))]
      exact valid.1
  | bvar _ => simp [Presentation.judgmentSchemaValid] at valid
  | fvar _ => simp [Presentation.judgmentSchemaValid] at valid
  | lambda _ _ => simp [Presentation.judgmentSchemaValid] at valid
  | multiLambda _ _ _ => simp [Presentation.judgmentSchemaValid] at valid
  | subst _ _ => simp [Presentation.judgmentSchemaValid] at valid
  | collection _ _ _ => simp [Presentation.judgmentSchemaValid] at valid

private theorem judgmentSchemaValid_merge_right (language : LanguageDef)
    (first second : ProofCalculus)
    (disjoint : ∀ head ∈ first.judgments.map JudgmentDecl.head,
      head ∉ second.judgments.map JudgmentDecl.head)
    {pattern : Pattern}
    (valid : (Presentation.mk language second).judgmentSchemaValid pattern = true) :
    (Presentation.mk language (mergeOf first second)).judgmentSchemaValid pattern
      = true := by
  cases pattern with
  | apply head arguments =>
      simp only [Presentation.judgmentSchemaValid, Bool.and_eq_true] at valid ⊢
      refine ⟨?_, valid.2⟩
      have absent : head ∉ first.judgments.map JudgmentDecl.head := by
        intro member
        exact disjoint head member (mem_judgmentHeads_of_lookup valid.1)
      rw [lookupJudgment_merge_right language first second absent]
      exact valid.1
  | bvar _ => simp [Presentation.judgmentSchemaValid] at valid
  | fvar _ => simp [Presentation.judgmentSchemaValid] at valid
  | lambda _ _ => simp [Presentation.judgmentSchemaValid] at valid
  | multiLambda _ _ _ => simp [Presentation.judgmentSchemaValid] at valid
  | subst _ _ => simp [Presentation.judgmentSchemaValid] at valid
  | collection _ _ _ => simp [Presentation.judgmentSchemaValid] at valid

private theorem isValidIn_merge_left (language : LanguageDef)
    (first second : ProofCalculus)
    (disjoint : ∀ head ∈ first.judgments.map JudgmentDecl.head,
      head ∉ second.judgments.map JudgmentDecl.head)
    {rule : RuleSchema}
    (valid : RuleSchema.isValidIn (Presentation.mk language first) rule = true) :
    RuleSchema.isValidIn (Presentation.mk language (mergeOf first second)) rule
      = true := by
  simp only [RuleSchema.isValidIn, Bool.and_eq_true, List.all_eq_true] at valid ⊢
  refine ⟨valid.1, fun pattern member => ?_, valid.2.2⟩
  exact judgmentSchemaValid_merge_left language first second disjoint
    (valid.2.1 pattern member)

private theorem isValidIn_merge_right (language : LanguageDef)
    (first second : ProofCalculus)
    (disjoint : ∀ head ∈ first.judgments.map JudgmentDecl.head,
      head ∉ second.judgments.map JudgmentDecl.head)
    {rule : RuleSchema}
    (valid : RuleSchema.isValidIn (Presentation.mk language second) rule = true) :
    RuleSchema.isValidIn (Presentation.mk language (mergeOf first second)) rule
      = true := by
  simp only [RuleSchema.isValidIn, Bool.and_eq_true, List.all_eq_true] at valid ⊢
  refine ⟨valid.1, fun pattern member => ?_, valid.2.2⟩
  exact judgmentSchemaValid_merge_right language first second disjoint
    (valid.2.1 pattern member)

/-! ## The gluing law -/

/-- **Compatible admitted calculi glue.**  Two proof calculi admitted against
one term language, overlapping cleanly, merge as authored data to a calculus
admitted against that same language.

With `admission_not_closed_under_composition` this is sharp in both directions:
the merge is admitted exactly when the overlap condition holds, and the
condition is about names rather than about how the declarations were written. -/
theorem gluing_of_compatible (language : LanguageDef) (first second : ProofCalculus)
    (firstValid : (Presentation.mk language first).isValidV2 = true)
    (secondValid : (Presentation.mk language second).isValidV2 = true)
    (compatible : Compatible first second) :
    proofCalculusMonoid.op first second = some (mergeOf first second) ∧
      (Presentation.mk language (mergeOf first second)).isValidV2 = true := by
  refine ⟨append_eq_mergeOf compatible, ?_⟩
  simp only [Presentation.isValidV2, Bool.and_eq_true] at firstValid secondValid ⊢
  obtain ⟨⟨⟨firstBase, firstSignature⟩, firstRules⟩, firstConversion⟩ := firstValid
  obtain ⟨⟨⟨secondBase, secondSignature⟩, secondRules⟩, secondConversion⟩ :=
    secondValid
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · -- V1: the base language is untouched; rule schemas are pointwise; rule
    -- identifiers stay duplicate-free because they were disjoint.
    simp only [Presentation.isValidV1, Bool.and_eq_true] at firstBase secondBase ⊢
    refine ⟨⟨firstBase.1.1, ?_⟩, ?_⟩
    · simp only [Presentation.rules, mergeOf_rules, List.all_append,
        Bool.and_eq_true]
      exact ⟨firstBase.1.2, secondBase.1.2⟩
    · simp only [Presentation.ruleIds, Presentation.rules, mergeOf_rules,
        List.map_append]
      exact eraseDups_length_append firstBase.2 secondBase.2
        (fun value member other => compatible.ruleIds value member other)
  · -- The judgment signature: pointwise conditions plus disjoint heads.
    simp only [Presentation.judgmentSignatureValid, Bool.and_eq_true,
      Presentation.judgments, Presentation.judgmentHeads, mergeOf_judgments,
      List.all_append, List.map_append] at firstSignature secondSignature ⊢
    refine ⟨⟨⟨firstSignature.1.1, secondSignature.1.1⟩, ?_⟩,
      firstSignature.2, secondSignature.2⟩
    exact eraseDups_length_append firstSignature.1.2 secondSignature.1.2
      (fun value member other => compatible.judgmentHeads value member other)
  · -- Every rule of either side stays valid, because every head it uses is
    -- declared on its own side and nowhere else.
    simp only [Presentation.rules, mergeOf_rules, List.all_append,
      Bool.and_eq_true, List.all_eq_true] at firstRules secondRules ⊢
    constructor
    · intro rule member
      exact isValidIn_merge_left language first second
        (fun head declared => compatible.judgmentHeads head declared)
        (firstRules rule member)
    · intro rule member
      exact isValidIn_merge_right language first second
        (fun head declared => compatible.judgmentHeads head declared)
        (secondRules rule member)
  · -- The surviving conversion authority resolves by the same lookup argument.
    cases compatible.conversion with
    | inl firstNone =>
        have conversionEq : (mergeOf first second).conversion = second.conversion := by
          cases hsecond : second.conversion <;> simp [mergeOf, firstNone, hsecond]
        cases hsecond : second.conversion with
        | none =>
            simp only [Presentation.conversionDeclarationValid,
              Presentation.conversion, conversionEq, hsecond]
        | some declaration =>
            simp only [Presentation.conversionDeclarationValid,
              Presentation.conversion, hsecond] at secondConversion
            simp only [Presentation.conversionDeclarationValid,
              Presentation.conversion, conversionEq, hsecond, Bool.and_eq_true]
              at secondConversion ⊢
            refine ⟨secondConversion.1, ?_⟩
            have absent : declaration.judgmentHead ∉
                first.judgments.map JudgmentDecl.head := by
              intro member
              exact compatible.judgmentHeads declaration.judgmentHead member
                (mem_judgmentHeads_of_lookup secondConversion.2)
            rw [lookupJudgment_merge_right language first second absent]
            exact secondConversion.2
    | inr secondNone =>
        have conversionEq : (mergeOf first second).conversion = first.conversion := by
          cases hfirst : first.conversion <;> simp [mergeOf, secondNone, hfirst]
        cases hfirst : first.conversion with
        | none =>
            simp only [Presentation.conversionDeclarationValid,
              Presentation.conversion, conversionEq, hfirst]
        | some declaration =>
            simp only [Presentation.conversionDeclarationValid,
              Presentation.conversion, hfirst] at firstConversion
            simp only [Presentation.conversionDeclarationValid,
              Presentation.conversion, conversionEq, hfirst, Bool.and_eq_true]
              at firstConversion ⊢
            refine ⟨firstConversion.1, ?_⟩
            rw [lookupJudgment_merge_left language first second
              (compatible.judgmentHeads declaration.judgmentHead
                (mem_judgmentHeads_of_lookup firstConversion.2))]
            exact firstConversion.2

/-! ## The generic contextual-admission instance -/

/-- Proof-calculus admission is an instance of the generic contextual class.
The source merge is the one forced by calculus-document concatenation;
`Compatible` is exactly the domain-specific overlap law needed by the
validator. -/
def calculusAdmission (language : LanguageDef) :
    GSLT.ContextualAdmission calculusAuthoringGSLT where
  Admitted := fun calculus =>
    (Presentation.mk language calculus).isValidV2 = true
  Compatible := Compatible
  glue := by
    intro first second firstValid secondValid compatible
    have glued := gluing_of_compatible language first second
      firstValid secondValid compatible
    refine ⟨mergeOf first second, ?_, glued.2⟩
    exact glued.1

/-- The authored, partial-merge notion of admission over an accumulated
calculus.  This is sharper than `AdmittedOver`: it records that concatenating
the two authored documents actually succeeds. -/
abbrev CompositionalAdmittedOver (language : LanguageDef)
    (base increment : ProofCalculus) : Prop :=
  (calculusAdmission language).AdmittedOver base increment

/-- When the overlap condition holds, the partial authored notion and the
existing total `mergeOf` presentation coincide. -/
theorem compositionalAdmittedOver_iff (language : LanguageDef)
    {base increment : ProofCalculus} (compatible : Compatible base increment) :
    CompositionalAdmittedOver language base increment ↔
      AdmittedOver language base increment := by
  constructor
  · rintro ⟨merged, mergedByAuthoring, admitted⟩
    have canonical := append_eq_mergeOf compatible
    change proofCalculusMonoid.op base increment = some merged at mergedByAuthoring
    rw [canonical] at mergedByAuthoring
    cases mergedByAuthoring
    exact admitted
  · intro admitted
    refine ⟨mergeOf base increment, ?_, admitted⟩
    change proofCalculusMonoid.op base increment = some (mergeOf base increment)
    exact append_eq_mergeOf compatible

/-- The generic sibling-gluing operation specializes to the established
calculus theorem. -/
theorem contextual_glue_exists (language : LanguageDef)
    {first second : ProofCalculus}
    (firstValid : (Presentation.mk language first).isValidV2 = true)
    (secondValid : (Presentation.mk language second).isValidV2 = true)
    (compatible : Compatible first second) :
    ∃ merged, calculusAuthoringGSLT.merge first second = some merged ∧
      (Presentation.mk language merged).isValidV2 = true :=
  (calculusAdmission language).exists_glue firstValid secondValid compatible

/-- The admitted fibre inherits the merge: gluing sends a compatible pair of
admitted calculi to an admitted calculus over the same language. -/
def glue {language : LanguageDef}
    (first second : ValidatedInferenceExtension.AdmittedCalculus language)
    (compatible : Compatible first.1 second.1) :
    ValidatedInferenceExtension.AdmittedCalculus language :=
  ⟨mergeOf first.1 second.1,
    (gluing_of_compatible language first.1 second.1 first.2 second.2 compatible).2⟩

@[simp] theorem glue_val {language : LanguageDef}
    (first second : ValidatedInferenceExtension.AdmittedCalculus language)
    (compatible : Compatible first.1 second.1) :
    (glue first second compatible).1 = mergeOf first.1 second.1 :=
  rfl

end Mettapedia.GSLT.LanguageDef.ExtensionGluing
