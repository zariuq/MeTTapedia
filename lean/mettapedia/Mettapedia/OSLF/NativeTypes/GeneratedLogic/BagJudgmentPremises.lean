import Mettapedia.OSLF.NativeTypes.GeneratedLogic.BagCanonicalForms
import Mettapedia.GSLT.LanguageDef.DecidableRelations.Stores

/-!
# Canonical forms for bags with judgment premises

A rule may ask that a judgment holds: a premise `J(t₁, …, tₙ) ~> v` whose source is built from metavariables and
bare rests `{...rest}` by constructors and whose target is a first-order verdict (`judgmentStep`), or the same premise at
each element of a captured collection (`forAll`). Complemented judgments enter rules this way:
- non-membership is `forAll` over the rest of a bag with the language's own disequality, as in
  `GSLT.LanguageDef.DecidableRelations.Membership`;
- counting asks the count of the rest, as in `GSLT.LanguageDef.DecidableRelations.Counting`.

A rule may also query a store over metavariables. The store must answer modulo the bag laws (`RespectsCanon`) and
offer tuples with no set (`TuplesSetFree`), as tables of first-order rows do.

Such a premise reads the captures only through constructors and whole captured collections. At canonical captures it
therefore asks the same judgments of canonical arguments (`applyBindingsScoped_canon_plain`,
`applyBindingsScoped_canon_rest`), and a query binds the canonical forms of what it bound (`query_canon`). A quantified premise asks them once per
element, in canonical order (`forAllValid_perm`). So a step of a rule whose premises are queries or judgment premises
is matched by a step of the same rule from the canonical form of its source (`simulatesJudgments`), by recursion on
the steps inside its premises. Such languages are coherent with sorted bags (`coherentJudgments`). The labels of the
two steps agree, since a label reads the steps among a rule's premises only through `any`, which is blind to their
order (`StepsAlike`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.BagForms

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv premiseStepWithEnv)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical (matchPatternForRule_eq_syntactic)
open Mettapedia.OSLF.MeTTaIL.CanonicalBags
  (canon canon_collection canon_apply arrange arrange_vec arrange_bag setFree setFreeList setFreeList_iff
    setFree_collection)
open Mettapedia.OSLF.MeTTaIL.PatternLexOrder (sortLex sortLex_perm)
open Mettapedia.GSLT.LanguageDef.DecidableRelations
  (FirstOrder isFirstOrder isFirstOrder_iff matchPattern_firstOrder mergeBindings_nil_right)

/-! ## Plain sources and first-order verdicts -/

mutual
/-- **A plain pattern**: metavariables and bare rests `{...rest}` of bags or vectors under constructors, with no
binder or substitution. -/
def plainPattern : Pattern → Bool
  | .fvar _ => true
  | .apply _ arguments => plainList arguments
  | .collection kind [] (some _) => kind != .hashSet
  | _ => false

/-- Every pattern of a list is plain. -/
def plainList : List Pattern → Bool
  | [] => true
  | pattern :: patterns => plainPattern pattern && plainList patterns
end

theorem plainList_iff : ∀ {patterns : List Pattern}, plainList patterns = true ↔ ∀ pattern ∈ patterns, plainPattern pattern = true
  | [] => by simp [plainList]
  | pattern :: patterns => by simp [plainList, plainList_iff]

/-- A first-order term is its own canonical form. -/
theorem canon_firstOrder {term : Pattern} (first : FirstOrder term) : canon term = term := by
  induction first with
  | @apply constructor arguments _ inner =>
    rw [canon_apply]
    congr 1
    conv_rhs => rw [← List.map_id arguments]
    exact List.map_congr_left inner

/-- Lists whose canonical forms are lists of patterns determined by their canonical forms are those lists. -/
theorem eq_of_map_canon_eq : ∀ {candidates targets : List Pattern},
    (∀ target ∈ targets, ∀ candidate, canon candidate = target → candidate = target) →
    candidates.map canon = targets → candidates = targets
  | [], [], _, _ => rfl
  | [], _ :: _, _, mapped => by simp at mapped
  | _ :: _, [], _, mapped => by simp at mapped
  | candidate :: candidates, target :: targets, determined, mapped => by
    simp only [List.map_cons, List.cons.injEq] at mapped
    rw [determined target List.mem_cons_self candidate mapped.1,
      eq_of_map_canon_eq (fun other member => determined other (List.mem_cons_of_mem _ member)) mapped.2]

/-- **Only a first-order term has a first-order term as canonical form**: canonical forms keep every constructor. -/
theorem eq_of_canon_eq_firstOrder {target : Pattern} (first : FirstOrder target) :
    ∀ candidate, canon candidate = target → candidate = target := by
  induction first with
  | @apply constructor arguments _ inner =>
    intro candidate same
    cases candidate with
    | apply label candidates =>
      rw [canon_apply] at same
      simp only [Pattern.apply.injEq] at same
      rw [same.1, eq_of_map_canon_eq inner same.2]
    | bvar => simp [canon] at same
    | fvar => simp [canon] at same
    | lambda => simp [canon] at same
    | multiLambda => simp [canon] at same
    | subst => simp [canon] at same
    | collection => simp [canon] at same

/-- A list of terms whose canonical forms are a first-order tuple is that tuple. -/
theorem eq_of_map_canon_eq_firstOrder {candidates tuple : List Pattern} (first : ∀ x ∈ tuple, FirstOrder x)
    (same : candidates.map canon = tuple) : candidates = tuple :=
  eq_of_map_canon_eq (fun target member => eq_of_canon_eq_firstOrder (first target member)) same

/-- A first-order verdict matches exactly itself. -/
theorem matchPattern_verdict {target : Pattern} (checked : isFirstOrder target = true) (candidate : Pattern) :
    matchPattern target candidate = if target = candidate then [[]] else [] :=
  matchPattern_firstOrder ((isFirstOrder_iff target).mp checked) candidate

/-! ## Judgment premises -/

/-- **A judgment step**: a judgment `J(t₁, …, tₙ)` built from metavariables and bare rests by constructors, stepping
to a first-order verdict. -/
def judgmentStep : Pattern → Pattern → Bool
  | .apply _ arguments, target => plainList arguments && isFirstOrder target
  | _, _ => false

/-- **The premises admitted with sorted bags**: queries over metavariables (guards among them), judgment steps, and a
judgment step at each element of a captured collection. -/
def judgmentPremise : Premise → Bool
  | .relationQuery _ arguments => arguments.all isMetavariable
  | .congruence source target => judgmentStep source target
  | .forAll _ _ (.congruence source target) => judgmentStep source target
  | _ => false

theorem judgmentStep_shape {source target : Pattern} (judged : judgmentStep source target = true) :
    ∃ label arguments, source = .apply label arguments ∧ plainList arguments = true ∧ isFirstOrder target = true := by
  cases source with
  | apply label arguments =>
    simp only [judgmentStep, Bool.and_eq_true] at judged
    exact ⟨label, arguments, rfl, judged⟩
  | _ => simp [judgmentStep] at judged

/-! ## Instances at canonical captures -/

theorem arrange_nil (kind : CollType) : arrange kind [] = [] := by
  cases kind <;> rfl

/-- **A bare rest at canonical captures is the canonical form of its instance.** -/
theorem applyBindingsScoped_canon_rest (sites : Pattern) (bindings : Bindings) (kind : CollType) (rest : String) :
    applyBindingsScoped sites (canonBindings bindings) 0 (.collection kind [] (some rest)) =
      canon (applyBindingsScoped sites bindings 0 (.collection kind [] (some rest))) := by
  simp only [applyBindingsScoped, applyBindingsScopedList, List.nil_append, restSplice, find?_canonBindings]
  cases bindings.find? (fun entry : String × Pattern => entry.1 == rest) with
  | none => simp [canon_collection, arrange_nil]
  | some entry =>
    obtain ⟨name, value⟩ := entry
    cases value with
    | collection boundKind elements boundRest =>
      cases boundRest with
      | none =>
        simp only [Option.map_some, canon_collection]
        by_cases sameKind : boundKind = kind
        · subst sameKind
          have liftZero : Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars 0 0 = id :=
            funext fun pattern => Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_zero pattern 0
          cases captureDepth rest 0 sites <;> simp [liftZero]
        · simp [sameKind, arrange_nil]
      | some _ => simp [canon_collection, arrange_nil]
    | _ => simp [canon, canon_collection, arrange_nil]

/-- A bare rest of a kind other than a set, instantiated with captures that have no set, has no set. -/
theorem setFree_applyBindingsScoped_rest (sites : Pattern) {bindings : Bindings}
    (valuesFree : ∀ entry ∈ bindings, setFree entry.2 = true) {kind : CollType} (notSet : kind ≠ .hashSet)
    (rest : String) : setFree (applyBindingsScoped sites bindings 0 (.collection kind [] (some rest))) = true := by
  simp only [applyBindingsScoped, applyBindingsScopedList, List.nil_append, restSplice]
  cases found : bindings.find? (fun entry : String × Pattern => entry.1 == rest) with
  | none => simp [setFree, setFreeList, notSet]
  | some entry =>
    have entryFree := valuesFree entry (List.mem_of_find?_eq_some found)
    obtain ⟨name, value⟩ := entry
    cases value with
    | collection boundKind elements boundRest =>
      obtain ⟨_, elementsFree⟩ := setFree_collection entryFree
      cases boundRest with
      | none =>
        by_cases sameKind : boundKind = kind
        · subst sameKind
          have liftZero : Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars 0 0 = id :=
            funext fun pattern => Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_zero pattern 0
          cases captureDepth rest 0 sites <;> simp [liftZero, setFree, notSet, setFreeList_iff] <;> exact elementsFree
        · simp [sameKind, setFree, setFreeList, notSet]
      | some _ => simp [setFree, setFreeList, notSet]
    | _ => simp [setFree, setFreeList, notSet]

/-- **Instantiating a plain pattern at canonical captures, at depth zero, gives the canonical form of its instance.** -/
theorem applyBindingsScoped_canon_plain (sites : Pattern) (bindings : Bindings) (pattern : Pattern) :
    plainPattern pattern = true →
      applyBindingsScoped sites (canonBindings bindings) 0 pattern =
        canon (applyBindingsScoped sites bindings 0 pattern) := by
  induction pattern using Pattern.inductionOn with
  | hfvar name =>
    intro _
    simp only [applyBindingsScoped, find?_canonBindings]
    cases bindings.find? (fun entry : String × Pattern => entry.1 == name) with
    | none => simp [canon]
    | some entry =>
      simp only [Option.map_some]
      cases captureDepth name 0 sites with
      | none => rfl
      | some depth => simp [Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_zero]
  | happly constructor arguments inner =>
    intro isPlain
    simp only [plainPattern, plainList_iff] at isPlain
    rw [applyBindingsScoped_apply, applyBindingsScoped_apply, canon_apply, List.map_map]
    congr 1
    exact List.map_congr_left fun argument member => inner argument member (isPlain argument member)
  | hbvar => simp [plainPattern]
  | hlambda => simp [plainPattern]
  | hmultiLambda => simp [plainPattern]
  | hsubst => simp [plainPattern]
  | hcollection kind elements rest _ =>
    intro isPlain
    cases elements with
    | cons => simp [plainPattern] at isPlain
    | nil =>
      cases rest with
      | none => simp [plainPattern] at isPlain
      | some name => exact applyBindingsScoped_canon_rest sites bindings kind name

/-- Instantiating a plain pattern with captures that have no set gives a term with no set. -/
theorem setFree_applyBindingsScoped_plain (sites : Pattern) {bindings : Bindings}
    (valuesFree : ∀ entry ∈ bindings, setFree entry.2 = true) (pattern : Pattern) :
    plainPattern pattern = true → setFree (applyBindingsScoped sites bindings 0 pattern) = true := by
  induction pattern using Pattern.inductionOn with
  | hfvar name =>
    intro _
    simp only [applyBindingsScoped]
    cases found : bindings.find? (fun entry : String × Pattern => entry.1 == name) with
    | none => simp [setFree]
    | some entry =>
      have entryFree := valuesFree entry (List.mem_of_find?_eq_some found)
      simp only
      cases captureDepth name 0 sites with
      | none => exact entryFree
      | some depth => simpa [Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_zero] using entryFree
  | happly constructor arguments inner =>
    intro isPlain
    simp only [plainPattern, plainList_iff] at isPlain
    rw [applyBindingsScoped_apply]
    simp only [setFree, setFreeList_iff, List.mem_map]
    rintro _ ⟨argument, member, rfl⟩
    exact inner argument member (isPlain argument member)
  | hbvar => simp [plainPattern]
  | hlambda => simp [plainPattern]
  | hmultiLambda => simp [plainPattern]
  | hsubst => simp [plainPattern]
  | hcollection kind elements rest _ =>
    intro isPlain
    cases elements with
    | cons => simp [plainPattern] at isPlain
    | nil =>
      cases rest with
      | none => simp [plainPattern] at isPlain
      | some name =>
        have notSet : kind ≠ .hashSet := by simpa [plainPattern] using isPlain
        exact setFree_applyBindingsScoped_rest sites valuesFree notSet name

/-- Binding a quantified parameter commutes with taking canonical forms. -/
theorem canonBindings_bindParameter (bindings : Bindings) (parameter : String) (element : Pattern) :
    canonBindings (bindParameter bindings parameter element) =
      bindParameter (canonBindings bindings) parameter (canon element) := by
  simp only [canonBindings, bindParameter, List.map_cons, List.filter_map]
  congr 2

/-! ## Captures with no set -/

/-- One step of a merge, as `mergeBindings` computes it. -/
theorem mergeBindings_cons_eq (first : Bindings) (entry : String × Pattern) (rest : Bindings) :
    mergeBindings first (entry :: rest) =
      (match first.find? (fun item : String × Pattern => item.1 == entry.1) with
        | none => some (entry :: first)
        | some (_, existing) => if existing == entry.2 then some first else none).bind
        fun accumulated => mergeBindings accumulated rest := by
  obtain ⟨entryName, entryValue⟩ := entry
  rfl

/-- **Merged bindings hold entries of the two merged lists.** -/
theorem mem_of_mergeBindings : ∀ (second : Bindings) {first result : Bindings}, mergeBindings first second = some result →
    ∀ entry ∈ result, entry ∈ first ∨ entry ∈ second
  | [], first, result, merged => by
    simp only [mergeBindings, List.foldlM_nil] at merged
    cases merged
    exact fun entry member => .inl member
  | next :: rest, first, result, merged => by
    rw [mergeBindings_cons_eq] at merged
    intro entry member
    cases found : first.find? (fun item : String × Pattern => item.1 == next.1) with
    | none =>
      rw [found] at merged
      simp only [Option.bind_some] at merged
      rcases mem_of_mergeBindings rest merged entry member with inFront | inRest
      · rcases List.mem_cons.mp inFront with isNext | earlier
        · exact .inr (by rw [isNext]; exact List.mem_cons_self)
        · exact .inl earlier
      · exact .inr (List.mem_cons_of_mem _ inRest)
    | some known =>
      obtain ⟨name, existing⟩ := known
      rw [found] at merged
      by_cases agrees : existing == next.2
      · simp only [agrees, ↓reduceIte, Option.bind_some] at merged
        rcases mem_of_mergeBindings rest merged entry member with early | inRest
        · exact .inl early
        · exact .inr (List.mem_cons_of_mem _ inRest)
      · simp only [agrees, Bool.false_eq_true, ↓reduceIte, Option.bind_none, reduceCtorEq] at merged

/-- Merging bindings whose captures have no set gives bindings whose captures have no set. -/
theorem capturesFree_merge {first second result : Bindings} (merged : mergeBindings first second = some result)
    (firstFree : ∀ entry ∈ first, setFree entry.2 = true) (secondFree : ∀ entry ∈ second, setFree entry.2 = true) :
    ∀ entry ∈ result, setFree entry.2 = true := fun entry member =>
  (mem_of_mergeBindings second merged entry member).elim (firstFree entry) (secondFree entry)

mutual
/-- **The captures of a match at a term with no set have no set.** -/
theorem capturesFree_matchRel : ∀ (pattern term : Pattern) (bindings : Bindings), setFree term = true →
    MatchRel pattern term bindings → ∀ entry ∈ bindings, setFree entry.2 = true
  | .fvar _, _, _, free, matched => by
    cases matched
    intro entry member
    simp only [List.mem_singleton] at member
    subst member
    exact free
  | .bvar _, _, _, _, matched => by
    cases matched
    simp
  | .apply label patterns, _, bindings, free, matched => by
    cases matched with
    | apply arguments lengths =>
      rename_i terms
      exact capturesFree_matchArgsRel patterns terms bindings (setFreeList_iff.mp free) arguments
  | .lambda _ body, _, bindings, free, matched => by
    cases matched with
    | lambda inner => exact capturesFree_matchRel body _ bindings (by simpa only [setFree] using free) inner
  | .multiLambda _ _ body, _, bindings, free, matched => by
    cases matched with
    | multiLambda inner => exact capturesFree_matchRel body _ bindings (by simpa only [setFree] using free) inner
  | .collection kind patterns rest, _, bindings, free, matched => by
    cases matched with
    | collection notVector bag =>
      rename_i terms termRest
      obtain ⟨notSet, frees⟩ := setFree_collection free
      exact capturesFree_matchBagRel patterns rest kind terms bindings notSet frees bag
    | vector arguments =>
      rename_i terms termRest
      obtain ⟨_, frees⟩ := setFree_collection free
      exact capturesFree_matchArgsRel patterns terms bindings frees arguments
    | vectorRest prefixMatch merged =>
      rename_i prefixBindings name terms termRest
      obtain ⟨_, frees⟩ := setFree_collection free
      refine capturesFree_merge merged
        (capturesFree_matchArgsRel patterns (terms.take patterns.length) prefixBindings
          (fun term member => frees term (List.mem_of_mem_take member)) prefixMatch) ?_
      intro entry member
      simp only [List.mem_singleton] at member
      subst member
      simp only [setFree, decide_false, Bool.not_false, Bool.true_and, reduceCtorEq]
      exact setFreeList_iff.mpr fun term member => frees term (List.mem_of_mem_drop member)
  | .subst body replacement, _, bindings, free, matched => by
    cases matched with
    | subst bodyMatch replacementMatch merged =>
      rename_i termBody first termReplacement second
      simp only [setFree, Bool.and_eq_true] at free
      exact capturesFree_merge merged (capturesFree_matchRel body termBody first free.1 bodyMatch)
        (capturesFree_matchRel replacement termReplacement second free.2 replacementMatch)
termination_by pattern => sizeOf pattern

/-- Argument lists. -/
theorem capturesFree_matchArgsRel : ∀ (patterns terms : List Pattern) (bindings : Bindings),
    (∀ term ∈ terms, setFree term = true) → MatchArgsRel patterns terms bindings →
      ∀ entry ∈ bindings, setFree entry.2 = true
  | [], _, _, _, matched => by
    cases matched
    simp
  | pattern :: patterns, _, _, free, matched => by
    cases matched with
    | cons head tail merged =>
      rename_i term headBindings terms tailBindings
      exact capturesFree_merge merged (capturesFree_matchRel pattern term headBindings (free term List.mem_cons_self) head)
        (capturesFree_matchArgsRel patterns terms tailBindings
          (fun other member => free other (List.mem_cons_of_mem _ member)) tail)
termination_by patterns => sizeOf patterns

/-- Bags and vectors matched as bags, whose kind is not a set. -/
theorem capturesFree_matchBagRel : ∀ (patterns : List Pattern) (rest : Option String) (kind : CollType)
    (terms : List Pattern) (bindings : Bindings), kind ≠ .hashSet → (∀ term ∈ terms, setFree term = true) →
    MatchBagRel patterns rest kind terms bindings → ∀ entry ∈ bindings, setFree entry.2 = true
  | [], none, _, _, _, _, _, matched => by
    cases matched
    simp
  | [], some _, kind, terms, _, notSet, free, matched => by
    cases matched
    intro entry member
    simp only [List.mem_singleton] at member
    subst member
    simp only [setFree, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
    exact ⟨notSet, setFreeList_iff.mpr free⟩
  | pattern :: patterns, rest, kind, terms, _, notSet, free, matched => by
    cases matched with
    | cons index within head tail merged =>
      rename_i headBindings restBindings
      exact capturesFree_merge merged
        (capturesFree_matchRel pattern terms[index] headBindings (free _ (List.getElem_mem within)) head)
        (capturesFree_matchBagRel patterns rest kind (terms.eraseIdx index) restBindings notSet
          (fun other member => free other (List.mem_of_mem_eraseIdx member)) tail)
termination_by patterns => sizeOf patterns
end

/-- A capture looked up in bindings is one of their captures. -/
theorem lookup_mem {bindings : Bindings} {name : String} {value : Pattern}
    (found : Bindings.lookup bindings name = some value) : ∃ entry ∈ bindings, entry.2 = value := by
  simp only [Bindings.lookup, Option.map_eq_some_iff] at found
  obtain ⟨entry, foundEntry, rfl⟩ := found
  exact ⟨entry, List.mem_of_find?_eq_some foundEntry, rfl⟩

/-! ## Steps no label tells apart -/

/-- **Two lists of steps no label tells apart**: every label admits a step of one exactly when it admits a step of
the other. -/
def StepsAlike (steps steps' : List Witness) : Prop :=
  ∀ label : StepLabel, steps.any label.admits = steps'.any label.admits

theorem StepsAlike.single {step step' : Witness} (alike : ∀ label : StepLabel, label.admits step = label.admits step') :
    StepsAlike [step] [step'] := fun label => by
  simp only [List.any_cons, List.any_nil, Bool.or_false, alike label]

theorem StepsAlike.append {first first' second second' : List Witness} (firstAlike : StepsAlike first first')
    (secondAlike : StepsAlike second second') : StepsAlike (first ++ second) (first' ++ second') := fun label => by
  simp only [List.any_append, firstAlike label, secondAlike label]

theorem StepsAlike.of_perm {steps steps' : List Witness} (permuted : steps.Perm steps') : StepsAlike steps steps' :=
  fun _ => permuted.any_eq

theorem StepsAlike.trans {first second third : List Witness} (firstAlike : StepsAlike first second)
    (secondAlike : StepsAlike second third) : StepsAlike first third := fun label =>
  (firstAlike label).trans (secondAlike label)

theorem premiseStepsList_cons (witness : Witness) (witnesses : List Witness) :
    premiseStepsList (witness :: witnesses) = premiseSteps witness ++ premiseStepsList witnesses := by
  simp only [premiseStepsList]

theorem premiseStepsList_eq_flatMap : ∀ witnesses : List Witness,
    premiseStepsList witnesses = witnesses.flatMap premiseSteps
  | [] => by simp only [premiseStepsList, List.flatMap_nil]
  | witness :: witnesses => by
    rw [premiseStepsList_cons, List.flatMap_cons, premiseStepsList_eq_flatMap witnesses]

/-- A label reads only a rule witness's rule and, through `any`, the steps among its premises. -/
theorem admits_alike (label : StepLabel) (index : ℕ) (first second : Bindings) {premises premises' : List Witness}
    (alike : StepsAlike (premiseStepsList premises) (premiseStepsList premises')) :
    label.admits (.rule index first premises) = label.admits (.rule index second premises') := by
  cases label with
  | any => rfl
  | rule => simp only [StepLabel.admits, ruleOf]
  | under _ inner => simp only [StepLabel.admits, alike inner]
  | context => simp only [StepLabel.admits]

mutual
/-- The steps inside a premise witness are smaller than it. -/
theorem sizeOf_lt_of_mem_premiseSteps : ∀ (witness : Witness) {step : Witness},
    step ∈ premiseSteps witness → sizeOf step < sizeOf witness
  | .premiseStep inner _ _ _, step, member => by
    simp only [premiseSteps, List.mem_singleton] at member
    subst member
    simp only [Witness.premiseStep.sizeOf_spec]
    omega
  | .forAll bodies, step, member => by
    simp only [premiseSteps] at member
    have smaller := sizeOf_lt_of_mem_premiseStepsList bodies member
    simp only [Witness.forAll.sizeOf_spec]
    omega
  | .rule _ _ _, step, member => by simp [premiseSteps] at member
  | .base _, step, member => by simp [premiseSteps] at member

/-- The steps inside a list of premise witnesses are smaller than it. -/
theorem sizeOf_lt_of_mem_premiseStepsList : ∀ (witnesses : List Witness) {step : Witness},
    step ∈ premiseStepsList witnesses → sizeOf step < sizeOf witnesses
  | [], step, member => by simp [premiseStepsList] at member
  | witness :: witnesses, step, member => by
    rw [premiseStepsList_cons, List.mem_append] at member
    simp only [List.cons.sizeOf_spec]
    rcases member with early | late
    · have smaller := sizeOf_lt_of_mem_premiseSteps witness early
      omega
    · have smaller := sizeOf_lt_of_mem_premiseStepsList witnesses late
      omega
end

/-- The steps inside a rule witness's premises are smaller than the rule witness. -/
theorem sizeOf_lt_rule {index : ℕ} {initial : Bindings} {witnesses : List Witness} {step : Witness}
    (member : step ∈ premiseStepsList witnesses) : sizeOf step < sizeOf (Witness.rule index initial witnesses) := by
  have smaller := sizeOf_lt_of_mem_premiseStepsList witnesses member
  simp only [Witness.rule.sizeOf_spec]
  omega

/-! ## Premises at canonical captures -/

variable {relEnv : RelationEnv} {language : LanguageDef}

/-- **A simulated step**: from any source with no set, it is matched by a step from the source's canonical form, with
the same labels and a target with the same canonical form. -/
def Simulated (relEnv : RelationEnv) (language : LanguageDef) (step : Witness) : Prop :=
  ∀ {source target : Pattern}, setFree source = true → StepValid relEnv language source step target →
    ∃ step' target', StepValid relEnv language (canon source) step' target' ∧
      (∀ label : StepLabel, label.admits step = label.admits step') ∧ canon target' = canon target

/-- Quantified premise evidence over a permutation of the elements: the same evidence, permuted. -/
theorem forAllValid_perm {sites : Pattern} {bindings : Bindings} {parameter : String} {body : Premise}
    {elements elements' : List Pattern} (permuted : elements.Perm elements') :
    ∀ {bodies : List Witness}, ForAllValid relEnv language sites bindings parameter body elements bodies →
      ∃ bodies', ForAllValid relEnv language sites bindings parameter body elements' bodies' ∧ bodies.Perm bodies' := by
  induction permuted with
  | nil =>
    intro bodies valid
    cases valid
    exact ⟨[], .nil, .nil⟩
  | cons element _ inner =>
    intro bodies valid
    cases valid with
    | cons head tail =>
      obtain ⟨bodies', tail', permutedBodies⟩ := inner tail
      exact ⟨_, .cons head tail', permutedBodies.cons _⟩
  | swap first second others =>
    intro bodies valid
    cases valid with
    | cons secondHead tail =>
      cases tail with
      | cons firstHead others' =>
        exact ⟨_, .cons firstHead (.cons secondHead others'), .swap _ _ _⟩
  | trans _ _ firstInner secondInner =>
    intro bodies valid
    obtain ⟨middle, middleValid, firstPermuted⟩ := firstInner valid
    obtain ⟨last, lastValid, secondPermuted⟩ := secondInner middleValid
    exact ⟨last, lastValid, firstPermuted.trans secondPermuted⟩

/-- **A judgment step at canonical captures**: it asks the same judgment of canonical arguments, which the simulated
step inside it answers. -/
theorem judgmentCanon {sites : Pattern} {label : String} {arguments : List Pattern} {target : Pattern}
    (plainArguments : plainList arguments = true) (firstTarget : isFirstOrder target = true)
    {bindings result : Bindings} {witness : Witness} (valuesFree : ∀ entry ∈ bindings, setFree entry.2 = true)
    (simulated : ∀ step ∈ premiseSteps witness, Simulated relEnv language step)
    (valid : PremiseValid relEnv language sites bindings (.congruence (.apply label arguments) target) witness result) :
    result = bindings ∧ ∃ witness', PremiseValid relEnv language sites (canonBindings bindings)
        (.congruence (.apply label arguments) target) witness' (canonBindings bindings) ∧
      StepsAlike (premiseSteps witness) (premiseSteps witness') := by
  cases valid with
  | base isBaseTrue _ => simp [isBase] at isBaseTrue
  | step endpoints stepped matchedTarget merged =>
    rename_i matched source' target' candidate step
    simp only [stepEndpoints, Option.some.injEq, Prod.mk.injEq] at endpoints
    obtain ⟨rfl, rfl⟩ := endpoints
    rw [matchPattern_verdict firstTarget] at matchedTarget
    split at matchedTarget
    · rename_i reached
      subst reached
      simp only [List.mem_singleton] at matchedTarget
      subst matchedTarget
      rw [mergeBindings_nil_right, Option.some.injEq] at merged
      subst merged
      have plainSource : plainPattern (.apply label arguments) = true := by simpa [plainPattern] using plainArguments
      have depth : stepDepth sites (.congruence (.apply label arguments) target) = 0 := rfl
      rw [depth] at stepped
      obtain ⟨step', target'', stepped', alike, sameCanon⟩ := simulated step (by simp [premiseSteps])
        (setFree_applyBindingsScoped_plain sites valuesFree _ plainSource) stepped
      rw [← applyBindingsScoped_canon_plain sites bindings _ plainSource] at stepped'
      have reachedTarget : target'' = target :=
        eq_of_canon_eq_firstOrder ((isFirstOrder_iff target).mp firstTarget) target''
          (sameCanon.trans (canon_firstOrder ((isFirstOrder_iff target).mp firstTarget)))
      subst reachedTarget
      refine ⟨rfl, .premiseStep step' target'' [] (canonBindings bindings), ?_, ?_⟩
      · refine .step (source := .apply label arguments) (target := target'') rfl (by rw [depth]; exact stepped') ?_
          (mergeBindings_nil_right _)
        rw [matchPattern_verdict firstTarget]
        simp
      · simpa [premiseSteps] using StepsAlike.single alike
    · simp at matchedTarget

/-- Each element's judgment at canonical captures, in the order of the canonical elements' list. -/
theorem forAllJudgmentCanon {sites : Pattern} {label : String} {arguments : List Pattern} {target : Pattern}
    (plainArguments : plainList arguments = true) (firstTarget : isFirstOrder target = true) {bindings : Bindings}
    {parameter : String} (valuesFree : ∀ entry ∈ bindings, setFree entry.2 = true) :
    ∀ {elements : List Pattern} {bodies : List Witness}, (∀ element ∈ elements, setFree element = true) →
      (∀ step ∈ premiseStepsList bodies, Simulated relEnv language step) →
      ForAllValid relEnv language sites bindings parameter (.congruence (.apply label arguments) target) elements bodies →
      ∃ bodies', ForAllValid relEnv language sites (canonBindings bindings) parameter
          (.congruence (.apply label arguments) target) (elements.map canon) bodies' ∧
        StepsAlike (premiseStepsList bodies) (premiseStepsList bodies')
  | [], _, _, _, valid => by
    cases valid
    exact ⟨[], .nil, fun _ => rfl⟩
  | element :: elements, _, elementsFree, simulated, valid => by
    cases valid with
    | cons head tail =>
      rename_i result witness witnesses
      have parameterFree : ∀ entry ∈ bindParameter bindings parameter element, setFree entry.2 = true := by
        intro entry member
        simp only [bindParameter, List.mem_cons, List.mem_filter] at member
        rcases member with rfl | ⟨earlier, _⟩
        · exact elementsFree element List.mem_cons_self
        · exact valuesFree entry earlier
      obtain ⟨_, witness', head', headAlike⟩ := judgmentCanon plainArguments firstTarget parameterFree
        (fun step member => simulated step (by rw [premiseStepsList_cons]; exact List.mem_append_left _ member)) head
      rw [canonBindings_bindParameter] at head'
      obtain ⟨bodies', tail', tailAlike⟩ := forAllJudgmentCanon plainArguments firstTarget valuesFree
        (fun other member => elementsFree other (List.mem_cons_of_mem _ member))
        (fun step member => simulated step (by rw [premiseStepsList_cons]; exact List.mem_append_right _ member)) tail
      refine ⟨witness' :: bodies', .cons head' tail', ?_⟩
      rw [premiseStepsList_cons, premiseStepsList_cons]
      exact headAlike.append tailAlike

/-- **A judgment step at each element, at canonical captures**: the canonical collection lists the canonical
elements in canonical order, and each is asked the same judgment of its canonical form. -/
theorem forAllCanon {sites : Pattern} {collection parameter label : String} {arguments : List Pattern}
    {target : Pattern} (plainArguments : plainList arguments = true) (firstTarget : isFirstOrder target = true)
    {bindings result : Bindings} {witness : Witness} (valuesFree : ∀ entry ∈ bindings, setFree entry.2 = true)
    (simulated : ∀ step ∈ premiseSteps witness, Simulated relEnv language step)
    (valid : PremiseValid relEnv language sites bindings
      (.forAll collection parameter (.congruence (.apply label arguments) target)) witness result) :
    result = bindings ∧ ∃ witness', PremiseValid relEnv language sites (canonBindings bindings)
        (.forAll collection parameter (.congruence (.apply label arguments) target)) witness' (canonBindings bindings) ∧
      StepsAlike (premiseSteps witness) (premiseSteps witness') := by
  cases valid with
  | base isBaseTrue _ => simp [isBase] at isBaseTrue
  | step endpoints _ _ _ => simp [stepEndpoints] at endpoints
  | forAll found validAll =>
    rename_i kind elements bodies
    obtain ⟨entry, member, value⟩ := lookup_mem found
    have collectionFree := valuesFree entry member
    rw [value] at collectionFree
    obtain ⟨notSet, elementsFree⟩ := setFree_collection collectionFree
    obtain ⟨bodies₁, valid₁, alike₁⟩ :=
      forAllJudgmentCanon plainArguments firstTarget valuesFree elementsFree simulated validAll
    have arranged : (elements.map canon).Perm (arrange kind (elements.map canon)) := by
      cases kind with
      | vec => rw [arrange_vec]
      | hashBag => rw [arrange_bag]; exact (sortLex_perm _).symm
      | hashSet => exact absurd rfl notSet
    obtain ⟨bodies₂, valid₂, permuted⟩ := forAllValid_perm arranged valid₁
    refine ⟨rfl, .forAll bodies₂, .forAll (kind := kind) ?_ valid₂, ?_⟩
    · rw [lookup_canonBindings, found]
      simp only [Option.map_some, canon_collection]
    · simp only [premiseSteps]
      refine alike₁.trans (StepsAlike.of_perm ?_)
      rw [premiseStepsList_eq_flatMap, premiseStepsList_eq_flatMap]
      exact permuted.flatMap_right _

/-! ## Queries -/

/-- **A store whose tuples have no set.** -/
def TuplesSetFree (relEnv : RelationEnv) : Prop :=
  ∀ relation arguments tuple, tuple ∈ relEnv.tuples relation arguments → ∀ x ∈ tuple, setFree x = true

theorem tuplesSetFree_empty : TuplesSetFree RelationEnv.empty := fun _ _ _ offered => by
  simp [RelationEnv.empty] at offered

/-- Matching a query over metavariables binds them to components of the tuple. -/
theorem mem_tuple_of_matchRelationArgs : ∀ (arguments : List Pattern) {seed : Bindings} {tuple : List Pattern}
    {extension : Bindings}, arguments.all isMetavariable = true →
    extension ∈ Mettapedia.OSLF.MeTTaIL.Engine.matchRelationArgs seed arguments tuple → ∀ entry ∈ extension, entry.2 ∈ tuple
  | [], seed, tuple, extension, _, matched => by
    cases tuple with
    | nil =>
      simp only [Mettapedia.OSLF.MeTTaIL.Engine.matchRelationArgs, List.mem_singleton] at matched
      subst matched
      simp
    | cons _ _ => simp [Mettapedia.OSLF.MeTTaIL.Engine.matchRelationArgs] at matched
  | argument :: arguments, seed, tuple, extension, metavariables, matched => by
    simp only [List.all_cons, Bool.and_eq_true] at metavariables
    cases tuple with
    | nil => simp [Mettapedia.OSLF.MeTTaIL.Engine.matchRelationArgs] at matched
    | cons value values =>
      cases argument with
      | fvar name =>
        simp only [Mettapedia.OSLF.MeTTaIL.Engine.matchRelationArgs, Mettapedia.OSLF.MeTTaIL.Engine.matchRelationArgument,
          List.mem_flatMap] at matched
        obtain ⟨headBindings, headMatched, rest⟩ := matched
        have headIn : ∀ entry ∈ headBindings, entry.2 ∈ value :: values := by
          intro entry member
          split at headMatched
          · split at headMatched
            · simp only [List.mem_singleton] at headMatched
              subst headMatched
              simp at member
            · simp at headMatched
          · simp only [List.mem_singleton] at headMatched
            subst headMatched
            simp only [List.mem_singleton] at member
            subst member
            simp
        split at rest
        · simp at rest
        · rename_i extended _
          simp only [List.mem_filterMap] at rest
          obtain ⟨tailBindings, tailMatched, merged⟩ := rest
          intro entry member
          rcases mem_of_mergeBindings tailBindings merged entry member with inHead | inTail
          · exact headIn entry inHead
          · exact List.mem_cons_of_mem _
              (mem_tuple_of_matchRelationArgs arguments metavariables.2 tailMatched entry inTail)
      | _ => simp [isMetavariable] at metavariables

/-- **A query over metavariables keeps captures free of sets**, in a store whose tuples have none. -/
theorem queryResult_free {relEnv : RelationEnv} {language : LanguageDef} (tuplesFree : TuplesSetFree relEnv)
    {bindings result : Bindings} {relation : String} {arguments : List Pattern}
    (metavariables : arguments.all isMetavariable = true) (valuesFree : ∀ entry ∈ bindings, setFree entry.2 = true)
    (member : result ∈ premiseStepWithEnv relEnv language bindings (.relationQuery relation arguments)) :
    ∀ entry ∈ result, setFree entry.2 = true := by
  simp only [premiseStepWithEnv, Mettapedia.OSLF.MeTTaIL.Engine.relationQueryStep, List.mem_flatMap,
    List.mem_filterMap, List.mem_append] at member
  obtain ⟨tuple, inTuples, extension, matched, merged⟩ := member
  have argumentsFree : ∀ value ∈ arguments.map (applyBindings bindings), setFree value = true := by
    intro value inArguments
    obtain ⟨argument, argumentMember, rfl⟩ := List.mem_map.mp inArguments
    cases argument with
    | fvar name =>
      rw [applyBindings_var]
      cases found : Bindings.lookup bindings name with
      | none => rfl
      | some captured =>
        obtain ⟨entry, entryMember, same⟩ := lookup_mem found
        simpa [same] using valuesFree entry entryMember
    | _ => exact absurd (List.all_eq_true.mp metavariables _ argumentMember) (by simp [isMetavariable])
  have tupleFree : ∀ x ∈ tuple, setFree x = true := by
    rcases inTuples with builtin | stored
    · unfold Mettapedia.OSLF.MeTTaIL.Engine.builtinRelationTuples at builtin
      split at builtin
      · rename_i lhs rhs instantiated
        have lhsFree := argumentsFree lhs (by rw [instantiated]; simp)
        have rhsFree := argumentsFree rhs (by rw [instantiated]; simp)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at builtin
        rcases builtin with rfl | rfl <;> simp [lhsFree, rhsFree]
      · simp at builtin
    · exact tuplesFree _ _ _ stored
  intro entry member
  rcases mem_of_mergeBindings extension merged entry member with inBindings | inExtension
  · exact valuesFree entry inBindings
  · exact tupleFree _ (mem_tuple_of_matchRelationArgs arguments metavariables matched entry inExtension)

/-- **An admitted premise at canonical captures** holds, to the canonical captures of its result, with steps no label
tells apart, and keeps captures free of sets. -/
theorem premiseCanon (respects : RespectsCanon relEnv) (tuplesFree : TuplesSetFree relEnv) {sites : Pattern}
    {premise : Premise} {bindings result : Bindings} {witness : Witness}
    (admitted : judgmentPremise premise = true) (valuesFree : ∀ entry ∈ bindings, setFree entry.2 = true)
    (simulated : ∀ step ∈ premiseSteps witness, Simulated relEnv language step)
    (valid : PremiseValid relEnv language sites bindings premise witness result) :
    (∀ entry ∈ result, setFree entry.2 = true) ∧ ∃ witness', PremiseValid relEnv language sites
        (canonBindings bindings) premise witness' (canonBindings result) ∧
      StepsAlike (premiseSteps witness) (premiseSteps witness') := by
  cases premise with
  | relationQuery relation arguments =>
    have metavariables : arguments.all isMetavariable = true := by simpa [judgmentPremise] using admitted
    cases valid with
    | base _ member =>
      exact ⟨queryResult_free tuplesFree metavariables valuesFree member, .base _,
        .base rfl (query_canon respects metavariables member), fun _ => rfl⟩
    | step endpoints _ _ _ => simp [stepEndpoints] at endpoints
  | congruence source target =>
    obtain ⟨label, arguments, rfl, plainArguments, firstTarget⟩ := judgmentStep_shape admitted
    obtain ⟨same, witness', valid', alike⟩ := judgmentCanon plainArguments firstTarget valuesFree simulated valid
    subst same
    exact ⟨valuesFree, witness', valid', alike⟩
  | forAll collection parameter body =>
    cases body with
    | congruence source target =>
      obtain ⟨label, arguments, rfl, plainArguments, firstTarget⟩ := judgmentStep_shape admitted
      obtain ⟨same, witness', valid', alike⟩ := forAllCanon plainArguments firstTarget valuesFree simulated valid
      subst same
      exact ⟨valuesFree, witness', valid', alike⟩
    | _ => simp [judgmentPremise] at admitted
  | freshness => simp [judgmentPremise] at admitted
  | scopedStep => simp [judgmentPremise] at admitted

/-- **Admitted premises at canonical captures** hold, to the canonical captures of their result, with steps no label
tells apart. -/
theorem premisesCanon (respects : RespectsCanon relEnv) (tuplesFree : TuplesSetFree relEnv) {sites : Pattern} :
    ∀ (premises : List Premise) {initial final : Bindings} {witnesses : List Witness},
    premises.all judgmentPremise = true → (∀ entry ∈ initial, setFree entry.2 = true) →
    (∀ step ∈ premiseStepsList witnesses, Simulated relEnv language step) →
    PremisesValid relEnv language sites initial premises witnesses final →
    ∃ witnesses', PremisesValid relEnv language sites (canonBindings initial) premises witnesses'
        (canonBindings final) ∧ StepsAlike (premiseStepsList witnesses) (premiseStepsList witnesses')
  | [], _, _, _, _, _, _, valid => by
    cases valid
    exact ⟨[], .nil _, fun _ => rfl⟩
  | premise :: premises, initial, final, _, admitted, valuesFree, simulated, valid => by
    simp only [List.all_cons, Bool.and_eq_true] at admitted
    cases valid with
    | cons head tail =>
      rename_i middle witness witnesses
      obtain ⟨middleFree, witness', head', headAlike⟩ := premiseCanon respects tuplesFree admitted.1 valuesFree
        (fun step member => simulated step (by rw [premiseStepsList_cons]; exact List.mem_append_left _ member)) head
      obtain ⟨witnesses', tail', tailAlike⟩ := premisesCanon respects tuplesFree premises admitted.2 middleFree
        (fun step member => simulated step (by rw [premiseStepsList_cons]; exact List.mem_append_right _ member)) tail
      refine ⟨witness' :: witnesses', .cons head' tail', ?_⟩
      rw [premiseStepsList_cons, premiseStepsList_cons]
      exact headAlike.append tailAlike

/-! ## Coherence -/

/-- **A step of a language whose premises are admitted is matched from the canonical form of its source**, by the same
rule, with the same labels and a target with the same canonical form. The steps inside its premises are matched first,
by the same theorem. -/
theorem simulatesJudgments (respects : RespectsCanon relEnv) (tuplesFree : TuplesSetFree relEnv)
    (admitted : language.rewrites.all (fun rule => rule.premises.all judgmentPremise) = true) :
    ∀ witness : Witness, Simulated relEnv language witness
  | .base _ => fun _ valid => by cases valid
  | .premiseStep _ _ _ _ => fun _ valid => by cases valid
  | .forAll _ => fun _ valid => by cases valid
  | .rule index initial witnesses => by
    intro free valid
    rename_i redex contractum
    cases valid with
    | rule found matched premises =>
      rename_i rule final
      have simulated : ∀ step ∈ premiseStepsList witnesses, Simulated relEnv language step :=
        fun step member => simulatesJudgments respects tuplesFree admitted step
      rw [matchPatternForRule_eq_syntactic, matchPattern_iff_matchRel] at matched
      obtain ⟨witnesses', canonValid, alike⟩ :=
        premisesCanon respects tuplesFree rule.premises (List.all_eq_true.mp admitted rule (List.mem_of_getElem? found))
          (capturesFree_matchRel rule.left redex initial free matched) simulated premises
      refine ⟨.rule index (canonBindings initial) witnesses',
        applyBindingsScoped (captureSites rule) (canonBindings final) 0 rule.right,
        .rule found ?_ canonValid, fun label => admits_alike label index _ _ alike, ?_⟩
      · rw [matchPatternForRule_eq_syntactic, matchPattern_iff_matchRel]
        exact matchRel_canon rule.left redex initial free matched
      · exact applyBindingsScoped_same _ (bindingsSame_canon final) 0 rule.right
termination_by witness => sizeOf witness
decreasing_by exact sizeOf_lt_rule member

/-- **Languages whose premises are admitted are coherent with sorted bags.** -/
theorem coherentJudgments (noEquations : language.equations = []) (noAlgebra : language.hasAlgebraDeclarations = false)
    (respects : RespectsCanon relEnv) (tuplesFree : TuplesSetFree relEnv)
    (admitted : language.rewrites.all (fun rule => rule.premises.all judgmentPremise) = true) (fuel : ℕ) :
    Coherent relEnv language fuel sortBags (domain language) List.singleton :=
  coherent_of_simulation (canonical noEquations noAlgebra) fun {redex _ _} _ inDomain valid => by
    simp only [domain, sortBags_eq_canon, Bool.and_eq_true] at inDomain
    rw [sortBags_eq_canon]
    exact simulatesJudgments respects tuplesFree admitted _ ((canon_setFree redex).symm.trans inDomain.1.2) valid

/-- **Canonical forms for a bag language with judgment premises**: no authored equations, no collection algebra, and
rules whose premises are guards, judgment steps, or judgment steps at each element of a captured collection. -/
def formsJudgments (noEquations : language.equations = []) (noAlgebra : language.hasAlgebraDeclarations = false)
    (respects : RespectsCanon relEnv) (tuplesFree : TuplesSetFree relEnv)
    (admitted : language.rewrites.all (fun rule => rule.premises.all judgmentPremise) = true) (fuel : ℕ) :
    CanonicalForms relEnv language fuel :=
  .ofCoherent (canonical noEquations noAlgebra) (coherentJudgments noEquations noAlgebra respects tuplesFree admitted fuel)

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.BagForms
