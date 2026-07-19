import Mettapedia.OSLF.MeTTaIL.Syntax

/-!
# One-hole contexts derived from language declarations

The shared `Pattern` carrier contains more shapes than any particular
`LanguageDef`.  This module therefore separates three notions:

* `OneHoleContext` is the structural derivative (zipper) of `Pattern`;
* `SignatureContext` records that every frame comes from a constructor slot in
  an authored term signature;
* `AuthoredContextFrame` records that an authored rewrite rule explicitly
  transports a `congruence` premise through that frame.

No collection representation is intrinsically reduction-active.  Contextual
closure is authority carried by rewrite rules.
-/

namespace Mettapedia.OSLF.MeTTaIL.DerivedContexts

open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## The structural derivative of `Pattern` -/

/-- A `Pattern` with exactly one distinguished hole. -/
inductive OneHoleContext where
  | hole
  | apply (constructor : String) (before : List Pattern)
      (inner : OneHoleContext) (after : List Pattern)
  | lambda (binderName : Option String) (inner : OneHoleContext)
  | multiLambda (arity : Nat) (binderNames : List String)
      (inner : OneHoleContext)
  | substBody (inner : OneHoleContext) (replacement : Pattern)
  | substReplacement (body : Pattern) (inner : OneHoleContext)
  | collection (collectionType : CollType) (before : List Pattern)
      (inner : OneHoleContext) (after : List Pattern) (rest : Option String)
deriving Repr, DecidableEq

namespace OneHoleContext

/-- Plug a pattern into the unique hole. -/
def fill : OneHoleContext → Pattern → Pattern
  | .hole, pattern => pattern
  | .apply constructor before inner after, pattern =>
      .apply constructor (before ++ inner.fill pattern :: after)
  | .lambda binderName inner, pattern =>
      .lambda binderName (inner.fill pattern)
  | .multiLambda arity binderNames inner, pattern =>
      .multiLambda arity binderNames (inner.fill pattern)
  | .substBody inner replacement, pattern =>
      .subst (inner.fill pattern) replacement
  | .substReplacement body inner, pattern =>
      .subst body (inner.fill pattern)
  | .collection collectionType before inner after rest, pattern =>
      .collection collectionType (before ++ inner.fill pattern :: after) rest

/-- Context composition: plug `inner` into the hole of `outer`. -/
def comp : OneHoleContext → OneHoleContext → OneHoleContext
  | .hole, inner => inner
  | .apply constructor before outer after, inner =>
      .apply constructor before (outer.comp inner) after
  | .lambda binderName outer, inner =>
      .lambda binderName (outer.comp inner)
  | .multiLambda arity binderNames outer, inner =>
      .multiLambda arity binderNames (outer.comp inner)
  | .substBody outer replacement, inner =>
      .substBody (outer.comp inner) replacement
  | .substReplacement body outer, inner =>
      .substReplacement body (outer.comp inner)
  | .collection collectionType before outer after rest, inner =>
      .collection collectionType before (outer.comp inner) after rest

@[simp] theorem fill_hole (pattern : Pattern) :
    fill .hole pattern = pattern := rfl

@[simp] theorem fill_comp (outer inner : OneHoleContext) (pattern : Pattern) :
    (outer.comp inner).fill pattern = outer.fill (inner.fill pattern) := by
  induction outer with
  | hole => rfl
  | apply constructor before outer after ih => simp [comp, fill, ih]
  | lambda binderName outer ih => simp [comp, fill, ih]
  | multiLambda arity binderNames outer ih => simp [comp, fill, ih]
  | substBody outer replacement ih => simp [comp, fill, ih]
  | substReplacement body outer ih => simp [comp, fill, ih]
  | collection collectionType before outer after rest ih => simp [comp, fill, ih]

end OneHoleContext

/-! ## Zipper derivation and its relational specification -/

/-- A proof that `context` selects an occurrence of `needle` in `pattern`.
The constructors are exactly the derivative of the `Pattern` constructors. -/
inductive Selects (needle : Pattern) : OneHoleContext → Pattern → Prop where
  | here : Selects needle .hole needle
  | apply {pattern : Pattern} {inner : OneHoleContext}
      {constructor : String} {before after : List Pattern} :
      Selects needle inner pattern →
      Selects needle (.apply constructor before inner after)
        (.apply constructor (before ++ pattern :: after))
  | lambda {inner : OneHoleContext} {pattern : Pattern}
      {binderName : Option String} :
      Selects needle inner pattern →
      Selects needle (.lambda binderName inner) (.lambda binderName pattern)
  | multiLambda {inner : OneHoleContext} {pattern : Pattern}
      {arity : Nat} {binderNames : List String} :
      Selects needle inner pattern →
      Selects needle (.multiLambda arity binderNames inner)
        (.multiLambda arity binderNames pattern)
  | substBody {inner : OneHoleContext} {pattern replacement : Pattern} :
      Selects needle inner pattern →
      Selects needle (.substBody inner replacement) (.subst pattern replacement)
  | substReplacement {inner : OneHoleContext} {body pattern : Pattern} :
      Selects needle inner pattern →
      Selects needle (.substReplacement body inner) (.subst body pattern)
  | collection {inner : OneHoleContext} {pattern : Pattern}
      {collectionType : CollType} {before after : List Pattern}
      {rest : Option String} :
      Selects needle inner pattern →
      Selects needle (.collection collectionType before inner after rest)
        (.collection collectionType (before ++ pattern :: after) rest)

/-- Every relationally selected context really reconstructs its source. -/
theorem Selects.fill_eq {needle pattern : Pattern} {context : OneHoleContext}
    (selected : Selects needle context pattern) :
    context.fill needle = pattern := by
  induction selected with
  | here => rfl
  | apply selected ih => simp [OneHoleContext.fill, ih]
  | lambda selected ih => simp [OneHoleContext.fill, ih]
  | multiLambda selected ih => simp [OneHoleContext.fill, ih]
  | substBody selected ih => simp [OneHoleContext.fill, ih]
  | substReplacement selected ih => simp [OneHoleContext.fill, ih]
  | collection selected ih => simp [OneHoleContext.fill, ih]

/-- Every one-hole context selects its hole after filling. -/
theorem Selects.of_fill (context : OneHoleContext) (needle : Pattern) :
    Selects needle context (context.fill needle) := by
  induction context with
  | hole => exact .here
  | apply constructor before inner after ih => exact .apply ih
  | lambda binderName inner ih => exact .lambda ih
  | multiLambda arity binderNames inner ih => exact .multiLambda ih
  | substBody inner replacement ih => exact .substBody ih
  | substReplacement body inner ih => exact .substReplacement ih
  | collection collectionType before inner after rest ih => exact .collection ih

/-- Enumerate the structural zippers selecting every occurrence of `needle`. -/
def zippersAt (needle : Pattern) : Pattern → List OneHoleContext
  | .bvar index => if needle = .bvar index then [.hole] else []
  | .fvar name => if needle = .fvar name then [.hole] else []
  | .apply constructor arguments =>
      (if needle = .apply constructor arguments then [.hole] else []) ++
        arguments.attach.zipIdx.flatMap fun (argument, index) =>
          (zippersAt needle argument.1).map fun inner =>
            .apply constructor (arguments.take index) inner
              (arguments.drop (index + 1))
  | .lambda binderName body =>
      (if needle = .lambda binderName body then [.hole] else []) ++
        (zippersAt needle body).map (.lambda binderName)
  | .multiLambda arity binderNames body =>
      (if needle = .multiLambda arity binderNames body then [.hole] else []) ++
        (zippersAt needle body).map (.multiLambda arity binderNames)
  | .subst body replacement =>
      (if needle = .subst body replacement then [.hole] else []) ++
        (zippersAt needle body).map (fun inner => .substBody inner replacement) ++
        (zippersAt needle replacement).map (fun inner => .substReplacement body inner)
  | .collection collectionType elements rest =>
      (if needle = .collection collectionType elements rest then [.hole] else []) ++
        elements.attach.zipIdx.flatMap fun (element, index) =>
          (zippersAt needle element.1).map fun inner =>
            .collection collectionType (elements.take index) inner
              (elements.drop (index + 1)) rest
termination_by pattern => sizeOf pattern
decreasing_by
  all_goals simp_wf
  all_goals first
    | (have smaller := List.sizeOf_lt_of_mem argument.property; omega)
    | (have smaller := List.sizeOf_lt_of_mem element.property; omega)
    | omega

private theorem take_getElem_drop {α : Type*} (elements : List α) (index : Nat)
    (inBounds : index < elements.length) :
    elements.take index ++ elements[index] :: elements.drop (index + 1) = elements := by
  rw [List.getElem_cons_drop inBounds]
  exact List.take_append_drop index elements

/-- Soundness of zipper compilation: every emitted context selects the stated
occurrence and therefore reconstructs the original pattern when filled. -/
theorem zippersAt_sound
    {needle pattern : Pattern} {context : OneHoleContext}
    (compiled : context ∈ zippersAt needle pattern) :
    Selects needle context pattern := by
  revert context
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      intro context compiled
      simp only [zippersAt] at compiled
      split at compiled
      · rename_i equal
        simp only [List.mem_singleton] at compiled
        subst context
        simpa [equal] using (Selects.here (needle := needle))
      · cases compiled
  | hfvar name =>
      intro context compiled
      simp only [zippersAt] at compiled
      split at compiled
      · rename_i equal
        simp only [List.mem_singleton] at compiled
        subst context
        simpa [equal] using (Selects.here (needle := needle))
      · cases compiled
  | happly constructor arguments recurse =>
      intro context compiled
      simp only [zippersAt, List.mem_append] at compiled
      rcases compiled with top | nested
      · split at top
        · rename_i equal
          simp only [List.mem_singleton] at top
          subst context
          simpa [equal] using (Selects.here (needle := needle))
        · cases top
      · rw [List.mem_flatMap] at nested
        obtain ⟨entry, attached, mapped⟩ := nested
        rcases entry with ⟨⟨argument, inArguments⟩, index⟩
        rw [List.mem_map] at mapped
        obtain ⟨inner, innerCompiled, contextEq⟩ := mapped
        subst context
        have attachedInfo := List.mem_zipIdx attached
        have indexBounds : index < arguments.attach.length := by omega
        have argumentAt : (arguments.attach)[index] = ⟨argument, inArguments⟩ := by
          simpa using attachedInfo.2.2.symm
        have originalBounds : index < arguments.length := by simpa using indexBounds
        have originalAt : arguments[index] = argument := by
          have := congrArg Subtype.val argumentAt
          simpa using this
        have selected := @Selects.apply needle argument inner constructor
          (arguments.take index) (arguments.drop (index + 1))
          (recurse argument inArguments innerCompiled)
        rw [← originalAt] at selected
        simpa [take_getElem_drop arguments index originalBounds] using selected
  | hlambda binderName body ih =>
      intro context compiled
      simp only [zippersAt, List.mem_append] at compiled
      rcases compiled with top | nested
      · split at top
        · rename_i equal
          simp only [List.mem_singleton] at top
          subst context
          simpa [equal] using (Selects.here (needle := needle))
        · cases top
      · rw [List.mem_map] at nested
        obtain ⟨inner, innerCompiled, contextEq⟩ := nested
        subst context
        exact .lambda (ih innerCompiled)
  | hmultiLambda arity binderNames body ih =>
      intro context compiled
      simp only [zippersAt, List.mem_append] at compiled
      rcases compiled with top | nested
      · split at top
        · rename_i equal
          simp only [List.mem_singleton] at top
          subst context
          simpa [equal] using (Selects.here (needle := needle))
        · cases top
      · rw [List.mem_map] at nested
        obtain ⟨inner, innerCompiled, contextEq⟩ := nested
        subst context
        exact .multiLambda (ih innerCompiled)
  | hsubst body replacement ihBody ihReplacement =>
      intro context compiled
      simp only [zippersAt, List.mem_append] at compiled
      rcases compiled with topOrBody | inReplacement
      · rcases topOrBody with top | inBody
        · split at top
          · rename_i equal
            simp only [List.mem_singleton] at top
            subst context
            simpa [equal] using (Selects.here (needle := needle))
          · cases top
        · rw [List.mem_map] at inBody
          obtain ⟨inner, innerCompiled, contextEq⟩ := inBody
          subst context
          exact .substBody (ihBody innerCompiled)
      · rw [List.mem_map] at inReplacement
        obtain ⟨inner, innerCompiled, contextEq⟩ := inReplacement
        subst context
        exact .substReplacement (ihReplacement innerCompiled)
  | hcollection collectionType elements rest recurse =>
      intro context compiled
      simp only [zippersAt, List.mem_append] at compiled
      rcases compiled with top | nested
      · split at top
        · rename_i equal
          simp only [List.mem_singleton] at top
          subst context
          simpa [equal] using (Selects.here (needle := needle))
        · cases top
      · rw [List.mem_flatMap] at nested
        obtain ⟨entry, attached, mapped⟩ := nested
        rcases entry with ⟨⟨element, inElements⟩, index⟩
        rw [List.mem_map] at mapped
        obtain ⟨inner, innerCompiled, contextEq⟩ := mapped
        subst context
        have attachedInfo := List.mem_zipIdx attached
        have indexBounds : index < elements.attach.length := by omega
        have elementAt : (elements.attach)[index] = ⟨element, inElements⟩ := by
          simpa using attachedInfo.2.2.symm
        have originalBounds : index < elements.length := by simpa using indexBounds
        have originalAt : elements[index] = element := by
          have := congrArg Subtype.val elementAt
          simpa using this
        have selected := @Selects.collection needle inner element collectionType
          (elements.take index) (elements.drop (index + 1)) rest
          (recurse element inElements innerCompiled)
        rw [← originalAt] at selected
        simpa [take_getElem_drop elements index originalBounds] using selected

private theorem zipIdx_getElem_mem {α : Type*} (elements : List α)
    (index : Nat) (inBounds : index < elements.length) :
    (elements[index], index) ∈ elements.zipIdx := by
  have zipBounds : index < elements.zipIdx.length := by simpa
  have member := List.getElem_mem (l := elements.zipIdx) zipBounds
  rw [List.getElem_zipIdx (j := 0) zipBounds] at member
  simpa using member

/-- Completeness of zipper compilation: every structural selection is emitted
by `zippersAt`. -/
theorem zippersAt_complete
    {needle pattern : Pattern} {context : OneHoleContext}
    (selected : Selects needle context pattern) :
    context ∈ zippersAt needle pattern := by
  induction selected with
  | here =>
      cases needle <;> simp [zippersAt]
  | @apply innerPattern inner constructor before after selected ih =>
      simp only [zippersAt, List.mem_append]
      right
      rw [List.mem_flatMap]
      let elements := before ++ innerPattern :: after
      have inBounds : before.length < elements.length := by
        simp [elements]
      let attachedElement : { element // element ∈ elements } :=
        ⟨elements[before.length], List.getElem_mem inBounds⟩
      have attachedBounds : before.length < elements.attach.length := by simpa
      have attachedAt : elements.attach[before.length] = attachedElement := by
        apply Subtype.ext
        simp [attachedElement]
      refine ⟨(attachedElement, before.length), ?_, ?_⟩
      · rw [← attachedAt]
        exact zipIdx_getElem_mem elements.attach before.length attachedBounds
      · rw [List.mem_map]
        refine ⟨inner, ?_, ?_⟩
        · simpa [attachedElement, elements] using ih
        · simp
  | lambda selected ih =>
      simp [zippersAt, ih]
  | multiLambda selected ih =>
      simp [zippersAt, ih]
  | substBody selected ih =>
      simp [zippersAt, ih]
  | substReplacement selected ih =>
      simp [zippersAt, ih]
  | @collection inner innerPattern collectionType before after rest selected ih =>
      simp only [zippersAt, List.mem_append]
      right
      rw [List.mem_flatMap]
      let elements := before ++ innerPattern :: after
      have inBounds : before.length < elements.length := by
        simp [elements]
      let attachedElement : { element // element ∈ elements } :=
        ⟨elements[before.length], List.getElem_mem inBounds⟩
      have attachedBounds : before.length < elements.attach.length := by simpa
      have attachedAt : elements.attach[before.length] = attachedElement := by
        apply Subtype.ext
        simp [attachedElement]
      refine ⟨(attachedElement, before.length), ?_, ?_⟩
      · rw [← attachedAt]
        exact zipIdx_getElem_mem elements.attach before.length attachedBounds
      · rw [List.mem_map]
        refine ⟨inner, ?_, ?_⟩
        · simpa [attachedElement, elements] using ih
        · simp

/-- The executable zipper derivative is exact. -/
theorem mem_zippersAt_iff_selects
    {needle pattern : Pattern} {context : OneHoleContext} :
    context ∈ zippersAt needle pattern ↔ Selects needle context pattern :=
  ⟨zippersAt_sound, zippersAt_complete⟩

/-! ## Contexts derived from a `LanguageDef` signature -/

/-- Sort-indexed contexts generated by declared constructor argument slots.
This derives syntax only; it does not grant reduction authority. -/
inductive SignatureContext (lang : LanguageDef) :
    String → String → OneHoleContext → Prop where
  | hole (sort : String) : SignatureContext lang sort sort .hole
  | simpleArg
      {source parameter result : String} {rule : GrammarRule}
      {parameterName : String} {beforeParams afterParams : List TermParam}
      {before after : List Pattern} {inner : OneHoleContext} :
      rule ∈ lang.terms →
      rule.params = beforeParams ++
        .simple parameterName (.base parameter) :: afterParams →
      before.length = beforeParams.length →
      after.length = afterParams.length →
      SignatureContext lang source parameter inner →
      SignatureContext lang source rule.category
        (.apply rule.label before inner after)
  | abstractionArg
      {source binderSort bodySort : String} {rule : GrammarRule}
      {binderName : Option String} {bodyName : String}
      {beforeParams afterParams : List TermParam}
      {before after : List Pattern} {inner : OneHoleContext} :
      rule ∈ lang.terms →
      rule.params = beforeParams ++
        .abstractionNamed binderName bodyName
          (.arrow (.base binderSort) (.base bodySort)) :: afterParams →
      before.length = beforeParams.length →
      after.length = afterParams.length →
      SignatureContext lang source bodySort inner →
      SignatureContext lang source rule.category
        (.apply rule.label before (.lambda binderName inner) after)
  | collectionElement
      {source elementSort : String} {rule : GrammarRule}
      {parameterName : String} {collectionType : CollType}
      {before after : List Pattern} {rest : Option String}
      {inner : OneHoleContext} :
      rule ∈ lang.terms →
      rule.params =
        [.simple parameterName (.collection collectionType (.base elementSort))] →
      SignatureContext lang source elementSort inner →
      SignatureContext lang source rule.category
        (.collection collectionType before inner after rest)

/-! ## Reduction authority derived from contextual rewrite rules -/

/-- A rewrite explicitly authorizes a one-hole frame when one of its
`congruence` premises supplies the hole's source and target and its left/right
sides are exactly that frame filled with those variables. -/
def RuleAuthorizesContext (rule : RewriteRule) (context : OneHoleContext) : Prop :=
  ∃ source target,
    .congruence (.fvar source) (.fvar target) ∈ rule.premises ∧
    rule.left = context.fill (.fvar source) ∧
    rule.right = context.fill (.fvar target)

/-- A single signature-derived frame with explicit rewrite-rule authority. -/
def AuthoredContextFrame (lang : LanguageDef)
    (sourceSort targetSort : String) (context : OneHoleContext) : Prop :=
  SignatureContext lang sourceSort targetSort context ∧
    ∃ rule ∈ lang.rewrites, RuleAuthorizesContext rule context

/-- Admissible contexts are the free category generated by authored context
frames: identity plus composition. -/
inductive AdmissibleContext (lang : LanguageDef) :
    String → String → OneHoleContext → Prop where
  | hole (sort : String) : AdmissibleContext lang sort sort .hole
  | comp
      {source middle target : String}
      {outer inner : OneHoleContext} :
      AuthoredContextFrame lang middle target outer →
      AdmissibleContext lang source middle inner →
      AdmissibleContext lang source target (outer.comp inner)

/-! ## Executable extraction from authored rules -/

/-- Compile all one-hole frames explicitly witnessed by congruence premises in
one rewrite rule.  Ambiguity is preserved as data rather than resolved by an
implicit collection policy. -/
def compileRuleContexts (rule : RewriteRule) : List OneHoleContext :=
  rule.premises.flatMap fun premise =>
    match premise with
    | .congruence (.fvar source) (.fvar target) =>
        (zippersAt (.fvar source) rule.left).filter fun context =>
          context.fill (.fvar target) = rule.right
    | _ => []

/-- Every compiled frame is authorized by the rule from which it was
compiled. -/
theorem compileRuleContexts_sound
    {rule : RewriteRule} {context : OneHoleContext}
    (compiled : context ∈ compileRuleContexts rule) :
    RuleAuthorizesContext rule context := by
  simp only [compileRuleContexts, List.mem_flatMap] at compiled
  obtain ⟨premise, premiseMem, compiled⟩ := compiled
  cases premise with
  | congruence sourcePattern targetPattern =>
      cases sourcePattern with
      | fvar source =>
          cases targetPattern with
          | fvar target =>
              simp only [List.mem_filter] at compiled
              exact ⟨source, target, premiseMem,
                (zippersAt_sound compiled.1).fill_eq.symm,
                (of_decide_eq_true compiled.2).symm⟩
          | _ => cases compiled
      | _ => cases compiled
  | _ => cases compiled

/-- Compilation is complete for every structurally selected context satisfying
the authored contextual-rule equations. -/
private theorem compileRuleContexts_complete_of_witness
    {rule : RewriteRule} {context : OneHoleContext} {source target : String}
    (premiseMem : .congruence (.fvar source) (.fvar target) ∈ rule.premises)
    (_left : rule.left = context.fill (.fvar source))
    (right : rule.right = context.fill (.fvar target))
    (selected : context ∈ zippersAt (.fvar source) rule.left) :
    context ∈ compileRuleContexts rule := by
  simp only [compileRuleContexts, List.mem_flatMap]
  refine ⟨.congruence (.fvar source) (.fvar target), premiseMem, ?_⟩
  simp only [List.mem_filter]
  exact ⟨selected, by simp [right]⟩

/-- Every authored contextual frame is recovered by the compiler. -/
theorem compileRuleContexts_complete
    {rule : RewriteRule} {context : OneHoleContext}
    (authorized : RuleAuthorizesContext rule context) :
    context ∈ compileRuleContexts rule := by
  obtain ⟨source, target, premiseMem, left, right⟩ := authorized
  apply compileRuleContexts_complete_of_witness premiseMem left right
  apply zippersAt_complete
  rw [left]
  exact Selects.of_fill context (.fvar source)

/-- Compiling contextual rewrite rules neither invents nor loses authority. -/
theorem mem_compileRuleContexts_iff_authorized
    {rule : RewriteRule} {context : OneHoleContext} :
    context ∈ compileRuleContexts rule ↔ RuleAuthorizesContext rule context :=
  ⟨compileRuleContexts_sound, compileRuleContexts_complete⟩

end Mettapedia.OSLF.MeTTaIL.DerivedContexts
