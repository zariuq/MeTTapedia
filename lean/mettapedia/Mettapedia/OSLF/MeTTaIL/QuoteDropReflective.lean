import Mettapedia.OSLF.MeTTaIL.QuoteDropMatching

/-!
# Reflective substitution and the quote-drop equation

Reflective substitution treats a quoted name as opaque: it compares the name's quote-drop normal
form with the substituted index and otherwise leaves it alone. Every drop of a well-sorted term
is applied to a name: an index, a free name or a quotation (`dropsNamed`). On such terms,
eliminating a binder from a term and from its quote-drop normal form gives quote-drop equal
results (`instantiate_normal`): a collapsed quotation `@(*n)` and its name `n` are treated alike,
because the substitution looks only at normal forms of names.

- `isName_normal`: the normal form of a name whose drops are applied to names is a name;
- `dropsNamed_normal`: the normal form keeps that property;
- `instantiate_normal`: binder elimination commutes with the normal form up to quote-drop
  equality;
- `reflectiveOperation_normal`: so does the reflective binder operation, for replacements with one
  normalized form.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.QuoteDrop

open Syntax ReflectiveSubstitution ReflectiveInstantiation CanonicalBags

variable {declaration : ReflectivePresentationDecl}

variable (declaration) in
/-- A name: an index, a free name or a quotation. -/
def isName : Pattern → Bool
  | .bvar _ | .fvar _ => true
  | .apply label [_] => label == declaration.quoteConstructor
  | _ => false

variable (declaration) in
/-- A single argument is a name. -/
def singleName : List Pattern → Bool
  | [argument] => isName declaration argument
  | _ => true

variable (declaration) in
/-- Every drop is applied to a name. -/
def dropsNamed : Pattern → Bool
  | .bvar _ | .fvar _ => true
  | .apply label arguments =>
      (label != declaration.dropConstructor || singleName declaration arguments) &&
      arguments.attach.all fun ⟨argument, _⟩ => dropsNamed argument
  | .lambda _ body => dropsNamed body
  | .multiLambda _ _ body => dropsNamed body
  | .subst body replacement => dropsNamed body && dropsNamed replacement
  | .collection _ elements _ => elements.attach.all fun ⟨element, _⟩ => dropsNamed element
decreasing_by all_goals sizeOf_pattern_dec

theorem dropsNamed_args {label : String} {arguments : List Pattern}
    (named : dropsNamed declaration (.apply label arguments) = true) :
    ∀ argument ∈ arguments, dropsNamed declaration argument = true := by
  rw [dropsNamed] at named
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_attach, true_implies, Subtype.forall] at named
  exact named.2

theorem dropsNamed_drop {name : Pattern}
    (named : dropsNamed declaration (.apply declaration.dropConstructor [name]) = true) : isName declaration name = true := by
  rw [dropsNamed] at named
  simp only [bne_self_eq_false, Bool.false_or, Bool.and_eq_true, singleName] at named
  exact named.1

theorem dropsNamed_of_apply {label : String} {arguments : List Pattern}
    (each : ∀ argument ∈ arguments, dropsNamed declaration argument = true)
    (atDrop : label = declaration.dropConstructor → ∀ argument, arguments = [argument] → isName declaration argument = true) :
    dropsNamed declaration (.apply label arguments) = true := by
  rw [dropsNamed]
  simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, List.all_eq_true, List.mem_attach, true_implies,
    Subtype.forall]
  refine ⟨?_, each⟩
  by_cases dropped : label = declaration.dropConstructor
  · right
    match arguments, atDrop dropped with
    | [argument], named => simpa [singleName] using named argument rfl
    | [], _ => rfl
    | _ :: _ :: _, _ => rfl
  · exact .inl dropped

theorem dropsNamed_collection {kind : CollType} {elements : List Pattern} {rest : Option String}
    (named : dropsNamed declaration (.collection kind elements rest) = true) :
    ∀ element ∈ elements, dropsNamed declaration element = true := by
  rw [dropsNamed] at named
  simpa using named

theorem plain_drop (distinct : declaration.dropConstructor ≠ declaration.quoteConstructor) (name : Pattern) :
    finishNormalizeReflectiveApply declaration declaration.dropConstructor [name] =
      .apply declaration.dropConstructor [name] := by
  unfold finishNormalizeReflectiveApply
  rw [if_neg (by simpa using distinct)]

theorem finish_quote_plain {payload : Pattern} (notDrop : ∀ name, payload ≠ .apply declaration.dropConstructor [name]) :
    finishNormalizeReflectiveApply declaration declaration.quoteConstructor [payload] =
      .apply declaration.quoteConstructor [payload] := by
  by_cases shaped : ∃ drop name, payload = .apply drop [name]
  · obtain ⟨drop, name, rfl⟩ := shaped
    rw [finish_drop]
    have different : drop ≠ declaration.dropConstructor := fun same => notDrop name (by rw [same])
    simp [different]
  · exact finish_plain declaration _ shaped

theorem isName_not_drop (distinct : declaration.dropConstructor ≠ declaration.quoteConstructor) {pattern name : Pattern}
    (nameShaped : isName declaration pattern = true) : pattern ≠ .apply declaration.dropConstructor [name] := by
  rintro rfl
  simp [isName, distinct] at nameShaped

/-- **The normal form of a name is a name**, and a normal form is a drop only for a drop. -/
theorem normal_shape_bounded (distinct : declaration.dropConstructor ≠ declaration.quoteConstructor) :
    ∀ (bound : Nat) (pattern : Pattern), sizeOf pattern < bound → dropsNamed declaration pattern = true →
      (isName declaration pattern = true → isName declaration (normal declaration pattern) = true) ∧
      (∀ name, normal declaration pattern = .apply declaration.dropConstructor [name] →
        ∃ argument, pattern = .apply declaration.dropConstructor [argument] ∧ normal declaration argument = name)
  | 0, _, small, _ => absurd small (Nat.not_lt_zero _)
  | _ + 1, .bvar index, _, _ => by
    refine ⟨fun _ => by rw [normal_bvar]; rfl, fun name same => ?_⟩
    rw [normal_bvar] at same; cases same
  | _ + 1, .fvar label, _, _ => by
    refine ⟨fun _ => by rw [normal_fvar]; rfl, fun name same => ?_⟩
    rw [normal_fvar] at same; cases same
  | _ + 1, .lambda binder body, _, _ => by
    refine ⟨fun nameShaped => by simp [isName] at nameShaped, fun name same => ?_⟩
    rw [normal_lambda] at same; cases same
  | _ + 1, .multiLambda arity binders body, _, _ => by
    refine ⟨fun nameShaped => by simp [isName] at nameShaped, fun name same => ?_⟩
    rw [normal_multiLambda] at same; cases same
  | _ + 1, .subst body replacement, _, _ => by
    refine ⟨fun nameShaped => by simp [isName] at nameShaped, fun name same => ?_⟩
    rw [normal_subst] at same; cases same
  | _ + 1, .collection kind elements rest, _, _ => by
    refine ⟨fun nameShaped => by simp [isName] at nameShaped, fun name same => ?_⟩
    rw [normal_collection] at same; cases same
  | bound + 1, .apply label arguments, small, named => by
    by_cases quoted : label = declaration.quoteConstructor
    · subst quoted
      rcases arguments with _ | ⟨payload, _ | ⟨second, rest⟩⟩
      · rw [normal_apply, List.map_nil, finish_nil]
        exact ⟨fun nameShaped => by simp [isName] at nameShaped, fun name same => by simp at same⟩
      rotate_left
      · rw [normal_apply, List.map_cons, List.map_cons, finish_long]
        exact ⟨fun nameShaped => by simp [isName] at nameShaped, fun name same => by simp at same⟩
      · have payloadNamed := dropsNamed_args named payload (by simp)
        rw [normal_apply, List.map_cons, List.map_nil]
        by_cases dropShaped : ∃ name, normal declaration payload = .apply declaration.dropConstructor [name]
        · obtain ⟨name, payloadNormal⟩ := dropShaped
          have payloadSmall : sizeOf payload < bound := by simp at small; omega
          obtain ⟨argument, rfl, argumentNormal⟩ :=
            (normal_shape_bounded distinct bound payload payloadSmall payloadNamed).2 name payloadNormal
          have argumentNamed := dropsNamed_args payloadNamed argument (by simp)
          have argumentName := dropsNamed_drop payloadNamed
          have argumentSmall : sizeOf argument < bound := by simp at small; omega
          have resultName := (normal_shape_bounded distinct bound argument argumentSmall argumentNamed).1 argumentName
          rw [payloadNormal, finish_drop]
          simp only [beq_self_eq_true, Bool.and_self, if_true]
          rw [← argumentNormal]
          exact ⟨fun _ => resultName, fun other same => absurd same (isName_not_drop distinct resultName)⟩
        · have plain : finishNormalizeReflectiveApply declaration declaration.quoteConstructor [normal declaration payload] =
              .apply declaration.quoteConstructor [normal declaration payload] :=
            finish_quote_plain (fun name same => dropShaped ⟨name, same⟩)
          rw [plain]
          exact ⟨fun _ => by simp [isName], fun name same => by simp at same; exact absurd same.1 distinct.symm⟩
    · rw [normal_apply, finish_not_quote quoted]
      refine ⟨fun nameShaped => ?_, fun name same => ?_⟩
      · match arguments, nameShaped with
        | [_], nameShaped => simp [isName, quoted] at nameShaped
        | [], nameShaped => simp [isName] at nameShaped
        | _ :: _ :: _, nameShaped => simp [isName] at nameShaped
      simp only [Pattern.apply.injEq] at same
      obtain ⟨rfl, mapped⟩ := same
      match arguments, mapped with
      | [argument], mapped =>
        simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at mapped
        exact ⟨argument, rfl, mapped⟩

/-- **The normal form of a name is a name**, and a normal form is a drop only for a drop. -/
theorem normal_shape (distinct : declaration.dropConstructor ≠ declaration.quoteConstructor) (pattern : Pattern)
    (named : dropsNamed declaration pattern = true) :
    (isName declaration pattern = true → isName declaration (normal declaration pattern) = true) ∧
      (∀ name, normal declaration pattern = .apply declaration.dropConstructor [name] →
        ∃ argument, pattern = .apply declaration.dropConstructor [argument] ∧ normal declaration argument = name) :=
  normal_shape_bounded distinct (sizeOf pattern + 1) pattern (Nat.lt_succ_self _) named

/-! ## Binder elimination -/

open ReflectiveSubstitution.BinderHead in
/-- A declared quote/drop equation preserves the whole-name head. -/
theorem QuoteDropStep.binderHead_eq
    (distinct : declaration.dropConstructor ≠ declaration.quoteConstructor)
    {left right : Pattern} (step : QuoteDropStep declaration left right) :
    ofPattern declaration left = ofPattern declaration right := by
  induction step with
  | collapse name =>
    cases head : ofPattern declaration name <;>
      simp [ofPattern, ofList, ReflectiveSubstitution.BinderHead.apply, rigid, distinct, head]
  | apply inner ih => simp [ofPattern, ofList_eq_map, ih]
  | lambda inner ih => rfl
  | multiLambda inner ih => rfl
  | substBody inner ih => rfl
  | substReplacement inner ih => rfl
  | @element kind before after element changed rest inner ih =>
    cases rest with
    | some rest => rfl
    | none => simp [ofPattern, ofList_eq_map, ih]

theorem nameMark_normal (distinct : declaration.dropConstructor ≠ declaration.quoteConstructor) (depth : Nat)
    (replacement name : Pattern) :
    nameMark declaration depth replacement (normal declaration name) = nameMark declaration depth replacement name := by
  unfold nameMark ReflectiveInstantiation.instantiate
  rw [ReflectiveCoherent.resolveQuotes_normalizeReflective distinct]

theorem beq_false_of_ne' {label other : String} (different : label ≠ other) : (label == other) = false := by
  simpa using different

/-- **Binder elimination ignores the quote-drop normal form**: it resolves
quotations first, and resolution subsumes the literal normal form. -/
theorem instantiate_normal (distinct : declaration.dropConstructor ≠ declaration.quoteConstructor) (pattern : Pattern) :
    dropsNamed declaration pattern = true → ∀ depth replacement,
      instantiate declaration depth replacement pattern = instantiate declaration depth replacement (normal declaration pattern) := by
  intro _ depth replacement
  unfold ReflectiveInstantiation.instantiate
  rw [ReflectiveCoherent.resolveQuotes_normalizeReflective distinct]

/-- **Declared binder elimination ignores the quote-drop normal form**, at every
quote scope: it resolves quotations first. -/
theorem instantiateDeclared_normal (distinct : declaration.dropConstructor ≠ declaration.quoteConstructor)
    (pattern : Pattern) (depth : Nat) (replacement : Pattern) :
    ReflectiveInstantiation.instantiateDeclared declaration depth replacement pattern =
      ReflectiveInstantiation.instantiateDeclared declaration depth replacement (normal declaration pattern) := by
  unfold ReflectiveInstantiation.instantiateDeclared
  cases declaration.quoteScope <;>
    simp only [ReflectiveSubstitution.substituteScoped, ReflectiveCoherent.resolveQuotes_normalizeReflective distinct]

/-- **The reflective binder operation commutes with the normal form of its body**, for a
replacement with one normalized form. -/
theorem reflectiveOperation_normal (distinct : declaration.dropConstructor ≠ declaration.quoteConstructor)
    {replacement replacement' body : Pattern}
    (sameReplacement : normalizeReflectiveReplacement declaration replacement =
      normalizeReflectiveReplacement declaration replacement') :
    ScopedRuleInstantiation.reflectiveOperation declaration replacement body =
      ScopedRuleInstantiation.reflectiveOperation declaration replacement' (normal declaration body) := by
  unfold ScopedRuleInstantiation.reflectiveOperation
  rw [sameReplacement]
  exact instantiateDeclared_normal distinct body 0 _

/-- An explicit quotation's normalized replacement depends only on the normal form of what it quotes. -/
theorem normalizeReflectiveReplacement_quote (payload payload' : Pattern)
    (same : normal declaration payload = normal declaration payload') :
    normalizeReflectiveReplacement declaration (.apply declaration.quoteConstructor [payload]) =
      normalizeReflectiveReplacement declaration (.apply declaration.quoteConstructor [payload']) := by
  simp only [normalizeReflectiveReplacement, beq_self_eq_true, if_true]
  exact congrArg (fun inner => Pattern.apply declaration.quoteConstructor [inner]) same

/-- **Ordinary binder elimination maps forward quote-drop chains to forward chains.** -/
theorem instantiateBVar_quoteDrop {replacement replacement' body body' : Pattern}
    (forwardReplacement : QuoteDropForward declaration replacement replacement')
    (forwardBody : QuoteDropForward declaration body body') :
    QuoteDropForward declaration (Substitution.instantiateBVar replacement body)
      (Substitution.instantiateBVar replacement' body') := by
  rw [← ContextSubstitution.substitute_single_eq_instantiateBVar,
    ← ContextSubstitution.substitute_single_eq_instantiateBVar]
  refine (forwardBody.substitute _).trans (quoteDropForward_substitute_assignment body' ?_)
  intro index
  cases index with
  | zero => exact forwardReplacement
  | succ => exact .refl

/-! ## Quotations exposing drops only literally

On terms whose drops receive names and whose quotations expose a drop only
literally (`ReflectiveCoherent.quotesLiteral`), resolving quotations is the
literal quote-drop normal form (`resolveQuotes_eq_normal`). -/

section Literal

open ReflectiveCoherent ReflectiveCanonical

/-- A name is a single member of the declared parallel composition. -/
theorem isMember_of_isName {pattern : Pattern} (named : isName declaration pattern = true) :
    IsMember declaration pattern := by
  cases pattern with
  | apply constructor arguments =>
      match arguments, named with
      | [_], _ => simp [IsMember]
  | bvar index => simp [IsMember]
  | fvar name => simp [IsMember]
  | lambda binder body => simp [isName] at named
  | multiLambda arity binders body => simp [isName] at named
  | subst body replacement => simp [isName] at named
  | collection kind elements rest => simp [isName] at named

/-- The quote-drop normal form keeps a single member a single member, on
terms whose drops receive names. -/
theorem isMember_normal (distinct : declaration.dropConstructor ≠ declaration.quoteConstructor)
    {pattern : Pattern} (named : dropsNamed declaration pattern = true)
    (member : IsMember declaration pattern) :
    IsMember declaration (normalizeReflective declaration pattern) := by
  cases pattern with
  | apply constructor arguments =>
      rw [← normal, normal_apply]
      rcases ReflectiveCoherent.finish_cases (declaration := declaration) constructor
          (arguments.map (normal declaration)) with plain | ⟨name, quoted, single, result⟩
      · rw [plain]
        refine ⟨?_, by simp⟩
        intro same
        simp only [Pattern.apply.injEq, List.map_eq_nil_iff] at same
        exact member.1 (by rw [same.1, same.2])
      · rw [result]
        obtain ⟨payload, rfl, payloadNormal⟩ := List.map_eq_singleton_iff.mp single
        have payloadNamed := dropsNamed_args named payload (by simp)
        obtain ⟨argument, rfl, argumentNormal⟩ :=
          (normal_shape distinct payload payloadNamed).2 name payloadNormal
        have argumentName := dropsNamed_drop payloadNamed
        have argumentNamed := dropsNamed_args payloadNamed argument (by simp)
        have resultName := (normal_shape distinct argument argumentNamed).1 argumentName
        rw [argumentNormal] at resultName
        exact isMember_of_isName resultName
  | collection kind elements rest =>
      rw [← normal, normal_collection]
      refine ⟨by simp, ?_⟩
      intro elements' same
      simp only [Pattern.collection.injEq] at same
      exact member.2 elements (by rw [same.1, same.2.2])
  | bvar index => exact member
  | fvar name => exact member
  | lambda binder body => simp [IsMember, normalizeReflective]
  | multiLambda arity binders body => simp [IsMember, normalizeReflective]
  | subst body replacement => simp [IsMember, normalizeReflective]

theorem dropsNamed_of_mem_parallelLeaves {pattern member : Pattern}
    (named : dropsNamed declaration pattern = true)
    (membership : member ∈ parallelLeaves declaration pattern) :
    dropsNamed declaration member = true := by
  by_cases single : IsMember declaration pattern
  · rw [parallelLeaves_of_isMember single, List.mem_singleton] at membership
    subst membership; exact named
  · induction pattern using Pattern.inductionOn with
    | hcollection kind elements rest ih =>
        cases rest with
        | some rest => exact absurd ⟨by simp, by simp⟩ single
        | none =>
            by_cases parallel : kind = declaration.parallelCollection
            · simp only [parallelLeaves, parallel, if_true, parallelLeavesList_eq_flatMap,
                List.mem_flatMap] at membership
              obtain ⟨element, elementMember, membership⟩ := membership
              have elementNamed := dropsNamed_collection named element elementMember
              by_cases elementSingle : IsMember declaration element
              · rw [parallelLeaves_of_isMember elementSingle, List.mem_singleton] at membership
                subst membership; exact elementNamed
              · exact ih element elementMember elementNamed membership elementSingle
            · exact absurd ⟨by simp, by simpa using parallel⟩ single
    | happly constructor arguments ih =>
        cases arguments with
        | nil =>
            by_cases unit : constructor = declaration.parallelUnitConstructor
            · simp [parallelLeaves, unit] at membership
            · exact absurd ⟨by simpa using unit, by simp⟩ single
        | cons argument arguments => exact absurd ⟨by simp, by simp⟩ single
    | hbvar index => exact absurd ⟨by simp, by simp⟩ single
    | hfvar name => exact absurd ⟨by simp, by simp⟩ single
    | hlambda binder body ih => exact absurd ⟨by simp, by simp⟩ single
    | hmultiLambda arity binders body ih => exact absurd ⟨by simp, by simp⟩ single
    | hsubst body replacement ihBody ihReplacement => exact absurd ⟨by simp, by simp⟩ single

/-- On terms whose drops receive names, the quote-drop normal form acts member
by member on the declared parallel composition. -/
theorem parallelLeaves_normal (distinct : declaration.dropConstructor ≠ declaration.quoteConstructor)
    {pattern : Pattern} (named : dropsNamed declaration pattern = true) :
    parallelLeaves declaration (normalizeReflective declaration pattern) =
      (parallelLeaves declaration pattern).map (normalizeReflective declaration) := by
  by_cases single : IsMember declaration pattern
  · rw [parallelLeaves_of_isMember single, parallelLeaves_of_isMember (isMember_normal distinct named single)]
    rfl
  · induction pattern using Pattern.inductionOn with
    | hcollection kind elements rest ih =>
        cases rest with
        | some rest => exact absurd ⟨by simp, by simp⟩ single
        | none =>
            by_cases parallel : kind = declaration.parallelCollection
            · subst parallel
              have each := dropsNamed_collection named
              rw [← normal, normal_collection]
              simp only [parallelLeaves, if_true, parallelLeavesList_eq_flatMap, List.flatMap_map,
                List.map_flatMap]
              refine List.flatMap_congr fun element member => ?_
              by_cases elementSingle : IsMember declaration element
              · rw [parallelLeaves_of_isMember elementSingle, parallelLeaves_of_isMember
                  (isMember_normal distinct (each element member) elementSingle)]
                rfl
              · exact ih element member (each element member) elementSingle
            · exact absurd ⟨by simp, by simpa using parallel⟩ single
    | happly constructor arguments ih =>
        cases arguments with
        | nil =>
            by_cases unit : constructor = declaration.parallelUnitConstructor
            · subst unit
              simp [normalizeReflective, normalizeReflectiveList, CanonicalBags.finish_nil, parallelLeaves]
            · exact absurd ⟨by simpa using unit, by simp⟩ single
        | cons argument arguments => exact absurd ⟨by simp, by simp⟩ single
    | hbvar index => exact absurd ⟨by simp, by simp⟩ single
    | hfvar name => exact absurd ⟨by simp, by simp⟩ single
    | hlambda binder body ih => exact absurd ⟨by simp, by simp⟩ single
    | hmultiLambda arity binders body ih => exact absurd ⟨by simp, by simp⟩ single
    | hsubst body replacement ihBody ihReplacement => exact absurd ⟨by simp, by simp⟩ single

private theorem exposedDrop?_drop (name : Pattern) :
    exposedDrop? declaration (.apply declaration.dropConstructor [name]) = some name :=
  exposedDrop?_eq_some_iff.mpr (parallelLeaves_of_isMember (by simp [IsMember]))

/-- On rho-shaped terms, resolving quotations is the quote-drop normal form. -/
theorem resolveQuotes_eq_normal (distinct : declaration.dropConstructor ≠ declaration.quoteConstructor)
    {pattern : Pattern} (named : dropsNamed declaration pattern = true)
    (literal : quotesLiteral declaration pattern = true) :
    resolveQuotes declaration pattern = normalizeReflective declaration pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => rfl
  | hfvar name => rfl
  | hlambda binder body ih =>
      simp only [resolveQuotes, normalizeReflective]
      rw [ih (by rw [dropsNamed] at named; exact named) literal]
  | hmultiLambda arity binders body ih =>
      simp only [resolveQuotes, normalizeReflective]
      rw [ih (by rw [dropsNamed] at named; exact named) literal]
  | hsubst body replacement ihBody ihReplacement =>
      rw [dropsNamed, Bool.and_eq_true] at named
      simp only [quotesLiteral, Bool.and_eq_true] at literal
      simp only [resolveQuotes, normalizeReflective]
      rw [ihBody named.1 literal.1, ihReplacement named.2 literal.2]
  | hcollection kind elements rest ih =>
      have each := dropsNamed_collection named
      have eachLiteral := (quotesLiteralList_iff elements).mp literal
      simp only [resolveQuotes, normalizeReflective, resolveQuotesList_eq_map,
        CanonicalBags.normalizeReflectiveList_map]
      congr 1
      exact List.map_congr_left fun element member =>
        ih element member (each element member) (eachLiteral element member)
  | happly constructor arguments ih =>
      have each := dropsNamed_args named
      have eachLiteral := quotesLiteral_args literal
      have mapped : arguments.map (resolveQuotes declaration) =
          arguments.map (normalizeReflective declaration) :=
        List.map_congr_left fun argument member =>
          ih argument member (each argument member) (eachLiteral argument member)
      simp only [resolveQuotes, normalizeReflective, resolveQuotesList_eq_map,
        CanonicalBags.normalizeReflectiveList_map, mapped]
      match arguments, literal with
      | [], _ => simp [finishResolveApply, CanonicalBags.finish_nil]
      | first :: second :: rest, _ =>
          simp [finishResolveApply, CanonicalBags.finish_long]
      | [payload], literal =>
          simp only [List.map_cons, List.map_nil, finishResolveApply]
          by_cases quoted : constructor = declaration.quoteConstructor
          · subst quoted
            simp only [if_true]
            by_cases dropShaped : ∃ name, normalizeReflective declaration payload =
                .apply declaration.dropConstructor [name]
            · obtain ⟨name, normal⟩ := dropShaped
              rw [normal, exposedDrop?_drop]
              simp [CanonicalBags.finish_drop]
            · rw [finish_quote_plain fun name same => dropShaped ⟨name, same⟩]
              cases exposed : exposedDrop? declaration (normalizeReflective declaration payload) with
              | none => rfl
              | some name =>
                  exfalso
                  have payloadNamed := each payload (by simp)
                  have leaves := exposedDrop?_eq_some_iff.mp exposed
                  rw [parallelLeaves_normal distinct payloadNamed] at leaves
                  obtain ⟨member, memberLeaves, memberNormal⟩ := List.map_eq_singleton_iff.mp leaves
                  have memberNamed := dropsNamed_of_mem_parallelLeaves (member := member)
                    payloadNamed (by simp [memberLeaves])
                  obtain ⟨argument, rfl, _⟩ :=
                    (normal_shape distinct member memberNamed).2 name memberNormal
                  have literalPayload : exposesLiterally declaration payload = true := by
                    simp only [quotesLiteral, Bool.and_eq_true, bne_self_eq_false,
                      Bool.false_or] at literal
                    exact literal.1
                  rw [exposesLiterally, exposedDrop?_eq_some_iff.mpr memberLeaves] at literalPayload
                  have payloadDrop := of_decide_eq_true literalPayload
                  subst payloadDrop
                  exact dropShaped ⟨_, by rw [← normal, normal_apply,
                    List.map_singleton, plain_drop distinct]⟩
          · simp [quoted, finish_not_quote quoted]

/-- A term whose quotations are resolved is already in quote-drop normal form. -/
theorem resolveQuotes_named {pattern : Pattern}
    (named : dropsNamed declaration pattern = true) :
    dropsNamed declaration (resolveQuotes declaration pattern) = true ∧
      (isName declaration pattern = true →
        isName declaration (resolveQuotes declaration pattern) = true) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => exact ⟨named, id⟩
  | hfvar name => exact ⟨named, id⟩
  | hlambda binder body ih =>
      rw [dropsNamed] at named
      refine ⟨?_, by simp [isName]⟩
      simp only [resolveQuotes]
      rw [dropsNamed]
      exact (ih named).1
  | hmultiLambda arity binders body ih =>
      rw [dropsNamed] at named
      refine ⟨?_, by simp [isName]⟩
      simp only [resolveQuotes]
      rw [dropsNamed]
      exact (ih named).1
  | hsubst body replacement ihBody ihReplacement =>
      rw [dropsNamed, Bool.and_eq_true] at named
      refine ⟨?_, by simp [isName]⟩
      simp only [resolveQuotes]
      rw [dropsNamed, Bool.and_eq_true]
      exact ⟨(ihBody named.1).1, (ihReplacement named.2).1⟩
  | hcollection kind elements rest ih =>
      have each := dropsNamed_collection named
      refine ⟨?_, by simp [isName]⟩
      simp only [resolveQuotes, resolveQuotesList_eq_map]
      rw [dropsNamed]
      simp only [List.all_eq_true, List.mem_attach, true_implies, Subtype.forall]
      intro element membership
      obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp membership
      exact (ih original originalMember (each original originalMember)).1
  | happly constructor arguments ih =>
      have each := dropsNamed_args named
      have eachIH : ∀ argument ∈ arguments,
          dropsNamed declaration (resolveQuotes declaration argument) = true ∧
            (isName declaration argument = true →
              isName declaration (resolveQuotes declaration argument) = true) :=
        fun argument member => ih argument member (each argument member)
      simp only [resolveQuotes, resolveQuotesList_eq_map]
      match arguments, named, eachIH with
      | [], _, _ =>
          refine ⟨dropsNamed_of_apply (by simp) (by simp), by simp [isName]⟩
      | first :: second :: rest, _, eachIH =>
          have mapped : ∀ argument ∈ (first :: second :: rest).map (resolveQuotes declaration),
              dropsNamed declaration argument = true := by
            intro argument membership
            obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp membership
            exact (eachIH original originalMember).1
          show dropsNamed declaration
              (.apply constructor ((first :: second :: rest).map (resolveQuotes declaration))) = true ∧ _
          exact ⟨dropsNamed_of_apply mapped (by simp), by simp [isName]⟩
      | [payload], named, eachIH =>
          obtain ⟨payloadNamed, payloadName⟩ := eachIH payload (by simp)
          have plain : dropsNamed declaration
              (.apply constructor [resolveQuotes declaration payload]) = true := by
            apply dropsNamed_of_apply
            · intro argument membership
              rw [List.mem_singleton] at membership
              subst membership
              exact payloadNamed
            · rintro rfl argument single
              rw [List.cons.injEq] at single
              rw [← single.1]
              exact payloadName (dropsNamed_drop named)
          simp only [List.map_cons, List.map_nil, finishResolveApply]
          by_cases quoted : constructor = declaration.quoteConstructor
          · subst quoted
            simp only [if_true]
            split
            · rename_i name exposed
              have dropNamed := dropsNamed_of_mem_parallelLeaves (member := .apply
                declaration.dropConstructor [name]) payloadNamed
                (by rw [exposedDrop?_eq_some_iff.mp exposed]; simp)
              exact ⟨dropsNamed_args dropNamed name (by simp),
                fun _ => dropsNamed_drop dropNamed⟩
            · exact ⟨plain, fun _ => by simp [isName]⟩
          · simp only [quoted, if_false]
            exact ⟨plain, fun nameShaped => by simp [isName, quoted] at nameShaped⟩

/-- The canonical form of a name whose drops receive names is a name. -/
theorem isName_canonicalize {pattern : Pattern}
    (named : dropsNamed declaration pattern = true)
    (nameShaped : isName declaration pattern = true) :
    isName declaration (canonicalize declaration pattern) = true := by
  rw [← canonicalize_resolveQuotes]
  have resolvedName := (resolveQuotes_named named).2 nameShaped
  have resolved := resolveQuotes_resolved (declaration := declaration) pattern
  generalize resolveQuotes declaration pattern = result at resolvedName resolved
  cases result with
  | bvar index => rfl
  | fvar name => rfl
  | apply constructor arguments =>
      match arguments, resolvedName, resolved with
      | [payload], resolvedName, resolved =>
          rw [canonicalize_unary_of_resolved resolved]
          simpa [isName] using resolvedName
  | lambda binder body => simp [isName] at resolvedName
  | multiLambda arity binders body => simp [isName] at resolvedName
  | subst body value => simp [isName] at resolvedName
  | collection kind elements rest => simp [isName] at resolvedName


end Literal

end Mettapedia.OSLF.MeTTaIL.QuoteDrop
