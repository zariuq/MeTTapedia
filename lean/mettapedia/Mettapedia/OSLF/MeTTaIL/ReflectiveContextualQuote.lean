import Mathlib.Data.Fintype.EquivFin
import Mettapedia.OSLF.MeTTaIL.ReflectiveInstantiation
import Mettapedia.OSLF.MeTTaIL.ReflectiveQuoteAdmission

/-!
# Contextual quotation: the core of reflective substitution and its views

A reflective presentation compares names modulo its declared equations
(quote-drop, and unit, associativity and commutativity of parallel
composition). Its binder elimination `ReflectiveInstantiation.instantiate`
first resolves every quotation whose payload is a drop modulo the parallel unit
and nesting, then substitutes structurally: a drop of the eliminated binder
receives the replacement and every other drop is substituted through. A
*genuine* quotation, one that survives resolution, is kept opaque. An index of
the eliminated binder inside it is therefore left as written and dangles, and an
ambient index inside it is not lowered.

This module makes the behaviour at a genuine quotation a declared view over one
core object.

## One traversal, one parameter

`substituteViewed` is `instantiate`'s traversal with one change: a genuine
quotation is entered, and inside it a second index action is used. Each view
is a choice of that action; outside quotations all views eliminate the binder
alike. Every operation here is this traversal with a declared inside action,
`instantiate` included: modulo the declared equations on every body, and
literally on canonical bodies.

* `applyView`: the inside action is the outside one. Substitution commutes
  with quotation, as in the Rholang interpreter, whose substitution recurses into
  quoted processes, and in MetaML (Taha and Sheard, 1997), where substitution
  enters code. A drop of the eliminated binder inside a quotation receives the
  value exactly as outside, as in Rholang, where `*x` is replaced by the
  received process.
* `freezeView`: inside a quotation the binder becomes a given name, its name in
  the reflective higher-order calculus of Meredith and Radestock (2005), whose
  names are global, so that a quoted process is impervious to substitution. A
  drop of the binder inside a quotation receives that name like any substituted
  value, so a name that is itself a quotation `@P` must be passed as `@(*@P)`,
  whose reception is the drop `*@P`; by the quote-drop equation it is the same
  name.
* `closureView`, the core: inside a quotation the binder keeps its value as
  explicit context.
* `instantiate` keeps quotations opaque. Its inside action is `keepIndex`,
  which leaves every index as written. Entering a quotation still respells a
  drop of the binder, `*(y | 0)` as `*y`, which is why the agreement is modulo
  the equations rather than literal on every resolved body. `instantiate`
  agrees with every view exactly on sealed bodies (below), which is how
  contextual modal type theory (Nanevski, Pfenning and Pientka, 2008) treats
  object variables at `box`.

## Representation of the context

The contextual quotation `@[σ]P` with `σ = [v/x]` is represented by
distributing `σ` over the constructors of `P`, as in calculi of explicit
substitutions (Abadi, Cardelli, Curien and Lévy, 1991). It stops at each
occurrence of `x`, which becomes `κ(v)` (`contextual`): the declared context
constructor `κ` applied to the value, lifted under the binders it crosses. This
is CMTT's closure form `clo(u, σ)` at the occurrence.

* It is a term of the calculus, not a side table. Canonicalization, scoping
  and substitution treat it as an ordinary application, so the coherence proof
  of the views covers the core unchanged, and a further substitution acts on the
  kept value like on any other subterm.
* The quotation stays a quotation of a term, and no index is permuted: the
  binder structure of `P` is untouched.
* `κ` lies outside the presentation's signature. Some such freshness is
  unavoidable: `closureView_not_factorable` exhibits a body that already
  contains `κ(v)` and has the same closure as a body that mentions the binder,
  while their apply views differ. `exists_freshContext` shows that a fresh `κ`
  always exists.

## Results

* Coherence, for every pair of actions and every declaration, hence for every
  view: `canonicalize_substituteViewed_resolveQuotes`,
  `substituteViewed_respects`, `closureView_respects`, `applyView_respects`,
  `freezeView_respects`.
* `instantiate` is one traversal: `instantiate_equivalent_substituteViewed`
  (every body, modulo the equations) and
  `instantiate_eq_substituteViewed_of_isCanonical` (canonical bodies,
  literally); `instantiate_not_substituteViewed` shows that no inside action
  gives literal equality on every resolved body.
* The views are observations of the core: `openContexts` opens every context,
  and `erase_closureView` (`apply = erase ∘ closure`) and `atomize_closureView`
  (`freeze = atomize ∘ closure`, for a closed name) hold for every depth,
  replacement and body without `κ`; `exists_closure_factorization` states this
  for every body. The
  closure keeps strictly more (controls).
* Sealed bodies, where no genuine quotation mentions the eliminated binder
  (`Sealed`): the views coincide (`freezeView_eq_applyView_of_sealed`,
  `closureView_eq_applyView_of_sealed`) and equal `instantiate` on bodies
  scoped under the binder (`applyView_eq_instantiate_of_sealed`). On
  quotation-sealed bodies (`binderSafeAt`, the admission of
  `instantiate_scoped`) they equal `instantiate` with ambient binders too
  (`applyView_eq_instantiate_of_binderSafeAt`).
* Sealed admission respects the declared equations (`sealed_respects`,
  `scopeAdmits_respects`). The equations never move an index
  (`mentions_canonicalize`), and on a resolved body a quotation test that reads
  its payload modulo the equations sees the same quotations in the canonical
  form (`everyQuotation_canonicalize`), so a body is sealed exactly when its
  canonical form is (`sealed_iff_canonicalize`). The unresolved admission
  `binderSafeAt` does not respect the equations: it accepts `y` and rejects
  `@(*y)` (`binderSafeAt_not_respects`).
* No view loses a binding dependency: `applyView_scoped`, `freezeView_scoped`
  and `closureView_scoped` need only ordinary scope, while `instantiate` needs
  quotation sealing; the controls show it leaving an index dangling.
* The declaration: a presentation's `quoteScope`, closed or reaching with a
  view; `substituteUnder` eliminates a binder under a scope, with
  `substituteUnder_respects`, `substituteUnder_scoped` and
  `substituteUnder_eq_instantiate_of_sealed`. The traversal `substituteViewed`
  and its coherence live in the core, where the rule application uses them.

## References

* M. Abadi, L. Cardelli, P.-L. Curien, J.-J. Lévy, *Explicit substitutions*,
  Journal of Functional Programming 1(4), 1991.
* L. G. Meredith, M. Radestock, *A reflective higher-order calculus*, ENTCS 141(5),
  2005.
* A. Nanevski, F. Pfenning, B. Pientka, *Contextual modal type theory*, ACM
  Transactions on Computational Logic 9(3), 2008.
* W. Taha, T. Sheard, *Multi-stage programming with explicit annotations*,
  PEPM 1997; *MetaML and multi-stage programming with explicit annotations*,
  Theoretical Computer Science 248, 2000.
* The Rholang interpreter (RChain), substitution of normalized processes.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.ReflectiveContextualQuote

open Syntax Reflection Substitution ScopedPattern ReflectiveSubstitution ReflectiveCanonical
open ReflectiveCoherent ReflectiveInstantiation ReflectiveQuoteAdmission

/-- Binder elimination at one index: an index below the eliminated level is
kept, the eliminated level becomes the replacement lifted under the
intervening binders, and an index above it is lowered. -/
def lowering (replacement : Pattern) (level index : Nat) : Pattern :=
  instantiateBVarAt level replacement (.bvar index)

theorem lowering_of_lt {replacement : Pattern} {level index : Nat} (below : index < level) :
    lowering replacement level index = .bvar index := by
  simp [lowering, instantiateBVarAt, below]

theorem lowering_self (replacement : Pattern) (level : Nat) :
    lowering replacement level level = liftBVars 0 level replacement := by
  simp [lowering, instantiateBVarAt]

theorem lowering_of_gt {replacement : Pattern} {level index : Nat} (above : level < index) :
    lowering replacement level index = .bvar (index - 1) := by
  simp [lowering, instantiateBVarAt, Nat.not_lt.mpr above.le, Nat.ne_of_gt above]

/-- Away from the eliminated level, lowering does not consult the replacement. -/
theorem lowering_of_ne (first second : Pattern) {level index : Nat} (other : index ≠ level) :
    lowering first level index = lowering second level index := by
  rcases Nat.lt_or_gt_of_ne other with below | above
  · rw [lowering_of_lt below, lowering_of_lt below]
  · rw [lowering_of_gt above, lowering_of_gt above]

/-- `instantiate` is the traversal that keeps every genuine quotation opaque. -/
theorem instantiate_eq (declaration : ReflectivePresentationDecl) (depth : Nat)
    (replacement body : Pattern) :
    instantiate declaration depth replacement body =
      substituteResolved declaration (lowering replacement) depth
        (resolveQuotes declaration body) := rfl

/-! ## The core and its views -/

/-- The eliminated value kept as explicit context: `κ(v)`. -/
def contextual (context : String) (value : Pattern) : Pattern := .apply context [value]

/-- The closure view: inside a genuine quotation the eliminated binder keeps
its value as explicit context. -/
def closureView (declaration : ReflectivePresentationDecl) (context : String) (depth : Nat)
    (replacement body : Pattern) : Pattern :=
  substituteViewed declaration (lowering (contextual context replacement)) (lowering replacement)
    depth (resolveQuotes declaration body)

/-- The apply view: substitution enters genuine quotations like any other
constructor. -/
def applyView (declaration : ReflectivePresentationDecl) (depth : Nat)
    (replacement body : Pattern) : Pattern :=
  substituteViewed declaration (lowering replacement) (lowering replacement)
    depth (resolveQuotes declaration body)

/-- The freeze view: inside a genuine quotation the eliminated binder becomes
`name`, lifted under the binders it crosses, and a drop of it receives `name`. -/
def freezeView (declaration : ReflectivePresentationDecl) (depth : Nat)
    (replacement name body : Pattern) : Pattern :=
  substituteViewed declaration (lowering name) (lowering replacement)
    depth (resolveQuotes declaration body)

/-! ## Coherence: every view respects the declared equations -/

section Coherence

variable {declaration : ReflectivePresentationDecl}

theorem closureView_respects (context : String) (depth : Nat) (replacement : Pattern)
    {left right : Pattern} (same : canonicalEquivalent declaration left right = true) :
    canonicalEquivalent declaration (closureView declaration context depth replacement left)
      (closureView declaration context depth replacement right) = true :=
  substituteViewed_respects _ _ depth same

theorem applyView_respects (depth : Nat) (replacement : Pattern)
    {left right : Pattern} (same : canonicalEquivalent declaration left right = true) :
    canonicalEquivalent declaration (applyView declaration depth replacement left)
      (applyView declaration depth replacement right) = true :=
  substituteViewed_respects _ _ depth same

theorem freezeView_respects (depth : Nat) (replacement name : Pattern)
    {left right : Pattern} (same : canonicalEquivalent declaration left right = true) :
    canonicalEquivalent declaration (freezeView declaration depth replacement name left)
      (freezeView declaration depth replacement name right) = true :=
  substituteViewed_respects _ _ depth same

end Coherence

/-! ## The core is one traversal

`instantiate` keeps a genuine quotation as written. The traversal whose inside
action leaves every index as written, `keepIndex`, enters it instead, and there
it respells each drop of the eliminated binder as the literal drop: `*(y | 0)`
becomes `*y`. That respelling is an instance of the declared equations, so the
two operations are equal modulo the equations on every body, and literally
equal on canonical bodies. No inside action makes them literally equal on all
resolved bodies (`instantiate_not_substituteViewed`). -/

/-- The index action that leaves every index as written. -/
def keepIndex : Nat → Nat → Pattern := fun _ index => .bvar index

section OneTraversal

variable {declaration : ReflectivePresentationDecl}

theorem canonicalize_apply_congr (constructor : String) {left right : List Pattern}
    (same : left.map (canonicalize declaration) = right.map (canonicalize declaration)) :
    canonicalize declaration (.apply constructor left) =
      canonicalize declaration (.apply constructor right) := by
  simp only [canonicalize, canonicalizeList_eq_map, same]

theorem canonicalize_collection_congr (kind : CollType) (rest : Option String)
    {left right : List Pattern}
    (same : left.map (canonicalize declaration) = right.map (canonicalize declaration)) :
    canonicalize declaration (.collection kind left rest) =
      canonicalize declaration (.collection kind right rest) := by
  cases rest <;> simp only [canonicalize, canonicalizeList_eq_map, same]

/-- A drop recognized as the binder has the canonical form of the literal drop. -/
theorem canonicalize_eq_bvar_of_matchesBinder {depth : Nat} {payload : Pattern}
    (matched : matchesBinder declaration depth payload = true) :
    canonicalize declaration payload = .bvar depth := by
  simp only [matchesBinder, decide_eq_true_eq] at matched
  exact (ReflectiveCanonical.BinderHead.ofPattern_index_iff _ _ _).mp matched

/-- Leaving every index as written changes a term only up to the declared
equations. -/
theorem canonicalize_substituteViewed_keepIndex (pattern : Pattern) :
    ∀ depth, canonicalize declaration
        (substituteViewed declaration keepIndex keepIndex depth pattern) =
      canonicalize declaration pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro _; rfl
  | hfvar name => intro _; rfl
  | hlambda binder body ih => intro depth; simp only [substituteViewed, canonicalize, ih]
  | hmultiLambda arity binders body ih => intro depth; simp only [substituteViewed, canonicalize, ih]
  | hsubst body value ihBody ihValue =>
      intro depth; simp only [substituteViewed, canonicalize, ihBody, ihValue]
  | hcollection kind elements rest ih =>
      intro depth
      simp only [substituteViewed, substituteViewedList_eq_map]
      exact canonicalize_collection_congr kind rest
        (by rw [List.map_map]; exact List.map_congr_left fun p m => ih p m depth)
  | happly constructor arguments ih =>
      intro depth
      match arguments, ih with
      | [], _ => rfl
      | first :: second :: rest, ih =>
          simp only [substituteViewed, substituteViewedList_eq_map]
          exact canonicalize_apply_congr constructor
            (by rw [List.map_map]; exact List.map_congr_left fun p m => ih p m depth)
      | [payload], ih =>
          have inner := ih payload (by simp) depth
          simp only [substituteViewed]
          split_ifs with isQuote isDrop matched
          · exact canonicalize_apply_congr constructor (by simp [inner])
          · exact canonicalize_apply_congr constructor
              (by simp [keepIndex, canonicalize_eq_bvar_of_matchesBinder matched, canonicalize])
          · exact canonicalize_apply_congr constructor (by simp [inner])
          · exact canonicalize_apply_congr constructor (by simp [inner])

/-- Entering quotations with `keepIndex` is keeping them opaque, up to the
declared equations, on every term. -/
theorem canonicalize_substituteViewed_keepIndex_substituteResolved (atIndex : Nat → Nat → Pattern)
    (pattern : Pattern) :
    ∀ depth, canonicalize declaration (substituteViewed declaration keepIndex atIndex depth pattern) =
      canonicalize declaration (substituteResolved declaration atIndex depth pattern) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro _; rfl
  | hfvar name => intro _; rfl
  | hlambda binder body ih =>
      intro depth; simp only [substituteViewed, substituteResolved, canonicalize, ih]
  | hmultiLambda arity binders body ih =>
      intro depth; simp only [substituteViewed, substituteResolved, canonicalize, ih]
  | hsubst body value ihBody ihValue =>
      intro depth; simp only [substituteViewed, substituteResolved, canonicalize, ihBody, ihValue]
  | hcollection kind elements rest ih =>
      intro depth
      simp only [substituteViewed, substituteResolved, substituteViewedList_eq_map,
        substituteResolvedList_eq_map]
      exact canonicalize_collection_congr kind rest
        (by rw [List.map_map, List.map_map]; exact List.map_congr_left fun p m => ih p m depth)
  | happly constructor arguments ih =>
      intro depth
      match arguments, ih with
      | [], _ => rfl
      | first :: second :: rest, ih =>
          simp only [substituteViewed, substituteResolved, substituteViewedList_eq_map,
            substituteResolvedList_eq_map]
          exact canonicalize_apply_congr constructor
            (by rw [List.map_map, List.map_map]; exact List.map_congr_left fun p m => ih p m depth)
      | [payload], ih =>
          have inner := ih payload (by simp) depth
          simp only [substituteViewed, substituteResolved]
          split_ifs
          · exact canonicalize_apply_congr constructor
              (by simp [canonicalize_substituteViewed_keepIndex])
          · rfl
          · exact canonicalize_apply_congr constructor (by simp [inner])
          · exact canonicalize_apply_congr constructor (by simp [inner])

/-- **`instantiate` is the traversal whose inside action leaves every index as
written**, up to the declared equations, on every body. -/
theorem instantiate_equivalent_substituteViewed (depth : Nat) (replacement body : Pattern) :
    canonicalEquivalent declaration (instantiate declaration depth replacement body)
      (substituteViewed declaration keepIndex (lowering replacement) depth
        (resolveQuotes declaration body)) = true :=
  canonicalEquivalent_eq_true_iff.mpr
    (canonicalize_substituteViewed_keepIndex_substituteResolved _ _ depth).symm

/-- On a canonical term, leaving every index as written changes nothing. -/
theorem substituteViewed_keepIndex_of_isCanonical {pattern : Pattern}
    (canonical : IsCanonical declaration pattern) :
    ∀ depth, substituteViewed declaration keepIndex keepIndex depth pattern = pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro _; rfl
  | hfvar name => intro _; rfl
  | hlambda binder body ih => intro depth; simp only [substituteViewed, ih canonical]
  | hmultiLambda arity binders body ih => intro depth; simp only [substituteViewed, ih canonical]
  | hsubst body value ihBody ihValue =>
      intro depth; simp only [substituteViewed, ihBody canonical.1, ihValue canonical.2]
  | hcollection kind elements rest ih =>
      intro depth
      simp only [substituteViewed, substituteViewedList_eq_map]
      rw [(List.map_congr_left fun p m =>
        ih p m (isCanonicalList_mem declaration canonical.1 m) depth).trans (List.map_id' _)]
  | happly constructor arguments ih =>
      intro depth
      have each : ∀ p ∈ arguments, IsCanonical declaration p :=
        fun _ m => isCanonicalList_mem declaration canonical.1 m
      match arguments, each, ih with
      | [], _, _ => rfl
      | first :: second :: rest, each, ih =>
          simp only [substituteViewed, substituteViewedList_eq_map]
          rw [(List.map_congr_left fun p m => ih p m (each p m) depth).trans (List.map_id' _)]
      | [payload], each, ih =>
          have payloadCanonical := each payload (by simp)
          have inner := ih payload (by simp) payloadCanonical depth
          simp only [substituteViewed]
          split_ifs with isQuote isDrop matched
          · rw [inner]
          · have literal := canonicalize_eq_bvar_of_matchesBinder matched
            rw [canonicalize_eq_of_isCanonical declaration payloadCanonical] at literal
            subst literal
            rfl
          · rw [inner]
          · rw [inner]

/-- On a canonical term, entering quotations with `keepIndex` is keeping them
opaque. -/
theorem substituteViewed_keepIndex_eq_substituteResolved (atIndex : Nat → Nat → Pattern)
    {pattern : Pattern} (canonical : IsCanonical declaration pattern) :
    ∀ depth, substituteViewed declaration keepIndex atIndex depth pattern =
      substituteResolved declaration atIndex depth pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro _; rfl
  | hfvar name => intro _; rfl
  | hlambda binder body ih =>
      intro depth; simp only [substituteViewed, substituteResolved, ih canonical]
  | hmultiLambda arity binders body ih =>
      intro depth; simp only [substituteViewed, substituteResolved, ih canonical]
  | hsubst body value ihBody ihValue =>
      intro depth
      simp only [substituteViewed, substituteResolved, ihBody canonical.1, ihValue canonical.2]
  | hcollection kind elements rest ih =>
      intro depth
      simp only [substituteViewed, substituteResolved, substituteViewedList_eq_map,
        substituteResolvedList_eq_map]
      rw [List.map_congr_left fun p m => ih p m (isCanonicalList_mem declaration canonical.1 m) depth]
  | happly constructor arguments ih =>
      intro depth
      have each : ∀ p ∈ arguments, IsCanonical declaration p :=
        fun _ m => isCanonicalList_mem declaration canonical.1 m
      match arguments, each, ih with
      | [], _, _ => rfl
      | first :: second :: rest, each, ih =>
          simp only [substituteViewed, substituteResolved, substituteViewedList_eq_map,
            substituteResolvedList_eq_map]
          rw [List.map_congr_left fun p m => ih p m (each p m) depth]
      | [payload], each, ih =>
          have payloadCanonical := each payload (by simp)
          simp only [substituteViewed, substituteResolved]
          split_ifs
          · rw [substituteViewed_keepIndex_of_isCanonical payloadCanonical]
          · rfl
          · rw [ih payload (by simp) payloadCanonical depth]
          · rw [ih payload (by simp) payloadCanonical depth]

/-- A canonical quotation payload exposes no drop. -/
theorem exposedDrop?_of_isCanonical {payload : Pattern} (canonical : IsCanonical declaration payload)
    (notDrop : ∀ name, payload ≠ .apply declaration.dropConstructor [name]) :
    exposedDrop? declaration payload = none := by
  rcases exposed : exposedDrop? declaration payload with _ | name
  · rfl
  · exfalso
    have leaves := exposedDrop?_eq_some_iff.mp exposed
    by_cases isUnit : payload = .apply declaration.parallelUnitConstructor []
    · subst isUnit; simp [parallelLeaves] at leaves
    · by_cases isParallel : ∃ elements, payload = .collection declaration.parallelCollection elements none
      · obtain ⟨elements, rfl⟩ := isParallel
        have properties := canonical.2 ⟨rfl, rfl⟩
        have flat : parallelLeaves declaration
            (.collection declaration.parallelCollection elements none) = elements := by
          simp only [parallelLeaves, if_true, parallelLeavesList_eq_flatMap]
          rw [List.flatMap_congr fun element member => parallelLeaves_of_isMember
            ⟨(properties.2.2 element member).1, (properties.2.2 element member).2⟩]
          exact List.flatMap_singleton' elements
        rw [flat] at leaves
        have length := properties.1
        rw [leaves] at length
        simp at length
      · have member : IsMember declaration payload :=
          ⟨isUnit, fun elements same => isParallel ⟨elements, same⟩⟩
        rw [parallelLeaves_of_isMember member, List.singleton_inj] at leaves
        exact notDrop name leaves

/-- Canonical terms are resolved. -/
theorem quotesResolved_of_isCanonical {pattern : Pattern} (canonical : IsCanonical declaration pattern) :
    QuotesResolved declaration pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => trivial
  | hfvar name => trivial
  | hlambda binder body ih => exact ih canonical
  | hmultiLambda arity binders body ih => exact ih canonical
  | hsubst body value ihBody ihValue => exact ⟨ihBody canonical.1, ihValue canonical.2⟩
  | hcollection kind elements rest ih =>
      exact (quotesResolvedList_iff elements).mpr fun p m =>
        ih p m (isCanonicalList_mem declaration canonical.1 m)
  | happly constructor arguments ih =>
      refine ⟨(quotesResolvedList_iff arguments).mpr fun p m =>
        ih p m (isCanonicalList_mem declaration canonical.1 m), ?_⟩
      rintro payload rfl isQuote
      exact exposedDrop?_of_isCanonical (isCanonicalList_mem declaration canonical.1 (by simp))
        fun name same => canonical.2 name isQuote (by rw [same])

/-- **On canonical bodies, `instantiate` is literally the traversal whose
inside action leaves every index as written.** -/
theorem instantiate_eq_substituteViewed_of_isCanonical {depth : Nat} {replacement body : Pattern}
    (canonical : IsCanonical declaration body) :
    instantiate declaration depth replacement body =
      substituteViewed declaration keepIndex (lowering replacement) depth
        (resolveQuotes declaration body) := by
  rw [instantiate_eq, resolveQuotes_of_resolved (quotesResolved_of_isCanonical canonical),
    substituteViewed_keepIndex_eq_substituteResolved _ canonical]

end OneTraversal

/-! ## Observations of the core -/

/-- The value of a context reference `κ(v)`. -/
def contextOf? (context : String) : Pattern → Option Pattern
  | .apply constructor [value] => if constructor = context then some value else none
  | _ => none

mutual
  /-- Open every context reference with `observe`: `κ(v)` becomes `observe v`,
  and a drop of a context reference receives `observe v`, as a drop of the
  selected binder does. Everything else is kept. -/
  def openContexts (declaration : ReflectivePresentationDecl) (context : String)
      (observe : Pattern → Pattern) : Pattern → Pattern
    | .bvar index => .bvar index
    | .fvar name => .fvar name
    | .apply constructor [] => .apply constructor []
    | .apply constructor [payload] =>
        if constructor = declaration.quoteConstructor then
          .apply constructor [openContexts declaration context observe payload]
        else if constructor = context then observe payload
        else if constructor = declaration.dropConstructor then
          match contextOf? context payload with
          | some value => receive declaration constructor (observe value)
          | none => .apply constructor [openContexts declaration context observe payload]
        else .apply constructor [openContexts declaration context observe payload]
    | .apply constructor (first :: second :: rest) =>
        .apply constructor (openContextsList declaration context observe (first :: second :: rest))
    | .lambda binder body => .lambda binder (openContexts declaration context observe body)
    | .multiLambda arity binders body =>
        .multiLambda arity binders (openContexts declaration context observe body)
    | .subst body value =>
        .subst (openContexts declaration context observe body)
          (openContexts declaration context observe value)
    | .collection kind elements rest =>
        .collection kind (openContextsList declaration context observe elements) rest

  /-- List recursion for `openContexts`. -/
  def openContextsList (declaration : ReflectivePresentationDecl) (context : String)
      (observe : Pattern → Pattern) : List Pattern → List Pattern
    | [] => []
    | pattern :: patterns =>
        openContexts declaration context observe pattern ::
          openContextsList declaration context observe patterns
end

/-- Push the context into the quoted code. -/
def erase (declaration : ReflectivePresentationDecl) (context : String) : Pattern → Pattern :=
  openContexts declaration context id

/-- Read the context as the name of the eliminated binder. -/
def atomize (declaration : ReflectivePresentationDecl) (context : String) (name : Pattern) :
    Pattern → Pattern :=
  openContexts declaration context fun _ => name

theorem openContextsList_eq_map (declaration : ReflectivePresentationDecl) (context : String)
    (observe : Pattern → Pattern) (patterns : List Pattern) :
    openContextsList declaration context observe patterns =
      patterns.map (openContexts declaration context observe) := by
  induction patterns with
  | nil => rfl
  | cons pattern patterns ih => simp [openContextsList, ih]

mutual
  /-- `label` is used by no application in the term. -/
  def labelFresh (label : String) : Pattern → Bool
    | .bvar _ => true
    | .fvar _ => true
    | .apply constructor arguments => decide (constructor ≠ label) && labelFreshList label arguments
    | .lambda _ body => labelFresh label body
    | .multiLambda _ _ body => labelFresh label body
    | .subst body value => labelFresh label body && labelFresh label value
    | .collection _ elements _ => labelFreshList label elements

  /-- List recursion for `labelFresh`. -/
  def labelFreshList (label : String) : List Pattern → Bool
    | [] => true
    | pattern :: patterns => labelFresh label pattern && labelFreshList label patterns
end

section Observation

variable {declaration : ReflectivePresentationDecl} {context : String}

theorem labelFreshList_iff (patterns : List Pattern) :
    labelFreshList context patterns = true ↔ ∀ pattern ∈ patterns, labelFresh context pattern = true := by
  induction patterns with
  | nil => simp [labelFreshList]
  | cons pattern patterns ih => simp [labelFreshList, ih]

theorem labelFresh_apply {constructor : String} {arguments : List Pattern} :
    labelFresh context (.apply constructor arguments) = true ↔
      constructor ≠ context ∧ ∀ argument ∈ arguments, labelFresh context argument = true := by
  simp [labelFresh, labelFreshList_iff]

theorem contextOf?_eq_none_of_labelFresh {pattern : Pattern}
    (fresh : labelFresh context pattern = true) : contextOf? context pattern = none := by
  cases pattern with
  | apply constructor arguments =>
      match arguments, fresh with
      | [], _ => rfl
      | [_], fresh => simp [contextOf?, (labelFresh_apply.mp fresh).1]
      | _ :: _ :: _, _ => rfl
  | _ => rfl

theorem contextOf?_contextual (value : Pattern) :
    contextOf? context (contextual context value) = some value := by
  simp [contextOf?, contextual]

theorem contextOf?_apply_of_ne {constructor : String} (other : constructor ≠ context)
    (arguments : List Pattern) : contextOf? context (.apply constructor arguments) = none := by
  match arguments with
  | [] => rfl
  | [_] => simp [contextOf?, other]
  | _ :: _ :: _ => rfl

/-- Observation fixes a term with no context reference. -/
theorem openContexts_of_labelFresh (observe : Pattern → Pattern) {pattern : Pattern}
    (fresh : labelFresh context pattern = true) :
    openContexts declaration context observe pattern = pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => rfl
  | hfvar name => rfl
  | hlambda binder body ih => simp only [openContexts, ih fresh]
  | hmultiLambda arity binders body ih => simp only [openContexts, ih fresh]
  | hsubst body value ihBody ihValue =>
      simp only [labelFresh, Bool.and_eq_true] at fresh
      simp only [openContexts, ihBody fresh.1, ihValue fresh.2]
  | hcollection kind elements rest ih =>
      have each := (labelFreshList_iff elements).mp fresh
      simp only [openContexts, openContextsList_eq_map]
      rw [(List.map_congr_left fun p m => ih p m (each p m)).trans (List.map_id' _)]
  | happly constructor arguments ih =>
      obtain ⟨other, each⟩ := labelFresh_apply.mp fresh
      match arguments, each, ih with
      | [], _, _ => rfl
      | first :: second :: rest, each, ih =>
          simp only [openContexts, openContextsList_eq_map]
          rw [(List.map_congr_left fun p m => ih p m (each p m)).trans (List.map_id' _)]
      | [payload], each, ih =>
          have payloadFresh := each payload (by simp)
          simp only [openContexts, if_neg other, ih payload (by simp) payloadFresh,
            contextOf?_eq_none_of_labelFresh payloadFresh, ite_self]

theorem labelFresh_liftBVars (cutoff shift : Nat) {pattern : Pattern}
    (fresh : labelFresh context pattern = true) :
    labelFresh context (liftBVars cutoff shift pattern) = true := by
  induction pattern using Pattern.inductionOn generalizing cutoff with
  | hbvar index => simp only [liftBVars]; split <;> rfl
  | hfvar name => rfl
  | hlambda binder body ih => exact ih (cutoff + 1) fresh
  | hmultiLambda arity binders body ih => exact ih (cutoff + arity) fresh
  | hsubst body value ihBody ihValue =>
      simp only [labelFresh, Bool.and_eq_true, liftBVars] at fresh ⊢
      exact ⟨ihBody _ fresh.1, ihValue _ fresh.2⟩
  | hcollection kind elements rest ih =>
      have each := (labelFreshList_iff elements).mp fresh
      simp only [liftBVars, liftBVarsList_eq_map, labelFresh, labelFreshList_iff, List.mem_map]
      rintro _ ⟨original, member, rfl⟩
      exact ih original member cutoff (each original member)
  | happly constructor arguments ih =>
      obtain ⟨other, each⟩ := labelFresh_apply.mp fresh
      simp only [liftBVars, liftBVarsList_eq_map]
      refine labelFresh_apply.mpr ⟨other, ?_⟩
      simp only [List.mem_map]
      rintro _ ⟨original, member, rfl⟩
      exact ih original member cutoff (each original member)

theorem labelFresh_lowering {replacement : Pattern} (fresh : labelFresh context replacement = true)
    (level index : Nat) : labelFresh context (lowering replacement level index) = true := by
  rcases Nat.lt_trichotomy index level with below | rfl | above
  · rw [lowering_of_lt below]; rfl
  · rw [lowering_self]; exact labelFresh_liftBVars 0 _ fresh
  · rw [lowering_of_gt above]; rfl

theorem labelFresh_receive {constructor : String} (other : constructor ≠ context) {name : Pattern}
    (fresh : labelFresh context name = true) :
    labelFresh context (receive declaration constructor name) = true := by
  rcases receive_cases (declaration := declaration) constructor name with plain | ⟨process, rfl, ran⟩
  · rw [plain]; exact labelFresh_apply.mpr ⟨other, by simpa using fresh⟩
  · rw [ran]; exact (labelFresh_apply.mp fresh).2 process (by simp)

theorem labelFresh_of_mem_parallelLeaves {pattern member : Pattern}
    (fresh : labelFresh context pattern = true)
    (membership : member ∈ parallelLeaves declaration pattern) :
    labelFresh context member = true := by
  induction pattern using Pattern.inductionOn with
  | hcollection kind elements rest ih =>
      cases rest with
      | some rest =>
          simp only [parallelLeaves, List.mem_singleton] at membership; subst membership; exact fresh
      | none =>
          by_cases parallel : kind = declaration.parallelCollection
          · simp only [parallelLeaves, parallel, if_true, parallelLeavesList_eq_flatMap,
              List.mem_flatMap] at membership
            obtain ⟨element, elementMember, membership⟩ := membership
            exact ih element elementMember
              ((labelFreshList_iff elements).mp fresh element elementMember) membership
          · simp only [parallelLeaves, parallel, if_false, List.mem_singleton] at membership
            subst membership; exact fresh
  | happly constructor arguments ih =>
      cases arguments with
      | nil =>
          by_cases unit : constructor = declaration.parallelUnitConstructor
          · simp [parallelLeaves, unit] at membership
          · simp only [parallelLeaves, unit, if_false, List.mem_singleton] at membership
            subst membership; exact fresh
      | cons argument arguments =>
          simp only [parallelLeaves, List.mem_singleton] at membership; subst membership; exact fresh
  | hbvar index => simp only [parallelLeaves, List.mem_singleton] at membership; subst membership; exact fresh
  | hfvar name => simp only [parallelLeaves, List.mem_singleton] at membership; subst membership; exact fresh
  | hlambda binder body ih =>
      simp only [parallelLeaves, List.mem_singleton] at membership; subst membership; exact fresh
  | hmultiLambda arity binders body ih =>
      simp only [parallelLeaves, List.mem_singleton] at membership; subst membership; exact fresh
  | hsubst body replacement ihBody ihReplacement =>
      simp only [parallelLeaves, List.mem_singleton] at membership; subst membership; exact fresh

/-- Resolution never introduces a label. -/
theorem labelFresh_resolveQuotes {pattern : Pattern} (fresh : labelFresh context pattern = true) :
    labelFresh context (resolveQuotes declaration pattern) = true := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => rfl
  | hfvar name => rfl
  | hlambda binder body ih => exact ih fresh
  | hmultiLambda arity binders body ih => exact ih fresh
  | hsubst body value ihBody ihValue =>
      simp only [labelFresh, Bool.and_eq_true, resolveQuotes] at fresh ⊢
      exact ⟨ihBody fresh.1, ihValue fresh.2⟩
  | hcollection kind elements rest ih =>
      have each := (labelFreshList_iff elements).mp fresh
      show labelFreshList context (resolveQuotesList declaration elements) = true
      rw [resolveQuotesList_eq_map, labelFreshList_iff]
      intro p member
      obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
      exact ih original originalMember (each original originalMember)
  | happly constructor arguments ih =>
      obtain ⟨other, each⟩ := labelFresh_apply.mp fresh
      have mappedFresh : ∀ p ∈ arguments.map (resolveQuotes declaration),
          labelFresh context p = true := by
        intro p member
        obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
        exact ih original originalMember (each original originalMember)
      simp only [resolveQuotes, resolveQuotesList_eq_map]
      generalize arguments.map (resolveQuotes declaration) = resolved at mappedFresh
      match resolved, mappedFresh with
      | [], _ => exact labelFresh_apply.mpr ⟨other, by simp⟩
      | first :: second :: rest, mappedFresh =>
          exact labelFresh_apply.mpr ⟨other, mappedFresh⟩
      | [payload], mappedFresh =>
          have payloadFresh := mappedFresh payload (by simp)
          have plain : labelFresh context (.apply constructor [payload]) = true :=
            labelFresh_apply.mpr ⟨other, by simpa using payloadFresh⟩
          simp only [finishResolveApply]
          split
          · split
            · rename_i name exposed
              have dropFresh := labelFresh_of_mem_parallelLeaves payloadFresh
                (by rw [exposedDrop?_eq_some_iff.mp exposed]; exact List.mem_singleton_self _)
              exact (labelFresh_apply.mp dropFresh).2 name (by simp)
            · exact plain
          · exact plain

/-- How a pair of index actions of the core corresponds, under an observation,
to a pair of actions of a view. -/
structure Corresponds (declaration : ReflectivePresentationDecl) (context : String)
    (observe : Pattern → Pattern) (core view : Nat → Nat → Pattern) : Prop where
  atIndex : ∀ level index,
    openContexts declaration context observe (core level index) = view level index
  indexNotContext : ∀ level index, index ≠ level → contextOf? context (core level index) = none
  atReceive : declaration.dropConstructor ≠ declaration.quoteConstructor → ∀ level,
    openContexts declaration context observe
        (receive declaration declaration.dropConstructor (core level level)) =
      receive declaration declaration.dropConstructor (view level level)
  receivedNotContext : ∀ level,
    contextOf? context (receive declaration declaration.dropConstructor (core level level)) = none

/-- The core is never a context reference at a position that does not receive
the eliminated binder. -/
theorem contextOf?_substituteViewed {insideQuote atIndex : Nat → Nat → Pattern}
    {observe : Pattern → Pattern} {view : Nat → Nat → Pattern}
    (outside : Corresponds declaration context observe atIndex view) {depth : Nat}
    {pattern : Pattern} (fresh : labelFresh context pattern = true)
    (miss : ∀ index, pattern = .bvar index → index ≠ depth) :
    contextOf? context (substituteViewed declaration insideQuote atIndex depth pattern) = none := by
  cases pattern with
  | bvar index => exact outside.indexNotContext depth index (miss index rfl)
  | apply constructor arguments =>
      obtain ⟨other, _⟩ := labelFresh_apply.mp fresh
      match arguments with
      | [] => rfl
      | _ :: _ :: _ => rfl
      | [payload] =>
          simp only [substituteViewed]
          by_cases isQuote : constructor = declaration.quoteConstructor
          · rw [if_pos isQuote]; exact contextOf?_apply_of_ne other _
          · rw [if_neg isQuote]
            by_cases isDrop : constructor = declaration.dropConstructor
            · subst isDrop
              rw [if_pos rfl]
              split
              · exact outside.receivedNotContext depth
              · exact contextOf?_apply_of_ne other _
            · rw [if_neg isDrop]; exact contextOf?_apply_of_ne other _
  | _ => rfl

/-- **Observing the core is the view**, for any pair of corresponding actions
inside and outside quotations, on every body without context references. -/
theorem openContexts_substituteViewed {observe : Pattern → Pattern}
    {insideCore insideView : Nat → Nat → Pattern}
    (notDrop : context ≠ declaration.dropConstructor)
    (inside : Corresponds declaration context observe insideCore insideView) {pattern : Pattern}
    (fresh : labelFresh context pattern = true) :
    ∀ {core view : Nat → Nat → Pattern}, Corresponds declaration context observe core view →
      ∀ depth, openContexts declaration context observe
          (substituteViewed declaration insideCore core depth pattern) =
        substituteViewed declaration insideView view depth pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro core view outside depth; exact outside.atIndex depth index
  | hfvar name => intro core view outside depth; rfl
  | hlambda binder body ih =>
      intro core view outside depth
      simp only [substituteViewed, openContexts, ih fresh outside]
  | hmultiLambda arity binders body ih =>
      intro core view outside depth
      simp only [substituteViewed, openContexts, ih fresh outside]
  | hsubst body value ihBody ihValue =>
      intro core view outside depth
      simp only [labelFresh, Bool.and_eq_true] at fresh
      simp only [substituteViewed, openContexts, ihBody fresh.1 outside, ihValue fresh.2 outside]
  | hcollection kind elements rest ih =>
      intro core view outside depth
      have each := (labelFreshList_iff elements).mp fresh
      simp only [substituteViewed, openContexts, substituteViewedList_eq_map,
        openContextsList_eq_map, List.map_map, Function.comp_def]
      rw [List.map_congr_left fun p m => ih p m (each p m) outside depth]
  | happly constructor arguments ih =>
      intro core view outside depth
      obtain ⟨other, each⟩ := labelFresh_apply.mp fresh
      match arguments, each, ih with
      | [], _, _ => rfl
      | first :: second :: rest, each, ih =>
          have atFirst := ih first (by simp) (each first (by simp)) outside depth
          have atSecond := ih second (by simp) (each second (by simp)) outside depth
          have atRest : rest.map (fun p => openContexts declaration context observe
                (substituteViewed declaration insideCore core depth p)) =
              rest.map (substituteViewed declaration insideView view depth) :=
            List.map_congr_left fun p m =>
              ih p (by simp [m]) (each p (by simp [m])) outside depth
          simp only [substituteViewed, substituteViewedList_eq_map, List.map_cons, openContexts,
            openContextsList_eq_map, List.map_map, Function.comp_def, atFirst, atSecond, atRest]
      | [payload], each, ih =>
          have payloadFresh := each payload (by simp)
          by_cases isQuote : constructor = declaration.quoteConstructor
          · subst isQuote
            simp only [substituteViewed, openContexts, if_true,
              ih payload (by simp) payloadFresh inside depth]
          · by_cases isDrop : constructor = declaration.dropConstructor
            · subst isDrop
              have dropNotQuote : declaration.dropConstructor ≠ declaration.quoteConstructor := isQuote
              simp only [substituteViewed, if_neg isQuote, if_true]
              split
              · exact outside.atReceive dropNotQuote depth
              · rename_i miss
                have notContext : contextOf? context
                    (substituteViewed declaration insideCore core depth payload) = none :=
                  contextOf?_substituteViewed outside payloadFresh
                    (fun index same => by
                      subst same
                      simpa [matchesBinder_bvar] using miss)
                simp only [openContexts, if_neg isQuote, if_neg (Ne.symm notDrop), if_true,
                  notContext, ih payload (by simp) payloadFresh outside depth]
            · simp only [substituteViewed, openContexts, if_neg isQuote, if_neg isDrop,
                if_neg other, ih payload (by simp) payloadFresh outside depth]

/-- Outside quotations every view eliminates the binder alike. -/
theorem corresponds_lowering (observe : Pattern → Pattern) {replacement : Pattern}
    (notDrop : context ≠ declaration.dropConstructor)
    (fresh : labelFresh context replacement = true) :
    Corresponds declaration context observe (lowering replacement) (lowering replacement) where
  atIndex level index := openContexts_of_labelFresh observe (labelFresh_lowering fresh level index)
  indexNotContext level index _ := contextOf?_eq_none_of_labelFresh (labelFresh_lowering fresh level index)
  atReceive _ level := openContexts_of_labelFresh observe
    (labelFresh_receive (Ne.symm notDrop) (labelFresh_lowering fresh level level))
  receivedNotContext level := contextOf?_eq_none_of_labelFresh
    (labelFresh_receive (Ne.symm notDrop) (labelFresh_lowering fresh level level))

theorem liftBVars_contextual (cutoff shift : Nat) (value : Pattern) :
    liftBVars cutoff shift (contextual context value) =
      contextual context (liftBVars cutoff shift value) := by
  simp [contextual, liftBVars]

theorem openContexts_contextual (observe : Pattern → Pattern)
    (notQuote : context ≠ declaration.quoteConstructor) (value : Pattern) :
    openContexts declaration context observe (contextual context value) = observe value := by
  simp [contextual, openContexts, notQuote]

theorem receive_contextual (constructor : String) (notQuote : context ≠ declaration.quoteConstructor)
    (value : Pattern) :
    receive declaration constructor (contextual context value) =
      .apply constructor [contextual context value] := by
  simp [contextual, receive, notQuote]

/-- A drop of a context reference receives the observed value. -/
theorem openContexts_drop_contextual (observe : Pattern → Pattern)
    (dropNotQuote : declaration.dropConstructor ≠ declaration.quoteConstructor)
    (notDrop : context ≠ declaration.dropConstructor) (value : Pattern) :
    openContexts declaration context observe
        (.apply declaration.dropConstructor [contextual context value]) =
      receive declaration declaration.dropConstructor (observe value) := by
  simp only [openContexts, if_neg dropNotQuote, if_neg (Ne.symm notDrop), if_true,
    contextOf?_contextual]

/-- Inside quotations the core keeps the value as context, and observing that
context is substituting its observation. -/
theorem corresponds_contextual (observe : Pattern → Pattern) (replacement : Pattern)
    (notQuote : context ≠ declaration.quoteConstructor) (notDrop : context ≠ declaration.dropConstructor)
    (commutes : ∀ level, observe (liftBVars 0 level replacement) =
      liftBVars 0 level (observe replacement)) :
    Corresponds declaration context observe (lowering (contextual context replacement))
      (lowering (observe replacement)) where
  atIndex level index := by
    rcases Nat.lt_trichotomy index level with below | rfl | above
    · rw [lowering_of_lt below, lowering_of_lt below]; rfl
    · rw [lowering_self, lowering_self, ← commutes, liftBVars_contextual,
        openContexts_contextual observe notQuote]
    · rw [lowering_of_gt above, lowering_of_gt above]; rfl
  indexNotContext level index other := by
    rcases Nat.lt_or_gt_of_ne other with below | above
    · rw [lowering_of_lt below]; rfl
    · rw [lowering_of_gt above]; rfl
  atReceive dropNotQuote level := by
    rw [lowering_self, lowering_self, ← commutes, liftBVars_contextual,
      receive_contextual _ notQuote, openContexts_drop_contextual observe dropNotQuote notDrop]
  receivedNotContext level := by
    rw [lowering_self, liftBVars_contextual, receive_contextual _ notQuote]
    exact contextOf?_apply_of_ne (Ne.symm notDrop) _

/-- **Observing the closure.** With a context constructor that is fresh for the
presentation, the body and the replacement, opening the contexts of the closure
view with `observe` is the view that enters quotations with `observe` of the
replacement. -/
theorem openContexts_closureView (observe : Pattern → Pattern) (depth : Nat)
    {replacement body : Pattern}
    (notQuote : context ≠ declaration.quoteConstructor) (notDrop : context ≠ declaration.dropConstructor)
    (bodyFresh : labelFresh context body = true) (replacementFresh : labelFresh context replacement = true)
    (commutes : ∀ level, observe (liftBVars 0 level replacement) =
      liftBVars 0 level (observe replacement)) :
    openContexts declaration context observe (closureView declaration context depth replacement body) =
      substituteViewed declaration (lowering (observe replacement)) (lowering replacement) depth
        (resolveQuotes declaration body) :=
  openContexts_substituteViewed notDrop
    (corresponds_contextual observe replacement notQuote notDrop commutes)
    (labelFresh_resolveQuotes bodyFresh)
    (corresponds_lowering observe notDrop replacementFresh) depth

/-- **Apply is erasure of the closure** (`apply = erase ∘ closure`). -/
theorem erase_closureView (depth : Nat) {replacement body : Pattern}
    (notQuote : context ≠ declaration.quoteConstructor) (notDrop : context ≠ declaration.dropConstructor)
    (bodyFresh : labelFresh context body = true) (replacementFresh : labelFresh context replacement = true) :
    erase declaration context (closureView declaration context depth replacement body) =
      applyView declaration depth replacement body :=
  openContexts_closureView id depth notQuote notDrop bodyFresh replacementFresh fun _ => rfl

/-- **Freeze is atomization of the closure** (`freeze = atomize ∘ closure`), for
a closed name: atomization does not see the binders above a context reference,
so the name must not need lifting. -/
theorem atomize_closureView (depth : Nat) {name replacement body : Pattern}
    (nameClosed : name.isWellScopedAt 0 = true)
    (notQuote : context ≠ declaration.quoteConstructor) (notDrop : context ≠ declaration.dropConstructor)
    (bodyFresh : labelFresh context body = true) (replacementFresh : labelFresh context replacement = true) :
    atomize declaration context name (closureView declaration context depth replacement body) =
      freezeView declaration depth replacement name body :=
  openContexts_closureView (fun _ => name) depth notQuote notDrop bodyFresh replacementFresh
    fun _ => (liftBVars_eq_self_of_isWellScopedAt nameClosed).symm

end Observation

/-! ## A fresh context constructor always exists -/

mutual
  /-- The application labels of a term. -/
  def labels : Pattern → List String
    | .bvar _ => []
    | .fvar _ => []
    | .apply constructor arguments => constructor :: labelsList arguments
    | .lambda _ body => labels body
    | .multiLambda _ _ body => labels body
    | .subst body value => labels body ++ labels value
    | .collection _ elements _ => labelsList elements

  /-- List recursion for `labels`. -/
  def labelsList : List Pattern → List String
    | [] => []
    | pattern :: patterns => labels pattern ++ labelsList patterns
end

theorem labelsList_eq_flatMap (patterns : List Pattern) :
    labelsList patterns = patterns.flatMap labels := by
  induction patterns with
  | nil => rfl
  | cons pattern patterns ih => simp [labelsList, ih]

theorem labelFresh_of_not_mem {context : String} {pattern : Pattern}
    (absent : context ∉ labels pattern) : labelFresh context pattern = true := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => rfl
  | hfvar name => rfl
  | hlambda binder body ih => exact ih absent
  | hmultiLambda arity binders body ih => exact ih absent
  | hsubst body value ihBody ihValue =>
      simp only [labels, List.mem_append, not_or] at absent
      simp only [labelFresh, ihBody absent.1, ihValue absent.2, Bool.and_self]
  | hcollection kind elements rest ih =>
      simp only [labels, labelsList_eq_flatMap, List.mem_flatMap, not_exists, not_and] at absent
      exact (labelFreshList_iff elements).mpr fun p member => ih p member (absent p member)
  | happly constructor arguments ih =>
      simp only [labels, labelsList_eq_flatMap, List.mem_cons, List.mem_flatMap, not_or,
        not_exists, not_and] at absent
      exact labelFresh_apply.mpr ⟨Ne.symm absent.1, fun p member => ih p member (absent.2 p member)⟩

/-- For every presentation, body and replacement there is a context
constructor distinct from quote and drop that neither uses. -/
theorem exists_freshContext (declaration : ReflectivePresentationDecl) (body replacement : Pattern) :
    ∃ context, context ≠ declaration.quoteConstructor ∧ context ≠ declaration.dropConstructor ∧
      labelFresh context body = true ∧ labelFresh context replacement = true := by
  obtain ⟨context, absent⟩ := Infinite.exists_notMem_finset
    (declaration.quoteConstructor :: declaration.dropConstructor ::
      (labels body ++ labels replacement)).toFinset
  simp only [List.mem_toFinset, List.mem_cons, List.mem_append, not_or] at absent
  exact ⟨context, absent.1, absent.2.1, labelFresh_of_not_mem absent.2.2.1,
    labelFresh_of_not_mem absent.2.2.2⟩

/-- **The closure is the initial view**: for every body, depth and replacement
there is a context constructor for which erasing the closure is the apply view
and atomizing it is the freeze view, for every closed name. -/
theorem exists_closure_factorization (declaration : ReflectivePresentationDecl) (depth : Nat)
    (replacement body : Pattern) :
    ∃ context,
      erase declaration context (closureView declaration context depth replacement body) =
          applyView declaration depth replacement body ∧
        ∀ name : Pattern, name.isWellScopedAt 0 = true → atomize declaration context name
            (closureView declaration context depth replacement body) =
          freezeView declaration depth replacement name body := by
  obtain ⟨context, notQuote, notDrop, bodyFresh, replacementFresh⟩ :=
    exists_freshContext declaration body replacement
  exact ⟨context, erase_closureView depth notQuote notDrop bodyFresh replacementFresh,
    fun _ nameClosed =>
      atomize_closureView depth nameClosed notQuote notDrop bodyFresh replacementFresh⟩

/-! ## Sealed bodies: where the views coincide -/

/-- The bound index a binder observation selects, seen through drops. -/
def headIndex? : BinderHead → Option Nat
  | .index level => some level
  | .drop name => headIndex? name
  | _ => none

theorem headIndex?_join {first second : BinderHead} {level : Nat}
    (found : headIndex? (BinderHead.join first second) = some level) :
    headIndex? first = some level ∨ headIndex? second = some level := by
  cases first <;> cases second <;> simp_all [BinderHead.join, headIndex?]

theorem headIndex?_fold {heads : List BinderHead} {level : Nat}
    (found : headIndex? (heads.foldr BinderHead.join .unit) = some level) :
    ∃ head ∈ heads, headIndex? head = some level := by
  induction heads with
  | nil => simp [headIndex?] at found
  | cons head heads ih =>
      rcases headIndex?_join found with here | there
      · exact ⟨head, by simp, here⟩
      · obtain ⟨other, member, found⟩ := ih there
        exact ⟨other, by simp [member], found⟩

theorem headIndex?_rigid {declaration : ReflectivePresentationDecl} {constructor : String}
    {heads : List BinderHead} {level : Nat}
    (found : headIndex? (BinderHead.rigid declaration constructor heads) = some level) :
    ∃ head, heads = [head] ∧ headIndex? head = some level := by
  match heads with
  | [] => simp only [BinderHead.rigid] at found; split at found <;> simp [headIndex?] at found
  | [head] =>
      simp only [BinderHead.rigid] at found
      split at found
      · exact ⟨head, rfl, found⟩
      · simp [headIndex?] at found
  | _ :: _ :: _ => simp [BinderHead.rigid, headIndex?] at found

theorem headIndex?_apply {declaration : ReflectivePresentationDecl} {constructor : String}
    {heads : List BinderHead} {level : Nat}
    (found : headIndex? (BinderHead.apply declaration constructor heads) = some level) :
    ∃ head, heads = [head] ∧ headIndex? head = some level := by
  unfold BinderHead.apply at found
  split at found
  · rename_i name
    split at found
    · exact ⟨.drop name, rfl, found⟩
    · exact headIndex?_rigid found
  · exact headIndex?_rigid found

/-- A term recognized as a binder mentions it. -/
theorem mentions_of_headIndex? {declaration : ReflectivePresentationDecl} {level : Nat}
    {pattern : Pattern} (found : headIndex? (BinderHead.ofPattern declaration pattern) = some level) :
    mentions level pattern = true := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      simp only [BinderHead.ofPattern, headIndex?, Option.some.injEq] at found
      simp [mentions, found]
  | happly constructor arguments ih =>
      simp only [BinderHead.ofPattern, BinderHead.ofList_eq_map] at found
      obtain ⟨head, heads, headFound⟩ := headIndex?_apply found
      obtain ⟨argument, rfl, rfl⟩ := List.map_eq_singleton_iff.mp heads
      simp [mentions, mentionsList, ih argument (by simp) headFound]
  | hcollection kind elements rest ih =>
      cases rest with
      | some rest => simp [BinderHead.ofPattern, headIndex?] at found
      | none =>
          simp only [BinderHead.ofPattern, BinderHead.ofList_eq_map] at found
          split at found
          · obtain ⟨head, member, headFound⟩ := headIndex?_fold found
            obtain ⟨element, elementMember, rfl⟩ := List.mem_map.mp member
            have elementMentions := ih element elementMember headFound
            simp only [mentions]
            by_contra absent
            rw [Bool.not_eq_true, mentionsList_eq_false_iff] at absent
            rw [absent element elementMember] at elementMentions
            cases elementMentions
          · simp [headIndex?] at found
  | hfvar name => simp [BinderHead.ofPattern, headIndex?] at found
  | hlambda binder body ih => simp [BinderHead.ofPattern, headIndex?] at found
  | hmultiLambda arity binders body ih => simp [BinderHead.ofPattern, headIndex?] at found
  | hsubst body value ihBody ihValue => simp [BinderHead.ofPattern, headIndex?] at found

theorem mentions_of_matchesBinder {declaration : ReflectivePresentationDecl} {level : Nat}
    {pattern : Pattern} (matched : matchesBinder declaration level pattern = true) :
    mentions level pattern = true := by
  simp only [matchesBinder, decide_eq_true_eq] at matched
  exact mentions_of_headIndex? (declaration := declaration) (by rw [matched]; rfl)

mutual
  /-- Every genuine quotation passes `test` at the number of binders between
  the eliminated binder and the quotation. -/
  def everyQuotation (declaration : ReflectivePresentationDecl) (test : Nat → Pattern → Bool) :
      Nat → Pattern → Bool
    | _, .bvar _ => true
    | _, .fvar _ => true
    | _, .apply _ [] => true
    | level, .apply constructor [payload] =>
        if constructor = declaration.quoteConstructor then test level payload
        else everyQuotation declaration test level payload
    | level, .apply _ (first :: second :: rest) =>
        everyQuotationList declaration test level (first :: second :: rest)
    | level, .lambda _ body => everyQuotation declaration test (level + 1) body
    | level, .multiLambda arity _ body => everyQuotation declaration test (level + arity) body
    | level, .subst body value =>
        everyQuotation declaration test (level + 1) body && everyQuotation declaration test level value
    | level, .collection _ elements _ => everyQuotationList declaration test level elements

  /-- List recursion for `everyQuotation`. -/
  def everyQuotationList (declaration : ReflectivePresentationDecl) (test : Nat → Pattern → Bool) :
      Nat → List Pattern → Bool
    | _, [] => true
    | level, pattern :: patterns =>
        everyQuotation declaration test level pattern && everyQuotationList declaration test level patterns
end

theorem everyQuotationList_iff (declaration : ReflectivePresentationDecl) (test : Nat → Pattern → Bool)
    (level : Nat) (patterns : List Pattern) :
    everyQuotationList declaration test level patterns = true ↔
      ∀ pattern ∈ patterns, everyQuotation declaration test level pattern = true := by
  induction patterns with
  | nil => simp [everyQuotationList]
  | cons pattern patterns ih => simp [everyQuotationList, ih]

/-- **The admission restriction**: no genuine quotation mentions the eliminated
binder. -/
def Sealed (declaration : ReflectivePresentationDecl) (depth : Nat) (body : Pattern) : Prop :=
  everyQuotation declaration (fun level payload => !mentions level payload) depth
    (resolveQuotes declaration body) = true

instance (declaration : ReflectivePresentationDecl) (depth : Nat) (body : Pattern) :
    Decidable (Sealed declaration depth body) :=
  inferInstanceAs (Decidable (_ = true))

/-! ## Sealed admission respects the declared equations

The equations never move an index: the quote-drop equation removes two
constructors, and normalizing a parallel bag permutes, flattens and drops
units. So `mentions` reads only the canonical form. On a resolved term
canonicalization applies no quote-drop equation at a quotation: it keeps every
genuine quotation and canonicalizes its payload. After resolution, a quotation
test that reads its payload modulo the equations therefore depends only on the
canonical form of the body. -/

section Invariance

variable {declaration : ReflectivePresentationDecl}

private theorem all_congr_of_mem {α : Type} {patterns : List α} {first second : α → Bool}
    (same : ∀ pattern ∈ patterns, first pattern = second pattern) :
    patterns.all first = patterns.all second := by
  induction patterns with
  | nil => rfl
  | cons pattern patterns ih =>
      simp only [List.all_cons, same pattern (by simp), ih fun other member => same other (by simp [member])]

theorem everyQuotationList_eq_all (test : Nat → Pattern → Bool) (level : Nat)
    (patterns : List Pattern) :
    everyQuotationList declaration test level patterns =
      patterns.all (everyQuotation declaration test level) := by
  induction patterns with
  | nil => rfl
  | cons pattern patterns ih => simp [everyQuotationList, ih]

/-- On a resolved term, a quotation test that reads its payload modulo the
equations gives the same verdict on the canonical form. -/
theorem everyQuotation_canonicalize {test : Nat → Pattern → Bool}
    (invariant : ∀ level payload, test level (canonicalize declaration payload) = test level payload)
    {pattern : Pattern} (resolved : QuotesResolved declaration pattern) :
    ∀ level, everyQuotation declaration test level (canonicalize declaration pattern) =
      everyQuotation declaration test level pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro _; rfl
  | hfvar name => intro _; rfl
  | hlambda binder body ih => intro level; exact ih resolved (level + 1)
  | hmultiLambda arity binders body ih => intro level; exact ih resolved (level + arity)
  | hsubst body value ihBody ihValue =>
      intro level
      simp only [canonicalize, everyQuotation, ihBody resolved.1, ihValue resolved.2]
  | happly constructor arguments ih =>
      intro level
      match arguments, resolved, ih with
      | [], _, _ => simp [canonicalize, canonicalizeList, finish_nil, everyQuotation]
      | [payload], resolved, ih =>
          rw [canonicalize_unary_of_resolved resolved]
          by_cases isQuote : constructor = declaration.quoteConstructor
          · simp only [everyQuotation, isQuote, if_true, invariant]
          · simp only [everyQuotation, isQuote, if_false, ih payload (by simp) resolved.1.1 level]
      | first :: second :: rest, resolved, ih =>
          have each := (quotesResolvedList_iff _).mp resolved.1
          have mapped : ((first :: second :: rest).map (canonicalize declaration)).all
                (everyQuotation declaration test level) =
              (first :: second :: rest).all (everyQuotation declaration test level) := by
            rw [List.all_map]
            exact all_congr_of_mem fun pattern member => ih pattern member (each pattern member) level
          simp only [List.map_cons] at mapped
          simp only [canonicalize, canonicalizeList_eq_map, List.map_cons, finish_long, everyQuotation,
            everyQuotationList_eq_all, mapped]
  | hcollection kind elements rest ih =>
      intro level
      have each := (quotesResolvedList_iff elements).mp resolved
      have mapped : (elements.map (canonicalize declaration)).all (everyQuotation declaration test level) =
          elements.all (everyQuotation declaration test level) := by
        rw [List.all_map]
        exact all_congr_of_mem fun pattern member => ih pattern member (each pattern member) level
      cases rest with
      | some rest =>
          simp only [canonicalize, canonicalizeList_eq_map, everyQuotation, everyQuotationList_eq_all,
            mapped]
      | none =>
          by_cases isParallel : kind = declaration.parallelCollection
          · subst isParallel
            rw [canonicalize_parallel_eq, collapse_normalize_all (everyQuotation declaration test level)
              rfl (fun elements => everyQuotationList_eq_all test level elements), mapped]
            exact (everyQuotationList_eq_all test level elements).symm
          · have notParallel : (kind == declaration.parallelCollection) = false := by
              simpa using isParallel
            simp only [canonicalize, notParallel, Bool.false_eq_true, if_false,
              canonicalizeList_eq_map, everyQuotation, everyQuotationList_eq_all, mapped]

/-- After resolution, a quotation test that reads its payload modulo the
equations depends only on the canonical form of the body. -/
theorem everyQuotation_resolveQuotes {test : Nat → Pattern → Bool}
    (invariant : ∀ level payload, test level (canonicalize declaration payload) = test level payload)
    (level : Nat) (body : Pattern) :
    everyQuotation declaration test level (resolveQuotes declaration body) =
      everyQuotation declaration test level (canonicalize declaration body) := by
  rw [← everyQuotation_canonicalize invariant (resolveQuotes_resolved body), canonicalize_resolveQuotes]

/-- A body is sealed exactly when no quotation of its canonical form mentions
the eliminated binder. -/
theorem sealed_iff_canonicalize {depth : Nat} {body : Pattern} :
    Sealed declaration depth body ↔
      everyQuotation declaration (fun level payload => !mentions level payload) depth
        (canonicalize declaration body) = true := by
  unfold Sealed
  rw [everyQuotation_resolveQuotes (fun level payload => by rw [mentions_canonicalize])]

/-- **Sealed admission respects the declared equations.** -/
theorem sealed_respects (depth : Nat) {left right : Pattern}
    (same : canonicalEquivalent declaration left right = true) :
    Sealed declaration depth left ↔ Sealed declaration depth right := by
  rw [sealed_iff_canonicalize, sealed_iff_canonicalize, canonicalEquivalent_eq_true_iff.mp same]

end Invariance

/-! ## Closed quotations seal every binder

Under a closed scope a presentation admits only closed quoted code
(`ReflectiveQuoteAdmission.QuotesClosed`). Such a body is sealed for every
eliminated binder. -/

section ClosedSeals

variable {declaration : ReflectivePresentationDecl}

/-- Closed code mentions no binder inside a genuine quotation. -/
theorem everyQuotation_of_closedCode {test : Nat → Pattern → Bool}
    (closedPasses : ∀ level payload, payload.isWellScopedAt 0 = true → test level payload = true)
    {pattern : Pattern} : closedCode declaration pattern = true → ∀ level,
      everyQuotation declaration test level pattern = true := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro _ _; rfl
  | hfvar name => intro _ _; rfl
  | hlambda binder body ih => intro closed level; exact ih closed (level + 1)
  | hmultiLambda arity binders body ih => intro closed level; exact ih closed (level + arity)
  | hsubst body value ihBody ihValue =>
      intro closed level
      simp only [closedCode, Bool.and_eq_true] at closed
      simp only [everyQuotation, ihBody closed.1 (level + 1), ihValue closed.2 level, Bool.and_self]
  | hcollection kind elements rest ih =>
      intro closed level
      simp only [closedCode, closedCodeList_eq_all, List.all_eq_true] at closed
      simp only [everyQuotation, everyQuotationList_eq_all, List.all_eq_true]
      exact fun element member => ih element member (closed element member) level
  | happly constructor arguments ih =>
      intro closed level
      match arguments, closed, ih with
      | [], _, _ => rfl
      | [payload], closed, ih =>
          by_cases isQuote : constructor = declaration.quoteConstructor
          · simp only [closedCode, isQuote, if_true, Bool.and_eq_true] at closed
            simp only [everyQuotation, isQuote, if_true]
            exact closedPasses level payload closed.1
          · simp only [closedCode, isQuote, if_false] at closed
            simp only [everyQuotation, isQuote, if_false]
            exact ih payload (by simp) closed level
      | first :: second :: rest, closed, ih =>
          simp only [closedCode, closedCodeList_eq_all, List.all_eq_true] at closed
          simp only [everyQuotation, everyQuotationList_eq_all, List.all_eq_true]
          exact fun element member => ih element member (closed element member) level

/-- **Admission under a closed scope seals every binder.** -/
theorem sealed_of_quotesClosed {body : Pattern} (admitted : QuotesClosed declaration body) (depth : Nat) :
    Sealed declaration depth body := by
  unfold Sealed
  apply everyQuotation_of_closedCode _ admitted depth
  intro level payload closed
  have never := (isWellScopedAt_iff_not_mentions payload 0).mp closed level (Nat.zero_le _)
  simp [never]

end ClosedSeals

section Sealed

variable {declaration : ReflectivePresentationDecl}

/-- Inside a quotation that does not mention the eliminated binder, the action
is never consulted at the eliminated level. -/
theorem substituteViewed_inside_congr {first second : Nat → Nat → Pattern}
    (agree : ∀ level index, index ≠ level → first level index = second level index)
    {pattern : Pattern} :
    ∀ {depth}, mentions depth pattern = false →
      substituteViewed declaration first first depth pattern =
        substituteViewed declaration second second depth pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      intro depth absent
      simp only [mentions, beq_eq_false_iff_ne] at absent
      exact agree depth index absent
  | hfvar name => intro depth _; rfl
  | hlambda binder body ih =>
      intro depth absent; simp only [substituteViewed, ih absent]
  | hmultiLambda arity binders body ih =>
      intro depth absent; simp only [substituteViewed, ih absent]
  | hsubst body value ihBody ihValue =>
      intro depth absent
      simp only [mentions, Bool.or_eq_false_iff] at absent
      simp only [substituteViewed, ihBody absent.1, ihValue absent.2]
  | hcollection kind elements rest ih =>
      intro depth absent
      have each := (mentionsList_eq_false_iff _ _).mp absent
      simp only [substituteViewed, substituteViewedList_eq_map]
      rw [List.map_congr_left fun p m => ih p m (each p m)]
  | happly constructor arguments ih =>
      intro depth absent
      have each := (mentionsList_eq_false_iff _ _).mp absent
      match arguments, each, ih with
      | [], _, _ => rfl
      | first :: second :: rest, each, ih =>
          simp only [substituteViewed, substituteViewedList_eq_map]
          rw [List.map_congr_left fun p m => ih p m (each p m)]
      | [payload], each, ih =>
          have payloadAbsent := each payload (by simp)
          have miss : matchesBinder declaration depth payload = false := by
            cases matched : matchesBinder declaration depth payload
            · rfl
            · rw [mentions_of_matchesBinder matched] at payloadAbsent; cases payloadAbsent
          simp only [substituteViewed, miss, Bool.false_eq_true, if_false,
            ih payload (by simp) payloadAbsent]

/-- On a body none of whose genuine quotations mentions the eliminated binder,
the inside action is never consulted at the eliminated level. -/
theorem substituteViewed_congr_of_avoids {first second : Nat → Nat → Pattern}
    (agree : ∀ level index, index ≠ level → first level index = second level index)
    (atIndex : Nat → Nat → Pattern) {pattern : Pattern} :
    ∀ {depth}, everyQuotation declaration (fun level payload => !mentions level payload) depth pattern = true →
      substituteViewed declaration first atIndex depth pattern =
        substituteViewed declaration second atIndex depth pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro depth _; rfl
  | hfvar name => intro depth _; rfl
  | hlambda binder body ih =>
      intro depth avoids; simp only [substituteViewed, ih avoids]
  | hmultiLambda arity binders body ih =>
      intro depth avoids; simp only [substituteViewed, ih avoids]
  | hsubst body value ihBody ihValue =>
      intro depth avoids
      simp only [everyQuotation, Bool.and_eq_true] at avoids
      simp only [substituteViewed, ihBody avoids.1, ihValue avoids.2]
  | hcollection kind elements rest ih =>
      intro depth avoids
      have each := (everyQuotationList_iff _ _ _ _).mp avoids
      simp only [substituteViewed, substituteViewedList_eq_map]
      rw [List.map_congr_left fun p m => ih p m (each p m)]
  | happly constructor arguments ih =>
      intro depth avoids
      match arguments, avoids, ih with
      | [], _, _ => rfl
      | first :: second :: rest, avoids, ih =>
          have each := (everyQuotationList_iff _ _ _ _).mp avoids
          simp only [substituteViewed, substituteViewedList_eq_map]
          rw [List.map_congr_left fun p m => ih p m (each p m)]
      | [payload], avoids, ih =>
          simp only [everyQuotation] at avoids
          by_cases isQuote : constructor = declaration.quoteConstructor
          · simp only [isQuote, if_true, Bool.not_eq_true'] at avoids
            simp only [substituteViewed, isQuote, if_true,
              substituteViewed_inside_congr agree avoids]
          · simp only [isQuote, if_false] at avoids
            simp only [substituteViewed, isQuote, if_false, ih payload (by simp) avoids]

/-- **On sealed bodies the views coincide.** -/
theorem freezeView_eq_applyView_of_sealed {depth : Nat} {replacement body : Pattern}
    (name : Pattern) (sealed : Sealed declaration depth body) :
    freezeView declaration depth replacement name body = applyView declaration depth replacement body :=
  substituteViewed_congr_of_avoids (fun _ _ other => lowering_of_ne _ _ other) _ sealed

theorem closureView_eq_applyView_of_sealed {depth : Nat} {replacement body : Pattern}
    (context : String) (sealed : Sealed declaration depth body) :
    closureView declaration context depth replacement body = applyView declaration depth replacement body :=
  substituteViewed_congr_of_avoids (fun _ _ other => lowering_of_ne _ _ other) _ sealed

/-- Actions that fix every index below the level fix a term with no index at
or above it. -/
theorem substituteViewed_of_isWellScopedAt {insideQuote : Nat → Nat → Pattern}
    (insideFixes : ∀ level index, index < level → insideQuote level index = .bvar index)
    {pattern : Pattern} :
    ∀ {atIndex : Nat → Nat → Pattern}, (∀ level index, index < level → atIndex level index = .bvar index) →
      ∀ {depth}, pattern.isWellScopedAt depth = true →
        substituteViewed declaration insideQuote atIndex depth pattern = pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      intro atIndex fixes depth safe
      exact fixes depth index (by simpa [Pattern.isWellScopedAt] using safe)
  | hfvar name => intro _ _ _ _; rfl
  | hlambda binder body ih =>
      intro atIndex fixes depth safe; simp only [substituteViewed, ih fixes safe]
  | hmultiLambda arity binders body ih =>
      intro atIndex fixes depth safe; simp only [substituteViewed, ih fixes safe]
  | hsubst body value ihBody ihValue =>
      intro atIndex fixes depth safe
      simp only [Pattern.isWellScopedAt, Bool.and_eq_true] at safe
      simp only [substituteViewed, ihBody fixes safe.1, ihValue fixes safe.2]
  | hcollection kind elements rest ih =>
      intro atIndex fixes depth safe
      have each := (isWellScopedListAt_eq_true_iff _ _).mp safe
      simp only [substituteViewed, substituteViewedList_eq_map]
      rw [(List.map_congr_left fun p m => ih p m fixes (each p m)).trans (List.map_id' _)]
  | happly constructor arguments ih =>
      intro atIndex fixes depth safe
      have each := (isWellScopedListAt_eq_true_iff _ _).mp safe
      match arguments, each, ih with
      | [], _, _ => rfl
      | first :: second :: rest, each, ih =>
          simp only [substituteViewed, substituteViewedList_eq_map]
          rw [(List.map_congr_left fun p m => ih p m fixes (each p m)).trans (List.map_id' _)]
      | [payload], each, ih =>
          have payloadSafe := each payload (by simp)
          have miss : matchesBinder declaration depth payload = false := by
            simp only [matchesBinder, decide_eq_false_iff_not,
              ReflectiveCanonical.BinderHead.ofPattern_index_iff]
            intro binder
            have canonicalSafe := canonicalize_scoped declaration payloadSafe
            rw [binder] at canonicalSafe
            simp [Pattern.isWellScopedAt] at canonicalSafe
          simp only [substituteViewed, miss, Bool.false_eq_true, if_false, ite_self,
            ih payload (by simp) insideFixes payloadSafe, ih payload (by simp) fixes payloadSafe]

/-- Where every genuine quotation refers only to binders below it, entering a
quotation changes nothing: the traversal is the opaque one. -/
theorem substituteViewed_eq_substituteResolved {insideQuote : Nat → Nat → Pattern}
    (insideFixes : ∀ level index, index < level → insideQuote level index = .bvar index)
    (atIndex : Nat → Nat → Pattern) {pattern : Pattern} :
    ∀ {depth}, everyQuotation declaration (fun level payload => payload.isWellScopedAt level) depth
        pattern = true →
      substituteViewed declaration insideQuote atIndex depth pattern =
        substituteResolved declaration atIndex depth pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro depth _; rfl
  | hfvar name => intro depth _; rfl
  | hlambda binder body ih =>
      intro depth inScope; simp only [substituteViewed, substituteResolved, ih inScope]
  | hmultiLambda arity binders body ih =>
      intro depth inScope; simp only [substituteViewed, substituteResolved, ih inScope]
  | hsubst body value ihBody ihValue =>
      intro depth inScope
      simp only [everyQuotation, Bool.and_eq_true] at inScope
      simp only [substituteViewed, substituteResolved, ihBody inScope.1, ihValue inScope.2]
  | hcollection kind elements rest ih =>
      intro depth inScope
      have each := (everyQuotationList_iff _ _ _ _).mp inScope
      simp only [substituteViewed, substituteResolved, substituteViewedList_eq_map,
        substituteResolvedList_eq_map]
      rw [List.map_congr_left fun p m => ih p m (each p m)]
  | happly constructor arguments ih =>
      intro depth inScope
      match arguments, inScope, ih with
      | [], _, _ => rfl
      | first :: second :: rest, inScope, ih =>
          have each := (everyQuotationList_iff _ _ _ _).mp inScope
          simp only [substituteViewed, substituteResolved, substituteViewedList_eq_map,
            substituteResolvedList_eq_map]
          rw [List.map_congr_left fun p m => ih p m (each p m)]
      | [payload], inScope, ih =>
          simp only [everyQuotation] at inScope
          by_cases isQuote : constructor = declaration.quoteConstructor
          · simp only [isQuote, if_true] at inScope
            simp only [substituteViewed, substituteResolved, isQuote, if_true,
              substituteViewed_of_isWellScopedAt insideFixes insideFixes inScope]
          · simp only [isQuote, if_false] at inScope
            simp only [substituteViewed, substituteResolved, isQuote, if_false,
              ih payload (by simp) inScope]

theorem isWellScopedAt_of_not_mentions {pattern : Pattern} :
    ∀ {level}, pattern.isWellScopedAt (level + 1) = true → mentions level pattern = false →
      pattern.isWellScopedAt level = true := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      intro level safe absent
      simp only [Pattern.isWellScopedAt, decide_eq_true_eq] at safe ⊢
      simp only [mentions, beq_eq_false_iff_ne] at absent
      omega
  | hfvar name => intro _ _ _; rfl
  | hlambda binder body ih =>
      intro level safe absent
      exact ih (level := level + 1) (by simpa [Pattern.isWellScopedAt, Nat.add_right_comm] using safe)
        absent
  | hmultiLambda arity binders body ih =>
      intro level safe absent
      exact ih (level := level + arity) (by simpa [Pattern.isWellScopedAt, Nat.add_right_comm] using safe)
        absent
  | hsubst body value ihBody ihValue =>
      intro level safe absent
      simp only [Pattern.isWellScopedAt, Bool.and_eq_true] at safe ⊢
      simp only [mentions, Bool.or_eq_false_iff] at absent
      exact ⟨ihBody (level := level + 1) (by simpa [Nat.add_right_comm] using safe.1) absent.1,
        ihValue safe.2 absent.2⟩
  | hcollection kind elements rest ih =>
      intro level safe absent
      have each := (isWellScopedListAt_eq_true_iff _ _).mp safe
      have none := (mentionsList_eq_false_iff _ _).mp absent
      exact (isWellScopedListAt_eq_true_iff _ _).mpr fun p m => ih p m (each p m) (none p m)
  | happly constructor arguments ih =>
      intro level safe absent
      have each := (isWellScopedListAt_eq_true_iff _ _).mp safe
      have none := (mentionsList_eq_false_iff _ _).mp absent
      exact (isWellScopedListAt_eq_true_iff _ _).mpr fun p m => ih p m (each p m) (none p m)

/-- In a body scoped under the eliminated binder, a quotation that does not
mention it refers only to binders below it. -/
theorem everyQuotation_scoped_of_avoids {pattern : Pattern} :
    ∀ {level}, pattern.isWellScopedAt (level + 1) = true →
      everyQuotation declaration (fun level payload => !mentions level payload) level pattern = true →
        everyQuotation declaration (fun level payload => payload.isWellScopedAt level) level pattern = true := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro _ _ _; rfl
  | hfvar name => intro _ _ _; rfl
  | hlambda binder body ih =>
      intro level safe avoids
      exact ih (level := level + 1) (by simpa [Pattern.isWellScopedAt, Nat.add_right_comm] using safe)
        avoids
  | hmultiLambda arity binders body ih =>
      intro level safe avoids
      exact ih (level := level + arity)
        (by simpa [Pattern.isWellScopedAt, Nat.add_right_comm] using safe) avoids
  | hsubst body value ihBody ihValue =>
      intro level safe avoids
      simp only [Pattern.isWellScopedAt, Bool.and_eq_true] at safe
      simp only [everyQuotation, Bool.and_eq_true] at avoids ⊢
      exact ⟨ihBody (level := level + 1) (by simpa [Nat.add_right_comm] using safe.1) avoids.1,
        ihValue safe.2 avoids.2⟩
  | hcollection kind elements rest ih =>
      intro level safe avoids
      have each := (isWellScopedListAt_eq_true_iff _ _).mp safe
      have eachAvoids := (everyQuotationList_iff _ _ _ _).mp avoids
      exact (everyQuotationList_iff _ _ _ _).mpr fun p m => ih p m (each p m) (eachAvoids p m)
  | happly constructor arguments ih =>
      intro level safe avoids
      have each := (isWellScopedListAt_eq_true_iff _ _).mp safe
      match arguments, each, avoids, ih with
      | [], _, _, _ => rfl
      | first :: second :: rest, each, avoids, ih =>
          have eachAvoids := (everyQuotationList_iff _ _ _ _).mp avoids
          exact (everyQuotationList_iff _ _ _ _).mpr fun p m => ih p m (each p m) (eachAvoids p m)
      | [payload], each, avoids, ih =>
          have payloadSafe := each payload (by simp)
          simp only [everyQuotation] at avoids ⊢
          by_cases isQuote : constructor = declaration.quoteConstructor
          · simp only [isQuote, if_true, Bool.not_eq_true'] at avoids ⊢
            exact isWellScopedAt_of_not_mentions payloadSafe avoids
          · simp only [isQuote, if_false] at avoids ⊢
            exact ih payload (by simp) payloadSafe avoids

private theorem binderSafeAt_single (quoteConstructor constructor : String) (depth : Nat)
    (payload : Pattern) :
    binderSafeAt quoteConstructor depth (.apply constructor [payload]) =
      if constructor = quoteConstructor then binderSafeAt quoteConstructor 0 payload
      else binderSafeAt quoteConstructor depth payload := by
  by_cases quoted : constructor = quoteConstructor
  · simp [binderSafeAt, quoted]
  · simp [binderSafeAt, quoted, binderSafeListAt]

/-- Quotation sealing (`binderSafeAt`), the admission of `instantiate_scoped`,
makes every genuine quotation closed. -/
theorem everyQuotation_scoped_of_binderSafeAt {pattern : Pattern} :
    ∀ {safeDepth level}, binderSafeAt declaration.quoteConstructor safeDepth pattern = true →
      everyQuotation declaration (fun level payload => payload.isWellScopedAt level) level pattern =
        true := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro _ _ _; rfl
  | hfvar name => intro _ _ _; rfl
  | hlambda binder body ih => intro _ _ safe; exact ih safe
  | hmultiLambda arity binders body ih => intro _ _ safe; exact ih safe
  | hsubst body value ihBody ihValue =>
      intro _ _ safe
      simp only [binderSafeAt, Bool.and_eq_true] at safe
      simp only [everyQuotation, Bool.and_eq_true]
      exact ⟨ihBody safe.1, ihValue safe.2⟩
  | hcollection kind elements rest ih =>
      intro _ _ safe
      have each := (binderSafeListAt_eq_true_iff _ _ _).mp safe
      exact (everyQuotationList_iff _ _ _ _).mpr fun p m => ih p m (each p m)
  | happly constructor arguments ih =>
      intro safeDepth level safe
      match arguments, safe, ih with
      | [], _, _ => rfl
      | first :: second :: rest, safe, ih =>
          have each := (binderSafeListAt_eq_true_iff _ _ _).mp (by simpa [binderSafeAt] using safe)
          exact (everyQuotationList_iff _ _ _ _).mpr fun p m => ih p m (each p m)
      | [payload], safe, ih =>
          rw [binderSafeAt_single] at safe
          simp only [everyQuotation]
          by_cases isQuote : constructor = declaration.quoteConstructor
          · simp only [isQuote, if_true] at safe ⊢
            exact isWellScopedAt_mono (isWellScopedAt_of_binderSafeAt _ safe) (Nat.zero_le _)
          · simp only [isQuote, if_false] at safe ⊢
            exact ih payload (by simp) safe

theorem lowering_fixes (replacement : Pattern) :
    ∀ level index, index < level → lowering replacement level index = .bvar index :=
  fun _ _ below => lowering_of_lt below

/-- **On sealed bodies every view is `instantiate`**, for bodies scoped under
the eliminated binder. -/
theorem applyView_eq_instantiate_of_sealed {depth : Nat} {replacement body : Pattern}
    (sealed : Sealed declaration depth body) (inScope : body.isWellScopedAt (depth + 1) = true) :
    applyView declaration depth replacement body = instantiate declaration depth replacement body :=
  substituteViewed_eq_substituteResolved (lowering_fixes replacement) _
    (everyQuotation_scoped_of_avoids (resolveQuotes_isWellScopedAt inScope) sealed)

theorem freezeView_eq_instantiate_of_sealed {depth : Nat} {replacement body : Pattern}
    (name : Pattern) (sealed : Sealed declaration depth body)
    (inScope : body.isWellScopedAt (depth + 1) = true) :
    freezeView declaration depth replacement name body =
      instantiate declaration depth replacement body := by
  rw [freezeView_eq_applyView_of_sealed name sealed, applyView_eq_instantiate_of_sealed sealed inScope]

theorem closureView_eq_instantiate_of_sealed {depth : Nat} {replacement body : Pattern}
    (context : String) (sealed : Sealed declaration depth body)
    (inScope : body.isWellScopedAt (depth + 1) = true) :
    closureView declaration context depth replacement body =
      instantiate declaration depth replacement body := by
  rw [closureView_eq_applyView_of_sealed context sealed, applyView_eq_instantiate_of_sealed sealed inScope]

/-- On quotation-sealed bodies (`binderSafeAt`, ambient binders allowed) every
view is `instantiate`. -/
theorem applyView_eq_instantiate_of_binderSafeAt {safeDepth depth : Nat} {replacement body : Pattern}
    (safe : binderSafeAt declaration.quoteConstructor safeDepth body = true) :
    applyView declaration depth replacement body = instantiate declaration depth replacement body :=
  substituteViewed_eq_substituteResolved (lowering_fixes replacement) _
    (everyQuotation_scoped_of_binderSafeAt (resolveQuotes_binderSafeAt declaration safe))

theorem freezeView_eq_instantiate_of_binderSafeAt {safeDepth depth : Nat} {replacement body : Pattern}
    (name : Pattern) (safe : binderSafeAt declaration.quoteConstructor safeDepth body = true) :
    freezeView declaration depth replacement name body =
      instantiate declaration depth replacement body :=
  substituteViewed_eq_substituteResolved (lowering_fixes _) _
    (everyQuotation_scoped_of_binderSafeAt (resolveQuotes_binderSafeAt declaration safe))

theorem closureView_eq_instantiate_of_binderSafeAt {safeDepth depth : Nat}
    {replacement body : Pattern} (context : String)
    (safe : binderSafeAt declaration.quoteConstructor safeDepth body = true) :
    closureView declaration context depth replacement body =
      instantiate declaration depth replacement body :=
  substituteViewed_eq_substituteResolved (lowering_fixes _) _
    (everyQuotation_scoped_of_binderSafeAt (resolveQuotes_binderSafeAt declaration safe))

end Sealed

/-! ## Every view keeps every binding dependency -/

section Scope

variable {declaration : ReflectivePresentationDecl}

/-- With lowering actions, the traversal preserves ordinary scope on every
body: no quotation sealing is needed, because quotations are entered. -/
theorem substituteViewed_lowering_scoped {ambient : Nat} {inside : Pattern}
    (insideSafe : inside.isWellScopedAt ambient = true) {pattern : Pattern} :
    ∀ {depth : Nat} {replacement : Pattern}, replacement.isWellScopedAt ambient = true →
      pattern.isWellScopedAt (ambient + depth + 1) = true →
        (substituteViewed declaration (lowering inside) (lowering replacement) depth
          pattern).isWellScopedAt (ambient + depth) = true := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      intro depth replacement replacementSafe safe
      exact instantiateBVarAt_isWellScopedAt safe replacementSafe
  | hfvar name => intro _ _ _ _; rfl
  | hlambda binder body ih =>
      intro depth replacement replacementSafe safe
      have bodySafe : body.isWellScopedAt (ambient + (depth + 1) + 1) = true := by
        simpa [Pattern.isWellScopedAt, Nat.add_assoc] using safe
      simpa [substituteViewed, Pattern.isWellScopedAt, Nat.add_assoc] using
        ih replacementSafe bodySafe
  | hmultiLambda arity binders body ih =>
      intro depth replacement replacementSafe safe
      have bodySafe : body.isWellScopedAt (ambient + (depth + arity) + 1) = true := by
        simpa [Pattern.isWellScopedAt, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using safe
      simpa [substituteViewed, Pattern.isWellScopedAt, Nat.add_assoc] using
        ih replacementSafe bodySafe
  | hsubst body value ihBody ihValue =>
      intro depth replacement replacementSafe safe
      simp only [Pattern.isWellScopedAt, Bool.and_eq_true] at safe
      simp only [substituteViewed, Pattern.isWellScopedAt, Bool.and_eq_true]
      refine ⟨?_, ihValue replacementSafe safe.2⟩
      simpa [Nat.add_assoc] using ihBody (depth := depth + 1) replacementSafe
        (by simpa [Nat.add_assoc] using safe.1)
  | hcollection kind elements rest ih =>
      intro depth replacement replacementSafe safe
      have each := (isWellScopedListAt_eq_true_iff _ _).mp safe
      show Pattern.isWellScopedListAt (ambient + depth)
        (substituteViewedList declaration _ _ depth elements) = true
      rw [substituteViewedList_eq_map, isWellScopedListAt_eq_true_iff]
      intro p member
      obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
      exact ih original originalMember replacementSafe (each original originalMember)
  | happly constructor arguments ih =>
      intro depth replacement replacementSafe safe
      have each := (isWellScopedListAt_eq_true_iff _ _).mp safe
      match arguments, each, ih with
      | [], _, _ => rfl
      | first :: second :: rest, each, ih =>
          show Pattern.isWellScopedListAt (ambient + depth)
            (substituteViewedList declaration _ _ depth (first :: second :: rest)) = true
          rw [substituteViewedList_eq_map, isWellScopedListAt_eq_true_iff]
          intro p member
          obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
          exact ih original originalMember replacementSafe (each original originalMember)
      | [payload], each, ih =>
          have payloadSafe := each payload (by simp)
          by_cases isQuote : constructor = declaration.quoteConstructor
          · simp only [substituteViewed, isQuote, if_true]
            simpa [Pattern.isWellScopedAt, Pattern.isWellScopedListAt] using
              ih payload (by simp) insideSafe payloadSafe
          · have received : (lowering replacement depth depth).isWellScopedAt (ambient + depth) = true :=
              instantiateBVarAt_isWellScopedAt (by simp [Pattern.isWellScopedAt]; omega) replacementSafe
            have through : (Pattern.apply constructor [substituteViewed declaration (lowering inside)
                (lowering replacement) depth payload]).isWellScopedAt (ambient + depth) = true := by
              simpa [Pattern.isWellScopedAt, Pattern.isWellScopedListAt] using
                ih payload (by simp) replacementSafe payloadSafe
            simp only [substituteViewed, isQuote, if_false]
            split
            · split
              · rcases receive_cases (declaration := declaration) constructor
                    (lowering replacement depth depth) with plain | ⟨process, shaped, ran⟩
                · rw [plain]
                  simpa [Pattern.isWellScopedAt, Pattern.isWellScopedListAt] using received
                · rw [ran]
                  rw [shaped] at received
                  simpa [Pattern.isWellScopedAt, Pattern.isWellScopedListAt] using received
              · exact through
            · exact through

theorem applyView_scoped {ambient depth : Nat} {replacement body : Pattern}
    (bodySafe : body.isWellScopedAt (ambient + depth + 1) = true)
    (replacementSafe : replacement.isWellScopedAt ambient = true) :
    (applyView declaration depth replacement body).isWellScopedAt (ambient + depth) = true :=
  substituteViewed_lowering_scoped replacementSafe replacementSafe
    (resolveQuotes_isWellScopedAt bodySafe)

theorem freezeView_scoped {ambient depth : Nat} {replacement name body : Pattern}
    (nameSafe : name.isWellScopedAt ambient = true)
    (bodySafe : body.isWellScopedAt (ambient + depth + 1) = true)
    (replacementSafe : replacement.isWellScopedAt ambient = true) :
    (freezeView declaration depth replacement name body).isWellScopedAt (ambient + depth) = true :=
  substituteViewed_lowering_scoped nameSafe replacementSafe (resolveQuotes_isWellScopedAt bodySafe)

theorem closureView_scoped {ambient depth : Nat} {replacement body : Pattern} (context : String)
    (bodySafe : body.isWellScopedAt (ambient + depth + 1) = true)
    (replacementSafe : replacement.isWellScopedAt ambient = true) :
    (closureView declaration context depth replacement body).isWellScopedAt (ambient + depth) = true :=
  substituteViewed_lowering_scoped
    (by simpa [contextual, Pattern.isWellScopedAt, Pattern.isWellScopedListAt] using replacementSafe)
    replacementSafe (resolveQuotes_isWellScopedAt bodySafe)

end Scope

/-! ## The declared quote scope

A presentation declares its quote scope (`ReflectivePresentationDecl.quoteScope`);
the declared substitution is `substituteScoped` in the core. Eliminating a binder
under a scope: -/

/-- **Binder elimination under a quote scope.** A closed scope is `instantiate`; a
reaching scope enters genuine quotations with its view. -/
def substituteUnder (declaration : ReflectivePresentationDecl) (scope : QuoteScope) (depth : Nat)
    (replacement body : Pattern) : Pattern :=
  substituteScoped declaration scope (lowering replacement) depth body

/-- The bodies a quote scope admits for eliminating the binder at `depth`: a
closed scope admits the sealed bodies, a reaching scope every body. -/
def scopeAdmits (declaration : ReflectivePresentationDecl) : QuoteScope → Nat → Pattern → Bool
  | .closed, depth, body =>
      everyQuotation declaration (fun level payload => !mentions level payload) depth
        (resolveQuotes declaration body)
  | .reaching _, _, _ => true

section Declared

variable {declaration : ReflectivePresentationDecl}

theorem scopeAdmits_closed_iff {depth : Nat} {body : Pattern} :
    scopeAdmits declaration .closed depth body = true ↔ Sealed declaration depth body := Iff.rfl

/-- **Every quote scope admits equal bodies alike.** -/
theorem scopeAdmits_respects (scope : QuoteScope) (depth : Nat) {left right : Pattern}
    (same : canonicalEquivalent declaration left right = true) :
    scopeAdmits declaration scope depth left = scopeAdmits declaration scope depth right := by
  cases scope with
  | closed => exact Bool.eq_iff_iff.mpr (sealed_respects depth same)
  | reaching view => rfl

/-- **Binder elimination under every quote scope respects the declared equations.** -/
theorem substituteUnder_respects (scope : QuoteScope) (depth : Nat) (replacement : Pattern)
    {left right : Pattern} (same : canonicalEquivalent declaration left right = true) :
    canonicalEquivalent declaration (substituteUnder declaration scope depth replacement left)
      (substituteUnder declaration scope depth replacement right) = true :=
  substituteScoped_respects scope (lowering replacement) depth same

theorem substituteUnder_closed (depth : Nat) (replacement body : Pattern) :
    substituteUnder declaration .closed depth replacement body =
      instantiate declaration depth replacement body := rfl

theorem substituteUnder_apply (depth : Nat) (replacement body : Pattern) :
    substituteUnder declaration (.reaching .apply) depth replacement body =
      applyView declaration depth replacement body := rfl

theorem substituteUnder_freeze (depth : Nat) (frozen : FrozenSpelling) (replacement body : Pattern) :
    substituteUnder declaration (.reaching (.freeze frozen)) depth replacement body =
      freezeView declaration depth replacement frozen.spelling body := by
  show substituteViewed declaration ((QuoteView.freeze frozen).inside (lowering replacement))
      (lowering replacement) depth (resolveQuotes declaration body) =
    substituteViewed declaration (lowering frozen.spelling) (lowering replacement) depth
      (resolveQuotes declaration body)
  congr 1
  funext level index
  by_cases same : index = level
  · subst same
    simp [QuoteView.inside, lowering_self, liftBVars_eq_self_of_isWellScopedAt frozen.ground.2]
  · simp [QuoteView.inside, same, lowering_of_ne replacement frozen.spelling same]

theorem substituteUnder_closure (depth : Nat) (context : String) (replacement body : Pattern) :
    substituteUnder declaration (.reaching (.closure context)) depth replacement body =
      closureView declaration context depth replacement body := by
  show substituteViewed declaration ((QuoteView.closure context).inside (lowering replacement))
      (lowering replacement) depth (resolveQuotes declaration body) =
    substituteViewed declaration (lowering (contextual context replacement)) (lowering replacement) depth
      (resolveQuotes declaration body)
  congr 1
  funext level index
  by_cases same : index = level
  · subst same
    simp [QuoteView.inside, lowering_self, contextual, liftBVars, liftBVarsList_eq_map]
  · simp [QuoteView.inside, same, lowering_of_ne replacement (contextual context replacement) same]

/-- **On sealed bodies, every quote scope gives the same result**, which is
`instantiate`. -/
theorem substituteUnder_eq_instantiate_of_sealed (scope : QuoteScope) {depth : Nat}
    {replacement body : Pattern}
    (admitted : scopeAdmits declaration .closed depth body = true)
    (inScope : body.isWellScopedAt (depth + 1) = true) :
    substituteUnder declaration scope depth replacement body =
      instantiate declaration depth replacement body := by
  rcases scope with _ | (_ | frozen | context)
  · rfl
  · exact applyView_eq_instantiate_of_sealed admitted inScope
  · rw [substituteUnder_freeze]
    exact freezeView_eq_instantiate_of_sealed frozen.spelling admitted inScope
  · rw [substituteUnder_closure]
    exact closureView_eq_instantiate_of_sealed context admitted inScope

/-- **Every quote scope keeps every binding dependency** on the bodies it
admits: a closed replacement and a body scoped under the eliminated binder give
a result with no dangling index. -/
theorem substituteUnder_scoped (scope : QuoteScope) {depth : Nat} {replacement body : Pattern}
    (admitted : scopeAdmits declaration scope depth body = true)
    (bodySafe : body.isWellScopedAt (depth + 1) = true)
    (replacementSafe : replacement.isWellScopedAt 0 = true) :
    (substituteUnder declaration scope depth replacement body).isWellScopedAt depth = true := by
  have bodySafe' : body.isWellScopedAt (0 + depth + 1) = true := by simpa using bodySafe
  have applied := applyView_scoped (declaration := declaration) bodySafe' replacementSafe
  rw [Nat.zero_add] at applied
  rcases scope with _ | (_ | frozen | context)
  · show (instantiate declaration depth replacement body).isWellScopedAt depth = true
    rw [← applyView_eq_instantiate_of_sealed admitted bodySafe]
    exact applied
  · exact applied
  · rw [substituteUnder_freeze]
    simpa using freezeView_scoped (declaration := declaration) frozen.ground.2 bodySafe'
      replacementSafe
  · rw [substituteUnder_closure]
    simpa using closureView_scoped (declaration := declaration) context bodySafe' replacementSafe

end Declared

/-! ## Controls -/

section Controls

/-- One carrier: names and processes share a sort. -/
private def oneCarrier : ReflectivePresentationDecl where
  name := "oneCarrier"
  processSort := "Term"
  nameSort := "Term"
  quoteConstructor := "Quote"
  dropConstructor := "Drop"
  parallelCollection := .hashBag
  parallelUnitConstructor := "Nil"
  quoteDropEquation := "QuoteDrop"
  -- Closed: the baseline; each view below is passed to the operations explicitly.
  quoteScope := .closed

private def quoteOf (process : Pattern) : Pattern := .apply "Quote" [process]
private def dropOf (name : Pattern) : Pattern := .apply "Drop" [name]
private def par (first second : Pattern) : Pattern := .collection .hashBag [first, second] none
private def nil : Pattern := .apply "Nil" []
private def f (argument : Pattern) : Pattern := .apply "F" [argument]
private def lam (body : Pattern) : Pattern := .lambda none body
/-- The replacement: the quotation of `G(g)`. -/
private def received : Pattern := quoteOf (.apply "G" [.fvar "g"])

/-- `*@(*y | 0)`: the name equations resolve the quotation first, so the body is
the drop `*y`, which receives the replacement under every view. -/
private def throughUnit : Pattern := dropOf (quoteOf (par (dropOf (.bvar 0)) nil))
/-- `F(@(*y | *z))`: a genuine quotation mentions `y`. -/
private def quotedDrop : Pattern := f (quoteOf (par (dropOf (.bvar 0)) (dropOf (.fvar "z"))))
/-- `F(@(λ. *y))`: a genuine quotation mentions `y` under its own binder. -/
private def quotedUnder : Pattern := f (quoteOf (lam (dropOf (.bvar 1))))
/-- `F(*y | @(λ. *0))`: the only quotation mentions only its own binder. -/
private def sealedBody : Pattern := f (par (dropOf (.bvar 0)) (quoteOf (lam (dropOf (.bvar 0)))))

/-- Positive: through the unit, every view and `instantiate` run the received
quotation. -/
example :
    [instantiate oneCarrier 0 received throughUnit, applyView oneCarrier 0 received throughUnit,
        freezeView oneCarrier 0 received (.fvar "y") throughUnit,
        closureView oneCarrier "Ctx" 0 received throughUnit] =
      List.replicate 4 (.apply "G" [.fvar "g"]) := by
  decide +kernel

/-- Separating: `instantiate` leaves `y` dangling inside the quotation; apply
runs the received drop inside it; freeze names the binder; closure keeps the
value as context. -/
example : instantiate oneCarrier 0 received quotedDrop = quotedDrop := by decide +kernel
example : (instantiate oneCarrier 0 received quotedDrop).isWellScopedAt 0 = false := by
  decide +kernel
example : applyView oneCarrier 0 received quotedDrop =
    f (quoteOf (par (.apply "G" [.fvar "g"]) (dropOf (.fvar "z")))) := by decide +kernel
example : freezeView oneCarrier 0 received (.fvar "y") quotedDrop =
    f (quoteOf (par (dropOf (.fvar "y")) (dropOf (.fvar "z")))) := by decide +kernel
example : closureView oneCarrier "Ctx" 0 received quotedDrop =
    f (quoteOf (par (dropOf (contextual "Ctx" received)) (dropOf (.fvar "z")))) := by decide +kernel

/-- Separating under an inner binder. -/
example : instantiate oneCarrier 0 received quotedUnder = quotedUnder := by decide +kernel
example : (instantiate oneCarrier 0 received quotedUnder).isWellScopedAt 0 = false := by
  decide +kernel
example : applyView oneCarrier 0 received quotedUnder =
    f (quoteOf (lam (.apply "G" [.fvar "g"]))) := by decide +kernel
example : freezeView oneCarrier 0 received (.fvar "y") quotedUnder =
    f (quoteOf (lam (dropOf (.fvar "y")))) := by decide +kernel
example : closureView oneCarrier "Ctx" 0 received quotedUnder =
    f (quoteOf (lam (dropOf (contextual "Ctx" received)))) := by decide +kernel

/-- The observations recover the views on the separating bodies. -/
example : erase oneCarrier "Ctx" (closureView oneCarrier "Ctx" 0 received quotedDrop) =
    applyView oneCarrier 0 received quotedDrop := by decide +kernel
example : atomize oneCarrier "Ctx" (.fvar "y") (closureView oneCarrier "Ctx" 0 received quotedUnder) =
    freezeView oneCarrier 0 received (.fvar "y") quotedUnder := by decide +kernel

/-- Positive: on a sealed body all views are `instantiate`. -/
example : Sealed oneCarrier 0 sealedBody := by decide +kernel
example :
    [applyView oneCarrier 0 received sealedBody, freezeView oneCarrier 0 received (.fvar "y") sealedBody,
        closureView oneCarrier "Ctx" 0 received sealedBody] =
      List.replicate 3 (instantiate oneCarrier 0 received sealedBody) := by
  decide +kernel

/-- Negative: the separating bodies are not sealed. -/
example : ¬ Sealed oneCarrier 0 quotedDrop := by decide +kernel
example : ¬ Sealed oneCarrier 0 quotedUnder := by decide +kernel

/-- A quotation that mentions only an ambient binder is sealed, and the views
lower that index; `instantiate` does not. The scope premise of
`applyView_eq_instantiate_of_sealed` is therefore needed. -/
example : Sealed oneCarrier 0 (quoteOf (f (.bvar 1))) := by decide +kernel
example : applyView oneCarrier 0 received (quoteOf (f (.bvar 1))) = quoteOf (f (.bvar 0)) := by
  decide +kernel
example : instantiate oneCarrier 0 received (quoteOf (f (.bvar 1))) = quoteOf (f (.bvar 1)) := by
  decide +kernel

/-- The closure keeps strictly more than apply and freeze: bodies they identify,
it separates. -/
example : applyView oneCarrier 0 received (quoteOf (f (.bvar 0))) =
    applyView oneCarrier 0 received (quoteOf (f received)) := by decide +kernel
example : closureView oneCarrier "Ctx" 0 received (quoteOf (f (.bvar 0))) ≠
    closureView oneCarrier "Ctx" 0 received (quoteOf (f received)) := by decide +kernel
example : freezeView oneCarrier 0 received (.fvar "y") (quoteOf (f (.bvar 0))) =
    freezeView oneCarrier 0 received (.fvar "y") (quoteOf (f (.fvar "y"))) := by decide +kernel
example : closureView oneCarrier "Ctx" 0 received (quoteOf (f (.bvar 0))) ≠
    closureView oneCarrier "Ctx" 0 received (quoteOf (f (.fvar "y"))) := by decide +kernel

/-- **Freshness is necessary.** A body that already contains the context
constructor has the same closure as a body that mentions the binder, while
their apply views differ: no observation of the closure recovers apply on all
bodies. The same holds for freeze. -/
theorem closureView_not_factorable :
    ¬ ∃ observe : Pattern → Pattern, ∀ body,
      observe (closureView oneCarrier "Ctx" 0 (.fvar "c") body) = applyView oneCarrier 0 (.fvar "c") body := by
  rintro ⟨observe, factors⟩
  have sameCore : closureView oneCarrier "Ctx" 0 (.fvar "c") (quoteOf (f (contextual "Ctx" (.fvar "c")))) =
      closureView oneCarrier "Ctx" 0 (.fvar "c") (quoteOf (f (.bvar 0))) := by decide +kernel
  have differentViews : applyView oneCarrier 0 (.fvar "c") (quoteOf (f (contextual "Ctx" (.fvar "c")))) ≠
      applyView oneCarrier 0 (.fvar "c") (quoteOf (f (.bvar 0))) := by decide +kernel
  exact differentViews (by rw [← factors, ← factors, sameCore])

theorem closureView_not_factorable_freeze :
    ¬ ∃ observe : Pattern → Pattern, ∀ body,
      observe (closureView oneCarrier "Ctx" 0 (.fvar "c") body) =
        freezeView oneCarrier 0 (.fvar "c") (.fvar "y") body := by
  rintro ⟨observe, factors⟩
  have sameCore : closureView oneCarrier "Ctx" 0 (.fvar "c") (quoteOf (f (contextual "Ctx" (.fvar "c")))) =
      closureView oneCarrier "Ctx" 0 (.fvar "c") (quoteOf (f (.bvar 0))) := by decide +kernel
  have differentViews : freezeView oneCarrier 0 (.fvar "c") (.fvar "y") (quoteOf (f (contextual "Ctx" (.fvar "c")))) ≠
      freezeView oneCarrier 0 (.fvar "c") (.fvar "y") (quoteOf (f (.bvar 0))) := by decide +kernel
  exact differentViews (by rw [← factors, ← factors, sameCore])

/-! The validator enforces the freshness that `closureView_not_factorable`
shows necessary: a closure context constructor lies outside the signature. -/

/-- Positive: rho with a closure view on a constructor outside its signature
validates. -/
theorem closure_fresh_context_validates :
    rhoCalc.validateReflectivePresentation
      { rhoReflectivePresentation.toReflectivePresentationDecl with
        quoteScope := .reaching (.closure "QuoteContext") } = [] := by
  decide +kernel

/-- Negative: a closure view on rho's own unit constructor is rejected, by
exactly one error. -/
theorem closure_signature_context_rejected :
    (rhoCalc.validateReflectivePresentation
      { rhoReflectivePresentation.toReflectivePresentationDecl with
        quoteScope := .reaching (.closure "PZero") }).length = 1 := by
  decide +kernel

/-- Negative: a context constructor equal to the quote constructor is read back
as a quotation, and erasure no longer recovers apply. -/
example : erase oneCarrier "Quote" (closureView oneCarrier "Quote" 0 received (quoteOf (f (.bvar 0)))) ≠
    applyView oneCarrier 0 received (quoteOf (f (.bvar 0))) := by decide +kernel

/-- Coherence on a respelling: `F(@(*@(*y) | *z))` is `F(@(*y | *z))` by the
quote-drop equation, and every view treats them alike. -/
example :
    let respelled := f (quoteOf (par (dropOf (quoteOf (dropOf (.bvar 0)))) (dropOf (.fvar "z"))))
    [applyView oneCarrier 0 received respelled, freezeView oneCarrier 0 received (.fvar "y") respelled,
        closureView oneCarrier "Ctx" 0 received respelled] =
      [applyView oneCarrier 0 received quotedDrop, freezeView oneCarrier 0 received (.fvar "y") quotedDrop,
        closureView oneCarrier "Ctx" 0 received quotedDrop] := by
  decide +kernel

/-- The declared scope dispatches. -/
example : substituteUnder oneCarrier (.reaching (.closure "Ctx")) 0 received quotedDrop =
    closureView oneCarrier "Ctx" 0 received quotedDrop :=
  substituteUnder_closure 0 "Ctx" received quotedDrop
example : scopeAdmits oneCarrier .closed 0 quotedDrop = false := by decide +kernel
example : scopeAdmits oneCarrier (.reaching .apply) 0 quotedDrop = true := rfl

/-! ### Admission and the declared equations -/

/-- `@(*y)`: by the quote-drop equation, the name `y`. -/
private def quotedBinder : Pattern := quoteOf (dropOf (.bvar 0))

/-- `F(@(λ. *0) | *@(*y))`: `sealedBody` respelled by commutativity and the
quote-drop equation. -/
private def sealedRespelled : Pattern :=
  f (par (quoteOf (lam (dropOf (.bvar 0)))) (dropOf (quoteOf (dropOf (.bvar 0)))))

/-- `F(@(*@(*y) | *z))`: `quotedDrop` respelled by the quote-drop equation. -/
private def quotedDropRespelled : Pattern :=
  f (quoteOf (par (dropOf (quoteOf (dropOf (.bvar 0)))) (dropOf (.fvar "z"))))

/- Sorting a bag is well-founded recursion, which the kernel does not unfold;
the equations of a bag are taken from `canonicalize_parallel_permutation` and
congruence, and only bag-free members are computed. -/

private theorem sealedRespelled_equivalent :
    canonicalEquivalent oneCarrier sealedBody sealedRespelled = true := by
  rw [canonicalEquivalent_eq_true_iff]
  refine canonicalize_apply_congr "F" ?_
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
  refine (canonicalize_parallel_permutation oneCarrier (List.Perm.swap _ _ [])).trans ?_
  exact canonicalize_collection_congr _ _ (by decide +kernel)

private theorem quotedDropRespelled_equivalent :
    canonicalEquivalent oneCarrier quotedDrop quotedDropRespelled = true := by
  rw [canonicalEquivalent_eq_true_iff]
  refine canonicalize_apply_congr "F" ?_
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
  refine canonicalize_apply_congr "Quote" ?_
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
  exact canonicalize_collection_congr _ _ (by decide +kernel)

/-- Positive: equal bodies are admitted alike, sealed or not. -/
example : Sealed oneCarrier 0 sealedBody ∧ Sealed oneCarrier 0 sealedRespelled := by decide +kernel
example : Sealed oneCarrier 0 sealedRespelled :=
  (sealed_respects 0 sealedRespelled_equivalent).mp (by decide +kernel)
example : ¬ Sealed oneCarrier 0 quotedDrop ∧ ¬ Sealed oneCarrier 0 quotedDropRespelled := by
  decide +kernel
example : canonicalEquivalent oneCarrier throughUnit (dropOf (.bvar 0)) = true ∧
    Sealed oneCarrier 0 throughUnit ∧ Sealed oneCarrier 0 (dropOf (.bvar 0)) := by
  decide +kernel
example (scope : QuoteScope) : scopeAdmits oneCarrier scope 0 quotedDrop =
    scopeAdmits oneCarrier scope 0 quotedDropRespelled :=
  scopeAdmits_respects scope 0 quotedDropRespelled_equivalent

/-- **Negative: the unresolved admission does not respect the equations.**
`@(*y)` and `y` are equal, and so are their instantiations, but `binderSafeAt`,
the admission of `instantiate_scoped` at ambient and depth zero, accepts `y`
and rejects `@(*y)`. Sealed admission accepts both. -/
theorem binderSafeAt_not_respects :
    canonicalEquivalent oneCarrier quotedBinder (.bvar 0) = true ∧
      binderSafeAt oneCarrier.quoteConstructor 1 quotedBinder = false ∧
      binderSafeAt oneCarrier.quoteConstructor 1 (.bvar 0) = true := by
  decide +kernel
example : Sealed oneCarrier 0 quotedBinder ∧ Sealed oneCarrier 0 (.bvar 0) := by decide +kernel
example : instantiate oneCarrier 0 received quotedBinder =
    instantiate oneCarrier 0 received (.bvar 0) := by decide +kernel

/-- Resolution is necessary in `everyQuotation_canonicalize`: on the
unresolved `@(*y)` the test reads a quotation that canonicalization removes. -/
example : everyQuotation oneCarrier (fun level payload => !mentions level payload) 0 quotedBinder =
      false ∧
    everyQuotation oneCarrier (fun level payload => !mentions level payload) 0
      (canonicalize oneCarrier quotedBinder) = true := by
  decide +kernel

/-! ### `instantiate` as one traversal -/

/-- `@(*(y | 0) | *y)`: one genuine quotation spells the binder's drop twice,
once through the unit. It is resolved. -/
private def twoSpellings : Pattern := quoteOf (par (dropOf (par (.bvar 0) nil)) (dropOf (.bvar 0)))

/-- `instantiate` keeps both spellings; the traversal with `keepIndex` writes
both as `*y`, which is equal modulo the equations. -/
example : resolveQuotes oneCarrier twoSpellings = twoSpellings ∧
    instantiate oneCarrier 0 received twoSpellings = twoSpellings ∧
    substituteViewed oneCarrier keepIndex (lowering received) 0 (resolveQuotes oneCarrier twoSpellings) =
      quoteOf (par (dropOf (.bvar 0)) (dropOf (.bvar 0))) := by
  decide +kernel
example : canonicalEquivalent oneCarrier (instantiate oneCarrier 0 received twoSpellings)
    (substituteViewed oneCarrier keepIndex (lowering received) 0
      (resolveQuotes oneCarrier twoSpellings)) = true :=
  instantiate_equivalent_substituteViewed 0 received twoSpellings

/-- **No inside action makes `instantiate` literally a traversal on resolved
bodies.** A traversal gives every drop of the binder inside a quotation the
same result, while `instantiate` keeps the two spellings apart. -/
theorem instantiate_not_substituteViewed :
    ¬ ∃ insideQuote : Nat → Nat → Pattern,
      substituteViewed oneCarrier insideQuote (lowering received) 0
          (resolveQuotes oneCarrier twoSpellings) =
        instantiate oneCarrier 0 received twoSpellings := by
  rintro ⟨insideQuote, same⟩
  have resolved : resolveQuotes oneCarrier twoSpellings = twoSpellings := by decide +kernel
  have kept : instantiate oneCarrier 0 received twoSpellings = twoSpellings := by decide +kernel
  have traversed : substituteViewed oneCarrier insideQuote (lowering received) 0 twoSpellings =
      quoteOf (.collection .hashBag [receive oneCarrier "Drop" (insideQuote 0 0),
        receive oneCarrier "Drop" (insideQuote 0 0)] none) := rfl
  rw [resolved, kept, traversed] at same
  simp only [quoteOf, twoSpellings, par, dropOf, nil, Pattern.apply.injEq, Pattern.collection.injEq,
    List.cons.injEq, true_and, and_true] at same
  exact absurd (same.1.symm.trans same.2) (by decide)

end Controls

end Mettapedia.OSLF.MeTTaIL.ReflectiveContextualQuote
