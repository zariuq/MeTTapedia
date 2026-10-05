import Mettapedia.Languages.MM0.Upstream.Lean3Typing
import Mettapedia.Languages.MM0.Kernel.SubstitutionTyping
import Mettapedia.Languages.MM0.Presentation.SubstitutionCorrespondence
import Mettapedia.Languages.MM0.Presentation.FreeVariablesCorrespondence

/-!
# The pinned MM0 occurrence, substitution and free-variable accounts

The historical definitions below adapt `sexpr.has_var`, `sexpr.free'` and
`sexpr.subst` from `mm0-lean/mm0/mm0.lean`, lines 114--136 and 183--191, at
revision `6d5f0d4fae8e2e3ae0b998bcbaa9d059cad99fad`:
https://github.com/digama0/mm0/blob/6d5f0d4fae8e2e3ae0b998bcbaa9d059cad99fad/mm0-lean/mm0/mm0.lean

The separate `specifiedFreeSpine` retains that spine representation but uses
the union in `mm0.md` and `examples/mm0.mm0`'s `FreeApp`. The historical
conjunction and missing-substitution default are kept explicitly, rather than
asserting equivalence at inputs where those definitions differ.

This is a logical-account bridge, not a third checking implementation.
Historical theorem admissibility, dummy freshness, conversion and proofs are
outside its compatibility claim.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Upstream.Lean3Dependencies

open Lean3Typing

namespace Reference

open Lean3Typing.Reference

/-- The context-relative occurrence predicate of the pinned specification. -/
def hasVar (context : Context) : SExpr → Nat → Prop
  | .var source, index => ∃ binder, context[source]? = some binder ∧
      match binder with
      | .bound _ => source = index
      | .reg _ dependencies => index ∈ dependencies
  | .term _, _ => False
  | .app1 function argument, index => hasVar context function index ∨ hasVar context argument index

/-- `σ.inth` in the historical source returns the inhabited default on a miss. -/
def substitute (images : List SExpr) : SExpr → SExpr
  | .var index => (images[index]?).getD (.var 0)
  | .term index => .term index
  | .app1 function argument => .app1 (substitute images function) (substitute images argument)

/-- Exactly the syntactic occurrences at which a simultaneous image is needed. -/
def withinImages (count : Nat) : SExpr → Prop
  | .var index => index < count
  | .term _ => True
  | .app1 function argument => withinImages count function ∧ withinImages count argument

def maybeFreeArgument (arguments : List SExpr) (binder : Binder) (index : Nat) : Prop :=
  ∃ sort dependencies, binder = .reg sort dependencies ∧
    ¬ ∃ position ∈ dependencies, arguments[position]? = some (.var index)

/-- The conjunction is verbatim historical behavior, including recursive children. -/
def historicalFreeSpine (environment : Env) (context : Context) (index : Nat) :
    SExpr → List SExpr → List Prop → Prop
  | .var source, _, _ => hasVar context (.var source) index
  | .term symbol, arguments, children => ∃ formal sort dependencies body,
      GetTerm environment symbol formal (sort, dependencies) body ∧
      (∃ (position : Nat) (free : Prop) (binder : Binder), children[position]? = some free ∧
        formal[position]? = some binder ∧ free ∧ maybeFreeArgument arguments binder index) ∧
      ∃ position ∈ dependencies, arguments[position]? = some (.var index)
  | .app1 function argument, arguments, children =>
      historicalFreeSpine environment context index function (argument :: arguments)
        (historicalFreeSpine environment context index argument [] [] :: children)

def historicalFree (environment : Env) (context : Context) (expression : SExpr) (index : Nat) : Prop :=
  historicalFreeSpine environment context index expression [] []

/-- The specified `FreeApp` disjunction, distinct from the historical Lean definition. -/
def specifiedFreeSpine (environment : Env) (context : Context) (index : Nat) :
    SExpr → List SExpr → List Prop → Prop
  | .var source, _, _ => hasVar context (.var source) index
  | .term symbol, arguments, children => ∃ formal sort dependencies body,
      GetTerm environment symbol formal (sort, dependencies) body ∧
      ((∃ (position : Nat) (free : Prop) (binder : Binder), children[position]? = some free ∧
        formal[position]? = some binder ∧ free ∧ maybeFreeArgument arguments binder index) ∨
       ∃ position ∈ dependencies, arguments[position]? = some (.var index))
  | .app1 function argument, arguments, children =>
      specifiedFreeSpine environment context index function (argument :: arguments)
        (specifiedFreeSpine environment context index argument [] [] :: children)

def specifiedFree (environment : Env) (context : Context) (expression : SExpr) (index : Nat) : Prop :=
  specifiedFreeSpine environment context index expression [] []

/-- The historical positive predicate entails the specified one. The converse
fails: a returned dependency alone is already sufficient in `FreeApp`. -/
theorem historical_implies_specified_spine (environment : Env) (context : Context) (index : Nat)
    (expression : SExpr) (arguments : List SExpr) (oldChildren newChildren : List Prop) :
    historicalFreeSpine environment context index expression arguments oldChildren →
      specifiedFreeSpine environment context index expression arguments newChildren := by
  induction expression generalizing arguments oldChildren newChildren with
  | var => exact id
  | term symbol =>
      rintro ⟨formal, sort, dependencies, body, known, _, returned⟩
      exact ⟨formal, sort, dependencies, body, known, .inr returned⟩
  | app1 function argument ihFunction _ =>
      simpa only [historicalFreeSpine, specifiedFreeSpine] using ihFunction (argument :: arguments)
        (historicalFreeSpine environment context index argument [] [] :: oldChildren)
        (specifiedFreeSpine environment context index argument [] [] :: newChildren)

theorem historical_implies_specified (environment : Env) (context : Context)
    (expression : SExpr) (index : Nat) :
    historicalFree environment context expression index → specifiedFree environment context expression index :=
  historical_implies_specified_spine environment context index expression [] [] []

end Reference

open Lean3Typing.Reference

/-- Declared regular-variable dependencies, not their syntactic indices, are retained. -/
theorem hasVar_iff (context : Context) (expression : SExpr) (index : Nat) :
    Reference.hasVar context expression index ↔
      Kernel.Preterm.HasVar (toContext context) index expression.toKernel := by
  induction expression with
  | var source =>
      cases lookup : context[source]? with
      | none =>
          simp [Reference.hasVar, Kernel.Preterm.hasVar_var_iff, toContext,
            List.getElem?_map, lookup, SExpr.toKernel]
      | some binder =>
          cases binder <;>
            simp [Reference.hasVar, Kernel.Preterm.hasVar_var_iff, toContext,
              List.getElem?_map, lookup, SExpr.toKernel, Binder.toKernel, eq_comm]
  | term symbol => simp [Reference.hasVar, SExpr.toKernel]
  | app1 function argument ihFunction ihArgument =>
      simp only [Reference.hasVar, SExpr.toKernel, Kernel.Preterm.hasVar_app_iff,
        ihFunction, ihArgument]

theorem hasVar_ofKernel_iff (context : Kernel.Context) (expression : Kernel.Preterm) (index : Nat) :
    Reference.hasVar (ofContext context) (SExpr.ofKernel expression) index ↔
      Kernel.Preterm.HasVar context index expression := by
  simpa using hasVar_iff (ofContext context) (SExpr.ofKernel expression) index

/-- Success of complete support is a real domain premise: an undefined child
cannot be rescued by an occurrence in another child. -/
theorem supported_membership_iff {context : Kernel.Context} {expression : Kernel.Preterm}
    {support : Finset Nat} (supported : Kernel.Preterm.Supports context expression support) (index : Nat) :
    index ∈ support ↔ Reference.hasVar (ofContext context) (SExpr.ofKernel expression) index :=
  (supported.mem_iff_hasVar index).trans (hasVar_ofKernel_iff context expression index).symm

theorem typed_support_exists {environment : Env} {theory : Kernel.Theory}
    (related : EnvironmentRelated environment theory) {context remaining : Context}
    {expression : SExpr} {sort : Nat} (typed : Typed environment context expression remaining sort) :
    ∃ support, Kernel.Preterm.support? (toContext context) expression.toKernel = some support ∧
      ∀ index, index ∈ support ↔ Reference.hasVar context expression index := by
  obtain ⟨support, supported⟩ := (typed_toKernel related typed).support_exists
  exact ⟨support, supported.eval, fun index =>
    (supported.mem_iff_hasVar index).trans (hasVar_iff context expression index).symm⟩

theorem withinImages_iff (source : Kernel.Preterm) (count : Nat) :
    Reference.withinImages count (SExpr.ofKernel source) ↔
      ∀ index, Kernel.Preterm.Occurs index source → index < count := by
  induction source with
  | var source =>
      constructor
      · intro bounded index occurrence; cases occurrence; exact bounded
      · intro bounded; exact bounded source .var
  | term => constructor <;> intro _
            · intro index occurrence; cases occurrence
            · trivial
  | app function argument ihFunction ihArgument =>
      constructor
      · intro bounded index occurrence
        cases occurrence with
        | function head => exact ihFunction.mp bounded.1 index head
        | argument tail => exact ihArgument.mp bounded.2 index tail
      · intro bounded
        exact ⟨ihFunction.mpr (fun index occurrence => bounded index (.function occurrence)),
          ihArgument.mpr (fun index occurrence => bounded index (.argument occurrence))⟩

/-- The independent substitution rules, not defaulting, determine the common result. -/
theorem substitution_of_derivation {images : List Kernel.Preterm} {source result : Kernel.Preterm}
    (substituted : Kernel.Preterm.Substitutes (Kernel.Substitution.ofList images) source result) :
    Reference.substitute (images.map SExpr.ofKernel) (SExpr.ofKernel source) = SExpr.ofKernel result := by
  induction substituted with
  | var lookup => simp [Reference.substitute, SExpr.ofKernel, List.getElem?_map,
      Kernel.Substitution.ofList] at lookup ⊢; rw [lookup]; rfl
  | term => rfl
  | app _ _ ihFunction ihArgument =>
      simp only [SExpr.ofKernel, Reference.substitute, ihFunction, ihArgument]

/-- Exact agreement requires precisely the source's image-lookup domain.
Outside it the local operation refuses, while the historical operation defaults. -/
theorem substitution_iff (images : List Kernel.Preterm) (source result : Kernel.Preterm) :
    Kernel.Preterm.substitute (Kernel.Substitution.ofList images) source = some result ↔
      Reference.withinImages images.length (SExpr.ofKernel source) ∧
        Reference.substitute (images.map SExpr.ofKernel) (SExpr.ofKernel source) = SExpr.ofKernel result := by
  constructor
  · intro accepted
    exact ⟨(withinImages_iff source images.length).mpr
      ((Kernel.Preterm.substitute_ofList_defined_iff images source).mp ⟨result, accepted⟩),
      substitution_of_derivation (Kernel.Preterm.substitute_sound accepted)⟩
  · rintro ⟨domain, legacy⟩
    obtain ⟨computed, accepted⟩ := (Kernel.Preterm.substitute_ofList_defined_iff images source).mpr
      ((withinImages_iff source images.length).mp domain)
    have equal := (substitution_of_derivation (Kernel.Preterm.substitute_sound accepted)).symm.trans legacy
    have same : computed = result := by simpa using congrArg SExpr.toKernel equal
    simpa [same] using accepted

theorem substitution_refuses_iff (images : List Kernel.Preterm) (source : Kernel.Preterm) :
    Kernel.Preterm.substitute (Kernel.Substitution.ofList images) source = none ↔
      ¬ Reference.withinImages images.length (SExpr.ofKernel source) := by
  constructor
  · intro refused domain
    obtain ⟨result, accepted⟩ := (Kernel.Preterm.substitute_ofList_defined_iff images source).mpr
      ((withinImages_iff source images.length).mp domain)
    simp [refused] at accepted
  · intro missing
    cases computed : Kernel.Preterm.substitute (Kernel.Substitution.ofList images) source with
    | none => rfl
    | some result => exact False.elim (missing ((substitution_iff images source result).mp computed).1)

theorem fitsList_toKernel {environment : Env} {theory : Kernel.Theory}
    (related : EnvironmentRelated environment theory) (target : Context)
    {formal : Context} {images : List SExpr}
    (typed : List.Forall₂ (FitsBinder environment target) images formal) :
    List.Forall₂ (Kernel.Preterm.FitsBinder theory.termSignature (toContext target))
      (images.map SExpr.toKernel) (toContext formal) := by
  induction typed with
  | nil => exact .nil
  | cons fits _ ih => exact .cons ((fitsBinder_iff related target _ _).mp fits) ih

theorem typed_images_cover_source {environment : Env} {theory : Kernel.Theory}
    (related : EnvironmentRelated environment theory) {formal target remaining : Context}
    {images : List SExpr} {source : SExpr} {sort : Nat}
    (typed : Typed environment formal source remaining sort)
    (imagesTyped : List.Forall₂ (FitsBinder environment target) images formal) :
    Reference.withinImages images.length source := by
  obtain ⟨_, supported⟩ := (typed_toKernel related typed).support_exists
  have bounded : ∀ index, Kernel.Preterm.Occurs index source.toKernel → index < images.length := by
    intro index occurrence
    obtain ⟨binder, lookup⟩ := supported.lookup_exists index occurrence
    have bound := (List.getElem?_eq_some_iff.mp lookup).1
    simpa only [toContext, List.length_map, imagesTyped.length_eq] using bound
  simpa using (withinImages_iff source.toKernel images.length).mpr bounded

/-- Historical substitution preserves the common typing fragment when its
actual argument vector fits. This does not assert theorem independence. -/
theorem typed_substitution {environment : Env} {theory : Kernel.Theory}
    (related : EnvironmentRelated environment theory) {formal target remaining : Context}
    {images : List SExpr} {source : SExpr} {sort : Nat}
    (typed : Typed environment formal source remaining sort)
    (imagesTyped : List.Forall₂ (FitsBinder environment target) images formal) :
    Typed environment target (Reference.substitute images source) remaining sort := by
  have domain := typed_images_cover_source related typed imagesTyped
  have translatedDomain : Reference.withinImages (images.map SExpr.toKernel).length
      (SExpr.ofKernel source.toKernel) := by simpa using domain
  obtain ⟨result, substituted⟩ := (Kernel.Preterm.substitute_ofList_defined_iff
    (images.map SExpr.toKernel) source.toKernel).mpr
      ((withinImages_iff _ _).mp translatedDomain)
  have same : SExpr.ofKernel result = Reference.substitute images source := by
    have agrees := substitution_of_derivation (Kernel.Preterm.substitute_sound substituted)
    simpa [List.map_map, Function.comp_def] using agrees.symm
  have resultTyped := (typed_toKernel related typed).substitute
    (fitsList_toKernel related target imagesTyped) (Kernel.Preterm.substitute_sound substituted)
  simpa only [same, ofContext_toContext] using typed_ofKernel related resultTyped

open Mettapedia.GSLT.LanguageDef.DeterministicEquations (Applies naturalHost computationalHost)

/-- The existing authored raw-substitution entry checks the same exact domain
and submitted result; the historical default cannot manufacture an acceptance. -/
theorem authored_substitution_iff (images : List Kernel.Preterm) (source result : Kernel.Preterm) :
    Applies Presentation.substitutionProgram naturalHost "mm0:subst"
      [Presentation.encode source, Presentation.encodeValues images]
      (Presentation.encodeResult (some result)) ↔
      Reference.withinImages images.length (SExpr.ofKernel source) ∧
        Reference.substitute (images.map SExpr.ofKernel) (SExpr.ofKernel source) = SExpr.ofKernel result := by
  rw [Presentation.substitution_accepts_iff, ← Kernel.Preterm.substitute_eq_some_iff]
  exact substitution_iff images source result

theorem authored_substitution_refusal_iff (images : List Kernel.Preterm) (source : Kernel.Preterm) :
    Applies Presentation.substitutionProgram naturalHost "mm0:subst"
      [Presentation.encode source, Presentation.encodeValues images] (Presentation.encodeResult none) ↔
      ¬ Reference.withinImages images.length (SExpr.ofKernel source) := by
  rw [Presentation.substitution_refuses_iff, ← Kernel.Preterm.substitute_none_iff]
  exact substitution_refuses_iff images source

@[simp] theorem translated_argument_var_iff (arguments : List Kernel.Preterm) (position index : Nat) :
    (arguments.map SExpr.ofKernel)[position]? = some (.var index) ↔
      arguments[position]? = some (.var index) := by
  rw [List.getElem?_map]
  cases known : arguments[position]? with
  | none => simp
  | some argument => cases argument <;> simp [SExpr.ofKernel]

theorem images_membership_iff {target formal : Kernel.Context} {arguments : List Kernel.Preterm}
    {dependencies images : Finset Nat}
    (known : Kernel.FreeVariables.Images target formal arguments dependencies images) (index : Nat) :
    index ∈ images ↔ ∃ position ∈ dependencies,
      (arguments.map SExpr.ofKernel)[position]? = some (.var index) := by
  rw [← known.selected_eq, Kernel.FreeVariables.mem_selectedImages]
  simp only [translated_argument_var_iff]

theorem maybeFree_regular_iff (arguments : List Kernel.Preterm) (sort index : Nat)
    (dependencies : Finset Nat) :
    Reference.maybeFreeArgument (arguments.map SExpr.ofKernel) (.reg sort dependencies) index ↔
      index ∉ Kernel.FreeVariables.selectedImages arguments dependencies := by
  constructor
  · rintro ⟨otherSort, otherDependencies, same, survives⟩
    obtain ⟨sortEq, dependenciesEq⟩ := Binder.reg.inj same
    subst otherSort
    subst otherDependencies
    simpa only [Kernel.FreeVariables.mem_selectedImages, translated_argument_var_iff] using survives
  · intro survives
    refine ⟨sort, dependencies, rfl, ?_⟩
    simpa only [Kernel.FreeVariables.mem_selectedImages, translated_argument_var_iff] using survives

/-- Ordered regular slots contribute separately; a bound slot contributes no
free set of its own. The images used for subtraction remain the full vector. -/
theorem contributions_membership_iff {target full formal : Kernel.Context}
    {arguments : List Kernel.Preterm} {freeSets : List (Finset Nat)} {result : Finset Nat}
    (contributed : Kernel.FreeVariables.Contributions target full arguments formal freeSets result)
    (index : Nat) :
    index ∈ result ↔ ∃ binder free, (binder, free) ∈ formal.zip freeSets ∧ index ∈ free ∧
      Reference.maybeFreeArgument (arguments.map SExpr.ofKernel) (Binder.ofKernel binder) index := by
  induction contributed with
  | nil => simp
  | @bound sort rest free freeSets result _ ih =>
      constructor
      · intro member
        obtain ⟨binder, set, paired, occurs, survives⟩ := ih.mp member
        exact ⟨binder, set, by simp [paired], occurs, survives⟩
      · rintro ⟨binder, set, paired, occurs, survives⟩
        rcases List.mem_cons.mp paired with same | tail
        · have binderEq : binder = .bound sort := congrArg Prod.fst same
          simp [binderEq, Binder.ofKernel, Reference.maybeFreeArgument] at survives
        · exact ih.mpr ⟨binder, set, tail, occurs, survives⟩
  | @regular sort dependencies free bound result rest freeSets images _ ih =>
      have atSlot : Reference.maybeFreeArgument (arguments.map SExpr.ofKernel)
          (.reg sort dependencies) index ↔ index ∉ bound := by
        rw [maybeFree_regular_iff, images.selected_eq]
      constructor
      · intro member
        rcases Finset.mem_union.mp member with first | tail
        · obtain ⟨occurs, unbound⟩ := Finset.mem_sdiff.mp first
          exact ⟨.regular sort dependencies, free, by simp, occurs, atSlot.mpr unbound⟩
        · obtain ⟨binder, set, paired, occurs, survives⟩ := ih.mp tail
          exact ⟨binder, set, by simp [paired], occurs, survives⟩
      · rintro ⟨binder, set, paired, occurs, survives⟩
        rcases List.mem_cons.mp paired with same | tail
        · have binderEq : binder = .regular sort dependencies := congrArg Prod.fst same
          have setEq : set = free := congrArg Prod.snd same
          subst binder
          subst set
          exact Finset.mem_union.mpr (.inl (Finset.mem_sdiff.mpr ⟨occurs, atSlot.mp survives⟩))
        · exact Finset.mem_union.mpr (.inr (ih.mpr ⟨binder, set, tail, occurs, survives⟩))

private theorem contributed_slot_formula (formal : Kernel.Context) (arguments : List Kernel.Preterm)
    (freeSets : List (Finset Nat)) (index : Nat) :
    (∃ (position : Nat) (free : Prop) (binder : Binder),
      (freeSets.map (fun set => index ∈ set))[position]? = some free ∧
      (ofContext formal)[position]? = some binder ∧ free ∧
      Reference.maybeFreeArgument (arguments.map SExpr.ofKernel) binder index) ↔
    ∃ binder free, (binder, free) ∈ formal.zip freeSets ∧ index ∈ free ∧
      Reference.maybeFreeArgument (arguments.map SExpr.ofKernel) (Binder.ofKernel binder) index := by
  constructor
  · rintro ⟨position, free, binder, child, slot, occurs, survives⟩
    rw [List.getElem?_map] at child
    obtain ⟨set, setLookup, rfl⟩ := Option.map_eq_some_iff.mp child
    rw [ofContext, List.getElem?_map] at slot
    obtain ⟨sourceBinder, binderLookup, rfl⟩ := Option.map_eq_some_iff.mp slot
    exact ⟨sourceBinder, set, List.mem_of_getElem?
      (List.getElem?_zip_eq_some.mpr ⟨binderLookup, setLookup⟩), occurs, survives⟩
  · rintro ⟨binder, free, paired, occurs, survives⟩
    obtain ⟨position, pairedLookup⟩ := List.mem_iff_getElem?.mp paired
    obtain ⟨binderLookup, freeLookup⟩ := List.getElem?_zip_eq_some.mp pairedLookup
    refine ⟨position, index ∈ free, Binder.ofKernel binder, ?_, ?_, occurs, survives⟩
    · simp only [List.getElem?_map, freeLookup, Option.map_some]
    · simp only [ofContext, List.getElem?_map, binderLookup, Option.map_some]

/-- Full-spine membership correspondence with the specified disjunction.
Independent `FreeSpine` evidence supplies typing and resolved dependency
images; there is no assumption that the two membership predicates agree. -/
theorem specified_free_spine_iff {environment : Env} {theory : Kernel.Theory}
    (related : EnvironmentRelated environment theory) {context : Kernel.Context}
    {source : Kernel.Preterm} {arguments : List Kernel.Preterm}
    {freeSets : List (Finset Nat)} {result : Finset Nat}
    (free : Kernel.Preterm.FreeSpine theory.termSignature context source arguments freeSets result)
    (index : Nat) :
    Reference.specifiedFreeSpine environment (ofContext context) index (SExpr.ofKernel source)
      (arguments.map SExpr.ofKernel) (freeSets.map (fun set => index ∈ set)) ↔ index ∈ result := by
  induction free with
  | var supported =>
      exact (supported_membership_iff supported index).symm
  | @term symbol declaration arguments freeSets contributed returned known _ contributions images =>
      have selected : theory.termSignature symbol = some
          (termDecl (ofContext declaration.arguments) (declaration.resultSort, declaration.dependencies)) := by
        simpa only [termDecl_ofKernel] using known
      obtain ⟨storedBody, stored⟩ := (related.terms _ _ _).mpr selected
      have argumentFormula := (contributed_slot_formula declaration.arguments arguments freeSets index).trans
        (contributions_membership_iff contributions index).symm
      have returnedFormula := images_membership_iff images index
      constructor
      · rintro ⟨formal, sort, dependencies, body, declared, occurs⟩
        have same : termDecl formal (sort, dependencies) = declaration :=
          Option.some.inj (((related.terms _ _ _).mp ⟨body, declared⟩).symm.trans known)
        obtain ⟨formalEq, resultEq⟩ := (termDecl_eq_iff _ _ _).mp same
        have sortEq : sort = declaration.resultSort := congrArg Prod.fst resultEq
        have dependenciesEq : dependencies = declaration.dependencies := congrArg Prod.snd resultEq
        subst formal
        subst sort
        subst dependencies
        exact Finset.mem_union.mpr (occurs.imp argumentFormula.mp returnedFormula.mpr)
      · intro occurs
        refine ⟨_, _, _, storedBody, stored, ?_⟩
        exact (Finset.mem_union.mp occurs).imp argumentFormula.mpr returnedFormula.mp
  | app _ _ ihArgument ihFunction =>
      simp only [List.map_nil] at ihArgument
      simpa only [SExpr.ofKernel, Reference.specifiedFreeSpine, List.map_cons, ihArgument] using ihFunction

theorem specified_free_iff_membership {environment : Env} {theory : Kernel.Theory}
    (related : EnvironmentRelated environment theory) {context : Kernel.Context}
    {source : Kernel.Preterm} {free : Finset Nat}
    (account : Kernel.Preterm.FreeVars theory.termSignature context source free) (index : Nat) :
    Reference.specifiedFree environment (ofContext context) (SExpr.ofKernel source) index ↔ index ∈ free :=
  specified_free_spine_iff related account index

private theorem lookup_append {α : Type} {initial : List α} {index : Nat} {value : α}
    (known : initial[index]? = some value) (remaining : List α) :
    (initial ++ remaining)[index]? = some value := by
  induction initial generalizing index with
  | nil => simp at known
  | cons first rest ih =>
      cases index with
      | zero => simpa using known
      | succ index => exact ih (by simpa using known)

/-- Ordered context admission discharges dependency validity in the final
context, rather than imposing a fresh well-formedness premise on each use. -/
theorem admitted_context_dependencies {sorts : Kernel.SortSignature} {initial added : Kernel.Context}
    (admitted : Kernel.Context.Extension sorts initial added) :
    ∀ sort dependencies, Kernel.Binder.regular sort dependencies ∈ added →
      ∀ position ∈ dependencies, ∃ boundSort,
        (initial ++ added)[position]? = some (.bound boundSort) := by
  induction admitted with
  | nil => simp
  | @cons initial binder remaining admitted _ ih =>
      intro sort dependencies member position included
      rcases List.mem_cons.mp member with same | tail
      · subst binder
        cases admitted with
        | regular _ bounded =>
            obtain ⟨boundSort, known⟩ := bounded position included
            exact ⟨boundSort, lookup_append known _⟩
      · simpa only [List.append_assoc, List.singleton_append] using
          ih sort dependencies tail position included

theorem admitted_declaration_dependencies {sorts : Kernel.SortSignature} {declaration : Kernel.TermDecl}
    (admitted : declaration.Admissible sorts) : declaration.DependenciesBound := by
  refine ⟨admitted.dependencies, ?_⟩
  simpa using admitted_context_dependencies admitted.context

theorem checked_run_dependencies {theory : Kernel.Theory} {admissions : List Kernel.Admission}
    (checked : Kernel.Theory.run? {} admissions = some theory) :
    ∀ symbol declaration, theory.termSignature symbol = some declaration → declaration.DependenciesBound :=
  fun symbol declaration known =>
    admitted_declaration_dependencies ((Kernel.Theory.run_from_empty_wellFormed checked).terms symbol declaration known)

/-- The input-domain premise is typing alone; dependency validity is derived
from the actual checked history. Historical AND is not substituted for OR. -/
theorem checked_run_specified_free_iff {theory : Kernel.Theory} {admissions : List Kernel.Admission}
    (checked : Kernel.Theory.run? {} admissions = some theory) {context : Kernel.Context}
    {source : Kernel.Preterm} {sort : Nat}
    (typed : Typed (projectRun admissions) (ofContext context) (SExpr.ofKernel source) [] sort)
    (index : Nat) :
    Reference.specifiedFree (projectRun admissions) (ofContext context) (SExpr.ofKernel source) index ↔
      Kernel.Preterm.IsFree theory.termSignature context source index := by
  have related := checked_run_environment_related checked
  have localTyped : Kernel.Preterm.HasType theory.termSignature context source [] sort :=
    (checked_run_typing_iff checked context [] source sort).mp typed
  obtain ⟨free, computed⟩ := localTyped.freeVariables_exists (checked_run_dependencies checked)
  have account := (Kernel.Preterm.freeVariables_eq_some_iff _ _ _ _).mp computed
  rw [specified_free_iff_membership related account index]
  constructor
  · intro member; exact ⟨free, account, member⟩
  · rintro ⟨other, otherAccount, member⟩
    have same := Kernel.Preterm.FreeSpine.deterministic otherAccount account
    simpa only [same] using member

/-- Exact whole-set agreement with the existing authored free-variable entry,
on the saturated typing domain of a concrete checked theory. -/
theorem checked_run_authored_free_iff {theory : Kernel.Theory} {admissions : List Kernel.Admission}
    (checked : Kernel.Theory.run? {} admissions = some theory) {context : Kernel.Context}
    {source : Kernel.Preterm} {sort : Nat}
    (typed : Typed (projectRun admissions) (ofContext context) (SExpr.ofKernel source) [] sort)
    (claimed : Finset Nat) :
    (∃ indices, Applies Presentation.ComputationalFreeVariables.freeVariablesProgram computationalHost
      "mm0:free-variables" [Presentation.ComputationalTyping.encodeTable theory.terms,
        Presentation.ComputationalContext.encodeContext context, Presentation.encode source]
      (Presentation.ComputationalSupport.encodeResult (some indices)) ∧ indices.toFinset = claimed) ↔
      ∀ index, index ∈ claimed ↔ Reference.specifiedFree (projectRun admissions)
        (ofContext context) (SExpr.ofKernel source) index := by
  rw [Presentation.ComputationalFreeVariables.theory_free_variables_accepts_iff]
  constructor
  · intro accounted index
    exact (specified_free_iff_membership (checked_run_environment_related checked) accounted index).symm
  · intro exactMembers
    have localTyped := (checked_run_typing_iff checked context [] source sort).mp typed
    obtain ⟨free, computed⟩ := localTyped.freeVariables_exists (checked_run_dependencies checked)
    have account := (Kernel.Preterm.freeVariables_eq_some_iff _ _ _ _).mp computed
    have same : claimed = free := Finset.ext (fun index => (exactMembers index).trans
      (specified_free_iff_membership (checked_run_environment_related checked) account index))
    simpa only [same] using account

namespace Controls

private def neg : Kernel.TermDecl := ⟨[.regular 1 ∅], 1, ∅⟩
private def mark : Kernel.TermDecl := ⟨[.bound 0], 1, {0}⟩
private def all : Kernel.TermDecl := ⟨[.bound 0, .regular 1 {0}], 1, ∅⟩
private def foo : Kernel.TermDecl := ⟨[.bound 0, .bound 0, .regular 1 {0}], 1, {1}⟩
private def both : Kernel.TermDecl := ⟨[.bound 0, .regular 1 ∅], 1, {0}⟩
private def history : List Kernel.Admission :=
  [.sort 0 {}, .sort 1 { provable := true }, .term 7 neg, .term 8 mark,
    .term 9 all, .term 10 foo, .term 11 both]
private def theory : Kernel.Theory :=
  { sorts := [(1, { provable := true }), (0, {})],
    terms := [(11, both), (10, foo), (9, all), (8, mark), (7, neg)] }
private def target : Kernel.Context := [.bound 0, .regular 1 {0}]
private def negSource : Kernel.Preterm := .app (.term 7) (.var 1)
private def markSource : Kernel.Preterm := .app (.term 8) (.var 0)
private def allSource : Kernel.Preterm := .app (.app (.term 9) (.var 0)) (.var 1)
private def bothSource : Kernel.Preterm := .app (.app (.term 11) (.var 0)) (.var 1)

theorem history_checked : Kernel.Theory.run? {} history = some theory := by rfl

private theorem related : EnvironmentRelated (projectRun history) theory :=
  checked_run_environment_related history_checked

private theorem negFree : Kernel.Preterm.FreeVars theory.termSignature target negSource {0} :=
  (Kernel.Preterm.freeVariables_eq_some_iff _ _ _ _).mp (by decide +kernel)

private theorem markFree : Kernel.Preterm.FreeVars theory.termSignature target markSource {0} :=
  (Kernel.Preterm.freeVariables_eq_some_iff _ _ _ _).mp (by decide +kernel)

private theorem allFree : Kernel.Preterm.FreeVars theory.termSignature target allSource ∅ :=
  (Kernel.Preterm.freeVariables_eq_some_iff _ _ _ _).mp (by decide +kernel)

theorem regular_dependency_is_bound_support :
    Reference.hasVar (ofContext target) (.var 1) 0 :=
  (hasVar_ofKernel_iff target (.var 1) 0).mpr (.regular rfl (by simp))

theorem regular_index_is_not_its_dependency : ¬ Reference.hasVar (ofContext target) (.var 1) 1 := by
  simp [Reference.hasVar, target, ofContext, Binder.ofKernel]

theorem undefined_child_refuses_whole_support :
    Reference.hasVar (ofContext target) (.app1 (.var 0) (.var 99)) 0 ∧
      Kernel.Preterm.support? target (.app (.var 0) (.var 99)) = none := by
  constructor
  · exact .inl ⟨.bound 0, rfl, rfl⟩
  · decide +kernel

theorem simultaneous_swap :
    Reference.substitute [.var 1, .var 0] (.app1 (.var 0) (.var 1)) = .app1 (.var 1) (.var 0) ∧
      Kernel.Preterm.substitute (Kernel.Substitution.ofList [.var 1, .var 0])
        (.app (.var 0) (.var 1)) = some (.app (.var 1) (.var 0)) := by decide +kernel

theorem replacement_is_not_substituted_again :
    Reference.substitute [.app1 (.term 8) (.var 1), .term 7] (.var 0) = .app1 (.term 8) (.var 1) ∧
      Kernel.Preterm.substitute (Kernel.Substitution.ofList [.app (.term 8) (.var 1), .term 7])
        (.var 0) = some (.app (.term 8) (.var 1)) := by decide +kernel

theorem missing_image_historical_default : Reference.substitute [.term 7] (.var 1) = .var 0 := rfl

theorem missing_image_current_refusal :
    Kernel.Preterm.substitute (Kernel.Substitution.ofList [.term 7]) (.var 1) = none := rfl

theorem historical_default_does_not_authorize_result :
    ¬ Applies Presentation.substitutionProgram naturalHost "mm0:subst"
      [Presentation.encode (.var 1), Presentation.encodeValues [.term 7]]
      (Presentation.encodeResult (some (.var 0))) := by
  rw [authored_substitution_iff]
  simp [Reference.withinImages, SExpr.ofKernel]

theorem typed_binding_substitution_preserved :
    Typed (projectRun history) (ofContext ([.bound 0, .bound 0, .regular 1 {1}] : Kernel.Context))
      (Reference.substitute [.var 1, .var 2] (SExpr.ofKernel allSource)) [] 1 := by
  have typed : Typed (projectRun history) (ofContext target) (SExpr.ofKernel allSource) [] 1 :=
    (checked_run_typing_iff history_checked target [] allSource 1).mpr
      ((Kernel.Preterm.infer_eq_some_iff _ _ _ _ _).mp (by decide +kernel))
  have regular : FitsBinder (projectRun history)
      (ofContext ([.bound 0, .bound 0, .regular 1 {1}] : Kernel.Context)) (.var 2) (.reg 1 {0}) := by
    apply (fitsBinder_iff related _ _ _).mpr
    apply Kernel.Preterm.FitsBinder.regular
    simpa [SExpr.toKernel, Kernel.Binder.sort] using (Kernel.Preterm.HasType.var (signature := theory.termSignature)
      (context := [.bound 0, .bound 0, .regular 1 {1}])
      (binder := .regular 1 {1}) (index := 2) rfl)
  exact typed_substitution related typed (.cons ⟨1, rfl, rfl⟩ (.cons regular .nil))

/-- A genuine separator: surviving regular freedom does not require a returned dependency. -/
theorem surviving_regular_separates_historical_and :
    Reference.specifiedFree (projectRun history) (ofContext target) (SExpr.ofKernel negSource) 0 ∧
      ¬ Reference.historicalFree (projectRun history) (ofContext target) (SExpr.ofKernel negSource) 0 := by
  constructor
  · exact (specified_free_iff_membership related negFree 0).mpr (by simp)
  · intro historical
    simp only [Reference.historicalFree, negSource, SExpr.ofKernel,
      Reference.historicalFreeSpine] at historical
    obtain ⟨formal, sort, dependencies, body, declared, _, returned⟩ := historical
    have same : termDecl formal (sort, dependencies) = neg :=
      Option.some.inj (((related.terms _ _ _).mp ⟨body, declared⟩).symm.trans (by rfl))
    have empty : dependencies = ∅ := congrArg Kernel.TermDecl.dependencies same
    simp [empty] at returned

/-- The other disjunct separates too: a returned bound image needs no regular slot. -/
theorem returned_bound_separates_historical_and :
    Reference.specifiedFree (projectRun history) (ofContext target) (SExpr.ofKernel markSource) 0 ∧
      ¬ Reference.historicalFree (projectRun history) (ofContext target) (SExpr.ofKernel markSource) 0 := by
  constructor
  · exact (specified_free_iff_membership related markFree 0).mpr (by simp)
  · intro historical
    simp only [Reference.historicalFree, markSource, SExpr.ofKernel,
      Reference.historicalFreeSpine] at historical
    obtain ⟨formal, sort, dependencies, body, declared, contributed, _⟩ := historical
    have same : termDecl formal (sort, dependencies) = mark :=
      Option.some.inj (((related.terms _ _ _).mp ⟨body, declared⟩).symm.trans (by rfl))
    have formalEq : formal = [.bound 0] := by
      simpa [mark, ofContext, Binder.ofKernel] using ((termDecl_eq_iff _ _ _).mp same).1
    subst formal
    obtain ⟨position, free, binder, _, slot, _, survives⟩ := contributed
    cases position with
    | zero =>
        have binderEq : binder = .bound 0 := Option.some.inj slot.symm
        simp [binderEq, Reference.maybeFreeArgument] at survives
    | succ position => simp at slot

theorem two_contributing_branches_are_historically_positive :
    Reference.historicalFree (projectRun history) (ofContext target) (SExpr.ofKernel bothSource) 0 := by
  simp only [Reference.historicalFree, bothSource, SExpr.ofKernel, Reference.historicalFreeSpine]
  refine ⟨[.bound 0, .reg 1 ∅], 1, {0}, none,
    .term (by simp [projectRun, projectAdmission, history, both, ofContext, Binder.ofKernel]), ?_, ?_⟩
  · refine ⟨1, Reference.hasVar (ofContext target) (.var 1) 0, .reg 1 ∅,
      rfl, rfl, regular_dependency_is_bound_support, ?_⟩
    exact ⟨1, ∅, rfl, by simp⟩
  · exact ⟨0, by simp, rfl⟩

theorem binding_removes_only_free_occurrence :
    Reference.hasVar (ofContext target) (SExpr.ofKernel allSource) 0 ∧
      ¬ Reference.specifiedFree (projectRun history) (ofContext target) (SExpr.ofKernel allSource) 0 := by
  constructor
  · exact (hasVar_ofKernel_iff target allSource 0).mpr (.argument (.regular rfl (by simp)))
  · rw [specified_free_iff_membership related allFree]
    simp

theorem returned_and_surviving_union_keeps_both_positions :
    let context : Kernel.Context := [.bound 0, .bound 0, .bound 0, .regular 1 {0, 1, 2}]
    let source : Kernel.Preterm := .app (.app (.app (.term 10) (.var 0)) (.var 1)) (.var 3)
    Kernel.Preterm.freeVariables? theory.termSignature context source = some {1, 2} := by decide +kernel

theorem absent_bound_slot_is_still_an_occurrence :
    Reference.hasVar (ofContext target) (SExpr.ofKernel allSource) 0 ∧
      Kernel.Preterm.freeVariables? theory.termSignature target allSource = some ∅ :=
  ⟨(hasVar_ofKernel_iff target allSource 0).mpr (.function (.argument (.bound rfl))), allFree.eval⟩

theorem wrong_whole_free_set_is_not_authorized :
    ¬ ∃ indices, Applies Presentation.ComputationalFreeVariables.freeVariablesProgram computationalHost
      "mm0:free-variables" [Presentation.ComputationalTyping.encodeTable theory.terms,
        Presentation.ComputationalContext.encodeContext target, Presentation.encode negSource]
      (Presentation.ComputationalSupport.encodeResult (some indices)) ∧ indices.toFinset = ∅ := by
  rw [Presentation.ComputationalFreeVariables.theory_free_variables_accepts_iff]
  intro empty
  have same := Kernel.Preterm.FreeSpine.deterministic empty negFree
  simp at same

end Controls

end Mettapedia.Languages.MM0.Upstream.Lean3Dependencies
