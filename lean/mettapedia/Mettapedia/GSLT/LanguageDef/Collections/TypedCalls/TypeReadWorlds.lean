import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeCacheFreshReads
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.OpenFrameEffects

/-!
# Extending private coordinates after unequal allocation histories

A cache hit can skip private allocations. The two supplies therefore need
not have equal used-name sets or counters. Their next actual declaration
reads admit an extension of the previous coordinate map that preserves all
retained names. This extends the existing fresh-candidate theorem; it does
not replace the query semantics or equate the complete allocation states.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadWorlds

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Exact
open Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.ScopeObservation
open TypeDependencyAdmission TypeScopeMatcher TypeScopeRenaming TypeFreshReadEquivalence

theorem rename_agrees_on_support (first second : String → String) (atom : Atom)
    (same : ∀ name ∈ TypeSubst.typeVars atom, first name = second name) :
    renameAtom first atom = renameAtom second atom := by
  rw [atom_rename_presentation, atom_rename_presentation]
  exact renameTypeVars_congr_on_typeVars atom same

theorem rename_comp (first second : String → String) (atom : Atom) :
    renameAtom second (renameAtom first atom) = renameAtom (second ∘ first) atom := by
  simp only [atom_rename_presentation, renameTypeVars_comp]

theorem rename_inverse (names : Equiv.Perm String) (atom : Atom) :
    renameAtom names (renameAtom names.symm atom) = atom := by
  rw [rename_comp]
  have identity : ((names : String → String) ∘ names.symm) = id := by
    funext name
    exact names.apply_symm_apply name
  rw [identity, atom_rename_presentation, renameTypeVars_id]

/-- Align two private families while extending a possibly nonidentity
coordinate map on the retained interface. -/
theorem extend_variant_family (previous : Equiv.Perm String) (live : List String)
    (sources leftValues rightValues : List Atom)
    (left : ArgumentAlphaVariantsRel live sources leftValues)
    (right : ArgumentAlphaVariantsRel (live.map previous) sources rightValues) :
    ∃ next : Equiv.Perm String,
      (∀ name ∈ live, next name = previous name) ∧
      rightValues = leftValues.map (renameAtom next) := by
  have undone : (live.map previous).map previous.symm = live := by
    simp [List.map_map, Function.comp_def]
  have aligned : ArgumentAlphaVariantsRel live sources
      (rightValues.map (renameTypeVars previous.symm)) := by
    simpa only [undone] using right.rename_targets previous.symm
  obtain ⟨adjustment, fixes, carried⟩ := argumentAlphaVariants_public_fixed_permutation left aligned
  refine ⟨adjustment.trans previous, ?_, ?_⟩
  · intro name member
    change previous (adjustment name) = previous name
    rw [fixes name member]
  · have carriedAtoms :
        rightValues.map (renameAtom previous.symm) = leftValues.map (renameAtom adjustment) := by
      simpa only [show renameAtom previous.symm = renameTypeVars previous.symm
          from funext (atom_rename_presentation previous.symm),
        show renameAtom adjustment = renameTypeVars adjustment
          from funext (atom_rename_presentation adjustment)] using carried
    have forward := congrArg (fun values : List Atom => values.map (renameAtom previous)) carriedAtoms
    have combined (atom : Atom) :
        renameAtom previous (renameAtom adjustment atom) = renameAtom (adjustment.trans previous) atom :=
      rename_comp adjustment previous atom
    simp only [List.map_map, Function.comp_def, rename_inverse, combined] at forward
    change rightValues.map id = leftValues.map (renameAtom (adjustment.trans previous)) at forward
    simpa only [List.map_id] using forward

/-- Extra old allocations in either supply are harmless; only the retained
interface must already be protected in its corresponding coordinates. -/
theorem extend_allocated_family (previous : Equiv.Perm String) (live : List String)
    (first second : TypeReadSupply.Supply)
    (firstProtected : live ⊆ first.used)
    (secondProtected : live.map previous ⊆ second.used) (sources : List Atom) :
    ∃ next : Equiv.Perm String,
      (∀ name ∈ live, next name = previous name) ∧
      (TypeReadSupply.freshList second sources).1 =
        (TypeReadSupply.freshList first sources).1.map (renameAtom next) :=
  extend_variant_family previous live sources _ _
    ((TypeReadSupply.freshList_variants first sources).restrict (fun _ member => firstProtected member))
    ((TypeReadSupply.freshList_variants second sources).restrict (fun _ member => secondProtected member))

/-- A retained observed term keeps its former translation under the new
private map. This protects alias structure, not only its variable set. -/
theorem retained_term_unchanged (previous next : Equiv.Perm String) (live : List String)
    (agrees : ∀ name ∈ live, next name = previous name) (term : Atom)
    (covered : TypeSubst.typeVars term ⊆ live) :
    renameAtom next term = renameAtom previous term :=
  rename_agrees_on_support next previous term (fun name member => agrees name (covered member))

theorem variables_support (atom : Atom) (name : String) :
    name ∈ TypeSubst.typeVars atom ↔ name ∈ UnifyingFrames.support atom := by
  induction atom using Atom.rec
    (motive_2 := fun atoms => name ∈ TypeSubst.typeVarsList atoms ↔
      ∃ atom ∈ atoms, name ∈ UnifyingFrames.support atom) with
  | var other => simp [TypeSubst.typeVars, UnifyingFrames.support,
      UnifyAtoms.encode, Mettapedia.Logic.LP.Term.freeVars]
  | symbol _ => simp [TypeSubst.typeVars, UnifyingFrames.support,
      UnifyAtoms.encode, Mettapedia.Logic.LP.Term.freeVars]
  | grounded _ => simp [TypeSubst.typeVars, UnifyingFrames.support,
      UnifyAtoms.encode, Mettapedia.Logic.LP.Term.freeVars]
  | expression atoms ih => rw [TypeSubst.typeVars, ih, OpenFrameEffects.support_expression]
  | nil => simp [TypeSubst.typeVarsList]
  | cons atom atoms ih ihs =>
      simp only [TypeSubst.typeVarsList, List.mem_append, ih, ihs, List.mem_cons,
        exists_eq_or_imp]

abbrev Supported (live : List String) (state : TypeScopeMatcher.State) : Prop :=
  OpenFrameEffects.Local live.toFinset state

theorem initial_supported (live : List String) : Supported live Atom.var :=
  OpenFrameEffects.Local.identity live.toFinset

theorem supported_readout (live : List String) (state : TypeScopeMatcher.State)
    (supported : Supported live state) (previous next : Equiv.Perm String)
    (agrees : ∀ name ∈ live, next name = previous name) :
    renameState next state = renameState previous state := by
  funext observed
  by_cases present : previous.symm observed ∈ live
  · have inverse : next.symm observed = previous.symm observed := by
      apply next.injective
      rw [next.apply_symm_apply, agrees _ present, previous.apply_symm_apply]
    simp only [renameState, inverse]
    apply retained_term_unchanged previous next live agrees
    intro name member
    exact List.mem_toFinset.mp (supported.closed _ (List.mem_toFinset.mpr present)
      ((variables_support _ name).mp member))
  · have absent : next.symm observed ∉ live := by
      intro presentNext
      have equal : previous.symm observed = next.symm observed := by
        apply previous.injective
        rw [previous.apply_symm_apply, ← agrees _ presentNext, next.apply_symm_apply]
      exact present (equal.symm ▸ presentNext)
    have firstFixed := supported.fixes _ (by simpa only [List.mem_toFinset] using absent)
    have secondFixed := supported.fixes _ (by simpa only [List.mem_toFinset] using present)
    simp only [renameState, firstFixed, secondFixed, renameAtom,
      next.apply_symm_apply, previous.apply_symm_apply]

theorem supported_mono {live larger : List String} {state : TypeScopeMatcher.State}
    (supported : Supported live state) (included : live ⊆ larger) : Supported larger state := by
  constructor
  · intro name member
    by_cases present : name ∈ live.toFinset
    · exact fun other occurs => List.mem_toFinset.mpr
        (included (List.mem_toFinset.mp (supported.closed name present occurs)))
    · rw [supported.fixes name present]
      intro other occurs
      have same : other = name := by
        simpa [UnifyingFrames.support, UnifyAtoms.encode, Mettapedia.Logic.LP.Term.freeVars] using occurs
      simpa only [same] using member
  · intro name absent
    exact supported.fixes name (fun member => absent (List.mem_toFinset.mpr (included (List.mem_toFinset.mp member))))

theorem covered_support {live : List String} {atom : Atom}
    (covered : TypeSubst.typeVars atom ⊆ live) : UnifyingFrames.support atom ⊆ live.toFinset :=
  fun name member => List.mem_toFinset.mpr (covered ((variables_support atom name).mpr member))

theorem unify_preserves_support (world : RetainedTypePayloads.ExternalView)
    (live : List String) (state : TypeScopeMatcher.State)
    (supported : Supported live state) (safe : SafeState state)
    (actual expected : Atom) (actualSafe : resourceFree actual = true)
    (expectedSafe : resourceFree expected = true)
    (actualCovered : TypeSubst.typeVars actual ⊆ live)
    (expectedCovered : TypeSubst.typeVars expected ⊆ live)
    (after : TypeScopeMatcher.State) (matched : unify world state actual expected = some after) :
    Supported live after := by
  have leftSafe := substitute_resourceFree state safe actual actualSafe
  have rightSafe := substitute_resourceFree state safe expected expectedSafe
  have leftCovered := OpenFrameEffects.subst_support_subset supported.closed (covered_support actualCovered)
  have rightCovered := OpenFrameEffects.subst_support_subset supported.closed (covered_support expectedCovered)
  simp only [unify, observe_resourceFree world _ leftSafe, observe_resourceFree world _ rightSafe] at matched
  split at matched
  · cases Option.some.inj matched
    exact supported
  · simp only [Option.map_eq_some_iff] at matched
    obtain ⟨theta, unified, rfl⟩ := matched
    exact supported.compose (OpenFrameEffects.unify_local unified (Finset.union_subset leftCovered rightCovered))

theorem firstChoice_preserves_support (world : RetainedTypePayloads.ExternalView)
    (live : List String) (state : TypeScopeMatcher.State)
    (supported : Supported live state) (safe : SafeState state)
    (expected : Atom) (expectedSafe : resourceFree expected = true)
    (expectedCovered : TypeSubst.typeVars expected ⊆ live)
    (actuals : List Atom) (actualsSafe : resourceFreeList actuals = true)
    (actualsCovered : ∀ actual ∈ actuals, TypeSubst.typeVars actual ⊆ live)
    (after : TypeScopeMatcher.State)
    (selected : StampInference.firstResult (fun actual => unify world state actual expected) actuals = some after) :
    Supported live after := by
  obtain ⟨before, actual, later, shape, _, matched⟩ :=
    (StampInference.firstResult_some_iff _ _ _).mp selected
  have present : actual ∈ actuals := by simp [shape]
  exact unify_preserves_support world live state supported safe actual expected
    ((resourceFreeList_iff _).mp actualsSafe actual present) expectedSafe
    (actualsCovered actual present) expectedCovered after matched

/-- The next pair of supplies protects the enlarged live interface, so
the extension theorem can be used again after this read. -/
theorem extend_allocated_world (previous : Equiv.Perm String) (live : List String)
    (first second : TypeReadSupply.Supply)
    (firstProtected : live ⊆ first.used)
    (secondProtected : live.map previous ⊆ second.used) (sources : List Atom) :
    ∃ next : Equiv.Perm String,
      (∀ name ∈ live, next name = previous name) ∧
      (TypeReadSupply.freshList second sources).1 =
        (TypeReadSupply.freshList first sources).1.map (renameAtom next) ∧
      (live ++ atomListVariables (TypeReadSupply.freshList first sources).1) ⊆
        (TypeReadSupply.freshList first sources).2.used ∧
      (live ++ atomListVariables (TypeReadSupply.freshList first sources).1).map next ⊆
        (TypeReadSupply.freshList second sources).2.used := by
  obtain ⟨next, agrees, carried⟩ :=
    extend_allocated_family previous live first second firstProtected secondProtected sources
  refine ⟨next, agrees, carried, ?_, ?_⟩
  · intro name member
    rcases List.mem_append.mp member with old | fresh
    · exact TypeReadSupply.freshList_remembers first sources (firstProtected old)
    · exact TypeReadSupply.freshList_output_remembers first sources fresh
  · intro name member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    rcases List.mem_append.mp present with old | fresh
    · rw [agrees original old]
      exact TypeReadSupply.freshList_remembers second sources
        (secondProtected (List.mem_map.mpr ⟨original, old, rfl⟩))
    · apply TypeReadSupply.freshList_output_remembers second sources
      rw [carried, ← renameAtomList_eq_map, TypeReadSupply.variablesList_rename]
      exact List.mem_map.mpr ⟨original, fresh, rfl⟩

/-- Fresh replies transport the actual selected substitution under the
extended map, while the incoming caller state still uses the old map. -/
theorem allocated_firstChoice (world : RetainedTypePayloads.ExternalView)
    (previous : Equiv.Perm String) (live : List String)
    (first second : TypeReadSupply.Supply)
    (firstProtected : live ⊆ first.used)
    (secondProtected : live.map previous ⊆ second.used)
    (sources : List Atom) (sourcesSafe : resourceFreeList sources = true)
    (state : TypeScopeMatcher.State) (stateSafe : SafeState state) (stateSupported : Supported live state)
    (expected : Atom) (expectedSafe : resourceFree expected = true)
    (expectedCovered : TypeSubst.typeVars expected ⊆ live) :
    ∃ next : Equiv.Perm String,
      (∀ name ∈ live, next name = previous name) ∧
      (TypeReadSupply.freshList second sources).1 =
        (TypeReadSupply.freshList first sources).1.map (renameAtom next) ∧
      StampInference.firstResult
          (fun actual => unify world (renameState previous state) actual (renameAtom previous expected))
          (TypeReadSupply.freshList second sources).1 =
        (StampInference.firstResult (fun actual => unify world state actual expected)
          (TypeReadSupply.freshList first sources).1).map (renameState next) := by
  obtain ⟨next, agrees, carried⟩ :=
    extend_allocated_family previous live first second firstProtected secondProtected sources
  refine ⟨next, agrees, carried, ?_⟩
  have step := firstChoice_rename world next state stateSafe expected expectedSafe
    (TypeReadSupply.freshList first sources).1
    (TypeReadSupply.freshList_resourceFree first sources sourcesSafe)
  rw [supported_readout live state stateSupported previous next agrees,
    retained_term_unchanged previous next live agrees expected expectedCovered, ← carried] at step
  exact step

open private atomVariables_eq_typeVars atomListVariables_eq_typeVarsList
  from Mettapedia.Languages.MeTTa.HE.EquationFreshening

theorem list_rename_agrees (first second : Equiv.Perm String) (atoms : List Atom)
    (same : ∀ name ∈ atomListVariables atoms, first name = second name) :
    atoms.map (renameAtom first) = atoms.map (renameAtom second) := by
  apply List.map_congr_left
  intro atom present
  apply rename_agrees_on_support
  intro name occurs
  apply same name
  rw [atomListVariables_eq_typeVarsList]
  exact Freshness.typeVars_mem_typeVarsList_of_mem present name occurs

/-- The returned family and every retained name have one coherent map;
the complete private supplies need not be equal or bijective as sets. -/
def ResultRelated (previous : Equiv.Perm String) (live : List String)
    (first second : List Atom × TypeReadSupply.Supply) : Prop :=
  ∃ next : Equiv.Perm String,
    (∀ name ∈ live, next name = previous name) ∧
    second.1 = first.1.map (renameAtom next) ∧
    (live ++ atomListVariables first.1) ⊆ first.2.used ∧
    (live ++ atomListVariables first.1).map next ⊆ second.2.used

theorem empty_related (previous : Equiv.Perm String) (live : List String)
    (first second : TypeReadSupply.Supply) (firstProtected : live ⊆ first.used)
    (secondProtected : live.map previous ⊆ second.used) :
    ResultRelated previous live ([], first) ([], second) := by
  exact ⟨previous, fun _ _ => rfl, rfl,
    by simpa only [atomListVariables, List.append_nil] using firstProtected,
    by simpa only [atomListVariables, List.append_nil] using secondProtected⟩

theorem allocated_related (previous : Equiv.Perm String) (live : List String)
    (first second : TypeReadSupply.Supply) (firstProtected : live ⊆ first.used)
    (secondProtected : live.map previous ⊆ second.used) (sources : List Atom) :
    ResultRelated previous live (TypeReadSupply.freshList first sources)
      (TypeReadSupply.freshList second sources) :=
  extend_allocated_world previous live first second firstProtected secondProtected sources

/-- Publishing an already related reply protects every name it exposes.
It does not require retaining private names that the reply does not expose. -/
theorem remember_related (names : Equiv.Perm String) (live : List String)
    (first second : TypeReadSupply.Supply) (firstProtected : live ⊆ first.used)
    (secondProtected : live.map names ⊆ second.used) (types : List Atom) :
    ResultRelated names live (types, TypeReadSupply.remember first types)
      (types.map (renameAtom names), TypeReadSupply.remember second (types.map (renameAtom names))) := by
  refine ⟨names, fun _ _ => rfl, rfl, ?_, ?_⟩
  · intro name member
    rcases List.mem_append.mp member with old | exposed
    · exact TypeReadSupply.remember_old first types (firstProtected old)
    · exact TypeReadSupply.remember_new first types exposed
  · intro name member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    rcases List.mem_append.mp present with old | exposed
    · exact TypeReadSupply.remember_old second _
        (secondProtected (List.mem_map.mpr ⟨original, old, rfl⟩))
    · apply TypeReadSupply.remember_new second _
      rw [← renameAtomList_eq_map, TypeReadSupply.variablesList_rename]
      exact List.mem_map.mpr ⟨original, exposed, rfl⟩

theorem ResultRelated.change_base {previous middle : Equiv.Perm String} {live : List String}
    {first second : List Atom × TypeReadSupply.Supply}
    (related : ResultRelated middle live first second)
    (agrees : ∀ name ∈ live, middle name = previous name) : ResultRelated previous live first second := by
  obtain ⟨next, nextAgrees, carried, firstProtected, secondProtected⟩ := related
  exact ⟨next, fun name member => (nextAgrees name member).trans (agrees name member),
    carried, firstProtected, secondProtected⟩

theorem ResultRelated.restrict {previous : Equiv.Perm String} {live smaller : List String}
    {first second : List Atom × TypeReadSupply.Supply}
    (related : ResultRelated previous live first second) (included : smaller ⊆ live) :
    ResultRelated previous smaller first second := by
  obtain ⟨next, agrees, carried, firstProtected, secondProtected⟩ := related
  have scopeIncluded : smaller ++ atomListVariables first.1 ⊆ live ++ atomListVariables first.1 := by
    intro name member
    rcases List.mem_append.mp member with old | returned
    · exact List.mem_append_left _ (included old)
    · exact List.mem_append_right _ returned
  refine ⟨next, fun name member => agrees name (included member), carried,
    fun _ member => firstProtected (scopeIncluded member), ?_⟩
  intro name member
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  exact secondProtected (List.mem_map.mpr ⟨original, scopeIncluded present, rfl⟩)

/-- A later extension may rename its own private names but cannot rewrite
earlier returned aliases. Concatenation keeps their original occurrence order. -/
theorem append_related (previous middle : Equiv.Perm String) (live : List String)
    (firstPrefix secondPrefix : List Atom)
    (firstTail secondTail : List Atom × TypeReadSupply.Supply)
    (firstAgrees : ∀ name ∈ live, middle name = previous name)
    (prefixCarried : secondPrefix = firstPrefix.map (renameAtom middle))
    (later : ResultRelated middle (live ++ atomListVariables firstPrefix) firstTail secondTail) :
    ResultRelated previous live (firstPrefix ++ firstTail.1, firstTail.2)
      (secondPrefix ++ secondTail.1, secondTail.2) := by
  obtain ⟨next, agrees, carried, firstProtected, secondProtected⟩ := later
  have prefixUnchanged : firstPrefix.map (renameAtom next) = firstPrefix.map (renameAtom middle) :=
    list_rename_agrees next middle firstPrefix
      (fun name member => agrees name (List.mem_append_right _ member))
  refine ⟨next, fun name member => (agrees name (List.mem_append_left _ member)).trans (firstAgrees name member), ?_, ?_, ?_⟩
  · simp only [List.map_append, prefixUnchanged, ← prefixCarried, carried]
  · simpa only [atomListVariables_append, List.append_assoc] using firstProtected
  · simpa only [atomListVariables_append, List.append_assoc] using secondProtected

namespace Controls

def before : TypeReadSupply.Supply := ⟨["caller"], 0⟩
def afterSkipped : TypeReadSupply.Supply := ⟨["caller", "dead#1", "dead#2"], 7⟩
def schema : Atom := .expression [.symbol "Pair", .var "a", .var "a"]

theorem unequal_histories_are_not_equal_states : before ≠ afterSkipped := by decide

theorem unequal_histories_keep_caller_and_shared_schema :
    ∃ next : Equiv.Perm String, next "caller" = "caller" ∧
      (TypeReadSupply.freshList afterSkipped [schema]).1 =
        (TypeReadSupply.freshList before [schema]).1.map (renameAtom next) := by
  obtain ⟨next, fixes, shared⟩ := extend_allocated_family (Equiv.refl String) ["caller"]
    before afterSkipped (by simp [before]) (by simp [afterSkipped]) [schema]
  exact ⟨next, fixes "caller" (by simp), shared⟩

def callerState : TypeScopeMatcher.State := fun name =>
  if name = "caller" then .var "alias" else .var name

theorem caller_alias_is_supported : Supported ["caller", "alias"] callerState := by
  constructor
  · intro name member other occurs
    by_cases same : name = "caller"
    · have aliasEq : other = "alias" := by
        simpa [callerState, same, UnifyingFrames.support, UnifyAtoms.encode,
          Mettapedia.Logic.LP.Term.freeVars] using occurs
      simp [aliasEq]
    · have original : other = name := by
        simpa [callerState, same, UnifyingFrames.support, UnifyAtoms.encode,
          Mettapedia.Logic.LP.Term.freeVars] using occurs
      simpa [original] using member
  · intro name absent
    have different : name ≠ "caller" := by
      intro same
      subst name
      simp at absent
    simp [callerState, different]

theorem a_preserved_name_may_still_have_an_observable_alias :
    TypeScopeRenaming.renameState (Equiv.swap "alias" "other") callerState "caller" ≠
      TypeScopeRenaming.renameState (Equiv.refl String) callerState "caller" := by
  simp [TypeScopeRenaming.renameState, callerState, renameAtom, Equiv.swap_apply_of_ne_of_ne]

theorem pretending_the_alias_is_private_breaks_support :
    ¬Supported ["caller"] callerState := by
  intro supported
  have closed := supported.closed "caller" (by simp)
  have member : "alias" ∈ UnifyingFrames.support (callerState "caller") := by
    simp [callerState, UnifyingFrames.support, UnifyAtoms.encode, Mettapedia.Logic.LP.Term.freeVars]
  have impossible := closed member
  simp at impossible

theorem allocation_cannot_split_a_repeated_schema_variable :
    (TypeReadSupply.freshList before [schema]).1 =
      [.expression [.symbol "Pair", .var "a#0", .var "a#0"]] := by cbv

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadWorlds
