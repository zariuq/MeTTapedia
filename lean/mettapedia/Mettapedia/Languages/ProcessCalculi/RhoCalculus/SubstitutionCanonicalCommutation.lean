import Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefAdequacy
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalTyping
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.PureBoundary

/-!
# Semantic COMM substitution commutes with canonicalization

The canonical stepper fires COMM on the canonical representative of a
process, so its contractum substitutes the canonical payload into the
canonical body.  Any other representative substitutes some other spelling of
the same payload into some other spelling of the same body.  This module
proves that the two contracta have the same canonical form, for the
well-sorted, binder-safe bodies of the closed rho carrier.

Two facts carry the argument.  First, canonicalization absorbs the quote/drop
normalization performed during substitution, so a name and its canonical
form behave identically at every substitution site: they are the same bound
variable, or neither is a bound variable.  Second, substitution is a bag
homomorphism (it fixes the unit and maps a parallel bag pointwise), so it
commutes with flattening, unit absorption, and sorting up to canonical form.
Binder safety is essential: a bound name never occurs under a quotation, so
substitution never has to look inside quoted code, which canonicalization
may reshape.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.SubstitutionCanonicalCommutation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.GSLT.LanguageDef.ReflectionExtension
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalTyping
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.PureBoundary

set_option autoImplicit false

/-! ## Canonicalization absorbs semantic normalization -/

theorem canonicalize_semanticNormalizeProc {process : Pattern} (free : HashSetFree process) :
    canonicalize (semanticNormalizeProc process) = canonicalize process :=
  canonicalize_eq_of_structuralCongruence (semanticNormalizeProc_sound process)
    ((hashSetFree_iff_of_structuralCongruence (semanticNormalizeProc_sound process)).mpr free)
    free

theorem canonicalize_semanticNormalizeName {name : Pattern} (free : HashSetFree name) :
    canonicalize (semanticNormalizeName name) = canonicalize name :=
  canonicalize_eq_of_structuralCongruence semanticNormalizeName_sound_struct
    ((hashSetFree_iff_of_structuralCongruence semanticNormalizeName_sound_struct).mpr free)
    free

theorem hashSetFree_canonicalize {pattern : Pattern} (free : HashSetFree pattern) :
    HashSetFree (canonicalize pattern) :=
  (hashSetFree_iff_of_structuralCongruence (canonicalize_sound pattern)).mp free

/-! ## Binder-safe names never normalize to a bound variable -/

/-- A bound variable is binder-safe only below the current depth; at depth
zero none is. -/
theorem not_bvar_of_binderSafe_zero {name : Pattern}
    (safe : binderSafeAt "NQuote" 0 name = true) (index : Nat) : name ≠ .bvar index := by
  intro equal
  subst equal
  simp [binderSafeAt] at safe

/-- Under a quotation, binder safety restarts at depth zero. -/
theorem binderSafe_of_quote {depth : Nat} {process : Pattern}
    (safe : binderSafeAt "NQuote" depth (.apply "NQuote" [process]) = true) :
    binderSafeAt "NQuote" 0 process = true := by
  simpa [binderSafeAt] using safe

/-- Binder safety of a drop is binder safety of its name. -/
theorem binderSafe_of_drop {depth : Nat} {name : Pattern}
    (safe : binderSafeAt "NQuote" depth (.apply "PDrop" [name]) = true) :
    binderSafeAt "NQuote" depth name = true := by
  simpa [binderSafeAt, binderSafeListAt] using safe

/-- Semantic name normalization of a well-sorted, binder-safe name other than
a bound variable is not a bound variable. -/
theorem semanticNormalizeName_ne_bvar :
    ∀ (bound : Nat) {free : FreeSortContext} {context : List String} (name : Pattern),
      sizeOf name ≤ bound →
      NameWellSorted rhoReflectivePresentation free context name →
      ∀ depth, binderSafeAt "NQuote" depth name = true →
      (∀ index, name ≠ .bvar index) →
      ∀ index, semanticNormalizeName name ≠ .bvar index := by
  intro bound
  induction bound with
  | zero =>
      intro free context name sizeBound
      cases name <;> simp at sizeBound
  | succ bound inductionHypothesis =>
      intro free context name sizeBound typed depth safe notBvar index
      cases typed with
      | bvar lookup => exact absurd rfl (notBvar _)
      | fvar lookup => simp [semanticNormalizeName]
      | @quote _ process processTyped =>
          simp only [rhoReflectivePresentation] at safe ⊢
          have processSafe := binderSafe_of_quote safe
          cases processTyped with
          | bvar lookup => simp [semanticNormalizeName]
          | fvar lookup => simp [semanticNormalizeName]
          | unit => simp [semanticNormalizeName, rhoReflectivePresentation]
          | @drop _ innerName innerTyped =>
              simp only [rhoReflectivePresentation] at processSafe ⊢
              have innerSafe := binderSafe_of_drop processSafe
              have innerNotBvar := not_bvar_of_binderSafe_zero innerSafe
              have innerSize : sizeOf innerName ≤ bound := by
                simp only [Pattern.apply.sizeOf_spec, List.cons.sizeOf_spec,
                  List.nil.sizeOf_spec] at sizeBound
                omega
              have := inductionHypothesis innerName innerSize innerTyped 0 innerSafe
                innerNotBvar index
              simpa [semanticNormalizeName] using this
          | output channelTyped payloadTyped =>
              simp [semanticNormalizeName, rhoReflectivePresentation]
          | input channelTyped bodyTyped =>
              simp [semanticNormalizeName, rhoReflectivePresentation]
          | parallel elementsTyped =>
              simp [semanticNormalizeName, rhoReflectivePresentation]

theorem semanticNormalizeName_ne_bvar_of_nameWellSorted
    {free : FreeSortContext} {context : List String} {name : Pattern}
    (typed : NameWellSorted rhoReflectivePresentation free context name)
    {depth : Nat} (safe : binderSafeAt "NQuote" depth name = true)
    (notBvar : ∀ index, name ≠ .bvar index) (index : Nat) :
    semanticNormalizeName name ≠ .bvar index :=
  semanticNormalizeName_ne_bvar (sizeOf name) name le_rfl typed depth safe notBvar index

/-- The canonical form of a well-sorted, binder-safe name other than a bound
variable is not a bound variable. -/
theorem canonicalize_ne_bvar_of_nameWellSorted
    {free : FreeSortContext} {context : List String} {name : Pattern}
    (typed : NameWellSorted rhoReflectivePresentation free context name)
    {depth : Nat} (safe : binderSafeAt "NQuote" depth name = true)
    (notBvar : ∀ index, name ≠ .bvar index) (index : Nat) :
    canonicalize name ≠ .bvar index := by
  cases typed with
  | bvar lookup => exact absurd rfl (notBvar _)
  | fvar lookup => simp [canonicalize]
  | @quote _ process processTyped =>
      simp only [rhoReflectivePresentation] at safe ⊢
      have processSafe := binderSafe_of_quote safe
      have canonicalSafe := canonicalize_binderSafeAt process 0 processSafe
      intro equal
      simp only [canonicalize] at equal
      unfold normalizeQuote at equal
      split at equal
      · rename_i innerName innerEq
        rw [innerEq] at canonicalSafe
        subst equal
        simp [binderSafeAt, binderSafeListAt] at canonicalSafe
      · exact Pattern.noConfusion equal

/-! ## Substitution sites agree between a name and its canonical form -/

/-- At a substitution site a well-sorted binder-safe name and its canonical
form are the same bound variable, or both are unmatched with canonically
equal results. -/
theorem semanticSubstNameMark_canonicalize
    {free : FreeSortContext} {context : List String} {name : Pattern}
    (typed : NameWellSorted rhoReflectivePresentation free context name)
    {depth : Nat} (safe : binderSafeAt "NQuote" depth name = true)
    (k : Nat) (replacement : Pattern) :
    (semanticSubstNameMark k replacement name).2 =
        (semanticSubstNameMark k replacement (canonicalize name)).2 ∧
      canonicalize (semanticSubstNameMark k replacement name).1 =
        canonicalize (semanticSubstNameMark k replacement (canonicalize name)).1 := by
  by_cases isBvar : ∃ index, name = .bvar index
  · obtain ⟨index, rfl⟩ := isBvar
    simp [canonicalize]
  · have notBvar : ∀ index, name ≠ .bvar index := fun index equal => isBvar ⟨index, equal⟩
    have nameFree : HashSetFree name := rhoNameWellSorted_hashSetFree typed
    have canonicalTyped := canonicalize_nameWellSorted context typed
    have canonicalSafe := canonicalize_binderSafeAt name depth safe
    have canonicalNotBvar := canonicalize_ne_bvar_of_nameWellSorted typed safe notBvar
    have unmatched : ∀ index, semanticNormalizeName name ≠ .bvar index :=
      semanticNormalizeName_ne_bvar_of_nameWellSorted typed safe notBvar
    have unmatchedCanonical :
        ∀ index, semanticNormalizeName (canonicalize name) ≠ .bvar index :=
      semanticNormalizeName_ne_bvar_of_nameWellSorted canonicalTyped canonicalSafe
        canonicalNotBvar
    have leftMark : semanticSubstNameMark k replacement name =
        (semanticNormalizeName name, false) := by
      unfold semanticSubstNameMark
      cases normalized : semanticNormalizeName name with
      | bvar index => exact absurd normalized (unmatched index)
      | fvar _ => rfl
      | apply _ _ => rfl
      | lambda _ _ => rfl
      | multiLambda _ _ _ => rfl
      | subst _ _ => rfl
      | collection _ _ _ => rfl
    have rightMark : semanticSubstNameMark k replacement (canonicalize name) =
        (semanticNormalizeName (canonicalize name), false) := by
      unfold semanticSubstNameMark
      cases normalized : semanticNormalizeName (canonicalize name) with
      | bvar index => exact absurd normalized (unmatchedCanonical index)
      | fvar _ => rfl
      | apply _ _ => rfl
      | lambda _ _ => rfl
      | multiLambda _ _ _ => rfl
      | subst _ _ => rfl
      | collection _ _ _ => rfl
    rw [leftMark, rightMark]
    refine ⟨rfl, ?_⟩
    simp only
    rw [canonicalize_semanticNormalizeName nameFree,
      canonicalize_semanticNormalizeName (hashSetFree_canonicalize nameFree),
      canonicalize_idempotent]

/-! ## Substitution is a bag homomorphism -/

theorem semanticSubstProcList_eq_map (k : Nat) (replacement : Pattern) :
    ∀ patterns : List Pattern,
      semanticSubstProcList k replacement patterns =
        patterns.map (semanticSubstProc k replacement)
  | [] => rfl
  | pattern :: patterns => by
      simp [semanticSubstProcList, semanticSubstProcList_eq_map k replacement patterns]

theorem semanticSubstProc_zero (k : Nat) (replacement : Pattern) :
    semanticSubstProc k replacement (.apply "PZero" []) = .apply "PZero" [] := by
  simp [semanticSubstProc]

theorem semanticSubstProc_bag (k : Nat) (replacement : Pattern) (elements : List Pattern) :
    semanticSubstProc k replacement (.collection .hashBag elements none) =
      .collection .hashBag (elements.map (semanticSubstProc k replacement)) none := by
  simp [semanticSubstProc, semanticSubstProcList_eq_map]

/-- Pointwise canonicity of a mapped list. -/
theorem isCanonicalList_map_canonicalize (transform : Pattern → Pattern) :
    ∀ patterns : List Pattern, IsCanonicalList (patterns.map (canonicalize ∘ transform))
  | [] => trivial
  | _ :: patterns =>
      ⟨canonicalize_isCanonical _, isCanonicalList_map_canonicalize transform patterns⟩

/-- The contents of a canonical element after a bag-homomorphic map, up to
permutation, are the contents of its spliced elements after the map. -/
theorem bagContents_singleton_hom (transform : Pattern → Pattern)
    (transformZero : transform (.apply "PZero" []) = .apply "PZero" [])
    (transformBag : ∀ elements, transform (.collection .hashBag elements none) =
      .collection .hashBag (elements.map transform) none)
    {element : Pattern} (canonical : IsCanonical element) :
    List.Perm (bagContents [canonicalize (transform element)])
      (bagContents ((bagContents [element]).map (canonicalize ∘ transform))) := by
  by_cases isZero : element = .apply "PZero" []
  · subst isZero
    simp [bagContents, bagSplice, transformZero, canonicalize, canonicalizeList]
  · by_cases isBag : ∃ elements, element = .collection .hashBag elements none
    · obtain ⟨elements, rfl⟩ := isBag
      have elementsNonZero : ∀ inner ∈ elements, inner ≠ .apply "PZero" [] := by
        intro inner membership
        exact (canonical.2.2.1 inner membership).1
      have leftContents :
          bagContents [canonicalize (transform (.collection .hashBag elements none))] =
            normalizeBagElements (elements.map (canonicalize ∘ transform)) := by
        rw [transformBag]
        simp only [canonicalize, canonicalizeList_eq_map, List.map_map]
        exact bagContents_collapse_normalized (isCanonicalList_map_canonicalize transform elements)
      have rightContents :
          bagContents ((bagContents [.collection .hashBag elements none]).map
            (canonicalize ∘ transform)) =
              bagContents (elements.map (canonicalize ∘ transform)) := by
        have contents : bagContents [.collection .hashBag elements none] = elements := by
          simp only [bagContents, List.flatMap_cons, List.flatMap_nil, bagSplice,
            List.append_nil]
          exact List.filter_eq_self.mpr (fun inner membership => by
            simpa using elementsNonZero inner membership)
        rw [contents]
      rw [leftContents, rightContents, normalizeBagElements_eq_sort_bagContents]
      exact sortPatterns_perm _ |>.symm
    · have splice : bagSplice element = [element] := by
        apply bagSplice_eq_singleton_of_not_bag
        intro elements equal
        exact isBag ⟨elements, equal⟩
      have contents : bagContents [element] = [element] := by
        simp [bagContents, splice, isZero]
      rw [contents]
      exact List.Perm.refl _

/-- Contents of a mapped canonical list, up to permutation, are the contents
of the mapped contents. -/
theorem bagContents_map_hom (transform : Pattern → Pattern)
    (transformZero : transform (.apply "PZero" []) = .apply "PZero" [])
    (transformBag : ∀ elements, transform (.collection .hashBag elements none) =
      .collection .hashBag (elements.map transform) none) :
    ∀ {elements : List Pattern}, IsCanonicalList elements →
      List.Perm (bagContents (elements.map (canonicalize ∘ transform)))
        (bagContents ((bagContents elements).map (canonicalize ∘ transform)))
  | [], _ => by simp [bagContents]
  | element :: elements, ⟨canonical, canonicalRest⟩ => by
      have headPerm := bagContents_singleton_hom transform transformZero transformBag canonical
      have tailPerm := bagContents_map_hom transform transformZero transformBag canonicalRest
      have leftSplit :
          bagContents ((element :: elements).map (canonicalize ∘ transform)) =
            bagContents [canonicalize (transform element)] ++
              bagContents (elements.map (canonicalize ∘ transform)) := by
        rw [List.map_cons, ← List.singleton_append, bagContents_append]
        rfl
      have rightSplit :
          bagContents ((bagContents (element :: elements)).map (canonicalize ∘ transform)) =
            bagContents ((bagContents [element]).map (canonicalize ∘ transform)) ++
              bagContents ((bagContents elements).map (canonicalize ∘ transform)) := by
        rw [← List.singleton_append, bagContents_append, List.map_append, bagContents_append]
      rw [leftSplit, rightSplit]
      exact headPerm.append tailPerm

/-- Canonical bag normalization commutes with a bag-homomorphic map on the
canonical elements: normalizing first changes nothing. -/
theorem normalizeBagElements_map_hom (transform : Pattern → Pattern)
    (transformZero : transform (.apply "PZero" []) = .apply "PZero" [])
    (transformBag : ∀ elements, transform (.collection .hashBag elements none) =
      .collection .hashBag (elements.map transform) none)
    {elements : List Pattern} (canonical : IsCanonicalList elements) :
    normalizeBagElements (elements.map (canonicalize ∘ transform)) =
      normalizeBagElements ((normalizeBagElements elements).map (canonicalize ∘ transform)) := by
  simp only [normalizeBagElements_eq_sort_bagContents]
  apply sortPatterns_eq_of_perm
  have sortedPerm : List.Perm
      ((sortPatterns (bagContents elements)).map (canonicalize ∘ transform))
      ((bagContents elements).map (canonicalize ∘ transform)) :=
    ((sortPatterns_perm (bagContents elements)).map _).symm
  exact (bagContents_map_hom transform transformZero transformBag canonical).trans
    (bagContents_perm sortedPerm).symm

/-! ## Substitution sites under two payloads -/

/-- A matched substitution site returns the replacement. -/
theorem semanticSubstNameMark_true {k : Nat} {replacement name name' : Pattern}
    (mark : semanticSubstNameMark k replacement name = (name', true)) :
    name' = replacement := by
  unfold semanticSubstNameMark at mark
  generalize semanticNormalizeName name = normalized at mark
  cases normalized with
  | bvar index =>
      by_cases equal : index = k
      · simp [equal] at mark
        exact mark.symm
      · simp [equal] at mark
  | fvar _ => simp at mark
  | apply _ _ => simp at mark
  | lambda _ _ => simp at mark
  | multiLambda _ _ _ => simp at mark
  | subst _ _ => simp at mark
  | collection _ _ _ => simp at mark

/-- Two canonically equal payloads produce the same match and canonically
equal names at every substitution site. -/
theorem semanticSubstNameMark_payload (k : Nat) {payload payload' : Pattern}
    (payloadEq : canonicalize payload = canonicalize payload') (name : Pattern) :
    (semanticSubstNameMark k (.apply "NQuote" [payload]) name).2 =
        (semanticSubstNameMark k (.apply "NQuote" [payload']) name).2 ∧
      canonicalize (semanticSubstNameMark k (.apply "NQuote" [payload]) name).1 =
        canonicalize (semanticSubstNameMark k (.apply "NQuote" [payload']) name).1 := by
  unfold semanticSubstNameMark
  generalize semanticNormalizeName name = normalized
  cases normalized with
  | bvar index =>
      by_cases equal : index = k
      · subst equal
        simp [canonicalize, payloadEq]
      · simp [equal]
  | fvar _ => exact ⟨rfl, rfl⟩
  | apply _ _ => exact ⟨rfl, rfl⟩
  | lambda _ _ => exact ⟨rfl, rfl⟩
  | multiLambda _ _ _ => exact ⟨rfl, rfl⟩
  | subst _ _ => exact ⟨rfl, rfl⟩
  | collection _ _ _ => exact ⟨rfl, rfl⟩

theorem canonicalize_semanticSubstName_payload (k : Nat) {payload payload' : Pattern}
    (payloadEq : canonicalize payload = canonicalize payload') (name : Pattern) :
    canonicalize (semanticSubstName k (.apply "NQuote" [payload]) name) =
      canonicalize (semanticSubstName k (.apply "NQuote" [payload']) name) :=
  (semanticSubstNameMark_payload k payloadEq name).2

/-- The drop case shared by both inductions: when the matched results agree
and the sites agree, the drop results are canonically equal. -/
theorem canonicalize_drop_of_marks {k : Nat} {replacement replacement' name name' : Pattern}
    (matchedAgree :
      canonicalize (semanticSubstProc k replacement (.apply "PDrop" [.bvar k])) =
        canonicalize (semanticSubstProc k replacement' (.apply "PDrop" [.bvar k])))
    (flags : (semanticSubstNameMark k replacement name).2 =
      (semanticSubstNameMark k replacement' name').2)
    (values : canonicalize (semanticSubstNameMark k replacement name).1 =
      canonicalize (semanticSubstNameMark k replacement' name').1) :
    canonicalize (semanticSubstProc k replacement (.apply "PDrop" [name])) =
      canonicalize (semanticSubstProc k replacement' (.apply "PDrop" [name'])) := by
  rcases leftMark : semanticSubstNameMark k replacement name with ⟨leftName, leftFlag⟩
  rcases rightMark : semanticSubstNameMark k replacement' name' with ⟨rightName, rightFlag⟩
  rw [leftMark] at flags values
  rw [rightMark] at flags values
  simp only at flags values
  subst flags
  cases leftFlag with
  | false =>
      simp only [semanticSubstProc, leftMark, rightMark]
      rw [canonicalize_apply_general "PDrop" _ (by simp),
        canonicalize_apply_general "PDrop" _ (by simp)]
      simp [canonicalizeList, values]
  | true =>
      have leftIs := semanticSubstNameMark_true leftMark
      have rightIs := semanticSubstNameMark_true rightMark
      subst leftIs
      subst rightIs
      simp only [semanticSubstProc, leftMark, rightMark]
      simpa [semanticSubstProc, semanticSubstNameMark, semanticNormalizeName] using matchedAgree

/-- Binder safety of an output is binder safety of its components. -/
theorem binderSafe_of_output {depth : Nat} {channel payload : Pattern}
    (safe : binderSafeAt "NQuote" depth (.apply "POutput" [channel, payload]) = true) :
    binderSafeAt "NQuote" depth channel = true ∧
      binderSafeAt "NQuote" depth payload = true := by
  simpa [binderSafeAt, binderSafeListAt] using safe

/-- Binder safety of an input is binder safety of its channel and of its body
one binder deeper. -/
theorem binderSafe_of_input {depth : Nat} {channel body : Pattern}
    (safe : binderSafeAt "NQuote" depth
      (.apply "PInput" [channel, .lambda none body]) = true) :
    binderSafeAt "NQuote" depth channel = true ∧
      binderSafeAt "NQuote" (depth + 1) body = true := by
  simpa [binderSafeAt, binderSafeListAt] using safe

/-- Binder safety of a parallel bag is pointwise. -/
theorem binderSafe_of_parallel {depth : Nat} {processes : List Pattern}
    (safe : binderSafeAt "NQuote" depth (.collection .hashBag processes none) = true) :
    binderSafeListAt "NQuote" depth processes = true := by
  simpa [binderSafeAt] using safe

mutual
  /-- Substituting canonically equal payloads into one well-sorted body gives
  canonically equal results. -/
  theorem canonicalize_semanticSubstProc_payload
      {free : FreeSortContext} {bound : List String} {process : Pattern}
      (typed : ProcWellSorted rhoReflectivePresentation free bound process)
      {payload payload' : Pattern} (payloadEq : canonicalize payload = canonicalize payload')
      (k : Nat) :
      canonicalize (semanticSubstProc k (.apply "NQuote" [payload]) process) =
        canonicalize (semanticSubstProc k (.apply "NQuote" [payload']) process) := by
    cases typed with
    | @bvar _ index lookup =>
        by_cases equal : index = k
        · subst equal
          simp [semanticSubstProc, canonicalize, payloadEq]
        · simp [semanticSubstProc, equal]
    | fvar lookup => simp [semanticSubstProc]
    | unit => simp [semanticSubstProc, rhoReflectivePresentation]
    | @drop _ name nameTyped =>
        simp only [rhoReflectivePresentation]
        obtain ⟨flags, values⟩ := semanticSubstNameMark_payload k payloadEq name
        exact canonicalize_drop_of_marks
          (by simpa [semanticSubstProc, semanticSubstNameMark, semanticNormalizeName]
            using payloadEq)
          flags values
    | @output _ channel payload₀ channelTyped payloadTyped =>
        simp only [rhoReflectivePresentation, semanticSubstProc]
        rw [canonicalize_apply_general "POutput" _ (by simp),
          canonicalize_apply_general "POutput" _ (by simp)]
        simp only [canonicalizeList]
        rw [canonicalize_semanticSubstName_payload k payloadEq channel,
          canonicalize_semanticSubstProc_payload payloadTyped payloadEq k]
    | @input _ channel body channelTyped bodyTyped =>
        simp only [rhoReflectivePresentation, semanticSubstProc]
        rw [canonicalize_apply_general "PInput" _ (by simp),
          canonicalize_apply_general "PInput" _ (by simp)]
        simp only [canonicalizeList, canonicalize]
        rw [canonicalize_semanticSubstName_payload k payloadEq channel,
          canonicalize_semanticSubstProc_payload bodyTyped payloadEq (k + 1)]
    | @parallel _ processes elementsTyped =>
        simp only [rhoReflectivePresentation, semanticSubstProc, canonicalize]
        rw [canonicalizeList_semanticSubstProcList_payload elementsTyped payloadEq k]

  /-- List form. -/
  theorem canonicalizeList_semanticSubstProcList_payload
      {free : FreeSortContext} {bound : List String} {processes : List Pattern}
      (typed : ProcListWellSorted rhoReflectivePresentation free bound processes)
      {payload payload' : Pattern} (payloadEq : canonicalize payload = canonicalize payload')
      (k : Nat) :
      canonicalizeList (semanticSubstProcList k (.apply "NQuote" [payload]) processes) =
        canonicalizeList (semanticSubstProcList k (.apply "NQuote" [payload']) processes) := by
    cases typed with
    | nil => rfl
    | cons processTyped processesTyped =>
        simp only [semanticSubstProcList, canonicalizeList]
        rw [canonicalize_semanticSubstProc_payload processTyped payloadEq k,
          canonicalizeList_semanticSubstProcList_payload processesTyped payloadEq k]
end

/-! ## Substitution into the canonical body -/

theorem isCanonicalList_map_canonicalize' :
    ∀ patterns : List Pattern, IsCanonicalList (patterns.map canonicalize)
  | [] => trivial
  | _ :: patterns => ⟨canonicalize_isCanonical _, isCanonicalList_map_canonicalize' patterns⟩

theorem normalizeBagElements_nil : normalizeBagElements [] = [] := by
  simp [normalizeBagElements, sortPatterns]

/-- A bag-homomorphic map applied to the collapsed canonical bag has the
canonical form of the map applied elementwise. -/
theorem canonicalize_hom_collapseBag (transform : Pattern → Pattern)
    (transformZero : transform (.apply "PZero" []) = .apply "PZero" [])
    (transformBag : ∀ elements, transform (.collection .hashBag elements none) =
      .collection .hashBag (elements.map transform) none)
    {elements : List Pattern} (canonical : IsCanonicalList elements) :
    canonicalize (transform (collapseBag (normalizeBagElements elements))) =
      collapseBag (normalizeBagElements (elements.map (canonicalize ∘ transform))) := by
  have hom := normalizeBagElements_map_hom transform transformZero transformBag canonical
  rw [hom]
  generalize normalizeBagElements elements = normalizedElements
  match normalizedElements with
  | [] =>
      show canonicalize (transform (.apply "PZero" [])) =
        collapseBag (normalizeBagElements [])
      rw [transformZero, normalizeBagElements_nil,
        canonicalize_apply_general "PZero" [] (by simp)]
      rfl
  | [element] =>
      show canonicalize (transform element) =
        collapseBag (normalizeBagElements [canonicalize (transform element)])
      have singleton := canonicalize_parallel_singleton (transform element)
      simp only [canonicalize, canonicalizeList] at singleton
      exact singleton.symm
  | first :: second :: rest =>
      show canonicalize (transform (.collection .hashBag (first :: second :: rest) none)) =
        collapseBag (normalizeBagElements
          ((first :: second :: rest).map (canonicalize ∘ transform)))
      rw [transformBag]
      simp only [canonicalize, canonicalizeList_eq_map, List.map_map]

/-- Substituting into a well-sorted, binder-safe body or into its canonical
form gives canonically equal results, together with the pointwise list form. -/
theorem canonicalize_semanticSubstProc_canonicalize_all
    {free : FreeSortContext} (replacement : Pattern) :
    (∀ {bound : List String} {process : Pattern},
      ProcWellSorted rhoReflectivePresentation free bound process →
      ∀ depth, binderSafeAt "NQuote" depth process = true →
        ∀ k, canonicalize (semanticSubstProc k replacement process) =
          canonicalize (semanticSubstProc k replacement (canonicalize process))) ∧
    (∀ {bound : List String} {processes : List Pattern},
      ProcListWellSorted rhoReflectivePresentation free bound processes →
      ∀ depth, binderSafeListAt "NQuote" depth processes = true →
        ∀ k, ∀ process ∈ processes,
          canonicalize (semanticSubstProc k replacement process) =
            canonicalize (semanticSubstProc k replacement (canonicalize process))) := by
  refine ⟨fun {bound} {process} typed => ?_, fun {bound} {processes} typed => ?_⟩
  all_goals
    first
    | apply ProcWellSorted.rec
        (presentation := rhoReflectivePresentation) (free := free) (t := typed)
        (motive_1 := fun _ _ _ => True)
        (motive_2 := fun _ process _ =>
          ∀ depth, binderSafeAt "NQuote" depth process = true →
            ∀ k, canonicalize (semanticSubstProc k replacement process) =
              canonicalize (semanticSubstProc k replacement (canonicalize process)))
        (motive_3 := fun _ processes _ =>
          ∀ depth, binderSafeListAt "NQuote" depth processes = true →
            ∀ k, ∀ process ∈ processes,
              canonicalize (semanticSubstProc k replacement process) =
                canonicalize (semanticSubstProc k replacement (canonicalize process)))
    | apply ProcListWellSorted.rec
        (presentation := rhoReflectivePresentation) (free := free) (t := typed)
        (motive_1 := fun _ _ _ => True)
        (motive_2 := fun _ process _ =>
          ∀ depth, binderSafeAt "NQuote" depth process = true →
            ∀ k, canonicalize (semanticSubstProc k replacement process) =
              canonicalize (semanticSubstProc k replacement (canonicalize process)))
        (motive_3 := fun _ processes _ =>
          ∀ depth, binderSafeListAt "NQuote" depth processes = true →
            ∀ k, ∀ process ∈ processes,
              canonicalize (semanticSubstProc k replacement process) =
                canonicalize (semanticSubstProc k replacement (canonicalize process)))
  all_goals
    try (intros; exact trivial)
  all_goals
    first
    | -- process bound variable
      (intro _ index _ _ _ k
       simp [canonicalize]
       done)
    | -- process free variable
      (intro _ _ _ _ _ k
       simp [canonicalize]
       done)
    | -- unit
      (intro _ _ _ k
       simp [semanticSubstProc, rhoReflectivePresentation, canonicalize, canonicalizeList]
       done)
    | -- drop
      (intro _ name nameTyped _ depth safe k
       simp only [rhoReflectivePresentation] at safe ⊢
       have nameSafe := binderSafe_of_drop safe
       obtain ⟨flags, values⟩ :=
         semanticSubstNameMark_canonicalize nameTyped nameSafe k replacement
       rw [canonicalize_apply_general "PDrop" _ (by simp)]
       simp only [canonicalizeList]
       exact canonicalize_drop_of_marks rfl flags values)
    | -- output
      (intro _ channel payload channelTyped _ _ payloadIH depth safe k
       simp only [rhoReflectivePresentation] at safe ⊢
       obtain ⟨channelSafe, payloadSafe⟩ := binderSafe_of_output safe
       have channelAgreement :=
         (semanticSubstNameMark_canonicalize channelTyped channelSafe k replacement).2
       rw [canonicalize_apply_general "POutput" _ (by simp)]
       simp only [canonicalizeList, semanticSubstProc]
       rw [canonicalize_apply_general "POutput" _ (by simp),
         canonicalize_apply_general "POutput" _ (by simp)]
       simp only [canonicalizeList, semanticSubstName]
       rw [channelAgreement, payloadIH depth payloadSafe k])
    | -- input
      (intro _ channel body channelTyped _ _ bodyIH depth safe k
       simp only [rhoReflectivePresentation] at safe ⊢
       obtain ⟨channelSafe, bodySafe⟩ := binderSafe_of_input safe
       have channelAgreement :=
         (semanticSubstNameMark_canonicalize channelTyped channelSafe k replacement).2
       rw [canonicalize_apply_general "PInput" _ (by simp)]
       simp only [canonicalizeList, canonicalize, semanticSubstProc]
       rw [canonicalize_apply_general "PInput" _ (by simp),
         canonicalize_apply_general "PInput" _ (by simp)]
       simp only [canonicalizeList, canonicalize, semanticSubstName]
       rw [channelAgreement, bodyIH (depth + 1) bodySafe (k + 1)])
    | -- parallel
      (intro _ processes _ listIH depth safe k
       simp only [rhoReflectivePresentation] at safe ⊢
       have elementsSafe := binderSafe_of_parallel safe
       have pointwise := listIH depth elementsSafe k
       have leftForm : canonicalize (semanticSubstProc k replacement
           (.collection .hashBag processes none)) =
             collapseBag (normalizeBagElements
               (processes.map (canonicalize ∘ semanticSubstProc k replacement))) := by
         simp only [semanticSubstProc_bag, canonicalize, canonicalizeList_eq_map, List.map_map]
       have rightForm : canonicalize (semanticSubstProc k replacement
           (canonicalize (.collection .hashBag processes none))) =
             collapseBag (normalizeBagElements
               ((processes.map canonicalize).map
                 (canonicalize ∘ semanticSubstProc k replacement))) := by
         simp only [canonicalize, canonicalizeList_eq_map]
         exact canonicalize_hom_collapseBag (semanticSubstProc k replacement)
           (semanticSubstProc_zero k replacement) (semanticSubstProc_bag k replacement)
           (isCanonicalList_map_canonicalize' processes)
       rw [leftForm, rightForm, List.map_map]
       congr 2
       exact List.map_congr_left fun process membership => pointwise process membership)
    | -- cons
      (intro _ process processes _ _ processIH listIH depth safe k element membership
       have componentsSafe : binderSafeAt "NQuote" depth process = true ∧
           binderSafeListAt "NQuote" depth processes = true := by
         simpa [binderSafeListAt] using safe
       simp only [List.mem_cons] at membership
       rcases membership with rfl | membership
       · exact processIH depth componentsSafe.1 k
       · exact listIH depth componentsSafe.2 k element membership)

theorem canonicalize_semanticSubstProc_canonicalize
    {free : FreeSortContext} {bound : List String} {process : Pattern}
    (typed : ProcWellSorted rhoReflectivePresentation free bound process)
    (replacement : Pattern) {depth : Nat}
    (safe : binderSafeAt "NQuote" depth process = true) (k : Nat) :
    canonicalize (semanticSubstProc k replacement process) =
      canonicalize (semanticSubstProc k replacement (canonicalize process)) :=
  (canonicalize_semanticSubstProc_canonicalize_all replacement).1 typed depth safe k

/-! ## The COMM contractum -/

/-- COMM substitution of the canonical payload into the canonical body has the
canonical form of COMM substitution of the original payload into the original
body, for well-sorted binder-safe bodies and hash-set-free payloads. -/
theorem canonicalize_semanticCommSubst_canonicalize
    {free : FreeSortContext} {bound : List String} {body payload : Pattern}
    (bodyTyped : ProcWellSorted rhoReflectivePresentation free bound body)
    {depth : Nat} (bodySafe : binderSafeAt "NQuote" depth body = true)
    (payloadFree : HashSetFree payload) :
    canonicalize (semanticCommSubst (canonicalize body) (canonicalize payload)) =
      canonicalize (semanticCommSubst body payload) := by
  unfold semanticCommSubst
  have payloadEq : canonicalize (semanticNormalizeProc (canonicalize payload)) =
      canonicalize (semanticNormalizeProc payload) := by
    rw [canonicalize_semanticNormalizeProc (hashSetFree_canonicalize payloadFree),
      canonicalize_idempotent, canonicalize_semanticNormalizeProc payloadFree]
  rw [canonicalize_semanticSubstProc_payload (canonicalize_procWellSorted bound bodyTyped)
    payloadEq 0]
  exact (canonicalize_semanticSubstProc_canonicalize bodyTyped
    (.apply "NQuote" [semanticNormalizeProc payload]) bodySafe 0).symm

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.SubstitutionCanonicalCommutation
