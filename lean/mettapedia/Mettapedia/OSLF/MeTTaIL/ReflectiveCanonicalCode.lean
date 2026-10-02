import Mettapedia.OSLF.MeTTaIL.CollectionCode
import Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical

/-!
# The canonical form of a reflective presentation, on codes

The canonical representative compiled from a reflective presentation rewrites
a pattern from the leaves up.  At an application it orients the quote-drop
equation; at a closed parallel collection it splices, drops units, sorts and
removes an empty or singleton wrapper.  Both operations are primitive
recursive on the code of the node, so the canonical form is tracked by a
primitive recursive function on codes.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.PatternCode
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution

/-! ## The canonical form as a bottom-up rewriting -/

/-- The operation at a node whose sub-patterns are canonical. -/
def canonicalizeRoot (declaration : ReflectivePresentationDecl) : Pattern → Pattern
  | .apply constructor arguments =>
      finishNormalizeReflectiveApply declaration constructor arguments
  | .collection collectionType elements none =>
      if collectionType == declaration.parallelCollection then
        collapseParallel declaration (normalizeParallelElements declaration elements)
      else
        .collection collectionType elements none
  | pattern => pattern

/-- **The canonical form rewrites from the leaves up.** -/
theorem canonicalize_eq_bottomUp (declaration : ReflectivePresentationDecl)
    (pattern : Pattern) :
    canonicalize declaration pattern = pattern.bottomUp (canonicalizeRoot declaration) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => rfl
  | hfvar name => rfl
  | happly constructor arguments recurse =>
      simp only [canonicalize, canonicalizeList_eq_map, Pattern.bottomUp,
        Pattern.bottomUpList_eq_map, canonicalizeRoot]
      rw [List.map_congr_left recurse]
  | hlambda binder body recurse =>
      simp only [canonicalize, Pattern.bottomUp, recurse]
      rfl
  | hmultiLambda arity binders body recurse =>
      simp only [canonicalize, Pattern.bottomUp, recurse]
      rfl
  | hsubst body replacement recurseBody recurseReplacement =>
      simp only [canonicalize, Pattern.bottomUp, recurseBody, recurseReplacement]
      rfl
  | hcollection kind elements rest recurse =>
      cases rest with
      | none =>
          simp only [canonicalize, canonicalizeList_eq_map, Pattern.bottomUp,
            Pattern.bottomUpList_eq_map, canonicalizeRoot]
          rw [List.map_congr_left recurse]
      | some name =>
          simp only [canonicalize, canonicalizeList_eq_map, Pattern.bottomUp,
            Pattern.bottomUpList_eq_map, canonicalizeRoot]
          rw [List.map_congr_left recurse]

/-! ## The quote-drop equation, on codes -/

/-- Orient the quote-drop equation on the code of an application: a quote
whose one argument is a drop with one argument becomes that argument. -/
def quoteDropCode (quote drop code : ℕ) : ℕ :=
  if code.unpair.2.unpair.1 = quote ∧
      (Denumerable.ofNat (List ℕ) code.unpair.2.unpair.2).length = 1 ∧
      (Denumerable.ofNat (List ℕ) code.unpair.2.unpair.2).headI.unpair.1 = 2 ∧
      (Denumerable.ofNat (List ℕ) code.unpair.2.unpair.2).headI.unpair.2.unpair.1 = drop ∧
      (Denumerable.ofNat (List ℕ)
        (Denumerable.ofNat (List ℕ) code.unpair.2.unpair.2).headI.unpair.2.unpair.2).length = 1
  then
    (Denumerable.ofNat (List ℕ)
      (Denumerable.ofNat (List ℕ) code.unpair.2.unpair.2).headI.unpair.2.unpair.2).headI
  else code

theorem quoteDropCode_patternCode (declaration : ReflectivePresentationDecl)
    (constructor : String) (arguments : List Pattern) :
    quoteDropCode (stringCode declaration.quoteConstructor)
        (stringCode declaration.dropConstructor) (patternCode (.apply constructor arguments)) =
      patternCode (finishNormalizeReflectiveApply declaration constructor arguments) := by
  simp only [quoteDropCode, patternCode, Nat.unpair_pair, ofNat_patternListCode,
    stringCode_injective.eq_iff, finishNormalizeReflectiveApply, beq_iff_eq]
  by_cases quoted : constructor = declaration.quoteConstructor
  · match arguments with
    | [] => simp [quoted, patternCode]
    | [.bvar _] => simp [quoted, patternCode]
    | [.fvar _] => simp [quoted, patternCode]
    | [.lambda _ _] => simp [quoted, patternCode]
    | [.multiLambda _ _ _] => simp [quoted, patternCode]
    | [.subst _ _] => simp [quoted, patternCode]
    | [.collection _ _ _] => simp [quoted, patternCode]
    | [.apply drop []] => simp [quoted, patternCode, patternListCode]
    | [.apply drop [name]] =>
        by_cases dropped : drop = declaration.dropConstructor
        · simp [quoted, dropped, patternCode, ofNat_patternListCode]
        · simp [quoted, dropped, patternCode, ofNat_patternListCode,
            stringCode_injective.eq_iff]
    | [.apply drop (_ :: _ :: _)] =>
        simp [quoted, patternCode, ofNat_patternListCode]
    | _ :: _ :: _ => simp [quoted, patternCode]
  · simp [quoted, patternCode]

theorem quoteDropCode_primrec (quote drop : ℕ) : Primrec (quoteDropCode quote drop) := by
  have payload : Primrec fun code : ℕ => code.unpair.2 := Primrec.snd.comp Primrec.unpair
  have label : Primrec fun code : ℕ => code.unpair.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp payload)
  have arguments : Primrec fun code : ℕ =>
      Denumerable.ofNat (List ℕ) code.unpair.2.unpair.2 :=
    (Primrec.ofNat (List ℕ)).comp (Primrec.snd.comp (Primrec.unpair.comp payload))
  have inner : Primrec fun code : ℕ =>
      (Denumerable.ofNat (List ℕ) code.unpair.2.unpair.2).headI :=
    Primrec.list_headI.comp arguments
  have innerPayload : Primrec fun code : ℕ =>
      (Denumerable.ofNat (List ℕ) code.unpair.2.unpair.2).headI.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp inner)
  have innerArguments : Primrec fun code : ℕ =>
      Denumerable.ofNat (List ℕ)
        (Denumerable.ofNat (List ℕ) code.unpair.2.unpair.2).headI.unpair.2.unpair.2 :=
    (Primrec.ofNat (List ℕ)).comp (Primrec.snd.comp (Primrec.unpair.comp innerPayload))
  exact Primrec.ite
    ((Primrec.eq.comp label (Primrec.const quote)).and
      ((Primrec.eq.comp (Primrec.list_length.comp arguments) (Primrec.const 1)).and
        ((Primrec.eq.comp (Primrec.fst.comp (Primrec.unpair.comp inner)) (Primrec.const 2)).and
          ((Primrec.eq.comp (Primrec.fst.comp (Primrec.unpair.comp innerPayload))
              (Primrec.const drop)).and
            (Primrec.eq.comp (Primrec.list_length.comp innerArguments) (Primrec.const 1))))))
    (Primrec.list_headI.comp innerArguments) Primrec.id

/-! ## The operation at a node, on codes -/

/-- The operation at a node, on codes. -/
def canonicalizeRootCode (declaration : ReflectivePresentationDecl) (code : ℕ) : ℕ :=
  if code.unpair.1 = 2 then
    quoteDropCode (stringCode declaration.quoteConstructor)
      (stringCode declaration.dropConstructor) code
  else if IsClosedCollectionCode (collectionCode declaration.parallelCollection) code then
    normalizeCollectionCode (collectionCode declaration.parallelCollection)
      (patternCode (.apply declaration.parallelUnitConstructor [])) (collectionComponents code)
  else code

/-- **The operation at a node is tracked on codes.** -/
theorem canonicalizeRootCode_patternCode (declaration : ReflectivePresentationDecl)
    (pattern : Pattern) :
    canonicalizeRootCode declaration (patternCode pattern) =
      patternCode (canonicalizeRoot declaration pattern) := by
  cases pattern with
  | apply constructor arguments =>
      have tagged : (patternCode (.apply constructor arguments)).unpair.1 = 2 := by
        simp [patternCode]
      rw [canonicalizeRootCode, if_pos tagged, quoteDropCode_patternCode]
      rfl
  | collection kind elements rest =>
      have tagged : ¬ (patternCode (.collection kind elements rest)).unpair.1 = 2 := by
        simp [patternCode]
      rw [canonicalizeRootCode, if_neg tagged]
      by_cases parallel : ∃ members,
          Pattern.collection kind elements rest =
            .collection declaration.parallelCollection members none
      · obtain ⟨members, same⟩ := parallel
        obtain ⟨rfl, rfl, rfl⟩ : kind = declaration.parallelCollection ∧ elements = members ∧
            rest = none := by simpa using same
        rw [if_pos ((isClosedCollectionCode_patternCode _ _).mpr ⟨elements, rfl⟩),
          patternCode_closedCollection, collectionComponents_closedCollectionCode,
          normalizeCollectionCode_map (kind := declaration.parallelCollection)
            (splice := parallelSplice declaration) (collapse := collapseParallel declaration)
            (fun members => by simp [parallelSplice])
            (fun other notParallel =>
              parallelSplice_eq_singleton_of_not_parallel declaration other
                fun members same => notParallel ⟨members, same⟩)
            rfl (fun _ => rfl) (fun _ _ _ => rfl)]
        simp [canonicalizeRoot, normalizeParallelElements]
      · rw [if_neg (mt (isClosedCollectionCode_patternCode _ _).mp parallel)]
        cases rest with
        | some name => rfl
        | none =>
            have other : (kind == declaration.parallelCollection) = false := by
              apply beq_false_of_ne
              rintro rfl
              exact parallel ⟨elements, rfl⟩
            simp [canonicalizeRoot, other]
  | bvar index => simp [canonicalizeRootCode, IsClosedCollectionCode, patternCode, canonicalizeRoot]
  | fvar name => simp [canonicalizeRootCode, IsClosedCollectionCode, patternCode, canonicalizeRoot]
  | lambda binder body =>
      simp [canonicalizeRootCode, IsClosedCollectionCode, patternCode, canonicalizeRoot]
  | multiLambda arity binders body =>
      simp [canonicalizeRootCode, IsClosedCollectionCode, patternCode, canonicalizeRoot]
  | subst body replacement =>
      simp [canonicalizeRootCode, IsClosedCollectionCode, patternCode, canonicalizeRoot]

theorem canonicalizeRootCode_primrec (declaration : ReflectivePresentationDecl) :
    Primrec (canonicalizeRootCode declaration) :=
  Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.unpair) (Primrec.const 2))
    (quoteDropCode_primrec _ _)
    (Primrec.ite (isClosedCollectionCode_primrecPred _)
      ((normalizeCollectionCode_primrec _ _).comp collectionComponents_primrec) Primrec.id)

/-! ## The canonical form on codes -/

/-- The function on codes that tracks the canonical form. -/
def canonicalizeCode (declaration : ReflectivePresentationDecl) : ℕ → ℕ :=
  bottomUpCode (canonicalizeRootCode declaration)

/-- **The canonical form is primitive recursive on codes.** -/
theorem canonicalizeCode_primrec (declaration : ReflectivePresentationDecl) :
    Primrec (canonicalizeCode declaration) :=
  bottomUpCode_primrec (canonicalizeRootCode_primrec declaration)

/-- **The function on codes tracks the canonical form.** -/
theorem canonicalizeCode_patternCode (declaration : ReflectivePresentationDecl)
    (pattern : Pattern) :
    canonicalizeCode declaration (patternCode pattern) =
      patternCode (canonicalize declaration pattern) := by
  rw [canonicalize_eq_bottomUp]
  exact bottomUpCode_patternCode (canonicalizeRootCode_patternCode declaration) pattern

end Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
