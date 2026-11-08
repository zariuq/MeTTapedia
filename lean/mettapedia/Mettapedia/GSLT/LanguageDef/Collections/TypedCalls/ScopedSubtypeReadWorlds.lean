import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ScopedSubtypeReadCoordinates

/-!
# Ordered subtype reads under extended private coordinates

Every candidate occurrence uses the existing freshener and full-row matcher.
Failed rows still advance the supply. Successful rows retain their exact
result before the next row is read. Coordinate extension fixes that retained
prefix, preserving duplicate and shared-variable occurrences.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ScopedSubtypeReadWorlds

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation
open TypeDependencyAdmission TypeReadWorlds ScopedSubtypeReadCoordinates ScopedSubtypeReads
open TypeReadSupply (Supply fresh remember)
open RetainedTypePayloads (ExternalView)

theorem rows_append (world : ExternalView) (input : Atom) (resultName : String)
    (before after : List Atom) (supply : Supply) :
    rows world input resultName (before ++ after) supply =
      let first := rows world input resultName before supply
      let second := rows world input resultName after first.2
      (first.1 ++ second.1, second.2) := by
  induction before generalizing supply with
  | nil => simp [rows]
  | cons row rest ih =>
      simp only [List.cons_append, rows]
      split
      · rw [ih]
        simp only [List.append_assoc]
      · exact ih supply

theorem one_row_coordinates (world : ExternalView) (previous : Equiv.Perm String)
    (live : List String) (input : Atom) (resultName : String)
    (inputSafe : resourceFree input = true) (inputCovered : TypeSubst.typeVars input ⊆ live)
    (resultLive : resultName ∈ live) (row : Atom)
    (rowSafe : possibleRow row = true → resourceFree row = true)
    (first second : Supply) (firstProtected : live ⊆ first.used)
    (secondProtected : live.map previous ⊆ second.used) :
    ResultRelated previous live (rows world input resultName [row] first)
      (rows world (renameAtom previous input) (previous resultName) [row] second) := by
  by_cases possible : possibleRow row = true
  · obtain ⟨next, agrees, carried⟩ :=
      extend_allocated_family previous live first second firstProtected secondProtected [row]
    have rowCarried : (fresh second row).1 = renameAtom next (fresh first row).1 := by
      simpa only [TypeReadSupply.freshList, List.map_cons, List.map_nil, List.cons.injEq, and_true] using carried
    have sameInput := retained_term_unchanged previous next live agrees input inputCovered
    have sameName := agrees resultName resultLive
    have leftSafe : resourceFree (fresh first row).1 = true := by
      rw [TypeReadSupply.fresh_resourceFree]
      exact rowSafe possible
    have replyCarried :
        TypeScopeClosure.subtypeRow world (renameAtom previous input) (previous resultName) (fresh second row).1 =
          (TypeScopeClosure.subtypeRow world input resultName (fresh first row).1).map (renameAtom next) := by
      rw [rowCarried, ← sameInput, ← sameName]
      exact subtypeRow_rename world next input resultName _ inputSafe leftSafe
    have firstKeeps : live ⊆ (fresh first row).2.used :=
      fun _ member => (TypeReadSupply.fresh_remembers first row).1 (firstProtected member)
    have secondKeeps : live.map next ⊆ (fresh second row).2.used := by
      intro name member
      obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
      rw [agrees original present]
      exact (TypeReadSupply.fresh_remembers second row).1
        (secondProtected (List.mem_map.mpr ⟨original, present, rfl⟩))
    cases found : TypeScopeClosure.subtypeRow world input resultName (fresh first row).1 with
    | none =>
        have related := (empty_related next live _ _ firstKeeps secondKeeps).change_base agrees
        simpa only [rows, if_pos possible, found, replyCarried, Option.map_none,
          Option.toList_none, List.nil_append] using related
    | some result =>
        have related := (remember_related next live _ _ firstKeeps secondKeeps [result]).change_base agrees
        simpa only [rows, if_pos possible, found, replyCarried, Option.map_some,
          Option.toList_some, List.map_cons, List.map_nil, List.append_nil] using related
  · simpa only [rows, if_neg possible] using empty_related previous live first second firstProtected secondProtected

/-- Induction follows the actual state-threaded row scan. A later freshener
must preserve the entire previously returned family, not only the original
input, so duplicate answers and aliases keep one common naming map. -/
theorem rows_coordinates (world : ExternalView) (sourceRows : List Atom)
    (safe : ScopedSubtypeReadSafety.RowsSafe sourceRows) :
    ∀ (previous : Equiv.Perm String) (live : List String) (input : Atom) (resultName : String),
      resourceFree input = true → TypeSubst.typeVars input ⊆ live → resultName ∈ live →
      ∀ first second : Supply, live ⊆ first.used → live.map previous ⊆ second.used →
        ResultRelated previous live (rows world input resultName sourceRows first)
          (rows world (renameAtom previous input) (previous resultName) sourceRows second) := by
  induction sourceRows with
  | nil =>
      intro previous live input resultName _ _ _ first second firstProtected secondProtected
      exact empty_related previous live first second firstProtected secondProtected
  | cons row rest ih =>
      intro previous live input resultName inputSafe inputCovered resultLive first second firstProtected secondProtected
      let firstHead := rows world input resultName [row] first
      let secondHead := rows world (renameAtom previous input) (previous resultName) [row] second
      obtain ⟨middle, agrees, carried, firstKept, secondKept⟩ :=
        one_row_coordinates world previous live input resultName inputSafe inputCovered resultLive row
          (safe row (by simp)) first second firstProtected secondProtected
      have later := ih (ScopedSubtypeReadSafety.rowsSafe_tail safe) middle
        (live ++ atomListVariables firstHead.1) input resultName inputSafe
        (fun name member => List.mem_append_left _ (inputCovered member))
        (List.mem_append_left _ resultLive) firstHead.2 secondHead.2 firstKept secondKept
      have inputSame := retained_term_unchanged previous middle live agrees input inputCovered
      have resultSame := agrees resultName resultLive
      rw [inputSame, resultSame] at later
      have joined := append_related previous middle live firstHead.1 secondHead.1
        (rows world input resultName rest firstHead.2)
        (rows world (renameAtom previous input) (previous resultName) rest secondHead.2)
        agrees carried later
      rw [show row :: rest = [row] ++ rest from rfl, rows_append, rows_append]
      exact joined

open private atomVariables_eq_typeVars
  from Mettapedia.Languages.MeTTa.HE.EquationFreshening

/-- The real query first captures its input, then allocates the result name,
then scans candidate rows. None of those allocations is a fixed-key lookup. -/
theorem query_coordinates (world : ExternalView) (sourceRows : List Atom)
    (safe : ScopedSubtypeReadSafety.RowsSafe sourceRows)
    (previous : Equiv.Perm String) (live : List String) (base : String)
    (input : Atom) (inputSafe : resourceFree input = true)
    (first second : Supply) (firstProtected : live ⊆ first.used)
    (secondProtected : live.map previous ⊆ second.used) :
    ResultRelated previous (live ++ atomVariables input) (query world sourceRows base input first)
      (query world sourceRows base (renameAtom previous input) second) := by
  let protectedNames := live ++ atomVariables input
  let firstCaptured := remember first [input]
  let secondCaptured := remember second [renameAtom previous input]
  have firstCapturedKeeps : protectedNames ⊆ firstCaptured.used := by
    intro name member
    rcases List.mem_append.mp member with old | inputName
    · exact TypeReadSupply.remember_old first [input] (firstProtected old)
    · apply TypeReadSupply.remember_new first [input]
      simpa only [atomListVariables, List.append_nil] using inputName
  have secondCapturedKeeps : protectedNames.map previous ⊆ secondCaptured.used := by
    intro name member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    rcases List.mem_append.mp present with old | inputName
    · exact TypeReadSupply.remember_old second [renameAtom previous input]
        (secondProtected (List.mem_map.mpr ⟨original, old, rfl⟩))
    · apply TypeReadSupply.remember_new second [renameAtom previous input]
      simp only [atomListVariables, List.append_nil, TypeReadSupply.variables_rename]
      exact List.mem_map.mpr ⟨original, inputName, rfl⟩
  obtain ⟨middle, agrees, outputName⟩ := chosen_name_extension previous protectedNames
    firstCaptured secondCaptured firstCapturedKeeps secondCapturedKeeps base
  let firstChosen := chooseFreshName base firstCaptured.used firstCaptured.next
  let secondChosen := chooseFreshName base secondCaptured.used secondCaptured.next
  let firstStart : Supply := ⟨firstChosen.1 :: firstCaptured.used, firstChosen.2⟩
  let secondStart : Supply := ⟨secondChosen.1 :: secondCaptured.used, secondChosen.2⟩
  let nextLive := firstChosen.1 :: protectedNames
  have firstKeeps : nextLive ⊆ firstStart.used := by
    intro name member
    rcases List.mem_cons.mp member with rfl | old
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (firstCapturedKeeps old)
  have secondKeeps : nextLive.map middle ⊆ secondStart.used := by
    intro name member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    rcases List.mem_cons.mp present with rfl | old
    · change middle firstChosen.1 ∈ secondChosen.1 :: secondCaptured.used
      rw [outputName]
      exact List.mem_cons_self
    · rw [agrees original old]
      exact List.mem_cons_of_mem _ (secondCapturedKeeps (List.mem_map.mpr ⟨original, old, rfl⟩))
  have inputCovered : TypeSubst.typeVars input ⊆ protectedNames := by
    intro name member
    apply List.mem_append_right
    simpa only [atomVariables_eq_typeVars] using member
  have result := rows_coordinates world sourceRows safe middle nextLive input firstChosen.1
    inputSafe (fun _ member => List.mem_cons_of_mem _ (inputCovered member)) (List.mem_cons_self)
    firstStart secondStart firstKeeps secondKeeps
  have inputSame := retained_term_unchanged previous middle protectedNames agrees input inputCovered
  rw [inputSame, outputName] at result
  have smaller : protectedNames ⊆ nextLive := fun _ member => List.mem_cons_of_mem _ member
  have reduced := (result.restrict smaller).change_base
    agrees
  exact reduced

/-- The retained cache compares actual immutable ground payloads. At that
boundary, alpha transport becomes literal equality for arbitrary allocation
histories, even if unsuccessful candidate rows allocated private names. -/
theorem retained_query_equal (world : ExternalView) (sourceRows : List Atom)
    (safe : ScopedSubtypeReadSafety.RowsSafe sourceRows) (base : String)
    (input : Atom) (inputSafe : resourceFree input = true) (first second : Supply)
    (retained : RetainedTypePayloads.admittedList (query world sourceRows base input first).1 = true) :
    (query world sourceRows base input second).1 = (query world sourceRows base input first).1 := by
  have related := query_coordinates world sourceRows safe (Equiv.refl String) [] base input inputSafe
    first second (by simp) (by simp)
  obtain ⟨names, _, carried, _, _⟩ := related
  have inputFixed : renameAtom (Equiv.refl String) input = input := by
    rw [TypeFreshReadEquivalence.atom_rename_presentation]
    exact ScopeObservation.renameTypeVars_id input
  rw [inputFixed] at carried
  rw [carried, ← renameAtomList_eq_map]
  exact TypeRowFreshening.admittedList_rename names _ retained

namespace Controls

def external : ExternalView := fun tag key => .grounded (.custom tag key)
def first : Supply := ⟨["caller"], 0⟩
def second : Supply := ⟨["caller", "dead#1"], 9⟩
def repeated : List Atom :=
  [.expression [.symbol ":<", .symbol "A", .symbol "B"],
   .expression [.symbol ":<", .symbol "A", .symbol "B"]]

theorem actual_query_keeps_duplicate_supertypes :
    (query external repeated "output" (.symbol "A") first).1 = [.symbol "B", .symbol "B"] ∧
    (query external repeated "output" (.symbol "A") second).1 = [.symbol "B", .symbol "B"] := by cbv

def failedBefore : List Atom :=
  [.expression [.symbol ":<", .expression [.symbol "Wrong", .var "x"], .var "y"],
   .expression [.symbol ":<", .symbol "A", .symbol "B"]]

theorem failed_candidate_does_not_erase_a_later_answer :
    (query external failedBefore "output" (.symbol "A") first).1 = [.symbol "B"] := by cbv

theorem failed_candidate_still_allocates :
    (query external failedBefore "output" (.symbol "A") first).2.next > first.next := by cbv

def openRow : List Atom := [.expression [.symbol ":<", .symbol "A", .expression [.symbol "B", .var "x"]]]

theorem nonretained_result_exposes_private_coordinates :
    (query external openRow "output" (.symbol "A") first).1 ≠
      (query external openRow "output" (.symbol "A") second).1 := by
  cbv
  simp

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ScopedSubtypeReadWorlds
