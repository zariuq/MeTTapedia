import Mettapedia.Languages.MM0.MeTTa.Formats.MMB.MMBMachineSoundness

/-!
# MMB source slots and the retained unification machine

The source decoder's slots are related to actual unifier heap pointers by
the existing kernel substitution judgment. Reserved source slots carry no
completed substitution evidence. Source order and pointer identity are
retained; this module does not introduce another unifier or expression checker.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.MMBUnificationSoundness

open Formats.MMB
open Kernel

/-- Each filled source slot denotes the actual pointer at the same heap
position after the chosen simultaneous substitution. -/
structure SlotsSubstitute (store : List Alloc) (substitution : Substitution)
    (slots : List (Option Preterm)) (heap : List (Nat × Bool)) : Prop where
  length : slots.length = heap.length
  filled : ∀ (index : Nat) (source : Preterm), slots[index]? = some (some source) →
    ∃ (position : Nat) (saved : Bool) (image : Preterm), heap[index]? = some (position, saved) ∧
      Soundness.decode store position = some image ∧
      Preterm.Substitutes substitution source image

theorem substitution_application (substitution : Substitution) (source image : Preterm)
    (sources images : List Preterm) (head : Preterm.Substitutes substitution source image)
    (children : List.Forall₂ (Preterm.Substitutes substitution) sources images) :
    Preterm.Substitutes substitution (Preterm.applyArgs source sources) (Preterm.applyArgs image images) := by
  induction children generalizing source image with
  | nil => exact head
  | cons child _ ih => exact ih _ _ (.app head child)

theorem SlotsSubstitute.reserve (store : List Alloc) (substitution : Substitution)
    (slots : List (Option Preterm)) (heap : List (Nat × Bool))
    (matching : SlotsSubstitute store substitution slots heap) (position : Nat) :
    SlotsSubstitute store substitution (slots ++ [none]) (heap ++ [(position, true)]) := by
  constructor
  · simp only [List.length_append, List.length_singleton, matching.length]
  · intro index source found
    by_cases earlier : index < slots.length
    · rw [List.getElem?_append_left earlier] at found
      obtain ⟨pointer, saved, image, pointerRead, imageRead, substituted⟩ := matching.filled index source found
      have heapEarlier : index < heap.length := by simpa [matching.length] using earlier
      exact ⟨pointer, saved, image, by simpa only [List.getElem?_append_left heapEarlier] using pointerRead,
        imageRead, substituted⟩
    · have inside := (List.getElem?_eq_some_iff.mp found).choose
      have last : index = slots.length := by
        simp only [List.length_append, List.length_singleton] at inside
        omega
      subst index
      simp at found

theorem SlotsSubstitute.append_filled (store : List Alloc) (substitution : Substitution)
    (slots : List (Option Preterm)) (heap : List (Nat × Bool))
    (matching : SlotsSubstitute store substitution slots heap)
    (position : Nat) (saved : Bool) (source image : Preterm)
    (decoded : Soundness.decode store position = some image)
    (substituted : Preterm.Substitutes substitution source image) :
    SlotsSubstitute store substitution (slots ++ [some source]) (heap ++ [(position, saved)]) := by
  constructor
  · simp only [List.length_append, List.length_singleton, matching.length]
  · intro index expression found
    by_cases earlier : index < slots.length
    · rw [List.getElem?_append_left earlier] at found
      obtain ⟨pointer, marked, value, pointerRead, imageRead, substitutionRead⟩ :=
        matching.filled index expression found
      have heapEarlier : index < heap.length := by simpa [matching.length] using earlier
      exact ⟨pointer, marked, value, by simpa only [List.getElem?_append_left heapEarlier] using pointerRead,
        imageRead, substitutionRead⟩
    · have inside := (List.getElem?_eq_some_iff.mp found).choose
      have last : index = slots.length := by
        simp only [List.length_append, List.length_singleton] at inside
        omega
      subst index
      have same : expression = source := by simpa using found.symm
      subst expression
      exact ⟨position, saved, image, by simp [matching.length], decoded, substituted⟩

theorem SlotsSubstitute.fill_reserved (store : List Alloc) (substitution : Substitution)
    (slots : List (Option Preterm)) (heap : List (Nat × Bool))
    (matching : SlotsSubstitute store substitution slots heap)
    (index position : Nat) (source image : Preterm)
    (reserved : slots[index]? = some none) (pointerRead : heap[index]? = some (position, true))
    (decoded : Soundness.decode store position = some image)
    (substituted : Preterm.Substitutes substitution source image) :
    SlotsSubstitute store substitution (slots.set index (some source)) heap := by
  constructor
  · simpa only [List.length_set] using matching.length
  · intro other expression found
    by_cases same : other = index
    · subst other
      have inside := (List.getElem?_eq_some_iff.mp reserved).choose
      rw [List.getElem?_set_self inside] at found
      have expressionSame : expression = source := by simpa using found.symm
      subst expression
      exact ⟨position, true, image, pointerRead, decoded, substituted⟩
    · rw [List.getElem?_set_ne (Ne.symm same)] at found
      exact matching.filled other expression found

/-- The initial formal variables substitute to the independently decoded
argument vector, at the exact public heap positions. -/
theorem SlotsSubstitute.initial (store : List Alloc) (positions : List Nat) (images : List Preterm)
    (decoded : positions.mapM (Soundness.decode store) = some images) :
    SlotsSubstitute store (Substitution.ofList images)
      (Statements.initial positions.length).slots (positions.map (·, false)) := by
  have related := MMBMachineSoundness.decoded_arguments store positions images decoded
  constructor
  · simp [Statements.initial]
  · intro index source found
    have inside : index < positions.length := by
      have bound := (List.getElem?_eq_some_iff.mp found).choose
      simpa [Statements.initial] using bound
    have imageInside : index < images.length := by simpa [related.length_eq] using inside
    have sourceRead : (Statements.initial positions.length).slots[index]? =
        some (some (.var index)) := by
      simp [Statements.initial, inside]
    have same : source = .var index := Option.some.inj (Option.some.inj (found.symm.trans sourceRead))
    subst source
    refine ⟨positions[index]'inside, false, images[index]'imageInside, ?_, ?_, .var ?_⟩
    · simp [List.getElem?_map, List.getElem?_eq_getElem inside]
    · exact related.get inside imageInside
    · exact List.getElem?_eq_getElem imageInside

theorem SlotsSubstitute.reference (store : List Alloc) (substitution : Substitution)
    (slots : List (Option Preterm)) (unifier after : Unifier) (mode : UMode)
    (matching : SlotsSubstitute store substitution slots unifier.heap)
    (index position : Nat) (rest : List Nat) (source : Preterm)
    (sourceRead : slots[index]? = some (some source))
    (stack : unifier.stack = position :: rest)
    (executed : unifyStep store mode unifier (.ref index) = some after) :
    ∃ image, Soundness.decode store position = some image ∧
      Preterm.Substitutes substitution source image ∧
      after = { unifier with stack := rest } := by
  obtain ⟨pointer, saved, image, pointerRead, imageRead, substituted⟩ := matching.filled index source sourceRead
  change (unifier.heap[index]?).bind _ = some after at executed
  rw [pointerRead, Option.bind_some] at executed
  change (match unifier.stack with
    | first :: remaining => if first = pointer then some { unifier with stack := remaining } else none
    | [] => none) = some after at executed
  rw [stack] at executed
  change (if position = pointer then some { unifier with stack := rest } else none) = some after at executed
  split at executed
  · rename_i samePointer
    subst pointer
    exact ⟨image, imageRead, substituted, (Option.some.inj executed).symm⟩
  · simp at executed

/-- Successful term unification expands the actual application's ordered
children and reserves a saved pointer before checking those children. -/
theorem unifyTerm_operands (store : List Alloc) (before after : Unifier)
    (term position : Nat) (save : Bool) (rest : List Nat)
    (stack : before.stack = position :: rest)
    (executed : unifyTerm store before term save = some after) :
    ∃ arguments type,
      store[position]? = some ⟨.app term arguments, type⟩ ∧
      after = { before with stack := (arguments ++ rest), heap := (if save then before.heap ++ [(position, true)] else before.heap) } := by
  simp only [unifyTerm, stack] at executed
  change (store[position]?).bind _ = some after at executed
  cases found : store[position]? with
  | none => simp [found] at executed
  | some allocation =>
      rw [found, Option.bind_some] at executed
      rcases allocation with ⟨node, type⟩
      cases node with
      | var index => simp at executed
      | app head arguments =>
          change (if head = term then some { before with stack := (arguments ++ rest), heap := (if save then before.heap ++ [(position, true)] else before.heap) }
            else none) = some after at executed
          split at executed
          · rename_i same
            subst head
            exact ⟨arguments, type, rfl, (Option.some.inj executed).symm⟩
          · simp at executed

theorem unifyTerm_saved_slot (store : List Alloc) (substitution : Substitution)
    (source : Statements.Decoding) (before after : Unifier)
    (matching : SlotsSubstitute store substitution source.slots before.heap)
    (term position : Nat) (rest : List Nat) (stack : before.stack = position :: rest)
    (executed : unifyTerm store before term true = some after) :
    SlotsSubstitute store substitution (source.slots ++ [none]) after.heap := by
  obtain ⟨arguments, type, found, same⟩ := unifyTerm_operands store before after term position true rest stack executed
  rw [same]
  exact matching.reserve store substitution source.slots before.heap position

theorem unifyTerm_fitted_arguments (signature : TermSignature) (context : Context)
    (store : List Alloc) (typed : MMBMachineSoundness.TypedStore signature context store)
    (before after : Unifier) (term position : Nat) (save : Bool) (rest : List Nat)
    (stack : before.stack = position :: rest)
    (executed : unifyTerm store before term save = some after) :
    ∃ arguments images declaration,
      signature term = some declaration ∧ arguments.mapM (Soundness.decode store) = some images ∧
      List.Forall₂ (Preterm.FitsBinder signature context) images declaration.arguments ∧
      arguments.length = declaration.arguments.length ∧
      after.stack = arguments ++ rest ∧
      Soundness.decode store position = some (Preterm.applyArgs (.term term) images) := by
  obtain ⟨arguments, type, found, same⟩ := unifyTerm_operands store before after term position save rest stack executed
  obtain ⟨images, declaration, childRead, decoded, declared, fitted, _⟩ :=
    MMBMachineSoundness.TypedStore.application signature context store typed position term arguments type found
  have related := MMBMachineSoundness.decoded_arguments store arguments images childRead
  exact ⟨arguments, images, declaration, declared, childRead, fitted,
    related.length_eq.trans fitted.length_eq, by rw [same], decoded⟩

/-- Relate the retained runner to a generic fold of its own actual steps.
The final empty-stack and statement-hypothesis guards are retained. -/
theorem unifyRun_fold (store : List Alloc) (mode : UMode) (before : Unifier) (commands : List UnifyCmd) :
    unifyRun store mode before commands =
      (commands.foldlM (fun unifier command => unifyStep store mode unifier command) before).bind
        (fun after => if after.stack = [] ∧ (mode ≠ .statement ∨ after.hyps = []) then some after else none) := by
  induction commands generalizing before with
  | nil => rfl
  | cons command commands ih =>
      cases first : unifyStep store mode before command with
      | none => simp [unifyRun, List.foldlM_cons, first]
      | some after => simpa [unifyRun, List.foldlM_cons, first] using ih after

theorem unifyRun_after_prefix (store : List Alloc) (mode : UMode)
    (before middle : Unifier) (first rest : List UnifyCmd)
    (executed : first.foldlM (fun unifier command => unifyStep store mode unifier command) before = some middle) :
    unifyRun store mode before (first ++ rest) = unifyRun store mode middle rest := by
  rw [unifyRun_fold, List.foldlM_append]
  simp only [executed]
  exact (unifyRun_fold store mode middle rest).symm

theorem unifyRun_prefix (store : List Alloc) (mode : UMode)
    (before after : Unifier) (first rest : List UnifyCmd)
    (accepted : unifyRun store mode before (first ++ rest) = some after) :
    ∃ middle, first.foldlM (fun unifier command => unifyStep store mode unifier command) before = some middle ∧
      unifyRun store mode middle rest = some after := by
  induction first generalizing before with
  | nil => exact ⟨before, rfl, accepted⟩
  | cons command commands ih =>
      cases stepRead : unifyStep store mode before command with
      | none => simp [unifyRun, stepRead] at accepted
      | some next =>
          have nextAccepted : unifyRun store mode next (commands ++ rest) = some after := by
            simpa [unifyRun, stepRead] using accepted
          obtain ⟨middle, firstRead, restRead⟩ := ih next nextAccepted
          exact ⟨middle, by simp [List.foldlM_cons, stepRead, firstRead], restRead⟩

theorem unifyTerm_heap_prefix (store : List Alloc) (before after : Unifier)
    (term : Nat) (save : Bool) (executed : unifyTerm store before term save = some after) :
    ∃ suffix, after.heap = before.heap ++ suffix := by
  cases stack : before.stack with
  | nil => simp [unifyTerm, stack] at executed
  | cons position rest =>
      obtain ⟨arguments, type, found, same⟩ :=
        unifyTerm_operands store before after term position save rest stack executed
      rw [same]
      cases save
      · exact ⟨[], by simp⟩
      · exact ⟨[(position, true)], rfl⟩

theorem unifyStep_heap_prefix (store : List Alloc) (mode : UMode)
    (before after : Unifier) (command : UnifyCmd)
    (executed : unifyStep store mode before command = some after) :
    ∃ suffix, after.heap = before.heap ++ suffix := by
  cases command with
  | term term => exact unifyTerm_heap_prefix store before after term false executed
  | termSave term => exact unifyTerm_heap_prefix store before after term true executed
  | ref index =>
      simp only [unifyStep] at executed
      change (before.heap[index]?).bind _ = some after at executed
      cases found : before.heap[index]? with
      | none => simp [found] at executed
      | some pair =>
          rcases pair with ⟨position, saved⟩
          rw [found, Option.bind_some] at executed
          split at executed
          · split at executed
            · have same := Option.some.inj executed
              subst after
              exact ⟨[], by simp⟩
            · simp at executed
          · simp at executed
  | dummy sort =>
      simp only [unifyStep] at executed
      split at executed
      · simp at executed
      · split at executed
        · rename_i position rest shape
          change (store[position]?).bind _ = some after at executed
          cases found : store[position]? with
          | none => simp [found] at executed
          | some allocation =>
              rw [found, Option.bind_some] at executed
              cases node : allocation.node with
              | app term arguments => simp [node] at executed
              | var index =>
                  rw [node] at executed
                  repeat' (split at executed)
                  all_goals try cases executed
                  all_goals exact ⟨[(position, false)], rfl⟩
        · simp at executed
  | hyp =>
      simp only [unifyStep] at executed
      repeat' (split at executed)
      all_goals try cases executed
      all_goals exact ⟨[], by simp⟩

/-- A successful prefix of actual unifier steps only appends heap entries. -/
theorem unifyFold_heap_prefix (store : List Alloc) (mode : UMode)
    (before after : Unifier) (commands : List UnifyCmd)
    (executed : commands.foldlM (fun unifier command => unifyStep store mode unifier command) before = some after) :
    ∃ suffix, after.heap = before.heap ++ suffix := by
  induction commands generalizing before with
  | nil =>
      have same : before = after := Option.some.inj executed
      subst after
      exact ⟨[], by simp⟩
  | cons command commands ih =>
      cases first : unifyStep store mode before command with
      | none => simp [List.foldlM_cons, first] at executed
      | some middle =>
          have rest : commands.foldlM (fun unifier command => unifyStep store mode unifier command) middle = some after := by
            simpa [List.foldlM_cons, first] using executed
          obtain ⟨firstSuffix, firstHeap⟩ := unifyStep_heap_prefix store mode before middle command first
          obtain ⟨restSuffix, restHeap⟩ := ih middle rest
          exact ⟨firstSuffix ++ restSuffix, by rw [restHeap, firstHeap, List.append_assoc]⟩

theorem unifyRun_heap_prefix (store : List Alloc) (mode : UMode)
    (before after : Unifier) (commands : List UnifyCmd)
    (accepted : unifyRun store mode before commands = some after) :
    ∃ suffix, after.heap = before.heap ++ suffix := by
  induction commands generalizing before with
  | nil =>
      simp only [unifyRun] at accepted
      split at accepted
      · have same := Option.some.inj accepted
        subst after
        exact ⟨[], by simp⟩
      · simp at accepted
  | cons command commands ih =>
      cases first : unifyStep store mode before command with
      | none => simp [unifyRun, first] at accepted
      | some middle =>
          have remainder : unifyRun store mode middle commands = some after := by
            simpa [unifyRun, first] using accepted
          obtain ⟨firstSuffix, firstHeap⟩ := unifyStep_heap_prefix store mode before middle command first
          obtain ⟨restSuffix, restHeap⟩ := ih middle remainder
          exact ⟨firstSuffix ++ restSuffix, by rw [restHeap, firstHeap, List.append_assoc]⟩

mutual

/-- The exact expression prefix read by the retained source decoder, when
accepted by actual unifier steps, denotes the kernel substitution of that
source expression. The public arity agreement is supplied independently. -/
theorem decodeExpr_unifies (signature : TermSignature) (context : Context)
    (store : List Alloc) (typed : MMBMachineSoundness.TypedStore signature context store)
    (arity : Nat → Option Nat)
    (arities : ∀ term declaration, signature term = some declaration → arity term = some declaration.arguments.length)
    (substitution : Substitution) (mode : UMode) (ordinary : mode ≠ .definition)
    (arguments fuel : Nat) (sourceBefore sourceAfter : Statements.Decoding)
    (commandsBefore rest : List UnifyCmd) (source : Preterm) (before after : Unifier)
    (position : Nat) (outer : List Nat)
    (decoded : Statements.decodeExpr arity arguments fuel sourceBefore (commandsBefore ++ rest) = some (source, sourceAfter, rest))
    (executed : commandsBefore.foldlM (fun unifier command => unifyStep store mode unifier command) before = some after)
    (stack : before.stack = position :: outer)
    (matching : SlotsSubstitute store substitution sourceBefore.slots before.heap) :
    ∃ image, Soundness.decode store position = some image ∧
      Preterm.Substitutes substitution source image ∧ after.stack = outer ∧
      SlotsSubstitute store substitution sourceAfter.slots after.heap ∧
      after.main = before.main ∧ after.hyps = before.hyps ∧
      sourceAfter.dummies = sourceBefore.dummies := by
  cases fuel with
  | zero => simp [Statements.decodeExpr] at decoded
  | succ fuel =>
      cases commandsBefore with
      | nil =>
          obtain ⟨slots, consumed, _, consumedRead, nonempty⟩ :=
            Soundness.decodeExpr_source_order arity arguments (fuel + 1) sourceBefore sourceAfter rest rest source decoded
          have empty : consumed = [] := List.append_cancel_right (bs := rest) (by simpa using consumedRead.symm)
          exact False.elim (nonempty empty)
      | cons command commandsBefore =>
          cases command with
          | hyp => simp [Statements.decodeExpr] at decoded
          | dummy sort =>
              simp [List.foldlM_cons, unifyStep, ordinary] at executed
          | ref index =>
              change ((sourceBefore.slots[index]?).bind id).bind
                (fun expression => some (expression, sourceBefore, commandsBefore ++ rest)) =
                some (source, sourceAfter, rest) at decoded
              cases slotRead : sourceBefore.slots[index]? with
              | none => simp [slotRead] at decoded
              | some value =>
                  cases value with
                  | none => simp [slotRead] at decoded
                  | some expression =>
                      simp only [slotRead, Option.bind_some, id_eq] at decoded
                      have same : expression = source ∧ sourceBefore = sourceAfter ∧ commandsBefore ++ rest = rest := by
                        simpa using decoded
                      rcases same with ⟨sameSource, sameState, sameRest⟩
                      subst source
                      subst sourceAfter
                      have empty : commandsBefore = [] := List.append_cancel_right (bs := rest) (by simpa using sameRest)
                      subst commandsBefore
                      have stepRead : unifyStep store mode before (.ref index) = some after := by
                        simpa [List.foldlM_cons] using executed
                      obtain ⟨image, imageRead, substituted, sameAfter⟩ :=
                        matching.reference store substitution sourceBefore.slots before after mode index position outer expression slotRead stack stepRead
                      subst after
                      exact ⟨image, imageRead, substituted, rfl, matching, rfl, rfl, rfl⟩
          | term term =>
              cases countRead : arity term with
              | none => simp [Statements.decodeExpr, countRead] at decoded
              | some count =>
                  cases children : Statements.decodeExprs arity arguments fuel count sourceBefore (commandsBefore ++ rest) with
                  | none => simp [Statements.decodeExpr, countRead, children] at decoded
                  | some value =>
                      rcases value with ⟨sources, next, remaining⟩
                      have same : Preterm.applyArgs (.term term) sources = source ∧ next = sourceAfter ∧ remaining = rest := by
                        simpa [Statements.decodeExpr, countRead, children] using decoded
                      rcases same with ⟨sameSource, sameState, sameRest⟩
                      subst source
                      subst sourceAfter
                      subst remaining
                      cases first : unifyStep store mode before (.term term) with
                      | none => simp [List.foldlM_cons, first] at executed
                      | some middle =>
                          have later : commandsBefore.foldlM (fun unifier command => unifyStep store mode unifier command) middle = some after := by
                            simpa [List.foldlM_cons, first] using executed
                          obtain ⟨positions, type, found, sameMiddle⟩ :=
                            unifyTerm_operands store before middle term position false outer stack first
                          subst middle
                          obtain ⟨images, declaration, imageRead, parentRead, declared, fitted, _⟩ :=
                            MMBMachineSoundness.TypedStore.application signature context store typed position term positions type found
                          have countSame : count = declaration.arguments.length := Option.some.inj (countRead.symm.trans (arities term declaration declared))
                          have lengths : positions.length = count :=
                            (MMBMachineSoundness.decoded_arguments store positions images imageRead).length_eq.trans (fitted.length_eq.trans countSame.symm)
                          obtain ⟨values, valuesRead, substituted, afterStack, afterSlots, afterMain, afterHyps, afterDummies⟩ :=
                            decodeExprs_unifies signature context store typed arity arities substitution mode ordinary arguments fuel count
                              sourceBefore next commandsBefore rest sources _ after positions outer children later rfl lengths matching
                          have equalImages : values = images := Option.some.inj (valuesRead.symm.trans imageRead)
                          subst values
                          exact ⟨Preterm.applyArgs (.term term) images, parentRead,
                            substitution_application substitution (.term term) (.term term) sources images (.term term) substituted,
                            afterStack, afterSlots, afterMain, afterHyps, afterDummies⟩
          | termSave term =>
              cases countRead : arity term with
              | none => simp [Statements.decodeExpr, countRead] at decoded
              | some count =>
                  let reserved : Statements.Decoding := { sourceBefore with slots := sourceBefore.slots ++ [none] }
                  cases children : Statements.decodeExprs arity arguments fuel count reserved (commandsBefore ++ rest) with
                  | none => simp [Statements.decodeExpr, countRead, reserved, children] at decoded
                  | some value =>
                      rcases value with ⟨sources, next, remaining⟩
                      let body := Preterm.applyArgs (.term term) sources
                      have same : body = source ∧ { next with slots := next.slots.set sourceBefore.slots.length (some body) } = sourceAfter ∧ remaining = rest := by
                        simpa [Statements.decodeExpr, countRead, reserved, body, children] using decoded
                      rcases same with ⟨sameSource, sameState, sameRest⟩
                      subst source
                      subst sourceAfter
                      subst remaining
                      cases first : unifyStep store mode before (.termSave term) with
                      | none => simp [List.foldlM_cons, first] at executed
                      | some middle =>
                          have later : commandsBefore.foldlM (fun unifier command => unifyStep store mode unifier command) middle = some after := by
                            simpa [List.foldlM_cons, first] using executed
                          obtain ⟨positions, type, found, sameMiddle⟩ :=
                            unifyTerm_operands store before middle term position true outer stack first
                          subst middle
                          obtain ⟨images, declaration, imageRead, parentRead, declared, fitted, _⟩ :=
                            MMBMachineSoundness.TypedStore.application signature context store typed position term positions type found
                          have countSame : count = declaration.arguments.length := Option.some.inj (countRead.symm.trans (arities term declaration declared))
                          have lengths : positions.length = count :=
                            (MMBMachineSoundness.decoded_arguments store positions images imageRead).length_eq.trans (fitted.length_eq.trans countSame.symm)
                          obtain ⟨values, valuesRead, substituted, afterStack, afterSlots, afterMain, afterHyps, afterDummies⟩ :=
                            decodeExprs_unifies signature context store typed arity arities substitution mode ordinary arguments fuel count
                              reserved next commandsBefore rest sources _ after positions outer children later rfl lengths
                              (matching.reserve store substitution sourceBefore.slots before.heap position)
                          have equalImages : values = images := Option.some.inj (valuesRead.symm.trans imageRead)
                          subst values
                          have parentSubstitution : Preterm.Substitutes substitution body (Preterm.applyArgs (.term term) images) :=
                            substitution_application substitution (.term term) (.term term) sources images (.term term) substituted
                          obtain ⟨extraSlots, _, slotsRead, _, _⟩ :=
                            Soundness.decodeExprs_source_order arity arguments fuel count reserved next (commandsBefore ++ rest) rest sources children
                          have reservation : next.slots[sourceBefore.slots.length]? = some none := by
                            rw [slotsRead]
                            simp [reserved, List.append_assoc]
                          obtain ⟨extraHeap, heapRead⟩ := unifyFold_heap_prefix store mode _ after commandsBefore later
                          have saved : after.heap[sourceBefore.slots.length]? = some (position, true) := by
                            rw [heapRead]
                            simp [matching.length, List.append_assoc]
                          have filled := afterSlots.fill_reserved store substitution next.slots after.heap sourceBefore.slots.length position body
                            (Preterm.applyArgs (.term term) images) reservation saved parentRead parentSubstitution
                          exact ⟨Preterm.applyArgs (.term term) images, parentRead, parentSubstitution,
                            afterStack, filled, afterMain, afterHyps, afterDummies⟩
termination_by fuel

/-- Child correspondence consumes the exact ordered vector, rather than a
zip truncated to whichever vector is shorter. -/
theorem decodeExprs_unifies (signature : TermSignature) (context : Context)
    (store : List Alloc) (typed : MMBMachineSoundness.TypedStore signature context store)
    (arity : Nat → Option Nat)
    (arities : ∀ term declaration, signature term = some declaration → arity term = some declaration.arguments.length)
    (substitution : Substitution) (mode : UMode) (ordinary : mode ≠ .definition)
    (arguments fuel count : Nat) (sourceBefore sourceAfter : Statements.Decoding)
    (commandsBefore rest : List UnifyCmd) (sources : List Preterm) (before after : Unifier)
    (positions outer : List Nat)
    (decoded : Statements.decodeExprs arity arguments fuel count sourceBefore (commandsBefore ++ rest) = some (sources, sourceAfter, rest))
    (executed : commandsBefore.foldlM (fun unifier command => unifyStep store mode unifier command) before = some after)
    (stack : before.stack = positions ++ outer) (lengths : positions.length = count)
    (matching : SlotsSubstitute store substitution sourceBefore.slots before.heap) :
    ∃ images, positions.mapM (Soundness.decode store) = some images ∧
      List.Forall₂ (Preterm.Substitutes substitution) sources images ∧ after.stack = outer ∧
      SlotsSubstitute store substitution sourceAfter.slots after.heap ∧
      after.main = before.main ∧ after.hyps = before.hyps ∧
      sourceAfter.dummies = sourceBefore.dummies := by
  cases count with
  | zero =>
      have same : [] = sources ∧ sourceBefore = sourceAfter ∧ commandsBefore ++ rest = rest := by
        simpa [Statements.decodeExprs] using decoded
      rcases same with ⟨sameSources, sameState, sameRest⟩
      subst sources
      subst sourceAfter
      have emptyPrefix : commandsBefore = [] := List.append_cancel_right (bs := rest) (by simpa using sameRest)
      subst commandsBefore
      have sameAfter : before = after := Option.some.inj executed
      subst after
      have emptyPositions : positions = [] := List.length_eq_zero_iff.mp lengths
      subst positions
      exact ⟨[], rfl, .nil, by simpa using stack, matching, rfl, rfl, rfl⟩
  | succ count =>
      cases fuel with
      | zero => simp [Statements.decodeExprs] at decoded
      | succ fuel =>
          cases first : Statements.decodeExpr arity arguments fuel sourceBefore (commandsBefore ++ rest) with
          | none => simp [Statements.decodeExprs, first] at decoded
          | some value =>
              rcases value with ⟨source, middleSource, remaining⟩
              cases others : Statements.decodeExprs arity arguments fuel count middleSource remaining with
              | none => simp [Statements.decodeExprs, first, others] at decoded
              | some value =>
                  rcases value with ⟨earlier, finish, following⟩
                  have same : source :: earlier = sources ∧ finish = sourceAfter ∧ following = rest := by
                    simpa [Statements.decodeExprs, first, others] using decoded
                  rcases same with ⟨sameSources, sameState, sameRest⟩
                  subst sources
                  subst sourceAfter
                  subst following
                  obtain ⟨_, firstCommands, _, firstCommandsRead, _⟩ :=
                    Soundness.decodeExpr_source_order arity arguments fuel sourceBefore middleSource (commandsBefore ++ rest) remaining source first
                  obtain ⟨_, otherCommands, _, otherCommandsRead, _⟩ :=
                    Soundness.decodeExprs_source_order arity arguments fuel count middleSource finish remaining rest earlier others
                  have prefixRead : commandsBefore = firstCommands ++ otherCommands := List.append_cancel_right (bs := rest) (by
                    rw [firstCommandsRead, otherCommandsRead, List.append_assoc])
                  subst commandsBefore
                  have firstDecoded : Statements.decodeExpr arity arguments fuel sourceBefore (firstCommands ++ remaining) =
                      some (source, middleSource, remaining) := by simpa [firstCommandsRead] using first
                  have othersDecoded : Statements.decodeExprs arity arguments fuel count middleSource (otherCommands ++ rest) =
                      some (earlier, finish, rest) := by simpa [otherCommandsRead] using others
                  rw [List.foldlM_append] at executed
                  obtain ⟨middle, firstExecuted, othersExecuted⟩ := Option.bind_eq_some_iff.mp executed
                  cases positions with
                  | nil => simp at lengths
                  | cons position positions =>
                      have tailLength : positions.length = count := by simpa using lengths
                      have firstStack : before.stack = position :: (positions ++ outer) := by simpa using stack
                      obtain ⟨image, imageRead, substituted, middleStack, middleSlots, middleMain, middleHyps, middleDummies⟩ :=
                        decodeExpr_unifies signature context store typed arity arities substitution mode ordinary arguments fuel
                          sourceBefore middleSource firstCommands remaining source before middle position (positions ++ outer)
                          firstDecoded firstExecuted firstStack matching
                      obtain ⟨images, imagesRead, othersSubstituted, afterStack, afterSlots, afterMain, afterHyps, afterDummies⟩ :=
                        decodeExprs_unifies signature context store typed arity arities substitution mode ordinary arguments fuel count
                          middleSource finish otherCommands rest earlier middle after positions outer othersDecoded othersExecuted
                          middleStack tailLength middleSlots
                      exact ⟨image :: images, by simp [imageRead, imagesRead], .cons substituted othersSubstituted,
                        afterStack, afterSlots, afterMain.trans middleMain, afterHyps.trans middleHyps,
                        afterDummies.trans middleDummies⟩
termination_by fuel

end

namespace Controls

private def declaration : TermDecl := ⟨[.regular 0 ∅], 0, ∅⟩
private def signature : TermSignature := fun term => if term = 0 then some declaration else none
private def context : Context := [.bound 0, .bound 0, .bound 0]
private def variableType : ExprType := ⟨0, true, {2}⟩
private def applicationType : ExprType := ⟨0, false, {2}⟩
private def store : List Alloc :=
  [⟨.var 2, variableType⟩, ⟨.app 0 [0], applicationType⟩, ⟨.app 0 [1], applicationType⟩]
private def sourceInner : Preterm := .app (.term 0) (.var 0)
private def sourceOuter : Preterm := .app (.term 0) sourceInner
private def imageInner : Preterm := .app (.term 0) (.var 2)
private def imageOuter : Preterm := .app (.term 0) imageInner
private def arity : Nat → Option Nat := fun term => (signature term).map (·.arguments.length)
private def savedSource : Statements.Decoding :=
  ⟨[some (.var 0), some sourceOuter, some sourceInner], []⟩
private def before : Unifier := ⟨[2], [(0, false)], [], []⟩
private def after : Unifier := ⟨[], [(0, false), (2, true), (1, true)], [], []⟩
private def commands : List UnifyCmd := [.termSave 0, .termSave 0, .ref 0]

private theorem variable_decode : Soundness.decode store 0 = some (.var 2) := by
  rw [Soundness.decode]
  rfl

private theorem inner_decode : Soundness.decode store 1 = some imageInner := by
  have found : store[1]? = some ⟨.app 0 [0], applicationType⟩ := rfl
  rw [Soundness.decode, found]
  dsimp only
  rw [dif_pos (show ∀ argument ∈ [0], argument < 1 from by simp)]
  rw [List.mapM_subtype (g := Soundness.decode store)]
  · simp [variable_decode, imageInner, Preterm.applyArgs]
  · intros
    rfl

private theorem outer_decode : Soundness.decode store 2 = some imageOuter := by
  have found : store[2]? = some ⟨.app 0 [1], applicationType⟩ := rfl
  rw [Soundness.decode, found]
  dsimp only
  rw [dif_pos (show ∀ argument ∈ [1], argument < 2 from by simp)]
  rw [List.mapM_subtype (g := Soundness.decode store)]
  · simp [inner_decode, imageOuter, Preterm.applyArgs]
  · intros
    rfl

private theorem arities (term : Nat) (entry : TermDecl) (found : signature term = some entry) :
    arity term = some entry.arguments.length := by
  simp [arity, found]

private theorem typed : MMBMachineSoundness.TypedStore signature context store := by
  have variableTyping : Preterm.HasType signature context (.var 2) [] 0 :=
    Preterm.HasType.var (binder := .bound 0) (by rfl)
  have head : Preterm.HasType signature context (.term 0) [.regular 0 ∅] 0 :=
    Preterm.HasType.term (declaration := declaration) (by rfl)
  have inner : Preterm.HasType signature context imageInner [] 0 :=
    .regular head variableTyping
  have outer : Preterm.HasType signature context imageOuter [] 0 :=
    .regular head inner
  constructor
  intro position allocation found
  cases position with
  | zero =>
      have same : ⟨.var 2, variableType⟩ = allocation := by simpa [store] using found
      cases same
      exact ⟨.var 2, variable_decode, variableTyping, fun _ => ⟨2, rfl, rfl⟩⟩
  | succ position =>
      cases position with
      | zero =>
          have same : ⟨.app 0 [0], applicationType⟩ = allocation := by simpa [store] using found
          cases same
          exact ⟨imageInner, inner_decode, inner, by simp [applicationType]⟩
      | succ position =>
          cases position with
          | zero =>
              have same : ⟨.app 0 [1], applicationType⟩ = allocation := by simpa [store] using found
              cases same
              exact ⟨imageOuter, outer_decode, outer, by simp [applicationType]⟩
          | succ position => simp [store] at found

/-- Two nested saved applications reserve outer then inner heap slots. The
actual checked stream substitutes a different target variable for the formal
parameter and fills both reservations in their original positions. -/
theorem renamed_nested_saved_source_substitutes :
    Preterm.Substitutes (Substitution.ofList [.var 2]) sourceOuter imageOuter ∧
      SlotsSubstitute store (Substitution.ofList [.var 2]) savedSource.slots after.heap := by
  obtain ⟨image, imageRead, substituted, _, matching, _, _, _⟩ :=
    decodeExpr_unifies signature context store typed arity arities (Substitution.ofList [.var 2]) .apply (by decide)
      1 8 (Statements.initial 1) savedSource commands [] sourceOuter before after 2 []
      (by rfl) (by rfl) rfl (SlotsSubstitute.initial store [0] [.var 2] (by simp [variable_decode]))
  have sameImage : image = imageOuter := Option.some.inj (imageRead.symm.trans outer_decode)
  subst image
  exact ⟨substituted, matching⟩

/-- Repeated physical argument pointers are retained as two ordered child
images; they are not collapsed when deriving substitution. -/
theorem repeated_argument_vector_substitutes :
    List.Forall₂ (Preterm.Substitutes (Substitution.ofList [.var 2]))
      [.var 0, .var 0] [.var 2, .var 2] := by
  obtain ⟨images, imagesRead, substituted, _, _, _, _, _⟩ :=
    decodeExprs_unifies signature context store typed arity arities (Substitution.ofList [.var 2]) .statement (by decide)
      1 8 2 (Statements.initial 1) (Statements.initial 1) [.ref 0, .ref 0] [] [.var 0, .var 0]
      ⟨[0, 0], [(0, false)], [], []⟩ ⟨[], [(0, false)], [], []⟩ [0, 0] []
      (by rfl) (by rfl) rfl rfl (SlotsSubstitute.initial store [0] [.var 2] (by simp [variable_decode]))
  have sameImages : images = [.var 2, .var 2] := Option.some.inj (imagesRead.symm.trans (by simp [variable_decode]))
  subst images
  exact substituted

theorem unfilled_saved_source_slot_refused :
    Statements.decodeExpr arity 1 8 (Statements.initial 1) [.termSave 0, .ref 1] = none := by decide

theorem wrong_saved_pointer_refused :
    unifyRun store .apply before [.termSave 0, .ref 1] = none := by decide

theorem future_source_and_heap_slots_refused :
    Statements.decodeExpr arity 1 8 (Statements.initial 1) [.ref 1] = none ∧
      unifyRun store .apply before [.ref 1] = none := by
  constructor <;> decide

theorem ordinary_dummy_refused : unifyRun store .apply before [.dummy 0] = none := by decide

end Controls

end Mettapedia.Languages.MM0.MeTTa.MMBUnificationSoundness
