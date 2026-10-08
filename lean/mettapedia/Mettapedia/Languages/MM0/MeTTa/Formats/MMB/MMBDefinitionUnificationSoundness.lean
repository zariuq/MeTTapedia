import Mettapedia.Languages.MM0.MeTTa.Formats.MMB.MMBRunSoundness

/-!
# Definition-unifier scope and substitution images

Source slots contain only variables introduced by the retained decoder.
Extending an ordered substitution image vector preserves existing slot
meanings within that earned scope. The machine and kernel judgments are the
existing ones; saved expression slots remain distinct from dummy images.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.MMBDefinitionUnificationSoundness

open Formats.MMB Kernel
open MMBMachineSoundness MMBDependencySoundness MMBUnificationSoundness

def SourceSlotsScoped (arguments : Nat) (state : Statements.Decoding) : Prop :=
  ∀ (slot : Nat) (source : Preterm), state.slots[slot]? = some (some source) →
    ∀ index, Preterm.Occurs index source → index < arguments + state.dummies.length

theorem SourceSlotsScoped.initial (arguments : Nat) : SourceSlotsScoped arguments (Statements.initial arguments) := by
  intro slot source read index occurs
  have inside : slot < arguments := by
    have bound := (List.getElem?_eq_some_iff.mp read).choose
    simpa [Statements.initial] using bound
  have same : source = .var slot := by simpa [Statements.initial, inside] using read.symm
  subst source
  cases occurs
  simpa [Statements.initial] using inside

theorem SourceSlotsScoped.reserve (arguments : Nat) (state : Statements.Decoding)
    (inScope : SourceSlotsScoped arguments state) :
    SourceSlotsScoped arguments { state with slots := state.slots ++ [none] } := by
  intro slot source read index occurs
  by_cases old : slot < state.slots.length
  · rw [List.getElem?_append_left old] at read
    exact inScope slot source read index occurs
  · have inside := (List.getElem?_eq_some_iff.mp read).choose
    have last : slot = state.slots.length := by
      simp only [List.length_append, List.length_cons, List.length_nil] at inside
      omega
    subst slot
    simp at read

theorem SourceSlotsScoped.fill (arguments : Nat) (state : Statements.Decoding)
    (inScope : SourceSlotsScoped arguments state) (slot : Nat) (source : Preterm)
    (bounded : ∀ index, Preterm.Occurs index source → index < arguments + state.dummies.length) :
    SourceSlotsScoped arguments { state with slots := state.slots.set slot (some source) } := by
  intro other expression read index occurs
  by_cases same : other = slot
  · subst other
    have inside : slot < state.slots.length := by
      have bound := (List.getElem?_eq_some_iff.mp read).choose
      simpa only [List.length_set] using bound
    rw [List.getElem?_set_self inside] at read
    cases Option.some.inj (Option.some.inj read)
    exact bounded index occurs
  · rw [List.getElem?_set_ne (Ne.symm same)] at read
    exact inScope other expression read index occurs

theorem SourceSlotsScoped.dummy (arguments : Nat) (state : Statements.Decoding) (sort : Nat)
    (inScope : SourceSlotsScoped arguments state) :
    SourceSlotsScoped arguments
      ⟨state.slots ++ [some (.var (arguments + state.dummies.length))], state.dummies ++ [sort]⟩ := by
  intro slot source read index occurs
  by_cases old : slot < state.slots.length
  · rw [List.getElem?_append_left old] at read
    have earlier := inScope slot source read index occurs
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  · have inside := (List.getElem?_eq_some_iff.mp read).choose
    have last : slot = state.slots.length := by
      simp only [List.length_append, List.length_cons, List.length_nil] at inside
      omega
    subst slot
    have same : source = .var (arguments + state.dummies.length) := by simpa using read.symm
    subst source
    cases occurs
    simp

theorem occurs_applyArgs_bounded (bound : Nat) (head : Preterm) (sources : List Preterm)
    (headBound : ∀ index, Preterm.Occurs index head → index < bound)
    (children : ∀ source ∈ sources, ∀ index, Preterm.Occurs index source → index < bound) :
    ∀ index, Preterm.Occurs index (head.applyArgs sources) → index < bound := by
  induction sources generalizing head with
  | nil => exact headBound
  | cons first sources ih =>
      apply ih (.app head first)
      · intro index occurs
        cases occurs with
        | function earlier => exact headBound index earlier
        | argument earlier => exact children first (List.mem_cons_self) index earlier
      · intro source member
        exact children source (List.mem_cons_of_mem _ member)

theorem substitutes_append_images (images extra : List Preterm) (source image : Preterm)
    (bounded : ∀ index, Preterm.Occurs index source → index < images.length)
    (substituted : Preterm.Substitutes (Substitution.ofList images) source image) :
    Preterm.Substitutes (Substitution.ofList (images ++ extra)) source image := by
  apply Preterm.substitute_sound
  rw [Preterm.substitute_congr (Substitution.ofList (images ++ extra)) (Substitution.ofList images) source
    (fun index occurs => List.getElem?_append_left (bounded index occurs))]
  exact substituted.eval

theorem SlotsSubstitute.append_images (store : List Alloc) (images extra : List Preterm)
    (state : Statements.Decoding) (heap : List (Nat × Bool)) (arguments : Nat)
    (inScope : SourceSlotsScoped arguments state) (lengths : images.length = arguments + state.dummies.length)
    (matching : SlotsSubstitute store (Substitution.ofList images) state.slots heap) :
    SlotsSubstitute store (Substitution.ofList (images ++ extra)) state.slots heap := by
  refine ⟨matching.length, ?_⟩
  intro slot source found
  obtain ⟨position, saved, image, read, decoded, substituted⟩ := matching.filled slot source found
  exact ⟨position, saved, image, read, decoded, substitutes_append_images images extra source image
    (by simpa only [lengths] using inScope slot source found) substituted⟩

mutual

theorem decodeExpr_scoped (arity : Nat → Option Nat) (arguments fuel : Nat)
    (before after : Statements.Decoding) (commands rest : List UnifyCmd) (source : Preterm)
    (inScope : SourceSlotsScoped arguments before)
    (decoded : Statements.decodeExpr arity arguments fuel before commands = some (source, after, rest)) :
    (∃ introduced, after.dummies = before.dummies ++ introduced) ∧ SourceSlotsScoped arguments after ∧
      (∀ index, Preterm.Occurs index source → index < arguments + after.dummies.length) := by
  cases fuel with
  | zero => simp [Statements.decodeExpr] at decoded
  | succ fuel =>
      cases commands with
      | nil => simp [Statements.decodeExpr] at decoded
      | cons command commands =>
          cases command with
          | hyp => simp [Statements.decodeExpr] at decoded
          | ref slot =>
              change ((before.slots[slot]?).bind id).bind
                (fun expression => some (expression, before, commands)) = some (source, after, rest) at decoded
              cases slotRead : before.slots[slot]? with
              | none => simp [slotRead] at decoded
              | some value =>
                  cases value with
                  | none => simp [slotRead] at decoded
                  | some expression =>
                      have fields : expression = source ∧ before = after ∧ commands = rest := by
                        simpa [slotRead] using decoded
                      rcases fields with ⟨sameSource, sameState, sameRest⟩
                      subst source
                      subst after
                      subst rest
                      exact ⟨⟨[], by simp⟩, inScope, inScope slot expression slotRead⟩
          | dummy sort =>
              have fields : .var (arguments + before.dummies.length) = source ∧
                  (⟨before.slots ++ [some (.var (arguments + before.dummies.length))], before.dummies ++ [sort]⟩ : Statements.Decoding) = after ∧
                    commands = rest := by simpa [Statements.decodeExpr] using decoded
              rcases fields with ⟨rfl, rfl, rfl⟩
              exact ⟨⟨[sort], rfl⟩, inScope.dummy arguments before sort, by intro index occurs; cases occurs; simp⟩
          | term term =>
              obtain ⟨count, _, remaining⟩ := Option.bind_eq_some_iff.mp decoded
              obtain ⟨value, children, same⟩ := Option.bind_eq_some_iff.mp remaining
              rcases value with ⟨sources, middle, following⟩
              have fields : Preterm.applyArgs (.term term) sources = source ∧ middle = after ∧ following = rest := by simpa using same
              rcases fields with ⟨sameSource, sameState, sameRest⟩
              subst source
              subst middle
              subst following
              have checked := decodeExprs_scoped arity arguments fuel count before after commands rest sources inScope children
              exact ⟨checked.1, checked.2.1, occurs_applyArgs_bounded _ (.term term) sources
                (by intro index occurs; cases occurs) checked.2.2⟩
          | termSave term =>
              obtain ⟨count, _, remaining⟩ := Option.bind_eq_some_iff.mp decoded
              obtain ⟨value, children, same⟩ := Option.bind_eq_some_iff.mp remaining
              rcases value with ⟨sources, middle, following⟩
              let expression := Preterm.applyArgs (.term term) sources
              have fields : expression = source ∧
                  { middle with slots := middle.slots.set before.slots.length (some expression) } = after ∧ following = rest := by
                simpa [expression] using same
              rcases fields with ⟨sameSource, sameState, sameRest⟩
              subst source
              subst after
              subst following
              have checked := decodeExprs_scoped arity arguments fuel count
                { before with slots := before.slots ++ [none] } middle commands rest sources (inScope.reserve arguments before) children
              have bounded := occurs_applyArgs_bounded (arguments + middle.dummies.length) (.term term) sources
                (by intro index occurs; cases occurs) checked.2.2
              exact ⟨checked.1, checked.2.1.fill arguments middle before.slots.length expression bounded, bounded⟩
termination_by fuel

theorem decodeExprs_scoped (arity : Nat → Option Nat) (arguments fuel count : Nat)
    (before after : Statements.Decoding) (commands rest : List UnifyCmd) (sources : List Preterm)
    (inScope : SourceSlotsScoped arguments before)
    (decoded : Statements.decodeExprs arity arguments fuel count before commands = some (sources, after, rest)) :
    (∃ introduced, after.dummies = before.dummies ++ introduced) ∧ SourceSlotsScoped arguments after ∧
      (∀ source ∈ sources, ∀ index, Preterm.Occurs index source → index < arguments + after.dummies.length) := by
  cases count with
  | zero =>
      have fields : [] = sources ∧ before = after ∧ commands = rest := by simpa [Statements.decodeExprs] using decoded
      rcases fields with ⟨rfl, rfl, rfl⟩
      exact ⟨⟨[], by simp⟩, inScope, by simp⟩
  | succ count =>
      cases fuel with
      | zero => simp [Statements.decodeExprs] at decoded
      | succ fuel =>
          obtain ⟨value, firstRead, remaining⟩ := Option.bind_eq_some_iff.mp decoded
          rcases value with ⟨first, middle, following⟩
          obtain ⟨value, tailRead, same⟩ := Option.bind_eq_some_iff.mp remaining
          rcases value with ⟨tail, finish, finalCommands⟩
          have fields : first :: tail = sources ∧ finish = after ∧ finalCommands = rest := by simpa using same
          rcases fields with ⟨sameSources, sameState, sameRest⟩
          subst sources
          subst finish
          subst finalCommands
          obtain ⟨⟨firstDummies, firstHistory⟩, middleScope, firstBound⟩ :=
            decodeExpr_scoped arity arguments fuel before middle commands following first inScope firstRead
          obtain ⟨⟨tailDummies, tailHistory⟩, afterScope, tailBound⟩ :=
            decodeExprs_scoped arity arguments fuel count middle after following rest tail middleScope tailRead
          refine ⟨⟨firstDummies ++ tailDummies, by rw [tailHistory, firstHistory, List.append_assoc]⟩, afterScope, ?_⟩
          intro source member index occurs
          rcases List.mem_cons.mp member with rfl | tailMember
          · have earlier := firstBound index occurs
            rw [tailHistory, List.length_append]
            omega
          · exact tailBound source tailMember index occurs
termination_by fuel

end

def unsavedPositions (heap : List (Nat × Bool)) : List Nat :=
  heap.filterMap fun (position, saved) => if saved then none else some position

theorem unsavedPositions_mem (heap : List (Nat × Bool)) (position : Nat) :
    position ∈ unsavedPositions heap ↔ (position, false) ∈ heap := by
  constructor
  · intro member
    obtain ⟨⟨pointer, saved⟩, found, selected⟩ := List.mem_filterMap.mp member
    cases saved with
    | true => simp at selected
    | false =>
        have same : pointer = position := by simpa using selected
        subst pointer
        exact found
  · intro member
    exact List.mem_filterMap.mpr ⟨(position, false), member, rfl⟩

theorem unsavedPositions_append (first second : List (Nat × Bool)) :
    unsavedPositions (first ++ second) = unsavedPositions first ++ unsavedPositions second := by
  exact List.filterMap_append

def UnsavedImages (store : List Alloc) (heap : List (Nat × Bool)) (images : List Preterm) : Prop :=
  (unsavedPositions heap).mapM (Soundness.decode store) = some images

theorem UnsavedImages.reserve (store : List Alloc) (heap : List (Nat × Bool))
    (images : List Preterm) (position : Nat) (read : UnsavedImages store heap images) :
    UnsavedImages store (heap ++ [(position, true)]) images := by
  simpa [UnsavedImages, unsavedPositions_append, unsavedPositions] using read

theorem UnsavedImages.append_dummy (store : List Alloc) (heap : List (Nat × Bool))
    (images : List Preterm) (position index : Nat) (read : UnsavedImages store heap images)
    (decoded : Soundness.decode store position = some (.var index)) :
    UnsavedImages store (heap ++ [(position, false)]) (images ++ [.var index]) := by
  unfold UnsavedImages at read ⊢
  rw [unsavedPositions_append]
  change (unsavedPositions heap ++ [position]).mapM (Soundness.decode store) = some (images ++ [.var index])
  simp [List.mapM_append, read, decoded]

theorem UnsavedImages.fresh (store : List Alloc) (heap : List (Nat × Bool)) (images : List Preterm)
    (context : Context) (index : Nat) (read : UnsavedImages store heap images)
    (guarded : ∀ position, (position, false) ∈ heap →
      ∃ expression, Soundness.decode store position = some expression ∧ Preterm.FreshFor context index expression) :
    ∀ expression ∈ images, Preterm.FreshFor context index expression := by
  have related := decoded_arguments store (unsavedPositions heap) images read
  have represented : ∀ expression ∈ images, ∃ position,
      position ∈ unsavedPositions heap ∧ Soundness.decode store position = some expression := by
    clear read
    generalize unsavedPositions heap = positions at related ⊢
    induction related with
    | nil => simp
    | @cons position expression positions expressions decoded _ ih =>
        intro image member
        rcases List.mem_cons.mp member with rfl | later
        · exact ⟨position, List.mem_cons_self, decoded⟩
        · obtain ⟨pointer, found, imageRead⟩ := ih image later
          exact ⟨pointer, List.mem_cons_of_mem _ found, imageRead⟩
  intro expression member
  obtain ⟨position, found, decoded⟩ := represented expression member
  obtain ⟨image, imageRead, fresh⟩ := guarded position ((unsavedPositions_mem heap position).mp found)
  have same : image = expression := Option.some.inj (imageRead.symm.trans decoded)
  subst image
  exact fresh

theorem freshDummies_append (context : Context) (arguments : List Preterm)
    (sorts indices laterSorts laterIndices : List Nat)
    (first : Definition.FreshDummies context arguments sorts indices)
    (later : Definition.FreshDummies context (arguments ++ indices.map Preterm.var) laterSorts laterIndices) :
    Definition.FreshDummies context arguments (sorts ++ laterSorts) (indices ++ laterIndices) := by
  revert later
  induction first with
  | nil => intro later; simpa using later
  | cons lookup fresh _ ih =>
      intro later
      apply Definition.FreshDummies.cons lookup fresh
      apply ih
      simpa [List.map_cons, List.append_assoc] using later

mutual

/-- Actual definition-mode execution of the source decoder's consumed prefix
earns both substitution and ordered dummy freshness. The image vector grows
only when that prefix accepts a dummy command. -/
theorem decodeExpr_definition_unifies (signature : TermSignature) (context : Context)
    (store : List Alloc) (typed : TypedStore signature context store) (ranked : RankedStore context store)
    (arity : Nat → Option Nat)
    (arities : ∀ term declaration, signature term = some declaration → arity term = some declaration.arguments.length)
    (arguments fuel : Nat) (images : List Preterm) (sourceBefore sourceAfter : Statements.Decoding)
    (commandsBefore rest : List UnifyCmd) (source : Preterm) (before after : Unifier)
    (position : Nat) (outer : List Nat)
    (decoded : Statements.decodeExpr arity arguments fuel sourceBefore (commandsBefore ++ rest) = some (source, sourceAfter, rest))
    (executed : commandsBefore.foldlM (fun unifier command => unifyStep store .definition unifier command) before = some after)
    (stack : before.stack = position :: outer)
    (inScope : SourceSlotsScoped arguments sourceBefore)
    (lengths : images.length = arguments + sourceBefore.dummies.length)
    (matching : SlotsSubstitute store (Substitution.ofList images) sourceBefore.slots before.heap)
    (unsaved : UnsavedImages store before.heap images) :
    ∃ image sorts indices,
      sourceAfter.dummies = sourceBefore.dummies ++ sorts ∧
      Soundness.decode store position = some image ∧
      Preterm.Substitutes (Substitution.ofList (images ++ indices.map Preterm.var)) source image ∧
      Definition.FreshDummies context images sorts indices ∧ after.stack = outer ∧
      SlotsSubstitute store (Substitution.ofList (images ++ indices.map Preterm.var)) sourceAfter.slots after.heap ∧
      UnsavedImages store after.heap (images ++ indices.map Preterm.var) ∧
      after.main = before.main ∧ after.hyps = before.hyps := by
  cases fuel with
  | zero => simp [Statements.decodeExpr] at decoded
  | succ fuel =>
      cases commandsBefore with
      | nil =>
          obtain ⟨_, consumed, _, consumedRead, nonempty⟩ :=
            Soundness.decodeExpr_source_order arity arguments (fuel + 1) sourceBefore sourceAfter rest rest source decoded
          have empty : consumed = [] := List.append_cancel_right (bs := rest) (by simpa using consumedRead.symm)
          exact False.elim (nonempty empty)
      | cons command commandsBefore =>
          cases command with
          | hyp => simp [Statements.decodeExpr] at decoded
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
                      have same : expression = source ∧ sourceBefore = sourceAfter ∧ commandsBefore ++ rest = rest := by
                        simpa [slotRead] using decoded
                      rcases same with ⟨sameSource, sameState, sameRest⟩
                      subst source
                      subst sourceAfter
                      have empty : commandsBefore = [] := List.append_cancel_right (bs := rest) (by simpa using sameRest)
                      subst commandsBefore
                      have stepRead : unifyStep store .definition before (.ref index) = some after := by
                        simpa [List.foldlM_cons] using executed
                      obtain ⟨image, imageRead, substituted, sameAfter⟩ :=
                        matching.reference store (Substitution.ofList images) sourceBefore.slots before after .definition
                          index position outer expression slotRead stack stepRead
                      subst after
                      refine ⟨image, [], [], by simp, imageRead, ?_, .nil _, rfl, ?_, ?_, rfl, rfl⟩
                      · simpa using substituted
                      · simpa using matching
                      · simpa using unsaved
          | dummy sort =>
              have same : .var (arguments + sourceBefore.dummies.length) = source ∧
                  (⟨sourceBefore.slots ++ [some (.var (arguments + sourceBefore.dummies.length))], sourceBefore.dummies ++ [sort]⟩ : Statements.Decoding) = sourceAfter ∧
                  commandsBefore ++ rest = rest := by simpa [Statements.decodeExpr] using decoded
              rcases same with ⟨sameSource, sameState, sameRest⟩
              subst source
              subst sourceAfter
              have empty : commandsBefore = [] := List.append_cancel_right (bs := rest) (by simpa using sameRest)
              subst commandsBefore
              have stepRead : unifyStep store .definition before (.dummy sort) = some after := by
                simpa [List.foldlM_cons] using executed
              obtain ⟨actualPosition, actualOuter, index, shaped, sameAfter, imageRead, bound, guarded⟩ :=
                unify_definition_dummy_fresh signature context store ranked typed before after sort stepRead
              have shapeSame := List.cons.inj (shaped.symm.trans stack)
              rcases shapeSame with ⟨samePosition, sameOuter⟩
              subst actualPosition
              subst actualOuter
              subst after
              have fresh := UnsavedImages.fresh store before.heap images context index unsaved guarded
              have extended := SlotsSubstitute.append_images store images [.var index] sourceBefore before.heap arguments
                inScope lengths matching
              have variableSubstitution : Preterm.Substitutes (Substitution.ofList (images ++ [.var index]))
                  (.var (arguments + sourceBefore.dummies.length)) (.var index) := by
                apply Preterm.Substitutes.var
                simp [Substitution.ofList, ← lengths]
              refine ⟨.var index, [sort], [index], rfl, imageRead, ?_, .cons bound fresh (.nil _), rfl, ?_, ?_, rfl, rfl⟩
              · simpa using variableSubstitution
              · simpa using extended.append_filled store (Substitution.ofList (images ++ [.var index]))
                  sourceBefore.slots before.heap position false (.var (arguments + sourceBefore.dummies.length)) (.var index)
                  imageRead variableSubstitution
              · simpa using UnsavedImages.append_dummy store before.heap images position index unsaved imageRead
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
                      cases first : unifyStep store .definition before (.term term) with
                      | none => simp [List.foldlM_cons, first] at executed
                      | some middle =>
                          have later : commandsBefore.foldlM (fun unifier command => unifyStep store .definition unifier command) middle = some after := by
                            simpa [List.foldlM_cons, first] using executed
                          obtain ⟨positions, type, found, sameMiddle⟩ :=
                            unifyTerm_operands store before middle term position false outer stack first
                          subst middle
                          obtain ⟨values, declaration, imageRead, parentRead, declared, fitted, _⟩ :=
                            TypedStore.application signature context store typed position term positions type found
                          have countSame : count = declaration.arguments.length :=
                            Option.some.inj (countRead.symm.trans (arities term declaration declared))
                          have countPositions : positions.length = count :=
                            (decoded_arguments store positions values imageRead).length_eq.trans (fitted.length_eq.trans countSame.symm)
                          obtain ⟨childImages, sorts, indices, dummies, valuesRead, substituted, fresh,
                              afterStack, afterSlots, afterUnsaved, afterMain, afterHyps⟩ :=
                            decodeExprs_definition_unifies signature context store typed ranked arity arities arguments fuel count images
                              sourceBefore next commandsBefore rest sources _ after positions outer children later rfl countPositions
                              inScope lengths matching unsaved
                          have equalImages : childImages = values := Option.some.inj (valuesRead.symm.trans imageRead)
                          subst childImages
                          exact ⟨Preterm.applyArgs (.term term) values, sorts, indices, dummies, parentRead,
                            substitution_application _ (.term term) (.term term) sources values (.term term) substituted,
                            fresh, afterStack, afterSlots, afterUnsaved, afterMain, afterHyps⟩
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
                      cases first : unifyStep store .definition before (.termSave term) with
                      | none => simp [List.foldlM_cons, first] at executed
                      | some middle =>
                          have later : commandsBefore.foldlM (fun unifier command => unifyStep store .definition unifier command) middle = some after := by
                            simpa [List.foldlM_cons, first] using executed
                          obtain ⟨positions, type, found, sameMiddle⟩ :=
                            unifyTerm_operands store before middle term position true outer stack first
                          subst middle
                          obtain ⟨values, declaration, imageRead, parentRead, declared, fitted, _⟩ :=
                            TypedStore.application signature context store typed position term positions type found
                          have countSame : count = declaration.arguments.length :=
                            Option.some.inj (countRead.symm.trans (arities term declaration declared))
                          have countPositions : positions.length = count :=
                            (decoded_arguments store positions values imageRead).length_eq.trans (fitted.length_eq.trans countSame.symm)
                          obtain ⟨childImages, sorts, indices, dummies, valuesRead, substituted, fresh,
                              afterStack, afterSlots, afterUnsaved, afterMain, afterHyps⟩ :=
                            decodeExprs_definition_unifies signature context store typed ranked arity arities arguments fuel count images
                              reserved next commandsBefore rest sources _ after positions outer children later rfl countPositions
                              (SourceSlotsScoped.reserve arguments sourceBefore inScope) lengths
                              (matching.reserve store (Substitution.ofList images) sourceBefore.slots before.heap position)
                              (UnsavedImages.reserve store before.heap images position unsaved)
                          have equalImages : childImages = values := Option.some.inj (valuesRead.symm.trans imageRead)
                          subst childImages
                          have parentSubstitution : Preterm.Substitutes (Substitution.ofList (images ++ indices.map Preterm.var))
                              body (Preterm.applyArgs (.term term) values) :=
                            substitution_application _ (.term term) (.term term) sources values (.term term) substituted
                          obtain ⟨extraSlots, _, slotsRead, _, _⟩ :=
                            Soundness.decodeExprs_source_order arity arguments fuel count reserved next (commandsBefore ++ rest) rest sources children
                          have reservation : next.slots[sourceBefore.slots.length]? = some none := by
                            rw [slotsRead]
                            simp [reserved, List.append_assoc]
                          obtain ⟨extraHeap, heapRead⟩ := unifyFold_heap_prefix store .definition _ after commandsBefore later
                          have saved : after.heap[sourceBefore.slots.length]? = some (position, true) := by
                            rw [heapRead]
                            simp [matching.length, List.append_assoc]
                          have filled := afterSlots.fill_reserved store (Substitution.ofList (images ++ indices.map Preterm.var))
                            next.slots after.heap sourceBefore.slots.length position body (Preterm.applyArgs (.term term) values)
                            reservation saved parentRead parentSubstitution
                          exact ⟨Preterm.applyArgs (.term term) values, sorts, indices, dummies, parentRead,
                            parentSubstitution, fresh, afterStack, filled, afterUnsaved, afterMain, afterHyps⟩
termination_by fuel

theorem decodeExprs_definition_unifies (signature : TermSignature) (context : Context)
    (store : List Alloc) (typed : TypedStore signature context store) (ranked : RankedStore context store)
    (arity : Nat → Option Nat)
    (arities : ∀ term declaration, signature term = some declaration → arity term = some declaration.arguments.length)
    (arguments fuel count : Nat) (images : List Preterm) (sourceBefore sourceAfter : Statements.Decoding)
    (commandsBefore rest : List UnifyCmd) (sources : List Preterm) (before after : Unifier)
    (positions outer : List Nat)
    (decoded : Statements.decodeExprs arity arguments fuel count sourceBefore (commandsBefore ++ rest) = some (sources, sourceAfter, rest))
    (executed : commandsBefore.foldlM (fun unifier command => unifyStep store .definition unifier command) before = some after)
    (stack : before.stack = positions ++ outer) (countPositions : positions.length = count)
    (inScope : SourceSlotsScoped arguments sourceBefore)
    (lengths : images.length = arguments + sourceBefore.dummies.length)
    (matching : SlotsSubstitute store (Substitution.ofList images) sourceBefore.slots before.heap)
    (unsaved : UnsavedImages store before.heap images) :
    ∃ values sorts indices,
      sourceAfter.dummies = sourceBefore.dummies ++ sorts ∧
      positions.mapM (Soundness.decode store) = some values ∧
      List.Forall₂ (Preterm.Substitutes (Substitution.ofList (images ++ indices.map Preterm.var))) sources values ∧
      Definition.FreshDummies context images sorts indices ∧ after.stack = outer ∧
      SlotsSubstitute store (Substitution.ofList (images ++ indices.map Preterm.var)) sourceAfter.slots after.heap ∧
      UnsavedImages store after.heap (images ++ indices.map Preterm.var) ∧
      after.main = before.main ∧ after.hyps = before.hyps := by
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
      have emptyPositions : positions = [] := List.length_eq_zero_iff.mp countPositions
      subst positions
      refine ⟨[], [], [], by simp, rfl, .nil, .nil _, by simpa using stack, ?_, ?_, rfl, rfl⟩
      · simpa using matching
      · simpa using unsaved
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
                  | nil => simp at countPositions
                  | cons position positions =>
                      have tailLength : positions.length = count := by simpa using countPositions
                      have firstStack : before.stack = position :: (positions ++ outer) := by simpa using stack
                      obtain ⟨image, firstSorts, firstIndices, middleDummies, imageRead, substituted, firstFresh,
                          middleStack, middleSlots, middleUnsaved, middleMain, middleHyps⟩ :=
                        decodeExpr_definition_unifies signature context store typed ranked arity arities arguments fuel images
                          sourceBefore middleSource firstCommands remaining source before middle position (positions ++ outer)
                          firstDecoded firstExecuted firstStack inScope lengths matching unsaved
                      have sourceScope := decodeExpr_scoped arity arguments fuel sourceBefore middleSource
                        (firstCommands ++ remaining) remaining source inScope firstDecoded
                      have middleLengths : (images ++ firstIndices.map Preterm.var).length = arguments + middleSource.dummies.length := by
                        have counts := firstFresh.length_eq
                        rw [List.length_append, List.length_map, middleDummies, List.length_append]
                        omega
                      obtain ⟨values, laterSorts, laterIndices, afterDummies, valuesRead, othersSubstituted, laterFresh,
                          afterStack, afterSlots, afterUnsaved, afterMain, afterHyps⟩ :=
                        decodeExprs_definition_unifies signature context store typed ranked arity arities arguments fuel count
                          (images ++ firstIndices.map Preterm.var) middleSource finish otherCommands rest earlier middle after positions outer
                          othersDecoded othersExecuted middleStack tailLength sourceScope.2.1 middleLengths middleSlots middleUnsaved
                      have earlierSubstitution := substitutes_append_images (images ++ firstIndices.map Preterm.var)
                        (laterIndices.map Preterm.var) source image
                        (by simpa only [middleLengths] using sourceScope.2.2) substituted
                      refine ⟨image :: values, firstSorts ++ laterSorts, firstIndices ++ laterIndices, ?_,
                        by simp [imageRead, valuesRead], ?_,
                        freshDummies_append context images firstSorts firstIndices laterSorts laterIndices firstFresh laterFresh,
                        afterStack, ?_, ?_, afterMain.trans middleMain, afterHyps.trans middleHyps⟩
                      · rw [afterDummies, middleDummies, List.append_assoc]
                      · simpa only [List.map_append, List.append_assoc] using List.Forall₂.cons earlierSubstitution othersSubstituted
                      · simpa only [List.map_append, List.append_assoc] using afterSlots
                      · simpa only [List.map_append, List.append_assoc] using afterUnsaved
termination_by fuel

end

theorem termDecl_definition_source (terms : List TermEntry) (entry : TermEntry)
    (declaration : TermDecl) (body : Definition.Body) (commands : List UnifyCmd)
    (valueRead : entry.value = some commands)
    (decoded : Statements.termDecl terms entry = some (declaration, some body)) :
    ∃ state, Statements.decodeExpr (Statements.arityOf terms) entry.args.length (2 * commands.length + 2)
      (Statements.initial entry.args.length) commands = some (body.expression, state, []) ∧
      state.dummies = body.dummies := by
  unfold Statements.termDecl at decoded
  rw [valueRead] at decoded
  obtain ⟨value, sourceRead, checked⟩ := Option.bind_eq_some_iff.mp decoded
  rcases value with ⟨expression, state, remaining⟩
  change (if remaining ≠ [] then none else some
    (⟨Statements.context entry.args, entry.sort,
      entry.ret.deps.image (fun rank => (Statements.boundPositions entry.args).getD rank rank)⟩,
      some (⟨state.dummies, expression⟩ : Definition.Body))) = some (declaration, some body) at checked
  split at checked
  · cases checked
  · rename_i complete
    have empty : remaining = [] := by simpa using complete
    subst remaining
    have same := Option.some.inj checked
    have sameBody : (⟨state.dummies, expression⟩ : Definition.Body) = body := Option.some.inj (congrArg Prod.snd same)
    subst body
    exact ⟨state, sourceRead, rfl⟩

theorem UnsavedImages.initial (store : List Alloc) (positions : List Nat) (images : List Preterm)
    (read : positions.mapM (Soundness.decode store) = some images) :
    UnsavedImages store (positions.map (·, false)) images := by
  simpa [UnsavedImages, unsavedPositions, List.filterMap_map] using read

/-- The complete retained definition stream yields the decoded body's
ordered dummy images and simultaneous kernel substitution. -/
theorem unifyRun_definition_body (signature : TermSignature) (context : Context)
    (store : List Alloc) (typed : TypedStore signature context store) (ranked : RankedStore context store)
    (arity : Nat → Option Nat)
    (arities : ∀ term declaration, signature term = some declaration → arity term = some declaration.arguments.length)
    (arguments : Nat) (positions : List Nat) (images : List Preterm) (position : Nat)
    (main : List Elem) (hypotheses : List Nat) (commands : List UnifyCmd)
    (body : Definition.Body) (sourceState : Statements.Decoding) (after : Unifier)
    (countPositions : positions.length = arguments)
    (imageRead : positions.mapM (Soundness.decode store) = some images)
    (decoded : Statements.decodeExpr arity arguments (2 * commands.length + 2) (Statements.initial arguments)
      commands = some (body.expression, sourceState, []))
    (dummies : sourceState.dummies = body.dummies)
    (accepted : unifyRun store .definition ⟨[position], positions.map (·, false), main, hypotheses⟩ commands = some after) :
    ∃ indices image, Soundness.decode store position = some image ∧
      Definition.FreshDummies context images body.dummies indices ∧
      Preterm.Substitutes (Substitution.ofList (images ++ indices.map Preterm.var)) body.expression image ∧
      SlotsSubstitute store (Substitution.ofList (images ++ indices.map Preterm.var)) sourceState.slots after.heap ∧
      UnsavedImages store after.heap (images ++ indices.map Preterm.var) ∧
      after.main = main ∧ after.hyps = hypotheses := by
  obtain ⟨middle, executed, finished⟩ := unifyRun_prefix store .definition
    ⟨[position], positions.map (·, false), main, hypotheses⟩ after commands [] (by simpa using accepted)
  have terminal : middle.stack = [] ∧ middle = after := by simpa [unifyRun] using finished
  have same := terminal.2
  subst middle
  have lengths : images.length = arguments + (Statements.initial arguments).dummies.length := by
    have related := decoded_arguments store positions images imageRead
    simpa [Statements.initial, countPositions] using related.length_eq.symm
  have matching : SlotsSubstitute store (Substitution.ofList images) (Statements.initial arguments).slots
      (positions.map (·, false)) := by
    simpa only [countPositions] using SlotsSubstitute.initial store positions images imageRead
  obtain ⟨image, sorts, indices, sourceHistory, resultRead, substituted, fresh, _, finalSlots, finalImages, finalMain, finalHyps⟩ :=
    decodeExpr_definition_unifies signature context store typed ranked arity arities arguments (2 * commands.length + 2) images
      (Statements.initial arguments) sourceState commands [] body.expression _ after position [] (by simpa using decoded)
      executed rfl (SourceSlotsScoped.initial arguments) lengths matching (UnsavedImages.initial store positions images imageRead)
  have sameSorts : sorts = body.dummies := by simpa [Statements.initial, dummies] using sourceHistory.symm
  subst sorts
  exact ⟨indices, image, resultRead, fresh, substituted, finalSlots, finalImages, finalMain, finalHyps⟩

/-- A decoded definition and an accepted binary unfolding stream produce the
existing kernel unfolding judgment. Declaration and body authorization are
supplied by the independent environments. -/
theorem unifyRun_definition_unfolds (signature : TermSignature) (definitions : Definition.Signature)
    (context : Context) (tables : Tables) (store : List Alloc)
    (typed : TypedStore signature context store) (ranked : RankedStore context store)
    (arities : ∀ term declaration, signature term = some declaration →
      Statements.arityOf tables.terms term = some declaration.arguments.length)
    (term left position : Nat) (positions : List Nat) (type : ExprType)
    (entry : TermEntry) (declaration : TermDecl) (body : Definition.Body) (commands : List UnifyCmd)
    (main : List Elem) (hypotheses : List Nat) (after : Unifier)
    (leftRead : store[left]? = some ⟨.app term positions, type⟩)
    (declared : signature term = some declaration) (defined : definitions term = some body)
    (sourceRead : Statements.termDecl tables.terms entry = some (declaration, some body))
    (valueRead : entry.value = some commands)
    (accepted : unifyRun store .definition ⟨[position], positions.map (·, false), main, hypotheses⟩ commands = some after) :
    ∃ images indices image,
      Soundness.decode store left = some (Preterm.applyArgs (.term term) images) ∧
      Soundness.decode store position = some image ∧
      Definition.Unfolds signature definitions context term images indices image ∧
      after.main = main ∧ after.hyps = hypotheses := by
  obtain ⟨images, available, imageRead, leftDecoded, availableRead, fitted, _⟩ :=
    TypedStore.application signature context store typed left term positions type leftRead
  have same : available = declaration := Option.some.inj (availableRead.symm.trans declared)
  subst available
  have fields := MMBRunSoundness.termDecl_fields tables.terms entry declaration (some body) sourceRead
  have counts : positions.length = entry.args.length := by
    have count := (decoded_arguments store positions images imageRead).length_eq.trans fitted.length_eq
    simpa only [fields.1, Statements.context, List.length_map] using count
  obtain ⟨sourceState, decoded, dummies⟩ := termDecl_definition_source tables.terms entry declaration body commands valueRead sourceRead
  obtain ⟨indices, image, resultRead, fresh, substituted, _, _, finalMain, finalHyps⟩ :=
    unifyRun_definition_body signature context store typed ranked (Statements.arityOf tables.terms) arities entry.args.length
      positions images position main hypotheses commands body sourceState after counts imageRead decoded dummies accepted
  exact ⟨images, indices, image, leftDecoded, resultRead,
    .intro declared defined fitted fresh substituted, finalMain, finalHyps⟩

theorem authorized_unfolding_typed (signature : TermSignature) (definitions : Definition.Signature)
    (context : Context) (term : Nat) (declaration : TermDecl) (body : Definition.Body)
    (arguments : List Preterm) (indices : List Nat) (image : Preterm)
    (declared : signature term = some declaration) (defined : definitions term = some body)
    (bodyTyped : Preterm.HasType signature (declaration.arguments ++ body.dummies.map Binder.bound)
      body.expression [] declaration.resultSort)
    (unfolded : Definition.Unfolds signature definitions context term arguments indices image) :
    Preterm.HasType signature context image [] declaration.resultSort := by
  cases unfolded with
  | @intro actualDecl actualBody _ actualDeclared actualDefined fitted fresh substituted =>
      have sameDecl : actualDecl = declaration := Option.some.inj (actualDeclared.symm.trans declared)
      have sameBody : actualBody = body := Option.some.inj (actualDefined.symm.trans defined)
      subst actualDecl
      subst actualBody
      exact bodyTyped.substitute (fresh.typed_substitution fitted) substituted

/-- The actual binary `Unfold` command replaces its pending left endpoint
by the independently authorized body image, retaining the ordered suffix.
Body typing is an admission obligation, not inferred from proof input. -/
theorem step_unfold_preserves_stack (signature : TermSignature) (definitions : Definition.Signature)
    (theorems : TheoremSignature) (context : Context) (hypotheses : List Preterm)
    (tables : Tables) (mode : Mode) (before after : Formats.MMB.State)
    (typed : TypedStore signature context before.store) (ranked : RankedStore context before.store)
    (arities : ∀ term declaration, signature term = some declaration →
      Statements.arityOf tables.terms term = some declaration.arguments.length)
    (available : ∀ (term : Nat) (entry : TermEntry) (commands : List UnifyCmd),
      tables.terms[term]? = some entry → entry.value = some commands →
      ∃ declaration body, Statements.termDecl tables.terms entry = some (declaration, some body) ∧
        signature term = some declaration ∧ definitions term = some body ∧
        Preterm.HasType signature (declaration.arguments ++ body.dummies.map Binder.bound)
          body.expression [] declaration.resultSort)
    (sound : StackSound signature definitions theorems context hypotheses before.store before.stack)
    (executed : step tables mode before .unfold = some after) :
    StackSound signature definitions theorems context hypotheses after.store after.stack := by
  simp only [step] at executed
  split at executed
  · rename_i position left right rest shaped
    obtain ⟨allocation, allocationRead, checked⟩ := Option.bind_eq_some_iff.mp executed
    rcases allocation with ⟨node, type⟩
    cases node with
    | var index => cases checked
    | app term positions =>
        obtain ⟨entry, entryRead, checked⟩ := Option.bind_eq_some_iff.mp checked
        obtain ⟨commands, valueRead, checked⟩ := Option.bind_eq_some_iff.mp checked
        obtain ⟨unifier, accepted, checked⟩ := Option.bind_eq_some_iff.mp checked
        have sameAfter := (Option.some.inj checked).symm
        obtain ⟨declaration, body, sourceRead, declared, defined, bodyTyped⟩ := available term entry commands entryRead valueRead
        obtain ⟨arguments, indices, image, leftDecoded, imageRead, unfolded, mainKept, _⟩ :=
          unifyRun_definition_unfolds signature definitions context tables before.store typed ranked arities
            term left position positions type entry declaration body commands rest before.hyps unifier
            allocationRead declared defined sourceRead valueRead accepted
        have imageTyping := authorized_unfolding_typed signature definitions context term declaration body arguments indices image
          declared defined bodyTyped unfolded
        have leftImage : ConvertedPointers signature definitions context before.store left position :=
          ⟨Preterm.applyArgs (.term term) arguments, image, declaration.resultSort, leftDecoded, imageRead,
            .unfold declared unfolded imageTyping⟩
        rw [sameAfter, mainKept]
        have original := shaped ▸ sound
        cases original with
        | expr positionTyped guarded =>
            cases guarded with
            | goal _ rightTyped resume =>
                refine StackSound.goal positionTyped rightTyped ?_
                intro converted
                obtain ⟨source, middle, sort, sourceRead, middleRead, firstConversion⟩ := leftImage
                obtain ⟨middle', result, otherSort, middleRead', resultRead, lastConversion⟩ := converted
                have sameImage : middle' = middle := Option.some.inj (middleRead'.symm.trans middleRead)
                subst middle'
                have sameSort : sort = otherSort :=
                  (firstConversion.typed.2.deterministic lastConversion.typed.1).2
                subst otherSort
                exact resume ⟨source, result, sort, sourceRead, resultRead, .trans firstConversion lastConversion⟩
  · cases executed

namespace Controls

private def regular : ExprType := ⟨0, false, ∅⟩
private def bound (index : Nat) : ExprType := ⟨0, true, {index}⟩
private def publicArgs : List ExprType := [bound 0, bound 1, bound 2, bound 3, bound 4, bound 5]
private def binaryEntry : TermEntry := ⟨0, [regular, regular], regular, none⟩
private def commands : List UnifyCmd := [.termSave 1, .termSave 0, .dummy 0, .dummy 0, .ref 3]
private def definitionEntry : TermEntry := ⟨0, [regular], regular, some commands⟩
private def binaryDecl : TermDecl := ⟨[.regular 0 ∅, .regular 0 ∅], 0, ∅⟩
private def definitionDecl : TermDecl := ⟨[.regular 0 ∅], 0, ∅⟩
private def sourceInner : Preterm := Preterm.applyArgs (.term 0) [.var 1, .var 2]
private def sourceOuter : Preterm := Preterm.applyArgs (.term 1) [sourceInner, .var 1]
private def imageInner : Preterm := Preterm.applyArgs (.term 0) [.var 6, .var 7]
private def imageOuter : Preterm := Preterm.applyArgs (.term 1) [imageInner, .var 6]
private def body : Definition.Body := ⟨[0, 0], sourceOuter⟩
private def signature : TermSignature := fun term =>
  if term = 0 ∨ term = 1 then some binaryDecl else if term = 2 then some definitionDecl else none
private def definitions : Definition.Signature := fun term => if term = 2 then some body else none
private def tables : Tables := ⟨[⟨false, false, true, false⟩], [binaryEntry, binaryEntry, definitionEntry], []⟩
private def sourceState : Statements.Decoding :=
  ⟨[some (.var 0), some sourceOuter, some sourceInner, some (.var 1), some (.var 2)], [0, 0]⟩
private def initial : Formats.MMB.State :=
  ⟨(List.range 6).map (fun index => ⟨.var index, bound index⟩), [], (List.range 6).map Elem.expr, [], 6, 6⟩
private def proofCommands : List ProofCmd := [.dummy 0, .dummy 0, .termSave 0, .ref 6, .termSave 1, .ref 3, .termSave 2]
private def finalState : Formats.MMB.State :=
  ⟨initial.store ++ [⟨.var 6, bound 6⟩, ⟨.var 7, bound 7⟩,
    ⟨.app 0 [6, 7], ⟨0, false, {6, 7}⟩⟩, ⟨.app 1 [8, 6], ⟨0, false, {6, 7}⟩⟩,
    ⟨.app 2 [3], ⟨0, false, {3}⟩⟩],
    [.expr 10, .expr 9], initial.heap ++ [.expr 6, .expr 7, .expr 8, .expr 9, .expr 10], [], 8, 8⟩
private def context : Context := [.bound 0, .bound 0, .bound 0, .bound 0, .bound 0, .bound 0, .bound 0, .bound 0]
private def main : List Elem := [.expr 0, .goal 0 1]
private def hypotheses : List Nat := [2, 1, 2]
private def before : Unifier := ⟨[9], [(3, false)], main, hypotheses⟩
private def after : Unifier := ⟨[], [(3, false), (9, true), (8, true), (6, false), (7, false)], main, hypotheses⟩

private theorem available (term : Nat) (entry : TermEntry) (read : tables.terms[term]? = some entry) :
    ∃ declaration definition, Statements.termDecl tables.terms entry = some (declaration, definition) ∧
      signature term = some declaration := by
  have inside : term < 3 := by
    have bounded := (List.getElem?_eq_some_iff.mp read).choose
    simpa [tables] using bounded
  have casesTerm : term = 0 ∨ term = 1 ∨ term = 2 := by omega
  rcases casesTerm with rfl | rfl | rfl
  · have same : entry = binaryEntry := by simpa [tables] using read.symm
    subst entry
    exact ⟨binaryDecl, none, by decide, by simp [signature]⟩
  · have same : entry = binaryEntry := by simpa [tables] using read.symm
    subst entry
    exact ⟨binaryDecl, none, by decide, by simp [signature]⟩
  · have same : entry = definitionEntry := by simpa [tables] using read.symm
    subst entry
    exact ⟨definitionDecl, some body, by decide, by simp [signature]⟩

private theorem arities (term : Nat) (entry : TermDecl) (read : signature term = some entry) :
    Statements.arityOf tables.terms term = some entry.arguments.length := by
  by_cases binary : term = 0 ∨ term = 1
  · have same : entry = binaryDecl := by simpa [signature, binary] using read.symm
    subst entry
    rcases binary with rfl | rfl <;> rfl
  · by_cases definition : term = 2
    · subst term
      have same : entry = definitionDecl := by simpa [signature] using read.symm
      subst entry
      rfl
    · simp [signature, binary, definition] at read

theorem actual_run_builds_renamed_nested_dummy_store :
    loadArgs tables.sorts publicArgs = some initial ∧
      run tables .assertion initial proofCommands = some finalState := by
  constructor
  · decide
  · simp [run, proofCommands, step, stepTerm, State.popExprs, State.popExpr, State.pop,
      State.typeOf, State.alloc, State.push, tables, initial, regular, bound, appDeps, finalState,
      binaryEntry, definitionEntry, ExprType.fits]
    ext rank
    simp [or_comm]

private theorem storeEvidence : TypedStore signature context finalState.store ∧ RankedStore context finalState.store := by
  have earned := MMBRunSoundness.run_initialized_fixed_store signature tables available publicArgs proofCommands initial finalState
    actual_run_builds_renamed_nested_dummy_store.1 actual_run_builds_renamed_nested_dummy_store.2
  exact earned

private theorem variable_decode (index : Nat) (inside : index < 8) :
    Soundness.decode finalState.store index = some (.var index) := by
  have bounded : index < 8 := inside
  interval_cases index <;> rw [Soundness.decode] <;> rfl

private theorem inner_decode : Soundness.decode finalState.store 8 = some imageInner := by
  have found : finalState.store[8]? = some ⟨.app 0 [6, 7], ⟨0, false, {6, 7}⟩⟩ := rfl
  rw [Soundness.decode, found]
  dsimp only
  rw [dif_pos (show ∀ argument ∈ [6, 7], argument < 8 from by decide)]
  rw [List.mapM_subtype (g := Soundness.decode finalState.store)]
  · simp [variable_decode, imageInner, Preterm.applyArgs]
  · intros; rfl

private theorem outer_decode : Soundness.decode finalState.store 9 = some imageOuter := by
  have found : finalState.store[9]? = some ⟨.app 1 [8, 6], ⟨0, false, {6, 7}⟩⟩ := rfl
  rw [Soundness.decode, found]
  dsimp only
  rw [dif_pos (show ∀ argument ∈ [8, 6], argument < 9 from by decide)]
  rw [List.mapM_subtype (g := Soundness.decode finalState.store)]
  · simp [inner_decode, variable_decode, imageOuter, Preterm.applyArgs]
  · intros; rfl

theorem definition_source_retains_two_dummies_and_saved_slot_order :
    Statements.decodeExpr (Statements.arityOf tables.terms) 1 (2 * commands.length + 2)
      (Statements.initial 1) commands = some (sourceOuter, sourceState, []) := by rfl

theorem actual_definition_stream_preserves_auxiliary_state :
    unifyRun finalState.store .definition before commands = some after := by rfl

theorem saved_nodes_are_exempt_but_dummy_images_remain_ordered :
    unsavedPositions after.heap = [3, 6, 7] ∧
      UnsavedImages finalState.store after.heap [.var 3, .var 6, .var 7] := by
  constructor
  · rfl
  · simp [UnsavedImages, unsavedPositions, after, variable_decode]

theorem renamed_nested_saved_definition_substitutes :
    Preterm.Substitutes (Substitution.ofList [.var 3, .var 6, .var 7]) sourceOuter imageOuter ∧
      Definition.FreshDummies context [.var 3] [0, 0] [6, 7] ∧
      SlotsSubstitute finalState.store (Substitution.ofList [.var 3, .var 6, .var 7]) sourceState.slots after.heap := by
  obtain ⟨indices, image, decoded, fresh, substituted, slots, images, _, _⟩ :=
    unifyRun_definition_body signature context finalState.store storeEvidence.1 storeEvidence.2 (Statements.arityOf tables.terms)
      arities 1 [3] [.var 3] 9 main hypotheses commands body sourceState after rfl
      (by simp [variable_decode]) definition_source_retains_two_dummies_and_saved_slot_order rfl
      actual_definition_stream_preserves_auxiliary_state
  have sameImage : image = imageOuter := Option.some.inj (decoded.symm.trans outer_decode)
  subst image
  have sameValues : [.var 3] ++ indices.map Preterm.var = [.var 3, .var 6, .var 7] :=
    Option.some.inj (images.symm.trans saved_nodes_are_exempt_but_dummy_images_remain_ordered.2)
  have mapped : indices.map Preterm.var = [6, 7].map Preterm.var := by simpa using sameValues
  have sameIndices : indices = [6, 7] := (List.map_inj_right (fun _ _ same => by cases same; rfl)).mp mapped
  subst indices
  exact ⟨substituted, fresh, slots⟩

theorem scoped_slots_remain_valid_after_later_image_extension :
    SlotsSubstitute finalState.store (Substitution.ofList [.var 3, .var 6, .var 7, .var 0]) sourceState.slots after.heap := by
  have inScope := (decodeExpr_scoped (Statements.arityOf tables.terms) 1 (2 * commands.length + 2)
    (Statements.initial 1) sourceState commands [] sourceOuter (SourceSlotsScoped.initial 1)
    definition_source_retains_two_dummies_and_saved_slot_order).2.1
  exact SlotsSubstitute.append_images finalState.store [.var 3, .var 6, .var 7] [.var 0] sourceState after.heap 1
    inScope rfl renamed_nested_saved_definition_substitutes.2.2

theorem decoded_definition_body_earns_kernel_unfolding :
    ∃ indices, Definition.Unfolds signature definitions context 2 [.var 3] indices imageOuter := by
  obtain ⟨images, indices, image, leftDecoded, decoded, unfolded, _, _⟩ :=
    unifyRun_definition_unfolds signature definitions context tables finalState.store storeEvidence.1 storeEvidence.2 arities
      2 10 9 [3] ⟨0, false, {3}⟩ definitionEntry definitionDecl body commands main hypotheses after
      rfl (by simp [signature]) (by simp [definitions]) (by decide) rfl actual_definition_stream_preserves_auxiliary_state
  have sameImage : image = imageOuter := Option.some.inj (decoded.symm.trans outer_decode)
  subst image
  have expectedLeft : Soundness.decode finalState.store 10 = some (Preterm.applyArgs (.term 2) [.var 3]) := by
    have found : finalState.store[10]? = some ⟨.app 2 [3], ⟨0, false, {3}⟩⟩ := rfl
    rw [Soundness.decode, found]
    dsimp only
    rw [dif_pos (show ∀ argument ∈ [3], argument < 10 from by decide)]
    rw [List.mapM_subtype (g := Soundness.decode finalState.store)]
    · simp [variable_decode]
    · intros; rfl
  have singleton : ∃ argument, images = [argument] := by
    cases unfolded with
    | @intro declaration _ _ declared _ fitted _ _ =>
        have same : declaration = definitionDecl := by simpa [signature] using declared.symm
        subst declaration
        cases fitted with
        | cons _ rest =>
            cases rest
            exact ⟨_, rfl⟩
  obtain ⟨argument, sameArguments⟩ := singleton
  subst images
  have sameArgument : argument = .var 3 := by
    simpa [Preterm.applyArgs] using Option.some.inj (leftDecoded.symm.trans expectedLeft)
  subst argument
  exact ⟨indices, unfolded⟩

theorem unfilled_definition_reservation_refused :
    Statements.decodeExpr (Statements.arityOf tables.terms) 1 12 (Statements.initial 1)
      [.termSave 1, .ref 1, .dummy 0] = none := by decide

theorem future_definition_source_and_heap_slots_refused :
    Statements.decodeExpr (Statements.arityOf tables.terms) 1 12 (Statements.initial 1) [.ref 5] = none ∧
      unifyRun finalState.store .definition before [.ref 5] = none := by
  constructor <;> decide

theorem repeated_dummy_image_refused :
    unifyRun finalState.store .definition ⟨[6, 6], [(3, false)], [], []⟩ [.dummy 0, .dummy 0] = none := by decide

theorem already_parameter_image_cannot_be_dummy :
    unifyRun finalState.store .definition ⟨[3], [(3, false)], [], []⟩ [.dummy 0] = none := by decide

theorem saved_node_exemption_does_not_exempt_unsaved_children :
    unifyStep finalState.store .definition ⟨[6], [(9, true), (6, false)], [], []⟩ (.dummy 0) = none := by decide

theorem saved_node_including_current_dummy_is_allowed :
    unifyStep finalState.store .definition ⟨[6], [(9, true), (3, false)], [], []⟩ (.dummy 0) =
      some ⟨[], [(9, true), (3, false), (6, false)], [], []⟩ := by rfl

theorem nonvariable_dummy_image_refused :
    unifyRun finalState.store .definition ⟨[8], [(3, false)], [], []⟩ [.dummy 0] = none := by decide

theorem wrong_dummy_sort_refused :
    unifyRun finalState.store .definition before [.termSave 1, .termSave 0, .dummy 1, .dummy 0, .ref 3] = none := by decide

theorem incorrect_repeated_pointer_refused :
    unifyRun finalState.store .definition before [.termSave 1, .termSave 0, .dummy 0, .dummy 0, .ref 4] = none := by decide

theorem definition_hypothesis_command_refused :
    unifyRun finalState.store .definition before [.hyp] = none := by decide

theorem out_of_scope_source_slot_cannot_supply_scope_invariant :
    ¬ SourceSlotsScoped 1 ⟨[some (.var 2)], []⟩ := by
  intro inScope
  have bound := inScope 0 (.var 2) rfl 2 Preterm.Occurs.var
  simp at bound

theorem corrupted_parameter_image_cannot_match_initial_slot :
    ¬ SlotsSubstitute finalState.store (Substitution.ofList [.var 4, .var 6, .var 7]) sourceState.slots after.heap := by
  intro matching
  obtain ⟨position, saved, image, read, decoded, substituted⟩ := matching.filled 0 (.var 0) rfl
  have fields : position = 3 ∧ saved = false := by simpa [after] using read.symm
  rcases fields with ⟨rfl, rfl⟩
  have sameImage : image = .var 3 := Option.some.inj (decoded.symm.trans (variable_decode 3 (by decide)))
  subst image
  cases substituted with
  | var lookup => simp [Substitution.ofList] at lookup

theorem unfinished_definition_stream_refused :
    Statements.decodeExpr (Statements.arityOf tables.terms) 1 12 (Statements.initial 1)
      [.termSave 1, .dummy 0] = none ∧
      unifyRun finalState.store .definition before [.termSave 1, .termSave 0, .dummy 0] = none := by
  constructor <;> decide

theorem unknown_source_arity_refused :
    Statements.decodeExpr (Statements.arityOf tables.terms) 1 12 (Statements.initial 1) [.term 99] = none := by decide

private theorem bodyTyped : Preterm.HasType signature
    (definitionDecl.arguments ++ body.dummies.map Binder.bound) body.expression [] definitionDecl.resultSort := by
  have first : Preterm.HasType signature [.regular 0 ∅, .bound 0, .bound 0] (.var 1) [] 0 :=
    .var (binder := .bound 0) rfl
  have second : Preterm.HasType signature [.regular 0 ∅, .bound 0, .bound 0] (.var 2) [] 0 :=
    .var (binder := .bound 0) rfl
  have inner : Preterm.HasType signature [.regular 0 ∅, .bound 0, .bound 0] sourceInner [] 0 :=
    .regular (.regular (.term (declaration := binaryDecl) (by simp [signature])) first) second
  exact Preterm.HasType.regular (.regular (.term (declaration := binaryDecl) (by simp [signature])) inner) first

private theorem definitionsAvailable (term : Nat) (entry : TermEntry) (value : List UnifyCmd)
    (read : tables.terms[term]? = some entry) (valueRead : entry.value = some value) :
    ∃ declaration definition, Statements.termDecl tables.terms entry = some (declaration, some definition) ∧
      signature term = some declaration ∧ definitions term = some definition ∧
      Preterm.HasType signature (declaration.arguments ++ definition.dummies.map Binder.bound)
        definition.expression [] declaration.resultSort := by
  have inside : term < 3 := by
    have bounded := (List.getElem?_eq_some_iff.mp read).choose
    simpa [tables] using bounded
  have casesTerm : term = 0 ∨ term = 1 ∨ term = 2 := by omega
  rcases casesTerm with rfl | rfl | rfl
  · have same : entry = binaryEntry := by simpa [tables] using read.symm
    subst entry
    cases valueRead
  · have same : entry = binaryEntry := by simpa [tables] using read.symm
    subst entry
    cases valueRead
  · have same : entry = definitionEntry := by simpa [tables] using read.symm
    subst entry
    exact ⟨definitionDecl, body, by decide, by simp [signature], by simp [definitions], bodyTyped⟩

private def unfoldingBefore : Formats.MMB.State := { finalState with stack := [.expr 9, .goal 10 9, .expr 0] }
private def unfoldingAfter : Formats.MMB.State := { finalState with stack := [.goal 9 9, .expr 0] }
private def noTheorems : TheoremSignature := fun _ => none

private theorem unfoldingStack :
    StackSound signature definitions noTheorems context [] unfoldingBefore.store unfoldingBefore.stack := by
  have root : TypedPointer signature context finalState.store 9 :=
    storeEvidence.1.pointer signature context finalState.store 9 _ (by rfl)
  have left : TypedPointer signature context finalState.store 10 :=
    storeEvidence.1.pointer signature context finalState.store 10 _ (by rfl)
  have parameter : TypedPointer signature context finalState.store 0 :=
    storeEvidence.1.pointer signature context finalState.store 0 _ (by rfl)
  exact .expr root (.goal left root (fun _ => .expr parameter .empty))

theorem actual_unfold_preserves_pending_goal_suffix :
    step tables .assertion unfoldingBefore .unfold = some unfoldingAfter ∧
      StackSound signature definitions noTheorems context [] unfoldingAfter.store unfoldingAfter.stack := by
  have executed : step tables .assertion unfoldingBefore .unfold = some unfoldingAfter := by rfl
  exact ⟨executed, step_unfold_preserves_stack signature definitions noTheorems context [] tables .assertion
    unfoldingBefore unfoldingAfter storeEvidence.1 storeEvidence.2 arities definitionsAvailable unfoldingStack executed⟩

theorem actual_unfold_then_refl_releases_only_checked_suffix :
    let finished := { finalState with stack := [.expr 0] }
    run tables .assertion unfoldingBefore [.unfold, .refl] = some finished ∧
      StackSound signature definitions noTheorems context [] finished.store finished.stack := by
  dsimp only
  have executed : step tables .assertion unfoldingAfter .refl = some { finalState with stack := [.expr 0] } := by rfl
  exact ⟨by rfl, step_refl_preserves_stack tables .assertion unfoldingAfter _
    actual_unfold_preserves_pending_goal_suffix.2 executed⟩

theorem wrong_unfold_dummy_reference_refused :
    let changedTables := { tables with terms := [binaryEntry, binaryEntry,
      { definitionEntry with value := some [.termSave 1, .termSave 0, .dummy 0, .dummy 0, .ref 4] }] }
    step changedTables .assertion unfoldingBefore .unfold = none := by decide

theorem unauthorized_body_environment_cannot_supply_definition_basis :
    ¬ ∃ declaration definition, Statements.termDecl tables.terms definitionEntry = some (declaration, some definition) ∧
      (none : Option Definition.Body) = some definition := by simp

end Controls

end Mettapedia.Languages.MM0.MeTTa.MMBDefinitionUnificationSoundness
