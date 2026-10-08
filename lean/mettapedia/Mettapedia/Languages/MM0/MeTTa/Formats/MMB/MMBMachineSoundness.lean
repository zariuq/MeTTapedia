import Mettapedia.Languages.MM0.MeTTa.Formats.MMB.MMBExecution

/-!
# Typing and ordered evidence for the MMB proof machine

The invariants here concern the retained machine's allocations and the
existing kernel judgments. Binder fitting uses `FitsBinder`; it does not
introduce a second expression checker. Conversion obligations guard only
the stack beneath them. Unification, dependency checking and preservation
for the remaining proof commands are separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.MMBMachineSoundness

open Formats.MMB
open Kernel

/-- Every allocated pointer decodes to a saturated kernel expression of its
recorded sort. A bound allocation must decode to a bound context variable. -/
structure TypedStore (signature : TermSignature) (context : Context) (store : List Alloc) : Prop where
  expression : ∀ position allocation, store[position]? = some allocation →
    ∃ expression, Soundness.decode store position = some expression ∧
      Preterm.HasType signature context expression [] allocation.type.sort ∧
      (allocation.type.bound = true →
        ∃ index, expression = .var index ∧
          context[index]? = some (.bound allocation.type.sort))

theorem termProof_initial_store_typed (signature : TermSignature) (sorts : List SortInfo)
    (args : List ExprType) (ret : ExprType) (loaded : Formats.MMB.State)
    (validated : loadArgs sorts (args ++ [ret]) = some loaded) :
    TypedStore signature (Statements.context args) (loaded.forTermProof args.length).store := by
  constructor
  intro position allocation read
  obtain ⟨store, _⟩ := MMBExecution.termProof_initial_roots sorts args ret loaded validated
  have insideStore := (List.getElem?_eq_some_iff.mp read).choose
  have inside : position < args.length := by simpa [store] using insideStore
  have found : (loaded.forTermProof args.length).store[position]? =
      some ⟨.var position, args[position]'inside⟩ := by
    rw [store, List.getElem?_map, List.getElem?_zipIdx, List.getElem?_eq_getElem inside]
    simp only [Option.map_some, Nat.zero_add]
  have same : allocation = ⟨.var position, args[position]'inside⟩ :=
    Option.some.inj (read.symm.trans found)
  cases same
  have decoded := MMBExecution.termProof_argument_decode sorts args ret loaded validated position inside
  obtain ⟨expression, expressionRead, typing⟩ :=
    MMBExecution.termProof_argument_hasType signature sorts args ret loaded validated position inside
  have sameExpression : Preterm.var position = expression :=
    Option.some.inj (decoded.symm.trans expressionRead)
  rw [← sameExpression] at typing
  refine ⟨.var position, decoded, typing, ?_⟩
  intro bound
  change (args[position]'inside).bound = true at bound
  refine ⟨position, rfl, ?_⟩
  simp [Statements.context, List.getElem?_map, List.getElem?_eq_getElem inside,
    Statements.binder, bound]

theorem TypedStore.fits_binder (signature : TermSignature) (context : Context) (store : List Alloc)
    (typed : TypedStore signature context store) (position : Nat) (source target : ExprType)
    (positions : List Nat) (read : (store[position]?).map (·.type) = some source)
    (compatible : source.fits target = true) :
    ∃ expression, Soundness.decode store position = some expression ∧
      Preterm.FitsBinder signature context expression (Statements.binder positions target) := by
  obtain ⟨allocation, allocationRead, rfl⟩ := Option.map_eq_some_iff.mp read
  obtain ⟨expression, expressionRead, typing, bound⟩ := typed.expression position allocation allocationRead
  simp only [ExprType.fits, Bool.and_eq_true, beq_iff_eq] at compatible
  rw [compatible.1] at typing
  refine ⟨expression, expressionRead, ?_⟩
  unfold Statements.binder
  split
  · rename_i targetBound
    have sourceBound : allocation.type.bound = true := by
      simpa [targetBound] using compatible.2
    obtain ⟨index, same, lookup⟩ := bound sourceBound
    rw [same]
    rw [compatible.1] at lookup
    exact .bound lookup
  · exact .regular typing

theorem TypedStore.arguments_fit (signature : TermSignature) (context : Context) (store : List Alloc)
    (typed : TypedStore signature context store) (positions : List Nat) (types targets : List ExprType)
    (binderPositions : List Nat) (read : positions.mapM (fun position =>
      (store[position]?).map (·.type)) = some types)
    (arity : positions.length = targets.length)
    (compatible : (types.zip targets).all (fun (source, target) => source.fits target) = true) :
    ∃ expressions, positions.mapM (Soundness.decode store) = some expressions ∧
      List.Forall₂ (Preterm.FitsBinder signature context) expressions
        (targets.map (Statements.binder binderPositions)) := by
  induction positions generalizing types targets with
  | nil =>
      have empty : targets = [] := List.length_eq_zero_iff.mp (by simpa using arity.symm)
      subst targets
      exact ⟨[], by simp, .nil⟩
  | cons position positions ih =>
      cases targets with
      | nil => simp at arity
      | cons target targets =>
          cases first : (store[position]?).map (·.type) with
          | none => simp [first] at read
          | some source =>
              cases rest : positions.mapM (fun position => (store[position]?).map (·.type)) with
              | none => simp [first, rest] at read
              | some earlier =>
                  simp [first, rest] at read
                  cases read
                  have fitted : source.fits target = true ∧
                      (earlier.zip targets).all (fun (source, target) => source.fits target) = true := by
                    simpa using compatible
                  obtain ⟨expression, expressionRead, fit⟩ := typed.fits_binder signature context store
                    position source target binderPositions first fitted.1
                  obtain ⟨expressions, tailRead, fits⟩ := ih earlier targets rest (by simpa using arity) fitted.2
                  exact ⟨expression :: expressions, by simp [expressionRead, tailRead], .cons fit fits⟩

/-- Application allocation preserves old pointer meanings and uses the
existing kernel application rule to type the new pointer. -/
theorem TypedStore.allocate_application (signature : TermSignature) (context : Context)
    (state : Formats.MMB.State) (typed : TypedStore signature context state.store)
    (term : Nat) (args : List Nat) (expressions : List Preterm) (type : ExprType)
    (declaration : TermDecl) (declared : signature term = some declaration)
    (decoded : args.mapM (Soundness.decode state.store) = some expressions)
    (fitted : List.Forall₂ (Preterm.FitsBinder signature context) expressions declaration.arguments)
    (earlier : ∀ arg ∈ args, arg < state.store.length)
    (sameSort : type.sort = declaration.resultSort) (regular : type.bound = false) :
    TypedStore signature context (state.alloc ⟨.app term args, type⟩).1.store := by
  change TypedStore signature context (state.store ++ [⟨.app term args, type⟩])
  constructor
  intro position allocation read
  by_cases old : position < state.store.length
  · rw [List.getElem?_append_left old] at read
    obtain ⟨expression, expressionRead, typing, bound⟩ := typed.expression position allocation read
    exact ⟨expression, (MMBExecution.decode_append_preserves state.store
      [⟨.app term args, type⟩] position old).trans expressionRead, typing, bound⟩
  · have inside := (List.getElem?_eq_some_iff.mp read).choose
    have last : position = state.store.length := by simp only [List.length_append,
      List.length_cons, List.length_nil] at inside; omega
    subst position
    have fresh : (state.store ++ [⟨.app term args, type⟩])[state.store.length]? =
        some (⟨.app term args, type⟩ : Alloc) := by simp
    have same : allocation = ⟨.app term args, type⟩ := Option.some.inj (read.symm.trans fresh)
    cases same
    refine ⟨Preterm.applyArgs (.term term) expressions, ?_, ?_, ?_⟩
    · have decodedNew := MMBExecution.decode_alloc_application state term args type earlier
      rw [decoded] at decodedNew
      exact decodedNew
    · change Preterm.HasType signature context _ [] type.sort
      rw [sameSort]
      exact (Preterm.HasType.term declared).applyArgs fitted
    · intro bound
      change type.bound = true at bound
      rw [regular] at bound
      cases bound

/-- A successful actual `Term`/`TermSave` transition preserves allocation
typing when its previously declared table entry matches the given signature. -/
theorem stepTerm_preserves_typing (signature : TermSignature) (context : Context)
    (tables : Tables) (mode : Mode) (before after : Formats.MMB.State)
    (term : Nat) (save : Bool) (entry : TermEntry) (declaration : TermDecl)
    (typed : TypedStore signature context before.store)
    (entryRead : tables.terms[term]? = some entry)
    (declared : signature term = some declaration)
    (argumentsAgree : declaration.arguments = Statements.context entry.args)
    (sortAgree : declaration.resultSort = entry.sort)
    (executed : stepTerm tables mode before term save = some after) :
    TypedStore signature context after.store := by
  obtain ⟨args, types, count, readings, compatible, store⟩ :=
    stepTerm_operands tables mode before after term save entry entryRead executed
  obtain ⟨expressions, decoded, fitted⟩ := TypedStore.arguments_fit signature context before.store
    typed args types entry.args (Statements.boundPositions entry.args) readings count compatible
  have fittedDeclaration : List.Forall₂ (Preterm.FitsBinder signature context)
      expressions declaration.arguments := by
    simpa only [argumentsAgree, Statements.context] using fitted
  rw [store]
  exact TypedStore.allocate_application signature context before typed term args expressions
    ⟨entry.sort, false, appDeps mode entry.args entry.ret types⟩ declaration declared decoded
    fittedDeclaration (State.typesOf_allocated before args types readings) sortAgree.symm rfl

theorem stepThm_preserves_typing (signature : TermSignature) (context : Context)
    (tables : Tables) (before after : Formats.MMB.State) (theorem_ : Nat) (save : Bool)
    (typed : TypedStore signature context before.store)
    (executed : stepThm tables before theorem_ save = some after) :
    TypedStore signature context after.store := by
  rw [stepThm_keeps_store tables before after theorem_ save executed]
  exact typed

theorem self_referential_allocation_rejected (state : Formats.MMB.State)
    (term : Nat) (type : ExprType) :
    Soundness.decode (state.alloc ⟨.app term [state.store.length], type⟩).1.store
      (state.alloc ⟨.app term [state.store.length], type⟩).2 = none := by
  change Soundness.decode (state.store ++ [⟨.app term [state.store.length], type⟩])
    state.store.length = none
  have found : (state.store ++ [⟨.app term [state.store.length], type⟩])[state.store.length]? =
      some (⟨.app term [state.store.length], type⟩ : Alloc) := by simp
  rw [Soundness.decode, found]
  simp

/-- A pointer denotes a saturated expression in the existing typing judgment. -/
def TypedPointer (signature : TermSignature) (context : Context) (store : List Alloc)
    (position : Nat) : Prop :=
  ∃ expression sort, Soundness.decode store position = some expression ∧
    Preterm.HasType signature context expression [] sort

/-- Completed proof evidence for a pointer, without pending obligations. -/
def ProvenPointer (signature : TermSignature) (definitions : Definition.Signature)
    (theorems : TheoremSignature) (context : Context) (hypotheses : List Preterm)
    (store : List Alloc) (position : Nat) : Prop :=
  ∃ expression sort, Soundness.decode store position = some expression ∧
    Preterm.HasType signature context expression [] sort ∧
    Derives signature definitions theorems context hypotheses expression

/-- Completed conversion evidence retains both decoded endpoints and its sort. -/
def ConvertedPointers (signature : TermSignature) (definitions : Definition.Signature)
    (context : Context) (store : List Alloc) (left right : Nat) : Prop :=
  ∃ leftExpression rightExpression sort,
    Soundness.decode store left = some leftExpression ∧
    Soundness.decode store right = some rightExpression ∧
    Converts signature definitions context leftExpression rightExpression sort

section OrderedEvidence

variable {signature : TermSignature} {definitions : Definition.Signature}
  {theorems : TheoremSignature} {context : Context} {hypotheses : List Preterm}
  {store : List Alloc} {left right position : Nat}

theorem TypedPointer.refl (typed : TypedPointer signature context store position) :
    ConvertedPointers signature definitions context store position position := by
  obtain ⟨expression, sort, decoded, typing⟩ := typed
  exact ⟨expression, expression, sort, decoded, decoded, .refl typing⟩

theorem ProvenPointer.typed
    (proved : ProvenPointer signature definitions theorems context hypotheses store position) :
    TypedPointer signature context store position := by
  obtain ⟨expression, sort, decoded, typing, _⟩ := proved
  exact ⟨expression, sort, decoded, typing⟩

theorem ConvertedPointers.symm
    (converted : ConvertedPointers signature definitions context store left right) :
    ConvertedPointers signature definitions context store right left := by
  obtain ⟨leftExpression, rightExpression, sort, leftRead, rightRead, conversion⟩ := converted
  exact ⟨rightExpression, leftExpression, sort, rightRead, leftRead, .symm conversion⟩

theorem ConvertedPointers.typed
    (converted : ConvertedPointers signature definitions context store left right) :
    TypedPointer signature context store left ∧ TypedPointer signature context store right := by
  obtain ⟨leftExpression, rightExpression, sort, leftRead, rightRead, conversion⟩ := converted
  exact ⟨⟨leftExpression, sort, leftRead, conversion.typed.1⟩,
    ⟨rightExpression, sort, rightRead, conversion.typed.2⟩⟩

theorem ProvenPointer.convert
    (proved : ProvenPointer signature definitions theorems context hypotheses store left)
    (converted : ConvertedPointers signature definitions context store left right) :
    ProvenPointer signature definitions theorems context hypotheses store right := by
  obtain ⟨expression, _, decoded, _, derivation⟩ := proved
  obtain ⟨leftExpression, rightExpression, sort, leftRead, rightRead, conversion⟩ := converted
  have same : expression = leftExpression := Option.some.inj (decoded.symm.trans leftRead)
  subst expression
  exact ⟨rightExpression, sort, rightRead, conversion.typed.2, .conversion conversion derivation⟩

end OrderedEvidence

theorem decoded_pointer_allocated (store : List Alloc) (position : Nat) (expression : Preterm)
    (decoded : Soundness.decode store position = some expression) : position < store.length := by
  rw [Soundness.decode] at decoded
  cases found : store[position]? with
  | none =>
      rw [found] at decoded
      cases decoded
  | some allocation => exact (List.getElem?_eq_some_iff.mp found).choose

section StoreExtension

variable {signature : TermSignature} {definitions : Definition.Signature}
  {theorems : TheoremSignature} {context : Context} {hypotheses : List Preterm}
  {store : List Alloc} {left right position : Nat}

theorem TypedPointer.allocated (typed : TypedPointer signature context store position) :
    position < store.length := by
  obtain ⟨expression, _, decoded, _⟩ := typed
  exact decoded_pointer_allocated store position expression decoded

theorem TypedPointer.append_store (typed : TypedPointer signature context store position)
    (suffix : List Alloc) : TypedPointer signature context (store ++ suffix) position := by
  obtain ⟨expression, sort, decoded, typing⟩ := typed
  exact ⟨expression, sort, (MMBExecution.decode_append_preserves store suffix position
    (decoded_pointer_allocated store position expression decoded)).trans decoded, typing⟩

theorem ProvenPointer.append_store
    (proved : ProvenPointer signature definitions theorems context hypotheses store position)
    (suffix : List Alloc) :
    ProvenPointer signature definitions theorems context hypotheses (store ++ suffix) position := by
  obtain ⟨expression, sort, decoded, typing, derivation⟩ := proved
  exact ⟨expression, sort, (MMBExecution.decode_append_preserves store suffix position
    (decoded_pointer_allocated store position expression decoded)).trans decoded, typing, derivation⟩

theorem ConvertedPointers.append_store_iff (suffix : List Alloc)
    (leftAllocated : left < store.length) (rightAllocated : right < store.length) :
    ConvertedPointers signature definitions context (store ++ suffix) left right ↔
      ConvertedPointers signature definitions context store left right := by
  unfold ConvertedPointers
  rw [MMBExecution.decode_append_preserves store suffix left leftAllocated,
    MMBExecution.decode_append_preserves store suffix right rightAllocated]

theorem ConvertedPointers.append_store
    (converted : ConvertedPointers signature definitions context store left right)
    (suffix : List Alloc) :
    ConvertedPointers signature definitions context (store ++ suffix) left right :=
  (ConvertedPointers.append_store_iff suffix converted.typed.1.allocated converted.typed.2.allocated).mpr
    converted

end StoreExtension

/-- Heap entries carry completed evidence. A conversion goal cannot be a
certified heap entry. -/
def CertifiedElem (signature : TermSignature) (definitions : Definition.Signature)
    (theorems : TheoremSignature) (context : Context) (hypotheses : List Preterm)
    (store : List Alloc) : Elem → Prop
  | .expr position => TypedPointer signature context store position
  | .proof position => ProvenPointer signature definitions theorems context hypotheses store position
  | .conv left right => ConvertedPointers signature definitions context store left right
  | .goal _ _ => False

/-- An ordered invariant on the actual machine stack. A goal guards exactly
its suffix; entries above that goal require completed evidence already. -/
inductive StackSound (signature : TermSignature) (definitions : Definition.Signature)
    (theorems : TheoremSignature) (context : Context) (hypotheses : List Preterm)
    (store : List Alloc) : List Elem → Prop where
  | empty : StackSound signature definitions theorems context hypotheses store []
  | expr {position : Nat} {rest : List Elem} :
      TypedPointer signature context store position →
      StackSound signature definitions theorems context hypotheses store rest →
      StackSound signature definitions theorems context hypotheses store (.expr position :: rest)
  | proof {position : Nat} {rest : List Elem} :
      ProvenPointer signature definitions theorems context hypotheses store position →
      StackSound signature definitions theorems context hypotheses store rest →
      StackSound signature definitions theorems context hypotheses store (.proof position :: rest)
  | conv {left right : Nat} {rest : List Elem} :
      ConvertedPointers signature definitions context store left right →
      StackSound signature definitions theorems context hypotheses store rest →
      StackSound signature definitions theorems context hypotheses store (.conv left right :: rest)
  | goal {left right : Nat} {rest : List Elem} :
      TypedPointer signature context store left → TypedPointer signature context store right →
      (ConvertedPointers signature definitions context store left right →
        StackSound signature definitions theorems context hypotheses store rest) →
      StackSound signature definitions theorems context hypotheses store (.goal left right :: rest)

def HeapSound (signature : TermSignature) (definitions : Definition.Signature)
    (theorems : TheoremSignature) (context : Context) (hypotheses : List Preterm)
    (store : List Alloc) (heap : List Elem) : Prop :=
  ∀ element ∈ heap, CertifiedElem signature definitions theorems context hypotheses store element

section StackLaws

variable {signature : TermSignature} {definitions : Definition.Signature}
  {theorems : TheoremSignature} {context : Context} {hypotheses : List Preterm}
  {store : List Alloc} {left right position : Nat} {rest : List Elem}

theorem StackSound.completed_head {element : Elem}
    (sound : StackSound signature definitions theorems context hypotheses store (element :: rest))
    (completed : ∀ left right, element ≠ .goal left right) :
    CertifiedElem signature definitions theorems context hypotheses store element := by
  cases sound with
  | expr typed _ => exact typed
  | proof proved _ => exact proved
  | conv converted _ => exact converted
  | goal _ _ _ => exact False.elim (completed _ _ rfl)

theorem StackSound.push_certified {element : Elem}
    (certified : CertifiedElem signature definitions theorems context hypotheses store element)
    (sound : StackSound signature definitions theorems context hypotheses store rest) :
    StackSound signature definitions theorems context hypotheses store (element :: rest) := by
  cases element with
  | expr position => exact .expr certified sound
  | proof position => exact .proof certified sound
  | conv left right => exact .conv certified sound
  | goal left right => exact False.elim certified

theorem StackSound.conversion_obligation
    (sound : StackSound signature definitions theorems context hypotheses store
      (.proof right :: .expr left :: rest)) :
    StackSound signature definitions theorems context hypotheses store
      (.goal left right :: .proof left :: rest) := by
  cases sound with
  | proof proved tail =>
      cases tail with
      | expr typed restSound =>
          exact .goal typed proved.typed (fun converted => .proof (proved.convert converted.symm) restSound)

theorem StackSound.reflexivity
    (sound : StackSound signature definitions theorems context hypotheses store
      (.goal position position :: rest)) :
    StackSound signature definitions theorems context hypotheses store rest := by
  cases sound with
  | goal typed _ resume => exact resume typed.refl

theorem StackSound.symmetry
    (sound : StackSound signature definitions theorems context hypotheses store
      (.goal left right :: rest)) :
    StackSound signature definitions theorems context hypotheses store (.goal right left :: rest) := by
  cases sound with
  | goal leftTyped rightTyped resume =>
      exact .goal rightTyped leftTyped (fun converted => resume converted.symm)

theorem StackSound.conversion_cut
    (sound : StackSound signature definitions theorems context hypotheses store
      (.goal left right :: rest)) :
    StackSound signature definitions theorems context hypotheses store
      (.goal left right :: .conv left right :: rest) := by
  cases sound with
  | goal leftTyped rightTyped resume =>
      exact .goal leftTyped rightTyped (fun converted => .conv converted (resume converted))

/-- A final singleton proof stack supplies a derivation, with no obligation
premise. Preservation of this invariant must be proved for each command. -/
theorem StackSound.final_proof
    (sound : StackSound signature definitions theorems context hypotheses store [.proof position]) :
    ∃ expression, Soundness.decode store position = some expression ∧
      Derives signature definitions theorems context hypotheses expression := by
  cases sound with
  | proof proved _ =>
      obtain ⟨expression, _, decoded, _, derivation⟩ := proved
      exact ⟨expression, decoded, derivation⟩

theorem heap_conversion_goals_refused (heap : List Elem)
    (sound : HeapSound signature definitions theorems context hypotheses store heap) :
    Elem.goal left right ∉ heap := by
  intro member
  exact sound (.goal left right) member

theorem HeapSound.lookup {heap : List Elem} {element : Elem} {index : Nat}
    (sound : HeapSound signature definitions theorems context hypotheses store heap)
    (found : heap[index]? = some element) :
    CertifiedElem signature definitions theorems context hypotheses store element :=
  sound element (List.mem_of_getElem? found)

theorem HeapSound.append_certified {heap : List Elem} {element : Elem}
    (sound : HeapSound signature definitions theorems context hypotheses store heap)
    (certified : CertifiedElem signature definitions theorems context hypotheses store element) :
    HeapSound signature definitions theorems context hypotheses store (heap ++ [element]) := by
  intro other member
  rcases List.mem_append.mp member with old | fresh
  · exact sound other old
  · have same : other = element := by simpa using fresh
    subst other
    exact certified

theorem CertifiedElem.append_store {element : Elem}
    (certified : CertifiedElem signature definitions theorems context hypotheses store element)
    (suffix : List Alloc) :
    CertifiedElem signature definitions theorems context hypotheses (store ++ suffix) element := by
  cases element with
  | expr position => exact TypedPointer.append_store certified suffix
  | proof position => exact ProvenPointer.append_store certified suffix
  | conv left right => exact ConvertedPointers.append_store certified suffix
  | goal left right => exact False.elim certified

theorem StackSound.append_store
    (sound : StackSound signature definitions theorems context hypotheses store rest)
    (suffix : List Alloc) :
    StackSound signature definitions theorems context hypotheses (store ++ suffix) rest := by
  induction sound with
  | empty => exact .empty
  | expr typed _ ih => exact .expr (typed.append_store suffix) ih
  | proof proved _ ih => exact .proof (proved.append_store suffix) ih
  | conv converted _ ih => exact .conv (converted.append_store suffix) ih
  | goal leftTyped rightTyped _ ih =>
      exact .goal (leftTyped.append_store suffix) (rightTyped.append_store suffix)
        (fun converted => ih ((ConvertedPointers.append_store_iff suffix
          leftTyped.allocated rightTyped.allocated).mp converted))

theorem HeapSound.append_store {heap : List Elem}
    (sound : HeapSound signature definitions theorems context hypotheses store heap)
    (suffix : List Alloc) :
    HeapSound signature definitions theorems context hypotheses (store ++ suffix) heap :=
  fun element member => (sound element member).append_store suffix

end StackLaws

/-- Invert curried application typing in declaration order. This recovers
the actual bound-slot restrictions instead of assuming all children merely
have the right sort. -/
theorem application_typing_arguments (signature : TermSignature) (context : Context)
    (source : Preterm) (arguments : List Preterm) (remaining : Context) (sort : Nat)
    (typed : Preterm.HasType signature context (Preterm.applyArgs source arguments) remaining sort) :
    ∃ binders, Preterm.HasType signature context source (binders ++ remaining) sort ∧
      List.Forall₂ (Preterm.FitsBinder signature context) arguments binders := by
  induction arguments generalizing source with
  | nil => exact ⟨[], typed, .nil⟩
  | cons argument arguments ih =>
      obtain ⟨binders, applied, fitted⟩ := ih (.app source argument) typed
      cases applied with
      | bound functionTyped lookup => exact ⟨.bound _ :: binders, functionTyped, .cons (.bound lookup) fitted⟩
      | regular functionTyped argumentTyped =>
          exact ⟨.regular _ _ :: binders, functionTyped, .cons (.regular argumentTyped) fitted⟩

theorem saturated_application_declaration (signature : TermSignature) (context : Context)
    (term : Nat) (arguments : List Preterm) (sort : Nat)
    (typed : Preterm.HasType signature context (Preterm.applyArgs (.term term) arguments) [] sort) :
    ∃ declaration, signature term = some declaration ∧ declaration.resultSort = sort ∧
      List.Forall₂ (Preterm.FitsBinder signature context) arguments declaration.arguments := by
  obtain ⟨binders, headTyped, fitted⟩ := application_typing_arguments signature context
    (.term term) arguments [] sort typed
  simp only [List.append_nil] at headTyped
  cases headTyped with
  | term lookup => exact ⟨_, lookup, rfl, by simpa using fitted⟩

theorem TypedStore.application (signature : TermSignature) (context : Context)
    (store : List Alloc) (typed : TypedStore signature context store)
    (position term : Nat) (arguments : List Nat) (type : ExprType)
    (found : store[position]? = some ⟨.app term arguments, type⟩) :
    ∃ expressions declaration,
      arguments.mapM (Soundness.decode store) = some expressions ∧
      Soundness.decode store position = some (Preterm.applyArgs (.term term) expressions) ∧
      signature term = some declaration ∧
      List.Forall₂ (Preterm.FitsBinder signature context) expressions declaration.arguments ∧
      ∀ argument ∈ arguments, argument < position := by
  obtain ⟨expression, decoded, typing, _⟩ := typed.expression position _ found
  have read := decoded
  rw [Soundness.decode, found] at read
  dsimp only at read
  split at read
  · rename_i earlier
    rw [List.mapM_subtype (g := Soundness.decode store)] at read
    · obtain ⟨expressions, argumentsRead, rfl⟩ := Option.map_eq_some_iff.mp read
      obtain ⟨declaration, declared, _, fitted⟩ := saturated_application_declaration signature
        context term expressions type.sort typing
      exact ⟨expressions, declaration, by simpa using argumentsRead, decoded, declared, fitted, earlier⟩
    · intros
      rfl
  · cases read

theorem TypedStore.pointer (signature : TermSignature) (context : Context)
    (store : List Alloc) (typed : TypedStore signature context store)
    (position : Nat) (allocation : Alloc) (found : store[position]? = some allocation) :
    TypedPointer signature context store position := by
  obtain ⟨expression, decoded, typing, _⟩ := typed.expression position allocation found
  exact ⟨expression, allocation.type.sort, decoded, typing⟩

theorem decoded_arguments (store : List Alloc) (positions : List Nat) (expressions : List Preterm)
    (read : positions.mapM (Soundness.decode store) = some expressions) :
    List.Forall₂ (fun position expression => Soundness.decode store position = some expression)
      positions expressions := by
  induction positions generalizing expressions with
  | nil =>
      have empty : expressions = [] := by simpa using read.symm
      subst expressions
      exact .nil
  | cons position positions ih =>
      cases first : Soundness.decode store position with
      | none => simp [first] at read
      | some expression =>
          cases tail : positions.mapM (Soundness.decode store) with
          | none => simp [first, tail] at read
          | some earlier =>
              have same : expression :: earlier = expressions := by simpa [first, tail] using read
              subst expressions
              exact .cons first (ih earlier tail)

theorem converted_at_binder (signature : TermSignature) (definitions : Definition.Signature)
    (context : Context) (store : List Alloc) (left right : Nat)
    (leftExpression rightExpression : Preterm) (binder : Binder)
    (leftRead : Soundness.decode store left = some leftExpression)
    (rightRead : Soundness.decode store right = some rightExpression)
    (leftFits : Preterm.FitsBinder signature context leftExpression binder)
    (converted : ConvertedPointers signature definitions context store left right) :
    Converts signature definitions context leftExpression rightExpression binder.sort := by
  obtain ⟨leftDecoded, rightDecoded, sort, leftFound, rightFound, conversion⟩ := converted
  have leftSame : leftDecoded = leftExpression := Option.some.inj (leftFound.symm.trans leftRead)
  have rightSame : rightDecoded = rightExpression := Option.some.inj (rightFound.symm.trans rightRead)
  subst leftDecoded
  subst rightDecoded
  have sameSort := (conversion.typed.1.deterministic leftFits.hasType).2
  rw [← sameSort]
  exact conversion

/-- Congruence exposes child goals in their actual order. Each discharged
child produces the corresponding typed kernel conversion before the
continuation for the remaining children is available. -/
theorem StackSound.argument_goals
    (signature : TermSignature) (definitions : Definition.Signature) (theorems : TheoremSignature)
    (context : Context) (hypotheses : List Preterm) (store : List Alloc)
    (leftPositions rightPositions : List Nat) (leftExpressions rightExpressions : List Preterm)
    (binders : Context) (rest : List Elem)
    (leftDecoded : List.Forall₂ (fun position expression => Soundness.decode store position = some expression)
      leftPositions leftExpressions)
    (rightDecoded : List.Forall₂ (fun position expression => Soundness.decode store position = some expression)
      rightPositions rightExpressions)
    (leftFits : List.Forall₂ (Preterm.FitsBinder signature context) leftExpressions binders)
    (rightFits : List.Forall₂ (Preterm.FitsBinder signature context) rightExpressions binders)
    (resume : ConvertsArgs signature definitions context leftExpressions rightExpressions binders →
      StackSound signature definitions theorems context hypotheses store rest) :
    StackSound signature definitions theorems context hypotheses store
      ((leftPositions.zip rightPositions).map (fun (left, right) => Elem.goal left right) ++ rest) := by
  induction leftFits generalizing leftPositions rightPositions rightExpressions with
  | nil =>
      cases leftDecoded
      cases rightFits
      cases rightDecoded
      exact resume .nil
  | cons leftFit leftTail ih =>
      cases leftDecoded with
      | cons leftRead leftReads =>
          cases rightFits with
          | cons rightFit rightTail =>
              cases rightDecoded with
              | cons rightRead rightReads =>
                  refine .goal ⟨_, _, leftRead, leftFit.hasType⟩
                    ⟨_, _, rightRead, rightFit.hasType⟩ (fun converted => ?_)
                  exact ih _ _ _ leftReads rightReads rightTail (fun conversions =>
                    resume (.cons leftFit rightFit
                      (converted_at_binder _ _ _ _ _ _ _ _ _ leftRead rightRead leftFit converted)
                      conversions))

section ConversionCommands

variable {signature : TermSignature} {definitions : Definition.Signature}
  {theorems : TheoremSignature} {context : Context} {hypotheses : List Preterm}

theorem StackSound.popExpr (before after : Formats.MMB.State) (position : Nat)
    (sound : StackSound signature definitions theorems context hypotheses before.store before.stack)
    (popped : before.popExpr = some (position, after)) :
    StackSound signature definitions theorems context hypotheses after.store after.stack := by
  cases shape : before.stack with
  | nil => simp [State.popExpr, State.pop, shape] at popped
  | cons element rest =>
      cases element <;> simp [State.popExpr, State.pop, shape] at popped
      obtain ⟨rfl, rfl⟩ := popped
      have shaped := shape ▸ sound
      cases shaped with
      | expr _ tail => exact tail

theorem StackSound.popExprs (before after : Formats.MMB.State) (count : Nat) (positions : List Nat)
    (sound : StackSound signature definitions theorems context hypotheses before.store before.stack)
    (popped : before.popExprs count = some (positions, after)) :
    StackSound signature definitions theorems context hypotheses after.store after.stack := by
  induction count generalizing before positions with
  | zero =>
      simp only [State.popExprs, Option.some.injEq, Prod.mk.injEq] at popped
      obtain ⟨_, rfl⟩ := popped
      exact sound
  | succ count ih =>
      cases first : before.popExpr with
      | none => simp [State.popExprs, first] at popped
      | some pair =>
          rcases pair with ⟨last, middle⟩
          cases earlier : middle.popExprs count with
          | none => simp [State.popExprs, first, earlier] at popped
          | some pair =>
              rcases pair with ⟨firsts, finish⟩
              simp [State.popExprs, first, earlier] at popped
              obtain ⟨_, rfl⟩ := popped
              exact ih middle firsts (sound.popExpr before middle last first) earlier

theorem stepTerm_preserves_evidence (tables : Tables) (mode : Mode)
    (before after : Formats.MMB.State) (term : Nat) (save : Bool)
    (entry : TermEntry) (declaration : TermDecl)
    (typed : TypedStore signature context before.store)
    (sound : StackSound signature definitions theorems context hypotheses before.store before.stack)
    (heap : HeapSound signature definitions theorems context hypotheses before.store before.heap)
    (entryRead : tables.terms[term]? = some entry)
    (declared : signature term = some declaration)
    (argumentsAgree : declaration.arguments = Statements.context entry.args)
    (sortAgree : declaration.resultSort = entry.sort)
    (executed : stepTerm tables mode before term save = some after) :
    TypedStore signature context after.store ∧
      StackSound signature definitions theorems context hypotheses after.store after.stack ∧
      HeapSound signature definitions theorems context hypotheses after.store after.heap := by
  have typedAfter := stepTerm_preserves_typing signature context tables mode before after term save
    entry declaration typed entryRead declared argumentsAgree sortAgree executed
  refine ⟨typedAfter, ?_⟩
  unfold stepTerm at executed
  change (tables.terms[term]?).bind _ = some after at executed
  rw [entryRead, Option.bind_some] at executed
  cases popped : before.popExprs entry.args.length with
  | none => simp [popped] at executed
  | some pair =>
      rcases pair with ⟨args, state⟩
      change (before.popExprs entry.args.length).bind _ = some after at executed
      rw [popped, Option.bind_some] at executed
      cases readings : args.mapM state.typeOf with
      | none => simp [readings] at executed
      | some types =>
          change (args.mapM state.typeOf).bind _ = some after at executed
          rw [readings, Option.bind_some] at executed
          split at executed
          · have poppedSound := sound.popExprs before state entry.args.length args popped
            have kept := State.popExprs_keeps_state before state entry.args.length args popped
            have storeKept : state.store = before.store := by
              simpa only using congrArg State.store kept
            have heapKept : state.heap = before.heap := by
              simpa only using congrArg State.heap kept
            have poppedHeap : HeapSound signature definitions theorems context hypotheses
                state.store state.heap := by simpa only [storeKept, heapKept] using heap
            let allocation : Alloc := ⟨.app term args,
              ⟨entry.sort, false, appDeps mode entry.args entry.ret types⟩⟩
            have extendedStack := poppedSound.append_store [allocation]
            have extendedHeap := poppedHeap.append_store [allocation]
            have fresh : (state.store ++ [allocation])[state.store.length]? = some allocation := by simp
            cases save <;> simp [State.alloc, State.push] at executed
            all_goals
              subst after
              have pointer := TypedStore.pointer signature context (state.store ++ [allocation])
                typedAfter state.store.length allocation fresh
            · exact ⟨.expr pointer extendedStack, extendedHeap⟩
            · exact ⟨.expr pointer extendedStack, extendedHeap.append_certified pointer⟩
          · simp at executed

theorem step_conv_preserves_stack (tables : Tables) (mode : Mode)
    (before after : Formats.MMB.State)
    (sound : StackSound signature definitions theorems context hypotheses before.store before.stack)
    (executed : step tables mode before .conv = some after) :
    StackSound signature definitions theorems context hypotheses after.store after.stack := by
  simp only [step] at executed
  split at executed
  · rename_i right left rest shape
    have same := Option.some.inj executed
    subst after
    exact (shape ▸ sound).conversion_obligation
  · simp at executed

theorem step_refl_preserves_stack (tables : Tables) (mode : Mode)
    (before after : Formats.MMB.State)
    (sound : StackSound signature definitions theorems context hypotheses before.store before.stack)
    (executed : step tables mode before .refl = some after) :
    StackSound signature definitions theorems context hypotheses after.store after.stack := by
  simp only [step] at executed
  split at executed
  · rename_i left right rest shape
    split at executed
    · rename_i same
      subst right
      have stateSame := Option.some.inj executed
      subst after
      exact (shape ▸ sound).reflexivity
    · simp at executed
  · simp at executed

theorem step_symm_preserves_stack (tables : Tables) (mode : Mode)
    (before after : Formats.MMB.State)
    (sound : StackSound signature definitions theorems context hypotheses before.store before.stack)
    (executed : step tables mode before .symm = some after) :
    StackSound signature definitions theorems context hypotheses after.store after.stack := by
  simp only [step] at executed
  split at executed
  · rename_i left right rest shape
    have same := Option.some.inj executed
    subst after
    exact (shape ▸ sound).symmetry
  · simp at executed

theorem step_convCut_preserves_stack (tables : Tables) (mode : Mode)
    (before after : Formats.MMB.State)
    (sound : StackSound signature definitions theorems context hypotheses before.store before.stack)
    (executed : step tables mode before .convCut = some after) :
    StackSound signature definitions theorems context hypotheses after.store after.stack := by
  simp only [step] at executed
  split at executed
  · rename_i left right rest shape
    have same := Option.some.inj executed
    subst after
    exact (shape ▸ sound).conversion_cut
  · simp at executed

theorem step_convSave_preserves_evidence (tables : Tables) (mode : Mode)
    (before after : Formats.MMB.State)
    (sound : StackSound signature definitions theorems context hypotheses before.store before.stack)
    (heap : HeapSound signature definitions theorems context hypotheses before.store before.heap)
    (executed : step tables mode before .convSave = some after) :
    StackSound signature definitions theorems context hypotheses after.store after.stack ∧
      HeapSound signature definitions theorems context hypotheses after.store after.heap := by
  simp only [step] at executed
  split at executed
  · rename_i left right rest shape
    have same := Option.some.inj executed
    subst after
    have shaped := shape ▸ sound
    cases shaped with
    | conv converted tail => exact ⟨tail, heap.append_certified converted⟩
  · simp at executed

theorem step_save_preserves_evidence (tables : Tables) (mode : Mode)
    (before after : Formats.MMB.State)
    (sound : StackSound signature definitions theorems context hypotheses before.store before.stack)
    (heap : HeapSound signature definitions theorems context hypotheses before.store before.heap)
    (executed : step tables mode before .save = some after) :
    StackSound signature definitions theorems context hypotheses after.store after.stack ∧
      HeapSound signature definitions theorems context hypotheses after.store after.heap := by
  cases shape : before.stack with
  | nil => simp [step, shape] at executed
  | cons element rest =>
      cases element <;> simp only [step, shape] at executed
      case goal => cases executed
      all_goals
        have same := Option.some.inj executed
        subst after
        have shaped := shape ▸ sound
        exact ⟨shaped, heap.append_certified (shaped.completed_head (by intros; simp))⟩

theorem step_ref_preserves_evidence (tables : Tables) (mode : Mode)
    (before after : Formats.MMB.State) (index : Nat)
    (sound : StackSound signature definitions theorems context hypotheses before.store before.stack)
    (heap : HeapSound signature definitions theorems context hypotheses before.store before.heap)
    (executed : step tables mode before (.ref index) = some after) :
    StackSound signature definitions theorems context hypotheses after.store after.stack ∧
      HeapSound signature definitions theorems context hypotheses after.store after.heap := by
  cases found : before.heap[index]? with
  | none => simp [step, found] at executed
  | some element =>
      have certified := heap.lookup found
      cases element with
      | goal left right => exact False.elim certified
      | expr position =>
          have same : before.push (.expr position) = after := by simpa [step, found] using executed
          subst after
          exact ⟨.expr certified sound, heap⟩
      | proof position =>
          have same : before.push (.proof position) = after := by simpa [step, found] using executed
          subst after
          exact ⟨.proof certified sound, heap⟩
      | conv left right =>
          simp only [step, found] at executed
          split at executed
          · rename_i left' right' rest shape
            split at executed
            · rename_i endpoints
              obtain ⟨rfl, rfl⟩ := endpoints
              have same := Option.some.inj executed
              subst after
              have shaped := shape ▸ sound
              cases shaped with
              | goal _ _ resume => exact ⟨resume certified, heap⟩
            · simp at executed
          · simp at executed

theorem step_cong_preserves_stack (tables : Tables) (mode : Mode)
    (before after : Formats.MMB.State)
    (typed : TypedStore signature context before.store)
    (sound : StackSound signature definitions theorems context hypotheses before.store before.stack)
    (executed : step tables mode before .cong = some after) :
    StackSound signature definitions theorems context hypotheses after.store after.stack := by
  simp only [step] at executed
  split at executed
  · rename_i left right rest shape
    cases leftRead : before.store[left]? with
    | none => simp [leftRead] at executed
    | some leftAlloc =>
        cases rightRead : before.store[right]? with
        | none => simp [leftRead, rightRead] at executed
        | some rightAlloc =>
            rcases leftAlloc with ⟨leftNode, leftType⟩
            rcases rightAlloc with ⟨rightNode, rightType⟩
            simp only [leftRead, rightRead] at executed
            cases leftNode with
            | var index => simp at executed
            | app term leftArgs =>
                cases rightNode with
                | var index => simp at executed
                | app term' rightArgs =>
                    change (if term = term' then some { before with stack :=
                      ((leftArgs.zip rightArgs).map (fun (left, right) => Elem.goal left right) ++ rest) }
                      else none) = some after at executed
                    split at executed
                    · rename_i sameTerm
                      subst term'
                      have same := Option.some.inj executed
                      subst after
                      obtain ⟨leftExpressions, declaration, leftArguments, leftDecoded,
                        declared, leftFits, _⟩ := TypedStore.application signature context before.store
                          typed left term leftArgs leftType leftRead
                      obtain ⟨rightExpressions, rightDeclaration, rightArguments, rightDecoded,
                        rightDeclared, rightFits, _⟩ := TypedStore.application signature context before.store
                          typed right term rightArgs rightType rightRead
                      have sameDeclaration : rightDeclaration = declaration :=
                        Option.some.inj (rightDeclared.symm.trans declared)
                      subst rightDeclaration
                      have shaped := shape ▸ sound
                      cases shaped with
                      | goal _ _ resume =>
                          exact StackSound.argument_goals signature definitions theorems context hypotheses
                            before.store leftArgs rightArgs leftExpressions rightExpressions
                            declaration.arguments rest
                            (decoded_arguments _ _ _ leftArguments) (decoded_arguments _ _ _ rightArguments)
                            leftFits rightFits (fun conversions => resume
                              ⟨_, _, declaration.resultSort, leftDecoded, rightDecoded,
                                .congruence declared conversions⟩)
                    · simp at executed
  · simp at executed

end ConversionCommands

namespace Controls

private def sortsAndDeclarations : Tables := ⟨[], [], []⟩
private def terms : TermSignature := fun _ => none
private def definitions : Definition.Signature := fun _ => none
private def theorems : TheoremSignature := fun _ => none
private def context : Context := [.bound 0]
private def hypotheses : List Preterm := [.var 0]
private def store : List Alloc := [⟨.var 0, ⟨0, true, {0}⟩⟩]
private def initial : Formats.MMB.State := ⟨store, [], [.expr 0, .proof 0], [0], 1, 1⟩

private theorem typed : TypedPointer terms context store 0 :=
  ⟨.var 0, 0, by rw [Soundness.decode]; rfl, Preterm.HasType.var (binder := .bound 0) rfl⟩

private theorem proved : ProvenPointer terms definitions theorems context hypotheses store 0 :=
  ⟨.var 0, 0, by rw [Soundness.decode]; rfl, Preterm.HasType.var (binder := .bound 0) rfl,
    .hypothesis (by simp [hypotheses])⟩

private theorem initialHeap : HeapSound terms definitions theorems context hypotheses initial.store initial.heap := by
  intro element member
  simp [initial] at member
  rcases member with rfl | rfl
  · exact typed
  · exact proved

/-- The actual command trace saves a conversion only after reflexivity has
discharged its goal, then saves the completed proof. Its final derivation is
obtained through the ordered invariant. -/
theorem conversion_save_control :
    ∃ final, run sortsAndDeclarations .assertion initial
      [.ref 0, .ref 1, .conv, .convCut, .refl, .convSave, .save] = some final ∧
      HeapSound terms definitions theorems context hypotheses final.store final.heap ∧
      ∃ expression, Soundness.decode final.store 0 = some expression ∧
        Derives terms definitions theorems context hypotheses expression := by
  let first : Formats.MMB.State := initial.push (.expr 0)
  let second : Formats.MMB.State := first.push (.proof 0)
  let third : Formats.MMB.State := { second with stack := [.goal 0 0, .proof 0] }
  let fourth : Formats.MMB.State := { third with stack := [.goal 0 0, .conv 0 0, .proof 0] }
  let fifth : Formats.MMB.State := { fourth with stack := [.conv 0 0, .proof 0] }
  let sixth : Formats.MMB.State := { fifth with stack := [.proof 0], heap := fifth.heap ++ [.conv 0 0] }
  let final : Formats.MMB.State := { sixth with heap := sixth.heap ++ [.proof 0] }
  have one := step_ref_preserves_evidence sortsAndDeclarations .assertion initial first 0
    (signature := terms) (definitions := definitions) (theorems := theorems)
    (context := context) (hypotheses := hypotheses) .empty initialHeap rfl
  have two := step_ref_preserves_evidence sortsAndDeclarations .assertion first second 1 one.1 one.2 rfl
  have three := step_conv_preserves_stack sortsAndDeclarations .assertion second third two.1 rfl
  have four := step_convCut_preserves_stack sortsAndDeclarations .assertion third fourth three rfl
  have five := step_refl_preserves_stack sortsAndDeclarations .assertion fourth fifth four rfl
  have six := step_convSave_preserves_evidence sortsAndDeclarations .assertion fifth sixth five two.2 rfl
  have seven := step_save_preserves_evidence sortsAndDeclarations .assertion sixth final six.1 six.2 rfl
  exact ⟨final, rfl, seven.2, seven.1.final_proof⟩

theorem pending_conversion_save_refused (tables : Tables) (mode : Mode)
    (state : Formats.MMB.State) (left right : Nat) (rest : List Elem)
    (shape : state.stack = .goal left right :: rest) : step tables mode state .save = none := by
  simp [step, shape]

/-- Equal decoded expressions at different pointers are convertible in the
kernel, while the machine's `Refl` requires pointer identity. -/
theorem copied_pointer_reflexivity_refused :
    ConvertedPointers terms definitions context (store ++ store) 0 1 ∧
      step sortsAndDeclarations .assertion
        ⟨store ++ store, [.goal 0 1], [], [], 1, 1⟩ .refl = none := by
  exact ⟨⟨.var 0, .var 0, 0, by rw [Soundness.decode]; rfl, by rw [Soundness.decode]; rfl,
    .refl (Preterm.HasType.var (binder := .bound 0) rfl)⟩, rfl⟩

theorem wrong_saved_conversion_refused :
    step sortsAndDeclarations .assertion
      ⟨store ++ store, [.goal 0 0], [.conv 0 1], [], 1, 1⟩ (.ref 0) = none := rfl

end Controls

end Mettapedia.Languages.MM0.MeTTa.MMBMachineSoundness
