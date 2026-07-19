import Mettapedia.Languages.OpenTheory.Syntax

/-!
# OpenTheory type and term substitution

This file models the substitution semantics of OpenTheory revision
`f555adbf6f3ca52ef6a9c5ca35d0316e53a289c1`, following
`src/TypeSubst.sml`, `src/TermSubst.sml`, and `src/Var.sml`.

Type and term maps use the source convention that the last occurrence of a
key wins, after which exact identities are removed.  Type substitution is
simultaneous: a mapped type variable is replaced by the stored type without
recursively substituting that replacement.  For free term variables the type
substitution is applied before the term-map lookup, and a stored replacement
is inserted unchanged.

The executable term operation works on alpha-canonical de Bruijn syntax.
Bound indices are therefore outside the term-map domain and capture avoidance
is structural rather than dependent on a fresh-name convention.  A later
module will connect this operation to an independent named substitution
relation.
-/

namespace Mettapedia.Languages.OpenTheory

/-! ## Checked source terms -/

/-- A source term retained together with its successful source type check. -/
structure CheckedSourceTerm where
  source : SourceTerm
  ty : Ty
  checked : source.inferType = some ty

namespace CheckedSourceTerm

/-- The alpha-canonical image of a checked source term. -/
def canonical (term : CheckedSourceTerm) : CanonicalTerm :=
  ⟨term.source.toDB [], term.ty, by
    simpa using (DBTerm.inferType_toDB [] term.source).trans term.checked⟩

/-- A checked variable term. -/
def ofVariable (sourceVar : SourceVar) : CheckedSourceTerm :=
  ⟨.var sourceVar.name sourceVar.ty, sourceVar.ty, by simp⟩

end CheckedSourceTerm

/-! ## Type-substitution maps and normalization -/

/--
A type-substitution table.  `ofList` is the source-facing normalizing
constructor: later entries replace earlier entries and exact identities are
removed.  Its entries are stored newest first.  Direct structure construction
remains inspectable, so the semantic operations below also specify behavior
for arbitrary entry lists.
-/
structure TypeSubst where
  entries : List (Name × Ty)
deriving Repr

namespace TypeSubst

def empty : TypeSubst := ⟨[]⟩

/-- Remove every stored occurrence of a key. -/
def eraseKey (name : Name) (entries : List (Name × Ty)) : List (Name × Ty) :=
  entries.filter fun entry => decide (entry.1 ≠ name)

/-- Insert one maplet, removing an exact identity maplet. -/
def insert (substitution : TypeSubst) (name : Name) (ty : Ty) : TypeSubst :=
  let remaining := eraseKey name substitution.entries
  if Ty.same ty (.var name) then ⟨remaining⟩ else ⟨(name, ty) :: remaining⟩

/-- Decode a source list.  Fold-left insertion makes the final duplicate win. -/
def ofList (entries : List (Name × Ty)) : TypeSubst :=
  entries.foldl (fun substitution entry => substitution.insert entry.1 entry.2) empty

/-- Lookup in the normalized, newest-first representation. -/
def lookup (substitution : TypeSubst) (name : Name) : Option Ty :=
  List.lookup name substitution.entries

/-- Simultaneously substitute type variables in a type. -/
def apply (substitution : TypeSubst) : Ty → Ty
  | .var name => (substitution.lookup name).getD (.var name)
  | .op operator arguments => .op operator (arguments.map substitution.apply)
termination_by ty => sizeOf ty

/-- Apply only the type component of a typed variable. -/
def applyVar (substitution : TypeSubst) (sourceVar : SourceVar) : SourceVar :=
  ⟨sourceVar.name, substitution.apply sourceVar.ty⟩

/--
Compose in the pinned source direction: `first.compose second` applies
`first` and then `second`.
-/
def compose (first second : TypeSubst) : TypeSubst :=
  first.entries.reverse.foldl
    (fun result entry => result.insert entry.1 (second.apply entry.2)) second

@[simp] theorem lookup_empty (name : Name) : empty.lookup name = none := by
  rfl

@[simp] theorem apply_empty (ty : Ty) : empty.apply ty = ty := by
  fun_induction TypeSubst.apply with
  | case1 => rfl
  | case2 operator arguments ih =>
      exact congrArg (Ty.op operator)
        ((List.map_congr_left ih).trans (List.map_id arguments))

@[simp] theorem apply_var (substitution : TypeSubst) (name : Name) :
    substitution.apply (.var name) =
      (substitution.lookup name).getD (.var name) := by
  simp [apply]

@[simp] theorem apply_op
    (substitution : TypeSubst) (operator : TypeOp) (arguments : List Ty) :
    substitution.apply (.op operator arguments) =
      .op operator (arguments.map substitution.apply) := by
  simp [apply]

/-- Type substitution preserves the distinguished function-space head. -/
@[simp] theorem apply_function (substitution : TypeSubst) (domain codomain : Ty) :
    substitution.apply (.function domain codomain) =
      .function (substitution.apply domain) (substitution.apply codomain) := by
  simp [Ty.function]

/-- A recognized function type remains recognizable after substitution. -/
theorem destFunction?_apply
    (substitution : TypeSubst) {ty domain codomain : Ty}
    (h : ty.destFunction? = some (domain, codomain)) :
    (substitution.apply ty).destFunction? =
      some (substitution.apply domain, substitution.apply codomain) := by
  cases ty with
  | var name => simp [Ty.destFunction?] at h
  | op operator arguments =>
      cases arguments with
      | nil => simp [Ty.destFunction?] at h
      | cons first rest =>
          cases rest with
          | nil => simp [Ty.destFunction?] at h
          | cons second rest =>
              cases rest with
              | nil =>
                  simp only [Ty.destFunction?] at h
                  split at h
                  · rename_i operatorIsFunction
                    simp only [Option.some.injEq, Prod.mk.injEq] at h
                    obtain ⟨rfl, rfl⟩ := h
                    simp [Ty.destFunction?, operatorIsFunction]
                  · contradiction
              | cons third tail => simp [Ty.destFunction?] at h

/-- The operator, including its provenance, is opaque to type substitution. -/
theorem apply_op_preserves_operator
    (substitution : TypeSubst) (operator : TypeOp) (arguments : List Ty) :
    substitution.apply (.op operator arguments) =
      .op operator (arguments.map substitution.apply) := by
  exact apply_op substitution operator arguments

/-!
`TypeSubst.entries` is intentionally inspectable, so the lemmas below cover
even directly constructed lists with duplicate keys.  In particular,
composition traverses the first map from oldest to newest: its first lookup
entry is processed last and therefore remains authoritative.
-/

private theorem lookup_eraseKey_ne_raw
    {name other : Name} (different : other ≠ name)
    (entries : List (Name × Ty)) :
    List.lookup other
        (entries.filter fun entry => decide (entry.1 ≠ name)) =
      List.lookup other entries := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      rw [List.filter_cons]
      by_cases retained : entry.1 ≠ name
      · simp only [decide_eq_true retained, if_true]
        rw [List.lookup_cons, List.lookup_cons]
        split
        · rfl
        · exact ih
      · have keyEquality : entry.1 = name := not_ne_iff.mp retained
        simp only [decide_eq_false_iff_not.mpr retained]
        rw [List.lookup_cons]
        have missed : (other == entry.1) = false := by
          simp [keyEquality, different]
        rw [missed]
        exact ih

@[simp] theorem lookup_eraseKey_same
    (substitution : TypeSubst) (name : Name) :
    List.lookup name (eraseKey name substitution.entries) = none := by
  simp [eraseKey, ne_comm]

theorem lookup_eraseKey_ne
    (substitution : TypeSubst) {name other : Name}
    (different : other ≠ name) :
    List.lookup other (eraseKey name substitution.entries) =
      substitution.lookup other := by
  exact lookup_eraseKey_ne_raw different substitution.entries

/-- Insertion gives the inserted key exactly the supplied action on types. -/
@[simp] theorem apply_insert_same
    (substitution : TypeSubst) (name : Name) (ty : Ty) :
    (substitution.insert name ty).apply (.var name) = ty := by
  simp only [apply, insert]
  split
  · rename_i identity
    have typeEquality : ty = .var name :=
      (Ty.same_eq_true_iff _ _).mp identity
    subst ty
    simp [lookup]
  · simp [lookup]

/-- Insertion leaves every different variable action unchanged. -/
theorem apply_insert_ne
    (substitution : TypeSubst) {name other : Name} (ty : Ty)
    (different : other ≠ name) :
    (substitution.insert name ty).apply (.var other) =
      substitution.apply (.var other) := by
  simp only [apply, insert]
  split
  · change
      (List.lookup other (eraseKey name substitution.entries)).getD
          (.var other) = _
    rw [lookup_eraseKey_ne substitution different]
  · change
      (List.lookup other
          ((name, ty) :: eraseKey name substitution.entries)).getD
          (.var other) = _
    rw [List.lookup_cons]
    have missed : (other == name) = false := by simp [different]
    rw [missed, lookup_eraseKey_ne substitution different]

/-- Lookup records whether insertion normalized an exact identity away. -/
theorem lookup_insert_same
    (substitution : TypeSubst) (name : Name) (ty : Ty) :
    (substitution.insert name ty).lookup name =
      if Ty.same ty (.var name) then none else some ty := by
  simp only [insert]
  split
  · simp [lookup]
  · simp [lookup]

/-- Appending a source maplet performs one final insertion. -/
theorem ofList_append_singleton
    (entries : List (Name × Ty)) (name : Name) (ty : Ty) :
    ofList (entries ++ [(name, ty)]) = (ofList entries).insert name ty := by
  simp [ofList, List.foldl_append]

/--
The final occurrence of a key wins; when it is an exact identity, the key is
absent from the normalized map.
-/
theorem lookup_ofList_append_singleton
    (entries : List (Name × Ty)) (name : Name) (ty : Ty) :
    (ofList (entries ++ [(name, ty)])).lookup name =
      if Ty.same ty (.var name) then none else some ty := by
  rw [ofList_append_singleton, lookup_insert_same]

/-- Composition has the pinned source direction: first, then second. -/
theorem apply_compose_var
    (first second : TypeSubst) (name : Name) :
    (first.compose second).apply (.var name) =
      second.apply (first.apply (.var name)) := by
  rcases first with ⟨entries⟩
  induction entries with
  | nil => simp [compose, lookup]
  | cons entry rest ih =>
      have composeStep :
          (TypeSubst.mk (entry :: rest)).compose second =
            ((TypeSubst.mk rest).compose second).insert entry.1
              (second.apply entry.2) := by
        simp [compose, List.foldl_append]
      rw [composeStep]
      by_cases keyEquality : name = entry.1
      · subst name
        rw [apply_insert_same]
        simp only [apply, lookup]
        rw [List.lookup_cons]
        have hit : (entry.1 == entry.1) = true := by simp
        rw [hit]
        rfl
      · rw [apply_insert_ne _ _ keyEquality, ih]
        congr 1
        simp only [apply, lookup]
        rw [List.lookup_cons]
        have missed : (name == entry.1) = false := by simp [keyEquality]
        rw [missed]

/-- Extensional correctness of executable type-substitution composition. -/
theorem apply_compose (first second : TypeSubst) : ∀ ty : Ty,
    (first.compose second).apply ty = second.apply (first.apply ty)
  | .var name => apply_compose_var first second name
  | .op operator arguments => by
      simp only [apply]
      congr 1
      rw [List.map_map]
      exact List.map_congr_left
        (fun item _ => apply_compose first second item)
termination_by ty => sizeOf ty

end TypeSubst

/-! ## Term-substitution maps and normalization -/

/--
Combined type and term substitution.  The normalizing `ofList` constructor
stores term entries newest first.  Each value is independently checked, but
its type need not equal the key type; `TypeCorrect` states that additional
soundness condition explicitly.
-/
structure TermSubst where
  types : TypeSubst
  entries : List (SourceVar × CheckedSourceTerm)

namespace TermSubst

def empty : TermSubst := ⟨TypeSubst.empty, []⟩

/-- Exact typed-variable equality, used for map keys. -/
def keySame (left right : SourceVar) : Bool := sourceVarSame left right

/-- Remove every stored occurrence of a typed-variable key. -/
def eraseKey (sourceVar : SourceVar)
    (entries : List (SourceVar × CheckedSourceTerm)) :
    List (SourceVar × CheckedSourceTerm) :=
  entries.filter fun entry => !(keySame entry.1 sourceVar)

/-- Upstream normalization removes a replacement that is exactly its key. -/
def isIdentity (sourceVar : SourceVar) (replacement : CheckedSourceTerm) : Bool :=
  SourceTerm.same replacement.source (.var sourceVar.name sourceVar.ty)

/-- Insert a term maplet using last-wins and exact-identity normalization. -/
def insert (substitution : TermSubst) (sourceVar : SourceVar)
    (replacement : CheckedSourceTerm) : TermSubst :=
  let remaining := eraseKey sourceVar substitution.entries
  if isIdentity sourceVar replacement then
    ⟨substitution.types, remaining⟩
  else
    ⟨substitution.types, (sourceVar, replacement) :: remaining⟩

/-- Decode a source term-map list over an already decoded type substitution. -/
def ofList (types : TypeSubst)
    (entries : List (SourceVar × CheckedSourceTerm)) : TermSubst :=
  entries.foldl
    (fun substitution entry => substitution.insert entry.1 entry.2)
    ⟨types, []⟩

@[simp] theorem insert_types (substitution : TermSubst)
    (sourceVar : SourceVar) (replacement : CheckedSourceTerm) :
    (substitution.insert sourceVar replacement).types = substitution.types := by
  unfold insert
  split <;> rfl

private theorem foldl_insert_types
    (substitution : TermSubst)
    (entries : List (SourceVar × CheckedSourceTerm)) :
    (entries.foldl
      (fun result entry => result.insert entry.1 entry.2) substitution).types =
      substitution.types := by
  induction entries generalizing substitution with
  | nil => rfl
  | cons entry rest ih =>
      rw [List.foldl_cons, ih, insert_types]

@[simp] theorem ofList_types (types : TypeSubst)
    (entries : List (SourceVar × CheckedSourceTerm)) :
    (ofList types entries).types = types := by
  exact foldl_insert_types ⟨types, []⟩ entries

/-- Lookup a post-type-substitution variable in the term map. -/
def lookup (substitution : TermSubst) (sourceVar : SourceVar) :
    Option CheckedSourceTerm :=
  substitution.entries.find? (fun entry => keySame entry.1 sourceVar) |>.map Prod.snd

@[simp] theorem lookup_eraseKey_same
    (substitution : TermSubst) (sourceVar : SourceVar) :
    (TermSubst.mk substitution.types
      (eraseKey sourceVar substitution.entries)).lookup sourceVar = none := by
  simp [lookup, eraseKey, keySame]

/-- Lookup records whether insertion normalized an exact term identity away. -/
theorem lookup_insert_same
    (substitution : TermSubst) (sourceVar : SourceVar)
    (replacement : CheckedSourceTerm) :
    (substitution.insert sourceVar replacement).lookup sourceVar =
      if isIdentity sourceVar replacement then none else some replacement := by
  simp only [insert]
  split
  · simp [lookup, eraseKey, keySame]
  · simp [lookup, keySame]

/-- Appending a source term maplet performs one final insertion. -/
theorem ofList_append_singleton
    (types : TypeSubst)
    (entries : List (SourceVar × CheckedSourceTerm))
    (sourceVar : SourceVar) (replacement : CheckedSourceTerm) :
    ofList types (entries ++ [(sourceVar, replacement)]) =
      (ofList types entries).insert sourceVar replacement := by
  simp [ofList, List.foldl_append]

/--
The final occurrence of a typed-variable key wins; an exact identity removes
the key from the normalized term map.
-/
theorem lookup_ofList_append_singleton
    (types : TypeSubst)
    (entries : List (SourceVar × CheckedSourceTerm))
    (sourceVar : SourceVar) (replacement : CheckedSourceTerm) :
    (ofList types (entries ++ [(sourceVar, replacement)])).lookup sourceVar =
      if isIdentity sourceVar replacement then none else some replacement := by
  rw [ofList_append_singleton, lookup_insert_same]

/-- Every stored replacement has the exact type of its term-map key. -/
def TypeCorrect (substitution : TermSubst) : Prop :=
  ∀ entry ∈ substitution.entries, entry.2.ty = entry.1.ty

/-- Executable form of `TypeCorrect`. -/
def typeCorrectB (substitution : TermSubst) : Bool :=
  substitution.entries.all fun entry => Ty.same entry.2.ty entry.1.ty

theorem typeCorrectB_eq_true_iff (substitution : TermSubst) :
    substitution.typeCorrectB = true ↔ substitution.TypeCorrect := by
  simp only [typeCorrectB, List.all_eq_true, TypeCorrect]
  constructor
  · intro h entry membership
    exact (Ty.same_eq_true_iff _ _).mp (h entry membership)
  · intro h entry membership
    exact (Ty.same_eq_true_iff _ _).mpr (h entry membership)

/-- A successful term-map lookup came from a stored entry. -/
theorem lookup_mem
    {substitution : TermSubst} {sourceVar : SourceVar}
    {replacement : CheckedSourceTerm}
    (h : substitution.lookup sourceVar = some replacement) :
    ∃ stored ∈ substitution.entries,
      keySame stored.1 sourceVar = true ∧ stored.2 = replacement := by
  unfold lookup at h
  obtain ⟨stored, found, value⟩ := Option.map_eq_some_iff.mp h
  exact ⟨stored, List.mem_of_find?_eq_some found,
    List.find?_some (p := fun entry => keySame entry.1 sourceVar)
      (a := stored) found,
    value⟩

/-- Type correctness specializes to every successful lookup. -/
theorem typeCorrect_lookup
    {substitution : TermSubst} (correct : substitution.TypeCorrect)
    {sourceVar : SourceVar} {replacement : CheckedSourceTerm}
    (h : substitution.lookup sourceVar = some replacement) :
    replacement.ty = sourceVar.ty := by
  obtain ⟨stored, membership, keyEquality, rfl⟩ := lookup_mem h
  have storedType := correct stored membership
  have keysEqual : stored.1 = sourceVar := (sourceVarSame_eq_true_iff _ _).mp keyEquality
  simpa [keysEqual] using storedType

/--
Apply the combined substitution to canonical syntax.  Constants retain their
symbol provenance, bound indices are untouched, and stored replacements are
inserted without recursively applying either component of the substitution.
-/
def applyDB (substitution : TermSubst) : DBTerm → DBTerm
  | .const constant ty => .const constant (substitution.types.apply ty)
  | .free sourceVar =>
      let sourceVar' := substitution.types.applyVar sourceVar
      match substitution.lookup sourceVar' with
      | some replacement => replacement.canonical.term
      | none => .free sourceVar'
  | .bound index => .bound index
  | .app function argument =>
      .app (substitution.applyDB function) (substitution.applyDB argument)
  | .abs domain body =>
      .abs (substitution.types.apply domain) (substitution.applyDB body)
termination_by term => sizeOf term

@[simp] theorem applyDB_const
    (substitution : TermSubst) (constant : Const) (ty : Ty) :
    substitution.applyDB (.const constant ty) =
      .const constant (substitution.types.apply ty) := by
  simp [applyDB]

@[simp] theorem applyDB_bound (substitution : TermSubst) (index : Nat) :
    substitution.applyDB (.bound index) = .bound index := by
  simp [applyDB]

theorem applyDB_free_of_lookup_none
    (substitution : TermSubst) (sourceVar : SourceVar)
    (missing : substitution.lookup (substitution.types.applyVar sourceVar) = none) :
    substitution.applyDB (.free sourceVar) =
      .free (substitution.types.applyVar sourceVar) := by
  simp [applyDB, missing]

theorem applyDB_free_of_lookup_some
    (substitution : TermSubst) (sourceVar : SourceVar)
    (replacement : CheckedSourceTerm)
    (found : substitution.lookup (substitution.types.applyVar sourceVar) =
      some replacement) :
    substitution.applyDB (.free sourceVar) = replacement.canonical.term := by
  simp [applyDB, found]

@[simp] theorem applyDB_app
    (substitution : TermSubst) (function argument : DBTerm) :
    substitution.applyDB (.app function argument) =
      .app (substitution.applyDB function) (substitution.applyDB argument) := by
  simp [applyDB]

@[simp] theorem applyDB_abs
    (substitution : TermSubst) (domain : Ty) (body : DBTerm) :
    substitution.applyDB (.abs domain body) =
      .abs (substitution.types.apply domain) (substitution.applyDB body) := by
  simp [applyDB]

/-- Term substitution changes an occurrence type, never constant provenance. -/
theorem applyDB_const_preserves_const
    (substitution : TermSubst) (constant : Const) (ty : Ty) :
    substitution.applyDB (.const constant ty) =
      .const constant (substitution.types.apply ty) := by
  exact applyDB_const substitution constant ty

end TermSubst

/-! ## Type preservation on canonical syntax -/

namespace DBTerm

/--
A successfully checked term retains its type when binders are appended outside
its existing context.
-/
theorem inferType_append_context
    {term : DBTerm} {context : List Ty} {ty : Ty}
    (checked : term.inferType context = some ty) (suffix : List Ty) :
    term.inferType (context ++ suffix) = some ty := by
  induction term generalizing context ty with
  | const constant annotation =>
      simpa using checked
  | free sourceVar =>
      simpa using checked
  | bound index =>
      simp only [inferType] at checked ⊢
      obtain ⟨inRange, _⟩ := List.getElem?_eq_some_iff.mp checked
      rw [List.getElem?_append_left inRange]
      exact checked
  | app function argument functionIH argumentIH =>
      simp only [inferType] at checked ⊢
      cases functionTypeEq : function.inferType context with
      | none => simp [functionTypeEq] at checked
      | some functionType =>
          cases argumentTypeEq : argument.inferType context with
          | none => simp [functionTypeEq, argumentTypeEq] at checked
          | some argumentType =>
              cases functionShape : functionType.destFunction? with
              | none =>
                  simp [functionTypeEq, argumentTypeEq, functionShape] at checked
              | some pair =>
                  obtain ⟨domain, codomain⟩ := pair
                  have functionChecked := functionIH functionTypeEq
                  have argumentChecked := argumentIH argumentTypeEq
                  simpa [functionTypeEq, argumentTypeEq, functionShape,
                    functionChecked, argumentChecked] using checked
  | abs domain body bodyIH =>
      simp only [inferType] at checked ⊢
      cases bodyTypeEq : body.inferType (domain :: context) with
      | none => simp [bodyTypeEq] at checked
      | some codomain =>
          have bodyChecked := bodyIH bodyTypeEq
          rw [show domain :: (context ++ suffix) =
            (domain :: context) ++ suffix by rfl]
          rw [bodyChecked]
          simpa [bodyTypeEq] using checked

/--
A term checked without surrounding binders has the same type under any outer
context.  This is the weakening fact used when a canonical replacement is
inserted beneath an abstraction.
-/
theorem inferType_weaken_empty
    {term : DBTerm} {ty : Ty}
    (checked : term.inferType [] = some ty) (context : List Ty) :
    term.inferType context = some ty := by
  simpa using inferType_append_context checked context

end DBTerm

namespace TermSubst

/-- A type-correct substitution preserves successful DB type inference. -/
theorem inferType_applyDB
    {substitution : TermSubst} (correct : substitution.TypeCorrect)
    {term : DBTerm} {context : List Ty} {ty : Ty}
    (checked : term.inferType context = some ty) :
    (substitution.applyDB term).inferType
        (context.map substitution.types.apply) =
      some (substitution.types.apply ty) := by
  induction term generalizing context ty with
  | const constant annotation =>
      simp at checked
      subst ty
      simp
  | free sourceVar =>
      simp at checked
      subst ty
      simp only [applyDB]
      let sourceVar' := substitution.types.applyVar sourceVar
      cases lookupEq : substitution.lookup sourceVar' with
      | none =>
          simp [TypeSubst.applyVar]
      | some replacement =>
          have replacementType := typeCorrect_lookup correct lookupEq
          have replacementChecked :=
            DBTerm.inferType_weaken_empty replacement.canonical.checked
              (context.map substitution.types.apply)
          have resultType :
              replacement.canonical.ty = substitution.types.apply sourceVar.ty := by
            change replacement.ty = substitution.types.apply sourceVar.ty
            simpa [sourceVar', TypeSubst.applyVar] using replacementType
          exact replacementChecked.trans (congrArg some resultType)
  | bound index =>
      simp only [DBTerm.inferType.eq_3] at checked
      simp only [applyDB_bound, DBTerm.inferType.eq_3, List.getElem?_map]
      rw [checked]
      rfl
  | app function argument functionIH argumentIH =>
      simp only [DBTerm.inferType.eq_4] at checked ⊢
      cases functionTypeEq : function.inferType context with
      | none => simp [functionTypeEq] at checked
      | some functionType =>
          cases argumentTypeEq : argument.inferType context with
          | none => simp [functionTypeEq, argumentTypeEq] at checked
          | some argumentType =>
              cases functionShape : functionType.destFunction? with
              | none =>
                  simp [functionTypeEq, argumentTypeEq, functionShape] at checked
              | some pair =>
                  obtain ⟨domain, codomain⟩ := pair
                  have resultEqual : domain = argumentType ∧ codomain = ty := by
                    simpa [functionTypeEq, argumentTypeEq, functionShape] using checked
                  obtain ⟨rfl, rfl⟩ := resultEqual
                  have functionChecked := functionIH functionTypeEq
                  have argumentChecked := argumentIH argumentTypeEq
                  have substitutedShape :=
                    TypeSubst.destFunction?_apply substitution.types functionShape
                  simp [functionChecked, argumentChecked, substitutedShape]
  | abs domain body bodyIH =>
      simp only [DBTerm.inferType.eq_5] at checked ⊢
      cases bodyTypeEq : body.inferType (domain :: context) with
      | none => simp [bodyTypeEq] at checked
      | some codomain =>
          have resultType : Ty.function domain codomain = ty := by
            simpa [bodyTypeEq] using checked
          subst ty
          have bodyChecked := bodyIH bodyTypeEq
          have bodyChecked' :
              DBTerm.inferType
                  (substitution.types.apply domain ::
                    List.map substitution.types.apply context)
                  (substitution.applyDB body) =
                some (substitution.types.apply codomain) := by
            simpa using bodyChecked
          simp [bodyChecked']

/--
Validate the raw substitution result without assuming global type correctness.
This mirrors the term-level source behavior: a wrong-type unused entry is
harmless, while a used entry may either change the result type or make an
enclosing application ill typed.
-/
def applyChecked? (substitution : TermSubst)
    (term : CanonicalTerm) : Option CanonicalTerm :=
  let result := substitution.applyDB term.term
  match h : result.inferType [] with
  | some ty => some ⟨result, ty, h⟩
  | none => none

theorem applyChecked?_eq_none_iff
    (substitution : TermSubst) (term : CanonicalTerm) :
    substitution.applyChecked? term = none ↔
      (substitution.applyDB term.term).inferType [] = none := by
  simp only [applyChecked?]
  split <;> simp_all

theorem applyChecked?_isSome_iff
    (substitution : TermSubst) (term : CanonicalTerm) :
    (substitution.applyChecked? term).isSome = true ↔
      ((substitution.applyDB term.term).inferType []).isSome = true := by
  simp only [applyChecked?]
  split <;> simp_all

/-- The total, type-preserving application path for the strict profile. -/
def applyChecked (substitution : TermSubst)
    (correct : substitution.TypeCorrect) (term : CanonicalTerm) : CanonicalTerm :=
  ⟨substitution.applyDB term.term, substitution.types.apply term.ty,
    inferType_applyDB correct term.checked⟩

theorem applyChecked?_isSome_of_typeCorrect
    (substitution : TermSubst) (correct : substitution.TypeCorrect)
    (term : CanonicalTerm) :
    (substitution.applyChecked? term).isSome = true := by
  rw [applyChecked?_isSome_iff]
  have checkedResult := inferType_applyDB correct term.checked
  simpa using congrArg Option.isSome checkedResult

/-- Under the verified admission condition, raw source-compatible rechecking
and strict type-preserving application return exactly the same checked term. -/
theorem rawApplication_eq_some_strictApplication
    (substitution : TermSubst) (correct : substitution.TypeCorrect)
    (term : CanonicalTerm) :
    substitution.applyChecked? term =
      some (substitution.applyChecked correct term) := by
  have hchecked :
      (substitution.applyDB term.term).inferType [] =
        some (substitution.types.apply term.ty) := by
    simpa using inferType_applyDB correct term.checked
  simp only [applyChecked?]
  split
  · rename_i resultType hresult
    have htype : resultType = substitution.types.apply term.ty :=
      Option.some.inj (hresult.symm.trans hchecked)
    subst resultType
    rfl
  · rename_i hresult
    rw [hresult] at hchecked
    contradiction

end TermSubst

/-! ## Executable source-fidelity examples -/

namespace SubstitutionExamples

def alphaName : Name := Name.global "A"
def betaName : Name := Name.global "B"
def alpha : Ty := .var alphaName
def beta : Ty := .var betaName

def individual : Ty := Examples.individual
def bool : Ty := Examples.bool

def xVar (ty : Ty) : SourceVar := ⟨Name.global "x", ty⟩
def yVar (ty : Ty) : SourceVar := ⟨Name.global "y", ty⟩
def zVar (ty : Ty) : SourceVar := ⟨Name.global "z", ty⟩

def simultaneousTypes : TypeSubst :=
  TypeSubst.ofList [(alphaName, beta), (betaName, bool)]

private theorem alphaName_ne_betaName : alphaName ≠ betaName := by
  simp [alphaName, betaName, Name.global]

/-- Stored type replacements are not recursively substituted. -/
example : simultaneousTypes.apply alpha = beta := by
  change
    (TypeSubst.ofList
      ([(alphaName, beta)] ++ [(betaName, bool)])).apply
        (.var alphaName) = beta
  rw [TypeSubst.ofList_append_singleton,
    TypeSubst.apply_insert_ne _ _ alphaName_ne_betaName]
  change
    ((TypeSubst.empty.insert alphaName beta).apply (.var alphaName)) = beta
  rw [TypeSubst.apply_insert_same]

example : simultaneousTypes.apply alpha ≠ bool := by
  rw [show simultaneousTypes.apply alpha = beta by
    change
      (TypeSubst.ofList
        ([(alphaName, beta)] ++ [(betaName, bool)])).apply
          (.var alphaName) = beta
    rw [TypeSubst.ofList_append_singleton,
      TypeSubst.apply_insert_ne _ _ alphaName_ne_betaName]
    change
      ((TypeSubst.empty.insert alphaName beta).apply (.var alphaName)) = beta
    rw [TypeSubst.apply_insert_same]]
  simp [beta, betaName, bool, Examples.bool, Name.global]

example : simultaneousTypes.apply beta = bool := by
  change
    (TypeSubst.ofList
      ([(alphaName, beta)] ++ [(betaName, bool)])).apply
        (.var betaName) = bool
  rw [TypeSubst.ofList_append_singleton, TypeSubst.apply_insert_same]

/-- The final duplicate wins. -/
def duplicateTypes : TypeSubst :=
  TypeSubst.ofList [(alphaName, individual), (alphaName, bool)]

example : duplicateTypes.apply alpha = bool := by
  change
    (TypeSubst.ofList
      ([(alphaName, individual)] ++ [(alphaName, bool)])).apply
        (.var alphaName) = bool
  rw [TypeSubst.ofList_append_singleton, TypeSubst.apply_insert_same]

/-- A final exact identity removes the key rather than reviving an older maplet. -/
def finalIdentityTypes : TypeSubst :=
  TypeSubst.ofList [(alphaName, bool), (alphaName, alpha)]

example : finalIdentityTypes.lookup alphaName = none := by
  change
    (TypeSubst.ofList
      ([(alphaName, bool)] ++ [(alphaName, alpha)])).lookup alphaName = none
  rw [TypeSubst.lookup_ofList_append_singleton]
  simp [alpha]

example : finalIdentityTypes.apply alpha = alpha := by
  change
    (TypeSubst.ofList
      ([(alphaName, bool)] ++ [(alphaName, alpha)])).apply alpha = alpha
  rw [TypeSubst.ofList_append_singleton]
  exact TypeSubst.apply_insert_same _ _ _

/-- Composition applies its left argument first and its right argument second. -/
def firstTypes : TypeSubst := TypeSubst.ofList [(alphaName, beta)]
def secondTypes : TypeSubst := TypeSubst.ofList [(betaName, bool)]

example : (firstTypes.compose secondTypes).apply alpha = bool := by
  rw [TypeSubst.apply_compose]
  have firstResult : firstTypes.apply alpha = beta := by
    change
      ((TypeSubst.empty.insert alphaName beta).apply (.var alphaName)) = beta
    rw [TypeSubst.apply_insert_same]
  rw [firstResult]
  change
    ((TypeSubst.empty.insert betaName bool).apply (.var betaName)) = bool
  rw [TypeSubst.apply_insert_same]

/-- Even a directly constructed duplicate list obeys first-lookup semantics. -/
def directDuplicateTypes : TypeSubst :=
  ⟨[(alphaName, beta), (alphaName, individual)]⟩

example : (directDuplicateTypes.compose secondTypes).apply alpha = bool := by
  rw [TypeSubst.apply_compose]
  have firstResult : directDuplicateTypes.apply alpha = beta := by
    change
      (TypeSubst.mk [(alphaName, beta), (alphaName, individual)]).apply
        (.var alphaName) = beta
    simp only [TypeSubst.apply, TypeSubst.lookup]
    rw [List.lookup_cons]
    have hit : (alphaName == alphaName) = true := by simp
    rw [hit]
    rfl
  rw [firstResult]
  change
    ((TypeSubst.empty.insert betaName bool).apply (.var betaName)) = bool
  rw [TypeSubst.apply_insert_same]

def checkedY (ty : Ty) : CheckedSourceTerm := CheckedSourceTerm.ofVariable (yVar ty)
def checkedZ (ty : Ty) : CheckedSourceTerm := CheckedSourceTerm.ofVariable (zVar ty)

/-- Term lookup happens after applying the type substitution to the variable. -/
def postTypeLookup : TermSubst :=
  TermSubst.ofList (TypeSubst.ofList [(alphaName, bool)])
    [(xVar bool, checkedY bool)]

example : postTypeLookup.applyDB (.free (xVar alpha)) = .free (yVar bool) := by
  simp [postTypeLookup, TermSubst.ofList, TermSubst.insert,
    TermSubst.eraseKey, TermSubst.isIdentity, TermSubst.keySame,
    TermSubst.applyDB, TermSubst.lookup, TypeSubst.ofList, TypeSubst.insert,
    TypeSubst.eraseKey, TypeSubst.applyVar,
    TypeSubst.lookup, TypeSubst.empty, CheckedSourceTerm.ofVariable,
    CheckedSourceTerm.canonical, SourceTerm.toDB, boundIndex, sourceVarSame,
    SourceTerm.same, Ty.same, TypeOp.same, checkedY, xVar, yVar, alpha,
    alphaName, bool, Name.global, Examples.bool, List.lookup]

private theorem postTypeLookup_correct : postTypeLookup.TypeCorrect := by
  rw [← TermSubst.typeCorrectB_eq_true_iff]
  simp [postTypeLookup, TermSubst.typeCorrectB, TermSubst.ofList,
    TermSubst.insert, TermSubst.eraseKey, TermSubst.isIdentity,
    CheckedSourceTerm.ofVariable, checkedY, xVar, yVar, bool,
    SourceTerm.same, TypeSubst.ofList, TypeSubst.insert,
    TypeSubst.eraseKey, TypeSubst.empty, Name.global]

def checkedXAlpha : CanonicalTerm :=
  (CheckedSourceTerm.ofVariable (xVar alpha)).canonical

/-- The strict path preserves the type after applying the type component. -/
example : (postTypeLookup.applyChecked postTypeLookup_correct checkedXAlpha).ty =
    bool := by
  change postTypeLookup.types.apply alpha = bool
  simp only [postTypeLookup, TermSubst.ofList_types]
  change
    ((TypeSubst.empty.insert alphaName bool).apply (.var alphaName)) = bool
  rw [TypeSubst.apply_insert_same]

/-- A key at the pre-substitution type does not fire after type substitution. -/
def preTypeKey : TermSubst :=
  TermSubst.ofList (TypeSubst.ofList [(alphaName, bool)])
    [(xVar alpha, checkedY alpha)]

example : preTypeKey.applyDB (.free (xVar alpha)) = .free (xVar bool) := by
  simp [preTypeKey, TermSubst.ofList, TermSubst.insert,
    TermSubst.eraseKey, TermSubst.isIdentity, TermSubst.keySame,
    TermSubst.applyDB, TermSubst.lookup, TypeSubst.ofList, TypeSubst.insert,
    TypeSubst.eraseKey, TypeSubst.applyVar,
    TypeSubst.lookup, TypeSubst.empty, CheckedSourceTerm.ofVariable,
    sourceVarSame, SourceTerm.same, Ty.same, checkedY, xVar, yVar, alpha,
    alphaName, bool, Name.global, Examples.bool, List.lookup]

/-- Stored term replacements are simultaneous and are not recursively rewritten. -/
def nonrecursiveTerms : TermSubst :=
  TermSubst.ofList TypeSubst.empty
    [(xVar individual, checkedY individual),
     (yVar individual, checkedZ individual)]

private theorem nonrecursiveTerms_x :
    nonrecursiveTerms.applyDB (.free (xVar individual)) = .free (yVar individual) := by
  simp [nonrecursiveTerms, TermSubst.ofList, TermSubst.insert,
    TermSubst.eraseKey, TermSubst.isIdentity, TermSubst.keySame,
    TermSubst.applyDB, TermSubst.lookup, TypeSubst.applyVar,
    CheckedSourceTerm.ofVariable, CheckedSourceTerm.canonical,
    SourceTerm.toDB, boundIndex, sourceVarSame, SourceTerm.same, Ty.same,
    TypeOp.same, checkedY, checkedZ, xVar, yVar, zVar, individual,
    TypeSubst.empty, Name.global,
    Examples.individual]

example :
    nonrecursiveTerms.applyDB (.free (xVar individual)) = .free (yVar individual) :=
  nonrecursiveTerms_x

example :
    nonrecursiveTerms.applyDB (.free (xVar individual)) ≠ .free (zVar individual) := by
  rw [nonrecursiveTerms_x]
  simp [yVar, zVar, Name.global]

/-- A bound occurrence is outside the free-variable term-map domain. -/
def shadowingSubst : TermSubst :=
  TermSubst.ofList TypeSubst.empty [(xVar individual, checkedY individual)]

example : shadowingSubst.applyDB (.abs individual (.bound 0)) =
    .abs individual (.bound 0) := by
  change
    (TermSubst.ofList TypeSubst.empty
      [(xVar individual, checkedY individual)]).applyDB
        (.abs individual (.bound 0)) = .abs individual (.bound 0)
  rw [TermSubst.applyDB_abs]
  simp only [TermSubst.ofList_types]
  rw [TypeSubst.apply_empty, TermSubst.applyDB_bound]

/-- DB substitution inserts a free replacement without capture. -/
private theorem shadowingSubst_free :
    shadowingSubst.applyDB (.abs individual (.free (xVar individual))) =
    .abs individual (.free (yVar individual)) := by
  simp [shadowingSubst, TermSubst.ofList, TermSubst.insert,
    TermSubst.eraseKey, TermSubst.isIdentity, TermSubst.keySame,
    TermSubst.applyDB, TermSubst.lookup, TypeSubst.applyVar,
    CheckedSourceTerm.ofVariable, CheckedSourceTerm.canonical,
    SourceTerm.toDB, boundIndex, sourceVarSame, SourceTerm.same, Ty.same,
    TypeOp.same, checkedY, xVar, yVar, individual, TypeSubst.empty,
    Name.global, Examples.individual]

example : shadowingSubst.applyDB (.abs individual (.free (xVar individual))) =
    .abs individual (.free (yVar individual)) := shadowingSubst_free

example : shadowingSubst.applyDB (.abs individual (.free (xVar individual))) ≠
    .abs individual (.bound 0) := by
  rw [shadowingSubst_free]
  simp

/-- Type instantiation cannot capture a formerly different typed variable. -/
def typeCaptureAvoidance : TermSubst :=
  TermSubst.ofList
    (TypeSubst.ofList [(alphaName, individual), (betaName, individual)]) []

private theorem typeCaptureTypes_alpha :
    typeCaptureAvoidance.types.apply alpha = individual := by
  simp only [typeCaptureAvoidance, TermSubst.ofList_types]
  change
    (TypeSubst.ofList
      ([(alphaName, individual)] ++ [(betaName, individual)])).apply
        (.var alphaName) = individual
  rw [TypeSubst.ofList_append_singleton,
    TypeSubst.apply_insert_ne _ _ alphaName_ne_betaName]
  change
    ((TypeSubst.empty.insert alphaName individual).apply (.var alphaName)) =
      individual
  rw [TypeSubst.apply_insert_same]

private theorem typeCaptureTypes_beta :
    typeCaptureAvoidance.types.apply beta = individual := by
  simp only [typeCaptureAvoidance, TermSubst.ofList_types]
  change
    (TypeSubst.ofList
      ([(alphaName, individual)] ++ [(betaName, individual)])).apply
        (.var betaName) = individual
  rw [TypeSubst.ofList_append_singleton, TypeSubst.apply_insert_same]

private theorem typeCaptureAvoidance_result :
    typeCaptureAvoidance.applyDB
        (.abs alpha (.free ⟨Name.global "x", beta⟩)) =
      .abs individual (.free ⟨Name.global "x", individual⟩) := by
  rw [TermSubst.applyDB_abs, typeCaptureTypes_alpha]
  have missing :
      typeCaptureAvoidance.lookup
          (typeCaptureAvoidance.types.applyVar
            (⟨Name.global "x", beta⟩ : SourceVar)) = none := by
    simp [typeCaptureAvoidance, TermSubst.lookup, TermSubst.ofList]
  rw [TermSubst.applyDB_free_of_lookup_none _ _ missing]
  simp only [TypeSubst.applyVar]
  rw [typeCaptureTypes_beta]

example :
    typeCaptureAvoidance.applyDB
        (.abs alpha (.free ⟨Name.global "x", beta⟩)) =
      .abs individual (.free ⟨Name.global "x", individual⟩) :=
  typeCaptureAvoidance_result

example :
    typeCaptureAvoidance.applyDB
        (.abs alpha (.free ⟨Name.global "x", beta⟩)) ≠
      .abs individual (.bound 0) := by
  rw [typeCaptureAvoidance_result]
  simp

/-- Type substitution changes an occurrence annotation, not symbol provenance. -/
def provenanceConstant : Const :=
  .mk (Name.global "c") (.defined (.var (Name.global "p") alpha))

def provenanceTypes : TermSubst :=
  TermSubst.ofList (TypeSubst.ofList [(alphaName, bool)]) []

example : provenanceTypes.applyDB (.const provenanceConstant alpha) =
    .const provenanceConstant bool := by
  rw [TermSubst.applyDB_const]
  simp only [provenanceTypes, TermSubst.ofList_types]
  change
    DBTerm.const provenanceConstant
        ((TypeSubst.empty.insert alphaName bool).apply (.var alphaName)) =
      DBTerm.const provenanceConstant bool
  rw [TypeSubst.apply_insert_same]

example : provenanceConstant =
    .mk (Name.global "c") (.defined (.var (Name.global "p") alpha)) := by
  rfl

/-- A raw wrong-type replacement is representable and may change a lone term's type. -/
def wrongTypeSubst : TermSubst :=
  TermSubst.ofList TypeSubst.empty [(xVar individual, checkedY bool)]

example : wrongTypeSubst.typeCorrectB = false := by
  simp [wrongTypeSubst, TermSubst.typeCorrectB, TermSubst.ofList,
    TermSubst.insert, TermSubst.eraseKey, TermSubst.isIdentity,
    CheckedSourceTerm.ofVariable, checkedY, xVar, yVar, individual, bool,
    SourceTerm.same, Ty.same, TypeOp.same, TypeSubst.empty, Name.global,
    Examples.individual, Examples.bool]

private theorem wrongTypeSubst_result :
    wrongTypeSubst.applyDB (.free (xVar individual)) = .free (yVar bool) := by
  simp [wrongTypeSubst, TermSubst.ofList, TermSubst.insert,
    TermSubst.eraseKey, TermSubst.isIdentity, TermSubst.keySame,
    TermSubst.applyDB, TermSubst.lookup, TypeSubst.applyVar,
    CheckedSourceTerm.ofVariable, CheckedSourceTerm.canonical,
    SourceTerm.toDB, boundIndex, sourceVarSame, SourceTerm.same, Ty.same,
    TypeOp.same, checkedY, xVar, yVar, individual, bool, TypeSubst.empty,
    Name.global, Examples.individual,
    Examples.bool]

example : wrongTypeSubst.applyDB (.free (xVar individual)) = .free (yVar bool) :=
  wrongTypeSubst_result

def checkedXIndividual : CanonicalTerm :=
  (CheckedSourceTerm.ofVariable (xVar individual)).canonical

example : (wrongTypeSubst.applyChecked? checkedXIndividual).isSome = true := by
  have termEquality : checkedXIndividual.term = .free (xVar individual) := by
    simp [checkedXIndividual, CheckedSourceTerm.canonical,
      CheckedSourceTerm.ofVariable, SourceTerm.toDB, boundIndex]
  rw [TermSubst.applyChecked?_isSome_iff, termEquality,
    wrongTypeSubst_result]
  simp

/-- The same wrong-type replacement invalidates an enclosing application. -/
def checkedApplicationSource : CheckedSourceTerm :=
  ⟨.app (.var (Name.global "f") (.function individual bool))
      (.var (Name.global "x") individual),
    bool, by
      simp [SourceTerm.inferType]⟩

def checkedApplication : CanonicalTerm :=
  checkedApplicationSource.canonical

private theorem checkedApplication_term :
    checkedApplication.term =
      .app (.free ⟨Name.global "f", .function individual bool⟩)
        (.free (xVar individual)) := by
  simp [checkedApplication, checkedApplicationSource,
    CheckedSourceTerm.canonical, SourceTerm.toDB, boundIndex,
    xVar]

private theorem wrongTypeFunction_unchanged :
    wrongTypeSubst.applyDB
        (.free ⟨Name.global "f", .function individual bool⟩) =
      .free ⟨Name.global "f", .function individual bool⟩ := by
  let functionVar : SourceVar :=
    ⟨Name.global "f", .function individual bool⟩
  have variableUnchanged :
      wrongTypeSubst.types.applyVar functionVar = functionVar := by
    simp [functionVar, wrongTypeSubst, TypeSubst.applyVar]
  have missing :
      wrongTypeSubst.lookup
          (wrongTypeSubst.types.applyVar functionVar) = none := by
    rw [variableUnchanged]
    simp [functionVar, wrongTypeSubst, TermSubst.lookup, TermSubst.ofList,
      TermSubst.insert, TermSubst.eraseKey, TermSubst.isIdentity,
      TermSubst.keySame, checkedY, CheckedSourceTerm.ofVariable,
      SourceTerm.same, sourceVarSame, Ty.same, TypeOp.same, xVar, yVar,
      individual, bool, Name.global, Examples.individual, Examples.bool]
  calc
    wrongTypeSubst.applyDB (.free functionVar) =
        .free (wrongTypeSubst.types.applyVar functionVar) :=
      TermSubst.applyDB_free_of_lookup_none _ _ missing
    _ = .free functionVar := congrArg DBTerm.free variableUnchanged

private theorem wrongTypeApplication_result :
    wrongTypeSubst.applyDB checkedApplication.term =
      .app (.free ⟨Name.global "f", .function individual bool⟩)
        (.free (yVar bool)) := by
  rw [checkedApplication_term, TermSubst.applyDB_app,
    wrongTypeFunction_unchanged, wrongTypeSubst_result]

example : wrongTypeSubst.applyChecked? checkedApplication = none := by
  rw [TermSubst.applyChecked?_eq_none_iff, wrongTypeApplication_result]
  simp [individual, bool, yVar,
    Examples.individual, Examples.bool, Ty.destFunction?, Ty.function,
    TypeOp.function, TypeOp.same, Name.global]

end SubstitutionExamples

end Mettapedia.Languages.OpenTheory
