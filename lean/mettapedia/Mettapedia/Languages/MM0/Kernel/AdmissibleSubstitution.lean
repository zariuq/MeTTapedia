import Mettapedia.Languages.MM0.Kernel.Typing
import Mathlib.Data.List.Forall2

/-!
# MM0 admissible theorem substitution

Formal dependencies and target occurrences live in different contexts. The
formal binders determine which pairs must be independent; target expressions
determine whether independence is preserved. Bound images must be distinct
where required, including occurrences under binding constructors.

The computation first validates exact arity and argument typing. Its pairwise
dependency check then uses complete target occurrence support. This is not
the weaker free-variable test used when admitting definition bodies.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Kernel

namespace Binder

def DependsOn (binder : Binder) (position index : Nat) : Prop :=
  match binder with
  | .bound _ => index = position
  | .regular _ dependencies => index ∈ dependencies

instance dependsOnDecidable (binder : Binder) (position index : Nat) :
    Decidable (DependsOn binder position index) := by
  cases binder <;> unfold DependsOn <;> infer_instance

theorem dependsOn_iff_hasVar {context : Context} {binder : Binder} {position index : Nat}
    (lookup : context[position]? = some binder) :
    DependsOn binder position index ↔ Preterm.HasVar context index (.var position) := by
  cases binder <;> simp [DependsOn, Preterm.hasVar_var_iff, lookup]

end Binder

namespace Substitution

def checkArguments (signature : TermSignature) (target : Context) :
    List Preterm → Context → Bool
  | [], [] => true
  | expression :: expressions, binder :: binders =>
      Preterm.checkBinder signature target expression binder &&
        checkArguments signature target expressions binders
  | _, _ => false

theorem checkArguments_iff (signature : TermSignature) (target : Context)
    (expressions : List Preterm) (formal : Context) :
    checkArguments signature target expressions formal = true ↔
      List.Forall₂ (Preterm.FitsBinder signature target) expressions formal := by
  induction expressions generalizing formal with
  | nil => cases formal <;> simp [checkArguments]
  | cons expression expressions ih =>
      cases formal with
      | nil => simp [checkArguments]
      | cons binder binders =>
          simp [checkArguments, Preterm.checkBinder_iff, ih]

abbrev Entry := (Binder × Preterm) × Nat

def entries (formal : Context) (expressions : List Preterm) : List Entry :=
  (formal.zip expressions).zipIdx

/-- Independence from one formal bound variable, evaluated in the target context. -/
def checkPair (target : Context) (formalBound targetBound : Nat) (other : Entry) : Bool :=
  if other.1.1.DependsOn other.2 formalBound then true
  else
    match Preterm.support? target other.1.2 with
    | none => false
    | some support => decide (targetBound ∉ support)

def PairIndependent (target : Context) (formalBound targetBound : Nat) (other : Entry) : Prop :=
  ¬ other.1.1.DependsOn other.2 formalBound →
    ¬ Preterm.HasVar target targetBound other.1.2

theorem checkPair_iff {target : Context} {formalBound targetBound : Nat} {other : Entry}
    {support : Finset Nat} (supported : Preterm.Supports target other.1.2 support) :
    checkPair target formalBound targetBound other = true ↔
      PairIndependent target formalBound targetBound other := by
  by_cases depends : other.1.1.DependsOn other.2 formalBound
  · simp [checkPair, PairIndependent, depends]
  · simp [checkPair, PairIndependent, depends, supported.eval, ← supported.mem_iff_hasVar]

def checkRow (target : Context) (allEntries : List Entry) (entry : Entry) : Bool :=
  match entry.1 with
  | (.bound _, .var image) => allEntries.all (checkPair target entry.2 image)
  | _ => true

def RowIndependent (target : Context) (allEntries : List Entry) (entry : Entry) : Prop :=
  ∀ sort image, entry.1 = (.bound sort, .var image) →
    ∀ other ∈ allEntries, PairIndependent target entry.2 image other

theorem checkRow_iff {target : Context} {allEntries : List Entry} (entry : Entry)
    (supported : ∀ other ∈ allEntries, ∃ support, Preterm.Supports target other.1.2 support) :
    checkRow target allEntries entry = true ↔ RowIndependent target allEntries entry := by
  rcases entry with ⟨⟨binder, expression⟩, position⟩
  cases binder with
  | regular sort dependencies => simp [checkRow, RowIndependent]
  | bound sort =>
      cases expression with
      | term symbol => simp [checkRow, RowIndependent]
      | app function argument => simp [checkRow, RowIndependent]
      | var image =>
          simp only [checkRow, List.all_eq_true]
          unfold RowIndependent
          constructor
          · intro checked otherSort otherImage equal other member
            have same := Prod.mk.inj equal
            cases same.1
            cases same.2
            obtain ⟨support, proof⟩ := supported other member
            exact (checkPair_iff proof).mp (checked other member)
          · intro independent other member
            obtain ⟨support, proof⟩ := supported other member
            exact (checkPair_iff proof).mpr (independent sort image rfl other member)

structure Admissible (signature : TermSignature) (formal target : Context)
    (expressions : List Preterm) : Prop where
  typed : List.Forall₂ (Preterm.FitsBinder signature target) expressions formal
  independent : ∀ entry ∈ entries formal expressions,
    RowIndependent target (entries formal expressions) entry

def checkAdmissible (signature : TermSignature) (formal target : Context)
    (expressions : List Preterm) : Bool :=
  checkArguments signature target expressions formal &&
    (entries formal expressions).all (checkRow target (entries formal expressions))

theorem typed_entry_support {signature : TermSignature} {formal target : Context}
    {expressions : List Preterm}
    (typed : List.Forall₂ (Preterm.FitsBinder signature target) expressions formal)
    (entry : Entry) (member : entry ∈ entries formal expressions) :
    ∃ support, Preterm.Supports target entry.1.2 support := by
  have pairMember : entry.1 ∈ formal.zip expressions := List.fst_mem_of_mem_zipIdx member
  have fits : Preterm.FitsBinder signature target entry.1.2 entry.1.1 :=
    List.forall₂_zip typed.flip pairMember
  exact fits.support_exists

theorem checkAdmissible_iff (signature : TermSignature) (formal target : Context)
    (expressions : List Preterm) :
    checkAdmissible signature formal target expressions = true ↔
      Admissible signature formal target expressions := by
  simp only [checkAdmissible, Bool.and_eq_true, checkArguments_iff, List.all_eq_true]
  constructor
  · rintro ⟨typed, checked⟩
    refine ⟨typed, ?_⟩
    intro entry member
    exact (checkRow_iff entry (typed_entry_support typed)).mp (checked entry member)
  · intro admitted
    refine ⟨admitted.typed, ?_⟩
    intro entry member
    exact (checkRow_iff entry (typed_entry_support admitted.typed)).mpr
      (admitted.independent entry member)

theorem Admissible.length_eq {signature : TermSignature} {formal target : Context}
    {expressions : List Preterm} (admitted : Admissible signature formal target expressions) :
    expressions.length = formal.length := admitted.typed.length_eq

/-- The formal context selects independence; the target context checks its preservation. -/
theorem Admissible.preserves_independence {signature : TermSignature} {formal target : Context}
    {expressions : List Preterm} (admitted : Admissible signature formal target expressions)
    {u v sort image : Nat} {binder : Binder} {expression : Preterm}
    (formalBound : formal[u]? = some (.bound sort))
    (formalOther : formal[v]? = some binder)
    (independent : ¬ Preterm.HasVar formal u (.var v))
    (boundImage : expressions[u]? = some (.var image))
    (otherImage : expressions[v]? = some expression) :
    ¬ Preterm.HasVar target image expression := by
  have sourceMember : ((.bound sort, .var image), u) ∈ entries formal expressions := by
    simp [entries, List.mem_zipIdx_iff_getElem?, List.getElem?_zip_eq_some, formalBound, boundImage]
  have otherMember : ((binder, expression), v) ∈ entries formal expressions := by
    simp [entries, List.mem_zipIdx_iff_getElem?, List.getElem?_zip_eq_some, formalOther, otherImage]
  exact admitted.independent _ sourceMember sort image rfl _ otherMember
    (fun depends => independent ((Binder.dependsOn_iff_hasVar formalOther).mp depends))

def instantiate (signature : TermSignature) (formal target : Context)
    (expressions : List Preterm) (body : Preterm) : Option Preterm :=
  if checkAdmissible signature formal target expressions then body.substitute (ofList expressions)
  else none

theorem instantiate_eq_some_iff (signature : TermSignature) (formal target : Context)
    (expressions : List Preterm) (body result : Preterm) :
    instantiate signature formal target expressions body = some result ↔
      Admissible signature formal target expressions ∧
        Preterm.Substitutes (ofList expressions) body result := by
  unfold instantiate
  cases checked : checkAdmissible signature formal target expressions with
  | false =>
      have refused : ¬ Admissible signature formal target expressions := by
        intro admitted
        have := (checkAdmissible_iff _ _ _ _).mpr admitted
        simp [checked] at this
      simp [refused]
  | true =>
      simp [Preterm.substitute_eq_some_iff, (checkAdmissible_iff _ _ _ _).mp checked]

/-- An admitted substitution is defined on every expression typed in its formal context. -/
theorem Admissible.instantiate_defined {signature : TermSignature} {formal target : Context}
    {expressions : List Preterm} (admitted : Admissible signature formal target expressions)
    {body : Preterm} {remaining : Context} {sort : Nat}
    (typing : Preterm.HasType signature formal body remaining sort) :
    ∃ result, instantiate signature formal target expressions body = some result := by
  obtain ⟨support, supported⟩ := typing.support_exists
  have defined : ∃ result, body.substitute (ofList expressions) = some result := by
    apply (Preterm.substitute_ofList_defined_iff _ _).mpr
    intro index occurs
    obtain ⟨binder, lookup⟩ := supported.lookup_exists index occurs
    rw [admitted.length_eq]
    exact (List.getElem?_eq_some_iff.mp lookup).1
  obtain ⟨result, substituted⟩ := defined
  exact ⟨result, (instantiate_eq_some_iff _ _ _ _ _ _).mpr
    ⟨admitted, Preterm.substitute_sound substituted⟩⟩

end Substitution

end Mettapedia.Languages.MM0.Kernel
