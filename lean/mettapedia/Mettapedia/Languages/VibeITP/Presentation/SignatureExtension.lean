import Mettapedia.Languages.VibeITP.Presentation.TermShape

/-!
# Extension of signatures on known terms

An extension preserves the complete immutable data of every previously
allocated symbol.  Newly allocated symbols may change operations on unknown
heads, so invariance is stated on the structural `TermShape` profile.  This
profile permits unrestricted natural arities, bound indices and byte lengths;
the kernel's arithmetic refusal guards remain separate.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation

open Mettapedia.Languages.VibeITP.Spec

def SigExt (source target : Sig) : Prop :=
  ∀ symbol info, source symbol = some info → target symbol = some info

def KnownSymbol (sig : Sig) (symbol : SymId) : Prop :=
  ∃ info, sig symbol = some info

def KnownParameters (sig : Sig) (parameters : List SymId) : Prop :=
  ∀ symbol ∈ parameters, KnownSymbol sig symbol

structure TheoryExt (source target : Theory) : Prop where
  sig : SigExt source.sig target.sig
  axioms : ∀ statement ∈ source.axioms, statement ∈ target.axioms
  definitions : ∀ definition ∈ source.definitions, definition ∈ target.definitions

theorem SigExt.refl (sig : Sig) : SigExt sig sig := fun _ _ h => h

theorem SigExt.trans {source middle target : Sig}
    (first : SigExt source middle) (second : SigExt middle target) : SigExt source target :=
  fun symbol info h => second symbol info (first symbol info h)

theorem TheoryExt.refl (theory : Theory) : TheoryExt theory theory :=
  ⟨SigExt.refl _, fun _ h => h, fun _ h => h⟩

theorem TheoryExt.trans {source middle target : Theory}
    (first : TheoryExt source middle) (second : TheoryExt middle target) :
    TheoryExt source target :=
  ⟨first.sig.trans second.sig, fun statement h => second.axioms statement (first.axioms statement h),
    fun definition h => second.definitions definition (first.definitions definition h)⟩

theorem SigExt.known {source target : Sig} (extension : SigExt source target)
    {symbol : SymId} (h : KnownSymbol source symbol) : KnownSymbol target symbol := by
  obtain ⟨info, hs⟩ := h
  exact ⟨info, extension symbol info hs⟩

theorem binderAt_sigExt {source target : Sig} (extension : SigExt source target)
    {symbol : SymId} (known : KnownSymbol source symbol) (index : Nat) :
    binderAt target symbol index = binderAt source symbol index := by
  obtain ⟨info, hs⟩ := known
  simp only [binderAt, hs, extension symbol info hs]

theorem bindersOf_sigExt {source target : Sig} (extension : SigExt source target)
    {symbol : SymId} (known : KnownSymbol source symbol) :
    bindersOf target symbol = bindersOf source symbol := by
  obtain ⟨info, hs⟩ := known
  simp only [bindersOf, hs, extension symbol info hs]

theorem kindOf_sigExt {source target : Sig} (extension : SigExt source target)
    {symbol : SymId} (known : KnownSymbol source symbol) :
    kindOf target symbol = kindOf source symbol := by
  obtain ⟨info, hs⟩ := known
  simp only [kindOf, hs, extension symbol info hs]

theorem isFvarSym_sigExt {source target : Sig} (extension : SigExt source target)
    {symbol : SymId} (known : KnownSymbol source symbol) :
    isFvarSym target symbol = isFvarSym source symbol := by
  obtain ⟨info, hs⟩ := known
  simp only [isFvarSym, hs, extension symbol info hs]

theorem symArity_sigExt {source target : Sig} (extension : SigExt source target)
    {symbol : SymId} (known : KnownSymbol source symbol) :
    symArity target symbol = symArity source symbol := by
  obtain ⟨info, hs⟩ := known
  simp only [symArity, hs, extension symbol info hs]

theorem knownSymbol_of_isFvarSym {sig : Sig} {symbol : SymId}
    (h : isFvarSym sig symbol = true) : KnownSymbol sig symbol := by
  cases hs : sig symbol with
  | none => simp [isFvarSym, hs] at h
  | some info => exact ⟨info, hs⟩

theorem Term.args_sizeOf_lt_app (symbol : SymId) (args : List Term) :
    sizeOf args < sizeOf (Term.app symbol args) := by
  rw [Term.app.sizeOf_spec]
  exact Nat.lt_add_of_pos_left (Nat.lt_add_right (sizeOf symbol) Nat.zero_lt_one)

theorem term_head_sizeOf_lt_cons (term : Term) (terms : List Term) :
    sizeOf term < sizeOf (term :: terms) := by
  change sizeOf term < 1 + sizeOf term + sizeOf terms
  exact Nat.lt_add_right (sizeOf terms) (Nat.lt_add_of_pos_left Nat.zero_lt_one)

theorem term_tail_sizeOf_lt_cons (term : Term) (terms : List Term) :
    sizeOf terms < sizeOf (term :: terms) := by
  change sizeOf terms < 1 + sizeOf term + sizeOf terms
  exact Nat.lt_add_of_pos_left (Nat.lt_add_right (sizeOf term) Nat.zero_lt_one)

mutual
theorem termShape_sigExt {source target : Sig} (extension : SigExt source target)
    (term : Term) (shape : TermShape source term) : TermShape target term := by
  cases shape with
  | bvar index => exact .bvar index
  | lit bytes => exact .lit bytes
  | app hs hlen hargs =>
      exact .app (extension _ _ hs) hlen (termShapeList_sigExt extension _ hargs)
termination_by sizeOf term
decreasing_by
  exact Term.args_sizeOf_lt_app _ _

theorem termShapeList_sigExt {source target : Sig} (extension : SigExt source target)
    (terms : List Term) (shape : TermShapeList source terms) : TermShapeList target terms := by
  cases shape with
  | nil => exact .nil
  | cons head tail =>
      exact .cons (termShape_sigExt extension _ head) (termShapeList_sigExt extension _ tail)
termination_by sizeOf terms
decreasing_by
  · exact term_head_sizeOf_lt_cons _ _
  · exact term_tail_sizeOf_lt_cons _ _
end

mutual
theorem depth_sigExt {source target : Sig} (extension : SigExt source target)
    (term : Term) (shape : TermShape source term) : depth target term = depth source term := by
  cases shape with
  | bvar index => rfl
  | lit bytes => rfl
  | @app symbol info args hs _ hargs =>
      exact depthArgs_sigExt extension ⟨info, hs⟩ 0 args hargs
termination_by sizeOf term
decreasing_by
  exact Term.args_sizeOf_lt_app _ _

theorem depthArgs_sigExt {source target : Sig} (extension : SigExt source target)
    {symbol : SymId} (known : KnownSymbol source symbol) (index : Nat)
    (terms : List Term) (shape : TermShapeList source terms) :
    depthArgs target symbol index terms = depthArgs source symbol index terms := by
  cases shape with
  | nil => rfl
  | cons head tail =>
      simp only [depthArgs, depth_sigExt extension _ head,
        binderAt_sigExt extension known index,
        depthArgs_sigExt extension known (index + 1) _ tail]
termination_by sizeOf terms
decreasing_by
  · exact term_head_sizeOf_lt_cons _ _
  · exact term_tail_sizeOf_lt_cons _ _
end

mutual
theorem hasFvar_sigExt {source target : Sig} (extension : SigExt source target)
    (term : Term) (shape : TermShape source term) : hasFvar target term = hasFvar source term := by
  cases shape with
  | bvar index => rfl
  | lit bytes => rfl
  | @app symbol info args hs _ hargs =>
      simp only [hasFvar, isFvarSym_sigExt extension ⟨info, hs⟩,
        hasFvarList_sigExt extension args hargs]
termination_by sizeOf term
decreasing_by
  exact Term.args_sizeOf_lt_app _ _

theorem hasFvarList_sigExt {source target : Sig} (extension : SigExt source target)
    (terms : List Term) (shape : TermShapeList source terms) :
    hasFvarList target terms = hasFvarList source terms := by
  cases shape with
  | nil => rfl
  | cons head tail =>
      simp only [hasFvarList, hasFvar_sigExt extension _ head,
        hasFvarList_sigExt extension _ tail]
termination_by sizeOf terms
decreasing_by
  · exact term_head_sizeOf_lt_cons _ _
  · exact term_tail_sizeOf_lt_cons _ _
end

mutual
theorem wellFormed_sigExt {source target : Sig} (extension : SigExt source target)
    (term : Term) (shape : TermShape source term) : WellFormed target term = WellFormed source term := by
  cases shape with
  | bvar index => rfl
  | lit bytes => rfl
  | @app symbol info args hs _ hargs =>
      simp only [WellFormed, hs, extension symbol info hs,
        wellFormedList_sigExt extension args hargs]
termination_by sizeOf term
decreasing_by
  exact Term.args_sizeOf_lt_app _ _

theorem wellFormedList_sigExt {source target : Sig} (extension : SigExt source target)
    (terms : List Term) (shape : TermShapeList source terms) :
    WellFormedList target terms = WellFormedList source terms := by
  cases shape with
  | nil => rfl
  | cons head tail =>
      simp only [WellFormedList, wellFormed_sigExt extension _ head,
        wellFormedList_sigExt extension _ tail]
termination_by sizeOf terms
decreasing_by
  · exact term_head_sizeOf_lt_cons _ _
  · exact term_tail_sizeOf_lt_cons _ _
end

theorem wellFormed_true_sigExt {source target : Sig} (extension : SigExt source target)
    {term : Term} (formed : WellFormed source term = true) : WellFormed target term = true := by
  rw [wellFormed_sigExt extension term (wellFormed_termShape source term formed)]
  exact formed

theorem closed_sigExt {source target : Sig} (extension : SigExt source target)
    (term : Term) (shape : TermShape source term) : Closed target term ↔ Closed source term := by
  unfold Closed
  rw [depth_sigExt extension term shape]

mutual
theorem fvarOccurrences_sigExt {source target : Sig} (extension : SigExt source target)
    (term : Term) (shape : TermShape source term) :
    fvarOccurrences target term = fvarOccurrences source term := by
  cases shape with
  | bvar index => rfl
  | lit bytes => rfl
  | @app symbol info args hs _ hargs =>
      simp only [fvarOccurrences, isFvarSym_sigExt extension ⟨info, hs⟩,
        fvarOccurrencesList_sigExt extension args hargs]
termination_by sizeOf term
decreasing_by
  exact Term.args_sizeOf_lt_app _ _

theorem fvarOccurrencesList_sigExt {source target : Sig} (extension : SigExt source target)
    (terms : List Term) (shape : TermShapeList source terms) :
    fvarOccurrencesList target terms = fvarOccurrencesList source terms := by
  cases shape with
  | nil => rfl
  | cons head tail =>
      simp only [fvarOccurrencesList, fvarOccurrences_sigExt extension _ head,
        fvarOccurrencesList_sigExt extension _ tail]
termination_by sizeOf terms
decreasing_by
  · exact term_head_sizeOf_lt_cons _ _
  · exact term_tail_sizeOf_lt_cons _ _
end

theorem definitionAdmissible_parameters_known (sig : Sig) (parameters : List SymId)
    (hints : List Nat) (value : Term)
    (admitted : definitionAdmissible sig parameters hints value = true) :
    KnownParameters sig parameters := by
  have hall : parameters.all (isFvarSym sig) = true := by
    simp only [definitionAdmissible, Bool.and_eq_true] at admitted
    exact admitted.1.2
  intro symbol member
  exact knownSymbol_of_isFvarSym (List.all_eq_true.mp hall symbol member)

theorem definitionInfo_sigExt {source target : Sig} (extension : SigExt source target)
    (parameters : List SymId) (known : KnownParameters source parameters) :
    definitionInfo target parameters = definitionInfo source parameters := by
  unfold definitionInfo
  congr 1
  exact List.map_congr_left fun symbol member => symArity_sigExt extension (known symbol member)

theorem definitionStatement_sigExt {source target : Sig} (extension : SigExt source target)
    (symbol : SymId) (parameters : List SymId) (value : Term)
    (known : KnownParameters source parameters) :
    definitionStatement target symbol parameters value =
      definitionStatement source symbol parameters value := by
  unfold definitionStatement
  have hmap := List.map_congr_left fun parameter member =>
    congrArg (etaFvar parameter) (symArity_sigExt extension (known parameter member))
  rw [hmap]

theorem definitionAdmissible_sigExt {source target : Sig} (extension : SigExt source target)
    (parameters : List SymId) (hints : List Nat) (value : Term)
    (known : KnownParameters source parameters) (shape : TermShape source value) :
    definitionAdmissible target parameters hints value =
      definitionAdmissible source parameters hints value := by
  have hfvars : parameters.all (isFvarSym target) = parameters.all (isFvarSym source) := by
    induction parameters with
    | nil => rfl
    | cons symbol parameters ih =>
        have htail : KnownParameters source parameters :=
          fun parameter member => known parameter (List.mem_cons_of_mem symbol member)
        simp only [List.all_cons, isFvarSym_sigExt extension (known symbol (by simp)), ih htail]
  simp only [definitionAdmissible, depth_sigExt extension value shape, hfvars,
    fvarOccurrences_sigExt extension value shape]

end Mettapedia.Languages.VibeITP.Presentation
