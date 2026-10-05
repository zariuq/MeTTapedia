import Mettapedia.Languages.VibeITP.Presentation.ShiftCorrespondence

/-!
# Finite signature data for arbitrary shift queries

A raw term has finitely many application heads. Its signature snapshot stores
exactly the available information at those heads; unknown heads remain absent.
Duplicate occurrences need no uniqueness assumption because every occurrence
gets the same immutable information.

Depth and shifting inspect only these binder lists. The snapshot therefore
computes the same result for an arbitrary specification signature, without
requiring a global finite signature or well-formed input term.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation.ComputationalShift

open ComputationalData
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

def tableFor (signature : Spec.Sig) : List Spec.SymId → SignatureTable
  | [] => []
  | symbol :: rest =>
      match signature symbol with
      | none => tableFor signature rest
      | some info => (symbol, info) :: tableFor signature rest

theorem tableFor_lookup (signature : Spec.Sig) (symbols : List Spec.SymId) (symbol : Spec.SymId) :
    signatureOf (tableFor signature symbols) symbol =
      if symbol ∈ symbols then signature symbol else none := by
  induction symbols with
  | nil => rfl
  | cons first rest ih =>
      cases declared : signature first with
      | none =>
          by_cases same : symbol = first
          · subst symbol
            simp [tableFor, declared, ih]
          · simp [tableFor, declared, ih, same]
      | some info =>
          by_cases same : symbol = first
          · subst symbol
            simp [tableFor, declared, signatureOf]
          · simp [tableFor, declared, signatureOf, ih, same]

mutual
def termHeads : Spec.Term → List Spec.SymId
  | .bvar _ => []
  | .lit _ => []
  | .app symbol terms => symbol :: termHeadsList terms

def termHeadsList : List Spec.Term → List Spec.SymId
  | [] => []
  | first :: rest => termHeads first ++ termHeadsList rest
end

def snapshot (signature : Spec.Sig) (term : Spec.Term) : SignatureTable :=
  tableFor signature (termHeads term)

theorem snapshot_lookup (signature : Spec.Sig) (term : Spec.Term) (symbol : Spec.SymId)
    (used : symbol ∈ termHeads term) : signatureOf (snapshot signature term) symbol = signature symbol := by
  simp only [snapshot, tableFor_lookup, used, ↓reduceIte]

def BindersAgree (source target : Spec.Sig) (heads : List Spec.SymId) : Prop :=
  ∀ symbol ∈ heads, bindersOf source symbol = bindersOf target symbol

theorem BindersAgree.head {source target : Spec.Sig} {symbol : Spec.SymId} {heads : List Spec.SymId}
    (agree : BindersAgree source target (symbol :: heads)) :
    bindersOf source symbol = bindersOf target symbol := agree symbol (List.mem_cons_self ..)

theorem BindersAgree.tail {source target : Spec.Sig} {symbol : Spec.SymId} {heads : List Spec.SymId}
    (agree : BindersAgree source target (symbol :: heads)) : BindersAgree source target heads :=
  fun next member => agree next (List.mem_cons_of_mem _ member)

theorem BindersAgree.left {source target : Spec.Sig} {left right : List Spec.SymId}
    (agree : BindersAgree source target (left ++ right)) : BindersAgree source target left :=
  fun symbol member => agree symbol (List.mem_append_left _ member)

theorem BindersAgree.right {source target : Spec.Sig} {left right : List Spec.SymId}
    (agree : BindersAgree source target (left ++ right)) : BindersAgree source target right :=
  fun symbol member => agree symbol (List.mem_append_right _ member)

theorem snapshot_binders (signature : Spec.Sig) (term : Spec.Term) :
    BindersAgree (signatureOf (snapshot signature term)) signature (termHeads term) := by
  intro symbol used
  unfold bindersOf
  rw [snapshot_lookup signature term symbol used]

mutual
theorem depth_on_heads (source target : Spec.Sig) (term : Spec.Term)
    (agree : BindersAgree source target (termHeads term)) : Spec.depth source term = Spec.depth target term := by
  cases term with
  | bvar _ => rfl
  | lit _ => rfl
  | app symbol terms =>
      rw [Presentation.depth_app, Presentation.depth_app, agree.head]
      exact depthList_on_heads source target _ terms agree.tail

theorem depthList_on_heads (source target : Spec.Sig) (binders : List Nat) (terms : List Spec.Term)
    (agree : BindersAgree source target (termHeadsList terms)) :
    depthBinders source binders terms = depthBinders target binders terms := by
  cases terms with
  | nil => rfl
  | cons first rest =>
      rw [depthBinders, depthBinders, depth_on_heads source target first agree.left,
        depthList_on_heads source target binders.tail rest agree.right]
end

mutual
theorem shift_on_heads (source target : Spec.Sig) (amount cutoff : Nat) (term : Spec.Term)
    (agree : BindersAgree source target (termHeads term)) :
    Spec.shift source amount cutoff term = Spec.shift target amount cutoff term := by
  cases term with
  | bvar _ => rfl
  | lit _ => rfl
  | app symbol terms =>
      rw [Spec.shift, Spec.shift, depth_on_heads source target (.app symbol terms) agree]
      split
      · rfl
      · rw [shiftArgs_eq, shiftArgs_eq, List.drop_zero, List.drop_zero, agree.head,
          shiftList_on_heads source target amount cutoff _ terms agree.tail]

theorem shiftList_on_heads (source target : Spec.Sig) (amount cutoff : Nat)
    (binders : List Nat) (terms : List Spec.Term)
    (agree : BindersAgree source target (termHeadsList terms)) :
    shiftList source amount cutoff binders terms = shiftList target amount cutoff binders terms := by
  cases terms with
  | nil => rfl
  | cons first rest =>
      rw [shiftList, shiftList]
      split
      · rw [shift_on_heads source target amount (cutoff + binders.headD 0) first agree.left,
          shiftList_on_heads source target amount cutoff binders.tail rest agree.right]
      · rfl
end

theorem snapshot_depth (signature : Spec.Sig) (term : Spec.Term) :
    Spec.depth (signatureOf (snapshot signature term)) term = Spec.depth signature term :=
  depth_on_heads _ _ _ (snapshot_binders signature term)

theorem snapshot_shift (signature : Spec.Sig) (amount cutoff : Nat) (term : Spec.Term) :
    Spec.shift (signatureOf (snapshot signature term)) amount cutoff term =
      Spec.shift signature amount cutoff term :=
  shift_on_heads _ _ _ _ _ (snapshot_binders signature term)

/-- Every shift query for an arbitrary signature has a sufficient finite
data snapshot. No signature or shift operation is delegated to the host. -/
theorem shift_computes_for_signature (signature : Spec.Sig) (amount cutoff : Nat) (term : Spec.Term) :
    Applies shiftProgram computationalHost "vibe:shift"
      [encodeTable (snapshot signature term), encode term, natural amount, natural cutoff]
      (encodeResult (Spec.shift signature amount cutoff term)) := by
  rw [← snapshot_shift signature amount cutoff term]
  exact shift_computes _ _ _ _

theorem shift_signature_result_exact (signature : Spec.Sig) (amount cutoff : Nat) (term : Spec.Term)
    (result : Term) :
    Applies shiftProgram computationalHost "vibe:shift"
      [encodeTable (snapshot signature term), encode term, natural amount, natural cutoff] result ↔
      result = encodeResult (Spec.shift signature amount cutoff term) := by
  rw [shift_result_exact, snapshot_shift]

end Mettapedia.Languages.VibeITP.Presentation.ComputationalShift
