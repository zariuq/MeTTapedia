import Mettapedia.Languages.MM0.Presentation.TypingProgram
import Mettapedia.GSLT.LanguageDef.DeterministicEquations.Computation

/-! # Exact lookup computations of the authored MM0 typing program -/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Presentation.ComputationalTyping

open Kernel ComputationalContext
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => typingProgram
local notation "H" => computationalHost

def encodeItemResult : Option Term → Term
  | none => .sym "None"
  | some item => .expr [.sym "Some", item]

theorem view_applies (values : List Term) :
    Applies P H "nik:list-view" [.list values] (listView values) :=
  .primitive (by rfl) (computationalHost_list_view values)

theorem equal_applies (left right : Nat) :
    Applies P H "nik:nat-eq" [natural left, natural right] (boolean (decide (left = right))) :=
  .primitive (by rfl) (naturalArithmeticHost_eq left right)

private theorem at_start (values : List Term) (index : Nat) (result : Term)
    (next : Applies P H "mm0:at-view" [listView values, natural index] result) :
    Applies P H "mm0:data-at" [.list values, natural index] result := by
  refine Applies.equation (equation := P[0])
    (environment := [("values", .list values), ("index", natural index)]) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) .nil)) next
  exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (view_applies values)

private theorem at_cons (first : Term) (rest : List Term) (index : Nat) (result : Term)
    (next : Applies P H "mm0:at-zero"
      [.sym (if index = 0 then "True" else "False"), first, .list rest, natural index] result) :
    Applies P H "mm0:at-view" [listView (first :: rest), natural index] result := by
  refine Applies.equation (equation := P[2])
    (environment := [("first", first), ("rest", .list rest), ("index", natural index)])
    (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))) next
  exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil)
    (.primitive (by rfl) (computationalHost_zero index))

private theorem at_next (first : Term) (rest : List Term) (index : Nat) (result : Term)
    (next : Applies P H "mm0:data-at" [.list rest, natural index] result) :
    Applies P H "mm0:at-zero" [.sym "False", first, .list rest, natural (index + 1)] result := by
  refine Applies.equation (equation := P[4])
    (environment := [("first", first), ("rest", .list rest), ("index", natural (index + 1))])
    (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) (.cons ?_ .nil)) next
  exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil)
    (.primitive (by rfl) (computationalHost_pred (index + 1)))

theorem at_computes (values : List Term) (index : Nat) :
    Applies P H "mm0:data-at" [.list values, natural index] (encodeItemResult values[index]?) := by
  induction values generalizing index with
  | nil => exact at_start [] index _ ⟨1, rfl⟩
  | cons first rest ih =>
    apply at_start
    apply at_cons
    cases index with
    | zero => exact ⟨2, rfl⟩
    | succ index =>
      simpa only [Nat.add_one_ne_zero, ↓reduceIte, List.getElem?_cons_succ] using
        at_next first rest index _ (ih index)

theorem context_lookup_computes (context : Context) (index : Nat) :
    Applies P H "mm0:data-at" [encodeContext context, natural index]
      (encodeBinderResult context[index]?) := by
  have done := at_computes (context.map encodeBinder) index
  rw [List.getElem?_map] at done
  cases found : context[index]? <;> simpa [encodeContext, found, encodeItemResult, encodeBinderResult] using done

private theorem declaration_start (table : SignatureTable) (index : Nat) (result : Term)
    (next : Applies P H "mm0:declaration-view"
      [listView (table.map fun (key, decl) => .list [natural key, encodeDeclaration decl]), natural index] result) :
    Applies P H "mm0:declaration" [encodeTable table, natural index] result := by
  refine Applies.equation (equation := P[5])
    (environment := [("table", encodeTable table), ("index", natural index)]) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) .nil)) next
  exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (view_applies _)

private theorem declaration_cons (key index : Nat) (declaration : TermDecl)
    (rest : SignatureTable) (result : Term)
    (next : Applies P H "mm0:declaration-equal"
      [boolean (decide (index = key)), encodeDeclaration declaration, encodeTable rest, natural index] result) :
    Applies P H "mm0:declaration-view"
      [listView (((key, declaration) :: rest).map fun (key, decl) =>
        .list [natural key, encodeDeclaration decl]), natural index] result := by
  refine Applies.equation (equation := P[7])
    (environment := [("key", natural key), ("declaration", encodeDeclaration declaration),
      ("rest", encodeTable rest), ("index", natural index)]) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))) next
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (equal_applies index key)

private theorem declaration_next (declaration : TermDecl) (rest : SignatureTable) (index : Nat)
    (result : Term) (next : Applies P H "mm0:declaration" [encodeTable rest, natural index] result) :
    Applies P H "mm0:declaration-equal"
      [.sym "False", encodeDeclaration declaration, encodeTable rest, natural index] result := by
  refine Applies.equation (equation := P[9])
    (environment := [("declaration", encodeDeclaration declaration), ("rest", encodeTable rest),
      ("index", natural index)]) (by rfl) (by rfl) ?_
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) next

theorem declaration_computes (table : SignatureTable) (index : Nat) :
    Applies P H "mm0:declaration" [encodeTable table, natural index]
      (encodeDeclarationResult (signatureOf table index)) := by
  induction table with
  | nil => exact declaration_start [] index _ ⟨1, rfl⟩
  | cons entry rest ih =>
    obtain ⟨key, declaration⟩ := entry
    apply declaration_start
    apply declaration_cons
    by_cases same : index = key
    · subst index
      exact ⟨2, by simp only [signatureOf, ↓reduceIte]; rfl⟩
    · simpa [signatureOf, same, boolean] using declaration_next declaration rest index _ ih

private theorem bound_binder_computes (binder : Option Kernel.Binder) :
    Applies P H "mm0:bound-binder" [encodeBinderResult binder]
      (encodeSortResult (match binder with | some (.bound sort) => some sort | _ => none)) := by
  cases binder with
  | none => exact ⟨1, rfl⟩
  | some binder => cases binder <;> exact ⟨2, rfl⟩

theorem bound_sort_computes (context : Context) (expression : Preterm) :
    Applies P H "mm0:bound-sort" [encodeContext context, encode expression]
      (encodeSortResult (Preterm.boundSort? context expression)) := by
  cases expression with
  | var index =>
    refine Applies.equation (equation := P[23])
      (environment := [("context", encodeContext context), ("index", natural index)]) (by rfl) (by rfl) ?_
    refine Evaluates.call (by simp [Special]) (.cons ?_ .nil) (bound_binder_computes context[index]?)
    exact Evaluates.call (by simp [Special])
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (context_lookup_computes context index)
  | term index => exact ⟨1, rfl⟩
  | app function argument => exact ⟨1, rfl⟩

end Mettapedia.Languages.MM0.Presentation.ComputationalTyping
