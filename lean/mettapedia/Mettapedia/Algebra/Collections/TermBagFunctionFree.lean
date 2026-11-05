import Mettapedia.Algebra.Collections.TermBagBasis
import Mettapedia.Algebra.Collections.FlatBagBasis
import Mathlib.Data.List.InsertIdx

/-!
# Flat bags are the function-free instance of term bags

Flat elements, constants and element variables, are exactly the terms of the
signature without function symbols (`FlatElementEncoding`). Under that
encoding the flat development is the term development on that signature,
piece by piece:

* answers, instances, generality and solutions correspond
  (`instance_encode_iff`, `moreGeneral_encode_iff`, `solves_encode_iff`), and
  every answer of an encoded problem is an encoded answer
  (`encodeAnswer_decodeAnswer`);
* the partial matchings of mapped sides are the mapped matchings
  (`matchings_map`), and the family of an encoded matching is the encoded flat
  family (`candidate_encode`), so the two searches produce the same families
  in the same order (`families_encode`);
* the stable selector commutes with every map that preserves and reflects
  generality (`select_map`), so **the flat basis is the decoded term basis**,
  with the same representatives in the same order (`flat_basis_eq`,
  `flat_executable_eq`).
-/

set_option autoImplicit false

universe u v

namespace Mettapedia.Algebra.Collections.TermBagFunctionFree

open Mettapedia.Logic.LP (LPSignature Term Subst unifyTotal)
open FlatElementEncoding (Element apply encode decode encodeSubst decodeSubst signature)

/-! ## The stable selector under a map -/

section Select

variable {α β : Type*}

theorem finRange_cast {n m : ℕ} (same : n = m) : List.finRange m = (List.finRange n).map (Fin.cast same) := by
  subst same
  simp

/-- **Selection commutes with a map that preserves and reflects generality**:
selecting from the mapped candidates retains the images of the candidates
retained before mapping, in the same order. -/
theorem select_map (items : List α) (g : α → β) (covers : β → β → Prop) [DecidableRel covers]
    (pulled : α → α → Prop) [DecidableRel pulled] (same : ∀ a b, pulled a b ↔ covers (g a) (g b)) :
    FiniteUnifierBasis.select (items.map g) covers = (FiniteUnifierBasis.select items pulled).map g := by
  have length : (items.map g).length = items.length := List.length_map _
  have entry (i : Fin (items.map g).length) : (items.map g).get i = g (items.get (Fin.cast length i)) := by
    simp [List.get_eq_getElem]
  have dominates (better worse : Fin (items.map g).length) :
      FiniteUnifierBasis.Dominates (items.map g) covers better worse ↔
        FiniteUnifierBasis.Dominates items pulled (Fin.cast length better) (Fin.cast length worse) := by
    simp only [FiniteUnifierBasis.Dominates, entry, ← same, Fin.val_cast]
  have kept (i : Fin (items.map g).length) :
      i ∈ FiniteUnifierBasis.retained (items.map g) covers ↔
        Fin.cast length i ∈ FiniteUnifierBasis.retained items pulled := by
    rw [FiniteUnifierBasis.mem_retained, FiniteUnifierBasis.mem_retained]
    apply not_congr
    constructor
    · rintro ⟨other, dominated⟩
      exact ⟨Fin.cast length other, (dominates other i).mp dominated⟩
    · rintro ⟨other, dominated⟩
      refine ⟨Fin.cast length.symm other, (dominates _ i).mpr ?_⟩
      simpa using dominated
  unfold FiniteUnifierBasis.select FiniteUnifierBasis.indices
  rw [finRange_cast length.symm, List.filter_map, List.map_map, List.map_map]
  congr 1
  · funext i
    simp
  · apply List.filter_congr
    intro i _
    simp [kept]

end Select

/-! ## Partial matchings under maps -/

section Matchings

variable {α β α' β' : Type*}

theorem flatMap_finRange_cast {γ : Type*} {n m : ℕ} (same : n = m) (F : Fin m → List γ) :
    (List.finRange m).flatMap F = (List.finRange n).flatMap fun j => F (Fin.cast same j) := by
  subst same
  simp

/-- The partial matchings of mapped lists are the mapped partial matchings, in
the same order. -/
theorem matchings_map (f : α → α') (g : β → β') : ∀ (xs : List α) (ys : List β),
    Unification.matchings (xs.map f) (ys.map g) =
      (Unification.matchings xs ys).map fun r => (r.1.map (Prod.map f g), r.2.1.map f, r.2.2.map g)
  | [], ys => by simp [Unification.matchings]
  | x :: xs, ys => by
      have length : ys.length = (ys.map g).length := (List.length_map _).symm
      rw [List.map_cons, Unification.matchings, Unification.matchings, List.map_append,
        matchings_map f g xs ys, flatMap_finRange_cast length, List.map_flatMap]
      congr 1
      · simp only [List.map_map]
        rfl
      · congr 1
        funext j
        have entry : (ys.map g).get (Fin.cast length j) = g (ys.get j) := by
          simp [List.get_eq_getElem]
        rw [Fin.val_cast, List.eraseIdx_map, matchings_map f g xs (ys.eraseIdx j), entry, List.map_map,
          List.map_map]
        rfl

end Matchings

/-! ## Encoding answers and families -/

section Encoding

variable {A : Type u} {X : Type v}

/-- A flat answer as an answer over the function-free signature. -/
def encodeAnswer (answer : FlatBagUnifiers.Answer A X) : TermBagUnifiers.Answer (signature A X) where
  elements := encodeSubst answer.elements
  rest slot := (answer.rest slot).map encode

/-- An answer over the function-free signature as a flat answer. -/
def decodeAnswer (answer : TermBagUnifiers.Answer (signature A X)) : FlatBagUnifiers.Answer A X where
  elements := decodeSubst answer.elements
  rest slot := (answer.rest slot).map decode

def encodeFamily (family : FlatBagUnifiers.Family A X) : TermBagUnifiers.Family (signature A X) where
  elements := encodeSubst family.elements
  base slot := (family.base slot).map encode

def decodeFamily (family : TermBagUnifiers.Family (signature A X)) : FlatBagUnifiers.Family A X where
  elements := decodeSubst family.elements
  base slot := (family.base slot).map decode

def encodeMatching (matching : FlatBagUnifiers.Matching A X) : TermBagUnifiers.Matching (signature A X) :=
  (matching.1.map (Prod.map encode encode), matching.2.1.map encode, matching.2.2.map encode)

theorem encode_injective : Function.Injective (encode : Element A X → Term (signature A X)) :=
  Function.LeftInverse.injective (g := decode) fun element => FlatElementEncoding.decode_encode element

@[simp] theorem decodeSubst_encodeSubst (assignment : X → Element A X) :
    decodeSubst (encodeSubst assignment) = assignment := by
  funext name
  simp [decodeSubst, encodeSubst]

@[simp] theorem encodeSubst_decodeSubst (assignment : Subst (signature A X)) :
    encodeSubst (decodeSubst assignment) = assignment := by
  funext name
  simp [decodeSubst, encodeSubst]

@[simp] theorem decode_map_encode (bag : Multiset (Element A X)) : (bag.map encode).map decode = bag := by
  simp [Multiset.map_map]

@[simp] theorem encode_map_decode (bag : Multiset (Term (signature A X))) : (bag.map decode).map encode = bag := by
  simp [Multiset.map_map]

@[simp] theorem decodeFamily_encodeFamily (family : FlatBagUnifiers.Family A X) :
    decodeFamily (encodeFamily family) = family := by
  apply FlatBagUnifiers.Family.ext
  · exact decodeSubst_encodeSubst family.elements
  · funext slot
    exact decode_map_encode (family.base slot)

@[simp] theorem encodeFamily_decodeFamily (family : TermBagUnifiers.Family (signature A X)) :
    encodeFamily (decodeFamily family) = family := by
  apply TermBagUnifiers.Family.ext
  · exact encodeSubst_decodeSubst family.elements
  · funext slot
    exact encode_map_decode (family.base slot)

@[simp] theorem encodeAnswer_decodeAnswer (answer : TermBagUnifiers.Answer (signature A X)) :
    encodeAnswer (decodeAnswer answer) = answer := by
  apply TermBagUnifiers.Answer.ext
  · exact encodeSubst_decodeSubst answer.elements
  · funext slot
    exact encode_map_decode (answer.rest slot)

theorem encodeAnswer_injective : Function.Injective (encodeAnswer (A := A) (X := X)) := by
  intro first second same
  have elements := congrArg (fun answer => decodeSubst answer.elements) same
  have rests := congrArg (fun answer => fun slot => (TermBagUnifiers.Answer.rest answer slot).map decode) same
  apply FlatBagUnifiers.Answer.ext
  · simpa [encodeAnswer] using elements
  · funext slot
    simpa [encodeAnswer] using congrFun rests slot

theorem encodeSubst_comp (outer inner : X → Element A X) :
    encodeSubst (fun name => apply outer (inner name)) = encodeSubst outer ∘ₛ encodeSubst inner := by
  funext name
  exact FlatElementEncoding.encode_apply outer (inner name.down)

theorem encodeAnswer_instantiate (family : FlatBagUnifiers.Family A X) (remainder : X → Element A X)
    (common : Multiset (Element A X)) :
    encodeAnswer (FlatBagUnifiers.instantiate family remainder common) =
      TermBagUnifiers.instantiate (encodeFamily family) (encodeSubst remainder) (common.map encode) := by
  apply TermBagUnifiers.Answer.ext
  · exact encodeSubst_comp remainder family.elements
  · funext slot
    simp only [encodeAnswer, FlatBagUnifiers.instantiate, TermBagUnifiers.instantiate, encodeFamily,
      Multiset.map_add, Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro element _
    exact FlatElementEncoding.encode_apply remainder element

theorem encodeAnswer_generic (family : FlatBagUnifiers.Family A X) :
    encodeAnswer (FlatBagUnifiers.genericAnswer family) = TermBagUnifiers.genericAnswer (encodeFamily family) :=
  rfl

/-- Instances correspond. -/
theorem instance_encode_iff (family : FlatBagUnifiers.Family A X) (answer : FlatBagUnifiers.Answer A X) :
    TermBagUnifiers.Instance (encodeFamily family) (encodeAnswer answer) ↔
      FlatBagUnifiers.Instance family answer := by
  constructor
  · rintro ⟨remainder, common, represented⟩
    refine ⟨decodeSubst remainder, common.map decode, encodeAnswer_injective ?_⟩
    rw [encodeAnswer_instantiate, encodeSubst_decodeSubst, encode_map_decode]
    exact represented
  · rintro ⟨remainder, common, rfl⟩
    exact ⟨encodeSubst remainder, common.map encode, encodeAnswer_instantiate family remainder common⟩

/-- Generality corresponds. -/
theorem moreGeneral_encode_iff (general specific : FlatBagUnifiers.Family A X) :
    TermBagUnifiers.MoreGeneral (encodeFamily general) (encodeFamily specific) ↔
      FlatBagUnifiers.MoreGeneral general specific :=
  instance_encode_iff general (FlatBagUnifiers.genericAnswer specific)

theorem encode_map_apply (assignment : X → Element A X) (elements : List (Element A X)) :
    (((elements.map encode).map (encodeSubst assignment).applyTerm : List (Term (signature A X))) :
        Multiset (Term (signature A X))) =
      ((elements.map (apply assignment) : List (Element A X)) : Multiset (Element A X)).map encode := by
  rw [Multiset.map_coe, List.map_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro element _
  exact (FlatElementEncoding.encode_apply assignment element).symm

/-- Solutions correspond. -/
theorem solves_encode_iff (left right : List (Element A X)) (answer : FlatBagUnifiers.Answer A X) :
    TermBagUnifiers.Solves (left.map encode) (right.map encode) (encodeAnswer answer) ↔
      FlatBagUnifiers.Solves left right answer := by
  unfold TermBagUnifiers.Solves FlatBagUnifiers.Solves
  change (((left.map encode).map (encodeSubst answer.elements).applyTerm : List (Term (signature A X))) :
      Multiset (Term (signature A X))) + (answer.rest .left).map encode =
    (((right.map encode).map (encodeSubst answer.elements).applyTerm : List (Term (signature A X))) :
      Multiset (Term (signature A X))) + (answer.rest .right).map encode ↔ _
  rw [encode_map_apply, encode_map_apply, ← Multiset.map_add, ← Multiset.map_add]
  exact (Multiset.map_injective encode_injective).eq_iff

theorem matchings_encode (left right : List (Element A X)) :
    Unification.matchings (left.map encode) (right.map encode) =
      (Unification.matchings left right).map encodeMatching :=
  matchings_map encode encode left right

theorem fromMatching_encode (matching : FlatBagUnifiers.Matching A X) (general : Subst (signature A X)) :
    TermBagUnifiers.fromMatching (encodeMatching matching) general =
      encodeFamily (FlatBagUnifiers.fromMatching matching (decodeSubst general)) := by
  have side (elements : List (Element A X)) :
      (((elements.map encode).map general.applyTerm : List (Term (signature A X))) :
          Multiset (Term (signature A X))) =
        ((elements.map (apply (decodeSubst general)) : List (Element A X)) : Multiset (Element A X)).map encode := by
    rw [← encode_map_apply, encodeSubst_decodeSubst]
  apply TermBagUnifiers.Family.ext
  · exact (encodeSubst_decodeSubst general).symm
  · funext slot
    cases slot with
    | left => exact side matching.2.2
    | right => exact side matching.2.1

variable [DecidableEq A] [DecidableEq X]

/-- The family of an encoded matching is the encoded flat family. -/
theorem candidate_encode (matching : FlatBagUnifiers.Matching A X) :
    TermBagUnifiers.candidate (encodeMatching matching) = (FlatBagUnifiers.candidate matching).map encodeFamily := by
  unfold TermBagUnifiers.candidate FlatBagUnifiers.candidate FlatElementEncoding.solve
  rw [Option.map_map, Option.map_map]
  change (unifyTotal (FlatElementEncoding.equations matching.1)).map _ = _
  congr 1
  funext general
  exact fromMatching_encode matching general

/-- **The two searches produce the same families, in the same order.** -/
theorem families_encode (left right : List (Element A X)) :
    TermBagUnifiers.families (left.map encode) (right.map encode) =
      (FlatBagUnifiers.families left right).map encodeFamily := by
  unfold TermBagUnifiers.families FlatBagUnifiers.families
  rw [matchings_encode, List.filterMap_map, List.map_filterMap]
  congr 1
  funext matching
  exact candidate_encode matching

/-- The term basis of the encoded problem is the encoded flat basis, whatever
procedures decide generality. -/
theorem basis_encode [DecidableRel (FlatBagUnifiers.MoreGeneral : FlatBagUnifiers.Family A X → _ → Prop)]
    [DecidableRel (TermBagUnifiers.MoreGeneral : TermBagUnifiers.Family (signature A X) → _ → Prop)]
    (left right : List (Element A X)) :
    TermBagBasis.basis (left.map encode) (right.map encode) = (FlatBagBasis.basis left right).map encodeFamily := by
  unfold TermBagBasis.basis FlatBagBasis.basis
  rw [families_encode]
  exact select_map _ encodeFamily _ _ fun general specific => (moreGeneral_encode_iff general specific).symm

/-- **The flat basis is the function-free instance of the term basis.** -/
theorem flat_basis_eq [DecidableRel (FlatBagUnifiers.MoreGeneral : FlatBagUnifiers.Family A X → _ → Prop)]
    [DecidableRel (TermBagUnifiers.MoreGeneral : TermBagUnifiers.Family (signature A X) → _ → Prop)]
    (left right : List (Element A X)) :
    FlatBagBasis.basis left right = (TermBagBasis.basis (left.map encode) (right.map encode)).map decodeFamily := by
  rw [basis_encode, List.map_map]
  conv_lhs => rw [← List.map_id (FlatBagBasis.basis left right)]
  congr 1
  funext family
  simp

/-- The executable flat basis, computed with the flat checker, is the decoded
executable term basis, computed with the term checker. -/
theorem flat_executable_eq [Fintype X] (left right : List (Element A X)) :
    FlatBagBasis.executable left right =
      (TermBagBasis.executable (left.map encode) (right.map encode)).map decodeFamily :=
  flat_basis_eq left right

end Encoding

end Mettapedia.Algebra.Collections.TermBagFunctionFree
