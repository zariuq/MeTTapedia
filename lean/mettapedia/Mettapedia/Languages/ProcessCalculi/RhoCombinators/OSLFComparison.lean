import Mettapedia.Languages.ProcessCalculi.RhoCombinators.Characteristic
import Mettapedia.OSLF.StructuralModal.SeparatingConjunction

/-!
# Comparison with the structural-modal logic of OSLF

The spatial logic of `GSLT/Logic/SpatialCharacteristic.lean` is not a rival to
`OSLF/StructuralModal/Formula.lean`.  This module says exactly how the two are
related at the combinator carrier, and exactly where they part.

A process is encoded as an OSLF pattern: a term becomes the bag of its
components, and an atom becomes an application node whose arguments are
encoded as bags in turn (`encList`, `enc`).  Congruent processes are encoded by
lists differing by a permutation (`perm_encList_of_cong`), which is the
statement that the encoding respects the presentation's equations.

**Where the two agree.**  On the fragment with no atom former, satisfaction
depends only on how many components a bag has, and there the translation into
OSLF's own `emptyColl`/`cut` formers is exact: `spatial_agrees` proves
`Sat rhoSoup φ m ↔ satisfiesOver inertSpan (tr φ) (.collection .hashBag l none)`
for every element list of the matching length.  So on that fragment `sep` *is*
OSLF's collection cut, and the reuse is proved rather than asserted.

**Where they part, and why it is not a conflation.**  `sep` is symmetric
(`sat_sep_comm`), because a bag sum is.  OSLF's positional reading of the same
split is not — `SeparatingConjunction.positional_not_closed_under_swap` is the
existing counterexample, and `SeparatingConjunction.sepConj_comm` recovers
symmetry only from the presentation's permutation law.  So `sep` matches OSLF's
`SepConj`, its equation-relative reading, and not its `PositionalConj`.  The
agreement above is not in tension with this: an atom-free formula cannot tell
two components apart, so the order a split happens to take is immaterial there,
and it is exactly the atom former that makes order visible.

**The obstruction.**  OSLF's atom-like former is `Formula.headed`, which holds
only of an application node, while an encoded process is always a collection:
`no_headed_at_enc` proves that no `headed` formula holds at any encoded term.
So that language has no connective for *a bag with one element, which satisfies
a formula*, and this lane's atom former is exactly the missing one.  Adding it
to `OSLF.StructuralModal.Formula` would extend an inductive type with several
exhaustive consumers, including its certificate calculus, so it is proposed
here rather than performed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCombinators
namespace OSLFComparison

open Comb
open Mettapedia.GSLT.SpatialCharacteristic
open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern CollType)
open Mettapedia.OSLF.StructuralModal (satisfiesOver)
open Mettapedia.OSLF.StructuralModal.SeparatingConjunction (inertSpan PositionalConj)

/-- OSLF's structural-modal formula type, under a name that does not clash with
this lane's spatial `Formula`. -/
abbrev OFormula := Mettapedia.OSLF.StructuralModal.Formula

/-! ## The encoding -/

/-- The name OSLF sees for a shape. -/
def shapeName : Shape → String
  | .mm => "mm"
  | .dd => "dd"
  | .kk => "kk"
  | .fw => "fw"
  | .bl => "bl"
  | .br => "br"
  | .sy => "sy"
  | .ev => "ev"
  | .qq => "qq"
  | .consPar => "consPar"
  | .consMsg => "consMsg"
  | .consDup => "consDup"
  | .consSyn => "consSyn"

/-- A bag of encoded arguments. -/
private def bagOf (l : List Pattern) : Pattern := .collection .hashBag l none

/-- A process as the list of its encoded components.  An atom becomes an
application node whose arguments are encoded as bags in turn; this is
structural recursion, because an argument is a proper subterm. -/
def encList : Comb → List Pattern
  | nil => []
  | par p q => encList p ++ encList q
  | mm a b => [.apply "mm" [bagOf (encList a), bagOf (encList b)]]
  | dd a b c => [.apply "dd" [bagOf (encList a), bagOf (encList b), bagOf (encList c)]]
  | kk a => [.apply "kk" [bagOf (encList a)]]
  | fw a b => [.apply "fw" [bagOf (encList a), bagOf (encList b)]]
  | bl a b => [.apply "bl" [bagOf (encList a), bagOf (encList b)]]
  | br a b => [.apply "br" [bagOf (encList a), bagOf (encList b)]]
  | sy a b c => [.apply "sy" [bagOf (encList a), bagOf (encList b), bagOf (encList c)]]
  | ev a => [.apply "ev" [bagOf (encList a)]]
  | qq a p => [.apply "qq" [bagOf (encList a), bagOf (encList p)]]
  | consPar a b c =>
      [.apply "consPar" [bagOf (encList a), bagOf (encList b), bagOf (encList c)]]
  | consMsg a b c =>
      [.apply "consMsg" [bagOf (encList a), bagOf (encList b), bagOf (encList c)]]
  | consDup a b c e =>
      [.apply "consDup" [bagOf (encList a), bagOf (encList b), bagOf (encList c),
        bagOf (encList e)]]
  | consSyn a b c e =>
      [.apply "consSyn" [bagOf (encList a), bagOf (encList b), bagOf (encList c),
        bagOf (encList e)]]

/-- A process as an OSLF pattern: the bag of its encoded components. -/
def enc (t : Comb) : Pattern := bagOf (encList t)

theorem enc_eq (t : Comb) : enc t = .collection .hashBag (encList t) none := rfl

/-- The encoding has one entry per component. -/
theorem length_encList : ∀ t : Comb, (encList t).length = (componentList t).length
  | nil => rfl
  | par p q => by
      simp only [encList, componentList, List.length_append, length_encList p,
        length_encList q]
  | mm _ _ | dd _ _ _ | kk _ | fw _ _ | bl _ _ | br _ _ | sy _ _ _
  | ev _ | qq _ _ | consPar _ _ _ | consMsg _ _ _ | consDup _ _ _ _
  | consSyn _ _ _ _ => rfl

theorem length_encList_eq_card (t : Comb) :
    (encList t).length = Multiset.card (components t) := by
  rw [length_encList, components_eq_coe, Multiset.coe_card]

/-- **The encoding respects the equations.**  Congruent processes are encoded by
lists that differ by a permutation of the component bag, which is why the
equation-relative reading of the cut is the right one. -/
theorem perm_encList_of_cong : ∀ {p q : Comb}, Cong p q → (encList p).Perm (encList q) := by
  intro p q h
  induction h with
  | refl p => exact List.Perm.refl _
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | parNil p => simpa only [encList, List.append_nil] using List.Perm.refl (encList p)
  | parComm p q => simpa only [encList] using List.perm_append_comm
  | parAssoc p q r => simpa only [encList, List.append_assoc] using List.Perm.refl _
  | parLeft q _ ih => simpa only [encList] using ih.append_right _
  | parRight p _ ih => simpa only [encList] using ih.append_left _

/-! ## Splitting a bag at a prescribed size -/

theorem exists_split_of_card {m : Multiset Comb} {k₁ k₂ : Nat}
    (h : Multiset.card m = k₁ + k₂) :
    ∃ m₁ m₂, m = m₁ + m₂ ∧ Multiset.card m₁ = k₁ ∧ Multiset.card m₂ = k₂ := by
  refine ⟨(m.toList.take k₁ : Multiset Comb), (m.toList.drop k₁ : Multiset Comb), ?_, ?_, ?_⟩
  · calc m = (m.toList : Multiset Comb) := (Multiset.coe_toList m).symm
      _ = ((m.toList.take k₁ ++ m.toList.drop k₁ : List Comb) : Multiset Comb) := by
            rw [List.take_append_drop]
      _ = _ := Multiset.coe_add _ _
  · rw [Multiset.coe_card, List.length_take, Multiset.length_toList]
    omega
  · rw [Multiset.coe_card, List.length_drop, Multiset.length_toList]
    omega

/-! ## The atom-free fragment, and exact agreement there -/

/-- Formulas with no atom former. -/
inductive AtomFree : Formula Shape → Prop
  | nil : AtomFree .nil
  | top : AtomFree .top
  | sep {l r : Formula Shape} : AtomFree l → AtomFree r → AtomFree (.sep l r)
  | and {l r : Formula Shape} : AtomFree l → AtomFree r → AtomFree (.and l r)
  | or {l r : Formula Shape} : AtomFree l → AtomFree r → AtomFree (.or l r)

/-- The translation into OSLF's own formula language.  The atom former has no
image, which is the obstruction recorded at the end of this file. -/
def tr : Formula Shape → OFormula
  | .nil => .emptyColl .hashBag
  | .top => .top
  | .sep l r => .cut .hashBag (tr l) (tr r)
  | .and l r => .and (tr l) (tr r)
  | .or l r => .or (tr l) (tr r)
  | .atom _ _ => .bot

/-- **Exact agreement on the atom-free fragment.**  A bag satisfies an
atom-free formula exactly when any OSLF collection with as many elements
satisfies the translated formula. -/
theorem spatial_agrees {φ : Formula Shape} (free : AtomFree φ) :
    ∀ (m : Multiset Comb) (l : List Pattern), l.length = Multiset.card m →
      (Sat rhoSoup φ m ↔
        satisfiesOver inertSpan (tr φ)
          (.collection .hashBag l none)) := by
  induction free with
  | nil =>
      intro m l hlen
      rw [sat_nil_iff]
      simp only [tr, satisfiesOver]
      constructor
      · rintro rfl
        simp only [Multiset.card_zero] at hlen
        rw [List.eq_nil_of_length_eq_zero hlen]
      · intro h
        have : l = [] := by
          have := congrArg (fun p => match p with
            | Pattern.collection _ elements _ => elements
            | _ => []) h
          simpa using this
        rw [this, List.length_nil] at hlen
        exact (Multiset.card_eq_zero).mp hlen.symm
  | top =>
      intro m l _
      simp only [tr, satisfiesOver]
      exact ⟨fun _ => trivial, fun _ => .top m⟩
  | @sep φ₁ φ₂ _ _ ih₁ ih₂ =>
      intro m l hlen
      rw [sat_sep_iff]
      simp only [tr, satisfiesOver]
      constructor
      · rintro ⟨m₁, m₂, rfl, h₁, h₂⟩
        refine ⟨l.take (Multiset.card m₁), l.drop (Multiset.card m₁),
          by rw [List.take_append_drop], ?_, ?_⟩
        · refine (ih₁ m₁ _ ?_).mp h₁
          rw [List.length_take]
          rw [Multiset.card_add] at hlen
          omega
        · refine (ih₂ m₂ _ ?_).mp h₂
          rw [List.length_drop]
          rw [Multiset.card_add] at hlen
          omega
      · rintro ⟨le, re, hsplit, h₁, h₂⟩
        have hle : l = le ++ re := by
          have := congrArg (fun p => match p with
            | Pattern.collection _ elements _ => elements
            | _ => []) hsplit
          simpa using this
        obtain ⟨m₁, m₂, rfl, hc₁, hc₂⟩ :=
          exists_split_of_card (m := m) (k₁ := le.length) (k₂ := re.length)
            (by rw [← hlen, hle, List.length_append])
        exact ⟨m₁, m₂, rfl, (ih₁ m₁ le hc₁.symm).mpr h₁, (ih₂ m₂ re hc₂.symm).mpr h₂⟩
  | @and φ₁ φ₂ _ _ ih₁ ih₂ =>
      intro m l hlen
      rw [sat_and_iff]
      simp only [tr, satisfiesOver]
      exact and_congr (ih₁ m l hlen) (ih₂ m l hlen)
  | @or φ₁ φ₂ _ _ ih₁ ih₂ =>
      intro m l hlen
      rw [sat_or_iff]
      simp only [tr, satisfiesOver]
      exact or_congr (ih₁ m l hlen) (ih₂ m l hlen)

/-- The agreement at an encoded process. -/
theorem spatial_agrees_enc {φ : Formula Shape} (free : AtomFree φ) (t : Comb) :
    Sat rhoSoup φ (components t) ↔
      satisfiesOver inertSpan (tr φ) (enc t) :=
  spatial_agrees free (components t) (encList t) (length_encList_eq_card t)

/-! ## Where the two part -/

/-- **`sep` is symmetric**, because a bag sum is.  This is the law that
distinguishes it from the positional reading. -/
theorem sat_sep_comm {φ ψ : Formula Shape} {m : Multiset Comb} :
    Sat rhoSoup (.sep φ ψ) m ↔ Sat rhoSoup (.sep ψ φ) m := by
  rw [sat_sep_iff, sat_sep_iff]
  constructor
  · rintro ⟨m₁, m₂, rfl, h₁, h₂⟩; exact ⟨m₂, m₁, add_comm _ _, h₂, h₁⟩
  · rintro ⟨m₁, m₂, rfl, h₁, h₂⟩; exact ⟨m₂, m₁, add_comm _ _, h₂, h₁⟩

/-- The positional reading is *not* symmetric; the counterexample is the one
`SeparatingConjunction.lean` already records, cited here so the comparison
rests on that file rather than on a fresh claim. -/
theorem positional_not_symmetric :
    ¬ PositionalConj .hashBag
        Mettapedia.OSLF.StructuralModal.SeparatingConjunction.Difference.isSingletonB
        Mettapedia.OSLF.StructuralModal.SeparatingConjunction.Difference.isSingletonA
        Mettapedia.OSLF.StructuralModal.SeparatingConjunction.Difference.bagAB :=
  Mettapedia.OSLF.StructuralModal.SeparatingConjunction.Difference.positional_not_closed_under_swap

/-- **The obstruction.**  OSLF's atom-like former holds only of an application
node, and an encoded process is always a collection, so no `headed` formula
holds at any encoded term.  A connective for "a bag with one element satisfying
a formula" is therefore absent from that language, and is exactly what this
lane's atom former supplies. -/
theorem no_headed_at_enc (constructor : String)
    (arguments : List OFormula) (t : Comb) :
    ¬ satisfiesOver inertSpan
        (.headed constructor arguments) (enc t) := by
  intro h
  simp only [satisfiesOver] at h
  obtain ⟨children, hshape, -⟩ := h
  rw [enc_eq] at hshape
  simp at hshape

/-- And therefore the translation cannot be extended to the atom former by any
choice of OSLF formula that is meant to hold at encoded atoms. -/
theorem tr_atom_is_unsatisfiable (s : Shape) (arguments : List (Formula Shape))
    (t : Comb) :
    ¬ satisfiesOver inertSpan
        (tr (.atom s arguments)) (enc t) := by
  simp only [tr, satisfiesOver]
  exact False.elim

end OSLFComparison
end Mettapedia.Languages.ProcessCalculi.RhoCombinators

#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.OSLFComparison.perm_encList_of_cong
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.OSLFComparison.spatial_agrees
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.OSLFComparison.spatial_agrees_enc
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.OSLFComparison.sat_sep_comm
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.OSLFComparison.no_headed_at_enc
