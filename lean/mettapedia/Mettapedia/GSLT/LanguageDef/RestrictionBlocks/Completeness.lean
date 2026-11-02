import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.Soundness
import Mathlib.Algebra.Order.BigOperators.Group.List

/-!
# Restriction blocks are complete

Over any calculus with restriction (`BlockLanguage`), object patterns equivalent under its static theory have one
canonical form (`canon_complete`). With soundness, the static theory is decided by the canonical form on object
terms of a sort (`equationEquiv_iff_canon_eq`).

The canonical form of a block reads its components under every order of its restrictions and keeps the least
sorted reading, so it depends only on the set of readings (`least_eq_of_same`). Similar blocks (the same number of
restrictions, and components alike under one order up to a permutation) have the same readings (`readings_same`).

- Every generator of the static theory gives similar blocks (`generator_similar`): ν of inaction, exchange and
  extrusion in both orientations (inverting the scoped matcher), and the bag laws.
- Similarity is a congruence for the block structure: restriction, juxtaposition, renaming. Inside any other frame
  the components are alike, since each is a canonical form of something smaller (`component_canon`), so no
  context tells the two sides of a generator apart (`context_similar`).
- Enough fuel settles the canonical form (`fuel_settles`).

Explicit substitutions are not object-language terms; the canonical form does not look inside them, and the
completeness theorem is stated for object patterns.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars)
open Mettapedia.OSLF.MeTTaIL.PatternLexOrder (PatternLe ser serList ser_prefix)
open Prenex

variable {language : LanguageDef} {block : Block}

/-! ## Sorting forgets the order of the components -/

theorem sortComponents_pairwise (components : List Pattern) : (sortComponents components).Pairwise PatternLe :=
  List.pairwise_insertionSort _ components

/-- **Sorting forgets the order of the components.** -/
theorem sortComponents_perm {first second : List Pattern} (permutation : first.Perm second) :
    sortComponents first = sortComponents second :=
  List.Perm.eq_of_pairwise' (sortComponents_pairwise first) (sortComponents_pairwise second)
    ((List.perm_insertionSort _ first).trans (permutation.trans (List.perm_insertionSort _ second).symm))

/-- **Distinct lists of patterns have distinct serializations**, each serialization being prefix free. -/
theorem serList_injective : Function.Injective serList := by
  intro first
  induction first with
  | nil =>
      intro second same
      cases second with
      | nil => rfl
      | cons head tail => cases head <;> simp [serList, Mettapedia.OSLF.MeTTaIL.PatternLexOrder.ser] at same
  | cons head tail recurse =>
      intro second same
      cases second with
      | nil => cases head <;> simp [serList, Mettapedia.OSLF.MeTTaIL.PatternLexOrder.ser] at same
      | cons head' tail' =>
          simp only [serList] at same
          obtain ⟨heads, tails⟩ := ser_prefix head head' same
          rw [heads, recurse tails]

/-! ## The least reading is determined by the set of readings -/

/-- Keeping the better of two readings never keeps one above a reading seen. -/
theorem foldl_least_minimal : ∀ (pending : List (List Pattern)) (best : List Pattern), ∀ other ∈ best :: pending,
    ¬ serList other < serList (pending.foldl (fun best next =>
      if serList next < serList best then next else best) best)
  | [], best, other, member => by
      simp only [List.mem_singleton] at member
      subst member
      exact List.lt_irrefl _
  | next :: more, best, other, member => by
      simp only [List.foldl_cons]
      have later := foldl_least_minimal more (if serList next < serList best then next else best)
      simp only [List.mem_cons] at member
      rcases member with equal | equal | member
      · subst equal
        split_ifs at later ⊢ with better
        · exact fun below => later _ List.mem_cons_self (List.lt_trans better below)
        · exact later _ List.mem_cons_self
      · subst equal
        split_ifs at later ⊢ with better
        · exact later _ List.mem_cons_self
        · exact fun below => later _ List.mem_cons_self (List.lt_of_le_of_lt better below)
      · exact later other (List.mem_cons_of_mem _ member)

/-- **No reading is below the least one.** -/
theorem least_minimal : ∀ {candidates : List (List Pattern)}, ∀ other ∈ candidates,
    ¬ serList other < serList (least candidates)
  | first :: rest, other, member => by
      unfold least
      exact foldl_least_minimal rest first other member

/-- **The least reading is determined by the set of readings.** -/
theorem least_eq_of_same {first second : List (List Pattern)} (firstNonempty : first ≠ [])
    (secondNonempty : second ≠ []) (same : ∀ candidate, candidate ∈ first ↔ candidate ∈ second) :
    least first = least second := by
  have inSecond := (same _).mp (least_mem firstNonempty)
  have inFirst := (same _).mpr (least_mem secondNonempty)
  have codes := List.le_antisymm (least_minimal _ inFirst) (least_minimal _ inSecond)
  exact serList_injective codes

/-! ## The orders of the restrictions are all permutations -/

theorem insertions_mem {α : Type} (element : α) : ∀ (before after : List α),
    before ++ element :: after ∈ insertions element (before ++ after)
  | [], after => by cases after <;> simp [insertions]
  | first :: before, after => by
      simp only [List.cons_append, insertions, List.mem_cons, List.mem_map]
      exact Or.inr ⟨_, insertions_mem element before after, rfl⟩

theorem insertions_perm {α : Type} (element : α) : ∀ (list : List α), ∀ next ∈ insertions element list,
    next.Perm (element :: list)
  | [], next, member => by
      simp only [insertions, List.mem_singleton] at member
      rw [member]
  | first :: rest, next, member => by
      simp only [insertions, List.mem_cons, List.mem_map] at member
      rcases member with rfl | ⟨inserted, insertedMember, rfl⟩
      · exact .refl _
      · exact ((insertions_perm element rest inserted insertedMember).cons first).trans (.swap _ _ _)

/-- **Every permutation is an order.** -/
theorem orders_complete {α : Type} : ∀ (list order : List α), order.Perm list → order ∈ orders list
  | [], order, permutation => by
      rw [List.perm_nil.mp permutation]
      simp [orders]
  | first :: rest, order, permutation => by
      obtain ⟨before, after, rfl⟩ := List.append_of_mem (permutation.symm.subset List.mem_cons_self)
      have restPerm : (before ++ after).Perm rest := (List.perm_cons first).mp (List.perm_middle.symm.trans permutation)
      simp only [orders, List.mem_flatMap]
      exact ⟨before ++ after, orders_complete rest _ restPerm, insertions_mem first before after⟩

/-- Every order is a permutation. -/
theorem orders_perm {α : Type} : ∀ (list : List α), ∀ order ∈ orders list, order.Perm list
  | [], order, member => by
      simp only [orders, List.mem_singleton] at member
      rw [member]
  | first :: rest, order, member => by
      simp only [orders, List.mem_flatMap] at member
      obtain ⟨middle, middleMember, inserted⟩ := member
      exact (insertions_perm first middle order inserted).trans ((orders_perm rest middle middleMember).cons first)

/-! ## Composing orders -/

/-- Orders of a block's restrictions: permutations of `0, …, count - 1`. -/
def IsOrder (count : Nat) (order : List Nat) : Prop := order.Perm (List.range count)

theorem IsOrder.length {count : Nat} {order : List Nat} (isOrder : IsOrder count order) : order.length = count := by
  simpa using isOrder.length_eq

theorem IsOrder.lt {count : Nat} {order : List Nat} (isOrder : IsOrder count order) {index : Nat}
    (inside : index < count) : order.getD index index < count := by
  have length := isOrder.length
  rw [List.getD_eq_getElem _ _ (by omega)]
  exact List.mem_range.mp (isOrder.subset (List.getElem_mem _))

theorem permute_lt {count : Nat} {order : List Nat} (isOrder : IsOrder count order) {index : Nat}
    (inside : index < count) : Prenex.permute count order index < count := by
  simp only [Prenex.permute, if_pos inside]
  exact isOrder.lt inside

theorem permute_of_lt {count : Nat} {order : List Nat} (length : order.length = count) {index : Nat}
    (inside : index < count) : Prenex.permute count order index = order[index]'(by omega) := by
  simp only [Prenex.permute, if_pos inside, List.getD_eq_getElem _ _ (by omega : index < order.length)]

theorem permute_of_ge {count : Nat} (order : List Nat) {index : Nat} (outside : ¬ index < count) :
    Prenex.permute count order index = index := by
  simp only [Prenex.permute, if_neg outside]

/-- **Renaming by one order and then another is renaming by a third.** -/
theorem permute_comp {count : Nat} (first : List Nat) {second : List Nat} (secondOrder : IsOrder count second) :
    Prenex.permute count first ∘ Prenex.permute count second =
      Prenex.permute count (second.map (Prenex.permute count first)) := by
  funext index
  simp only [Function.comp]
  by_cases inside : index < count
  · have length := secondOrder.length
    rw [permute_of_lt length inside, permute_of_lt (by simpa using length) inside, List.getElem_map]
  · rw [permute_of_ge second inside, permute_of_ge first inside, permute_of_ge _ inside]

/-- The range read through an order is the order. -/
theorem range_map_permute {count : Nat} {order : List Nat} (isOrder : IsOrder count order) :
    (List.range count).map (Prenex.permute count order) = order := by
  apply List.ext_getElem
  · simp [isOrder.length]
  · intro index first second
    simp only [List.getElem_map, List.getElem_range, Prenex.permute]
    rw [if_pos (by simpa using first), List.getD_eq_getElem _ _ second]

/-- The composite of two orders is an order. -/
theorem IsOrder.comp {count : Nat} {first second : List Nat} (firstOrder : IsOrder count first)
    (secondOrder : IsOrder count second) : IsOrder count (second.map (Prenex.permute count first)) := by
  have mapped := (secondOrder.map (Prenex.permute count first))
  rw [range_map_permute firstOrder] at mapped
  exact mapped.trans firstOrder

/-- The order undoing an order. -/
def inverse (count : Nat) (order : List Nat) : List Nat := (List.range count).map fun index => order.idxOf index

theorem IsOrder.nodup {count : Nat} {order : List Nat} (isOrder : IsOrder count order) : order.Nodup :=
  isOrder.nodup_iff.mpr List.nodup_range

theorem IsOrder.mem {count : Nat} {order : List Nat} (isOrder : IsOrder count order) {index : Nat}
    (inside : index < count) : index ∈ order :=
  isOrder.symm.subset (List.mem_range.mpr inside)

theorem IsOrder.getElem_lt {count : Nat} {order : List Nat} (isOrder : IsOrder count order) {index : Nat}
    (inside : index < order.length) : order[index] < count :=
  List.mem_range.mp (isOrder.subset (List.getElem_mem _))

theorem inverse_isOrder {count : Nat} {order : List Nat} (isOrder : IsOrder count order) :
    IsOrder count (inverse count order) := by
  have length := isOrder.length
  unfold IsOrder inverse
  refine (List.perm_ext_iff_of_nodup ?_ List.nodup_range).mpr ?_
  · refine List.Nodup.map_on ?_ List.nodup_range
    intro first firstMember second secondMember equal
    exact (List.idxOf_inj (isOrder.mem (List.mem_range.mp firstMember))).mp equal
  · intro index
    simp only [List.mem_map, List.mem_range]
    constructor
    · rintro ⟨value, inside, rfl⟩
      exact length ▸ List.idxOf_lt_length_of_mem (isOrder.mem inside)
    · intro inside
      exact ⟨order[index]'(by omega), isOrder.getElem_lt _, isOrder.nodup.idxOf_getElem _ _⟩

/-- **Undoing an order.** -/
theorem permute_inverse {count : Nat} {order : List Nat} (isOrder : IsOrder count order) :
    Prenex.permute count (inverse count order) ∘ Prenex.permute count order = id := by
  funext index
  simp only [Function.comp, id]
  by_cases inside : index < count
  · have length := isOrder.length
    have value : Prenex.permute count order index = order[index]'(by omega) := by
      simp only [Prenex.permute, if_pos inside, List.getD_eq_getElem _ _ (by omega : index < order.length)]
    rw [value]
    have valueInside : order[index]'(by omega) < count := isOrder.getElem_lt _
    simp only [Prenex.permute, if_pos valueInside, inverse]
    rw [List.getD_eq_getElem _ _ (by simpa using valueInside)]
    simp only [List.getElem_map, List.getElem_range]
    exact isOrder.nodup.idxOf_getElem _ _
  · simp only [Prenex.permute, if_neg inside]

/-! ## Renamings -/

open Mettapedia.OSLF.MeTTaIL.ContextSubstitution (substitute lift substituteList_eq_map)
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (indexRenaming lift_renaming liftIndex FreeIn freeIn_bvar freeIn_apply
  freeIn_lambda freeIn_multiLambda freeIn_subst freeIn_collection)
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars)

theorem rename_bvar (relabel : Nat → Nat) (index : Nat) : rename relabel (.bvar index) = .bvar (relabel index) := rfl

theorem rename_fvar (relabel : Nat → Nat) (name : String) : rename relabel (.fvar name) = .fvar name := rfl

theorem rename_apply (relabel : Nat → Nat) (constructor : String) (arguments : List Pattern) :
    rename relabel (.apply constructor arguments) = .apply constructor (arguments.map (rename relabel)) := by
  simp [rename, substitute, substituteList_eq_map]

theorem rename_lambda (relabel : Nat → Nat) (binder : Option String) (body : Pattern) :
    rename relabel (.lambda binder body) = .lambda binder (rename (liftIndex 1 relabel) body) := by
  simp only [rename, substitute, lift_renaming]

theorem rename_multiLambda (relabel : Nat → Nat) (arity : Nat) (binders : List String) (body : Pattern) :
    rename relabel (.multiLambda arity binders body) = .multiLambda arity binders (rename (liftIndex arity relabel) body) := by
  simp only [rename, substitute, lift_renaming]

theorem rename_subst (relabel : Nat → Nat) (body replacement : Pattern) :
    rename relabel (.subst body replacement) =
      .subst (rename (liftIndex 1 relabel) body) (rename relabel replacement) := by
  simp only [rename, substitute, lift_renaming]

theorem rename_collection (relabel : Nat → Nat) (kind : CollType) (elements : List Pattern) (rest : Option String) :
    rename relabel (.collection kind elements rest) = .collection kind (elements.map (rename relabel)) rest := by
  simp [rename, substitute, substituteList_eq_map]

/-- Indices above a cutoff move up by a shift. -/
def shiftAbove (cutoff shift index : Nat) : Nat := if index < cutoff then index else index + shift

/-- **Lifting is a renaming.** -/
theorem liftBVars_eq_rename (cutoff shift : Nat) (pattern : Pattern) :
    liftBVars cutoff shift pattern = rename (shiftAbove cutoff shift) pattern := by
  rw [← substitute_shift shift pattern cutoff]
  show substitute (lift cutoff (indexRenaming fun index => shift + index)) pattern = _
  rw [lift_renaming]
  unfold rename
  congr 1
  funext index
  simp only [indexRenaming, liftIndex, shiftAbove]
  split_ifs
  · rfl
  · congr 1
    omega

theorem liftIndex_zero (relabel : Nat → Nat) : liftIndex 0 relabel = relabel := by
  funext index
  simp [liftIndex]

/-- **A renaming reads only the variables a pattern uses.** -/
theorem rename_congr (pattern : Pattern) : ∀ {first second : Nat → Nat},
    (∀ index, FreeIn index pattern → first index = second index) → rename first pattern = rename second pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      intro first second agree
      simp only [rename_bvar, agree index (.bvar index)]
  | hfvar name => intro _ _ _; rfl
  | happly constructor arguments recurse =>
      intro first second agree
      simp only [rename_apply]
      congr 1
      exact List.map_congr_left fun argument member =>
        recurse argument member fun index free => agree index (.apply member free)
  | hlambda binder body recurse =>
      intro first second agree
      simp only [rename_lambda]
      congr 1
      apply recurse
      intro index free
      simp only [liftIndex]
      split_ifs with below
      · rfl
      · have outer : FreeIn (index - 1) (.lambda binder body) :=
          .lambda (by rwa [show index - 1 + 1 = index by omega])
        rw [agree _ outer]
  | hmultiLambda arity binders body recurse =>
      intro first second agree
      simp only [rename_multiLambda]
      congr 1
      apply recurse
      intro index free
      simp only [liftIndex]
      split_ifs with below
      · rfl
      · have outer : FreeIn (index - arity) (.multiLambda arity binders body) :=
          .multiLambda (by rwa [show index - arity + arity = index by omega])
        rw [agree _ outer]
  | hsubst body replacement bodyRecurse replacementRecurse =>
      intro first second agree
      simp only [rename_subst]
      congr 1
      · apply bodyRecurse
        intro index free
        simp only [liftIndex]
        split_ifs with below
        · rfl
        · have outer : FreeIn (index - 1) (.subst body replacement) :=
            .substBody (by rwa [show index - 1 + 1 = index by omega])
          rw [agree _ outer]
      · exact replacementRecurse fun index free => agree index (.substReplacement free)
  | hcollection kind elements rest recurse =>
      intro first second agree
      simp only [rename_collection]
      congr 1
      exact List.map_congr_left fun element member =>
        recurse element member fun index free => agree index (.element member free)

/-- **The variables of a renamed pattern** are the renamed variables. -/
theorem freeIn_rename (pattern : Pattern) : ∀ {relabel : Nat → Nat} {index : Nat},
    FreeIn index (rename relabel pattern) ↔ ∃ original, FreeIn original pattern ∧ relabel original = index := by
  induction pattern using Pattern.inductionOn with
  | hbvar other =>
      intro relabel index
      simp only [rename_bvar, freeIn_bvar]
      constructor
      · rintro rfl; exact ⟨other, rfl, rfl⟩
      · rintro ⟨_, rfl, rfl⟩; rfl
  | hfvar name =>
      intro relabel index
      simp only [rename_fvar]
      constructor
      · rintro ⟨⟩
      · rintro ⟨_, ⟨⟩, _⟩
  | happly constructor arguments recurse =>
      intro relabel index
      simp only [rename_apply, freeIn_apply, List.mem_map]
      constructor
      · rintro ⟨_, ⟨argument, member, rfl⟩, free⟩
        obtain ⟨original, originalFree, rfl⟩ := (recurse argument member).mp free
        exact ⟨original, ⟨argument, member, originalFree⟩, rfl⟩
      · rintro ⟨original, ⟨argument, member, free⟩, rfl⟩
        exact ⟨_, ⟨argument, member, rfl⟩, (recurse argument member).mpr ⟨original, free, rfl⟩⟩
  | hlambda binder body recurse =>
      intro relabel index
      simp only [rename_lambda, freeIn_lambda, recurse]
      constructor
      · rintro ⟨original, free, equal⟩
        simp only [liftIndex] at equal
        split_ifs at equal with below
        · omega
        · exact ⟨original - 1, by rwa [show original - 1 + 1 = original by omega], by omega⟩
      · rintro ⟨original, free, rfl⟩
        exact ⟨original + 1, free, by simp [liftIndex]⟩
  | hmultiLambda arity binders body recurse =>
      intro relabel index
      simp only [rename_multiLambda, freeIn_multiLambda, recurse]
      constructor
      · rintro ⟨original, free, equal⟩
        simp only [liftIndex] at equal
        split_ifs at equal with below
        · omega
        · exact ⟨original - arity, by rwa [show original - arity + arity = original by omega], by omega⟩
      · rintro ⟨original, free, rfl⟩
        exact ⟨original + arity, free, by simp [liftIndex]⟩
  | hsubst body replacement bodyRecurse replacementRecurse =>
      intro relabel index
      simp only [rename_subst, freeIn_subst, bodyRecurse, replacementRecurse]
      constructor
      · rintro (⟨original, free, equal⟩ | ⟨original, free, rfl⟩)
        · simp only [liftIndex] at equal
          split_ifs at equal with below
          · omega
          · exact ⟨original - 1, .inl (by rwa [show original - 1 + 1 = original by omega]), by omega⟩
        · exact ⟨original, .inr free, rfl⟩
      · rintro ⟨original, free | free, rfl⟩
        · exact .inl ⟨original + 1, free, by simp [liftIndex]⟩
        · exact .inr ⟨original, free, rfl⟩
  | hcollection kind elements rest recurse =>
      intro relabel index
      simp only [rename_collection, freeIn_collection, List.mem_map]
      constructor
      · rintro ⟨_, ⟨element, member, rfl⟩, free⟩
        obtain ⟨original, originalFree, rfl⟩ := (recurse element member).mp free
        exact ⟨original, ⟨element, member, originalFree⟩, rfl⟩
      · rintro ⟨original, ⟨element, member, free⟩, rfl⟩
        exact ⟨_, ⟨element, member, rfl⟩, (recurse element member).mpr ⟨original, free, rfl⟩⟩

/-! ## Blocks under renaming -/

namespace Prenex

/-- Rename the variables a block reads from outside, past its restrictions. -/
def renameOuter (relabel : Nat → Nat) (form : Prenex) : Prenex :=
  ⟨form.count, form.components.map (rename (liftIndex form.count relabel))⟩

end Prenex

theorem nil_renameOuter (relabel : Nat → Nat) : Prenex.nil.renameOuter relabel = Prenex.nil := rfl

theorem atom_renameOuter (relabel : Nat → Nat) (component : Pattern) :
    (Prenex.atom component).renameOuter relabel = Prenex.atom (rename relabel component) := by
  simp [Prenex.renameOuter, Prenex.atom, liftIndex_zero]

theorem renameOuter_eq_nil {relabel : Nat → Nat} {form : Prenex} (isNil : form.renameOuter relabel = Prenex.nil) :
    form = Prenex.nil := by
  obtain ⟨count, components⟩ := form
  simp only [Prenex.renameOuter, Prenex.nil, Prenex.mk.injEq, List.map_eq_nil_iff] at isNil
  obtain ⟨rfl, rfl⟩ := isNil
  rfl

theorem rename_liftBVars_zero {inner outer : Nat → Nat} (shift : Nat)
    (same : ∀ index, inner (index + shift) = outer index + shift) (pattern : Pattern) :
    rename inner (liftBVars 0 shift pattern) = liftBVars 0 shift (rename outer pattern) := by
  rw [liftBVars_eq_rename, liftBVars_eq_rename, rename_comp, rename_comp]
  congr 1
  funext index
  simp only [Function.comp, shiftAbove, Nat.not_lt_zero, if_false]
  exact same index

/-- **Renaming commutes with putting blocks side by side.** -/
theorem par_renameOuter (relabel : Nat → Nat) (first second : Prenex) :
    (first.par second).renameOuter relabel = (first.renameOuter relabel).par (second.renameOuter relabel) := by
  obtain ⟨outer, firstComponents⟩ := first
  obtain ⟨inner, secondComponents⟩ := second
  simp only [Prenex.par, Prenex.renameOuter, List.map_append, List.map_map, Prenex.mk.injEq, true_and]
  congr 1
  · refine List.map_congr_left fun component _ => ?_
    simp only [Function.comp]
    rw [liftBVars_eq_rename, liftBVars_eq_rename, rename_comp, rename_comp]
    congr 1
    funext index
    simp only [Function.comp, shiftAbove, Nat.not_lt_zero, if_false, liftIndex]
    split_ifs with first second <;> try omega
    rw [show index + inner - (outer + inner) = index - outer by omega]
    omega
  · refine List.map_congr_left fun component _ => ?_
    simp only [Function.comp]
    rw [liftBVars_eq_rename, liftBVars_eq_rename, rename_comp, rename_comp]
    congr 1
    funext index
    simp only [Function.comp, shiftAbove, liftIndex]
    split_ifs <;> try omega
    rw [show index + outer - (outer + inner) = index - inner by omega]
    omega

/-- **Renaming commutes with closing a restriction**: the restriction is the variable just past the block's own,
which a renaming of the outside does not reach. -/
theorem close_renameOuter (relabel : Nat → Nat) (form : Prenex) :
    (form.renameOuter (liftIndex 1 relabel)).close = form.close.renameOuter relabel := by
  obtain ⟨count, components⟩ := form
  have lifted : liftIndex count (liftIndex 1 relabel) = liftIndex (count + 1) relabel := liftIndex_succ count relabel
  have mentionsSame : ∀ component, mentions count (rename (liftIndex (count + 1) relabel) component) =
      mentions count component := by
    intro component
    apply Bool.eq_iff_iff.mpr
    rw [mentions_iff, mentions_iff, freeIn_rename]
    constructor
    · rintro ⟨original, free, equal⟩
      simp only [liftIndex] at equal
      split_ifs at equal with below
      · rwa [← equal]
      · omega
    · intro free
      exact ⟨count, free, by simp [liftIndex]⟩
  simp only [Prenex.renameOuter, Prenex.close, lifted, List.any_map, Function.comp_def, mentionsSame]
  split_ifs with used
  · rfl
  · simp only [Prenex.mk.injEq, true_and, List.map_map]
    refine List.map_congr_left fun component member => ?_
    simp only [Function.comp]
    have unused : ¬ FreeIn count component := by
      intro free
      exact used (List.any_eq_true.mpr ⟨component, member, (mentions_iff component count).mpr free⟩)
    rw [rename_comp, rename_comp]
    apply rename_congr
    intro index free
    have different : index ≠ count := fun equal => unused (equal ▸ free)
    simp only [Function.comp, dropIndex, liftIndex]
    split_ifs <;> try omega
    rw [show index - 1 - count = index - (count + 1) by omega]
    omega

/-! ### Renamed patterns keep their outermost shape -/

theorem rename_eq_nil {relabel : Nat → Nat} {pattern : Pattern}
    (equal : rename relabel pattern = .apply block.unit []) : pattern = .apply block.unit [] := by
  cases pattern with
  | apply constructor arguments =>
      rw [rename_apply] at equal
      simp only [Pattern.apply.injEq, List.map_eq_nil_iff] at equal
      rw [equal.1, equal.2]
  | _ => simp [rename_bvar, rename_fvar, rename_lambda, rename_multiLambda, rename_subst, rename_collection] at equal

theorem rename_eq_restriction {relabel : Nat → Nat} {pattern : Pattern} {binder : Option String} {body : Pattern}
    (equal : rename relabel pattern = .apply block.restrict [.lambda binder body]) :
    ∃ binder' original, pattern = .apply block.restrict [.lambda binder' original] := by
  cases pattern with
  | apply constructor arguments =>
      rw [rename_apply] at equal
      simp only [Pattern.apply.injEq, List.map_eq_singleton_iff] at equal
      obtain ⟨rfl, argument, rfl, renamed⟩ := equal
      cases argument with
      | lambda binder' inner => exact ⟨binder', inner, rfl⟩
      | _ => simp [rename_bvar, rename_fvar, rename_apply, rename_multiLambda, rename_subst, rename_collection]
          at renamed
  | _ => simp [rename_bvar, rename_fvar, rename_lambda, rename_multiLambda, rename_subst, rename_collection] at equal

theorem rename_eq_bag {relabel : Nat → Nat} {pattern : Pattern} {elements : List Pattern}
    (equal : rename relabel pattern = .collection .hashBag elements none) :
    ∃ originals, pattern = .collection .hashBag originals none := by
  cases pattern with
  | collection kind originals rest =>
      rw [rename_collection] at equal
      simp only [Pattern.collection.injEq] at equal
      obtain ⟨rfl, -, rfl⟩ := equal
      exact ⟨originals, rfl⟩
  | _ => simp [rename_bvar, rename_fvar, rename_apply, rename_lambda, rename_multiLambda, rename_subst] at equal

mutual
  /-- **Reading the block of a renamed process** renames what the block reads from outside. -/
  theorem decompose_renameOuter (relabel : Nat → Nat) (pattern : Pattern) :
      decompose block (rename relabel pattern) = (decompose block pattern).renameOuter relabel := by
    by_cases isNil : pattern = .apply block.unit []
    · subst isNil
      rw [rename_apply, List.map_nil, decompose_unit, nil_renameOuter]
    by_cases isRestriction : ∃ binder body, pattern = .apply block.restrict [.lambda binder body]
    · obtain ⟨binder, body, rfl⟩ := isRestriction
      rw [show rename relabel (.apply block.restrict [.lambda binder body]) =
          .apply block.restrict [.lambda binder (rename (liftIndex 1 relabel) body)] by simp [rename_apply, rename_lambda],
        decompose_restrict, decompose_restrict, decompose_renameOuter (liftIndex 1 relabel) body, close_renameOuter]
    by_cases isBag : ∃ elements, pattern = .collection .hashBag elements none
    · obtain ⟨elements, rfl⟩ := isBag
      rw [rename_collection, decompose_bag, decompose_bag]
      exact decomposeList_renameOuter relabel elements
    by_cases isEmptyCandidate : ∃ label argument, pattern = .apply label [argument] ∧ label ∈ block.emptyUnits
    · obtain ⟨label, argument, rfl, listed⟩ := isEmptyCandidate
      have renamedIs : rename relabel (.apply label [argument]) = .apply label [rename relabel argument] := by
        simp [rename_apply]
      have notRestriction := fun binder body equal => isRestriction ⟨binder, body, equal⟩
      have renamedNotRestriction : ∀ binder body,
          Pattern.apply label [rename relabel argument] ≠ .apply block.restrict [.lambda binder body] := by
        intro binder body equal
        exact isRestriction (rename_eq_restriction (renamedIs.trans equal))
      rw [renamedIs, decompose_multiset notRestriction, decompose_multiset renamedNotRestriction,
        decompose_renameOuter relabel argument]
      by_cases empty : decompose block argument = Prenex.nil
      · rw [if_pos ⟨listed, by rw [empty, nil_renameOuter]⟩, if_pos ⟨listed, empty⟩, nil_renameOuter]
      · have notEmpty : ¬ (label ∈ block.emptyUnits ∧ (decompose block argument).renameOuter relabel = Prenex.nil) := by
          rintro ⟨-, renamedNil⟩
          exact empty (renameOuter_eq_nil renamedNil)
        rw [if_neg notEmpty, if_neg (fun both => empty both.2), atom_renameOuter, renamedIs]
    have renamedNotEmpty : ∀ label argument,
        rename relabel pattern = .apply label [argument] → label ∉ block.emptyUnits := by
      intro label argument equal listed
      cases pattern with
      | apply constructor arguments =>
          rw [rename_apply] at equal
          simp only [Pattern.apply.injEq, List.map_eq_singleton_iff] at equal
          obtain ⟨rfl, original, rfl, -⟩ := equal
          exact isEmptyCandidate ⟨constructor, original, rfl, listed⟩
      | _ => simp [rename_bvar, rename_fvar, rename_lambda, rename_multiLambda, rename_subst, rename_collection] at equal
    rw [decompose_atom isNil (fun binder body equal => isRestriction ⟨binder, body, equal⟩)
        (fun elements equal => isBag ⟨elements, equal⟩)
        (fun label argument equal listed => isEmptyCandidate ⟨label, argument, equal, listed⟩),
      decompose_atom (fun equal => isNil (rename_eq_nil equal))
        (fun binder body equal => isRestriction (rename_eq_restriction equal))
        (fun elements equal => isBag (rename_eq_bag equal)) renamedNotEmpty,
      atom_renameOuter]
  termination_by sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  theorem decomposeList_renameOuter (relabel : Nat → Nat) (elements : List Pattern) :
      decomposeList block (elements.map (rename relabel)) = (decomposeList block elements).renameOuter relabel := by
    match elements with
    | [] => rfl
    | element :: elements =>
        simp only [List.map_cons, decomposeList]
        rw [decompose_renameOuter relabel element, decomposeList_renameOuter relabel elements, par_renameOuter]
  termination_by sizeOf elements
  decreasing_by all_goals sizeOf_pattern_dec
end

/-! ## Readings -/

/-- The readings of a block: its sorted components with canonical parts, under every order of its restrictions. -/
def readings (block : Block) (fuel : Nat) (form : Prenex) : List (List Pattern) :=
  (orders (List.range form.count)).map fun order =>
    sortComponents (form.components.map fun component =>
      canonComponentWith block fuel (rename (Prenex.permute form.count order) component))

theorem canonWith_succ (fuel : Nat) (process : Pattern) :
    canonWith block (fuel + 1) process =
      (Prenex.toPattern block) ⟨(decompose block process).count, least (readings block fuel (decompose block process))⟩ := by
  simp only [canonWith, readings]

theorem readings_ne_nil (fuel : Nat) (form : Prenex) : readings block fuel form ≠ [] := by
  simpa [readings] using orders_ne_nil (List.range form.count)

open Mettapedia.GSLT.LanguageDef.WellSorted (isObjectPattern isObjectPatternList)

/-- Two components are alike when they use the same variables, are both object patterns or both not, and every
renaming of them has one canonical form. -/
def Alike (block : Block) (fuel : Nat) (first second : Pattern) : Prop :=
  (∀ index, FreeIn index first ↔ FreeIn index second) ∧
    isObjectPattern first = isObjectPattern second ∧
    ∀ relabel, canonComponentWith block fuel (rename relabel first) = canonComponentWith block fuel (rename relabel second)

theorem Alike.refl (fuel : Nat) (component : Pattern) : Alike block fuel component component :=
  ⟨fun _ => Iff.rfl, rfl, fun _ => rfl⟩

theorem isObjectPatternList_eq_all (patterns : List Pattern) :
    isObjectPatternList patterns = patterns.all isObjectPattern := by
  induction patterns with
  | nil => rfl
  | cons pattern patterns recurse => simp [isObjectPatternList, recurse]

/-- **A renaming keeps a pattern an object pattern**, and keeps it not one. -/
theorem isObjectPattern_rename (pattern : Pattern) : ∀ (relabel : Nat → Nat),
    isObjectPattern (rename relabel pattern) = isObjectPattern pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro _; rfl
  | hfvar name => intro _; rfl
  | happly constructor arguments recurse =>
      intro relabel
      simp only [rename_apply, isObjectPattern, isObjectPatternList_eq_all, List.all_map]
      apply Bool.eq_iff_iff.mpr
      simp only [List.all_eq_true, Function.comp]
      exact forall₂_congr fun argument member => by rw [recurse argument member relabel]
  | hlambda binder body recurse =>
      intro relabel
      simp only [rename_lambda, isObjectPattern, recurse]
  | hmultiLambda arity binders body recurse =>
      intro relabel
      simp only [rename_multiLambda, isObjectPattern, recurse]
  | hsubst body replacement _ _ =>
      intro relabel
      simp only [rename_subst, isObjectPattern]
  | hcollection kind elements rest recurse =>
      intro relabel
      simp only [rename_collection, isObjectPattern, isObjectPatternList_eq_all, List.all_map]
      congr 1
      apply Bool.eq_iff_iff.mpr
      simp only [List.all_eq_true, Function.comp]
      exact forall₂_congr fun element member => by rw [recurse element member relabel]

/-- Renaming alike components keeps them alike. -/
theorem Alike.rename {fuel : Nat} {first second : Pattern} (alike : Alike block fuel first second) (relabel : Nat → Nat) :
    Alike block fuel (rename relabel first) (rename relabel second) := by
  refine ⟨fun index => ?_, ?_, fun outer => ?_⟩
  · rw [freeIn_rename, freeIn_rename]
    exact exists_congr fun original => and_congr_left fun _ => alike.1 original
  · rw [isObjectPattern_rename, isObjectPattern_rename]
    exact alike.2.1
  · rw [rename_comp, rename_comp]
    exact alike.2.2 (outer ∘ relabel)

/-- **Similar blocks**: the same number of restrictions, and the components of one, read under some order of
the restrictions, are alike to the components of the other in some order. -/
def Similar (block : Block) (fuel : Nat) (first second : Prenex) : Prop :=
  first.count = second.count ∧ ∃ order middle, IsOrder first.count order ∧
    List.Forall₂ (Alike block fuel) (first.components.map (rename (Prenex.permute first.count order))) middle ∧
    middle.Perm second.components

theorem sort_map_forall₂ {fuel : Nat} {first second : List Pattern} (relabel : Nat → Nat)
    (related : List.Forall₂ (Alike block fuel) first second) :
    first.map (fun component => canonComponentWith block fuel (rename relabel component)) =
      second.map (fun component => canonComponentWith block fuel (rename relabel component)) := by
  induction related with
  | nil => rfl
  | cons here _ recurse => simp only [List.map_cons, here.2.2 relabel, recurse]

/-- **Similar blocks have the same readings.** -/
theorem readings_same {fuel : Nat} {first second : Prenex} (similar : Similar block fuel first second) :
    ∀ reading, reading ∈ readings block fuel first ↔ reading ∈ readings block fuel second := by
  obtain ⟨countEq, order, middle, isOrder, related, permutation⟩ := similar
  obtain ⟨count, firstComponents⟩ := first
  obtain ⟨count', secondComponents⟩ := second
  simp only at countEq isOrder related permutation
  subst countEq
  have through : ∀ (outer : List Nat),
      sortComponents (secondComponents.map fun component =>
          canonComponentWith block fuel (rename (Prenex.permute count outer) component)) =
        sortComponents (firstComponents.map fun component =>
          canonComponentWith block fuel (rename (Prenex.permute count outer ∘ Prenex.permute count order) component)) := by
    intro outer
    rw [← sortComponents_perm (permutation.map _), ← sort_map_forall₂ _ related, List.map_map]
    congr 1
    exact List.map_congr_left fun component _ => by simp only [Function.comp, rename_comp]
  intro reading
  simp only [readings, List.mem_map]
  constructor
  · rintro ⟨outer, outerMember, rfl⟩
    have outerOrder : IsOrder count outer := orders_perm _ outer outerMember
    refine ⟨(inverse count order).map (Prenex.permute count outer),
      orders_complete _ _ (outerOrder.comp (inverse_isOrder isOrder)), ?_⟩
    rw [through, ← permute_comp outer (inverse_isOrder isOrder), Function.comp_assoc, permute_inverse isOrder]
    rfl
  · rintro ⟨outer, outerMember, rfl⟩
    refine ⟨order.map (Prenex.permute count outer), orders_complete _ _ (IsOrder.comp (orders_perm _ outer outerMember) isOrder),
      ?_⟩
    rw [through, permute_comp outer isOrder]

/-- **Similar blocks have one canonical form.** -/
theorem canonWith_eq_of_similar {fuel : Nat} {first second : Pattern}
    (similar : Similar block fuel (decompose block first) (decompose block second)) :
    canonWith block (fuel + 1) first = canonWith block (fuel + 1) second := by
  rw [canonWith_succ, canonWith_succ, similar.1,
    least_eq_of_same (readings_ne_nil _ _) (readings_ne_nil _ _) (readings_same similar)]

/-- **The canonical argument of a named multiset, of an object**, is read from the same readings as the canonical
form. -/
theorem canonMultisetWith_succ_of_object (fuel : Nat) {argument : Pattern} (object : isObjectPattern argument = true) :
    canonMultisetWith block (fuel + 1) argument =
      multisetOf block ⟨(decompose block argument).count, least (readings block fuel (decompose block argument))⟩ := by
  cases argument with
  | collection kind elements rest =>
      cases rest with
      | some name => simp [isObjectPattern] at object
      | none => simp only [canonMultisetWith, readings]
  | subst body replacement => simp [isObjectPattern] at object
  | _ => simp only [canonMultisetWith, readings]

/-- **Objects with similar blocks have one canonical multiset.** -/
theorem canonMultisetWith_eq_of_similar {fuel : Nat} {first second : Pattern} (firstObject : isObjectPattern first = true)
    (secondObject : isObjectPattern second = true)
    (similar : Similar block fuel (decompose block first) (decompose block second)) :
    canonMultisetWith block (fuel + 1) first = canonMultisetWith block (fuel + 1) second := by
  rw [canonMultisetWith_succ_of_object fuel firstObject, canonMultisetWith_succ_of_object fuel secondObject, similar.1,
    least_eq_of_same (readings_ne_nil _ _) (readings_ne_nil _ _) (readings_same similar)]

/-- A block similar to inaction is inaction. -/
theorem Similar.eq_nil {fuel : Nat} {first second : Prenex} (similar : Similar block fuel first second)
    (isNil : first = Prenex.nil) : second = Prenex.nil := by
  subst isNil
  obtain ⟨countEq, order, middle, -, related, permutation⟩ := similar
  obtain ⟨count, components⟩ := second
  simp only [Prenex.nil, List.map_nil] at countEq related
  cases related
  have empty : components = [] := List.nil_perm.mp permutation
  subst countEq empty
  rfl

/-! ### Similarity is an equivalence -/

theorem Alike.symm {fuel : Nat} {first second : Pattern} (alike : Alike block fuel first second) :
    Alike block fuel second first :=
  ⟨fun index => (alike.1 index).symm, alike.2.1.symm, fun relabel => (alike.2.2 relabel).symm⟩

theorem Alike.trans {fuel : Nat} {first second third : Pattern} (alike : Alike block fuel first second)
    (alike' : Alike block fuel second third) : Alike block fuel first third :=
  ⟨fun index => (alike.1 index).trans (alike'.1 index), alike.2.1.trans alike'.2.1,
    fun relabel => (alike.2.2 relabel).trans (alike'.2.2 relabel)⟩

theorem forall₂_alike_trans {fuel : Nat} {first second third : List Pattern}
    (related : List.Forall₂ (Alike block fuel) first second) (related' : List.Forall₂ (Alike block fuel) second third) :
    List.Forall₂ (Alike block fuel) first third := by
  induction related generalizing third with
  | nil => cases related'; exact .nil
  | cons here _ recurse =>
      cases related' with
      | cons here' rest' => exact .cons (here.trans here') (recurse rest')

theorem forall₂_alike_rename {fuel : Nat} {first second : List Pattern} (relabel : Nat → Nat)
    (related : List.Forall₂ (Alike block fuel) first second) :
    List.Forall₂ (Alike block fuel) (first.map (rename relabel)) (second.map (rename relabel)) := by
  induction related with
  | nil => exact .nil
  | cons here _ recurse => exact .cons (here.rename relabel) recurse

theorem forall₂_alike_symm {fuel : Nat} {first second : List Pattern}
    (related : List.Forall₂ (Alike block fuel) first second) : List.Forall₂ (Alike block fuel) second first := by
  induction related with
  | nil => exact .nil
  | cons here _ recurse => exact .cons here.symm recurse

theorem forall₂_alike_refl (fuel : Nat) (components : List Pattern) :
    List.Forall₂ (Alike block fuel) components components :=
  List.forall₂_same.mpr fun component _ => Alike.refl fuel component

theorem map_rename_permute_range (count : Nat) (components : List Pattern) :
    components.map (rename (Prenex.permute count (List.range count))) = components := by
  rw [permute_range]
  conv_rhs => rw [← List.map_id components]
  exact List.map_congr_left fun component _ => rename_id component

theorem Similar.refl (fuel : Nat) (form : Prenex) : Similar block fuel form form :=
  ⟨rfl, List.range form.count, form.components, List.Perm.refl _,
    by rw [map_rename_permute_range]; exact forall₂_alike_refl fuel _, .refl _⟩

theorem Similar.of_eq {fuel : Nat} {first second : Prenex} (equal : first = second) : Similar block fuel first second :=
  equal ▸ Similar.refl fuel first

/-- Blocks whose components are one reordering of the restrictions and one permutation apart are similar. -/
theorem Similar.of_order {fuel : Nat} {first second : Prenex} (countEq : first.count = second.count)
    {order : List Nat} (isOrder : IsOrder first.count order)
    (permutation : (first.components.map (rename (Prenex.permute first.count order))).Perm second.components) :
    Similar block fuel first second :=
  ⟨countEq, order, _, isOrder, forall₂_alike_refl fuel _, permutation⟩

theorem Similar.trans {fuel : Nat} {first second third : Prenex} (similar : Similar block fuel first second)
    (similar' : Similar block fuel second third) : Similar block fuel first third := by
  obtain ⟨countEq, order, middle, isOrder, related, permutation⟩ := similar
  obtain ⟨countEq', order', middle', isOrder', related', permutation'⟩ := similar'
  obtain ⟨count, firstComponents⟩ := first
  obtain ⟨count₂, secondComponents⟩ := second
  obtain ⟨count₃, thirdComponents⟩ := third
  simp only at countEq countEq' isOrder isOrder' related related' permutation permutation'
  subst countEq countEq'
  have renamed := forall₂_alike_rename (Prenex.permute count order') related
  obtain ⟨rearranged, relatedRearranged, rearrangedPerm⟩ :=
    List.perm_comp_forall₂ (permutation.map (rename (Prenex.permute count order'))) related'
  refine ⟨rfl, order.map (Prenex.permute count order'), rearranged, isOrder'.comp isOrder, ?_,
    rearrangedPerm.trans permutation'⟩
  have composed : firstComponents.map (rename (Prenex.permute count (order.map (Prenex.permute count order')))) =
      (firstComponents.map (rename (Prenex.permute count order))).map (rename (Prenex.permute count order')) := by
    rw [← permute_comp order' isOrder, List.map_map]
    exact List.map_congr_left fun component _ => (rename_comp _ _ component).symm
  rw [composed]
  exact forall₂_alike_trans renamed relatedRearranged

theorem Similar.symm {fuel : Nat} {first second : Prenex} (similar : Similar block fuel first second) :
    Similar block fuel second first := by
  obtain ⟨countEq, order, middle, isOrder, related, permutation⟩ := similar
  obtain ⟨count, firstComponents⟩ := first
  obtain ⟨count', secondComponents⟩ := second
  simp only at countEq isOrder related permutation
  subst countEq
  have back : (firstComponents.map (rename (Prenex.permute count order))).map
      (rename (Prenex.permute count (inverse count order))) = firstComponents := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id firstComponents]
    refine List.map_congr_left fun component _ => ?_
    simp only [Function.comp, rename_comp, permute_inverse isOrder, rename_id, id]
  have renamed := forall₂_alike_rename (Prenex.permute count (inverse count order)) (forall₂_alike_symm related)
  rw [back] at renamed
  obtain ⟨rearranged, relatedRearranged, rearrangedPerm⟩ :=
    List.perm_comp_forall₂ (permutation.symm.map (rename (Prenex.permute count (inverse count order)))) renamed
  exact ⟨rfl, inverse count order, rearranged, inverse_isOrder isOrder, relatedRearranged, rearrangedPerm⟩

/-! ### Similarity is a congruence for blocks -/

theorem permute_eq_count {count : Nat} {order : List Nat} (isOrder : IsOrder count order) {index : Nat} :
    Prenex.permute count order index = count ↔ index = count := by
  constructor
  · intro equal
    by_cases inside : index < count
    · have := permute_lt isOrder inside
      omega
    · rwa [permute_of_ge order inside] at equal
  · rintro rfl
    exact permute_of_ge order (Nat.lt_irrefl _)

/-- An order fixes what lies past the block; the order is named so that it can be read off. -/
theorem permute_ge {count : Nat} {order : List Nat} (_isOrder : IsOrder count order) {index : Nat}
    (outside : count ≤ index) : Prenex.permute count order index = index :=
  permute_of_ge order (by omega)

theorem forall₂_partner_right {α β : Type} {relation : α → β → Prop} {first : List α} {second : List β}
    (related : List.Forall₂ relation first second) {element : α} (member : element ∈ first) :
    ∃ partner ∈ second, relation element partner := by
  induction related with
  | nil => exact absurd member (List.not_mem_nil)
  | @cons head partner _ _ here _ recurse =>
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨partner, List.mem_cons_self, here⟩
      · obtain ⟨other, otherMember, related⟩ := recurse member
        exact ⟨other, List.mem_cons_of_mem _ otherMember, related⟩

theorem forall₂_partner_left {α β : Type} {relation : α → β → Prop} {first : List α} {second : List β}
    (related : List.Forall₂ relation first second) {element : β} (member : element ∈ second) :
    ∃ partner ∈ first, relation partner element := by
  induction related with
  | nil => exact absurd member (List.not_mem_nil)
  | @cons partner head _ _ here _ recurse =>
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨partner, List.mem_cons_self, here⟩
      · obtain ⟨other, otherMember, related⟩ := recurse member
        exact ⟨other, List.mem_cons_of_mem _ otherMember, related⟩

/-- Similar blocks use the same variables past their restrictions. -/
theorem Similar.mentions_eq {fuel : Nat} {first second : Prenex} (similar : Similar block fuel first second) (index : Nat)
    (outside : first.count ≤ index) :
    first.components.any (mentions index) = second.components.any (mentions index) := by
  obtain ⟨countEq, order, middle, isOrder, related, permutation⟩ := similar
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, mentions_iff]
  have keep : ∀ component, FreeIn index (rename (Prenex.permute first.count order) component) ↔ FreeIn index component := by
    intro component
    rw [freeIn_rename]
    constructor
    · rintro ⟨original, free, equal⟩
      by_cases inside : original < first.count
      · have := permute_lt isOrder inside
        omega
      · rw [permute_of_ge order inside] at equal
        exact equal ▸ free
    · intro free
      exact ⟨index, free, permute_ge isOrder outside⟩
  have toMiddle : (∃ component ∈ first.components, FreeIn index component) ↔
      ∃ component ∈ middle, FreeIn index component := by
    constructor
    · rintro ⟨component, member, free⟩
      obtain ⟨other, otherMember, alike⟩ := forall₂_partner_right related (List.mem_map_of_mem member)
      exact ⟨other, otherMember, (alike.1 index).mp ((keep component).mpr free)⟩
    · rintro ⟨other, otherMember, free⟩
      obtain ⟨renamed, renamedMember, alike⟩ := forall₂_partner_left related otherMember
      obtain ⟨component, member, rfl⟩ := List.mem_map.mp renamedMember
      exact ⟨component, member, (keep component).mp ((alike.1 index).mpr free)⟩
  rw [toMiddle]
  exact exists_congr fun component => and_congr_left fun _ => permutation.mem_iff

/-- One more restriction keeps an order an order, fixing the new one. -/
theorem IsOrder.extend {count : Nat} {order : List Nat} (isOrder : IsOrder count order) :
    IsOrder (count + 1) (order ++ [count]) := by
  unfold IsOrder
  rw [List.range_succ]
  exact isOrder.append_right [count]

theorem permute_extend {count : Nat} {order : List Nat} (isOrder : IsOrder count order) :
    Prenex.permute (count + 1) (order ++ [count]) = Prenex.permute count order := by
  funext index
  have length := isOrder.length
  by_cases inside : index < count
  · rw [permute_of_lt (by simp [length]) (by omega), permute_of_lt length inside,
      List.getElem_append_left (by omega)]
  · rw [permute_of_ge order inside]
    by_cases top : index = count
    · subst top
      rw [permute_of_lt (by simp [length]) (by omega), List.getElem_append_right (by omega)]
      simp [length]
    · exact permute_of_ge _ (by omega)

/-- **Closing a restriction keeps blocks similar.** -/
theorem Similar.close {fuel : Nat} {first second : Prenex} (similar : Similar block fuel first second) :
    Similar block fuel first.close second.close := by
  have sameMentions := similar.mentions_eq first.count (Nat.le_refl _)
  obtain ⟨countEq, order, middle, isOrder, related, permutation⟩ := similar
  obtain ⟨count, firstComponents⟩ := first
  obtain ⟨count', secondComponents⟩ := second
  simp only at countEq isOrder related permutation sameMentions
  subst countEq
  simp only [Prenex.close, ← sameMentions]
  split_ifs with used
  · refine ⟨rfl, order ++ [count], middle, isOrder.extend, ?_, permutation⟩
    simpa [Prenex.restrict, permute_extend isOrder] using related
  · have unused : ∀ component ∈ firstComponents, ¬ FreeIn count component := by
      intro component member free
      exact used (List.any_eq_true.mpr ⟨component, member, (mentions_iff component count).mpr free⟩)
    refine ⟨rfl, order, middle.map (rename (dropIndex count)), isOrder, ?_, permutation.map _⟩
    have commute : (firstComponents.map (rename (dropIndex count))).map (rename (Prenex.permute count order)) =
        (firstComponents.map (rename (Prenex.permute count order))).map (rename (dropIndex count)) := by
      simp only [List.map_map]
      refine List.map_congr_left fun component member => ?_
      simp only [Function.comp, rename_comp]
      apply rename_congr
      intro index free
      have different : index ≠ count := fun equal => unused component member (equal ▸ free)
      simp only [Function.comp]
      by_cases inside : index < count
      · have below := permute_lt isOrder inside
        simp only [dropIndex, if_pos inside, if_pos below]
      · rw [show dropIndex count index = index - 1 by simp [dropIndex, inside], permute_ge isOrder (by omega),
          permute_ge isOrder (by omega)]
        simp [dropIndex, inside]
    simp only
    rw [commute]
    exact forall₂_alike_rename _ related

theorem forall₂_append {α β : Type} {relation : α → β → Prop} {first second : List α} {first' second' : List β}
    (related : List.Forall₂ relation first first') (related' : List.Forall₂ relation second second') :
    List.Forall₂ relation (first ++ second) (first' ++ second') := by
  induction related with
  | nil => simpa using related'
  | cons here _ recurse => exact .cons here recurse

/-- A block beside an order's block: the second block's restrictions come first, the first one's after. -/
theorem IsOrder.after {count : Nat} {order : List Nat} (isOrder : IsOrder count order) (before : Nat) :
    IsOrder (count + before) (List.range before ++ order.map (· + before)) := by
  unfold IsOrder
  rw [Nat.add_comm, List.range_add]
  refine List.Perm.append_left _ ?_
  have mapped := isOrder.map (· + before)
  simpa [Nat.add_comm] using mapped

theorem permute_after {count : Nat} {order : List Nat} (isOrder : IsOrder count order) (before : Nat) :
    Prenex.permute (count + before) (List.range before ++ order.map (· + before)) =
      fun index => if index < before then index else Prenex.permute count order (index - before) + before := by
  funext index
  have length := isOrder.length
  by_cases low : index < before
  · rw [if_pos low, permute_of_lt (by simp [length]; omega) (by omega), List.getElem_append_left (by simpa using low)]
    simp
  · rw [if_neg low]
    by_cases inside : index < count + before
    · rw [permute_of_lt (by simp [length]; omega) inside, List.getElem_append_right (by simpa using Nat.le_of_not_gt low),
        permute_of_lt length (by omega)]
      simp
    · rw [permute_of_ge _ inside, permute_of_ge order (by omega)]
      omega

/-- A renaming of a block's restrictions that keeps them in place. -/
structure Confined (count : Nat) (relabel : Nat → Nat) : Prop where
  below : ∀ index, index < count → relabel index < count
  above : ∀ index, count ≤ index → relabel index = index

theorem confined_permute {count : Nat} {order : List Nat} (isOrder : IsOrder count order) :
    Confined count (Prenex.permute count order) :=
  ⟨fun _ inside => permute_lt isOrder inside, fun _ outside => permute_ge isOrder outside⟩

theorem rename_shifted_lift {before : Nat} (relabel : Nat → Nat) :
    rename (fun index => if index < before then index else relabel (index - before) + before) ∘
        liftBVars 0 before = rename (shiftAbove 0 before) ∘ rename relabel := by
  funext component
  simp only [Function.comp, liftBVars_eq_rename, rename_comp]
  congr 1
  funext index
  simp [shiftAbove]

theorem rename_shifted_lift_other {before count : Nat} {relabel : Nat → Nat} (confined : Confined count relabel) :
    rename (fun index => if index < before then index else relabel (index - before) + before) ∘
        liftBVars before count = liftBVars before count := by
  funext component
  simp only [Function.comp, liftBVars_eq_rename, rename_comp]
  congr 1
  funext index
  simp only [Function.comp, shiftAbove]
  by_cases low : index < before
  · simp [low]
  · simp only [low, if_false]
    rw [if_neg (by omega), confined.above _ (by omega)]
    omega

theorem rename_confined_lift {count : Nat} {relabel : Nat → Nat} (confined : Confined count relabel) :
    rename relabel ∘ liftBVars 0 count = liftBVars 0 count := by
  funext component
  simp only [Function.comp, liftBVars_eq_rename, rename_comp]
  congr 1
  funext index
  simp only [Function.comp, shiftAbove, Nat.not_lt_zero, if_false]
  exact confined.above _ (by omega)

theorem rename_confined_lift_other {count shift : Nat} {relabel : Nat → Nat} (confined : Confined count relabel) :
    rename relabel ∘ liftBVars count shift = rename (shiftAbove count shift) ∘ rename relabel := by
  funext component
  simp only [Function.comp, liftBVars_eq_rename, rename_comp]
  congr 1
  funext index
  simp only [Function.comp, shiftAbove]
  by_cases inside : index < count
  · simp [inside, confined.below _ inside]
  · rw [if_neg inside, confined.above _ (by omega), confined.above _ (by omega), if_neg (by omega)]

/-- **A block beside similar blocks keeps them similar**, on either side. -/
theorem Similar.par_left {fuel : Nat} {first second : Prenex} (similar : Similar block fuel first second) (other : Prenex) :
    Similar block fuel (first.par other) (second.par other) := by
  obtain ⟨countEq, order, middle, isOrder, related, permutation⟩ := similar
  obtain ⟨count, firstComponents⟩ := first
  obtain ⟨count', secondComponents⟩ := second
  obtain ⟨others, otherComponents⟩ := other
  simp only at countEq isOrder related permutation
  subst countEq
  refine ⟨rfl, List.range others ++ order.map (· + others), middle.map (liftBVars 0 others) ++
    otherComponents.map (liftBVars others count), isOrder.after others, ?_,
    (permutation.map _).append_right _⟩
  simp only [Prenex.par, List.map_append, List.map_map]
  rw [permute_after isOrder others, rename_shifted_lift, rename_shifted_lift_other (confined_permute isOrder)]
  refine forall₂_append ?_ (forall₂_alike_refl fuel _)
  rw [show liftBVars 0 others = rename (shiftAbove 0 others) from funext (liftBVars_eq_rename 0 others),
    ← List.map_map]
  exact forall₂_alike_rename _ related

theorem Similar.par_right {fuel : Nat} {first second : Prenex} (similar : Similar block fuel first second) (other : Prenex) :
    Similar block fuel (other.par first) (other.par second) := by
  obtain ⟨countEq, order, middle, isOrder, related, permutation⟩ := similar
  obtain ⟨count, firstComponents⟩ := first
  obtain ⟨count', secondComponents⟩ := second
  obtain ⟨others, otherComponents⟩ := other
  simp only at countEq isOrder related permutation
  subst countEq
  refine ⟨rfl, order ++ (List.range others).map (· + count), otherComponents.map (liftBVars 0 count) ++
    middle.map (liftBVars count others), ?_, ?_, (permutation.map _).append_left _⟩
  · show (order ++ (List.range others).map (· + count)).Perm (List.range (others + count))
    have swapped : (List.range others).map (· + count) = (List.range others).map (count + ·) :=
      List.map_congr_left fun _ _ => Nat.add_comm _ _
    rw [Nat.add_comm others count, List.range_add, swapped]
    exact isOrder.append_right _
  · have same : Prenex.permute (others + count) (order ++ (List.range others).map (· + count)) =
        Prenex.permute count order := by
      funext index
      have length := isOrder.length
      by_cases inside : index < count
      · rw [permute_of_lt (by simp [length]; omega) (by omega), permute_of_lt length inside,
          List.getElem_append_left (by omega)]
      · rw [permute_of_ge order inside]
        by_cases within : index < others + count
        · rw [permute_of_lt (by simp [length]; omega) within, List.getElem_append_right (by omega)]
          simp [length]
          omega
        · exact permute_of_ge _ within
    simp only [Prenex.par, List.map_append, List.map_map, same]
    rw [rename_confined_lift (confined_permute isOrder), rename_confined_lift_other (confined_permute isOrder)]
    refine forall₂_append (forall₂_alike_refl fuel _) ?_
    rw [show liftBVars count others = rename (shiftAbove count others) from
      funext (liftBVars_eq_rename count others), ← List.map_map]
    exact forall₂_alike_rename _ related

/-! ## The algebra of blocks side by side -/

theorem par_nil (form : Prenex) : form.par Prenex.nil = form := by
  obtain ⟨count, components⟩ := form
  simp only [Prenex.par, Prenex.nil, Nat.add_zero, List.map_nil, List.append_nil, Prenex.mk.injEq, true_and]
  conv_rhs => rw [← List.map_id components]
  exact List.map_congr_left fun component _ => Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_zero _ _

theorem liftBVars_comp (first second : Nat → Nat) (component : Pattern) :
    rename first (rename second component) = rename (first ∘ second) component := rename_comp first second component

/-- **Blocks side by side associate.** -/
theorem par_assoc (first second third : Prenex) :
    (first.par second).par third = first.par (second.par third) := by
  obtain ⟨a, firstComponents⟩ := first
  obtain ⟨b, secondComponents⟩ := second
  obtain ⟨c, thirdComponents⟩ := third
  simp only [Prenex.par, List.map_append, List.map_map, List.append_assoc, Prenex.mk.injEq]
  refine ⟨by omega, ?_⟩
  have same : ∀ (components : List Pattern) {first second : Pattern → Pattern},
      (∀ component, first component = second component) → components.map first = components.map second :=
    fun components _ _ pointwise => List.map_congr_left fun component _ => pointwise component
  congr 1
  · refine same _ fun component => ?_
    simp only [Function.comp, liftBVars_eq_rename, rename_comp]
    congr 1
    funext index
    simp only [Function.comp, shiftAbove]
    split_ifs <;> omega
  · congr 1
    · refine same _ fun component => ?_
      simp only [Function.comp, liftBVars_eq_rename, rename_comp]
      congr 1
      funext index
      simp only [Function.comp, shiftAbove]
      split_ifs <;> omega
    · refine same _ fun component => ?_
      simp only [Function.comp, liftBVars_eq_rename, rename_comp]
      congr 1
      funext index
      simp only [Function.comp, shiftAbove]
      split_ifs <;> omega

theorem decomposeList_append : ∀ (first second : List Pattern),
    decomposeList block (first ++ second) = (decomposeList block first).par (decomposeList block second)
  | [], second => by simp [decomposeList, Prenex.nil_par]
  | element :: first, second => by
      simp only [List.cons_append, decomposeList]
      rw [decomposeList_append first second, par_assoc]

/-- The order exchanging two blocks side by side: the second block's restrictions, then the first one's. -/
def exchangeBlocks (first second : Nat) : List Nat :=
  (List.range second).map (· + first) ++ List.range first

theorem exchangeBlocks_isOrder (first second : Nat) : IsOrder (second + first) (exchangeBlocks first second) := by
  unfold IsOrder exchangeBlocks
  rw [Nat.add_comm, List.range_add]
  have swapped : (List.range second).map (· + first) = (List.range second).map (first + ·) :=
    List.map_congr_left fun _ _ => Nat.add_comm _ _
  rw [swapped]
  exact List.perm_append_comm

theorem permute_exchangeBlocks (first second : Nat) :
    Prenex.permute (second + first) (exchangeBlocks first second) =
      fun index => if index < second then index + first else if index < second + first then index - second else index := by
  funext index
  have length : (exchangeBlocks first second).length = second + first := by simp [exchangeBlocks]
  by_cases low : index < second
  · rw [if_pos low, permute_of_lt length (by omega)]
    simp [exchangeBlocks, low]
  · rw [if_neg low]
    by_cases inside : index < second + first
    · rw [if_pos inside, permute_of_lt length inside]
      simp [exchangeBlocks, List.getElem_append, low]
    · rw [if_neg inside, permute_of_ge _ inside]

/-- **Blocks side by side commute**, up to the order of their restrictions. -/
theorem par_comm_similar (fuel : Nat) (first second : Prenex) : Similar block fuel (first.par second) (second.par first) := by
  obtain ⟨a, firstComponents⟩ := first
  obtain ⟨b, secondComponents⟩ := second
  refine Similar.of_order (by simp [Prenex.par]; omega) (order := exchangeBlocks a b) ?_ ?_
  · simpa [Prenex.par, Nat.add_comm] using exchangeBlocks_isOrder a b
  · have permuted : Prenex.permute (Prenex.par ⟨a, firstComponents⟩ ⟨b, secondComponents⟩).count (exchangeBlocks a b) =
        Prenex.permute (b + a) (exchangeBlocks a b) := by simp [Prenex.par, Nat.add_comm]
    rw [permuted, permute_exchangeBlocks]
    simp only [Prenex.par, List.map_append, List.map_map]
    have firstPart : (rename (fun index => if index < b then index + a else if index < b + a then index - b else index) ∘
        liftBVars 0 b) = liftBVars a b := by
      funext component
      simp only [Function.comp, liftBVars_eq_rename, rename_comp]
      congr 1
      funext index
      simp only [Function.comp, shiftAbove]
      split_ifs <;> omega
    have secondPart : (rename (fun index => if index < b then index + a else if index < b + a then index - b else index) ∘
        liftBVars b a) = liftBVars 0 a := by
      funext component
      simp only [Function.comp, liftBVars_eq_rename, rename_comp]
      congr 1
      funext index
      simp only [Function.comp, shiftAbove]
      split_ifs <;> omega
    rw [firstPart, secondPart]
    exact List.perm_append_comm

/-! ## The laws on blocks -/

theorem liftIndex_shiftAbove_zero (cutoff shift : Nat) :
    liftIndex cutoff (shiftAbove 0 shift) = shiftAbove cutoff shift := by
  funext index
  simp only [liftIndex, shiftAbove, Nat.not_lt_zero, if_false]
  split_ifs <;> omega

theorem mentions_liftBVars_zero (index shift : Nat) (component : Pattern) :
    mentions (index + shift) (liftBVars 0 shift component) = mentions index component := by
  apply Bool.eq_iff_iff.mpr
  rw [mentions_iff, mentions_iff, liftBVars_eq_rename, freeIn_rename]
  constructor
  · rintro ⟨original, free, equal⟩
    simp only [shiftAbove, Nat.not_lt_zero, if_false] at equal
    rwa [show index = original by omega]
  · intro free
    exact ⟨index, free, by simp [shiftAbove]⟩

/-- **Scope extrusion on blocks**: a restriction closed over one block and then set beside another is the
restriction closed over both, the other block lifted past it. -/
theorem extrusion_block (first other : Prenex) :
    first.close.par other = (first.par (other.renameOuter (shiftAbove 0 1))).close := by
  obtain ⟨count, components⟩ := first
  obtain ⟨others, otherComponents⟩ := other
  have otherFree : ∀ component, mentions (count + others)
      (liftBVars others count (rename (shiftAbove others 1) component)) = false := by
    intro component
    apply Bool.eq_false_iff.mpr
    rw [Ne, mentions_iff, liftBVars_eq_rename, rename_comp, freeIn_rename]
    rintro ⟨original, _, equal⟩
    simp only [Function.comp, shiftAbove] at equal
    split_ifs at equal <;> omega
  have test : ((components.map (liftBVars 0 others)) ++
      (otherComponents.map (rename (shiftAbove others 1))).map (liftBVars others count)).any (mentions (count + others)) =
      components.any (mentions count) := by
    simp [List.any_append, List.any_map, Function.comp_def, mentions_liftBVars_zero, otherFree]
  simp only [Prenex.renameOuter, liftIndex_shiftAbove_zero, Prenex.close, Prenex.par, test]
  split_ifs with used
  · simp only [Prenex.restrict, Prenex.mk.injEq, List.map_map]
    refine ⟨by omega, ?_⟩
    congr 1
    refine List.map_congr_left fun component _ => ?_
    simp only [Function.comp, liftBVars_eq_rename, rename_comp]
    congr 1
    funext index
    simp only [Function.comp, shiftAbove]
    split_ifs <;> omega
  · have unused : ∀ component ∈ components, ¬ FreeIn count component := by
      intro component member free
      exact used (List.any_eq_true.mpr ⟨component, member, (mentions_iff component count).mpr free⟩)
    simp only [Prenex.mk.injEq, true_and, List.map_append, List.map_map]
    congr 1
    · refine List.map_congr_left fun component member => ?_
      simp only [Function.comp, liftBVars_eq_rename, rename_comp]
      apply rename_congr
      intro index free
      have different : index ≠ count := fun equal => unused component member (equal ▸ free)
      simp only [Function.comp, shiftAbove, dropIndex, Nat.not_lt_zero, if_false]
      split_ifs <;> omega
    · refine List.map_congr_left fun component _ => ?_
      simp only [Function.comp, liftBVars_eq_rename, rename_comp]
      congr 1
      funext index
      simp only [Function.comp, shiftAbove, dropIndex]
      split_ifs <;> omega

theorem close_of_used {form : Prenex} (used : form.components.any (mentions form.count) = true) :
    form.close = form.restrict := by
  simp [Prenex.close, used]

theorem close_of_unused {form : Prenex} (unused : form.components.any (mentions form.count) = false) :
    form.close = ⟨form.count, form.components.map (rename (dropIndex form.count))⟩ := by
  simp [Prenex.close, unused]

theorem unused_of_any {index : Nat} {components : List Pattern} (unused : components.any (mentions index) = false) :
    ∀ component ∈ components, ¬ FreeIn index component := by
  intro component member free
  have := List.any_eq_false.mp unused component member
  rw [(mentions_iff component index).mpr free] at this
  exact absurd rfl this

theorem any_mentions_rename {index : Nat} {relabel : Nat → Nat} {components : List Pattern} {target : Nat}
    (preimage : ∀ component ∈ components, ∀ original, FreeIn original component →
      (relabel original = index ↔ original = target)) :
    (components.map (rename relabel)).any (mentions index) = components.any (mentions target) := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_map, List.any_eq_true, Function.comp, mentions_iff, freeIn_rename]
  constructor
  · rintro ⟨component, member, original, free, equal⟩
    exact ⟨component, member, ((preimage component member original free).mp equal) ▸ free⟩
  · rintro ⟨component, member, free⟩
    exact ⟨component, member, target, free, (preimage component member target free).mpr rfl⟩

theorem swapAt_eq_iff (position index target : Nat) (isTarget : target = position ∨ target = position + 1) :
    swapAt position index = target ↔ index = (if target = position then position + 1 else position) := by
  simp only [swapAt]
  rcases isTarget with rfl | rfl <;> split_ifs <;> omega

/-- **Exchanging two restrictions on blocks**: the two closed blocks are similar, by exchanging the two
restrictions when both are used, and equal otherwise. -/
theorem exchange_block (fuel : Nat) (form : Prenex) :
    Similar block fuel form.close.close (form.renameOuter swapInner).close.close := by
  obtain ⟨count, components⟩ := form
  simp only [Prenex.renameOuter, liftIndex_swapInner]
  have swapInner' : (components.map (rename (swapAt count))).any (mentions count) =
      components.any (mentions (count + 1)) :=
    any_mentions_rename fun _ _ original _ => by simp only [swapAt]; split_ifs <;> omega
  have swapOuter' : (components.map (rename (swapAt count))).any (mentions (count + 1)) =
      components.any (mentions count) :=
    any_mentions_rename fun _ _ original _ => by simp only [swapAt]; split_ifs <;> omega
  by_cases inner : components.any (mentions count) = true <;>
    by_cases outer : components.any (mentions (count + 1)) = true
  · -- both restrictions are used: exchange them
    rw [close_of_used (form := ⟨count, components⟩) inner,
      close_of_used (form := Prenex.restrict ⟨count, components⟩) outer,
      close_of_used (form := ⟨count, components.map (rename (swapAt count))⟩) (swapInner'.trans outer),
      close_of_used (form := Prenex.restrict ⟨count, components.map (rename (swapAt count))⟩)
        (swapOuter'.trans inner)]
    refine Similar.of_order rfl (order := List.range count ++ [count + 1, count]) ?_ ?_
    · show (List.range count ++ [count + 1, count]).Perm (List.range (count + 2))
      rw [show count + 2 = count + 1 + 1 by omega, List.range_succ, List.range_succ, List.append_assoc]
      exact List.Perm.append_left _ (.swap _ _ _)
    · have same : Prenex.permute (count + 1 + 1) (List.range count ++ [count + 1, count]) = swapAt count := by
        funext index
        have length : (List.range count ++ [count + 1, count]).length = count + 1 + 1 := by simp
        by_cases inside : index < count + 1 + 1
        · rw [permute_of_lt length inside]
          by_cases low : index < count
          · have value : (List.range count ++ [count + 1, count])[index]'(by simp; omega) = index := by
              rw [List.getElem_append_left (by simpa using low)]
              simp
            rw [value]
            simp only [swapAt]
            split_ifs <;> omega
          · have : index = count ∨ index = count + 1 := by omega
            rcases this with rfl | rfl <;> simp [swapAt]
        · rw [permute_of_ge _ inside]
          simp only [swapAt]
          split_ifs <;> omega
      simp only [Prenex.restrict, same]
      exact .refl _
  · -- the inner restriction is used, the outer one is garbage
    have outer' : components.any (mentions (count + 1)) = false := by simpa using outer
    have swappedInner : (components.map (rename (swapAt count))).any (mentions count) = false :=
      swapInner'.trans outer'
    have unusedOuter := unused_of_any outer'
    have unusedSwapped := unused_of_any swappedInner
    have dropped : ((components.map (rename (swapAt count))).map (rename (dropIndex count))).any (mentions count) =
        true := by
      rw [any_mentions_rename (target := count + 1) fun component member original free => by
        have different : original ≠ count := fun equal => unusedSwapped component member (equal ▸ free)
        simp only [dropIndex]
        split_ifs <;> omega]
      exact swapOuter'.trans inner
    rw [close_of_used (form := ⟨count, components⟩) inner,
      close_of_unused (form := Prenex.restrict ⟨count, components⟩) outer',
      close_of_unused (form := ⟨count, components.map (rename (swapAt count))⟩) swappedInner,
      close_of_used (form := ⟨count, (components.map (rename (swapAt count))).map (rename (dropIndex count))⟩)
        dropped]
    refine Similar.of_eq ?_
    simp only [Prenex.restrict, List.map_map, Prenex.mk.injEq, true_and]
    refine List.map_congr_left fun component member => ?_
    simp only [Function.comp, rename_comp]
    apply rename_congr
    intro index free
    have different : index ≠ count + 1 := fun equal => unusedOuter component member (equal ▸ free)
    simp only [Function.comp, dropIndex, swapAt]
    split_ifs <;> omega
  · -- the inner restriction is garbage, the outer one is used
    have inner' : components.any (mentions count) = false := by simpa using inner
    have swappedOuter : (components.map (rename (swapAt count))).any (mentions (count + 1)) = false :=
      swapOuter'.trans inner'
    have unusedInner := unused_of_any inner'
    have dropped : (components.map (rename (dropIndex count))).any (mentions count) = true := by
      rw [any_mentions_rename (target := count + 1) fun component member original free => by
        have different : original ≠ count := fun equal => unusedInner component member (equal ▸ free)
        simp only [dropIndex]
        split_ifs <;> omega]
      exact outer
    rw [close_of_unused (form := ⟨count, components⟩) inner',
      close_of_used (form := ⟨count, components.map (rename (dropIndex count))⟩) dropped,
      close_of_used (form := ⟨count, components.map (rename (swapAt count))⟩) (swapInner'.trans outer),
      close_of_unused (form := Prenex.restrict ⟨count, components.map (rename (swapAt count))⟩) swappedOuter]
    refine Similar.of_eq ?_
    simp only [Prenex.restrict, List.map_map, Prenex.mk.injEq, true_and]
    refine List.map_congr_left fun component member => ?_
    simp only [Function.comp, rename_comp]
    apply rename_congr
    intro index free
    have different : index ≠ count := fun equal => unusedInner component member (equal ▸ free)
    simp only [Function.comp, dropIndex, swapAt]
    split_ifs <;> omega
  · -- both restrictions are garbage
    have inner' : components.any (mentions count) = false := by simpa using inner
    have outer' : components.any (mentions (count + 1)) = false := by simpa using outer
    have unusedInner := unused_of_any inner'
    have unusedOuter := unused_of_any outer'
    have swappedInner : (components.map (rename (swapAt count))).any (mentions count) = false :=
      swapInner'.trans outer'
    have unusedSwapped := unused_of_any swappedInner
    have dropped : (components.map (rename (dropIndex count))).any (mentions count) = false := by
      rw [any_mentions_rename (target := count + 1) fun component member original free => by
        have different : original ≠ count := fun equal => unusedInner component member (equal ▸ free)
        simp only [dropIndex]
        split_ifs <;> omega]
      exact outer'
    have droppedSwapped :
        ((components.map (rename (swapAt count))).map (rename (dropIndex count))).any (mentions count) = false := by
      rw [any_mentions_rename (target := count + 1) fun component member original free => by
        have different : original ≠ count := fun equal => unusedSwapped component member (equal ▸ free)
        simp only [dropIndex]
        split_ifs <;> omega]
      exact swapOuter'.trans inner'
    rw [close_of_unused (form := ⟨count, components⟩) inner',
      close_of_unused (form := ⟨count, components.map (rename (dropIndex count))⟩) dropped,
      close_of_unused (form := ⟨count, components.map (rename (swapAt count))⟩) swappedInner,
      close_of_unused (form := ⟨count, (components.map (rename (swapAt count))).map (rename (dropIndex count))⟩)
        droppedSwapped]
    refine Similar.of_eq ?_
    simp only [List.map_map, Prenex.mk.injEq, true_and]
    refine List.map_congr_left fun component member => ?_
    simp only [Function.comp, rename_comp]
    apply rename_congr
    intro index free
    have different : index ≠ count := fun equal => unusedInner component member (equal ▸ free)
    have different' : index ≠ count + 1 := fun equal => unusedOuter component member (equal ▸ free)
    simp only [Function.comp, dropIndex, swapAt]
    split_ifs <;> omega

/-! ## The generators of the static theory on blocks -/

variable [laws : BlockLanguage language block]

open Mettapedia.GSLT.LanguageDef.EquationSemantics (DerivedInstance AlgebraRule readsRaw)
open Mettapedia.GSLT.LanguageDef.WellSorted (CollectionTypedAt)

/-- **Permuting the members of a bag** gives similar blocks. -/
theorem decomposeList_perm_similar (fuel : Nat) {first second : List Pattern} (permutation : first.Perm second) :
    Similar block fuel (decomposeList block first) (decomposeList block second) := by
  induction permutation with
  | nil => exact .refl _ _
  | cons element _ recurse => exact recurse.par_right _
  | swap first second rest =>
      simp only [decomposeList]
      rw [← par_assoc, ← par_assoc]
      exact (par_comm_similar fuel _ _).par_left _
  | trans _ _ first second => exact first.trans second

/-- **The bag laws on blocks**: a permutation gives similar blocks, the other laws equal ones. -/
theorem derived_similar (fuel : Nat) {source target : Pattern} (derived : DerivedInstance language source target) :
    Similar block fuel (decompose block source) (decompose block target) := by
  cases derived with
  | bagPerm _ _ permutation =>
      rw [decompose_bag, decompose_bag]
      exact decomposeList_perm_similar fuel permutation
  | setPerm member typed => exact absurd typed (laws.no_set_rule member)
  | setDedup member typed => exact absurd typed (laws.no_set_rule member)
  | @flatten rule kind algebra pre inner post algebraRule _ _ =>
      obtain ⟨rfl, _⟩ := laws.algebra_shape algebraRule
      refine Similar.of_eq ?_
      rw [decompose_bag, decompose_bag, decomposeList_append, decomposeList_append, decomposeList_append,
        decomposeList, decompose_bag, par_assoc]
  | @singleton rule kind algebra element algebraRule _ _ =>
      obtain ⟨rfl, _⟩ := laws.algebra_shape algebraRule
      refine Similar.of_eq ?_
      rw [decompose_bag]
      exact par_nil _
  | @unitElim rule kind algebra unit pre post algebraRule unitIs _ =>
      obtain ⟨rfl, named⟩ := laws.algebra_shape algebraRule
      rw [unitIs, Option.some.injEq] at named
      subst named
      refine Similar.of_eq ?_
      rw [decompose_bag, decompose_bag, decomposeList_append, decomposeList_append, decomposeList, decompose_unit,
        Prenex.nil_par]
  | @emptyUnit rule kind algebra unit algebraRule unitIs _ =>
      obtain ⟨rfl, named⟩ := laws.algebra_shape algebraRule
      rw [unitIs, Option.some.injEq] at named
      subst named
      exact Similar.of_eq (by rw [decompose_bag, decompose_unit]; rfl)

/-- `(νx) 0` and `0` have one block. -/
theorem restrictionNil_block : decompose block (.apply block.restrict [.lambda none (.apply block.unit [])]) =
    decompose block (.apply block.unit []) := by
  simp [decompose, Prenex.close, Prenex.nil]

/-! ## The declared laws on blocks -/

open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.OSLF.MeTTaIL.RuleBinding (ContextualValue recoverValue? instantiateValue? arguments?
  dependencies? occurrenceDeclared sitePattern? occurrenceAt?)
open Mettapedia.OSLF.MeTTaIL.ScopedPattern (isWellScopedListAt_eq_true_iff)
open Mettapedia.OSLF.MeTTaIL.ScopedEquationExecution (Orientation orientedRule)
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVarsList_eq_map)

theorem perm_getElem_eraseIdx {α : Type} : ∀ (list : List α) (index : Nat) (inside : index < list.length),
    list.Perm (list[index] :: list.eraseIdx index)
  | [], _, inside => absurd inside (by simp)
  | head :: tail, 0, _ => by simp
  | head :: tail, index + 1, inside => by
      simp only [List.getElem_cons_succ, List.eraseIdx_cons_succ]
      exact ((perm_getElem_eraseIdx tail index (by simpa using inside)).cons head).trans (.swap _ _ _)

/-- **Every forward instance of scope extrusion**: a bag with a restriction among its members becomes the restriction
over the bag of the restricted body and the other members, lifted past it. -/
theorem extrusion_forward_shape {ambient : Nat} {spec : RuleBindingSpec} {captured : Assignment}
    {source target : Pattern} (bound : (orientedRule (scopeExtrusionOf block) .forward).bindings = some spec)
    (sourceScoped : source.isWellScopedAt ambient = true)
    (matched : captured ∈ matchRuleAt (orientedRule (scopeExtrusionOf block) .forward) spec ambient source)
    (applied : reduct? (orientedRule (scopeExtrusionOf block) .forward) spec ambient captured = some target) :
    ∃ (members : List Pattern) (selected : Nat) (binder : Option String) (body : Pattern)
      (inside : selected < members.length), members[selected] = .apply block.restrict [.lambda binder body] ∧
      source = .collection .hashBag members none ∧
      target = .apply block.restrict [.lambda none (.collection .hashBag
        (body :: (members.eraseIdx selected).map (liftBVars 0 1)) none)] := by
  obtain rfl : spec = (orientedRule (scopeExtrusionOf block) .forward).bindings.getD { dependencies := [] } := by
    rw [bound]; rfl
  simp only [matchRuleAt, matchRuleWithAt] at matched
  rw [show (orientedRule (scopeExtrusionOf block) .forward).left =
      .collection .hashBag [.apply block.restrict [.lambda none (.fvar "P")]] (some "rest") from rfl,
    mem_matchAtWith_bag] at matched
  obtain ⟨members, rfl, matched⟩ := matched
  rw [mem_matchBagAtWith_cons] at matched
  obtain ⟨element, selected, zipped, middle, first, matched⟩ := matched
  rw [mem_matchBagAtWith_rest] at matched
  rw [mem_matchAtWith_apply] at first
  obtain ⟨arguments, rfl, first⟩ := first
  rw [mem_matchArgsAtWith_cons] at first
  obtain ⟨argument, rest, afterArgument, rfl, binderMatched, first⟩ := first
  rw [mem_matchArgsAtWith_nil] at first
  obtain ⟨rfl, rfl⟩ := first
  rw [mem_matchAtWith_lambda] at binderMatched
  obtain ⟨binder, body, rfl, binderMatched⟩ := binderMatched
  obtain ⟨inside, chosen⟩ := List.mem_zipIdx' zipped
  have membersScoped : Pattern.isWellScopedListAt ambient members = true := by
    simpa [Pattern.isWellScopedAt] using sourceScoped
  have elementScoped : (Pattern.apply block.restrict [.lambda binder body]).isWellScopedAt ambient = true := by
    rw [chosen]
    exact ((isWellScopedListAt_eq_true_iff _ _).mp membersScoped) _ (List.getElem_mem _)
  have bodyScoped : body.isWellScopedAt (1 + ambient) = true := by
    simpa [Pattern.isWellScopedAt, Pattern.isWellScopedListAt, Nat.add_comm] using elementScoped
  have othersScoped : (Pattern.collection .hashBag (members.eraseIdx selected) none).isWellScopedAt ambient =
      true := by
    simp only [Pattern.isWellScopedAt]
    exact (isWellScopedListAt_eq_true_iff _ _).mpr fun other member =>
      ((isWellScopedListAt_eq_true_iff _ _).mp membersScoped) _ (List.mem_of_mem_eraseIdx member)
  rw [mem_matchAtWith_fvar, captureWith?_literal] at binderMatched
  simp [capture?, orientedRule, scopeExtrusionOf, dependencies?, arguments?, occurrenceDeclared, sitePattern?,
    occurrenceAt?, recoverValue?_one bodyScoped, assign, lookup] at binderMatched
  subst binderMatched
  simp [captureRestWith?_literal, captureRest?, capture?, orientedRule, scopeExtrusionOf, dependencies?, arguments?,
    occurrenceDeclared, sitePattern?, occurrenceAt?, recoverValue?_zero othersScoped, assign, lookup] at matched
  subst matched
  simp [reduct?, instantiateAt?, instantiateWith?, instantiateArgsWith?, orientedRule, scopeExtrusionOf,
    arguments?, dependencies?, occurrenceDeclared, sitePattern?, occurrenceAt?, lookup,
    instantiateValue?_one bodyScoped, instantiateValue?_shift othersScoped, liftBVars, liftBVarsList_eq_map]
    at applied
  subst applied
  exact ⟨members, selected, binder, body, inside, chosen.symm, rfl, rfl⟩

/-- **Forward scope extrusion on blocks** gives similar blocks. -/
theorem extrusion_forward_similar (fuel : Nat) {ambient : Nat} {spec : RuleBindingSpec} {captured : Assignment}
    {source target : Pattern} (bound : (orientedRule (scopeExtrusionOf block) .forward).bindings = some spec)
    (sourceScoped : source.isWellScopedAt ambient = true)
    (matched : captured ∈ matchRuleAt (orientedRule (scopeExtrusionOf block) .forward) spec ambient source)
    (applied : reduct? (orientedRule (scopeExtrusionOf block) .forward) spec ambient captured = some target) :
    Similar block fuel (decompose block source) (decompose block target) := by
  obtain ⟨members, selected, binder, body, inside, chosen, rfl, rfl⟩ :=
    extrusion_forward_shape bound sourceScoped matched applied
  rw [decompose_bag, decompose_restrict, decompose_bag]
  refine (decomposeList_perm_similar fuel (perm_getElem_eraseIdx members selected inside)).trans
    (Similar.of_eq ?_)
  rw [chosen, decomposeList, decompose_restrict, extrusion_block, decomposeList, ← decomposeList_renameOuter]
  congr 3
  exact List.map_congr_left fun other _ => (liftBVars_eq_rename 0 1 other).symm

/-! ### Scope through free indices, and the recoveries of the declared laws -/

open Mettapedia.OSLF.MeTTaIL.RuleBinding (recoveryAssignment occurrenceAssignment variableSpine? recoverValue?_forward
  recoverValue?_context)
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (FreeIn.lt_of_scoped)

/-- **A pattern is scoped where its free indices are.** -/
theorem scoped_of_freeIn (pattern : Pattern) : ∀ {depth : Nat}, (∀ index, FreeIn index pattern → index < depth) →
    pattern.isWellScopedAt depth = true := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      intro depth below
      simpa [Pattern.isWellScopedAt] using below index (.bvar index)
  | hfvar name => intro _ _; simp [Pattern.isWellScopedAt]
  | happly constructor arguments recurse =>
      intro depth below
      simp only [Pattern.isWellScopedAt]
      exact (isWellScopedListAt_eq_true_iff _ _).mpr fun argument member =>
        recurse argument member fun index free => below index (.apply member free)
  | hlambda binder body recurse =>
      intro depth below
      simp only [Pattern.isWellScopedAt]
      apply recurse
      intro index free
      cases index with
      | zero => omega
      | succ index =>
          have := below index (.lambda free)
          omega
  | hmultiLambda arity binders body recurse =>
      intro depth below
      simp only [Pattern.isWellScopedAt]
      apply recurse
      intro index free
      by_cases low : index < arity
      · omega
      · have := below (index - arity) (.multiLambda (by rwa [show index - arity + arity = index by omega]))
        omega
  | hsubst body replacement bodyRecurse replacementRecurse =>
      intro depth below
      simp only [Pattern.isWellScopedAt, Bool.and_eq_true]
      refine ⟨bodyRecurse fun index free => ?_, replacementRecurse fun index free => below index (.substReplacement free)⟩
      cases index with
      | zero => omega
      | succ index =>
          have := below index (.substBody free)
          omega
  | hcollection kind elements rest recurse =>
      intro depth below
      simp only [Pattern.isWellScopedAt]
      exact (isWellScopedListAt_eq_true_iff _ _).mpr fun element member =>
        recurse element member fun index free => below index (.element member free)

theorem rename_scoped {relabel : Nat → Nat} {pattern : Pattern} {depth : Nat}
    (inside : ∀ index, FreeIn index pattern → relabel index < depth) : (rename relabel pattern).isWellScopedAt depth = true :=
  scoped_of_freeIn _ fun index free => by
    obtain ⟨original, originalFree, rfl⟩ := (freeIn_rename pattern).mp free
    exact inside original originalFree

theorem swapInner_swapInner (index : Nat) : swapInner (swapInner index) = index := by
  rcases index with _ | _ | index <;> simp [swapInner]

theorem rename_swapInner_swapInner (pattern : Pattern) : rename swapInner (rename swapInner pattern) = pattern := by
  rw [rename_comp]
  conv_rhs => rw [← rename_id pattern]
  congr 1
  funext index
  exact swapInner_swapInner index

theorem swapped_scoped {body : Pattern} {depth : Nat} (wellScoped : body.isWellScopedAt (2 + depth) = true) :
    (rename swapInner body).isWellScopedAt (2 + depth) = true :=
  rename_scoped fun index free => by
    have := FreeIn.lt_of_scoped free wellScoped
    simp only [swapInner]
    split_ifs <;> omega

theorem recovery_swap (ambient : Nat) :
    recoveryAssignment 2 2 ambient [1, 0] = fun index => Pattern.bvar (swapInner index) := by
  funext index
  by_cases inside : index < 2
  · rcases (by omega : index = 0 ∨ index = 1) with rfl | rfl <;> simp [recoveryAssignment, swapInner]
  · have recovered : 2 + (index - 2) = index := by omega
    have notZero : index ≠ 0 := by omega
    have notOne : index ≠ 1 := by omega
    simp [recoveryAssignment, inside, recovered, swapInner, notZero, notOne]

/-- A body under two binders, read through the exchanged spine, is recovered exchanged. -/
theorem recoverValue?_swap {first second : TypeExpr} {ambient : Nat} {body : Pattern}
    (wellScoped : body.isWellScopedAt (2 + ambient) = true) :
    recoverValue? [first, second] ambient 2 [.bvar 1, .bvar 0] body =
      some ⟨[first, second], ambient, rename swapInner body⟩ := by
  have inside : 1 < 2 + ambient := by omega
  have swappedScoped := swapped_scoped wellScoped
  have back : substitute (fun index => Pattern.bvar (swapInner index)) (rename swapInner body) = body :=
    rename_swapInner_swapInner body
  have swapped : substitute (fun index => Pattern.bvar (swapInner index)) body = rename swapInner body := rfl
  simp [recoverValue?, wellScoped, variableSpine?, recovery_swap, instantiateValue?, occurrence_swap,
    Pattern.isWellScopedAt, inside, swappedScoped, back, swapped]

theorem instantiateValue?_swap {first second : TypeExpr} {ambient : Nat} {body : Pattern}
    (wellScoped : body.isWellScopedAt (2 + ambient) = true) :
    instantiateValue? ⟨[first, second], ambient, body⟩ ambient 2 [.bvar 1, .bvar 0] = some (rename swapInner body) := by
  have inside : 1 < 2 + ambient := by omega
  have swappedScoped := swapped_scoped wellScoped
  have swapped : substitute (fun index => Pattern.bvar (swapInner index)) body = rename swapInner body := rfl
  simp [instantiateValue?, occurrence_swap, Pattern.isWellScopedAt, inside, wellScoped, swappedScoped, swapped]

theorem instantiateValue?_two {first second : TypeExpr} {ambient : Nat} {body : Pattern}
    (wellScoped : body.isWellScopedAt (2 + ambient) = true) :
    instantiateValue? ⟨[first, second], ambient, body⟩ ambient 2 [.bvar 0, .bvar 1] = some body := by
  have inside : 1 < 2 + ambient := by omega
  simp [instantiateValue?, occurrence_two, Pattern.isWellScopedAt, inside, wellScoped,
    Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute_id]

theorem instantiateValue?_root {ambient : Nat} {body : Pattern} (wellScoped : body.isWellScopedAt ambient = true) :
    instantiateValue? ⟨[], ambient, body⟩ ambient 0 [] = some body := by
  simp [instantiateValue?, occurrence_zero, wellScoped, Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute_id]

/-- A value read one binder deeper is lifted. -/
theorem instantiateValue?_shift_inv {ambient : Nat} {body result : Pattern}
    (instantiated : instantiateValue? ⟨[], ambient, body⟩ ambient 1 [] = some result) :
    body.isWellScopedAt ambient = true ∧ result = liftBVars 0 1 body := by
  by_cases wellScoped : body.isWellScopedAt ambient = true
  · rw [instantiateValue?_shift wellScoped, Option.some.injEq] at instantiated
    exact ⟨wellScoped, instantiated.symm⟩
  · simp [instantiateValue?, wellScoped] at instantiated

open Mettapedia.OSLF.MeTTaIL.ScopedEquationExecution (exchangeBindings exchangeOccurrence exchangeSite)

/-- A lifted pattern that is a collection lifts a collection. -/
theorem liftBVars_eq_collection {cutoff shift : Nat} {pattern : Pattern} {kind : CollType} {elements : List Pattern}
    {rest : Option String} (equal : liftBVars cutoff shift pattern = .collection kind elements rest) :
    ∃ originals, pattern = .collection kind originals rest ∧ elements = originals.map (liftBVars cutoff shift) := by
  cases pattern with
  | collection kind' originals rest' =>
      simp only [liftBVars, liftBVarsList_eq_map, Pattern.collection.injEq] at equal
      obtain ⟨rfl, rfl, rfl⟩ := equal
      exact ⟨originals, rfl, rfl⟩
  | bvar index =>
      simp only [liftBVars] at equal
      split_ifs at equal
  | _ => simp [liftBVars] at equal

/-- **Every reverse instance of scope extrusion**: a restriction over a bag, one member of which is the restricted
body and the others lifts of terms that do not use the restriction, becomes the bag of the restricted body and those
terms. -/
theorem extrusion_reverse_shape {ambient : Nat} {spec : RuleBindingSpec} {captured : Assignment}
    {source target : Pattern} (bound : (orientedRule (scopeExtrusionOf block) .reverse).bindings = some spec)
    (sourceScoped : source.isWellScopedAt ambient = true)
    (matched : captured ∈ matchRuleAt (orientedRule (scopeExtrusionOf block) .reverse) spec ambient source)
    (applied : reduct? (orientedRule (scopeExtrusionOf block) .reverse) spec ambient captured = some target) :
    ∃ (binder : Option String) (members : List Pattern) (selected : Nat) (originals : List Pattern)
      (inside : selected < members.length), members.eraseIdx selected = originals.map (liftBVars 0 1) ∧
      source = .apply block.restrict [.lambda binder (.collection .hashBag members none)] ∧
      target = .collection .hashBag (.apply block.restrict [.lambda none members[selected]] :: originals) none := by
  obtain rfl : spec = (orientedRule (scopeExtrusionOf block) .reverse).bindings.getD { dependencies := [] } := by
    rw [bound]; rfl
  simp only [matchRuleAt, matchRuleWithAt] at matched
  rw [show (orientedRule (scopeExtrusionOf block) .reverse).left =
      .apply block.restrict [.lambda none (.collection .hashBag [.fvar "P"] (some "rest"))] from rfl,
    mem_matchAtWith_apply] at matched
  obtain ⟨arguments, rfl, matched⟩ := matched
  rw [mem_matchArgsAtWith_cons] at matched
  obtain ⟨argument, rest, afterArgument, rfl, binderMatched, matched⟩ := matched
  rw [mem_matchArgsAtWith_nil] at matched
  obtain ⟨rfl, rfl⟩ := matched
  rw [mem_matchAtWith_lambda] at binderMatched
  obtain ⟨binder, inner, rfl, binderMatched⟩ := binderMatched
  rw [mem_matchAtWith_bag] at binderMatched
  obtain ⟨members, rfl, binderMatched⟩ := binderMatched
  rw [mem_matchBagAtWith_cons] at binderMatched
  obtain ⟨element, selected, zipped, middle, first, binderMatched⟩ := binderMatched
  rw [mem_matchBagAtWith_rest] at binderMatched
  obtain ⟨inside, chosen⟩ := List.mem_zipIdx' zipped
  have membersScoped : Pattern.isWellScopedListAt (ambient + 1) members = true := by
    simpa [Pattern.isWellScopedAt, Pattern.isWellScopedListAt] using sourceScoped
  have elementScoped : element.isWellScopedAt (1 + ambient) = true := by
    rw [chosen, Nat.add_comm]
    exact ((isWellScopedListAt_eq_true_iff _ _).mp membersScoped) _ (List.getElem_mem _)
  rw [mem_matchAtWith_fvar, captureWith?_literal] at first
  simp [capture?, orientedRule, scopeExtrusionOf, exchangeBindings, exchangeOccurrence, exchangeSite, dependencies?, arguments?,
    occurrenceDeclared, sitePattern?, occurrenceAt?, recoverValue?_one elementScoped, assign, lookup] at first
  subst first
  simp only [captureRestWith?_literal, captureRest?, capture?, orientedRule, scopeExtrusionOf,
    Option.bind_eq_bind, Option.bind_eq_some_iff] at binderMatched
  obtain ⟨restDependencies, restDeclared, restArguments, restSupplied, restValue, restRecovered, restAssigned⟩ :=
    binderMatched
  simp [dependencies?, exchangeBindings, exchangeOccurrence, exchangeSite] at restDeclared
  subst restDeclared
  simp [dependencies?, arguments?, occurrenceDeclared, sitePattern?, occurrenceAt?, exchangeBindings,
    exchangeOccurrence, exchangeSite] at restSupplied
  subst restSupplied
  have restContext := recoverValue?_context _ _ _ _ _ _ restRecovered
  have restForward := recoverValue?_forward _ _ _ _ _ _ restRecovered
  obtain ⟨restDependencies, restAmbient, lowered⟩ := restValue
  simp only at restContext
  obtain ⟨rfl, rfl⟩ := restContext
  obtain ⟨loweredScoped, liftedEq⟩ := instantiateValue?_shift_inv restForward
  obtain ⟨originals, rfl, othersEq⟩ := liftBVars_eq_collection liftedEq.symm
  simp [assign, lookup] at restAssigned
  subst restAssigned
  simp [reduct?, instantiateAt?, instantiateWith?, instantiateArgsWith?, orientedRule, scopeExtrusionOf,
    exchangeBindings, exchangeOccurrence, exchangeSite, arguments?, dependencies?, occurrenceDeclared, sitePattern?, occurrenceAt?,
    lookup, instantiateValue?_one elementScoped, instantiateValue?_root loweredScoped] at applied
  subst applied
  rw [chosen]
  exact ⟨binder, members, selected, originals, inside, othersEq, rfl, rfl⟩

/-- **Reverse scope extrusion on blocks** gives similar blocks. -/
theorem extrusion_reverse_similar (fuel : Nat) {ambient : Nat} {spec : RuleBindingSpec} {captured : Assignment}
    {source target : Pattern} (bound : (orientedRule (scopeExtrusionOf block) .reverse).bindings = some spec)
    (sourceScoped : source.isWellScopedAt ambient = true)
    (matched : captured ∈ matchRuleAt (orientedRule (scopeExtrusionOf block) .reverse) spec ambient source)
    (applied : reduct? (orientedRule (scopeExtrusionOf block) .reverse) spec ambient captured = some target) :
    Similar block fuel (decompose block source) (decompose block target) := by
  obtain ⟨binder, members, selected, originals, inside, othersEq, rfl, rfl⟩ :=
    extrusion_reverse_shape bound sourceScoped matched applied
  rw [decompose_restrict, decompose_bag, decompose_bag]
  refine (Similar.close (decomposeList_perm_similar fuel (perm_getElem_eraseIdx members selected inside))).trans
    (Similar.of_eq ?_)
  rw [othersEq, decomposeList, decomposeList, decompose_restrict, extrusion_block, ← decomposeList_renameOuter]
  congr 3
  exact List.map_congr_left fun other _ => liftBVars_eq_rename 0 1 other

/-- **Exchange on blocks, read forward**: two restrictions over a body and the two restrictions over the body with
its two innermost bound names exchanged have similar blocks. -/
theorem exchange_forward_shape {ambient : Nat} {spec : RuleBindingSpec} {captured : Assignment}
    {source target : Pattern} (bound : (orientedRule (restrictionExchangeOf block) .forward).bindings = some spec)
    (sourceScoped : source.isWellScopedAt ambient = true)
    (matched : captured ∈ matchRuleAt (orientedRule (restrictionExchangeOf block) .forward) spec ambient source)
    (applied : reduct? (orientedRule (restrictionExchangeOf block) .forward) spec ambient captured = some target) :
    ∃ (outerBinder innerBinder : Option String) (body : Pattern),
      source = .apply block.restrict [.lambda outerBinder (.apply block.restrict [.lambda innerBinder body])] ∧
      target = .apply block.restrict [.lambda none (.apply block.restrict [.lambda none (rename swapInner body)])] := by
  obtain rfl : spec = (orientedRule (restrictionExchangeOf block) .forward).bindings.getD { dependencies := [] } := by
    rw [bound]; rfl
  simp only [matchRuleAt, matchRuleWithAt] at matched
  rw [show (orientedRule (restrictionExchangeOf block) .forward).left =
      .apply block.restrict [.lambda none (.apply block.restrict [.lambda none (.fvar "P")])] from rfl,
    mem_matchAtWith_apply] at matched
  obtain ⟨arguments, rfl, matched⟩ := matched
  rw [mem_matchArgsAtWith_cons] at matched
  obtain ⟨argument, rest, afterArgument, rfl, outer, matched⟩ := matched
  rw [mem_matchArgsAtWith_nil] at matched
  obtain ⟨rfl, rfl⟩ := matched
  rw [mem_matchAtWith_lambda] at outer
  obtain ⟨outerBinder, inner, rfl, outer⟩ := outer
  rw [mem_matchAtWith_apply] at outer
  obtain ⟨innerArguments, rfl, outer⟩ := outer
  rw [mem_matchArgsAtWith_cons] at outer
  obtain ⟨innerArgument, innerRest, afterInner, rfl, innerMatched, outer⟩ := outer
  rw [mem_matchArgsAtWith_nil] at outer
  obtain ⟨rfl, rfl⟩ := outer
  rw [mem_matchAtWith_lambda] at innerMatched
  obtain ⟨innerBinder, body, rfl, innerMatched⟩ := innerMatched
  have bodyScoped : body.isWellScopedAt (2 + ambient) = true := by
    have := sourceScoped
    simp only [Pattern.isWellScopedAt, Pattern.isWellScopedListAt, Bool.and_true] at this
    rwa [show 2 + ambient = ambient + 1 + 1 by omega]
  rw [mem_matchAtWith_fvar, captureWith?_literal] at innerMatched
  simp [capture?, orientedRule, restrictionExchangeOf, dependencies?, arguments?, occurrenceDeclared, sitePattern?,
    occurrenceAt?, recoverValue?_two bodyScoped, assign, lookup] at innerMatched
  subst innerMatched
  simp [reduct?, instantiateAt?, instantiateWith?, instantiateArgsWith?, orientedRule, restrictionExchangeOf,
    arguments?, dependencies?, occurrenceDeclared, sitePattern?, occurrenceAt?, lookup,
    instantiateValue?_swap bodyScoped] at applied
  subst applied
  exact ⟨outerBinder, innerBinder, body, rfl, rfl⟩

/-- **Exchange on blocks, read backward.** -/
theorem exchange_reverse_shape {ambient : Nat} {spec : RuleBindingSpec} {captured : Assignment}
    {source target : Pattern} (bound : (orientedRule (restrictionExchangeOf block) .reverse).bindings = some spec)
    (sourceScoped : source.isWellScopedAt ambient = true)
    (matched : captured ∈ matchRuleAt (orientedRule (restrictionExchangeOf block) .reverse) spec ambient source)
    (applied : reduct? (orientedRule (restrictionExchangeOf block) .reverse) spec ambient captured = some target) :
    ∃ (outerBinder innerBinder : Option String) (body : Pattern),
      source = .apply block.restrict [.lambda outerBinder (.apply block.restrict [.lambda innerBinder body])] ∧
      target = .apply block.restrict [.lambda none (.apply block.restrict [.lambda none (rename swapInner body)])] := by
  obtain rfl : spec = (orientedRule (restrictionExchangeOf block) .reverse).bindings.getD { dependencies := [] } := by
    rw [bound]; rfl
  simp only [matchRuleAt, matchRuleWithAt] at matched
  rw [show (orientedRule (restrictionExchangeOf block) .reverse).left =
      .apply block.restrict [.lambda none (.apply block.restrict [.lambda none (.fvar "P")])] from rfl,
    mem_matchAtWith_apply] at matched
  obtain ⟨arguments, rfl, matched⟩ := matched
  rw [mem_matchArgsAtWith_cons] at matched
  obtain ⟨argument, rest, afterArgument, rfl, outer, matched⟩ := matched
  rw [mem_matchArgsAtWith_nil] at matched
  obtain ⟨rfl, rfl⟩ := matched
  rw [mem_matchAtWith_lambda] at outer
  obtain ⟨outerBinder, inner, rfl, outer⟩ := outer
  rw [mem_matchAtWith_apply] at outer
  obtain ⟨innerArguments, rfl, outer⟩ := outer
  rw [mem_matchArgsAtWith_cons] at outer
  obtain ⟨innerArgument, innerRest, afterInner, rfl, innerMatched, outer⟩ := outer
  rw [mem_matchArgsAtWith_nil] at outer
  obtain ⟨rfl, rfl⟩ := outer
  rw [mem_matchAtWith_lambda] at innerMatched
  obtain ⟨innerBinder, body, rfl, innerMatched⟩ := innerMatched
  have bodyScoped : body.isWellScopedAt (2 + ambient) = true := by
    have := sourceScoped
    simp only [Pattern.isWellScopedAt, Pattern.isWellScopedListAt, Bool.and_true] at this
    rwa [show 2 + ambient = ambient + 1 + 1 by omega]
  have swappedScoped := swapped_scoped bodyScoped
  rw [mem_matchAtWith_fvar, captureWith?_literal] at innerMatched
  simp [capture?, orientedRule, restrictionExchangeOf, exchangeBindings, exchangeOccurrence, exchangeSite,
    dependencies?, arguments?, occurrenceDeclared, sitePattern?, occurrenceAt?, recoverValue?_swap bodyScoped,
    assign, lookup] at innerMatched
  subst innerMatched
  simp [reduct?, instantiateAt?, instantiateWith?, instantiateArgsWith?, orientedRule, restrictionExchangeOf,
    exchangeBindings, exchangeOccurrence, exchangeSite, arguments?, dependencies?, occurrenceDeclared, sitePattern?,
    occurrenceAt?, lookup, instantiateValue?_two swappedScoped] at applied
  subst applied
  exact ⟨outerBinder, innerBinder, body, rfl, rfl⟩

/-- **Exchange on blocks** gives similar blocks. -/
theorem exchange_similar (fuel : Nat) {outerBinder innerBinder : Option String} {body : Pattern} :
    Similar block fuel (decompose block (.apply block.restrict [.lambda outerBinder (.apply block.restrict [.lambda innerBinder body])]))
      (decompose block (.apply block.restrict [.lambda none (.apply block.restrict [.lambda none (rename swapInner body)])])) := by
  rw [decompose_restrict, decompose_restrict, decompose_restrict, decompose_restrict, decompose_renameOuter]
  exact exchange_block fuel (decompose block body)

/-! ## Every generator gives similar blocks -/

open Mettapedia.GSLT.LanguageDef.EquationSemantics (EquationGenerator EquationInstance EquationInstanceAt
  DeclaredInstanceAt closedRoot extendClosed extendClosed_closedRoot)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (BasePremiseEvaluator PremisesAt)
open Mettapedia.OSLF.MeTTaIL.Match (matchPattern applyBindings)
open Mettapedia.OSLF.MeTTaIL.MatchSpec (matchPattern_correct)

/-- A raw match of `(νx) 0` is `(νx) 0`, under any binder display name. -/
theorem restrictionNil_raw {bindings : Mettapedia.OSLF.MeTTaIL.Match.Bindings} {pattern : Pattern}
    (matched : bindings ∈ matchPattern (restrictionNilOf block).left pattern) :
    ∃ binder, pattern = .apply block.restrict [.lambda binder (.apply block.unit [])] := by
  have related := Mettapedia.OSLF.MeTTaIL.MatchSpec.matchPattern_sound matched
  simp only [restrictionNilOf] at related
  cases related with
  | apply arguments _ =>
      cases arguments with
      | cons head tail =>
          cases tail
          cases head with
          | lambda body =>
              cases body with
              | apply inner _ =>
                  cases inner
                  exact ⟨_, rfl⟩

theorem restrictionNil_raw_right {bindings : Mettapedia.OSLF.MeTTaIL.Match.Bindings} {pattern : Pattern}
    (matched : bindings ∈ matchPattern (restrictionNilOf block).right pattern) : pattern = .apply block.unit [] := by
  have related := Mettapedia.OSLF.MeTTaIL.MatchSpec.matchPattern_sound matched
  simp only [restrictionNilOf] at related
  cases related with
  | apply arguments _ =>
      cases arguments
      rfl

theorem emptyUnit_forward_shape {label : String} {ambient : Nat} {spec : RuleBindingSpec} {captured : Assignment}
    {source target : Pattern}
    (matched : captured ∈ matchRuleAt (orientedRule (emptyUnitOf block label) .forward) spec ambient source)
    (applied : reduct? (orientedRule (emptyUnitOf block label) .forward) spec ambient captured = some target) :
    source = .apply label [.collection .hashBag [] none] ∧
      target = .apply block.restrict [.lambda none (.apply block.unit [])] := by
  simp only [matchRuleAt, matchRuleWithAt, orientedRule, emptyUnitOf] at matched
  obtain ⟨targets, rfl, arguments⟩ := mem_matchAtWith_apply.mp matched
  obtain ⟨argument, rest, middle, rfl, first, second⟩ := mem_matchArgsAtWith_cons.mp arguments
  obtain ⟨rfl, -⟩ := mem_matchArgsAtWith_nil.mp second
  obtain ⟨members, rfl, bagMatched⟩ := mem_matchAtWith_bag.mp first
  cases members with
  | nil =>
      refine ⟨rfl, ?_⟩
      simp [reduct?, instantiateAt?, instantiateWith?, instantiateArgsWith?, orientedRule, emptyUnitOf] at applied
      exact applied.symm
  | cons member others => simp [matchBagAtWith] at bagMatched

theorem emptyUnit_reverse_shape {label : String} {ambient : Nat} {spec : RuleBindingSpec} {captured : Assignment}
    {source target : Pattern}
    (matched : captured ∈ matchRuleAt (orientedRule (emptyUnitOf block label) .reverse) spec ambient source)
    (applied : reduct? (orientedRule (emptyUnitOf block label) .reverse) spec ambient captured = some target) :
    (∃ binder, source = .apply block.restrict [.lambda binder (.apply block.unit [])]) ∧
      target = .apply label [.collection .hashBag [] none] := by
  simp only [matchRuleAt, matchRuleWithAt, orientedRule, emptyUnitOf] at matched
  obtain ⟨targets, rfl, arguments⟩ := mem_matchAtWith_apply.mp matched
  obtain ⟨argument, rest, middle, rfl, first, second⟩ := mem_matchArgsAtWith_cons.mp arguments
  obtain ⟨rfl, -⟩ := mem_matchArgsAtWith_nil.mp second
  obtain ⟨binder, inner, rfl, innerMatched⟩ := mem_matchAtWith_lambda.mp first
  obtain ⟨innerArguments, rfl, innerRest⟩ := mem_matchAtWith_apply.mp innerMatched
  obtain ⟨rfl, -⟩ := mem_matchArgsAtWith_nil.mp innerRest
  refine ⟨⟨binder, rfl⟩, ?_⟩
  simp [reduct?, instantiateAt?, instantiateWith?, instantiateArgsWith?, orientedRule, emptyUnitOf] at applied
  exact applied.symm

theorem emptyMultiset_nil {label : String} (listed : label ∈ block.emptyUnits) :
    decompose block (.apply label [.collection .hashBag [] none]) = Prenex.nil := by
  have notRestriction : ∀ binder body, Pattern.apply label [.collection .hashBag [] none] ≠
      .apply block.restrict [.lambda binder body] := by
    intro binder body equal
    simp at equal
  rw [decompose_multiset notRestriction, if_pos ⟨listed, by rw [decompose_bag]; rfl⟩]

/-- **Every authored instance of the static theory gives similar blocks.** -/
theorem instance_similar (fuel : Nat) {base : BasePremiseEvaluator} {premiseFuel : Nat} {source target : Pattern}
    (equationInstance : EquationInstanceAt base language premiseFuel source target) :
    Similar block fuel (decompose block source) (decompose block target) := by
  cases equationInstance with
  | forward member raw matched _ applied =>
      rcases laws.equations_mem member with rfl | rfl | rfl | ⟨label, listed, rfl⟩
      · obtain ⟨binder, rfl⟩ := restrictionNil_raw matched
        rw [← applied]
        refine Similar.of_eq ?_
        rw [decompose_restrict]
        simp [restrictionNilOf, applyBindings, decompose_unit]
        rfl
      · exact absurd raw (by rw [exchange_raw]; decide)
      · exact absurd raw (by rw [extrusion_raw]; decide)
      · exact absurd raw (by rw [emptyUnit_raw]; decide)
  | reverse member raw matched _ applied =>
      rcases laws.equations_mem member with rfl | rfl | rfl | ⟨label, listed, rfl⟩
      · rw [restrictionNil_raw_right matched, ← applied]
        refine Similar.of_eq ?_
        simp [restrictionNilOf, applyBindings, decompose_unit, decompose_restrict]
        rfl
      · exact absurd raw (by rw [exchange_raw]; decide)
      · exact absurd raw (by rw [extrusion_raw]; decide)
      · exact absurd raw (by rw [emptyUnit_raw]; decide)
  | @declared equation orientation ambient _ _ member notRaw declared =>
      obtain ⟨spec, captured, final, bound, _, sourceScoped, matched, premises, applied, _⟩ := declared
      rcases laws.equations_mem member with rfl | rfl | rfl | ⟨label, listed, rfl⟩
      · exact absurd notRaw (by simp [nil_raw])
      · have premisesNil : (restrictionExchangeOf block).premises = [] := rfl
        rw [premisesNil] at premises
        cases premises
        rw [extendClosed_closedRoot] at applied
        cases orientation with
        | forward =>
            obtain ⟨_, _, _, rfl, rfl⟩ := exchange_forward_shape bound sourceScoped matched applied
            exact exchange_similar fuel
        | reverse =>
            obtain ⟨_, _, _, rfl, rfl⟩ := exchange_reverse_shape bound sourceScoped matched applied
            exact exchange_similar fuel
      · have premisesNil : (scopeExtrusionOf block).premises = [] := rfl
        rw [premisesNil] at premises
        cases premises
        rw [extendClosed_closedRoot] at applied
        cases orientation with
        | forward => exact extrusion_forward_similar fuel bound sourceScoped matched applied
        | reverse => exact extrusion_reverse_similar fuel bound sourceScoped matched applied
      · have premisesNil : (emptyUnitOf block label).premises = [] := rfl
        rw [premisesNil] at premises
        cases premises
        rw [extendClosed_closedRoot] at applied
        cases orientation with
        | forward =>
            obtain ⟨rfl, rfl⟩ := emptyUnit_forward_shape matched applied
            refine Similar.of_eq ?_
            rw [emptyMultiset_nil listed, decompose_restrict, decompose_unit]
            rfl
        | reverse =>
            obtain ⟨⟨binder, rfl⟩, rfl⟩ := emptyUnit_reverse_shape matched applied
            refine Similar.of_eq ?_
            rw [emptyMultiset_nil listed, decompose_restrict, decompose_unit]
            rfl

/-- **Every generator of the static theory gives similar blocks.** -/
theorem generator_similar (fuel : Nat) {base : BasePremiseEvaluator} {source target : Pattern}
    (generator : EquationGenerator base language source target) : Similar block fuel (decompose block source) (decompose block target) := by
  rcases generator with ⟨_, equationInstance⟩ | derived
  · exact instance_similar fuel equationInstance
  · exact derived_similar fuel derived

/-! ## What a block keeps of its process -/

/-- The block's components, with what they use past the block's restrictions. -/
def Prenex.FreePast (form : Prenex) (index : Nat) : Prop :=
  ∃ component ∈ form.components, FreeIn (index + form.count) component

theorem freePast_par (first second : Prenex) (index : Nat) :
    (first.par second).FreePast index ↔ first.FreePast index ∨ second.FreePast index := by
  obtain ⟨a, firstComponents⟩ := first
  obtain ⟨b, secondComponents⟩ := second
  simp only [Prenex.FreePast, Prenex.par, List.mem_append, List.mem_map]
  constructor
  · rintro ⟨_, (⟨component, member, rfl⟩ | ⟨component, member, rfl⟩), free⟩
    · rw [liftBVars_eq_rename, freeIn_rename] at free
      obtain ⟨original, originalFree, equal⟩ := free
      simp only [shiftAbove, Nat.not_lt_zero, if_false] at equal
      exact .inl ⟨component, member, by rwa [show index + a = original by omega]⟩
    · rw [liftBVars_eq_rename, freeIn_rename] at free
      obtain ⟨original, originalFree, equal⟩ := free
      simp only [shiftAbove] at equal
      split_ifs at equal with below
      · omega
      · exact .inr ⟨component, member, by rwa [show index + b = original by omega]⟩
  · rintro (⟨component, member, free⟩ | ⟨component, member, free⟩)
    · refine ⟨_, .inl ⟨component, member, rfl⟩, ?_⟩
      rw [liftBVars_eq_rename, freeIn_rename]
      exact ⟨index + a, free, by simp [shiftAbove, Nat.add_assoc]⟩
    · refine ⟨_, .inr ⟨component, member, rfl⟩, ?_⟩
      rw [liftBVars_eq_rename, freeIn_rename]
      exact ⟨index + b, free, by simp [shiftAbove]; omega⟩

theorem freePast_close (form : Prenex) (index : Nat) :
    form.close.FreePast index ↔ form.FreePast (index + 1) := by
  obtain ⟨count, components⟩ := form
  simp only [Prenex.close]
  split_ifs with used
  · simp only [Prenex.FreePast, Prenex.restrict]
    exact exists_congr fun component => and_congr_right fun _ => by rw [show index + (count + 1) = index + 1 + count by omega]
  · have unused := unused_of_any (Bool.eq_false_iff.mpr used)
    simp only [Prenex.FreePast, List.mem_map]
    constructor
    · rintro ⟨_, ⟨component, member, rfl⟩, free⟩
      rw [freeIn_rename] at free
      obtain ⟨original, originalFree, equal⟩ := free
      have different : original ≠ count := fun same => unused component member (same ▸ originalFree)
      simp only [dropIndex] at equal
      split_ifs at equal with below
      · omega
      · exact ⟨component, member, by rwa [show index + 1 + count = original by omega]⟩
    · rintro ⟨component, member, free⟩
      refine ⟨_, ⟨component, member, rfl⟩, ?_⟩
      rw [freeIn_rename]
      exact ⟨index + 1 + count, free, by simp [dropIndex]⟩

mutual
  /-- **A process uses what its block's components use past the block's restrictions.** -/
  theorem freeIn_decompose (pattern : Pattern) : ∀ index, FreeIn index pattern ↔ (decompose block pattern).FreePast index := by
    intro index
    by_cases isNil : pattern = .apply block.unit []
    · subst isNil
      simp only [decompose_unit, Prenex.FreePast, Prenex.nil, List.not_mem_nil, false_and, exists_false, iff_false]
      rw [freeIn_apply]
      simp
    by_cases isRestriction : ∃ binder body, pattern = .apply block.restrict [.lambda binder body]
    · obtain ⟨binder, body, rfl⟩ := isRestriction
      rw [decompose_restrict, freePast_close, ← freeIn_decompose body (index + 1), freeIn_apply]
      simp [freeIn_lambda]
    by_cases isBag : ∃ elements, pattern = .collection .hashBag elements none
    · obtain ⟨elements, rfl⟩ := isBag
      rw [decompose_bag, freeIn_collection]
      exact freeIn_decomposeList elements index
    by_cases isEmptyCandidate : ∃ label argument, pattern = .apply label [argument] ∧ label ∈ block.emptyUnits
    · obtain ⟨label, argument, rfl, listed⟩ := isEmptyCandidate
      rw [decompose_multiset (fun binder body equal => isRestriction ⟨binder, body, equal⟩)]
      split_ifs with empty
      · have inner := freeIn_decompose argument index
        rw [empty.2] at inner
        rw [freeIn_apply, ← inner]
        simp
      · simp [Prenex.FreePast, Prenex.atom]
    rw [decompose_atom isNil (fun binder body equal => isRestriction ⟨binder, body, equal⟩)
      (fun elements equal => isBag ⟨elements, equal⟩)
      (fun label argument equal listed => isEmptyCandidate ⟨label, argument, equal, listed⟩)]
    simp [Prenex.FreePast, Prenex.atom]
  termination_by sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  theorem freeIn_decomposeList (elements : List Pattern) : ∀ index,
      (∃ element ∈ elements, FreeIn index element) ↔ (decomposeList block elements).FreePast index := by
    intro index
    match elements with
    | [] => simp [decomposeList, Prenex.FreePast, Prenex.nil]
    | element :: elements =>
        rw [decomposeList, freePast_par, ← freeIn_decompose element index,
          ← freeIn_decomposeList elements index]
        simp
  termination_by sizeOf elements
  decreasing_by all_goals sizeOf_pattern_dec
end

/-- **Similar blocks use the same variables past their restrictions.** -/
theorem Similar.freePast_iff {fuel : Nat} {first second : Prenex} (similar : Similar block fuel first second) (index : Nat) :
    first.FreePast index ↔ second.FreePast index := by
  have same := similar.mentions_eq (index + first.count) (by omega)
  simp only [Prenex.FreePast, ← similar.1]
  have toBool : ∀ (form : Prenex), (∃ component ∈ form.components, FreeIn (index + first.count) component) ↔
      form.components.any (mentions (index + first.count)) = true := by
    intro form
    simp only [List.any_eq_true, mentions_iff]
  rw [toBool, toBool, same]

theorem allObject_par (first second : Prenex) :
    (first.par second).components.all isObjectPattern =
      (first.components.all isObjectPattern && second.components.all isObjectPattern) := by
  simp [Prenex.par, List.all_append, List.all_map, Function.comp_def, liftBVars_eq_rename, isObjectPattern_rename]

theorem allObject_close (form : Prenex) :
    form.close.components.all isObjectPattern = form.components.all isObjectPattern := by
  obtain ⟨count, components⟩ := form
  simp only [Prenex.close]
  split_ifs
  · rfl
  · simp [List.all_map, Function.comp_def, isObjectPattern_rename]

mutual
  /-- **A process is an object pattern exactly when its block's components are.** -/
  theorem isObject_decompose (pattern : Pattern) :
      isObjectPattern pattern = (decompose block pattern).components.all isObjectPattern := by
    by_cases isNil : pattern = .apply block.unit []
    · subst isNil
      rw [decompose_unit]
      rfl
    by_cases isRestriction : ∃ binder body, pattern = .apply block.restrict [.lambda binder body]
    · obtain ⟨binder, body, rfl⟩ := isRestriction
      rw [decompose_restrict, allObject_close, ← isObject_decompose body]
      simp [isObjectPattern, isObjectPatternList]
    by_cases isBag : ∃ elements, pattern = .collection .hashBag elements none
    · obtain ⟨elements, rfl⟩ := isBag
      rw [decompose_bag, ← isObject_decomposeList elements]
      simp [isObjectPattern, isObjectPatternList_eq_all]
    by_cases isEmptyCandidate : ∃ label argument, pattern = .apply label [argument] ∧ label ∈ block.emptyUnits
    · obtain ⟨label, argument, rfl, listed⟩ := isEmptyCandidate
      rw [decompose_multiset (fun binder body equal => isRestriction ⟨binder, body, equal⟩)]
      split_ifs with empty
      · have inner := isObject_decompose argument
        rw [empty.2] at inner
        simp only [isObjectPattern, isObjectPatternList, Bool.and_true]
        simpa [Prenex.nil] using inner
      · simp [Prenex.atom]
    rw [decompose_atom isNil (fun binder body equal => isRestriction ⟨binder, body, equal⟩)
      (fun elements equal => isBag ⟨elements, equal⟩)
      (fun label argument equal listed => isEmptyCandidate ⟨label, argument, equal, listed⟩)]
    simp [Prenex.atom]
  termination_by sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  theorem isObject_decomposeList (elements : List Pattern) :
      elements.all isObjectPattern = (decomposeList block elements).components.all isObjectPattern := by
    match elements with
    | [] => rfl
    | element :: elements =>
        rw [decomposeList, allObject_par, ← isObject_decompose element, ← isObject_decomposeList elements]
        rfl
  termination_by sizeOf elements
  decreasing_by all_goals sizeOf_pattern_dec
end

/-- **Similar blocks are both made of object patterns or both not.** -/
theorem Similar.allObject_eq {fuel : Nat} {first second : Prenex} (similar : Similar block fuel first second) :
    first.components.all isObjectPattern = second.components.all isObjectPattern := by
  obtain ⟨_, order, middle, _, related, permutation⟩ := similar
  have renamed : (first.components.map (rename (Prenex.permute first.count order))).all isObjectPattern =
      first.components.all isObjectPattern := by
    simp [List.all_map, Function.comp_def, isObjectPattern_rename]
  rw [← renamed, ← (permutation.all_eq (f := isObjectPattern))]
  clear renamed permutation
  generalize first.components.map (rename (Prenex.permute first.count order)) = renamedList at related ⊢
  induction related with
  | nil => rfl
  | cons here _ recurse => simp only [List.all_cons, here.2.1, recurse]

/-- **Renaming the outside keeps blocks similar.** -/
theorem Similar.renameOuter {fuel : Nat} {first second : Prenex} (similar : Similar block fuel first second)
    (relabel : Nat → Nat) : Similar block fuel (first.renameOuter relabel) (second.renameOuter relabel) := by
  obtain ⟨countEq, order, middle, isOrder, related, permutation⟩ := similar
  obtain ⟨count, firstComponents⟩ := first
  obtain ⟨count', secondComponents⟩ := second
  simp only at countEq isOrder related permutation
  subst countEq
  refine ⟨rfl, order, middle.map (rename (liftIndex count relabel)), isOrder, ?_, permutation.map _⟩
  have confined := confined_permute isOrder
  have commute : (firstComponents.map (rename (liftIndex count relabel))).map (rename (Prenex.permute count order)) =
      (firstComponents.map (rename (Prenex.permute count order))).map (rename (liftIndex count relabel)) := by
    simp only [List.map_map]
    refine List.map_congr_left fun component _ => ?_
    simp only [Function.comp, rename_comp]
    congr 1
    funext index
    simp only [Function.comp, liftIndex]
    by_cases inside : index < count
    · simp [inside, confined.below _ inside]
    · rw [if_neg inside, confined.above _ (by omega), confined.above _ (by omega), if_neg inside]
  simp only [Prenex.renameOuter]
  rw [commute]
  exact forall₂_alike_rename _ related

/-! ## Contexts -/

open Mettapedia.OSLF.MeTTaIL.DerivedContexts (OneHoleContext)

namespace ContextRenaming

/-- The number of frames around the hole. -/
def frames : OneHoleContext → Nat
  | .hole => 0
  | .apply _ _ inner _ => frames inner + 1
  | .lambda _ inner => frames inner + 1
  | .multiLambda _ _ inner => frames inner + 1
  | .substBody inner _ => frames inner + 1
  | .substReplacement _ inner => frames inner + 1
  | .collection _ _ inner _ _ => frames inner + 1

/-- Rename the variables of a context, passing each binder. -/
def rename : (Nat → Nat) → OneHoleContext → OneHoleContext
  | _, .hole => .hole
  | relabel, .apply constructor before inner after =>
      .apply constructor (before.map (RestrictionBlocks.rename relabel)) (rename relabel inner)
        (after.map (RestrictionBlocks.rename relabel))
  | relabel, .lambda binder inner => .lambda binder (rename (liftIndex 1 relabel) inner)
  | relabel, .multiLambda arity binders inner => .multiLambda arity binders (rename (liftIndex arity relabel) inner)
  | relabel, .substBody inner replacement =>
      .substBody (rename (liftIndex 1 relabel) inner) (RestrictionBlocks.rename relabel replacement)
  | relabel, .substReplacement body inner =>
      .substReplacement (RestrictionBlocks.rename (liftIndex 1 relabel) body) (rename relabel inner)
  | relabel, .collection kind before inner after rest =>
      .collection kind (before.map (RestrictionBlocks.rename relabel)) (rename relabel inner)
        (after.map (RestrictionBlocks.rename relabel)) rest

/-- The renaming that reaches the hole. -/
def atHole : (Nat → Nat) → OneHoleContext → (Nat → Nat)
  | relabel, .hole => relabel
  | relabel, .apply _ _ inner _ => atHole relabel inner
  | relabel, .lambda _ inner => atHole (liftIndex 1 relabel) inner
  | relabel, .multiLambda arity _ inner => atHole (liftIndex arity relabel) inner
  | relabel, .substBody inner _ => atHole (liftIndex 1 relabel) inner
  | relabel, .substReplacement _ inner => atHole relabel inner
  | relabel, .collection _ _ inner _ _ => atHole relabel inner

theorem frames_rename : ∀ (relabel : Nat → Nat) (context : OneHoleContext),
    frames (rename relabel context) = frames context
  | _, .hole => rfl
  | relabel, .apply _ _ inner _ => by simp [rename, frames, frames_rename relabel inner]
  | relabel, .lambda _ inner => by simp [rename, frames, frames_rename _ inner]
  | relabel, .multiLambda _ _ inner => by simp [rename, frames, frames_rename _ inner]
  | relabel, .substBody inner _ => by simp [rename, frames, frames_rename _ inner]
  | relabel, .substReplacement _ inner => by simp [rename, frames, frames_rename relabel inner]
  | relabel, .collection _ _ inner _ _ => by simp [rename, frames, frames_rename relabel inner]

/-- **Renaming a filled context** renames the context and the filling, the filling past the context's binders. -/
theorem rename_fill : ∀ (relabel : Nat → Nat) (context : OneHoleContext) (filling : Pattern),
    RestrictionBlocks.rename relabel (context.fill filling) =
      (rename relabel context).fill (RestrictionBlocks.rename (atHole relabel context) filling)
  | _, .hole, _ => rfl
  | relabel, .apply _ _ inner _, filling => by
      simp only [OneHoleContext.fill, rename, atHole, rename_apply, List.map_append, List.map_cons,
        rename_fill relabel inner filling]
  | relabel, .lambda _ inner, filling => by
      simp only [OneHoleContext.fill, rename, atHole, rename_lambda, rename_fill _ inner filling]
  | relabel, .multiLambda _ _ inner, filling => by
      simp only [OneHoleContext.fill, rename, atHole, rename_multiLambda, rename_fill _ inner filling]
  | relabel, .substBody inner _, filling => by
      simp only [OneHoleContext.fill, rename, atHole, rename_subst, rename_fill _ inner filling]
  | relabel, .substReplacement _ inner, filling => by
      simp only [OneHoleContext.fill, rename, atHole, rename_subst, rename_fill relabel inner filling]
  | relabel, .collection _ _ inner _ _, filling => by
      simp only [OneHoleContext.fill, rename, atHole, rename_collection, List.map_append, List.map_cons,
        rename_fill relabel inner filling]

end ContextRenaming

/-- Fillings using the same variables give fillings using the same variables. -/
theorem freeIn_fill_congr {first second : Pattern} (same : ∀ index, FreeIn index first ↔ FreeIn index second) :
    ∀ (context : OneHoleContext) (index : Nat), FreeIn index (context.fill first) ↔ FreeIn index (context.fill second)
  | .hole, index => same index
  | .apply _ before inner after, index => by
      simp only [OneHoleContext.fill, freeIn_apply, List.mem_append, List.mem_cons]
      constructor
      · rintro ⟨argument, (member | rfl | member), free⟩
        · exact ⟨argument, .inl member, free⟩
        · exact ⟨_, .inr (.inl rfl), (freeIn_fill_congr same inner index).mp free⟩
        · exact ⟨argument, .inr (.inr member), free⟩
      · rintro ⟨argument, (member | rfl | member), free⟩
        · exact ⟨argument, .inl member, free⟩
        · exact ⟨_, .inr (.inl rfl), (freeIn_fill_congr same inner index).mpr free⟩
        · exact ⟨argument, .inr (.inr member), free⟩
  | .lambda _ inner, index => by
      simp only [OneHoleContext.fill, freeIn_lambda]
      exact freeIn_fill_congr same inner (index + 1)
  | .multiLambda arity _ inner, index => by
      simp only [OneHoleContext.fill, freeIn_multiLambda]
      exact freeIn_fill_congr same inner (index + arity)
  | .substBody inner _, index => by
      simp only [OneHoleContext.fill, freeIn_subst]
      rw [freeIn_fill_congr same inner (index + 1)]
  | .substReplacement _ inner, index => by
      simp only [OneHoleContext.fill, freeIn_subst]
      rw [freeIn_fill_congr same inner index]
  | .collection _ before inner after _, index => by
      simp only [OneHoleContext.fill, freeIn_collection, List.mem_append, List.mem_cons]
      constructor
      · rintro ⟨element, (member | rfl | member), free⟩
        · exact ⟨element, .inl member, free⟩
        · exact ⟨_, .inr (.inl rfl), (freeIn_fill_congr same inner index).mp free⟩
        · exact ⟨element, .inr (.inr member), free⟩
      · rintro ⟨element, (member | rfl | member), free⟩
        · exact ⟨element, .inl member, free⟩
        · exact ⟨_, .inr (.inl rfl), (freeIn_fill_congr same inner index).mpr free⟩
        · exact ⟨element, .inr (.inr member), free⟩

/-- Fillings that are both object patterns or both not give fillings that are both or both not. -/
theorem isObject_fill_congr {first second : Pattern} (same : isObjectPattern first = isObjectPattern second) :
    ∀ (context : OneHoleContext), isObjectPattern (context.fill first) = isObjectPattern (context.fill second)
  | .hole => same
  | .apply _ before inner after => by
      simp only [OneHoleContext.fill, isObjectPattern, isObjectPatternList_eq_all, List.all_append, List.all_cons,
        isObject_fill_congr same inner]
  | .lambda _ inner => by simp only [OneHoleContext.fill, isObjectPattern, isObject_fill_congr same inner]
  | .multiLambda _ _ inner => by simp only [OneHoleContext.fill, isObjectPattern, isObject_fill_congr same inner]
  | .substBody _ _ => rfl
  | .substReplacement _ _ => rfl
  | .collection _ before inner after _ => by
      simp only [OneHoleContext.fill, isObjectPattern, isObjectPatternList_eq_all, List.all_append, List.all_cons,
        isObject_fill_congr same inner]

/-! ## Variables and explicit substitutions are their own canonical form -/

/-- A pattern the canonical form leaves as it is: a variable or an explicit substitution. -/
def Inert : Pattern → Prop
  | .bvar _ => True
  | .fvar _ => True
  | .subst _ _ => True
  | _ => False

theorem inert_decompose {pattern : Pattern} (inert : Inert pattern) : decompose block pattern = Prenex.atom pattern := by
  cases pattern <;> simp_all [Inert, decompose]

theorem inert_component : ∀ (fuel : Nat) {pattern : Pattern}, Inert pattern → canonComponentWith block fuel pattern = pattern
  | 0, _, _ => rfl
  | _ + 1, pattern, inert => by cases pattern <;> simp_all [Inert, canonComponentWith]

theorem inert_rename_id {pattern : Pattern} : rename (Prenex.permute 0 []) pattern = pattern := by
  have identity : Prenex.permute 0 [] = id := by
    funext index
    simp [Prenex.permute]
  rw [identity, rename_id]

/-- **Variables and explicit substitutions are their own canonical form.** -/
theorem canonWith_inert : ∀ (fuel : Nat) {pattern : Pattern}, Inert pattern → canonWith block fuel pattern = pattern
  | 0, _, _ => rfl
  | fuel + 1, pattern, inert => by
      rw [canonWith_succ, inert_decompose inert]
      have reading : readings block fuel (Prenex.atom pattern) = [[pattern]] := by
        simp only [readings, Prenex.atom, List.range_zero, orders, List.map_cons, List.map_nil, inert_rename_id,
          inert_component fuel inert]
        rfl
      rw [reading]
      rfl

theorem canonArgument_of_notLambda {canonical : Pattern → Pattern} (fuelled : ∀ pattern, Inert pattern →
    canonical pattern = pattern) {pattern : Pattern} (notLambda : ∀ binder body, pattern ≠ .lambda binder body) :
    canonArgument canonical pattern = canonical pattern := by
  cases pattern with
  | lambda binder body => exact absurd rfl (notLambda binder body)
  | bvar index => exact (fuelled (.bvar index) trivial).symm
  | fvar name => exact (fuelled (.fvar name) trivial).symm
  | subst body replacement => exact (fuelled (.subst body replacement) trivial).symm
  | apply => rfl
  | multiLambda => rfl
  | collection => rfl

/-! ## Fillings a context cannot tell apart -/

/-- Two fillings no context tells apart: similar blocks at every fuel, the same variables, both object patterns or
both not, and neither an abstraction. -/
structure Interchangeable (block : Block) (first second : Pattern) : Prop where
  similar : ∀ fuel, Similar block fuel (decompose block first) (decompose block second)
  free : ∀ index, FreeIn index first ↔ FreeIn index second
  object : isObjectPattern first = isObjectPattern second
  firstNotLambda : ∀ binder body, first ≠ .lambda binder body
  secondNotLambda : ∀ binder body, second ≠ .lambda binder body

theorem rename_notLambda {relabel : Nat → Nat} {pattern : Pattern} (notLambda : ∀ binder body, pattern ≠ .lambda binder body) :
    ∀ binder body, rename relabel pattern ≠ .lambda binder body := by
  intro binder body equal
  cases pattern with
  | lambda binder' body' => exact notLambda binder' body' rfl
  | _ => simp [rename_bvar, rename_fvar, rename_apply, rename_multiLambda, rename_subst, rename_collection] at equal

theorem Interchangeable.rename {first second : Pattern} (pair : Interchangeable block first second) (relabel : Nat → Nat) :
    Interchangeable block (rename relabel first) (rename relabel second) where
  similar fuel := by
    rw [decompose_renameOuter, decompose_renameOuter]
    exact (pair.similar fuel).renameOuter relabel
  free index := by
    rw [freeIn_rename, freeIn_rename]
    exact exists_congr fun original => and_congr_left fun _ => pair.free original
  object := by rw [isObjectPattern_rename, isObjectPattern_rename, pair.object]
  firstNotLambda := rename_notLambda pair.firstNotLambda
  secondNotLambda := rename_notLambda pair.secondNotLambda

theorem instantiateWith?_apply {operation : Pattern → Pattern → Pattern} {rule : RewriteRule} {spec : RuleBindingSpec}
    {ambient : Nat} {site : RulePatternSite} {path : List Nat} {depth : Nat} {assignment : Assignment}
    {constructor : String} {arguments : List Pattern} {result : Pattern}
    (instantiated : instantiateWith? operation rule spec ambient site path depth assignment
      (.apply constructor arguments) = some result) : ∃ results, result = .apply constructor results := by
  simp only [instantiateWith?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at instantiated
  obtain ⟨results, _, rfl⟩ := instantiated
  exact ⟨results, rfl⟩

theorem instantiateWith?_collection {operation : Pattern → Pattern → Pattern} {rule : RewriteRule}
    {spec : RuleBindingSpec} {ambient : Nat} {site : RulePatternSite} {path : List Nat} {depth : Nat}
    {assignment : Assignment} {kind : CollType} {elements : List Pattern} {rest : Option String} {result : Pattern}
    (instantiated : instantiateWith? operation rule spec ambient site path depth assignment
      (.collection kind elements rest) = some result) : ∃ results, result = .collection kind results none := by
  simp only [instantiateWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at instantiated
  obtain ⟨explicit, _, rest'⟩ := instantiated
  cases rest with
  | none =>
      simp only [Option.some.injEq] at rest'
      exact ⟨explicit, rest'.symm⟩
  | some name =>
      simp only [Option.bind_eq_some_iff] at rest'
      obtain ⟨value, _, arguments, _, instantiatedValue, _, matched⟩ := rest'
      split at matched
      · split_ifs at matched with sameKind
        · simp only [Option.some.injEq] at matched
          exact ⟨_, matched.symm⟩
      · cases matched

/-- A rule whose left side is a constructor or a collection never matches an abstraction. -/
theorem matched_notLambda {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat} {captured : Assignment}
    {source : Pattern} (matched : captured ∈ matchRuleAt rule spec ambient source)
    (shape : (∃ constructor patterns, rule.left = .apply constructor patterns) ∨
      ∃ patterns rest, rule.left = .collection .hashBag patterns rest) :
    ∀ binder body, source ≠ .lambda binder body := by
  intro binder body equal
  subst equal
  simp only [matchRuleAt, matchRuleWithAt] at matched
  rcases shape with ⟨constructor, patterns, leftIs⟩ | ⟨patterns, rest, leftIs⟩ <;> rw [leftIs] at matched
  · obtain ⟨_, equal, _⟩ := mem_matchAtWith_apply.mp matched
    cases equal
  · obtain ⟨_, equal, _⟩ := mem_matchAtWith_bag.mp matched
    cases equal

/-- A rule whose right side is a constructor or a collection never emits an abstraction. -/
theorem reduct_notLambda {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat} {captured : Assignment}
    {target : Pattern} (applied : reduct? rule spec ambient captured = some target)
    (shape : (∃ constructor patterns, rule.right = .apply constructor patterns) ∨
      ∃ kind patterns rest, rule.right = .collection kind patterns rest) :
    ∀ binder body, target ≠ .lambda binder body := by
  intro binder body equal
  subst equal
  simp only [reduct?, instantiateAt?] at applied
  rcases shape with ⟨constructor, patterns, rightIs⟩ | ⟨kind, patterns, rest, rightIs⟩ <;> rw [rightIs] at applied
  · obtain ⟨_, equal⟩ := instantiateWith?_apply applied
    cases equal
  · obtain ⟨_, equal⟩ := instantiateWith?_collection applied
    cases equal

include laws in
/-- **No endpoint of a generator of the static theory is an abstraction.** -/
theorem generator_notLambda {base : BasePremiseEvaluator} {source target : Pattern}
    (generator : EquationGenerator base language source target) :
    (∀ binder body, source ≠ .lambda binder body) ∧ (∀ binder body, target ≠ .lambda binder body) := by
  rcases generator with ⟨_, equationInstance⟩ | derived
  · cases equationInstance with
    | forward member raw matched _ applied =>
        rcases laws.equations_mem member with rfl | rfl | rfl | ⟨label, listed, rfl⟩
        · obtain ⟨binder, rfl⟩ := restrictionNil_raw matched
          refine ⟨fun _ _ equal => (by cases equal), fun _ _ equal => ?_⟩
          rw [← applied] at equal
          simp [restrictionNilOf, applyBindings] at equal
        · exact absurd raw (by rw [exchange_raw]; decide)
        · exact absurd raw (by rw [extrusion_raw]; decide)
        · exact absurd raw (by rw [emptyUnit_raw]; decide)
    | reverse member raw matched _ applied =>
        rcases laws.equations_mem member with rfl | rfl | rfl | ⟨label, listed, rfl⟩
        · rw [restrictionNil_raw_right matched]
          refine ⟨fun _ _ equal => (by cases equal), fun _ _ equal => ?_⟩
          rw [← applied] at equal
          simp [restrictionNilOf, applyBindings] at equal
        · exact absurd raw (by rw [exchange_raw]; decide)
        · exact absurd raw (by rw [extrusion_raw]; decide)
        · exact absurd raw (by rw [emptyUnit_raw]; decide)
    | @declared equation orientation ambient _ _ member notRaw declared =>
        obtain ⟨spec, captured, final, bound, _, _, matched, premises, applied, _⟩ := declared
        rcases laws.equations_mem member with rfl | rfl | rfl | ⟨label, listed, rfl⟩
        · exact absurd notRaw (by simp [nil_raw])
        · cases orientation
          · exact ⟨matched_notLambda matched (.inl ⟨_, _, rfl⟩), reduct_notLambda applied (.inl ⟨_, _, rfl⟩)⟩
          · exact ⟨matched_notLambda matched (.inl ⟨_, _, rfl⟩), reduct_notLambda applied (.inl ⟨_, _, rfl⟩)⟩
        · cases orientation
          · exact ⟨matched_notLambda matched (.inr ⟨_, _, rfl⟩), reduct_notLambda applied (.inl ⟨_, _, rfl⟩)⟩
          · exact ⟨matched_notLambda matched (.inl ⟨_, _, rfl⟩), reduct_notLambda applied (.inr ⟨_, _, _, rfl⟩)⟩
        · cases orientation
          · exact ⟨matched_notLambda matched (.inl ⟨_, _, rfl⟩), reduct_notLambda applied (.inl ⟨_, _, rfl⟩)⟩
          · exact ⟨matched_notLambda matched (.inl ⟨_, _, rfl⟩), reduct_notLambda applied (.inl ⟨_, _, rfl⟩)⟩
  · cases derived with
    | bagPerm => exact ⟨fun _ _ equal => (by cases equal), fun _ _ equal => (by cases equal)⟩
    | setPerm member typed => exact absurd typed (laws.no_set_rule member)
    | setDedup member typed => exact absurd typed (laws.no_set_rule member)
    | flatten => exact ⟨fun _ _ equal => (by cases equal), fun _ _ equal => (by cases equal)⟩
    | @singleton rule kind algebra element algebraRule _ sorted =>
        refine ⟨fun _ _ equal => (by cases equal), fun binder body equal => ?_⟩
        subst equal
        obtain ⟨free, bound, typed⟩ := sorted
        rcases Mettapedia.GSLT.LanguageDef.WellSorted.hasType_collection_inversion typed with
          ⟨_, typeIs, _⟩ | ⟨rule', _, _, member', shape, _, elementsTyped⟩
        · cases typeIs
        · obtain ⟨_, rfl, _⟩ := laws.bare_shape member' shape
          have lambdaTyped := Mettapedia.GSLT.LanguageDef.BagNormalForm.elementsHaveType_iff.mp elementsTyped _
            List.mem_cons_self
          cases lambdaTyped
    | unitElim => exact ⟨fun _ _ equal => (by cases equal), fun _ _ equal => (by cases equal)⟩
    | emptyUnit => exact ⟨fun _ _ equal => (by cases equal), fun _ _ equal => (by cases equal)⟩

/-- **The two sides of a generator are interchangeable.** -/
theorem generator_interchangeable {base : BasePremiseEvaluator} {source target : Pattern}
    (generator : EquationGenerator base language source target) : Interchangeable block source target where
  similar fuel := generator_similar fuel generator
  free index := by
    rw [freeIn_decompose (block := block), freeIn_decompose (block := block)]
    exact (generator_similar 0 generator).freePast_iff index
  object := by
    rw [isObject_decompose (block := block), isObject_decompose (block := block)]
    exact (generator_similar 0 generator).allObject_eq
  firstNotLambda := (generator_notLambda (block := block) generator).1
  secondNotLambda := (generator_notLambda (block := block) generator).2

/-! ## Contexts cannot tell interchangeable fillings apart -/

open ContextRenaming (frames)

theorem isObject_apply_member {constructor : String} {before after : List Pattern} {middle : Pattern}
    (object : isObjectPattern (.apply constructor (before ++ middle :: after)) = true) : isObjectPattern middle = true := by
  simp only [isObjectPattern, isObjectPatternList_eq_all, List.all_eq_true] at object
  exact object middle (by simp)

theorem isObject_collection_member {kind : CollType} {before after : List Pattern} {middle : Pattern}
    {rest : Option String} (object : isObjectPattern (.collection kind (before ++ middle :: after) rest) = true) :
    isObjectPattern middle = true := by
  simp only [isObjectPattern, isObjectPatternList_eq_all, Bool.and_eq_true, List.all_eq_true] at object
  exact object.2 middle (by simp)

/-- The hypothesis of the induction over contexts: contexts with fewer frames do not tell interchangeable fillings
apart. -/
def Undetected (block : Block) (bound : Nat) : Prop :=
  ∀ (context : OneHoleContext), frames context < bound → ∀ {first second : Pattern}, Interchangeable block first second →
    ∀ fuel, 2 * frames context ≤ fuel → isObjectPattern (context.fill first) = true →
      Similar block fuel (decompose block (context.fill first)) (decompose block (context.fill second))

/-- Inner contexts with fewer frames give one canonical form, with fuel to spare. -/
theorem undetected_canon {bound : Nat} (inner : Undetected block bound) {context : OneHoleContext}
    (fewer : frames context < bound) {first second : Pattern} (pair : Interchangeable block first second) {fuel : Nat}
    (enough : 2 * frames context ≤ fuel) (object : isObjectPattern (context.fill first) = true) :
    canonWith block (fuel + 1) (context.fill first) = canonWith block (fuel + 1) (context.fill second) :=
  canonWith_eq_of_similar (inner context fewer pair fuel enough object)

theorem fill_eq_lambda {context : OneHoleContext} {filling : Pattern} {binder : Option String} {body : Pattern}
    (equal : context.fill filling = .lambda binder body) :
    (context = .hole ∧ filling = .lambda binder body) ∨ ∃ inner, context = .lambda binder inner := by
  cases context with
  | hole => exact .inl ⟨rfl, equal⟩
  | lambda binder' inner =>
      simp only [OneHoleContext.fill, Pattern.lambda.injEq] at equal
      exact .inr ⟨inner, by rw [equal.1]⟩
  | _ => simp [OneHoleContext.fill] at equal

/-- **The component lemma**: inside a frame, interchangeable fillings give one component with canonical parts. -/
theorem component_canon {context : OneHoleContext} (notHole : 0 < frames context)
    (inner : Undetected block (frames context)) {first second : Pattern} (pair : Interchangeable block first second) {fuel : Nat}
    (enough : 2 * frames context ≤ fuel) (object : isObjectPattern (context.fill first) = true) :
    canonComponentWith block fuel (context.fill first) = canonComponentWith block fuel (context.fill second) := by
  obtain ⟨spare, rfl⟩ : ∃ spare, fuel = spare + 2 := ⟨fuel - 2, by omega⟩
  cases context with
  | hole => simp [frames] at notHole
  | apply constructor before middle after =>
      have middleObject := isObject_apply_member object
      by_cases isMultiset : constructor ∈ block.multisets
      · simp only [OneHoleContext.fill, canonComponentWith, if_pos isMultiset, List.map_append, List.map_cons]
        congr 3
        have secondObject : isObjectPattern (middle.fill second) = true := by
          rw [← isObject_fill_congr pair.object middle]
          exact middleObject
        exact canonMultisetWith_eq_of_similar middleObject secondObject
          (inner middle (by simp only [frames]; omega) pair spare (by simp [frames] at enough; omega) middleObject)
      simp only [OneHoleContext.fill, canonComponentWith, if_neg isMultiset, List.map_append, List.map_cons]
      congr 3
      cases middle with
      | hole =>
          show canonArgument (canonWith block (spare + 1)) first = canonArgument (canonWith block (spare + 1)) second
          rw [canonArgument_of_notLambda (canonical := canonWith block (spare + 1))
              (fun _ inert => canonWith_inert (spare + 1) inert) pair.firstNotLambda,
            canonArgument_of_notLambda (canonical := canonWith block (spare + 1))
              (fun _ inert => canonWith_inert (spare + 1) inert) pair.secondNotLambda]
          exact canonWith_eq_of_similar (pair.similar spare)
      | lambda binder body =>
          simp only [OneHoleContext.fill, canonArgument]
          congr 1
          exact undetected_canon inner (by simp only [frames]; omega) pair (by simp [frames] at enough ⊢; omega)
            (by simpa [OneHoleContext.fill, isObjectPattern] using middleObject)
      | substBody body replacement => simp [OneHoleContext.fill, isObjectPattern] at middleObject
      | substReplacement body replacement => simp [OneHoleContext.fill, isObjectPattern] at middleObject
      | _ =>
          rw [canonArgument_of_notLambda (canonical := canonWith block (spare + 1))
              (fun _ inert => canonWith_inert (spare + 1) inert) (by simp [OneHoleContext.fill]),
            canonArgument_of_notLambda (canonical := canonWith block (spare + 1))
              (fun _ inert => canonWith_inert (spare + 1) inert) (by simp [OneHoleContext.fill])]
          exact undetected_canon inner (by simp only [frames]; omega) pair (by simp [frames] at enough ⊢; omega) middleObject
  | lambda binder body =>
      simp only [OneHoleContext.fill, canonComponentWith]
      congr 1
      exact undetected_canon inner (by simp only [frames]; omega) pair (by simp [frames] at enough ⊢; omega)
        (by simpa [OneHoleContext.fill, isObjectPattern] using object)
  | multiLambda arity binders body =>
      simp only [OneHoleContext.fill, canonComponentWith]
      congr 1
      exact undetected_canon inner (by simp only [frames]; omega) pair (by simp [frames] at enough ⊢; omega)
        (by simpa [OneHoleContext.fill, isObjectPattern] using object)
  | substBody body replacement => simp [OneHoleContext.fill, isObjectPattern] at object
  | substReplacement body replacement => simp [OneHoleContext.fill, isObjectPattern] at object
  | collection kind before middle after rest =>
      simp only [OneHoleContext.fill, canonComponentWith, List.map_append, List.map_cons]
      congr 3
      exact undetected_canon inner (by simp only [frames]; omega) pair (by simp [frames] at enough ⊢; omega)
        (isObject_collection_member object)

/-- Single components alike give similar atoms. -/
theorem Similar.of_alike {fuel : Nat} {first second : Pattern} (alike : Alike block fuel first second) :
    Similar block fuel (Prenex.atom first) (Prenex.atom second) :=
  ⟨rfl, [], [second], List.Perm.refl _, by
    simpa only [Prenex.atom, List.map_cons, List.map_nil, inert_rename_id] using List.Forall₂.cons alike .nil,
    .refl _⟩

/-- **Inside a frame, interchangeable fillings give alike components.** -/
theorem component_alike {context : OneHoleContext} (notHole : 0 < frames context)
    (inner : Undetected block (frames context)) {first second : Pattern} (pair : Interchangeable block first second) {fuel : Nat}
    (enough : 2 * frames context ≤ fuel) (object : isObjectPattern (context.fill first) = true) :
    Alike block fuel (context.fill first) (context.fill second) := by
  refine ⟨freeIn_fill_congr pair.free context, isObject_fill_congr pair.object context, fun relabel => ?_⟩
  rw [ContextRenaming.rename_fill, ContextRenaming.rename_fill]
  refine component_canon (by rwa [ContextRenaming.frames_rename]) (by rwa [ContextRenaming.frames_rename])
    (pair.rename _) (by rwa [ContextRenaming.frames_rename]) ?_
  rw [← ContextRenaming.rename_fill, isObjectPattern_rename]
  exact object

/-- A frame read into the block: a restriction, a place in a bag, or the argument of a multiset whose empty instance
is the unit. -/
def BlockFrame (block : Block) (context : OneHoleContext) : Prop :=
  (∃ binder inner, context = .apply block.restrict [] (.lambda binder inner) []) ∨
    (∃ before inner after, context = .collection .hashBag before inner after none) ∨
    ∃ label inner, label ∈ block.emptyUnits ∧ context = .apply label [] inner []

theorem append_cons_eq_singleton {α : Type} {before after : List α} {middle single : α}
    (equal : before ++ middle :: after = [single]) : before = [] ∧ after = [] ∧ middle = single := by
  cases before with
  | nil =>
      simp only [List.nil_append, List.cons.injEq] at equal
      exact ⟨rfl, equal.2, equal.1⟩
  | cons head tail => simp at equal

/-- A filled frame that the block does not read is one component. -/
theorem decompose_fill_atom {context : OneHoleContext} (notHole : 0 < frames context) (notBlock : ¬ BlockFrame block context)
    {filling : Pattern} (notLambda : ∀ binder body, filling ≠ .lambda binder body) :
    decompose block (context.fill filling) = Prenex.atom (context.fill filling) := by
  apply decompose_atom
  · intro equal
    cases context with
    | hole => simp [frames] at notHole
    | apply constructor before inner after =>
        simp only [OneHoleContext.fill, Pattern.apply.injEq] at equal
        exact absurd equal.2 (by simp)
    | _ => simp [OneHoleContext.fill] at equal
  · intro binder body equal
    cases context with
    | hole => simp [frames] at notHole
    | apply constructor before inner after =>
        simp only [OneHoleContext.fill, Pattern.apply.injEq] at equal
        obtain ⟨rfl, listEq⟩ := equal
        obtain ⟨rfl, rfl, filled⟩ := append_cons_eq_singleton listEq
        rcases fill_eq_lambda filled with ⟨rfl, isLambda⟩ | ⟨inner', rfl⟩
        · exact notLambda _ _ isLambda
        · exact notBlock (.inl ⟨binder, inner', rfl⟩)
    | _ => simp [OneHoleContext.fill] at equal
  · intro elements equal
    cases context with
    | hole => simp [frames] at notHole
    | collection kind before inner after rest =>
        simp only [OneHoleContext.fill, Pattern.collection.injEq] at equal
        obtain ⟨rfl, -, rfl⟩ := equal
        exact notBlock (.inr (.inl ⟨before, inner, after, rfl⟩))
    | _ => simp [OneHoleContext.fill] at equal
  · intro label argument equal listed
    cases context with
    | hole => simp [frames] at notHole
    | apply constructor before inner after =>
        simp only [OneHoleContext.fill, Pattern.apply.injEq] at equal
        obtain ⟨rfl, listEq⟩ := equal
        obtain ⟨rfl, rfl, -⟩ := append_cons_eq_singleton listEq
        exact notBlock (.inr (.inr ⟨constructor, inner, listed, rfl⟩))
    | _ => simp [OneHoleContext.fill] at equal

include laws in
/-- **One step of the induction over contexts.** -/
theorem context_similar_step {context : OneHoleContext} (inner : Undetected block (frames context))
    {first second : Pattern} (pair : Interchangeable block first second) {fuel : Nat} (enough : 2 * frames context ≤ fuel)
    (object : isObjectPattern (context.fill first) = true) :
    Similar block fuel (decompose block (context.fill first)) (decompose block (context.fill second)) := by
  by_cases notHole : frames context = 0
  · cases context <;> simp [frames] at notHole
    exact pair.similar fuel
  have positive : 0 < frames context := by omega
  by_cases framed : BlockFrame block context
  · rcases framed with ⟨binder, inner', rfl⟩ | ⟨before, inner', after, rfl⟩ | ⟨label, inner', listed, rfl⟩
    · simp only [OneHoleContext.fill, List.nil_append]
      rw [decompose_restrict, decompose_restrict]
      exact (inner inner' (by simp only [frames]; omega) pair fuel (by simp [frames] at enough; omega)
        (by simpa [OneHoleContext.fill, isObjectPattern, isObjectPatternList] using object)).close
    · simp only [OneHoleContext.fill]
      rw [decompose_bag, decompose_bag, decomposeList_append, decomposeList_append, decomposeList, decomposeList]
      exact ((inner inner' (by simp only [frames]; omega) pair fuel (by simp [frames] at enough; omega)
        (isObject_collection_member object)).par_left _).par_right _
    · have notRestriction : ∀ argument binder body,
          Pattern.apply label [argument] ≠ .apply block.restrict [.lambda binder body] := by
        intro argument binder body equal
        simp only [Pattern.apply.injEq] at equal
        exact laws.restrict_not_emptyUnit (equal.1 ▸ listed)
      have filledIs : ∀ filling, OneHoleContext.fill (.apply label [] inner' []) filling =
          .apply label [inner'.fill filling] := fun filling => by simp [OneHoleContext.fill]
      have middleSimilar := inner inner' (by simp only [frames]; omega) pair fuel (by simp [frames] at enough; omega)
        (by simpa [OneHoleContext.fill, isObjectPattern, isObjectPatternList] using object)
      by_cases firstEmpty : decompose block (inner'.fill first) = Prenex.nil
      · have secondEmpty := middleSimilar.eq_nil firstEmpty
        rw [filledIs, filledIs, decompose_multiset (notRestriction _), decompose_multiset (notRestriction _),
          if_pos ⟨listed, firstEmpty⟩, if_pos ⟨listed, secondEmpty⟩]
        exact Similar.refl fuel _
      · have secondNotEmpty : decompose block (inner'.fill second) ≠ Prenex.nil := fun secondEmpty =>
          firstEmpty (middleSimilar.symm.eq_nil secondEmpty)
        have atoms := Similar.of_alike (component_alike positive inner pair enough object)
        rw [filledIs, filledIs] at atoms ⊢
        rw [decompose_multiset (notRestriction _), decompose_multiset (notRestriction _),
          if_neg (fun both => firstEmpty both.2), if_neg (fun both => secondNotEmpty both.2)]
        exact atoms
  · rw [decompose_fill_atom positive framed pair.firstNotLambda, decompose_fill_atom positive framed pair.secondNotLambda]
    exact Similar.of_alike (component_alike positive inner pair enough object)

include laws in
/-- **No context tells interchangeable fillings apart.** -/
theorem context_similar : ∀ (bound : Nat), Undetected block bound := by
  intro bound
  induction bound with
  | zero => intro context fewer; omega
  | succ bound recurse =>
      intro context fewer first second pair fuel enough object
      exact context_similar_step (language := language) (fun context' fewer' => recurse context' (by omega)) pair enough object

/-! ## Enough fuel -/

theorem sizeList_eq_sum : ∀ (patterns : List Pattern), sizeList patterns = (patterns.map size).sum
  | [] => rfl
  | pattern :: patterns => by simp [sizeList, sizeList_eq_sum patterns]

theorem size_pos : ∀ (pattern : Pattern), 0 < size pattern := by
  intro pattern
  cases pattern <;> simp [size]

theorem size_lt_of_mem {pattern : Pattern} {patterns : List Pattern} (member : pattern ∈ patterns) :
    size pattern ≤ sizeList patterns := by
  rw [sizeList_eq_sum]
  exact List.le_sum_of_mem (List.mem_map_of_mem member)

/-- **A renaming keeps the size.** -/
theorem size_rename (pattern : Pattern) : ∀ (relabel : Nat → Nat), size (rename relabel pattern) = size pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro _; rfl
  | hfvar name => intro _; rfl
  | happly constructor arguments recurse =>
      intro relabel
      simp only [rename_apply, size, sizeList_eq_sum, List.map_map]
      congr 2
      exact List.map_congr_left fun argument member => recurse argument member relabel
  | hlambda binder body recurse => intro relabel; simp only [rename_lambda, size, recurse]
  | hmultiLambda arity binders body recurse => intro relabel; simp only [rename_multiLambda, size, recurse]
  | hsubst body replacement bodyRecurse replacementRecurse =>
      intro relabel
      simp only [rename_subst, size, bodyRecurse, replacementRecurse]
  | hcollection kind elements rest recurse =>
      intro relabel
      simp only [rename_collection, size, sizeList_eq_sum, List.map_map]
      congr 2
      exact List.map_congr_left fun element member => recurse element member relabel

theorem close_components_size {form : Prenex} {bound : Nat} (small : ∀ component ∈ form.components, size component ≤ bound) :
    ∀ component ∈ form.close.components, size component ≤ bound := by
  obtain ⟨count, components⟩ := form
  simp only [Prenex.close]
  split_ifs
  · exact small
  · intro component member
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    rw [size_rename]
    exact small original originalMember

mutual
  /-- **A block's components are no larger than the process.** -/
  theorem decompose_size (pattern : Pattern) : ∀ component ∈ (decompose block pattern).components, size component ≤ size pattern := by
    by_cases isNil : pattern = .apply block.unit []
    · subst isNil
      simp [decompose_unit, Prenex.nil]
    by_cases isRestriction : ∃ binder body, pattern = .apply block.restrict [.lambda binder body]
    · obtain ⟨binder, body, rfl⟩ := isRestriction
      rw [decompose_restrict]
      refine close_components_size fun component member => ?_
      have := decompose_size body component member
      simp only [size, sizeList]
      omega
    by_cases isBag : ∃ elements, pattern = .collection .hashBag elements none
    · obtain ⟨elements, rfl⟩ := isBag
      rw [decompose_bag]
      intro component member
      have := decomposeList_size elements component member
      simp only [size]
      omega
    by_cases isEmptyCandidate : ∃ label argument, pattern = .apply label [argument] ∧ label ∈ block.emptyUnits
    · obtain ⟨label, argument, rfl, listed⟩ := isEmptyCandidate
      rw [decompose_multiset (fun binder body equal => isRestriction ⟨binder, body, equal⟩)]
      split_ifs
      · simp [Prenex.nil]
      · intro component member
        simp only [Prenex.atom, List.mem_singleton] at member
        rw [member]
    rw [decompose_atom isNil (fun binder body equal => isRestriction ⟨binder, body, equal⟩)
      (fun elements equal => isBag ⟨elements, equal⟩)
      (fun label argument equal listed => isEmptyCandidate ⟨label, argument, equal, listed⟩)]
    intro component member
    simp only [Prenex.atom, List.mem_singleton] at member
    rw [member]
  termination_by sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  theorem decomposeList_size (elements : List Pattern) :
      ∀ component ∈ (decomposeList block elements).components, size component ≤ sizeList elements := by
    match elements with
    | [] => simp [decomposeList, Prenex.nil]
    | element :: elements =>
        intro component member
        simp only [decomposeList, Prenex.par, List.mem_append, List.mem_map] at member
        simp only [sizeList]
        rcases member with ⟨original, originalMember, rfl⟩ | ⟨original, originalMember, rfl⟩
        · rw [liftBVars_eq_rename, size_rename]
          have := decompose_size element original originalMember
          omega
        · rw [liftBVars_eq_rename, size_rename]
          have := decomposeList_size elements original originalMember
          omega
  termination_by sizeOf elements
  decreasing_by all_goals sizeOf_pattern_dec
end

/-- A filled context has at least one node per frame. -/
theorem frames_le_size : ∀ (context : OneHoleContext) (filling : Pattern), frames context < size (context.fill filling)
  | .hole, filling => by simpa [frames] using size_pos filling
  | .apply _ before inner after, filling => by
      have := frames_le_size inner filling
      have member := size_lt_of_mem (pattern := inner.fill filling) (patterns := before ++ inner.fill filling :: after)
        (by simp)
      simp only [frames, OneHoleContext.fill, size]
      omega
  | .lambda _ inner, filling => by
      have := frames_le_size inner filling
      simp only [frames, OneHoleContext.fill, size]
      omega
  | .multiLambda _ _ inner, filling => by
      have := frames_le_size inner filling
      simp only [frames, OneHoleContext.fill, size]
      omega
  | .substBody inner _, filling => by
      have := frames_le_size inner filling
      simp only [frames, OneHoleContext.fill, size]
      omega
  | .substReplacement _ inner, filling => by
      have := frames_le_size inner filling
      simp only [frames, OneHoleContext.fill, size]
      omega
  | .collection _ before inner after _, filling => by
      have := frames_le_size inner filling
      have member := size_lt_of_mem (pattern := inner.fill filling) (patterns := before ++ inner.fill filling :: after)
        (by simp)
      simp only [frames, OneHoleContext.fill, size]
      omega

/-- **Enough fuel settles the canonical form**: twice the size suffices for a process, and one less for a
component. -/
theorem fuel_settles : ∀ (bound : Nat),
    (∀ component, size component ≤ bound → ∀ first second, 2 * size component ≤ first + 1 →
      2 * size component ≤ second + 1 → canonComponentWith block first component = canonComponentWith block second component) ∧
    (∀ pattern, size pattern ≤ bound → ∀ first second, 2 * size pattern ≤ first → 2 * size pattern ≤ second →
      canonWith block first pattern = canonWith block second pattern) := by
  intro bound
  induction bound with
  | zero =>
      refine ⟨fun component small => absurd small (by have := size_pos component; omega),
        fun pattern small => absurd small (by have := size_pos pattern; omega)⟩
  | succ bound recurse =>
      obtain ⟨componentsSmaller, smaller⟩ := recurse
      have multisetSettles : ∀ argument, size argument ≤ bound → ∀ first second, 2 * size argument ≤ first →
          2 * size argument ≤ second → canonMultisetWith block first argument = canonMultisetWith block second argument := by
        intro argument small first second enough enough'
        have positive := size_pos argument
        obtain ⟨first, rfl⟩ : ∃ spare, first = spare + 1 := ⟨first - 1, by omega⟩
        obtain ⟨second, rfl⟩ : ∃ spare, second = spare + 1 := ⟨second - 1, by omega⟩
        have general : ∀ (fuel : Nat), (∀ kind elements rest, argument ≠ .collection kind elements (some rest)) →
            (∀ body replacement, argument ≠ .subst body replacement) →
            canonMultisetWith block (fuel + 1) argument =
              multisetOf block ⟨(decompose block argument).count,
                least (readings block fuel (decompose block argument))⟩ := by
          intro fuel notOpen notSubst
          cases argument with
          | collection kind elements rest =>
              cases rest with
              | some name => exact absurd rfl (notOpen kind elements name)
              | none => simp only [canonMultisetWith, readings]
          | subst body replacement => exact absurd rfl (notSubst body replacement)
          | _ => simp only [canonMultisetWith, readings]
        by_cases isOpen : ∃ kind elements rest, argument = .collection kind elements (some rest)
        · obtain ⟨kind, elements, rest, rfl⟩ := isOpen
          simp only [canonMultisetWith]
          congr 1
          refine List.map_congr_left fun element member => ?_
          have elementSmall := size_lt_of_mem member
          simp only [size] at small enough enough'
          exact smaller element (by omega) first second (by omega) (by omega)
        by_cases isSubst : ∃ body replacement, argument = .subst body replacement
        · obtain ⟨body, replacement, rfl⟩ := isSubst
          rfl
        have notOpen : ∀ kind elements rest, argument ≠ .collection kind elements (some rest) :=
          fun kind elements rest equal => isOpen ⟨kind, elements, rest, equal⟩
        have notSubst : ∀ body replacement, argument ≠ .subst body replacement :=
          fun body replacement equal => isSubst ⟨body, replacement, equal⟩
        rw [general first notOpen notSubst, general second notOpen notSubst]
        congr 3
        simp only [readings]
        refine List.map_congr_left fun order _ => ?_
        congr 1
        refine List.map_congr_left fun component member => ?_
        have componentSmall := decompose_size argument component member
        exact componentsSmaller _ (by rw [size_rename]; omega) first second (by rw [size_rename]; omega)
          (by rw [size_rename]; omega)
      have components : ∀ component, size component ≤ bound + 1 → ∀ first second, 2 * size component ≤ first + 1 →
          2 * size component ≤ second + 1 → canonComponentWith block first component = canonComponentWith block second component := by
        intro component small first second enough enough'
        have positive := size_pos component
        obtain ⟨first, rfl⟩ : ∃ spare, first = spare + 1 := ⟨first - 1, by omega⟩
        obtain ⟨second, rfl⟩ : ∃ spare, second = spare + 1 := ⟨second - 1, by omega⟩
        cases component with
        | bvar => rfl
        | fvar => rfl
        | subst => rfl
        | apply constructor arguments =>
            by_cases isMultiset : constructor ∈ block.multisets
            · simp only [canonComponentWith, if_pos isMultiset]
              congr 1
              refine List.map_congr_left fun argument member => ?_
              have argumentSmall := size_lt_of_mem member
              simp only [size] at small enough enough'
              exact multisetSettles argument (by omega) first second (by omega) (by omega)
            simp only [canonComponentWith, if_neg isMultiset]
            congr 1
            refine List.map_congr_left fun argument member => ?_
            have argumentSmall := size_lt_of_mem member
            simp only [size] at small enough enough'
            cases argument with
            | lambda binder body =>
                simp only [canonArgument]
                congr 1
                simp only [size] at argumentSmall
                exact smaller body (by omega) first second (by omega) (by omega)
            | bvar => rfl
            | fvar => rfl
            | subst => rfl
            | apply _ _ => exact smaller _ (by omega) first second (by omega) (by omega)
            | multiLambda _ _ _ => exact smaller _ (by omega) first second (by omega) (by omega)
            | collection _ _ _ => exact smaller _ (by omega) first second (by omega) (by omega)
        | lambda binder body =>
            simp only [canonComponentWith]
            simp only [size] at small enough enough'
            congr 1
            exact smaller body (by omega) first second (by omega) (by omega)
        | multiLambda arity binders body =>
            simp only [canonComponentWith]
            simp only [size] at small enough enough'
            congr 1
            exact smaller body (by omega) first second (by omega) (by omega)
        | collection kind elements rest =>
            simp only [canonComponentWith]
            congr 1
            refine List.map_congr_left fun element member => ?_
            have elementSmall := size_lt_of_mem member
            simp only [size] at small enough enough'
            exact smaller element (by omega) first second (by omega) (by omega)
      refine ⟨components, fun pattern small first second enough enough' => ?_⟩
      have positive := size_pos pattern
      obtain ⟨first, rfl⟩ : ∃ spare, first = spare + 1 := ⟨first - 1, by omega⟩
      obtain ⟨second, rfl⟩ : ∃ spare, second = spare + 1 := ⟨second - 1, by omega⟩
      rw [canonWith_succ, canonWith_succ]
      congr 3
      simp only [readings]
      refine List.map_congr_left fun order _ => ?_
      congr 1
      refine List.map_congr_left fun component member => ?_
      have componentSmall := decompose_size pattern component member
      exact components _ (by rw [size_rename]; omega) first second (by rw [size_rename]; omega)
        (by rw [size_rename]; omega)

theorem canon_eq_canonWith {pattern : Pattern} {fuel : Nat} (enough : 2 * size pattern + 2 ≤ fuel) :
    canon block pattern = canonWith block fuel pattern :=
  (fuel_settles (size pattern)).2 pattern (Nat.le_refl _) _ _ (by omega) (by omega)

/-! ## Completeness -/

open Mettapedia.GSLT.LanguageDef.EquationSemantics (EquationContextStep EquationEquiv)

/-- One step of the static theory on an object pattern keeps the canonical form. -/
theorem step_canon {base : BasePremiseEvaluator} {first second : Pattern}
    (step : EquationContextStep base language first second) (object : isObjectPattern first = true) :
    canon block first = canon block second := by
  cases step with
  | @inContext context redex contractum generator =>
      have pair := generator_interchangeable (block := block) generator
      have fewer := frames_le_size context redex
      have bigger := le_max_left (2 * size (context.fill redex) + 2) (2 * size (context.fill contractum) + 2)
      have bigger' := le_max_right (2 * size (context.fill redex) + 2) (2 * size (context.fill contractum) + 2)
      generalize max (2 * size (context.fill redex) + 2) (2 * size (context.fill contractum) + 2) = fuel
        at bigger bigger'
      obtain ⟨spare, rfl⟩ : ∃ spare, fuel = spare + 1 := ⟨fuel - 1, by omega⟩
      rw [canon_eq_canonWith bigger, canon_eq_canonWith bigger']
      exact canonWith_eq_of_similar
        (context_similar (language := language) (frames context + 1) context (by omega) pair spare (by omega) object)

include laws in
/-- the static theory relates object patterns only to object patterns. -/
theorem equationEquiv_isObject {base : BasePremiseEvaluator} {first second : Pattern}
    (equivalent : EquationEquiv base language first second) : isObjectPattern first = isObjectPattern second := by
  induction equivalent with
  | rel _ _ step =>
      cases step with
      | inContext context generator => exact isObject_fill_congr (generator_interchangeable (block := block) generator).object context
  | refl => rfl
  | symm _ _ _ recurse => exact recurse.symm
  | trans _ _ _ _ _ first second => exact first.trans second

/-- **the canonical form is complete**: object patterns equivalent under `language`'s static theory have one
canonical form. -/
theorem canon_complete {base : BasePremiseEvaluator} {first second : Pattern}
    (object : isObjectPattern first = true) (equivalent : EquationEquiv base language first second) :
    canon block first = canon block second := by
  revert object
  induction equivalent with
  | rel _ _ step => exact step_canon step
  | refl => intro _; rfl
  | symm _ _ relation recurse =>
      intro object
      exact (recurse (by rw [equationEquiv_isObject (block := block) relation]; exact object)).symm
  | trans _ _ _ relation _ first second =>
      intro object
      exact (first object).trans (second (by rw [← equationEquiv_isObject (block := block) relation]; exact object))

open Mettapedia.GSLT.LanguageDef.WellSorted (HasType FreeTypeContext)
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (engineBasePremises)

/-- Typed terms with one canonical form are related by a chain through terms of their sort. -/
theorem sortedEquiv_of_canon_eq {free : FreeTypeContext} {bound : List TypeExpr} (context : BaseContext free bound)
    {first second : Pattern} {sort : String} (firstTyped : HasType language free bound first (.base sort))
    (secondTyped : HasType language free bound second (.base sort)) (equal : canon block first = canon block second) :
    SortedEquiv language free bound (.base sort) first second := by
  have firstChain := (canon_sound (block := block) context firstTyped).2
  have secondChain := (canon_sound (block := block) context secondTyped).2
  rw [equal] at firstChain
  exact .trans _ _ _ firstChain (.symm _ _ secondChain)

/-- **The static theory is decided by the canonical form** on object terms of a sort. -/
theorem equationEquiv_iff_canon_eq {free : FreeTypeContext} {bound : List TypeExpr} (context : BaseContext free bound)
    {first second : Pattern} {sort : String} (firstTyped : HasType language free bound first (.base sort))
    (secondTyped : HasType language free bound second (.base sort)) (object : isObjectPattern first = true) :
    EquationEquiv (engineBasePremises RelationEnv.empty) language first second ↔
      canon block first = canon block second :=
  ⟨canon_complete object, fun equal => (sortedEquiv_of_canon_eq context firstTyped secondTyped equal).toEquationEquiv⟩

include laws in
/-- **Equivalent object terms of a sort are related by a chain of laws through terms of that sort.** -/
theorem sortedEquiv_of_equationEquiv {free : FreeTypeContext} {bound : List TypeExpr} (context : BaseContext free bound)
    {first second : Pattern} {sort : String} (firstTyped : HasType language free bound first (.base sort))
    (secondTyped : HasType language free bound second (.base sort)) (object : isObjectPattern first = true)
    {base : BasePremiseEvaluator} (equivalent : EquationEquiv base language first second) :
    SortedEquiv language free bound (.base sort) first second :=
  sortedEquiv_of_canon_eq context firstTyped secondTyped (canon_complete (block := block) object equivalent)

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks
