import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationSettle

/-!
# The orders a block is read under

The canonical form reads a block under orders of its restrictions and keeps the least reading (`readingOrders`).
An unrefined block is read under every order. A refined block is read only under the orders that sort its
restrictions by their signatures (`signatureOf`: the profiles of the components that mention a restriction, each
counted once), restrictions of one signature in every order among themselves. The signature is read off the block
without any order, so these orders are carried along by a renaming:

- **The orders sorting by a key** (`mem_keyedArrangements`, `mem_readingOrders_refined`): the arrangements whose keys
  never decrease are exactly the permutations sorted by the key, and their inverses are exactly the orders under which
  a smaller key comes first.
- **Reading orders are orders** (`readingOrders_isOrder`), there is one (`readingOrders_ne_nil`), and a block without
  restrictions has only the empty one (`readingOrders_zero`).
- **Signatures** depend only on which components a block has (`signatureOf_congr`), are kept by components that
  mention the same restrictions and are replications alike (`signatureOf_forall₂`, `signatureOf_map`), and are
  carried along by renaming the restrictions (`signatureOf_rename`).
- **Transport** (`readingOrders_transport`, `readingOrders_transport_inverse`): when one block's signatures are the
  other's carried along an order, the reading orders of one composed with that order are reading orders of the other.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (FreeIn)

variable {block : ReplicationBlock}

/-! ## Arrangements whose keys never decrease -/

theorem foldr_min_le {key : Nat → Nat} : ∀ (rest : List Nat) (start : Nat),
    rest.foldr (fun other low => min (key other) low) start ≤ start ∧
      ∀ element ∈ rest, rest.foldr (fun other low => min (key other) low) start ≤ key element
  | [], start => ⟨le_refl _, by simp⟩
  | head :: tail, start => by
      obtain ⟨leStart, leElements⟩ := foldr_min_le tail start
      simp only [List.foldr_cons]
      refine ⟨(min_le_right _ _).trans leStart, fun element member => ?_⟩
      rcases List.mem_cons.mp member with rfl | later
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (leElements element later)

theorem foldr_min_mem {key : Nat → Nat} : ∀ (rest : List Nat) (start : Nat),
    rest.foldr (fun other low => min (key other) low) start = start ∨
      ∃ element ∈ rest, rest.foldr (fun other low => min (key other) low) start = key element
  | [], start => .inl rfl
  | head :: tail, start => by
      simp only [List.foldr_cons]
      rcases foldr_min_mem tail start with same | ⟨element, member, same⟩
      · rw [same]
        rcases Nat.le_total (key head) start with le | ge
        · exact .inr ⟨head, List.mem_cons_self, Nat.min_eq_left le⟩
        · exact .inl (Nat.min_eq_right ge)
      · rw [same]
        rcases Nat.le_total (key head) (key element) with le | ge
        · exact .inr ⟨head, List.mem_cons_self, Nat.min_eq_left le⟩
        · exact .inr ⟨element, List.mem_cons_of_mem _ member, Nat.min_eq_right ge⟩

/-- **The least key of a nonempty list** is at most every key and is some element's key. -/
theorem lowest_spec {key : Nat → Nat} (first : Nat) (rest : List Nat) :
    (∀ element ∈ first :: rest, rest.foldr (fun other low => min (key other) low) (key first) ≤ key element) ∧
      ∃ element ∈ first :: rest, key element = rest.foldr (fun other low => min (key other) low) (key first) := by
  obtain ⟨leStart, leRest⟩ := foldr_min_le (key := key) rest (key first)
  refine ⟨fun element member => ?_, ?_⟩
  · rcases List.mem_cons.mp member with rfl | later
    · exact leStart
    · exact leRest element later
  · rcases foldr_min_mem (key := key) rest (key first) with same | ⟨element, member, same⟩
    · exact ⟨first, List.mem_cons_self, same.symm⟩
    · exact ⟨element, List.mem_cons_of_mem _ member, same.symm⟩

/-- **The arrangements whose keys never decrease** are exactly the permutations sorted by the key. -/
theorem mem_keyedArrangements {key : Nat → Nat} : ∀ (fuel : Nat) {elements : List Nat}, elements.Nodup →
    elements.length ≤ fuel → ∀ {arrangement : List Nat}, arrangement ∈ keyedArrangements key fuel elements ↔
      arrangement.Perm elements ∧ arrangement.Pairwise (fun first second => key first ≤ key second)
  | 0, elements, _, short, arrangement => by
      have empty : elements = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst empty
      simp only [keyedArrangements, List.mem_singleton, List.perm_nil]
      constructor
      · rintro rfl
        exact ⟨rfl, List.Pairwise.nil⟩
      · exact fun ⟨empty, _⟩ => empty
  | fuel + 1, [], _, _, arrangement => by
      simp only [keyedArrangements, List.mem_singleton, List.perm_nil]
      constructor
      · rintro rfl
        exact ⟨rfl, List.Pairwise.nil⟩
      · exact fun ⟨empty, _⟩ => empty
  | fuel + 1, first :: rest, nodup, short, arrangement => by
      obtain ⟨lowestLe, lowestAt⟩ := lowest_spec (key := key) first rest
      have erasedShort : ∀ chosen ∈ first :: rest, ((first :: rest).erase chosen).length ≤ fuel := by
        intro chosen member
        rw [List.length_erase_of_mem member]
        simp only [List.length_cons] at short ⊢
        omega
      simp only [keyedArrangements]
      constructor
      · intro member
        obtain ⟨chosen, chosenIn, inner⟩ := List.mem_flatMap.mp member
        obtain ⟨tail, tailIn, rfl⟩ := List.mem_map.mp inner
        obtain ⟨chosenMember, chosenLowest⟩ := List.mem_filter.mp chosenIn
        obtain ⟨tailPerm, tailSorted⟩ :=
          (mem_keyedArrangements fuel (nodup.erase chosen) (erasedShort chosen chosenMember)).mp tailIn
        refine ⟨(tailPerm.cons chosen).trans (List.perm_cons_erase chosenMember).symm,
          List.Pairwise.cons (fun other otherIn => ?_) tailSorted⟩
        rw [of_decide_eq_true chosenLowest]
        exact lowestLe other (List.mem_of_mem_erase (tailPerm.subset otherIn))
      · rintro ⟨perm, sorted⟩
        match arrangement, perm, sorted with
        | [], perm, _ => exact absurd perm.length_eq (by simp)
        | chosen :: tail, perm, sorted =>
            have chosenMember : chosen ∈ first :: rest := perm.subset List.mem_cons_self
            have tailPerm : tail.Perm ((first :: rest).erase chosen) :=
              (List.perm_cons chosen).mp (perm.trans (List.perm_cons_erase chosenMember))
            obtain ⟨lowElement, lowIn, lowKey⟩ := lowestAt
            have chosenLowest : key chosen = rest.foldr (fun other low => min (key other) low) (key first) := by
              apply le_antisymm
              · rcases List.mem_cons.mp (perm.symm.subset lowIn) with same | inTail
                · rw [← same, lowKey]
                · rw [← lowKey]
                  exact List.rel_of_pairwise_cons sorted inTail
              · exact lowestLe chosen chosenMember
            refine List.mem_flatMap.mpr ⟨chosen, List.mem_filter.mpr ⟨chosenMember, decide_eq_true chosenLowest⟩,
              List.mem_map.mpr ⟨tail, ?_, rfl⟩⟩
            exact (mem_keyedArrangements fuel (nodup.erase chosen) (erasedShort chosen chosenMember)).mpr
              ⟨tailPerm, sorted.of_cons⟩

theorem keyedArrangements_ne_nil {key : Nat → Nat} : ∀ (fuel : Nat) (elements : List Nat),
    keyedArrangements key fuel elements ≠ []
  | 0, _ => by simp [keyedArrangements]
  | _ + 1, [] => by simp [keyedArrangements]
  | fuel + 1, first :: rest => by
      obtain ⟨-, low, lowIn, lowKey⟩ := lowest_spec (key := key) first rest
      simp only [keyedArrangements, ne_eq, List.flatMap_eq_nil_iff, not_forall]
      refine ⟨low, List.mem_filter.mpr ⟨lowIn, decide_eq_true lowKey⟩, ?_⟩
      simpa using keyedArrangements_ne_nil fuel ((first :: rest).erase low)

/-! ## Orders -/

/-- **Reading through an order is injective.** -/
theorem permute_injective {count : Nat} {order : List Nat} (isOrder : IsOrder count order) :
    Function.Injective (Prenex.permute count order) := by
  intro first second same
  have undoneFirst := congrFun (permute_inverse isOrder) first
  have undoneSecond := congrFun (permute_inverse isOrder) second
  simp only [Function.comp, id] at undoneFirst undoneSecond
  rw [← undoneFirst, ← undoneSecond, same]

/-- **Undoing the undoing of an order** gives the order back. -/
theorem inverse_inverse {count : Nat} {order : List Nat} (isOrder : IsOrder count order) :
    inverse count (inverse count order) = order := by
  have length := isOrder.length
  have inverseOrder := inverse_isOrder isOrder
  have inverseLength := inverseOrder.length
  apply List.ext_getElem
  · simp [inverse, length]
  · intro position first second
    have inside : position < count := by simpa [inverse] using first
    have valueInside : order[position] < count := isOrder.getElem_lt _
    have atValue : (inverse count order)[order[position]]'(by omega) = position := by
      simp only [inverse, List.getElem_map, List.getElem_range]
      exact isOrder.nodup.idxOf_getElem _ _
    simp only [inverse, List.getElem_map, List.getElem_range]
    conv_lhs => rw [← atValue]
    exact inverseOrder.nodup.idxOf_getElem _ _

/-- **An order and its undoing undo each other** both ways. -/
theorem permute_inverse_right {count : Nat} {order : List Nat} (isOrder : IsOrder count order) :
    Prenex.permute count order ∘ Prenex.permute count (inverse count order) = id := by
  have undone := permute_inverse (inverse_isOrder isOrder)
  rwa [inverse_inverse isOrder] at undone

/-- **An order sorts by a key**: a restriction of smaller key comes first. -/
def SortsBy (key : Nat → Nat) (count : Nat) (order : List Nat) : Prop :=
  ∀ first < count, ∀ second < count, key first < key second →
    Prenex.permute count order first < Prenex.permute count order second

/-- **The orders of a refined block** are exactly the orders sorting by the signatures. -/
theorem mem_readingOrders_refined (refined : block.refined = true) {form : Prenex} {order : List Nat} :
    order ∈ readingOrders block form ↔ IsOrder form.count order ∧ SortsBy (signatureOf block form) form.count order := by
  unfold readingOrders
  rw [if_pos refined]
  have spec := fun arrangement =>
    (mem_keyedArrangements (key := signatureOf block form) form.count (elements := List.range form.count)
      List.nodup_range (by simp) (arrangement := arrangement))
  constructor
  · intro member
    obtain ⟨arrangement, inArrangements, rfl⟩ := List.mem_map.mp member
    obtain ⟨perm, sorted⟩ := (spec arrangement).mp inArrangements
    refine ⟨inverse_isOrder perm, fun first firstInside second secondInside smaller => ?_⟩
    rw [permute_of_lt (inverse_isOrder perm).length firstInside,
      permute_of_lt (inverse_isOrder perm).length secondInside]
    simp only [inverse, List.getElem_map, List.getElem_range]
    have firstIn : first ∈ arrangement := perm.symm.subset (List.mem_range.mpr firstInside)
    have secondIn : second ∈ arrangement := perm.symm.subset (List.mem_range.mpr secondInside)
    have firstAt := List.idxOf_lt_length_of_mem firstIn
    have secondAt := List.idxOf_lt_length_of_mem secondIn
    by_contra notBefore
    rcases Nat.lt_or_eq_of_le (Nat.le_of_not_lt notBefore) with before | same
    · have related := List.pairwise_iff_getElem.mp sorted _ _ secondAt firstAt before
      rw [List.getElem_idxOf secondAt, List.getElem_idxOf firstAt] at related
      omega
    · have equal : first = second := by
        have := congrArg (fun position => arrangement[position]?) same
        simp only [List.getElem?_idxOf secondIn, List.getElem?_idxOf firstIn, Option.some.injEq] at this
        exact this.symm
      subst equal
      omega
  · rintro ⟨isOrder, sorts⟩
    refine List.mem_map.mpr ⟨inverse form.count order, (spec _).mpr ⟨inverse_isOrder isOrder, ?_⟩,
      inverse_inverse isOrder⟩
    have inverseLength := (inverse_isOrder isOrder).length
    rw [List.pairwise_iff_getElem]
    intro firstPosition secondPosition firstInside secondInside before
    by_contra larger
    push Not at larger
    have firstInside' : firstPosition < form.count := by omega
    have secondInside' : secondPosition < form.count := by omega
    simp only [inverse, List.getElem_map, List.getElem_range] at larger
    have firstMember := isOrder.mem firstInside'
    have secondMember := isOrder.mem secondInside'
    have firstIndexInside : order.idxOf firstPosition < form.count :=
      isOrder.length ▸ List.idxOf_lt_length_of_mem firstMember
    have secondIndexInside : order.idxOf secondPosition < form.count :=
      isOrder.length ▸ List.idxOf_lt_length_of_mem secondMember
    have sorted := sorts _ secondIndexInside _ firstIndexInside larger
    rw [permute_of_lt isOrder.length secondIndexInside, permute_of_lt isOrder.length firstIndexInside,
      List.getElem_idxOf, List.getElem_idxOf] at sorted
    omega

/-! ## Reading orders -/

/-- **Reading orders are orders.** -/
theorem readingOrders_isOrder {form : Prenex} {order : List Nat} (member : order ∈ readingOrders block form) :
    IsOrder form.count order := by
  unfold readingOrders at member
  split_ifs at member
  · obtain ⟨arrangement, inArrangements, rfl⟩ := List.mem_map.mp member
    exact inverse_isOrder ((mem_keyedArrangements _ List.nodup_range (by simp)).mp inArrangements).1
  · exact orders_perm _ order member

/-- **A block has a reading order.** -/
theorem readingOrders_ne_nil (form : Prenex) : readingOrders block form ≠ [] := by
  unfold readingOrders
  split_ifs
  · simpa using keyedArrangements_ne_nil (key := signatureOf block form) form.count (List.range form.count)
  · exact orders_ne_nil _

/-- **A block without restrictions is read under the empty order alone.** -/
theorem readingOrders_zero (components : List Pattern) : readingOrders block ⟨0, components⟩ = [[]] := by
  unfold readingOrders
  split_ifs <;> rfl

/-- Arrangements read only the keys of the elements arranged. -/
theorem keyedArrangements_congr {key key' : Nat → Nat} : ∀ (fuel : Nat) (elements : List Nat),
    (∀ element ∈ elements, key element = key' element) →
      keyedArrangements key fuel elements = keyedArrangements key' fuel elements
  | 0, _, _ => rfl
  | _ + 1, [], _ => rfl
  | fuel + 1, first :: rest, same => by
      simp only [keyedArrangements]
      have lowest : rest.foldr (fun other low => min (key other) low) (key first) =
          rest.foldr (fun other low => min (key' other) low) (key' first) := by
        have restSame : ∀ element ∈ rest, key element = key' element :=
          fun element member => same element (List.mem_cons_of_mem _ member)
        rw [same first List.mem_cons_self]
        clear same
        induction rest with
        | nil => rfl
        | cons head tail recurse =>
            simp only [List.foldr_cons]
            rw [restSame head List.mem_cons_self, recurse fun element member =>
              restSame element (List.mem_cons_of_mem _ member)]
      rw [lowest]
      have filtered : ((first :: rest).filter fun element =>
            key element = rest.foldr (fun other low => min (key' other) low) (key' first)) =
          (first :: rest).filter fun element =>
            key' element = rest.foldr (fun other low => min (key' other) low) (key' first) :=
        List.filter_congr fun element member => by rw [same element member]
      rw [filtered]
      refine List.flatMap_congr fun chosen _ => ?_
      rw [keyedArrangements_congr fuel _ fun element member => same element (List.mem_of_mem_erase member)]

/-- **Blocks with the same number of restrictions and the same signatures at them have the same reading
orders.** -/
theorem readingOrders_congr {first second : Prenex} (sameCount : first.count = second.count)
    (signatures : ∀ index < first.count, signatureOf block first index = signatureOf block second index) :
    readingOrders block first = readingOrders block second := by
  unfold readingOrders
  split_ifs
  · rw [keyedArrangements_congr _ _ fun element member => signatures element (List.mem_range.mp member), sameCount]
  · rw [sameCount]

/-- **Reading orders carried along an order**: when the second block's signatures are the first's carried along an
order, a reading order of the second, composed with that order, is a reading order of the first. -/
theorem readingOrders_transport {first second : Prenex} {order outer : List Nat} (sameCount : first.count = second.count)
    (isOrder : IsOrder first.count order)
    (signatures : ∀ index < first.count,
      signatureOf block second (Prenex.permute first.count order index) = signatureOf block first index)
    (member : outer ∈ readingOrders block second) :
    order.map (Prenex.permute first.count outer) ∈ readingOrders block first := by
  have outerOrder : IsOrder first.count outer := sameCount ▸ readingOrders_isOrder member
  have composite := IsOrder.comp outerOrder isOrder
  cases refined : block.refined with
  | false =>
      unfold readingOrders
      rw [if_neg (by simp [refined])]
      exact orders_complete _ _ composite
  | true =>
      rw [mem_readingOrders_refined refined] at member ⊢
      refine ⟨composite, fun index indexInside other otherInside smaller => ?_⟩
      rw [← permute_comp outer isOrder]
      simp only [Function.comp]
      rw [← signatures index indexInside, ← signatures other otherInside] at smaller
      have sorted := member.2 _ (sameCount ▸ permute_lt isOrder indexInside) _
        (sameCount ▸ permute_lt isOrder otherInside) smaller
      rwa [← sameCount] at sorted

/-- **Reading orders carried back along an order**: when the second block's signatures are the first's carried along
an order, a reading order of the first, composed with the undoing of that order, is a reading order of the second. -/
theorem readingOrders_transport_inverse {first second : Prenex} {order outer : List Nat}
    (sameCount : first.count = second.count) (isOrder : IsOrder first.count order)
    (signatures : ∀ index < first.count,
      signatureOf block second (Prenex.permute first.count order index) = signatureOf block first index)
    (member : outer ∈ readingOrders block first) :
    (inverse first.count order).map (Prenex.permute first.count outer) ∈ readingOrders block second := by
  have outerOrder : IsOrder first.count outer := readingOrders_isOrder member
  have composite := IsOrder.comp outerOrder (inverse_isOrder isOrder)
  cases refined : block.refined with
  | false =>
      unfold readingOrders
      rw [if_neg (by simp [refined]), ← sameCount]
      exact orders_complete _ _ composite
  | true =>
      rw [mem_readingOrders_refined refined] at member ⊢
      rw [← sameCount]
      refine ⟨composite, fun index indexInside other otherInside smaller => ?_⟩
      rw [← permute_comp outer (inverse_isOrder isOrder)]
      simp only [Function.comp]
      have back : ∀ position, Prenex.permute first.count order (Prenex.permute first.count (inverse first.count order)
          position) = position := fun position => congrFun (permute_inverse_right isOrder) position
      have indexBack := permute_lt (inverse_isOrder isOrder) indexInside
      have otherBack := permute_lt (inverse_isOrder isOrder) otherInside
      rw [← back index, ← back other, signatures _ indexBack, signatures _ otherBack] at smaller
      exact member.2 _ indexBack _ otherBack smaller

/-! ## Signatures -/

/-- **Signatures depend only on which components a block has.** -/
theorem signatureOf_congr {first second : Prenex} (sameCount : first.count = second.count)
    (same : ∀ component, component ∈ first.components ↔ component ∈ second.components) (index : Nat) :
    signatureOf block first index = signatureOf block second index := by
  unfold signatureOf
  rw [sameCount]
  apply List.Perm.sum_eq
  apply List.Perm.map
  apply (List.perm_ext_iff_of_nodup (List.nodup_dedup _) (List.nodup_dedup _)).mpr
  intro code
  simp only [List.mem_dedup, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨component, ⟨member, mentioned⟩, rfl⟩
    exact ⟨component, ⟨(same component).mp member, mentioned⟩, rfl⟩
  · rintro ⟨component, ⟨member, mentioned⟩, rfl⟩
    exact ⟨component, ⟨(same component).mpr member, mentioned⟩, rfl⟩

/-- Components mentioning the same restrictions, replications alike, have one profile. -/
theorem profileCode_congr {count : Nat} {first second : Pattern}
    (mentionsSame : ∀ index < count, mentions index first = mentions index second)
    (replicatedSame : isReplicated block first = isReplicated block second) :
    profileCode block count first = profileCode block count second := by
  unfold profileCode
  rw [replicatedSame]
  congr 3
  exact List.filter_congr fun index member => mentionsSame index (List.mem_range.mp member)

/-- **Components related one for one, mentioning the same restrictions and replications alike, give the same
signatures.** -/
theorem signatureOf_forall₂ {count : Nat} {first second : List Pattern}
    (related : List.Forall₂ (fun one other => (∀ index < count, mentions index one = mentions index other) ∧
      isReplicated block one = isReplicated block other) first second) {index : Nat} (inside : index < count) :
    signatureOf block ⟨count, first⟩ index = signatureOf block ⟨count, second⟩ index := by
  unfold signatureOf
  congr 3
  simp only
  induction related with
  | nil => rfl
  | @cons one other firstRest secondRest here _ recurse =>
      simp only [List.filter_cons, here.1 index inside]
      split_ifs
      · simp only [List.map_cons, recurse, profileCode_congr here.1 here.2]
      · exact recurse

/-- **Components mapped keeping their mentions and replications give the same signatures.** -/
theorem signatureOf_map {count : Nat} {components : List Pattern} {read : Pattern → Pattern}
    (keeps : ∀ component ∈ components, (∀ index < count, mentions index (read component) = mentions index component) ∧
      isReplicated block (read component) = isReplicated block component) {index : Nat} (inside : index < count) :
    signatureOf block ⟨count, components.map read⟩ index = signatureOf block ⟨count, components⟩ index := by
  apply signatureOf_forall₂ _ inside
  rw [List.forall₂_map_left_iff]
  exact List.forall₂_same.mpr keeps

/-- Renaming keeps a component replicated or not. -/
theorem isReplicated_rename (relabel : Nat → Nat) (component : Pattern) :
    isReplicated block (rename relabel component) = isReplicated block component := by
  cases component with
  | apply label arguments =>
      rw [rename_apply]
      match arguments with
      | [] => rfl
      | [_] => rfl
      | _ :: _ :: _ => rfl
  | _ => rfl

/-- An injective renaming mentions an image exactly where the original mentioned. -/
theorem mentions_rename_of_injective {relabel : Nat → Nat} (injective : Function.Injective relabel)
    (component : Pattern) (index : Nat) :
    mentions (relabel index) (rename relabel component) = mentions index component := by
  apply Bool.eq_iff_iff.mpr
  rw [mentions_iff, mentions_iff, freeIn_rename]
  constructor
  · rintro ⟨original, free, same⟩
    rwa [← injective same]
  · exact fun free => ⟨index, free, rfl⟩

/-- **Renaming a block's restrictions by an order keeps the profile of each component.** -/
theorem profileCode_rename {count : Nat} {order : List Nat} (isOrder : IsOrder count order) (component : Pattern) :
    profileCode block count (rename (Prenex.permute count order) component) = profileCode block count component := by
  unfold profileCode
  rw [isReplicated_rename]
  congr 2
  have injective := permute_injective isOrder
  have perm : ((List.range count).filter fun index => mentions index (rename (Prenex.permute count order) component)).Perm
      (((List.range count).filter fun index => mentions index component).map (Prenex.permute count order)) := by
    refine (List.perm_ext_iff_of_nodup (List.nodup_range.filter _)
      ((List.nodup_range.filter _).map injective)).mpr fun index => ?_
    simp only [List.mem_filter, List.mem_range, List.mem_map]
    constructor
    · rintro ⟨inside, mentioned⟩
      rw [mentions_iff, freeIn_rename] at mentioned
      obtain ⟨original, free, rfl⟩ := mentioned
      have originalInside : original < count := by
        by_contra outside
        rw [permute_of_ge order outside] at inside
        exact outside inside
      exact ⟨original, ⟨originalInside, (mentions_iff _ _).mpr free⟩, rfl⟩
    · rintro ⟨original, ⟨inside, mentioned⟩, rfl⟩
      exact ⟨permute_lt isOrder inside, by rw [mentions_rename_of_injective injective]; exact mentioned⟩
  rw [perm.length_eq, List.length_map]

/-- **Renaming a block's restrictions by an order carries its signatures along.** -/
theorem signatureOf_rename {count : Nat} {order : List Nat} (isOrder : IsOrder count order)
    (components : List Pattern) (index : Nat) :
    signatureOf block ⟨count, components.map (rename (Prenex.permute count order))⟩
        (Prenex.permute count order index) = signatureOf block ⟨count, components⟩ index := by
  have injective := permute_injective isOrder
  unfold signatureOf
  simp only
  congr 3
  rw [List.filter_map, List.map_map]
  have sameFilter : (components.filter (mentions (Prenex.permute count order index) ∘
      rename (Prenex.permute count order))) = components.filter (mentions index) :=
    List.filter_congr fun component _ => by
      simp only [Function.comp]
      exact mentions_rename_of_injective injective component index
  rw [sameFilter]
  exact List.map_congr_left fun component _ => by
    simp only [Function.comp]
    exact profileCode_rename isOrder component

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks
