import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationShapes
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationClose
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationOrders
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationRename

/-!
# The canonical form commutes with order-preserving renamings

Patterns are compared by their serializations (`ser`): a variable serializes as `[0, index]`, and every other part of
the serialization is a tag, a length or a character, which a renaming of variables leaves alone. The serialization is
prefix-free, so two different patterns are told apart before either code ends.

- **Order**: a strictly monotone renaming, lifted under binders, stays strictly monotone (`strictMono_liftIndex`), so
  it keeps the comparison of any two patterns (`ser_rename_lexLe`, `patternLe_rename_iff`) and of any two lists of
  patterns (`lexLe_serList_rename`, `serList_lt_rename_iff`): the first place where the codes differ is a tag, a
  length, a character or two variables at one depth, and the renaming keeps each of these comparisons.
- **The canonical form**: renaming the names outside a block strictly monotonically commutes with its canonical form
  (`normal_renameOuter_mono`, `canonicalOf_rename_mono`). The canonical form reads the block's restrictions, which
  such a renaming leaves alone: which components mention which restrictions, so the groups a copy is looked for in
  (`groupsThrough_renamed`), the signatures and so the reading orders (`readingOrders_renameOuter`), and whether a
  component is replicated; it compares canonical forms of smaller blocks, which commute by induction
  (`absorbOnce_renameOuter`); and it sorts and chooses by codes, whose order the renaming keeps
  (`sortComponents_map_rename`, `least_map_rename`).
-/
set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (liftIndex FreeIn)
open Mettapedia.OSLF.MeTTaIL.PatternLexOrder (ser serList lexLe serString serOptString serStringList collectionTag
  collectionTag_injective serString_prefix serOptString_prefix serStringList_prefix ser_prefix PatternLe)

/-! ## Comparing codes -/

/-- A common prefix is passed over. -/
theorem lexLe_append_same : ∀ (common xs ys : List Nat), lexLe (common ++ xs) (common ++ ys) = lexLe xs ys
  | [], _, _ => rfl
  | head :: common, xs, ys => by
      simp only [List.cons_append, lexLe, Nat.lt_irrefl, decide_false, beq_self_eq_true, Bool.true_and,
        Bool.false_or]
      exact lexLe_append_same common xs ys

/-- **Two codes neither of which begins the other** compare the same whatever follows them. -/
theorem lexLe_append_apart : ∀ (first second xs ys xs' ys' : List Nat),
    (∀ tail, first ++ tail ≠ second) → (∀ tail, second ++ tail ≠ first) →
    lexLe (first ++ xs) (second ++ ys) = lexLe (first ++ xs') (second ++ ys')
  | [], second, _, _, _, _, apart, _ => absurd (by simp) (apart second)
  | head :: rest, [], _, _, _, _, _, apart' => absurd (by simp) (apart' (head :: rest))
  | a :: first, b :: second, xs, ys, xs', ys', apart, apart' => by
      simp only [List.cons_append, lexLe]
      by_cases same : a = b
      · subst same
        have inner : lexLe (first ++ xs) (second ++ ys) = lexLe (first ++ xs') (second ++ ys') :=
          lexLe_append_apart first second xs ys xs' ys'
            (fun tail equal => apart tail (by simp [equal]))
            (fun tail equal => apart' tail (by simp [equal]))
        rw [inner]
      · simp [beq_false_of_ne same]

theorem serString_apart {first second : String} (different : first ≠ second) :
    ∀ tail, serString first ++ tail ≠ serString second := fun tail equal =>
  different (serString_prefix (rest := tail) (rest' := []) (by simpa using equal)).1

theorem serOptString_apart {first second : Option String} (different : first ≠ second) :
    ∀ tail, serOptString first ++ tail ≠ serOptString second := fun tail equal =>
  different (serOptString_prefix (rest := tail) (rest' := []) (by simpa using equal)).1

theorem serStringList_apart {first second : List String} (different : first ≠ second) :
    ∀ tail, serStringList first ++ tail ≠ serStringList second := fun tail equal =>
  different (serStringList_prefix (rest := tail) (rest' := []) (by simpa using equal)).1

/-- Codes of strings compare the same after any continuations, related or equal. -/
theorem lexLe_serString {first second : String} {xs ys xs' ys' : List Nat}
    (continuations : first = second → lexLe xs' ys' = lexLe xs ys) :
    lexLe (serString first ++ xs') (serString second ++ ys') = lexLe (serString first ++ xs) (serString second ++ ys) := by
  by_cases same : first = second
  · subst same
    rw [lexLe_append_same, lexLe_append_same, continuations rfl]
  · exact lexLe_append_apart _ _ _ _ _ _ (serString_apart same) (serString_apart (Ne.symm same))

theorem lexLe_serOptString {first second : Option String} {xs ys xs' ys' : List Nat}
    (continuations : first = second → lexLe xs' ys' = lexLe xs ys) :
    lexLe (serOptString first ++ xs') (serOptString second ++ ys') =
      lexLe (serOptString first ++ xs) (serOptString second ++ ys) := by
  by_cases same : first = second
  · subst same
    rw [lexLe_append_same, lexLe_append_same, continuations rfl]
  · exact lexLe_append_apart _ _ _ _ _ _ (serOptString_apart same) (serOptString_apart (Ne.symm same))

theorem lexLe_serStringList {first second : List String} {xs ys xs' ys' : List Nat}
    (continuations : first = second → lexLe xs' ys' = lexLe xs ys) :
    lexLe (serStringList first ++ xs') (serStringList second ++ ys') =
      lexLe (serStringList first ++ xs) (serStringList second ++ ys) := by
  by_cases same : first = second
  · subst same
    rw [lexLe_append_same, lexLe_append_same, continuations rfl]
  · exact lexLe_append_apart _ _ _ _ _ _ (serStringList_apart same) (serStringList_apart (Ne.symm same))

/-- Numbers in front compare first, then what follows them. -/
theorem lexLe_cons_cons {first second : Nat} {xs ys xs' ys' : List Nat}
    (continuations : first = second → lexLe xs' ys' = lexLe xs ys) :
    lexLe (first :: xs') (second :: ys') = lexLe (first :: xs) (second :: ys) := by
  by_cases same : first = second
  · subst same
    simp [lexLe, continuations rfl]
  · simp [lexLe, beq_false_of_ne same]

/-! ## Strictly monotone renamings -/

/-- **A strictly monotone renaming lifted under binders stays strictly monotone.** -/
theorem strictMono_liftIndex {relabel : Nat → Nat} (mono : StrictMono relabel) (cutoff : Nat) :
    StrictMono (liftIndex cutoff relabel) := by
  intro first second less
  simp only [liftIndex]
  split_ifs with firstBelow secondBelow secondBelow
  · exact less
  · omega
  · omega
  · have := mono (show first - cutoff < second - cutoff by omega)
    omega

/-! ## Renaming keeps the order of codes -/

mutual
  /-- **A strictly monotone renaming keeps the comparison of two patterns**, followed by continuations that compare
  alike. -/
  theorem ser_rename_lexLe : ∀ {relabel : Nat → Nat}, StrictMono relabel → ∀ (left right : Pattern)
      {rest rest' renamed renamed' : List Nat}, lexLe renamed renamed' = lexLe rest rest' →
      lexLe (ser (rename relabel left) ++ renamed) (ser (rename relabel right) ++ renamed') =
        lexLe (ser left ++ rest) (ser right ++ rest')
    | relabel, mono, .bvar first, .bvar second, rest, rest', renamed, renamed', continuations => by
        simp only [rename_bvar, ser, List.cons_append, List.nil_append, lexLe, Nat.lt_irrefl, decide_false,
          beq_self_eq_true, Bool.true_and, Bool.false_or, continuations, mono.lt_iff_lt]
        by_cases same : first = second
        · subst same
          simp
        · simp [beq_false_of_ne same, beq_false_of_ne (mono.injective.ne same)]
    | relabel, mono, .fvar first, .fvar second, rest, rest', renamed, renamed', continuations => by
        simp only [rename_fvar, ser, List.cons_append]
        exact lexLe_cons_cons fun _ => lexLe_serString fun _ => continuations
    | relabel, mono, .apply first arguments, .apply second arguments', rest, rest', renamed, renamed', continuations => by
        simp only [rename_apply, ser, List.cons_append, List.append_assoc, List.length_map]
        refine lexLe_cons_cons fun _ => lexLe_serString fun _ => lexLe_cons_cons fun lengths => ?_
        exact serList_rename_lexLe mono arguments arguments' lengths continuations
    | relabel, mono, .lambda first body, .lambda second body', rest, rest', renamed, renamed', continuations => by
        simp only [rename_lambda, ser, List.cons_append, List.append_assoc]
        refine lexLe_cons_cons fun _ => lexLe_serOptString fun _ => ?_
        exact ser_rename_lexLe (strictMono_liftIndex mono 1) body body' continuations
    | relabel, mono, .multiLambda arity binders body, .multiLambda arity' binders' body', rest, rest', renamed,
        renamed', continuations => by
        simp only [rename_multiLambda, ser, List.cons_append, List.append_assoc]
        refine lexLe_cons_cons fun _ => lexLe_cons_cons fun arities => lexLe_serStringList fun _ => ?_
        subst arities
        exact ser_rename_lexLe (strictMono_liftIndex mono arity) body body' continuations
    | relabel, mono, .subst body replacement, .subst body' replacement', rest, rest', renamed, renamed',
        continuations => by
        simp only [rename_subst, ser, List.cons_append, List.append_assoc]
        refine lexLe_cons_cons fun _ => ?_
        exact ser_rename_lexLe (strictMono_liftIndex mono 1) body body'
          (ser_rename_lexLe mono replacement replacement' continuations)
    | relabel, mono, .collection kind elements tail, .collection kind' elements' tail', rest, rest', renamed,
        renamed', continuations => by
        simp only [rename_collection, ser, List.cons_append, List.append_assoc, List.length_map]
        refine lexLe_cons_cons fun _ => lexLe_cons_cons fun _ => lexLe_cons_cons fun lengths => ?_
        exact serList_rename_lexLe mono elements elements' lengths (lexLe_serOptString fun _ => continuations)
    | _, _, .bvar _, .fvar _, _, _, _, _, _ | _, _, .bvar _, .apply _ _, _, _, _, _, _
    | _, _, .bvar _, .lambda _ _, _, _, _, _, _ | _, _, .bvar _, .multiLambda _ _ _, _, _, _, _, _
    | _, _, .bvar _, .subst _ _, _, _, _, _, _ | _, _, .bvar _, .collection _ _ _, _, _, _, _, _
    | _, _, .fvar _, .bvar _, _, _, _, _, _ | _, _, .fvar _, .apply _ _, _, _, _, _, _
    | _, _, .fvar _, .lambda _ _, _, _, _, _, _ | _, _, .fvar _, .multiLambda _ _ _, _, _, _, _, _
    | _, _, .fvar _, .subst _ _, _, _, _, _, _ | _, _, .fvar _, .collection _ _ _, _, _, _, _, _
    | _, _, .apply _ _, .bvar _, _, _, _, _, _ | _, _, .apply _ _, .fvar _, _, _, _, _, _
    | _, _, .apply _ _, .lambda _ _, _, _, _, _, _ | _, _, .apply _ _, .multiLambda _ _ _, _, _, _, _, _
    | _, _, .apply _ _, .subst _ _, _, _, _, _, _ | _, _, .apply _ _, .collection _ _ _, _, _, _, _, _
    | _, _, .lambda _ _, .bvar _, _, _, _, _, _ | _, _, .lambda _ _, .fvar _, _, _, _, _, _
    | _, _, .lambda _ _, .apply _ _, _, _, _, _, _ | _, _, .lambda _ _, .multiLambda _ _ _, _, _, _, _, _
    | _, _, .lambda _ _, .subst _ _, _, _, _, _, _ | _, _, .lambda _ _, .collection _ _ _, _, _, _, _, _
    | _, _, .multiLambda _ _ _, .bvar _, _, _, _, _, _ | _, _, .multiLambda _ _ _, .fvar _, _, _, _, _, _
    | _, _, .multiLambda _ _ _, .apply _ _, _, _, _, _, _ | _, _, .multiLambda _ _ _, .lambda _ _, _, _, _, _, _
    | _, _, .multiLambda _ _ _, .subst _ _, _, _, _, _, _ | _, _, .multiLambda _ _ _, .collection _ _ _, _, _, _, _, _
    | _, _, .subst _ _, .bvar _, _, _, _, _, _ | _, _, .subst _ _, .fvar _, _, _, _, _, _
    | _, _, .subst _ _, .apply _ _, _, _, _, _, _ | _, _, .subst _ _, .lambda _ _, _, _, _, _, _
    | _, _, .subst _ _, .multiLambda _ _ _, _, _, _, _, _ | _, _, .subst _ _, .collection _ _ _, _, _, _, _, _
    | _, _, .collection _ _ _, .bvar _, _, _, _, _, _ | _, _, .collection _ _ _, .fvar _, _, _, _, _, _
    | _, _, .collection _ _ _, .apply _ _, _, _, _, _, _ | _, _, .collection _ _ _, .lambda _ _, _, _, _, _, _
    | _, _, .collection _ _ _, .multiLambda _ _ _, _, _, _, _, _
    | _, _, .collection _ _ _, .subst _ _, _, _, _, _, _ => by
        simp [rename_bvar, rename_fvar, rename_apply, rename_lambda, rename_multiLambda, rename_subst,
          rename_collection, ser, lexLe]

  /-- **A strictly monotone renaming keeps the comparison of two lists of patterns of one length**, followed by
  continuations that compare alike. -/
  theorem serList_rename_lexLe : ∀ {relabel : Nat → Nat}, StrictMono relabel → ∀ (left right : List Pattern),
      left.length = right.length → ∀ {rest rest' renamed renamed' : List Nat}, lexLe renamed renamed' = lexLe rest rest' →
      lexLe (serList (left.map (rename relabel)) ++ renamed) (serList (right.map (rename relabel)) ++ renamed') =
        lexLe (serList left ++ rest) (serList right ++ rest')
    | _, _, [], [], _, _, _, _, _, continuations => by simpa [serList] using continuations
    | _, _, _ :: _, [], lengths, _, _, _, _, _ => by simp at lengths
    | _, _, [], _ :: _, lengths, _, _, _, _, _ => by simp at lengths
    | relabel, mono, first :: left, second :: right, lengths, rest, rest', renamed, renamed', continuations => by
        simp only [List.map_cons, serList, List.append_assoc]
        exact ser_rename_lexLe mono first second
          (serList_rename_lexLe mono left right (by simpa using lengths) continuations)
end

/-- **A strictly monotone renaming keeps the order of patterns.** -/
theorem patternLe_rename_iff {relabel : Nat → Nat} (mono : StrictMono relabel) (left right : Pattern) :
    PatternLe (rename relabel left) (rename relabel right) ↔ PatternLe left right := by
  unfold PatternLe
  have same := ser_rename_lexLe mono left right (rest := []) (rest' := []) (renamed := []) (renamed' := []) rfl
  simp only [List.append_nil] at same
  rw [same]

/-! ## Lists of any lengths -/

theorem ser_ne_nil (pattern : Pattern) : ser pattern ≠ [] := by
  cases pattern <;> simp [ser]

/-- Two different patterns' codes compare the same whatever follows them. -/
theorem lexLe_ser_apart {first second : Pattern} (different : first ≠ second) (xs ys xs' ys' : List Nat) :
    lexLe (ser first ++ xs) (ser second ++ ys) = lexLe (ser first ++ xs') (ser second ++ ys') :=
  lexLe_append_apart _ _ _ _ _ _
    (fun tail equal => different (ser_prefix first second (rest := tail) (rest' := []) (by simpa using equal)).1)
    (fun tail equal => different (ser_prefix second first (rest := tail) (rest' := []) (by simpa using equal)).1.symm)

/-- **A strictly monotone renaming keeps the comparison of two lists of patterns**, of any lengths. -/
theorem lexLe_serList_rename {relabel : Nat → Nat} (mono : StrictMono relabel) :
    ∀ (left right : List Pattern),
      lexLe (serList (left.map (rename relabel))) (serList (right.map (rename relabel))) =
        lexLe (serList left) (serList right)
  | [], right => by cases right <;> simp [serList, lexLe]
  | first :: left, [] => by
      obtain ⟨head, tail, isCons⟩ := List.exists_cons_of_ne_nil (ser_ne_nil (rename relabel first))
      obtain ⟨head', tail', isCons'⟩ := List.exists_cons_of_ne_nil (ser_ne_nil first)
      simp [serList, isCons, isCons', lexLe]
  | first :: left, second :: right => by
      simp only [List.map_cons, serList]
      by_cases same : first = second
      · subst same
        rw [lexLe_append_same, lexLe_append_same]
        exact lexLe_serList_rename mono left right
      · have renamedDifferent : rename relabel first ≠ rename relabel second :=
          fun equal => same (rename_injective mono.injective equal)
        rw [lexLe_ser_apart renamedDifferent _ _ [] [], lexLe_ser_apart same _ _ [] [],
          List.append_nil, List.append_nil, List.append_nil, List.append_nil]
        have core := ser_rename_lexLe mono first second (rest := []) (rest' := []) (renamed := [])
          (renamed' := []) rfl
        simpa using core

/-- The strict order of number lists is the lexicographic order without equality. -/
theorem list_lt_iff_lexLe : ∀ (xs ys : List Nat), xs < ys ↔ lexLe xs ys = true ∧ xs ≠ ys
  | [], [] => by simp [lexLe]
  | [], _ :: _ => by simp [lexLe, List.nil_lt_cons]
  | _ :: _, [] => by simp [lexLe]
  | x :: xs, y :: ys => by
      rw [List.cons_lt_cons_iff, list_lt_iff_lexLe xs ys]
      simp only [lexLe, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq, ne_eq,
        List.cons.injEq, not_and]
      constructor
      · rintro (less | ⟨rfl, tail, different⟩)
        · exact ⟨.inl less, fun same => absurd same (Nat.ne_of_lt less)⟩
        · exact ⟨.inr ⟨rfl, tail⟩, fun _ => different⟩
      · rintro ⟨less | ⟨rfl, tail⟩, different⟩
        · exact .inl less
        · exact .inr ⟨rfl, tail, different rfl⟩

/-- **A strictly monotone renaming keeps the strict order of lists of patterns**, as `least` reads it. -/
theorem serList_lt_rename_iff {relabel : Nat → Nat} (mono : StrictMono relabel) (left right : List Pattern) :
    serList (left.map (rename relabel)) < serList (right.map (rename relabel)) ↔ serList left < serList right := by
  rw [list_lt_iff_lexLe, list_lt_iff_lexLe, lexLe_serList_rename mono]
  constructor
  · rintro ⟨order, different⟩
    exact ⟨order, fun same => different (by rw [serList_injective same])⟩
  · rintro ⟨order, different⟩
    refine ⟨order, fun same => different ?_⟩
    have mapped := serList_injective same
    rw [List.map_injective_iff.mpr (rename_injective mono.injective) mapped]

/-! ## Renaming outside a block -/

variable {block : ReplicationBlock}

theorem liftIndex_of_lt (relabel : Nat → Nat) {count index : Nat} (below : index < count) :
    liftIndex count relabel index = index := by
  simp [liftIndex, below]

theorem liftIndex_liftIndex (inner outer : Nat) (relabel : Nat → Nat) :
    liftIndex inner (liftIndex outer relabel) = liftIndex (inner + outer) relabel := by
  funext index
  simp only [liftIndex, Nat.sub_sub]
  split_ifs <;> omega

/-- Renaming outside a block keeps which of its restrictions a component mentions. -/
theorem mentions_liftIndex {relabel : Nat → Nat} (injective : Function.Injective relabel) {count index : Nat}
    (below : index < count) (component : Pattern) :
    mentions index (rename (liftIndex count relabel) component) = mentions index component := by
  have kept := mentions_rename_of_injective (liftIndex_injective injective count) component index
  rwa [liftIndex_of_lt relabel below] at kept

theorem usedRestrictions_liftIndex {relabel : Nat → Nat} (injective : Function.Injective relabel) (count : Nat)
    (component : Pattern) :
    usedRestrictions count (rename (liftIndex count relabel) component) = usedRestrictions count component :=
  List.filter_congr fun _ member => mentions_liftIndex injective (List.mem_range.mp member) component

/-- Reordering a block's restrictions commutes with renaming outside it. -/
theorem permute_comp_liftIndex {count : Nat} {order : List Nat} (isOrder : IsOrder count order)
    (relabel : Nat → Nat) :
    Prenex.permute count order ∘ liftIndex count relabel = liftIndex count relabel ∘ Prenex.permute count order := by
  funext index
  simp only [Function.comp_apply]
  by_cases below : index < count
  · rw [liftIndex_of_lt relabel below, liftIndex_of_lt relabel (permute_lt isOrder below)]
  · have above : ¬ liftIndex count relabel index < count := by
      simp only [liftIndex, below, if_false]
      omega
    rw [permute_of_ge order above, permute_of_ge order below]

theorem rename_permute_liftIndex {count : Nat} {order : List Nat} (isOrder : IsOrder count order)
    (relabel : Nat → Nat) (component : Pattern) :
    rename (Prenex.permute count order) (rename (liftIndex count relabel) component) =
      rename (liftIndex count relabel) (rename (Prenex.permute count order) component) := by
  rw [rename_comp, rename_comp, permute_comp_liftIndex isOrder]

/-- Profiles read only a block's restrictions. -/
theorem profileCode_liftIndex {relabel : Nat → Nat} (injective : Function.Injective relabel) (count : Nat)
    (component : Pattern) :
    profileCode block count (rename (liftIndex count relabel) component) = profileCode block count component := by
  unfold profileCode
  rw [isReplicated_rename,
    List.filter_congr fun _ member => mentions_liftIndex injective (List.mem_range.mp member) component]

/-- Signatures read only a block's restrictions. -/
theorem signatureOf_renameOuter {relabel : Nat → Nat} (injective : Function.Injective relabel) (form : Prenex)
    {index : Nat} (below : index < form.count) :
    signatureOf block (form.renameOuter relabel) index = signatureOf block form index := by
  obtain ⟨count, components⟩ := form
  unfold signatureOf
  simp only [Prenex.renameOuter, List.filter_map, List.map_map]
  have filterSame : (components.filter (mentions index ∘ rename (liftIndex count relabel))) =
      components.filter (mentions index) :=
    List.filter_congr fun component _ => mentions_liftIndex injective below component
  have profileSame : profileCode block count ∘ rename (liftIndex count relabel) = profileCode block count :=
    funext fun component => profileCode_liftIndex injective count component
  rw [filterSame, profileSame]

/-- **Renaming outside a block keeps its reading orders.** -/
theorem readingOrders_renameOuter {relabel : Nat → Nat} (injective : Function.Injective relabel) (form : Prenex) :
    readingOrders block (form.renameOuter relabel) = readingOrders block form :=
  readingOrders_congr rfl fun _ below => signatureOf_renameOuter injective form below

/-! ## Groups renamed outside -/

/-- A group with its components renamed. -/
def Group.renamed (relabel : Nat → Nat) (group : Group) : Group :=
  ⟨group.restrictions, group.components.map (rename relabel)⟩

theorem Group.renamed_injective {relabel : Nat → Nat} (injective : Function.Injective relabel) :
    Function.Injective (Group.renamed relabel) := by
  rintro ⟨restrictions, components⟩ ⟨restrictions', components'⟩ same
  simp only [Group.renamed, Group.mk.injEq] at same
  obtain ⟨rfl, mapped⟩ := same
  rw [List.map_injective_iff.mpr (rename_injective injective) mapped]

/-- Merging reads only the groups' restrictions. -/
theorem insertUsing_renamed (count : Nat) (used : List Nat) (relabel : Nat → Nat) (component : Pattern)
    (groups : List Group) :
    insertUsing count used (rename relabel component) (groups.map (Group.renamed relabel)) =
      (insertUsing count used component groups).map (Group.renamed relabel) := by
  simp [insertUsing, List.filter_map, Function.comp_def, Group.renamed, List.map_flatMap, List.flatMap_map]
  rfl

/-- **The groups of components renamed outside are the groups renamed.** -/
theorem groupsThrough_renamed (allowed : List Nat) (count : Nat) {relabel : Nat → Nat}
    (keeps : ∀ component, usedRestrictions count (rename relabel component) = usedRestrictions count component)
    (components : List Pattern) :
    groupsThrough allowed count (components.map (rename relabel)) =
      (groupsThrough allowed count components).map (Group.renamed relabel) := by
  unfold groupsThrough
  rw [List.foldl_map]
  suffices general : ∀ start : List Group,
      components.foldl (fun groups component => insertUsing count
          ((usedRestrictions count (rename relabel component)).filter allowed.contains) (rename relabel component) groups)
        (start.map (Group.renamed relabel)) =
      (components.foldl (fun groups component => insertUsing count
          ((usedRestrictions count component).filter allowed.contains) component groups) start).map
        (Group.renamed relabel) by
    simpa using general []
  induction components with
  | nil => intro start; rfl
  | cons component rest recurse =>
      intro start
      simp only [List.foldl_cons]
      rw [keeps, insertUsing_renamed]
      exact recurse _

theorem eraseIdx_map {α β : Type} (f : α → β) : ∀ (list : List α) (position : Nat),
    (list.map f).eraseIdx position = (list.eraseIdx position).map f
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | head :: tail, position + 1 => by
      simp only [List.map_cons, List.eraseIdx_cons_succ]
      rw [eraseIdx_map f tail position]

/-- **A group's copy, its components renamed outside the block, is the copy renamed outside.** -/
theorem copyOf_renamed {count : Nat} {group : Group} (nodup : group.restrictions.Nodup)
    (inside : ∀ index ∈ group.restrictions, index < count) (relabel : Nat → Nat) :
    copyOf block.toBlock count (group.renamed (liftIndex count relabel)) =
      rename (liftIndex (outsideOf count group.restrictions).length relabel) (copyOf block.toBlock count group) := by
  have fewer : group.restrictions.length ≤ count := by
    simpa using nodup.length_le_of_subset fun index member => List.mem_range.mpr (inside index member)
  have isOrder : IsOrder count (splitOrder count (outsideOf count group.restrictions) group.restrictions) :=
    (outside_parts nodup inside).splitOrder_perm
  unfold copyOf
  rw [rename_toPattern]
  simp only [Group.renamed, Prenex.renameOuter, List.map_map]
  congr 2
  refine List.map_congr_left fun component _ => ?_
  simp only [Function.comp_apply]
  rw [liftIndex_liftIndex, outsideOf_length nodup inside, show group.restrictions.length + (count -
    group.restrictions.length) = count by omega, rename_permute_liftIndex isOrder]

/-- **An argument read past a group, renamed outside the block, is the argument read past it renamed outside.** -/
theorem rename_groupIndex_liftIndex {count : Nat} {outside : List Nat} (relabel : Nat → Nat) {argument : Pattern}
    (within : ∀ index, FreeIn index argument → index < count → index ∈ outside) :
    rename (Prenex.groupIndex count outside) (rename (liftIndex count relabel) argument) =
      rename (liftIndex outside.length relabel) (rename (Prenex.groupIndex count outside) argument) := by
  rw [rename_comp, rename_comp]
  apply rename_congr
  intro index free
  simp only [Function.comp_apply]
  by_cases below : index < count
  · have position : Prenex.groupIndex count outside index < outside.length := by
      simp only [Prenex.groupIndex, below, if_true]
      exact List.idxOf_lt_length_of_mem (within index free below)
    rw [liftIndex_of_lt relabel below, liftIndex_of_lt relabel position]
  · have lifted : liftIndex count relabel index = relabel (index - count) + count := by
      simp [liftIndex, below]
    rw [lifted, groupIndex_above (by omega), groupIndex_above (by omega)]
    simp only [liftIndex]
    split_ifs with low
    · omega
    · rw [Nat.add_sub_cancel, Nat.add_sub_cancel]

/-! ## Absorption renamed outside -/

theorem findSome?_map_map {α β γ : Type} (f : α → Option β) (g : β → γ) : ∀ list : List α,
    (list.findSome? f).map g = list.findSome? fun element => (f element).map g
  | [] => rfl
  | head :: tail => by
      rw [List.findSome?_cons, List.findSome?_cons]
      rcases found : f head with _ | value
      · simpa using findSome?_map_map f g tail
      · simp

theorem findSome?_congr_mem {α β : Type} {f g : α → Option β} :
    ∀ {list : List α}, (∀ element ∈ list, f element = g element) → list.findSome? f = list.findSome? g
  | [], _ => rfl
  | head :: tail, same => by
      rw [List.findSome?_cons, List.findSome?_cons, same head List.mem_cons_self,
        findSome?_congr_mem fun element member => same element (List.mem_cons_of_mem head member)]

section Absorb

variable {canonical : Pattern → Pattern}
  (keeps : ∀ relabel : Nat → Nat, StrictMono relabel → ∀ pattern,
    canonical (rename relabel pattern) = rename relabel (canonical pattern))

include keeps in
/-- **One absorption renamed outside**: when the reading of copies commutes with strictly monotone renamings, a
block renamed outside absorbs the same group of the same replicated component, renamed. -/
theorem absorbOnce_renameOuter {relabel : Nat → Nat} (mono : StrictMono relabel) (form : Prenex) :
    absorbOnce block canonical (form.renameOuter relabel) =
      (absorbOnce block canonical form).map (Prenex.renameOuter relabel) := by
  obtain ⟨count, components⟩ := form
  have injective := mono.injective
  have lifted : StrictMono (liftIndex count relabel) := strictMono_liftIndex mono count
  unfold absorbOnce
  simp only [Prenex.renameOuter, List.length_map]
  rw [findSome?_map_map]
  apply findSome?_congr_mem
  intro position _
  rw [List.getElem?_map]
  rcases found : components[position]? with _ | component
  · rfl
  · cases component with
    | apply label arguments =>
        rcases arguments with _ | ⟨argument, _ | ⟨second, rest⟩⟩
        · simp [rename_apply]
        · simp only [Option.map_some, rename_apply, List.map_cons, List.map_nil]
          split_ifs with isReplicate
          · have renamedServer : Pattern.apply label [rename (liftIndex count relabel) argument] =
                rename (liftIndex count relabel) (.apply label [argument]) := by
              simp [rename_apply]
            rw [renamedServer]
            have allowedSame : ((List.range count).filter fun index =>
                !mentions index (rename (liftIndex count relabel) (.apply label [argument]))) =
                (List.range count).filter fun index => !mentions index (.apply label [argument]) :=
              List.filter_congr fun index member => by
                rw [mentions_liftIndex injective (List.mem_range.mp member)]
            rw [allowedSame, eraseIdx_map,
              groupsThrough_renamed _ _ (usedRestrictions_liftIndex injective count), List.find?_map,
              Option.map_map, Option.map_map]
            have partition := (groupsThrough_partition ((List.range count).filter fun index =>
              !mentions index (.apply label [argument])) count (components.eraseIdx position)).1
            congr 1
            · funext group
              simp only [Function.comp_apply]
              rw [← List.map_erase (Group.renamed_injective (liftIndex_injective injective count))]
              simp [Group.renamed, List.flatMap_map, List.map_flatMap, rename_apply, Prenex.renameOuter]
            · apply find?_congr_mem
              intro group member
              have nodup := partition.nodup group member
              have inside := partition.inside group member
              have within : ∀ index, FreeIn index argument → index < count →
                  index ∈ outsideOf count group.restrictions := by
                intro index free below
                refine mem_outsideOf.mpr ⟨below, fun inGroup => ?_⟩
                have allowedIndex := (List.mem_filter.mp (partition.allowedOnly group member index inGroup)).2
                have mentioned : mentions index (.apply label [argument]) = true := by
                  simp only [mentions, mentionsList, Bool.or_false]
                  exact (mentions_iff argument index).mpr free
                simp [mentioned] at allowedIndex
              simp only [Function.comp_apply]
              rw [copyOf_renamed nodup inside]
              dsimp only [Group.renamed]
              rw [rename_groupIndex_liftIndex relabel within]
              simp only [keeps (liftIndex (outsideOf count group.restrictions).length relabel)
                  (strictMono_liftIndex mono _), keeps (liftIndex count relabel) lifted,
                (rename_injective (liftIndex_injective injective (outsideOf count group.restrictions).length)).beq_eq,
                isReplicated_rename, List.all_map, Function.comp_def, argumentOf?_rename, size_rename, List.any_map]
              congr 1
              exact all_congr_mem fun index member => by
                rw [mentions_liftIndex injective (List.mem_range.mp member)]
                congr 1
                exact List.any_congr rfl fun component => mentions_liftIndex injective (List.mem_range.mp member) component
          · rfl
        · simp [rename_apply]
    | _ => simp [rename_bvar, rename_fvar, rename_lambda, rename_multiLambda, rename_subst, rename_collection]

include keeps in
theorem absorbRounds_renameOuter {relabel : Nat → Nat} (mono : StrictMono relabel) :
    ∀ (rounds : Nat) (form : Prenex),
      absorbRounds block canonical rounds (form.renameOuter relabel) =
        (absorbRounds block canonical rounds form).renameOuter relabel
  | 0, _ => rfl
  | rounds + 1, form => by
      simp only [absorbRounds, absorbOnce_renameOuter keeps mono form]
      rcases absorbOnce block canonical form with _ | next
      · rfl
      · exact absorbRounds_renameOuter mono rounds next

include keeps in
/-- **Absorption renamed outside.** -/
theorem absorb_renameOuter {relabel : Nat → Nat} (mono : StrictMono relabel) (form : Prenex) :
    absorb block canonical (form.renameOuter relabel) = (absorb block canonical form).renameOuter relabel := by
  unfold absorb
  rw [show (form.renameOuter relabel).components.length = form.components.length by simp [Prenex.renameOuter],
    absorbRounds_renameOuter keeps mono, prune_renameOuter]

end Absorb

/-! ## The canonical form renamed outside -/

/-- Sorting components commutes with a strictly monotone renaming. -/
theorem sortComponents_map_rename {relabel : Nat → Nat} (mono : StrictMono relabel) (components : List Pattern) :
    sortComponents (components.map (rename relabel)) = (sortComponents components).map (rename relabel) :=
  (List.map_insertionSort PatternLe PatternLe (rename relabel) components
    fun first _ second _ => (patternLe_rename_iff mono first second).symm).symm

/-- The least reading commutes with a strictly monotone renaming. -/
theorem least_map_rename {relabel : Nat → Nat} (mono : StrictMono relabel) :
    ∀ candidates : List (List Pattern),
      least (candidates.map (List.map (rename relabel))) = (least candidates).map (rename relabel)
  | [] => rfl
  | first :: rest => by
      simp only [List.map_cons, least]
      suffices general : ∀ (best : List Pattern) (rest : List (List Pattern)),
          (rest.map (List.map (rename relabel))).foldl
              (fun best next => if serList next < serList best then next else best) (best.map (rename relabel)) =
            (rest.foldl (fun best next => if serList next < serList best then next else best) best).map
              (rename relabel) from general first rest
      intro best rest
      induction rest generalizing best with
      | nil => rfl
      | cons next rest recurse =>
          simp only [List.map_cons, List.foldl_cons, serList_lt_rename_iff mono]
          split_ifs
          · exact recurse next
          · exact recurse best

/-- A constructor's argument read canonically commutes with strictly monotone renamings, when the reading does. -/
theorem canonArgument_rename {canonical : Pattern → Pattern}
    (keeps : ∀ relabel : Nat → Nat, StrictMono relabel → ∀ pattern,
      canonical (rename relabel pattern) = rename relabel (canonical pattern))
    {relabel : Nat → Nat} (mono : StrictMono relabel) (argument : Pattern) :
    canonArgument canonical (rename relabel argument) = rename relabel (canonArgument canonical argument) := by
  cases argument with
  | lambda binder body =>
      rw [rename_lambda]
      simp only [canonArgument]
      rw [keeps _ (strictMono_liftIndex mono 1), rename_lambda]
  | bvar index => rfl
  | fvar name => rfl
  | subst body replacement =>
      rw [rename_subst]
      simp only [canonArgument]
      rw [rename_subst]
  | apply constructor arguments =>
      rw [rename_apply]
      simp only [canonArgument]
      rw [← rename_apply, keeps relabel mono]
  | multiLambda arity binders body =>
      rw [rename_multiLambda]
      simp only [canonArgument]
      rw [← rename_multiLambda, keeps relabel mono]
  | collection kind elements rest =>
      rw [rename_collection]
      simp only [canonArgument]
      rw [← rename_collection, keeps relabel mono]

/-- A block read back as a multiset, renamed outside, is the multiset renamed. -/
theorem multisetOf_renameOuter (relabel : Nat → Nat) (form : Prenex) :
    multisetOf block.toBlock (form.renameOuter relabel) = rename relabel (multisetOf block.toBlock form) := by
  obtain ⟨count, components⟩ := form
  unfold multisetOf
  simp only [Prenex.renameOuter]
  by_cases empty : count = 0
  · subst empty
    simp [rename_collection, liftIndex_zero]
  · simp only [empty, if_false]
    rw [rename_collection, List.map_singleton, rename_toPattern]
    rfl

/-- **The canonical form within a fuel commutes with strictly monotone renamings outside**, and so do the readings of
a component's parts and of a named multiset's argument. -/
theorem normalizeWith_renameOuter_and : ∀ fuel : Nat,
    (∀ relabel : Nat → Nat, StrictMono relabel → ∀ form : Prenex,
      normalizeWith block fuel (form.renameOuter relabel) = (normalizeWith block fuel form).renameOuter relabel) ∧
    (∀ relabel : Nat → Nat, StrictMono relabel → ∀ component : Pattern,
      recanonWith block fuel (rename relabel component) = rename relabel (recanonWith block fuel component)) ∧
    (∀ relabel : Nat → Nat, StrictMono relabel → ∀ argument : Pattern,
      recanonMultisetWith block fuel (rename relabel argument) =
        rename relabel (recanonMultisetWith block fuel argument))
  | 0 => ⟨fun _ _ _ => by simp only [normalizeWith], fun _ _ _ => by simp only [recanonWith],
      fun _ _ _ => by simp only [recanonMultisetWith]⟩
  | fuel + 1 => by
      obtain ⟨normalKeeps, recanonKeeps, multisetKeeps⟩ := normalizeWith_renameOuter_and fuel
      have canonicalKeeps : ∀ relabel : Nat → Nat, StrictMono relabel → ∀ pattern,
          Prenex.toPattern block.toBlock (normalizeWith block fuel (decompose block.toBlock (rename relabel pattern))) =
            rename relabel
              (Prenex.toPattern block.toBlock (normalizeWith block fuel (decompose block.toBlock pattern))) := by
        intro relabel mono pattern
        rw [decompose_renameOuter, normalKeeps relabel mono, rename_toPattern]
      refine ⟨fun relabel mono form => ?_, fun relabel mono component => ?_, fun relabel mono argument => ?_⟩
      -- the canonical form of a block
      · simp only [normalizeWith]
        rw [absorb_renameOuter (canonical := fun pattern =>
            Prenex.toPattern block.toBlock (normalizeWith block fuel (decompose block.toBlock pattern)))
          canonicalKeeps mono, readingOrders_renameOuter mono.injective]
        generalize absorb block (fun pattern =>
          Prenex.toPattern block.toBlock (normalizeWith block fuel (decompose block.toBlock pattern))) form = absorbed
        obtain ⟨count, components⟩ := absorbed
        have lifted : StrictMono (liftIndex count relabel) := strictMono_liftIndex mono count
        simp only [Prenex.renameOuter, Prenex.mk.injEq, true_and]
        rw [← least_map_rename lifted, List.map_map]
        congr 1
        refine List.map_congr_left fun order member => ?_
        have isOrder : IsOrder count order := readingOrders_isOrder member
        simp only [Function.comp_apply]
        rw [← dedupReplicated_map (rename_injective lifted.injective) (isReplicated_rename _),
          ← sortComponents_map_rename lifted, List.map_map, List.map_map]
        congr 2
        refine List.map_congr_left fun component _ => ?_
        simp only [Function.comp_apply]
        rw [rename_permute_liftIndex isOrder, recanonKeeps _ lifted]
      -- a component's parts
      · cases component with
        | apply constructor arguments =>
            rw [rename_apply]
            simp only [recanonWith]
            split_ifs with isRestrict isMultiset
            · rw [rename_apply]
            · rw [rename_apply, List.map_map, List.map_map]
              congr 1
              exact List.map_congr_left fun argument _ => multisetKeeps relabel mono argument
            · rw [rename_apply, List.map_map, List.map_map]
              congr 1
              exact List.map_congr_left fun argument _ => canonArgument_rename (canonical := fun pattern =>
                Prenex.toPattern block.toBlock (normalizeWith block fuel (decompose block.toBlock pattern)))
                canonicalKeeps mono argument
        | lambda binder body =>
            rw [rename_lambda]
            simp only [recanonWith]
            rw [canonicalKeeps _ (strictMono_liftIndex mono 1), rename_lambda]
        | multiLambda arity binders body =>
            rw [rename_multiLambda]
            simp only [recanonWith]
            rw [canonicalKeeps _ (strictMono_liftIndex mono arity), rename_multiLambda]
        | collection kind elements rest =>
            rw [rename_collection]
            simp only [recanonWith]
            rw [rename_collection, List.map_map, List.map_map]
            congr 1
            exact List.map_congr_left fun element _ => canonicalKeeps relabel mono element
        | bvar index => rfl
        | fvar name => rfl
        | subst body replacement => rfl
      -- a named multiset's argument
      · by_cases isOpen : ∃ kind elements rest, argument = .collection kind elements (some rest)
        · obtain ⟨kind, elements, rest, rfl⟩ := isOpen
          rw [rename_collection]
          simp only [recanonMultisetWith]
          rw [rename_collection, List.map_map, List.map_map]
          congr 1
          exact List.map_congr_left fun element _ => canonicalKeeps relabel mono element
        by_cases isSubst : ∃ body replacement, argument = .subst body replacement
        · obtain ⟨body, replacement, rfl⟩ := isSubst
          rfl
        have notOpen : ∀ kind elements rest, argument ≠ .collection kind elements (some rest) :=
          fun kind elements rest same => isOpen ⟨kind, elements, rest, same⟩
        have notSubst : ∀ body replacement, argument ≠ .subst body replacement :=
          fun body replacement same => isSubst ⟨body, replacement, same⟩
        have renamedNotOpen : ∀ kind elements rest, rename relabel argument ≠ .collection kind elements (some rest) := by
          intro kind elements rest same
          cases argument with
          | collection kind' elements' rest' =>
              rw [rename_collection] at same
              simp only [Pattern.collection.injEq] at same
              obtain ⟨rfl, -, rfl⟩ := same
              exact notOpen _ elements' rest rfl
          | _ => simp [rename_bvar, rename_fvar, rename_apply, rename_lambda, rename_multiLambda, rename_subst] at same
        have renamedNotSubst : ∀ body replacement, rename relabel argument ≠ .subst body replacement := by
          intro body replacement same
          cases argument with
          | subst body' replacement' => exact notSubst body' replacement' rfl
          | _ => simp [rename_bvar, rename_fvar, rename_apply, rename_lambda, rename_multiLambda,
              rename_collection] at same
        rw [recanonMultisetWith_other renamedNotOpen renamedNotSubst, recanonMultisetWith_other notOpen notSubst,
          decompose_renameOuter, normalKeeps relabel mono, multisetOf_renameOuter]

/-- **MONO: the canonical form commutes with strictly monotone renamings outside a block.** The canonical form reads
a block's restrictions and compares its components by their codes, and such a renaming keeps both. -/
theorem normal_renameOuter_mono {relabel : Nat → Nat} (mono : StrictMono relabel) (form : Prenex) :
    normal block (form.renameOuter relabel) = (normal block form).renameOuter relabel := by
  unfold normal
  rw [← rename_toPattern, size_rename]
  exact (normalizeWith_renameOuter_and _).1 relabel mono form

/-- **The canonical form of a pattern commutes with strictly monotone renamings.** -/
theorem canonicalOf_rename_mono {relabel : Nat → Nat} (mono : StrictMono relabel) (pattern : Pattern) :
    canonicalOf block (rename relabel pattern) = rename relabel (canonicalOf block pattern) := by
  unfold canonicalOf
  rw [decompose_renameOuter, normal_renameOuter_mono mono, rename_toPattern]

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks
