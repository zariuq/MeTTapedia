import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationForm
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.FormComputable

/-!
# The pieces of the canonical form with replication are computable on codes

A group of a block is coded by its restrictions and its components (`Coded RestrictionBlocks.Group`). The molecules of a block
(`groups`, `groupsThrough`), a group as a block and as a copy (`Prenex.molecule`, `copyOf`), dropping unused
restrictions (`Prenex.prune`), keeping one of each replicated component (`dedupReplicated`), the signatures of the
restrictions and the orders a block is read under (`readingOrders`) are computable on codes.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.Computability
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.PatternCode
open Mettapedia.OSLF.MeTTaIL.PatternCode.CodeComputable'
open CodeComputable
open FormCodes

instance : Coded RestrictionBlocks.Group := ⟨fun group => code (group.restrictions, group.components)⟩

namespace ReplicationCodes

variable {α : Type*} [Coded α]

/-! ## Lists of coded values -/

theorem idxOf_map_code {β : Type*} [DecidableEq β] [Coded β] (injective : Function.Injective (code : β → ℕ))
    (element : β) : ∀ members : List β, (members.map code).idxOf (code element) = members.idxOf element
  | [] => rfl
  | member :: rest => by
      by_cases same : member = element
      · subst same; simp [List.idxOf_cons_self]
      · have different : code member ≠ code element := fun equal => same (injective equal)
        simp [List.idxOf_cons_ne _ different, List.idxOf_cons_ne _ same, idxOf_map_code injective element rest]

theorem list_idxOf {β : Type*} [DecidableEq β] [Coded β] (injective : Function.Injective (code : β → ℕ))
    {members : α → List β} {element : α → β} (hMembers : CodeComputable members)
    (hElement : CodeComputable element) : CodeComputable fun argument => (members argument).idxOf (element argument) := by
  obtain ⟨trackMembers, computableMembers, tracksMembers⟩ := hMembers
  obtain ⟨trackElement, computableElement, tracksElement⟩ := hElement
  refine ⟨fun n => (Denumerable.ofNat (List ℕ) (trackMembers n)).idxOf (trackElement n),
    (Primrec.list_idxOf.to_comp).comp computableElement ((Primrec.ofNat (List ℕ)).to_comp.comp computableMembers),
    fun argument => ?_⟩
  beta_reduce
  rw [tracksMembers, tracksElement, ofNat_code_list, idxOf_map_code injective]
  rfl

theorem list_eraseIdx {β : Type*} [Coded β] {members : α → List β} {position : α → ℕ}
    (hMembers : CodeComputable members) (hPosition : CodeComputable position) :
    CodeComputable fun argument => (members argument).eraseIdx (position argument) :=
  (list_append (list_take hPosition hMembers) (list_drop (nat_add hPosition (const 1)) hMembers)).of_eq
    fun _ => (List.eraseIdx_eq_take_drop_succ _ _).symm

theorem list_erase {β : Type*} [DecidableEq β] [Coded β] (injective : Function.Injective (code : β → ℕ))
    {members : α → List β} {element : α → β} (hMembers : CodeComputable members)
    (hElement : CodeComputable element) : CodeComputable fun argument => (members argument).erase (element argument) :=
  (list_eraseIdx hMembers (list_idxOf injective hMembers hElement)).of_eq fun _ =>
    (List.erase_eq_eraseIdx_of_idxOf rfl).symm

theorem nat_injective : Function.Injective (code : ℕ → ℕ) := fun _ _ same => same

theorem dedup_eq_foldr : ∀ members : List ℕ,
    members.dedup = members.foldr (fun member kept => if kept.contains member then kept else member :: kept) []
  | [] => rfl
  | member :: rest => by
      rw [List.foldr_cons, ← dedup_eq_foldr rest]
      by_cases inRest : member ∈ rest
      · rw [List.dedup_cons_of_mem inRest, if_pos (by simpa [List.contains_iff_mem, List.mem_dedup] using inRest)]
      · rw [List.dedup_cons_of_notMem inRest, if_neg (by simpa [List.contains_iff_mem, List.mem_dedup] using inRest)]

theorem list_dedup {members : α → List ℕ} (hMembers : CodeComputable members) :
    CodeComputable fun argument => (members argument).dedup :=
  (list_foldr (step := fun _ member kept => if kept.contains member then kept else member :: kept) hMembers list_nil
    (ite (list_contains nat_injective (snd.comp snd) (fst.comp snd)) (snd.comp snd)
      (list_cons (fst.comp snd) (snd.comp snd)))).of_eq fun _ => (dedup_eq_foldr _).symm

theorem pow_two_eq_iterate (exponent : ℕ) : 2 ^ exponent = (fun value => value * 2)^[exponent] 1 := by
  induction exponent with
  | zero => rfl
  | succ exponent recurse => rw [Function.iterate_succ_apply', ← recurse, pow_succ]

theorem pow_two {exponent : α → ℕ} (hExponent : CodeComputable exponent) :
    CodeComputable fun argument => 2 ^ exponent argument :=
  (iterate hExponent (const 1) (nat_mul snd (const 2))).of_eq fun _ => (pow_two_eq_iterate _).symm

theorem tails_eq_map_drop {β : Type*} : ∀ members : List β,
    members.tails = (List.range (members.length + 1)).map fun position => members.drop position
  | [] => rfl
  | member :: rest => by
      rw [List.tails_cons, tails_eq_map_drop rest, List.length_cons, List.range_succ_eq_map (n := rest.length + 1),
        List.map_cons, List.map_map]
      rfl

/-! ## Groups -/

theorem group {restrictions : α → List ℕ} {components : α → List Pattern} (hRestrictions : CodeComputable restrictions)
    (hComponents : CodeComputable components) :
    CodeComputable fun argument => (⟨restrictions argument, components argument⟩ : RestrictionBlocks.Group) := by
  obtain ⟨track, computable, tracks⟩ := hRestrictions.pair hComponents
  exact ⟨track, computable, tracks⟩

theorem groupRestrictions : CodeComputable fun group : RestrictionBlocks.Group => group.restrictions := by
  obtain ⟨track, computable, tracks⟩ := (fst : CodeComputable fun pair : List ℕ × List Pattern => pair.1)
  exact ⟨track, computable, fun group => tracks (group.restrictions, group.components)⟩

theorem groupComponents : CodeComputable fun group : RestrictionBlocks.Group => group.components := by
  obtain ⟨track, computable, tracks⟩ := (snd : CodeComputable fun pair : List ℕ × List Pattern => pair.2)
  exact ⟨track, computable, fun group => tracks (group.restrictions, group.components)⟩

theorem code_group_injective : Function.Injective (code : RestrictionBlocks.Group → ℕ) := by
  intro first second same
  simp only [show ∀ group : RestrictionBlocks.Group, code group = code (group.restrictions, group.components) from fun _ => rfl,
    code_pair, code_list, Nat.pair_eq_pair] at same
  obtain ⟨restrictions, components⟩ := same
  have restrictionsEqual : first.restrictions = second.restrictions := by
    have := Encodable.encode_injective restrictions
    simpa using this
  have componentsEqual : first.components = second.components :=
    (List.map_injective_iff.mpr patternCode_injective') (Encodable.encode_injective components)
  cases first; cases second
  simp_all

theorem usedRestrictions_codeComputable : CodeComputable₂ usedRestrictions :=
  list_filter (members := fun input : ℕ × Pattern => List.range input.1)
    (test := fun input index => mentions index input.2) (list_range fst)
    (mentions_codeComputable.comp (snd.pair (snd.comp fst)))

theorem shares_codeComputable : CodeComputable₂ shares :=
  list_any (members := fun input : List ℕ × List ℕ => input.1) (test := fun input index => input.2.contains index) fst
    (list_contains nat_injective (snd.comp fst) snd)

theorem insertUsing_codeComputable :
    CodeComputable fun input : ℕ × List ℕ × Pattern × List RestrictionBlocks.Group =>
      insertUsing input.1 input.2.1 input.2.2.1 input.2.2.2 := by
  have used : CodeComputable fun input : ℕ × List ℕ × Pattern × List RestrictionBlocks.Group => input.2.1 := fst.comp snd
  have groupsIn : CodeComputable fun input : ℕ × List ℕ × Pattern × List RestrictionBlocks.Group => input.2.2.2 :=
    snd.comp (snd.comp snd)
  have sharing : CodeComputable₂ fun (input : ℕ × List ℕ × Pattern × List RestrictionBlocks.Group) (group : RestrictionBlocks.Group) =>
      shares input.2.1 group.restrictions :=
    shares_codeComputable.comp ((used.comp fst).pair (groupRestrictions.comp snd))
  have notSharing : CodeComputable₂ fun (input : ℕ × List ℕ × Pattern × List RestrictionBlocks.Group) (group : RestrictionBlocks.Group) =>
      !shares input.2.1 group.restrictions := not sharing
  have joined : CodeComputable fun input : ℕ × List ℕ × Pattern × List RestrictionBlocks.Group =>
      input.2.2.2.filter fun group => shares input.2.1 group.restrictions :=
    list_filter (members := fun input : ℕ × List ℕ × Pattern × List RestrictionBlocks.Group => input.2.2.2)
      (test := fun input group => shares input.2.1 group.restrictions) groupsIn sharing
  have apart : CodeComputable fun input : ℕ × List ℕ × Pattern × List RestrictionBlocks.Group =>
      input.2.2.2.filter fun group => !shares input.2.1 group.restrictions :=
    list_filter (members := fun input : ℕ × List ℕ × Pattern × List RestrictionBlocks.Group => input.2.2.2)
      (test := fun input group => !shares input.2.1 group.restrictions) groupsIn notSharing
  have inJoined : CodeComputable₂ fun (input : ℕ × List ℕ × Pattern × List RestrictionBlocks.Group) (index : ℕ) =>
      (input.2.2.2.filter fun group => shares input.2.1 group.restrictions).any fun group =>
        group.restrictions.contains index :=
    list_any (members := fun pair : (ℕ × List ℕ × Pattern × List RestrictionBlocks.Group) × ℕ =>
        pair.1.2.2.2.filter fun group => shares pair.1.2.1 group.restrictions)
      (test := fun pair group => group.restrictions.contains pair.2) (joined.comp fst)
      (list_contains nat_injective (groupRestrictions.comp snd) (snd.comp fst))
  have restrictions : CodeComputable fun input : ℕ × List ℕ × Pattern × List RestrictionBlocks.Group =>
      (List.range input.1).filter fun index => input.2.1.contains index ||
        (input.2.2.2.filter fun group => shares input.2.1 group.restrictions).any fun group =>
          group.restrictions.contains index :=
    list_filter (members := fun input : ℕ × List ℕ × Pattern × List RestrictionBlocks.Group => List.range input.1)
      (test := fun input index => input.2.1.contains index ||
        (input.2.2.2.filter fun group => shares input.2.1 group.restrictions).any fun group =>
          group.restrictions.contains index)
      (list_range fst) (or (list_contains nat_injective (used.comp fst) snd) inJoined)
  have merged : CodeComputable fun input : ℕ × List ℕ × Pattern × List RestrictionBlocks.Group =>
      (⟨(List.range input.1).filter fun index => input.2.1.contains index ||
          (input.2.2.2.filter fun group => shares input.2.1 group.restrictions).any fun group =>
            group.restrictions.contains index,
        (input.2.2.2.filter fun group => shares input.2.1 group.restrictions).flatMap RestrictionBlocks.Group.components ++
          [input.2.2.1]⟩ : RestrictionBlocks.Group) :=
    group restrictions (list_append (list_flatMap (members := fun input : ℕ × List ℕ × Pattern × List RestrictionBlocks.Group =>
        input.2.2.2.filter fun group => shares input.2.1 group.restrictions)
      (image := fun _ group => group.components) joined (groupComponents.comp snd))
      (list_cons (fst.comp (snd.comp snd)) list_nil))
  exact (list_append apart (list_cons merged list_nil)).of_eq fun _ => rfl

theorem insertComponent_codeComputable :
    CodeComputable fun input : ℕ × Pattern × List RestrictionBlocks.Group => insertComponent input.1 input.2.1 input.2.2 :=
  (insertUsing_codeComputable.comp (fst.pair ((usedRestrictions_codeComputable.comp (fst.pair (fst.comp snd))).pair
    ((fst.comp snd).pair (snd.comp snd))))).of_eq fun _ => rfl

theorem groupsThrough_codeComputable :
    CodeComputable fun input : List ℕ × ℕ × List Pattern => groupsThrough input.1 input.2.1 input.2.2 :=
  list_foldl (members := fun input : List ℕ × ℕ × List Pattern => input.2.2)
    (start := fun _ => ([] : List RestrictionBlocks.Group))
    (step := fun input groups component => insertUsing input.2.1
      ((usedRestrictions input.2.1 component).filter input.1.contains) component groups)
    (snd.comp snd) list_nil
    (insertUsing_codeComputable.comp ((fst.comp (snd.comp fst)).pair
      ((list_filter (members := fun input : (List ℕ × ℕ × List Pattern) × List RestrictionBlocks.Group × Pattern =>
          usedRestrictions input.1.2.1 input.2.2)
        (test := fun input index => input.1.1.contains index)
        (usedRestrictions_codeComputable.comp ((fst.comp (snd.comp fst)).pair (snd.comp snd)))
        (list_contains nat_injective (fst.comp (fst.comp fst)) snd)).pair ((snd.comp snd).pair (fst.comp snd)))))

theorem groups_codeComputable : CodeComputable groups :=
  list_foldl (members := fun form : Prenex => form.components) (start := fun _ => ([] : List RestrictionBlocks.Group))
    (step := fun form groups component => insertComponent form.count component groups) components list_nil
    (insertComponent_codeComputable.comp ((count.comp fst).pair ((snd.comp snd).pair (fst.comp snd))))

/-! ## Renamings of groups and copies -/

/-- The renumberings of a group's variables, as a family of renamings indexed by codes. -/
def groupIndexFamily (data index : ℕ) : ℕ :=
  Prenex.groupIndex data.unpair.1 (Denumerable.ofNat (List ℕ) data.unpair.2) index

theorem groupIndexFamily_computable : Computable₂ groupIndexFamily := by
  have count : Computable fun input : ℕ × ℕ => input.1.unpair.1 :=
    Primrec.fst.to_comp.comp (Primrec.unpair.to_comp.comp Computable.fst)
  have restrictions : Computable fun input : ℕ × ℕ => Denumerable.ofNat (List ℕ) input.1.unpair.2 :=
    (Primrec.ofNat (List ℕ)).to_comp.comp (Primrec.snd.to_comp.comp (Primrec.unpair.to_comp.comp Computable.fst))
  exact (Computable.cond ((Primrec.nat_lt.decide.to_comp).comp Computable.snd count)
    ((Primrec.list_idxOf.to_comp).comp Computable.snd restrictions)
    (Primrec.nat_add.to_comp.comp (Primrec.nat_sub.to_comp.comp Computable.snd count)
      (Primrec.list_length.to_comp.comp restrictions))).of_eq fun input => by
    by_cases below : input.2 < input.1.unpair.1 <;> simp [groupIndexFamily, Prenex.groupIndex, below]

theorem rename_groupIndex :
    CodeComputable fun input : (ℕ × List ℕ) × Pattern => rename (Prenex.groupIndex input.1.1 input.1.2) input.2 :=
  ((rename' groupIndexFamily_computable).comp ((code'.comp fst).pair snd)).of_eq fun input => by
    simp only [rename]
    congr 1
    funext index
    simp [groupIndexFamily, code_pair, ofNat_code_list]

theorem molecule_codeComputable : CodeComputable₂ Prenex.molecule :=
  prenex (list_length (groupRestrictions.comp snd))
    (list_map (members := fun input : ℕ × RestrictionBlocks.Group => input.2.components)
      (image := fun input component => rename (Prenex.groupIndex input.1 input.2.restrictions) component)
      (groupComponents.comp snd) (rename_groupIndex.comp (((fst.comp fst).pair (groupRestrictions.comp
        (snd.comp fst))).pair snd)))

theorem outsideOf_codeComputable : CodeComputable₂ outsideOf :=
  list_filter (members := fun input : ℕ × List ℕ => List.range input.1)
    (test := fun input index => !input.2.contains index) (list_range fst)
    (not (list_contains nat_injective (snd.comp fst) snd))

/-- The places of a split, as a family indexed by codes. -/
def splitPlaceFamily (data index : ℕ) : ℕ :=
  splitPlace data.unpair.1 (Denumerable.ofNat (List ℕ) data.unpair.2.unpair.1)
    (Denumerable.ofNat (List ℕ) data.unpair.2.unpair.2) index

theorem splitPlace_codeComputable :
    CodeComputable fun input : ℕ × List ℕ × List ℕ × ℕ => splitPlace input.1 input.2.1 input.2.2.1 input.2.2.2 := by
  have first : CodeComputable fun input : ℕ × List ℕ × List ℕ × ℕ => input.2.1 := fst.comp snd
  have second : CodeComputable fun input : ℕ × List ℕ × List ℕ × ℕ => input.2.2.1 := fst.comp (snd.comp snd)
  have index : CodeComputable fun input : ℕ × List ℕ × List ℕ × ℕ => input.2.2.2 := snd.comp (snd.comp snd)
  have others := list_filter (members := fun input : ℕ × List ℕ × List ℕ × ℕ => List.range input.1)
    (test := fun input other => !input.2.1.contains other && !input.2.2.1.contains other) (list_range fst)
    (and (not (list_contains nat_injective (first.comp fst) snd)) (not (list_contains nat_injective (second.comp fst)
      snd)))
  exact (ite (list_contains nat_injective second index) (list_idxOf nat_injective second index)
    (ite (list_contains nat_injective first index) (nat_add (list_length second) (list_idxOf nat_injective first index))
      (nat_add (nat_add (list_length second) (list_length first)) (list_idxOf nat_injective others index)))).of_eq
    fun _ => rfl

theorem splitOrder_codeComputable :
    CodeComputable fun input : ℕ × List ℕ × List ℕ => splitOrder input.1 input.2.1 input.2.2 :=
  list_map (members := fun input : ℕ × List ℕ × List ℕ => List.range input.1)
    (image := fun input index => splitPlace input.1 input.2.1 input.2.2 index) (list_range fst)
    (splitPlace_codeComputable.comp ((fst.comp fst).pair ((fst.comp (snd.comp fst)).pair ((snd.comp (snd.comp fst)).pair
      snd))))

theorem copyOf_codeComputable (block : Block) : CodeComputable₂ (copyOf block) := by
  have order := splitOrder_codeComputable.comp (fst.pair ((outsideOf_codeComputable.comp (fst.pair
    (groupRestrictions.comp snd))).pair (groupRestrictions.comp snd)))
  exact toPattern_codeComputable block (prenex (list_length (groupRestrictions.comp snd))
    (list_map (members := fun input : ℕ × RestrictionBlocks.Group => input.2.components)
      (image := fun input component => rename (Prenex.permute input.1 (splitOrder input.1
        (outsideOf input.1 input.2.restrictions) input.2.restrictions)) component)
      (groupComponents.comp snd) (rename_permute.comp (((fst.comp fst).pair (order.comp fst)).pair snd))))

/-! ## Pruning, keeping one of each replication -/

theorem prune_codeComputable : CodeComputable Prenex.prune := by
  have used := list_filter (members := fun form : Prenex => List.range form.count)
    (test := fun form index => form.components.any (mentions index)) (list_range count)
    (list_any (components.comp fst) (mentions_codeComputable.comp ((snd.comp fst).pair snd)))
  exact (prenex (list_length used) (list_map (members := fun form : Prenex => form.components)
    (image := fun form component => rename (Prenex.groupIndex form.count
      ((List.range form.count).filter fun index => form.components.any (mentions index))) component)
    components (rename_groupIndex.comp (((count.comp fst).pair (used.comp fst)).pair snd)))).of_eq fun _ => rfl

theorem isReplicated_eq (block : ReplicationBlock) (pattern : Pattern) :
    isReplicated block pattern = (isApply pattern && decide ((applyArguments pattern).length = 1) &&
      decide (applyLabel pattern = block.replicate)) := by
  cases pattern with
  | apply label arguments =>
      rcases arguments with _ | ⟨argument, _ | ⟨second, rest⟩⟩
      · rfl
      · by_cases same : label = block.replicate <;> simp [isReplicated, isApply, applyArguments, applyLabel, same]
      · rfl
  | _ => rfl

/-- **Whether a pattern is a replication of the block is computable on codes.** -/
theorem isReplicated_codeComputable (block : ReplicationBlock) : CodeComputable (isReplicated block) :=
  (and (and isApply_codeComputable (nat_eq (list_length applyArguments_codeComputable) (const 1)))
    (stringEq.comp (applyLabel_codeComputable.pair (const block.replicate)))).of_eq
    fun pattern => (isReplicated_eq block pattern).symm

theorem argumentOf?_eq (pattern : Pattern) :
    argumentOf? pattern = if isApply pattern && decide ((applyArguments pattern).length = 1) then
      (applyArguments pattern).getD 0 (.bvar 0) else pattern := by
  cases pattern with
  | apply label arguments =>
      rcases arguments with _ | ⟨argument, _ | ⟨second, rest⟩⟩ <;> simp [argumentOf?, isApply, applyArguments]
  | _ => rfl

theorem argumentOf?_codeComputable : CodeComputable argumentOf? :=
  (ite (and isApply_codeComputable (nat_eq (list_length applyArguments_codeComputable) (const 1)))
    (list_getD (.bvar 0) applyArguments_codeComputable (const 0)) CodeComputable.id).of_eq
    fun pattern => (argumentOf?_eq pattern).symm

/-! ## Keeping one of each replication -/

/-- The member a tail keeps: its first, unless a replication repeated later in it. -/
def keptHead (block : ReplicationBlock) (tail : List Pattern) : Option Pattern :=
  Option.casesOn (motive := fun _ => Option Pattern) tail.head? none fun first =>
    if isReplicated block first && tail.tail.contains first then none else some first

theorem dedupReplicated_eq_tails (block : ReplicationBlock) : ∀ components : List Pattern,
    dedupReplicated block components = components.tails.filterMap (keptHead block)
  | [] => rfl
  | component :: rest => by
      rw [List.tails_cons, List.filterMap_cons, ← dedupReplicated_eq_tails block rest, dedupReplicated]
      by_cases dropped : isReplicated block component = true ∧ component ∈ rest
      · simp [keptHead, dropped]
      · simp [keptHead, dropped]

theorem dedupReplicated_codeComputable (block : ReplicationBlock) : CodeComputable (dedupReplicated block) := by
  have tails : CodeComputable fun components : List Pattern => components.tails :=
    (list_map (members := fun components : List Pattern => List.range (components.length + 1))
      (image := fun components position => components.drop position) (list_range (nat_add (list_length id) (const 1)))
      (list_drop snd fst)).of_eq fun components => (tails_eq_map_drop components).symm
  have kept : CodeComputable (keptHead block) :=
    option_casesOn (option := fun tail : List Pattern => tail.head?) (onNone := fun _ => (none : Option Pattern))
      (onSome := fun tail first => if isReplicated block first && tail.tail.contains first then none else some first)
      (list_head? id) option_none
      (ite (and ((isReplicated_codeComputable block).comp snd)
          (list_contains patternCode_injective' (list_tail fst) snd)) option_none (option_some snd))
  exact (list_filterMap (members := fun components : List Pattern => components.tails)
    (image := fun _ tail => keptHead block tail) tails (kept.comp snd)).of_eq
    fun components => (dedupReplicated_eq_tails block components).symm

/-! ## Signatures and reading orders -/

theorem profileCode_codeComputable (block : ReplicationBlock) :
    CodeComputable fun input : ℕ × Pattern => profileCode block input.1 input.2 :=
  (nat_add (nat_mul (const 2) (list_length (usedRestrictions_codeComputable)))
    (ite ((isReplicated_codeComputable block).comp snd) (const 1) (const 0))).of_eq fun input => by
    simp only [profileCode]
    rfl

theorem signatureOf_codeComputable (block : ReplicationBlock) :
    CodeComputable fun input : Prenex × ℕ => signatureOf block input.1 input.2 := by
  have mentioning := list_filter (members := fun input : Prenex × ℕ => input.1.components)
    (test := fun input component => mentions input.2 component) (components.comp fst)
    (mentions_codeComputable.comp ((snd.comp fst).pair snd))
  have profiles := list_map (members := fun input : Prenex × ℕ => input.1.components.filter (mentions input.2))
    (image := fun input component => profileCode block input.1.count component) mentioning
    ((profileCode_codeComputable block).comp ((count.comp (fst.comp fst)).pair snd))
  exact list_sum (list_map (members := fun input : Prenex × ℕ =>
      ((input.1.components.filter (mentions input.2)).map (profileCode block input.1.count)).dedup)
    (image := fun _ profile => 2 ^ profile) (list_dedup profiles) (pow_two snd))

/-- The keyed arrangements of a list, with the key the signatures of a block, as a function of the block and the
list. -/
def arrangements (block : ReplicationBlock) (fuel : ℕ) (input : Prenex × List ℕ) : List (List ℕ) :=
  keyedArrangements (signatureOf block input.1) fuel input.2

/-- The members of a list of least key under the signatures of a block. -/
def leastKeyed (block : ReplicationBlock) (input : Prenex × List ℕ) : List ℕ :=
  if input.2.length = 0 then [] else
    input.2.filter fun element => signatureOf block input.1 element =
      input.2.tail.foldr (fun other low => min (signatureOf block input.1 other) low)
        (signatureOf block input.1 (input.2.getD 0 0))

theorem arrangements_succ (block : ReplicationBlock) (fuel : ℕ) (input : Prenex × List ℕ) :
    arrangements block (fuel + 1) input =
      if input.2.length = 0 then [[]] else
        (List.zipWith (fun chosen arranged => arranged.map (chosen :: ·)) (leastKeyed block input)
          (((leastKeyed block input).map fun chosen => (input.1, input.2.erase chosen)).map
            (arrangements block fuel))).flatten := by
  rcases input with ⟨form, _ | ⟨first, rest⟩⟩
  · rfl
  · simp only [arrangements, leastKeyed, List.length_cons, Nat.add_one_ne_zero, if_false, List.map_map,
      Function.comp_def, zipWith_map_self, keyedArrangements, List.tail_cons, List.getD_cons_zero]
    rw [List.flatMap_def]

theorem signatureKey_codeComputable (block : ReplicationBlock) :
    CodeComputable₂ fun (input : Prenex × List ℕ) (element : ℕ) => signatureOf block input.1 element :=
  (signatureOf_codeComputable block).comp ((fst.comp fst).pair snd)

theorem leastKey_codeComputable (block : ReplicationBlock) :
    CodeComputable fun input : Prenex × List ℕ =>
      input.2.tail.foldr (fun other low => min (signatureOf block input.1 other) low)
        (signatureOf block input.1 (input.2.getD 0 0)) :=
  list_foldr (members := fun input : Prenex × List ℕ => input.2.tail)
    (start := fun input => signatureOf block input.1 (input.2.getD 0 0))
    (step := fun input other low => min (signatureOf block input.1 other) low) (list_tail snd)
    ((signatureKey_codeComputable block).comp (CodeComputable.id.pair (list_getD 0 snd (const 0))))
    ((of_computable₂ Primrec.nat_min.to_comp).comp
      (((signatureKey_codeComputable block).comp (fst.pair (fst.comp snd))).pair (snd.comp snd)))

theorem leastKeyed_codeComputable (block : ReplicationBlock) : CodeComputable (leastKeyed block) := by
  have filtered : CodeComputable fun input : Prenex × List ℕ =>
      input.2.filter fun element => decide (signatureOf block input.1 element =
        input.2.tail.foldr (fun other low => min (signatureOf block input.1 other) low)
          (signatureOf block input.1 (input.2.getD 0 0))) :=
    list_filter (members := fun input : Prenex × List ℕ => input.2)
      (test := fun input element => decide (signatureOf block input.1 element =
        input.2.tail.foldr (fun other low => min (signatureOf block input.1 other) low)
          (signatureOf block input.1 (input.2.getD 0 0)))) snd
      (nat_eq (signatureKey_codeComputable block) ((leastKey_codeComputable block).comp fst))
  refine (ite (nat_eq (list_length snd) (const 0)) list_nil filtered).of_eq fun input => ?_
  simp only [leastKeyed, decide_eq_true_eq]

theorem arrangementsCalls_codeComputable (block : ReplicationBlock) :
    CodeComputable₂ fun (_ : ℕ) (input : Prenex × List ℕ) =>
      (leastKeyed block input).map fun chosen => (input.1, input.2.erase chosen) :=
  list_map (members := fun pair : ℕ × (Prenex × List ℕ) => leastKeyed block pair.2)
    (image := fun pair chosen => (pair.2.1, pair.2.2.erase chosen)) ((leastKeyed_codeComputable block).comp snd)
    ((fst.comp (snd.comp fst)).pair (list_erase nat_injective (snd.comp (snd.comp fst)) snd))

theorem prefixed_codeComputable :
    CodeComputable fun input : (ℕ × (Prenex × List ℕ) × List (List (List ℕ))) × ℕ × List (List ℕ) =>
      input.2.2.map (input.2.1 :: ·) :=
  list_map (members := fun input : (ℕ × (Prenex × List ℕ) × List (List (List ℕ))) × ℕ × List (List ℕ) =>
      input.2.2) (image := fun input arranged => input.2.1 :: arranged) (snd.comp snd)
    (list_cons (fst.comp (snd.comp fst)) snd)

theorem arrangementsCombine_codeComputable (block : ReplicationBlock) :
    CodeComputable fun input : ℕ × (Prenex × List ℕ) × List (List (List ℕ)) =>
      if input.2.1.2.length = 0 then [[]] else
        (List.zipWith (fun chosen arranged => arranged.map (chosen :: ·)) (leastKeyed block input.2.1)
          input.2.2).flatten := by
  have zipped := list_zipWith (lefts := fun input : ℕ × (Prenex × List ℕ) × List (List (List ℕ)) =>
      leastKeyed block input.2.1) (rights := fun input => input.2.2)
    (combine := fun _ chosen arranged => arranged.map (chosen :: ·)) 0 []
    ((leastKeyed_codeComputable block).comp (fst.comp snd)) (snd.comp snd) prefixed_codeComputable
  refine (ite (nat_eq (list_length (snd.comp (fst.comp snd))) (const 0)) (const [[]])
    (list_flatten zipped)).of_eq fun input => ?_
  simp only [decide_eq_true_eq]

theorem arrangements_codeComputable (block : ReplicationBlock) : CodeComputable₂ (arrangements block) :=
  fuel (run := arrangements block) (base := fun _ => [[]])
    (calls := fun _ input => (leastKeyed block input).map fun chosen => (input.1, input.2.erase chosen))
    (combine := fun _ input values => if input.2.length = 0 then [[]] else
      (List.zipWith (fun chosen arranged => arranged.map (chosen :: ·)) (leastKeyed block input) values).flatten)
    (fun _ => rfl) (arrangements_succ block) (const _) (arrangementsCalls_codeComputable block)
    (arrangementsCombine_codeComputable block)

theorem inverse_codeComputable : CodeComputable fun input : ℕ × List ℕ => inverse input.1 input.2 :=
  list_map (members := fun input : ℕ × List ℕ => List.range input.1)
    (image := fun input index => input.2.idxOf index) (list_range fst)
    (list_idxOf nat_injective (snd.comp fst) snd)

theorem readingOrders_codeComputable (block : ReplicationBlock) : CodeComputable (readingOrders block) := by
  have arranged : CodeComputable fun form : Prenex => arrangements block form.count (form, List.range form.count) :=
    CodeComputable.comp (f := fun pair : ℕ × (Prenex × List ℕ) => arrangements block pair.1 pair.2)
      (g := fun form : Prenex => (form.count, (form, List.range form.count))) (arrangements_codeComputable block)
      (count.pair (CodeComputable.id.pair (list_range count)))
  have inverted : CodeComputable₂ fun (form : Prenex) (order : List ℕ) => inverse form.count order :=
    CodeComputable.comp (f := fun pair : ℕ × List ℕ => inverse pair.1 pair.2)
      (g := fun input : Prenex × List ℕ => (input.1.count, input.2)) inverse_codeComputable ((count.comp fst).pair snd)
  have keyed : CodeComputable fun form : Prenex =>
      (keyedArrangements (signatureOf block form) form.count (List.range form.count)).map (inverse form.count) :=
    list_map (members := fun form : Prenex => arrangements block form.count (form, List.range form.count))
      (image := fun form order => inverse form.count order) arranged inverted
  exact (ite (const block.refined) keyed (orders_codeComputable (list_range count))).of_eq fun form => by
    simp only [readingOrders]

/-! ## The replicated molecules of a block -/

theorem replicatedOf_eq (block : ReplicationBlock) (canonical : Pattern → Pattern) (inner : Prenex) :
    replicatedOf block canonical inner = (groups inner).map fun group =>
      if decide ((Prenex.molecule inner.count group).count = 0) &&
          decide ((Prenex.molecule inner.count group).components.length = 1) &&
          isReplicated block ((Prenex.molecule inner.count group).components.getD 0 (.bvar 0)) then
        .apply block.replicate [canonical (argumentOf? ((Prenex.molecule inner.count group).components.getD 0
          (.bvar 0)))]
      else .apply block.replicate [canonical (Prenex.toPattern block.toBlock (Prenex.molecule inner.count group))] := by
  simp only [replicatedOf]
  apply List.map_congr_left
  intro group _
  generalize Prenex.molecule inner.count group = form
  rcases form with ⟨_ | count, _ | ⟨component, _ | ⟨second, rest⟩⟩⟩
  · simp
  · cases component with
    | apply label arguments =>
        rcases arguments with _ | ⟨argument, _ | ⟨other, more⟩⟩
        · simp [isReplicated]
        · by_cases same : label = block.replicate
          · subst same; simp [isReplicated, argumentOf?]
          · simp [isReplicated, same]
        · simp [isReplicated]
    | _ => simp [isReplicated]
  · simp
  · simp
  · simp
  · simp

theorem replicatedOf_codeComputable (block : ReplicationBlock) {canonical : Pattern → Pattern}
    (hCanonical : CodeComputable canonical) :
    CodeComputable fun inner : Prenex => replicatedOf block canonical inner := by
  have molecule : CodeComputable₂ fun (inner : Prenex) (group : RestrictionBlocks.Group) => Prenex.molecule inner.count group :=
    molecule_codeComputable.comp ((count.comp fst).pair snd)
  have only := list_getD (.bvar 0) (components.comp molecule) (const 0)
  exact (list_map (members := fun inner : Prenex => groups inner)
    (image := fun inner group =>
      if decide ((Prenex.molecule inner.count group).count = 0) &&
          decide ((Prenex.molecule inner.count group).components.length = 1) &&
          isReplicated block ((Prenex.molecule inner.count group).components.getD 0 (.bvar 0)) then
        .apply block.replicate [canonical (argumentOf? ((Prenex.molecule inner.count group).components.getD 0
          (.bvar 0)))]
      else .apply block.replicate [canonical (Prenex.toPattern block.toBlock (Prenex.molecule inner.count group))])
    groups_codeComputable
    (ite (and (and (nat_eq (count.comp molecule) (const 0)) (nat_eq (list_length (components.comp molecule)) (const 1)))
        ((isReplicated_codeComputable block).comp only))
      (apply (const _) (list_cons (hCanonical.comp (argumentOf?_codeComputable.comp only)) list_nil))
      (apply (const _) (list_cons (hCanonical.comp (toPattern_codeComputable block.toBlock molecule)) list_nil)))).of_eq
    fun inner => (replicatedOf_eq block canonical inner).symm

/-! ## Absorption, judged by an oracle -/

/-- The candidate copies of the component at a position: the groups of the other components linked through the
restrictions it does not use. -/
def candidatesAt (form : Prenex) (position : ℕ) : List RestrictionBlocks.Group :=
  groupsThrough ((List.range form.count).filter fun index => !mentions index (form.components.getD position (.bvar 0)))
    form.count (form.components.eraseIdx position)

/-- Whether a group is a copy of a replicated component, judged by `canonical`. -/
def isCopy (block : ReplicationBlock) (canonical : Pattern → Pattern) (form : Prenex) (replicated : Pattern)
    (group : RestrictionBlocks.Group) : Bool :=
  (canonical (copyOf block.toBlock form.count group) ==
      canonical (rename (Prenex.groupIndex form.count (outsideOf form.count group.restrictions))
        (argumentOf? replicated))) &&
    !isReplicated block (canonical (copyOf block.toBlock form.count group)) &&
    group.components.all (fun component => !isReplicated block component ||
      decide (size (canonical (argumentOf? component)) < size (canonical (argumentOf? replicated)))) &&
    (List.range form.count).all (fun index => !mentions index replicated || group.components.any (mentions index))

/-- One absorption at a position. -/
def absorbAt (block : ReplicationBlock) (canonical : Pattern → Pattern) (form : Prenex) (position : ℕ) :
    Option Prenex :=
  if isReplicated block (form.components.getD position (.bvar 0)) then
    ((candidatesAt form position).find? (isCopy block canonical form (form.components.getD position (.bvar 0)))).map
      fun group => ⟨form.count, ((candidatesAt form position).erase group).flatMap RestrictionBlocks.Group.components ++
        [form.components.getD position (.bvar 0)]⟩
  else none

theorem findSome?_congr {β γ : Type*} {first second : β → Option γ} :
    ∀ {members : List β}, (∀ member ∈ members, first member = second member) →
      members.findSome? first = members.findSome? second
  | [], _ => rfl
  | member :: rest, same => by
      rw [List.findSome?_cons, List.findSome?_cons, same member List.mem_cons_self,
        findSome?_congr fun other inRest => same other (List.mem_cons_of_mem _ inRest)]

theorem find?_congr {β : Type*} {first second : β → Bool} :
    ∀ {members : List β}, (∀ member ∈ members, first member = second member) →
      members.find? first = members.find? second
  | [], _ => rfl
  | member :: rest, same => by
      rw [List.find?_cons, List.find?_cons, same member List.mem_cons_self,
        find?_congr fun other inRest => same other (List.mem_cons_of_mem _ inRest)]

/-- **One absorption is the first absorption at a position.** -/
theorem absorbOnce_eq (block : ReplicationBlock) (canonical : Pattern → Pattern) (form : Prenex) :
    absorbOnce block canonical form = (List.range form.components.length).findSome? (absorbAt block canonical form) := by
  unfold absorbOnce
  apply findSome?_congr
  intro position member
  have inside : position < form.components.length := List.mem_range.mp member
  rw [List.getElem?_eq_getElem inside]
  have component : form.components.getD position (.bvar 0) = form.components[position] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inside, Option.getD_some]
  simp only [absorbAt, candidatesAt, component]
  unfold isCopy
  generalize form.components[position] = replicated
  cases replicated with
  | apply label arguments =>
      rcases arguments with _ | ⟨argument, _ | ⟨second, rest⟩⟩
      · simp [isReplicated]
      · by_cases same : label = block.replicate
        · subst same
          simp only [isReplicated, argumentOf?, beq_self_eq_true, if_true]
          rfl
        · simp [isReplicated, same]
      · simp [isReplicated]
  | _ => simp [isReplicated]

/-- **The patterns an absorption may judge**: for each replicated component, its argument, and for each candidate
copy, the copy, the argument renamed into it, and the arguments of the copy's components. -/
def absorbQueries (block : ReplicationBlock) (form : Prenex) : List Pattern :=
  (List.range form.components.length).flatMap fun position =>
    if isReplicated block (form.components.getD position (.bvar 0)) then
      argumentOf? (form.components.getD position (.bvar 0)) ::
        (candidatesAt form position).flatMap fun group => copyOf block.toBlock form.count group ::
          rename (Prenex.groupIndex form.count (outsideOf form.count group.restrictions))
            (argumentOf? (form.components.getD position (.bvar 0))) ::
          group.components.map argumentOf?
    else []

theorem all_congr' {β : Type*} {first second : β → Bool} :
    ∀ {members : List β}, (∀ member ∈ members, first member = second member) → members.all first = members.all second
  | [], _ => rfl
  | member :: rest, same => by
      rw [List.all_cons, List.all_cons, same member List.mem_cons_self,
        all_congr' fun other inRest => same other (List.mem_cons_of_mem _ inRest)]

/-- **Two oracles agreeing on a copy's queries judge it alike.** -/
theorem isCopy_congr (block : ReplicationBlock) {first second : Pattern → Pattern} (form : Prenex)
    (replicated : Pattern) (group : RestrictionBlocks.Group)
    (same : ∀ query ∈ argumentOf? replicated :: copyOf block.toBlock form.count group ::
      rename (Prenex.groupIndex form.count (outsideOf form.count group.restrictions)) (argumentOf? replicated) ::
      group.components.map argumentOf?, first query = second query) :
    isCopy block first form replicated group = isCopy block second form replicated group := by
  have argument := same (argumentOf? replicated) List.mem_cons_self
  have copy := same (copyOf block.toBlock form.count group) (by simp)
  have renamed := same (rename (Prenex.groupIndex form.count (outsideOf form.count group.restrictions))
    (argumentOf? replicated)) (by simp)
  have parts : group.components.all (fun component => !isReplicated block component ||
        decide (size (first (argumentOf? component)) < size (first (argumentOf? replicated)))) =
      group.components.all (fun component => !isReplicated block component ||
        decide (size (second (argumentOf? component)) < size (second (argumentOf? replicated)))) :=
    all_congr' fun component inGroup => by
      rw [same (argumentOf? component) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_map_of_mem inGroup)))), argument]
  unfold isCopy
  rw [copy, renamed, parts]

/-- **Absorption judged by two oracles agreeing on its queries is one absorption.** -/
theorem absorbOnce_congr (block : ReplicationBlock) {first second : Pattern → Pattern} (form : Prenex)
    (same : ∀ query ∈ absorbQueries block form, first query = second query) :
    absorbOnce block first form = absorbOnce block second form := by
  rw [absorbOnce_eq, absorbOnce_eq]
  apply findSome?_congr
  intro position inRange
  unfold absorbAt
  split_ifs with replicated
  · congr 1
    apply find?_congr
    intro group candidate
    apply isCopy_congr
    intro query member
    apply same
    simp only [absorbQueries, List.mem_flatMap, List.mem_range]
    refine ⟨position, List.mem_range.mp inRange, ?_⟩
    rw [if_pos replicated]
    simp only [List.mem_cons, List.mem_flatMap] at member ⊢
    rcases member with rfl | rfl | rfl | member
    · exact .inl rfl
    · exact .inr ⟨group, candidate, .inl rfl⟩
    · exact .inr ⟨group, candidate, .inr (.inl rfl)⟩
    · exact .inr ⟨group, candidate, .inr (.inr member)⟩
  · rfl

/-- The value of a table at a pattern, the pattern itself if absent. -/
def lookupIn (table : List (Pattern × Pattern)) (pattern : Pattern) : Pattern :=
  ((table.find? fun entry => decide (entry.1 = pattern)).map Prod.snd).getD pattern

/-- **A table of an oracle's answers answers as the oracle** on its questions. -/
theorem lookupIn_zip (oracle : Pattern → Pattern) :
    ∀ (questions : List Pattern) (pattern : Pattern), pattern ∈ questions →
      lookupIn (questions.map fun question => (question, oracle question)) pattern = oracle pattern
  | [], _, member => absurd member (List.not_mem_nil)
  | question :: rest, pattern, member => by
      by_cases same : question = pattern
      · subst same; simp [lookupIn]
      · have later : pattern ∈ rest := (List.mem_cons.mp member).resolve_left (Ne.symm same)
        have recurse := lookupIn_zip oracle rest pattern later
        simp only [lookupIn, List.map_cons, List.find?_cons, same, decide_false] at recurse ⊢
        exact recurse

theorem lookupIn_codeComputable : CodeComputable₂ lookupIn :=
  option_getD (option_map (list_find? (members := fun input : List (Pattern × Pattern) × Pattern => input.1)
      (test := fun input entry => decide (entry.1 = input.2)) fst
      (patternEq.comp ((fst.comp snd).pair (snd.comp fst)))) (snd.comp snd)) snd

/-! ## Absorption computable on codes -/

theorem candidatesAt_codeComputable : CodeComputable₂ candidatesAt := by
  have component : CodeComputable fun input : Prenex × ℕ => input.1.components.getD input.2 (.bvar 0) :=
    list_getD (.bvar 0) (components.comp fst) snd
  have allowed := list_filter (members := fun input : Prenex × ℕ => List.range input.1.count)
    (test := fun input index => !mentions index (input.1.components.getD input.2 (.bvar 0)))
    (list_range (count.comp fst)) (not (mentions_codeComputable.comp (snd.pair (component.comp fst))))
  exact groupsThrough_codeComputable.comp (allowed.pair ((count.comp fst).pair (list_eraseIdx (components.comp fst) snd)))

theorem isCopy_codeComputable (block : ReplicationBlock) :
    CodeComputable fun input : List (Pattern × Pattern) × Prenex × Pattern × RestrictionBlocks.Group =>
      isCopy block (lookupIn input.1) input.2.1 input.2.2.1 input.2.2.2 := by
  have table : CodeComputable fun input : List (Pattern × Pattern) × Prenex × Pattern × RestrictionBlocks.Group => input.1 := fst
  have form : CodeComputable fun input : List (Pattern × Pattern) × Prenex × Pattern × RestrictionBlocks.Group => input.2.1 :=
    fst.comp snd
  have replicated : CodeComputable fun input : List (Pattern × Pattern) × Prenex × Pattern × RestrictionBlocks.Group => input.2.2.1 :=
    fst.comp (snd.comp snd)
  have groupIn : CodeComputable fun input : List (Pattern × Pattern) × Prenex × Pattern × RestrictionBlocks.Group => input.2.2.2 :=
    snd.comp (snd.comp snd)
  have look : ∀ {query : List (Pattern × Pattern) × Prenex × Pattern × RestrictionBlocks.Group → Pattern}, CodeComputable query →
      CodeComputable fun input => lookupIn input.1 (query input) :=
    fun hQuery => lookupIn_codeComputable.comp (table.pair hQuery)
  have copied := (copyOf_codeComputable block.toBlock).comp ((count.comp form).pair groupIn)
  have renamedArgument := rename_groupIndex.comp (((count.comp form).pair (outsideOf_codeComputable.comp
    ((count.comp form).pair (groupRestrictions.comp groupIn)))).pair (argumentOf?_codeComputable.comp replicated))
  have componentTest : CodeComputable₂ fun (input : List (Pattern × Pattern) × Prenex × Pattern × RestrictionBlocks.Group)
      (component : Pattern) => !isReplicated block component ||
        decide (size (lookupIn input.1 (argumentOf? component)) <
          size (lookupIn input.1 (argumentOf? input.2.2.1))) :=
    or (not ((isReplicated_codeComputable block).comp snd))
      (nat_lt (size_codeComputable.comp (lookupIn_codeComputable.comp ((table.comp fst).pair
        (argumentOf?_codeComputable.comp snd))))
        (size_codeComputable.comp ((look (argumentOf?_codeComputable.comp replicated)).comp fst)))
  have indexTest : CodeComputable₂ fun (input : List (Pattern × Pattern) × Prenex × Pattern × RestrictionBlocks.Group) (index : ℕ) =>
      !mentions index input.2.2.1 || input.2.2.2.components.any (mentions index) :=
    or (not (mentions_codeComputable.comp (snd.pair (replicated.comp fst))))
      (list_any (members := fun pair : (List (Pattern × Pattern) × Prenex × Pattern × RestrictionBlocks.Group) × ℕ =>
          pair.1.2.2.2.components) (test := fun pair component => mentions pair.2 component)
        (groupComponents.comp (groupIn.comp fst)) (mentions_codeComputable.comp ((snd.comp fst).pair snd)))
  exact (and (and (and (patternEq.comp ((look copied).pair (look renamedArgument)))
      (not ((isReplicated_codeComputable block).comp (look copied))))
      (list_all (members := fun input : List (Pattern × Pattern) × Prenex × Pattern × RestrictionBlocks.Group =>
          input.2.2.2.components) (groupComponents.comp groupIn) componentTest))
    (list_all (members := fun input : List (Pattern × Pattern) × Prenex × Pattern × RestrictionBlocks.Group =>
        List.range input.2.1.count) (list_range (count.comp form)) indexTest)).of_eq fun input => by
    simp only [isCopy]
    rfl

/-- The block after absorbing a copy. -/
def absorbedBy (form : Prenex) (position : ℕ) (group : RestrictionBlocks.Group) : Prenex :=
  ⟨form.count, ((candidatesAt form position).erase group).flatMap RestrictionBlocks.Group.components ++
    [form.components.getD position (.bvar 0)]⟩

theorem absorbedBy_codeComputable :
    CodeComputable fun input : Prenex × ℕ × RestrictionBlocks.Group => absorbedBy input.1 input.2.1 input.2.2 := by
  have candidates : CodeComputable fun input : Prenex × ℕ × RestrictionBlocks.Group => candidatesAt input.1 input.2.1 :=
    CodeComputable.comp₂ candidatesAt_codeComputable fst (fst.comp snd)
  have rest : CodeComputable fun input : Prenex × ℕ × RestrictionBlocks.Group =>
      (candidatesAt input.1 input.2.1).erase input.2.2 :=
    list_erase (members := fun input : Prenex × ℕ × RestrictionBlocks.Group => candidatesAt input.1 input.2.1)
      (element := fun input : Prenex × ℕ × RestrictionBlocks.Group => input.2.2) code_group_injective candidates
      (snd.comp snd)
  have kept : CodeComputable fun input : Prenex × ℕ × RestrictionBlocks.Group =>
      ((candidatesAt input.1 input.2.1).erase input.2.2).flatMap RestrictionBlocks.Group.components :=
    list_flatMap (members := fun input : Prenex × ℕ × RestrictionBlocks.Group => (candidatesAt input.1 input.2.1).erase input.2.2)
      (image := fun _ group => group.components) rest (groupComponents.comp snd)
  have replicated : CodeComputable fun input : Prenex × ℕ × RestrictionBlocks.Group =>
      input.1.components.getD input.2.1 (.bvar 0) :=
    list_getD (.bvar 0) (components.comp fst) (fst.comp snd)
  exact (prenex (count.comp fst) (list_append kept (list_cons replicated list_nil))).of_eq fun _ => rfl

theorem absorbAt_eq (block : ReplicationBlock) (canonical : Pattern → Pattern) (form : Prenex) (position : ℕ) :
    absorbAt block canonical form position =
      if isReplicated block (form.components.getD position (.bvar 0)) then
        ((candidatesAt form position).find? (isCopy block canonical form
          (form.components.getD position (.bvar 0)))).map (absorbedBy form position)
      else none := rfl

theorem absorbAt_codeComputable (block : ReplicationBlock) :
    CodeComputable fun input : List (Pattern × Pattern) × Prenex × ℕ =>
      absorbAt block (lookupIn input.1) input.2.1 input.2.2 := by
  have replicated : CodeComputable fun input : List (Pattern × Pattern) × Prenex × ℕ =>
      input.2.1.components.getD input.2.2 (.bvar 0) :=
    list_getD (.bvar 0) (components.comp (fst.comp snd)) (snd.comp snd)
  have candidates : CodeComputable fun input : List (Pattern × Pattern) × Prenex × ℕ =>
      candidatesAt input.2.1 input.2.2 :=
    CodeComputable.comp₂ candidatesAt_codeComputable (fst.comp snd) (snd.comp snd)
  have judged : CodeComputable₂ fun (input : List (Pattern × Pattern) × Prenex × ℕ) (group : RestrictionBlocks.Group) =>
      isCopy block (lookupIn input.1) input.2.1 (input.2.1.components.getD input.2.2 (.bvar 0)) group :=
    CodeComputable.comp (f := fun input : List (Pattern × Pattern) × Prenex × Pattern × RestrictionBlocks.Group =>
        isCopy block (lookupIn input.1) input.2.1 input.2.2.1 input.2.2.2)
      (g := fun pair : (List (Pattern × Pattern) × Prenex × ℕ) × RestrictionBlocks.Group =>
        (pair.1.1, pair.1.2.1, pair.1.2.1.components.getD pair.1.2.2 (.bvar 0), pair.2))
      (isCopy_codeComputable block) ((fst.comp fst).pair ((fst.comp (snd.comp fst)).pair
        ((replicated.comp fst).pair snd)))
  have found : CodeComputable fun input : List (Pattern × Pattern) × Prenex × ℕ =>
      (candidatesAt input.2.1 input.2.2).find? (isCopy block (lookupIn input.1) input.2.1
        (input.2.1.components.getD input.2.2 (.bvar 0))) :=
    list_find? (members := fun input : List (Pattern × Pattern) × Prenex × ℕ => candidatesAt input.2.1 input.2.2)
      (test := fun input group => isCopy block (lookupIn input.1) input.2.1
        (input.2.1.components.getD input.2.2 (.bvar 0)) group) candidates judged
  have absorbed : CodeComputable₂ fun (input : List (Pattern × Pattern) × Prenex × ℕ) (group : RestrictionBlocks.Group) =>
      absorbedBy input.2.1 input.2.2 group :=
    CodeComputable.comp (f := fun input : Prenex × ℕ × RestrictionBlocks.Group =>
        absorbedBy input.1 input.2.1 input.2.2)
      (g := fun pair : (List (Pattern × Pattern) × Prenex × ℕ) × RestrictionBlocks.Group =>
        (pair.1.2.1, pair.1.2.2, pair.2))
      absorbedBy_codeComputable ((fst.comp (snd.comp fst)).pair ((snd.comp (snd.comp fst)).pair snd))
  have mapped : CodeComputable fun input : List (Pattern × Pattern) × Prenex × ℕ =>
      ((candidatesAt input.2.1 input.2.2).find? (isCopy block (lookupIn input.1) input.2.1
        (input.2.1.components.getD input.2.2 (.bvar 0)))).map (absorbedBy input.2.1 input.2.2) :=
    option_map (option := fun input : List (Pattern × Pattern) × Prenex × ℕ =>
        (candidatesAt input.2.1 input.2.2).find? (isCopy block (lookupIn input.1) input.2.1
          (input.2.1.components.getD input.2.2 (.bvar 0))))
      (image := fun input group => absorbedBy input.2.1 input.2.2 group) found absorbed
  exact (ite (test := fun input : List (Pattern × Pattern) × Prenex × ℕ =>
      isReplicated block (input.2.1.components.getD input.2.2 (.bvar 0)))
    ((isReplicated_codeComputable block).comp replicated) mapped option_none).of_eq
    fun input => (absorbAt_eq block _ _ _).symm

theorem absorbOnce_codeComputable (block : ReplicationBlock) :
    CodeComputable fun input : List (Pattern × Pattern) × Prenex =>
      absorbOnce block (lookupIn input.1) input.2 :=
  (list_findSome? (members := fun input : List (Pattern × Pattern) × Prenex => List.range input.2.components.length)
    (image := fun input position => absorbAt block (lookupIn input.1) input.2 position)
    (list_range (list_length (components.comp snd)))
    ((absorbAt_codeComputable block).comp ((fst.comp fst).pair ((snd.comp fst).pair snd)))).of_eq
    fun _ => (absorbOnce_eq block _ _).symm

theorem absorbQueries_codeComputable (block : ReplicationBlock) : CodeComputable (absorbQueries block) := by
  have replicated : CodeComputable₂ fun (form : Prenex) (position : ℕ) => form.components.getD position (.bvar 0) :=
    list_getD (.bvar 0) (components.comp fst) snd
  have perGroup : CodeComputable₂ fun (input : Prenex × ℕ) (group : RestrictionBlocks.Group) =>
      copyOf block.toBlock input.1.count group ::
        rename (Prenex.groupIndex input.1.count (outsideOf input.1.count group.restrictions))
          (argumentOf? (input.1.components.getD input.2 (.bvar 0))) :: group.components.map argumentOf? :=
    list_cons ((copyOf_codeComputable block.toBlock).comp ((count.comp (fst.comp fst)).pair snd))
      (list_cons (rename_groupIndex.comp (((count.comp (fst.comp fst)).pair (outsideOf_codeComputable.comp
        ((count.comp (fst.comp fst)).pair (groupRestrictions.comp snd)))).pair
          (argumentOf?_codeComputable.comp (replicated.comp fst))))
        (list_map (members := fun pair : (Prenex × ℕ) × RestrictionBlocks.Group => pair.2.components)
          (image := fun _ component => argumentOf? component) (groupComponents.comp snd)
          (argumentOf?_codeComputable.comp snd)))
  have perPosition : CodeComputable₂ fun (form : Prenex) (position : ℕ) =>
      if isReplicated block (form.components.getD position (.bvar 0)) then
        argumentOf? (form.components.getD position (.bvar 0)) ::
          (candidatesAt form position).flatMap fun group => copyOf block.toBlock form.count group ::
            rename (Prenex.groupIndex form.count (outsideOf form.count group.restrictions))
              (argumentOf? (form.components.getD position (.bvar 0))) ::
            group.components.map argumentOf?
      else [] :=
    ite ((isReplicated_codeComputable block).comp replicated)
      (list_cons (argumentOf?_codeComputable.comp replicated)
        (list_flatMap (members := fun input : Prenex × ℕ => candidatesAt input.1 input.2)
          (image := fun input group => copyOf block.toBlock input.1.count group ::
            rename (Prenex.groupIndex input.1.count (outsideOf input.1.count group.restrictions))
              (argumentOf? (input.1.components.getD input.2 (.bvar 0))) :: group.components.map argumentOf?)
          candidatesAt_codeComputable perGroup))
      list_nil
  exact list_flatMap (members := fun form : Prenex => List.range form.components.length)
    (image := fun form position => if isReplicated block (form.components.getD position (.bvar 0)) then
        argumentOf? (form.components.getD position (.bvar 0)) ::
          (candidatesAt form position).flatMap fun group => copyOf block.toBlock form.count group ::
            rename (Prenex.groupIndex form.count (outsideOf form.count group.restrictions))
              (argumentOf? (form.components.getD position (.bvar 0))) ::
            group.components.map argumentOf?
      else []) (list_range (list_length components)) perPosition

/-! ## Absorption rounds replayed from answers -/

/-- One absorption, the step `absorbRounds` repeats, staying put when no copy is found. -/
def absorbStep (block : ReplicationBlock) (canonical : Pattern → Pattern) (form : Prenex) : Prenex :=
  (absorbOnce block canonical form).getD form

theorem absorbRounds_eq_iterate (block : ReplicationBlock) (canonical : Pattern → Pattern) :
    ∀ (rounds : ℕ) (form : Prenex), absorbRounds block canonical rounds form = (absorbStep block canonical)^[rounds] form
  | 0, _ => rfl
  | rounds + 1, form => by
      rw [Function.iterate_succ_apply, absorbRounds]
      cases found : absorbOnce block canonical form with
      | none =>
          have fixed : absorbStep block canonical form = form := by simp [absorbStep, found]
          rw [fixed, Function.iterate_fixed fixed]
      | some next =>
          have stepped : absorbStep block canonical form = next := by simp [absorbStep, found]
          rw [stepped]
          exact absorbRounds_eq_iterate block canonical rounds next

/-- One absorption judged by the answers of a round to its queries: the canonical blocks of the queried patterns. -/
def replayStep (block : ReplicationBlock) (form : Prenex) (round : List (Prenex × Pattern)) : Prenex :=
  absorbStep block (lookupIn (List.zipWith Prod.mk (absorbQueries block form)
    (round.map fun answer => Prenex.toPattern block.toBlock answer.1))) form

/-- The absorptions judged by the answered rounds, one after another. -/
def replay (block : ReplicationBlock) (form : Prenex) (rounds : List (List (Prenex × Pattern))) : Prenex :=
  rounds.foldl (replayStep block) form

/-- **A round answered by an oracle replays as the oracle's absorption.** -/
theorem replayStep_answered (block : ReplicationBlock) (canonical : Pattern → Pattern) (form : Prenex)
    (oracle : Pattern → Prenex × Pattern) (answers : ∀ query, Prenex.toPattern block.toBlock (oracle query).1 =
      canonical query) :
    replayStep block form ((absorbQueries block form).map oracle) = absorbStep block canonical form := by
  unfold replayStep absorbStep
  rw [absorbOnce_congr block form (second := canonical)]
  intro query member
  rw [List.map_map, zipWith_map_self]
  have tabled := lookupIn_zip (fun query => Prenex.toPattern block.toBlock (oracle query).1)
    (absorbQueries block form) query member
  simp only [Function.comp_def] at tabled ⊢
  rw [tabled, answers]

/-! ## The normalization family -/

/-- The question that asks for a pattern's block normalized within the fuel below. -/
def canonicalQuestion (block : ReplicationBlock) (pattern : Pattern) : ℕ × Prenex × Pattern :=
  (0, decompose block.toBlock pattern, .bvar 0)

/-- **The normalizations within a fuel, as one family**: `0` normalizes a block, `1` reads a component's parts
again, `2` reads a named multiset's argument again, any other tag keeps the pattern. -/
def normalFamily (block : ReplicationBlock) (fuel : ℕ) (input : ℕ × Prenex × Pattern) : Prenex × Pattern :=
  if input.1 = 0 then (normalizeWith block fuel input.2.1, .bvar 0)
  else if input.1 = 1 then (Prenex.nil, recanonWith block fuel input.2.2)
  else if input.1 = 2 then (Prenex.nil, recanonMultisetWith block fuel input.2.2)
  else (Prenex.nil, input.2.2)

/-- The number of rounds: one per component to absorb and one to read for a block, one for a part, none to keep. -/
def normalCount (_ : ℕ) (input : ℕ × Prenex × Pattern) : ℕ :=
  if input.1 = 0 then input.2.1.components.length + 1 else if input.1 = 1 ∨ input.1 = 2 then 1 else 0

/-- The questions of the reading round of an absorbed block. -/
def readingQuestions (block : ReplicationBlock) (absorbed : Prenex) : List (ℕ × Prenex × Pattern) :=
  (readingOrders block absorbed).flatMap fun order => absorbed.components.map fun component =>
    (1, Prenex.nil, rename (Prenex.permute absorbed.count order) component)

/-- The least reading of an absorbed block, from the answers of its reading round. -/
def readingLeast (block : ReplicationBlock) (absorbed : Prenex) (values : List Pattern) : Prenex :=
  ⟨absorbed.count, least ((List.range (readingOrders block absorbed).length).map fun position =>
    dedupReplicated block (sortComponents ((values.drop (position * absorbed.components.length)).take
      absorbed.components.length)))⟩

/-- The question for a constructor argument outside a named multiset. -/
def argumentQuestion (block : ReplicationBlock) (argument : Pattern) : ℕ × Prenex × Pattern :=
  if isLambda argument then canonicalQuestion block (lambdaBody argument)
  else if isKept argument then (3, Prenex.nil, argument) else canonicalQuestion block argument

/-- A constructor argument read back from its answer. -/
def argumentAnswer (block : ReplicationBlock) (argument : Pattern) (answer : Prenex × Pattern) : Pattern :=
  if isLambda argument then withBody argument (Prenex.toPattern block.toBlock answer.1)
  else if isKept argument then answer.2 else Prenex.toPattern block.toBlock answer.1

/-- The questions of reading a component's parts again. -/
def recanonQuestions (block : ReplicationBlock) (component : Pattern) : List (ℕ × Prenex × Pattern) :=
  if isApply component then
    if decide (applyLabel component = block.restrict) then []
    else if block.multisets.contains (applyLabel component) then
      (applyArguments component).map fun argument => (2, Prenex.nil, argument)
    else (applyArguments component).map (argumentQuestion block)
  else if isBinder component then [canonicalQuestion block (binderBody component)]
  else if isCollection component then (collectionElements component).map (canonicalQuestion block)
  else []

/-- A component read again from the answers to its questions. -/
def recanonAnswer (block : ReplicationBlock) (component : Pattern) (answers : List (Prenex × Pattern)) : Pattern :=
  if isApply component then
    if decide (applyLabel component = block.restrict) then component
    else if block.multisets.contains (applyLabel component) then .apply (applyLabel component) (answers.map Prod.snd)
    else .apply (applyLabel component) (List.zipWith (argumentAnswer block) (applyArguments component) answers)
  else if isBinder component then
    withBody component (Prenex.toPattern block.toBlock (answers.getD 0 (Prenex.nil, .bvar 0)).1)
  else if isCollection component then
    withElements component (answers.map fun answer => Prenex.toPattern block.toBlock answer.1)
  else component

/-- The questions of reading a named multiset's argument again. -/
def multisetQuestions (block : ReplicationBlock) (argument : Pattern) : List (ℕ × Prenex × Pattern) :=
  if isOpenCollection argument then (collectionElements argument).map (canonicalQuestion block)
  else if isSubst argument then [] else [canonicalQuestion block argument]

/-- A named multiset's argument read again from the answers to its questions. -/
def multisetAnswer (block : ReplicationBlock) (argument : Pattern) (answers : List (Prenex × Pattern)) : Pattern :=
  if isOpenCollection argument then
    withElements argument (answers.map fun answer => Prenex.toPattern block.toBlock answer.1)
  else if isSubst argument then argument else multisetOf block.toBlock (answers.getD 0 (Prenex.nil, .bvar 0)).1

/-- The questions of the next round. -/
def normalAsk (block : ReplicationBlock) (_ : ℕ) (input : ℕ × Prenex × Pattern)
    (answers : List (List (Prenex × Pattern))) : List (ℕ × Prenex × Pattern) :=
  if input.1 = 0 then
    if answers.length < input.2.1.components.length then
      (absorbQueries block (replay block input.2.1 answers)).map (canonicalQuestion block)
    else readingQuestions block (replay block input.2.1 (answers.take input.2.1.components.length)).prune
  else if input.1 = 1 then recanonQuestions block input.2.2
  else if input.1 = 2 then multisetQuestions block input.2.2
  else []

/-- The value at the end of the rounds. -/
def normalFinish (block : ReplicationBlock) (_ : ℕ) (input : ℕ × Prenex × Pattern)
    (answers : List (List (Prenex × Pattern))) : Prenex × Pattern :=
  if input.1 = 0 then
    (readingLeast block (replay block input.2.1 (answers.take input.2.1.components.length)).prune
      ((answers.getD input.2.1.components.length []).map Prod.snd), .bvar 0)
  else if input.1 = 1 then (Prenex.nil, recanonAnswer block input.2.2 (answers.getD 0 []))
  else if input.1 = 2 then (Prenex.nil, multisetAnswer block input.2.2 (answers.getD 0 []))
  else (Prenex.nil, input.2.2)

theorem normalFamily_zero (block : ReplicationBlock) (input : ℕ × Prenex × Pattern) :
    normalFamily block 0 input = if input.1 = 0 then (input.2.1, .bvar 0) else (Prenex.nil, input.2.2) := by
  simp only [normalFamily]
  split_ifs <;> simp_all [normalizeWith, recanonWith, recanonMultisetWith]

/-- The answers of a conversation after some rounds. -/
def transcript (ask : ℕ → (ℕ × Prenex × Pattern) → List (List (Prenex × Pattern)) → List (ℕ × Prenex × Pattern))
    (value : (ℕ × Prenex × Pattern) → Prenex × Pattern) (k : ℕ) (input : ℕ × Prenex × Pattern) :
    ℕ → List (List (Prenex × Pattern)) → List (List (Prenex × Pattern))
  | 0, answers => answers
  | r + 1, answers => transcript ask value k input r (answers ++ [(ask k input answers).map value])

theorem conversation_eq_transcript
    (ask : ℕ → (ℕ × Prenex × Pattern) → List (List (Prenex × Pattern)) → List (ℕ × Prenex × Pattern))
    (finish : ℕ → (ℕ × Prenex × Pattern) → List (List (Prenex × Pattern)) → Prenex × Pattern)
    (value : (ℕ × Prenex × Pattern) → Prenex × Pattern) (k : ℕ) (input : ℕ × Prenex × Pattern) :
    ∀ (r : ℕ) (answers : List (List (Prenex × Pattern))),
      CodeComputable.conversation ask finish value k input r answers =
        finish k input (transcript ask value k input r answers)
  | 0, _ => rfl
  | r + 1, _ => conversation_eq_transcript ask finish value k input r _

/-- The answers of the first rounds of a conversation, round by round. -/
def roundsSoFar (block : ReplicationBlock) (k : ℕ) (input : ℕ × Prenex × Pattern) :
    ℕ → List (List (Prenex × Pattern))
  | 0 => []
  | i + 1 => roundsSoFar block k input i ++
      [(normalAsk block k input (roundsSoFar block k input i)).map (normalFamily block k)]

theorem transcript_roundsSoFar (block : ReplicationBlock) (k : ℕ) (input : ℕ × Prenex × Pattern) :
    ∀ (r i : ℕ), transcript (normalAsk block) (normalFamily block k) k input r (roundsSoFar block k input i) =
      roundsSoFar block k input (i + r)
  | 0, _ => rfl
  | r + 1, i => by
      have step : transcript (normalAsk block) (normalFamily block k) k input (r + 1) (roundsSoFar block k input i) =
          transcript (normalAsk block) (normalFamily block k) k input r (roundsSoFar block k input (i + 1)) := rfl
      rw [step, transcript_roundsSoFar block k input r (i + 1)]
      congr 1
      omega

theorem roundsSoFar_length (block : ReplicationBlock) (k : ℕ) (input : ℕ × Prenex × Pattern) :
    ∀ i, (roundsSoFar block k input i).length = i
  | 0 => rfl
  | i + 1 => by simp [roundsSoFar, roundsSoFar_length block k input i]

/-- The canonical form within the fuel below, as an absorption judges with it. -/
def canonicalBelow (block : ReplicationBlock) (k : ℕ) (pattern : Pattern) : Pattern :=
  Prenex.toPattern block.toBlock (normalizeWith block k (decompose block.toBlock pattern))

/-- **The absorption rounds replay as the absorptions judged by the canonical form below.** -/
theorem replay_roundsSoFar (block : ReplicationBlock) (k : ℕ) (form : Prenex) (pattern : Pattern) :
    ∀ i, i ≤ form.components.length →
      replay block form (roundsSoFar block k (0, form, pattern) i) =
        (absorbStep block (canonicalBelow block k))^[i] form
  | 0, _ => rfl
  | i + 1, within => by
      have before := replay_roundsSoFar block k form pattern i (Nat.le_of_succ_le within)
      have asked : normalAsk block k (0, form, pattern) (roundsSoFar block k (0, form, pattern) i) =
          (absorbQueries block (replay block form (roundsSoFar block k (0, form, pattern) i))).map
            (canonicalQuestion block) := by
        simp [normalAsk, roundsSoFar_length, Nat.lt_of_succ_le within]
      have stepped : replay block form (roundsSoFar block k (0, form, pattern) (i + 1)) =
          replayStep block (replay block form (roundsSoFar block k (0, form, pattern) i))
            ((normalAsk block k (0, form, pattern) (roundsSoFar block k (0, form, pattern) i)).map
              (normalFamily block k)) := by
        simp [roundsSoFar, replay, List.foldl_append]
      rw [stepped, asked, List.map_map, before, Function.iterate_succ_apply']
      exact replayStep_answered block (canonicalBelow block k) _ (normalFamily block k ∘ canonicalQuestion block)
        fun query => by simp [normalFamily, canonicalQuestion, canonicalBelow]

theorem argumentAnswer_question (block : ReplicationBlock) (k : ℕ) (argument : Pattern) :
    argumentAnswer block argument (normalFamily block k (argumentQuestion block argument)) =
      canonArgument (fun argument => Prenex.toPattern block.toBlock
        (normalizeWith block k (decompose block.toBlock argument))) argument := by
  cases argument <;> simp [argumentAnswer, argumentQuestion, normalFamily, canonicalQuestion, isLambda, isKept,
    lambdaBody, withBody, canonArgument]

theorem recanonAnswer_questions (block : ReplicationBlock) (k : ℕ) (component : Pattern) :
    recanonAnswer block component ((recanonQuestions block component).map (normalFamily block k)) =
      recanonWith block (k + 1) component := by
  cases component with
  | apply label arguments =>
      by_cases restricted : label = block.restrict
      · simp [recanonAnswer, isApply, applyLabel, restricted, recanonWith]
      · by_cases multiset : label ∈ block.multisets
        · simp [recanonAnswer, recanonQuestions, isApply, applyLabel, applyArguments, restricted, multiset,
            recanonWith, normalFamily, Function.comp_def]
        · simp only [recanonAnswer, recanonQuestions, isApply, if_true, recanonWith, if_neg restricted,
            if_neg multiset]
          split_ifs with first second
          · exact absurd (of_decide_eq_true first) restricted
          · simp [applyLabel] at second
            exact absurd second multiset
          · simp only [applyLabel, applyArguments, List.map_map, zipWith_map_self]
            congr 1
            exact List.map_congr_left fun argument _ => argumentAnswer_question block k argument
  | lambda binder body => simp [recanonAnswer, recanonQuestions, isApply, isBinder, binderBody, withBody, recanonWith,
      normalFamily, canonicalQuestion]
  | multiLambda arity binders body => simp [recanonAnswer, recanonQuestions, isApply, isBinder, binderBody, withBody,
      recanonWith, normalFamily, canonicalQuestion]
  | collection kind elements rest => simp [recanonAnswer, recanonQuestions, isApply, isBinder, isCollection,
      collectionElements, withElements, recanonWith, normalFamily, canonicalQuestion, Function.comp_def]
  | _ => simp [recanonAnswer, isApply, isBinder, isCollection, recanonWith]

theorem multisetAnswer_questions (block : ReplicationBlock) (k : ℕ) (argument : Pattern) :
    multisetAnswer block argument ((multisetQuestions block argument).map (normalFamily block k)) =
      recanonMultisetWith block (k + 1) argument := by
  cases argument with
  | collection kind elements rest =>
      cases rest with
      | some rest => simp [multisetAnswer, multisetQuestions, isOpenCollection, collectionElements, withElements,
          recanonMultisetWith, normalFamily, canonicalQuestion, Function.comp_def]
      | none => simp [multisetAnswer, multisetQuestions, isOpenCollection, isSubst, recanonMultisetWith, normalFamily,
          canonicalQuestion]
  | subst body replacement => simp [multisetAnswer, isOpenCollection, isSubst, recanonMultisetWith]
  | _ => simp [multisetAnswer, multisetQuestions, isOpenCollection, isSubst, recanonMultisetWith, normalFamily,
      canonicalQuestion]

theorem readingLeast_answers (block : ReplicationBlock) (k : ℕ) (absorbed : Prenex) :
    readingLeast block absorbed (((readingQuestions block absorbed).map (normalFamily block k)).map Prod.snd) =
      ⟨absorbed.count, least ((readingOrders block absorbed).map fun order => dedupReplicated block (sortComponents
        (absorbed.components.map fun component => recanonWith block k
          (rename (Prenex.permute absorbed.count order) component))))⟩ := by
  have values : ((readingQuestions block absorbed).map (normalFamily block k)).map Prod.snd =
      (readingOrders block absorbed).flatMap fun order => absorbed.components.map fun component =>
        recanonWith block k (rename (Prenex.permute absorbed.count order) component) := by
    simp [readingQuestions, List.map_flatMap, normalFamily, Function.comp_def]
  have chunked := chunks_flatMap (fun order => absorbed.components.map fun component =>
      recanonWith block k (rename (Prenex.permute absorbed.count order) component))
    absorbed.components.length (readingOrders block absorbed) (fun _ _ => by simp)
  simp only [readingLeast, values]
  congr 2
  have sorted := congrArg (List.map fun components => dedupReplicated block (sortComponents components)) chunked
  simpa [List.map_map, Function.comp_def] using sorted

/-- **The family within one more fuel is its conversation.** -/
theorem normalFamily_succ (block : ReplicationBlock) (k : ℕ) (input : ℕ × Prenex × Pattern) :
    normalFamily block (k + 1) input =
      CodeComputable.conversation (normalAsk block) (normalFinish block) (normalFamily block k) k input
        (normalCount k input) [] := by
  rw [conversation_eq_transcript]
  rcases input with ⟨tag, form, pattern⟩
  by_cases zero : tag = 0
  · subst zero
    have transcribed : transcript (normalAsk block) (normalFamily block k) k (0, form, pattern)
        (normalCount k (0, form, pattern)) [] = roundsSoFar block k (0, form, pattern) (form.components.length + 1) := by
      have := transcript_roundsSoFar block k (0, form, pattern) (form.components.length + 1) 0
      simpa [normalCount, roundsSoFar] using this
    rw [transcribed]
    have taken : (roundsSoFar block k (0, form, pattern) (form.components.length + 1)).take form.components.length =
        roundsSoFar block k (0, form, pattern) form.components.length := by
      rw [roundsSoFar, List.take_left' (roundsSoFar_length block k _ _)]
    have last : (roundsSoFar block k (0, form, pattern) (form.components.length + 1)).getD form.components.length [] =
        (normalAsk block k (0, form, pattern) (roundsSoFar block k (0, form, pattern) form.components.length)).map
          (normalFamily block k) := by
      rw [roundsSoFar, List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp [roundsSoFar_length])]
      simp [roundsSoFar_length]
    have replayed := replay_roundsSoFar block k form pattern form.components.length le_rfl
    have reading : normalAsk block k (0, form, pattern) (roundsSoFar block k (0, form, pattern) form.components.length) =
        readingQuestions block (replay block form (roundsSoFar block k (0, form, pattern)
          form.components.length)).prune := by
      simp [normalAsk, roundsSoFar_length, List.take_of_length_le]
    simp only [normalFinish, if_true, taken, last, reading, replayed, readingLeast_answers, normalFamily, normalizeWith]
    rw [← absorbRounds_eq_iterate]
    rfl
  by_cases one : tag = 1
  · subst one
    simp [normalFamily, normalFinish, normalCount, normalAsk, transcript, recanonAnswer_questions]
  by_cases two : tag = 2
  · subst two
    simp [normalFamily, normalFinish, normalCount, normalAsk, transcript, multisetAnswer_questions]
  simp [normalFamily, normalFinish, zero, one, two]

/-! ## The normalization family is computable on codes -/

theorem replayStep_codeComputable (block : ReplicationBlock) :
    CodeComputable fun input : Prenex × List (Prenex × Pattern) => replayStep block input.1 input.2 := by
  have answers : CodeComputable fun input : Prenex × List (Prenex × Pattern) =>
      input.2.map fun answer => Prenex.toPattern block.toBlock answer.1 :=
    list_map (members := fun input : Prenex × List (Prenex × Pattern) => input.2)
      (image := fun _ answer => Prenex.toPattern block.toBlock answer.1) snd
      (toPattern_codeComputable block.toBlock (fst.comp snd))
  have table : CodeComputable fun input : Prenex × List (Prenex × Pattern) =>
      List.zipWith Prod.mk (absorbQueries block input.1) (input.2.map fun answer => Prenex.toPattern block.toBlock
        answer.1) :=
    list_zipWith (combine := fun _ query answer => (query, answer)) (.bvar 0) (.bvar 0)
      ((absorbQueries_codeComputable block).comp fst) answers ((fst.comp snd).pair (snd.comp snd))
  have absorbed := CodeComputable.comp (f := fun input : List (Pattern × Pattern) × Prenex =>
      absorbOnce block (lookupIn input.1) input.2) (g := fun input : Prenex × List (Prenex × Pattern) =>
      (List.zipWith Prod.mk (absorbQueries block input.1) (input.2.map fun answer => Prenex.toPattern block.toBlock
        answer.1), input.1)) (absorbOnce_codeComputable block) (table.pair fst)
  exact (option_getD absorbed fst).of_eq fun _ => rfl

theorem replay_codeComputable (block : ReplicationBlock) :
    CodeComputable fun input : Prenex × List (List (Prenex × Pattern)) => replay block input.1 input.2 :=
  list_foldl (members := fun input : Prenex × List (List (Prenex × Pattern)) => input.2) (start := fun input => input.1)
    (step := fun _ form round => replayStep block form round) snd fst
    ((replayStep_codeComputable block).comp ((fst.comp snd).pair (snd.comp snd)))

theorem canonicalQuestion_codeComputable (block : ReplicationBlock) : CodeComputable (canonicalQuestion block) :=
  (const 0).pair ((decompose_codeComputable block.toBlock).pair (const _))

theorem readingQuestions_codeComputable (block : ReplicationBlock) : CodeComputable (readingQuestions block) :=
  list_flatMap (members := fun absorbed : Prenex => readingOrders block absorbed)
    (image := fun absorbed order => absorbed.components.map fun component =>
      ((1 : ℕ), Prenex.nil, rename (Prenex.permute absorbed.count order) component))
    (readingOrders_codeComputable block)
    (list_map (members := fun input : Prenex × List ℕ => input.1.components)
      (image := fun input component => ((1 : ℕ), Prenex.nil, rename (Prenex.permute input.1.count input.2) component))
      (components.comp fst) ((const 1).pair (nil.pair (rename_permute.comp (((count.comp (fst.comp fst)).pair
        (snd.comp fst)).pair snd)))))

theorem argumentQuestion_codeComputable (block : ReplicationBlock) : CodeComputable (argumentQuestion block) :=
  (ite isLambda_codeComputable ((canonicalQuestion_codeComputable block).comp lambdaBody_codeComputable)
    (ite isKept_codeComputable ((const 3).pair (nil.pair CodeComputable.id))
      (canonicalQuestion_codeComputable block))).of_eq fun _ => rfl

theorem recanonQuestions_codeComputable (block : ReplicationBlock) : CodeComputable (recanonQuestions block) :=
  (ite isApply_codeComputable
    (ite (stringEq.comp (applyLabel_codeComputable.pair (const block.restrict))) list_nil
      (ite (list_contains stringCode_injective' (const block.multisets) applyLabel_codeComputable)
        (list_map (members := applyArguments) (image := fun _ argument => ((2 : ℕ), Prenex.nil, argument))
          applyArguments_codeComputable ((const 2).pair (nil.pair snd)))
        (list_map (members := applyArguments) (image := fun _ argument => argumentQuestion block argument)
          applyArguments_codeComputable ((argumentQuestion_codeComputable block).comp snd))))
    (ite isBinder_codeComputable
      (list_cons ((canonicalQuestion_codeComputable block).comp binderBody_codeComputable) list_nil)
      (ite isCollection_codeComputable
        (list_map (members := collectionElements) (image := fun _ element => canonicalQuestion block element)
          collectionElements_codeComputable ((canonicalQuestion_codeComputable block).comp snd))
        list_nil))).of_eq fun _ => rfl

theorem multisetQuestions_codeComputable (block : ReplicationBlock) : CodeComputable (multisetQuestions block) :=
  (ite isOpenCollection_codeComputable
    (list_map (members := collectionElements) (image := fun _ element => canonicalQuestion block element)
      collectionElements_codeComputable ((canonicalQuestion_codeComputable block).comp snd))
    (ite isSubst_codeComputable list_nil
      (list_cons (canonicalQuestion_codeComputable block) list_nil))).of_eq fun _ => rfl

theorem normalAsk_codeComputable (block : ReplicationBlock) :
    CodeComputable fun input : ℕ × (ℕ × Prenex × Pattern) × List (List (Prenex × Pattern)) =>
      normalAsk block input.1 input.2.1 input.2.2 := by
  have tag : CodeComputable fun input : ℕ × (ℕ × Prenex × Pattern) × List (List (Prenex × Pattern)) => input.2.1.1 :=
    fst.comp (fst.comp snd)
  have form : CodeComputable fun input : ℕ × (ℕ × Prenex × Pattern) × List (List (Prenex × Pattern)) => input.2.1.2.1 :=
    fst.comp (snd.comp (fst.comp snd))
  have pattern : CodeComputable fun input : ℕ × (ℕ × Prenex × Pattern) × List (List (Prenex × Pattern)) =>
      input.2.1.2.2 := snd.comp (snd.comp (fst.comp snd))
  have answers : CodeComputable fun input : ℕ × (ℕ × Prenex × Pattern) × List (List (Prenex × Pattern)) => input.2.2 :=
    snd.comp snd
  have components' := list_length (components.comp form)
  have replayed := CodeComputable.comp₂ (replay_codeComputable block) form answers
  have replayedTaken := CodeComputable.comp₂ (replay_codeComputable block) form (list_take components' answers)
  have absorbing := list_map (members := fun input : ℕ × (ℕ × Prenex × Pattern) × List (List (Prenex × Pattern)) =>
      absorbQueries block (replay block input.2.1.2.1 input.2.2)) (image := fun _ query => canonicalQuestion block query)
    ((absorbQueries_codeComputable block).comp replayed) ((canonicalQuestion_codeComputable block).comp snd)
  have computed := ite (nat_eq tag (const 0))
    (ite (nat_lt (list_length answers) components') absorbing
      ((readingQuestions_codeComputable block).comp (prune_codeComputable.comp replayedTaken)))
    (ite (nat_eq tag (const 1)) ((recanonQuestions_codeComputable block).comp pattern)
      (ite (nat_eq tag (const 2)) ((multisetQuestions_codeComputable block).comp pattern) list_nil))
  refine computed.of_eq fun input => ?_
  simp only [normalAsk, decide_eq_true_eq]

theorem readingLeast_codeComputable (block : ReplicationBlock) :
    CodeComputable fun input : Prenex × List Pattern => readingLeast block input.1 input.2 := by
  have size' := list_length (components.comp (fst : CodeComputable fun input : Prenex × List Pattern => input.1))
  have readings := list_length ((readingOrders_codeComputable block).comp
    (fst : CodeComputable fun input : Prenex × List Pattern => input.1))
  have chunk : CodeComputable₂ fun (input : Prenex × List Pattern) (position : ℕ) =>
      dedupReplicated block (sortComponents ((input.2.drop (position * input.1.components.length)).take
        input.1.components.length)) :=
    (dedupReplicated_codeComputable block).comp (insertionSort'.comp (list_take (size'.comp fst)
      (list_drop (nat_mul snd (size'.comp fst)) (snd.comp fst))))
  exact prenex (count.comp fst) (least_codeComputable (list_map (list_range readings) chunk))

theorem argumentAnswer_codeComputable (block : ReplicationBlock) :
    CodeComputable₂ (argumentAnswer block) :=
  (ite (isLambda_codeComputable.comp fst)
    (withBody_codeComputable.comp (fst.pair (toPattern_codeComputable block.toBlock (fst.comp snd))))
    (ite (isKept_codeComputable.comp fst) (snd.comp snd)
      (toPattern_codeComputable block.toBlock (fst.comp snd)))).of_eq fun _ => rfl

theorem recanonAnswer_codeComputable (block : ReplicationBlock) :
    CodeComputable fun input : Pattern × List (Prenex × Pattern) => recanonAnswer block input.1 input.2 := by
  have component : CodeComputable fun input : Pattern × List (Prenex × Pattern) => input.1 := fst
  have answers : CodeComputable fun input : Pattern × List (Prenex × Pattern) => input.2 := snd
  have label := applyLabel_codeComputable.comp component
  have patterns := list_map (members := fun input : Pattern × List (Prenex × Pattern) => input.2)
    (image := fun _ answer => Prenex.toPattern block.toBlock answer.1) answers
    (toPattern_codeComputable block.toBlock (fst.comp snd))
  exact (ite (isApply_codeComputable.comp component)
    (ite (stringEq.comp (label.pair (const block.restrict))) component
      (ite (list_contains stringCode_injective' (const block.multisets) label)
        (apply label (list_map (members := fun input : Pattern × List (Prenex × Pattern) => input.2)
          (image := fun _ answer => answer.2) answers (snd.comp snd)))
        (apply label (list_zipWith (combine := fun _ argument answer => argumentAnswer block argument answer)
          (.bvar 0) (Prenex.nil, .bvar 0) (applyArguments_codeComputable.comp component) answers
          ((argumentAnswer_codeComputable block).comp snd)))))
    (ite (isBinder_codeComputable.comp component)
      (withBody_codeComputable.comp (component.pair (toPattern_codeComputable block.toBlock
        (fst.comp (list_getD (Prenex.nil, .bvar 0) answers (const 0))))))
      (ite (isCollection_codeComputable.comp component)
        (withElements_codeComputable.comp (component.pair patterns)) component))).of_eq fun _ => rfl

theorem multisetAnswer_codeComputable (block : ReplicationBlock) :
    CodeComputable fun input : Pattern × List (Prenex × Pattern) => multisetAnswer block input.1 input.2 := by
  have component : CodeComputable fun input : Pattern × List (Prenex × Pattern) => input.1 := fst
  have patterns := list_map (members := fun input : Pattern × List (Prenex × Pattern) => input.2)
    (image := fun _ answer => Prenex.toPattern block.toBlock answer.1) snd
    (toPattern_codeComputable block.toBlock (fst.comp snd))
  exact (ite (isOpenCollection_codeComputable.comp component) (withElements_codeComputable.comp (component.pair patterns))
    (ite (isSubst_codeComputable.comp component) component
      (multisetOf_codeComputable block.toBlock (fst.comp (list_getD (Prenex.nil, .bvar 0) snd (const 0)))))).of_eq
    fun _ => rfl

theorem normalFinish_codeComputable (block : ReplicationBlock) :
    CodeComputable fun input : ℕ × (ℕ × Prenex × Pattern) × List (List (Prenex × Pattern)) =>
      normalFinish block input.1 input.2.1 input.2.2 := by
  have tag : CodeComputable fun input : ℕ × (ℕ × Prenex × Pattern) × List (List (Prenex × Pattern)) => input.2.1.1 :=
    fst.comp (fst.comp snd)
  have form : CodeComputable fun input : ℕ × (ℕ × Prenex × Pattern) × List (List (Prenex × Pattern)) => input.2.1.2.1 :=
    fst.comp (snd.comp (fst.comp snd))
  have pattern : CodeComputable fun input : ℕ × (ℕ × Prenex × Pattern) × List (List (Prenex × Pattern)) =>
      input.2.1.2.2 := snd.comp (snd.comp (fst.comp snd))
  have answers : CodeComputable fun input : ℕ × (ℕ × Prenex × Pattern) × List (List (Prenex × Pattern)) => input.2.2 :=
    snd.comp snd
  have components' := list_length (components.comp form)
  have absorbed := prune_codeComputable.comp (CodeComputable.comp₂ (replay_codeComputable block) form
    (list_take components' answers))
  have read := list_map (members := fun input : ℕ × (ℕ × Prenex × Pattern) × List (List (Prenex × Pattern)) =>
      input.2.2.getD input.2.1.2.1.components.length []) (image := fun _ answer => answer.2)
    (list_getD [] answers components') (snd.comp snd)
  have first := list_getD [] answers (const 0)
  have computed := ite (nat_eq tag (const 0))
    ((CodeComputable.comp₂ (readingLeast_codeComputable block) absorbed read).pair (const (Pattern.bvar 0)))
    (ite (nat_eq tag (const 1)) (nil.pair (CodeComputable.comp₂ (recanonAnswer_codeComputable block) pattern first))
      (ite (nat_eq tag (const 2)) (nil.pair (CodeComputable.comp₂ (multisetAnswer_codeComputable block) pattern first))
        (nil.pair pattern)))
  refine computed.of_eq fun input => ?_
  simp only [normalFinish, decide_eq_true_eq]

theorem normalCount_codeComputable : CodeComputable₂ normalCount := by
  have tag : CodeComputable fun input : ℕ × ℕ × Prenex × Pattern => input.2.1 := fst.comp snd
  refine (ite (nat_eq tag (const 0)) (nat_add (list_length (components.comp (fst.comp (snd.comp snd)))) (const 1))
    (ite (or (nat_eq tag (const 1)) (nat_eq tag (const 2))) (const 1) (const 0))).of_eq fun input => ?_
  simp only [normalCount, decide_eq_true_eq, Bool.or_eq_true]

/-- **The normalizations within a fuel are computable on codes.** -/
theorem normalFamily_codeComputable (block : ReplicationBlock) : CodeComputable₂ (normalFamily block) :=
  rounds (run := normalFamily block)
    (base := fun input => if input.1 = 0 then (input.2.1, Pattern.bvar 0) else (Prenex.nil, input.2.2))
    (count := normalCount) (ask := normalAsk block) (finish := normalFinish block) (normalFamily_zero block)
    (normalFamily_succ block)
    ((ite (nat_eq fst (const 0)) ((fst.comp snd).pair (const (Pattern.bvar 0))) (nil.pair (snd.comp snd))).of_eq
      fun input => by
      simp only [decide_eq_true_eq])
    normalCount_codeComputable (normalAsk_codeComputable block) (normalFinish_codeComputable block)

/-! ## The canonical form with replication -/

theorem normal_codeComputable (block : ReplicationBlock) : CodeComputable (normal block) :=
  (fst.comp (CodeComputable.comp₂ (normalFamily_codeComputable block)
    (nat_add (nat_mul (const 3) (size_codeComputable.comp (toPattern_codeComputable block.toBlock CodeComputable.id)))
      (const 3)) ((const 0).pair (CodeComputable.id.pair (const (Pattern.bvar 0)))))).of_eq fun form => by
    simp [normal, normalFamily]

theorem canonicalOf_codeComputable (block : ReplicationBlock) : CodeComputable (canonicalOf block) :=
  toPattern_codeComputable block.toBlock ((normal_codeComputable block).comp (decompose_codeComputable block.toBlock))

theorem argumentOf_eq (block : ReplicationBlock) (label : String) (argument : Pattern) (form : Prenex) :
    argumentOf block label argument form =
      if block.multisets.contains label then
        if isOpenCollection argument || isSubst argument then Prenex.toPattern block.toBlock form
        else multisetOf block.toBlock form
      else Prenex.toPattern block.toBlock form := by
  unfold argumentOf
  by_cases multiset : label ∈ block.multisets
  · cases argument with
    | collection kind elements rest => cases rest <;> simp [multiset, isOpenCollection, isSubst]
    | subst body replacement => simp [multiset, isOpenCollection, isSubst]
    | _ => simp [multiset, isOpenCollection, isSubst]
  · simp [multiset]

theorem argumentOf_codeComputable (block : ReplicationBlock) :
    CodeComputable fun input : String × Pattern × Prenex => argumentOf block input.1 input.2.1 input.2.2 :=
  (ite (list_contains stringCode_injective' (const block.multisets) fst)
    (ite (or (isOpenCollection_codeComputable.comp (fst.comp snd)) (isSubst_codeComputable.comp (fst.comp snd)))
      (toPattern_codeComputable block.toBlock (snd.comp snd)) (multisetOf_codeComputable block.toBlock (snd.comp snd)))
    (toPattern_codeComputable block.toBlock (snd.comp snd))).of_eq fun _ => (argumentOf_eq block _ _ _).symm

/-- The calls of `canonP`: the body of a single abstraction argument, the arguments of another application, the members
of a collection, the body of a binder. -/
def canonPCalls (_ : ℕ) (pattern : Pattern) : List (ℕ × Pattern) :=
  if isApply pattern then
    if decide ((applyArguments pattern).length = 1) && isLambda ((applyArguments pattern).getD 0 (.bvar 0)) then
      [(0, lambdaBody ((applyArguments pattern).getD 0 (.bvar 0)))]
    else (applyArguments pattern).map fun argument => (0, argument)
  else if isCollection pattern then (collectionElements pattern).map fun element => (0, element)
  else if isBinder pattern then [(0, binderBody pattern)]
  else []

/-- The combination of `canonP`. -/
def canonPCombine (block : ReplicationBlock) (_ : ℕ) (pattern : Pattern) (values : List Prenex) : Prenex :=
  if isApply pattern then
    if decide ((applyArguments pattern).length = 0) then
      if decide (applyLabel pattern = block.unit) then Prenex.nil else Prenex.atom pattern
    else if decide ((applyArguments pattern).length = 1) then
      if isLambda ((applyArguments pattern).getD 0 (.bvar 0)) then
        if decide (applyLabel pattern = block.restrict) then normal block (values.getD 0 Prenex.nil).close
        else Prenex.atom (.apply (applyLabel pattern) [argumentOf block (applyLabel pattern)
          ((applyArguments pattern).getD 0 (.bvar 0)) (Prenex.atom (withBody ((applyArguments pattern).getD 0 (.bvar 0))
            (Prenex.toPattern block.toBlock (values.getD 0 Prenex.nil))))])
      else if decide (applyLabel pattern = block.replicate) then
        normal block ⟨0, replicatedOf block (canonicalOf block) (values.getD 0 Prenex.nil)⟩
      else if block.emptyUnits.contains (applyLabel pattern) && decide (values.getD 0 Prenex.nil = Prenex.nil) then
        Prenex.nil
      else Prenex.atom (.apply (applyLabel pattern) [argumentOf block (applyLabel pattern)
        ((applyArguments pattern).getD 0 (.bvar 0)) (values.getD 0 Prenex.nil)])
    else Prenex.atom (.apply (applyLabel pattern)
      (List.zipWith (argumentOf block (applyLabel pattern)) (applyArguments pattern) values))
  else if isClosedBag pattern then normal block (values.foldr Prenex.par Prenex.nil)
  else if isCollection pattern then Prenex.atom (withElements pattern (values.map (Prenex.toPattern block.toBlock)))
  else if isBinder pattern then Prenex.atom (withBody pattern (Prenex.toPattern block.toBlock (values.getD 0 Prenex.nil)))
  else Prenex.atom pattern

theorem canonsP_eq_map (block : ReplicationBlock) : ∀ patterns : List Pattern,
    canonsP block patterns = patterns.map (canonP block)
  | [] => rfl
  | pattern :: patterns => by rw [canonsP, canonsP_eq_map block patterns, List.map_cons]

theorem canonP_node (block : ReplicationBlock) (parameter : ℕ) (pattern : Pattern) :
    canonP block pattern = canonPCombine block parameter pattern
      ((canonPCalls parameter pattern).map fun call => canonP block call.2) := by
  cases pattern with
  | apply label arguments =>
      rcases arguments with _ | ⟨argument, _ | ⟨second, rest⟩⟩
      · by_cases unit : label = block.unit <;>
          simp [canonP, canonPCombine, isApply, applyArguments, applyLabel, unit]
      · cases argument with
        | lambda binder body =>
            by_cases restricted : label = block.restrict <;>
              simp [canonP, canonPCombine, canonPCalls, isApply, applyArguments, applyLabel, isLambda, lambdaBody,
                withBody, restricted]
        | _ =>
            by_cases replicated : label = block.replicate
            · simp [canonP, canonPCombine, canonPCalls, isApply, applyArguments, applyLabel, isLambda, replicated]
            · by_cases empty : label ∈ block.emptyUnits <;>
                simp [canonP, canonPCombine, canonPCalls, isApply, applyArguments, applyLabel, isLambda, replicated,
                  empty]
      · simp [canonP, canonPCombine, canonPCalls, isApply, applyArguments, applyLabel, canonsP_eq_map,
          zipWith_map_self, Function.comp_def]
  | collection kind elements rest =>
      cases kind <;> cases rest <;>
        simp [canonP, canonPCombine, canonPCalls, isApply, isClosedBag, isCollection, collectionElements,
          withElements, canonsP_eq_map, List.foldr_map, Function.comp_def]
  | lambda binder body => simp [canonP, canonPCombine, canonPCalls, isApply, isClosedBag, isCollection, isBinder,
      binderBody, withBody]
  | multiLambda arity binders body => simp [canonP, canonPCombine, canonPCalls, isApply, isClosedBag, isCollection,
      isBinder, binderBody, withBody]
  | _ => simp [canonP, canonPCombine, isApply, isClosedBag, isCollection, isBinder]

theorem canonPCalls_smaller (parameter : ℕ) (pattern : Pattern) :
    ∀ call ∈ canonPCalls parameter pattern, patternCode call.2 < patternCode pattern := by
  intro call member
  cases pattern with
  | apply label arguments =>
      rcases arguments with _ | ⟨argument, _ | ⟨second, rest⟩⟩
      · simp [canonPCalls, isApply, applyArguments] at member
      · cases argument with
        | lambda binder body =>
            simp [canonPCalls, isApply, applyArguments, isLambda, lambdaBody] at member
            subst member
            exact (patternCode_lt_lambda binder body).trans (patternCode_lt_apply (List.mem_singleton_self _))
        | _ =>
            simp [canonPCalls, isApply, applyArguments, isLambda] at member
            subst member
            exact patternCode_lt_apply (List.mem_singleton_self _)
      · simp only [canonPCalls, isApply, applyArguments, if_true, List.length_cons] at member
        simp only [show (rest.length + 1 + 1 = 1) = False by simp, decide_false, Bool.false_and, Bool.false_eq_true,
          if_false, List.mem_map] at member
        obtain ⟨element, inArguments, rfl⟩ := member
        exact patternCode_lt_apply inArguments
  | collection kind elements rest =>
      simp only [canonPCalls, isApply, isCollection, collectionElements, Bool.false_eq_true, if_false, if_true,
        List.mem_map] at member
      obtain ⟨element, inElements, rfl⟩ := member
      exact patternCode_lt_collection inElements
  | lambda binder body =>
      simp [canonPCalls, isApply, isCollection, isBinder, binderBody] at member
      subst member
      exact patternCode_lt_lambda binder body
  | multiLambda arity binders body =>
      simp [canonPCalls, isApply, isCollection, isBinder, binderBody] at member
      subst member
      exact patternCode_lt_multiLambda arity binders body
  | _ => simp [canonPCalls, isApply, isCollection, isBinder] at member

theorem canonPCalls_codeComputable : CodeComputable₂ canonPCalls := by
  have pattern : CodeComputable fun input : ℕ × Pattern => input.2 := snd
  have arguments := applyArguments_codeComputable.comp pattern
  have first := list_getD (.bvar 0) arguments (const 0)
  exact (ite (isApply_codeComputable.comp pattern)
    (ite (and (nat_eq (list_length arguments) (const 1)) (isLambda_codeComputable.comp first))
      (list_cons ((const 0).pair (lambdaBody_codeComputable.comp first)) list_nil)
      (list_map (members := fun input : ℕ × Pattern => applyArguments input.2)
        (image := fun _ argument => ((0 : ℕ), argument)) arguments ((const 0).pair snd)))
    (ite (isCollection_codeComputable.comp pattern)
      (list_map (members := fun input : ℕ × Pattern => collectionElements input.2)
        (image := fun _ element => ((0 : ℕ), element)) (collectionElements_codeComputable.comp pattern)
        ((const 0).pair snd))
      (ite (isBinder_codeComputable.comp pattern)
        (list_cons ((const 0).pair (binderBody_codeComputable.comp pattern)) list_nil) list_nil))).of_eq
    fun _ => rfl

/-- `argumentOf` on a computable argument and block, with the label of the input pattern. -/
theorem argumentOf_comp (block : ReplicationBlock) {argument : ℕ × Pattern × List Prenex → Pattern}
    {form : ℕ × Pattern × List Prenex → Prenex} (hArgument : CodeComputable argument) (hForm : CodeComputable form) :
    CodeComputable fun input => argumentOf block (applyLabel input.2.1) (argument input) (form input) :=
  CodeComputable.comp (f := fun triple : String × Pattern × Prenex => argumentOf block triple.1 triple.2.1 triple.2.2)
    (g := fun input : ℕ × Pattern × List Prenex => (applyLabel input.2.1, argument input, form input))
    (argumentOf_codeComputable block) ((applyLabel_codeComputable.comp (fst.comp snd)).pair (hArgument.pair hForm))

/-- The combination of `canonP` at an application. -/
def applyCombine (block : ReplicationBlock) (pattern : Pattern) (values : List Prenex) : Prenex :=
  if decide ((applyArguments pattern).length = 0) then
    if decide (applyLabel pattern = block.unit) then Prenex.nil else Prenex.atom pattern
  else if decide ((applyArguments pattern).length = 1) then
    if isLambda ((applyArguments pattern).getD 0 (.bvar 0)) then
      if decide (applyLabel pattern = block.restrict) then normal block (values.getD 0 Prenex.nil).close
      else Prenex.atom (.apply (applyLabel pattern) [argumentOf block (applyLabel pattern)
        ((applyArguments pattern).getD 0 (.bvar 0)) (Prenex.atom (withBody ((applyArguments pattern).getD 0 (.bvar 0))
          (Prenex.toPattern block.toBlock (values.getD 0 Prenex.nil))))])
    else if decide (applyLabel pattern = block.replicate) then
      normal block ⟨0, replicatedOf block (canonicalOf block) (values.getD 0 Prenex.nil)⟩
    else if block.emptyUnits.contains (applyLabel pattern) && decide (values.getD 0 Prenex.nil = Prenex.nil) then
      Prenex.nil
    else Prenex.atom (.apply (applyLabel pattern) [argumentOf block (applyLabel pattern)
      ((applyArguments pattern).getD 0 (.bvar 0)) (values.getD 0 Prenex.nil)])
  else Prenex.atom (.apply (applyLabel pattern)
    (List.zipWith (argumentOf block (applyLabel pattern)) (applyArguments pattern) values))

theorem applyCombine_codeComputable (block : ReplicationBlock) :
    CodeComputable fun input : ℕ × Pattern × List Prenex => applyCombine block input.2.1 input.2.2 := by
  have pattern : CodeComputable fun input : ℕ × Pattern × List Prenex => input.2.1 := fst.comp snd
  have values : CodeComputable fun input : ℕ × Pattern × List Prenex => input.2.2 := snd.comp snd
  have arguments : CodeComputable fun input : ℕ × Pattern × List Prenex => applyArguments input.2.1 :=
    applyArguments_codeComputable.comp pattern
  have label : CodeComputable fun input : ℕ × Pattern × List Prenex => applyLabel input.2.1 :=
    applyLabel_codeComputable.comp pattern
  have first : CodeComputable fun input : ℕ × Pattern × List Prenex => (applyArguments input.2.1).getD 0 (.bvar 0) :=
    list_getD (.bvar 0) arguments (const 0)
  have value : CodeComputable fun input : ℕ × Pattern × List Prenex => input.2.2.getD 0 Prenex.nil :=
    list_getD Prenex.nil values (const 0)
  have closed : CodeComputable fun input : ℕ × Pattern × List Prenex => normal block (input.2.2.getD 0 Prenex.nil).close :=
    (normal_codeComputable block).comp (close value)
  have wrapped : CodeComputable fun input : ℕ × Pattern × List Prenex =>
      Prenex.atom (.apply (applyLabel input.2.1) [argumentOf block (applyLabel input.2.1)
        ((applyArguments input.2.1).getD 0 (.bvar 0)) (Prenex.atom (withBody ((applyArguments input.2.1).getD 0 (.bvar 0))
          (Prenex.toPattern block.toBlock (input.2.2.getD 0 Prenex.nil))))]) :=
    atom (apply label (list_cons (argumentOf_comp block first (atom (CodeComputable.comp₂ withBody_codeComputable first
      (toPattern_codeComputable block.toBlock value)))) list_nil))
  have replicated : CodeComputable fun input : ℕ × Pattern × List Prenex =>
      normal block ⟨0, replicatedOf block (canonicalOf block) (input.2.2.getD 0 Prenex.nil)⟩ :=
    (normal_codeComputable block).comp (prenex (const 0)
      ((replicatedOf_codeComputable block (canonicalOf_codeComputable block)).comp value))
  have emptied : CodeComputable fun input : ℕ × Pattern × List Prenex =>
      block.emptyUnits.contains (applyLabel input.2.1) && decide (input.2.2.getD 0 Prenex.nil = Prenex.nil) :=
    and (list_contains stringCode_injective' (const block.emptyUnits) label)
      (CodeComputable.comp₂ (beq_of_injective code_prenex_injective) value nil)
  have single : CodeComputable fun input : ℕ × Pattern × List Prenex =>
      Prenex.atom (.apply (applyLabel input.2.1) [argumentOf block (applyLabel input.2.1)
        ((applyArguments input.2.1).getD 0 (.bvar 0)) (input.2.2.getD 0 Prenex.nil)]) :=
    atom (apply label (list_cons (argumentOf_comp block first value) list_nil))
  have many : CodeComputable fun input : ℕ × Pattern × List Prenex =>
      Prenex.atom (.apply (applyLabel input.2.1)
        (List.zipWith (argumentOf block (applyLabel input.2.1)) (applyArguments input.2.1) input.2.2)) :=
    atom (apply label (list_zipWith (combine := fun input argument form =>
        argumentOf block (applyLabel input.2.1) argument form) (.bvar 0) Prenex.nil arguments values
      (CodeComputable.comp (f := fun triple : String × Pattern × Prenex =>
          argumentOf block triple.1 triple.2.1 triple.2.2)
        (g := fun input : (ℕ × Pattern × List Prenex) × Pattern × Prenex =>
          (applyLabel input.1.2.1, input.2.1, input.2.2))
        (argumentOf_codeComputable block) ((label.comp fst).pair ((fst.comp snd).pair (snd.comp snd))))))
  exact (ite (nat_eq (list_length arguments) (const 0))
    (ite (stringEq.comp (label.pair (const block.unit))) nil (atom pattern))
    (ite (nat_eq (list_length arguments) (const 1))
      (ite (isLambda_codeComputable.comp first) (ite (stringEq.comp (label.pair (const block.restrict))) closed wrapped)
        (ite (stringEq.comp (label.pair (const block.replicate))) replicated (ite emptied nil single)))
      many)).of_eq fun _ => rfl

theorem canonPCombine_codeComputable (block : ReplicationBlock) :
    CodeComputable fun input : ℕ × Pattern × List Prenex => canonPCombine block input.1 input.2.1 input.2.2 := by
  have pattern : CodeComputable fun input : ℕ × Pattern × List Prenex => input.2.1 := fst.comp snd
  have values : CodeComputable fun input : ℕ × Pattern × List Prenex => input.2.2 := snd.comp snd
  have value : CodeComputable fun input : ℕ × Pattern × List Prenex => input.2.2.getD 0 Prenex.nil :=
    list_getD Prenex.nil values (const 0)
  have bag : CodeComputable fun input : ℕ × Pattern × List Prenex =>
      normal block (input.2.2.foldr Prenex.par Prenex.nil) :=
    (normal_codeComputable block).comp (list_foldr (step := fun _ form rest => form.par rest) values nil
      (par (fst.comp snd) (snd.comp snd)))
  have collected : CodeComputable fun input : ℕ × Pattern × List Prenex =>
      Prenex.atom (withElements input.2.1 (input.2.2.map (Prenex.toPattern block.toBlock))) :=
    atom (CodeComputable.comp₂ withElements_codeComputable pattern (list_map (members := fun input :
      ℕ × Pattern × List Prenex => input.2.2) (image := fun _ form => Prenex.toPattern block.toBlock form) values
        (toPattern_codeComputable block.toBlock snd)))
  have bound : CodeComputable fun input : ℕ × Pattern × List Prenex =>
      Prenex.atom (withBody input.2.1 (Prenex.toPattern block.toBlock (input.2.2.getD 0 Prenex.nil))) :=
    atom (CodeComputable.comp₂ withBody_codeComputable pattern (toPattern_codeComputable block.toBlock value))
  exact (ite (isApply_codeComputable.comp pattern) (applyCombine_codeComputable block)
    (ite (isClosedBag_codeComputable.comp pattern) bag
      (ite (isCollection_codeComputable.comp pattern) collected
        (ite (isBinder_codeComputable.comp pattern) bound (atom pattern))))).of_eq fun _ => rfl

/-- **The canonical block with replication is computable on codes.** -/
theorem canonP_codeComputable (block : ReplicationBlock) : CodeComputable (canonP block) :=
  (structural (value := fun (_ : ℕ) pattern => canonP block pattern) (canonP_node block) canonPCalls_smaller
    canonPCalls_codeComputable (canonPCombine_codeComputable block)).comp ((const 0).pair CodeComputable.id)

/-- **The canonical form with replication is computable on codes.** -/
theorem canonR_codeComputable (block : ReplicationBlock) : CodeComputable (canonR block) :=
  toPattern_codeComputable block.toBlock (canonP_codeComputable block)

end ReplicationCodes

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks
