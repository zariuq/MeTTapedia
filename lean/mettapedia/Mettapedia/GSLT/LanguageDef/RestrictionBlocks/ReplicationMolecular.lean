import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationMono
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationReflection

/-!
# Presentations when replicated components copy molecules

A replicated component whose copy has no replicated component of its own copies a **molecule**: unfolding it adds
the copy's restrictions and components and no more replicated components. When every replicated component of a block
copies a molecule (`moleculeServers`), a reaction of any unfolding is a reaction of an unfolding within the arity:

- **A copy beside its replicated component is absorbed at any depth** (`drop_copy_at`): the copy's restrictions,
  moved inside the inner ones, make the block an unfolding of the block without the copy.
- **An unfolding compresses to the copies holding taken components** (`compress_unfolds`): a copy of a replicated
  component that was itself lifted is the copy of the original lifted, since the canonical form commutes with strictly
  monotone renamings outside a block; so an unfolding is, up to an order-preserving renaming, the unfolding of the
  copies that hold taken components beside the other copies, and every context reads beside the other copies as it
  reads without them.
- **A reaction of any unfolding is, renamed, a reaction of an unfolding within the arity** (`compress_molecular`),
  leaving what reads as the first reaction leaves: a redex takes components of at most one copy per part. One-component
  replicated components copy molecules (`moleculeServers_of_flat`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.EquationSemantics (EquationEquiv)
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (engineBasePremises)
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (FreeIn liftIndex)
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars)
open Mettapedia.GSLT.LanguageDef.WellSorted

variable {block : ReplicationBlock}

/-! ## Lifting -/

theorem liftBVars_zero_eq_rename (shift : Nat) (pattern : Pattern) :
    liftBVars 0 shift pattern = rename (· + shift) pattern := by
  rw [liftBVars_eq_rename]
  congr 1

theorem strictMono_add_shift (shift : Nat) : StrictMono (· + shift : Nat → Nat) :=
  fun _ _ less => Nat.add_lt_add_right less shift

theorem liftIndex_comp (cutoff : Nat) (first second : Nat → Nat) :
    liftIndex cutoff (first ∘ second) = liftIndex cutoff first ∘ liftIndex cutoff second := by
  funext index
  simp only [Function.comp_apply, liftIndex]
  split_ifs with below lifted
  · rfl
  · omega
  · rw [Nat.add_sub_cancel]

theorem liftIndex_add_cutoff (cutoff : Nat) (relabel : Nat → Nat) (index : Nat) :
    liftIndex cutoff relabel (index + cutoff) = relabel index + cutoff := by
  simp [liftIndex]

/-- Lifting past new innermost restrictions commutes with a renaming lifted past them. -/
theorem liftBVars_rename (shift : Nat) (relabel : Nat → Nat) (pattern : Pattern) :
    liftBVars 0 shift (rename relabel pattern) = rename (liftIndex shift relabel) (liftBVars 0 shift pattern) := by
  rw [liftBVars_zero_eq_rename, liftBVars_zero_eq_rename, rename_comp, rename_comp]
  congr 1
  funext index
  simp only [Function.comp_apply]
  rw [liftIndex_add_cutoff]

/-! ## Moving restrictions past a copy -/

/-- **The inner restrictions moved out past the next ones**: the `inner` innermost restrictions of a block go just
outside the next `moved`, which become innermost. -/
def rotateIndex (inner moved index : Nat) : Nat :=
  if index < inner then index + moved else if index < inner + moved then index - inner else index

/-- The rotation as an order of a block's restrictions. -/
def rotateOrder (inner moved count : Nat) : List Nat := (List.range count).map (rotateIndex inner moved)

theorem rotateOrder_isOrder {inner moved count : Nat} (fits : inner + moved ≤ count) :
    IsOrder count (rotateOrder inner moved count) := by
  have nodup : (rotateOrder inner moved count).Nodup := by
    refine List.Nodup.map_on ?_ List.nodup_range
    intro first _ second _ same
    simp only [rotateIndex] at same
    split_ifs at same <;> omega
  have within : rotateOrder inner moved count ⊆ List.range count := by
    intro place member
    obtain ⟨index, inRange, rfl⟩ := List.mem_map.mp member
    rw [List.mem_range] at inRange ⊢
    simp only [rotateIndex]
    split_ifs <;> omega
  exact (nodup.subperm within).perm_of_length_le (by simp [rotateOrder])

theorem permute_rotateOrder {inner moved count : Nat} (fits : inner + moved ≤ count) :
    Prenex.permute count (rotateOrder inner moved count) = rotateIndex inner moved := by
  funext index
  unfold Prenex.permute rotateOrder
  split_ifs with below
  · simp [List.getD_eq_getElem?_getD, below]
  · simp only [rotateIndex]
    split_ifs <;> omega

theorem rotateIndex_lift (inner moved : Nat) :
    rotateIndex moved inner ∘ (· + moved) = liftIndex inner (· + moved) := by
  funext index
  simp only [Function.comp_apply, rotateIndex, liftIndex]
  split_ifs <;> omega

theorem rotateIndex_copy (inner moved : Nat) :
    rotateIndex moved inner ∘ liftIndex moved (· + inner) = (· + inner) := by
  funext index
  simp only [Function.comp_apply, rotateIndex, liftIndex]
  split_ifs <;> omega

/-! ## A copy dropped at any depth -/

section Drop

variable {language : LanguageDef} [laws : ReplicationLanguage language block]

include laws in
/-- **A copy beside its replicated component is absorbed at any depth**: below `inner` restrictions of a block whose
components hold a replicated component, a copy of its argument, the copy's restrictions just outside the inner ones,
drops out. Moving the copy's restrictions inside the inner ones makes the block the unfolding of the replicated
component. -/
theorem drop_copy_at {free : FreeTypeContext} {bound : List TypeExpr} (context : BaseContext free bound)
    {inner count : Nat} {components : List Pattern} {argument : Pattern}
    (member : Pattern.apply block.replicate [liftBVars 0 inner argument] ∈ components)
    (members : Members language block.toBlock free
      (List.replicate (inner + count) (TypeExpr.base block.name) ++ bound) components) :
    EquationEquiv (engineBasePremises RelationEnv.empty) language
      (Prenex.toPattern block.toBlock ⟨inner + (normal block (decompose block.toBlock argument)).count + count,
        components.map (rename (liftIndex inner (· + (normal block (decompose block.toBlock argument)).count))) ++
          (normal block (decompose block.toBlock argument)).components.map (liftBVars 0 inner)⟩)
      (Prenex.toPattern block.toBlock ⟨inner + count, components⟩) := by
  set copy := normal block (decompose block.toBlock argument) with copyIs
  have liftedCopy : normal block (decompose block.toBlock (liftBVars 0 inner argument)) =
      copy.renameOuter (· + inner) := by
    rw [liftBVars_zero_eq_rename, decompose_renameOuter, normal_renameOuter_mono (strictMono_add_shift inner)]
  have sound := unfoldWith_sound context (form := ⟨inner + count, components⟩) member members
  have unfoldedMembers := (UnfoldsWithin.single (block := block) (form := ⟨inner + count, components⟩)
    member).members context members
  rw [liftedCopy] at sound unfoldedMembers
  have fits : copy.count + inner ≤ copy.count + (inner + count) := by omega
  obtain ⟨-, reordered⟩ := block_reorder_equivalent (block := block.toBlock) (language := language)
    (orders_reorders _ _ (orders_complete _ _ (rotateOrder_isOrder fits))) unfoldedMembers
  have moved : (components.map (liftBVars 0 copy.count) ++
      copy.components.map (rename (liftIndex copy.count (· + inner)))).map
        (rename (Prenex.permute (copy.count + (inner + count)) (rotateOrder copy.count inner (copy.count + (inner + count))))) =
      components.map (rename (liftIndex inner (· + copy.count))) ++ copy.components.map (liftBVars 0 inner) := by
    rw [permute_rotateOrder fits, List.map_append, List.map_map, List.map_map]
    congr 1
    · refine List.map_congr_left fun component _ => ?_
      simp only [Function.comp_apply]
      rw [liftBVars_zero_eq_rename, rename_comp, rotateIndex_lift]
    · refine List.map_congr_left fun component _ => ?_
      simp only [Function.comp_apply]
      rw [liftBVars_zero_eq_rename, rename_comp, rotateIndex_copy]
  change EquationEquiv _ _ _ (Prenex.toPattern block.toBlock ⟨copy.count + (inner + count),
    components.map (liftBVars 0 copy.count) ++ copy.components.map (rename (liftIndex copy.count (· + inner)))⟩)
    at sound
  change ProcEquiv language block.toBlock free bound _ (Prenex.toPattern block.toBlock ⟨copy.count + (inner + count),
    (components.map (liftBVars 0 copy.count) ++ copy.components.map (rename (liftIndex copy.count (· + inner)))).map
      (rename (Prenex.permute (copy.count + (inner + count))
        (rotateOrder copy.count inner (copy.count + (inner + count)))))⟩) at reordered
  rw [moved] at reordered
  rw [show inner + copy.count + count = copy.count + (inner + count) by omega]
  exact Relation.EqvGen.symm _ _ (Relation.EqvGen.trans _ _ _ sound reordered.toEquationEquiv)

end Drop

/-! ## Copies of molecules -/

/-- **One-component replicated components copy molecules.** -/
theorem moleculeServers_of_flat (fresh : block.replicate ∉ block.emptyUnits) (restrictFresh : block.replicate ≠ block.restrict)
    {form : Prenex} (flat : flatServers block form = true) : moleculeServers block form = true := by
  unfold moleculeServers
  refine List.all_eq_true.mpr fun component member => ?_
  rcases found : replicatedArgument block component with _ | argument
  · rfl
  · obtain ⟨atomic, notReplicated⟩ :=
      flatServers_spec flat component member argument (mem_replicatedArgument.mp found)
    simp only [Option.all_some, List.all_eq_true]
    intro part partMember
    rw [atomic, normal_atom fresh restrictFresh atomic] at partMember
    simp only [Prenex.atom, List.mem_singleton] at partMember
    subst partMember
    simp [isReplicated_recanon, notReplicated]

/-- **The copy of a renamed argument is the copy renamed outside**, for a strictly monotone renaming. -/
theorem copy_rename {relabel : Nat → Nat} (mono : StrictMono relabel) (argument : Pattern) :
    normal block (decompose block.toBlock (rename relabel argument)) =
      (normal block (decompose block.toBlock argument)).renameOuter relabel := by
  rw [decompose_renameOuter, normal_renameOuter_mono mono]

theorem renameOuter_plain {form : Prenex} (plain : ∀ part ∈ form.components, isReplicated block part = false)
    (relabel : Nat → Nat) : ∀ part ∈ (form.renameOuter relabel).components, isReplicated block part = false := by
  intro part member
  obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp member
  rw [isReplicated_rename]
  exact plain original inOriginal

theorem liftBVars_apply_single (shift : Nat) (label : String) (argument : Pattern) :
    liftBVars 0 shift (.apply label [argument]) = .apply label [liftBVars 0 shift argument] := by
  rw [liftBVars_zero_eq_rename, liftBVars_zero_eq_rename, rename_apply]
  rfl

theorem isReplicated_liftBVars (shift : Nat) (component : Pattern) :
    isReplicated block (liftBVars 0 shift component) = isReplicated block component := by
  rw [liftBVars_zero_eq_rename, isReplicated_rename]

theorem map_rename_id (list : List Pattern) : list.map (rename id) = list := by
  conv_rhs => rw [← List.map_id list]
  exact List.map_congr_left fun pattern _ => rename_id pattern

theorem liftIndex_id (cutoff : Nat) : liftIndex cutoff id = id := by
  funext index
  simp only [liftIndex, id]
  split_ifs <;> omega

/-! ## Compressing an unfolding -/

/-- **A compression of an unfolding** to the copies holding some taken components: an unfolding of the same block
within as many unfoldings as taken components, whose components, renamed by a strictly monotone renaming into the
unfolding's restrictions and names, are the unfolding's but for dropped components, none replicated; the taken
components are among them, renamed; the block's replicated components stay, lifted, and are the only replicated
ones; and every context holding them reads beside the dropped components, below any number of inner restrictions,
as it reads without them. -/
structure Compression (language : LanguageDef) (block : ReplicationBlock) (free : FreeTypeContext)
    (bound : List TypeExpr) (form unfolded : Prenex) (taken : List Pattern) (compressed : Prenex)
    (embed : Nat → Nat) (dropped taken' : List Pattern) : Prop where
  within : UnfoldsWithin block taken.length form compressed
  mono : StrictMono embed
  inside : ∀ index < compressed.count, embed index < unfolded.count
  outside : ∀ index, compressed.count ≤ index → embed index = index - compressed.count + unfolded.count
  grows : form.count ≤ compressed.count
  components : unfolded.components.Perm (compressed.components.map (rename embed) ++ dropped)
  droppedPlain : ∀ component ∈ dropped, isReplicated block component = false
  takenFrom : taken'.Subperm compressed.components
  takenRenamed : taken.Perm (taken'.map (rename embed))
  serversKept : ∀ server ∈ form.components, isReplicated block server = true →
    liftBVars 0 (compressed.count - form.count) server ∈ compressed.components
  serversOnly : ∀ component ∈ compressed.components, isReplicated block component = true →
    ∃ server ∈ form.components, component = liftBVars 0 (compressed.count - form.count) server
  contexts : ∀ (inner : Nat) (others : List Pattern),
    (∀ server ∈ form.components, isReplicated block server = true →
      liftBVars 0 (inner + (compressed.count - form.count)) server ∈ others) →
    Members language block.toBlock free (List.replicate (inner + compressed.count) (TypeExpr.base block.name) ++ bound)
      others →
    EquationEquiv (engineBasePremises RelationEnv.empty) language
      (Prenex.toPattern block.toBlock ⟨inner + unfolded.count,
        others.map (rename (liftIndex inner embed)) ++ dropped.map (liftBVars 0 inner)⟩)
      (Prenex.toPattern block.toBlock ⟨inner + compressed.count, others⟩)

/-- Components renamed by a renaming that keeps restrictions among restrictions and moves names outside past them
stay typed. -/
theorem members_rename_lifted {language : LanguageDef} {free : FreeTypeContext} {bound : List TypeExpr}
    {inner source target : Nat} {embed : Nat → Nat} (inside : ∀ index < source, embed index < target)
    (outside : ∀ index, source ≤ index → embed index = index - source + target) {others : List Pattern}
    (members : Members language block.toBlock free
      (List.replicate (inner + source) (TypeExpr.base block.name) ++ bound) others) :
    Members language block.toBlock free (List.replicate (inner + target) (TypeExpr.base block.name) ++ bound)
      (others.map (rename (liftIndex inner embed))) := by
  intro element member
  obtain ⟨original, inOthers, rfl⟩ := List.mem_map.mp member
  refine rename_typed_on_support (members original inOthers) fun index sort _ lookup =>
    frame_lookup ⟨fun below => ?_, fun above => ?_⟩ lookup
  · simp only [liftIndex]
    split_ifs with low
    · omega
    · have := inside (index - inner) (by omega)
      omega
  · simp only [liftIndex]
    rw [if_neg (by omega), outside (index - inner) (by omega)]
    omega

section Compress

variable {language : LanguageDef} [laws : ReplicationLanguage language block]

include laws in
/-- **An unfolding of a block whose replicated components copy molecules compresses to the copies holding taken
components**: by induction on the unfolding, a copy holding none is dropped, beside its replicated component at the
depth of the copies unfolded after it, and a copy holding some is the copy of the compressed block's replicated
component renamed. -/
theorem compress_unfolds {free : FreeTypeContext} {bound : List TypeExpr} (context : BaseContext free bound)
    {form unfolded : Prenex} (unfolds : Unfolds block form unfolded)
    (molecular : ∀ component ∈ form.components, ∀ argument, component = .apply block.replicate [argument] →
      ∀ part ∈ (normal block (decompose block.toBlock argument)).components, isReplicated block part = false)
    (formMembers : Members language block.toBlock free
      (List.replicate form.count (TypeExpr.base block.name) ++ bound) form.components) :
    ∀ (taken rest : List Pattern), unfolded.components.Perm (taken ++ rest) →
      (∀ part ∈ taken, isReplicated block part = false) →
      ∃ compressed embed dropped taken',
        Compression language block free bound form unfolded taken compressed embed dropped taken' := by
  induction unfolds with
  | refl =>
      intro taken rest split _
      refine ⟨_, id, [], taken, ⟨.refl _ _, strictMono_id, fun _ below => below, fun index above => by
        simp only [id]; omega, le_refl _, by simp [map_rename_id], by simp,
        (List.sublist_append_left taken rest).subperm.trans split.symm.subperm, by simp [map_rename_id],
        fun server member _ => by
          rw [Nat.sub_self, Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_zero]
          exact member,
        fun component member _ => ⟨component, member, by
          rw [Nat.sub_self, Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_zero]⟩,
        fun inner others _ _ => by
          rw [liftIndex_id, map_rename_id, List.map_nil, List.append_nil]
          exact .refl _⟩⟩
  | @step next argument prevUnfolds member recurse =>
      intro taken rest split plain
      generalize copyIs : normal block (decompose block.toBlock argument) = copy at split ⊢
      -- the taken components of the block and of the copy
      obtain ⟨tags, takenFirst, takenSecond, restFirst, restSecond, takenIs, firstPerm, secondPerm, -⟩ :=
        perm_append_split (first := next.components.map (liftBVars 0 copy.count)) (second := copy.components) split
      obtain ⟨chosen, unchosen, nextPerm, chosenMap⟩ := exists_perm_map (liftBVars 0 copy.count)
        ((List.sublist_append_left takenFirst restFirst).subperm.trans firstPerm.symm.subperm)
      have takenPerm : taken.Perm (takenFirst ++ takenSecond) := by
        rw [takenIs]
        exact interleave_perm tags takenFirst takenSecond
      have chosenPlain : ∀ part ∈ chosen, isReplicated block part = false := by
        intro part inChosen
        have lifted : liftBVars 0 copy.count part ∈ takenFirst := by
          rw [← chosenMap]
          exact List.mem_map_of_mem inChosen
        rw [← isReplicated_liftBVars copy.count]
        exact plain _ (takenPerm.symm.subset (List.mem_append_left _ lifted))
      obtain ⟨compressed, embed, dropped, taken', comp⟩ := recurse chosen unchosen nextPerm chosenPlain
      -- the replicated component unfolded renames a lifted replicated component of the block
      have serverIn : Pattern.apply block.replicate [argument] ∈ compressed.components.map (rename embed) := by
        rcases List.mem_append.mp (comp.components.subset member) with found | inDropped
        · exact found
        · have notReplicated := comp.droppedPlain _ inDropped
          simp [isReplicated] at notReplicated
      obtain ⟨serverC, inCompressed, serverCIs⟩ := List.mem_map.mp serverIn
      have serverCReplicated : isReplicated block serverC = true := by
        rw [← isReplicated_rename embed, serverCIs]
        simp [isReplicated]
      obtain ⟨server, inForm, serverCLift⟩ := comp.serversOnly serverC inCompressed serverCReplicated
      have serverReplicated : isReplicated block server = true := by
        rwa [serverCLift, isReplicated_liftBVars] at serverCReplicated
      obtain ⟨argument₀, rfl⟩ := eq_of_isReplicated serverReplicated
      rw [liftBVars_apply_single] at serverCLift
      subst serverCLift
      have argumentIs : argument = rename embed (liftBVars 0 (compressed.count - form.count) argument₀) := by
        rw [rename_apply] at serverCIs
        simp only [List.map_cons, List.map_nil, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at serverCIs
        exact serverCIs.symm
      -- the copies
      have copyCIs : normal block (decompose block.toBlock (liftBVars 0 (compressed.count - form.count) argument₀)) =
          (normal block (decompose block.toBlock argument₀)).renameOuter (· + (compressed.count - form.count)) := by
        rw [liftBVars_zero_eq_rename, copy_rename (strictMono_add_shift _)]
      have copyCPlain : ∀ part ∈ (normal block (decompose block.toBlock
          (liftBVars 0 (compressed.count - form.count) argument₀))).components, isReplicated block part = false := by
        rw [copyCIs]
        exact renameOuter_plain (molecular _ inForm argument₀ rfl) _
      have copyRenamed : copy = (normal block (decompose block.toBlock
          (liftBVars 0 (compressed.count - form.count) argument₀))).renameOuter embed := by
        rw [← copyIs, argumentIs, copy_rename comp.mono]
      have copyPlain : ∀ part ∈ copy.components, isReplicated block part = false := by
        rw [copyRenamed]
        exact renameOuter_plain copyCPlain _
      -- the typed block before the unfolding
      have nextMembers : Members language block.toBlock free
          (List.replicate next.count (TypeExpr.base block.name) ++ bound) next.components := by
        obtain ⟨depth, within⟩ := prevUnfolds.within
        exact within.members context formMembers
      have droppedMembers : Members language block.toBlock free
          (List.replicate next.count (TypeExpr.base block.name) ++ bound) dropped := fun element inDropped =>
        nextMembers element (comp.components.symm.subset (List.mem_append_right _ inDropped))
      by_cases untouched : takenSecond = []
      -- a copy holding no taken component is dropped
      · subst untouched
        rw [List.append_nil] at takenPerm
        refine ⟨compressed, (· + copy.count) ∘ embed, dropped.map (liftBVars 0 copy.count) ++ copy.components, taken',
          ⟨?_, (strictMono_add_shift copy.count).comp comp.mono, fun index below => ?_, fun index above => ?_,
          comp.grows, ?_, fun component inDropped => ?_, comp.takenFrom, ?_, comp.serversKept, comp.serversOnly,
          fun inner outside servers outsideMembers => ?_⟩⟩
        · have lengths : chosen.length = taken.length := by
            rw [takenPerm.length_eq, ← chosenMap, List.length_map]
          rw [← lengths]
          exact comp.within
        · have inside := comp.inside index below
          show embed index + copy.count < copy.count + next.count
          omega
        · show embed index + copy.count = index - compressed.count + (copy.count + next.count)
          rw [comp.outside index above]
          omega
        · show (next.components.map (liftBVars 0 copy.count) ++ copy.components).Perm
            (compressed.components.map (rename ((· + copy.count) ∘ embed)) ++
              (dropped.map (liftBVars 0 copy.count) ++ copy.components))
          have lifted := comp.components.map (liftBVars 0 copy.count)
          rw [List.map_append, List.map_map] at lifted
          have renamed : liftBVars 0 copy.count ∘ rename embed = rename ((· + copy.count) ∘ embed) := by
            funext component
            simp only [Function.comp_apply]
            rw [liftBVars_zero_eq_rename, rename_comp]
          rw [renamed] at lifted
          rw [← List.append_assoc]
          exact lifted.append_right _
        · rcases List.mem_append.mp inDropped with lifted | inCopy
          · obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp lifted
            rw [isReplicated_liftBVars]
            exact comp.droppedPlain original inOriginal
          · exact copyPlain component inCopy
        · refine takenPerm.trans ?_
          rw [← chosenMap]
          refine (comp.takenRenamed.map (liftBVars 0 copy.count)).trans (List.Perm.of_eq ?_)
          rw [List.map_map]
          refine List.map_congr_left fun part _ => ?_
          simp only [Function.comp_apply]
          rw [liftBVars_zero_eq_rename, rename_comp]
        -- every context: the copy is absorbed at its depth
        · have SMembers : Members language block.toBlock free
              (List.replicate (inner + next.count) (TypeExpr.base block.name) ++ bound)
              (outside.map (rename (liftIndex inner embed)) ++ dropped.map (liftBVars 0 inner)) := by
            intro element inS
            rcases List.mem_append.mp inS with renamed | lifted
            · exact members_rename_lifted comp.inside comp.outside outsideMembers element renamed
            · have liftedMembers := Members.lift (List.replicate inner (TypeExpr.base block.name)) droppedMembers
              rw [List.length_replicate, ← List.append_assoc, ← List.replicate_add] at liftedMembers
              exact liftedMembers element lifted
          have serverInS : Pattern.apply block.replicate [liftBVars 0 inner argument] ∈
              outside.map (rename (liftIndex inner embed)) ++ dropped.map (liftBVars 0 inner) := by
            refine List.mem_append_left _ (List.mem_map.mpr ⟨liftBVars 0 (inner + (compressed.count - form.count))
              (.apply block.replicate [argument₀]), servers _ inForm serverReplicated, ?_⟩)
            rw [liftBVars_apply_single, rename_apply, argumentIs, liftBVars_rename, ← liftBVars_liftBVars]
            rfl
          have drop := drop_copy_at context serverInS SMembers
          rw [copyIs] at drop
          have ih := comp.contexts inner outside servers outsideMembers
          have blockIs : (⟨inner + (copy.count + next.count),
              outside.map (rename (liftIndex inner ((· + copy.count) ∘ embed))) ++
                (dropped.map (liftBVars 0 copy.count) ++ copy.components).map (liftBVars 0 inner)⟩ : Prenex) =
              ⟨inner + copy.count + next.count,
                (outside.map (rename (liftIndex inner embed)) ++ dropped.map (liftBVars 0 inner)).map
                  (rename (liftIndex inner (· + copy.count))) ++ copy.components.map (liftBVars 0 inner)⟩ := by
            simp only [List.map_append, List.map_map, List.append_assoc, Prenex.mk.injEq]
            refine ⟨by omega, ?_⟩
            congr 1
            · refine List.map_congr_left fun component _ => ?_
              simp only [Function.comp_apply]
              rw [liftIndex_comp, rename_comp]
            · congr 1
              refine List.map_congr_left fun component _ => ?_
              simp only [Function.comp_apply]
              rw [liftBVars_zero_eq_rename copy.count, liftBVars_rename]
          show EquationEquiv _ _ (Prenex.toPattern block.toBlock ⟨inner + (copy.count + next.count),
              outside.map (rename (liftIndex inner ((· + copy.count) ∘ embed))) ++
                (dropped.map (liftBVars 0 copy.count) ++ copy.components).map (liftBVars 0 inner)⟩) _
          rw [blockIs]
          exact Relation.EqvGen.trans _ _ _ drop ih
      -- a copy holding taken components is kept: the copy of the compressed block's replicated component renamed
      · generalize copyCIs' : normal block (decompose block.toBlock
          (liftBVars 0 (compressed.count - form.count) argument₀)) = copyC at copyCPlain copyRenamed
        have countSame : copy.count = copyC.count := by
          rw [copyRenamed]
          rfl
        have copyComponents : copy.components = copyC.components.map (rename (liftIndex copyC.count embed)) := by
          rw [copyRenamed]
          rfl
        have secondSub : takenSecond.Subperm (copyC.components.map (rename (liftIndex copyC.count embed))) := by
          rw [← copyComponents]
          exact (List.sublist_append_left takenSecond restSecond).subperm.trans secondPerm.symm.subperm
        obtain ⟨chosenSecond, unchosenSecond, copyCPerm, chosenSecondMap⟩ :=
          exists_perm_map (rename (liftIndex copyC.count embed)) secondSub
        have lengths : chosen.length + 1 ≤ taken.length := by
          rw [takenPerm.length_eq, List.length_append, ← chosenMap, List.length_map]
          have := List.length_pos_of_ne_nil untouched
          omega
        have grows := comp.grows
        refine ⟨compressed.unfoldWith copyC, liftIndex copyC.count embed, dropped.map (liftBVars 0 copyC.count),
          taken'.map (liftBVars 0 copyC.count) ++ chosenSecond,
          ⟨?_, strictMono_liftIndex comp.mono _, fun index below => ?_, fun index above => ?_,
          comp.grows.trans (Nat.le_add_left _ _), ?_, fun component inDropped => ?_, ?_, ?_,
          fun server' inForm' replicated' => ?_, fun component inC replicated' => ?_,
          fun inner outside servers outsideMembers => ?_⟩⟩
        · have within := comp.within.snoc inCompressed
          rw [copyCIs'] at within
          exact within.mono lengths
        · have below' : index < copyC.count + compressed.count := below
          show liftIndex copyC.count embed index < copy.count + next.count
          rw [countSame]
          simp only [liftIndex]
          split_ifs with low
          · omega
          · have := comp.inside (index - copyC.count) (by omega)
            omega
        · have above' : copyC.count + compressed.count ≤ index := above
          show liftIndex copyC.count embed index = index - (copyC.count + compressed.count) + (copy.count + next.count)
          rw [countSame]
          simp only [liftIndex]
          rw [if_neg (by omega), comp.outside (index - copyC.count) (by omega)]
          omega
        · show (next.components.map (liftBVars 0 copy.count) ++ copy.components).Perm
            ((compressed.components.map (liftBVars 0 copyC.count) ++ copyC.components).map
              (rename (liftIndex copyC.count embed)) ++ dropped.map (liftBVars 0 copyC.count))
          have lifted := comp.components.map (liftBVars 0 copyC.count)
          rw [List.map_append, List.map_map] at lifted
          have renamed : liftBVars 0 copyC.count ∘ rename embed =
              rename (liftIndex copyC.count embed) ∘ liftBVars 0 copyC.count := by
            funext component
            simp only [Function.comp_apply]
            rw [liftBVars_rename]
          rw [renamed, ← List.map_map] at lifted
          rw [countSame, copyComponents, List.map_append]
          refine (lifted.append_right _).trans ?_
          rw [List.append_assoc, List.append_assoc]
          exact List.Perm.append_left _ List.perm_append_comm
        · obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp inDropped
          rw [isReplicated_liftBVars]
          exact comp.droppedPlain original inOriginal
        · show (taken'.map (liftBVars 0 copyC.count) ++ chosenSecond).Subperm
            (compressed.components.map (liftBVars 0 copyC.count) ++ copyC.components)
          obtain ⟨sub, subPerm, subSublist⟩ := comp.takenFrom
          obtain ⟨sub', subPerm', subSublist'⟩ :=
            (List.sublist_append_left chosenSecond unchosenSecond).subperm.trans copyCPerm.symm.subperm
          exact ⟨sub.map (liftBVars 0 copyC.count) ++ sub', (subPerm.map _).append subPerm',
            (subSublist.map _).append subSublist'⟩
        · refine takenPerm.trans ?_
          rw [← chosenMap, ← chosenSecondMap, List.map_append]
          refine List.Perm.append_right _ ((comp.takenRenamed.map (liftBVars 0 copy.count)).trans
            (List.Perm.of_eq ?_))
          rw [List.map_map, List.map_map, countSame]
          refine List.map_congr_left fun part _ => ?_
          simp only [Function.comp_apply]
          rw [liftBVars_rename]
        · show liftBVars 0 (copyC.count + compressed.count - form.count) server' ∈
            compressed.components.map (liftBVars 0 copyC.count) ++ copyC.components
          rw [show copyC.count + compressed.count - form.count = copyC.count + (compressed.count - form.count) by
            omega, ← liftBVars_liftBVars]
          exact List.mem_append_left _ (List.mem_map_of_mem (comp.serversKept server' inForm' replicated'))
        · rcases List.mem_append.mp inC with lifted | inCopy
          · obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp lifted
            rw [isReplicated_liftBVars] at replicated'
            obtain ⟨server', inForm', originalIs⟩ := comp.serversOnly original inOriginal replicated'
            refine ⟨server', inForm', ?_⟩
            show liftBVars 0 copyC.count original =
              liftBVars 0 (copyC.count + compressed.count - form.count) server'
            rw [originalIs, liftBVars_liftBVars,
              show copyC.count + compressed.count - form.count = copyC.count + (compressed.count - form.count) by
                omega]
          · rw [copyCPlain component inCopy] at replicated'
            cases replicated'
        -- every context: the inner restrictions grow by the copy's
        · have servers' : ∀ server ∈ form.components, isReplicated block server = true →
              liftBVars 0 (inner + copyC.count + (compressed.count - form.count)) server ∈ outside := by
            intro server' inForm' replicated'
            have kept : liftBVars 0 (inner + (copyC.count + compressed.count - form.count)) server' ∈ outside :=
              servers server' inForm' replicated'
            rwa [show inner + (copyC.count + compressed.count - form.count) =
              inner + copyC.count + (compressed.count - form.count) by omega] at kept
          have members' : Members language block.toBlock free
              (List.replicate (inner + copyC.count + compressed.count) (TypeExpr.base block.name) ++ bound)
              outside := by
            have typed : Members language block.toBlock free
                (List.replicate (inner + (copyC.count + compressed.count)) (TypeExpr.base block.name) ++ bound)
                outside := outsideMembers
            rwa [← Nat.add_assoc] at typed
          have ih := comp.contexts (inner + copyC.count) outside servers' members'
          rw [liftIndex_liftIndex, List.map_map]
          have droppedLifted : liftBVars 0 inner ∘ liftBVars 0 copyC.count = liftBVars 0 (inner + copyC.count) := by
            funext component
            exact liftBVars_liftBVars _ _ _
          rw [droppedLifted]
          show EquationEquiv _ _ (Prenex.toPattern block.toBlock ⟨inner + (copy.count + next.count), _⟩)
            (Prenex.toPattern block.toBlock ⟨inner + (copyC.count + compressed.count), outside⟩)
          rw [countSame, ← Nat.add_assoc, ← Nat.add_assoc]
          exact ih

end Compress

/-! ## Reactions of compressed unfoldings -/

section Reactions

variable {language : LanguageDef} [laws : ReplicationLanguage language block]
variable {step : Pattern → Pattern → Prop}

include laws in
/-- **Compressing an unfolding to the copies a reaction takes**, when the replicated components of a block copy
molecules: a reaction of an unfolding of the block is, renamed, a reaction of an unfolding within the arity, leaving
what reads as the first reaction leaves: the copies it does not take are absorbed by their replicated components,
which are not parts. -/
theorem compress_molecular (reactions : ReplicationReactions language block step) {free : FreeTypeContext}
    {bound : List TypeExpr} (context : BaseContext free bound) {depth : Nat} {form unfolded : Prenex}
    (molecular : ∀ component ∈ form.components, ∀ argument, component = .apply block.replicate [argument] →
      ∀ part ∈ (normal block (decompose block.toBlock argument)).components, isReplicated block part = false)
    (formMembers : Members language block.toBlock free
      (List.replicate form.count (TypeExpr.base block.name) ++ bound) form.components)
    (unfolds : UnfoldsWithin block depth form unfolded) {redex : reactions.Redex} {restU : List Pattern}
    (split : unfolded.components.Perm (reactions.parts redex ++ restU))
    (plain : ∀ part ∈ reactions.parts redex, isReplicated block part = false)
    (members : Members language block.toBlock free (List.replicate unfolded.count (TypeExpr.base block.name) ++ bound)
      unfolded.components)
    (objects : ∀ component ∈ unfolded.components, isObjectPattern component = true) :
    ∃ compressed, UnfoldsWithin block reactions.arity form compressed ∧
      ∃ (redex' : reactions.Redex) (restC : List Pattern),
        compressed.components.Perm (reactions.parts redex' ++ restC) ∧
        (∀ part ∈ reactions.parts redex', isReplicated block part = false) ∧
        Members language block.toBlock free (List.replicate compressed.count (TypeExpr.base block.name) ++ bound)
          compressed.components ∧
        (∀ component ∈ compressed.components, isObjectPattern component = true) ∧
        EquationEquiv (engineBasePremises RelationEnv.empty) language
          (Prenex.restricts block.toBlock compressed.count
            (.collection .hashBag (reactions.result redex' ++ restC) none))
          (Prenex.restricts block.toBlock unfolded.count
            (.collection .hashBag (reactions.result redex ++ restU) none)) := by
  obtain ⟨compressed, embed, dropped, taken', comp⟩ :=
    compress_unfolds context unfolds.unfolds molecular formMembers (reactions.parts redex) restU split plain
  have back : Function.LeftInverse (Function.invFun embed) embed := Function.leftInverse_invFun comp.mono.injective
  -- the redex read back through the renaming
  have partsIs : (reactions.parts (reactions.rename (Function.invFun embed) redex)).Perm taken' := by
    rw [reactions.parts_rename]
    refine (comp.takenRenamed.map _).trans (List.Perm.of_eq ?_)
    rw [List.map_map]
    conv_rhs => rw [← map_rename_id taken']
    refine List.map_congr_left fun part _ => ?_
    simp only [Function.comp_apply]
    rw [rename_comp]
    congr 1
    funext index
    exact back index
  obtain ⟨chosen, restC, compressedPerm, chosenIs⟩ := exists_perm_map id (by simpa using comp.takenFrom)
  rw [List.map_id] at chosenIs
  subst chosenIs
  have takenPlain : ∀ part ∈ chosen, isReplicated block part = false := by
    intro part inTaken
    rw [← isReplicated_rename embed]
    exact plain _ (comp.takenRenamed.symm.subset (List.mem_map_of_mem inTaken))
  have compressedMembers := comp.within.members context formMembers
  have restCMembers : Members language block.toBlock free
      (List.replicate compressed.count (TypeExpr.base block.name) ++ bound) restC := fun element member =>
    compressedMembers element (compressedPerm.symm.subset (List.mem_append_right _ member))
  have partsMembers : Members language block.toBlock free
      (List.replicate compressed.count (TypeExpr.base block.name) ++ bound)
      (reactions.parts (reactions.rename (Function.invFun embed) redex)) := fun element member =>
    compressedMembers element (compressedPerm.symm.subset (List.mem_append_left _ (partsIs.subset member)))
  have leftMembers : Members language block.toBlock free
      (List.replicate compressed.count (TypeExpr.base block.name) ++ bound)
      (reactions.result (reactions.rename (Function.invFun embed) redex) ++ restC) := by
    intro element member
    rcases List.mem_append.mp member with inResult | inRest
    · exact reactions.result_members _ partsMembers element inResult
    · exact restCMembers element inRest
  -- what the redex leaves is what the redex read back leaves, renamed
  have resultIs : reactions.result redex =
      (reactions.result (reactions.rename (Function.invFun embed) redex)).map (rename embed) := by
    rw [reactions.result_rename, List.map_map]
    conv_lhs => rw [← map_rename_id (reactions.result redex)]
    refine List.map_congr_left fun element inResult => ?_
    simp only [Function.comp_apply]
    rw [rename_comp]
    apply rename_congr
    intro index free
    obtain ⟨part, inParts, partFree⟩ := reactions.freeIn_result redex inResult free
    obtain ⟨original, -, rfl⟩ := List.mem_map.mp (comp.takenRenamed.subset inParts)
    obtain ⟨index', -, rfl⟩ := (freeIn_rename original).mp partFree
    simp only [id, Function.comp_apply]
    rw [back index']
  -- the rest of the unfolding is the rest of the compressed one renamed, beside the dropped components
  have restIs : restU.Perm (restC.map (rename embed) ++ dropped) := by
    have whole : unfolded.components.Perm (reactions.parts redex ++ (restC.map (rename embed) ++ dropped)) := by
      refine comp.components.trans ?_
      rw [← List.append_assoc]
      refine List.Perm.append_right _ ?_
      exact (compressedPerm.map _).trans ((List.Perm.of_eq List.map_append).trans
        (comp.takenRenamed.symm.append_right _))
    exact (List.perm_append_left_iff _).mp (split.symm.trans whole)
  have leftPerm : (reactions.result redex ++ restU).Perm
      ((reactions.result (reactions.rename (Function.invFun embed) redex) ++ restC).map (rename embed) ++ dropped) := by
    rw [List.map_append, List.append_assoc, ← resultIs]
    exact List.Perm.append_left _ restIs
  have unfoldedLeftMembers : Members language block.toBlock free
      (List.replicate unfolded.count (TypeExpr.base block.name) ++ bound) (reactions.result redex ++ restU) := by
    have unfoldedParts : Members language block.toBlock free
        (List.replicate unfolded.count (TypeExpr.base block.name) ++ bound) (reactions.parts redex) :=
      fun element member => members element (split.symm.subset (List.mem_append_left _ member))
    intro element member
    rcases List.mem_append.mp member with inResult | inRest
    · exact reactions.result_members redex unfoldedParts element inResult
    · exact members element (split.symm.subset (List.mem_append_right _ inRest))
  -- every replicated component of the block stays beside what the redex leaves
  have servers : ∀ server ∈ form.components, isReplicated block server = true →
      liftBVars 0 (0 + (compressed.count - form.count)) server ∈
        reactions.result (reactions.rename (Function.invFun embed) redex) ++ restC := by
    intro server inForm replicated
    rw [Nat.zero_add]
    have kept := compressedPerm.subset (comp.serversKept server inForm replicated)
    rcases List.mem_append.mp kept with inTaken | inRest
    · have notReplicated := takenPlain _ inTaken
      rw [isReplicated_liftBVars, replicated] at notReplicated
      cases notReplicated
    · exact List.mem_append_right _ inRest
  have contexts := comp.contexts 0 _ servers (by simpa using leftMembers)
  have liftNone : liftBVars 0 0 = id :=
    funext fun pattern => Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_zero pattern 0
  rw [liftIndex_zero, liftNone, List.map_id, Nat.zero_add, Nat.zero_add] at contexts
  refine ⟨compressed, comp.within.mono (reactions.arity_le redex), reactions.rename (Function.invFun embed) redex, restC,
    (compressedPerm.trans (partsIs.symm.append_right _)), fun part inParts => takenPlain part (partsIs.subset inParts),
    compressedMembers, fun component inCompressed => ?_, ?_⟩
  · rw [← isObjectPattern_rename component embed]
    exact objects _ (comp.components.symm.subset (List.mem_append_left _ (List.mem_map_of_mem inCompressed)))
  · have mappedMembers : Members language block.toBlock free
        (List.replicate unfolded.count (TypeExpr.base block.name) ++ bound)
        ((reactions.result (reactions.rename (Function.invFun embed) redex) ++ restC).map (rename embed) ++ dropped) :=
      fun element member => unfoldedLeftMembers element (leftPerm.symm.subset member)
    simp only [Prenex.toPattern] at contexts
    exact Relation.EqvGen.trans _ _ _
      (restricts_equation (block := block.toBlock) compressed.count (bag_body_equivalent leftMembers).toEquationEquiv)
      (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ contexts)
        (restricts_equation (block := block.toBlock) unfolded.count (Relation.EqvGen.trans _ _ _
          (Relation.EqvGen.symm _ _ (bag_body_equivalent mappedMembers).toEquationEquiv)
          (bag_perm_equivalent (block := block) mappedMembers leftPerm.symm).toEquationEquiv)))

end Reactions

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks
