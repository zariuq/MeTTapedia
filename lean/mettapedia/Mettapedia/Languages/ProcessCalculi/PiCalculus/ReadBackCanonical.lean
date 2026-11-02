import Mettapedia.Languages.ProcessCalculi.PiCalculus.ReadBackAlpha

/-!
# The canonical form of a named pattern, read back

`piCalc`'s prenex canonical form changes a named pattern only by the named calculus's structural congruence without
unfolding:

- **The block of a named pattern reads back as the restriction of its components** at any fresh, distinct names
  (`decompose_reads`): restrictions are extruded past parallel components, renamed apart, and garbage restrictions
  dropped.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PiCalculus.PrenexForm

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Blocks (piBlock piRepBlock piBlockSignature)
open Mettapedia.OSLF.MeTTaIL.ContextSubstitution (Assignment substitute lift substituteList_eq_map)
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars freeVars)
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (FreeIn)
open Mettapedia.FreshString (fresh fresh_not_mem)
open Prenex

/-! ## Guards -/

/-- A component of a block of a named pattern: an input, a replicated input or an output. -/
def isGuard : Pattern → Bool
  | .apply "PiInp" [_, .lambda _ _] => true
  | .apply "PiRep" [.apply "PiInp" [_, .lambda _ _]] => true
  | .apply "PiOut" [_, _] => true
  | _ => false

theorem guard_cases {component : Pattern} (guard : isGuard component = true) :
    (∃ channel binder body, component = .apply "PiInp" [channel, .lambda binder body]) ∨
      (∃ channel binder body, component = .apply "PiRep" [.apply "PiInp" [channel, .lambda binder body]]) ∨
        ∃ channel datum, component = .apply "PiOut" [channel, datum] := by
  unfold isGuard at guard
  split at guard
  · exact .inl ⟨_, _, _, rfl⟩
  · exact .inr (.inl ⟨_, _, _, rfl⟩)
  · exact .inr (.inr ⟨_, _, rfl⟩)
  · cases guard

theorem isGuard_substitute (assignment : Assignment) {component : Pattern} (guard : isGuard component = true) :
    isGuard (substitute assignment component) = true := by
  rcases guard_cases guard with ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩ <;>
    simp [substitute, substituteList_eq_map, isGuard]

theorem isGuard_rename (relabel : Nat → Nat) {component : Pattern} (guard : isGuard component = true) :
    isGuard (rename relabel component) = true :=
  isGuard_substitute _ guard

theorem isGuard_liftBVars (cutoff amount : Nat) {component : Pattern} (guard : isGuard component = true) :
    isGuard (liftBVars cutoff amount component) = true := by
  rw [liftBVars_eq_rename]
  exact isGuard_rename _ guard

/-! ## Blocks read back -/

/-- **A process read as a block**: the block's components are guards, readable under its restrictions, and the process
is congruent to their restriction at any fresh, distinct names. -/
structure Reads (avoid : Finset Name) (env : List Name) (process : Process) (form : Prenex) : Prop where
  guards : ∀ component ∈ form.components, isGuard component = true
  readable : ∀ component ∈ form.components, Readable avoid (env.length + form.count) component
  reads : ∀ names : List Name, names.length = form.count → names.Nodup → (∀ name ∈ names, name ∉ avoid ∧ name ∉ env) →
    Congruent process (nuList names (parList (form.components.map (readBack avoid (names.reverse ++ env)))))

theorem nil_reads (avoid : Finset Name) (env : List Name) : Reads avoid env .nil nil := by
  refine ⟨by simp, by simp, fun names length _ _ => ?_⟩
  rw [List.length_eq_zero_iff.mp length]
  exact Congruent.refl _

theorem atom_reads {avoid : Finset Name} {env : List Name} {component : Pattern} (guard : isGuard component = true)
    (readable : Readable avoid env.length component) : Reads avoid env (readBack avoid env component) (atom component) := by
  refine ⟨by simpa [atom] using guard, by simpa [atom] using readable, fun names length _ _ => ?_⟩
  rw [List.length_eq_zero_iff.mp length]
  simpa [atom, nuList, parList] using (Congruent.nilRight (readBack avoid env component)).symm

theorem mem_freeNames_parList {name : Name} : ∀ {processes : List Process}, name ∈ (parList processes).freeNames →
    ∃ process ∈ processes, name ∈ process.freeNames
  | [], free => by simp [parList, Process.freeNames] at free
  | first :: rest, free => by
      simp only [parList, Process.freeNames, Finset.mem_union] at free
      rcases free with here | there
      · exact ⟨first, List.mem_cons_self, here⟩
      · obtain ⟨process, member, inside⟩ := mem_freeNames_parList there
        exact ⟨process, List.mem_cons_of_mem _ member, inside⟩

/-- The free names of the read-back components of a block are avoided, among the block's names, or given. -/
theorem freeNames_components {avoid : Finset Name} {env names : List Name} {components : List Pattern}
    (readable : ∀ component ∈ components, Readable avoid (env.length + names.length) component) {name : Name}
    (free : name ∈ (parList (components.map (readBack avoid (names.reverse ++ env)))).freeNames) :
    name ∈ avoid ∨ name ∈ names ∨ name ∈ env := by
  obtain ⟨process, member, inside⟩ := mem_freeNames_parList free
  obtain ⟨component, componentMember, rfl⟩ := List.mem_map.mp member
  rcases ((readable component componentMember).depth (by simp; omega) :
      Readable avoid (names.reverse ++ env).length component).freeNames inside with here | there
  · exact .inl here
  · rcases List.mem_append.mp there with inNames | inEnv
    · exact .inr (.inl (List.mem_reverse.mp inNames))
    · exact .inr (.inr inEnv)

theorem forall₂_map_map {α β γ : Type} {relation : β → γ → Prop} {first : α → β} {second : α → γ} :
    ∀ {list : List α}, (∀ element ∈ list, relation (first element) (second element)) →
      List.Forall₂ relation (list.map first) (list.map second)
  | [], _ => .nil
  | element :: _, each => .cons (each element List.mem_cons_self)
      (forall₂_map_map fun other member => each other (List.mem_cons_of_mem _ member))

/-- **Two blocks side by side read as one block**: the restrictions merge, the first's outermost. -/
theorem par_reads {avoid : Finset Name} {env : List Name} {first second : Process} {firstForm secondForm : Prenex}
    (firstReads : Reads avoid env first firstForm) (secondReads : Reads avoid env second secondForm) :
    Reads avoid env (first ||| second) (firstForm.par secondForm) := by
  refine ⟨?_, ?_, ?_⟩
  · intro component member
    simp only [Prenex.par, List.mem_append, List.mem_map] at member
    rcases member with ⟨original, originalMember, rfl⟩ | ⟨original, originalMember, rfl⟩
    · exact isGuard_liftBVars _ _ (firstReads.guards original originalMember)
    · exact isGuard_liftBVars _ _ (secondReads.guards original originalMember)
  · intro component member
    simp only [Prenex.par, List.mem_append, List.mem_map] at member
    rcases member with ⟨original, originalMember, rfl⟩ | ⟨original, originalMember, rfl⟩
    · rw [liftBVars_eq_rename]
      refine (firstReads.readable original originalMember).rename _ fun index free => ?_
      have below := free.lt_of_scoped (firstReads.readable original originalMember).inScope
      simp only [shiftAbove, Nat.not_lt_zero, if_false, Prenex.par_count]
      omega
    · rw [liftBVars_eq_rename]
      refine (secondReads.readable original originalMember).rename _ fun index free => ?_
      have below := free.lt_of_scoped (secondReads.readable original originalMember).inScope
      simp only [shiftAbove, Prenex.par_count]
      split <;> omega
  · intro names length nodup fresh
    simp only [Prenex.par_count] at length
    set firstNames := names.take firstForm.count
    set secondNames := names.drop firstForm.count
    have split : names = firstNames ++ secondNames := (List.take_append_drop _ _).symm
    have firstLength : firstNames.length = firstForm.count := by simp [firstNames]; omega
    have secondLength : secondNames.length = secondForm.count := by simp [secondNames]; omega
    rw [split] at nodup fresh
    have apart := (List.nodup_append.mp nodup).2.2
    have firstFresh : ∀ name ∈ firstNames, name ∉ avoid ∧ name ∉ env := fun name member =>
      fresh name (List.mem_append_left _ member)
    have secondFresh : ∀ name ∈ secondNames, name ∉ avoid ∧ name ∉ env := fun name member =>
      fresh name (List.mem_append_right _ member)
    have firstReadable : ∀ component ∈ firstForm.components,
        Readable avoid (env.length + firstNames.length) component := fun component member =>
      (firstReads.readable component member).depth (by rw [firstLength])
    have secondReadable : ∀ component ∈ secondForm.components,
        Readable avoid (env.length + secondNames.length) component := fun component member =>
      (secondReads.readable component member).depth (by rw [secondLength])
    refine (Congruent.par (firstReads.reads firstNames firstLength (List.nodup_append.mp nodup).1 firstFresh)
      (secondReads.reads secondNames secondLength (List.nodup_append.mp nodup).2.1 secondFresh)).trans ?_
    refine (nuList_merge ?_ ?_).trans ?_
    · refine Finset.disjoint_left.mpr fun name inFirst inside => ?_
      rw [freeNames_nuList] at inside
      obtain ⟨inside, notSecond⟩ := Finset.mem_sdiff.mp inside
      have inFirst := List.mem_toFinset.mp inFirst
      rcases freeNames_components secondReadable inside with avoided | inSecond | inEnv
      · exact (firstFresh name inFirst).1 avoided
      · exact notSecond (List.mem_toFinset.mpr inSecond)
      · exact (firstFresh name inFirst).2 inEnv
    · refine Finset.disjoint_left.mpr fun name inSecond inside => ?_
      have inSecond := List.mem_toFinset.mp inSecond
      rcases freeNames_components firstReadable inside with avoided | inFirst | inEnv
      · exact (secondFresh name inSecond).1 avoided
      · exact apart name inFirst name inSecond rfl
      · exact (secondFresh name inSecond).2 inEnv
    rw [← split]
    refine nuList_congruent names ((parList_append _ _).symm.trans (parList_forall₂ ?_))
    rw [Prenex.par, List.map_append, List.map_map, List.map_map]
    refine forall₂_append (forall₂_map_map fun component member => ?_) (forall₂_map_map fun component member => ?_)
    · rw [Function.comp_apply, liftBVars_eq_rename]
      refine (readBack_rename _ ((firstReadable _ member).depth (by simp; omega)) (fun index' free => ?_)
        (fun index' free => ?_)).symm
      · have below := free.lt_of_scoped (firstReadable _ member).inScope
        simp only [shiftAbove, Nat.not_lt_zero, if_false, List.length_append, List.length_reverse]
        rw [split, List.length_append]
        omega
      · have shifted := envAssignment_shift [] secondNames.reverse (firstNames.reverse ++ env) index'
        simp only [List.nil_append, List.length_nil, Nat.not_lt_zero, if_false, List.length_reverse] at shifted
        rw [split, List.reverse_append, List.append_assoc]
        simpa [shiftAbove, secondLength] using shifted
    · rw [Function.comp_apply, liftBVars_eq_rename]
      refine (readBack_rename _ ((secondReadable _ member).depth (by rw [List.length_append, List.length_reverse]; omega)) (fun index' free => ?_)
        (fun index' free => ?_)).symm
      · have below := free.lt_of_scoped (secondReadable _ member).inScope
        simp only [shiftAbove, List.length_append, List.length_reverse]
        rw [split, List.length_append]
        split <;> omega
      · have shifted := envAssignment_shift secondNames.reverse firstNames.reverse env index'
        simp only [List.length_reverse] at shifted
        rw [split, List.reverse_append]
        simpa [shiftAbove, secondLength, firstLength] using shifted

theorem decomposeList_reads {avoid : Finset Name} {env : List Name} : ∀ {elements : List Pattern},
    (∀ element ∈ elements, Reads avoid env (readBack avoid env element) (decompose piBlock element)) →
      Reads avoid env (parList (elements.map (readBack avoid env))) (decomposeList piBlock elements)
  | [], _ => by simpa [decomposeList, parList] using nil_reads avoid env
  | element :: rest, each => by
      simp only [decomposeList, List.map_cons, parList]
      exact par_reads (each element List.mem_cons_self)
        (decomposeList_reads fun other member => each other (List.mem_cons_of_mem _ member))

/-- The one place of a name fresh for the others. -/
theorem index_of_fresh {names env : List Name} {name : Name} (notNames : name ∉ names) (notEnv : name ∉ env)
    {index : Nat} (inside : index < (names.reverse ++ name :: env).length)
    (found : (names.reverse ++ name :: env)[index] = name) : index = names.length := by
  rw [List.getElem_append] at found
  split at found
  · exact absurd (List.mem_reverse.mp (found ▸ List.getElem_mem _)) notNames
  · rename_i outside
    simp only [List.length_reverse] at outside found
    cases position : index - names.length with
    | zero => omega
    | succ rest =>
        simp only [position, List.getElem_cons_succ] at found
        exact absurd (found ▸ List.getElem_mem _) notEnv

/-- **A restriction over a block reads as one block**: its name joins the block's restrictions when a component uses
it, and is garbage otherwise. -/
theorem close_reads {avoid : Finset Name} {env : List Name} {binder : Option String} {body : Pattern} {form : Prenex}
    (bodyReadable : Readable avoid (env.length + 1) body)
    (inner : ∀ name : Name, Reads avoid (name :: env) (readBack avoid (name :: env) body) form) :
    Reads avoid env (readBack avoid env (.apply "PiNu" [.lambda binder body])) form.close := by
  unfold Prenex.close
  split
  · refine ⟨fun component member => (inner "").guards component member,
      fun component member => ((inner "").readable component member).depth (by simp; omega), ?_⟩
    intro names length nodup freshNames
    cases names with
    | nil => simp at length
    | cons name rest =>
      simp only [Prenex.restrict_count, List.length_cons, Nat.add_right_cancel_iff] at length
      obtain ⟨notRest, restNodup⟩ := List.nodup_cons.mp nodup
      refine (readBack_nu bodyReadable (freshNames name List.mem_cons_self).1
        (freshNames name List.mem_cons_self).2).trans ?_
      simp only [nuList]
      refine Congruent.nu name ?_
      have expanded := (inner name).reads rest length restNodup fun other member =>
        ⟨(freshNames other (List.mem_cons_of_mem _ member)).1, by
          simp only [List.mem_cons, not_or]
          exact ⟨fun same => notRest (same ▸ member), (freshNames other (List.mem_cons_of_mem _ member)).2⟩⟩
      simpa [Prenex.restrict, List.reverse_cons, List.append_assoc] using expanded
  · rename_i unused
    have absent : ∀ component ∈ form.components, ¬ FreeIn form.count component := fun component member free =>
      unused (List.any_eq_true.mpr ⟨component, member, (mentions_iff component form.count).mpr free⟩)
    refine ⟨?_, ?_, ?_⟩
    · intro component member
      obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
      exact isGuard_rename _ ((inner "").guards original originalMember)
    · intro component member
      obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
      have readable := (inner "").readable original originalMember
      refine readable.rename _ fun index free => ?_
      have below := free.lt_of_scoped readable.inScope
      have notCount : index ≠ form.count := fun same => absent original originalMember (same ▸ free)
      simp only [List.length_cons] at below
      simp only [dropIndex]
      split <;> omega
    · intro names length nodup freshNames
      simp only at length
      have chosen := fresh_not_mem (avoid ∪ env.toFinset ∪ names.toFinset)
      generalize fresh (avoid ∪ env.toFinset ∪ names.toFinset) = name at chosen
      simp only [Finset.mem_union, List.mem_toFinset, not_or] at chosen
      obtain ⟨⟨notAvoid, notEnv⟩, notNames⟩ := chosen
      have namesFresh : ∀ other ∈ names, other ∉ avoid ∧ other ∉ name :: env := fun other member =>
        ⟨(freshNames other member).1, by
          simp only [List.mem_cons, not_or]
          exact ⟨fun same => notNames (same ▸ member), (freshNames other member).2⟩⟩
      have expanded := (inner name).reads names length nodup namesFresh
      refine (readBack_nu bodyReadable notAvoid notEnv).trans ((Congruent.nu name expanded).trans ?_)
      have componentReadable : ∀ component ∈ form.components,
          Readable avoid (names.reverse ++ name :: env).length component := fun component member =>
        ((inner name).readable component member).depth (by simp; omega)
      refine (nu_garbage ?_).trans ?_
      · rw [freeNames_nuList]
        intro inside
        obtain ⟨inside, _⟩ := Finset.mem_sdiff.mp inside
        obtain ⟨process, member, free⟩ := mem_freeNames_parList inside
        obtain ⟨component, componentMember, rfl⟩ := List.mem_map.mp member
        rcases (componentReadable component componentMember).freeName_index free with
          avoided | ⟨index, freeIndex, bound, found⟩
        · exact notAvoid avoided
        · have place := index_of_fresh notNames notEnv bound found
          exact absent component componentMember (by rw [← length, ← place]; exact freeIndex)
      · refine nuList_congruent names (parList_forall₂ ?_)
        rw [List.map_map]
        refine forall₂_map_map fun component member => ?_
        rw [Function.comp_apply]
        have readable := componentReadable component member
        refine (readBack_rename (dropIndex form.count) readable (fun index free => ?_)
          (fun index free => ?_)).symm
        · have below := free.lt_of_scoped readable.inScope
          have notCount : index ≠ form.count := fun same => absent component member (same ▸ free)
          simp only [List.length_append, List.length_reverse, List.length_cons] at below ⊢
          simp only [dropIndex]
          split <;> omega
        · have notCount : index ≠ form.count := fun same => absent component member (same ▸ free)
          have shifted := envAssignment_shift names.reverse [name] env (dropIndex form.count index)
          have back : (if dropIndex form.count index < names.reverse.length then dropIndex form.count index
              else dropIndex form.count index + [name].length) = index := by
            simp only [dropIndex, List.length_reverse, List.length_singleton, length]
            split_ifs <;> omega
          rw [back] at shifted
          simpa using shifted.symm

/-- **The block of a named pattern reads back as the restriction of its components** at any fresh, distinct
names. -/
theorem decompose_reads (avoid : Finset Name) : ∀ (size : Nat) {pattern : Pattern} (env : List Name),
    sizeOf pattern < size → Readable avoid env.length pattern →
      Reads avoid env (readBack avoid env pattern) (decompose piBlock pattern)
  | 0, _, _, small, _ => absurd small (Nat.not_lt_zero _)
  | size + 1, pattern, env, small, readable => by
      rcases named_cases readable.named with rfl | ⟨elements, rfl, elementsNamed⟩ | ⟨binder, body, rfl, bodyNamed⟩ |
        ⟨channel, binder, body, rfl, channelNamed, bodyNamed⟩ | ⟨channel, binder, body, rfl, channelNamed, bodyNamed⟩ |
        ⟨channel, datum, rfl, channelNamed, datumNamed⟩
      · simpa [decompose, readBack] using nil_reads avoid env
      · rw [decompose_bag, readBack_bag]
        apply decomposeList_reads
        intro element member
        exact decompose_reads avoid size env (by
          have := List.sizeOf_lt_of_mem member
          simp only [Pattern.collection.sizeOf_spec] at small
          omega) ⟨namedList_iff.mp elementsNamed element member, scoped_bag readable.inScope element member,
            avoided_bag readable.avoided element member⟩
      · have bodyReadable : Readable avoid (env.length + 1) body :=
          ⟨bodyNamed, scoped_lambda (scoped_unary readable.inScope), avoided_lambda (avoided_unary readable.avoided)⟩
        have bodySmall : sizeOf body < size := by
          simp only [Pattern.apply.sizeOf_spec, List.cons.sizeOf_spec, Pattern.lambda.sizeOf_spec] at small
          omega
        rw [decompose_restrict]
        exact close_reads bodyReadable fun name =>
          decompose_reads avoid size (name :: env) bodySmall (by simpa using bodyReadable)
      all_goals
        rw [decompose_atom (by simp) (by intro _ _; simp) (by intro _; simp) (by intro _ _ _ listed; simp at listed)]
        exact atom_reads (by simp [isGuard]) readable

/-! ## Fresh names, and reordering a block's names -/

/-- Distinct names fresh for a set. -/
def freshNames (avoid : Finset Name) : Nat → List Name
  | 0 => []
  | count + 1 => fresh avoid :: freshNames (insert (fresh avoid) avoid) count

theorem freshNames_length : ∀ (avoid : Finset Name) (count : Nat), (freshNames avoid count).length = count
  | _, 0 => rfl
  | _, count + 1 => by simp [freshNames, freshNames_length _ count]

theorem freshNames_fresh : ∀ (count : Nat) {avoid : Finset Name} {name : Name}, name ∈ freshNames avoid count →
    name ∉ avoid
  | 0, _, _, member => by simp [freshNames] at member
  | count + 1, avoid, name, member => by
      simp only [freshNames, List.mem_cons] at member
      rcases member with rfl | inside
      · exact fresh_not_mem avoid
      · exact fun inAvoid => freshNames_fresh count inside (Finset.mem_insert_of_mem inAvoid)

theorem freshNames_nodup : ∀ (count : Nat) (avoid : Finset Name), (freshNames avoid count).Nodup
  | 0, _ => List.nodup_nil
  | count + 1, _ => List.nodup_cons.mpr
      ⟨fun inside => freshNames_fresh count inside (Finset.mem_insert_self _ _), freshNames_nodup count _⟩

/-- The names of a block reordered: restriction `index` gets the name of restriction `order[index]`. -/
def reorder (names : List Name) (order : List Nat) : List Name :=
  (order.map fun index => names.reverse.getD index "").reverse

theorem map_getD_range {α : Type} (list : List α) (default : α) :
    (List.range list.length).map (fun index => list.getD index default) = list := by
  apply List.ext_getElem (by simp)
  intro index first second
  simp [List.getElem?_eq_getElem second]

theorem reorder_perm {names : List Name} {order : List Nat} (isOrder : IsOrder names.length order) :
    (reorder names order).Perm names := by
  unfold reorder
  refine (List.reverse_perm _).trans ?_
  have mapped := isOrder.map fun index => names.reverse.getD index ""
  rw [show names.length = names.reverse.length by simp, map_getD_range] at mapped
  exact mapped.trans (List.reverse_perm _)

theorem envAssignment_append_lt {front back : List Name} {index : Nat} (inside : index < front.length) :
    envAssignment (front ++ back) index = .fvar (front.getD index "") := by
  unfold envAssignment
  rw [dif_pos (by simp; omega)]
  simp [List.getElem_append_left inside, List.getElem?_eq_getElem inside]

theorem envAssignment_append_ge {front front' back : List Name} (same : front.length = front'.length) {index : Nat}
    (outside : front.length ≤ index) : envAssignment (front ++ back) index = envAssignment (front' ++ back) index := by
  unfold envAssignment
  by_cases inBack : index < front.length + back.length
  · rw [dif_pos (by simp; omega), dif_pos (by simp; omega)]
    rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega)]
    simp [same]
  · rw [dif_neg (by simp; omega), dif_neg (by simp; omega)]
    simp [same]

/-- **Renaming a block's restrictions by an order is reading it back at the reordered names.** -/
theorem envAssignment_permute {names : List Name} {order : List Nat} (isOrder : IsOrder names.length order)
    (env : List Name) (index : Nat) :
    envAssignment (names.reverse ++ env) (Prenex.permute names.length order index) =
      envAssignment ((reorder names order).reverse ++ env) index := by
  have orderLength := isOrder.length
  by_cases inside : index < names.length
  · have image := permute_lt isOrder inside
    have lhs := envAssignment_append_lt (front := names.reverse) (back := env)
      (index := Prenex.permute names.length order index) (by simpa using image)
    have rhs := envAssignment_append_lt (front := (reorder names order).reverse) (back := env) (index := index)
      (by simp [reorder, orderLength, inside])
    rw [lhs, rhs, permute_of_lt orderLength inside]
    simp only [reorder, List.reverse_reverse]
    congr 1
    rw [List.getD_eq_getElem (order.map fun index => names.reverse.getD index "") "" (by simp; omega),
      List.getElem_map]
  · rw [permute_of_ge order inside]
    exact envAssignment_append_ge (by simp [reorder, orderLength]) (by simpa using inside)

theorem canonArgument_name (canonical : Pattern → Pattern) {channel : Pattern} (named : isName channel = true) :
    canonArgument canonical channel = channel := by
  cases channel <;> simp_all [isName, canonArgument]

theorem canonArgument_lambda (canonical : Pattern → Pattern) (binder : Option String) (body : Pattern) :
    canonArgument canonical (.lambda binder body) = .lambda binder (canonical body) := rfl

/-! ## The canonical form read back -/

/-- **The canonical form of a named pattern reads back congruent to the pattern**, and the canonical parts of a
guard to the guard. -/
theorem canon_reads (avoid : Finset Name) : ∀ (fuel : Nat),
    (∀ {pattern : Pattern} (env : List Name), Readable avoid env.length pattern →
      Readable avoid env.length (canonWith piBlock fuel pattern) ∧
        Congruent (readBack avoid env (canonWith piBlock fuel pattern)) (readBack avoid env pattern)) ∧
    (∀ {component : Pattern} (env : List Name), isGuard component = true → Readable avoid env.length component →
      isGuard (canonComponentWith piBlock fuel component) = true ∧
        Readable avoid env.length (canonComponentWith piBlock fuel component) ∧
          Congruent (readBack avoid env (canonComponentWith piBlock fuel component)) (readBack avoid env component))
  | 0 => ⟨fun _ readable => by simpa [canonWith] using ⟨readable, Congruent.refl _⟩,
      fun _ guard readable => by simpa [canonComponentWith] using ⟨guard, readable, Congruent.refl _⟩⟩
  | fuel + 1 => by
      obtain ⟨wholes, parts⟩ := canon_reads avoid fuel
      refine ⟨fun {pattern} env readable => ?_, fun {component} env guard readable => ?_⟩
      · have reads := decompose_reads avoid _ env (Nat.lt_succ_self _) readable
        generalize formIs : decompose piBlock pattern = form at reads
        have nonempty : ((orders (List.range form.count)).map fun order => sortComponents
            (form.components.map fun component =>
              canonComponentWith piBlock fuel (rename (Prenex.permute form.count order) component))) ≠ [] := by
          simpa using orders_ne_nil (List.range form.count)
        obtain ⟨order, orderMember, leastIs⟩ := List.mem_map.mp (least_mem nonempty)
        have isOrder : IsOrder form.count order := orders_perm _ order orderMember
        have canonIs : canonWith piBlock (fuel + 1) pattern = Prenex.toPattern piBlock ⟨form.count, sortComponents
            (form.components.map fun component =>
              canonComponentWith piBlock fuel (rename (Prenex.permute form.count order) component))⟩ := by
          simp only [canonWith, formIs]
          rw [leastIs]
        rw [canonIs]
        -- each renamed component, and its canonical parts
        have renamedFacts : ∀ component ∈ form.components,
            isGuard (rename (Prenex.permute form.count order) component) = true ∧
              Readable avoid (env.length + form.count) (rename (Prenex.permute form.count order) component) :=
          fun component member => ⟨isGuard_rename _ (reads.guards component member),
            (reads.readable component member).rename _ fun index free => by
              have below := free.lt_of_scoped (reads.readable component member).inScope
              by_cases inside : index < form.count
              · have := permute_lt isOrder inside
                omega
              · rw [permute_of_ge order inside]
                exact below⟩
        set names := freshNames (avoid ∪ env.toFinset) form.count with namesIs
        have namesLength : names.length = form.count := freshNames_length _ _
        have namesNodup : names.Nodup := freshNames_nodup _ _
        have namesFresh : ∀ name ∈ names, name ∉ avoid ∧ name ∉ env := fun name member => by
          have outside := freshNames_fresh form.count member
          exact ⟨fun inside => outside (Finset.mem_union_left _ inside),
            fun inside => outside (Finset.mem_union_right _ (List.mem_toFinset.mpr inside))⟩
        have partFacts : ∀ component ∈ form.components,
            let renamed := rename (Prenex.permute form.count order) component
            isGuard (canonComponentWith piBlock fuel renamed) = true ∧
              Readable avoid (env.length + form.count) (canonComponentWith piBlock fuel renamed) ∧
                Congruent (readBack avoid (names.reverse ++ env) (canonComponentWith piBlock fuel renamed))
                  (readBack avoid (names.reverse ++ env) renamed) := fun component member => by
          have facts := renamedFacts component member
          have inner := parts (names.reverse ++ env) facts.1
            (facts.2.depth (by rw [List.length_append, List.length_reverse, namesLength]; omega))
          exact ⟨inner.1, inner.2.1.depth (by rw [List.length_append, List.length_reverse, namesLength]; omega),
            inner.2.2⟩
        have sortedReadable : ∀ component ∈ sortComponents (form.components.map fun component =>
            canonComponentWith piBlock fuel (rename (Prenex.permute form.count order) component)),
            Readable avoid (env.length + form.count) component := fun component member => by
          obtain ⟨original, originalMember, rfl⟩ :=
            List.mem_map.mp ((List.perm_insertionSort _ _).mem_iff.mp member)
          exact (partFacts original originalMember).2.1
        refine ⟨Readable.restricts _ (Readable.body sortedReadable), ?_⟩
        have toPatternIs := readBack_toPattern (env := env) names (fun component member =>
          (sortedReadable component member).depth (by rw [namesLength])) namesNodup namesFresh
        rw [namesLength] at toPatternIs
        refine toPatternIs.trans ?_
        refine (nuList_congruent names (parList_perm ((List.perm_insertionSort _ _).map _))).trans ?_
        have isOrder' : IsOrder names.length order := namesLength ▸ isOrder
        refine (nuList_congruent names (parList_forall₂ (?_ : List.Forall₂ Congruent _
          (form.components.map (readBack avoid ((reorder names order).reverse ++ env)))))).trans ?_
        · rw [List.map_map]
          refine forall₂_map_map fun component member => ?_
          rw [Function.comp_apply]
          refine (partFacts component member).2.2.trans ?_
          refine readBack_rename _ ((reads.readable component member).depth (by
            rw [List.length_append, List.length_reverse,
              show (reorder names order).length = names.length by simp [reorder, isOrder'.length], namesLength]
            omega))
            (fun index free => ?_) (fun index free => ?_)
          · have facts := (renamedFacts component member).2
            have below := free.lt_of_scoped (reads.readable component member).inScope
            simp only [List.length_append, List.length_reverse, namesLength]
            by_cases inside : index < form.count
            · have := permute_lt isOrder inside
              omega
            · rw [permute_of_ge order inside]
              omega
          · have permuted := envAssignment_permute isOrder' env index
            rw [namesLength] at permuted
            exact permuted
        refine (nuList_perm (reorder_perm isOrder').symm _).trans ?_
        refine (reads.reads (reorder names order) (by simp [reorder, isOrder'.length, namesLength])
          ((reorder_perm isOrder').nodup_iff.mpr namesNodup)
          (fun name member => namesFresh name ((reorder_perm isOrder').mem_iff.mp member))).symm
      · rcases guard_cases guard with ⟨channel, binder, body, rfl⟩ | ⟨channel, binder, body, rfl⟩ |
          ⟨channel, datum, rfl⟩
        all_goals have named := readable.named
        all_goals simp only [Named, Bool.and_eq_true] at named
        · have channelNamed := named.1
          have bodyReadable : ∀ name : Name, Readable avoid (name :: env).length body := fun _ =>
            ⟨named.2, by simpa using scoped_lambda (scoped_binary readable.inScope).2,
              avoided_lambda (avoided_binary readable.avoided).2⟩
          have inner := fun name => wholes (name :: env) (bodyReadable name)
          simp only [canonComponentWith, List.not_mem_nil, ↓reduceIte, List.map_cons, List.map_nil, canonArgument_name _ channelNamed,
            canonArgument_lambda]
          refine ⟨by simp [isGuard], ⟨by simp [Named, channelNamed, (inner "").1.named], ?_, ?_⟩, ?_⟩
          · simp only [Pattern.isWellScopedAt, Pattern.isWellScopedListAt, Bool.and_eq_true]
            exact ⟨(scoped_binary readable.inScope).1, by simpa using (inner "").1.inScope, trivial⟩
          · intro name free
            simp only [freeVars, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append] at free
            rcases free with here | there
            · exact (avoided_binary readable.avoided).1 name here
            · exact (inner "").1.avoided name there
          · simp only [readBack]
            exact Congruent.input _ _ (inner _).2
        · -- a server, the replication of an input: its input read canonically two levels of fuel down
          have channelNamed := named.1
          have inputScoped := scoped_unary readable.inScope
          have inputAvoided := avoided_unary readable.avoided
          have inputAtom : decompose piBlock (.apply "PiInp" [channel, .lambda binder body]) =
              Prenex.atom (.apply "PiInp" [channel, .lambda binder body]) := by
            apply decompose_atom
            · simp
            · intro binder' body' equal
              simp at equal
            · intro elements equal
              simp at equal
            · intro label argument _ listed
              simp at listed
          cases fuel with
          | zero =>
              simp only [canonComponentWith, List.not_mem_nil, ↓reduceIte, List.map_cons, List.map_nil, canonArgument,
                canonWith]
              exact ⟨guard, readable, Congruent.refl _⟩
          | succ fuel =>
              cases fuel with
              | zero =>
                  simp only [canonComponentWith, List.not_mem_nil, ↓reduceIte, List.map_cons, List.map_nil, canonArgument]
                  rw [canonWith_atom (block := piBlock) 0 inputAtom]
                  simp only [canonComponentWith]
                  exact ⟨guard, readable, Congruent.refl _⟩
              | succ fuel =>
                  obtain ⟨wholesBody, -⟩ := canon_reads avoid fuel
                  have bodyReadable : ∀ name : Name, Readable avoid (name :: env).length body := fun _ =>
                    ⟨named.2, by simpa using scoped_lambda (scoped_binary inputScoped).2,
                      avoided_lambda (avoided_binary inputAvoided).2⟩
                  have inner := fun name => wholesBody (name :: env) (bodyReadable name)
                  simp only [canonComponentWith, List.not_mem_nil, ↓reduceIte, List.map_cons, List.map_nil, canonArgument]
                  rw [canonWith_atom (block := piBlock) (fuel + 1) inputAtom]
                  simp only [canonComponentWith, List.not_mem_nil, ↓reduceIte, List.map_cons, List.map_nil,
                    canonArgument_name _ channelNamed, canonArgument_lambda]
                  refine ⟨by simp [isGuard], ⟨by simp [Named, channelNamed, (inner "").1.named], ?_, ?_⟩, ?_⟩
                  · simp only [Pattern.isWellScopedAt, Pattern.isWellScopedListAt, Bool.and_eq_true, Bool.and_true]
                    exact ⟨(scoped_binary inputScoped).1, by simpa using (inner "").1.inScope⟩
                  · intro name free
                    simp only [freeVars, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append] at free
                    rcases free with here | there
                    · exact (avoided_binary inputAvoided).1 name here
                    · exact (inner "").1.avoided name there
                  · simp only [readBack]
                    exact Congruent.replicate _ _ (inner _).2
        · simp only [canonComponentWith, List.not_mem_nil, ↓reduceIte, List.map_cons, List.map_nil,
            canonArgument_name _ named.1, canonArgument_name _ named.2]
          exact ⟨by simp [isGuard], ⟨readable.named, readable.inScope, readable.avoided⟩,
            Congruent.refl _⟩

/-- **A named pattern's canonical form reads back congruent to it.** -/
theorem readBack_canon {avoid : Finset Name} {env : List Name} {pattern : Pattern}
    (readable : Readable avoid env.length pattern) :
    Readable avoid env.length (canon piBlock pattern) ∧
      Congruent (readBack avoid env (canon piBlock pattern)) (readBack avoid env pattern) :=
  (canon_reads avoid _).1 env readable

/-! ## Reading back a translation -/

open Mettapedia.OSLF.MeTTaIL.Substitution (closeFVar)
open Mettapedia.Languages.ProcessCalculi.PiCalculus.PiCalcInstance (piToPattern piPar piPar_components
  piComponents freeVars_piToPattern)

theorem isName_close (name : String) (level : Nat) {channel : Pattern} (named : isName channel = true) :
    isName (closeFVar level name channel) = true := by
  cases channel with
  | fvar other => by_cases same : other = name <;> simp [closeFVar, same, isName]
  | bvar => simp [closeFVar, isName]
  | _ => simp [isName] at named

theorem close_piParList (name : String) (level : Nat) : ∀ patterns : List Pattern,
    closeFVar level name (piParList patterns) = piParList (patterns.map (closeFVar level name))
  | [] => by simp [piParList, closeFVar]
  | first :: rest => by simp [piParList, close_piPar, close_piParList name level rest]

/-- **Closing a name commutes with the normal form**, and keeps a pattern named. -/
theorem normal_close (name : String) : ∀ (size : Nat) {pattern : Pattern} (level : Nat), sizeOf pattern < size →
    Named pattern = true →
      Named (closeFVar level name pattern) = true ∧
        normal (closeFVar level name pattern) = closeFVar level name (normal pattern)
  | 0, _, _, small, _ => absurd small (Nat.not_lt_zero _)
  | size + 1, pattern, level, small, named => by
      rcases named_cases named with rfl | ⟨elements, rfl, elementsNamed⟩ | ⟨binder, body, rfl, bodyNamed⟩ |
        ⟨channel, binder, body, rfl, channelNamed, bodyNamed⟩ | ⟨channel, binder, body, rfl, channelNamed, bodyNamed⟩ |
        ⟨channel, datum, rfl, channelNamed, datumNamed⟩
      · simp [closeFVar, normal, Named]
      · have each : ∀ element ∈ elements, Named (closeFVar level name element) = true ∧
            normal (closeFVar level name element) = closeFVar level name (normal element) :=
          fun element member => normal_close name size level (by
            have := List.sizeOf_lt_of_mem member
            simp only [Pattern.collection.sizeOf_spec] at small
            omega) (namedList_iff.mp elementsNamed element member)
        simp only [closeFVar, normal, normalList_eq_map, Named]
        refine ⟨namedList_iff.mpr fun element member => ?_, ?_⟩
        · obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
          exact (each original originalMember).1
        · rw [close_piParList, List.map_map, List.map_map]
          congr 1
          exact List.map_congr_left fun element member => (each element member).2
      · have inner := normal_close name size (level + 1) (by
          simp only [Pattern.apply.sizeOf_spec, List.cons.sizeOf_spec, Pattern.lambda.sizeOf_spec] at small
          omega) bodyNamed
        simp only [closeFVar, List.map_cons, List.map_nil, normal, Named]
        exact ⟨inner.1, by rw [inner.2]⟩
      · have inner := normal_close name size (level + 1) (by
          simp only [Pattern.apply.sizeOf_spec, List.cons.sizeOf_spec, Pattern.lambda.sizeOf_spec] at small
          omega) bodyNamed
        simp only [closeFVar, List.map_cons, List.map_nil, normal, Named, Bool.and_eq_true]
        exact ⟨⟨isName_close name level channelNamed, inner.1⟩, by rw [inner.2]⟩
      · have inner := normal_close name size (level + 1) (by
          simp only [Pattern.apply.sizeOf_spec, List.cons.sizeOf_spec, Pattern.lambda.sizeOf_spec] at small
          omega) bodyNamed
        simp only [closeFVar, List.map_cons, List.map_nil, normal, Named, Bool.and_eq_true]
        exact ⟨⟨isName_close name level channelNamed, inner.1⟩, by rw [inner.2]⟩
      · simp only [closeFVar, List.map_cons, List.map_nil, normal, Named, Bool.and_eq_true]
        exact ⟨⟨isName_close name level channelNamed, isName_close name level datumNamed⟩, trivial⟩

/-- **A translation is named.** -/
theorem named_piToPattern : ∀ process : Process, Named (piToPattern process) = true
  | .nil => rfl
  | .par first second => named_piPar (named_piToPattern first) (named_piToPattern second)
  | .input x y body => by
      simp [piToPattern, Named, isName, (normal_close y _ 0 (Nat.lt_succ_self _) (named_piToPattern body)).1]
  | .output x z => rfl
  | .nu x body => by
      simp [piToPattern, Named, (normal_close x _ 0 (Nat.lt_succ_self _) (named_piToPattern body)).1]
  | .replicate x y body => by
      simp [piToPattern, Named, isName, (normal_close y _ 0 (Nat.lt_succ_self _) (named_piToPattern body)).1]

mutual
  /-- **A process flattened**: parallel composition nested as a list, restrictions and prefixes kept. Its translation
  is the normal form of the process's translation (`normal_piToPattern`). -/
  def flatten : Process → Process
    | .nil => .nil
    | .par first second => parList (flattenParts first ++ flattenParts second)
    | .input x y body => .input x y (flatten body)
    | .output x z => .output x z
    | .nu x body => .nu x (flatten body)
    | .replicate x y body => .replicate x y (flatten body)

  /-- The parallel components of a process, flattened. -/
  def flattenParts : Process → List Process
    | .par first second => flattenParts first ++ flattenParts second
    | .nil => [.nil]
    | .input x y body => [.input x y (flatten body)]
    | .output x z => [.output x z]
    | .nu x body => [.nu x (flatten body)]
    | .replicate x y body => [.replicate x y (flatten body)]
end

theorem normal_piToPattern : ∀ process : Process,
    normal (piToPattern process) = piToPattern (flatten process) ∧
      (piComponents (piToPattern process)).map normal = (flattenParts process).map piToPattern
  | .nil => ⟨rfl, rfl⟩
  | .par first second => by
      obtain ⟨_, firstParts⟩ := normal_piToPattern first
      obtain ⟨_, secondParts⟩ := normal_piToPattern second
      have bagIs : piToPattern (.par first second) = .collection .hashBag
          (piComponents (piToPattern first) ++ piComponents (piToPattern second)) none := by
        rw [piToPattern, piPar_components]
      have components : (piComponents (piToPattern first) ++ piComponents (piToPattern second)).map normal =
          (flattenParts first ++ flattenParts second).map piToPattern := by
        rw [List.map_append, firstParts, secondParts, List.map_append]
      refine ⟨?_, ?_⟩
      · rw [bagIs]
        simp only [normal, normalList_eq_map]
        rw [components]
        simp only [flatten]
        rw [Mettapedia.Languages.ProcessCalculi.PiCalculus.PrenexForm.piToPattern_parList]
      · rw [bagIs]
        exact components
  | .input x y body => by
      obtain ⟨inner, _⟩ := normal_piToPattern body
      have closed := (normal_close y _ 0 (Nat.lt_succ_self _) (named_piToPattern body)).2
      simp [piToPattern, normal, flatten, flattenParts, piComponents, closed, inner]
  | .output x z => ⟨rfl, rfl⟩
  | .nu x body => by
      obtain ⟨inner, _⟩ := normal_piToPattern body
      have closed := (normal_close x _ 0 (Nat.lt_succ_self _) (named_piToPattern body)).2
      simp [piToPattern, normal, flatten, flattenParts, piComponents, closed, inner]
  | .replicate x y body => by
      obtain ⟨inner, _⟩ := normal_piToPattern body
      have closed := (normal_close y _ 0 (Nat.lt_succ_self _) (named_piToPattern body)).2
      simp [piToPattern, normal, flatten, flattenParts, piComponents, closed, inner]

theorem flatten_congruent : ∀ process : Process,
    Congruent (flatten process) process ∧ Congruent (parList (flattenParts process)) process
  | .nil => ⟨Congruent.refl _, Congruent.nilRight _⟩
  | .par first second => by
      have both := (parList_append (flattenParts first) (flattenParts second)).trans
        (Congruent.par (flatten_congruent first).2 (flatten_congruent second).2)
      exact ⟨by simpa [flatten] using both, by simpa [flattenParts] using both⟩
  | .input x y body =>
      ⟨Congruent.input x y (flatten_congruent body).1,
        (Congruent.nilRight _).trans (Congruent.input x y (flatten_congruent body).1)⟩
  | .output x z => ⟨Congruent.refl _, Congruent.nilRight _⟩
  | .nu x body =>
      ⟨Congruent.nu x (flatten_congruent body).1,
        (Congruent.nilRight _).trans (Congruent.nu x (flatten_congruent body).1)⟩
  | .replicate x y body =>
      ⟨Congruent.replicate x y (flatten_congruent body).1,
        (Congruent.nilRight _).trans (Congruent.replicate x y (flatten_congruent body).1)⟩

theorem openWith_nil (pattern : Pattern) : openWith [] pattern = pattern := by
  have identity : envAssignment [] = fun index => .bvar (id index) := by
    funext index
    simp [envAssignment]
  rw [openWith, identity]
  exact rename_id pattern

/-- **A translation is readable**, its free names avoided. -/
theorem readable_piToPattern {avoid : Finset Name} {process : Process} (avoided : process.freeNames ⊆ avoid) :
    Readable avoid 0 (piToPattern process) :=
  ⟨named_piToPattern process, piToPattern_scoped process,
    fun name free => avoided ((freeVars_piToPattern process name).mp free)⟩

/-- **Reading back a translation gives a congruent process.** -/
theorem readBack_piToPattern {avoid : Finset Name} {process : Process} (avoided : process.freeNames ⊆ avoid) :
    Congruent (readBack avoid [] (piToPattern process)) process := by
  refine (congruent_of_piToPattern_eq _ _ _ le_rfl ?_).trans (flatten_congruent process).1
  rw [(readable_piToPattern avoided).translation, openWith_nil, (normal_piToPattern process).1]

end Mettapedia.Languages.ProcessCalculi.PiCalculus.PrenexForm
