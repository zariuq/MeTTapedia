import Mettapedia.Languages.MeTTa.OSLFCore.Atomspace
import Mettapedia.Languages.MeTTa.Translation.HEPeTTaTranslateStableCommon

/-!
# HE↔PeTTa Operational Bridge Fragments

Small-step/trace bridge relations for the currently theorem-backed sequential
state fragment and the shared atomspace-handle fragment.

The key scope boundary is honest:

- builtin state surface: `new-state`, `get-state`, `change-state!`
- shared atomspace surface: `match`, `get-atoms`, `add-atom`, `remove-atom`
- explicit handles are allowed as long as the handle itself is already in the
  stable/common fragment
- allocation of new spaces is still outside this theorem file

The proof strategy is intentionally lightweight: the executable translators are
already identity on these validated fragments, so translation preservation of
the operational relations reduces to those fixed-point theorems.
-/

namespace Mettapedia.Languages.MeTTa.Translation

open scoped Classical
open Mettapedia.Languages.MeTTa.OSLFCore (Atom Atomspace Bindings)

abbrev StateStore := List (Atom × Atom)
abbrev SpaceStore := List (Atom × Atomspace)

structure StateConfig where
  store : StateStore
  fresh : List Atom
deriving Repr

structure SpaceConfig where
  store : SpaceStore

inductive StateObservation where
  | allocated (ref : Atom)
  | value (val : Atom)
  | effect
deriving Repr

inductive SpaceObservation where
  | effect
  | values (vals : List Atom)
deriving Repr

def lookupState : StateStore → Atom → Option Atom
  | [], _ => none
  | (ref, val) :: rest, target =>
      if ref == target then some val else lookupState rest target

def updateState : StateStore → Atom → Atom → StateStore
  | [], _, _ => []
  | (ref, old) :: rest, target, val =>
      if ref == target then (ref, val) :: rest else (ref, old) :: updateState rest target val

def insertState (store : StateStore) (ref val : Atom) : StateStore :=
  (ref, val) :: store

def lookupSpace : SpaceStore → Atom → Option Atomspace
  | [], _ => none
  | (ref, space) :: rest, target =>
      if ref == target then some space else lookupSpace rest target

def updateSpace : SpaceStore → Atom → Atomspace → SpaceStore
  | [], _, _ => []
  | (ref, space) :: rest, target, newSpace =>
      if ref == target then (ref, newSpace) :: rest else (ref, space) :: updateSpace rest target newSpace

def stateKeys (store : StateStore) : List Atom :=
  store.map Prod.fst

def spaceKeys (store : SpaceStore) : List Atom :=
  store.map Prod.fst

/-- Sequential non-interference for builtin state: no duplicate live state
handles, no duplicate future fresh handles, and no fresh token collides with the
current store. -/
def SequentialStateNonInterference (cfg : StateConfig) : Prop :=
  cfg.fresh.Nodup ∧
    (stateKeys cfg.store).Nodup ∧
    ∀ ref, ref ∈ cfg.fresh → lookupState cfg.store ref = none

/-- Sequential non-interference for named spaces: the current handle map has no
duplicate keys, so reads and updates target a unique space. -/
def SequentialSpaceNonInterference (cfg : SpaceConfig) : Prop :=
  (spaceKeys cfg.store).Nodup

private theorem atom_beq_false_of_ne {a b : Atom} (h : a ≠ b) :
    (a == b) = false := by
  by_cases hbeq : a == b
  · exact False.elim (h (Atom.eq_of_beq_eq_true hbeq))
  · exact Bool.eq_false_iff.mpr hbeq

private theorem lookupState_insert_same (store : StateStore) (ref val : Atom) :
    lookupState (insertState store ref val) ref = some val := by
  simp [lookupState, insertState]

private theorem stateKeys_insert (store : StateStore) (ref val : Atom) :
    stateKeys (insertState store ref val) = ref :: stateKeys store := by
  rfl

private theorem updateState_preserves_keys (store : StateStore) (ref val : Atom) :
    stateKeys (updateState store ref val) = stateKeys store := by
  induction store with
  | nil => rfl
  | cons head rest ih =>
      cases head with
      | mk ref' old =>
          by_cases h : ref' == ref
          · simp [updateState, stateKeys, h]
          · simp [updateState, stateKeys, h]
            exact ih

private theorem lookupState_some_of_mem
    {store : StateStore} {ref val : Atom}
    (hmem : (ref, val) ∈ store) :
    ∃ out, lookupState store ref = some out := by
  induction store with
  | nil =>
      cases hmem
  | cons head rest ih =>
      cases head with
      | mk ref' val' =>
          simp at hmem
          rcases hmem with hEq | htail
          · rcases hEq with ⟨href, hval⟩
            subst href hval
            exact ⟨val, by simp [lookupState]⟩
          · obtain ⟨out, hout⟩ := ih htail
            by_cases hbeq : ref' == ref
            · exact ⟨val', by simp [lookupState, hbeq]⟩
            · exact ⟨out, by simp [lookupState, hbeq, hout]⟩

private theorem lookupState_none_not_mem_keys
    {store : StateStore} {ref : Atom}
    (h : lookupState store ref = none) :
    ref ∉ stateKeys store := by
  intro hmem
  rcases List.mem_map.mp hmem with ⟨pair, hp, hpref⟩
  cases pair with
  | mk ref' val' =>
      have href : ref' = ref := by simpa using hpref
      subst href
      rcases lookupState_some_of_mem hp with ⟨out, hout⟩
      rw [h] at hout
      cases hout

private theorem lookupState_update_same
    (store : StateStore) (ref old val : Atom)
    (h : lookupState store ref = some old) :
    lookupState (updateState store ref val) ref = some val := by
  induction store with
  | nil =>
      simp [lookupState] at h
  | cons head rest ih =>
      cases head with
      | mk ref' cur =>
          by_cases hEq : ref' == ref
          · have href' : ref' = ref := Atom.eq_of_beq_eq_true hEq
            subst href'
            simp [lookupState, updateState]
          · simp [lookupState, updateState, hEq] at h ⊢
            exact ih h

private theorem lookupState_update_of_ne
    (store : StateStore) (target key newVal : Atom)
    (hneq : target ≠ key) :
    lookupState (updateState store target newVal) key = lookupState store key := by
  induction store with
  | nil => rfl
  | cons head rest ih =>
      cases head with
      | mk curRef curVal =>
          by_cases hcur : curRef = target
          · subst hcur
            have hbeqFalse : (curRef == key) = false := atom_beq_false_of_ne hneq
            simp [updateState, lookupState, hbeqFalse]
          · have htarget : (curRef == target) = false := atom_beq_false_of_ne hcur
            simp [updateState, lookupState, htarget, ih]

private theorem sequentialStateNonInterference_newState
    {cfg : StateConfig} {ref init : Atom} {freshTail : List Atom}
    (hcfg : SequentialStateNonInterference cfg)
    (hfresh : cfg.fresh = ref :: freshTail)
    (hmiss : lookupState cfg.store ref = none) :
    SequentialStateNonInterference
      { store := insertState cfg.store ref init, fresh := freshTail } := by
  have hfreshAll : (ref :: freshTail).Nodup := by simpa [hfresh] using hcfg.1
  have htailNodup : freshTail.Nodup := (List.nodup_cons.mp hfreshAll).2
  have hrefNotMem : ref ∉ freshTail := (List.nodup_cons.mp hfreshAll).1
  refine ⟨htailNodup, ?_, ?_⟩
  · rw [stateKeys_insert]
    exact List.nodup_cons.mpr ⟨lookupState_none_not_mem_keys hmiss, hcfg.2.1⟩
  · intro ref' href'
    have hold : lookupState cfg.store ref' = none := hcfg.2.2 ref' (by
      rw [hfresh]
      exact List.mem_cons_of_mem ref href')
    have hneq : ref ≠ ref' := by
      intro hEq
      subst hEq
      exact hrefNotMem href'
    have hbeq : (ref == ref') = false := atom_beq_false_of_ne hneq
    simp [lookupState, insertState, hbeq, hold]

private theorem sequentialStateNonInterference_update
    {cfg : StateConfig} {ref old val : Atom}
    (hcfg : SequentialStateNonInterference cfg)
    (hlookup : lookupState cfg.store ref = some old) :
    SequentialStateNonInterference
      { store := updateState cfg.store ref val, fresh := cfg.fresh } := by
  refine ⟨hcfg.1, ?_, ?_⟩
  · simpa [updateState_preserves_keys] using hcfg.2.1
  · intro ref' href'
    have hnone : lookupState cfg.store ref' = none := hcfg.2.2 ref' href'
    have hneq : ref ≠ ref' := by
      intro hEq
      subst hEq
      rw [hlookup] at hnone
      cases hnone
    rw [lookupState_update_of_ne cfg.store ref ref' val hneq]
    exact hnone

/-- A small-step operational relation for the builtin state fragment.

    Positive example:
    - `(change-state! &counter 1)` updates the unique `&counter` cell and emits
      an abstract `effect` observation.

    Negative example:
    - concurrent aliasing is not modeled here; the relation is intentionally
      sequential and relies on `SequentialStateNonInterference`.
-/
inductive StateStep : StateConfig → Atom → StateConfig → StateObservation → Prop where
  | newState
      (cfg : StateConfig) (init ref : Atom) (freshTail : List Atom)
      (hinit : isStableCommonForm init = true)
      (hfresh : cfg.fresh = ref :: freshTail)
      (hmiss : lookupState cfg.store ref = none) :
      StateStep cfg
        (.expression [.symbol "new-state", init])
        { store := insertState cfg.store ref init, fresh := freshTail }
        (.allocated ref)
  | getState
      (cfg : StateConfig) (stateRef val : Atom)
      (href : isStableCommonForm stateRef = true)
      (hlookup : lookupState cfg.store stateRef = some val) :
      StateStep cfg
        (.expression [.symbol "get-state", stateRef])
        cfg
        (.value val)
  | changeState
      (cfg : StateConfig) (stateRef old val : Atom)
      (href : isStableCommonForm stateRef = true)
      (hval : isStableCommonForm val = true)
      (hlookup : lookupState cfg.store stateRef = some old) :
      StateStep cfg
        (.expression [.symbol "change-state!", stateRef, val])
        { store := updateState cfg.store stateRef val, fresh := cfg.fresh }
        .effect

inductive StateTrace : StateConfig → List Atom → StateConfig → List StateObservation → Prop where
  | nil (cfg : StateConfig) :
      StateTrace cfg [] cfg []
  | cons
      {cfg cfg1 cfg2 : StateConfig}
      {cmd : Atom} {rest : List Atom}
      {obs : StateObservation} {obsRest : List StateObservation}
      (hstep : StateStep cfg cmd cfg1 obs)
      (hrest : StateTrace cfg1 rest cfg2 obsRest) :
      StateTrace cfg (cmd :: rest) cfg2 (obs :: obsRest)

def SharedStateProgram (ops : List Atom) : Prop :=
  ∀ a, a ∈ ops → isSharedStateFragment a = true

private theorem sharedStateProgram_tail
    {x : Atom} {xs : List Atom}
    (hprog : SharedStateProgram (x :: xs)) :
    SharedStateProgram xs := by
  intro a ha
  exact hprog a (by simp [ha])

private theorem translateHEList_id_of_sharedStateProgram
    (ops : List Atom) (s : Nat) (hprog : SharedStateProgram ops) :
    translateHE.translateHEList ops s = (ops, s) := by
  induction ops generalizing s with
  | nil => rfl
  | cons x xs ih =>
      have hx : translateHE x s = (x, s) :=
        translateHE_id_of_sharedStateFragment x s (hprog x (by simp))
      have hxs : translateHE.translateHEList xs s = (xs, s) :=
        ih s (sharedStateProgram_tail hprog)
      simp [translateHE.translateHEList, hx, hxs]

private theorem translatePeTTaList_id_of_sharedStateProgram
    (ops : List Atom) (s : Nat) (hprog : SharedStateProgram ops) :
    translatePeTTa.translatePeTTaList ops s = (ops, s) := by
  induction ops generalizing s with
  | nil => rfl
  | cons x xs ih =>
      have hx : translatePeTTa x s = (x, s) :=
        translatePeTTa_id_of_sharedStateFragment x s (hprog x (by simp))
      have hxs : translatePeTTa.translatePeTTaList xs s = (xs, s) :=
        ih s (sharedStateProgram_tail hprog)
      simp [translatePeTTa.translatePeTTaList, hx, hxs]

theorem stateStep_preserves_nonInterference
    {cfg cfg' : StateConfig} {cmd : Atom} {obs : StateObservation}
    (hcfg : SequentialStateNonInterference cfg)
    (hstep : StateStep cfg cmd cfg' obs) :
    SequentialStateNonInterference cfg' := by
  cases hstep with
  | newState init ref freshTail _ hfresh hmiss =>
      exact sequentialStateNonInterference_newState hcfg hfresh hmiss
  | getState =>
      simpa using hcfg
  | changeState stateRef old val _ _ hlookup =>
      exact sequentialStateNonInterference_update hcfg hlookup

theorem translateHE_preserves_stateStep
    {cfg cfg' : StateConfig} {cmd : Atom} {obs : StateObservation} {s : Nat}
    (hcmd : isSharedStateFragment cmd = true)
    (hstep : StateStep cfg cmd cfg' obs) :
    StateStep cfg (translateHE cmd s).1 cfg' obs := by
  have hfix : translateHE cmd s = (cmd, s) :=
    translateHE_id_of_sharedStateFragment cmd s hcmd
  simpa [hfix] using hstep

theorem translatePeTTa_preserves_stateStep
    {cfg cfg' : StateConfig} {cmd : Atom} {obs : StateObservation} {s : Nat}
    (hcmd : isSharedStateFragment cmd = true)
    (hstep : StateStep cfg cmd cfg' obs) :
    StateStep cfg (translatePeTTa cmd s).1 cfg' obs := by
  have hfix : translatePeTTa cmd s = (cmd, s) :=
    translatePeTTa_id_of_sharedStateFragment cmd s hcmd
  simpa [hfix] using hstep

theorem translateHE_preserves_stateTrace
    {cfg cfg' : StateConfig} {ops : List Atom} {obs : List StateObservation} {s : Nat}
    (hprog : SharedStateProgram ops)
    (htrace : StateTrace cfg ops cfg' obs) :
    StateTrace cfg (translateHE.translateHEList ops s).1 cfg' obs ∧
      (translateHE.translateHEList ops s).2 = s := by
  have hfix := translateHEList_id_of_sharedStateProgram ops s hprog
  constructor
  · simpa [hfix] using htrace
  · simpa using congrArg Prod.snd hfix

theorem translatePeTTa_preserves_stateTrace
    {cfg cfg' : StateConfig} {ops : List Atom} {obs : List StateObservation} {s : Nat}
    (hprog : SharedStateProgram ops)
    (htrace : StateTrace cfg ops cfg' obs) :
    StateTrace cfg (translatePeTTa.translatePeTTaList ops s).1 cfg' obs ∧
      (translatePeTTa.translatePeTTaList ops s).2 = s := by
  have hfix := translatePeTTaList_id_of_sharedStateProgram ops s hprog
  constructor
  · simpa [hfix] using htrace
  · simpa using congrArg Prod.snd hfix

noncomputable def atomspaceSnapshot (space : Atomspace) : List Atom :=
  space.toList

noncomputable def atomspaceMatchOutputs (space : Atomspace) (pat tmpl : Atom) : List Atom :=
  (space.query pat).toList.map fun entry => entry.2.apply tmpl

/-- Fresh handle schedule for space allocation: a list of unused space handles. -/
structure SpaceAllocConfig where
  store : SpaceStore
  fresh : List Atom

/-- Sequential non-interference for space allocation: fresh handles don't
    collide with existing handles. -/
def SequentialSpaceAllocNonInterference (cfg : SpaceAllocConfig) : Prop :=
  cfg.fresh.Nodup ∧
    (spaceKeys cfg.store).Nodup ∧
    ∀ ref, ref ∈ cfg.fresh → lookupSpace cfg.store ref = none

/-- Small-step operational relation for the shared explicit-handle atomspace
fragment, now including `new-space` allocation.

    Positive examples:
    - `(new-space)` allocates a fresh handle bound to an empty space
    - `(add-atom &bag (edge a b))`
    - `(match &self (edge $x $y) ($x $y))`
-/
inductive SpaceStep : SpaceConfig → Atom → SpaceConfig → SpaceObservation → Prop where
  | addAtom
      (cfg : SpaceConfig) (handle payload : Atom) (space : Atomspace)
      (hhandle : isSharedAtomSpaceHandle handle = true)
      (hpayload : isStableCommonForm payload = true)
      (hlookup : lookupSpace cfg.store handle = some space) :
      SpaceStep cfg
        (.expression [.symbol "add-atom", handle, payload])
        { store := updateSpace cfg.store handle (space.add payload) }
        .effect
  | removeAtom
      (cfg : SpaceConfig) (handle payload : Atom) (space : Atomspace)
      (hhandle : isSharedAtomSpaceHandle handle = true)
      (hpayload : isStableCommonForm payload = true)
      (hlookup : lookupSpace cfg.store handle = some space) :
      SpaceStep cfg
        (.expression [.symbol "remove-atom", handle, payload])
        { store := updateSpace cfg.store handle (space.remove payload) }
        .effect
  | getAtoms
      (cfg : SpaceConfig) (handle : Atom) (space : Atomspace)
      (hhandle : isSharedAtomSpaceHandle handle = true)
      (hlookup : lookupSpace cfg.store handle = some space) :
      SpaceStep cfg
        (.expression [.symbol "get-atoms", handle])
        cfg
        (.values (atomspaceSnapshot space))
  | matchSpace
      (cfg : SpaceConfig) (handle pat tmpl : Atom) (space : Atomspace)
      (hhandle : isSharedAtomSpaceHandle handle = true)
      (hpat : isStableCommonForm pat = true)
      (htmpl : isStableCommonForm tmpl = true)
      (hlookup : lookupSpace cfg.store handle = some space) :
      SpaceStep cfg
        (.expression [.symbol "match", handle, pat, tmpl])
        cfg
        (.values (atomspaceMatchOutputs space pat tmpl))

/-- Small-step relation for `new-space` allocation.
    Mirrors `StateStep.newState`: consumes a fresh handle from the schedule,
    inserts an empty space into the store, and emits a handle observation.

    This is a separate relation from `SpaceStep` because allocation requires
    the fresh-handle schedule (`SpaceAllocConfig`), while query/mutation
    operations work on the fixed store (`SpaceConfig`). -/
inductive SpaceAllocStep :
    SpaceAllocConfig → Atom → SpaceAllocConfig → SpaceObservation → Prop where
  | newSpace
      (cfg : SpaceAllocConfig) (ref : Atom) (freshTail : List Atom)
      (hfresh : cfg.fresh = ref :: freshTail)
      (hmiss : lookupSpace cfg.store ref = none) :
      SpaceAllocStep cfg
        (.expression [.symbol "new-space"])
        { store := (ref, Atomspace.empty) :: cfg.store, fresh := freshTail }
        (.values [ref])

private theorem lookupSpace_some_of_mem
    {store : SpaceStore} {ref : Atom} {space : Atomspace}
    (hmem : (ref, space) ∈ store) :
    ∃ out, lookupSpace store ref = some out := by
  induction store with
  | nil => cases hmem
  | cons head rest ih =>
    cases head with
    | mk ref' space' =>
      simp at hmem
      rcases hmem with hEq | htail
      · rcases hEq with ⟨href, _⟩
        subst href
        exact ⟨space', by simp [lookupSpace]⟩
      · obtain ⟨out, hout⟩ := ih htail
        by_cases hbeq : ref' == ref
        · exact ⟨space', by simp [lookupSpace, hbeq]⟩
        · exact ⟨out, by simp [lookupSpace, hbeq, hout]⟩

private theorem lookupSpace_none_not_mem_spaceKeys
    {store : SpaceStore} {ref : Atom}
    (h : lookupSpace store ref = none) :
    ref ∉ spaceKeys store := by
  intro hmem
  rcases List.mem_map.mp hmem with ⟨pair, hp, hpref⟩
  cases pair with
  | mk ref' space' =>
    have href : ref' = ref := by simpa using hpref
    subst href
    rcases lookupSpace_some_of_mem hp with ⟨out, hout⟩
    rw [h] at hout
    cases hout

/-- Allocation preserves non-interference: fresh handles remain disjoint
    from the store after consuming one. Mirrors `sequentialStateNonInterference_newState`. -/
theorem spaceAllocStep_preserves_nonInterference
    {cfg cfg' : SpaceAllocConfig} {cmd : Atom} {obs : SpaceObservation}
    (hcfg : SequentialSpaceAllocNonInterference cfg)
    (hstep : SpaceAllocStep cfg cmd cfg' obs) :
    SequentialSpaceAllocNonInterference cfg' := by
  cases hstep with
  | newSpace ref freshTail hfresh hmiss =>
    have hfreshAll : (ref :: freshTail).Nodup := by simpa [hfresh] using hcfg.1
    have htailNodup : freshTail.Nodup := (List.nodup_cons.mp hfreshAll).2
    have hrefNotMem : ref ∉ freshTail := (List.nodup_cons.mp hfreshAll).1
    refine ⟨htailNodup, ?_, ?_⟩
    · rw [spaceKeys]
      exact List.nodup_cons.mpr ⟨lookupSpace_none_not_mem_spaceKeys hmiss, hcfg.2.1⟩
    · intro ref' href'
      have hold := hcfg.2.2 ref' (by rw [hfresh]; exact List.mem_cons_of_mem ref href')
      have hneq : ref ≠ ref' := by intro hEq; subst hEq; exact hrefNotMem href'
      simp [lookupSpace, atom_beq_false_of_ne hneq, hold]

inductive SpaceTrace : SpaceConfig → List Atom → SpaceConfig → List SpaceObservation → Prop where
  | nil (cfg : SpaceConfig) :
      SpaceTrace cfg [] cfg []
  | cons
      {cfg cfg1 cfg2 : SpaceConfig}
      {cmd : Atom} {rest : List Atom}
      {obs : SpaceObservation} {obsRest : List SpaceObservation}
      (hstep : SpaceStep cfg cmd cfg1 obs)
      (hrest : SpaceTrace cfg1 rest cfg2 obsRest) :
      SpaceTrace cfg (cmd :: rest) cfg2 (obs :: obsRest)

def SharedAtomSpaceProgram (ops : List Atom) : Prop :=
  ∀ a, a ∈ ops → isSharedAtomSpaceFragment a = true

private theorem sharedAtomSpaceProgram_tail
    {x : Atom} {xs : List Atom}
    (hprog : SharedAtomSpaceProgram (x :: xs)) :
    SharedAtomSpaceProgram xs := by
  intro a ha
  exact hprog a (by simp [ha])

private theorem translateHEList_id_of_sharedAtomSpaceProgram
    (ops : List Atom) (s : Nat) (hprog : SharedAtomSpaceProgram ops) :
    translateHE.translateHEList ops s = (ops, s) := by
  induction ops generalizing s with
  | nil => rfl
  | cons x xs ih =>
      have hx : translateHE x s = (x, s) :=
        translateHE_id_of_sharedAtomSpaceFragment x s (hprog x (by simp))
      have hxs : translateHE.translateHEList xs s = (xs, s) :=
        ih s (sharedAtomSpaceProgram_tail hprog)
      simp [translateHE.translateHEList, hx, hxs]

private theorem translatePeTTaList_id_of_sharedAtomSpaceProgram
    (ops : List Atom) (s : Nat) (hprog : SharedAtomSpaceProgram ops) :
    translatePeTTa.translatePeTTaList ops s = (ops, s) := by
  induction ops generalizing s with
  | nil => rfl
  | cons x xs ih =>
      have hx : translatePeTTa x s = (x, s) :=
        translatePeTTa_id_of_sharedAtomSpaceFragment x s (hprog x (by simp))
      have hxs : translatePeTTa.translatePeTTaList xs s = (xs, s) :=
        ih s (sharedAtomSpaceProgram_tail hprog)
      simp [translatePeTTa.translatePeTTaList, hx, hxs]

private theorem updateSpace_preserves_keys (store : SpaceStore) (handle : Atom) (space : Atomspace) :
    spaceKeys (updateSpace store handle space) = spaceKeys store := by
  induction store with
  | nil => rfl
  | cons head rest ih =>
      cases head with
      | mk handle' old =>
          by_cases h : handle' == handle
          · simp [updateSpace, spaceKeys, h]
          · simp [updateSpace, spaceKeys, h]
            exact ih

theorem spaceStep_preserves_nonInterference
    {cfg cfg' : SpaceConfig} {cmd : Atom} {obs : SpaceObservation}
    (hcfg : SequentialSpaceNonInterference cfg)
    (hstep : SpaceStep cfg cmd cfg' obs) :
    SequentialSpaceNonInterference cfg' := by
  cases hstep with
  | addAtom =>
      simpa [SequentialSpaceNonInterference, updateSpace_preserves_keys] using hcfg
  | removeAtom =>
      simpa [SequentialSpaceNonInterference, updateSpace_preserves_keys] using hcfg
  | getAtoms =>
      simpa using hcfg
  | matchSpace =>
      simpa using hcfg

theorem translateHE_preserves_spaceStep
    {cfg cfg' : SpaceConfig} {cmd : Atom} {obs : SpaceObservation} {s : Nat}
    (hcmd : isSharedAtomSpaceFragment cmd = true)
    (hstep : SpaceStep cfg cmd cfg' obs) :
    SpaceStep cfg (translateHE cmd s).1 cfg' obs := by
  have hfix : translateHE cmd s = (cmd, s) :=
    translateHE_id_of_sharedAtomSpaceFragment cmd s hcmd
  simpa [hfix] using hstep

theorem translatePeTTa_preserves_spaceStep
    {cfg cfg' : SpaceConfig} {cmd : Atom} {obs : SpaceObservation} {s : Nat}
    (hcmd : isSharedAtomSpaceFragment cmd = true)
    (hstep : SpaceStep cfg cmd cfg' obs) :
    SpaceStep cfg (translatePeTTa cmd s).1 cfg' obs := by
  have hfix : translatePeTTa cmd s = (cmd, s) :=
    translatePeTTa_id_of_sharedAtomSpaceFragment cmd s hcmd
  simpa [hfix] using hstep

theorem translateHE_preserves_spaceTrace
    {cfg cfg' : SpaceConfig} {ops : List Atom} {obs : List SpaceObservation} {s : Nat}
    (hprog : SharedAtomSpaceProgram ops)
    (htrace : SpaceTrace cfg ops cfg' obs) :
    SpaceTrace cfg (translateHE.translateHEList ops s).1 cfg' obs ∧
      (translateHE.translateHEList ops s).2 = s := by
  have hfix := translateHEList_id_of_sharedAtomSpaceProgram ops s hprog
  constructor
  · simpa [hfix] using htrace
  · simpa using congrArg Prod.snd hfix

theorem translatePeTTa_preserves_spaceTrace
    {cfg cfg' : SpaceConfig} {ops : List Atom} {obs : List SpaceObservation} {s : Nat}
    (hprog : SharedAtomSpaceProgram ops)
    (htrace : SpaceTrace cfg ops cfg' obs) :
    SpaceTrace cfg (translatePeTTa.translatePeTTaList ops s).1 cfg' obs ∧
      (translatePeTTa.translatePeTTaList ops s).2 = s := by
  have hfix := translatePeTTaList_id_of_sharedAtomSpaceProgram ops s hprog
  constructor
  · simpa [hfix] using htrace
  · simpa using congrArg Prod.snd hfix

private theorem sharedAtomSpaceFragment_of_default
    (a : Atom) (h : isDefaultAtomSpaceSharedFragment a = true) :
    isSharedAtomSpaceFragment a = true := by
  have hself : isSharedAtomSpaceHandle (.symbol "&self") = true := by
    simp [isSharedAtomSpaceHandle, isStableCommonForm]
  cases defaultAtomSpaceSharedFragment_has_operational_bridge a h with
  | matchSelf pat tmpl hpat htmpl =>
      simp [isSharedAtomSpaceFragment, hself, hpat, htmpl]
  | getAtomsSelf =>
      simp [isSharedAtomSpaceFragment, hself]
  | addAtomSelf payload hpayload =>
      simp [isSharedAtomSpaceFragment, hself, hpayload]
  | removeAtomSelf payload hpayload =>
      simp [isSharedAtomSpaceFragment, hself, hpayload]

/-- The proof-backed operational reading of `&self` is just the shared-handle
theory specialized to the distinguished default handle. -/
theorem translateHE_preserves_defaultAtomSpaceStep
    {cfg cfg' : SpaceConfig} {cmd : Atom} {obs : SpaceObservation} {s : Nat}
    (hcmd : isDefaultAtomSpaceSharedFragment cmd = true)
    (hstep : SpaceStep cfg cmd cfg' obs) :
    SpaceStep cfg (translateHE cmd s).1 cfg' obs := by
  exact translateHE_preserves_spaceStep
    (sharedAtomSpaceFragment_of_default cmd hcmd) hstep

theorem translatePeTTa_preserves_defaultAtomSpaceStep
    {cfg cfg' : SpaceConfig} {cmd : Atom} {obs : SpaceObservation} {s : Nat}
    (hcmd : isDefaultAtomSpaceSharedFragment cmd = true)
    (hstep : SpaceStep cfg cmd cfg' obs) :
    SpaceStep cfg (translatePeTTa cmd s).1 cfg' obs := by
  exact translatePeTTa_preserves_spaceStep
    (sharedAtomSpaceFragment_of_default cmd hcmd) hstep

end Mettapedia.Languages.MeTTa.Translation
