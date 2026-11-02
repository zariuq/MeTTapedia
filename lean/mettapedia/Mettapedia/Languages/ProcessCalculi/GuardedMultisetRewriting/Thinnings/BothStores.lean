import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.SharedSteps
import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.SharedSteps

/-!
# Shifts and thinnings: one semantics, two stores

This is the only module of the thinnings layer that imports the shifts layer
(`GuardedMultisetRewriting.SharedTerms`, `GuardedMultisetRewriting.SharedSteps`). It relates the two stores.

* **A shift is a thinning**: a shifts reference `⟨k, i⟩` stands for its node's tree renamed by the
  thinning that skips `k` innermost variables (`shift_is_thinning`). Shifts are the thinnings of
  the form "skip a prefix"; thinnings also skip variables in the middle of a scope.
* **Common semantics**: both stores stand for binding trees, `SignatureIndexedABT.Term`. Unfolding
  in one and encoding into the other translates a reference and keeps its tree
  (`toThinned_spec`, `toShifted_spec`), and both stores decide alpha-equivalence alike
  (`same_pointer_equality`).
* **One step relation, either store** (`both_stores_step`): from configurations that stand for one
  bag of trees, the shifts store and the thinned store reach exactly the same bags of trees in one
  step. The step law is invariant under any translation of patterns that keeps instantiation and
  variables (`Transfer.step_map_iff`), and the two pattern types translate (`patToThin`). So a
  runtime may keep each space in either store.
* **Measured on the same inputs** (`Measurements`, decided by the kernel): where the two stores'
  costs differ, and by how much, on small examples.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.BothStores

open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting
open Thin

/-! ## A shift is a thinning -/

/-- **A shift on an edge is a thinning**: the shifts reference `⟨k, i⟩` stands for its node's tree
renamed by the thinning that skips `k` innermost variables. -/
theorem shift_is_thinning {Head : Type} {S : SharedTerms.Store Head} (topo : SharedTerms.Topo S)
    (k i : ℕ) : SharedTerms.unfold S ⟨k, i⟩ = rename (dropN k []) (SharedTerms.nodeTree S i) := by
  rw [SharedTerms.unfold_shift topo, lift_zero_eq_rename]

/-! ## Common semantics -/

section Common

variable {Head : Type} [DecidableEq Head]

/-- Translate a shifts reference into a thinned store: unfold it, encode the tree. -/
def toThinned (S : SharedTerms.Store Head) (r : SharedTerms.Ref) (T : Store Head) : Store Head × Ref :=
  encodeR T (SharedTerms.unfold S r)

/-- Translate a thinned reference into a shifts store. -/
def toShifted (T : Store Head) (r : Ref) (S : SharedTerms.Store Head) :
    SharedTerms.Store Head × SharedTerms.Ref :=
  SharedTerms.encode S (unfold T r)

/-- **A shifts reference translates into the thinned store with its tree.** -/
theorem toThinned_spec (S : SharedTerms.Store Head) (r : SharedTerms.Ref) {T : Store Head}
    (canon : Canonical T) :
    T <+: (toThinned S r T).1 ∧ Canonical (toThinned S r T).1 ∧
      CanonRef (toThinned S r T).1 (toThinned S r T).2 ∧
      unfold (toThinned S r T).1 (toThinned S r T).2 = SharedTerms.unfold S r := by
  obtain ⟨grow, canon2, cr, -⟩ := encodeR_spec T canon (SharedTerms.unfold S r)
  exact ⟨grow, canon2, cr, encodeR_unfold canon _⟩

/-- **A thinned reference translates into the shifts store with its tree.** -/
theorem toShifted_spec (T : Store Head) (r : Ref) {S : SharedTerms.Store Head}
    (canon : SharedTerms.Canonical S) :
    S <+: (toShifted T r S).1 ∧ SharedTerms.Canonical (toShifted T r S).1 ∧
      SharedTerms.CanonRef (toShifted T r S).1 (toShifted T r S).2 ∧
      SharedTerms.unfold (toShifted T r S).1 (toShifted T r S).2 = unfold T r :=
  SharedTerms.encode_spec S canon (unfold T r)

/-- **Both stores decide alpha-equivalence alike**: two canonical shifts references are equal
exactly when their translations into one thinned store are. -/
theorem same_pointer_equality {S : SharedTerms.Store Head} (cS : SharedTerms.Canonical S)
    {r₁ r₂ : SharedTerms.Ref} (h₁ : SharedTerms.CanonRef S r₁) (h₂ : SharedTerms.CanonRef S r₂)
    {T : Store Head} (cT : Canonical T) :
    r₁ = r₂ ↔ (toThinned S r₁ T).2 = (toThinned S r₂ (toThinned S r₁ T).1).2 := by
  rw [← SharedTerms.unfold_eq_iff cS h₁ h₂]
  exact encodeR_eq_iff cT _ _

end Common

/-! ## The step law is invariant under a translation of patterns -/

namespace Transfer

universe uV uT uP uP'

variable {V : Type uV} {T : Type uT} {P : Type uP} {P' : Type uP'}

/-- A translation of patterns from one term layer to another over the same terms that keeps the
declared theory, instantiation and variables. -/
structure PatMap (L : TermLayer V T P) (L' : TermLayer V T P') (f : P → P') : Prop where
  E : ∀ a b, L'.E a b ↔ L.E a b
  inst : ∀ σ p, L'.inst σ (f p) = L.inst σ p
  vars : ∀ p, L'.vars (f p) = L.vars p

/-- A rule with its patterns translated. -/
def mapRule (f : P → P') (r : Rule V T P) : Rule V T P' where
  take := r.take.map f
  read := r.read.map f
  checks := r.checks.map fun c => ⟨f c.pattern, c.holds⟩
  produce := r.produce.map f

variable {L : TermLayer V T P} {L' : TermLayer V T P'} {f : P → P'}

theorem PatMap.solves (m : PatMap L L' f) (σ : Subst V T) (p : P) (t : T) :
    L'.Solves σ (f p) t ↔ L.Solves σ p t := by
  simp only [TermLayer.Solves, m.inst, m.E]

theorem PatMap.step (m : PatMap L L' f) (σ τ : Subst V T) (p : P) (t : T) :
    L'.Step σ (f p) t τ ↔ L.Step σ p t τ := by
  constructor
  · rintro ⟨e, o, s⟩
    exact ⟨e, fun v nv => o v (by rw [m.vars]; exact nv), (m.solves τ p t).mp s⟩
  · rintro ⟨e, o, s⟩
    exact ⟨e, fun v nv => o v (by rw [← m.vars]; exact nv), (m.solves τ p t).mpr s⟩

theorem PatMap.matchesIn (m : PatMap L L' f) (σ : Subst V T) (p : P) (M : Multiset T) :
    GuardedMultisetRewriting.matchesIn L' σ (f p) M = GuardedMultisetRewriting.matchesIn L σ p M := by
  unfold GuardedMultisetRewriting.matchesIn
  congr 1
  funext t
  have h : L'.Covers σ (f p) t ↔ L.Covers σ p t := exists_congr fun τ => m.step σ τ p t
  simp only [semRegion, decide_eq_true_eq, h]

theorem PatMap.forall₂ (m : PatMap L L' f) (σ : Subst V T) :
    ∀ (ps : List P) (ts : List T),
      List.Forall₂ (L'.Solves σ) (ps.map f) ts ↔ List.Forall₂ (L.Solves σ) ps ts
  | [], ts => by simp
  | p :: ps, [] => by simp
  | p :: ps, t :: ts => by
      simp only [List.map_cons, List.forall₂_cons, m.solves, m.forall₂ σ ps ts]

theorem PatMap.inst_template (m : PatMap L L' f) (σ : Subst V T) :
    ∀ ps : List P, instTemplate L' σ (ps.map f) = instTemplate L σ ps
  | [] => rfl
  | p :: ps => by
      have := m.inst_template σ ps
      simp only [instTemplate] at this ⊢
      rw [List.map_cons, List.mapM_cons, List.mapM_cons, m.inst, this]

/-- **The step law is invariant under the translation**: a rule steps a bag exactly when its
translation does. -/
theorem step_map_iff [DecidableEq V] (m : PatMap L L' f) (r : Rule V T P) (M M' : Multiset T) :
    GuardedMultisetRewriting.Step L' (mapRule f r) M M' ↔ GuardedMultisetRewriting.Step L r M M' := by
  have binds : ∀ σ, BindsOnlyGathers L' (mapRule f r) σ ↔ BindsOnlyGathers L r σ := by
    intro σ
    simp only [BindsOnlyGathers, mapRule, ← List.map_append, List.forall_mem_map, m.vars]
  have matches_ : ∀ σ ps bag, Matches L' σ (ps.map f) bag ↔ Matches L σ ps bag := by
    intro σ ps bag
    simp only [Matches, m.forall₂]
  have reads : ∀ σ ps kept, Reads L' σ (ps.map f) kept ↔ Reads L σ ps kept := by
    intro σ ps kept
    simp only [Reads, m.forall₂]
  have checks : ∀ σ, (∀ c ∈ (mapRule f r).checks, c.holds σ (GuardedMultisetRewriting.matchesIn L' σ c.pattern M)) ↔
      (∀ c ∈ r.checks, c.holds σ (GuardedMultisetRewriting.matchesIn L σ c.pattern M)) := by
    intro σ
    simp only [mapRule, List.forall_mem_map, m.matchesIn]
  simp only [GuardedMultisetRewriting.Step]
  constructor
  · rintro ⟨σ, S, taken, kept, made, hb, hm, hr, hM, hc, hi, hM'⟩
    refine ⟨σ, S, taken, kept, made, (binds σ).mp hb, (matches_ σ _ _).mp hm, (reads σ _ _).mp hr,
      hM, (checks σ).mp hc, ?_, hM'⟩
    exact (m.inst_template σ r.produce).symm.trans hi
  · rintro ⟨σ, S, taken, kept, made, hb, hm, hr, hM, hc, hi, hM'⟩
    refine ⟨σ, S, taken, kept, made, (binds σ).mpr hb, (matches_ σ _ _).mpr hm, (reads σ _ _).mpr hr,
      hM, (checks σ).mpr hc, ?_, hM'⟩
    exact (m.inst_template σ r.produce).trans hi

end Transfer

/-! ## One step relation, either store -/

section OneStep

variable {Head : Type} {V : Type}

mutual

/-- The shifts layer's patterns, read as the thinnings layer's (the same syntax). -/
def patToThin : SharedTerms.TreePat Head V → TreePat Head V
  | .mvar v => .mvar v
  | .idx n => .idx n
  | .node h fs => .node h (patFieldsToThin fs)

def patFieldsToThin : SharedTerms.TreePatFields Head V → TreePatFields Head V
  | .nil => .nil
  | .cons d p rest => .cons d (patToThin p) (patFieldsToThin rest)

end

mutual

theorem inst_patToThin (σ : Subst V (SignatureIndexedABT.Term Head)) :
    ∀ p : SharedTerms.TreePat Head V, (patToThin p).inst σ = p.inst σ
  | .mvar v => by simp [patToThin, TreePat.inst, SharedTerms.TreePat.inst]
  | .idx n => by simp [patToThin, TreePat.inst, SharedTerms.TreePat.inst]
  | .node h fs => by
      simp only [patToThin, TreePat.inst, SharedTerms.TreePat.inst, inst_patFieldsToThin σ fs]

theorem inst_patFieldsToThin (σ : Subst V (SignatureIndexedABT.Term Head)) :
    ∀ fs : SharedTerms.TreePatFields Head V, (patFieldsToThin fs).inst σ = fs.inst σ
  | .nil => by simp [patFieldsToThin, TreePatFields.inst, SharedTerms.TreePatFields.inst]
  | .cons d p rest => by
      simp only [patFieldsToThin, TreePatFields.inst, SharedTerms.TreePatFields.inst,
        inst_patToThin σ p, inst_patFieldsToThin σ rest]
      cases SharedTerms.TreePat.inst σ p <;> cases SharedTerms.TreePatFields.inst σ rest <;> rfl

end

mutual

theorem vars_patToThin [DecidableEq V] :
    ∀ p : SharedTerms.TreePat Head V, (patToThin p).vars = p.vars
  | .mvar v => by simp [patToThin, TreePat.vars, SharedTerms.TreePat.vars]
  | .idx n => by simp [patToThin, TreePat.vars, SharedTerms.TreePat.vars]
  | .node h fs => by simp only [patToThin, TreePat.vars, SharedTerms.TreePat.vars, vars_patFieldsToThin fs]

theorem vars_patFieldsToThin [DecidableEq V] :
    ∀ fs : SharedTerms.TreePatFields Head V, (patFieldsToThin fs).vars = fs.vars
  | .nil => by simp [patFieldsToThin, TreePatFields.vars, SharedTerms.TreePatFields.vars]
  | .cons d p rest => by
      simp only [patFieldsToThin, TreePatFields.vars, SharedTerms.TreePatFields.vars,
        vars_patToThin p, vars_patFieldsToThin rest]

end

/-- The two binding-tree term layers are one, up to the translation of patterns. -/
theorem treeLayer_patMap [DecidableEq V] :
    Transfer.PatMap (SharedTerms.treeLayer (Head := Head) (V := V)) (treeLayer (Head := Head) (V := V))
      patToThin where
  E := fun _ _ => Iff.rfl
  inst := fun σ p => inst_patToThin σ p
  vars := fun p => vars_patToThin p

variable [DecidableEq V] [DecidableEq Head]

/-- **One step relation, either store**: from a shifts configuration and a thinned configuration
that stand for one bag of trees, a rule reaches exactly the same bags of trees in one shared step,
whichever store runs it. -/
theorem both_stores_step (r : Rule V (SignatureIndexedABT.Term Head) (SharedTerms.TreePat Head V))
    {S : SharedTerms.Store Head} {bagS : Multiset SharedTerms.Ref} (cS : SharedTerms.Canonical S)
    (hS : ∀ x ∈ bagS, SharedTerms.CanonRef S x) {T : Store Head} {bagT : Multiset Ref}
    (cT : Canonical T) (hT : ∀ x ∈ bagT, CanonRef T x)
    (same : GuardedMultisetRewriting.trees S bagS = Thinnings.trees T bagT)
    (M' : Multiset (SignatureIndexedABT.Term Head)) :
    (∃ S' bagS', GuardedMultisetRewriting.SharedStep r S bagS S' bagS' ∧ GuardedMultisetRewriting.trees S' bagS' = M') ↔
      (∃ T' bagT', Thinnings.SharedStep (Transfer.mapRule patToThin r) T bagT T' bagT' ∧
        Thinnings.trees T' bagT' = M') := by
  constructor
  · rintro ⟨S', bagS', step, rfl⟩
    have tree := (GuardedMultisetRewriting.sharedStep_sound cS hS step).2.2.2
    rw [same, ← Transfer.step_map_iff treeLayer_patMap] at tree
    exact Thinnings.sharedStep_complete cT hT tree
  · rintro ⟨T', bagT', step, rfl⟩
    have tree := (Thinnings.sharedStep_sound cT hT step).2.2.2
    rw [← same, Transfer.step_map_iff treeLayer_patMap] at tree
    exact GuardedMultisetRewriting.sharedStep_complete cS hS tree

end OneStep

/-! ## Measured on the same inputs -/

namespace Measurements

/-- One head type for both stores: a binder over one field, and application. -/
inductive H where
  | lam
  | app
  deriving DecidableEq, Repr

abbrev Tm := SignatureIndexedABT.Term H

def lam (b : Tm) : Tm := .node .lam (.cons 1 b .nil)

def app (f x : Tm) : Tm := .node .app (.cons 0 f (.cons 0 x .nil))

/-- `λ. (0 1)` and `λ. (0 2)`. -/
def t1 : Tm := lam (app (.idx 0) (.idx 1))
def t2 : Tm := lam (app (.idx 0) (.idx 2))

/-- **Binder construction.** Encoding `λ. (0 1)` then `λ. (0 2)`: the shifts store holds four
nodes, one of them unused (the body `(0 2)` stored before the binder showed it must be lowered);
the thinned store holds three, all used. -/
theorem binder_nodes :
    (SharedTerms.encode (SharedTerms.encode [] t1).1 t2).1.length = 4 ∧
      (encodeR (encodeR [] t1).1 t2).1.length = 3 := by
  decide +kernel

/-- `(x z)` and `(x y)` in the scope `x, y, z`. -/
def xz : Tm := app (.idx 2) (.idx 0)
def xy : Tm := app (.idx 2) (.idx 1)

/-- **Context-free sharing.** `(x z)` and `(x y)` are two nodes in the shifts store (their
variables have different gaps) and one node in the thinned store. -/
theorem context_sharing :
    (SharedTerms.encode [] xz).2.id ≠ (SharedTerms.encode (SharedTerms.encode [] xz).1 xy).2.id ∧
      (encodeR [] xz).2.id = (encodeR (encodeR [] xz).1 xy).2.id := by
  decide +kernel

/-- `(0 1)`, stored in each store. -/
def body : Tm := app (.idx 0) (.idx 1)

/-- **Weakening under a binder.** Lifting `(0 1)` past one bound variable by one (giving
`(0 2)`) allocates one node in the shifts store and no node in the thinned store, where it only
edits the reference; both stand for `(0 2)`. -/
theorem lift_under_binder :
    (SharedTerms.liftRef (SharedTerms.encode [] body).1 1 1 (SharedTerms.encode [] body).2).1.length =
        (SharedTerms.encode [] body).1.length + 1 ∧
      liftRef 1 1 (encodeR [] body).2 = ⟨[true, false, true], (encodeR [] body).2.id⟩ := by
  decide +kernel

/-- `((0 2) 1)` and the value `5`. -/
def openBody : Tm := app (app (.idx 0) (.idx 2)) (.idx 1)

/-- **Opening a variable that a subterm skips.** Opening variable `1` of `((0 2) 1)` with `5`
(giving `((0 1) 6)`): the subterm `(0 2)` does not use variable `1`. The shifts store rebuilds it
as a new node `(0 1)` and makes the new root, two allocations; the thinned store only erases the
variable from the subterm's reference and makes the new root, one allocation. -/
theorem open_allocations :
    (let S := (SharedTerms.encode (SharedTerms.encode [] (.idx 5 : Tm)).1 openBody).1
     let v := (SharedTerms.encode [] (.idx 5 : Tm)).2
     let b := (SharedTerms.encode (SharedTerms.encode [] (.idx 5 : Tm)).1 openBody).2
     (SharedTerms.openRef S 1 v b).1.length - S.length) = 2 ∧
    (let T := (encodeR (encodeR [] (.idx 5 : Tm)).1 openBody).1
     let v := (encodeR [] (.idx 5 : Tm)).2
     let b := (encodeR (encodeR [] (.idx 5 : Tm)).1 openBody).2
     (openRef T 1 v b).1.length - T.length) = 1 := by
  decide +kernel

end Measurements

end Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.BothStores
