import Mettapedia.Logic.TierZero.Kernel2.Walk
import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.Matching

/-!
# The side conditions on thinned references

The kernel's terms live in a canonical thinned store (`Thinnings.Store`): a reference `⟨θ, i⟩` is
node `i`'s co-de-Bruijn term placed in the surrounding scope by the thinning `θ`, and two canonical
references stand for one tree exactly when they are equal (`unfold_eq_iff`). Each side condition
of `Rules` is computed here on references, and proved to compute the tree function on what the
references stand for:

* **local closedness is a length**: a canonical reference stands for a term locally closed at depth
  `d` exactly when its thinning is at most `d` long (`lcR_spec`); no node is visited. Example: the
  reference `⟨[true], v⟩` to the variable node stands for `(bv 0)`, closed at depth `1` and not at
  depth `0`;
* **distinctness of terms is a pointer comparison** (`differR_spec`);
* **occurrence** (`occursR_spec`): a variable occurs exactly where its position is kept by the
  thinning, one bit test (`bit r.thin j`); any other term is looked for by walking the views and
  comparing pointers at each depth (`occursF_spec`);
* **the claim names of a term** (`fvsR_spec`), for `dv`;
* **opening** is `openRef` (`openValR_spec`), which allocates only along paths to the opened
  variable; **abstraction and substitution** are computed on the tree the references stand for and
  stored back (`abstractValR_spec`, `substValR_spec`).

Store-level `abstract` and `subst` that rebuild only the nodes on paths to an occurrence (as
`openRef` does) are not written yet: these two cost the size of the tree, not of the shared DAG.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Kernel2

open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources
open Thin

/-- The kernel's store. -/
abbrev KStore := Store Head

/-! ## Local closedness -/

/-- Locally closed at depth `d`, read off a reference. -/
def lcR (r : Ref) (d : ℕ) : Bool := decide (r.thin.length ≤ d)

/-- **Local closedness is a length.** -/
theorem lcR_spec {St : KStore} (canon : Canonical St) {r : Ref} (hr : CanonRef St r) (d : ℕ) :
    Term.supportedAt d (unfold St r) = lcR r d :=
  Scope.check_spec canon hr d

/-! ## Views: children come first -/

theorem view_children_lt {St : KStore} (canon : Canonical St) {r : Ref} {h : Head}
    {fs : List (ℕ × Ref)} (hv : view St r = .node h fs) : ∀ x ∈ fs, x.2.id < r.id := by
  unfold view at hv
  cases hn : St[r.id]? with
  | none => rw [hn] at hv; cases hv
  | some nd =>
      rw [hn] at hv
      cases nd with
      | var => cases hv
      | node h' n fs' =>
          simp only [View.node.injEq] at hv
          obtain ⟨-, rfl⟩ := hv
          intro x m
          obtain ⟨y, my, rfl⟩ := List.mem_map.mp m
          exact canon.topo r.id _ hn y.2 (by simpa using ⟨y.1, my⟩)

/-! ## Distinctness -/

/-- **Distinct terms are distinct references.** -/
theorem differR_spec {St : KStore} (canon : Canonical St) {x y : Ref} (hx : CanonRef St x)
    (hy : CanonRef St y) : differOk (unfold St x) (unfold St y) = decide (x ≠ y) := by
  unfold differOk
  by_cases e : x = y
  · subst e; simp
  · have ne : unfold St x ≠ unfold St y := fun h => e ((unfold_eq_iff canon hx hy).mp h)
    simp [e, ne]

/-! ## Occurrence -/

theorem any_congr_mem {α : Type} : ∀ {l : List α} {f g : α → Bool}, (∀ c ∈ l, f c = g c) → l.any f = l.any g
  | [], _, _, _ => rfl
  | a :: l, f, g, h => by
      simp only [List.any_cons, h a List.mem_cons_self, any_congr_mem (fun c m => h c (List.mem_cons_of_mem _ m))]

/-- Look for `x`, seen under `d` binders, in what `r` stands for, walking at most `fuel` nodes
deep. -/
def occursF (St : KStore) (x : Ref) : ℕ → ℕ → Ref → Bool
  | 0, _, _ => false
  | fuel + 1, d, r =>
      decide (r = liftRef 0 d x) ||
        match view St r with
        | .node _ fs => fs.any fun c => occursF St x fuel (d + c.1) c.2
        | .idx _ => false

theorem occursFields_fieldsOfRefs (x : Tm) (d : ℕ) (St : KStore) :
    ∀ fs : List (ℕ × Ref),
      occursFields x d (fieldsOfRefs St fs) = fs.any fun c => occursAt x (d + c.1) (unfold St c.2)
  | [] => by simp [fieldsOfRefs, occursFields]
  | (e, c) :: rest => by
      simp [fieldsOfRefs, occursFields, occursFields_fieldsOfRefs x d St rest]

/-- **The occurrence walk computes occurrence on the trees.** -/
theorem occursF_spec {St : KStore} (canon : Canonical St) {x : Ref} (hx : CanonRef St x) :
    ∀ (fuel d : ℕ) (r : Ref), CanonRef St r → r.id < fuel →
      occursF St x fuel d r = occursAt (unfold St x) d (unfold St r)
  | 0, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | fuel + 1, d, r, hr, lt => by
      obtain ⟨cl, ul⟩ := liftRef_spec canon hx.placed 0 d
      have here : decide (r = liftRef 0 d x) = decide (Term.lift 0 d (unfold St x) = unfold St r) := by
        rw [← ul]
        by_cases e : r = liftRef 0 d x
        · subst e; simp
        · have : unfold St (liftRef 0 d x) ≠ unfold St r :=
            fun h => e ((unfold_eq_iff canon cl hr).mp h).symm
          simp [e, this]
      have shows := view_spec canon r
      simp only [occursF]
      rw [here]
      generalize hv : view St r = w at shows
      cases w with
      | idx n =>
          change unfold St r = .idx n at shows
          rw [shows]
          simp [occursAt]
      | node h fs =>
          obtain ⟨kids, eq⟩ := shows
          have below := view_children_lt canon hv
          rw [eq]
          simp only [occursAt, occursFields_fieldsOfRefs]
          congr 1
          refine any_congr_mem fun c m => ?_
          exact occursF_spec canon hx fuel (d + c.1) c.2 (kids c m) (by have := below c m; omega)

/-- **Occurrence on references**: a variable by one bit of the thinning, any other term by the
walk. -/
def occursR (St : KStore) (x r : Ref) : Bool :=
  match view St x with
  | .idx j => bit r.thin j
  | .node _ _ => occursF St x (r.id + 1) 0 r

theorem occursR_spec {St : KStore} (canon : Canonical St) {x r : Ref} (hx : CanonRef St x)
    (hr : CanonRef St r) : occursR St x r = occursIn (unfold St x) (unfold St r) := by
  have shows := view_spec canon x
  unfold occursR
  generalize view St x = w at shows
  cases w with
  | idx j =>
      change unfold St x = .idx j at shows
      rw [shows, occursIn_idx, freeAt_unfold canon hr]
  | node h fs =>
      exact occursF_spec canon hx _ 0 r hr (Nat.lt_succ_self _)

theorem absentR_spec {St : KStore} (canon : Canonical St) {x b : Ref} (hx : CanonRef St x)
    (hb : CanonRef St b) : absentOk (unfold St x) (unfold St b) = !occursR St x b := by
  rw [occursR_spec canon hx hb]; rfl

/-! ## Claim names -/

/-- The claim names in what `r` stands for, walking at most `fuel` nodes deep. -/
def fvsF (St : KStore) : ℕ → Ref → List ℕ
  | 0, _ => []
  | fuel + 1, r =>
      match view St r with
      | .idx _ => []
      | .node h fs =>
          (match h with
            | .fv k => [k]
            | _ => []) ++ (fs.map fun c => fvsF St fuel c.2).flatten

theorem fvsFields_fieldsOfRefs (St : KStore) :
    ∀ fs : List (ℕ × Ref), fvsFields (fieldsOfRefs St fs) = (fs.map fun c => fvsOf (unfold St c.2)).flatten
  | [] => by simp [fieldsOfRefs, fvsFields]
  | (e, c) :: rest => by
      simp [fieldsOfRefs, fvsFields, fvsFields_fieldsOfRefs St rest]

theorem fvsOf_node (h : Head) (fs : Fields Head) :
    fvsOf (.node h fs) = (match h with
      | .fv k => [k]
      | _ => []) ++ fvsFields fs := by
  cases h <;> simp [fvsOf]

theorem fvsF_spec {St : KStore} (canon : Canonical St) :
    ∀ (fuel : ℕ) (r : Ref), CanonRef St r → r.id < fuel → fvsF St fuel r = fvsOf (unfold St r)
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | fuel + 1, r, hr, lt => by
      have shows := view_spec canon r
      simp only [fvsF]
      generalize hv : view St r = w at shows
      cases w with
      | idx n =>
          change unfold St r = .idx n at shows
          rw [shows]; simp [fvsOf]
      | node h fs =>
          obtain ⟨kids, eq⟩ := shows
          have below := view_children_lt canon hv
          simp only []
          rw [eq, fvsOf_node, fvsFields_fieldsOfRefs]
          congr 1
          congr 1
          refine List.map_congr_left fun c m => ?_
          exact fvsF_spec canon fuel c.2 (kids c m) (by have := below c m; omega)

/-- The claim names of a reference. -/
def fvsR (St : KStore) (r : Ref) : List ℕ := fvsF St (r.id + 1) r

theorem fvsR_spec {St : KStore} (canon : Canonical St) {r : Ref} (hr : CanonRef St r) :
    fvsR St r = fvsOf (unfold St r) :=
  fvsF_spec canon _ r hr (Nat.lt_succ_self _)

/-- Distinctness of the frame names of two references. -/
def dvOkR (St : KStore) (fr : Frame) (x y : Ref) : Bool :=
  (fvsR St x).all fun a => (fvsR St y).all fun b =>
    !(decide (a < fr.nvars) && decide (b < fr.nvars)) || (decide (a ≠ b) && fr.declared a b)

theorem dvOkR_spec {St : KStore} (canon : Canonical St) (fr : Frame) {x y : Ref}
    (hx : CanonRef St x) (hy : CanonRef St y) : fr.dvOk (unfold St x) (unfold St y) = dvOkR St fr x y := by
  unfold dvOkR Frame.dvOk
  rw [fvsR_spec canon hx, fvsR_spec canon hy]

/-! ## The computed side conditions -/

/-- What a computed side condition on references promises: the store grows and stays canonical,
the result is canonical and stands for the tree function's result. -/
def ComputesR (St : KStore) (res : Option (KStore × Ref)) (expected : Option Tm) : Prop :=
  (∀ St' v, res = some (St', v) → St <+: St' ∧ Canonical St' ∧ CanonRef St' v) ∧
    res.map (fun p => unfold p.1 p.2) = expected

/-- Opening on references. -/
def openValR (St : KStore) (b v : Ref) : Option (KStore × Ref) :=
  if lcR b 1 && lcR v 0 then some (openRef St 0 v b) else none

theorem openValR_spec {St : KStore} (canon : Canonical St) {b v : Ref} (hb : CanonRef St b)
    (hv : CanonRef St v) : ComputesR St (openValR St b v) (openVal (unfold St b) (unfold St v)) := by
  unfold openValR openVal
  rw [lcR_spec canon hb, lcR_spec canon hv]
  by_cases c : (lcR b 1 && lcR v 0) = true
  · obtain ⟨grow, canon2, cr, eq⟩ := openRef_spec canon hv hb 0
    rw [if_pos c, if_pos c]
    refine ⟨fun St' r h => ?_, ?_⟩
    · simp only [Option.some.injEq] at h
      obtain ⟨e1, e2⟩ := Prod.ext_iff.mp h
      simp only at e1 e2
      subst e1 e2
      exact ⟨grow, canon2, cr⟩
    · simp [eq, openT, Term.instantiate]
  · rw [if_neg c, if_neg c]
    exact ⟨fun St' r h => (by cases h), rfl⟩

/-- Store a tree: encode it into the store. -/
def storeTm (St : KStore) (t : Tm) : KStore × Ref := encodeR St t

theorem storeTm_spec {St : KStore} (canon : Canonical St) (t : Tm) :
    St <+: (storeTm St t).1 ∧ Canonical (storeTm St t).1 ∧ CanonRef (storeTm St t).1 (storeTm St t).2 ∧
      unfold (storeTm St t).1 (storeTm St t).2 = t := by
  obtain ⟨g, c, cr, -⟩ := encodeR_spec St canon t
  exact ⟨g, c, cr, encodeR_unfold canon t⟩

/-- Abstraction on references: computed on the trees, stored back. -/
def abstractValR (St : KStore) (x b : Ref) : Option (KStore × Ref) :=
  if lcR x 0 && lcR b 0 then some (storeTm St (abstractT (unfold St x) (unfold St b))) else none

theorem abstractValR_spec {St : KStore} (canon : Canonical St) {x b : Ref} (hx : CanonRef St x)
    (hb : CanonRef St b) :
    ComputesR St (abstractValR St x b) (abstractVal (unfold St x) (unfold St b)) := by
  unfold abstractValR abstractVal
  rw [lcR_spec canon hx, lcR_spec canon hb]
  by_cases c : (lcR x 0 && lcR b 0) = true
  · obtain ⟨grow, canon2, cr, eq⟩ := storeTm_spec canon (abstractT (unfold St x) (unfold St b))
    rw [if_pos c, if_pos c]
    refine ⟨fun St' r h => ?_, ?_⟩
    · simp only [Option.some.injEq] at h
      obtain ⟨e1, e2⟩ := Prod.ext_iff.mp h
      simp only at e1 e2
      subst e1 e2
      exact ⟨grow, canon2, cr⟩
    · simp [eq]
  · rw [if_neg c, if_neg c]
    exact ⟨fun St' r h => (by cases h), rfl⟩

/-- Substitution on references: computed on the trees, stored back. -/
def substValR (St : KStore) (s b : Ref) : Option (KStore × Ref) :=
  match decodePairs (unfold St s) with
  | some pairs =>
      if pairsClosed pairs && lcR b 0 then some (storeTm St (substT pairs (unfold St b))) else none
  | none => none

theorem substValR_spec {St : KStore} (canon : Canonical St) {s b : Ref} (hb : CanonRef St b) :
    ComputesR St (substValR St s b) (substVal (unfold St s) (unfold St b)) := by
  unfold substValR substVal
  cases decodePairs (unfold St s) with
  | none => exact ⟨fun St' r h => (by cases h), rfl⟩
  | some pairs =>
      simp only
      rw [lcR_spec canon hb]
      by_cases c : (pairsClosed pairs && lcR b 0) = true
      · obtain ⟨grow, canon2, cr, eq⟩ := storeTm_spec canon (substT pairs (unfold St b))
        rw [if_pos c, if_pos c]
        refine ⟨fun St' r h => ?_, ?_⟩
        · simp only [Option.some.injEq] at h
          obtain ⟨e1, e2⟩ := Prod.ext_iff.mp h
          simp only at e1 e2
          subst e1 e2
          exact ⟨grow, canon2, cr⟩
        · simp [eq]
      · rw [if_neg c, if_neg c]
        exact ⟨fun St' r h => (by cases h), rfl⟩

/-! ## Controls -/

namespace Controls

/-- The store holding `(f a (bv 0))` and `a`. -/
def St₀ : KStore := (storeTm (storeTm [] (ex [sym "f", sym "a", .idx 0])).1 (sym "a")).1

def fa0 : Ref := (storeTm [] (ex [sym "f", sym "a", .idx 0])).2

def a₀ : Ref := (storeTm (storeTm [] (ex [sym "f", sym "a", .idx 0])).1 (sym "a")).2

/-- `(f a (bv 0))` is locally closed at depth `1`, not `0`: its thinning is `[true]`. -/
theorem lc_by_length : fa0.thin = [true] ∧ lcR fa0 0 = false ∧ lcR fa0 1 = true := by
  decide +kernel

/-- `a` occurs in `(f a (bv 0))` (a pointer found by the walk); `(bv 0)` occurs (one bit). -/
theorem occurs_examples : occursR St₀ a₀ fa0 = true := by decide +kernel

end Controls

end Mettapedia.Logic.TierZero.Kernel2
