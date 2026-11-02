import Mettapedia.Logic.TierZero.Kernel2.StoreOps

/-!
# The kernel on thinned shared terms

The executable kernel: every term of a claim lives in one canonical thinned store
(`Thinnings.Store`), every judgment is a reference, and

* matching a rule's premise against a child's theorem is `matchR`: it takes nodes apart with
  `view` and compares the values of a repeated formal by pointer equality; it reads the store and
  never writes it;
* a side condition is computed on references (`StoreOps`): `differ` is a pointer comparison, `lc`
  a length, occurrence of a variable one bit;
* the conclusion is built by `instR`; a node allocates only the nodes its conclusion and its
  computed side conditions need;
* a node cites a theorem by its reference, and the root proves the goal when the two references
  are equal: **pointer equality is tree equality**.

**The refinement.** Each store-level function computes the tree-level one on what the references
stand for: `solveKindsR_spec`, `ruleStepR_spec`, `nodeStepR_spec`, `runR_spec`. Hence
`Claim.verdictR_eq_verdict`: the kernel on thinned terms gives every claim the verdict of
`Claim.verdict`, which is `ChildBound.checkCB` on the claim's translation, so
`verdictR_sound` and `verdictR_complete` carry `ChildBound.checkCB_iff_derivable` and
`Kernel.check_iff_derivable` over to the executable kernel.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Kernel2

open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources
open Mettapedia.Logic.TierZero

/-! ## Premises on references -/

/-- What a premise does, on references. -/
inductive KindR where
  | consume (q : Pat)
  | check (ins : List Pat) (ok : KStore → Frame → List Ref → Bool)
  | compute (r : Pat) (ins : List Pat) (f : KStore → List Ref → Option (KStore × Ref))
  | each (l : Pat) (x : ℕ) (p : Pat)

/-- The kind of each premise, on references. -/
def Premise.kindR : Premise → KindR
  | .judg p => .consume p
  | .given p => .consume (givenPat p)
  | .differ a b => .check [a, b] fun _ _ vs => match vs with
      | [x, y] => decide (x ≠ y)
      | _ => false
  | .absent x b => .check [x, b] fun St _ vs => match vs with
      | [xv, bv] => !occursR St xv bv
      | _ => false
  | .dv x y => .check [x, y] fun St fr vs => match vs with
      | [xv, yv] => dvOkR St fr xv yv
      | _ => false
  | .isOpen r b v => .compute r [b, v] fun St vs => match vs with
      | [bb, vv] => openValR St bb vv
      | _ => none
  | .isAbstract r x b => .compute r [x, b] fun St vs => match vs with
      | [xv, bv] => abstractValR St xv bv
      | _ => none
  | .isSubst r s b => .compute r [s, b] fun St vs => match vs with
      | [sv, bv] => substValR St sv bv
      | _ => none
  | .unionOf u g d => .check [u, g, d] fun St _ vs => match vs.map (unfold St) with
      | [uv, gv, dset] => unionOfOk uv gv dset
      | _ => false
  | .removeOf r x g => .check [r, x, g] fun St _ vs => match vs.map (unfold St) with
      | [rv, xv, gv] => removeOfOk rv xv gv
      | _ => false
  | .singletonOf s x => .check [s, x] fun St _ vs => match vs.map (unfold St) with
      | [sv, xv] => singletonOfOk sv xv
      | _ => false
  | .imageOf h' s h => .check [h', s, h] fun St _ vs => match vs.map (unfold St) with
      | [hv', sv, hv] => imageOfOk hv' sv hv
      | _ => false
  | .atomKind x k => .check [x, k] fun St _ vs => match vs.map (unfold St) with
      | [xv, kv] => atomKindOk xv kv
      | _ => false
  | .each x l p => .each l x p

/-- A premise kind on references computes the premise kind on trees. -/
def KindR.Refines : KindR → Kind → Prop
  | .consume q, .consume q' => q = q'
  | .check ins okR, .check ins' ok =>
      ins = ins' ∧ ∀ (St : KStore) fr vs, Canonical St → (∀ v ∈ vs, CanonRef St v) →
        okR St fr vs = ok fr (vs.map (unfold St))
  | .compute r ins fR, .compute r' ins' f =>
      r = r' ∧ ins = ins' ∧ ∀ (St : KStore) vs, Canonical St → (∀ v ∈ vs, CanonRef St v) →
        ComputesR St (fR St vs) (f (vs.map (unfold St)))
  | .each l x p, .each l' x' p' => l = l' ∧ x = x' ∧ p = p'
  | _, _ => False

theorem none_computes (St : KStore) : ComputesR St none none := by
  exact ⟨fun _ _ h => (by cases h), rfl⟩

/-- **Every premise's store-level kind computes its tree-level kind.** -/
theorem kindR_refines (p : Premise) : p.kindR.Refines p.kind := by
  cases p with
  | judg q => rfl
  | given q => rfl
  | differ a b =>
      simp only [Premise.kindR, Premise.kind, KindR.Refines, true_and]
      intro St fr vs canon hvs
      rcases vs with _ | ⟨x, _ | ⟨y, _ | ⟨z, rest⟩⟩⟩ <;> try rfl
      simp only [List.map_cons, List.map_nil]
      rw [differR_spec canon (hvs x (by simp)) (hvs y (by simp))]
  | absent x b =>
      simp only [Premise.kindR, Premise.kind, KindR.Refines, true_and]
      intro St fr vs canon hvs
      rcases vs with _ | ⟨x, _ | ⟨y, _ | ⟨z, rest⟩⟩⟩ <;> try rfl
      simp only [List.map_cons, List.map_nil]
      rw [absentR_spec canon (hvs x (by simp)) (hvs y (by simp))]
  | dv x y =>
      simp only [Premise.kindR, Premise.kind, KindR.Refines, true_and]
      intro St fr vs canon hvs
      rcases vs with _ | ⟨x, _ | ⟨y, _ | ⟨z, rest⟩⟩⟩ <;> try rfl
      simp only [List.map_cons, List.map_nil]
      rw [dvOkR_spec canon fr (hvs x (by simp)) (hvs y (by simp))]
  | isOpen r b v =>
      simp only [Premise.kindR, Premise.kind, KindR.Refines, true_and]
      intro St vs canon hvs
      rcases vs with _ | ⟨x, _ | ⟨y, _ | ⟨z, rest⟩⟩⟩ <;> try exact none_computes St
      exact openValR_spec canon (hvs x (by simp)) (hvs y (by simp))
  | isAbstract r x b =>
      simp only [Premise.kindR, Premise.kind, KindR.Refines, true_and]
      intro St vs canon hvs
      rcases vs with _ | ⟨x, _ | ⟨y, _ | ⟨z, rest⟩⟩⟩ <;> try exact none_computes St
      exact abstractValR_spec canon (hvs x (by simp)) (hvs y (by simp))
  | isSubst r s b =>
      simp only [Premise.kindR, Premise.kind, KindR.Refines, true_and]
      intro St vs canon hvs
      rcases vs with _ | ⟨x, _ | ⟨y, _ | ⟨z, rest⟩⟩⟩ <;> try exact none_computes St
      exact substValR_spec canon (hvs y (by simp))
  | unionOf u g d => exact ⟨rfl, fun _ _ _ _ _ => rfl⟩
  | removeOf r x g => exact ⟨rfl, fun _ _ _ _ _ => rfl⟩
  | singletonOf s x => exact ⟨rfl, fun _ _ _ _ _ => rfl⟩
  | imageOf h' s h => exact ⟨rfl, fun _ _ _ _ _ => rfl⟩
  | atomKind x k => exact ⟨rfl, fun _ _ _ _ _ => rfl⟩
  | each x l p => exact ⟨rfl, rfl, rfl⟩

/-! ## Instantiating lists of patterns in the store -/

/-- Build the instances of a list of patterns in the store. -/
def instAllR : List Pat → KStore → Subst ℕ Ref → KStore × Option (List Ref)
  | [], St, _ => (St, some [])
  | p :: ps, St, σ =>
      match instR p St σ with
      | (St1, some r) =>
          match instAllR ps St1 σ with
          | (St2, some rs) => (St2, some (r :: rs))
          | (St2, none) => (St2, none)
      | (St1, none) => (St1, none)

theorem instAllR_spec : ∀ (ps : List Pat) (St : KStore) (σ : Subst ℕ Ref),
    Canonical St → CanonSubst St σ →
    St <+: (instAllR ps St σ).1 ∧ Canonical (instAllR ps St σ).1 ∧
      (∀ rs, (instAllR ps St σ).2 = some rs → ∀ r ∈ rs, CanonRef (instAllR ps St σ).1 r) ∧
      (instAllR ps St σ).2.map (List.map (unfold (instAllR ps St σ).1)) = instAll (unfoldSubst St σ) ps
  | [], St, σ, canon, _ => by
      refine ⟨List.prefix_refl St, canon, fun rs h => ?_, ?_⟩
      · simp only [instAllR, Option.some.injEq] at h; subst h; simp
      · simp [instAllR, instAll]
  | p :: ps, St, σ, canon, hσ => by
      obtain ⟨grow1, canon1, cr1, eq1⟩ := instR_spec p St σ canon hσ
      have unfoldL : instAllR (p :: ps) St σ =
          (match instR p St σ with
            | (St1, some r) =>
                match instAllR ps St1 σ with
                | (St2, some rs) => (St2, some (r :: rs))
                | (St2, none) => (St2, none)
            | (St1, none) => (St1, none)) := by
        simp only [instAllR]
      rw [unfoldL]
      generalize instR p St σ = res1 at grow1 canon1 cr1 eq1 ⊢
      obtain ⟨St1, res1⟩ := res1
      dsimp only at grow1 canon1 cr1 eq1 ⊢
      cases res1 with
      | none =>
          dsimp only
          simp only [Option.map_none] at eq1
          refine ⟨grow1, canon1, fun rs h => (by cases h), ?_⟩
          simp [instAll, ← eq1]
      | some r =>
          dsimp only
          simp only [Option.map_some] at eq1
          have hσ1 := hσ.prefix grow1
          obtain ⟨grow2, canon2, kids2, eq2⟩ := instAllR_spec ps St1 σ canon1 hσ1
          rw [unfoldSubst_prefix canon.topo grow1 hσ] at eq2
          generalize instAllR ps St1 σ = res2 at grow2 canon2 kids2 eq2 ⊢
          obtain ⟨St2, res2⟩ := res2
          dsimp only at grow2 canon2 kids2 eq2 ⊢
          cases res2 with
          | none =>
              dsimp only
              simp only [Option.map_none] at eq2
              refine ⟨grow1.trans grow2, canon2, fun rs h => (by cases h), ?_⟩
              simp [instAll, ← eq1, ← eq2]
          | some rs =>
              dsimp only
              simp only [Option.map_some] at eq2
              refine ⟨grow1.trans grow2, canon2, fun rs' h => ?_, ?_⟩
              · simp only [Option.some.injEq] at h
                subst h
                intro x m
                rcases List.mem_cons.mp m with rfl | m
                · exact (cr1 x rfl).prefix grow2
                · exact kids2 rs rfl x m
              · simp only [Option.map_some, instAll, ← eq1, ← eq2, List.map_cons,
                  unfold_prefix canon1.topo grow2 (cr1 r rfl).valid]

/-! ## The matcher on references -/

/-- **The kernel's matching at a node, on references.** -/
def solveKindsR (fr : Frame) : List KindR → KStore → Subst ℕ Ref → List Ref →
    Option (KStore × Subst ℕ Ref)
  | [], St, σ, js => if js = [] then some (St, σ) else none
  | .consume q :: ks, St, σ, js =>
      match js with
      | [] => none
      | j :: rest =>
          match matchR q St σ j with
          | some τ => solveKindsR fr ks St τ rest
          | none => none
  | .check ins ok :: ks, St, σ, js =>
      match instAllR ins St σ with
      | (St1, some vs) => if ok St1 fr vs then solveKindsR fr ks St1 σ js else none
      | (_, none) => none
  | .compute r ins f :: ks, St, σ, js =>
      match instAllR ins St σ with
      | (St1, some vs) =>
          match f St1 vs with
          | some (St2, v) =>
              match matchR r St2 σ v with
              | some τ => solveKindsR fr ks St2 τ js
              | none => none
          | none => none
      | (_, none) => none
  | .each l x p :: ks, St, σ, js =>
      match (l.inst (unfoldSubst St σ)).bind (fun lv => eachJudgments lv x p (unfoldSubst St σ)) with
      | some es =>
          if (js.map (unfold St)).take es.length = es then solveKindsR fr ks St σ (js.drop es.length) else none
      | none => none

/-- What a store-level matching promises. -/
def SolvesR (St : KStore) (res : Option (KStore × Subst ℕ Ref)) (expected : Option (Subst ℕ Tm)) :
    Prop :=
  (∀ St' τ, res = some (St', τ) → St <+: St' ∧ Canonical St' ∧ CanonSubst St' τ) ∧
    res.map (fun p => unfoldSubst p.1 p.2) = expected

theorem SolvesR.lift {St St1 : KStore} (grow : St <+: St1) {res : Option (KStore × Subst ℕ Ref)}
    {expected : Option (Subst ℕ Tm)} (h : SolvesR St1 res expected) : SolvesR St res expected :=
  ⟨fun St' τ e => by obtain ⟨g, c, s⟩ := h.1 St' τ e; exact ⟨grow.trans g, c, s⟩, h.2⟩

theorem map_unfold_prefix {St St' : KStore} (topo : Topo St) (grow : St <+: St') {js : List Ref}
    (hjs : ∀ j ∈ js, CanonRef St j) : js.map (unfold St') = js.map (unfold St) :=
  List.map_congr_left fun j m => unfold_prefix topo grow (hjs j m).valid

/-- **Matching on references computes the matching on trees.** -/
theorem solveKindsR_spec (fr : Frame) :
    ∀ (kRs : List KindR) (ks : List Kind), List.Forall₂ KindR.Refines kRs ks →
    ∀ (St : KStore) (σ : Subst ℕ Ref) (js : List Ref), Canonical St → CanonSubst St σ →
      (∀ j ∈ js, CanonRef St j) →
      SolvesR St (solveKindsR fr kRs St σ js) (solveKinds fr ks (unfoldSubst St σ) (js.map (unfold St)))
  | [], [], _, St, σ, js, canon, hσ, hjs => by
      simp only [solveKindsR, solveKinds]
      by_cases e : js = []
      · subst e
        refine ⟨fun St' τ h => ?_, by simp⟩
        simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨List.prefix_refl _, canon, hσ⟩
      · have e' : js.map (unfold St) ≠ [] := by simpa using e
        rw [if_neg e, if_neg e']
        exact ⟨fun St' τ h => (by cases h), rfl⟩
  | .consume q :: kRs, .consume q' :: ks, all, St, σ, js, canon, hσ, hjs => by
      obtain ⟨hq, rest⟩ := List.forall₂_cons.mp all
      change q = q' at hq
      subst hq
      cases js with
      | nil => exact ⟨fun St' τ h => (by simp [solveKindsR] at h), by simp [solveKindsR, solveKinds]⟩
      | cons j jr =>
          have hj : CanonRef St j := hjs j (by simp)
          obtain ⟨hres, eq⟩ := matchR_spec q St σ j canon hσ hj
          simp only [solveKindsR, solveKinds, List.map_cons]
          cases hm : matchR q St σ j with
          | none =>
              rw [hm] at eq
              simp only [Option.map_none] at eq
              rw [← eq]
              exact ⟨fun St' τ h => (by cases h), rfl⟩
          | some τ1 =>
              rw [hm] at eq hres
              simp only [Option.map_some] at eq
              rw [← eq]
              exact solveKindsR_spec fr kRs ks rest St τ1 jr canon (hres τ1 rfl)
                fun x m => hjs x (by simp [m])
  | .check insR okR :: kRs, .check ins ok :: ks, all, St, σ, js, canon, hσ, hjs => by
      obtain ⟨⟨hins, hok⟩, rest⟩ := List.forall₂_cons.mp all
      subst hins
      obtain ⟨grow1, canon1, cr1, eq1⟩ := instAllR_spec insR St σ canon hσ
      simp only [solveKindsR, solveKinds]
      generalize instAllR insR St σ = res1 at grow1 canon1 cr1 eq1 ⊢
      obtain ⟨St1, res1⟩ := res1
      dsimp only at grow1 canon1 cr1 eq1 ⊢
      cases res1 with
      | none =>
          simp only [Option.map_none] at eq1
          rw [← eq1]
          exact ⟨fun St' τ h => (by cases h), rfl⟩
      | some vs =>
          simp only [Option.map_some] at eq1
          rw [← eq1]
          dsimp only
          rw [hok St1 fr vs canon1 (cr1 vs rfl)]
          by_cases c : ok fr (vs.map (unfold St1)) = true
          · rw [if_pos c, if_pos c]
            have sub := solveKindsR_spec fr kRs ks rest St1 σ js canon1 (hσ.prefix grow1)
              fun j m => (hjs j m).prefix grow1
            rw [unfoldSubst_prefix canon.topo grow1 hσ, map_unfold_prefix canon.topo grow1 hjs] at sub
            exact sub.lift grow1
          · rw [if_neg c, if_neg c]
            exact ⟨fun St' τ h => (by cases h), rfl⟩
  | .compute rR insR fR :: kRs, .compute r ins f :: ks, all, St, σ, js, canon, hσ, hjs => by
      obtain ⟨⟨hr, hins, hf⟩, rest⟩ := List.forall₂_cons.mp all
      subst hr hins
      obtain ⟨grow1, canon1, cr1, eq1⟩ := instAllR_spec insR St σ canon hσ
      simp only [solveKindsR, solveKinds]
      generalize instAllR insR St σ = res1 at grow1 canon1 cr1 eq1 ⊢
      obtain ⟨St1, res1⟩ := res1
      dsimp only at grow1 canon1 cr1 eq1 ⊢
      cases res1 with
      | none =>
          simp only [Option.map_none] at eq1
          rw [← eq1]
          exact ⟨fun St' τ h => (by cases h), rfl⟩
      | some vs =>
          simp only [Option.map_some] at eq1
          rw [← eq1]
          dsimp only
          obtain ⟨fres, feq⟩ := hf St1 vs canon1 (cr1 vs rfl)
          cases hfv : fR St1 vs with
          | none =>
              rw [hfv] at feq
              simp only [Option.map_none] at feq
              rw [← feq]
              dsimp only
              exact ⟨fun St' τ h => (by cases h), rfl⟩
          | some p =>
              obtain ⟨St2, v⟩ := p
              rw [hfv] at feq
              simp only [Option.map_some] at feq
              rw [← feq]
              dsimp only
              obtain ⟨grow2, canon2, cv⟩ := fres St2 v hfv
              have hσ2 := hσ.prefix (grow1.trans grow2)
              obtain ⟨mres, meq⟩ := matchR_spec rR St2 σ v canon2 hσ2 cv
              rw [unfoldSubst_prefix canon.topo (grow1.trans grow2) hσ] at meq
              cases hm : matchR rR St2 σ v with
              | none =>
                  rw [hm] at meq
                  simp only [Option.map_none] at meq
                  rw [← meq]
                  exact ⟨fun St' τ h => (by cases h), rfl⟩
              | some τ1 =>
                  rw [hm] at meq mres
                  simp only [Option.map_some] at meq
                  rw [← meq]
                  have sub := solveKindsR_spec fr kRs ks rest St2 τ1 js canon2 (mres τ1 rfl)
                    fun j m => (hjs j m).prefix (grow1.trans grow2)
                  rw [map_unfold_prefix canon.topo (grow1.trans grow2) hjs] at sub
                  exact sub.lift (grow1.trans grow2)
  | .each lR xR pR :: kRs, .each l x p :: ks, all, St, σ, js, canon, hσ, hjs => by
      obtain ⟨⟨hl, hx, hp⟩, rest⟩ := List.forall₂_cons.mp all
      subst hl hx hp
      simp only [solveKindsR, solveKinds]
      cases (lR.inst (unfoldSubst St σ)).bind (fun lv => eachJudgments lv xR pR (unfoldSubst St σ)) with
      | none => exact ⟨fun St' τ h => (by cases h), rfl⟩
      | some es =>
          simp only
          by_cases ht : (js.map (unfold St)).take es.length = es
          · rw [if_pos ht, if_pos ht]
            have sub := solveKindsR_spec fr kRs ks rest St σ (js.drop es.length) canon hσ
              fun j m => hjs j (List.mem_of_mem_drop m)
            rw [List.map_drop] at sub
            exact sub
          · rw [if_neg ht, if_neg ht]
            exact ⟨fun St' τ h => (by cases h), rfl⟩
  | .consume _ :: _, .check _ _ :: _, all, _, _, _, _, _, _ => (List.forall₂_cons.mp all).1.elim
  | .consume _ :: _, .each _ _ _ :: _, all, _, _, _, _, _, _ => (List.forall₂_cons.mp all).1.elim
  | .check _ _ :: _, .each _ _ _ :: _, all, _, _, _, _, _, _ => (List.forall₂_cons.mp all).1.elim
  | .compute _ _ _ :: _, .each _ _ _ :: _, all, _, _, _, _, _, _ => (List.forall₂_cons.mp all).1.elim
  | .each _ _ _ :: _, .consume _ :: _, all, _, _, _, _, _, _ => (List.forall₂_cons.mp all).1.elim
  | .each _ _ _ :: _, .check _ _ :: _, all, _, _, _, _, _, _ => (List.forall₂_cons.mp all).1.elim
  | .each _ _ _ :: _, .compute _ _ _ :: _, all, _, _, _, _, _, _ => (List.forall₂_cons.mp all).1.elim
  | .consume _ :: _, .compute _ _ _ :: _, all, _, _, _, _, _, _ => (List.forall₂_cons.mp all).1.elim
  | .check _ _ :: _, .consume _ :: _, all, _, _, _, _, _, _ => (List.forall₂_cons.mp all).1.elim
  | .check _ _ :: _, .compute _ _ _ :: _, all, _, _, _, _, _, _ => (List.forall₂_cons.mp all).1.elim
  | .compute _ _ _ :: _, .consume _ :: _, all, _, _, _, _, _, _ => (List.forall₂_cons.mp all).1.elim
  | .compute _ _ _ :: _, .check _ _ :: _, all, _, _, _, _, _, _ => (List.forall₂_cons.mp all).1.elim
  | [], _ :: _, all, _, _, _, _, _, _ => by cases all
  | _ :: _, [], all, _, _, _, _, _, _ => by cases all

theorem rule_refines (ru : Rule) : List.Forall₂ KindR.Refines (ru.prems.map Premise.kindR) ru.kinds := by
  unfold Rule.kinds
  induction ru.prems with
  | nil => exact .nil
  | cons p ps ih => exact .cons (kindR_refines p) ih

/-! ## The step at a node, on references -/

theorem mapM_range_unfold (St : KStore) (τ : Subst ℕ Ref) :
    ∀ n : ℕ, ((List.range n).mapM τ).map (List.map (unfold St)) = (List.range n).mapM (unfoldSubst St τ)
  | 0 => by simp
  | n + 1 => by
      rw [List.range_succ, List.mapM_append, List.mapM_append, ← mapM_range_unfold St τ n]
      cases (List.range n).mapM τ <;> cases h : τ n <;> simp [unfoldSubst, h]

/-- The conclusion of a rule from its children's theorems, on references. -/
def ruleStepR (fr : Frame) (ru : Rule) (St : KStore) (js : List Ref) : Option (KStore × Ref) :=
  match solveKindsR fr (ru.prems.map Premise.kindR) St (fun _ => none) js with
  | some (St1, τ) =>
      match (List.range ru.nformals).mapM τ with
      | some a =>
          match instR ru.concl St1 (fun v => a[v]?) with
          | (St2, some c) => some (St2, c)
          | (_, none) => none
      | none => none
  | none => none

theorem unfoldSubst_list (St : KStore) (a : List Ref) :
    unfoldSubst St (fun v : ℕ => a[v]?) = substOf (a.map (unfold St)) := by
  funext v; simp [unfoldSubst, substOf]

theorem canonSubst_list {St : KStore} {a : List Ref} (h : ∀ r ∈ a, CanonRef St r) :
    CanonSubst St (fun v : ℕ => a[v]?) := fun _ r e => h r (List.mem_of_getElem? e)

theorem mapM_canon {St : KStore} {τ : Subst ℕ Ref} (hτ : CanonSubst St τ) :
    ∀ {l : List ℕ} {a : List Ref}, l.mapM τ = some a → ∀ r ∈ a, CanonRef St r
  | [], a, h, r, m => by simp at h; subst h; simp at m
  | x :: l, a, h, r, m => by
      simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at h
      cases hx : τ x with
      | none => simp [hx] at h
      | some y =>
          cases hl : l.mapM τ with
          | none => simp [hx, hl] at h
          | some ys =>
              simp only [hx, hl, Option.bind_some, Option.some.injEq] at h
              subst h
              rcases List.mem_cons.mp m with rfl | m
              · exact hτ x r hx
              · exact mapM_canon hτ hl r m

/-- **The step of a rule on references computes it on trees.** -/
theorem ruleStepR_spec (fr : Frame) (ru : Rule) {St : KStore} (canon : Canonical St) {js : List Ref}
    (hjs : ∀ j ∈ js, CanonRef St j) :
    ComputesR St (ruleStepR fr ru St js) (ruleStep fr ru (js.map (unfold St))) := by
  have empty : CanonSubst St (fun _ => none : Subst ℕ Ref) := fun _ _ h => by cases h
  have unfoldEmpty : unfoldSubst St (fun _ => none : Subst ℕ Ref) = emptySubst := by
    funext v; simp [unfoldSubst, emptySubst]
  obtain ⟨sres, seq⟩ := solveKindsR_spec fr _ _ (rule_refines ru) St (fun _ => none) js canon empty hjs
  rw [unfoldEmpty] at seq
  unfold ruleStepR ruleStep
  cases hs : solveKindsR fr (ru.prems.map Premise.kindR) St (fun _ => none) js with
  | none =>
      rw [hs] at seq
      simp only [Option.map_none] at seq
      rw [← seq]
      exact none_computes St
  | some p =>
      obtain ⟨St1, τ⟩ := p
      rw [hs] at seq sres
      simp only [Option.map_some] at seq
      rw [← seq]
      obtain ⟨grow1, canon1, hτ⟩ := sres St1 τ rfl
      dsimp only
      have mm := mapM_range_unfold St1 τ ru.nformals
      cases ha : (List.range ru.nformals).mapM τ with
      | none =>
          rw [ha] at mm
          simp only [Option.map_none] at mm
          rw [← mm]
          exact none_computes St
      | some a =>
          rw [ha] at mm
          simp only [Option.map_some] at mm
          rw [← mm]
          dsimp only
          have ha' := canonSubst_list (mapM_canon hτ ha)
          obtain ⟨grow2, canon2, cr2, eq2⟩ := instR_spec ru.concl St1 (fun v => a[v]?) canon1 ha'
          rw [unfoldSubst_list] at eq2
          generalize instR ru.concl St1 (fun v => a[v]?) = res at grow2 canon2 cr2 eq2 ⊢
          obtain ⟨St2, res⟩ := res
          dsimp only at grow2 canon2 cr2 eq2 ⊢
          cases res with
          | none =>
              simp only [Option.map_none] at eq2
              rw [← eq2]
              exact none_computes St
          | some c =>
              simp only [Option.map_some] at eq2
              rw [← eq2]
              refine ⟨fun St' v h => ?_, rfl⟩
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact ⟨grow1.trans grow2, canon2, cr2 c rfl⟩

variable {R : Type}

/-- The theorem a child names, on references. -/
def lookupR (hyps done : List Ref) : Kid → Option Ref
  | .hyp i => hyps[i]?
  | .node n => done[n]?

theorem lookupR_unfold (St : KStore) (hyps done : List Ref) (k : Kid) :
    (lookupR hyps done k).map (unfold St) = lookupT (hyps.map (unfold St)) (done.map (unfold St)) k := by
  cases k <;> simp [lookupR, lookupT]

theorem lookupR_canon {St : KStore} {hyps done : List Ref} (hh : ∀ r ∈ hyps, CanonRef St r)
    (hd : ∀ r ∈ done, CanonRef St r) {k : Kid} {r : Ref} (h : lookupR hyps done k = some r) :
    CanonRef St r := by
  cases k with
  | hyp i => exact hh r (List.mem_of_getElem? h)
  | node n => exact hd r (List.mem_of_getElem? h)

theorem mapM_map_some {α β γ : Type} (f : α → Option β) (g : β → γ) :
    ∀ l : List α, (l.mapM f).map (List.map g) = l.mapM (fun a => (f a).map g)
  | [] => rfl
  | a :: l => by
      simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def]
      rw [← mapM_map_some f g l]
      cases f a <;> cases l.mapM f <;> simp

theorem mapM_mem {α β : Type} {f : α → Option β} {P : β → Prop} (hf : ∀ a b, f a = some b → P b) :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → ∀ b ∈ l', P b
  | [], l', h, b, m => by simp at h; subst h; simp at m
  | a :: l, l', h, b, m => by
      simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at h
      cases ha : f a with
      | none => simp [ha] at h
      | some x =>
          cases hl : l.mapM f with
          | none => simp [ha, hl] at h
          | some xs =>
              simp only [ha, hl, Option.bind_some, Option.some.injEq] at h
              subst h
              rcases List.mem_cons.mp m with rfl | m
              · exact hf a b ha
              · exact mapM_mem hf hl b m

/-- **The kernel's step at a node, on references.** -/
def nodeStepR (env : Env R) (fr : Frame) (look : Kid → Option Ref) (St : KStore) (r : R)
    (kids : List Kid) : Option (KStore × Ref) :=
  match kids.mapM look, env r with
  | some js, some ru => ruleStepR fr ru St js
  | _, _ => none

theorem nodeStepR_spec (env : Env R) (fr : Frame) {St : KStore} (canon : Canonical St)
    {hyps done : List Ref} (hh : ∀ r ∈ hyps, CanonRef St r) (hd : ∀ r ∈ done, CanonRef St r)
    (r : R) (kids : List Kid) :
    ComputesR St (nodeStepR env fr (lookupR hyps done) St r kids)
      (nodeStep env fr (lookupT (hyps.map (unfold St)) (done.map (unfold St))) r kids) := by
  unfold nodeStepR nodeStep
  have same : kids.mapM (lookupT (hyps.map (unfold St)) (done.map (unfold St))) =
      (kids.mapM (lookupR hyps done)).map (List.map (unfold St)) := by
    rw [mapM_map_some]
    congr 1
    funext k
    rw [lookupR_unfold]
  rw [same]
  cases hk : kids.mapM (lookupR hyps done) with
  | none => exact none_computes St
  | some js =>
      cases env r with
      | none => exact none_computes St
      | some ru =>
          exact ruleStepR_spec fr ru canon (mapM_mem (fun k x h => lookupR_canon hh hd h) hk)

/-! ## The walk in order, on references -/

/-- **The walk in order on references.** -/
def runR (env : Env R) (fr : Frame) (hyps : List Ref) :
    KStore → List Ref → List (R × List Kid) → Option (KStore × List Ref)
  | St, done, [] => some (St, done)
  | St, done, (r, kids) :: rest =>
      match nodeStepR env fr (lookupR hyps done) St r kids with
      | some (St1, c) => runR env fr hyps St1 (done ++ [c]) rest
      | none => none

/-- **The walk on references computes the walk on trees.** -/
theorem runR_spec (env : Env R) (fr : Frame) (hyps : List Ref) :
    ∀ (proof : List (R × List Kid)) (St : KStore) (done : List Ref), Canonical St →
      (∀ r ∈ hyps, CanonRef St r) → (∀ r ∈ done, CanonRef St r) →
      (∀ St' out, runR env fr hyps St done proof = some (St', out) →
          St <+: St' ∧ Canonical St' ∧ ∀ r ∈ out, CanonRef St' r) ∧
        (runR env fr hyps St done proof).map (fun p => p.2.map (unfold p.1)) =
          runT env fr (hyps.map (unfold St)) (done.map (unfold St)) proof
  | [], St, done, canon, hh, hd => by
      refine ⟨fun St' out h => ?_, by simp [runR, runT]⟩
      simp only [runR, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨List.prefix_refl _, canon, hd⟩
  | (r, kids) :: rest, St, done, canon, hh, hd => by
      obtain ⟨nres, neq⟩ := nodeStepR_spec env fr canon hh hd r kids
      simp only [runR, runT]
      cases hn : nodeStepR env fr (lookupR hyps done) St r kids with
      | none =>
          rw [hn] at neq
          simp only [Option.map_none] at neq
          rw [← neq]
          exact ⟨fun St' out h => (by cases h), rfl⟩
      | some p =>
          obtain ⟨St1, c⟩ := p
          rw [hn] at neq
          simp only [Option.map_some] at neq
          rw [← neq]
          obtain ⟨grow1, canon1, cc⟩ := nres St1 c hn
          have hh1 : ∀ x ∈ hyps, CanonRef St1 x := fun x m => (hh x m).prefix grow1
          have hd1 : ∀ x ∈ done ++ [c], CanonRef St1 x := by
            intro x m
            rcases List.mem_append.mp m with m | m
            · exact (hd x m).prefix grow1
            · rw [List.mem_singleton.mp m]; exact cc
          obtain ⟨rres, req⟩ := runR_spec env fr hyps rest St1 (done ++ [c]) canon1 hh1 hd1
          refine ⟨fun St' out h => ?_, ?_⟩
          · obtain ⟨g, cn, co⟩ := rres St' out h
            exact ⟨grow1.trans g, cn, co⟩
          · rw [req, map_unfold_prefix canon.topo grow1 hh, List.map_append,
              map_unfold_prefix canon.topo grow1 hd]
            simp

/-! ## The verdict on a claim, on references -/

namespace Claim

/-- The patterns of the theorems a claim's proof may cite: its judgment hypotheses, its locals,
and `(given T)` for each stored term. -/
def hypPats (c : Claim R) : List Pat :=
  judgPats c.hyps ++ c.locals.map (fun l => pjd l.1 [pv l.2]) ++ c.terms.map (fun x => givenPat x.2)

theorem instAll_append (σ : Subst ℕ Tm) :
    ∀ (ps qs : List Pat), instAll σ (ps ++ qs) = (instAll σ ps).bind fun a => (instAll σ qs).map (a ++ ·)
  | [], qs => by cases h : instAll σ qs <;> simp [instAll, h]
  | p :: ps, qs => by
      simp only [List.cons_append, instAll, instAll_append σ ps qs]
      cases p.inst σ <;> cases instAll σ ps <;> cases instAll σ qs <;> simp

theorem instAll_eq_mapM (σ : Subst ℕ Tm) : ∀ ps : List Pat, instAll σ ps = ps.mapM (·.inst σ)
  | [] => rfl
  | p :: ps => by
      simp only [instAll, List.mapM_cons, Option.bind_eq_bind, Option.pure_def, instAll_eq_mapM σ ps]
      cases p.inst σ <;> cases ps.mapM (·.inst σ) <;> simp

theorem cbHyps_eq (c : Claim R) : c.cbHyps = instAll c.σ c.hypPats := by
  unfold cbHyps hypPats
  rw [instAll_append, instAll_append, instAll_eq_mapM, instAll_eq_mapM, instAll_eq_mapM]
  have hl : (c.locals.map fun l => pjd l.1 [pv l.2]).mapM (·.inst c.σ) = c.locals.mapM c.localJudgment := by
    rw [List.mapM_map]
    congr 1
    funext l
    simp [localJudgment, pjd, pex, pflds, psym, pv, TreePat.inst, TreePatFields.inst, σ, substOf, jd, ex, flds, sym]
    cases c.vals[l.2]? <;> rfl
  have hg : (c.terms.map fun x => givenPat x.2).mapM (·.inst c.σ) =
      c.terms.mapM (fun x => (x.2.inst c.σ).map givenTm) := by
    rw [List.mapM_map]
    congr 1
    funext x
    simp [givenPat, pjd, pex, pflds, psym, TreePat.inst, TreePatFields.inst]
    cases x.2.inst c.σ <;> rfl
  rw [hl, hg]
  simp only [Option.bind_eq_bind, Option.pure_def]
  cases (judgPats c.hyps).mapM (·.inst c.σ) <;> cases c.locals.mapM c.localJudgment <;>
    cases c.terms.mapM (fun x => (x.2.inst c.σ).map givenTm) <;> simp

/-- Store a list of trees. -/
def storeAll : KStore → List Tm → KStore × List Ref
  | St, [] => (St, [])
  | St, t :: ts =>
      let first := storeTm St t
      let rest := storeAll first.1 ts
      (rest.1, first.2 :: rest.2)

theorem storeAll_spec : ∀ (ts : List Tm) (St : KStore), Canonical St →
    St <+: (storeAll St ts).1 ∧ Canonical (storeAll St ts).1 ∧
      (∀ r ∈ (storeAll St ts).2, CanonRef (storeAll St ts).1 r) ∧
      (storeAll St ts).2.map (unfold (storeAll St ts).1) = ts
  | [], St, canon => ⟨List.prefix_refl St, canon, by simp [storeAll], rfl⟩
  | t :: ts, St, canon => by
      obtain ⟨g1, c1, cr1, e1⟩ := storeTm_spec canon t
      obtain ⟨g2, c2, cr2, e2⟩ := storeAll_spec ts (storeTm St t).1 c1
      refine ⟨g1.trans g2, c2, fun r m => ?_, ?_⟩
      · simp only [storeAll, List.mem_cons] at m
        rcases m with rfl | m
        · exact cr1.prefix g2
        · exact cr2 r m
      · simp only [storeAll, List.map_cons, e2, unfold_prefix c1.topo g2 cr1.valid, e1]

/-- **The verdict on a claim, computed on references**: the claim's variables, hypotheses and goal
are stored once, the proof is walked on references, and the root proves the goal when its
reference is the goal's. -/
def verdictR (env : Env R) (c : Claim R) : Bool :=
  c.wellFormed &&
    let made := storeAll [] c.vals
    let σR : Subst ℕ Ref := fun v => made.2[v]?
    match instAllR c.hypPats made.1 σR with
    | (St1, some hs) =>
        match instR c.concl St1 σR with
        | (St2, some g) =>
            match c.translate with
            | some (pf, rt) =>
                match runR env c.frame hs St2 [] pf with
                | some (_, done) => decide (lookupR hs done rt = some g)
                | none => false
            | none => false
        | (_, none) => false
    | (_, none) => false

theorem lookupR_eq_iff {St : KStore} (canon : Canonical St) {hs done : List Ref}
    (hh : ∀ r ∈ hs, CanonRef St r) (hd : ∀ r ∈ done, CanonRef St r) {g : Ref} (hg : CanonRef St g)
    (k : Kid) :
    lookupR hs done k = some g ↔ lookupT (hs.map (unfold St)) (done.map (unfold St)) k = some (unfold St g) := by
  rw [← lookupR_unfold]
  cases e : lookupR hs done k with
  | none => simp
  | some r =>
      have hr := lookupR_canon hh hd e
      simp only [Option.map_some, Option.some.injEq]
      exact (unfold_eq_iff canon hr hg).symm

/-- **The kernel on thinned terms gives every claim the verdict of `Claim.verdict`.** -/
theorem verdictR_eq_verdictT (env : Env R) (c : Claim R) : c.verdictR env = c.verdictT env := by
  unfold verdictR verdictT
  cases hw : c.wellFormed with
  | false => rfl
  | true =>
      simp only [Bool.true_and]
      obtain ⟨g0, c0, cr0, e0⟩ := storeAll_spec c.vals [] canonical_nil
      generalize storeAll [] c.vals = made at g0 c0 cr0 e0 ⊢
      obtain ⟨St0, vs⟩ := made
      dsimp only at g0 c0 cr0 e0 ⊢
      have hσ0 : CanonSubst St0 (fun v => vs[v]?) := canonSubst_list cr0
      have uσ : unfoldSubst St0 (fun v => vs[v]?) = c.σ := by
        rw [unfoldSubst_list, e0]; rfl
      obtain ⟨g1, c1, cr1, e1⟩ := instAllR_spec c.hypPats St0 _ c0 hσ0
      rw [uσ, ← cbHyps_eq] at e1
      generalize instAllR c.hypPats St0 (fun v => vs[v]?) = res1 at g1 c1 cr1 e1 ⊢
      obtain ⟨St1, res1⟩ := res1
      dsimp only at g1 c1 cr1 e1 ⊢
      cases res1 with
      | none => simp only [Option.map_none] at e1; rw [← e1]
      | some hs =>
          simp only [Option.map_some] at e1
          rw [← e1]
          dsimp only
          obtain ⟨g2, c2, cr2, e2⟩ := instR_spec c.concl St1 _ c1 (hσ0.prefix g1)
          rw [unfoldSubst_prefix c0.topo g1 hσ0, uσ] at e2
          change _ = c.goal at e2
          generalize instR c.concl St1 (fun v => vs[v]?) = res2 at g2 c2 cr2 e2 ⊢
          obtain ⟨St2, res2⟩ := res2
          dsimp only at g2 c2 cr2 e2 ⊢
          cases res2 with
          | none => simp only [Option.map_none] at e2; rw [← e2]
          | some g =>
              simp only [Option.map_some] at e2
              rw [← e2]
              dsimp only
              cases c.translate with
              | none => rfl
              | some p =>
                  obtain ⟨pf, rt⟩ := p
                  dsimp only
                  have hh2 : ∀ r ∈ hs, CanonRef St2 r := fun r m => (cr1 hs rfl r m).prefix g2
                  obtain ⟨rres, req⟩ := runR_spec env c.frame hs pf St2 [] c2 hh2 (by simp)
                  rw [map_unfold_prefix c1.topo g2 (cr1 hs rfl)] at req
                  simp only [List.map_nil] at req
                  rw [← req]
                  cases hrun : runR env c.frame hs St2 [] pf with
                  | none => rfl
                  | some q =>
                      obtain ⟨St3, done⟩ := q
                      obtain ⟨g3, c3, cd⟩ := rres St3 done hrun
                      simp only [Option.map_some]
                      have hh3 : ∀ r ∈ hs, CanonRef St3 r := fun r m => (hh2 r m).prefix g3
                      have hg3 : CanonRef St3 g := (cr2 g rfl).prefix g3
                      have iff := lookupR_eq_iff c3 hh3 cd hg3 rt
                      rw [map_unfold_prefix c2.topo g3 hh2, unfold_prefix c2.topo g3 (cr2 g rfl).valid,
                        map_unfold_prefix c1.topo g2 (cr1 hs rfl)] at iff
                      exact decide_eq_decide.mpr iff

/-- **The kernel on thinned terms computes the verdict.** -/
theorem verdictR_eq_verdict (env : Env R) (wf : EnvDetermined env) (c : Claim R) :
    c.verdictR env = c.verdict env wf :=
  (verdictR_eq_verdictT env c).trans (verdictT_eq_verdict env wf c)

end Claim

/-- **Soundness of the kernel on thinned terms.** -/
theorem verdictR_sound {env : Env R} (wf : EnvDetermined env) {c : Claim R}
    (h : c.verdictR env = true) :
    ∃ hs g, c.cbHyps = some hs ∧ c.goal = some g ∧ Derivable (presOf env c.frame) hs g :=
  verdict_sound (wf := wf) (by rw [← Claim.verdictR_eq_verdict env wf]; exact h)

/-- **Completeness of the kernel on thinned terms.** -/
theorem verdictR_complete {env : Env R} (wf : EnvDetermined env) {c : Claim R}
    (ok : c.stmtOk = true) {hs : List Tm} {g : Tm} (hh : c.cbHyps = some hs) (hg : c.goal = some g)
    (d : Derivable (presOf env c.frame) hs g) :
    ∃ (proof : List (CProofNode R)) (root : CKid),
      ({ c with proof := proof, root := root } : Claim R).verdictR env = true := by
  obtain ⟨proof, root, h⟩ := verdict_complete (wf := wf) ok hh hg d
  exact ⟨proof, root, by rw [Claim.verdictR_eq_verdict env wf]; exact h⟩

end Mettapedia.Logic.TierZero.Kernel2
