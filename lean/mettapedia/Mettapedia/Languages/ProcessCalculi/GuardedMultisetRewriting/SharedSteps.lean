import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Step
import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.SharedTerms.Matching

/-!
# Running on shared terms gives exactly the results of running on trees

A configuration of shared terms is a canonical store and a bag of references into it; it stands
for the bag of trees the references unfold to. **A shared step** (`SharedStep`) does everything on
references: it matches the gather patterns with `matchR` (taking nodes apart with `view`, comparing
repeated variables by pointer equality), finds each check's matches by matching every reference
of the bag, and builds the produced terms in the store with `instR`.

**The theorem** (`sharedStep_sound`, `sharedStep_complete`): for the binding-tree term layer
(`treeLayer`), a shared step from a configuration is exactly a step (`Step`, the two-line law) of
the bag of trees it stands for:

* every shared step unfolds to a step of the trees, the store only grows and stays canonical;
* every step of the trees is the unfolding of a shared step.

So a program cannot tell whether its values are stored as shared, shifted DAGs or as trees.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting

open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources
open SharedTerms

variable {Head : Type} {V : Type} [DecidableEq V] [DecidableEq Head]

/-! ## Lists of patterns -/

/-- Match a list of patterns against a list of references, one after another. -/
def matchListR : List (TreePat Head V) → Store Head → Subst V Ref → List Ref →
    Store Head × Option (Subst V Ref)
  | [], St, σ, [] => (St, some σ)
  | p :: ps, St, σ, r :: rs =>
      match matchR p St σ r with
      | (St1, some σ') => matchListR ps St1 σ' rs
      | (St1, none) => (St1, none)
  | [], St, _, _ :: _ => (St, none)
  | _ :: _, St, _, [] => (St, none)

/-- Match a list of patterns against a list of trees, one after another. -/
def matchListT : List (TreePat Head V) → Subst V (Term Head) → List (Term Head) →
    Option (Subst V (Term Head))
  | [], σ, [] => some σ
  | p :: ps, σ, t :: ts => (matchT p σ t).bind fun σ' => matchListT ps σ' ts
  | [], _, _ :: _ => none
  | _ :: _, _, [] => none

/-- Build a list of templates in the store. -/
def instListR : List (TreePat Head V) → Store Head → Subst V Ref → Store Head × Option (List Ref)
  | [], St, _ => (St, some [])
  | p :: ps, St, σ =>
      match instR p St σ with
      | (St1, some r) =>
          match instListR ps St1 σ with
          | (St2, some rs) => (St2, some (r :: rs))
          | (St2, none) => (St2, none)
      | (St1, none) => (St1, none)

theorem matchT_iff_step (p : TreePat Head V) (σ τ : Subst V (Term Head)) (t : Term Head) :
    matchT p σ t = some τ ↔ (treeLayer (Head := Head) (V := V)).Step σ p t τ := by
  constructor
  · intro h
    obtain ⟨grow, only, inst⟩ := matchT_sound p σ τ t h
    exact ⟨grow, only, ⟨t, inst, rfl⟩⟩
  · intro step
    obtain ⟨u, inst, e⟩ := step.solves
    have e' : u = t := e
    subst e'
    exact matchT_complete p σ τ u step.extends_ step.only inst

/-- **Matching a list is a chain of steps.** -/
theorem matchListT_iff_chain :
    ∀ (ps : List (TreePat Head V)) (σ υ : Subst V (Term Head)) (ts : List (Term Head)),
      matchListT ps σ ts = some υ ↔ StepChain (treeLayer (Head := Head) (V := V)) σ ps ts υ
  | [], σ, υ, [] => by
      simp only [matchListT, Option.some.injEq]
      constructor
      · rintro rfl; exact .nil σ
      · intro chain; cases chain; rfl
  | [], σ, υ, _ :: _ => by
      simp only [matchListT, reduceCtorEq, false_iff]
      intro chain; cases chain
  | _ :: _, σ, υ, [] => by
      simp only [matchListT, reduceCtorEq, false_iff]
      intro chain; cases chain
  | p :: ps, σ, υ, t :: ts => by
      simp only [matchListT]
      constructor
      · intro h
        cases hm : matchT p σ t with
        | none => rw [hm] at h; cases h
        | some τ =>
            rw [hm, Option.bind_some] at h
            exact .cons ((matchT_iff_step p σ τ t).mp hm) ((matchListT_iff_chain ps τ υ ts).mp h)
      · intro chain
        cases chain with
        | cons step rest =>
            rw [(matchT_iff_step p σ _ t).mpr step, Option.bind_some]
            exact (matchListT_iff_chain ps _ υ ts).mpr rest

/-- **Matching a list on shared terms is matching it on trees.** -/
theorem matchListR_spec : ∀ (ps : List (TreePat Head V)) (St : Store Head) (σ : Subst V Ref)
    (rs : List Ref), Canonical St → CanonSubst St σ → (∀ r ∈ rs, CanonRef St r) →
    MatchROk St (matchListR ps St σ rs).1 (matchListR ps St σ rs).2
      (matchListT ps (unfoldSubst St σ) (rs.map (unfold St)))
  | [], St, σ, [], canon, hσ, _ => by
      simp only [matchListR, matchListT, List.map_nil]
      exact ⟨List.prefix_refl St, canon, fun τ h => by cases h; exact hσ, rfl⟩
  | [], St, σ, _ :: _, canon, _, _ => by
      simp only [matchListR, matchListT, List.map_cons]
      exact ⟨List.prefix_refl St, canon, fun τ h => (by cases h), rfl⟩
  | _ :: _, St, σ, [], canon, _, _ => by
      simp only [matchListR, matchListT, List.map_nil]
      exact ⟨List.prefix_refl St, canon, fun τ h => (by cases h), rfl⟩
  | p :: ps, St, σ, r :: rs, canon, hσ, hrs => by
      have hr : CanonRef St r := hrs r (by simp)
      obtain ⟨grow1, canon1, hres1, eq1⟩ := matchR_spec p St σ r canon hσ hr
      have unfoldL : matchListR (p :: ps) St σ (r :: rs) =
          (match matchR p St σ r with
            | (St1, some σ') => matchListR ps St1 σ' rs
            | (St1, none) => (St1, none)) := by
        simp only [matchListR]
      rw [unfoldL]
      simp only [List.map_cons, matchListT]
      generalize matchR p St σ r = res at grow1 canon1 hres1 eq1 ⊢
      obtain ⟨St1, res⟩ := res
      dsimp only at grow1 canon1 hres1 eq1 ⊢
      cases res with
      | none =>
          dsimp only
          simp only [Option.map_none] at eq1
          rw [← eq1]
          exact ⟨grow1, canon1, fun τ h => (by cases h), rfl⟩
      | some σ' =>
          dsimp only
          simp only [Option.map_some] at eq1
          rw [← eq1, Option.bind_some]
          have hrs1 : ∀ x ∈ rs, CanonRef St1 x := fun x m => (hrs x (by simp [m])).prefix canon.topo grow1
          obtain ⟨grow2, canon2, hres2, eq2⟩ := matchListR_spec ps St1 σ' rs canon1 (hres1 σ' rfl) hrs1
          refine ⟨grow1.trans grow2, canon2, hres2, ?_⟩
          rw [eq2]
          congr 1
          exact List.map_congr_left fun x m => unfold_prefix canon.topo grow1 (hrs x (by simp [m])).valid

/-- **Building a list of templates on shared terms is instantiating it on trees.** -/
theorem instListR_spec : ∀ (ps : List (TreePat Head V)) (St : Store Head) (σ : Subst V Ref),
    Canonical St → CanonSubst St σ →
    St <+: (instListR ps St σ).1 ∧ Canonical (instListR ps St σ).1 ∧
      (∀ rs, (instListR ps St σ).2 = some rs → ∀ r ∈ rs, CanonRef (instListR ps St σ).1 r) ∧
      (instListR ps St σ).2.map (List.map (unfold (instListR ps St σ).1)) =
        instTemplate (treeLayer (Head := Head) (V := V)) (unfoldSubst St σ) ps
  | [], St, σ, canon, _ => by
      refine ⟨List.prefix_refl St, canon, fun rs h => ?_, ?_⟩
      · simp only [instListR, Option.some.injEq] at h; subst h; simp
      · simp [instListR, instTemplate]
  | p :: ps, St, σ, canon, hσ => by
      obtain ⟨grow1, canon1, cr1, eq1⟩ := instR_spec p St σ canon hσ
      have unfoldL : instListR (p :: ps) St σ =
          (match instR p St σ with
            | (St1, some r) =>
                match instListR ps St1 σ with
                | (St2, some rs) => (St2, some (r :: rs))
                | (St2, none) => (St2, none)
            | (St1, none) => (St1, none)) := by
        simp only [instListR]
      rw [unfoldL]
      have instCons : instTemplate (treeLayer (Head := Head) (V := V)) (unfoldSubst St σ) (p :: ps) =
          (p.inst (unfoldSubst St σ)).bind fun t =>
            (instTemplate (treeLayer (Head := Head) (V := V)) (unfoldSubst St σ) ps).map (t :: ·) := by
        simp only [instTemplate, List.mapM_cons, treeLayer]
        cases h1 : TreePat.inst (unfoldSubst St σ) p <;>
          cases h2 : List.mapM (fun p => TreePat.inst (unfoldSubst St σ) p) ps <;> simp
      rw [instCons]
      generalize instR p St σ = res1 at grow1 canon1 cr1 eq1 ⊢
      obtain ⟨St1, res1⟩ := res1
      dsimp only at grow1 canon1 cr1 eq1 ⊢
      cases res1 with
      | none =>
          dsimp only
          simp only [Option.map_none] at eq1
          rw [← eq1]
          exact ⟨grow1, canon1, fun rs h => (by cases h), rfl⟩
      | some r =>
          dsimp only
          simp only [Option.map_some] at eq1
          rw [← eq1, Option.bind_some]
          have hσ1 := hσ.prefix canon.topo grow1
          obtain ⟨grow2, canon2, kids2, eq2⟩ := instListR_spec ps St1 σ canon1 hσ1
          rw [unfoldSubst_prefix canon.topo grow1 hσ] at eq2
          generalize instListR ps St1 σ = res2 at grow2 canon2 kids2 eq2 ⊢
          obtain ⟨St2, res2⟩ := res2
          dsimp only at grow2 canon2 kids2 eq2 ⊢
          cases res2 with
          | none =>
              dsimp only
              simp only [Option.map_none] at eq2
              rw [← eq2]
              exact ⟨grow1.trans grow2, canon2, fun rs h => (by cases h), rfl⟩
          | some rs =>
              dsimp only
              simp only [Option.map_some] at eq2
              refine ⟨grow1.trans grow2, canon2, fun rs' h => ?_, ?_⟩
              · simp only [Option.some.injEq] at h
                subst h
                intro x m
                rcases List.mem_cons.mp m with hx | m
                · rw [hx]; exact (cr1 r rfl).prefix canon1.topo grow2
                · exact kids2 rs rfl x m
              · rw [← eq2]
                simp [unfold_prefix canon1.topo grow2 (cr1 r rfl).valid]

/-! ## Bags of references -/

theorem map_eq_add {α β : Type*} (f : α → β) :
    ∀ (a : Multiset β) (s : Multiset α) (b : Multiset β), s.map f = a + b →
      ∃ s₁ s₂, s = s₁ + s₂ ∧ s₁.map f = a ∧ s₂.map f = b := by
  classical
  intro a
  induction a using Multiset.induction_on with
  | empty => intro s b h; exact ⟨0, s, by simp, by simp, by simpa using h⟩
  | cons x a ih =>
      intro s b h
      have mem : x ∈ s.map f := by rw [h]; simp
      obtain ⟨y, ys, rfl⟩ := Multiset.mem_map.mp mem
      have split : s = y ::ₘ s.erase y := (Multiset.cons_erase ys).symm
      rw [split, Multiset.map_cons, Multiset.cons_add] at h
      obtain ⟨s₁, s₂, e, h₁, h₂⟩ := ih (s.erase y) b (Multiset.cons_inj_right _ |>.mp h)
      refine ⟨y ::ₘ s₁, s₂, ?_, by simp [h₁], h₂⟩
      rw [split, e, Multiset.cons_add]

theorem exists_list_of_map {α β : Type*} (f : α → β) :
    ∀ (ts : List β) (m : Multiset α), m.map f = (ts : Multiset β) →
      ∃ l : List α, (l : Multiset α) = m ∧ l.map f = ts := by
  classical
  intro ts
  induction ts with
  | nil => intro m h; simp at h; exact ⟨[], by simp [h], rfl⟩
  | cons t ts ih =>
      intro m h
      have mem : t ∈ m.map f := by rw [h]; simp
      obtain ⟨y, ym, rfl⟩ := Multiset.mem_map.mp mem
      have split : m = y ::ₘ m.erase y := (Multiset.cons_erase ym).symm
      rw [split, Multiset.map_cons, ← Multiset.cons_coe] at h
      obtain ⟨l, hl, hmap⟩ := ih (m.erase y) (Multiset.cons_inj_right _ |>.mp h)
      refine ⟨y :: l, ?_, by simp [hmap]⟩
      rw [← Multiset.cons_coe, hl, ← split]

theorem forall₂_split {α β : Type*} {R : α → β → Prop} :
    ∀ {a b : List α} {c d : List β}, List.Forall₂ R (a ++ b) (c ++ d) → a.length = c.length →
      List.Forall₂ R a c ∧ List.Forall₂ R b d
  | [], _, [], _, h, _ => ⟨.nil, h⟩
  | [], _, _ :: _, _, _, len => by simp at len
  | _ :: _, _, [], _, _, len => by simp at len
  | _ :: _, _, _ :: _, _, .cons head tail, len => by
      obtain ⟨first, second⟩ := forall₂_split tail (by simpa using len)
      exact ⟨.cons head first, second⟩

/-! ## Shared steps -/

/-- The trees a bag of references stands for. -/
def trees (St : Store Head) (bag : Multiset Ref) : Multiset (Term Head) := bag.map (unfold St)


/-- **A shared step**: match the gathers on references (`takenR` are taken; `readR` are read, one
per read pattern, and may repeat), keep the read references once in the bag (`keptR`), find each
check's matches by matching references, and build the produced terms in the store. -/
def SharedStep (r : Rule V (Term Head) (TreePat Head V)) (St : Store Head) (bag : Multiset Ref)
    (St' : Store Head) (bag' : Multiset Ref) : Prop :=
  ∃ (σ : Subst V Ref) (rest keptR : Multiset Ref) (takenR readR madeR : List Ref) (St₁ : Store Head),
    takenR.length = r.take.length ∧ bag = rest + takenR + keptR ∧
    keptR ≤ (readR : Multiset Ref) ∧ (∀ x ∈ readR, x ∈ keptR) ∧
    matchListR (r.take ++ r.read) St (fun _ => none) (takenR ++ readR) = (St₁, some σ) ∧
    (∀ c ∈ r.checks, c.holds (unfoldSubst St₁ σ)
      ((bag.filter fun x => (matchR c.pattern St₁ σ x).2.isSome).map (unfold St₁))) ∧
    instListR r.produce St₁ σ = (St', some madeR) ∧
    bag' = rest + keptR + madeR

/-- The matches of a check, found on references, unfold to the matches among the trees. -/
theorem matchesIn_shared {St : Store Head} (canon : Canonical St) {σ : Subst V Ref}
    (hσ : CanonSubst St σ) (q : TreePat Head V) {bag : Multiset Ref}
    (hbag : ∀ x ∈ bag, CanonRef St x) :
    (bag.filter fun x => (matchR q St σ x).2.isSome).map (unfold St) =
      matchesIn (treeLayer (Head := Head) (V := V)) (unfoldSubst St σ) q (bag.map (unfold St)) := by
  rw [matchesIn, Multiset.filter_map]
  congr 1
  apply Multiset.filter_congr
  intro x mem
  obtain ⟨-, -, -, eq⟩ := matchR_spec q St σ x canon hσ (hbag x mem)
  simp only [Function.comp, semRegion_eq_true]
  rw [← Matcher.region_eq_true_iff treeMatcher_sound treeMatcher_complete,
    Matcher.region_eq_true_iff_exists]
  simp only [treeMatcher, Option.mem_toList]
  constructor
  · intro h
    obtain ⟨τ, hτ⟩ := Option.isSome_iff_exists.mp h
    rw [hτ, Option.map_some] at eq
    exact ⟨_, eq.symm⟩
  · rintro ⟨τ, hτ⟩
    cases e : (matchR q St σ x).2 with
    | none => rw [e, Option.map_none, hτ] at eq; cases eq
    | some _ => rfl

omit [DecidableEq Head] in
theorem trees_prefix {St St' : Store Head} (topo : Topo St) (grow : St <+: St') {bag : Multiset Ref}
    (hbag : ∀ x ∈ bag, CanonRef St x) : trees St' bag = trees St bag :=
  Multiset.map_congr rfl fun x m => unfold_prefix topo grow (hbag x m).valid

omit [DecidableEq V] [DecidableEq Head] in
theorem unfoldSubst_none (St : Store Head) :
    unfoldSubst St (fun _ => none : Subst V Ref) = fun _ => none := by
  funext v; simp [unfoldSubst]


/-- **Every shared step is a step of the trees**, and the store only grows and stays canonical. -/
theorem sharedStep_sound {r : Rule V (Term Head) (TreePat Head V)} {St St' : Store Head}
    {bag bag' : Multiset Ref} (canon : Canonical St) (hbag : ∀ x ∈ bag, CanonRef St x)
    (step : SharedStep r St bag St' bag') :
    St <+: St' ∧ Canonical St' ∧ (∀ x ∈ bag', CanonRef St' x) ∧
      Step (treeLayer (Head := Head) (V := V)) r (trees St bag) (trees St' bag') := by
  obtain ⟨σ, rest, keptR, takenR, readR, madeR, St₁, lenT, hbagEq, keptLe, readIn, hmatch, hchecks,
    hinst, rfl⟩ := step
  have inRest : ∀ x ∈ rest, CanonRef St x := fun x m => hbag x (by rw [hbagEq]; simp [m])
  have inKept : ∀ x ∈ keptR, CanonRef St x := fun x m => hbag x (by rw [hbagEq]; simp [m])
  have inBag : ∀ x ∈ takenR ++ readR, CanonRef St x := fun x m => by
    rcases List.mem_append.mp m with m | m
    · exact hbag x (by rw [hbagEq]; simp [m])
    · exact inKept x (readIn x m)
  obtain ⟨grow1, canon1, hres1, eq1⟩ := matchListR_spec (r.take ++ r.read) St (fun _ => none)
    (takenR ++ readR) canon (fun _ _ h => by cases h) inBag
  rw [hmatch] at grow1 canon1 hres1 eq1
  dsimp only at grow1 canon1 hres1 eq1
  simp only [Option.map_some] at eq1
  have hσ : CanonSubst St₁ σ := hres1 σ rfl
  obtain ⟨grow2, canon2, kids2, eq2⟩ := instListR_spec r.produce St₁ σ canon1 hσ
  rw [hinst] at grow2 canon2 kids2 eq2
  dsimp only at grow2 canon2 kids2 eq2
  simp only [Option.map_some] at eq2
  rw [unfoldSubst_none] at eq1
  have chain := (matchListT_iff_chain _ _ _ _).mp eq1.symm
  obtain ⟨only, solves⟩ := (stepChain_empty_iff _ _ _ _).mp chain
  rw [List.map_append] at solves
  obtain ⟨solves₁, solves₂⟩ := forall₂_split solves (by simp [lenT])
  have grow := grow1.trans grow2
  refine ⟨grow, canon2, ?_, ?_⟩
  · intro x m
    simp only [Multiset.mem_add, Multiset.mem_coe] at m
    rcases m with (m | m) | m
    · exact (inRest x m).prefix canon.topo grow
    · exact (inKept x m).prefix canon.topo grow
    · exact kids2 madeR rfl x m
  · refine ⟨unfoldSubst St₁ σ, trees St rest, ((takenR.map (unfold St) : List _) : Multiset _),
      keptR.map (unfold St), madeR.map (unfold St'), only, ⟨_, solves₁, rfl⟩,
      ⟨_, solves₂, ?_, ?_⟩, ?_, ?_, eq2.symm, ?_⟩
    · rw [← Multiset.map_coe]
      exact Multiset.map_le_map keptLe
    · intro t m
      obtain ⟨x, xm, rfl⟩ := List.mem_map.mp m
      exact Multiset.mem_map_of_mem _ (readIn x xm)
    · simp [trees, hbagEq, Multiset.map_add]
    · intro c mem
      have h := hchecks c mem
      have hbag1 : ∀ x ∈ bag, CanonRef St₁ x := fun x m => (hbag x m).prefix canon.topo grow1
      have e : bag.map (unfold St₁) = trees St bag := trees_prefix canon.topo grow1 hbag
      rw [matchesIn_shared canon1 hσ c.pattern hbag1, e] at h
      exact h
    · simp only [trees, Multiset.map_add, Multiset.map_coe]
      congr 2
      · exact Multiset.map_congr rfl fun x m => unfold_prefix canon.topo grow (inRest x m).valid
      · exact Multiset.map_congr rfl fun x m => unfold_prefix canon.topo grow (inKept x m).valid

/-- **Every step of the trees is the unfolding of a shared step.** -/
theorem sharedStep_complete {r : Rule V (Term Head) (TreePat Head V)} {St : Store Head}
    {bag : Multiset Ref} (canon : Canonical St) (hbag : ∀ x ∈ bag, CanonRef St x)
    {M' : Multiset (Term Head)} (step : Step (treeLayer (Head := Head) (V := V)) r (trees St bag) M') :
    ∃ St' bag', SharedStep r St bag St' bag' ∧ trees St' bag' = M' := by
  classical
  obtain ⟨σT, S, _, kept, made, only, ⟨ts₁, solves₁, rfl⟩, ⟨ts₂, solves₂, keptLe, support⟩, hM,
    holds, inst, rfl⟩ := step
  obtain ⟨s₁, keptS, e₁, h₁, h₂⟩ := map_eq_add (unfold St) _ bag _ hM
  obtain ⟨rest, s₃, e₂, h₃, h₄⟩ := map_eq_add (unfold St) _ s₁ _ h₁
  obtain ⟨takenR, ht, hmapT⟩ := exists_list_of_map (unfold St) ts₁ s₃ h₄
  -- the read references: the kept ones, and for each extra read a kept reference with its value
  obtain ⟨extra, hts⟩ := Multiset.le_iff_exists_add.mp keptLe
  have extraKept : ∀ t ∈ extra, t ∈ kept := fun t m =>
    support t (by rw [← Multiset.mem_coe, hts]; exact Multiset.mem_add.mpr (Or.inr m))
  let pick : Term Head → Ref := fun t => if h : ∃ x ∈ keptS, unfold St x = t then h.choose else ⟨0, 0⟩
  have pick_spec : ∀ t ∈ kept, pick t ∈ keptS ∧ unfold St (pick t) = t := by
    intro t m
    have h : ∃ x ∈ keptS, unfold St x = t := by
      rw [← h₂] at m; exact Multiset.mem_map.mp m
    simp only [pick, dif_pos h]
    exact h.choose_spec
  have mapX : (keptS + extra.map pick).map (unfold St) = (ts₂ : Multiset (Term Head)) := by
    rw [Multiset.map_add, h₂, Multiset.map_map, hts]
    congr 1
    conv_rhs => rw [← Multiset.map_id extra]
    exact Multiset.map_congr rfl fun t m => (pick_spec t (extraKept t m)).2
  obtain ⟨readR, hr, hmapR⟩ := exists_list_of_map (unfold St) ts₂ _ mapX
  have keptLeR : keptS ≤ (readR : Multiset Ref) := by rw [hr]; exact Multiset.le_add_right _ _
  have readIn : ∀ x ∈ readR, x ∈ keptS := by
    intro x m
    rw [← Multiset.mem_coe, hr] at m
    rcases Multiset.mem_add.mp m with m | m
    · exact m
    · obtain ⟨t, tm, rfl⟩ := Multiset.mem_map.mp m
      exact (pick_spec t (extraKept t tm)).1
  have hbagEq : bag = rest + takenR + keptS := by rw [e₁, e₂, ht]
  have inRest : ∀ x ∈ rest, CanonRef St x := fun x m => hbag x (by rw [hbagEq]; simp [m])
  have inKept : ∀ x ∈ keptS, CanonRef St x := fun x m => hbag x (by rw [hbagEq]; simp [m])
  have inBag : ∀ x ∈ takenR ++ readR, CanonRef St x := fun x m => by
    rcases List.mem_append.mp m with m | m
    · exact hbag x (by rw [hbagEq]; simp [m])
    · exact inKept x (readIn x m)
  obtain ⟨grow1, canon1, hres1, eq1⟩ := matchListR_spec (r.take ++ r.read) St (fun _ => none)
    (takenR ++ readR) canon (fun _ _ h => by cases h) inBag
  rw [unfoldSubst_none, List.map_append, hmapT, hmapR] at eq1
  have matched : matchListT (r.take ++ r.read) (fun _ => none) (ts₁ ++ ts₂) = some σT :=
    (matchListT_iff_chain _ _ _ _).mpr
      ((stepChain_empty_iff _ _ _ _).mpr ⟨only, List.rel_append solves₁ solves₂⟩)
  rw [matched] at eq1
  generalize hres : matchListR (r.take ++ r.read) St (fun _ => none) (takenR ++ readR) = res at grow1 canon1 hres1 eq1
  obtain ⟨St₁, res⟩ := res
  dsimp only at grow1 canon1 hres1 eq1
  cases res with
  | none => simp at eq1
  | some σ =>
      simp only [Option.map_some, Option.some.injEq] at eq1
      have hσ : CanonSubst St₁ σ := hres1 σ rfl
      obtain ⟨grow2, canon2, kids2, eq2⟩ := instListR_spec r.produce St₁ σ canon1 hσ
      rw [eq1, inst] at eq2
      generalize hinst : instListR r.produce St₁ σ = res2 at grow2 canon2 kids2 eq2
      obtain ⟨St', res2⟩ := res2
      dsimp only at grow2 canon2 kids2 eq2
      cases res2 with
      | none => simp at eq2
      | some madeR =>
          simp only [Option.map_some, Option.some.injEq] at eq2
          have grow := grow1.trans grow2
          refine ⟨St', rest + keptS + madeR, ⟨σ, rest, keptS, takenR, readR, madeR, St₁, ?_, hbagEq,
            keptLeR, readIn, hres, ?_, hinst, rfl⟩, ?_⟩
          · rw [← List.length_map (unfold St), hmapT]
            exact solves₁.length_eq.symm
          · intro c mem
            have hbag1 : ∀ x ∈ bag, CanonRef St₁ x := fun x m => (hbag x m).prefix canon.topo grow1
            have e : bag.map (unfold St₁) = trees St bag := trees_prefix canon.topo grow1 hbag
            rw [matchesIn_shared canon1 hσ c.pattern hbag1, eq1, e]
            exact holds c mem
          · simp only [trees, Multiset.map_add, Multiset.map_coe, eq2]
            rw [← h₃, ← h₂]
            congr 2
            · exact Multiset.map_congr rfl fun x m => unfold_prefix canon.topo grow (inRest x m).valid
            · exact Multiset.map_congr rfl fun x m => unfold_prefix canon.topo grow (inKept x m).valid

end Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting
