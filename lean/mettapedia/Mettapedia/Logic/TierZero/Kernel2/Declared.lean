import Mettapedia.Logic.TierZero.Kernel2.Shared
import Mettapedia.Logic.TierZero.Extension

/-!
# Claims as rules under the declared discipline: safe at every instance

An accepted claim becomes a rule over its formals. Finding F5: a proof that decides a side condition
on the claim's own names, e.g. `(differ x y)` for two formals, proves something about those fresh
names only; as a rule it would also fire where `x = y`.

**The declared discipline** (`Claim.declaredB`, the MeTTa kernel-v2's notion): every formal, of
any kind, is the claim's own name. A side condition the proof decides is **stable** when its
values mention no formal (a dummy is fresh at every instance), or when it is `(absent-from D B)` for
a dummy `D` (a fresh name occurs in no instance of a formal); any other one must be **declared**:
one of the claim's hypotheses, instantiated, which the rule then checks at every instance. A `dv`
condition is decided by the pairs the claim declares (Metamath's `$d`). Example: `honest` (from
`(set x) (set y)`, `needs-diff` proves `(ne x y)`) fails it and stays a verdict; the same claim with
the hypothesis `(differ x y)` passes it and becomes a rule.

**Carrying a proof to an instance** (`substN a f`): each formal `k` becomes the value `a[k]`, and
every other name `k` (a dummy) becomes the name `f k`, fresh for the instance. Matching,
instantiation of patterns without claim names and the kernel's step at a node commute with it
(`matchT_substN`, `inst_substN`, `ruleStep_subst`). Stable side conditions keep their outcome: the
side conditions' functions commute with renaming names injectively (`renN`: `occursAt_renN`,
`abstractAt_renN`, `substAt_renN`, `instantiateAt_renN`), and a fresh name occurs in no instance of
a formal (`occursAt_substN_dummy`).

**The theorems.** `runT_subst`: the claim's proof, run at the instance, gives every judgment
carried. `derived_instance_derivable`: for an accepted claim passing the discipline, **every**
instance of the rule it becomes, in any frame, has a conclusion derivable from the instance's
premises, its stored terms (`given`) and its dummies' sorts at fresh names, with the table's rules
alone. `derived_conservative`: adding the rule adds no theorems, up to citing terms and taking
fresh names of the dummies' sorts.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Kernel2

open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources
open Mettapedia.Logic.TierZero

variable {R : Type}

/-! ## Patterns without claim names -/

mutual

/-- A pattern mentions no claim name (claims' names are fresh, private to each claim). -/
def patNoFv : Pat → Bool
  | .mvar _ => true
  | .idx _ => true
  | .node (.fv _) _ => false
  | .node _ fs => patFieldsNoFv fs

def patFieldsNoFv : TreePatFields Head ℕ → Bool
  | .nil => true
  | .cons _ p rest => patNoFv p && patFieldsNoFv rest

end

/-- The patterns of a premise. -/
def Premise.pats : Premise → List Pat
  | .judg p => [p]
  | .given p => [p]
  | .differ a b => [a, b]
  | .absent x b => [x, b]
  | .dv x y => [x, y]
  | .isOpen r b v => [r, b, v]
  | .isAbstract r x b => [r, x, b]
  | .isSubst r s b => [r, s, b]
  | .unionOf u g d => [u, g, d]
  | .removeOf r x g => [r, x, g]
  | .singletonOf s x => [s, x]
  | .imageOf h' s h => [h', s, h]
  | .atomKind x k => [x, k]
  | .each _ l p => [l, p]

/-- The inputs of a side condition. -/
def Premise.sideIns : Premise → List Pat
  | .differ a b => [a, b]
  | .absent x b => [x, b]
  | .dv x y => [x, y]
  | .isOpen _ b v => [b, v]
  | .isAbstract _ x b => [x, b]
  | .isSubst _ s b => [s, b]
  | .unionOf u g d => [u, g, d]
  | .removeOf r x g => [r, x, g]
  | .singletonOf s x => [s, x]
  | .imageOf h' s h => [h', s, h]
  | .atomKind x k => [x, k]
  | _ => []

/-- The result pattern of a computed side condition. -/
def Premise.sideOut : Premise → Option Pat
  | .isOpen r _ _ => some r
  | .isAbstract r _ _ => some r
  | .isSubst r _ _ => some r
  | _ => none

/-- The form of a premise. -/
def Premise.tag : Premise → ℕ
  | .judg _ => 0
  | .given _ => 1
  | .differ _ _ => 2
  | .absent _ _ => 3
  | .dv _ _ => 4
  | .isOpen _ _ _ => 5
  | .isAbstract _ _ _ => 6
  | .isSubst _ _ _ => 7
  | .unionOf _ _ _ => 8
  | .removeOf _ _ _ => 9
  | .singletonOf _ _ => 10
  | .imageOf _ _ _ => 11
  | .atomKind _ _ => 12
  | .each _ _ _ => 13

/-- A rule mentions no claim name. -/
def RuleNoFv (ru : Rule) : Prop :=
  (∀ p ∈ ru.prems, ∀ q ∈ p.pats, patNoFv q = true) ∧ patNoFv ru.concl = true

/-- Every rule of the table mentions no claim name. -/
def EnvNoFv (env : Env R) : Prop := ∀ r ru, env r = some ru → RuleNoFv ru

/-! ## Rule instances, by membership -/

/-- What a premise kind asks of an instance. -/
def KindHolds (fr : Frame) (σ : Subst ℕ Tm) : Kind → Prop
  | .consume q => (q.inst σ).isSome
  | .check ins ok => ∃ vs, instAll σ ins = some vs ∧ ok fr vs = true
  | .compute r ins f => ∃ vs rv, instAll σ ins = some vs ∧ r.inst σ = some rv ∧ f vs = some rv
  | .each l x p => ((l.inst σ).bind (fun lv => eachJudgments lv x p σ)).isSome

theorem instKinds_holds (fr : Frame) (σ : Subst ℕ Tm) :
    ∀ {ks : List Kind} {ps : List Tm}, instKinds fr σ ks = some ps → ∀ k ∈ ks, KindHolds fr σ k
  | [], _, _, k, m => by simp at m
  | k :: ks, ps, h, k', m => by
      cases k with
      | consume q =>
          simp only [instKinds] at h
          cases hq : q.inst σ with
          | none => rw [hq] at h; simp at h
          | some j =>
              cases hr : instKinds fr σ ks with
              | none => rw [hq, hr] at h; simp at h
              | some js =>
                  rcases List.mem_cons.mp m with rfl | m
                  · simp [KindHolds, hq]
                  · exact instKinds_holds fr σ hr k' m
      | check ins ok =>
          simp only [instKinds] at h
          cases ha : instAll σ ins with
          | none => rw [ha] at h; simp at h
          | some vs =>
              rw [ha] at h
              by_cases hok : ok fr vs = true
              · simp only [hok, ↓reduceIte] at h
                rcases List.mem_cons.mp m with rfl | m
                · exact ⟨vs, ha, hok⟩
                · exact instKinds_holds fr σ h k' m
              · simp [hok] at h
      | compute r ins f =>
          simp only [instKinds] at h
          cases ha : instAll σ ins with
          | none => rw [ha] at h; simp at h
          | some vs =>
              cases hr : r.inst σ with
              | none => rw [ha, hr] at h; simp at h
              | some rv =>
                  rw [ha, hr] at h
                  by_cases hf : f vs = some rv
                  · simp only [hf, ↓reduceIte] at h
                    rcases List.mem_cons.mp m with rfl | m
                    · exact ⟨vs, rv, ha, hr, hf⟩
                    · exact instKinds_holds fr σ h k' m
                  · simp [hf] at h
      | each l x p =>
          simp only [instKinds] at h
          cases he : (l.inst σ).bind (fun lv => eachJudgments lv x p σ) with
          | none => rw [he] at h; simp at h
          | some es =>
              cases hr : instKinds fr σ ks with
              | none => rw [he, hr] at h; simp at h
              | some js =>
                  rcases List.mem_cons.mp m with rfl | m
                  · simp [KindHolds, he]
                  · exact instKinds_holds fr σ hr k' m

theorem instKinds_of_holds (fr : Frame) (σ : Subst ℕ Tm) :
    ∀ (ks : List Kind), (∀ k ∈ ks, KindHolds fr σ k) → ∃ ps, instKinds fr σ ks = some ps
  | [], _ => ⟨[], rfl⟩
  | k :: ks, h => by
      obtain ⟨ps, hps⟩ := instKinds_of_holds fr σ ks fun k' m => h k' (List.mem_cons_of_mem _ m)
      have here := h k List.mem_cons_self
      cases k with
      | consume q =>
          obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp here
          exact ⟨j :: ps, by simp [instKinds, hj, hps]⟩
      | check ins ok =>
          obtain ⟨vs, ha, hok⟩ := here
          exact ⟨ps, by simp [instKinds, ha, hok, hps]⟩
      | compute r ins f =>
          obtain ⟨vs, rv, ha, hr, hf⟩ := here
          exact ⟨ps, by simp [instKinds, ha, hr, hf, hps]⟩
      | each l x p =>
          obtain ⟨es, he⟩ := Option.isSome_iff_exists.mp here
          exact ⟨es ++ ps, by simp only [instKinds, he, hps]⟩

/-- A list premise's judgments at `σ`, if its list is a list. -/
def eachAt (σ : Subst ℕ Tm) (l : Pat) (x : ℕ) (p : Pat) : Option (List Tm) :=
  (l.inst σ).bind (fun lv => eachJudgments lv x p σ)

theorem instKinds_mem (fr : Frame) (σ : Subst ℕ Tm) :
    ∀ {ks : List Kind} {ps : List Tm}, instKinds fr σ ks = some ps →
      ∀ j ∈ ps, (∃ q, Kind.consume q ∈ ks ∧ q.inst σ = some j) ∨
        (∃ l x p es, Kind.each l x p ∈ ks ∧ eachAt σ l x p = some es ∧ j ∈ es)
  | [], ps, h, j, m => by simp [instKinds] at h; subst h; simp at m
  | k :: ks, ps, h, j, m => by
      have lift : ((∃ q, Kind.consume q ∈ ks ∧ q.inst σ = some j) ∨
          (∃ l x p es, Kind.each l x p ∈ ks ∧ eachAt σ l x p = some es ∧ j ∈ es)) →
          ((∃ q, Kind.consume q ∈ k :: ks ∧ q.inst σ = some j) ∨
          (∃ l x p es, Kind.each l x p ∈ k :: ks ∧ eachAt σ l x p = some es ∧ j ∈ es)) := by
        rintro (⟨q, mq, iq⟩ | ⟨l, x, p, es, me, he, mj⟩)
        · exact Or.inl ⟨q, List.mem_cons_of_mem _ mq, iq⟩
        · exact Or.inr ⟨l, x, p, es, List.mem_cons_of_mem _ me, he, mj⟩
      cases k with
      | consume q =>
          simp only [instKinds] at h
          cases hq : q.inst σ with
          | none => rw [hq] at h; simp at h
          | some j' =>
              cases hr : instKinds fr σ ks with
              | none => rw [hq, hr] at h; simp at h
              | some js =>
                  rw [hq, hr] at h
                  simp only [Option.some.injEq] at h
                  subst h
                  rcases List.mem_cons.mp m with rfl | m
                  · exact Or.inl ⟨q, List.mem_cons_self, hq⟩
                  · exact lift (instKinds_mem fr σ hr j m)
      | check ins ok =>
          simp only [instKinds] at h
          cases ha : instAll σ ins with
          | none => rw [ha] at h; simp at h
          | some vs =>
              rw [ha] at h
              by_cases hok : ok fr vs = true
              · simp only [hok, ↓reduceIte] at h
                exact lift (instKinds_mem fr σ h j m)
              · simp [hok] at h
      | compute r ins f =>
          simp only [instKinds] at h
          cases ha : instAll σ ins with
          | none => rw [ha] at h; simp at h
          | some vs =>
              cases hr : r.inst σ with
              | none => rw [ha, hr] at h; simp at h
              | some rv =>
                  rw [ha, hr] at h
                  by_cases hf : f vs = some rv
                  · simp only [hf, ↓reduceIte] at h
                    exact lift (instKinds_mem fr σ h j m)
                  · simp [hf] at h
      | each l x p =>
          simp only [instKinds] at h
          cases he : (l.inst σ).bind (fun lv => eachJudgments lv x p σ) with
          | none => rw [he] at h; simp at h
          | some es =>
              cases hr : instKinds fr σ ks with
              | none => rw [he, hr] at h; simp at h
              | some js =>
                  rw [he, hr] at h
                  simp only [Option.some.injEq] at h
                  subst h
                  rcases List.mem_append.mp m with m | m
                  · exact Or.inr ⟨l, x, p, es, List.mem_cons_self, he, m⟩
                  · exact lift (instKinds_mem fr σ hr j m)

theorem instKinds_consume (fr : Frame) (σ : Subst ℕ Tm) :
    ∀ {ks : List Kind} {ps : List Tm}, instKinds fr σ ks = some ps →
      ∀ q, Kind.consume q ∈ ks → ∃ j ∈ ps, q.inst σ = some j
  | [], _, _, _, m => by simp at m
  | k :: ks, ps, h, q, m => by
      cases k with
      | consume q' =>
          simp only [instKinds] at h
          cases hq : q'.inst σ with
          | none => rw [hq] at h; simp at h
          | some j =>
              cases hr : instKinds fr σ ks with
              | none => rw [hq, hr] at h; simp at h
              | some js =>
                  rw [hq, hr] at h
                  simp only [Option.some.injEq] at h
                  subst h
                  rcases List.mem_cons.mp m with e | m
                  · cases e; exact ⟨j, List.mem_cons_self, hq⟩
                  · obtain ⟨j', mj, ij⟩ := instKinds_consume fr σ hr q m
                    exact ⟨j', List.mem_cons_of_mem _ mj, ij⟩
      | check ins ok =>
          simp only [instKinds] at h
          cases ha : instAll σ ins with
          | none => rw [ha] at h; simp at h
          | some vs =>
              rw [ha] at h
              by_cases hok : ok fr vs = true
              · simp only [hok, ↓reduceIte] at h
                rcases List.mem_cons.mp m with e | m
                · cases e
                · exact instKinds_consume fr σ h q m
              · simp [hok] at h
      | compute r ins f =>
          simp only [instKinds] at h
          cases ha : instAll σ ins with
          | none => rw [ha] at h; simp at h
          | some vs =>
              cases hr : r.inst σ with
              | none => rw [ha, hr] at h; simp at h
              | some rv =>
                  rw [ha, hr] at h
                  by_cases hf : f vs = some rv
                  · simp only [hf, ↓reduceIte] at h
                    rcases List.mem_cons.mp m with e | m
                    · cases e
                    · exact instKinds_consume fr σ h q m
                  · simp [hf] at h
      | each l x p =>
          simp only [instKinds] at h
          cases he : (l.inst σ).bind (fun lv => eachJudgments lv x p σ) with
          | none => rw [he] at h; simp at h
          | some es =>
              cases hr : instKinds fr σ ks with
              | none => rw [he, hr] at h; simp at h
              | some js =>
                  rw [he, hr] at h
                  simp only [Option.some.injEq] at h
                  subst h
                  rcases List.mem_cons.mp m with e | m
                  · cases e
                  · obtain ⟨j', mj, ij⟩ := instKinds_consume fr σ hr q m
                    exact ⟨j', List.mem_append_right _ mj, ij⟩

/-- A rule instance, unfolded. -/
theorem instance_iff (fr : Frame) (ru : Rule) (a ps : List Tm) (c : Tm) :
    ru.instance fr a = some (ps, c) ↔
      a.length = ru.nformals ∧ instKinds fr (substOf a) ru.kinds = some ps ∧
        ru.concl.inst (substOf a) = some c := by
  unfold Rule.instance
  constructor
  · intro h
    split at h
    · rename_i len
      cases hi : instKinds fr (substOf a) ru.kinds with
      | none => rw [hi] at h; simp at h
      | some ps' =>
          cases hc : ru.concl.inst (substOf a) with
          | none => rw [hi, hc] at h; simp at h
          | some c' =>
              rw [hi, hc] at h
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact ⟨len, rfl, rfl⟩
    · cases h
  · rintro ⟨len, hi, hc⟩
    simp [len, hi, hc]

/-- The kind of an `absent-from` premise holds exactly when the check holds. -/
theorem holds_absent (fr : Frame) (σ : Subst ℕ Tm) (x b : Pat) :
    KindHolds fr σ (Premise.absent x b).kind ↔
      ∃ xv bv, x.inst σ = some xv ∧ b.inst σ = some bv ∧ absentOk xv bv = true := by
  simp only [Premise.kind, KindHolds, instAll]
  constructor
  · rintro ⟨vs, hvs, hok⟩
    cases hx : x.inst σ with
    | none => rw [hx] at hvs; simp at hvs
    | some xv =>
        cases hb : b.inst σ with
        | none => rw [hx, hb] at hvs; simp at hvs
        | some bv =>
            rw [hx, hb] at hvs
            simp only [Option.some.injEq] at hvs
            subst hvs
            exact ⟨xv, bv, rfl, rfl, hok⟩
  · rintro ⟨xv, bv, hx, hb, hok⟩
    exact ⟨[xv, bv], by simp [hx, hb], hok⟩

/-! ## Carrying a proof to an instance: formals to values, other names renamed -/

mutual

/-- **Replace each formal `fv k` (`k < a.length`) by the value `a[k]`, and rename every other name
`k` to `f k`.** -/
def substN (a : List Tm) (f : ℕ → ℕ) : Tm → Tm
  | .idx k => .idx k
  | .node (.fv k) fs => (a[k]?).getD (.node (.fv (f k)) (substNF a f fs))
  | .node (.sym s) fs => .node (.sym s) (substNF a f fs)
  | .node (.num m) fs => .node (.num m) (substNF a f fs)
  | .node (.str m) fs => .node (.str m) (substNF a f fs)
  | .node .expr fs => .node .expr (substNF a f fs)
  | .node .bind fs => .node .bind (substNF a f fs)

/-- Replace in each field. -/
def substNF (a : List Tm) (f : ℕ → ℕ) : Fields Head → Fields Head
  | .nil => .nil
  | .cons d t rest => .cons d (substN a f t) (substNF a f rest)

end

/-- A substitution carried by `substN`. -/
def mapS (a : List Tm) (f : ℕ → ℕ) (σ : Subst ℕ Tm) : Subst ℕ Tm := fun v => (σ v).map (substN a f)

mutual

/-- A term without claim names is not changed. -/
theorem substN_of_nil (a : List Tm) (f : ℕ → ℕ) : ∀ t : Tm, fvsOf t = [] → substN a f t = t
  | .idx _, _ => rfl
  | .node (.fv _) _, h => by simp [fvsOf] at h
  | .node (.sym s) fs, h => by
      simp only [fvsOf] at h; simp only [substN, substNF_of_nil a f fs h]
  | .node (.num m) fs, h => by
      simp only [fvsOf] at h; simp only [substN, substNF_of_nil a f fs h]
  | .node (.str m) fs, h => by
      simp only [fvsOf] at h; simp only [substN, substNF_of_nil a f fs h]
  | .node .expr fs, h => by
      simp only [fvsOf] at h; simp only [substN, substNF_of_nil a f fs h]
  | .node .bind fs, h => by
      simp only [fvsOf] at h; simp only [substN, substNF_of_nil a f fs h]

theorem substNF_of_nil (a : List Tm) (f : ℕ → ℕ) : ∀ fs : Fields Head, fvsFields fs = [] → substNF a f fs = fs
  | .nil, _ => rfl
  | .cons d t rest, h => by
      simp only [fvsFields, List.append_eq_nil_iff] at h
      simp only [substNF, substN_of_nil a f t h.1, substNF_of_nil a f rest h.2]

end

mutual

/-- The names of a carried term come from the formals' values, or are renamed names. -/
theorem mem_fvs_substN (a : List Tm) (f : ℕ → ℕ) {x : ℕ} : ∀ t : Tm, x ∈ fvsOf (substN a f t) →
    (∃ k ∈ fvsOf t, ∃ v, a[k]? = some v ∧ x ∈ fvsOf v) ∨ (∃ k ∈ fvsOf t, a.length ≤ k ∧ x = f k)
  | .idx _, h => by simp [substN, fvsOf] at h
  | .node (.fv k) fs, h => by
      simp only [substN] at h
      cases hk : a[k]? with
      | some v => rw [hk] at h; exact Or.inl ⟨k, by simp [fvsOf], v, hk, h⟩
      | none =>
          rw [hk] at h
          simp only [Option.getD_none, fvsOf, List.mem_cons] at h
          have len : a.length ≤ k := by simpa using hk
          rcases h with rfl | h
          · exact Or.inr ⟨k, by simp [fvsOf], len, rfl⟩
          · rcases mem_fvsF_substN a f fs h with ⟨k', mk, v, hv, hx⟩ | ⟨k', mk, lk, e⟩
            · exact Or.inl ⟨k', by simp [fvsOf, mk], v, hv, hx⟩
            · exact Or.inr ⟨k', by simp [fvsOf, mk], lk, e⟩
  | .node (.sym s) fs, h => by
      simp only [substN, fvsOf] at h ⊢; exact mem_fvsF_substN a f fs h
  | .node (.num m) fs, h => by
      simp only [substN, fvsOf] at h ⊢; exact mem_fvsF_substN a f fs h
  | .node (.str m) fs, h => by
      simp only [substN, fvsOf] at h ⊢; exact mem_fvsF_substN a f fs h
  | .node .expr fs, h => by
      simp only [substN, fvsOf] at h ⊢; exact mem_fvsF_substN a f fs h
  | .node .bind fs, h => by
      simp only [substN, fvsOf] at h ⊢; exact mem_fvsF_substN a f fs h

theorem mem_fvsF_substN (a : List Tm) (f : ℕ → ℕ) {x : ℕ} : ∀ fs : Fields Head,
    x ∈ fvsFields (substNF a f fs) →
      (∃ k ∈ fvsFields fs, ∃ v, a[k]? = some v ∧ x ∈ fvsOf v) ∨ (∃ k ∈ fvsFields fs, a.length ≤ k ∧ x = f k)
  | .nil, h => by simp [substNF, fvsFields] at h
  | .cons d t rest, h => by
      simp only [substNF, fvsFields, List.mem_append] at h ⊢
      rcases h with h | h
      · rcases mem_fvs_substN a f t h with ⟨k, mk, v, hv, hx⟩ | ⟨k, mk, lk, e⟩
        · exact Or.inl ⟨k, Or.inl mk, v, hv, hx⟩
        · exact Or.inr ⟨k, Or.inl mk, lk, e⟩
      · rcases mem_fvsF_substN a f rest h with ⟨k, mk, v, hv, hx⟩ | ⟨k, mk, lk, e⟩
        · exact Or.inl ⟨k, Or.inr mk, v, hv, hx⟩
        · exact Or.inr ⟨k, Or.inr mk, lk, e⟩

end

mutual

/-- **Instantiation commutes with carrying**, for patterns without claim names. -/
theorem inst_substN (a : List Tm) (f : ℕ → ℕ) (σ : Subst ℕ Tm) : ∀ p : Pat, patNoFv p = true →
    (p.inst σ).map (substN a f) = p.inst (mapS a f σ)
  | .mvar _, _ => rfl
  | .idx _, _ => rfl
  | .node (.fv _) _, h => by simp [patNoFv] at h
  | .node (.sym s) fs, h => by
      simp only [patNoFv] at h
      simp only [TreePat.inst, ← instF_substN a f σ fs h]
      cases TreePatFields.inst σ fs <;> rfl
  | .node (.num m) fs, h => by
      simp only [patNoFv] at h
      simp only [TreePat.inst, ← instF_substN a f σ fs h]
      cases TreePatFields.inst σ fs <;> rfl
  | .node (.str m) fs, h => by
      simp only [patNoFv] at h
      simp only [TreePat.inst, ← instF_substN a f σ fs h]
      cases TreePatFields.inst σ fs <;> rfl
  | .node .expr fs, h => by
      simp only [patNoFv] at h
      simp only [TreePat.inst, ← instF_substN a f σ fs h]
      cases TreePatFields.inst σ fs <;> rfl
  | .node .bind fs, h => by
      simp only [patNoFv] at h
      simp only [TreePat.inst, ← instF_substN a f σ fs h]
      cases TreePatFields.inst σ fs <;> rfl

theorem instF_substN (a : List Tm) (f : ℕ → ℕ) (σ : Subst ℕ Tm) : ∀ fs : TreePatFields Head ℕ,
    patFieldsNoFv fs = true → (fs.inst σ).map (substNF a f) = fs.inst (mapS a f σ)
  | .nil, _ => rfl
  | .cons d p rest, h => by
      simp only [patFieldsNoFv, Bool.and_eq_true] at h
      simp only [TreePatFields.inst, ← inst_substN a f σ p h.1, ← instF_substN a f σ rest h.2]
      cases p.inst σ <;> cases TreePatFields.inst σ rest <;> rfl

end

theorem instAll_substN (a : List Tm) (f : ℕ → ℕ) (σ : Subst ℕ Tm) :
    ∀ ps : List Pat, (∀ p ∈ ps, patNoFv p = true) →
      (instAll σ ps).map (List.map (substN a f)) = instAll (mapS a f σ) ps
  | [], _ => rfl
  | p :: ps, h => by
      simp only [instAll, ← inst_substN a f σ p (h p List.mem_cons_self),
        ← instAll_substN a f σ ps (fun q m => h q (List.mem_cons_of_mem _ m))]
      cases p.inst σ <;> cases instAll σ ps <;> rfl

theorem extends_mapS (a : List Tm) (f : ℕ → ℕ) {σ τ : Subst ℕ Tm} (h : Extends σ τ) :
    Extends (mapS a f σ) (mapS a f τ) := by
  intro v t hv
  simp only [mapS] at hv ⊢
  cases hσ : σ v with
  | none => rw [hσ] at hv; cases hv
  | some u => rw [hσ] at hv; rw [h v u hσ]; exact hv

/-- **Matching commutes with carrying.** -/
theorem matchT_substN (a : List Tm) (f : ℕ → ℕ) {q : Pat} (hq : patNoFv q = true) {σ τ : Subst ℕ Tm}
    {j : Tm} (h : matchT q σ j = some τ) : matchT q (mapS a f σ) (substN a f j) = some (mapS a f τ) := by
  obtain ⟨grow, only, inst⟩ := matchT_sound q σ τ j h
  refine matchT_complete q (mapS a f σ) (mapS a f τ) (substN a f j) (extends_mapS a f grow)
    (fun v nv => ?_) ?_
  · simp only [mapS, only v nv]
  · rw [← inst_substN a f τ q hq, inst]; rfl

/-! ## The step at a node commutes with carrying, when its side conditions are stable -/

/-- A premise kind whose check or computation, carried, holds in the frame `fr'`. -/
def KindStable (fr fr' : Frame) (a : List Tm) (f : ℕ → ℕ) (τ : Subst ℕ Tm) : Kind → Prop
  | .consume q => patNoFv q = true
  | .check ins ok => (∀ p ∈ ins, patNoFv p = true) ∧
      ∀ vs, instAll τ ins = some vs → ok fr vs = true → ok fr' (vs.map (substN a f)) = true
  | .compute r ins g => patNoFv r = true ∧ (∀ p ∈ ins, patNoFv p = true) ∧
      ∀ vs rv, instAll τ ins = some vs → r.inst τ = some rv → g vs = some rv →
        g (vs.map (substN a f)) = some (substN a f rv)
  | .each l _ p => patNoFv l = true ∧ patNoFv p = true

theorem fieldsAtZero_substNF (a : List Tm) (f : ℕ → ℕ) :
    ∀ fs : Fields Head, fieldsAtZero (substNF a f fs) = (fieldsAtZero fs).map (List.map (substN a f))
  | .nil => rfl
  | .cons 0 t rest => by
      simp only [substNF, fieldsAtZero, fieldsAtZero_substNF a f rest]
      cases fieldsAtZero rest <;> rfl
  | .cons (_ + 1) _ _ => rfl

theorem listElems_substN (a : List Tm) (f : ℕ → ℕ) {t : Tm} {es : List Tm} (h : listElems t = some es) :
    listElems (substN a f t) = some (es.map (substN a f)) := by
  cases t with
  | idx _ => simp [listElems] at h
  | node hd fs =>
      cases hd with
      | expr =>
          simp only [listElems] at h
          simp only [substN, listElems, fieldsAtZero_substNF, h, Option.map_some]
      | _ => simp [listElems] at h

theorem mapS_updS (a : List Tm) (f : ℕ → ℕ) (σ : Subst ℕ Tm) (x : ℕ) (e : Tm) :
    mapS a f (updS σ x e) = updS (mapS a f σ) x (substN a f e) := by
  funext v
  simp only [mapS, updS]
  split_ifs <;> rfl

theorem eachAt_substN (a : List Tm) (f : ℕ → ℕ) {σ : Subst ℕ Tm} {l p : Pat} {x : ℕ} {es : List Tm}
    (hl : patNoFv l = true) (hp : patNoFv p = true)
    (h : (l.inst σ).bind (fun lv => eachJudgments lv x p σ) = some es) :
    (l.inst (mapS a f σ)).bind (fun lv => eachJudgments lv x p (mapS a f σ)) = some (es.map (substN a f)) := by
  cases hli : l.inst σ with
  | none => rw [hli] at h; cases h
  | some lv =>
      rw [hli] at h
      have hl' : l.inst (mapS a f σ) = some (substN a f lv) := by
        rw [← inst_substN a f σ l hl, hli]; rfl
      rw [hl']
      simp only [Option.bind_some, eachJudgments] at h ⊢
      cases hle : listElems lv with
      | none => rw [hle] at h; cases h
      | some ls =>
          rw [hle] at h
          rw [listElems_substN a f hle]
          simp only [Option.bind_some] at h ⊢
          clear hle hli hl'
          induction ls generalizing es with
          | nil => simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h; subst h; rfl
          | cons e ls ih =>
              simp only [List.map_cons, List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at h ⊢
              cases hpe : p.inst (updS σ x e) with
              | none => rw [hpe] at h; simp at h
              | some j =>
                  rw [hpe] at h
                  have hpe' : p.inst (updS (mapS a f σ) x (substN a f e)) = some (substN a f j) := by
                    rw [← mapS_updS, ← inst_substN a f _ p hp, hpe]; rfl
                  rw [hpe']
                  cases hr : ls.mapM (fun e => p.inst (updS σ x e)) with
                  | none => rw [hr] at h; simp at h
                  | some js =>
                      rw [hr] at h
                      simp only [Option.bind_some, Option.some.injEq] at h
                      subst h
                      rw [ih hr]
                      rfl

theorem solveKinds_subst (fr fr' : Frame) (a : List Tm) (f : ℕ → ℕ) :
    ∀ (ks : List Kind) (σ τ : Subst ℕ Tm) (js : List Tm), (∀ k ∈ ks, KindStable fr fr' a f τ k) →
      solveKinds fr ks σ js = some τ →
        solveKinds fr' ks (mapS a f σ) (js.map (substN a f)) = some (mapS a f τ)
  | [], σ, τ, js, _, h => by
      simp only [solveKinds] at h
      by_cases e : js = []
      · rw [if_pos e] at h; cases h; subst e; simp [solveKinds]
      · rw [if_neg e] at h; cases h
  | .consume q :: ks, σ, τ, js, st, h => by
      cases js with
      | nil => simp [solveKinds] at h
      | cons j rest =>
          simp only [solveKinds] at h
          cases hm : matchT q σ j with
          | none => rw [hm] at h; cases h
          | some τ1 =>
              rw [hm] at h
              have hq : patNoFv q = true := st _ List.mem_cons_self
              simp only [List.map_cons, solveKinds, matchT_substN a f hq hm]
              exact solveKinds_subst fr fr' a f ks τ1 τ rest (fun k m => st k (List.mem_cons_of_mem _ m)) h
  | .check ins ok :: ks, σ, τ, js, st, h => by
      obtain ⟨hins, hok⟩ := st _ List.mem_cons_self
      simp only [solveKinds] at h
      cases hi : instAll σ ins with
      | none => rw [hi] at h; simp at h
      | some vs =>
          rw [hi] at h
          by_cases c : ok fr vs = true
          · simp only [c, ↓reduceIte] at h
            have grow := (solveKinds_sound fr ks σ τ js h).1
            have hi' : instAll (mapS a f σ) ins = some (vs.map (substN a f)) := by
              rw [← instAll_substN a f σ ins hins, hi]; rfl
            have c' := hok vs (instAll_extends grow hi) c
            simp only [solveKinds, hi', c', ↓reduceIte]
            exact solveKinds_subst fr fr' a f ks σ τ js (fun k m => st k (List.mem_cons_of_mem _ m)) h
          · simp [c] at h
  | .compute r ins g :: ks, σ, τ, js, st, h => by
      obtain ⟨hr, hins, hf⟩ := st _ List.mem_cons_self
      simp only [solveKinds] at h
      cases hi : instAll σ ins with
      | none => rw [hi] at h; simp at h
      | some vs =>
          simp only [hi] at h
          cases hfv : g vs with
          | none => simp [hfv] at h
          | some v =>
              simp only [hfv] at h
              cases hm : matchT r σ v with
              | none => simp [hm] at h
              | some τ1 =>
                  simp only [hm] at h
                  obtain ⟨g1, -, i1⟩ := matchT_sound r σ τ1 v hm
                  have g2 := (solveKinds_sound fr ks τ1 τ js h).1
                  have hi' : instAll (mapS a f σ) ins = some (vs.map (substN a f)) := by
                    rw [← instAll_substN a f σ ins hins, hi]; rfl
                  have fv' := hf vs v (instAll_extends (g1.trans g2) hi) (inst_extends i1 g2) hfv
                  simp only [solveKinds, hi', fv', matchT_substN a f hr hm]
                  exact solveKinds_subst fr fr' a f ks τ1 τ js (fun k m => st k (List.mem_cons_of_mem _ m)) h
  | .each l x p :: ks, σ, τ, js, st, h => by
      obtain ⟨hl, hp⟩ := st _ List.mem_cons_self
      simp only [solveKinds] at h
      cases he : (l.inst σ).bind (fun lv => eachJudgments lv x p σ) with
      | none => rw [he] at h; simp at h
      | some es =>
          rw [he] at h
          simp only at h
          by_cases ht : js.take es.length = es
          · rw [if_pos ht] at h
            have ht' : (js.map (substN a f)).take es.length = es.map (substN a f) := by
              rw [← List.map_take, ht]
            simp only [solveKinds, eachAt_substN a f hl hp he, ht', ↓reduceIte, List.length_map]
            rw [← List.map_drop]
            exact solveKinds_subst fr fr' a f ks σ τ (js.drop es.length)
              (fun k m => st k (List.mem_cons_of_mem _ m)) h
          · rw [if_neg ht] at h; cases h

theorem mapM_range_mapS (a : List Tm) (f : ℕ → ℕ) (τ : Subst ℕ Tm) :
    ∀ n : ℕ, ((List.range n).mapM τ).map (List.map (substN a f)) = (List.range n).mapM (mapS a f τ)
  | 0 => by simp
  | n + 1 => by
      rw [List.range_succ, List.mapM_append, List.mapM_append, ← mapM_range_mapS a f τ n]
      cases (List.range n).mapM τ <;> cases h : τ n <;> simp [mapS, h]

theorem substOf_mapS (a : List Tm) (f : ℕ → ℕ) (as : List Tm) :
    substOf (as.map (substN a f)) = mapS a f (substOf as) := by
  funext v; simp [substOf, mapS]

/-- **The step of a rule commutes with carrying**, when its kinds are stable. -/
theorem ruleStep_subst (fr fr' : Frame) (a : List Tm) (f : ℕ → ℕ) {ru : Rule} {js : List Tm} {c : Tm}
    (h : ruleStep fr ru js = some c) (hc : patNoFv ru.concl = true)
    (st : ∀ τ, solveKinds fr ru.kinds emptySubst js = some τ → ∀ k ∈ ru.kinds, KindStable fr fr' a f τ k) :
    ruleStep fr' ru (js.map (substN a f)) = some (substN a f c) := by
  unfold ruleStep at h ⊢
  cases hs : solveKinds fr ru.kinds emptySubst js with
  | none => rw [hs] at h; cases h
  | some τ =>
      rw [hs] at h
      have e : mapS a f emptySubst = emptySubst := by funext v; rfl
      have hs' := solveKinds_subst fr fr' a f ru.kinds emptySubst τ js (st τ hs) hs
      rw [e] at hs'
      rw [hs']
      simp only at h ⊢
      have mm := mapM_range_mapS a f τ ru.nformals
      cases ha : (List.range ru.nformals).mapM τ with
      | none => rw [ha] at h; cases h
      | some as =>
          rw [ha] at h mm
          simp only [Option.map_some] at mm
          rw [← mm]
          simp only
          rw [substOf_mapS, ← inst_substN a f _ _ hc]
          simp only [h, Option.map_some]

/-! ## Renaming names injectively commutes with the side conditions' functions -/

/-- Rename a head's name. -/
def renH (f : ℕ → ℕ) : Head → Head
  | .fv k => .fv (f k)
  | h => h

mutual

/-- **Rename every name `k` to `f k`**; bound variables and other heads stay. -/
def renN (f : ℕ → ℕ) : Tm → Tm
  | .idx k => .idx k
  | .node h fs => .node (renH f h) (renNF f fs)

/-- Rename in each field. -/
def renNF (f : ℕ → ℕ) : Fields Head → Fields Head
  | .nil => .nil
  | .cons d t rest => .cons d (renN f t) (renNF f rest)

end

/-- Rename both sides of a pair. -/
def renPair (f : ℕ → ℕ) (p : Tm × Tm) : Tm × Tm := (renN f p.1, renN f p.2)

theorem mapM_map_of {α β : Type} (g : β → β) {look look' : α → Option β} :
    ∀ xs : List α, (∀ x ∈ xs, look' x = (look x).map g) →
      xs.mapM look' = (xs.mapM look).map (List.map g)
  | [], _ => rfl
  | x :: xs, h => by
      rw [List.mapM_cons, List.mapM_cons, h x List.mem_cons_self,
        mapM_map_of g xs fun y m => h y (List.mem_cons_of_mem _ m)]
      cases look x <;> cases xs.mapM look <;> simp

mutual

/-- On a term mentioning no formal, carrying is renaming. -/
theorem substN_eq_renN (a : List Tm) (f : ℕ → ℕ) :
    ∀ t : Tm, (∀ k ∈ fvsOf t, a.length ≤ k) → substN a f t = renN f t
  | .idx _, _ => rfl
  | .node (.fv k) fs, h => by
      have hk : a[k]? = none := List.getElem?_eq_none (h k (by simp [fvsOf]))
      simp only [substN, hk, Option.getD_none, renN, renH,
        substNF_eq_renNF a f fs fun j m => h j (by simp [fvsOf, m])]
  | .node (.sym s) fs, h => by
      simp only [substN, renN, renH, substNF_eq_renNF a f fs fun j m => h j (by simpa [fvsOf] using m)]
  | .node (.num m) fs, h => by
      simp only [substN, renN, renH, substNF_eq_renNF a f fs fun j mj => h j (by simpa [fvsOf] using mj)]
  | .node (.str m) fs, h => by
      simp only [substN, renN, renH, substNF_eq_renNF a f fs fun j mj => h j (by simpa [fvsOf] using mj)]
  | .node .expr fs, h => by
      simp only [substN, renN, renH, substNF_eq_renNF a f fs fun j m => h j (by simpa [fvsOf] using m)]
  | .node .bind fs, h => by
      simp only [substN, renN, renH, substNF_eq_renNF a f fs fun j m => h j (by simpa [fvsOf] using m)]

theorem substNF_eq_renNF (a : List Tm) (f : ℕ → ℕ) :
    ∀ fs : Fields Head, (∀ k ∈ fvsFields fs, a.length ≤ k) → substNF a f fs = renNF f fs
  | .nil, _ => rfl
  | .cons d t rest, h => by
      simp only [substNF, renNF,
        substN_eq_renN a f t fun k m => h k (by simp [fvsFields, m]),
        substNF_eq_renNF a f rest fun k m => h k (by simp [fvsFields, m])]

end

theorem renH_inj {f : ℕ → ℕ} (hf : Function.Injective f) {h h' : Head} (e : renH f h = renH f h') :
    h = h' := by
  cases h <;> cases h' <;> simp only [renH, Head.fv.injEq, Head.sym.injEq, Head.num.injEq,
    Head.str.injEq, reduceCtorEq] at e ⊢ <;> first | exact e | exact hf e

mutual

theorem renN_inj {f : ℕ → ℕ} (hf : Function.Injective f) : ∀ {t u : Tm}, renN f t = renN f u → t = u
  | .idx _, .idx _, e => by simpa [renN] using e
  | .idx _, .node _ _, e => by simp [renN] at e
  | .node _ _, .idx _, e => by simp [renN] at e
  | .node _ fs, .node _ gs, e => by
      simp only [renN, Term.node.injEq] at e
      rw [renH_inj hf e.1, renNF_inj hf e.2]

theorem renNF_inj {f : ℕ → ℕ} (hf : Function.Injective f) :
    ∀ {fs gs : Fields Head}, renNF f fs = renNF f gs → fs = gs
  | .nil, .nil, _ => rfl
  | .nil, .cons _ _ _, e => by simp [renNF] at e
  | .cons _ _ _, .nil, e => by simp [renNF] at e
  | .cons _ _ _, .cons _ _ _, e => by
      simp only [renNF, Fields.cons.injEq] at e
      rw [e.1, renN_inj hf e.2.1, renNF_inj hf e.2.2]

end

theorem renN_eq_iff {f : ℕ → ℕ} (hf : Function.Injective f) (t u : Tm) : renN f t = renN f u ↔ t = u :=
  ⟨renN_inj hf, fun e => by rw [e]⟩

mutual

theorem lift_renN (f : ℕ → ℕ) (amt : ℕ) :
    ∀ (c : ℕ) (t : Tm), Term.lift c amt (renN f t) = renN f (Term.lift c amt t)
  | c, .idx k => by
      simp only [renN, Term.lift]
      split <;> rfl
  | c, .node h fs => by simp only [renN, Term.lift, lift_renNF f amt c fs]

theorem lift_renNF (f : ℕ → ℕ) (amt : ℕ) :
    ∀ (c : ℕ) (fs : Fields Head), Term.Fields.lift c amt (renNF f fs) = renNF f (Term.Fields.lift c amt fs)
  | _, .nil => rfl
  | c, .cons e t rest => by
      simp only [renNF, Term.Fields.lift, lift_renN f amt (c + e) t, lift_renNF f amt c rest]

end

mutual

theorem occursAt_renN {f : ℕ → ℕ} (hf : Function.Injective f) (x : Tm) :
    ∀ (d : ℕ) (t : Tm), occursAt (renN f x) d (renN f t) = occursAt x d t
  | d, .idx k => by
      simp only [renN, occursAt, lift_renN]
      exact decide_eq_decide.mpr (renN_eq_iff hf _ (.idx k))
  | d, .node h fs => by
      simp only [renN, occursAt, lift_renN]
      rw [show decide (renN f (Term.lift 0 d x) = .node (renH f h) (renNF f fs)) =
          decide (Term.lift 0 d x = .node h fs) from decide_eq_decide.mpr (renN_eq_iff hf _ (.node h fs)),
        occursFields_renN hf x d fs]

theorem occursFields_renN {f : ℕ → ℕ} (hf : Function.Injective f) (x : Tm) :
    ∀ (d : ℕ) (fs : Fields Head), occursFields (renN f x) d (renNF f fs) = occursFields x d fs
  | _, .nil => rfl
  | d, .cons e t rest => by
      simp only [renNF, occursFields, occursAt_renN hf x (d + e) t, occursFields_renN hf x d rest]

end

mutual

theorem supportedAt_renN (f : ℕ → ℕ) :
    ∀ (d : ℕ) (t : Tm), Term.supportedAt d (renN f t) = Term.supportedAt d t
  | _, .idx _ => rfl
  | d, .node h fs => by simp only [renN, Term.supportedAt, fieldsSupportedAt_renN f d fs]

theorem fieldsSupportedAt_renN (f : ℕ → ℕ) :
    ∀ (d : ℕ) (fs : Fields Head), Term.Fields.supportedAt d (renNF f fs) = Term.Fields.supportedAt d fs
  | _, .nil => rfl
  | d, .cons e t rest => by
      simp only [renNF, Term.Fields.supportedAt, supportedAt_renN f (d + e) t, fieldsSupportedAt_renN f d rest]

end

mutual

theorem instantiateAt_renN (f : ℕ → ℕ) (v : Tm) :
    ∀ (d : ℕ) (b : Tm), Term.instantiateAt d (renN f v) (renN f b) = renN f (Term.instantiateAt d v b)
  | d, .idx k => by
      simp only [renN, Term.instantiateAt]
      split_ifs <;> simp only [renN, lift_renN]
  | d, .node h fs => by
      simp only [renN, Term.instantiateAt, fieldsInstantiateAt_renN f v d fs]

theorem fieldsInstantiateAt_renN (f : ℕ → ℕ) (v : Tm) :
    ∀ (d : ℕ) (fs : Fields Head),
      Term.Fields.instantiateAt d (renN f v) (renNF f fs) = renNF f (Term.Fields.instantiateAt d v fs)
  | _, .nil => rfl
  | d, .cons e t rest => by
      simp only [renNF, Term.Fields.instantiateAt, instantiateAt_renN f v (d + e) t,
        fieldsInstantiateAt_renN f v d rest]

end

mutual

theorem abstractAt_renN {f : ℕ → ℕ} (hf : Function.Injective f) (x : Tm) :
    ∀ (d : ℕ) (t : Tm), abstractAt (renN f x) d (renN f t) = renN f (abstractAt x d t)
  | d, .idx k => by
      simp only [renN, abstractAt, lift_renN]
      by_cases c1 : Term.lift 0 d x = .idx k
      · have c2 : renN f (Term.lift 0 d x) = .idx k := (renN_eq_iff hf _ (.idx k)).mpr c1
        rw [if_pos c2, if_pos c1]; rfl
      · have c2 : ¬ renN f (Term.lift 0 d x) = .idx k := fun e => c1 ((renN_eq_iff hf _ (.idx k)).mp e)
        rw [if_neg c2, if_neg c1]
        split_ifs <;> rfl
  | d, .node h fs => by
      simp only [renN, abstractAt, lift_renN]
      by_cases c1 : Term.lift 0 d x = .node h fs
      · have c2 : renN f (Term.lift 0 d x) = .node (renH f h) (renNF f fs) :=
          (renN_eq_iff hf _ (.node h fs)).mpr c1
        rw [if_pos c2, if_pos c1]; rfl
      · have c2 : ¬ renN f (Term.lift 0 d x) = .node (renH f h) (renNF f fs) :=
          fun e => c1 ((renN_eq_iff hf _ (.node h fs)).mp e)
        rw [if_neg c2, if_neg c1, abstractFields_renN hf x d fs]
        rfl

theorem abstractFields_renN {f : ℕ → ℕ} (hf : Function.Injective f) (x : Tm) :
    ∀ (d : ℕ) (fs : Fields Head), abstractFields (renN f x) d (renNF f fs) = renNF f (abstractFields x d fs)
  | _, .nil => rfl
  | d, .cons e t rest => by
      simp only [renNF, abstractFields, abstractAt_renN hf x (d + e) t, abstractFields_renN hf x d rest]

end

theorem lookupAt_renN {f : ℕ → ℕ} (hf : Function.Injective f) (s : List (Tm × Tm)) (d : ℕ) (t : Tm) :
    lookupAt (s.map (renPair f)) d (renN f t) = (lookupAt s d t).map (renN f) := by
  unfold lookupAt
  rw [List.find?_map]
  have e : ((fun p : Tm × Tm => decide (Term.lift 0 d p.1 = renN f t)) ∘ renPair f) =
      fun p => decide (Term.lift 0 d p.1 = t) := by
    funext p
    simp only [Function.comp, renPair, lift_renN]
    exact decide_eq_decide.mpr (renN_eq_iff hf _ _)
  rw [e]
  cases List.find? (fun p => decide (Term.lift 0 d p.1 = t)) s <;> simp [renPair, lift_renN]

mutual

theorem substAt_renN {f : ℕ → ℕ} (hf : Function.Injective f) (s : List (Tm × Tm)) :
    ∀ (d : ℕ) (t : Tm), substAt (s.map (renPair f)) d (renN f t) = renN f (substAt s d t)
  | d, .idx k => by
      have e := lookupAt_renN hf s d (.idx k)
      simp only [renN] at e
      simp only [renN, substAt, e]
      cases lookupAt s d (.idx k) <;> rfl
  | d, .node h fs => by
      have e := lookupAt_renN hf s d (.node h fs)
      simp only [renN] at e
      simp only [renN, substAt, e]
      cases lookupAt s d (.node h fs) with
      | some v => rfl
      | none => simp only [Option.map_none, renN, substFields_renN hf s d fs]

theorem substFields_renN {f : ℕ → ℕ} (hf : Function.Injective f) (s : List (Tm × Tm)) :
    ∀ (d : ℕ) (fs : Fields Head), substFields (s.map (renPair f)) d (renNF f fs) = renNF f (substFields s d fs)
  | _, .nil => rfl
  | d, .cons e t rest => by
      simp only [renNF, substFields, substAt_renN hf s (d + e) t, substFields_renN hf s d rest]

end

theorem pairOf_eq_some {t x v : Tm} : pairOf t = some (x, v) ↔ t = .node .expr (.cons 0 x (.cons 0 v .nil)) := by
  constructor
  · intro h
    unfold pairOf at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    · cases h
  · rintro rfl; rfl

theorem pairOf_renN (f : ℕ → ℕ) (t : Tm) : pairOf (renN f t) = (pairOf t).map (renPair f) := by
  cases h : pairOf t with
  | some p =>
      obtain ⟨x, v⟩ := p
      rw [pairOf_eq_some] at h
      subst h
      rfl
  | none =>
      cases h' : pairOf (renN f t) with
      | none => rfl
      | some p =>
          obtain ⟨x', v'⟩ := p
          rw [pairOf_eq_some] at h'
          exfalso
          cases t with
          | idx _ => simp [renN] at h'
          | node hd fs =>
              simp only [renN, Term.node.injEq] at h'
              obtain ⟨eh, efs⟩ := h'
              cases hd <;> simp [renH] at eh
              cases fs with
              | nil => simp [renNF] at efs
              | cons d x rest =>
                  simp only [renNF, Fields.cons.injEq] at efs
                  obtain ⟨rfl, -, erest⟩ := efs
                  cases rest with
                  | nil => simp [renNF] at erest
                  | cons e v rest2 =>
                      simp only [renNF, Fields.cons.injEq] at erest
                      obtain ⟨rfl, -, erest2⟩ := erest
                      cases rest2 with
                      | nil => simp [pairOf] at h
                      | cons _ _ _ => simp [renNF] at erest2

theorem fieldsToList_renNF (f : ℕ → ℕ) :
    ∀ fs : Fields Head, fieldsToList (renNF f fs) = (fieldsToList fs).map fun p => (p.1, renN f p.2)
  | .nil => rfl
  | .cons d t rest => by simp [renNF, fieldsToList, fieldsToList_renNF f rest]

theorem decodePairs_renN (f : ℕ → ℕ) (s : Tm) :
    decodePairs (renN f s) = (decodePairs s).map (List.map (renPair f)) := by
  cases s with
  | idx _ => rfl
  | node h fs =>
      cases h with
      | expr =>
          simp only [renN, renH, decodePairs, fieldsToList_renNF, List.mapM_map]
          apply mapM_map_of
          intro p _
          obtain ⟨d, t⟩ := p
          simp only [Function.comp]
          split_ifs <;> simp [pairOf_renN]
      | fv _ => rfl
      | sym _ => rfl
      | num _ => rfl
      | str _ => rfl
      | bind => rfl

theorem pairsClosed_renN (f : ℕ → ℕ) (pairs : List (Tm × Tm)) :
    pairsClosed (pairs.map (renPair f)) = pairsClosed pairs := by
  simp [pairsClosed, renPair, supportedAt_renN, Function.comp_def]

/-! The side conditions' functions, renamed. -/

theorem differOk_renN {f : ℕ → ℕ} (hf : Function.Injective f) (x y : Tm) :
    differOk (renN f x) (renN f y) = differOk x y := by
  simp only [differOk]
  exact decide_eq_decide.mpr (not_congr (renN_eq_iff hf x y))

theorem absentOk_renN {f : ℕ → ℕ} (hf : Function.Injective f) (x b : Tm) :
    absentOk (renN f x) (renN f b) = absentOk x b := by
  simp only [absentOk, occursIn, occursAt_renN hf]

theorem openVal_renN (f : ℕ → ℕ) (b v : Tm) : openVal (renN f b) (renN f v) = (openVal b v).map (renN f) := by
  unfold openVal
  rw [supportedAt_renN, supportedAt_renN]
  split_ifs <;> simp [openT, Term.instantiate, instantiateAt_renN]

theorem abstractVal_renN {f : ℕ → ℕ} (hf : Function.Injective f) (x b : Tm) :
    abstractVal (renN f x) (renN f b) = (abstractVal x b).map (renN f) := by
  unfold abstractVal
  rw [supportedAt_renN, supportedAt_renN]
  split_ifs <;> simp [abstractT, abstractAt_renN hf]

theorem substVal_renN {f : ℕ → ℕ} (hf : Function.Injective f) (s b : Tm) :
    substVal (renN f s) (renN f b) = (substVal s b).map (renN f) := by
  unfold substVal
  rw [decodePairs_renN]
  cases decodePairs s with
  | none => rfl
  | some pairs =>
      simp only [Option.map_some]
      rw [pairsClosed_renN, supportedAt_renN]
      split_ifs <;> simp [substT, substAt_renN hf]

/-! The relations between sets, and atom kinds, renamed. -/

theorem fieldsAtZero_renNF (f : ℕ → ℕ) :
    ∀ fs : Fields Head, fieldsAtZero (renNF f fs) = (fieldsAtZero fs).map (List.map (renN f))
  | .nil => rfl
  | .cons 0 t rest => by
      simp only [renNF, fieldsAtZero, fieldsAtZero_renNF f rest]
      cases fieldsAtZero rest <;> rfl
  | .cons (_ + 1) _ _ => rfl

theorem setMembers_eq_some {t : Tm} {ms : List Tm} :
    setMembers t = some ms ↔
      ∃ rest, t = .node .expr (.cons 0 (.node (.sym "set") .nil) rest) ∧ fieldsAtZero rest = some ms := by
  constructor
  · intro h
    unfold setMembers at h
    split at h
    · exact ⟨_, rfl, h⟩
    · cases h
  · rintro ⟨rest, rfl, h⟩
    simpa [setMembers] using h

theorem setMembers_renN (f : ℕ → ℕ) (t : Tm) :
    setMembers (renN f t) = (setMembers t).map (List.map (renN f)) := by
  cases h : setMembers t with
  | some ms =>
      obtain ⟨rest, rfl, hr⟩ := setMembers_eq_some.mp h
      simp [renN, renH, renNF, setMembers, fieldsAtZero_renNF, hr]
  | none =>
      cases h' : setMembers (renN f t) with
      | none => rfl
      | some ms' =>
          obtain ⟨rest', e, hr'⟩ := setMembers_eq_some.mp h'
          exfalso
          cases t with
          | idx _ => simp [renN] at e
          | node hd fs =>
              simp only [renN, Term.node.injEq] at e
              obtain ⟨eh, efs⟩ := e
              cases hd <;> simp [renH] at eh
              cases fs with
              | nil => simp [renNF] at efs
              | cons d x rest =>
                  simp only [renNF, Fields.cons.injEq] at efs
                  obtain ⟨rfl, ex, erest⟩ := efs
                  cases x with
                  | idx _ => simp [renN] at ex
                  | node hx fx =>
                      simp only [renN, Term.node.injEq] at ex
                      obtain ⟨ehx, efx⟩ := ex
                      cases hx <;> simp [renH] at ehx
                      subst ehx
                      cases fx with
                      | nil =>
                          rw [← erest, fieldsAtZero_renNF] at hr'
                          simp only [setMembers] at h
                          rw [h] at hr'
                          simp at hr'
                      | cons _ _ _ => simp [renNF] at efx

theorem mem_map_renN {f : ℕ → ℕ} (hf : Function.Injective f) (m : Tm) (l : List Tm) :
    renN f m ∈ l.map (renN f) ↔ m ∈ l := by
  constructor
  · intro h
    obtain ⟨m', hm', e⟩ := List.mem_map.mp h
    rwa [← renN_inj hf e]
  · exact List.mem_map_of_mem

theorem unionOfOk_renN {f : ℕ → ℕ} (hf : Function.Injective f) (u g d : Tm) :
    unionOfOk (renN f u) (renN f g) (renN f d) = unionOfOk u g d := by
  unfold unionOfOk
  rw [setMembers_renN, setMembers_renN, setMembers_renN]
  cases setMembers u <;> cases setMembers g <;> cases setMembers d <;>
    simp [List.all_map, Function.comp_def, renN_eq_iff hf]

theorem removeOfOk_renN {f : ℕ → ℕ} (hf : Function.Injective f) (r x g : Tm) :
    removeOfOk (renN f r) (renN f x) (renN f g) = removeOfOk r x g := by
  unfold removeOfOk
  rw [setMembers_renN, setMembers_renN]
  cases setMembers r <;> cases setMembers g <;>
    simp [List.all_map, Function.comp_def, renN_eq_iff hf]

theorem singletonOfOk_renN {f : ℕ → ℕ} (hf : Function.Injective f) (s x : Tm) :
    singletonOfOk (renN f s) (renN f x) = singletonOfOk s x := by
  unfold singletonOfOk
  rw [setMembers_renN]
  cases setMembers s <;> simp [List.all_map, Function.comp_def, renN_eq_iff hf]

theorem imageOfOk_renN {f : ℕ → ℕ} (hf : Function.Injective f) (h' s h : Tm) :
    imageOfOk (renN f h') (renN f s) (renN f h) = imageOfOk h' s h := by
  unfold imageOfOk
  rw [setMembers_renN, decodePairs_renN, setMembers_renN]
  cases setMembers h' with
  | none => rfl
  | some hs' =>
    cases decodePairs s with
    | none => rfl
    | some pairs =>
      cases setMembers h with
      | none => rfl
      | some hs =>
          simp only [Option.map_some, pairsClosed_renN]
          have img : (hs.map (renN f)).map (substT (pairs.map (renPair f))) =
              (hs.map (substT pairs)).map (renN f) := by
            simp only [List.map_map]
            exact List.map_congr_left fun t _ => by simp [Function.comp, substT, substAt_renN hf]
          rw [img]
          simp [List.all_map, Function.comp_def, renN_eq_iff hf, supportedAt_renN]

theorem isSymAtom_renN (f : ℕ → ℕ) (x : Tm) : isSymAtom (renN f x) = isSymAtom x := by
  cases x with
  | idx _ => rfl
  | node h fs => cases h <;> cases fs <;> rfl

theorem isNumAtom_renN (f : ℕ → ℕ) (x : Tm) : isNumAtom (renN f x) = isNumAtom x := by
  cases x with
  | idx _ => rfl
  | node h fs => cases h <;> cases fs <;> rfl

theorem isStrAtom_renN (f : ℕ → ℕ) (x : Tm) : isStrAtom (renN f x) = isStrAtom x := by
  cases x with
  | idx _ => rfl
  | node h fs => cases h <;> cases fs <;> rfl

theorem isNameAtom_renN (f : ℕ → ℕ) (x : Tm) : isNameAtom (renN f x) = isNameAtom x := by
  cases x with
  | idx _ => rfl
  | node h fs => cases h <;> cases fs <;> rfl

theorem atomKindOk_renN {f : ℕ → ℕ} (hf : Function.Injective f) (x k : Tm) :
    atomKindOk (renN f x) (renN f k) = atomKindOk x k := by
  have e : ∀ s : String, (renN f k = sym s) ↔ (k = sym s) := fun s => renN_eq_iff hf k (sym s)
  simp only [atomKindOk, isSymAtom_renN, isNumAtom_renN, isStrAtom_renN, isNameAtom_renN]
  simp only [decide_eq_decide.mpr (e "symbol"), decide_eq_decide.mpr (e "number"),
    decide_eq_decide.mpr (e "string"), decide_eq_decide.mpr (e "name")]

/-! ## A fresh name occurs in no instance of a formal -/

mutual

theorem fvs_of_occursAt (m : ℕ) :
    ∀ (e : ℕ) (t : Tm), occursAt (.node (.fv m) .nil) e t = true → m ∈ fvsOf t
  | _, .idx _, h => by simp [occursAt, Term.lift, Term.Fields.lift] at h
  | e, .node hd fs, h => by
      simp only [occursAt, Bool.or_eq_true, decide_eq_true_eq] at h
      rcases h with h | h
      · simp only [Term.lift, Term.Fields.lift, Term.node.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [fvsOf]
      · have := fvsF_of_occursFields m e fs h
        cases hd <;> simp [fvsOf, this]

theorem fvsF_of_occursFields (m : ℕ) :
    ∀ (e : ℕ) (fs : Fields Head), occursFields (.node (.fv m) .nil) e fs = true → m ∈ fvsFields fs
  | _, .nil, h => by simp [occursFields] at h
  | e, .cons e' t rest, h => by
      simp only [occursFields, Bool.or_eq_true] at h
      rcases h with h | h
      · simp [fvsFields, fvs_of_occursAt m (e + e') t h]
      · simp [fvsFields, fvsF_of_occursFields m e rest h]

end

mutual

/-- **A fresh name occurs in no instance of a formal**: if the renamed dummy `f d` occurs in a
carried term, the dummy `d` occurred in the term. -/
theorem occursAt_substN_dummy (a : List Tm) {f : ℕ → ℕ} {d : ℕ}
    (inj : ∀ k, a.length ≤ k → f k = f d → k = d) (apart : ∀ v ∈ a, f d ∉ fvsOf v) :
    ∀ (e : ℕ) (t : Tm), occursAt (.node (.fv (f d)) .nil) e (substN a f t) = true →
      occursAt (.node (.fv d) .nil) e t = true
  | _, .idx _, h => by simp [substN, occursAt, Term.lift, Term.Fields.lift] at h
  | e, .node (.fv k) fs, h => by
      simp only [substN] at h
      cases hk : a[k]? with
      | some v =>
          rw [hk] at h
          simp only [Option.getD_some] at h
          exact absurd (fvs_of_occursAt _ e v h) (apart v (List.mem_iff_getElem?.mpr ⟨k, hk⟩))
      | none =>
          rw [hk] at h
          simp only [Option.getD_none] at h
          have lk : a.length ≤ k := by simpa using hk
          simp only [occursAt, Bool.or_eq_true, decide_eq_true_eq] at h ⊢
          rcases h with h | h
          · simp only [Term.lift, Term.Fields.lift, Term.node.injEq, Head.fv.injEq] at h
            obtain ⟨efk, efs⟩ := h
            obtain rfl := inj k lk efk.symm
            cases fs with
            | nil => left; simp [Term.lift, Term.Fields.lift]
            | cons _ _ _ => simp [substNF] at efs
          · exact Or.inr (occursFields_substN_dummy a inj apart e fs h)
  | e, .node (.sym s) fs, h => by
      simp only [substN, occursAt, Bool.or_eq_true, decide_eq_true_eq] at h ⊢
      rcases h with h | h
      · simp [Term.lift, Term.Fields.lift] at h
      · exact Or.inr (occursFields_substN_dummy a inj apart e fs h)
  | e, .node (.num m) fs, h => by
      simp only [substN, occursAt, Bool.or_eq_true, decide_eq_true_eq] at h ⊢
      rcases h with h | h
      · simp [Term.lift, Term.Fields.lift] at h
      · exact Or.inr (occursFields_substN_dummy a inj apart e fs h)
  | e, .node (.str m) fs, h => by
      simp only [substN, occursAt, Bool.or_eq_true, decide_eq_true_eq] at h ⊢
      rcases h with h | h
      · simp [Term.lift, Term.Fields.lift] at h
      · exact Or.inr (occursFields_substN_dummy a inj apart e fs h)
  | e, .node .expr fs, h => by
      simp only [substN, occursAt, Bool.or_eq_true, decide_eq_true_eq] at h ⊢
      rcases h with h | h
      · simp [Term.lift, Term.Fields.lift] at h
      · exact Or.inr (occursFields_substN_dummy a inj apart e fs h)
  | e, .node .bind fs, h => by
      simp only [substN, occursAt, Bool.or_eq_true, decide_eq_true_eq] at h ⊢
      rcases h with h | h
      · simp [Term.lift, Term.Fields.lift] at h
      · exact Or.inr (occursFields_substN_dummy a inj apart e fs h)

theorem occursFields_substN_dummy (a : List Tm) {f : ℕ → ℕ} {d : ℕ}
    (inj : ∀ k, a.length ≤ k → f k = f d → k = d) (apart : ∀ v ∈ a, f d ∉ fvsOf v) :
    ∀ (e : ℕ) (fs : Fields Head), occursFields (.node (.fv (f d)) .nil) e (substNF a f fs) = true →
      occursFields (.node (.fv d) .nil) e fs = true
  | _, .nil, h => by simp [substNF, occursFields] at h
  | e, .cons e' t rest, h => by
      simp only [substNF, occursFields, Bool.or_eq_true] at h ⊢
      rcases h with h | h
      · exact Or.inl (occursAt_substN_dummy a inj apart (e + e') t h)
      · exact Or.inr (occursFields_substN_dummy a inj apart e rest h)

end

/-! ## The declared discipline -/

/-- The values mention none of the claim's formals `0 … n-1`. -/
def noFormals (n : ℕ) (vs : List Tm) : Bool := vs.all fun v => (fvsOf v).all (n ≤ ·)

/-- A value that is a dummy's name: the plain name `d`, `n ≤ d < m`. -/
def isDummyName (n m : ℕ) : Tm → Bool
  | .node (.fv d) .nil => decide (n ≤ d) && decide (d < m)
  | _ => false

/-- The claim's hypothesis `h` (instantiated by the claim's freshening `σ0`) is the side condition
`p` of a rule at the substitution `τ`. -/
def sameSide (σ0 τ : Subst ℕ Tm) (h p : Premise) : Bool :=
  h.tag == p.tag && instAll σ0 h.sideIns == instAll τ p.sideIns &&
    (h.sideOut.bind fun r => r.inst σ0) == (p.sideOut.bind fun r => r.inst τ)

/-- A claim's formal, as a plain name `j < n`. -/
def isFormalName (n : ℕ) : Tm → Bool
  | .node (.fv j) .nil => decide (j < n)
  | _ => false

/-- The claim declares the value `xv` a name: one of its hypotheses is `(atom-kind X name)` with `X`'s
value `xv`. -/
def namedByHyps (σ0 : Subst ℕ Tm) (hyps : List Premise) (xv : Tm) : Bool :=
  hyps.any fun h => match h with
    | .atomKind q k => decide (q.inst σ0 = some xv) && decide (k.inst σ0 = some (sym "name"))
    | _ => false

/-- The claim declares `(absent-from xv t)`. -/
def absentDeclared (σ0 : Subst ℕ Tm) (hyps : List Premise) (xv t : Tm) : Bool :=
  hyps.any fun h => match h with
    | .absent q1 q2 => decide (q1.inst σ0 = some xv) && decide (q2.inst σ0 = some t)
    | _ => false

/-- A name head. -/
def isFvHead : Head → Bool
  | .fv _ => true
  | _ => false

mutual

/-- **`(absent-from xv t)` derived by the structure of `t`**: `t` mentions no formal, or the claim
declares it, or `t` is a node other than a name whose parts all qualify. Example: the declared
`(absent-from x p)` and `(absent-from x q)` give `(absent-from x (f p q))`. -/
def absStruct (n : ℕ) (σ0 : Subst ℕ Tm) (hyps : List Premise) (xv : Tm) : Tm → Bool
  | .idx _ => true
  | .node h fs => noFormals n [.node h fs] || absentDeclared σ0 hyps xv (.node h fs) ||
      (!isFvHead h && absStructF n σ0 hyps xv fs)

def absStructF (n : ℕ) (σ0 : Subst ℕ Tm) (hyps : List Premise) (xv : Tm) : Fields Head → Bool
  | .nil => true
  | .cons _ c rest => absStruct n σ0 hyps xv c && absStructF n σ0 hyps xv rest

end

/-- **The discipline at one premise** (formals `0 … n-1`, dummies `n … m-1`): a `dv` condition is
decided by the declared pairs; any other side condition mentions no formal, or is `absent-from` a
dummy, or is one of the claim's hypotheses. -/
def sideOk (n m : ℕ) (σ0 τ : Subst ℕ Tm) (hyps : List Premise) (p : Premise) : Bool :=
  match p with
  | .judg _ => true
  | .given _ => true
  | .dv _ _ => true
  | .each _ _ _ => true
  | .absent x b =>
      (match x.inst τ, b.inst τ with
        | some xv, some bv => noFormals n [xv, bv] || isDummyName n m xv ||
            (isFormalName n xv && namedByHyps σ0 hyps xv && absStruct n σ0 hyps xv bv)
        | _, _ => true) || hyps.any fun h => sameSide σ0 τ h p
  | _ =>
      (match instAll τ p.sideIns with
        | some vs => noFormals n ((p.sideOut.bind fun r => r.inst τ).toList ++ vs)
        | none => true) || hyps.any fun h => sameSide σ0 τ h p

/-- The discipline at a node. -/
def nodeDisc (n m : ℕ) (σ0 : Subst ℕ Tm) (hyps : List Premise) (fr : Frame) (ru : Rule) (js : List Tm) :
    Bool :=
  match solveKinds fr ru.kinds emptySubst js with
  | some τ => ru.prems.all (sideOk n m σ0 τ hyps)
  | none => true

/-- The discipline along the walk in order. -/
def runDisc (env : Env R) (fr : Frame) (n m : ℕ) (σ0 : Subst ℕ Tm) (hyps : List Premise) (hs : List Tm) :
    List Tm → List (R × List Kid) → Bool
  | _, [] => true
  | done, (r, kids) :: rest =>
      match kids.mapM (lookupT hs done), env r with
      | some js, some ru =>
          nodeDisc n m σ0 hyps fr ru js &&
            match ruleStep fr ru js with
            | some c => runDisc env fr n m σ0 hyps hs (done ++ [c]) rest
            | none => true
      | _, _ => true

namespace Claim

/-- **The declared discipline of a claim**, any formal kinds, any dummies: an accepted claim passing
it becomes a rule; one failing it is a verdict only. -/
def declaredB (env : Env R) (c : Claim R) : Bool :=
  match c.cbHyps, c.translate with
  | some hs, some (pf, _) => runDisc env c.frame c.nformals c.nvars c.σ c.hyps hs [] pf
  | _, _ => false

end Claim

/-! ## Stability from the discipline -/

/-- What an instance provides for running a claim's proof there: the claim's hypotheses hold at
the carried freshening (`holds`), the formals are frame names (`le`), the declared pairs of plain
names hold carried (`dvFacts`), and the renaming is injective, fresh for the instance's frame and
apart from the formals' values (`inj`, `fresh`, `apart`). -/
structure InstFacts (fr fr' : Frame) (a : List Tm) (f : ℕ → ℕ) (σ0 : Subst ℕ Tm) (hyps : List Premise) :
    Prop where
  le : a.length ≤ fr.nvars
  holds : ∀ h ∈ hyps, KindHolds fr' (mapS a f σ0) h.kind
  hypsNoFv : ∀ h ∈ hyps, ∀ q ∈ h.pats, patNoFv q = true
  dvFacts : ∀ k l, (fvar k, fvar l) ∈ fr.dvs → fr'.dvOk (substN a f (fvar k)) (substN a f (fvar l)) = true
  inj : Function.Injective f
  fresh : ∀ k, a.length ≤ k → fr'.nvars ≤ f k
  apart : ∀ k, a.length ≤ k → ∀ v ∈ a, f k ∉ fvsOf v

theorem map_substN_eq_renN (a : List Tm) (f : ℕ → ℕ) {vs : List Tm} (h : noFormals a.length vs = true) :
    vs.map (substN a f) = vs.map (renN f) := by
  simp only [noFormals, List.all_eq_true, decide_eq_true_eq] at h
  exact List.map_congr_left fun v m => substN_eq_renN a f v (h v m)

theorem substN_fvar {a : List Tm} {f : ℕ → ℕ} {k : ℕ} {v : Tm} (hv : a[k]? = some v) :
    substN a f (fvar k) = v := by
  simp [fvar, flds, substN, hv]

theorem substN_fvar_past {a : List Tm} {f : ℕ → ℕ} {k : ℕ} (hk : a.length ≤ k) :
    substN a f (.node (.fv k) .nil) = .node (.fv (f k)) .nil := by
  simp [substN, List.getElem?_eq_none hk, substNF]

theorem Frame.declared_comm (fr : Frame) (x y : ℕ) : fr.declared x y = fr.declared y x := by
  simp only [Frame.declared, Bool.or_comm]

/-- **Metamath's discipline**: a distinctness condition holding in the claim's frame holds, carried,
in the instance's frame, when the declared pairs do. -/
theorem dv_stable {fr fr' : Frame} {a : List Tm} {f : ℕ → ℕ} (le : a.length ≤ fr.nvars)
    (fresh : ∀ k, a.length ≤ k → fr'.nvars ≤ f k)
    (dvFacts : ∀ k l, (fvar k, fvar l) ∈ fr.dvs → fr'.dvOk (substN a f (fvar k)) (substN a f (fvar l)) = true)
    {X Y : Tm} (h : fr.dvOk X Y = true) : fr'.dvOk (substN a f X) (substN a f Y) = true := by
  unfold Frame.dvOk at h ⊢
  rw [List.all_eq_true] at h ⊢
  intro x' hx'
  rw [List.all_eq_true]
  intro y' hy'
  rcases mem_fvs_substN a f X hx' with ⟨k, mk, v, hv, xv⟩ | ⟨k, mk, lk, rfl⟩
  · rcases mem_fvs_substN a f Y hy' with ⟨l, ml, w, hw, yw⟩ | ⟨l, ml, ll, rfl⟩
    · have lk : k < a.length := (List.getElem?_eq_some_iff.mp hv).1
      have ll : l < a.length := (List.getElem?_eq_some_iff.mp hw).1
      have hkl := List.all_eq_true.mp (h k mk) l ml
      simp only [show k < fr.nvars by omega, show l < fr.nvars by omega, decide_true, Bool.and_self,
        Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at hkl
      obtain ⟨-, decl⟩ := hkl
      simp only [Frame.declared, Bool.or_eq_true, decide_eq_true_eq] at decl
      rcases decl with dd | dd
      · have fct := dvFacts _ _ dd
        rw [substN_fvar hv, substN_fvar hw] at fct
        unfold Frame.dvOk at fct
        exact List.all_eq_true.mp (List.all_eq_true.mp fct x' xv) y' yw
      · have fct := dvFacts _ _ dd
        rw [substN_fvar hw, substN_fvar hv] at fct
        unfold Frame.dvOk at fct
        have := List.all_eq_true.mp (List.all_eq_true.mp fct y' yw) x' xv
        rw [Frame.declared_comm, Bool.and_comm (decide (y' < fr'.nvars))] at this
        simpa [ne_comm] using this
    · have := fresh l ll
      simp [show ¬ f l < fr'.nvars by omega]
  · have := fresh k lk
    simp [show ¬ f k < fr'.nvars by omega]

/-- A declared computation: the claim's hypothesis with the same inputs and result holds at the
instance. -/
theorem compute_declared {a : List Tm} {f : ℕ → ℕ} {σ0 τ : Subst ℕ Tm} {r r' : Pat}
    {ins ins' : List Pat} {g : List Tm → Option Tm} (hr' : patNoFv r' = true)
    (hins' : ∀ p ∈ ins', patNoFv p = true) (same : instAll σ0 ins' = instAll τ ins)
    (sameR : r'.inst σ0 = r.inst τ)
    (holds : ∃ vs' rv', instAll (mapS a f σ0) ins' = some vs' ∧ r'.inst (mapS a f σ0) = some rv' ∧ g vs' = some rv')
    {vs : List Tm} {rv : Tm} (hvs : instAll τ ins = some vs) (hrv : r.inst τ = some rv) :
    g (vs.map (substN a f)) = some (substN a f rv) := by
  obtain ⟨vs', rv', hv', hrv', hg'⟩ := holds
  rw [← instAll_substN a f σ0 ins' hins', same, hvs] at hv'
  rw [← inst_substN a f σ0 r' hr', sameR, hrv] at hrv'
  simp only [Option.map_some, Option.some.injEq] at hv' hrv'
  rw [hv', hrv']; exact hg'

theorem sameSide_spec {σ0 τ : Subst ℕ Tm} {h p : Premise} (hs : sameSide σ0 τ h p = true) :
    h.tag = p.tag ∧ instAll σ0 h.sideIns = instAll τ p.sideIns ∧
      (h.sideOut.bind fun r => r.inst σ0) = (p.sideOut.bind fun r => r.inst τ) := by
  simp only [sameSide, Bool.and_eq_true, beq_iff_eq] at hs
  exact ⟨hs.1.1, hs.1.2, hs.2⟩

/-! ## `absent-from` derived by structure, for a formal declared a name -/

mutual

theorem occursAt_name_depth (m : ℕ) : ∀ (d : ℕ) (t : Tm),
    occursAt (.node (.fv m) .nil) d t = occursAt (.node (.fv m) .nil) 0 t
  | _, .idx _ => by simp [occursAt, Term.lift, Term.Fields.lift]
  | d, .node h fs => by
      have l : ∀ d, Term.lift 0 d (.node (.fv m) .nil : Tm) = .node (.fv m) .nil := fun d => by
        simp [Term.lift, Term.Fields.lift]
      rw [occursAt, occursAt, l d, l 0, occursFields_name_depth m d fs]

theorem occursFields_name_depth (m : ℕ) : ∀ (d : ℕ) (fs : Fields Head),
    occursFields (.node (.fv m) .nil) d fs = occursFields (.node (.fv m) .nil) 0 fs
  | _, .nil => rfl
  | d, .cons e t rest => by
      simp only [occursFields, occursAt_name_depth m (d + e) t, occursAt_name_depth m (0 + e) t,
        occursFields_name_depth m d rest]

end

theorem substN_node_of_not_fv (a : List Tm) (f : ℕ → ℕ) {h : Head} (hh : isFvHead h = false)
    (fs : Fields Head) : substN a f (.node h fs) = .node h (substNF a f fs) := by
  cases h <;> simp_all [isFvHead, substN]

mutual

/-- **The structural derivation is sound**: the instance `m` of a formal declared a name occurs in
no instance of a term that `absStruct` accepts. -/
theorem absStruct_sound {a : List Tm} {f : ℕ → ℕ} {σ0 : Subst ℕ Tm} {hyps : List Premise} {xv : Tm}
    {m : ℕ} (hxm : substN a f xv = .node (.fv m) .nil) (hm : ∀ k, a.length ≤ k → f k ≠ m)
    (decl : ∀ t, absentDeclared σ0 hyps xv t = true → absentOk (substN a f xv) (substN a f t) = true) :
    ∀ (t : Tm) (d : ℕ), absStruct a.length σ0 hyps xv t = true →
      occursAt (.node (.fv m) .nil) d (substN a f t) = false
  | .idx _, _, _ => by simp [substN, occursAt, Term.lift, Term.Fields.lift]
  | .node h fs, d, st => by
      simp only [absStruct, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at st
      rcases st with (free | dec) | ⟨hh, sub⟩
      · cases e : occursAt (.node (.fv m) .nil) d (substN a f (.node h fs)) with
        | false => rfl
        | true =>
            have mem := fvs_of_occursAt m d _ e
            simp only [noFormals, List.all_cons, List.all_nil, Bool.and_true, List.all_eq_true,
              decide_eq_true_eq] at free
            rcases mem_fvs_substN a f _ mem with ⟨k, mk, v, hv, -⟩ | ⟨k, mk, lk, rfl⟩
            · have := free k mk
              have := (List.getElem?_eq_some_iff.mp hv).1
              omega
            · exact absurd rfl (hm k lk)
      · have ok := decl _ dec
        rw [hxm] at ok
        simp only [absentOk, occursIn, Bool.not_eq_true'] at ok
        rw [occursAt_name_depth]
        exact ok
      · rw [substN_node_of_not_fv a f hh]
        simp only [occursAt, Term.lift, Term.Fields.lift, Bool.or_eq_false_iff]
        refine ⟨?_, absStructF_sound hxm hm decl fs d sub⟩
        apply decide_eq_false
        intro e
        simp only [Term.node.injEq] at e
        cases h <;> simp_all [isFvHead]

theorem absStructF_sound {a : List Tm} {f : ℕ → ℕ} {σ0 : Subst ℕ Tm} {hyps : List Premise} {xv : Tm}
    {m : ℕ} (hxm : substN a f xv = .node (.fv m) .nil) (hm : ∀ k, a.length ≤ k → f k ≠ m)
    (decl : ∀ t, absentDeclared σ0 hyps xv t = true → absentOk (substN a f xv) (substN a f t) = true) :
    ∀ (fs : Fields Head) (d : ℕ), absStructF a.length σ0 hyps xv fs = true →
      occursFields (.node (.fv m) .nil) d (substNF a f fs) = false
  | .nil, _, _ => rfl
  | .cons e c rest, d, st => by
      simp only [absStructF, Bool.and_eq_true] at st
      simp only [substNF, occursFields, Bool.or_eq_false_iff]
      exact ⟨absStruct_sound hxm hm decl c (d + e) st.1, absStructF_sound hxm hm decl rest d st.2⟩

end

/-- **`absent-from` derived by structure holds at every instance**, for a formal the claim declares a
name. -/
theorem absent_struct_stable {fr fr' : Frame} {a : List Tm} {f : ℕ → ℕ} {σ0 : Subst ℕ Tm}
    {hyps : List Premise} (F : InstFacts fr fr' a f σ0 hyps) {xv bv : Tm}
    (fx : isFormalName a.length xv = true) (named : namedByHyps σ0 hyps xv = true)
    (st : absStruct a.length σ0 hyps xv bv = true) :
    absentOk (substN a f xv) (substN a f bv) = true := by
  -- the formal and its value at the instance
  obtain ⟨j, rfl, lj⟩ : ∃ j, xv = .node (.fv j) .nil ∧ j < a.length := by
    cases xv with
    | idx _ => simp [isFormalName] at fx
    | node hd fs =>
        cases hd <;> cases fs <;> simp_all [isFormalName]
  have hj : a[j]? = some a[j] := List.getElem?_eq_getElem lj
  have hxj : substN a f (.node (.fv j) .nil) = a[j] := by simp [substN, hj]
  -- the claim declares it a name, so its value is a name
  obtain ⟨h, mh, hn⟩ := List.any_eq_true.mp named
  cases h
  case atomKind q k =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hn
    obtain ⟨hq, hk⟩ := hn
    have hh := F.holds _ mh
    simp only [Premise.kind, KindHolds] at hh
    obtain ⟨vs, hvs, hok⟩ := hh
    have nq := F.hypsNoFv _ mh q (by simp [Premise.pats])
    have nk := F.hypsNoFv _ mh k (by simp [Premise.pats])
    have iq : q.inst (mapS a f σ0) = some a[j] := by
      rw [← inst_substN a f σ0 q nq, hq, ← hxj]; rfl
    have ik : k.inst (mapS a f σ0) = some (sym "name") := by
      rw [← inst_substN a f σ0 k nk, hk]; rfl
    simp only [instAll, iq, ik, Option.some.injEq] at hvs
    subst hvs
    have hname : isNameAtom a[j] = true := by
      simpa [atomKindOk, sym] using hok
    obtain ⟨m, hm⟩ : ∃ m, a[j] = .node (.fv m) .nil := by
      revert hname
      cases a[j] with
      | idx _ => simp [isNameAtom]
      | node hd fs => cases hd <;> cases fs <;> simp [isNameAtom]
    have hxm : substN a f (.node (.fv j) .nil) = .node (.fv m) .nil := by rw [hxj, hm]
    have apart : ∀ k, a.length ≤ k → f k ≠ m := by
      intro k lk e
      have := F.apart k lk a[j] (List.getElem_mem lj)
      rw [hm, e] at this
      simp [fvsOf, fvsFields] at this
    have decl : ∀ t, absentDeclared σ0 hyps (.node (.fv j) .nil) t = true →
        absentOk (substN a f (.node (.fv j) .nil)) (substN a f t) = true := by
      intro t dt
      obtain ⟨h', mh', hd⟩ := List.any_eq_true.mp dt
      cases h'
      case absent q1 q2 =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hd
        obtain ⟨h1, h2⟩ := hd
        have hh' := F.holds _ mh'
        simp only [Premise.kind, KindHolds] at hh'
        obtain ⟨vs', hvs', hok'⟩ := hh'
        have n1 := F.hypsNoFv _ mh' q1 (by simp [Premise.pats])
        have n2 := F.hypsNoFv _ mh' q2 (by simp [Premise.pats])
        have i1 : q1.inst (mapS a f σ0) = some (substN a f (.node (.fv j) .nil)) := by
          rw [← inst_substN a f σ0 q1 n1, h1]; rfl
        have i2 : q2.inst (mapS a f σ0) = some (substN a f t) := by
          rw [← inst_substN a f σ0 q2 n2, h2]; rfl
        simp only [instAll, i1, i2, Option.some.injEq] at hvs'
        subst hvs'
        exact hok'
      all_goals simp at hd
    have sound := absStruct_sound hxm apart decl bv 0 st
    rw [hxm]
    simp [absentOk, occursIn, sound]
  all_goals simp at hn

/-- **The discipline at a premise makes its kind stable** at every instance. -/
theorem stable_of_sideOk {fr fr' : Frame} {a : List Tm} {f : ℕ → ℕ} {σ0 τ : Subst ℕ Tm}
    {hyps : List Premise} {m : ℕ} (F : InstFacts fr fr' a f σ0 hyps) {p : Premise}
    (nf : ∀ q ∈ p.pats, patNoFv q = true) (ok : sideOk a.length m σ0 τ hyps p = true) :
    KindStable fr fr' a f τ p.kind := by
  cases p with
  | each x l p => exact ⟨nf l (by simp [Premise.pats]), nf p (by simp [Premise.pats])⟩
  | judg q => exact nf q (by simp [Premise.pats])
  | given q =>
      show patNoFv (givenPat q) = true
      simp [givenPat, pjd, pex, pflds, psym, patNoFv, patFieldsNoFv, nf q (by simp [Premise.pats])]
  | dv x y =>
      refine ⟨fun q mq => nf q (by simpa [Premise.pats] using mq), fun vs _ hok => ?_⟩
      rcases vs with _ | ⟨X, _ | ⟨Y, _ | ⟨Z, rest⟩⟩⟩
      · simp at hok
      · simp at hok
      · exact dv_stable F.le F.fresh F.dvFacts hok
      · simp at hok
  | differ x y =>
      refine ⟨fun q mq => nf q (by simpa [Premise.pats] using mq), fun vs hvs hok => ?_⟩
      simp only [sideOk, Bool.or_eq_true, List.any_eq_true] at ok
      rcases ok with free | ⟨h, mh, hs⟩
      · simp only [Premise.sideIns, Premise.sideOut, Option.bind_none, Option.toList_none,
          List.nil_append, hvs] at free
        rw [map_substN_eq_renN a f free]
        rcases vs with _ | ⟨X, _ | ⟨Y, _ | ⟨Z, rest⟩⟩⟩
        · simp at hok
        · simp at hok
        · simpa [differOk_renN F.inj] using hok
        · simp at hok
      · obtain ⟨tag, ins, -⟩ := sameSide_spec hs
        cases h <;> simp [Premise.tag] at tag
        rename_i x' y'
        have hh := F.holds _ mh
        simp only [Premise.kind, KindHolds] at hh
        simp only [Premise.sideIns] at ins
        obtain ⟨vs', hv', hok'⟩ := hh
        rw [← instAll_substN a f σ0 [x', y']
          (fun q mq => F.hypsNoFv _ mh q (by simpa [Premise.pats] using mq)), ins, hvs] at hv'
        simp only [Option.map_some, Option.some.injEq] at hv'
        rw [hv']
        exact hok'
  | absent x b =>
      refine ⟨fun q mq => nf q (by simpa [Premise.pats] using mq), fun vs hvs hok => ?_⟩
      simp only [sideOk, Bool.or_eq_true, List.any_eq_true] at ok
      have hvs' := hvs
      simp only [instAll] at hvs'
      cases hx : x.inst τ with
      | none => rw [hx] at hvs'; simp at hvs'
      | some xv =>
        cases hb : b.inst τ with
        | none => rw [hx, hb] at hvs'; simp at hvs'
        | some bv =>
          rw [hx, hb] at hvs'
          simp only [Option.some.injEq] at hvs'
          subst hvs'
          rcases ok with free | ⟨h, mh, hs⟩
          · rw [hx, hb] at free
            simp only [Bool.or_eq_true, Bool.and_eq_true] at free
            simp only [List.map_cons, List.map_nil] at hok ⊢
            rcases free with (free | dummy) | ⟨⟨fx, named⟩, st⟩
            · have e := map_substN_eq_renN a f free
              simp only [List.map_cons, List.map_nil, List.cons.injEq] at e
              rw [e.1, e.2.1, absentOk_renN F.inj]
              exact hok
            · -- `absent-from` a dummy: a fresh name occurs in no instance of a formal
              cases xv with
              | idx _ => simp [isDummyName] at dummy
              | node hd fs =>
                cases hd with
                | fv d =>
                  cases fs with
                  | cons _ _ _ => simp [isDummyName] at dummy
                  | nil =>
                    simp only [isDummyName, Bool.and_eq_true, decide_eq_true_eq] at dummy
                    rw [substN_fvar_past dummy.1]
                    simp only [absentOk, occursIn, Bool.not_eq_true'] at hok ⊢
                    cases e : occursAt (.node (.fv (f d)) .nil) 0 (substN a f bv) with
                    | false => rfl
                    | true =>
                        have := occursAt_substN_dummy a (fun k _ e' => F.inj e') (F.apart d dummy.1) 0 bv e
                        rw [this] at hok
                        cases hok
                | sym _ => simp [isDummyName] at dummy
                | num _ => simp [isDummyName] at dummy
                | str _ => simp [isDummyName] at dummy
                | expr => simp [isDummyName] at dummy
                | bind => simp [isDummyName] at dummy
            · exact absent_struct_stable F fx named st
          · obtain ⟨tag, ins, -⟩ := sameSide_spec hs
            cases h <;> simp [Premise.tag] at tag
            rename_i x' b'
            have hh := F.holds _ mh
            simp only [Premise.kind, KindHolds] at hh
            simp only [Premise.sideIns] at ins
            obtain ⟨vs', hv', hok'⟩ := hh
            rw [← instAll_substN a f σ0 [x', b']
              (fun q mq => F.hypsNoFv _ mh q (by simpa [Premise.pats] using mq)), ins, hvs] at hv'
            simp only [Option.map_some, Option.some.injEq] at hv'
            rw [hv']
            exact hok'
  | isOpen r b v =>
      refine ⟨nf r (by simp [Premise.pats]), fun q mq => nf q (by simp [Premise.pats] at mq ⊢; tauto),
        fun vs rv hvs hrv hg => ?_⟩
      simp only [sideOk, Bool.or_eq_true, List.any_eq_true] at ok
      rcases ok with free | ⟨h, mh, hs⟩
      · simp only [Premise.sideIns, Premise.sideOut, Option.bind_some, hrv, Option.toList_some,
          List.singleton_append, hvs] at free
        have both := map_substN_eq_renN a f free
        simp only [List.map_cons] at both
        obtain ⟨erv, evs⟩ := List.cons.inj both
        rw [evs, erv]
        rcases vs with _ | ⟨B, _ | ⟨V, _ | ⟨Z, rest⟩⟩⟩
        · simp at hg
        · simp at hg
        · simp only [List.map_cons, List.map_nil] at hg ⊢
          rw [openVal_renN, hg]; rfl
        · simp at hg
      · obtain ⟨tag, ins, outs⟩ := sameSide_spec hs
        cases h <;> simp [Premise.tag] at tag
        rename_i r' b' v'
        have hh := F.holds _ mh
        simp only [Premise.kind, KindHolds] at hh
        simp only [Premise.sideIns] at ins
        simp only [Premise.sideOut, Option.bind_some] at outs
        exact compute_declared (ins' := [b', v']) (F.hypsNoFv _ mh r' (by simp [Premise.pats]))
          (fun q mq => F.hypsNoFv _ mh q (by simp [Premise.pats] at mq ⊢; tauto)) ins outs hh hvs hrv
  | isAbstract r x b =>
      refine ⟨nf r (by simp [Premise.pats]), fun q mq => nf q (by simp [Premise.pats] at mq ⊢; tauto),
        fun vs rv hvs hrv hg => ?_⟩
      simp only [sideOk, Bool.or_eq_true, List.any_eq_true] at ok
      rcases ok with free | ⟨h, mh, hs⟩
      · simp only [Premise.sideIns, Premise.sideOut, Option.bind_some, hrv, Option.toList_some,
          List.singleton_append, hvs] at free
        have both := map_substN_eq_renN a f free
        simp only [List.map_cons] at both
        obtain ⟨erv, evs⟩ := List.cons.inj both
        rw [evs, erv]
        rcases vs with _ | ⟨X, _ | ⟨B, _ | ⟨Z, rest⟩⟩⟩
        · simp at hg
        · simp at hg
        · simp only [List.map_cons, List.map_nil] at hg ⊢
          rw [abstractVal_renN F.inj, hg]; rfl
        · simp at hg
      · obtain ⟨tag, ins, outs⟩ := sameSide_spec hs
        cases h <;> simp [Premise.tag] at tag
        rename_i r' x' b'
        have hh := F.holds _ mh
        simp only [Premise.kind, KindHolds] at hh
        simp only [Premise.sideIns] at ins
        simp only [Premise.sideOut, Option.bind_some] at outs
        exact compute_declared (ins' := [x', b']) (F.hypsNoFv _ mh r' (by simp [Premise.pats]))
          (fun q mq => F.hypsNoFv _ mh q (by simp [Premise.pats] at mq ⊢; tauto)) ins outs hh hvs hrv
  | isSubst r s b =>
      refine ⟨nf r (by simp [Premise.pats]), fun q mq => nf q (by simp [Premise.pats] at mq ⊢; tauto),
        fun vs rv hvs hrv hg => ?_⟩
      simp only [sideOk, Bool.or_eq_true, List.any_eq_true] at ok
      rcases ok with free | ⟨h, mh, hs⟩
      · simp only [Premise.sideIns, Premise.sideOut, Option.bind_some, hrv, Option.toList_some,
          List.singleton_append, hvs] at free
        have both := map_substN_eq_renN a f free
        simp only [List.map_cons] at both
        obtain ⟨erv, evs⟩ := List.cons.inj both
        rw [evs, erv]
        rcases vs with _ | ⟨S, _ | ⟨B, _ | ⟨Z, rest⟩⟩⟩
        · simp at hg
        · simp at hg
        · simp only [List.map_cons, List.map_nil] at hg ⊢
          rw [substVal_renN F.inj, hg]; rfl
        · simp at hg
      · obtain ⟨tag, ins, outs⟩ := sameSide_spec hs
        cases h <;> simp [Premise.tag] at tag
        rename_i r' s' b'
        have hh := F.holds _ mh
        simp only [Premise.kind, KindHolds] at hh
        simp only [Premise.sideIns] at ins
        simp only [Premise.sideOut, Option.bind_some] at outs
        exact compute_declared (ins' := [s', b']) (F.hypsNoFv _ mh r' (by simp [Premise.pats]))
          (fun q mq => F.hypsNoFv _ mh q (by simp [Premise.pats] at mq ⊢; tauto)) ins outs hh hvs hrv
  | unionOf u g d =>
      refine ⟨fun q mq => nf q (by simpa [Premise.pats] using mq), fun vs hvs hok => ?_⟩
      simp only [sideOk, Bool.or_eq_true, List.any_eq_true] at ok
      rcases ok with free | ⟨h, mh, hs⟩
      · simp only [Premise.sideIns, Premise.sideOut, Option.bind_none, Option.toList_none,
          List.nil_append, hvs] at free
        rw [map_substN_eq_renN a f free]
        rcases vs with _ | ⟨U, _ | ⟨G, _ | ⟨D, _ | ⟨Z, rest⟩⟩⟩⟩
        · simp at hok
        · simp at hok
        · simp at hok
        · simpa [unionOfOk_renN F.inj] using hok
        · simp at hok
      · obtain ⟨tag, ins, -⟩ := sameSide_spec hs
        cases h <;> simp [Premise.tag] at tag
        rename_i u' g' d'
        have hh := F.holds _ mh
        simp only [Premise.kind, KindHolds] at hh
        simp only [Premise.sideIns] at ins
        obtain ⟨vs', hv', hok'⟩ := hh
        rw [← instAll_substN a f σ0 [u', g', d']
          (fun q mq => F.hypsNoFv _ mh q (by simpa [Premise.pats] using mq)), ins, hvs] at hv'
        simp only [Option.map_some, Option.some.injEq] at hv'
        rw [hv']
        exact hok'
  | removeOf r x g =>
      refine ⟨fun q mq => nf q (by simpa [Premise.pats] using mq), fun vs hvs hok => ?_⟩
      simp only [sideOk, Bool.or_eq_true, List.any_eq_true] at ok
      rcases ok with free | ⟨h, mh, hs⟩
      · simp only [Premise.sideIns, Premise.sideOut, Option.bind_none, Option.toList_none,
          List.nil_append, hvs] at free
        rw [map_substN_eq_renN a f free]
        rcases vs with _ | ⟨R', _ | ⟨X, _ | ⟨G, _ | ⟨Z, rest⟩⟩⟩⟩
        · simp at hok
        · simp at hok
        · simp at hok
        · simpa [removeOfOk_renN F.inj] using hok
        · simp at hok
      · obtain ⟨tag, ins, -⟩ := sameSide_spec hs
        cases h <;> simp [Premise.tag] at tag
        rename_i r' x' g'
        have hh := F.holds _ mh
        simp only [Premise.kind, KindHolds] at hh
        simp only [Premise.sideIns] at ins
        obtain ⟨vs', hv', hok'⟩ := hh
        rw [← instAll_substN a f σ0 [r', x', g']
          (fun q mq => F.hypsNoFv _ mh q (by simpa [Premise.pats] using mq)), ins, hvs] at hv'
        simp only [Option.map_some, Option.some.injEq] at hv'
        rw [hv']
        exact hok'
  | singletonOf s x =>
      refine ⟨fun q mq => nf q (by simpa [Premise.pats] using mq), fun vs hvs hok => ?_⟩
      simp only [sideOk, Bool.or_eq_true, List.any_eq_true] at ok
      rcases ok with free | ⟨h, mh, hs⟩
      · simp only [Premise.sideIns, Premise.sideOut, Option.bind_none, Option.toList_none,
          List.nil_append, hvs] at free
        rw [map_substN_eq_renN a f free]
        rcases vs with _ | ⟨S, _ | ⟨X, _ | ⟨Z, rest⟩⟩⟩
        · simp at hok
        · simp at hok
        · simpa [singletonOfOk_renN F.inj] using hok
        · simp at hok
      · obtain ⟨tag, ins, -⟩ := sameSide_spec hs
        cases h <;> simp [Premise.tag] at tag
        rename_i s' x'
        have hh := F.holds _ mh
        simp only [Premise.kind, KindHolds] at hh
        simp only [Premise.sideIns] at ins
        obtain ⟨vs', hv', hok'⟩ := hh
        rw [← instAll_substN a f σ0 [s', x']
          (fun q mq => F.hypsNoFv _ mh q (by simpa [Premise.pats] using mq)), ins, hvs] at hv'
        simp only [Option.map_some, Option.some.injEq] at hv'
        rw [hv']
        exact hok'
  | imageOf h₁ s h₂ =>
      refine ⟨fun q mq => nf q (by simpa [Premise.pats] using mq), fun vs hvs hok => ?_⟩
      simp only [sideOk, Bool.or_eq_true, List.any_eq_true] at ok
      rcases ok with free | ⟨h, mh, hs⟩
      · simp only [Premise.sideIns, Premise.sideOut, Option.bind_none, Option.toList_none,
          List.nil_append, hvs] at free
        rw [map_substN_eq_renN a f free]
        rcases vs with _ | ⟨H1, _ | ⟨S, _ | ⟨H2, _ | ⟨Z, rest⟩⟩⟩⟩
        · simp at hok
        · simp at hok
        · simp at hok
        · simpa [imageOfOk_renN F.inj] using hok
        · simp at hok
      · obtain ⟨tag, ins, -⟩ := sameSide_spec hs
        cases h <;> simp [Premise.tag] at tag
        rename_i h₁' s' h₂'
        have hh := F.holds _ mh
        simp only [Premise.kind, KindHolds] at hh
        simp only [Premise.sideIns] at ins
        obtain ⟨vs', hv', hok'⟩ := hh
        rw [← instAll_substN a f σ0 [h₁', s', h₂']
          (fun q mq => F.hypsNoFv _ mh q (by simpa [Premise.pats] using mq)), ins, hvs] at hv'
        simp only [Option.map_some, Option.some.injEq] at hv'
        rw [hv']
        exact hok'
  | atomKind x k =>
      refine ⟨fun q mq => nf q (by simpa [Premise.pats] using mq), fun vs hvs hok => ?_⟩
      simp only [sideOk, Bool.or_eq_true, List.any_eq_true] at ok
      rcases ok with free | ⟨h, mh, hs⟩
      · simp only [Premise.sideIns, Premise.sideOut, Option.bind_none, Option.toList_none,
          List.nil_append, hvs] at free
        rw [map_substN_eq_renN a f free]
        rcases vs with _ | ⟨X, _ | ⟨K, _ | ⟨Z, rest⟩⟩⟩
        · simp at hok
        · simp at hok
        · simpa [atomKindOk_renN F.inj] using hok
        · simp at hok
      · obtain ⟨tag, ins, -⟩ := sameSide_spec hs
        cases h <;> simp [Premise.tag] at tag
        rename_i x' k'
        have hh := F.holds _ mh
        simp only [Premise.kind, KindHolds] at hh
        simp only [Premise.sideIns] at ins
        obtain ⟨vs', hv', hok'⟩ := hh
        rw [← instAll_substN a f σ0 [x', k']
          (fun q mq => F.hypsNoFv _ mh q (by simpa [Premise.pats] using mq)), ins, hvs] at hv'
        simp only [Option.map_some, Option.some.injEq] at hv'
        rw [hv']
        exact hok'

/-! ## The claim's proof runs at every instance -/

theorem lookupT_substN (a : List Tm) (f : ℕ → ℕ) (hs done : List Tm) (k : Kid) :
    lookupT (hs.map (substN a f)) (done.map (substN a f)) k = (lookupT hs done k).map (substN a f) := by
  cases k <;> simp [lookupT]

/-- **The claim's proof runs at every instance**: the walk in the claim's frame, carried, is the walk
in the instance's frame, when the discipline holds along it. -/
theorem runT_subst (env : Env R) (envNoFv : EnvNoFv env) {fr fr' : Frame} {a : List Tm} {f : ℕ → ℕ}
    {σ0 : Subst ℕ Tm} {hyps : List Premise} {m : ℕ} (F : InstFacts fr fr' a f σ0 hyps) (hs : List Tm) :
    ∀ (done : List Tm) (pf : List (R × List Kid)) (out : List Tm),
      runT env fr hs done pf = some out → runDisc env fr a.length m σ0 hyps hs done pf = true →
        runT env fr' (hs.map (substN a f)) (done.map (substN a f)) pf = some (out.map (substN a f))
  | done, [], out, h, _ => by
      simp only [runT, Option.some.injEq] at h ⊢
      rw [h]
  | done, (r, kids) :: rest, out, h, disc => by
      simp only [runT, nodeStep] at h
      simp only [runDisc] at disc
      cases hk : kids.mapM (lookupT hs done) with
      | none => rw [hk] at h; simp at h
      | some js =>
          cases he : env r with
          | none => rw [hk, he] at h; simp at h
          | some ru =>
              rw [hk, he] at h disc
              simp only at h disc
              cases hc : ruleStep fr ru js with
              | none => rw [hc] at h; simp at h
              | some c =>
                  rw [hc] at h disc
                  simp only [Bool.and_eq_true] at disc
                  obtain ⟨nd, disc⟩ := disc
                  have nf := envNoFv r ru he
                  have hk' : kids.mapM (lookupT (hs.map (substN a f)) (done.map (substN a f))) =
                      some (js.map (substN a f)) := by
                    rw [mapM_map_of (substN a f) kids fun k _ => lookupT_substN a f hs done k, hk]; rfl
                  have hc' : ruleStep fr' ru (js.map (substN a f)) = some (substN a f c) := by
                    refine ruleStep_subst fr fr' a f hc nf.2 fun τ hτ k mk => ?_
                    simp only [nodeDisc, hτ, List.all_eq_true] at nd
                    simp only [Rule.kinds, List.mem_map] at mk
                    obtain ⟨p, mp, rfl⟩ := mk
                    exact stable_of_sideOk F (nf.1 p mp) (nd p mp)
                  have ih := runT_subst env envNoFv F hs (done ++ [c]) rest out h disc
                  simp only [List.map_append, List.map_cons, List.map_nil] at ih
                  simp only [runT, nodeStep, hk', he, hc']
                  exact ih

/-! ## Claims as rules -/

/-- The patterns of a list instantiate to values each of which some pattern gives. -/
theorem instAll_mem (σ : Subst ℕ Tm) :
    ∀ {ps : List Pat} {vs : List Tm}, instAll σ ps = some vs → ∀ k ∈ vs, ∃ p ∈ ps, p.inst σ = some k
  | [], vs, h, k, m => by
      simp only [instAll, Option.some.injEq] at h; subst h; simp at m
  | p :: ps, vs, h, k, m => by
      simp only [instAll] at h
      cases hp : p.inst σ with
      | none => rw [hp] at h; simp at h
      | some t =>
          cases hr : instAll σ ps with
          | none => rw [hp, hr] at h; simp at h
          | some ts =>
              rw [hp, hr] at h
              simp only [Option.some.injEq] at h
              subst h
              rcases List.mem_cons.mp m with rfl | m
              · exact ⟨p, List.mem_cons_self, hp⟩
              · obtain ⟨q, mq, iq⟩ := instAll_mem σ hr k m
                exact ⟨q, List.mem_cons_of_mem _ mq, iq⟩

theorem instAll_append_some {σ : Subst ℕ Tm} {ps qs : List Pat} {vs : List Tm}
    (h : instAll σ (ps ++ qs) = some vs) :
    ∃ va vb, instAll σ ps = some va ∧ instAll σ qs = some vb ∧ vs = va ++ vb := by
  rw [Claim.instAll_append] at h
  cases ha : instAll σ ps with
  | none => rw [ha] at h; simp at h
  | some va =>
      cases hb : instAll σ qs with
      | none => rw [ha, hb] at h; simp at h
      | some vb =>
          rw [ha, hb] at h
          simp only [Option.bind_some, Option.map_some, Option.some.injEq] at h
          exact ⟨va, vb, rfl, rfl, h.symm⟩

theorem mem_judgPats : ∀ {hyps : List Premise} {p : Pat}, p ∈ judgPats hyps → Premise.judg p ∈ hyps
  | [], _, m => by simp [judgPats] at m
  | h :: hs, p, m => by
      cases hj : h.judgPat? with
      | none =>
          simp only [judgPats, hj] at m
          exact List.mem_cons_of_mem _ (mem_judgPats m)
      | some q =>
          simp only [judgPats, hj, List.mem_cons] at m
          rcases m with rfl | m
          · cases h <;> simp [Premise.judgPat?] at hj
            subst hj
            exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (mem_judgPats m)

theorem inst_givenPat (σ : Subst ℕ Tm) (p : Pat) : (givenPat p).inst σ = (p.inst σ).map givenTm := by
  simp only [givenPat, pjd, pex, pflds, psym, TreePat.inst, TreePatFields.inst]
  cases p.inst σ <;> rfl

theorem inst_localPat (σ : Subst ℕ Tm) (s : String) (d : ℕ) :
    (pjd s [pv d]).inst σ = (σ d).map fun v => jd s [v] := by
  simp only [pjd, pex, pflds, psym, pv, TreePat.inst, TreePatFields.inst]
  cases σ d <;> rfl

theorem derivable_mono {P : Presentation.{0}} {hyps hyps' : List P.J} {j : P.J} (h : Derivable P hyps j)
    (sub : ∀ k ∈ hyps, k ∈ hyps') : Derivable P hyps' j :=
  h.cut fun k m => Derivable.hyp (sub k m)

/-- Every claim variable's value is a name, plain or over names. -/
theorem value_head (κ : FormalKind) (k : ℕ) : ∃ fs, κ.value k = .node (.fv k) fs := by
  cases κ <;> exact ⟨_, rfl⟩

namespace Claim

/-- The claim's statement and stored terms mention no claim name. -/
def noFvB (c : Claim R) : Bool :=
  patNoFv c.concl && c.hyps.all (fun p => p.pats.all patNoFv) &&
    c.terms.all (fun x => patNoFv x.2) && c.dvl.all (fun pq => patNoFv pq.1 && patNoFv pq.2)

/-- **The stored terms of a claim at the values `θ`**, as `given` judgments. -/
def givensAt (c : Claim R) (θ : Subst ℕ Tm) : Option (List Tm) :=
  instAll θ (c.terms.map fun x => givenPat x.2)

/-- **The locals of a claim at the values `θ`**: each dummy's sort. -/
def localsAt (c : Claim R) (θ : Subst ℕ Tm) : Option (List Tm) :=
  instAll θ (c.locals.map fun l => pjd l.1 [pv l.2])

theorem vals_getElem? (c : Claim R) (v : ℕ) :
    c.vals[v]? = ((c.formals ++ c.dummies)[v]?).map fun κ => κ.value v := by
  simp [vals, List.getElem?_mapIdx]

/-- The carried freshening gives each formal its value. -/
theorem mapS_formal (c : Claim R) {a : List Tm} (f : ℕ → ℕ) (len : a.length = c.nformals) {v : ℕ}
    (lt : v < c.nformals) : mapS a f c.σ v = a[v]? := by
  simp only [mapS, σ, substOf, vals_getElem?]
  rw [List.getElem?_append_left (by simpa [nformals] using lt)]
  have hv : v < c.formals.length := by simpa [nformals] using lt
  rw [List.getElem?_eq_getElem hv]
  obtain ⟨fs, e⟩ := value_head c.formals[v] v
  have ha : a[v]? = some a[v] := List.getElem?_eq_getElem (by omega)
  simp [e, substN, ha]

theorem nformals_le (c : Claim R) : c.nformals ≤ c.nvars := by simp [nformals, nvars]

theorem stmt_facts {c : Claim R} (h : c.wellFormed = true) :
    premsVars c.hyps ⊆ Finset.range c.nformals ∧ c.concl.vars ⊆ Finset.range c.nformals ∧
      (∀ l ∈ c.locals, c.isDummy l.2 = true) ∧
      (∀ pq ∈ c.dvl, (c.patIsDummy pq.1 || c.patIsDummy pq.2) = true) := by
  simp only [wellFormed, stmtOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, hp⟩, hc⟩, -⟩, hl⟩, hd⟩, -⟩, -⟩, -⟩ := h
  exact ⟨hp, hc, hl, hd⟩

end Claim

/-- A name occurring in no value of `a` and past every frame name. -/
def nameBound (a : List Tm) : ℕ := (a.flatMap fvsOf).foldr max 0 + 1

theorem le_foldr_max : ∀ (l : List ℕ) (z : ℕ), z ∈ l → z ≤ l.foldr max 0
  | [], _, m => by simp at m
  | x :: l, z, m => by
      rcases List.mem_cons.mp m with rfl | m
      · simp
      · have := le_foldr_max l z m
        simp only [List.foldr_cons]
        omega

theorem lt_nameBound {a : List Tm} {v : Tm} (hv : v ∈ a) {z : ℕ} (hz : z ∈ fvsOf v) : z < nameBound a := by
  have := le_foldr_max (a.flatMap fvsOf) z (List.mem_flatMap.mpr ⟨v, hv, hz⟩)
  simp only [nameBound]
  omega

/-- A sort judgment about a name past the frame: a dummy's local, at a fresh name. -/
def IsLocalFact (sorts : List String) (fr : Frame) (j : Tm) : Prop :=
  ∃ s ∈ sorts, ∃ m fs, j = jd s [.node (.fv m) fs] ∧ fr.nvars ≤ m

/-- A `given` judgment: a cited term. -/
def IsGiven (j : Tm) : Prop := ∃ t, j = givenTm t

theorem givensAt_isGiven {c : Claim R} {θ : Subst ℕ Tm} {gs : List Tm} (h : c.givensAt θ = some gs) :
    ∀ g ∈ gs, IsGiven g := by
  intro g m
  obtain ⟨p, mp, ip⟩ := instAll_mem θ h g m
  obtain ⟨x, -, rfl⟩ := List.mem_map.mp mp
  rw [inst_givenPat] at ip
  cases hx : x.2.inst θ with
  | none => rw [hx] at ip; simp at ip
  | some t => rw [hx] at ip; simp only [Option.map_some, Option.some.injEq] at ip; exact ⟨t, ip.symm⟩

/-- **The instance theorem**: for an accepted claim passing the discipline, at any instance of the
rule it becomes, carried by an injective renaming of the dummies to names fresh for the instance
(`f`), the conclusion is derivable from the instance's premises, its stored terms and its dummies'
sorts, with the rules of the table alone. -/
theorem derived_instance_derivable_with (env : Env R) (wf : EnvDetermined env) (envNoFv : EnvNoFv env)
    {c : Claim R} (acc : c.verdictT env = true) (disc : c.declaredB env = true) (nf : c.noFvB = true)
    {fr' : Frame} {a ps : List Tm} {cl : Tm} (hi : c.toRule.instance fr' a = some (ps, cl))
    {f : ℕ → ℕ} (inj : Function.Injective f) (fresh : ∀ k, a.length ≤ k → fr'.nvars ≤ f k)
    (apart : ∀ k, a.length ≤ k → ∀ v ∈ a, f k ∉ fvsOf v) :
    ∃ gs ls, c.givensAt (mapS a f c.σ) = some gs ∧ c.localsAt (mapS a f c.σ) = some ls ∧
      Derivable (presOf env fr') (ps ++ gs ++ ls) cl := by
  obtain ⟨len, hk, hc⟩ := (instance_iff fr' c.toRule a ps cl).mp hi
  have len' : a.length = c.nformals := len
  simp only [Claim.noFvB, Bool.and_eq_true, List.all_eq_true] at nf
  obtain ⟨⟨⟨concNoFv, hypsNoFv⟩, termsNoFv⟩, -⟩ := nf
  simp only [Claim.verdictT, Bool.and_eq_true] at acc
  obtain ⟨wfc, acc⟩ := acc
  obtain ⟨premsSub, conclSub, localsDummy, dvlDummy⟩ := Claim.stmt_facts wfc
  set θ := mapS a f c.σ with hθ
  have agree : ∀ v, v < c.nformals → θ v = substOf a v := fun v lt => by
    rw [hθ, Claim.mapS_formal c f len' lt]; rfl
  have hk' : instKinds fr' θ c.toRule.kinds = some ps := by
    rw [instKinds_local fr' c.toRule.kinds fun v mv => agree v (Finset.mem_range.mp (premsSub mv)), hk]
  have hc' : c.concl.inst θ = some cl := by
    rw [TreePat.inst_local θ (substOf a) c.concl fun v mv => agree v (Finset.mem_range.mp (conclSub mv))]
    exact hc
  have hypsNoFv' : ∀ h ∈ c.hyps, ∀ q ∈ h.pats, patNoFv q = true := fun h mh q mq => hypsNoFv h mh q mq
  have holds : ∀ h ∈ c.hyps, KindHolds fr' θ h.kind := fun h mh =>
    instKinds_holds fr' θ hk' h.kind (List.mem_map_of_mem mh)
  -- carried names past the formals are fresh, so a pair with one of them holds vacuously
  have pastL : ∀ k, a.length ≤ k → ∀ Y, fr'.dvOk (substN a f (fvar k)) Y = true := by
    intro k lk Y
    rw [show fvar k = .node (.fv k) .nil from rfl, substN_fvar_past lk]
    have := fresh k lk
    simp [Frame.dvOk, fvsOf, fvsFields, show ¬ f k < fr'.nvars by omega]
  have pastR : ∀ l, a.length ≤ l → ∀ X, fr'.dvOk X (substN a f (fvar l)) = true := by
    intro l ll X
    rw [show fvar l = .node (.fv l) .nil from rfl, substN_fvar_past ll]
    have := fresh l ll
    simp [Frame.dvOk, fvsOf, fvsFields, show ¬ f l < fr'.nvars by omega]
  have dvFacts : ∀ k l, (fvar k, fvar l) ∈ c.frame.dvs →
      fr'.dvOk (substN a f (fvar k)) (substN a f (fvar l)) = true := by
    intro k l m
    by_cases lk : a.length ≤ k
    · exact pastL k lk _
    by_cases ll : a.length ≤ l
    · exact pastR l ll _
    simp only [Claim.frame, List.mem_append, List.mem_filterMap] at m
    rcases m with ⟨h, mh, dh⟩ | ⟨pq, mpq, dpq⟩
    · cases h
      case dv x y =>
        simp only [Claim.declaredBy] at dh
        cases hx : x.inst c.σ with
        | none => rw [hx] at dh; simp at dh
        | some X' =>
          cases hy : y.inst c.σ with
          | none => rw [hx, hy] at dh; simp at dh
          | some Y' =>
            rw [hx, hy] at dh
            simp only [Option.some.injEq, Prod.mk.injEq] at dh
            obtain ⟨rfl, rfl⟩ := dh
            have ix : x.inst θ = some (substN a f (fvar k)) := by
              rw [hθ, ← inst_substN a f c.σ x (hypsNoFv' _ mh x (by simp [Premise.pats])), hx]; rfl
            have iy : y.inst θ = some (substN a f (fvar l)) := by
              rw [hθ, ← inst_substN a f c.σ y (hypsNoFv' _ mh y (by simp [Premise.pats])), hy]; rfl
            obtain ⟨vs, hvs, hok⟩ := holds _ mh
            simp only [instAll, ix, iy, Option.some.injEq] at hvs
            subst hvs
            exact hok
      all_goals simp [Claim.declaredBy] at dh
    · -- a local pair has a dummy side, and a dummy is past the formals
      exfalso
      have dd := dvlDummy pq mpq
      cases h1 : pq.1.inst c.σ with
      | none => rw [h1] at dpq; simp at dpq
      | some X' =>
        cases h2 : pq.2.inst c.σ with
        | none => rw [h1, h2] at dpq; simp at dpq
        | some Y' =>
          rw [h1, h2] at dpq
          simp only [Option.some.injEq, Prod.mk.injEq] at dpq
          obtain ⟨rfl, rfl⟩ := dpq
          have dummyIdx : ∀ (p : Pat) (j : ℕ), c.patIsDummy p = true → p.inst c.σ = some (fvar j) →
              c.nformals ≤ j := by
            intro p j hp ip
            cases p with
            | mvar d =>
                simp only [Claim.patIsDummy, Claim.isDummy, Bool.and_eq_true, decide_eq_true_eq] at hp
                simp only [TreePat.inst, Claim.σ, substOf, Claim.vals_getElem?] at ip
                cases hd : (c.formals ++ c.dummies)[d]? with
                | none => rw [hd] at ip; simp at ip
                | some κ =>
                    rw [hd] at ip
                    obtain ⟨fs, e⟩ := value_head κ d
                    simp only [Option.map_some, Option.some.injEq, e, fvar, Term.node.injEq,
                      Head.fv.injEq] at ip
                    omega
            | idx _ => simp [Claim.patIsDummy] at hp
            | node _ _ => simp [Claim.patIsDummy] at hp
          simp only [Bool.or_eq_true] at dd
          rcases dd with d1 | d2
          · have := dummyIdx _ k d1 h1; omega
          · have := dummyIdx _ l d2 h2; omega
  have F : InstFacts c.frame fr' a f c.σ c.hyps :=
    ⟨by simp only [Claim.frame]; rw [len']; exact Claim.nformals_le c, holds, hypsNoFv', dvFacts, inj,
      fresh, apart⟩
  cases hh : c.cbHyps with
  | none => simp [hh] at acc
  | some hs =>
  cases hg : c.goal with
  | none => simp [hh, hg] at acc
  | some g =>
  cases ht : c.translate with
  | none => simp [hh, hg, ht] at acc
  | some pr =>
  obtain ⟨pf, rt⟩ := pr
  simp only [hh, hg, ht] at acc
  simp only [Claim.declaredB, hh, ht] at disc
  cases hr : runT env c.frame hs [] pf with
  | none => simp [hr] at acc
  | some done =>
  simp only [hr, decide_eq_true_eq] at acc
  have disc' : runDisc env c.frame a.length c.nvars c.σ c.hyps hs [] pf = true := by rw [len']; exact disc
  have run' := runT_subst env envNoFv F hs [] pf done hr disc'
  simp only [List.map_nil] at run'
  have gcl : substN a f g = cl := by
    have e := inst_substN a f c.σ c.concl concNoFv
    rw [← hθ, hc'] at e
    simp only [Claim.goal] at hg
    rw [hg] at e
    simpa using e
  have chk : ChildBound.checkCB (matcherOf env fr' wf) (hs.map (substN a f)) pf rt cl = true := by
    rw [Claim.checkCB_eq_runT, run']
    simp [lookupT_substN, acc, gcl]
  have der := ChildBound.checkCB_sound _ chk
  -- the claim's hypotheses, carried, are the instance's premises, stored terms and locals
  have hpats : instAll θ c.hypPats = some (hs.map (substN a f)) := by
    rw [hθ, ← instAll_substN a f c.σ c.hypPats ?_, ← Claim.cbHyps_eq, hh]; rfl
    intro p mp
    simp only [Claim.hypPats, List.mem_append, List.mem_map] at mp
    rcases mp with (mp | ⟨l, -, rfl⟩) | ⟨x, mx, rfl⟩
    · exact hypsNoFv' _ (mem_judgPats mp) p (by simp [Premise.pats])
    · simp [pjd, pex, pflds, psym, pv, patNoFv, patFieldsNoFv]
    · simp [givenPat, pjd, pex, pflds, psym, patNoFv, patFieldsNoFv, termsNoFv x mx]
  simp only [Claim.hypPats] at hpats
  obtain ⟨vjl, vg, hjl, hvg, split1⟩ := instAll_append_some hpats
  obtain ⟨vj, vl, hvj, hvl, split2⟩ := instAll_append_some hjl
  refine ⟨vg, vl, hvg, hvl, derivable_mono der fun k mk => ?_⟩
  rw [split1, split2] at mk
  simp only [List.mem_append] at mk ⊢
  rcases mk with (mk | mk) | mk
  · obtain ⟨p, mp, ip⟩ := instAll_mem θ hvj k mk
    have mc : Kind.consume p ∈ c.toRule.kinds :=
      List.mem_map_of_mem (f := Premise.kind) (mem_judgPats mp)
    obtain ⟨j, mj, ij⟩ := instKinds_consume fr' θ hk' p mc
    rw [ip] at ij
    cases ij
    exact Or.inl (Or.inl mj)
  · exact Or.inr mk
  · exact Or.inl (Or.inr mk)

/-- The locals at a freshening that sends every dummy past the frame are local facts. -/
theorem localsAt_isLocal {c : Claim R} (wfc : c.wellFormed = true) {a : List Tm} {f : ℕ → ℕ}
    (len : a.length = c.nformals) {fr' : Frame} (fresh : ∀ k, a.length ≤ k → fr'.nvars ≤ f k)
    {ls : List Tm} (h : c.localsAt (mapS a f c.σ) = some ls) :
    ∀ g ∈ ls, IsLocalFact (c.locals.map Prod.fst) fr' g := by
  intro g m
  obtain ⟨p, mp, ip⟩ := instAll_mem _ h g m
  obtain ⟨l, ml, rfl⟩ := List.mem_map.mp mp
  obtain ⟨-, -, localsDummy, -⟩ := Claim.stmt_facts wfc
  have hl := localsDummy l ml
  simp only [Claim.isDummy, Bool.and_eq_true, decide_eq_true_eq] at hl
  rw [inst_localPat] at ip
  simp only [mapS, Claim.σ, substOf, Claim.vals_getElem?] at ip
  cases hd : (c.formals ++ c.dummies)[l.2]? with
  | none => rw [hd] at ip; simp at ip
  | some κ =>
      rw [hd] at ip
      obtain ⟨fs, e⟩ := value_head κ l.2
      have past : a.length ≤ l.2 := by omega
      simp only [Option.map_some, e, substN, List.getElem?_eq_none past, Option.getD_none,
        Option.some.injEq] at ip
      exact ⟨l.1, List.mem_map_of_mem ml, f l.2, _, ip.symm, fresh l.2 past⟩

/-- **Every instance of an accepted claim that passes the discipline is derivable without it**, from
the instance's premises, cited terms, and its dummies' sorts at names fresh for the frame. -/
theorem derived_instance_derivable (env : Env R) (wf : EnvDetermined env) (envNoFv : EnvNoFv env)
    {c : Claim R} (acc : c.verdictT env = true) (disc : c.declaredB env = true) (nf : c.noFvB = true)
    {fr' : Frame} {a ps : List Tm} {cl : Tm} (hi : c.toRule.instance fr' a = some (ps, cl)) :
    ∃ gs, (∀ g ∈ gs, IsGiven g ∨ IsLocalFact (c.locals.map Prod.fst) fr' g) ∧
      Derivable (presOf env fr') (ps ++ gs) cl := by
  set B := fr'.nvars + nameBound a
  have inj : Function.Injective (fun k => B + k) := fun x y e => by simpa using e
  have fresh : ∀ k, a.length ≤ k → fr'.nvars ≤ B + k := fun k _ => by omega
  have apart : ∀ k, a.length ≤ k → ∀ v ∈ a, B + k ∉ fvsOf v := fun k _ v mv mz => by
    have := lt_nameBound mv mz; omega
  obtain ⟨gs, ls, hgs, hls, d⟩ :=
    derived_instance_derivable_with env wf envNoFv acc disc nf hi inj fresh apart
  have wfc : c.wellFormed = true := by
    simp only [Claim.verdictT, Bool.and_eq_true] at acc; exact acc.1
  have len : a.length = c.nformals := ((instance_iff fr' c.toRule a ps cl).mp hi).1
  refine ⟨gs ++ ls, fun g m => ?_, by simpa [List.append_assoc] using d⟩
  rcases List.mem_append.mp m with m | m
  · exact Or.inl (givensAt_isGiven hgs g m)
  · exact Or.inr (localsAt_isLocal wfc len fresh hls g m)

/-! ## Adding the rule is conservative -/

/-- The table with one more rule, under the name `r0`. -/
def extendEnv [DecidableEq R] (env : Env R) (r0 : R) (ru0 : Rule) : Env R :=
  fun r => if r = r0 then some ru0 else env r

theorem collect_givens {P : Presentation.{0}} {hyps : List P.J} {G : P.J → Prop} :
    ∀ ps : List P.J, (∀ p ∈ ps, ∃ gs : List P.J, (∀ g ∈ gs, G g) ∧ Derivable P (hyps ++ gs) p) →
      ∃ gs : List P.J, (∀ g ∈ gs, G g) ∧ ∀ p ∈ ps, Derivable P (hyps ++ gs) p
  | [], _ => ⟨[], by simp, by simp⟩
  | p :: ps, h => by
      obtain ⟨g1, G1, d1⟩ := h p List.mem_cons_self
      obtain ⟨g2, G2, d2⟩ := collect_givens ps fun q m => h q (List.mem_cons_of_mem _ m)
      refine ⟨g1 ++ g2, fun g m => ?_, fun q m => ?_⟩
      · rcases List.mem_append.mp m with m | m
        · exact G1 g m
        · exact G2 g m
      · rcases List.mem_cons.mp m with rfl | m
        · exact derivable_mono d1 fun k mk => by
            rcases List.mem_append.mp mk with mk | mk
            · exact List.mem_append_left _ mk
            · exact List.mem_append_right _ (List.mem_append_left _ mk)
        · exact derivable_mono (d2 q m) fun k mk => by
            rcases List.mem_append.mp mk with mk | mk
            · exact List.mem_append_left _ mk
            · exact List.mem_append_right _ (List.mem_append_right _ mk)

/-- **Adding an accepted claim that passes the discipline as a rule is conservative**: whatever the
extended table derives from `hyps`, in any frame, the table alone derives from `hyps`, some cited
terms, and some sorts of the claim's dummies at names fresh for the frame. -/
theorem derived_conservative [DecidableEq R] (env : Env R) (wf : EnvDetermined env)
    (envNoFv : EnvNoFv env) {c : Claim R} (acc : c.verdictT env = true) (disc : c.declaredB env = true)
    (nf : c.noFvB = true) {fr : Frame} {hyps : List Tm} {j : (presOf (extendEnv env c.id c.toRule) fr).J}
    (h : Derivable (presOf (extendEnv env c.id c.toRule) fr) hyps j) :
    ∃ gs : List Tm, (∀ g ∈ gs, IsGiven g ∨ IsLocalFact (c.locals.map Prod.fst) fr g) ∧
      Derivable (presOf env fr) (hyps ++ gs) j := by
  induction h with
  | hyp mem => exact ⟨[], by simp, Derivable.hyp (List.mem_append_left _ mem)⟩
  | @rule r a ps cl hi _ ih =>
      obtain ⟨gs, G, ds⟩ := collect_givens (P := presOf env fr)
        (G := fun g => IsGiven g ∨ IsLocalFact (c.locals.map Prod.fst) fr g) ps fun p m => ih p m rfl
      by_cases e : r = c.id
      · subst e
        have hi' : c.toRule.instance fr a = some (ps, cl) := by
          simpa [presOf, extendEnv] using hi
        obtain ⟨gs0, G0, d0⟩ := derived_instance_derivable env wf envNoFv acc disc nf hi'
        refine ⟨gs ++ gs0, fun g m => ?_, ?_⟩
        · rcases List.mem_append.mp m with m | m
          · exact G g m
          · exact G0 g m
        · refine d0.cut fun k mk => ?_
          rcases List.mem_append.mp mk with mk | mk
          · exact derivable_mono (ds k mk) fun x mx => by
              rcases List.mem_append.mp mx with mx | mx
              · exact List.mem_append_left _ mx
              · exact List.mem_append_right _ (List.mem_append_left _ mx)
          · exact Derivable.hyp (List.mem_append_right _ (List.mem_append_right _ mk))
      · have hi' : (presOf env fr).inst r a = some (ps, cl) := by
          simpa [presOf, extendEnv, e] using hi
        exact ⟨gs, G, Derivable.rule hi' fun p m _ => ds p m⟩

end Mettapedia.Logic.TierZero.Kernel2
