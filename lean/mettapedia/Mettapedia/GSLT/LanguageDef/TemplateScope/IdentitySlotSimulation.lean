import Mettapedia.GSLT.LanguageDef.TemplateScope.IdentitySlotRelation
import Mettapedia.GSLT.LanguageDef.TemplateScope.SpectrumTheorems

/-!
# Template scope: the two name disciplines evaluate alike

Related terms (`IdSlot.Rel`) run alike under the static discipline.  The first
side may take more steps (its `let`s and `new` blocks are activations) and
runs at other paths, so its fresh names are other copies; each result pair is
related by its own extension of the name map, injective on everything the
result and its store mention.

## Main results

* `sim` — **first side to second side**: if the first side's run is defined,
  so is the second side's at the same fuel, and the bags are related
  pointwise, in order, each pair through an injective extension of the name
  map: the result terms are related, and so are the final stores.
* `simI` — **second side to first side**: if the second side's run is defined
  at some fuel, so is the first side's at some fuel.
* `sim_iff` — together: the two runs are defined together, with related bags.
-/

namespace Mettapedia.GSLT.LanguageDef.TemplateScope

open Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline

universe u v

namespace IdSlot

variable {S : Type u} {X₁ X₂ : Type v}

/-! ## Paths -/

/-- `ρ` lies strictly below `π`. -/
def SPre (π ρ : Path) : Prop := ∃ i r, ρ = π ++ i :: r

/-- The activation tags of a name. -/
def tags {Y : Type v} : Nm Y → List Path
  | .src _ => []
  | .inst ρ n => ρ :: tags n

/-- No tag of the name lies strictly below `π`: the evaluation at `π` did not
make it. -/
def OldAt {Y : Type v} (π : Path) (n : Nm Y) : Prop := ∀ ρ ∈ tags n, ¬ SPre π ρ

/-- No tag of the name lies at or below `π`. -/
def Avoid {Y : Type v} (π : Path) (n : Nm Y) : Prop := ∀ ρ ∈ tags n, ¬ π <+: ρ

/-- A copy made by an activation strictly below `π`. -/
def NewAt {Y : Type v} (π : Path) (n : Nm Y) : Prop :=
  ∃ ρ s, n = .inst ρ (.src s) ∧ SPre π ρ

theorem SPre.child (π : Path) (i : ℕ) : SPre π (π ++ [i]) := ⟨i, [], rfl⟩

theorem SPre.of_child {π ρ : Path} {i : ℕ} (h : SPre (π ++ [i]) ρ) : SPre π ρ := by
  obtain ⟨j, r, rfl⟩ := h
  exact ⟨i, j :: r, by simp⟩

theorem SPre.prefix {π ρ : Path} (h : SPre π ρ) : π <+: ρ := by
  obtain ⟨i, r, rfl⟩ := h
  exact List.prefix_append π (i :: r)

theorem SPre.ne {π ρ : Path} (h : SPre π ρ) : ρ ≠ π := by
  obtain ⟨i, r, rfl⟩ := h
  intro e
  have := congrArg List.length e
  simp at this

/-- Two siblings are apart. -/
theorem not_prefix_sibling {π ρ : Path} {i j : ℕ} (hij : i ≠ j) (h : π ++ [i] <+: ρ) :
    ¬ π ++ [j] <+: ρ := by
  intro h'
  obtain ⟨r, rfl⟩ := h
  obtain ⟨r', e⟩ := h'
  simp only [List.append_assoc, List.singleton_append] at e
  have := List.append_cancel_left e
  simp only [List.cons.injEq] at this
  exact hij this.1.symm

theorem OldAt.avoid_child {Y : Type v} {π : Path} {n : Nm Y} (h : OldAt π n) (i : ℕ) :
    Avoid (π ++ [i]) n := by
  intro ρ hρ hp
  apply h ρ hρ
  obtain ⟨r, rfl⟩ := hp
  exact ⟨i, r, by simp⟩

theorem Avoid.oldAt {Y : Type v} {π : Path} {n : Nm Y} (h : Avoid π n) : OldAt π n :=
  fun ρ hρ hs => h ρ hρ hs.prefix

theorem OldAt.child {Y : Type v} {π : Path} {n : Nm Y} (h : OldAt π n) (i : ℕ) :
    OldAt (π ++ [i]) n := (h.avoid_child i).oldAt

theorem NewAt.parent {Y : Type v} {π : Path} {i : ℕ} {n : Nm Y} (h : NewAt (π ++ [i]) n) :
    NewAt π n := by
  obtain ⟨ρ, s, rfl, hs⟩ := h
  exact ⟨ρ, s, rfl, hs.of_child⟩

theorem NewAt.avoid_sibling {Y : Type v} {π : Path} {i j : ℕ} (hij : i ≠ j) {n : Nm Y}
    (h : NewAt (π ++ [i]) n) : Avoid (π ++ [j]) n := by
  obtain ⟨ρ, s, rfl, hs⟩ := h
  intro ρ' hρ'
  simp only [tags, List.mem_cons, List.not_mem_nil, or_false] at hρ'
  subst hρ'
  exact not_prefix_sibling hij hs.prefix

theorem NewAt.not_oldAt {Y : Type v} {π : Path} {n : Nm Y} (h : NewAt π n) : ¬ OldAt π n := by
  obtain ⟨ρ, s, rfl, hs⟩ := h
  intro ho
  exact ho ρ (by simp [tags]) hs

theorem Avoid.ne_inst {Y : Type v} {π : Path} {n : Nm Y} (h : Avoid π n) (m : Nm Y) :
    n ≠ .inst π m := by
  rintro rfl
  exact h π (by simp [tags]) (List.prefix_refl π)

theorem newAt_inst {Y : Type v} {π : Path} (i : ℕ) (s : Y) :
    NewAt π (.inst (π ++ [i]) (.src s) : Nm Y) := ⟨_, s, rfl, SPre.child π i⟩

theorem oldAt_inst_self {Y : Type v} (π : Path) (s : Y) : OldAt π (.inst π (.src s) : Nm Y) := by
  intro ρ hρ hs
  simp only [tags, List.mem_cons, List.not_mem_nil, or_false] at hρ
  subst hρ
  exact hs.ne rfl

theorem oldAt_src {Y : Type v} (π : Path) (s : Y) : OldAt π (.src s : Nm Y) := by
  intro ρ hρ
  simp [tags] at hρ

/-! ## The invariant of a configuration -/

/-- **The invariant of a configuration**: `D` holds every name that still
matters (the current term's, the waiting terms', the store's); `Res` the
reserved names of every pending construct.  The map is injective on `D`, no
image is reserved, reserved names are distinct, the stores are related, and
every name in play may occur free. -/
structure CI (C : Setting S X₁ X₂) (ν : Nm X₁ → Nm X₂) (D : Set (Nm X₁)) (Res : List (Nm X₂))
    (σ₁ : GStore S X₁) (σ₂ : GStore S X₂) : Prop where
  inj : Set.InjOn ν D
  nodup : Res.Nodup
  disj : ∀ n ∈ D, ν n ∉ Res
  store : StoreRel C ν D σ₁ σ₂
  ok₁ : ∀ n ∈ D, OK₁ C n
  ok₂ : ∀ n ∈ D, OK₂ C (ν n)
  okRes : ∀ m ∈ Res, OK₂ C m

/-- Nothing in play was made at or below the current paths. -/
structure Fresh (π π' : Path) (ν : Nm X₁ → Nm X₂) (D : Set (Nm X₁)) (Res : List (Nm X₂)) :
    Prop where
  old₁ : ∀ n ∈ D, OldAt π n
  old₂ : ∀ n ∈ D, OldAt π' (ν n)
  oldRes : ∀ m ∈ Res, OldAt π' m

/-- **An extension of the name map along an evaluation at `π`, `π'`**: it
keeps the old names, and every new name was made below `π`, with an image made
below `π'` or reserved in `Res`. -/
structure Ext (π π' : Path) (Res : List (Nm X₂)) (ν : Nm X₁ → Nm X₂) (D : Set (Nm X₁))
    (ν' : Nm X₁ → Nm X₂) (D' : Set (Nm X₁)) : Prop where
  agree : ∀ n ∈ D, ν' n = ν n
  sub : D ⊆ D'
  new : ∀ n ∈ D', n ∉ D → NewAt π n ∧ (NewAt π' (ν' n) ∨ ν' n ∈ Res)

variable {C : Setting S X₁ X₂}

theorem CI.res_unbound {ν : Nm X₁ → Nm X₂} {D : Set (Nm X₁)} {Res : List (Nm X₂)}
    {σ₁ : GStore S X₁} {σ₂ : GStore S X₂} (h : CI C ν D Res σ₁ σ₂) {m : Nm X₂} (hm : m ∈ Res) :
    σ₂ m = none := by
  by_contra hc
  obtain ⟨n, hn, rfl⟩ := h.store.only m hc
  exact h.disj n hn hm

theorem CI.drop {ν : Nm X₁ → Nm X₂} {D : Set (Nm X₁)} {A B : List (Nm X₂)}
    {σ₁ : GStore S X₁} {σ₂ : GStore S X₂} (h : CI C ν D (A ++ B) σ₁ σ₂) : CI C ν D B σ₁ σ₂ where
  inj := h.inj
  nodup := (List.nodup_append.1 h.nodup).2.1
  disj n hn hm := h.disj n hn (List.mem_append_right _ hm)
  store := h.store
  ok₁ := h.ok₁
  ok₂ := h.ok₂
  okRes m hm := h.okRes m (List.mem_append_right _ hm)

theorem CI.sub {ν : Nm X₁ → Nm X₂} {D E : Set (Nm X₁)} {Res : List (Nm X₂)}
    {σ₁ : GStore S X₁} {σ₂ : GStore S X₂} (h : CI C ν D Res σ₁ σ₂) (hE : E ⊆ D)
    (hdom : ∀ n, σ₁ n ≠ none → n ∈ E) : CI C ν E Res σ₁ σ₂ where
  inj := h.inj.mono hE
  nodup := h.nodup
  disj n hn := h.disj n (hE hn)
  store := {
    rel := fun n hn => h.store.rel n (hE hn)
    dom := hdom
    only := by
      intro m hm
      obtain ⟨n, hn, rfl⟩ := h.store.only m hm
      have hb : σ₁ n ≠ none := by
        intro e
        have hr := h.store.rel n hn
        rw [e] at hr
        cases h2 : σ₂ (ν n) with
        | none => exact hm h2
        | some _ => rw [h2] at hr; exact hr
      exact ⟨n, hdom n hb, rfl⟩ }
  ok₁ n hn := h.ok₁ n (hE hn)
  ok₂ n hn := h.ok₂ n (hE hn)
  okRes := h.okRes

theorem Fresh.drop {π π' : Path} {ν : Nm X₁ → Nm X₂} {D : Set (Nm X₁)} {A B : List (Nm X₂)}
    (h : Fresh π π' ν D (A ++ B)) : Fresh π π' ν D B where
  old₁ := h.old₁
  old₂ := h.old₂
  oldRes m hm := h.oldRes m (List.mem_append_right _ hm)

theorem Fresh.child {π π' : Path} {ν : Nm X₁ → Nm X₂} {D : Set (Nm X₁)} {Res : List (Nm X₂)}
    (h : Fresh π π' ν D Res) (i j : ℕ) : Fresh (π ++ [i]) (π' ++ [j]) ν D Res where
  old₁ n hn := (h.old₁ n hn).child i
  old₂ n hn := (h.old₂ n hn).child j
  oldRes m hm := (h.oldRes m hm).child j

theorem Fresh.child₁ {π π' : Path} {ν : Nm X₁ → Nm X₂} {D : Set (Nm X₁)} {Res : List (Nm X₂)}
    (h : Fresh π π' ν D Res) (i : ℕ) : Fresh (π ++ [i]) π' ν D Res where
  old₁ n hn := (h.old₁ n hn).child i
  old₂ := h.old₂
  oldRes := h.oldRes

theorem Ext.refl (π π' : Path) (Res : List (Nm X₂)) (ν : Nm X₁ → Nm X₂) (D : Set (Nm X₁)) :
    Ext π π' Res ν D ν D where
  agree _ _ := rfl
  sub := le_rfl
  new _ h h' := absurd h h'

theorem Ext.trans {π π' : Path} {R₁ R₂ : List (Nm X₂)} {ν ν₁ ν₂ : Nm X₁ → Nm X₂}
    {D D₁ D₂ : Set (Nm X₁)} (h₁ : Ext π π' R₁ ν D ν₁ D₁) (h₂ : Ext π π' R₂ ν₁ D₁ ν₂ D₂) :
    Ext π π' (R₁ ++ R₂) ν D ν₂ D₂ where
  agree n hn := (h₂.agree n (h₁.sub hn)).trans (h₁.agree n hn)
  sub := h₁.sub.trans h₂.sub
  new n hn hnD := by
    by_cases h1 : n ∈ D₁
    · obtain ⟨hp, hi⟩ := h₁.new n h1 hnD
      rw [h₂.agree n h1]
      exact ⟨hp, hi.imp_right (List.mem_append_left _)⟩
    · obtain ⟨hp, hi⟩ := h₂.new n hn h1
      exact ⟨hp, hi.imp_right (List.mem_append_right _)⟩

theorem Ext.res_mono {π π' : Path} {R R' : List (Nm X₂)} {ν ν' : Nm X₁ → Nm X₂}
    {D D' : Set (Nm X₁)} (h : Ext π π' R ν D ν' D') (hR : ∀ m ∈ R, m ∈ R') :
    Ext π π' R' ν D ν' D' where
  agree := h.agree
  sub := h.sub
  new n hn hnD := (h.new n hn hnD).imp_right (Or.imp_right (hR _))

theorem Ext.parent {π π' : Path} {i j : ℕ} {R : List (Nm X₂)} {ν ν' : Nm X₁ → Nm X₂}
    {D D' : Set (Nm X₁)} (h : Ext (π ++ [i]) (π' ++ [j]) R ν D ν' D') : Ext π π' R ν D ν' D' where
  agree := h.agree
  sub := h.sub
  new n hn hnD := by
    obtain ⟨hp, hi⟩ := h.new n hn hnD
    exact ⟨hp.parent, hi.imp_left NewAt.parent⟩

theorem Ext.parent₁ {π π' : Path} {i : ℕ} {R : List (Nm X₂)} {ν ν' : Nm X₁ → Nm X₂}
    {D D' : Set (Nm X₁)} (h : Ext (π ++ [i]) π' R ν D ν' D') : Ext π π' R ν D ν' D' where
  agree := h.agree
  sub := h.sub
  new n hn hnD := by
    obtain ⟨hp, hi⟩ := h.new n hn hnD
    exact ⟨hp.parent, hi⟩

/-- After an evaluation at the children `i`, `i'`, the configuration is fresh
for the siblings `j`, `j'`. -/
theorem Ext.fresh_sibling {π π' : Path} {i i' j j' : ℕ} (hij : i ≠ j) (hij' : i' ≠ j')
    {R Rc : List (Nm X₂)} {ν ν' : Nm X₁ → Nm X₂} {D D' : Set (Nm X₁)}
    (hF : Fresh π π' ν D (R ++ Rc)) (h : Ext (π ++ [i]) (π' ++ [i']) R ν D ν' D') :
    Fresh (π ++ [j]) (π' ++ [j']) ν' D' Rc where
  old₁ n hn := by
    by_cases hD : n ∈ D
    · exact (hF.old₁ n hD).child j
    · exact ((h.new n hn hD).1.avoid_sibling hij).oldAt
  old₂ n hn := by
    by_cases hD : n ∈ D
    · rw [h.agree n hD]; exact (hF.old₂ n hD).child j'
    · rcases (h.new n hn hD).2 with hp | hr
      · exact (hp.avoid_sibling hij').oldAt
      · exact (hF.oldRes _ (List.mem_append_left _ hr)).child j'
  oldRes m hm := (hF.oldRes m (List.mem_append_right _ hm)).child j'

/-- The same when the second side stays at its path: the new images are
reserved names. -/
theorem Ext.fresh_sibling₁ {π π' : Path} {i j : ℕ} (hij : i ≠ j)
    {R Rc : List (Nm X₂)} {ν ν' : Nm X₁ → Nm X₂} {D D' : Set (Nm X₁)}
    (hF : Fresh π π' ν D (R ++ Rc)) (h : Ext (π ++ [i]) π' R ν D ν' D')
    (hres : ∀ n ∈ D', n ∉ D → ν' n ∈ R) :
    Fresh (π ++ [j]) π' ν' D' Rc where
  old₁ n hn := by
    by_cases hD : n ∈ D
    · exact (hF.old₁ n hD).child j
    · exact ((h.new n hn hD).1.avoid_sibling hij).oldAt
  old₂ n hn := by
    by_cases hD : n ∈ D
    · rw [h.agree n hD]; exact hF.old₂ n hD
    · exact hF.oldRes _ (List.mem_append_left _ (hres n hn hD))
  oldRes m hm := hF.oldRes m (List.mem_append_right _ hm)

/-! ## Programs and inert values -/

variable [DecidableEq X₁] [DecidableEq X₂]

/-- Related programs: the same equations, each closed and related. -/
def ProgRel (C : Setting S X₁ X₂) (P₁ : S → Option (Tm S X₁)) (P₂ : S → Option (Tm S X₂)) :
    Prop :=
  ∀ F, OptRel (fun e₁ e₂ => freeNames e₁ = [] ∧ freeParams e₁ = [] ∧
    ∀ ν μ, Rel C ν μ .code [] true e₁ e₂) (P₁ F) (P₂ F)

/-- Terms that evaluate to themselves. -/
def Inert {Y : Type v} (P : S → Option (Tm S Y)) : Tm S Y → Prop
  | .sym _ => True
  | .fn F => P F = none
  | .var _ => True
  | .pvar _ => True
  | .lam _ _ _ => True
  | .quote _ => True
  | .ctx _ _ => True
  | .pquote _ => True
  | .app f a => Inert P f ∧ Inert P a ∧ ∀ x own b, f ≠ .lam x own b
  | _ => False


/-! ## The evaluator on inert terms, determinism, bags -/

section Eval

variable {Y : Type v} [DecidableEq S] [DecidableEq Y]

/-- **An inert term evaluates to itself**, whenever its run is defined. -/
theorem run_inert [CodeId Y] (P : S → Option (Tm S Y)) (d : Disc) :
    ∀ (v : Tm S Y), Inert P v → ∀ (n : ℕ) (π : Path) (σ : GStore S Y) (L : Result S Y),
      run d P n π σ v = some L → L = [(v, σ)]
  | .sym _, _, 0, _, _, _, h => by cases h
  | .sym _, _, _ + 1, _, _, _, h => by injection h with h; exact h.symm
  | .var _, _, 0, _, _, _, h => by cases h
  | .var _, _, _ + 1, _, _, _, h => by injection h with h; exact h.symm
  | .pvar _, _, 0, _, _, _, h => by cases h
  | .pvar _, _, _ + 1, _, _, _, h => by injection h with h; exact h.symm
  | .lam _ _ _, _, 0, _, _, _, h => by cases h
  | .lam _ _ _, _, _ + 1, _, _, _, h => by injection h with h; exact h.symm
  | .quote _, _, 0, _, _, _, h => by cases h
  | .quote _, _, _ + 1, _, _, _, h => by injection h with h; exact h.symm
  | .pquote _, _, 0, _, _, _, h => by cases h
  | .pquote _, _, _ + 1, _, _, _, h => by injection h with h; exact h.symm
  | .ctx _ _, _, 0, _, _, _, h => by cases h
  | .ctx _ _, _, _ + 1, _, _, _, h => by injection h with h; exact h.symm
  | .fn _, _, 0, _, _, _, h => by cases h
  | .fn F, hv, n + 1, π, σ, L, h => by
      have hP : P F = none := hv
      change step d P (run d P n) π σ (.fn F) = some L at h
      simp only [step, hP] at h
      injection h with h
      exact h.symm
  | .app _ _, _, 0, _, _, _, h => by cases h
  | .app f a, hv, n + 1, π, σ, L, h => by
      obtain ⟨hf, ha, hnl⟩ := hv
      change step d P (run d P n) π σ (.app f a) = some L at h
      simp only [step] at h
      cases hrf : run d P n (π ++ [0]) σ f with
      | none => rw [hrf] at h; cases h
      | some Lf =>
          rw [hrf, run_inert P d f hf n _ σ Lf hrf, bindOpt_some_singleton] at h
          cases hra : run d P n (π ++ [1]) σ a with
          | none => rw [hra] at h; cases h
          | some La =>
              rw [hra, run_inert P d a ha n _ σ La hra, bindOpt_some_singleton] at h
              cases f with
              | lam x own b => exact absurd rfl (hnl x own b)
              | _ => injection h with h; exact h.symm
  | .letP _ _ _, hv, _, _, _, _, _ => hv.elim
  | .alt _ _, hv, _, _, _, _, _ => hv.elim

/-- An inert term is defined at every large enough fuel. -/
theorem run_inert_def [CodeId Y] (P : S → Option (Tm S Y)) (d : Disc) :
    ∀ (v : Tm S Y), Inert P v → ∃ n₀, ∀ n, n₀ ≤ n → ∀ (π : Path) (σ : GStore S Y),
      run d P n π σ v = some [(v, σ)]
  | .sym _, _ => ⟨1, fun n hn π σ => by obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩; rfl⟩
  | .var _, _ => ⟨1, fun n hn π σ => by obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩; rfl⟩
  | .pvar _, _ => ⟨1, fun n hn π σ => by obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩; rfl⟩
  | .lam _ _ _, _ =>
      ⟨1, fun n hn π σ => by obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩; rfl⟩
  | .quote _, _ =>
      ⟨1, fun n hn π σ => by obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩; rfl⟩
  | .pquote _, _ =>
      ⟨1, fun n hn π σ => by obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩; rfl⟩
  | .ctx _ _, _ =>
      ⟨1, fun n hn π σ => by obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩; rfl⟩
  | .fn F, hv => ⟨1, fun n hn π σ => by
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have hP : P F = none := hv
      change step d P (run d P m) π σ (.fn F) = _
      simp [step, hP]⟩
  | .app f a, hv => by
      obtain ⟨hf, ha, hnl⟩ := hv
      obtain ⟨nf, hnf⟩ := run_inert_def P d f hf
      obtain ⟨na, hna⟩ := run_inert_def P d a ha
      refine ⟨max nf na + 1, fun n hn π σ => ?_⟩
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      change step d P (run d P m) π σ (.app f a) = _
      simp only [step]
      rw [hnf m (by omega), bindOpt_some_singleton, hna m (by omega), bindOpt_some_singleton]
      cases f with
      | lam x own b => exact absurd rfl (hnl x own b)
      | _ => rfl
  | .letP _ _ _, hv => hv.elim
  | .alt _ _, hv => hv.elim

/-- **Results are inert.** -/
theorem run_results_inert [CodeId Y] (P : S → Option (Tm S Y)) (d : Disc) :
    ∀ (n : ℕ) (π : Path) (σ : GStore S Y) (t : Tm S Y) (L : Result S Y),
      run d P n π σ t = some L → ∀ r ∈ L, Inert P r.1
  | 0, _, _, _, _, h => by cases h
  | n + 1, π, σ, t, L, h => by
      change step d P (run d P n) π σ t = some L at h
      intro r hr
      cases t with
      | fn F =>
          simp only [step] at h
          cases hP : P F with
          | none =>
              rw [hP] at h
              injection h with h
              subst h
              simp only [List.mem_singleton] at hr
              subst hr
              exact hP
          | some e =>
              rw [hP] at h
              exact run_results_inert P d n _ σ e L h r hr
      | app f a =>
          simp only [step] at h
          obtain ⟨l₁, hl₁, r₁, hr₁, M₁, hM₁, hx₁⟩ := bindOpt_mem h hr
          obtain ⟨l₂, hl₂, r₂, hr₂, M₂, hM₂, hx₂⟩ := bindOpt_mem hM₁ hx₁
          have i₁ := run_results_inert P d n _ σ f l₁ hl₁ r₁ hr₁
          have i₂ := run_results_inert P d n _ r₁.2 a l₂ hl₂ r₂ hr₂
          obtain ⟨u₁, σ₁⟩ := r₁
          cases u₁ with
          | lam x own body => exact run_results_inert P d n _ _ _ M₂ hM₂ r hx₂
          | _ =>
              injection hM₂ with hM₂
              subst hM₂
              simp only [List.mem_singleton] at hx₂
              subst hx₂
              exact ⟨i₁, i₂, fun _ _ _ e => by cases e⟩
      | letP p w b =>
          simp only [step] at h
          cases hl : letLam? p w with
          | some f => rw [hl] at h; exact run_results_inert P d n _ _ _ L h r hr
          | none =>
              rw [hl] at h
              simp only at h
              obtain ⟨l₁, hl₁, r₁, hr₁, M₁, hM₁, hx₁⟩ := bindOpt_mem h hr
              cases hg : (act r₁.2 r₁.1).toGVal? with
              | some g =>
                  rw [hg] at hM₁
                  simp only at hM₁
                  cases hm : matchT r₁.2 p g.toTm with
                  | some σ₂ =>
                      rw [hm] at hM₁
                      exact run_results_inert P d n _ _ _ M₁ hM₁ r hx₁
                  | none => rw [hm] at hM₁; injection hM₁ with hM₁; subst hM₁; cases hx₁
              | none =>
                  rw [hg] at hM₁
                  simp only at hM₁
                  cases p with
                  | var f => exact run_results_inert P d n _ _ _ M₁ hM₁ r hx₁
                  | _ => injection hM₁ with hM₁; subst hM₁; cases hx₁
      | alt t₁ t₂ =>
          simp only [step] at h
          cases h₁ : run d P n (π ++ [0]) σ t₁ with
          | none => rw [h₁] at h; cases h
          | some l =>
              cases h₂ : run d P n (π ++ [1]) σ t₂ with
              | none => rw [h₁, h₂] at h; cases h
              | some m =>
                  rw [h₁, h₂] at h
                  injection h with h
                  subst h
                  rcases List.mem_append.1 hr with hr | hr
                  · exact run_results_inert P d n _ σ t₁ l h₁ r hr
                  · exact run_results_inert P d n _ σ t₂ m h₂ r hr
      | sym s | var n | pvar y | lam y own body | quote c | pquote c | ctx _ _ =>
          injection h with h
          subst h
          simp only [List.mem_singleton] at hr
          subst hr
          trivial

/-- **Determinism**: two defined runs agree. -/
theorem run_det [CodeId Y] {d : Disc} {P : S → Option (Tm S Y)} {n m : ℕ} {π : Path} {σ : GStore S Y}
    {t : Tm S Y} {L L' : Result S Y} (h : run d P n π σ t = some L)
    (h' : run d P m π σ t = some L') : L = L' := by
  have e1 := run_mono d P (le_max_left n m) h
  have e2 := run_mono d P (le_max_right n m) h'
  rw [e1] at e2
  exact Option.some.inj e2

end Eval

theorem bindOpt_eq_some {α β : Type*} {o : Option (List α)} {g : α → Option (List β)}
    {L : List β} (h : bindOpt o g = some L) : ∃ l, o = some l ∧ bindAll l g = some L := by
  cases o with
  | none => cases h
  | some l => exact ⟨l, rfl, h⟩

/-- A bag simulation through `bindAll`. -/
theorem bindAll_sim {α₁ α₂ β₁ β₂ : Type*} {Rin : α₁ → α₂ → Prop} {Rout : β₁ → β₂ → Prop}
    {g₁ : α₁ → Option (List β₁)} {g₂ : α₂ → Option (List β₂)}
    (hg : ∀ a₁ a₂ M₁, Rin a₁ a₂ → g₁ a₁ = some M₁ →
      ∃ M₂, g₂ a₂ = some M₂ ∧ List.Forall₂ Rout M₁ M₂) :
    ∀ {l₁ : List α₁} {l₂ : List α₂} {L₁ : List β₁}, List.Forall₂ Rin l₁ l₂ →
      bindAll l₁ g₁ = some L₁ → ∃ L₂, bindAll l₂ g₂ = some L₂ ∧ List.Forall₂ Rout L₁ L₂
  | [], [], L₁, .nil, h => by
      simp only [bindAll] at h
      injection h with h
      subst h
      exact ⟨[], rfl, .nil⟩
  | a₁ :: l₁, a₂ :: l₂, L₁, .cons hr hrs, h => by
      unfold bindAll at h
      cases h1 : g₁ a₁ with
      | none => rw [h1] at h; cases h
      | some M₁ =>
          cases h2 : bindAll l₁ g₁ with
          | none => rw [h1, h2] at h; cases h
          | some N₁ =>
              rw [h1, h2] at h
              injection h with h
              subst h
              obtain ⟨M₂, e1, hM⟩ := hg a₁ a₂ M₁ hr h1
              obtain ⟨N₂, e2, hN⟩ := bindAll_sim hg hrs h2
              refine ⟨M₂ ++ N₂, ?_, forall₂_append hM hN⟩
              unfold bindAll
              rw [e1, e2]

theorem bindAll_some_each {α β : Type*} {g : α → Option (List β)} :
    ∀ {l : List α} {L : List β}, bindAll l g = some L → ∀ a ∈ l, ∃ M, g a = some M
  | [], _, _, a, ha => by cases ha
  | b :: l, L, h, a, ha => by
      unfold bindAll at h
      cases h1 : g b with
      | none => rw [h1] at h; cases h
      | some M =>
          cases h2 : bindAll l g with
          | none => rw [h1, h2] at h; cases h
          | some N =>
              rcases List.mem_cons.1 ha with rfl | ha
              · exact ⟨M, h1⟩
              · exact bindAll_some_each h2 a ha

/-- A finite bag is defined at a common fuel. -/
theorem exists_fuel_bindAll {α β : Type*} {g : ℕ → α → Option (List β)}
    (hmono : ∀ n n' a M, n ≤ n' → g n a = some M → g n' a = some M) :
    ∀ (l : List α), (∀ a ∈ l, ∃ n M, g n a = some M) → ∃ n M, bindAll l (g n) = some M
  | [], _ => ⟨0, [], rfl⟩
  | a :: l, h => by
      obtain ⟨n₁, M₁, h₁⟩ := h a List.mem_cons_self
      obtain ⟨n₂, M₂, h₂⟩ := exists_fuel_bindAll hmono l (fun b hb => h b (List.mem_cons_of_mem a hb))
      refine ⟨max n₁ n₂, M₁ ++ M₂, ?_⟩
      unfold bindAll
      rw [hmono n₁ _ a M₁ (le_max_left _ _) h₁,
        bindAll_mono (fun b M hb => hmono n₂ _ b M (le_max_right _ _) hb) l M₂ h₂]

/-! ## Openings -/

/-- The name map after opening an activation at `ρ` whose own names are `own`:
their copies go to `τ`. -/
def openMap (ρ : Path) (own : List X₁) (τ ν : Nm X₁ → Nm X₂) : Nm X₁ → Nm X₂
  | .inst ρ₀ m => if ρ₀ = ρ ∧ ownKey own m = true then τ m else ν (.inst ρ₀ m)
  | .src s => ν (.src s)

omit [DecidableEq X₂] in
theorem openMap_own {ρ : Path} {own : List X₁} {τ ν : Nm X₁ → Nm X₂} {m : Nm X₁}
    (h : ownKey own m = true) : openMap ρ own τ ν (.inst ρ m) = τ m := by
  simp [openMap, h]

omit [DecidableEq X₂] in
theorem openMap_other {ρ : Path} {own : List X₁} {τ ν : Nm X₁ → Nm X₂} {n : Nm X₁}
    (h : ∀ m, n ≠ .inst ρ m) : openMap ρ own τ ν n = ν n := by
  cases n with
  | src s => rfl
  | inst ρ₀ m =>
      have hne : ρ₀ ≠ ρ := by
        rintro rfl
        exact h m rfl
      simp [openMap, hne]

variable [DecidableEq S]

omit [DecidableEq S] in
/-- **Activating related lambdas** on related arguments at fresh paths gives
related bodies: the copies of the owned names are related, and the second
side's reserved names of the body become copies too. -/
theorem activate_lam {ν μ : Nm X₁ → Nm X₂} {x₁ : Nm X₁} {own₁ : List X₁} {b₁ : Tm S X₁}
    {x₂ : Nm X₂} {own₂ : List X₂} {b₂ : Tm S X₂} {νb μb : Nm X₁ → Nm X₂} {Rb : List (Nm X₂)}
    {ok : Bool}
    (hνb : ∀ n, ownKey own₁ n = false → νb n = ν n) (hμx : μb x₁ = x₂)
    (hb : Rel C νb μb .code Rb ok b₁ b₂)
    (hown : ∀ n ∈ freeNames b₁, ownKey own₂ (νb n) = ownKey own₁ n)
    (hres : ∀ m ∈ Rb, ownKey own₂ m = true)
    (hcl : ∀ x ∈ freeParams b₁, x = x₁)
    {a₁ : Tm S X₁} {a₂ : Tm S X₂} (ha : Rel C ν μ .val [] true a₁ a₂)
    (hca₁ : ∀ m ∈ freeNames a₁, OK₁ C m) (hpa₁ : freeParams a₁ = [])
    (hca₂ : ∀ m ∈ freeNames a₂, OK₂ C m) (hpa₂ : freeParams a₂ = [])
    {ρ ρ' : Path}
    (hav : ∀ n, (n ∈ freeNames (.lam x₁ own₁ b₁ : Tm S X₁) ∨ n ∈ freeNames a₁) → ∀ m, n ≠ .inst ρ m) :
    Rel C (openMap ρ own₁ (fun m => .inst ρ' (νb m)) ν) μ .code (Rb.map (Nm.inst ρ')) ok
      (subst (renameOwn ρ own₁) (Sub.single x₁ a₁) b₁)
      (subst (renameOwn ρ' own₂) (Sub.single x₂ a₂) b₂) := by
  refine hb.substitute {
    names := ?_, params := ?_, res := ?_, resInj := ?_, rnPres := C.preserve_inst ρ',
    cap₁ := ?_, capφ₁ := ?_, cap₂ := ?_,
    capφ₂ := ?_, capR := ?_ }
  · intro n hn
    by_cases ho : ownKey own₁ n = true
    · have h2 : ownKey own₂ (νb n) = true := by rw [hown n hn]; exact ho
      simp only [renameOwn, ho, h2, if_true, Option.getD_some]
      rw [← openMap_own (ρ := ρ) (τ := fun m => Nm.inst ρ' (νb m)) (ν := ν) ho]
      exact .var (.inst ρ n) <| by
        rw [openMap_own (ρ := ρ) (τ := fun m => Nm.inst ρ' (νb m)) (ν := ν) ho]
        exact C.varHole_rename (C.varHole_instL ρ (hb.varHole_free hn))
          (C.preserve_inst ρ' (νb n))
    · have ho' : ownKey own₁ n = false := by simpa using ho
      have h2 : ownKey own₂ (νb n) = false := by rw [hown n hn]; exact ho'
      simp only [renameOwn, ho', h2, Bool.false_eq_true, if_false, Option.getD_none]
      rw [hνb n ho', ← openMap_other (ρ := ρ) (own := own₁) (τ := fun m => Nm.inst ρ' (νb m))
        (ν := ν) (hav n (Or.inl (mem_freeNames_lam.2 ⟨hn, ho'⟩)))]
      exact .var n <| by
        rw [openMap_other (ρ := ρ) (own := own₁) (τ := fun m => Nm.inst ρ' (νb m))
          (ν := ν) (hav n (Or.inl (mem_freeNames_lam.2 ⟨hn, ho'⟩))), ← hνb n ho']
        exact hb.varHole_free hn
  · intro x hx
    obtain rfl := hcl x hx
    simp only [Sub.single, if_true, Option.getD_some, hμx]
    refine ha.congr (fun m hm => (openMap_other (hav m (Or.inr hm))).symm) (fun _ _ => rfl)
  · intro m hm
    simp [renameOwn, hres m hm]
  · intro m _ m' _ e
    exact Nm.inst.inj e |>.2
  · intro n _ w hw
    simp only [renameOwn] at hw
    split at hw
    · injection hw with hw
      subst hw
      exact ⟨by simp [freeNames, OK₁], rfl⟩
    · cases hw
  · intro x hx w hw
    obtain rfl := hcl x hx
    simp only [Sub.single, if_true] at hw
    injection hw with hw
    subst hw
    exact ⟨hca₁, hpa₁⟩
  · intro n _ w hw
    simp only [renameOwn] at hw
    split at hw
    · injection hw with hw
      subst hw
      exact ⟨by simp [freeNames, OK₂], rfl⟩
    · cases hw
  · intro x hx w hw
    obtain rfl := hcl x hx
    simp only [Sub.single, hμx, if_true] at hw
    injection hw with hw
    subst hw
    exact ⟨hca₂, hpa₂⟩
  · intro m _ w hw
    simp only [renameOwn] at hw
    split at hw
    · injection hw with hw
      subst hw
      exact ⟨by simp [freeNames, OK₂], rfl⟩
    · cases hw

omit [DecidableEq S] in
/-- **Opening a pending construct on the first side** (a `let` or a `new`
block): its own names become copies at `ρ`, related to the reserved names they
were bound to; the second side does not move. -/
theorem open_body {ν νi μ : Nm X₁ → Nm X₂} {own : List X₁} {ℓ : Nm X₁} {k : Kd}
    {Res : List (Nm X₂)} {ok : Bool} {u₁ : Tm S X₁} {u₂ : Tm S X₂}
    (hνi : ∀ n, ownKey own n = false → νi n = ν n) (hu : Rel C νi μ k Res ok u₁ u₂)
    (hfp : freeParams u₁ = []) (v₁ : Tm S X₁) {ρ : Path}
    (hav : ∀ n ∈ freeNames u₁, ownKey own n = false → ∀ m, n ≠ .inst ρ m) :
    Rel C (openMap ρ own νi ν) μ k Res ok
      (subst (renameOwn ρ own) (Sub.single ℓ v₁) u₁) u₂ := by
  have h := hu.substitute (θ₁ := renameOwn ρ own) (φ₁ := Sub.single ℓ v₁) (θ₂ := Sub.none)
    (φ₂ := Sub.none) (ν' := openMap ρ own νi ν) (μ' := μ) (rn := id) {
      names := ?_, params := ?_, res := ?_, resInj := ?_, rnPres := C.preserve_refl,
      cap₁ := ?_, capφ₁ := ?_, cap₂ := ?_,
      capφ₂ := ?_, capR := ?_ }
  · rw [List.map_id, subst_none_none] at h
    exact h
  · intro n hn
    by_cases ho : ownKey own n = true
    · simp only [renameOwn, ho, if_true, Option.getD_some, Sub.none, Option.getD_none]
      rw [← openMap_own (ρ := ρ) (τ := νi) (ν := ν) ho]
      exact .var (.inst ρ n) <| by
        rw [openMap_own (ρ := ρ) (τ := νi) (ν := ν) ho]
        exact C.varHole_instL ρ (hu.varHole_free hn)
    · have ho' : ownKey own n = false := by simpa using ho
      simp only [renameOwn, ho', Bool.false_eq_true, if_false, Option.getD_none, Sub.none]
      rw [hνi n ho', ← openMap_other (ρ := ρ) (own := own) (τ := νi) (ν := ν) (hav n hn ho')]
      exact .var n <| by
        rw [openMap_other (ρ := ρ) (own := own) (τ := νi) (ν := ν) (hav n hn ho'), ← hνi n ho']
        exact hu.varHole_free hn
  · intro x hx
    rw [hfp] at hx
    cases hx
  · intro m _
    rfl
  · intro m _ m' _ e
    exact e
  · intro n _ w hw
    simp only [renameOwn] at hw
    split at hw
    · injection hw with hw
      subst hw
      exact ⟨by simp [freeNames, OK₁], rfl⟩
    · cases hw
  · intro x hx
    rw [hfp] at hx
    cases hx
  · intro n _ w hw
    cases hw
  · intro x hx
    rw [hfp] at hx
    cases hx
  · intro m _ w hw
    cases hw

omit [DecidableEq S] in
/-- **Substituting related values for a store name** on both sides. -/
theorem subst_var {ν μ : Nm X₁ → Nm X₂} {k : Kd} {Res : List (Nm X₂)} {ok : Bool}
    {b₁ : Tm S X₁}
    {b₂ : Tm S X₂} (hb : Rel C ν μ k Res ok b₁ b₂) {f : Nm X₁} {w₁ : Tm S X₁} {w₂ : Tm S X₂}
    (hw : Rel C ν μ .val [] true w₁ w₂) (hcw₁ : ∀ m ∈ freeNames w₁, OK₁ C m) (hpw₁ : freeParams w₁ = [])
    (hcw₂ : ∀ m ∈ freeNames w₂, OK₂ C m) (hpw₂ : freeParams w₂ = [])
    (hinj : ∀ n ∈ freeNames b₁, ν n = ν f → n = f) (hfR : ν f ∉ Res) :
    Rel C ν μ k Res ok (subst (Sub.single f w₁) Sub.none b₁)
      (subst (Sub.single (ν f) w₂) Sub.none b₂) := by
  have h := hb.substitute (θ₁ := Sub.single f w₁) (φ₁ := Sub.none) (θ₂ := Sub.single (ν f) w₂)
    (φ₂ := Sub.none) (ν' := ν) (μ' := μ) (rn := id) {
      names := ?_, params := ?_, res := ?_, resInj := ?_, rnPres := C.preserve_refl,
      cap₁ := ?_, capφ₁ := ?_, cap₂ := ?_,
      capφ₂ := ?_, capR := ?_ }
  · rw [List.map_id] at h
    exact h
  · intro n hn
    by_cases hnf : n = f
    · subst hnf
      simp only [Sub.single, if_true, Option.getD_some]
      exact hw
    · have hne : ν n ≠ ν f := fun e => hnf (hinj n hn e)
      simp only [Sub.single, hnf, hne, if_false, Option.getD_none]
      exact .var n (hb.varHole_free hn)
  · intro x hx
    exact .pvar x (hb.parOK_free hx)
  · intro m hm
    have hne : m ≠ ν f := fun e => hfR (e ▸ hm)
    simp [Sub.single, hne]
  · intro m _ m' _ e
    exact e
  · intro n _ w hw'
    simp only [Sub.single] at hw'
    split at hw'
    · injection hw' with hw'
      subst hw'
      exact ⟨hcw₁, hpw₁⟩
    · cases hw'
  · intro x _ w hw'
    cases hw'
  · intro n _ w hw'
    simp only [Sub.single] at hw'
    split at hw'
    · injection hw' with hw'
      subst hw'
      exact ⟨hcw₂, hpw₂⟩
    · cases hw'
  · intro x _ w hw'
    cases hw'
  · intro m hm w hw'
    have hne : m ≠ ν f := fun e => hfR (e ▸ hm)
    simp [Sub.single, hne] at hw'


/-! ## More about the relation -/

omit [DecidableEq S] in
/-- Every free name of the second side is the image of a free name of the
first, or reserved. -/
theorem Rel.mem_freeNames_rev {ν μ : Nm X₁ → Nm X₂} {k : Kd} {Res : List (Nm X₂)} {ok : Bool}
    {t₁ : Tm S X₁} {t₂ : Tm S X₂} (h : Rel C ν μ k Res ok t₁ t₂) :
    ∀ {m}, m ∈ freeNames t₂ → (∃ n ∈ freeNames t₁, ν n = m) ∨ m ∈ Res := by
  induction h with
  | sym s => intro m hm; simp [freeNames] at hm
  | fn F => intro m hm; simp [freeNames] at hm
  | var n _ =>
      intro m hm
      simp only [freeNames, List.mem_singleton] at hm
      exact Or.inl ⟨n, by simp [freeNames], hm.symm⟩
  | pvar x _ => intro m hm; simp [freeNames] at hm
  | quote _ => intro m hm; simp [freeNames] at hm
  | ctx _ _ _ => intro m hm; simp [freeNames] at hm
  | pquote _ _ _ ih =>
      intro m hm
      simp only [freeNames] at hm ⊢
      exact ih hm
  | app _ _ ihf iha =>
      intro m hm
      simp only [freeNames, List.mem_append] at hm
      rcases hm with hm | hm
      · rcases ihf hm with ⟨n, hn, e⟩ | hr
        · exact Or.inl ⟨n, by simp [freeNames, hn], e⟩
        · exact Or.inr (List.mem_append_left _ hr)
      · rcases iha hm with ⟨n, hn, e⟩ | hr
        · exact Or.inl ⟨n, by simp [freeNames, hn], e⟩
        · exact Or.inr (List.mem_append_right _ hr)
  | letP _ _ _ _ ihp ihw ihb =>
      intro m hm
      simp only [freeNames, List.mem_append] at hm
      rcases hm with (hm | hm) | hm
      · rcases ihp hm with ⟨n, hn, e⟩ | hr
        · exact Or.inl ⟨n, by simp [freeNames, hn], e⟩
        · exact Or.inr (by simp [hr])
      · rcases ihw hm with ⟨n, hn, e⟩ | hr
        · exact Or.inl ⟨n, by simp [freeNames, hn], e⟩
        · exact Or.inr (by simp [hr])
      · rcases ihb hm with ⟨n, hn, e⟩ | hr
        · exact Or.inl ⟨n, by simp [freeNames, hn], e⟩
        · exact Or.inr (by simp [hr])
  | alt _ _ _ ih₁ ih₂ =>
      intro m hm
      simp only [freeNames, List.mem_append] at hm
      rcases hm with hm | hm
      · rcases ih₁ hm with ⟨n, hn, e⟩ | hr
        · exact Or.inl ⟨n, by simp [freeNames, hn], e⟩
        · exact Or.inr (List.mem_append_left _ hr)
      · rcases ih₂ hm with ⟨n, hn, e⟩ | hr
        · exact Or.inl ⟨n, by simp [freeNames, hn], e⟩
        · exact Or.inr (List.mem_append_right _ hr)
  | @lam ν μ k x₁ own₁ b₁ x₂ own₂ b₂ νb μb Rb _ hνb _ _ _ _ _ hown hres _ _ _ _ _ _ ihb =>
      intro m hm
      rw [mem_freeNames_lam] at hm
      obtain ⟨hm, hk⟩ := hm
      rcases ihb hm with ⟨n, hn, rfl⟩ | hr
      · have ho : ownKey own₁ n = false := by rw [← hown n hn]; exact hk
        exact Or.inl ⟨n, mem_freeNames_lam.2 ⟨hn, ho⟩, (hνb n ho).symm⟩
      · rw [hres _ hr] at hk
        cases hk
  | letAct _ hνi _ _ _ _ _ _ hlive _ ihw ihp ihb =>
      intro m hm
      simp only [freeNames, List.mem_append] at hm
      rcases hm with (hm | hm) | hm
      · rcases ihp hm with ⟨n, hn, rfl⟩ | hr
        · cases ho : ownKey _ n
          · exact Or.inl ⟨n, mem_freeNames_letAct.2 (Or.inl ⟨Or.inl hn, ho⟩), (hνi n ho).symm⟩
          · exact Or.inr (by simp [hlive n (List.mem_append_left _ hn) ho])
        · exact Or.inr (by simp [hr])
      · rcases ihw hm with ⟨n, hn, e⟩ | hr
        · exact Or.inl ⟨n, mem_freeNames_letAct.2 (Or.inr hn), e⟩
        · exact Or.inr (by simp [hr])
      · rcases ihb hm with ⟨n, hn, rfl⟩ | hr
        · cases ho : ownKey _ n
          · exact Or.inl ⟨n, mem_freeNames_letAct.2 (Or.inl ⟨Or.inr hn, ho⟩), (hνi n ho).symm⟩
          · exact Or.inr (by simp [hlive n (List.mem_append_right _ hn) ho])
        · exact Or.inr (by simp [hr])
  | newAct hνi _ _ _ hlive _ ihb =>
      intro m hm
      rcases ihb hm with ⟨n, hn, rfl⟩ | hr
      · cases ho : ownKey _ n
        · exact Or.inl ⟨n, mem_freeNames_newAct.2 ⟨hn, ho⟩, (hνi n ho).symm⟩
        · exact Or.inr (List.mem_append_left _ (hlive n hn ho))
      · exact Or.inr (List.mem_append_right _ hr)

omit [DecidableEq S] in
/-- Free names of a value pair on the second side are images of the first's. -/
theorem Rel.mem_freeNames_val {ν μ : Nm X₁ → Nm X₂} {k : Kd} {ok : Bool}
    {t₁ : Tm S X₁} {t₂ : Tm S X₂}
    (h : Rel C ν μ k [] ok t₁ t₂) {m : Nm X₂} (hm : m ∈ freeNames t₂) :
    ∃ n ∈ freeNames t₁, ν n = m := by
  rcases h.mem_freeNames_rev hm with h' | hr
  · exact h'
  · cases hr

omit [DecidableEq S] in
/-- Free parameters correspond backwards too. -/
theorem Rel.freeParams_nil {ν μ : Nm X₁ → Nm X₂} {k : Kd} {Res : List (Nm X₂)} {ok : Bool}
    {t₁ : Tm S X₁} {t₂ : Tm S X₂} (h : Rel C ν μ k Res ok t₁ t₂) :
    ∀ {x}, x ∈ freeParams t₂ → ∃ y ∈ freeParams t₁, μ y = x := by
  induction h with
  | sym s => intro x hx; simp [freeParams] at hx
  | fn F => intro x hx; simp [freeParams] at hx
  | var n _ => intro x hx; simp [freeParams] at hx
  | pvar y _ =>
      intro x hx
      simp only [freeParams, List.mem_singleton] at hx
      exact ⟨y, by simp [freeParams], hx.symm⟩
  | quote _ => intro x hx; simp [freeParams] at hx
  | ctx _ _ _ => intro x hx; simp [freeParams] at hx
  | pquote _ _ _ ih =>
      intro x hx
      simp only [freeParams] at hx ⊢
      exact ih hx
  | app _ _ ihf iha =>
      intro x hx
      simp only [freeParams, List.mem_append] at hx
      rcases hx with hx | hx
      · obtain ⟨y, hy, e⟩ := ihf hx; exact ⟨y, by simp [freeParams, hy], e⟩
      · obtain ⟨y, hy, e⟩ := iha hx; exact ⟨y, by simp [freeParams, hy], e⟩
  | letP _ _ _ _ ihp ihw ihb =>
      intro x hx
      simp only [freeParams, List.mem_append] at hx
      rcases hx with (hx | hx) | hx
      · obtain ⟨y, hy, e⟩ := ihp hx; exact ⟨y, by simp [freeParams, hy], e⟩
      · obtain ⟨y, hy, e⟩ := ihw hx; exact ⟨y, by simp [freeParams, hy], e⟩
      · obtain ⟨y, hy, e⟩ := ihb hx; exact ⟨y, by simp [freeParams, hy], e⟩
  | alt _ _ _ ih₁ ih₂ =>
      intro x hx
      simp only [freeParams, List.mem_append] at hx
      rcases hx with hx | hx
      · obtain ⟨y, hy, e⟩ := ih₁ hx; exact ⟨y, by simp [freeParams, hy], e⟩
      · obtain ⟨y, hy, e⟩ := ih₂ hx; exact ⟨y, by simp [freeParams, hy], e⟩
  | @lam ν μ k x₁ own₁ b₁ x₂ own₂ b₂ νb μb Rb _ _ hμb hμx _ _ _ _ _ _ _ _ _ _ _ ihb =>
      intro x hx
      rw [mem_freeParams_lam] at hx
      obtain ⟨hx, hne⟩ := hx
      obtain ⟨y, hy, rfl⟩ := ihb hx
      have hyx : y ≠ x₁ := by
        rintro rfl
        exact hne hμx
      exact ⟨y, mem_freeParams_lam.2 ⟨hy, hyx⟩, (hμb y hyx).symm⟩
  | @letAct ν μ k ℓ own p₁ w₁ b₁ p₂ w₂ b₂ νi Rh Rw Rp Rb _ _ _ _ _ _ hℓp hℓb _ _ _ _ _ ihw ihp ihb =>
      intro x hx
      simp only [freeParams, List.mem_append] at hx
      rcases hx with (hx | hx) | hx
      · obtain ⟨y, hy, rfl⟩ := ihp hx
        refine ⟨y, mem_freeParams_letAct.2 (Or.inl ⟨Or.inl hy, ?_⟩), rfl⟩
        rintro rfl
        exact hℓp hy
      · obtain ⟨y, hy, rfl⟩ := ihw hx
        exact ⟨y, mem_freeParams_letAct.2 (Or.inr hy), rfl⟩
      · obtain ⟨y, hy, rfl⟩ := ihb hx
        refine ⟨y, mem_freeParams_letAct.2 (Or.inl ⟨Or.inr hy, ?_⟩), rfl⟩
        rintro rfl
        exact hℓb hy
  | newAct _ _ hℓ _ _ _ ihb =>
      intro x hx
      obtain ⟨y, hy, rfl⟩ := ihb hx
      refine ⟨y, mem_freeParams_newAct.2 ⟨hy, ?_⟩, rfl⟩
      rintro rfl
      exact hℓ hy

omit [DecidableEq S] in
/-- A pair of value-shaped terms is a value pair. -/
theorem Rel.toVal {ν μ : Nm X₁ → Nm X₂} {k : Kd} {Res : List (Nm X₂)} {ok : Bool}
    {t₁ : Tm S X₁} {t₂ : Tm S X₂} (h : Rel C ν μ k Res ok t₁ t₂)
    (hv : (∃ s, t₁ = .sym s) ∨ (∃ F, t₁ = .fn F) ∨ (∃ n, t₁ = .var n) ∨ (∃ x, t₁ = .pvar x) ∨
      (∃ c, t₁ = .quote c) ∨ (∃ x own b, t₁ = .lam x own b)) :
    Res = [] ∧ Rel C ν μ .val Res true t₁ t₂ := by
  cases h with
  | sym s => exact ⟨rfl, .sym s⟩
  | fn F => exact ⟨rfl, .fn F⟩
  | var n hvh => exact ⟨rfl, .var n hvh⟩
  | pvar x hp => exact ⟨rfl, .pvar x hp⟩
  | quote hq => exact ⟨rfl, .quote hq⟩
  | ctx _ _ _ =>
      rcases hv with ⟨_, hs⟩ | ⟨_, hs⟩ | ⟨_, hs⟩ | ⟨_, hs⟩ | ⟨_, hs⟩ | ⟨_, _, _, hs⟩ <;>
        cases hs
  | pquote _ _ _ => simp at hv
  | lam hνb hμb hμx hr₁ hr₂ hb hown hres hinj hdisj hnd hpar hbare hseen =>
      exact ⟨rfl, .lam hνb hμb hμx hr₁ hr₂ hb hown hres hinj hdisj hnd hpar hbare hseen⟩
  | app => simp at hv
  | letP => simp at hv
  | alt => simp at hv
  | letAct => simp at hv
  | newAct => simp at hv

end IdSlot

end Mettapedia.GSLT.LanguageDef.TemplateScope
