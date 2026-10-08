import Mettapedia.GSLT.LanguageDef.TemplateScope.IdentitySlotSimulation

/-!
# Template scope: related runs

The simulation between related terms (`IdSlot.Rel`) under the static
discipline.

## Main results

* `sim` — **first side to second side**: if the first side's run is defined,
  so is the second side's at the same fuel, and the bags are related
  pointwise, in order (`Out`): each result pair through its own extension of
  the name map, injective on everything the pair's terms and stores mention,
  with related result terms and related final stores.
* `simI` — **second side to first side**: if the second side's run is defined,
  the first side's is defined at some fuel.
-/

namespace Mettapedia.GSLT.LanguageDef.TemplateScope

open Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline

universe u v

namespace IdSlot

variable {S : Type u} {X₁ X₂ : Type v} [DecidableEq S] [DecidableEq X₁] [DecidableEq X₂]
variable {C : Setting S X₁ X₂}

/-! ## Related results -/

/-- **A related result pair**, relative to the configuration it came from: an
extension of the name map along the evaluation, under which the result terms
are related values and the final stores are related. -/
def Out (C : Setting S X₁ X₂) (π π' : Path) (ν μ : Nm X₁ → Nm X₂) (D : Set (Nm X₁))
    (Res Rc : List (Nm X₂)) (r₁ : Tm S X₁ × GStore S X₁) (r₂ : Tm S X₂ × GStore S X₂) : Prop :=
  ∃ ν' D', (∀ n ∈ freeNames r₁.1, n ∈ D') ∧ Ext π π' Res ν D ν' D' ∧
    Rel C ν' μ .val [] true r₁.1 r₂.1 ∧ freeParams r₁.1 = [] ∧ CI C ν' D' Rc r₁.2 r₂.2

omit [DecidableEq S] in
theorem Out.parent {π π' : Path} {i j : ℕ} {ν μ : Nm X₁ → Nm X₂} {D : Set (Nm X₁)}
    {Res Rc : List (Nm X₂)} {r₁ : Tm S X₁ × GStore S X₁} {r₂ : Tm S X₂ × GStore S X₂}
    (h : Out C (π ++ [i]) (π' ++ [j]) ν μ D Res Rc r₁ r₂) : Out C π π' ν μ D Res Rc r₁ r₂ := by
  obtain ⟨ν', D', h1, h2, h3, h4, h5⟩ := h
  exact ⟨ν', D', h1, h2.parent, h3, h4, h5⟩

omit [DecidableEq S] in
theorem Out.parent₁ {π π' : Path} {i : ℕ} {ν μ : Nm X₁ → Nm X₂} {D : Set (Nm X₁)}
    {Res Rc : List (Nm X₂)} {r₁ : Tm S X₁ × GStore S X₁} {r₂ : Tm S X₂ × GStore S X₂}
    (h : Out C (π ++ [i]) π' ν μ D Res Rc r₁ r₂) : Out C π π' ν μ D Res Rc r₁ r₂ := by
  obtain ⟨ν', D', h1, h2, h3, h4, h5⟩ := h
  exact ⟨ν', D', h1, h2.parent₁, h3, h4, h5⟩

omit [DecidableEq S] in
theorem Out.res_mono {π π' : Path} {ν μ : Nm X₁ → Nm X₂} {D : Set (Nm X₁)}
    {Res Res' Rc : List (Nm X₂)} {r₁ : Tm S X₁ × GStore S X₁} {r₂ : Tm S X₂ × GStore S X₂}
    (h : Out C π π' ν μ D Res Rc r₁ r₂) (hR : ∀ m ∈ Res, m ∈ Res') :
    Out C π π' ν μ D Res' Rc r₁ r₂ := by
  obtain ⟨ν', D', h1, h2, h3, h4, h5⟩ := h
  exact ⟨ν', D', h1, h2.res_mono hR, h3, h4, h5⟩

omit [DecidableEq S] in
theorem Out.after {π π' : Path} {ν ν₁ μ : Nm X₁ → Nm X₂} {D D₁ : Set (Nm X₁)}
    {R₁ R₂ Rc : List (Nm X₂)} {r₁ : Tm S X₁ × GStore S X₁} {r₂ : Tm S X₂ × GStore S X₂}
    (hE : Ext π π' R₁ ν D ν₁ D₁) (h : Out C π π' ν₁ μ D₁ R₂ Rc r₁ r₂) :
    Out C π π' ν μ D (R₁ ++ R₂) Rc r₁ r₂ := by
  obtain ⟨ν', D', h1, h2, h3, h4, h5⟩ := h
  exact ⟨ν', D', h1, hE.trans h2, h3, h4, h5⟩

omit [DecidableEq S] in
theorem Out.drop {π π' : Path} {ν μ : Nm X₁ → Nm X₂} {D : Set (Nm X₁)}
    {Res A Rc : List (Nm X₂)} {r₁ : Tm S X₁ × GStore S X₁} {r₂ : Tm S X₂ × GStore S X₂}
    (h : Out C π π' ν μ D Res (A ++ Rc) r₁ r₂) : Out C π π' ν μ D Res Rc r₁ r₂ := by
  obtain ⟨ν', D', h1, h2, h3, h4, h5⟩ := h
  exact ⟨ν', D', h1, h2, h3, h4, h5.drop⟩

omit [DecidableEq S] in
/-- A value pair with nothing changed. -/
theorem Out.value {π π' : Path} {ν μ : Nm X₁ → Nm X₂} {D : Set (Nm X₁)} {Res Rc : List (Nm X₂)}
    {t₁ : Tm S X₁} {t₂ : Tm S X₂} {σ₁ : GStore S X₁} {σ₂ : GStore S X₂}
    (hrel : Rel C ν μ .val [] true t₁ t₂) (hfv : ∀ n ∈ freeNames t₁, n ∈ D) (hfp : freeParams t₁ = [])
    (hci : CI C ν D Rc σ₁ σ₂) : Out C π π' ν μ D Res Rc (t₁, σ₁) (t₂, σ₂) :=
  ⟨ν, D, hfv, (Ext.refl π π' [] ν D).res_mono (fun _ h => absurd h (List.not_mem_nil)), hrel,
    hfp, hci⟩

/-! ## Freshness along a chain of evaluations -/

omit [DecidableEq S] [DecidableEq X₁] [DecidableEq X₂] in
theorem Ext.avoid₁ {π π'' : Path} {i j : ℕ} (hij : i ≠ j) {R : List (Nm X₂)}
    {ν ν₁ : Nm X₁ → Nm X₂} {D D₁ : Set (Nm X₁)} (hE : Ext (π ++ [i]) π'' R ν D ν₁ D₁)
    (hD : ∀ n ∈ D, Avoid (π ++ [j]) n) : ∀ n ∈ D₁, Avoid (π ++ [j]) n := by
  intro n hn
  by_cases h : n ∈ D
  · exact hD n h
  · exact (hE.new n hn h).1.avoid_sibling hij

omit [DecidableEq S] [DecidableEq X₁] [DecidableEq X₂] in
theorem Ext.avoid₂ {π'' π' : Path} {i j : ℕ} (hij : i ≠ j) {R : List (Nm X₂)}
    {ν ν₁ : Nm X₁ → Nm X₂} {D D₁ : Set (Nm X₁)} (hE : Ext π'' (π' ++ [i]) R ν D ν₁ D₁)
    (hD : ∀ n ∈ D, Avoid (π' ++ [j]) (ν n)) (hR : ∀ m ∈ R, Avoid (π' ++ [j]) m) :
    ∀ n ∈ D₁, Avoid (π' ++ [j]) (ν₁ n) := by
  intro n hn
  by_cases h : n ∈ D
  · rw [hE.agree n h]; exact hD n h
  · rcases (hE.new n hn h).2 with hp | hr
    · exact hp.avoid_sibling hij
    · exact hR _ hr

/-! ## Free names after an opening -/

omit [DecidableEq S] [DecidableEq X₂] in
theorem mem_freeNames_open {own : List X₁} {ρ : Path} {ℓ : Nm X₁} {v b : Tm S X₁} {n : Nm X₁}
    (hn : n ∈ freeNames (subst (renameOwn ρ own) (Sub.single ℓ v) b)) :
    (n ∈ freeNames b ∧ ownKey own n = false) ∨
      (∃ m ∈ freeNames b, ownKey own m = true ∧ n = .inst ρ m) ∨
      (ℓ ∈ freeParams b ∧ n ∈ freeNames v) := by
  rcases mem_freeNames_subst' b _ _ n hn with ⟨h1, h2⟩ | ⟨m, hm, w, hw, hnw⟩ | ⟨x, hx, w, hw, hnw⟩
  · left
    refine ⟨h1, ?_⟩
    cases ho : ownKey own n
    · rfl
    · simp [renameOwn, ho] at h2
  · right; left
    simp only [renameOwn] at hw
    split at hw
    · rename_i ho
      injection hw with hw
      subst hw
      simp only [freeNames, List.mem_singleton] at hnw
      exact ⟨m, hm, ho, hnw⟩
    · cases hw
  · right; right
    simp only [Sub.single] at hw
    split at hw
    · rename_i hxe
      subst hxe
      injection hw with hw
      subst hw
      exact ⟨hx, hnw⟩
    · cases hw

omit [DecidableEq S] [DecidableEq X₂] in
theorem freeParams_open {own : List X₁} {ρ : Path} {ℓ : Nm X₁} {v b : Tm S X₁}
    (hb : ∀ x ∈ freeParams b, x = ℓ) (hv : freeParams v = []) :
    freeParams (subst (renameOwn ρ own) (Sub.single ℓ v) b) = [] := by
  apply List.eq_nil_iff_forall_not_mem.2
  intro x hx
  rcases mem_freeParams_subst' b _ _ x hx with ⟨h1, h2⟩ | ⟨m, _, w, hw, hxw⟩ | ⟨y, hy, w, hw, hxw⟩
  · obtain rfl := hb x h1
    simp [Sub.single] at h2
  · simp only [renameOwn] at hw
    split at hw
    · injection hw with hw
      subst hw
      simp [freeParams] at hxw
    · cases hw
  · obtain rfl := hb y hy
    simp only [Sub.single, if_true] at hw
    injection hw with hw
    subst hw
    rw [hv] at hxw
    cases hxw

/-! ## A chain of `new` blocks ending in a lambda -/

/-- **A chain of `new` blocks around a lambda** evaluates, on the first side,
to a lambda related to the second side's lambda, with the same store: each
block's names become copies whose images are the block's reserved names. -/
theorem newChain [CodeId X₁] {P₁ : S → Option (Tm S X₁)} : ∀ (n : ℕ) {ρ : Path} {σ₁ : GStore S X₁}
    {ν μ : Nm X₁ → Nm X₂} {k : Kd} {Res : List (Nm X₂)} {w₁ : Tm S X₁} {x₂ : Nm X₂}
    {own₂ : List X₂} {b₂ : Tm S X₂} {L₁ : Result S X₁} {ok : Bool},
    Rel C ν μ k Res ok w₁ (.lam x₂ own₂ b₂) → freeParams w₁ = [] → Res.Nodup →
    (∀ n ∈ freeNames w₁, OldAt ρ n) →
    run .static P₁ n ρ σ₁ w₁ = some L₁ →
    ∃ v₁ ν', L₁ = [(v₁, σ₁)] ∧ Rel C ν' μ .val [] true v₁ (.lam x₂ own₂ b₂) ∧
      freeParams v₁ = [] ∧ (∀ n, OldAt ρ n → ν' n = ν n) ∧
      (∀ n ∈ freeNames v₁, n ∈ freeNames w₁ ∨ (NewAt ρ n ∧ ν' n ∈ Res)) ∧
      (∀ n ∈ freeNames v₁, ∀ n' ∈ freeNames v₁, NewAt ρ n → NewAt ρ n' → ν' n = ν' n' → n = n')
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h => by cases h
  | n + 1, ρ, σ₁, ν, μ, k, Res, w₁, x₂, own₂, b₂, L₁, _, hR, hfp, hnd, hold, hrun => by
      cases hR with
      | lam hνb hμb hμx hr₁ hr₂ hb hown hres hinj hdisj hnd' hpar hbare hseen =>
          injection hrun with hrun
          subst hrun
          refine ⟨_, ν, rfl, .lam hνb hμb hμx hr₁ hr₂ hb hown hres hinj hdisj hnd' hpar hbare hseen, hfp,
            fun _ _ => rfl, fun n hn => Or.inl hn, ?_⟩
          intro n hn _ _ hnew _ _
          exact absurd (hold n hn) hnew.not_oldAt
      | @newAct _ _ ℓ own b₁ _ νi Rh Rb _ hνi hr hℓ hb hlive hinj =>
          cases n with
          | zero =>
              change step .static P₁ (run .static P₁ 0) ρ σ₁ _ = some L₁ at hrun
              simp [step, run, bindOpt] at hrun
          | succ n =>
              change step .static P₁ (run .static P₁ (n + 1)) ρ σ₁ _ = some L₁ at hrun
              simp only [step] at hrun
              rw [show run .static P₁ (n + 1) (ρ ++ [0]) σ₁ (.lam ℓ own b₁) =
                  some [(.lam ℓ own b₁, σ₁)] from rfl, bindOpt_some_singleton,
                show run .static P₁ (n + 1) (ρ ++ [1]) σ₁ (.lam ℓ [] (.pvar ℓ)) =
                  some [(.lam ℓ [] (.pvar ℓ), σ₁)] from rfl, bindOpt_some_singleton] at hrun
              simp only [activate] at hrun
              have hfpb : freeParams b₁ = [] := by
                apply List.eq_nil_iff_forall_not_mem.2
                intro x hx
                have hxne : x ≠ ℓ := by
                  rintro rfl
                  exact hℓ hx
                have := (mem_freeParams_newAct (S := S) (ℓ := ℓ) (own := own) (b := b₁)).2 ⟨hx, hxne⟩
                rw [hfp] at this
                cases this
              have hopen := open_body (ℓ := ℓ) hνi hb hfpb (.lam ℓ [] (.pvar ℓ)) (ρ := ρ ++ [2])
                (fun n hn ho m e => by
                  have hw := hold n (mem_freeNames_newAct.2 ⟨hn, ho⟩)
                  subst e
                  exact hw _ (by simp [tags]) (SPre.child ρ 2))
              have hfp' : freeParams (subst (renameOwn (ρ ++ [2]) own)
                  (Sub.single ℓ (.lam ℓ [] (.pvar ℓ))) b₁) = [] :=
                freeParams_open (fun x hx => by rw [hfpb] at hx; cases hx) (by simp [freeParams])
              have hnd' : Rb.Nodup := (List.nodup_append.1 hnd).2.1
              obtain ⟨v₁, ν'', hL, hrel, hfpv, hagree, hfv, hinj'⟩ :=
                newChain (n + 1) hopen hfp' hnd' (by
                  intro m hm
                  rcases mem_freeNames_open hm with ⟨h1, h2⟩ | ⟨m₀, hm₀, ho, rfl⟩ | ⟨h1, _⟩
                  · exact (hold m (mem_freeNames_newAct.2 ⟨h1, h2⟩)).child 2
                  · cases m₀ with
                    | src s => exact oldAt_inst_self _ s
                    | inst _ _ => simp [ownKey] at ho
                  · rw [hfpb] at h1; cases h1) hrun
              have hagree' : ∀ n, OldAt ρ n → ν'' n = ν n := by
                intro m hm
                rw [hagree m (hm.child 2), openMap_other]
                rintro m' rfl
                exact hm _ (by simp [tags]) (SPre.child ρ 2)
              refine ⟨v₁, ν'', hL, hrel, hfpv, hagree', ?_, ?_⟩
              · intro m hm
                rcases hfv m hm with h | ⟨hnew, hres⟩
                · rcases mem_freeNames_open h with ⟨h1, h2⟩ | ⟨m₀, hm₀, ho, rfl⟩ | ⟨h1, _⟩
                  · exact Or.inl (mem_freeNames_newAct.2 ⟨h1, h2⟩)
                  · cases m₀ with
                    | src s =>
                        refine Or.inr ⟨newAt_inst 2 s, ?_⟩
                        rw [hagree _ (oldAt_inst_self _ s), openMap_own ho]
                        exact List.mem_append_left _ (hlive _ hm₀ ho)
                    | inst _ _ => simp [ownKey] at ho
                  · rw [hfpb] at h1; cases h1
                · exact Or.inr ⟨hnew.parent, List.mem_append_right _ hres⟩
              · -- a new name is a renamed own name, or was made inside
                have hclass : ∀ m ∈ freeNames v₁, NewAt ρ m →
                    (∃ m₀ ∈ freeNames b₁, ownKey own m₀ = true ∧ m = .inst (ρ ++ [2]) m₀ ∧
                      ν'' m = νi m₀) ∨ (NewAt (ρ ++ [2]) m ∧ ν'' m ∈ Rb) := by
                  intro m hm hnew
                  rcases hfv m hm with h | hr
                  · rcases mem_freeNames_open h with ⟨h1, h2⟩ | ⟨m₀, hm₀, ho, rfl⟩ | ⟨h1, _⟩
                    · exact absurd (hold m (mem_freeNames_newAct.2 ⟨h1, h2⟩)) hnew.not_oldAt
                    · cases m₀ with
                      | src s =>
                          refine Or.inl ⟨_, hm₀, ho, rfl, ?_⟩
                          rw [hagree _ (oldAt_inst_self _ s), openMap_own ho]
                      | inst _ _ => simp [ownKey] at ho
                    · rw [hfpb] at h1; cases h1
                  · exact Or.inr hr
                intro m hm m' hm' hn hn' he
                rcases hclass m hm hn with ⟨m₀, hm₀, ho, rfl, e₀⟩ | ⟨hn₂, hr⟩ <;>
                  rcases hclass m' hm' hn' with ⟨m₀', hm₀', ho', rfl, e₀'⟩ | ⟨hn₂', hr'⟩
                · rw [e₀, e₀'] at he
                  rw [hinj m₀ hm₀ m₀' hm₀' ho ho' he]
                · rw [e₀] at he
                  have h1 : νi m₀ ∈ Rh := hlive m₀ hm₀ ho
                  rw [he] at h1
                  exact absurd hr' (List.disjoint_of_nodup_append hnd h1)
                · rw [e₀'] at he
                  have h1 : νi m₀' ∈ Rh := hlive m₀' hm₀' ho'
                  rw [← he] at h1
                  exact absurd hr (List.disjoint_of_nodup_append hnd h1)
                · exact hinj' m hm m' hm' hn₂ hn₂' he


omit [DecidableEq S] [DecidableEq X₂] in
/-- **The configuration after a chain of `new` blocks** evaluated at `π ++ [i]`
on the first side only: its copies' images are the chain's reserved names. -/
theorem newChain_cfg {ν ν' : Nm X₁ → Nm X₂} {D : Set (Nm X₁)} {Rw R : List (Nm X₂)}
    {σ₁ : GStore S X₁} {σ₂ : GStore S X₂} {π π' : Path} {i : ℕ} {v₁ w₁ : Tm S X₁}
    (hci : CI C ν D (Rw ++ R) σ₁ σ₂) (hF : Fresh π π' ν D (Rw ++ R))
    (hfvw : ∀ m ∈ freeNames w₁, m ∈ D)
    (hagree : ∀ n, OldAt (π ++ [i]) n → ν' n = ν n)
    (hfvv : ∀ n ∈ freeNames v₁, n ∈ freeNames w₁ ∨ (NewAt (π ++ [i]) n ∧ ν' n ∈ Rw))
    (hinjv : ∀ n ∈ freeNames v₁, ∀ n' ∈ freeNames v₁, NewAt (π ++ [i]) n →
      NewAt (π ++ [i]) n' → ν' n = ν' n' → n = n') :
    CI C ν' (D ∪ {n | n ∈ freeNames v₁}) R σ₁ σ₂ ∧ Ext π π' Rw ν D ν' (D ∪ {n | n ∈ freeNames v₁}) ∧
      (∀ n ∈ D, ν' n = ν n) ∧
      (∀ n ∈ D ∪ {n | n ∈ freeNames v₁}, n ∈ D ∨ (NewAt (π ++ [i]) n ∧ ν' n ∈ Rw)) := by
  have hold : ∀ n ∈ D, ν' n = ν n := fun n hn => hagree n ((hF.old₁ n hn).child i)
  have hclass : ∀ n ∈ D ∪ {n | n ∈ freeNames v₁}, n ∈ D ∨ (NewAt (π ++ [i]) n ∧ ν' n ∈ Rw) := by
    intro n hn
    rcases hn with hn | hn
    · exact Or.inl hn
    · rcases hfvv n hn with h | h
      · exact Or.inl (hfvw n h)
      · exact Or.inr h
  have hfv' : ∀ n ∈ D ∪ {n | n ∈ freeNames v₁}, n ∉ D → n ∈ freeNames v₁ := by
    intro n hn hnD
    rcases hn with hn | hn
    · exact absurd hn hnD
    · exact hn
  have hdj := List.disjoint_of_nodup_append hci.nodup
  refine ⟨⟨?_, (List.nodup_append.1 hci.nodup).2.1, ?_, ?_, ?_, ?_, ?_⟩, ⟨hold,
    Set.subset_union_left, ?_⟩, hold, hclass⟩
  · intro n hn n' hn' he
    rcases hclass n hn with h1 | ⟨hn1, hr1⟩ <;> rcases hclass n' hn' with h2 | ⟨hn2, hr2⟩
    · rw [hold n h1, hold n' h2] at he
      exact hci.inj h1 h2 he
    · have e : ν n = ν' n' := (hold n h1).symm.trans he
      exact absurd (List.mem_append_left _ (e ▸ hr2)) (hci.disj n h1)
    · have e : ν n' = ν' n := (hold n' h2).symm.trans he.symm
      exact absurd (List.mem_append_left _ (e ▸ hr1)) (hci.disj n' h2)
    · have hnD : n ∉ D := fun h => hn1.parent.not_oldAt (hF.old₁ n h)
      have hnD' : n' ∉ D := fun h => hn2.parent.not_oldAt (hF.old₁ n' h)
      exact hinjv n (hfv' n hn hnD) n' (hfv' n' hn' hnD') hn1 hn2 he
  · intro n hn hmem
    rcases hclass n hn with h1 | ⟨_, hr1⟩
    · rw [hold n h1] at hmem
      exact hci.disj n h1 (List.mem_append_right _ hmem)
    · exact hdj hr1 hmem
  · refine hci.store.mono Set.subset_union_left hold ?_
    intro n hn hnD
    rcases hclass n hn with h1 | ⟨_, hr1⟩
    · exact absurd h1 hnD
    · exact ⟨by by_contra hc; exact hnD (hci.store.dom n hc),
        hci.res_unbound (List.mem_append_left _ hr1)⟩
  · intro n hn
    rcases hclass n hn with h1 | ⟨hn1, _⟩
    · exact hci.ok₁ n h1
    · obtain ⟨ρ, s, rfl, _⟩ := hn1
      trivial
  · intro n hn
    rcases hclass n hn with h1 | ⟨_, hr1⟩
    · rw [hold n h1]; exact hci.ok₂ n h1
    · exact hci.okRes _ (List.mem_append_left _ hr1)
  · intro m hm
    exact hci.okRes m (List.mem_append_right _ hm)
  · intro n hn hnD
    rcases hclass n hn with h1 | ⟨hn1, hr1⟩
    · exact absurd h1 hnD
    · exact ⟨hn1.parent, Or.inr hr1⟩


/-! ## Reordering reserved names -/

omit [DecidableEq S] [DecidableEq X₁] [DecidableEq X₂] in
theorem CI.perm {ν : Nm X₁ → Nm X₂} {D : Set (Nm X₁)} {R R' : List (Nm X₂)} {σ₁ : GStore S X₁}
    {σ₂ : GStore S X₂} (h : CI C ν D R σ₁ σ₂) (hp : R.Perm R') : CI C ν D R' σ₁ σ₂ where
  inj := h.inj
  nodup := hp.nodup_iff.1 h.nodup
  disj n hn hm := h.disj n hn (hp.mem_iff.2 hm)
  store := h.store
  ok₁ := h.ok₁
  ok₂ := h.ok₂
  okRes m hm := h.okRes m (hp.mem_iff.2 hm)

omit [DecidableEq S] [DecidableEq X₁] [DecidableEq X₂] in
theorem Fresh.perm {π π' : Path} {ν : Nm X₁ → Nm X₂} {D : Set (Nm X₁)} {R R' : List (Nm X₂)}
    (h : Fresh π π' ν D R) (hp : R.Perm R') : Fresh π π' ν D R' where
  old₁ := h.old₁
  old₂ := h.old₂
  oldRes m hm := h.oldRes m (hp.mem_iff.2 hm)

omit [DecidableEq S] in
/-- Reserved names made below `π'` need no reservation. -/
theorem Out.res_newAt {π π' : Path} {ν μ : Nm X₁ → Nm X₂} {D : Set (Nm X₁)}
    {R R' Rc : List (Nm X₂)} {r₁ : Tm S X₁ × GStore S X₁} {r₂ : Tm S X₂ × GStore S X₂}
    (h : Out C π π' ν μ D R Rc r₁ r₂) (hR : ∀ m ∈ R, NewAt π' m) : Out C π π' ν μ D R' Rc r₁ r₂ := by
  obtain ⟨ν', D', h1, h2, h3, h4, h5⟩ := h
  refine ⟨ν', D', h1, ⟨h2.agree, h2.sub, fun n hn hnD => ?_⟩, h3, h4, h5⟩
  obtain ⟨hp, hi⟩ := h2.new n hn hnD
  rcases hi with hi | hi
  · exact ⟨hp, Or.inl hi⟩
  · exact ⟨hp, Or.inl (hR _ hi)⟩

/-! ## The simulation statement -/

/-- **The simulation at fuel `n`**: from a related configuration, a defined
run of the first side is matched by a defined run of the second side, with
related bags. -/
def SimAt [CodeId X₁] [CodeId X₂] (C : Setting S X₁ X₂) (P₁ : S → Option (Tm S X₁))
    (P₂ : S → Option (Tm S X₂)) (n : ℕ) : Prop :=
  ∀ {π π' : Path} {σ₁ : GStore S X₁} {σ₂ : GStore S X₂} {t₁ : Tm S X₁} {t₂ : Tm S X₂}
    {ν μ : Nm X₁ → Nm X₂} {Res Rc : List (Nm X₂)} {ok : Bool} {D : Set (Nm X₁)} {L₁ : Result S X₁},
    Rel C ν μ .code Res ok t₁ t₂ → freeParams t₁ = [] → (∀ m ∈ freeNames t₁, m ∈ D) →
    CI C ν D (Res ++ Rc) σ₁ σ₂ → Fresh π π' ν D (Res ++ Rc) →
    run .static P₁ n π σ₁ t₁ = some L₁ →
    ∃ L₂, run .static P₂ n π' σ₂ t₂ = some L₂ ∧ List.Forall₂ (Out C π π' ν μ D Res Rc) L₁ L₂

/-! ## Activation and opening on configurations -/

omit [DecidableEq S] [DecidableEq X₂] in
/-- **The configuration after activating related lambdas** at fresh paths. -/
theorem activation_ci {ν₂ : Nm X₁ → Nm X₂} {D₂ : Set (Nm X₁)} {Rc : List (Nm X₂)}
    {τ₁ : GStore S X₁} {τ₂ : GStore S X₂} (hci : CI C ν₂ D₂ Rc τ₁ τ₂) {ρ ρ' : Path}
    (hav₁ : ∀ n ∈ D₂, Avoid ρ n) (hav₂ : ∀ n ∈ D₂, Avoid ρ' (ν₂ n)) (havR : ∀ m ∈ Rc, Avoid ρ' m)
    {own₁ : List X₁} {νb : Nm X₁ → Nm X₂} {b₁ : Tm S X₁} {Rb : List (Nm X₂)}
    (hinj : ∀ n ∈ freeNames b₁, ∀ n' ∈ freeNames b₁, ownKey own₁ n = true →
      ownKey own₁ n' = true → νb n = νb n' → n = n')
    (hdisj : ∀ n ∈ freeNames b₁, ownKey own₁ n = true → νb n ∉ Rb) (hnd : Rb.Nodup)
    {body₁ : Tm S X₁}
    (hbody : ∀ n ∈ freeNames body₁, n ∈ D₂ ∨ ∃ m ∈ freeNames b₁, ownKey own₁ m = true ∧ n = .inst ρ m) :
    CI C (openMap ρ own₁ (fun m => .inst ρ' (νb m)) ν₂) (D₂ ∪ {n | n ∈ freeNames body₁})
      (Rb.map (Nm.inst ρ') ++ Rc) τ₁ τ₂ := by
  set ν₃ := openMap ρ own₁ (fun m => .inst ρ' (νb m)) ν₂ with hν₃
  have hold : ∀ n ∈ D₂, ν₃ n = ν₂ n := fun n hn => openMap_other (hav₁ n hn).ne_inst
  have hnew : ∀ m, ownKey own₁ m = true → ν₃ (.inst ρ m) = .inst ρ' (νb m) :=
    fun m ho => openMap_own ho
  have hclass : ∀ n ∈ D₂ ∪ {n | n ∈ freeNames body₁}, n ∈ D₂ ∨
      ∃ m ∈ freeNames b₁, ownKey own₁ m = true ∧ n = .inst ρ m := by
    intro n hn
    rcases hn with hn | hn
    · exact Or.inl hn
    · exact hbody n hn
  have hnotD : ∀ (n : Nm X₁) (m : Nm X₁), n ∈ D₂ → n ≠ Nm.inst ρ m :=
    fun n m hn => (hav₁ n hn).ne_inst m
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n hn n' hn' he
    rcases hclass n hn with h1 | ⟨m, hm, ho, rfl⟩ <;> rcases hclass n' hn' with h2 | ⟨m', hm', ho', rfl⟩
    · rw [hold n h1, hold n' h2] at he
      exact hci.inj h1 h2 he
    · rw [hold n h1, hnew m' ho'] at he
      exact absurd he ((hav₂ n h1).ne_inst _)
    · rw [hnew m ho, hold n' h2] at he
      exact absurd he.symm ((hav₂ n' h2).ne_inst _)
    · rw [hnew m ho, hnew m' ho'] at he
      rw [hinj m hm m' hm' ho ho' (Nm.inst.inj he).2]
  · refine List.nodup_append.2 ⟨hnd.map (fun a b e => (Nm.inst.inj e).2), hci.nodup, ?_⟩
    intro a ha b hb e
    obtain ⟨m, _, rfl⟩ := List.mem_map.1 ha
    subst e
    exact (havR _ hb).ne_inst m rfl
  · intro n hn hmem
    rcases hclass n hn with h1 | ⟨m, hm, ho, rfl⟩
    · rw [hold n h1] at hmem
      rcases List.mem_append.1 hmem with h | h
      · obtain ⟨m', _, e⟩ := List.mem_map.1 h
        exact (hav₂ n h1).ne_inst m' e.symm
      · exact hci.disj n h1 h
    · rw [hnew m ho] at hmem
      rcases List.mem_append.1 hmem with h | h
      · obtain ⟨m', hm', e⟩ := List.mem_map.1 h
        have := (Nm.inst.inj e).2
        subst this
        exact hdisj m hm ho hm'
      · exact (havR _ h).ne_inst _ rfl
  · refine hci.store.mono Set.subset_union_left hold ?_
    intro n hn hnD
    rcases hclass n hn with h1 | ⟨m, hm, ho, rfl⟩
    · exact absurd h1 hnD
    · refine ⟨?_, ?_⟩
      · by_contra hc
        exact hnotD _ m (hci.store.dom _ hc) rfl
      · rw [hnew m ho]
        by_contra hc
        obtain ⟨n', hn', e⟩ := hci.store.only _ hc
        exact (hav₂ n' hn').ne_inst _ e
  · intro n hn
    rcases hclass n hn with h1 | ⟨m, _, _, rfl⟩
    · exact hci.ok₁ n h1
    · trivial
  · intro n hn
    rcases hclass n hn with h1 | ⟨m, _, ho, rfl⟩
    · rw [hold n h1]; exact hci.ok₂ n h1
    · rw [hnew m ho]; trivial
  · intro m hm
    rcases List.mem_append.1 hm with h | h
    · obtain ⟨m', _, rfl⟩ := List.mem_map.1 h
      trivial
    · exact hci.okRes m h

omit [DecidableEq S] [DecidableEq X₂] in
/-- **The configuration after opening a pending construct** on the first side:
its names become copies whose images were reserved. -/
theorem open_ci {ν : Nm X₁ → Nm X₂} {D : Set (Nm X₁)} {Rh R : List (Nm X₂)}
    {τ₁ : GStore S X₁} {τ₂ : GStore S X₂} (hci : CI C ν D (Rh ++ R) τ₁ τ₂) {ρ : Path}
    (hav : ∀ n ∈ D, Avoid ρ n) {own : List X₁} {νi : Nm X₁ → Nm X₂} {E : List (Nm X₁)}
    (hlive : ∀ m ∈ E, ownKey own m = true → νi m ∈ Rh)
    (hinj : ∀ m ∈ E, ∀ m' ∈ E, ownKey own m = true → ownKey own m' = true → νi m = νi m' → m = m')
    {body₁ : Tm S X₁}
    (hbody : ∀ n ∈ freeNames body₁, n ∈ D ∨ ∃ m ∈ E, ownKey own m = true ∧ n = .inst ρ m) :
    CI C (openMap ρ own νi ν) (D ∪ {n | n ∈ freeNames body₁}) R τ₁ τ₂ := by
  have hold : ∀ n ∈ D, openMap ρ own νi ν n = ν n := fun n hn => openMap_other (hav n hn).ne_inst
  have hnew : ∀ m, ownKey own m = true → openMap ρ own νi ν (.inst ρ m) = νi m :=
    fun m ho => openMap_own ho
  have hclass : ∀ n ∈ D ∪ {n | n ∈ freeNames body₁}, n ∈ D ∨
      ∃ m ∈ E, ownKey own m = true ∧ n = .inst ρ m := by
    intro n hn
    rcases hn with hn | hn
    · exact Or.inl hn
    · exact hbody n hn
  have hdj := List.disjoint_of_nodup_append hci.nodup
  refine ⟨?_, (List.nodup_append.1 hci.nodup).2.1, ?_, ?_, ?_, ?_, ?_⟩
  · intro n hn n' hn' he
    rcases hclass n hn with h1 | ⟨m, hm, ho, rfl⟩ <;> rcases hclass n' hn' with h2 | ⟨m', hm', ho', rfl⟩
    · rw [hold n h1, hold n' h2] at he
      exact hci.inj h1 h2 he
    · rw [hold n h1, hnew m' ho'] at he
      exact absurd (List.mem_append_left _ (he ▸ hlive m' hm' ho')) (hci.disj n h1)
    · rw [hnew m ho, hold n' h2] at he
      exact absurd (List.mem_append_left _ (he ▸ hlive m hm ho)) (hci.disj n' h2)
    · rw [hnew m ho, hnew m' ho'] at he
      rw [hinj m hm m' hm' ho ho' he]
  · intro n hn hmem
    rcases hclass n hn with h1 | ⟨m, hm, ho, rfl⟩
    · rw [hold n h1] at hmem
      exact hci.disj n h1 (List.mem_append_right _ hmem)
    · rw [hnew m ho] at hmem
      exact hdj (hlive m hm ho) hmem
  · refine hci.store.mono Set.subset_union_left hold ?_
    intro n hn hnD
    rcases hclass n hn with h1 | ⟨m, hm, ho, rfl⟩
    · exact absurd h1 hnD
    · refine ⟨?_, ?_⟩
      · by_contra hc
        exact (hav _ (hci.store.dom _ hc)).ne_inst m rfl
      · rw [hnew m ho]
        exact hci.res_unbound (List.mem_append_left _ (hlive m hm ho))
  · intro n hn
    rcases hclass n hn with h1 | ⟨m, _, _, rfl⟩
    · exact hci.ok₁ n h1
    · trivial
  · intro n hn
    rcases hclass n hn with h1 | ⟨m, hm, ho, rfl⟩
    · rw [hold n h1]; exact hci.ok₂ n h1
    · rw [hnew m ho]; exact hci.okRes _ (List.mem_append_left _ (hlive m hm ho))
  · intro m hm
    exact hci.okRes m (List.mem_append_right _ hm)


/-! ## Small facts used by the cases -/

omit [DecidableEq S] [DecidableEq X₂] in
theorem src_of_ownKey {Y : Type v} [DecidableEq Y] {own : List Y} {n : Nm Y}
    (h : ownKey own n = true) : ∃ s, n = .src s := by
  cases n with
  | src s => exact ⟨s, rfl⟩
  | inst _ _ => simp [ownKey] at h

omit [DecidableEq S] [DecidableEq X₁] [DecidableEq X₂] in
theorem CI.with_store {ν : Nm X₁ → Nm X₂} {D : Set (Nm X₁)} {R : List (Nm X₂)}
    {σ₁ σ₁' : GStore S X₁} {σ₂ σ₂' : GStore S X₂} (h : CI C ν D R σ₁ σ₂)
    (hs : StoreRel C ν D σ₁' σ₂') : CI C ν D R σ₁' σ₂' where
  inj := h.inj
  nodup := h.nodup
  disj := h.disj
  store := hs
  ok₁ := h.ok₁
  ok₂ := h.ok₂
  okRes := h.okRes

omit [DecidableEq S] in
/-- Free names on the second side of a value pair may occur free. -/
theorem ok₂_of_val {ν μ : Nm X₁ → Nm X₂} {D : Set (Nm X₁)} {R : List (Nm X₂)}
    {σ₁ : GStore S X₁} {σ₂ : GStore S X₂} (hci : CI C ν D R σ₁ σ₂) {u : Tm S X₁} {u' : Tm S X₂}
    (h : Rel C ν μ .val [] true u u') (hfv : ∀ m ∈ freeNames u, m ∈ D) : ∀ m ∈ freeNames u', OK₂ C m := by
  intro m hm
  obtain ⟨n', hn', rfl⟩ := h.mem_freeNames_val hm
  exact hci.ok₂ n' (hfv n' hn')

omit [DecidableEq S] in
theorem freeParams_val {ν μ : Nm X₁ → Nm X₂} {k : Kd} {ok : Bool} {u : Tm S X₁} {u' : Tm S X₂}
    (h : Rel C ν μ k [] ok u u') (hfp : freeParams u = []) : freeParams u' = [] := by
  apply List.eq_nil_iff_forall_not_mem.2
  intro x hx
  obtain ⟨y, hy, _⟩ := h.freeParams_nil hx
  rw [hfp] at hy
  cases hy

/-! ## The `let` continuation -/

section LetCont

variable {Y : Type v} [DecidableEq Y]

/-- What a `let` does with one value of its right-hand side: match it (ground),
substitute it for a variable pattern (not ground), or give no answer. -/
def letCont [CodeId Y] (rec : Runner S Y) (π : Path) (p b : Tm S Y) (r₁ : Tm S Y × GStore S Y) :
    Option (Result S Y) :=
  match (act r₁.2 r₁.1).toGVal? with
  | some g =>
      match matchT r₁.2 p g.toTm with
      | some σ₂ => rec (π ++ [1]) σ₂ b
      | Option.none => some []
  | Option.none =>
      match p with
      | .var f => rec (π ++ [1]) r₁.2 (subst (Sub.single f r₁.1) Sub.none b)
      | _ => some []

theorem step_letP_none [CodeId Y] {d : Disc} {P : S → Option (Tm S Y)} {rec : Runner S Y} {π : Path}
    {σ : GStore S Y} {p w b : Tm S Y} (h : letLam? p w = none) :
    step d P rec π σ (.letP p w b) = bindOpt (rec (π ++ [0]) σ w) (letCont rec π p b) := by
  simp only [step, h]
  rfl

theorem step_letP_some [CodeId Y] {d : Disc} {P : S → Option (Tm S Y)} {rec : Runner S Y} {π : Path}
    {σ : GStore S Y} {p w b : Tm S Y} {f : Nm Y} (h : letLam? p w = some f) :
    step d P rec π σ (.letP p w b) = rec π σ (subst (Sub.single f w) Sub.none b) := by
  simp only [step, h]

omit [DecidableEq S] [DecidableEq Y] in
theorem letLam?_some {p w : Tm S Y} {f : Nm Y} (h : letLam? p w = some f) :
    p = .var f ∧ ∃ x own b, w = .lam x own b := by
  cases p with
  | var g =>
      cases w with
      | lam x own b =>
          simp only [letLam?, Option.some.injEq] at h
          exact ⟨by rw [h], x, own, b, rfl⟩
      | _ => simp [letLam?] at h
  | _ => simp [letLam?] at h

end LetCont

omit [DecidableEq S] in
/-- A pattern related to a store-name occurrence is one. -/
theorem Rel.right_var_pat {ν μ : Nm X₁ → Nm X₂} {Res : List (Nm X₂)} {ok : Bool}
    {t₁ : Tm S X₁} {m : Nm X₂}
    (h : Rel C ν μ .pat Res ok t₁ (.var m)) : ∃ n, t₁ = .var n := by
  cases h
  exact ⟨_, rfl⟩

omit [DecidableEq S] in
/-- A value related to a lambda is one. -/
theorem Rel.right_lam_val {ν μ : Nm X₁ → Nm X₂} {Res : List (Nm X₂)} {t₁ : Tm S X₁}
    {x₂ : Nm X₂} {own₂ : List X₂} {b₂ : Tm S X₂} {ok : Bool}
    (h : Rel C ν μ .val Res ok t₁ (.lam x₂ own₂ b₂)) :
    ∃ x own b, t₁ = .lam x own b := by
  cases h
  exact ⟨_, _, _, rfl⟩

omit [DecidableEq S] in
/-- Code related to a lambda is a lambda or a chain of `new` blocks. -/
theorem Rel.left_lam_code {ν μ : Nm X₁ → Nm X₂} {k : Kd} {Res : List (Nm X₂)}
    {x₁ : Nm X₁} {own₁ : List X₁} {b₁ : Tm S X₁} {t₂ : Tm S X₂}
    {ok : Bool} (h : Rel C ν μ k Res ok (.lam x₁ own₁ b₁) t₂) : ∃ x own b, t₂ = .lam x own b := by
  cases h
  exact ⟨_, _, _, rfl⟩

/-! ## Substituting a value for a store name -/

omit [DecidableEq S] [DecidableEq X₂] in
theorem freeParams_subst_single {f : Nm X₁} {v b : Tm S X₁} (hv : freeParams v = [])
    (hb : freeParams b = []) : freeParams (subst (Sub.single f v) Sub.none b) = [] := by
  apply List.eq_nil_iff_forall_not_mem.2
  intro y hy
  rcases mem_freeParams_subst' b _ _ y hy with ⟨h1, _⟩ | ⟨m, _, w, hw, hyw⟩ | ⟨z, _, w, hw, _⟩
  · rw [hb] at h1; cases h1
  · simp only [Sub.single] at hw
    split at hw
    · injection hw with hw
      subst hw
      rw [hv] at hyw
      cases hyw
    · cases hw
  · cases hw

omit [DecidableEq S] [DecidableEq X₂] in
theorem freeNames_subst_single {f : Nm X₁} {v b : Tm S X₁} {D : Set (Nm X₁)}
    (hv : ∀ m ∈ freeNames v, m ∈ D) (hb : ∀ m ∈ freeNames b, m ∈ D) :
    ∀ m ∈ freeNames (subst (Sub.single f v) Sub.none b), m ∈ D := by
  intro m hm
  rcases mem_freeNames_subst' b _ _ m hm with ⟨h1, _⟩ | ⟨m₀, _, w, hw, hmw⟩ | ⟨z, _, w, hw, _⟩
  · exact hb m h1
  · simp only [Sub.single] at hw
    split at hw
    · injection hw with hw
      subst hw
      exact hv m hmw
    · cases hw
  · cases hw

/-! ## The application case -/

section Cases

variable {P₁ : S → Option (Tm S X₁)} {P₂ : S → Option (Tm S X₂)}

/-- **A value substituted in place for a store name**, on both sides: the
substitutions are related, and a defined run of the first side is matched at
the same fuel. -/
theorem sim_chain [CodeId X₁] [CodeId X₂] {n : ℕ} (ih : SimAt C P₁ P₂ n) {ρ ρ' : Path} {σ₁ : GStore S X₁}
    {σ₂ : GStore S X₂} {f₁ : Nm X₁} {f₂ : Nm X₂} {v₁ b₁ : Tm S X₁} {v₂ b₂ : Tm S X₂}
    {ν μ : Nm X₁ → Nm X₂} {Rb Rc : List (Nm X₂)} {ob : Bool} {D : Set (Nm X₁)} {L₁ : Result S X₁}
    (hb : Rel C ν μ .code Rb ob b₁ b₂) (hv : Rel C ν μ .val [] true v₁ v₂) (hf₂ : ν f₁ = f₂)
    (hci : CI C ν D (Rb ++ Rc) σ₁ σ₂) (hF : Fresh ρ ρ' ν D (Rb ++ Rc))
    (hf : f₁ ∈ D) (hfvb : ∀ m ∈ freeNames b₁, m ∈ D) (hfvv : ∀ m ∈ freeNames v₁, m ∈ D)
    (hfpv : freeParams v₁ = []) (hfpb : freeParams b₁ = [])
    (hrun : run .static P₁ n ρ σ₁ (subst (Sub.single f₁ v₁) Sub.none b₁) = some L₁) :
    ∃ L₂, run .static P₂ n ρ' σ₂ (subst (Sub.single f₂ v₂) Sub.none b₂) = some L₂ ∧
      List.Forall₂ (Out C ρ ρ' ν μ D Rb Rc) L₁ L₂ := by
  have hsub := subst_var hb hv (fun m hm => hci.ok₁ m (hfvv m hm)) hfpv
    (ok₂_of_val hci hv hfvv) (freeParams_val hv hfpv)
    (fun m hm he => hci.inj (hfvb m hm) hf he)
    (fun h => hci.disj f₁ hf (by simp [h]))
  rw [hf₂] at hsub
  exact ih hsub (freeParams_subst_single hfpv hfpb) (freeNames_subst_single hfvv hfvb) hci hF hrun

/-- **The simulation of an application**: the function, then the argument,
then (for a lambda) the activation at fresh paths. -/
theorem sim_app [CodeId X₁] [CodeId X₂] {n : ℕ} (ih : SimAt C P₁ P₂ n) {π π' : Path} {σ₁ : GStore S X₁}
    {σ₂ : GStore S X₂} {f₁ a₁ : Tm S X₁} {f₂ a₂ : Tm S X₂} {ν μ : Nm X₁ → Nm X₂}
    {Rf Ra Rc : List (Nm X₂)} {okf oka : Bool} {D : Set (Nm X₁)} {L₁ : Result S X₁}
    (hf : Rel C ν μ .code Rf okf f₁ f₂) (ha : Rel C ν μ .code Ra oka a₁ a₂)
    (hfp : freeParams (.app f₁ a₁ : Tm S X₁) = [])
    (hfv : ∀ m ∈ freeNames (.app f₁ a₁ : Tm S X₁), m ∈ D)
    (hci : CI C ν D (Rf ++ Ra ++ Rc) σ₁ σ₂) (hF : Fresh π π' ν D (Rf ++ Ra ++ Rc))
    (hrun : step .static P₁ (run .static P₁ n) π σ₁ (.app f₁ a₁) = some L₁) :
    ∃ L₂, step .static P₂ (run .static P₂ n) π' σ₂ (.app f₂ a₂) = some L₂ ∧
      List.Forall₂ (Out C π π' ν μ D (Rf ++ Ra) Rc) L₁ L₂ := by
  simp only [freeParams, List.append_eq_nil_iff] at hfp
  obtain ⟨hfpf, hfpa⟩ := hfp
  have hfvf : ∀ m ∈ freeNames f₁, m ∈ D := fun m h => hfv m (by simp [freeNames, h])
  have hfva : ∀ m ∈ freeNames a₁, m ∈ D := fun m h => hfv m (by simp [freeNames, h])
  simp only [step] at hrun ⊢
  obtain ⟨Lf₁, hLf₁, hb₁⟩ := bindOpt_eq_some hrun
  have hcif : CI C ν D (Rf ++ (Ra ++ Rc)) σ₁ σ₂ := by rw [← List.append_assoc]; exact hci
  have hFf : Fresh π π' ν D (Rf ++ (Ra ++ Rc)) := by rw [← List.append_assoc]; exact hF
  obtain ⟨Lf₂, hLf₂, hfr⟩ := ih hf hfpf hfvf hcif (hFf.child 0 0) hLf₁
  rw [hLf₂]
  have hA₁ : ∀ n ∈ D, Avoid (π ++ [2]) n := fun n hn => (hF.old₁ n hn).avoid_child 2
  have hA₂ : ∀ n ∈ D, Avoid (π' ++ [2]) (ν n) := fun n hn => (hF.old₂ n hn).avoid_child 2
  have hAR : ∀ m ∈ Rf ++ Ra ++ Rc, Avoid (π' ++ [2]) m :=
    fun m hm => (hF.oldRes m hm).avoid_child 2
  refine bindAll_sim ?_ hfr hb₁
  rintro ⟨u₁, τ₁⟩ ⟨u₁', τ₁'⟩ M₁ ⟨ν₁, D₁, hfv₁, hE₁, hrel₁, hfp₁, hci₁⟩ hM₁
  simp only at hM₁ hfv₁ hrel₁ hfp₁ hci₁ ⊢
  obtain ⟨La₁, hLa₁, hb₂⟩ := bindOpt_eq_some hM₁
  have hra : Rel C ν₁ μ .code Ra oka a₁ a₂ :=
    ha.congr (fun m hm => (hE₁.agree m (hfva m hm)).symm) (fun _ _ => rfl)
  have hFa : Fresh (π ++ [1]) (π' ++ [1]) ν₁ D₁ (Ra ++ Rc) :=
    hE₁.fresh_sibling (by decide) (by decide) hFf
  obtain ⟨La₂, hLa₂, harel⟩ := ih hra hfpa (fun m hm => hE₁.sub (hfva m hm)) hci₁ hFa hLa₁
  rw [hLa₂]
  have hA₁' := hE₁.avoid₁ (by decide : (0 : ℕ) ≠ 2) hA₁
  have hA₂' := hE₁.avoid₂ (by decide : (0 : ℕ) ≠ 2) hA₂ (fun m hm => hAR m (by simp [hm]))
  refine bindAll_sim ?_ harel hb₂
  rintro ⟨u₂, τ₂⟩ ⟨u₂', τ₂'⟩ N₁ ⟨ν₂, D₂, hfv₂, hE₂, hrel₂, hfp₂, hci₂⟩ hN₁
  simp only at hN₁ hfv₂ hrel₂ hfp₂ hci₂ ⊢
  have hA₁'' := hE₂.avoid₁ (by decide : (1 : ℕ) ≠ 2) hA₁'
  have hA₂'' := hE₂.avoid₂ (by decide : (1 : ℕ) ≠ 2) hA₂' (fun m hm => hAR m (by simp [hm]))
  have hARc : ∀ m ∈ Rc, Avoid (π' ++ [2]) m := fun m hm => hAR m (by simp [hm])
  have hrelf : Rel C ν₂ μ .val [] true u₁ u₁' :=
    hrel₁.congr (fun m hm => (hE₂.agree m (hfv₁ m hm)).symm) (fun _ _ => rfl)
  have hE12 : Ext π π' (Rf ++ Ra) ν D ν₂ D₂ := hE₁.parent.trans hE₂.parent
  have hfvu₁ : ∀ m ∈ freeNames u₁, m ∈ D₂ := fun m hm => hE₂.sub (hfv₁ m hm)
  have hout_app : Out C π π' ν μ D (Rf ++ Ra) Rc (.app u₁ u₂, τ₂) (.app u₁' u₂', τ₂') := by
    refine ⟨ν₂, D₂, ?_, hE12, .app hrelf hrel₂, by simp [freeParams, hfp₁, hfp₂], hci₂⟩
    intro m hm
    simp only [freeNames, List.mem_append] at hm
    rcases hm with h | h
    · exact hfvu₁ m h
    · exact hfv₂ m h
  generalize hR0 : ([] : List (Nm X₂)) = R0 at hrelf
  generalize hokv : true = okv at hrelf
  cases hrelf with
  | @lam _ _ _ x₁ own₁ b₁ x₂ own₂ b₂ νb μb Rb _ hνb hμb hμx hr₁ hr₂ hb hown hres hinj hdisj hnd
      hpar _ _ =>
      simp only [activate] at hN₁ ⊢
      have hcl : ∀ x ∈ freeParams b₁, x = x₁ := by
        intro x hx
        by_contra hne
        have := (mem_freeParams_lam (own := own₁)).2 ⟨hx, hne⟩
        rw [hfp₁] at this
        cases this
      have hca₁ : ∀ m ∈ freeNames u₂, OK₁ C m := fun m hm => hci₂.ok₁ m (hfv₂ m hm)
      have hact := activate_lam hνb hμx hb hown hres hcl hrel₂ hca₁ hfp₂
        (ok₂_of_val hci₂ hrel₂ hfv₂) (freeParams_val hrel₂ hfp₂) (ρ := π ++ [2]) (ρ' := π' ++ [2])
        (fun n' hn' m e => by
          rcases hn' with h | h
          · exact (hA₁'' n' (hfvu₁ n' h)).ne_inst m e
          · exact (hA₁'' n' (hfv₂ n' h)).ne_inst m e)
      have hbody : ∀ m ∈ freeNames (subst (renameOwn (π ++ [2]) own₁) (Sub.single x₁ u₂) b₁),
          m ∈ D₂ ∨ ∃ m₀ ∈ freeNames b₁, ownKey own₁ m₀ = true ∧ m = .inst (π ++ [2]) m₀ := by
        intro m hm
        rcases mem_freeNames_open hm with ⟨h1, h2⟩ | ⟨m₀, hm₀, ho, rfl⟩ | ⟨_, h2⟩
        · exact Or.inl (hfvu₁ m (mem_freeNames_lam.2 ⟨h1, h2⟩))
        · exact Or.inr ⟨m₀, hm₀, ho, rfl⟩
        · exact Or.inl (hfv₂ m h2)
      have hci₃ := activation_ci hci₂ hA₁'' hA₂'' hARc hinj hdisj hnd hbody
      set ν₃ := openMap (π ++ [2]) own₁ (fun m => Nm.inst (π' ++ [2]) (νb m)) ν₂ with hν₃
      have hold₃ : ∀ n ∈ D₂, ν₃ n = ν₂ n := fun n hn => openMap_other (hA₁'' n hn).ne_inst
      have hF₃ : Fresh (π ++ [2]) (π' ++ [2]) ν₃ (D₂ ∪ {n | n ∈ freeNames
          (subst (renameOwn (π ++ [2]) own₁) (Sub.single x₁ u₂) b₁)})
          (Rb.map (Nm.inst (π' ++ [2])) ++ Rc) := by
        refine ⟨?_, ?_, ?_⟩
        · intro n hn
          rcases hn with hn | hn
          · exact (hA₁'' n hn).oldAt
          · rcases hbody n hn with h | ⟨m₀, _, ho, rfl⟩
            · exact (hA₁'' n h).oldAt
            · obtain ⟨s, rfl⟩ := src_of_ownKey ho
              exact oldAt_inst_self _ s
        · intro n hn
          rcases hn with hn | hn
          · rw [hold₃ n hn]; exact (hA₂'' n hn).oldAt
          · rcases hbody n hn with h | ⟨m₀, hm₀, ho, rfl⟩
            · rw [hold₃ n h]; exact (hA₂'' n h).oldAt
            · rw [hν₃, openMap_own ho]
              have h2 : ownKey own₂ (νb m₀) = true := by rw [hown m₀ hm₀]; exact ho
              obtain ⟨k, hk⟩ := src_of_ownKey h2
              simp only [hk]
              exact oldAt_inst_self _ k
        · intro m hm
          rcases List.mem_append.1 hm with h | h
          · obtain ⟨m', hm', rfl⟩ := List.mem_map.1 h
            obtain ⟨k, rfl⟩ := src_of_ownKey (hres m' hm')
            exact oldAt_inst_self _ k
          · exact (hARc m h).oldAt
      have hEact : Ext π π' [] ν₂ D₂ ν₃ (D₂ ∪ {n | n ∈ freeNames
          (subst (renameOwn (π ++ [2]) own₁) (Sub.single x₁ u₂) b₁)}) := by
        refine ⟨hold₃, Set.subset_union_left, ?_⟩
        intro n hn hnD
        rcases hn with hn | hn
        · exact absurd hn hnD
        · rcases hbody n hn with h | ⟨m₀, hm₀, ho, rfl⟩
          · exact absurd h hnD
          · obtain ⟨s, rfl⟩ := src_of_ownKey ho
            refine ⟨newAt_inst 2 s, Or.inl ?_⟩
            rw [hν₃, openMap_own ho]
            have h2 : ownKey own₂ (νb (.src s)) = true := by rw [hown _ hm₀]; exact ho
            obtain ⟨k, hk⟩ := src_of_ownKey h2
            rw [hk]
            exact newAt_inst 2 k
      have hfpb : freeParams (subst (renameOwn (π ++ [2]) own₁) (Sub.single x₁ u₂) b₁) = [] :=
        freeParams_open hcl hfp₂
      obtain ⟨N₂, hN₂, hrelN⟩ := ih hact hfpb (fun m hm => Or.inr hm) hci₃ hF₃ hN₁
      refine ⟨N₂, hN₂, hrelN.imp fun {r₁ r₂} h => ?_⟩
      have h' := ((h.parent.res_newAt (R' := []) ?_).after (hE12.trans hEact))
      · exact h'.res_mono (by simp)
      · intro m hm
        obtain ⟨m', hm', rfl⟩ := List.mem_map.1 hm
        obtain ⟨k, rfl⟩ := src_of_ownKey (hres m' hm')
        exact newAt_inst 2 k
  | sym s =>
      refine ⟨[(.app (.sym s) u₂', τ₂')], rfl, ?_⟩
      have e : [(Tm.app (.sym s) u₂, τ₂)] = N₁ := by simpa using hN₁
      subst e
      exact .cons hout_app .nil
  | fn F =>
      refine ⟨[(.app (.fn F) u₂', τ₂')], rfl, ?_⟩
      have e : [(Tm.app (.fn F) u₂, τ₂)] = N₁ := by simpa using hN₁
      subst e
      exact .cons hout_app .nil
  | var m _ =>
      refine ⟨[(.app (.var (ν₂ m)) u₂', τ₂')], rfl, ?_⟩
      have e : [(Tm.app (.var m) u₂, τ₂)] = N₁ := by simpa using hN₁
      subst e
      exact .cons hout_app .nil
  | pvar x _ =>
      refine ⟨[(.app (.pvar (μ x)) u₂', τ₂')], rfl, ?_⟩
      have e : [(Tm.app (.pvar x) u₂, τ₂)] = N₁ := by simpa using hN₁
      subst e
      exact .cons hout_app .nil
  | @quote _ _ _ c₁ c₂ hq =>
      refine ⟨[(.app (.quote c₂) u₂', τ₂')], rfl, ?_⟩
      have e : [(Tm.app (.quote c₁) u₂, τ₂)] = N₁ := by simpa using hN₁
      subst e
      exact .cons hout_app .nil
  | @pquote _ _ _ c₁ c₂ _ _ _ _ =>
      refine ⟨[(.app (.pquote c₂) u₂', τ₂')], rfl, ?_⟩
      have e : [(Tm.app (.pquote c₁) u₂, τ₂)] = N₁ := by simpa using hN₁
      subst e
      exact .cons hout_app .nil
  | @app _ _ _ _ _ _ _ g₁ h₁ g₂ h₂ _ _ =>
      refine ⟨[(.app (.app g₂ h₂) u₂', τ₂')], rfl, ?_⟩
      have e : [(Tm.app (.app g₁ h₁) u₂, τ₂)] = N₁ := by simpa using hN₁
      subst e
      exact .cons hout_app .nil
  | @ctx _ _ _ ks₁ c₁ ks₂ c₂ _ _ _ =>
      refine ⟨[(.app (.ctx ks₂ c₂) u₂', τ₂')], rfl, ?_⟩
      have e : [(Tm.app (.ctx ks₁ c₁) u₂, τ₂)] = N₁ := by simpa using hN₁
      subst e
      exact .cons hout_app .nil
  | letP hk => exact absurd rfl hk
  | alt hk => exact absurd rfl hk
  | letAct hk => exact absurd rfl hk


/-- **The simulation of alternatives**: each branch from the same store. -/
theorem sim_alt [CodeId X₁] [CodeId X₂] {n : ℕ} (ih : SimAt C P₁ P₂ n) {π π' : Path} {σ₁ : GStore S X₁}
    {σ₂ : GStore S X₂} {t₁ u₁ : Tm S X₁} {t₂ u₂ : Tm S X₂} {ν μ : Nm X₁ → Nm X₂}
    {R₁ R₂ Rc : List (Nm X₂)} {o₁ o₂ : Bool} {D : Set (Nm X₁)} {L₁ : Result S X₁}
    (h₁ : Rel C ν μ .code R₁ o₁ t₁ t₂) (h₂ : Rel C ν μ .code R₂ o₂ u₁ u₂)
    (hfp : freeParams (.alt t₁ u₁ : Tm S X₁) = [])
    (hfv : ∀ m ∈ freeNames (.alt t₁ u₁ : Tm S X₁), m ∈ D)
    (hci : CI C ν D (R₁ ++ R₂ ++ Rc) σ₁ σ₂) (hF : Fresh π π' ν D (R₁ ++ R₂ ++ Rc))
    (hrun : step .static P₁ (run .static P₁ n) π σ₁ (.alt t₁ u₁) = some L₁) :
    ∃ L₂, step .static P₂ (run .static P₂ n) π' σ₂ (.alt t₂ u₂) = some L₂ ∧
      List.Forall₂ (Out C π π' ν μ D (R₁ ++ R₂) Rc) L₁ L₂ := by
  simp only [freeParams, List.append_eq_nil_iff] at hfp
  simp only [step] at hrun ⊢
  cases e1 : run .static P₁ n (π ++ [0]) σ₁ t₁ with
  | none => rw [e1] at hrun; cases hrun
  | some l₁ =>
      cases e2 : run .static P₁ n (π ++ [1]) σ₁ u₁ with
      | none => rw [e1, e2] at hrun; cases hrun
      | some r₁ =>
          rw [e1, e2] at hrun
          injection hrun with hrun
          subst hrun
          have hci₁ : CI C ν D (R₁ ++ (R₂ ++ Rc)) σ₁ σ₂ := by rw [← List.append_assoc]; exact hci
          have hF₁ : Fresh π π' ν D (R₁ ++ (R₂ ++ Rc)) := by rw [← List.append_assoc]; exact hF
          obtain ⟨l₂, hl₂, hrl⟩ := ih h₁ hfp.1 (fun m h => hfv m (by simp [freeNames, h])) hci₁
            (hF₁.child 0 0) e1
          obtain ⟨r₂, hr₂, hrr⟩ := ih h₂ hfp.2 (fun m h => hfv m (by simp [freeNames, h])) hci₁.drop
            (hF₁.drop.child 1 1) e2
          refine ⟨l₂ ++ r₂, by rw [hl₂, hr₂], forall₂_append ?_ ?_⟩
          · exact hrl.imp fun _ _ h => (h.parent.drop).res_mono (fun m hm => by simp [hm])
          · exact hrr.imp fun _ _ h => h.parent.res_mono (fun m hm => by simp [hm])

/-- **The simulation of an equation call**: related programs. -/
theorem sim_fn [CodeId X₁] [CodeId X₂] (hP : ProgRel C P₁ P₂) {n : ℕ} (ih : SimAt C P₁ P₂ n) {π π' : Path}
    {σ₁ : GStore S X₁} {σ₂ : GStore S X₂} {F : S} {ν μ : Nm X₁ → Nm X₂} {Rc : List (Nm X₂)}
    {D : Set (Nm X₁)} {L₁ : Result S X₁}
    (hci : CI C ν D ([] ++ Rc) σ₁ σ₂) (hF : Fresh π π' ν D ([] ++ Rc))
    (hrun : step .static P₁ (run .static P₁ n) π σ₁ (.fn F) = some L₁) :
    ∃ L₂, step .static P₂ (run .static P₂ n) π' σ₂ (.fn F) = some L₂ ∧
      List.Forall₂ (Out C π π' ν μ D [] Rc) L₁ L₂ := by
  simp only [step] at hrun ⊢
  rcases OptRel.cases (hP F) with ⟨e1, e2⟩ | ⟨e₁, e₂, e1, e2, hfv0, hfp0, hrel0⟩
  · rw [e1] at hrun
    rw [e2]
    injection hrun with hrun
    subst hrun
    exact ⟨_, rfl, .cons (Out.value (.fn F) (by simp [freeNames]) rfl hci) .nil⟩
  · rw [e1] at hrun
    rw [e2]
    obtain ⟨L₂, hL₂, hrel⟩ := ih (hrel0 ν μ) hfp0 (by simp [hfv0]) hci (hF.child 0 0) hrun
    exact ⟨L₂, hL₂, hrel.imp fun _ _ h => h.parent⟩

/-- **The simulation of a `new` block**: the first side activates it, the
second side runs its body. -/
theorem sim_newAct [CodeId X₁] [CodeId X₂] {n : ℕ} (ih : SimAt C P₁ P₂ n) {π π' : Path} {σ₁ : GStore S X₁}
    {σ₂ : GStore S X₂} {ℓ : Nm X₁} {own : List X₁} {b₁ : Tm S X₁} {b₂ : Tm S X₂}
    {ν μ νi : Nm X₁ → Nm X₂} {Rh Rb Rc : List (Nm X₂)} {D : Set (Nm X₁)} {L₁ : Result S X₁}
    (hνi : ∀ n, ownKey own n = false → νi n = ν n) (hℓ : ℓ ∉ freeParams b₁)
    {ob : Bool} (hb : Rel C νi μ .code Rb ob b₁ b₂)
    (hlive : ∀ n ∈ freeNames b₁, ownKey own n = true → νi n ∈ Rh)
    (hinj : ∀ n ∈ freeNames b₁, ∀ n' ∈ freeNames b₁,
      ownKey own n = true → ownKey own n' = true → νi n = νi n' → n = n')
    (hfp : freeParams (.app (.lam ℓ own b₁) (.lam ℓ [] (.pvar ℓ)) : Tm S X₁) = [])
    (hfv : ∀ m ∈ freeNames (.app (.lam ℓ own b₁) (.lam ℓ [] (.pvar ℓ)) : Tm S X₁), m ∈ D)
    (hci : CI C ν D (Rh ++ Rb ++ Rc) σ₁ σ₂) (hF : Fresh π π' ν D (Rh ++ Rb ++ Rc))
    (hrun : step .static P₁ (run .static P₁ n) π σ₁
      (.app (.lam ℓ own b₁) (.lam ℓ [] (.pvar ℓ))) = some L₁) :
    ∃ L₂, step .static P₂ (run .static P₂ n) π' σ₂ b₂ = some L₂ ∧
      List.Forall₂ (Out C π π' ν μ D (Rh ++ Rb) Rc) L₁ L₂ := by
  cases n with
  | zero => simp [step, run, bindOpt] at hrun
  | succ n =>
      simp only [step] at hrun
      rw [show run .static P₁ (n + 1) (π ++ [0]) σ₁ (.lam ℓ own b₁) =
          some [(.lam ℓ own b₁, σ₁)] from rfl, bindOpt_some_singleton,
        show run .static P₁ (n + 1) (π ++ [1]) σ₁ (.lam ℓ [] (.pvar ℓ)) =
          some [(.lam ℓ [] (.pvar ℓ), σ₁)] from rfl, bindOpt_some_singleton] at hrun
      simp only [activate] at hrun
      have hfpb : freeParams b₁ = [] := by
        apply List.eq_nil_iff_forall_not_mem.2
        intro x hx
        have hxne : x ≠ ℓ := by
          rintro rfl
          exact hℓ hx
        have := (mem_freeParams_newAct (S := S) (ℓ := ℓ) (own := own) (b := b₁)).2 ⟨hx, hxne⟩
        rw [hfp] at this
        cases this
      have hA : ∀ n ∈ D, Avoid (π ++ [2]) n := fun n hn => (hF.old₁ n hn).avoid_child 2
      have hopen := open_body (ℓ := ℓ) hνi hb hfpb (.lam ℓ [] (.pvar ℓ)) (ρ := π ++ [2])
        (fun n hn ho m e => (hA n (hfv n (mem_freeNames_newAct.2 ⟨hn, ho⟩))).ne_inst m e)
      have hbody : ∀ m ∈ freeNames (subst (renameOwn (π ++ [2]) own)
          (Sub.single ℓ (.lam ℓ [] (.pvar ℓ))) b₁),
          m ∈ D ∨ ∃ m₀ ∈ freeNames b₁, ownKey own m₀ = true ∧ m = .inst (π ++ [2]) m₀ := by
        intro m hm
        rcases mem_freeNames_open hm with ⟨h1, h2⟩ | ⟨m₀, hm₀, ho, rfl⟩ | ⟨h1, _⟩
        · exact Or.inl (hfv m (mem_freeNames_newAct.2 ⟨h1, h2⟩))
        · exact Or.inr ⟨m₀, hm₀, ho, rfl⟩
        · exact absurd h1 hℓ
      have hci' : CI C ν D (Rh ++ (Rb ++ Rc)) σ₁ σ₂ := by rw [← List.append_assoc]; exact hci
      have hci₃ := open_ci hci' hA hlive hinj hbody
      set ν₃ := openMap (π ++ [2]) own νi ν with hν₃
      have hold₃ : ∀ n ∈ D, ν₃ n = ν n := fun n hn => openMap_other (hA n hn).ne_inst
      have hF₃ : Fresh (π ++ [2]) π' ν₃ (D ∪ {n | n ∈ freeNames (subst (renameOwn (π ++ [2]) own)
          (Sub.single ℓ (.lam ℓ [] (.pvar ℓ))) b₁)}) (Rb ++ Rc) := by
        refine ⟨?_, ?_, ?_⟩
        · intro n hn
          rcases hn with hn | hn
          · exact (hF.old₁ n hn).child 2
          · rcases hbody n hn with h | ⟨m₀, _, ho, rfl⟩
            · exact (hF.old₁ n h).child 2
            · obtain ⟨s, rfl⟩ := src_of_ownKey ho
              exact oldAt_inst_self _ s
        · intro n hn
          rcases hn with hn | hn
          · rw [hold₃ n hn]; exact hF.old₂ n hn
          · rcases hbody n hn with h | ⟨m₀, hm₀, ho, rfl⟩
            · rw [hold₃ n h]; exact hF.old₂ n h
            · rw [hν₃, openMap_own ho]
              exact hF.oldRes _ (by simp [hlive m₀ hm₀ ho])
        · intro m hm
          exact hF.oldRes m (by simp at hm ⊢; tauto)
      have hE : Ext π π' Rh ν D ν₃ (D ∪ {n | n ∈ freeNames (subst (renameOwn (π ++ [2]) own)
          (Sub.single ℓ (.lam ℓ [] (.pvar ℓ))) b₁)}) := by
        refine ⟨hold₃, Set.subset_union_left, ?_⟩
        intro n hn hnD
        rcases hn with hn | hn
        · exact absurd hn hnD
        · rcases hbody n hn with h | ⟨m₀, hm₀, ho, rfl⟩
          · exact absurd h hnD
          · obtain ⟨s, rfl⟩ := src_of_ownKey ho
            refine ⟨newAt_inst 2 s, Or.inr ?_⟩
            rw [hν₃, openMap_own ho]
            exact hlive _ hm₀ ho
      have hfpb' : freeParams (subst (renameOwn (π ++ [2]) own)
          (Sub.single ℓ (.lam ℓ [] (.pvar ℓ))) b₁) = [] :=
        freeParams_open (fun x hx => by rw [hfpb] at hx; cases hx) (by simp [freeParams])
      obtain ⟨L₂, hL₂, hrel⟩ := ih hopen hfpb' (fun m hm => Or.inr hm) hci₃ hF₃ hrun
      refine ⟨L₂, run_mono .static P₂ (Nat.le_succ _) hL₂, ?_⟩
      exact hrel.imp fun _ _ h => h.parent₁.after hE


/-- **The `let` continuation, on related values**: matching, substituting, or
no answer, alike on both sides. -/
theorem sim_letCont [CodeId X₁] [CodeId X₂] (hQ : C.BiUnique) (hC : C.CodeAgree) (hA : C.PatAgree) {n : ℕ} (ih : SimAt C P₁ P₂ n) {ρ₁ ρ₂ : Path}
    {τ₁ : GStore S X₁} {τ₂ : GStore S X₂} {v₁ : Tm S X₁} {v₂ : Tm S X₂} {p₁ b₁ : Tm S X₁}
    {p₂ b₂ : Tm S X₂} {ν₁ μ : Nm X₁ → Nm X₂} {Rp Rb Rc : List (Nm X₂)} {D₁ : Set (Nm X₁)}
    {M₁ : Result S X₁}
    (hv : Rel C ν₁ μ .val [] true v₁ v₂) (hfvv : ∀ m ∈ freeNames v₁, m ∈ D₁) (hfpv : freeParams v₁ = [])
    {op ob : Bool} (hp : Rel C ν₁ μ .pat Rp op p₁ p₂) (hb : Rel C ν₁ μ .code Rb ob b₁ b₂)
    (hfvp : ∀ m ∈ freeNames p₁, m ∈ D₁) (hfvb : ∀ m ∈ freeNames b₁, m ∈ D₁)
    (hfpb : freeParams b₁ = [])
    (hci : CI C ν₁ D₁ (Rp ++ Rb ++ Rc) τ₁ τ₂) (hF : Fresh (ρ₁ ++ [1]) (ρ₂ ++ [1]) ν₁ D₁ (Rp ++ Rb ++ Rc))
    (hrun : letCont (run .static P₁ n) ρ₁ p₁ b₁ (v₁, τ₁) = some M₁) :
    ∃ M₂, letCont (run .static P₂ n) ρ₂ p₂ b₂ (v₂, τ₂) = some M₂ ∧
      List.Forall₂ (Out C (ρ₁ ++ [1]) (ρ₂ ++ [1]) ν₁ μ D₁ Rb Rc) M₁ M₂ := by
  have hci' : CI C ν₁ D₁ (Rp ++ (Rb ++ Rc)) τ₁ τ₂ := by rw [← List.append_assoc]; exact hci
  have hF' : Fresh (ρ₁ ++ [1]) (ρ₂ ++ [1]) ν₁ D₁ (Rp ++ (Rb ++ Rc)) := by
    rw [← List.append_assoc]; exact hF
  have hact := hv.applyStore hfvv hci.store (fun m hm => by cases hm)
  have hg := hact.toGVal?
  unfold letCont at hrun ⊢
  simp only at hrun ⊢
  rcases OptRel.cases hg with ⟨e1, e2⟩ | ⟨g₁, g₂, e1, e2, hgg⟩
  · rw [e1] at hrun
    rw [e2]
    simp only at hrun ⊢
    cases p₁ with
    | var f₁ =>
        obtain rfl := hp.var_left
        simp only at hrun ⊢
        exact sim_chain ih hb hv rfl hci'.drop hF'.drop (hfvp f₁ (by simp [freeNames])) hfvb hfvv
          hfpv hfpb hrun
    | sym _ | fn _ | pvar _ | lam _ _ _ | app _ _ | quote _ | pquote _ | ctx _ _ | letP _ _ _ | alt _ _ =>
        simp only at hrun
        injection hrun with hrun
        subst hrun
        refine ⟨[], ?_, .nil⟩
        cases p₂ with
        | var m =>
            obtain ⟨_, h⟩ := hp.right_var_pat
            cases h
        | _ => rfl
  · rw [e1] at hrun
    rw [e2]
    simp only at hrun ⊢
    have hm := hp.matchT hQ hC hA hfvp hci.inj hgg hci.store
    rcases OptRel.cases hm with ⟨e3, e4⟩ | ⟨s₁, s₂, e3, e4, hss⟩
    · rw [e3] at hrun
      rw [e4]
      simp only at hrun ⊢
      injection hrun with hrun
      subst hrun
      exact ⟨[], rfl, .nil⟩
    · rw [e3] at hrun
      rw [e4]
      simp only at hrun ⊢
      exact ih hb hfpb hfvb (hci'.with_store hss).drop hF'.drop hrun

/-- **The simulation of a plain `let`.** -/
theorem sim_letP [CodeId X₁] [CodeId X₂] (hQ : C.BiUnique) (hC : C.CodeAgree) (hA : C.PatAgree) {n : ℕ} (ih : SimAt C P₁ P₂ n) {π π' : Path}
    {σ₁ : GStore S X₁} {σ₂ : GStore S X₂} {p₁ w₁ b₁ : Tm S X₁} {p₂ w₂ b₂ : Tm S X₂}
    {ν μ : Nm X₁ → Nm X₂} {Rp Rw Rb Rc : List (Nm X₂)} {op ow ob : Bool}
    {D : Set (Nm X₁)} {L₁ : Result S X₁}
    (hp : Rel C ν μ .pat Rp op p₁ p₂) (hw : Rel C ν μ .code Rw ow w₁ w₂)
    (hb : Rel C ν μ .code Rb ob b₁ b₂)
    (hfp : freeParams (.letP p₁ w₁ b₁ : Tm S X₁) = [])
    (hfv : ∀ m ∈ freeNames (.letP p₁ w₁ b₁ : Tm S X₁), m ∈ D)
    (hci : CI C ν D (Rp ++ Rw ++ Rb ++ Rc) σ₁ σ₂) (hF : Fresh π π' ν D (Rp ++ Rw ++ Rb ++ Rc))
    (hrun : step .static P₁ (run .static P₁ n) π σ₁ (.letP p₁ w₁ b₁) = some L₁) :
    ∃ L₂, step .static P₂ (run .static P₂ n) π' σ₂ (.letP p₂ w₂ b₂) = some L₂ ∧
      List.Forall₂ (Out C π π' ν μ D (Rp ++ Rw ++ Rb) Rc) L₁ L₂ := by
  simp only [freeParams, List.append_eq_nil_iff] at hfp
  obtain ⟨⟨hfpp, hfpw⟩, hfpb⟩ := hfp
  have hfvp : ∀ m ∈ freeNames p₁, m ∈ D := fun m h => hfv m (by simp [freeNames, h])
  have hfvw : ∀ m ∈ freeNames w₁, m ∈ D := fun m h => hfv m (by simp [freeNames, h])
  have hfvb : ∀ m ∈ freeNames b₁, m ∈ D := fun m h => hfv m (by simp [freeNames, h])
  have hperm : (Rp ++ Rw ++ Rb ++ Rc).Perm (Rw ++ (Rp ++ Rb ++ Rc)) := by
    simp only [List.append_assoc]
    exact List.perm_append_comm_assoc Rp Rw (Rb ++ Rc)
  cases hl₁ : letLam? p₁ w₁ with
  | some f₁ =>
      rw [step_letP_some hl₁] at hrun
      obtain ⟨rfl, x, own, bb, rfl⟩ := letLam?_some hl₁
      obtain rfl := hp.var_left
      obtain ⟨x', own', bb', rfl⟩ := hw.left_lam_code
      rw [step_letP_some (rfl : letLam? (.var (ν f₁)) (.lam x' own' bb') = some (ν f₁))]
      have hRp : Rp = [] := by cases hp; rfl
      have hRw : Rw = [] := by cases hw; rfl
      subst hRp hRw
      obtain ⟨-, hwv⟩ := hw.toVal (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨x, own, bb, rfl⟩)))))
      obtain ⟨L₂, hL₂, hrel⟩ := sim_chain ih hb hwv rfl (by simpa using hci) (by simpa using hF)
        (hfvp f₁ (by simp [freeNames])) hfvb hfvw hfpw hfpb hrun
      exact ⟨L₂, hL₂, hrel.imp fun _ _ h => h.res_mono (by simp)⟩
  | none =>
      rw [step_letP_none hl₁] at hrun
      obtain ⟨Lw₁, hLw₁, hbw⟩ := bindOpt_eq_some hrun
      cases hl₂ : letLam? p₂ w₂ with
      | some f₂ =>
          rw [step_letP_some hl₂]
          obtain ⟨rfl, x₂, own₂, bb₂, rfl⟩ := letLam?_some hl₂
          obtain ⟨f₁, rfl⟩ := hp.right_var_pat
          have hf2 : ν f₁ = f₂ := by have := hp.var_left; injection this with e; exact e.symm
          subst hf2
          have hRp : Rp = [] := by cases hp; rfl
          subst hRp
          have hciw : CI C ν D (Rw ++ (Rb ++ Rc)) σ₁ σ₂ := by simpa [List.append_assoc] using hci
          have hFw : Fresh π π' ν D (Rw ++ (Rb ++ Rc)) := by simpa [List.append_assoc] using hF
          have hold₀ : ∀ m ∈ freeNames w₁, OldAt (π ++ [0]) m :=
            fun m hm => (hF.old₁ m (hfvw m hm)).child 0
          obtain ⟨v₁, ν', hL, hrelv, hfpv, hagree, hfvv, hinjv⟩ :=
            newChain n hw hfpw (List.nodup_append.1 hciw.nodup).1 hold₀ hLw₁
          subst hL
          rw [bindAll_singleton] at hbw
          obtain ⟨hci', hE, hold, hclass⟩ := newChain_cfg hciw hFw hfvw hagree hfvv hinjv
          have hF' : Fresh (π ++ [1]) π' ν' (D ∪ {n | n ∈ freeNames v₁}) (Rb ++ Rc) := by
            refine ⟨?_, ?_, ?_⟩
            · intro n hn
              rcases hclass n hn with h1 | ⟨hn1, _⟩
              · exact (hF.old₁ n h1).child 1
              · exact (hn1.avoid_sibling (by decide)).oldAt
            · intro n hn
              rcases hclass n hn with h1 | ⟨_, hr1⟩
              · rw [hold n h1]; exact hF.old₂ n h1
              · exact hFw.oldRes _ (List.mem_append_left _ hr1)
            · intro m hm
              exact hFw.oldRes m (List.mem_append_right _ hm)
          have hf₁ : f₁ ∈ D := hfv f₁ (by simp [freeNames])
          have hb' : Rel C ν' μ .code Rb ob b₁ b₂ :=
            hb.congr (fun m hm => (hold m (hfvb m hm)).symm) (fun _ _ => rfl)
          obtain ⟨x₁, own₁, bb₁, rfl⟩ := hrelv.right_lam_val
          unfold letCont at hbw
          simp only [act_lam, Tm.toGVal?] at hbw
          obtain ⟨L₂, hL₂, hrel⟩ := sim_chain ih hb' hrelv (hold f₁ hf₁) hci' hF' (Or.inl hf₁)
            (fun m hm => Or.inl (hfvb m hm)) (fun m hm => Or.inr hm) hfpv hfpb hbw
          exact ⟨L₂, hL₂, hrel.imp fun _ _ h => (h.parent₁.after hE).res_mono (by simp)⟩
      | none =>
          rw [step_letP_none hl₂]
          obtain ⟨Lw₂, hLw₂, hwr⟩ := ih hw hfpw hfvw (hci.perm hperm) ((hF.perm hperm).child 0 0) hLw₁
          rw [hLw₂]
          refine bindAll_sim ?_ hwr hbw
          rintro ⟨v₁, τ₁⟩ ⟨v₂, τ₂⟩ M₁ ⟨ν₁, D₁, hfv₁, hE₁, hrel₁, hfp₁, hci₁⟩ hM₁
          simp only at hfv₁ hrel₁ hfp₁ hci₁
          have hp₁ : Rel C ν₁ μ .pat Rp op p₁ p₂ :=
            hp.congr (fun m hm => (hE₁.agree m (hfvp m hm)).symm) (fun _ _ => rfl)
          have hb₁ : Rel C ν₁ μ .code Rb ob b₁ b₂ :=
            hb.congr (fun m hm => (hE₁.agree m (hfvb m hm)).symm) (fun _ _ => rfl)
          have hFb : Fresh (π ++ [1]) (π' ++ [1]) ν₁ D₁ (Rp ++ Rb ++ Rc) :=
            hE₁.fresh_sibling (by decide) (by decide) (hF.perm hperm)
          obtain ⟨M₂, hM₂, hrelM⟩ := sim_letCont hQ hC hA ih hrel₁ hfv₁ hfp₁ hp₁ hb₁
            (fun m hm => hE₁.sub (hfvp m hm)) (fun m hm => hE₁.sub (hfvb m hm)) hfpb hci₁ hFb hM₁
          refine ⟨M₂, hM₂, hrelM.imp fun _ _ h => ?_⟩
          exact (h.parent.after hE₁.parent).res_mono (fun m hm => by simp at hm ⊢; tauto)


omit [DecidableEq S] [DecidableEq X₂] in
theorem subst_rename_var (ρ : Path) (own : List X₁) (φ : Sub S X₁) (f : Nm X₁) :
    subst (renameOwn ρ own) φ (.var f) =
      .var (if ownKey own f = true then .inst ρ f else f) := by
  by_cases h : ownKey own f = true
  · simp [subst, renameOwn, h]
  · simp [subst, renameOwn, h]

theorem letCont_mono {Y : Type v} [DecidableEq Y] [CodeId Y] {d : Disc} {P : S → Option (Tm S Y)}
    {n m : ℕ} (hnm : n ≤ m) {π : Path} {p b : Tm S Y} {r : Tm S Y × GStore S Y}
    {M : Result S Y} (h : letCont (run d P n) π p b r = some M) :
    letCont (run d P m) π p b r = some M := by
  unfold letCont at h ⊢
  cases hg : (act r.2 r.1).toGVal? with
  | some g =>
      rw [hg] at h
      simp only at h ⊢
      cases hm : matchT r.2 p g.toTm with
      | some σ₂ =>
          rw [hm] at h
          exact run_mono d P hnm h
      | none =>
          rw [hm] at h
          exact h
  | none =>
      rw [hg] at h
      simp only at h ⊢
      cases p with
      | var f => exact run_mono d P hnm h
      | _ => exact h

omit [DecidableEq S] in
/-- **Opening a `let`-activation on the first side**, after its right-hand side
was evaluated: the pattern, the value and the body are related under the map
that sends the copies of the `let`'s own names to its reserved names. -/
theorem letAct_open {ν ν₁ μ νi : Nm X₁ → Nm X₂} {own : List X₁} {ℓ : Nm X₁}
    {p₁ b₁ : Tm S X₁} {p₂ b₂ : Tm S X₂} {Rh Rp Rb Rc : List (Nm X₂)} {D D₁ : Set (Nm X₁)}
    {τ₁ : GStore S X₁} {τ₂ : GStore S X₂} {v₁ : Tm S X₁} {v₂ : Tm S X₂} {ρ : Path}
    (hνi : ∀ n, ownKey own n = false → νi n = ν n)
    {op ob : Bool} (hp : Rel C νi μ .pat Rp op p₁ p₂) (hb : Rel C νi μ .code Rb ob b₁ b₂)
    (hlive : ∀ n ∈ freeNames p₁ ++ freeNames b₁, ownKey own n = true → νi n ∈ Rh)
    (hinj : ∀ n ∈ freeNames p₁ ++ freeNames b₁, ∀ n' ∈ freeNames p₁ ++ freeNames b₁,
      ownKey own n = true → ownKey own n' = true → νi n = νi n' → n = n')
    (hfpp : freeParams p₁ = []) (hfpb : freeParams b₁ = [])
    (hfvo : ∀ n, (n ∈ freeNames p₁ ∨ n ∈ freeNames b₁) → ownKey own n = false → n ∈ D)
    (hsub : D ⊆ D₁) (hagree : ∀ n ∈ D, ν₁ n = ν n)
    (hv : Rel C ν₁ μ .val [] true v₁ v₂) (hfvv : ∀ m ∈ freeNames v₁, m ∈ D₁)
    (hci : CI C ν₁ D₁ (Rh ++ (Rp ++ Rb ++ Rc)) τ₁ τ₂) (hav : ∀ n ∈ D₁, Avoid ρ n) :
    ∃ D₂ : Set (Nm X₁), D₁ ⊆ D₂ ∧
      (∀ m ∈ freeNames (subst (renameOwn ρ own) (Sub.single ℓ v₁) p₁), m ∈ D₂) ∧
      (∀ m ∈ freeNames (subst (renameOwn ρ own) (Sub.single ℓ v₁) b₁), m ∈ D₂) ∧
      Rel C (openMap ρ own νi ν₁) μ .pat Rp op (subst (renameOwn ρ own) (Sub.single ℓ v₁) p₁) p₂ ∧
      Rel C (openMap ρ own νi ν₁) μ .code Rb ob (subst (renameOwn ρ own) (Sub.single ℓ v₁) b₁) b₂ ∧
      Rel C (openMap ρ own νi ν₁) μ .val [] true v₁ v₂ ∧
      CI C (openMap ρ own νi ν₁) D₂ (Rp ++ Rb ++ Rc) τ₁ τ₂ ∧
      (∀ n ∈ D₁, openMap ρ own νi ν₁ n = ν₁ n) ∧
      (∀ n ∈ D₂, n ∈ D₁ ∨ ∃ s, n = .inst ρ (.src s) ∧ openMap ρ own νi ν₁ n ∈ Rh) := by
  have hold : ∀ n ∈ D₁, openMap ρ own νi ν₁ n = ν₁ n := fun n hn => openMap_other (hav n hn).ne_inst
  -- free names of the opened pattern and body
  have hopen : ∀ (u : Tm S X₁), (∀ n ∈ freeNames u, n ∈ freeNames p₁ ∨ n ∈ freeNames b₁) →
      freeParams u = [] → ∀ m ∈ freeNames (subst (renameOwn ρ own) (Sub.single ℓ v₁) u),
        (m ∈ D ∧ ownKey own m = false) ∨
        ∃ m₀ ∈ freeNames p₁ ++ freeNames b₁, ownKey own m₀ = true ∧ m = .inst ρ m₀ := by
    intro u hu hfpu m hm
    rcases mem_freeNames_open hm with ⟨h1, h2⟩ | ⟨m₀, hm₀, ho, rfl⟩ | ⟨h1, _⟩
    · exact Or.inl ⟨hfvo m (hu m h1) h2, h2⟩
    · exact Or.inr ⟨m₀, List.mem_append.2 (hu m₀ hm₀), ho, rfl⟩
    · rw [hfpu] at h1; cases h1
  have hcongr : ∀ (u : Tm S X₁), (∀ n ∈ freeNames u, n ∈ freeNames p₁ ∨ n ∈ freeNames b₁) →
      freeParams u = [] → ∀ m ∈ freeNames (subst (renameOwn ρ own) (Sub.single ℓ v₁) u),
        openMap ρ own νi ν m = openMap ρ own νi ν₁ m := by
    intro u hu hfpu m hm
    rcases hopen u hu hfpu m hm with ⟨h1, _⟩ | ⟨m₀, _, ho, rfl⟩
    · rw [openMap_other (hav m (hsub h1)).ne_inst, openMap_other (hav m (hsub h1)).ne_inst,
        hagree m h1]
    · rw [openMap_own ho, openMap_own ho]
  have hav₀ : ∀ n ∈ freeNames p₁ ++ freeNames b₁, ownKey own n = false → ∀ m, n ≠ .inst ρ m :=
    fun n hn ho => (hav n (hsub (hfvo n (List.mem_append.1 hn) ho))).ne_inst
  have hp' := open_body (ℓ := ℓ) hνi hp hfpp v₁ (ρ := ρ)
    (fun n hn ho => hav₀ n (List.mem_append_left _ hn) ho)
  have hb' := open_body (ℓ := ℓ) hνi hb hfpb v₁ (ρ := ρ)
    (fun n hn ho => hav₀ n (List.mem_append_right _ hn) ho)
  refine ⟨D₁ ∪ {n | n ∈ freeNames (.letP (subst (renameOwn ρ own) (Sub.single ℓ v₁) p₁) v₁
      (subst (renameOwn ρ own) (Sub.single ℓ v₁) b₁) : Tm S X₁)}, Set.subset_union_left,
    fun m h => Or.inr (by simp [freeNames, h]), fun m h => Or.inr (by simp [freeNames, h]),
    hp'.congr (hcongr p₁ (fun n h => Or.inl h) hfpp) (fun _ _ => rfl),
    hb'.congr (hcongr b₁ (fun n h => Or.inr h) hfpb) (fun _ _ => rfl),
    hv.congr (fun m hm => (hold m (hfvv m hm)).symm) (fun _ _ => rfl), ?_, hold, ?_⟩
  · refine open_ci hci hav hlive hinj ?_
    intro n hn
    simp only [freeNames, List.mem_append] at hn
    rcases hn with (hn | hn) | hn
    · rcases hopen p₁ (fun n h => Or.inl h) hfpp n hn with ⟨h1, _⟩ | h
      · exact Or.inl (hsub h1)
      · exact Or.inr h
    · exact Or.inl (hfvv n hn)
    · rcases hopen b₁ (fun n h => Or.inr h) hfpb n hn with ⟨h1, _⟩ | h
      · exact Or.inl (hsub h1)
      · exact Or.inr h
  · intro n hn
    rcases hn with hn | hn
    · exact Or.inl hn
    · simp only [Set.mem_ofPred_eq, freeNames, List.mem_append] at hn
      have key : ∀ (u : Tm S X₁), (∀ n ∈ freeNames u, n ∈ freeNames p₁ ∨ n ∈ freeNames b₁) →
          freeParams u = [] → n ∈ freeNames (subst (renameOwn ρ own) (Sub.single ℓ v₁) u) →
          n ∈ D₁ ∨ ∃ s, n = .inst ρ (.src s) ∧ openMap ρ own νi ν₁ n ∈ Rh := by
        intro u hu hfpu hnu
        rcases hopen u hu hfpu n hnu with ⟨h1, _⟩ | ⟨m₀, hm₀, ho, rfl⟩
        · exact Or.inl (hsub h1)
        · obtain ⟨s, rfl⟩ := src_of_ownKey ho
          exact Or.inr ⟨s, rfl, by rw [openMap_own ho]; exact hlive _ hm₀ ho⟩
      rcases hn with (hn | hn) | hn
      · exact key p₁ (fun n h => Or.inl h) hfpp hn
      · exact Or.inl (hfvv n hn)
      · exact key b₁ (fun n h => Or.inr h) hfpb hn


omit [DecidableEq S] [DecidableEq X₁] [DecidableEq X₂] in
/-- A bag simulation through `bindAll` that knows where each element comes from. -/
theorem bindAll_sim_mem {α₁ α₂ β₁ β₂ : Type*} {Rin : α₁ → α₂ → Prop} {Rout : β₁ → β₂ → Prop}
    {g₁ : α₁ → Option (List β₁)} {g₂ : α₂ → Option (List β₂)} :
    ∀ {l₁ : List α₁} {l₂ : List α₂} {L₁ : List β₁},
      (∀ a₁ ∈ l₁, ∀ a₂ M₁, Rin a₁ a₂ → g₁ a₁ = some M₁ →
        ∃ M₂, g₂ a₂ = some M₂ ∧ List.Forall₂ Rout M₁ M₂) →
      List.Forall₂ Rin l₁ l₂ →
      bindAll l₁ g₁ = some L₁ → ∃ L₂, bindAll l₂ g₂ = some L₂ ∧ List.Forall₂ Rout L₁ L₂
  | [], [], L₁, _, .nil, h => by
      simp only [bindAll] at h
      injection h with h
      subst h
      exact ⟨[], rfl, .nil⟩
  | a₁ :: l₁, a₂ :: l₂, L₁, hg, .cons hr hrs, h => by
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
              obtain ⟨M₂, e1, hM⟩ := hg a₁ List.mem_cons_self a₂ M₁ hr h1
              obtain ⟨N₂, e2, hN⟩ := bindAll_sim_mem
                (fun b hb => hg b (List.mem_cons_of_mem a₁ hb)) hrs h2
              refine ⟨M₂ ++ N₂, ?_, forall₂_append hM hN⟩
              unfold bindAll
              rw [e1, e2]

omit [DecidableEq S] [DecidableEq X₁] [DecidableEq X₂] in
theorem Avoid.oldAt_append {Y : Type v} {ρ : Path} {n : Nm Y} (h : Avoid ρ n) (l : Path) :
    OldAt (ρ ++ l) n := by
  intro ρ' hρ' hs
  apply h ρ' hρ'
  obtain ⟨r, hr⟩ := hs.prefix
  exact ⟨l ++ r, by rw [← hr, List.append_assoc]⟩

omit [DecidableEq S] [DecidableEq X₁] [DecidableEq X₂] in
theorem oldAt_inst_append {Y : Type v} (ρ : Path) (l : Path) (s : Y) :
    OldAt (ρ ++ l) (.inst ρ (.src s) : Nm Y) := by
  intro ρ' hρ' hs
  simp only [tags, List.mem_cons, List.not_mem_nil, or_false] at hρ'
  subst hρ'
  obtain ⟨i, r, e⟩ := hs
  have := congrArg List.length e
  simp at this

omit [DecidableEq S] [DecidableEq X₂] in
theorem subst_letP_param (θ : Sub S X₁) (ℓ : Nm X₁) (v p b : Tm S X₁) :
    subst θ (Sub.single ℓ v) (.letP p (.pvar ℓ) b) =
      .letP (subst θ (Sub.single ℓ v) p) v (subst θ (Sub.single ℓ v) b) := by
  simp [subst, Sub.single]

/-- **After opening a `let`-activation** with one value of its right-hand side:
the first side's `let` at the activation path against the second side's `let`
continuation. -/
theorem sim_letAct_cont [CodeId X₁] [CodeId X₂] (hQ : C.BiUnique) (hC : C.CodeAgree) (hA : C.PatAgree) {n' : ℕ} (ih' : SimAt C P₁ P₂ n') {π π' : Path}
    {τ₁ : GStore S X₁} {τ₂ : GStore S X₂} {p₁' b₁' v₁ : Tm S X₁} {p₂ b₂ v₂ : Tm S X₂}
    {ν₂ μ : Nm X₁ → Nm X₂} {Rp Rb Rc : List (Nm X₂)} {D₂ : Set (Nm X₁)} {M₁ : Result S X₁}
    {op ob : Bool} (hp₂ : Rel C ν₂ μ .pat Rp op p₁' p₂) (hb₂ : Rel C ν₂ μ .code Rb ob b₁' b₂)
    (hv₂ : Rel C ν₂ μ .val [] true v₁ v₂) (hci₂ : CI C ν₂ D₂ (Rp ++ Rb ++ Rc) τ₁ τ₂)
    (hFresh : ∀ l : Path, Fresh (π ++ [2] ++ l) (π' ++ [1]) ν₂ D₂ (Rp ++ Rb ++ Rc))
    (hfvp : ∀ m ∈ freeNames p₁', m ∈ D₂) (hfvb : ∀ m ∈ freeNames b₁', m ∈ D₂)
    (hfvv : ∀ m ∈ freeNames v₁, m ∈ D₂) (hfpv : freeParams v₁ = []) (hfpb : freeParams b₁' = [])
    (hinert : Inert P₁ v₁)
    (hM₁ : step .static P₁ (run .static P₁ n') (π ++ [2]) τ₁ (.letP p₁' v₁ b₁') = some M₁) :
    ∃ M₂, letCont (run .static P₂ (n' + 1)) π' p₂ b₂ (v₂, τ₂) = some M₂ ∧
      List.Forall₂ (Out C π π' ν₂ μ D₂ Rb Rc) M₁ M₂ := by
  cases hl₃ : letLam? p₁' v₁ with
  | some f =>
      rw [step_letP_some hl₃] at hM₁
      obtain ⟨rfl, x, own', bb, rfl⟩ := letLam?_some hl₃
      have hRp : Rp = [] := by cases hp₂; rfl
      subst hRp
      obtain rfl := hp₂.var_left
      obtain ⟨x₂, own₂, bb₂, rfl⟩ := hv₂.left_lam_code
      have hF₂ : Fresh (π ++ [2]) (π' ++ [1]) ν₂ D₂ (Rb ++ Rc) := by
        have h := hFresh []
        simp only [List.append_nil, List.nil_append] at h
        exact h
      obtain ⟨M₂, hM₂, hrelM⟩ := sim_chain ih' hb₂ hv₂ rfl (by simpa using hci₂) hF₂
        (hfvp f (by simp [freeNames])) hfvb hfvv hfpv hfpb hM₁
      refine ⟨M₂, ?_, hrelM.imp fun _ _ h => h.parent⟩
      unfold letCont
      simp only [act_lam, Tm.toGVal?]
      exact run_mono .static P₂ (Nat.le_succ n') hM₂
  | none =>
      rw [step_letP_none hl₃] at hM₁
      obtain ⟨Lv, hLv, hbv⟩ := bindOpt_eq_some hM₁
      rw [run_inert P₁ .static v₁ hinert _ _ _ _ hLv, bindAll_singleton] at hbv
      obtain ⟨M₂, hM₂, hrelM⟩ := sim_letCont hQ hC hA ih' hv₂ hfvv hfpv hp₂ hb₂ hfvp hfvb hfpb
        hci₂ (hFresh [1]) hbv
      exact ⟨M₂, letCont_mono (Nat.le_succ n') hM₂, hrelM.imp fun _ _ h => h.parent.parent₁⟩

/-- **After a chain of `new` blocks and the opening**, when the second side's
`let` substitutes its lambda in place. -/
theorem sim_letAct_chain [CodeId X₁] [CodeId X₂] {n' : ℕ} (ih' : SimAt C P₁ P₂ n') {π π' : Path}
    {σ₁ : GStore S X₁} {σ₂ : GStore S X₂} {f₁' : Nm X₁} {f₂ : Nm X₂} {v₁ b₁' : Tm S X₁}
    {v₂ b₂ : Tm S X₂} {ν₂ μ : Nm X₁ → Nm X₂} {Rb Rc : List (Nm X₂)} {D₂ : Set (Nm X₁)}
    {L₁ : Result S X₁}
    {ob : Bool} (hb₂ : Rel C ν₂ μ .code Rb ob b₁' b₂) (hv₂ : Rel C ν₂ μ .val [] true v₁ v₂) (hf₂ : ν₂ f₁' = f₂)
    (hci₂ : CI C ν₂ D₂ (Rb ++ Rc) σ₁ σ₂) (hF₂ : Fresh (π ++ [2]) π' ν₂ D₂ (Rb ++ Rc))
    (hf : f₁' ∈ D₂) (hfvb : ∀ m ∈ freeNames b₁', m ∈ D₂) (hfvv : ∀ m ∈ freeNames v₁, m ∈ D₂)
    (hfpv : freeParams v₁ = []) (hfpb : freeParams b₁' = [])
    (hrun : run .static P₁ n' (π ++ [2]) σ₁ (subst (Sub.single f₁' v₁) Sub.none b₁') = some L₁) :
    ∃ L₂, run .static P₂ (n' + 1) π' σ₂ (subst (Sub.single f₂ v₂) Sub.none b₂) = some L₂ ∧
      List.Forall₂ (Out C π π' ν₂ μ D₂ Rb Rc) L₁ L₂ := by
  obtain ⟨L₂, hL₂, hrel⟩ := sim_chain ih' hb₂ hv₂ hf₂ hci₂ hF₂ hf hfvb hfvv hfpv hfpb hrun
  exact ⟨L₂, run_mono .static P₂ (Nat.le_succ n') hL₂, hrel.imp fun _ _ h => h.parent₁⟩

/-- **A `let`-activation whose second side substitutes a lambda in place**:
the first side evaluates its right-hand side (a chain of `new` blocks around a
lambda), opens the `let`, and substitutes. -/
theorem sim_letAct_inPlace [CodeId X₁] [CodeId X₂] {n' : ℕ} (ih' : SimAt C P₁ P₂ n') {π π' : Path}
    {σ₁ : GStore S X₁} {σ₂ : GStore S X₂} {ℓ : Nm X₁} {own : List X₁} {p₁ w₁ b₁ : Tm S X₁}
    {f₂ x₂ : Nm X₂} {own₂ : List X₂} {bb₂ b₂ : Tm S X₂}
    {ν μ νi : Nm X₁ → Nm X₂} {Rh Rw Rp Rb Rc : List (Nm X₂)} {D : Set (Nm X₁)}
    {Lw₁ L₁ : Result S X₁}
    (hνi : ∀ n, ownKey own n = false → νi n = ν n)
    {ow op ob : Bool}
    (hw : Rel C ν μ .code Rw ow w₁ (.lam x₂ own₂ bb₂)) (hp : Rel C νi μ .pat Rp op p₁ (.var f₂))
    (hb : Rel C νi μ .code Rb ob b₁ b₂)
    (hlive : ∀ n ∈ freeNames p₁ ++ freeNames b₁, ownKey own n = true → νi n ∈ Rh)
    (hinj : ∀ n ∈ freeNames p₁ ++ freeNames b₁, ∀ n' ∈ freeNames p₁ ++ freeNames b₁,
      ownKey own n = true → ownKey own n' = true → νi n = νi n' → n = n')
    (hfpp : freeParams p₁ = []) (hfpb : freeParams b₁ = []) (hfpw : freeParams w₁ = [])
    (hfvw : ∀ m ∈ freeNames w₁, m ∈ D)
    (hfvo : ∀ n, (n ∈ freeNames p₁ ∨ n ∈ freeNames b₁) → ownKey own n = false → n ∈ D)
    (hciw : CI C ν D (Rw ++ (Rh ++ (Rp ++ Rb ++ Rc))) σ₁ σ₂)
    (hFw : Fresh π π' ν D (Rw ++ (Rh ++ (Rp ++ Rb ++ Rc))))
    (hLw₁ : run .static P₁ (n' + 1) (π ++ [1]) σ₁ w₁ = some Lw₁)
    (hbw : bindAll Lw₁ (fun r₂ => run .static P₁ (n' + 1) (π ++ [2]) r₂.2
      (.letP (subst (renameOwn (π ++ [2]) own) (Sub.single ℓ r₂.1) p₁) r₂.1
        (subst (renameOwn (π ++ [2]) own) (Sub.single ℓ r₂.1) b₁))) = some L₁) :
    ∃ L₂, run .static P₂ (n' + 1) π' σ₂ (subst (Sub.single f₂ (.lam x₂ own₂ bb₂)) Sub.none b₂) =
      some L₂ ∧ List.Forall₂ (Out C π π' ν μ D (Rw ++ (Rh ++ Rb)) Rc) L₁ L₂ := by
  have hoffs : ∀ n ∈ D, Avoid (π ++ [2]) n := fun n hn => (hFw.old₁ n hn).avoid_child 2
  obtain ⟨f₁, rfl⟩ := hp.right_var_pat
  have hRp : Rp = [] := by cases hp; rfl
  subst hRp
  have hf₂ : f₂ = νi f₁ := by
    have := hp.var_left
    injection this
  subst hf₂
  have hndw : Rw.Nodup := (List.nodup_append.1 hciw.nodup).1
  obtain ⟨v₁, ν', hL, hrelv, hfpv, hagree, hfvv, hinjv⟩ :=
    newChain (n' + 1) hw hfpw hndw (fun m hm => (hFw.old₁ m (hfvw m hm)).child 1) hLw₁
  subst hL
  rw [bindAll_singleton] at hbw
  obtain ⟨hci₁, hE₁, hold₁, hclass₁⟩ := newChain_cfg hciw hFw hfvw hagree hfvv hinjv
  have hAv : ∀ n ∈ D ∪ {n | n ∈ freeNames v₁}, Avoid (π ++ [2]) n := by
    intro n hn
    rcases hclass₁ n hn with h | ⟨hn1, _⟩
    · exact hoffs n h
    · exact hn1.avoid_sibling (by decide)
  obtain ⟨D₂, hsub₂, hfvp', hfvb', hp₂, hb₂, hv₂, hci₂, hold₂, hclass₂⟩ :=
    letAct_open (ℓ := ℓ) hνi hp hb hlive hinj hfpp hfpb hfvo Set.subset_union_left hold₁ hrelv
      (fun m hm => Or.inr hm) hci₁ hAv
  obtain ⟨x₁, own₁, bb₁, rfl⟩ := hrelv.right_lam_val
  rw [subst_rename_var] at hp₂ hbw hfvp'
  have hpv := hp₂.var_left
  injection hpv with hpv
  change step .static P₁ (run .static P₁ n') (π ++ [2]) σ₁ (.letP (.var _) _ _) = some L₁ at hbw
  rw [step_letP_some rfl] at hbw
  have hE₂ : Ext π π' Rh ν' (D ∪ {n | n ∈ freeNames (.lam x₁ own₁ bb₁ : Tm S X₁)})
      (openMap (π ++ [2]) own νi ν') D₂ := by
    refine ⟨hold₂, hsub₂, ?_⟩
    intro n hn hnD
    rcases hclass₂ n hn with h | ⟨s, rfl, hr⟩
    · exact absurd h hnD
    · exact ⟨newAt_inst 2 s, Or.inr hr⟩
  have hRw : ∀ m ∈ Rw, m ∈ Rw ++ (Rh ++ ([] ++ Rb ++ Rc)) := fun m h => List.mem_append_left _ h
  have hRh : ∀ m ∈ Rh, m ∈ Rw ++ (Rh ++ ([] ++ Rb ++ Rc)) :=
    fun m h => List.mem_append_right _ (List.mem_append_left _ h)
  have hRbc : ∀ m ∈ Rb ++ Rc, m ∈ Rw ++ (Rh ++ ([] ++ Rb ++ Rc)) := by
    intro m h
    refine List.mem_append_right _ (List.mem_append_right _ ?_)
    simpa using h
  have hF₂ : Fresh (π ++ [2]) π' (openMap (π ++ [2]) own νi ν') D₂ (Rb ++ Rc) := by
    refine ⟨?_, ?_, ?_⟩
    · intro n hn
      rcases hclass₂ n hn with h | ⟨s, rfl, _⟩
      · exact (hAv n h).oldAt
      · exact oldAt_inst_self _ s
    · intro n hn
      rcases hclass₂ n hn with h | ⟨s, rfl, hr⟩
      · rw [hold₂ n h]
        rcases hclass₁ n h with h' | ⟨_, hr'⟩
        · rw [hold₁ n h']; exact hFw.old₂ n h'
        · exact hFw.oldRes _ (hRw _ hr')
      · exact hFw.oldRes _ (hRh _ hr)
    · intro m hm
      exact hFw.oldRes m (hRbc m hm)
  have hci₂' : CI C (openMap (π ++ [2]) own νi ν') D₂ (Rb ++ Rc) σ₁ σ₂ := by
    rw [List.nil_append] at hci₂
    exact hci₂
  obtain ⟨L₂, hL₂, hrel⟩ := sim_letAct_chain ih' hb₂ hv₂ hpv.symm hci₂' hF₂
    (hfvp' _ (by simp [freeNames])) hfvb' (fun m h => hsub₂ (Or.inr h)) hfpv
    (freeParams_open (fun x hx => by rw [hfpb] at hx; cases hx) hfpv) hbw
  exact ⟨L₂, hL₂, hrel.imp fun _ _ h => (h.after hE₂).after hE₁⟩

/-- **The simulation of a `let`-activation** against a plain `let`: the
right-hand side, then the first side opens the `let` at a fresh path, then
the match, substitution or failure, alike. -/
theorem sim_letAct [CodeId X₁] [CodeId X₂] (hQ : C.BiUnique) (hC : C.CodeAgree) (hA : C.PatAgree) {n' : ℕ} (ih : SimAt C P₁ P₂ (n' + 1))
    (ih' : SimAt C P₁ P₂ n') {π π' : Path} {σ₁ : GStore S X₁} {σ₂ : GStore S X₂}
    {ℓ : Nm X₁} {own : List X₁} {p₁ w₁ b₁ : Tm S X₁} {p₂ w₂ b₂ : Tm S X₂}
    {ν μ νi : Nm X₁ → Nm X₂} {Rh Rw Rp Rb Rc : List (Nm X₂)} {D : Set (Nm X₁)}
    {L₁ : Result S X₁}
    (hνi : ∀ n, ownKey own n = false → νi n = ν n)
    (hℓp : ℓ ∉ freeParams p₁) (hℓb : ℓ ∉ freeParams b₁)
    {ow op ob : Bool}
    (hw : Rel C ν μ .code Rw ow w₁ w₂) (hp : Rel C νi μ .pat Rp op p₁ p₂)
    (hb : Rel C νi μ .code Rb ob b₁ b₂)
    (hlive : ∀ n ∈ freeNames p₁ ++ freeNames b₁, ownKey own n = true → νi n ∈ Rh)
    (hinj : ∀ n ∈ freeNames p₁ ++ freeNames b₁, ∀ n' ∈ freeNames p₁ ++ freeNames b₁,
      ownKey own n = true → ownKey own n' = true → νi n = νi n' → n = n')
    (hfp : freeParams (.app (.lam ℓ own (.letP p₁ (.pvar ℓ) b₁)) w₁ : Tm S X₁) = [])
    (hfv : ∀ m ∈ freeNames (.app (.lam ℓ own (.letP p₁ (.pvar ℓ) b₁)) w₁ : Tm S X₁), m ∈ D)
    (hci : CI C ν D (Rh ++ Rw ++ Rp ++ Rb ++ Rc) σ₁ σ₂)
    (hF : Fresh π π' ν D (Rh ++ Rw ++ Rp ++ Rb ++ Rc))
    (hrun : step .static P₁ (run .static P₁ (n' + 1)) π σ₁
      (.app (.lam ℓ own (.letP p₁ (.pvar ℓ) b₁)) w₁) = some L₁) :
    ∃ L₂, step .static P₂ (run .static P₂ (n' + 1)) π' σ₂ (.letP p₂ w₂ b₂) = some L₂ ∧
      List.Forall₂ (Out C π π' ν μ D (Rh ++ Rw ++ Rp ++ Rb) Rc) L₁ L₂ := by
  have hmemp : ∀ x, x ∈ freeParams p₁ ∨ x ∈ freeParams b₁ →
      x ∈ freeParams (.app (.lam ℓ own (.letP p₁ (.pvar ℓ) b₁)) w₁ : Tm S X₁) := by
    intro x hx
    have hxne : x ≠ ℓ := by
      rintro rfl
      rcases hx with hx | hx
      · exact hℓp hx
      · exact hℓb hx
    exact (mem_freeParams_letAct (S := S) (ℓ := ℓ) (own := own) (p := p₁) (b := b₁)
      (w := w₁)).2 (Or.inl ⟨hx, hxne⟩)
  have hfpp : freeParams p₁ = [] := List.eq_nil_iff_forall_not_mem.2 fun x hx => by
    have := hmemp x (Or.inl hx); rw [hfp] at this; cases this
  have hfpb : freeParams b₁ = [] := List.eq_nil_iff_forall_not_mem.2 fun x hx => by
    have := hmemp x (Or.inr hx); rw [hfp] at this; cases this
  have hfpw : freeParams w₁ = [] := List.eq_nil_iff_forall_not_mem.2 fun x hx => by
    have := (mem_freeParams_letAct (S := S) (ℓ := ℓ) (own := own) (p := p₁) (b := b₁)
      (w := w₁)).2 (Or.inr hx)
    rw [hfp] at this; cases this
  have hfvw : ∀ m ∈ freeNames w₁, m ∈ D := fun m h => hfv m (mem_freeNames_letAct.2 (Or.inr h))
  have hfvo : ∀ n, (n ∈ freeNames p₁ ∨ n ∈ freeNames b₁) → ownKey own n = false → n ∈ D :=
    fun n h ho => hfv n (mem_freeNames_letAct.2 (Or.inl ⟨h, ho⟩))
  have hperm : (Rh ++ Rw ++ Rp ++ Rb ++ Rc).Perm (Rw ++ (Rh ++ (Rp ++ Rb ++ Rc))) := by
    simp only [List.append_assoc]
    exact List.perm_append_comm_assoc Rh Rw (Rp ++ (Rb ++ Rc))
  have hciw := hci.perm hperm
  have hFw := hF.perm hperm
  simp only [step] at hrun
  rw [show run .static P₁ (n' + 1) (π ++ [0]) σ₁ (.lam ℓ own (.letP p₁ (.pvar ℓ) b₁)) =
      some [(.lam ℓ own (.letP p₁ (.pvar ℓ) b₁), σ₁)] from rfl, bindOpt_some_singleton] at hrun
  simp only [activate, subst_letP_param] at hrun
  obtain ⟨Lw₁, hLw₁, hbw⟩ := bindOpt_eq_some hrun
  have hoffs : ∀ n ∈ D, Avoid (π ++ [2]) n := fun n hn => (hF.old₁ n hn).avoid_child 2
  have hres : ∀ m, m ∈ Rw ++ (Rh ++ Rb) → m ∈ Rh ++ Rw ++ Rp ++ Rb := by
    intro m hm
    simp only [List.mem_append] at hm ⊢
    tauto
  cases hl₂ : letLam? p₂ w₂ with
  | none =>
      rw [step_letP_none hl₂]
      obtain ⟨Lw₂, hLw₂, hwr⟩ := ih hw hfpw hfvw hciw (hFw.child 1 0) hLw₁
      rw [hLw₂]
      refine bindAll_sim_mem ?_ hwr hbw
      rintro ⟨v₁, τ₁⟩ hmem ⟨v₂, τ₂⟩ M₁ ⟨ν₁, D₁, hfv₁, hE₁, hrel₁, hfp₁, hci₁⟩ hM₁
      simp only at hfv₁ hrel₁ hfp₁ hci₁ hM₁ ⊢
      have hAv : ∀ n ∈ D₁, Avoid (π ++ [2]) n := hE₁.avoid₁ (by decide : (1 : ℕ) ≠ 2) hoffs
      obtain ⟨D₂, hsub₂, hfvp', hfvb', hp₂, hb₂, hv₂, hci₂, hold₂, hclass₂⟩ :=
        letAct_open (ℓ := ℓ) hνi hp hb hlive hinj hfpp hfpb hfvo hE₁.sub hE₁.agree hrel₁ hfv₁ hci₁ hAv
      have hE₂ : Ext π π' Rh ν₁ D₁ (openMap (π ++ [2]) own νi ν₁) D₂ := by
        refine ⟨hold₂, hsub₂, ?_⟩
        intro n hn hnD
        rcases hclass₂ n hn with h | ⟨s, rfl, hr⟩
        · exact absurd h hnD
        · exact ⟨newAt_inst 2 s, Or.inr hr⟩
      have hFresh : ∀ (l : Path), Fresh (π ++ [2] ++ l) (π' ++ [1]) (openMap (π ++ [2]) own νi ν₁)
          D₂ (Rp ++ Rb ++ Rc) := by
        intro l
        refine ⟨?_, ?_, ?_⟩
        · intro n hn
          rcases hclass₂ n hn with h | ⟨s, rfl, _⟩
          · exact (hAv n h).oldAt_append l
          · exact oldAt_inst_append _ l s
        · intro n hn
          rcases hclass₂ n hn with h | ⟨s, rfl, hr⟩
          · rw [hold₂ n h]
            by_cases hD : n ∈ D
            · rw [hE₁.agree n hD]; exact (hF.old₂ n hD).child 1
            · rcases (hE₁.new n h hD).2 with h' | h'
              · exact (h'.avoid_sibling (by decide)).oldAt
              · exact (hF.oldRes _ (by
                  simp only [List.mem_append, h']
                  exact Or.inl (Or.inl (Or.inl (Or.inr trivial))))).child 1
          · exact (hF.oldRes _ (by
              simp only [List.mem_append, hr]
              exact Or.inl (Or.inl (Or.inl (Or.inl trivial))))).child 1
        · intro m hm
          exact (hF.oldRes m (by
            simp only [List.mem_append] at hm ⊢
            tauto)).child 1
      have hinert := run_results_inert P₁ .static _ _ _ _ _ hLw₁ _ hmem
      obtain ⟨M₂, hM₂, hrelM⟩ := sim_letAct_cont hQ hC hA ih' hp₂ hb₂ hv₂ hci₂ hFresh hfvp' hfvb'
        (fun m h => hsub₂ (hfv₁ m h)) hfp₁
        (freeParams_open (fun x hx => by rw [hfpb] at hx; cases hx) hfp₁) hinert hM₁
      exact ⟨M₂, hM₂, hrelM.imp fun _ _ h => ((h.after hE₂).after hE₁.parent).res_mono hres⟩
  | some f₂ =>
      rw [step_letP_some hl₂]
      obtain ⟨rfl, x₂, own₂, bb₂, rfl⟩ := letLam?_some hl₂
      obtain ⟨L₂, hL₂, hrel⟩ := sim_letAct_inPlace ih' hνi hw hp hb hlive hinj hfpp hfpb hfpw hfvw
        hfvo hciw hFw hLw₁ hbw
      exact ⟨L₂, hL₂, hrel.imp fun _ _ h => h.res_mono hres⟩

end Cases

/-! ## The simulation -/

/-- **First side to second side.**  Under the static discipline, with bi-unique
code and related programs, a defined run of the first side from a related
configuration is matched, at the same fuel, by a defined run of the second
side, with the bags related pointwise and in order. -/
theorem sim {P₁ : S → Option (Tm S X₁)} {P₂ : S → Option (Tm S X₂)} [CodeId X₁] [CodeId X₂] (hQ : C.BiUnique) (hC : C.CodeAgree) (hA : C.PatAgree)
    (hP : ProgRel C P₁ P₂) : ∀ n, SimAt C P₁ P₂ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro π π' σ₁ σ₂ t₁ t₂ ν μ Res Rc _ D L₁ hR hfp hfv hci hF hrun
    cases n with
    | zero => cases hrun
    | succ n =>
      change step .static P₁ (run .static P₁ n) π σ₁ t₁ = some L₁ at hrun
      show ∃ L₂, step .static P₂ (run .static P₂ n) π' σ₂ t₂ = some L₂ ∧ _
      have ihn : SimAt C P₁ P₂ n := ih n (Nat.lt_succ_self n)
      cases hR with
      | sym s =>
          change some [(.sym s, σ₁)] = some L₁ at hrun
          injection hrun with hrun
          subst hrun
          exact ⟨_, rfl, .cons (Out.value (.sym s) hfv hfp (by simpa using hci)) .nil⟩
      | fn F => exact sim_fn hP ihn hci hF hrun
      | var m hv =>
          change some [(.var m, σ₁)] = some L₁ at hrun
          injection hrun with hrun
          subst hrun
          exact ⟨_, rfl, .cons (Out.value (.var m hv) hfv hfp (by simpa using hci)) .nil⟩
      | pvar x _ => simp [freeParams] at hfp
      | quote hq =>
          change some [(.quote _, σ₁)] = some L₁ at hrun
          injection hrun with hrun
          subst hrun
          exact ⟨_, rfl, .cons (Out.value (.quote hq) hfv hfp (by simpa using hci)) .nil⟩
      | ctx ho hks hc =>
          change some [(.ctx _ _, σ₁)] = some L₁ at hrun
          injection hrun with hrun
          subst hrun
          exact ⟨_, rfl, .cons (Out.value (.ctx ho hks hc) hfv hfp (by simpa using hci)) .nil⟩
      | pquote h hp hok =>
          change some [(.pquote _, σ₁)] = some L₁ at hrun
          injection hrun with hrun
          subst hrun
          exact ⟨_, rfl, .cons (Out.value (.pquote h hp hok) hfv hfp (by simpa using hci)) .nil⟩
      | app hf ha => exact sim_app ihn hf ha hfp hfv hci hF hrun
      | letP _ hp hw hb => exact sim_letP hQ hC hA ihn hp hw hb hfp hfv hci hF hrun
      | alt _ h₁ h₂ => exact sim_alt ihn h₁ h₂ hfp hfv hci hF hrun
      | lam hνb hμb hμx hr₁ hr₂ hb hown hres hinj hdisj hnd hpar hbare hseen =>
          change some [(.lam _ _ _, σ₁)] = some L₁ at hrun
          injection hrun with hrun
          subst hrun
          exact ⟨_, rfl, .cons (Out.value
            (.lam hνb hμb hμx hr₁ hr₂ hb hown hres hinj hdisj hnd hpar hbare hseen)
            hfv hfp (by simpa using hci)) .nil⟩
      | letAct _ hνi _ hℓp hℓb hw hp hb hlive hinj =>
          cases n with
          | zero => simp [step, run, bindOpt] at hrun
          | succ n' =>
              exact sim_letAct hQ hC hA ihn (ih n' (by omega)) hνi hℓp hℓb hw hp hb hlive hinj hfp hfv
                hci hF hrun
      | newAct hνi _ hℓ hb hlive hinj => exact sim_newAct ihn hνi hℓ hb hlive hinj hfp hfv hci hF hrun

/-! ## The converse direction: definedness -/

section Converse

variable {Y : Type v} [DecidableEq Y]

/-- What an application does with one value of its function part. -/
def appCont (rec : Runner S Y) (π : Path) (a : Tm S Y) (r₁ : Tm S Y × GStore S Y) :
    Option (Result S Y) :=
  bindOpt (rec (π ++ [1]) r₁.2 a) fun r₂ =>
    match r₁.1 with
    | .lam x own body => rec (π ++ [2]) r₂.2 (activate .static r₂.2 (π ++ [2]) x own body r₂.1)
    | fv => some [(.app fv r₂.1, r₂.2)]

theorem step_app [CodeId Y] {P : S → Option (Tm S Y)} {rec : Runner S Y} {π : Path} {σ : GStore S Y}
    {f a : Tm S Y} :
    step .static P rec π σ (.app f a) = bindOpt (rec (π ++ [0]) σ f) (appCont rec π a) := rfl

theorem appCont_mono [CodeId Y] {P : S → Option (Tm S Y)} {n n' : ℕ} (h : n ≤ n') {π : Path} {a : Tm S Y}
    {r : Tm S Y × GStore S Y} {M : Result S Y} (hM : appCont (run .static P n) π a r = some M) :
    appCont (run .static P n') π a r = some M := by
  unfold appCont at hM ⊢
  exact bindOpt_mono (fun l hl => run_mono .static P h hl)
    (fun r₂ M' hM' => by
      obtain ⟨u, τ⟩ := r
      cases u with
      | lam x own body => exact run_mono .static P h hM'
      | _ => exact hM') hM

omit [DecidableEq S] [DecidableEq Y] in
/-- Pairing a bag with a defined bag on the other side. -/
theorem forall₂_bindAll_each {α₁ α₂ β : Type*} {R : α₁ → α₂ → Prop} {g : α₂ → Option (List β)} :
    ∀ {l₁ : List α₁} {l₂ : List α₂} {L : List β}, List.Forall₂ R l₁ l₂ → bindAll l₂ g = some L →
      ∀ a₁ ∈ l₁, ∃ a₂, R a₁ a₂ ∧ ∃ M, g a₂ = some M
  | [], [], _, .nil, _, a, ha => by cases ha
  | b₁ :: l₁, b₂ :: l₂, L, .cons hr hrs, h, a, ha => by
      unfold bindAll at h
      cases h1 : g b₂ with
      | none => rw [h1] at h; cases h
      | some M =>
          cases h2 : bindAll l₂ g with
          | none => rw [h1, h2] at h; cases h
          | some N =>
              rcases List.mem_cons.1 ha with rfl | ha
              · exact ⟨b₂, hr, M, h1⟩
              · exact forall₂_bindAll_each hrs h2 a ha

end Converse

/-- **The converse at fuel `m`**: a defined run of the second side from a related
configuration has a defined counterpart on the first side, at some fuel. -/
def SimIAt [CodeId X₁] [CodeId X₂] (C : Setting S X₁ X₂) (P₁ : S → Option (Tm S X₁))
    (P₂ : S → Option (Tm S X₂)) (m : ℕ) : Prop :=
  ∀ {π π' : Path} {σ₁ : GStore S X₁} {σ₂ : GStore S X₂} {t₁ : Tm S X₁} {t₂ : Tm S X₂}
    {ν μ : Nm X₁ → Nm X₂} {Res Rc : List (Nm X₂)} {ok : Bool} {D : Set (Nm X₁)} {L₂ : Result S X₂},
    Rel C ν μ .code Res ok t₁ t₂ → freeParams t₁ = [] → (∀ x ∈ freeNames t₁, x ∈ D) →
    CI C ν D (Res ++ Rc) σ₁ σ₂ → Fresh π π' ν D (Res ++ Rc) →
    run .static P₂ m π' σ₂ t₂ = some L₂ → ∃ n L₁, run .static P₁ n π σ₁ t₁ = some L₁

end IdSlot

end Mettapedia.GSLT.LanguageDef.TemplateScope
