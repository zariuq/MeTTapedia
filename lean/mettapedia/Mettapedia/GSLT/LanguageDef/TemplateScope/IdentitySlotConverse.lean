import Mettapedia.GSLT.LanguageDef.TemplateScope.IdentitySlotRun

/-!
# Template scope: related runs, the converse direction

`simI` — if the second side's run from a related configuration is defined,
the first side's run is defined at some fuel.  Together with `sim`, the two
runs are defined together, with related bags (`sim_iff`).

The first side may need more fuel (its `let`s and `new` blocks are
activations), and a `new` block runs on the second side at the same fuel as
its body; the induction is on the second side's fuel, then on the size of the
first side's term (`tmSize`, which renaming does not change).
-/

namespace Mettapedia.GSLT.LanguageDef.TemplateScope

open Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline

universe u v

namespace IdSlot

variable {S : Type u} {X₁ X₂ : Type v} [DecidableEq S] [DecidableEq X₁] [DecidableEq X₂]
variable {C : Setting S X₁ X₂}

/-! ## A size that renaming keeps -/

/-- The number of constructors of a term, names not counted. -/
def tmSize {Y : Type v} : Tm S Y → ℕ
  | .lam _ _ b => tmSize b + 1
  | .app f a => tmSize f + tmSize a + 1
  | .quote _ => 1
  | .pquote c => tmSize c + 1
  | .letP p w b => tmSize p + tmSize w + tmSize b + 1
  | .alt t₁ t₂ => tmSize t₁ + tmSize t₂ + 1
  | _ => 1

omit [DecidableEq S] in
/-- **Renaming store names keeps the size**, when no free parameter is
instantiated. -/
theorem tmSize_subst_rename {Y : Type v} [DecidableEq Y] :
    ∀ (t : Tm S Y) (θ φ : Sub S Y), (∀ n w, θ n = some w → ∃ m, w = .var m) →
      (∀ x ∈ freeParams t, φ x = none) → tmSize (subst θ φ t) = tmSize t
  | .sym _, _, _, _, _ => rfl
  | .fn _, _, _, _, _ => rfl
  | .var n, θ, _, hθ, _ => by
      cases h : θ n with
      | none => simp [subst, h]
      | some w =>
          obtain ⟨m, rfl⟩ := hθ n w h
          simp [subst, h, tmSize]
  | .pvar x, _, φ, _, hφ => by
      simp [subst, hφ x (by simp [freeParams])]
  | .lam x own b, θ, φ, hθ, hφ => by
      simp only [subst, tmSize]
      rw [tmSize_subst_rename b _ _ (fun n w h => by
        unfold Sub.hideOwn at h
        split at h
        · cases h
        · exact hθ n w h)]
      intro y hy
      unfold Sub.hideParam
      by_cases hyx : y = x
      · simp [hyx]
      · simp only [hyx, if_false]
        exact hφ y (mem_freeParams_lam.2 ⟨hy, hyx⟩)
  | .app f a, θ, φ, hθ, hφ => by
      simp only [freeParams, List.mem_append] at hφ
      simp only [subst, tmSize]
      rw [tmSize_subst_rename f θ φ hθ (fun x h => hφ x (Or.inl h)),
        tmSize_subst_rename a θ φ hθ (fun x h => hφ x (Or.inr h))]
  | .quote _, _, _, _, _ => rfl
  | .ctx _ _, _, _, _, _ => rfl
  | .pquote c, θ, φ, hθ, hφ => by
      simp only [freeParams] at hφ
      simp only [subst, tmSize]
      rw [tmSize_subst_rename c θ φ hθ hφ]
  | .letP p w b, θ, φ, hθ, hφ => by
      simp only [freeParams, List.mem_append] at hφ
      simp only [subst, tmSize]
      rw [tmSize_subst_rename p θ φ hθ (fun x h => hφ x (Or.inl (Or.inl h))),
        tmSize_subst_rename w θ φ hθ (fun x h => hφ x (Or.inl (Or.inr h))),
        tmSize_subst_rename b θ φ hθ (fun x h => hφ x (Or.inr h))]
  | .alt t₁ t₂, θ, φ, hθ, hφ => by
      simp only [freeParams, List.mem_append] at hφ
      simp only [subst, tmSize]
      rw [tmSize_subst_rename t₁ θ φ hθ (fun x h => hφ x (Or.inl h)),
        tmSize_subst_rename t₂ θ φ hθ (fun x h => hφ x (Or.inr h))]

omit [DecidableEq S] in
/-- Opening a `new` block keeps its body's size. -/
theorem tmSize_open {own : List X₁} {ρ : Path} {ℓ : Nm X₁} {v b : Tm S X₁}
    (hb : freeParams b = []) :
    tmSize (subst (renameOwn ρ own) (Sub.single ℓ v) b) = tmSize b :=
  tmSize_subst_rename b _ _ (fun n w h => by
    simp only [renameOwn] at h
    split at h
    · injection h with h
      exact ⟨_, h.symm⟩
    · cases h) (fun x hx => by rw [hb] at hx; cases hx)

/-! ## A chain of `new` blocks around a lambda is defined -/

/-- **A chain of `new` blocks around a lambda** evaluates on the first side, at
some fuel. -/
theorem newChain_def [CodeId X₁] {P₁ : S → Option (Tm S X₁)} : ∀ (k : ℕ) {ρ : Path} {σ₁ : GStore S X₁}
    {ν μ : Nm X₁ → Nm X₂} {kd : Kd} {Res : List (Nm X₂)} {w₁ : Tm S X₁} {x₂ : Nm X₂}
    {own₂ : List X₂} {b₂ : Tm S X₂} {ok : Bool}, tmSize w₁ ≤ k →
    Rel C ν μ kd Res ok w₁ (.lam x₂ own₂ b₂) → freeParams w₁ = [] →
    (∀ n ∈ freeNames w₁, OldAt ρ n) →
    ∃ n L, run .static P₁ n ρ σ₁ w₁ = some L
  | k, ρ, σ₁, ν, μ, kd, Res, w₁, x₂, own₂, b₂, _, hk, hR, hfp, hold => by
      cases hR with
      | lam => exact ⟨1, _, rfl⟩
      | @newAct _ _ ℓ own b₁ _ νi Rh Rb _ hνi hr hℓ hb hlive hinj =>
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
          have hsz : tmSize (subst (renameOwn (ρ ++ [2]) own) (Sub.single ℓ (.lam ℓ [] (.pvar ℓ))) b₁)
              < k := by
            rw [tmSize_open hfpb]
            simp only [tmSize] at hk
            omega
          have hfp' : freeParams (subst (renameOwn (ρ ++ [2]) own)
              (Sub.single ℓ (.lam ℓ [] (.pvar ℓ))) b₁) = [] :=
            freeParams_open (fun x hx => by rw [hfpb] at hx; cases hx) (by simp [freeParams])
          obtain ⟨n, L, hL⟩ := newChain_def (tmSize (subst (renameOwn (ρ ++ [2]) own)
              (Sub.single ℓ (.lam ℓ [] (.pvar ℓ))) b₁)) (σ₁ := σ₁) le_rfl hopen hfp' (by
            intro m hm
            rcases mem_freeNames_open hm with ⟨h1, h2⟩ | ⟨m₀, hm₀, ho, rfl⟩ | ⟨h1, _⟩
            · exact (hold m (mem_freeNames_newAct.2 ⟨h1, h2⟩)).child 2
            · cases m₀ with
              | src s => exact oldAt_inst_self _ s
              | inst _ _ => simp [ownKey] at ho
            · rw [hfpb] at h1; cases h1)
          cases n with
          | zero => cases hL
          | succ n =>
              refine ⟨n + 2, L, ?_⟩
              change step .static P₁ (run .static P₁ (n + 1)) ρ σ₁ _ = some L
              rw [step_app, show run .static P₁ (n + 1) (ρ ++ [0]) σ₁ (.lam ℓ own b₁) =
                  some [(.lam ℓ own b₁, σ₁)] from rfl, bindOpt_some_singleton]
              unfold appCont
              rw [show run .static P₁ (n + 1) (ρ ++ [1]) σ₁ (.lam ℓ [] (.pvar ℓ)) =
                  some [(.lam ℓ [] (.pvar ℓ), σ₁)] from rfl, bindOpt_some_singleton]
              exact hL
  termination_by k => k
  decreasing_by omega

/-! ## The cases of the converse -/

section Cases

variable {P₁ : S → Option (Tm S X₁)} {P₂ : S → Option (Tm S X₂)}

/-- **A value substituted in place for a store name, converse.** -/
theorem simI_chain [CodeId X₁] [CodeId X₂] {m' : ℕ} (ihm : SimIAt C P₁ P₂ m') {ρ ρ' : Path}
    {σ₁ : GStore S X₁} {σ₂ : GStore S X₂} {f₁ : Nm X₁} {f₂ : Nm X₂} {v₁ b₁ : Tm S X₁}
    {v₂ b₂ : Tm S X₂} {ν μ : Nm X₁ → Nm X₂} {Rb Rc : List (Nm X₂)} {ob : Bool}
    {D : Set (Nm X₁)} {L₂ : Result S X₂}
    (hb : Rel C ν μ .code Rb ob b₁ b₂) (hv : Rel C ν μ .val [] true v₁ v₂) (hf₂ : ν f₁ = f₂)
    (hci : CI C ν D (Rb ++ Rc) σ₁ σ₂) (hF : Fresh ρ ρ' ν D (Rb ++ Rc))
    (hf : f₁ ∈ D) (hfvb : ∀ m ∈ freeNames b₁, m ∈ D) (hfvv : ∀ m ∈ freeNames v₁, m ∈ D)
    (hfpv : freeParams v₁ = []) (hfpb : freeParams b₁ = [])
    (hrun : run .static P₂ m' ρ' σ₂ (subst (Sub.single f₂ v₂) Sub.none b₂) = some L₂) :
    ∃ n L₁, run .static P₁ n ρ σ₁ (subst (Sub.single f₁ v₁) Sub.none b₁) = some L₁ := by
  have hsub := subst_var hb hv (fun m hm => hci.ok₁ m (hfvv m hm)) hfpv
    (ok₂_of_val hci hv hfvv) (freeParams_val hv hfpv)
    (fun m hm he => hci.inj (hfvb m hm) hf he)
    (fun h => hci.disj f₁ hf (by simp [h]))
  rw [hf₂] at hsub
  exact ihm hsub (freeParams_subst_single hfpv hfpb) (freeNames_subst_single hfvv hfvb)
    (by simpa using hci) hF hrun

/-- **The `let` continuation, converse**: a defined continuation on the second
side has a defined counterpart on the first side. -/
theorem simI_letCont [CodeId X₁] [CodeId X₂] (hQ : C.BiUnique) (hC : C.CodeAgree) (hA : C.PatAgree) {m' : ℕ} (ihm : SimIAt C P₁ P₂ m') {ρ₁ ρ₂ : Path}
    {τ₁ : GStore S X₁} {τ₂ : GStore S X₂} {v₁ : Tm S X₁} {v₂ : Tm S X₂} {p₁ b₁ : Tm S X₁}
    {p₂ b₂ : Tm S X₂} {ν₁ μ : Nm X₁ → Nm X₂} {Rp Rb Rc : List (Nm X₂)} {D₁ : Set (Nm X₁)}
    {M₂ : Result S X₂}
    (hv : Rel C ν₁ μ .val [] true v₁ v₂) (hfvv : ∀ m ∈ freeNames v₁, m ∈ D₁) (hfpv : freeParams v₁ = [])
    {op ob : Bool} (hp : Rel C ν₁ μ .pat Rp op p₁ p₂) (hb : Rel C ν₁ μ .code Rb ob b₁ b₂)
    (hfvp : ∀ m ∈ freeNames p₁, m ∈ D₁) (hfvb : ∀ m ∈ freeNames b₁, m ∈ D₁)
    (hfpb : freeParams b₁ = [])
    (hci : CI C ν₁ D₁ (Rp ++ Rb ++ Rc) τ₁ τ₂) (hF : Fresh (ρ₁ ++ [1]) (ρ₂ ++ [1]) ν₁ D₁ (Rp ++ Rb ++ Rc))
    (hrun : letCont (run .static P₂ m') ρ₂ p₂ b₂ (v₂, τ₂) = some M₂) :
    ∃ n M₁, letCont (run .static P₁ n) ρ₁ p₁ b₁ (v₁, τ₁) = some M₁ := by
  have hci' : CI C ν₁ D₁ (Rp ++ (Rb ++ Rc)) τ₁ τ₂ := by rw [← List.append_assoc]; exact hci
  have hF' : Fresh (ρ₁ ++ [1]) (ρ₂ ++ [1]) ν₁ D₁ (Rp ++ (Rb ++ Rc)) := by
    rw [← List.append_assoc]; exact hF
  have hact := hv.applyStore hfvv hci.store (fun m hm => by cases hm)
  have hg := hact.toGVal?
  unfold letCont at hrun ⊢
  simp only at hrun ⊢
  rcases OptRel.cases hg with ⟨e1, e2⟩ | ⟨g₁, g₂, e1, e2, hgg⟩
  · rw [e2] at hrun
    rw [e1]
    simp only at hrun ⊢
    cases p₁ with
    | var f₁ =>
        obtain rfl := hp.var_left
        simp only at hrun ⊢
        exact simI_chain ihm hb hv rfl hci'.drop hF'.drop (hfvp f₁ (by simp [freeNames])) hfvb hfvv
          hfpv hfpb hrun
    | sym _ | fn _ | pvar _ | lam _ _ _ | app _ _ | quote _ | pquote _ | ctx _ _ | letP _ _ _ | alt _ _ =>
        exact ⟨0, [], rfl⟩
  · rw [e2] at hrun
    rw [e1]
    simp only at hrun ⊢
    have hm := hp.matchT hQ hC hA hfvp hci.inj hgg hci.store
    rcases OptRel.cases hm with ⟨e3, e4⟩ | ⟨s₁, s₂, e3, e4, hss⟩
    · rw [e3]
      exact ⟨0, [], rfl⟩
    · rw [e4] at hrun
      rw [e3]
      simp only at hrun ⊢
      exact ihm hb hfpb hfvb (hci'.with_store hss).drop hF'.drop hrun

/-- What an application does after its argument, with the function value
`r₁`. -/
def actCont {Y : Type v} [DecidableEq Y] (rec : Runner S Y) (π : Path)
    (r₁ r₂ : Tm S Y × GStore S Y) : Option (Result S Y) :=
  match r₁.1 with
  | .lam x own body => rec (π ++ [2]) r₂.2 (activate .static r₂.2 (π ++ [2]) x own body r₂.1)
  | fv => some [(.app fv r₂.1, r₂.2)]

omit [DecidableEq S] in
theorem appCont_eq {Y : Type v} [DecidableEq Y] (rec : Runner S Y) (π : Path) (a : Tm S Y)
    (r₁ : Tm S Y × GStore S Y) :
    appCont rec π a r₁ = bindOpt (rec (π ++ [1]) r₁.2 a) (actCont rec π r₁) := rfl

theorem actCont_mono {Y : Type v} [DecidableEq Y] [CodeId Y] {P : S → Option (Tm S Y)} {n n' : ℕ}
    (h : n ≤ n') {π : Path} {r₁ r₂ : Tm S Y × GStore S Y} {M : Result S Y}
    (hM : actCont (run .static P n) π r₁ r₂ = some M) : actCont (run .static P n') π r₁ r₂ = some M := by
  obtain ⟨u, τ⟩ := r₁
  unfold actCont at hM ⊢
  cases u with
  | lam x own body => exact run_mono .static P h hM
  | _ => exact hM

/-- **The application, converse.** -/
theorem simI_app [CodeId X₁] [CodeId X₂] (hQ : C.BiUnique) (hC : C.CodeAgree) (hA : C.PatAgree) (hP : ProgRel C P₁ P₂) {m' : ℕ} (ihm : SimIAt C P₁ P₂ m')
    {π π' : Path} {σ₁ : GStore S X₁} {σ₂ : GStore S X₂} {f₁ a₁ : Tm S X₁} {f₂ a₂ : Tm S X₂}
    {ν μ : Nm X₁ → Nm X₂} {Rf Ra Rc : List (Nm X₂)} {okf oka : Bool} {D : Set (Nm X₁)}
    {L₂ : Result S X₂}
    (hf : Rel C ν μ .code Rf okf f₁ f₂) (ha : Rel C ν μ .code Ra oka a₁ a₂)
    (hfp : freeParams (.app f₁ a₁ : Tm S X₁) = [])
    (hfv : ∀ m ∈ freeNames (.app f₁ a₁ : Tm S X₁), m ∈ D)
    (hci : CI C ν D (Rf ++ Ra ++ Rc) σ₁ σ₂) (hF : Fresh π π' ν D (Rf ++ Ra ++ Rc))
    (hrun : step .static P₂ (run .static P₂ m') π' σ₂ (.app f₂ a₂) = some L₂) :
    ∃ n L₁, run .static P₁ n π σ₁ (.app f₁ a₁) = some L₁ := by
  simp only [freeParams, List.append_eq_nil_iff] at hfp
  obtain ⟨hfpf, hfpa⟩ := hfp
  have hfvf : ∀ m ∈ freeNames f₁, m ∈ D := fun m h => hfv m (by simp [freeNames, h])
  have hfva : ∀ m ∈ freeNames a₁, m ∈ D := fun m h => hfv m (by simp [freeNames, h])
  rw [step_app] at hrun
  obtain ⟨Lf₂, hLf₂, hb₂⟩ := bindOpt_eq_some hrun
  have hcif : CI C ν D (Rf ++ (Ra ++ Rc)) σ₁ σ₂ := by rw [← List.append_assoc]; exact hci
  have hFf : Fresh π π' ν D (Rf ++ (Ra ++ Rc)) := by rw [← List.append_assoc]; exact hF
  obtain ⟨nf, Lf₁, hLf₁⟩ := ihm hf hfpf hfvf hcif (hFf.child 0 0) hLf₂
  obtain ⟨Lf₂', hLf₂', hfr⟩ := sim hQ hC hA hP nf hf hfpf hfvf hcif (hFf.child 0 0) hLf₁
  obtain rfl := run_det hLf₂' hLf₂
  have hA₁ : ∀ n ∈ D, Avoid (π ++ [2]) n := fun n hn => (hF.old₁ n hn).avoid_child 2
  have hA₂ : ∀ n ∈ D, Avoid (π' ++ [2]) (ν n) := fun n hn => (hF.old₂ n hn).avoid_child 2
  have hAR : ∀ m ∈ Rf ++ Ra ++ Rc, Avoid (π' ++ [2]) m :=
    fun m hm => (hF.oldRes m hm).avoid_child 2
  have key : ∀ r₁ ∈ Lf₁, ∃ N M, appCont (run .static P₁ N) π a₁ r₁ = some M := by
    intro r₁ hr₁
    obtain ⟨r₁', hout, M₂, hM₂⟩ := forall₂_bindAll_each hfr hb₂ r₁ hr₁
    obtain ⟨u₁, τ₁⟩ := r₁
    obtain ⟨u₁', τ₁'⟩ := r₁'
    obtain ⟨ν₁, D₁, hfv₁, hE₁, hrel₁, hfp₁, hci₁⟩ := hout
    simp only at hfv₁ hrel₁ hfp₁ hci₁
    rw [appCont_eq] at hM₂
    obtain ⟨La₂, hLa₂, hbb₂⟩ := bindOpt_eq_some hM₂
    have hra : Rel C ν₁ μ .code Ra oka a₁ a₂ :=
      ha.congr (fun m hm => (hE₁.agree m (hfva m hm)).symm) (fun _ _ => rfl)
    have hFa : Fresh (π ++ [1]) (π' ++ [1]) ν₁ D₁ (Ra ++ Rc) :=
      hE₁.fresh_sibling (by decide) (by decide) hFf
    obtain ⟨na, La₁, hLa₁⟩ := ihm hra hfpa (fun m hm => hE₁.sub (hfva m hm)) hci₁ hFa hLa₂
    obtain ⟨La₂', hLa₂', harel⟩ :=
      sim hQ hC hA hP na hra hfpa (fun m hm => hE₁.sub (hfva m hm)) hci₁ hFa hLa₁
    obtain rfl := run_det hLa₂' hLa₂
    have hA₁' := hE₁.avoid₁ (by decide : (0 : ℕ) ≠ 2) hA₁
    have hA₂' := hE₁.avoid₂ (by decide : (0 : ℕ) ≠ 2) hA₂ (fun m hm => hAR m (by simp [hm]))
    have key2 : ∀ r₂ ∈ La₁, ∃ N M, actCont (run .static P₁ N) π (u₁, τ₁) r₂ = some M := by
      intro r₂ hr₂
      obtain ⟨r₂', hout₂, N₂, hN₂⟩ := forall₂_bindAll_each harel hbb₂ r₂ hr₂
      obtain ⟨u₂, τ₂⟩ := r₂
      obtain ⟨u₂', τ₂'⟩ := r₂'
      obtain ⟨ν₂, D₂, hfv₂, hE₂, hrel₂, hfp₂, hci₂⟩ := hout₂
      simp only at hfv₂ hrel₂ hfp₂ hci₂ hN₂
      have hA₁'' := hE₂.avoid₁ (by decide : (1 : ℕ) ≠ 2) hA₁'
      have hA₂'' := hE₂.avoid₂ (by decide : (1 : ℕ) ≠ 2) hA₂' (fun m hm => hAR m (by simp [hm]))
      have hARc : ∀ m ∈ Rc, Avoid (π' ++ [2]) m := fun m hm => hAR m (by simp [hm])
      have hrelf : Rel C ν₂ μ .val [] true u₁ u₁' :=
        hrel₁.congr (fun m hm => (hE₂.agree m (hfv₁ m hm)).symm) (fun _ _ => rfl)
      have hfvu₁ : ∀ m ∈ freeNames u₁, m ∈ D₂ := fun m hm => hE₂.sub (hfv₁ m hm)
      generalize hR0 : ([] : List (Nm X₂)) = R0 at hrelf
      generalize hokv : true = okv at hrelf
      cases hrelf with
      | @lam _ _ _ x₁ own₁ b₁ x₂ own₂ b₂ νb μb Rb _ hνb hμb hμx hr₁ hr₂ hb hown hres hinj hdisj
          hnd hpar _ _ =>
          unfold actCont at hN₂ ⊢
          simp only [activate] at hN₂ ⊢
          have hcl : ∀ x ∈ freeParams b₁, x = x₁ := by
            intro x hx
            by_contra hne
            have := (mem_freeParams_lam (own := own₁)).2 ⟨hx, hne⟩
            rw [hfp₁] at this
            cases this
          have hca₁ : ∀ m ∈ freeNames u₂, OK₁ C m := fun m hm => hci₂.ok₁ m (hfv₂ m hm)
          have hact := activate_lam hνb hμx hb hown hres hcl hrel₂ hca₁ hfp₂
            (ok₂_of_val hci₂ hrel₂ hfv₂) (freeParams_val hrel₂ hfp₂) (ρ := π ++ [2])
            (ρ' := π' ++ [2])
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
          have hold₃ : ∀ n ∈ D₂, openMap (π ++ [2]) own₁ (fun m => Nm.inst (π' ++ [2]) (νb m)) ν₂ n =
              ν₂ n := fun n hn => openMap_other (hA₁'' n hn).ne_inst
          have hF₃ : Fresh (π ++ [2]) (π' ++ [2])
              (openMap (π ++ [2]) own₁ (fun m => Nm.inst (π' ++ [2]) (νb m)) ν₂)
              (D₂ ∪ {n | n ∈ freeNames (subst (renameOwn (π ++ [2]) own₁) (Sub.single x₁ u₂) b₁)})
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
                · rw [openMap_own ho]
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
          have hfpb : freeParams (subst (renameOwn (π ++ [2]) own₁) (Sub.single x₁ u₂) b₁) = [] :=
            freeParams_open hcl hfp₂
          exact ihm hact hfpb (fun m hm => Or.inr hm) hci₃ hF₃ hN₂
      | sym _ => exact ⟨0, _, rfl⟩
      | fn _ => exact ⟨0, _, rfl⟩
      | var _ _ => exact ⟨0, _, rfl⟩
      | pvar _ _ => exact ⟨0, _, rfl⟩
      | quote _ => exact ⟨0, _, rfl⟩
      | pquote _ _ _ => exact ⟨0, _, rfl⟩
      | app _ _ => exact ⟨0, _, rfl⟩
      | ctx _ _ _ => exact ⟨0, _, rfl⟩
      | letP hk => exact absurd rfl hk
      | alt hk => exact absurd rfl hk
      | letAct hk => exact absurd rfl hk
    obtain ⟨N, M, hM⟩ := exists_fuel_bindAll
      (g := fun N r₂ => actCont (run .static P₁ N) π (u₁, τ₁) r₂)
      (fun n n' r M h hr => actCont_mono h hr) La₁ key2
    refine ⟨max N na, M, ?_⟩
    rw [appCont_eq, run_mono .static P₁ (le_max_right N na) hLa₁]
    exact bindAll_mono (fun r M h => actCont_mono (le_max_left N na) h) _ _ hM
  obtain ⟨N, M, hM⟩ := exists_fuel_bindAll (g := fun N r₁ => appCont (run .static P₁ N) π a₁ r₁)
    (fun n n' r M h hr => appCont_mono h hr) Lf₁ key
  refine ⟨max N nf + 1, M, ?_⟩
  change step .static P₁ (run .static P₁ (max N nf)) π σ₁ (.app f₁ a₁) = some M
  rw [step_app, run_mono .static P₁ (le_max_right N nf) hLf₁]
  exact bindAll_mono (fun r M h => appCont_mono (le_max_left N nf) h) _ _ hM

/-- **Alternatives, converse.** -/
theorem simI_alt [CodeId X₁] [CodeId X₂] {m' : ℕ} (ihm : SimIAt C P₁ P₂ m') {π π' : Path} {σ₁ : GStore S X₁}
    {σ₂ : GStore S X₂} {t₁ u₁ : Tm S X₁} {t₂ u₂ : Tm S X₂} {ν μ : Nm X₁ → Nm X₂}
    {R₁ R₂ Rc : List (Nm X₂)} {D : Set (Nm X₁)} {L₂ : Result S X₂}
    {o₁ o₂ : Bool} (h₁ : Rel C ν μ .code R₁ o₁ t₁ t₂) (h₂ : Rel C ν μ .code R₂ o₂ u₁ u₂)
    (hfp : freeParams (.alt t₁ u₁ : Tm S X₁) = [])
    (hfv : ∀ m ∈ freeNames (.alt t₁ u₁ : Tm S X₁), m ∈ D)
    (hci : CI C ν D (R₁ ++ R₂ ++ Rc) σ₁ σ₂) (hF : Fresh π π' ν D (R₁ ++ R₂ ++ Rc))
    (hrun : step .static P₂ (run .static P₂ m') π' σ₂ (.alt t₂ u₂) = some L₂) :
    ∃ n L₁, run .static P₁ n π σ₁ (.alt t₁ u₁) = some L₁ := by
  simp only [freeParams, List.append_eq_nil_iff] at hfp
  simp only [step] at hrun
  cases e1 : run .static P₂ m' (π' ++ [0]) σ₂ t₂ with
  | none => rw [e1] at hrun; cases hrun
  | some l =>
      cases e2 : run .static P₂ m' (π' ++ [1]) σ₂ u₂ with
      | none => rw [e1, e2] at hrun; cases hrun
      | some r =>
          have hci₁ : CI C ν D (R₁ ++ (R₂ ++ Rc)) σ₁ σ₂ := by rw [← List.append_assoc]; exact hci
          have hF₁ : Fresh π π' ν D (R₁ ++ (R₂ ++ Rc)) := by rw [← List.append_assoc]; exact hF
          obtain ⟨n₁, l₁, hl₁⟩ := ihm h₁ hfp.1 (fun m h => hfv m (by simp [freeNames, h])) hci₁
            (hF₁.child 0 0) e1
          obtain ⟨n₂, r₁, hr₁⟩ := ihm h₂ hfp.2 (fun m h => hfv m (by simp [freeNames, h])) hci₁.drop
            (hF₁.drop.child 1 1) e2
          refine ⟨max n₁ n₂ + 1, l₁ ++ r₁, ?_⟩
          change step .static P₁ (run .static P₁ (max n₁ n₂)) π σ₁ (.alt t₁ u₁) = some _
          simp only [step]
          rw [run_mono .static P₁ (le_max_left _ _) hl₁, run_mono .static P₁ (le_max_right _ _) hr₁]

/-- **An equation call, converse.** -/
theorem simI_fn [CodeId X₁] [CodeId X₂] (hP : ProgRel C P₁ P₂) {m' : ℕ} (ihm : SimIAt C P₁ P₂ m') {π π' : Path}
    {σ₁ : GStore S X₁} {σ₂ : GStore S X₂} {F : S} {ν : Nm X₁ → Nm X₂} {Rc : List (Nm X₂)}
    {D : Set (Nm X₁)} {L₂ : Result S X₂}
    (hci : CI C ν D ([] ++ Rc) σ₁ σ₂) (hF : Fresh π π' ν D ([] ++ Rc))
    (hrun : step .static P₂ (run .static P₂ m') π' σ₂ (.fn F) = some L₂) :
    ∃ n L₁, run .static P₁ n π σ₁ (.fn F) = some L₁ := by
  simp only [step] at hrun
  rcases OptRel.cases (hP F) with ⟨e1, e2⟩ | ⟨e₁, e₂, e1, e2, hfv0, hfp0, hrel0⟩
  · refine ⟨1, [(.fn F, σ₁)], ?_⟩
    change step .static P₁ (run .static P₁ 0) π σ₁ (.fn F) = _
    simp only [step, e1]
  · rw [e2] at hrun
    obtain ⟨n, L₁, h⟩ := ihm (hrel0 ν ν) hfp0 (by simp [hfv0]) hci (hF.child 0 0) hrun
    refine ⟨n + 1, L₁, ?_⟩
    change step .static P₁ (run .static P₁ n) π σ₁ (.fn F) = some L₁
    simp only [step, e1]
    exact h

/-- The converse at fuel `m` for first-side terms smaller than `k`. -/
def SimIAtSize [CodeId X₁] [CodeId X₂] (C : Setting S X₁ X₂) (P₁ : S → Option (Tm S X₁))
    (P₂ : S → Option (Tm S X₂))
    (m k : ℕ) : Prop :=
  ∀ {π π' : Path} {σ₁ : GStore S X₁} {σ₂ : GStore S X₂} {t₁ : Tm S X₁} {t₂ : Tm S X₂}
    {ν μ : Nm X₁ → Nm X₂} {Res Rc : List (Nm X₂)} {D : Set (Nm X₁)} {L₂ : Result S X₂},
    {ok : Bool} → tmSize t₁ < k → Rel C ν μ .code Res ok t₁ t₂ → freeParams t₁ = [] →
    (∀ x ∈ freeNames t₁, x ∈ D) → CI C ν D (Res ++ Rc) σ₁ σ₂ → Fresh π π' ν D (Res ++ Rc) →
    run .static P₂ m π' σ₂ t₂ = some L₂ → ∃ n L₁, run .static P₁ n π σ₁ t₁ = some L₁

/-- **A `new` block, converse**: the second side runs the body at the same fuel;
the first side's opened body is smaller than the block. -/
theorem simI_newAct [CodeId X₁] [CodeId X₂] {m k : ℕ} {ℓ : Nm X₁} {own : List X₁} {b₁ : Tm S X₁}
    (ihk : SimIAtSize C P₁ P₂ m k)
    (hk : tmSize (.app (.lam ℓ own b₁) (.lam ℓ [] (.pvar ℓ)) : Tm S X₁) ≤ k)
    {π π' : Path} {σ₁ : GStore S X₁} {σ₂ : GStore S X₂} {b₂ : Tm S X₂}
    {ν μ νi : Nm X₁ → Nm X₂} {Rh Rb Rc : List (Nm X₂)} {D : Set (Nm X₁)} {L₂ : Result S X₂}
    (hνi : ∀ n, ownKey own n = false → νi n = ν n) (hℓ : ℓ ∉ freeParams b₁)
    {ob : Bool} (hb : Rel C νi μ .code Rb ob b₁ b₂)
    (hlive : ∀ n ∈ freeNames b₁, ownKey own n = true → νi n ∈ Rh)
    (hinj : ∀ n ∈ freeNames b₁, ∀ n' ∈ freeNames b₁,
      ownKey own n = true → ownKey own n' = true → νi n = νi n' → n = n')
    (hfp : freeParams (.app (.lam ℓ own b₁) (.lam ℓ [] (.pvar ℓ)) : Tm S X₁) = [])
    (hfv : ∀ m ∈ freeNames (.app (.lam ℓ own b₁) (.lam ℓ [] (.pvar ℓ)) : Tm S X₁), m ∈ D)
    (hci : CI C ν D (Rh ++ Rb ++ Rc) σ₁ σ₂) (hF : Fresh π π' ν D (Rh ++ Rb ++ Rc))
    (hrun : run .static P₂ m π' σ₂ b₂ = some L₂) :
    ∃ n L₁, run .static P₁ n π σ₁ (.app (.lam ℓ own b₁) (.lam ℓ [] (.pvar ℓ))) = some L₁ := by
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
  have hold₃ : ∀ n ∈ D, openMap (π ++ [2]) own νi ν n = ν n :=
    fun n hn => openMap_other (hA n hn).ne_inst
  have hF₃ : Fresh (π ++ [2]) π' (openMap (π ++ [2]) own νi ν)
      (D ∪ {n | n ∈ freeNames (subst (renameOwn (π ++ [2]) own)
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
        · rw [openMap_own ho]
          exact hF.oldRes _ (by simp [hlive m₀ hm₀ ho])
    · intro m hm
      exact hF.oldRes m (by simp at hm ⊢; tauto)
  have hfpb' : freeParams (subst (renameOwn (π ++ [2]) own)
      (Sub.single ℓ (.lam ℓ [] (.pvar ℓ))) b₁) = [] :=
    freeParams_open (fun x hx => by rw [hfpb] at hx; cases hx) (by simp [freeParams])
  have hsz : tmSize (subst (renameOwn (π ++ [2]) own) (Sub.single ℓ (.lam ℓ [] (.pvar ℓ))) b₁) < k := by
    rw [tmSize_open hfpb]
    simp only [tmSize] at hk
    omega
  obtain ⟨n, L₁, h⟩ := ihk hsz hopen hfpb' (fun m hm => Or.inr hm) hci₃ hF₃ hrun
  cases n with
  | zero => cases h
  | succ n =>
      refine ⟨n + 2, L₁, ?_⟩
      change step .static P₁ (run .static P₁ (n + 1)) π σ₁ _ = some L₁
      rw [step_app, show run .static P₁ (n + 1) (π ++ [0]) σ₁ (.lam ℓ own b₁) =
          some [(.lam ℓ own b₁, σ₁)] from rfl, bindOpt_some_singleton, appCont_eq,
        show run .static P₁ (n + 1) (π ++ [1]) σ₁ (.lam ℓ [] (.pvar ℓ)) =
          some [(.lam ℓ [] (.pvar ℓ), σ₁)] from rfl, bindOpt_some_singleton]
      exact h

/-- **A plain `let`, converse.** -/
theorem simI_letP [CodeId X₁] [CodeId X₂] (hQ : C.BiUnique) (hC : C.CodeAgree) (hA : C.PatAgree) (hP : ProgRel C P₁ P₂) {m' : ℕ} (ihm : SimIAt C P₁ P₂ m')
    {π π' : Path} {σ₁ : GStore S X₁} {σ₂ : GStore S X₂} {p₁ w₁ b₁ : Tm S X₁}
    {p₂ w₂ b₂ : Tm S X₂} {ν μ : Nm X₁ → Nm X₂} {Rp Rw Rb Rc : List (Nm X₂)}
    {op ow ob : Bool} {D : Set (Nm X₁)} {L₂ : Result S X₂}
    (hp : Rel C ν μ .pat Rp op p₁ p₂) (hw : Rel C ν μ .code Rw ow w₁ w₂)
    (hb : Rel C ν μ .code Rb ob b₁ b₂)
    (hfp : freeParams (.letP p₁ w₁ b₁ : Tm S X₁) = [])
    (hfv : ∀ m ∈ freeNames (.letP p₁ w₁ b₁ : Tm S X₁), m ∈ D)
    (hci : CI C ν D (Rp ++ Rw ++ Rb ++ Rc) σ₁ σ₂) (hF : Fresh π π' ν D (Rp ++ Rw ++ Rb ++ Rc))
    (hrun : step .static P₂ (run .static P₂ m') π' σ₂ (.letP p₂ w₂ b₂) = some L₂) :
    ∃ n L₁, run .static P₁ n π σ₁ (.letP p₁ w₁ b₁) = some L₁ := by
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
      obtain ⟨rfl, x, own, bb, rfl⟩ := letLam?_some hl₁
      obtain rfl := hp.var_left
      obtain ⟨x', own', bb', rfl⟩ := hw.left_lam_code
      rw [step_letP_some (rfl : letLam? (.var (ν f₁)) (.lam x' own' bb') = some (ν f₁))] at hrun
      have hRp : Rp = [] := by cases hp; rfl
      have hRw : Rw = [] := by cases hw; rfl
      subst hRp hRw
      obtain ⟨-, hwv⟩ := hw.toVal (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨x, own, bb, rfl⟩)))))
      obtain ⟨n, L₁, h⟩ := simI_chain ihm hb hwv rfl (by simpa using hci) (by simpa using hF)
        (hfvp f₁ (by simp [freeNames])) hfvb hfvw hfpw hfpb hrun
      refine ⟨n + 1, L₁, ?_⟩
      change step .static P₁ (run .static P₁ n) π σ₁ _ = some L₁
      rw [step_letP_some hl₁]
      exact h
  | none =>
      cases hl₂ : letLam? p₂ w₂ with
      | some f₂ =>
          rw [step_letP_some hl₂] at hrun
          obtain ⟨rfl, x₂, own₂, bb₂, rfl⟩ := letLam?_some hl₂
          obtain ⟨f₁, rfl⟩ := hp.right_var_pat
          have hf2 : ν f₁ = f₂ := by have := hp.var_left; injection this with e; exact e.symm
          subst hf2
          have hRp : Rp = [] := by cases hp; rfl
          subst hRp
          have hciw : CI C ν D (Rw ++ (Rb ++ Rc)) σ₁ σ₂ := by simpa [List.append_assoc] using hci
          have hFw : Fresh π π' ν D (Rw ++ (Rb ++ Rc)) := by simpa [List.append_assoc] using hF
          have hnd : Rw.Nodup := (List.nodup_append.1 hciw.nodup).1
          have hold₀ : ∀ m ∈ freeNames w₁, OldAt (π ++ [0]) m :=
            fun m hm => (hF.old₁ m (hfvw m hm)).child 0
          obtain ⟨n₀, Lw₁, hLw₁⟩ := newChain_def (P₁ := P₁) (σ₁ := σ₁) (tmSize w₁) le_rfl hw hfpw
            hold₀
          obtain ⟨v₁, ν', hL, hrelv, hfpv, hagree, hfvv, hinjv⟩ := newChain n₀ hw hfpw hnd hold₀ hLw₁
          subst hL
          obtain ⟨hci', -, hold, hclass⟩ := newChain_cfg hciw hFw hfvw hagree hfvv hinjv
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
          have hf₁ : f₁ ∈ D := hfvp f₁ (by simp [freeNames])
          have hb' : Rel C ν' μ .code Rb ob b₁ b₂ :=
            hb.congr (fun m hm => (hold m (hfvb m hm)).symm) (fun _ _ => rfl)
          obtain ⟨n₁, L₁, h⟩ := simI_chain ihm hb' hrelv (hold f₁ hf₁) hci' hF' (Or.inl hf₁)
            (fun m hm => Or.inl (hfvb m hm)) (fun m hm => Or.inr hm) hfpv hfpb hrun
          obtain ⟨x₁, own₁, bb₁, rfl⟩ := hrelv.right_lam_val
          refine ⟨max n₀ n₁ + 1, L₁, ?_⟩
          change step .static P₁ (run .static P₁ (max n₀ n₁)) π σ₁ _ = some L₁
          rw [step_letP_none hl₁, run_mono .static P₁ (le_max_left _ _) hLw₁, bindOpt_some_singleton]
          unfold letCont
          simp only [act_lam, Tm.toGVal?]
          exact run_mono .static P₁ (le_max_right _ _) h
      | none =>
          rw [step_letP_none hl₂] at hrun
          obtain ⟨Lw₂, hLw₂, hbw⟩ := bindOpt_eq_some hrun
          obtain ⟨nw, Lw₁, hLw₁⟩ :=
            ihm hw hfpw hfvw (hci.perm hperm) ((hF.perm hperm).child 0 0) hLw₂
          obtain ⟨Lw₂', hLw₂', hwr⟩ :=
            sim hQ hC hA hP nw hw hfpw hfvw (hci.perm hperm) ((hF.perm hperm).child 0 0) hLw₁
          obtain rfl := run_det hLw₂' hLw₂
          have key : ∀ r₁ ∈ Lw₁, ∃ N M, letCont (run .static P₁ N) π p₁ b₁ r₁ = some M := by
            intro r₁ hr₁
            obtain ⟨r₂, hout, M₂, hM₂⟩ := forall₂_bindAll_each hwr hbw r₁ hr₁
            obtain ⟨v₁, τ₁⟩ := r₁
            obtain ⟨v₂, τ₂⟩ := r₂
            obtain ⟨ν₁, D₁, hfv₁, hE₁, hrel₁, hfp₁, hci₁⟩ := hout
            simp only at hfv₁ hrel₁ hfp₁ hci₁
            have hp₁ : Rel C ν₁ μ .pat Rp op p₁ p₂ :=
              hp.congr (fun m hm => (hE₁.agree m (hfvp m hm)).symm) (fun _ _ => rfl)
            have hb₁ : Rel C ν₁ μ .code Rb ob b₁ b₂ :=
              hb.congr (fun m hm => (hE₁.agree m (hfvb m hm)).symm) (fun _ _ => rfl)
            have hFb : Fresh (π ++ [1]) (π' ++ [1]) ν₁ D₁ (Rp ++ Rb ++ Rc) :=
              hE₁.fresh_sibling (by decide) (by decide) (hF.perm hperm)
            exact simI_letCont hQ hC hA ihm hrel₁ hfv₁ hfp₁ hp₁ hb₁ (fun m hm => hE₁.sub (hfvp m hm))
              (fun m hm => hE₁.sub (hfvb m hm)) hfpb hci₁ hFb hM₂
          obtain ⟨N, M, hM⟩ := exists_fuel_bindAll
            (g := fun N r₁ => letCont (run .static P₁ N) π p₁ b₁ r₁)
            (fun n n' r M h hr => letCont_mono h hr) Lw₁ key
          refine ⟨max N nw + 1, M, ?_⟩
          change step .static P₁ (run .static P₁ (max N nw)) π σ₁ _ = some M
          rw [step_letP_none hl₁, run_mono .static P₁ (le_max_right N nw) hLw₁]
          exact bindAll_mono (fun r M h => letCont_mono (le_max_left N nw) h) _ _ hM

/-- The first side's `let`-activation, unfolded: the right-hand side at
`π ++ [1]`, then the `let` opened at `π ++ [2]` with each of its values. -/
theorem run_letAct [CodeId X₁] (P : S → Option (Tm S X₁)) (N : ℕ) (π : Path) (σ : GStore S X₁) (ℓ : Nm X₁)
    (own : List X₁) (p w b : Tm S X₁) :
    run .static P (N + 2) π σ (.app (.lam ℓ own (.letP p (.pvar ℓ) b)) w) =
      bindOpt (run .static P (N + 1) (π ++ [1]) σ w) (fun r => run .static P (N + 1) (π ++ [2]) r.2
        (.letP (subst (renameOwn (π ++ [2]) own) (Sub.single ℓ r.1) p) r.1
          (subst (renameOwn (π ++ [2]) own) (Sub.single ℓ r.1) b))) := by
  change step .static P (run .static P (N + 1)) π σ _ = _
  rw [step_app, show run .static P (N + 1) (π ++ [0]) σ (.lam ℓ own (.letP p (.pvar ℓ) b)) =
      some [(.lam ℓ own (.letP p (.pvar ℓ) b), σ)] from rfl, bindOpt_some_singleton, appCont_eq]
  congr 1
  funext r
  simp only [actCont, activate, subst_letP_param]

/-- **A `let`-activation, converse**, against a plain `let` on the second side. -/
theorem simI_letAct [CodeId X₁] [CodeId X₂] (hQ : C.BiUnique) (hC : C.CodeAgree) (hA : C.PatAgree) (hP : ProgRel C P₁ P₂) {m' : ℕ} (ihm : SimIAt C P₁ P₂ m')
    {π π' : Path} {σ₁ : GStore S X₁} {σ₂ : GStore S X₂}
    {ℓ : Nm X₁} {own : List X₁} {p₁ w₁ b₁ : Tm S X₁} {p₂ w₂ b₂ : Tm S X₂}
    {ν μ νi : Nm X₁ → Nm X₂} {Rh Rw Rp Rb Rc : List (Nm X₂)} {D : Set (Nm X₁)}
    {L₂ : Result S X₂}
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
    (hrun : step .static P₂ (run .static P₂ m') π' σ₂ (.letP p₂ w₂ b₂) = some L₂) :
    ∃ n L₁, run .static P₁ n π σ₁ (.app (.lam ℓ own (.letP p₁ (.pvar ℓ) b₁)) w₁) = some L₁ := by
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
  have hoffs : ∀ n ∈ D, Avoid (π ++ [2]) n := fun n hn => (hF.old₁ n hn).avoid_child 2
  cases hl₂ : letLam? p₂ w₂ with
  | some f₂ =>
      rw [step_letP_some hl₂] at hrun
      obtain ⟨rfl, x₂, own₂, bb₂, rfl⟩ := letLam?_some hl₂
      obtain ⟨f₁, rfl⟩ := hp.right_var_pat
      have hRp : Rp = [] := by cases hp; rfl
      subst hRp
      have hf₂ : f₂ = νi f₁ := by
        have := hp.var_left
        injection this
      subst hf₂
      have hndw : Rw.Nodup := (List.nodup_append.1 hciw.nodup).1
      have hold₀ : ∀ m ∈ freeNames w₁, OldAt (π ++ [1]) m :=
        fun m hm => (hFw.old₁ m (hfvw m hm)).child 1
      obtain ⟨nw, Lw₁, hLw₁⟩ := newChain_def (P₁ := P₁) (σ₁ := σ₁) (tmSize w₁) le_rfl hw hfpw hold₀
      obtain ⟨v₁, ν', hL, hrelv, hfpv, hagree, hfvv, hinjv⟩ := newChain nw hw hfpw hndw hold₀ hLw₁
      subst hL
      obtain ⟨hci₁, -, hold₁, hclass₁⟩ := newChain_cfg hciw hFw hfvw hagree hfvv hinjv
      have hAv : ∀ n ∈ D ∪ {n | n ∈ freeNames v₁}, Avoid (π ++ [2]) n := by
        intro n hn
        rcases hclass₁ n hn with h | ⟨hn1, _⟩
        · exact hoffs n h
        · exact hn1.avoid_sibling (by decide)
      obtain ⟨D₂, hsub₂, hfvp', hfvb', hp₂, hb₂, hv₂, hci₂, hold₂, hclass₂⟩ :=
        letAct_open (ℓ := ℓ) hνi hp hb hlive hinj hfpp hfpb hfvo Set.subset_union_left hold₁ hrelv
          (fun m hm => Or.inr hm) hci₁ hAv
      obtain ⟨x₁, own₁, bb₁, rfl⟩ := hrelv.right_lam_val
      rw [subst_rename_var] at hp₂ hfvp'
      have hpv := hp₂.var_left
      injection hpv with hpv
      have hRw' : ∀ m ∈ Rw, m ∈ Rw ++ (Rh ++ ([] ++ Rb ++ Rc)) :=
        fun m h => List.mem_append_left _ h
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
            · exact hFw.oldRes _ (hRw' _ hr')
          · exact hFw.oldRes _ (hRh _ hr)
        · intro m hm
          exact hFw.oldRes m (hRbc m hm)
      have hci₂' : CI C (openMap (π ++ [2]) own νi ν') D₂ (Rb ++ Rc) σ₁ σ₂ := by
        rw [List.nil_append] at hci₂
        exact hci₂
      obtain ⟨N₁, L₁, h⟩ := simI_chain ihm hb₂ hv₂ hpv.symm hci₂' hF₂
        (hfvp' _ (by simp [freeNames])) hfvb' (fun m h => hsub₂ (Or.inr h)) hfpv
        (freeParams_open (fun x hx => by rw [hfpb] at hx; cases hx) hfpv) hrun
      refine ⟨max nw N₁ + 2, L₁, ?_⟩
      rw [run_letAct, run_mono .static P₁ (by omega : nw ≤ max nw N₁ + 1) hLw₁,
        bindOpt_some_singleton]
      simp only [subst_rename_var]
      change step .static P₁ (run .static P₁ (max nw N₁)) (π ++ [2]) σ₁ (.letP (.var _) _ _) = some L₁
      rw [step_letP_some rfl]
      exact run_mono .static P₁ (le_max_right _ _) h
  | none =>
      rw [step_letP_none hl₂] at hrun
      obtain ⟨Lw₂, hLw₂, hbw⟩ := bindOpt_eq_some hrun
      obtain ⟨nw, Lw₁, hLw₁⟩ := ihm hw hfpw hfvw hciw (hFw.child 1 0) hLw₂
      obtain ⟨Lw₂', hLw₂', hwr⟩ := sim hQ hC hA hP nw hw hfpw hfvw hciw (hFw.child 1 0) hLw₁
      obtain rfl := run_det hLw₂' hLw₂
      have key : ∀ r ∈ Lw₁, ∃ N M, run .static P₁ N (π ++ [2]) r.2
          (.letP (subst (renameOwn (π ++ [2]) own) (Sub.single ℓ r.1) p₁) r.1
            (subst (renameOwn (π ++ [2]) own) (Sub.single ℓ r.1) b₁)) = some M := by
        intro r hmem
        obtain ⟨r₂, hout, M₂, hM₂⟩ := forall₂_bindAll_each hwr hbw r hmem
        obtain ⟨v₁, τ₁⟩ := r
        obtain ⟨v₂, τ₂⟩ := r₂
        obtain ⟨ν₁, D₁, hfv₁, hE₁, hrel₁, hfp₁, hci₁⟩ := hout
        simp only at hfv₁ hrel₁ hfp₁ hci₁ hM₂ ⊢
        have hAv : ∀ n ∈ D₁, Avoid (π ++ [2]) n := hE₁.avoid₁ (by decide : (1 : ℕ) ≠ 2) hoffs
        obtain ⟨D₂, hsub₂, hfvp', hfvb', hp₂, hb₂, hv₂, hci₂, hold₂, hclass₂⟩ :=
          letAct_open (ℓ := ℓ) hνi hp hb hlive hinj hfpp hfpb hfvo hE₁.sub hE₁.agree hrel₁ hfv₁
            hci₁ hAv
        have hFresh : ∀ (l : Path), Fresh (π ++ [2] ++ l) (π' ++ [1])
            (openMap (π ++ [2]) own νi ν₁) D₂ (Rp ++ Rb ++ Rc) := by
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
        have hfpb' := freeParams_open (fun x hx => by rw [hfpb] at hx; cases hx) hfp₁
          (ρ := π ++ [2]) (own := own) (ℓ := ℓ) (b := b₁)
        cases hl₃ : letLam? (subst (renameOwn (π ++ [2]) own) (Sub.single ℓ v₁) p₁) v₁ with
        | some f =>
            obtain ⟨hpf, x, own', bb, rfl⟩ := letLam?_some hl₃
            rw [hpf] at hp₂ hfvp'
            have hRp : Rp = [] := by cases hp₂; rfl
            subst hRp
            obtain rfl := hp₂.var_left
            obtain ⟨x₂, own₂, bb₂, rfl⟩ := hv₂.left_lam_code
            unfold letCont at hM₂
            simp only [act_lam, Tm.toGVal?] at hM₂
            obtain ⟨N, M, h⟩ := simI_chain ihm hb₂ hv₂ rfl (by simpa using hci₂)
              (by simpa using hFresh []) (hfvp' f (by simp [freeNames])) hfvb'
              (fun m h => hsub₂ (hfv₁ m h)) hfp₁ hfpb' hM₂
            refine ⟨N + 1, M, ?_⟩
            change step .static P₁ (run .static P₁ N) (π ++ [2]) τ₁ _ = some M
            rw [step_letP_some hl₃]
            exact h
        | none =>
            obtain ⟨n₀, hn₀⟩ := run_inert_def P₁ .static v₁ hinert
            obtain ⟨N, M, h⟩ := simI_letCont hQ hC hA ihm hv₂ (fun m h => hsub₂ (hfv₁ m h)) hfp₁ hp₂ hb₂
              hfvp' hfvb' hfpb' hci₂ (hFresh [1]) hM₂
            refine ⟨max n₀ N + 1, M, ?_⟩
            change step .static P₁ (run .static P₁ (max n₀ N)) (π ++ [2]) τ₁ _ = some M
            rw [step_letP_none hl₃, hn₀ _ (le_max_left _ _), bindOpt_some_singleton]
            exact letCont_mono (le_max_right _ _) h
      obtain ⟨N, M, hM⟩ := exists_fuel_bindAll
        (g := fun N r => run .static P₁ N (π ++ [2]) r.2
          (.letP (subst (renameOwn (π ++ [2]) own) (Sub.single ℓ r.1) p₁) r.1
            (subst (renameOwn (π ++ [2]) own) (Sub.single ℓ r.1) b₁)))
        (fun n n' r M h hr => run_mono .static P₁ h hr) Lw₁ key
      refine ⟨max N nw + 2, M, ?_⟩
      rw [run_letAct, run_mono .static P₁ (by omega : nw ≤ max N nw + 1) hLw₁]
      exact bindAll_mono (fun r M h => run_mono .static P₁ (by omega : N ≤ max N nw + 1) h) _ _ hM

end Cases

/-! ## The converse, and both directions together -/

/-- **Second side to first side.**  Under the static discipline, with bi-unique
code and related programs, a defined run of the second side from a related
configuration has a defined counterpart on the first side. -/
theorem simI {P₁ : S → Option (Tm S X₁)} {P₂ : S → Option (Tm S X₂)} [CodeId X₁] [CodeId X₂] (hQ : C.BiUnique) (hC : C.CodeAgree) (hA : C.PatAgree)
    (hP : ProgRel C P₁ P₂) : ∀ m, SimIAt C P₁ P₂ m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ihm =>
    have hsize : ∀ k, SimIAtSize C P₁ P₂ m k := by
      intro k
      induction k with
      | zero =>
          intro _ _ _ _ _ _ _ _ _ _ _ _ _ hk
          exact absurd hk (Nat.not_lt_zero _)
      | succ k ihk =>
          intro π π' σ₁ σ₂ t₁ t₂ ν μ Res Rc D L₂ _ hk hR hfp hfv hci hF hrun
          cases hR with
          | sym s => exact ⟨1, _, rfl⟩
          | var n _ => exact ⟨1, _, rfl⟩
          | quote hq => exact ⟨1, _, rfl⟩
          | ctx _ _ _ => exact ⟨1, _, rfl⟩
          | pquote _ _ _ => exact ⟨1, _, rfl⟩
          | lam => exact ⟨1, _, rfl⟩
          | pvar x _ => simp [freeParams] at hfp
          | fn F =>
              cases m with
              | zero => cases hrun
              | succ m' =>
                  change step .static P₂ (run .static P₂ m') π' σ₂ _ = some L₂ at hrun
                  exact simI_fn hP (ihm m' (Nat.lt_succ_self _)) hci hF hrun
          | app hf ha =>
              cases m with
              | zero => cases hrun
              | succ m' =>
                  change step .static P₂ (run .static P₂ m') π' σ₂ _ = some L₂ at hrun
                  exact simI_app hQ hC hA hP (ihm m' (Nat.lt_succ_self _)) hf ha hfp hfv hci hF hrun
          | letP _ hp hw hb =>
              cases m with
              | zero => cases hrun
              | succ m' =>
                  change step .static P₂ (run .static P₂ m') π' σ₂ _ = some L₂ at hrun
                  exact simI_letP hQ hC hA hP (ihm m' (Nat.lt_succ_self _)) hp hw hb hfp hfv hci hF hrun
          | alt _ h₁ h₂ =>
              cases m with
              | zero => cases hrun
              | succ m' =>
                  change step .static P₂ (run .static P₂ m') π' σ₂ _ = some L₂ at hrun
                  exact simI_alt (ihm m' (Nat.lt_succ_self _)) h₁ h₂ hfp hfv hci hF hrun
          | letAct _ hνi _ hℓp hℓb hw hp hb hlive hinj =>
              cases m with
              | zero => cases hrun
              | succ m' =>
                  change step .static P₂ (run .static P₂ m') π' σ₂ _ = some L₂ at hrun
                  exact simI_letAct hQ hC hA hP (ihm m' (Nat.lt_succ_self _)) hνi hℓp hℓb hw hp hb hlive
                    hinj hfp hfv hci hF hrun
          | newAct hνi _ hℓ hb hlive hinj =>
              exact simI_newAct ihk (by omega) hνi hℓ hb hlive hinj hfp hfv hci hF hrun
    intro π π' σ₁ σ₂ t₁ t₂ ν μ Res Rc _ D L₂ hR hfp hfv hci hF hrun
    exact hsize (tmSize t₁ + 1) (Nat.lt_succ_self _) hR hfp hfv hci hF hrun

section Both

variable {P₁ : S → Option (Tm S X₁)} {P₂ : S → Option (Tm S X₂)}

/-- **The two runs are defined together.** -/
theorem defined_iff [CodeId X₁] [CodeId X₂] (hQ : C.BiUnique) (hC : C.CodeAgree) (hA : C.PatAgree) (hP : ProgRel C P₁ P₂) {π π' : Path} {σ₁ : GStore S X₁}
    {σ₂ : GStore S X₂} {t₁ : Tm S X₁} {t₂ : Tm S X₂} {ν μ : Nm X₁ → Nm X₂}
    {Res Rc : List (Nm X₂)} {ok : Bool} {D : Set (Nm X₁)} (hR : Rel C ν μ .code Res ok t₁ t₂)
    (hfp : freeParams t₁ = []) (hfv : ∀ x ∈ freeNames t₁, x ∈ D) (hci : CI C ν D (Res ++ Rc) σ₁ σ₂)
    (hF : Fresh π π' ν D (Res ++ Rc)) :
    (∃ n L₁, run .static P₁ n π σ₁ t₁ = some L₁) ↔ ∃ m L₂, run .static P₂ m π' σ₂ t₂ = some L₂ :=
  ⟨fun ⟨n, _, h⟩ => let ⟨L₂, h₂, _⟩ := sim hQ hC hA hP n hR hfp hfv hci hF h; ⟨n, L₂, h₂⟩,
    fun ⟨m, _, h⟩ => simI hQ hC hA hP m hR hfp hfv hci hF h⟩

/-- **Defined runs have related bags**, whatever fuel each side was given:
pointwise and in order, each pair of results related by its own extension of
the name map. -/
theorem bags_rel [CodeId X₁] [CodeId X₂] (hQ : C.BiUnique) (hC : C.CodeAgree) (hA : C.PatAgree) (hP : ProgRel C P₁ P₂) {π π' : Path} {σ₁ : GStore S X₁}
    {σ₂ : GStore S X₂} {t₁ : Tm S X₁} {t₂ : Tm S X₂} {ν μ : Nm X₁ → Nm X₂}
    {Res Rc : List (Nm X₂)} {D : Set (Nm X₁)} {n m : ℕ} {L₁ : Result S X₁} {L₂ : Result S X₂}
    {ok : Bool} (hR : Rel C ν μ .code Res ok t₁ t₂)
    (hfp : freeParams t₁ = []) (hfv : ∀ x ∈ freeNames t₁, x ∈ D) (hci : CI C ν D (Res ++ Rc) σ₁ σ₂)
    (hF : Fresh π π' ν D (Res ++ Rc)) (h₁ : run .static P₁ n π σ₁ t₁ = some L₁)
    (h₂ : run .static P₂ m π' σ₂ t₂ = some L₂) :
    List.Forall₂ (Out C π π' ν μ D Res Rc) L₁ L₂ := by
  obtain ⟨L₂', h₂', hrel⟩ := sim hQ hC hA hP n hR hfp hfv hci hF h₁
  rw [run_det h₂' h₂] at hrel
  exact hrel

end Both

end IdSlot

end Mettapedia.GSLT.LanguageDef.TemplateScope
