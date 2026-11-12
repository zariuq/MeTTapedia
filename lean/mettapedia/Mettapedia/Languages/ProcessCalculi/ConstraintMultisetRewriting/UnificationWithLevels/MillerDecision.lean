import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.MillerSolver

/-!
# Miller patterns are decided: a principal answer or no solution

**Termination** (`MStep.rank_lt`, `steps_terminate`). The rank of a store is the number of unknowns that occur, then
its size. Inversion removes an unknown (`invert_card_lt`). Pruning and intersection replace an unknown by one new
unknown of smaller arity, so the number of unknowns does not grow (`restrict_card_le`), and every application of the
restricted unknown shrinks (`size_act_restrict`). Deletion and decomposition shrink the store.

**The fragment** (`Patterns`): in every side of every equation, each unknown is applied to distinct locals. The rules
keep it: an inverted body is renamed injectively on the locals of an application (`Pattern.act_update`), and a
restriction applies the new unknown to a sublist of distinct locals.

**Progress** (`progress`): on a nonempty store of the fragment some transition or refutation applies. In
`X x̄ ≐ t`: `X` in `t` is an intersection (`t = X ȳ`) or an occurs refutation; a rigid local of `t` outside `x̄` is a
scope refutation; an argument of an unknown of `t` outside `x̄` is a pruning; and otherwise every local of `t` is in
`x̄` and `X` is inverted.

**Decision** (`decided`, `principal_or_unsolvable`): every store of the fragment has a run, through restricted
contexts, to the empty store or to a refutation; so it has a principal answer, in the sense of `Frames.Principal`, or
no solution. The condition of distinct locals cannot be dropped: the non-pattern store `X x x ≐ x` is solvable
without a principal answer (`MillerControls`). It is not the sharp boundary of principality: some stores with
repeated arguments have principal answers (`X x x ≐ gnd` has only `X := gnd`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

open Interface

namespace MillerCodes

/-! ## Measures -/

def storeUnknowns {Δ : Ctx} : EquationStore (Term Δ) → Finset Nat
  | [] => ∅
  | e :: S => Tm.unknowns e.1.1 ∪ Tm.unknowns e.2.1 ∪ storeUnknowns S

def storeSize {Δ : Ctx} : EquationStore (Term Δ) → Nat
  | [] => 0
  | e :: S => Tm.size e.1.1 + Tm.size e.2.1 + storeSize S

/-- The rank of a store: the number of unknowns that occur, then the size. -/
def rank {Δ : Ctx} (S : EquationStore (Term Δ)) : Nat × Nat := ((storeUnknowns S).card, storeSize S)

theorem mem_storeUnknowns {Δ : Ctx} {e : Equation (Term Δ)} {S : EquationStore (Term Δ)} {x : Nat} :
    x ∈ storeUnknowns (e :: S) ↔ x ∈ Tm.unknowns e.1.1 ∨ x ∈ Tm.unknowns e.2.1 ∨ x ∈ storeUnknowns S := by
  simp only [storeUnknowns, Finset.mem_union, or_assoc]

theorem unknowns_rename (ρ : Nat → Nat) : ∀ t : Tm, Tm.unknowns (Tm.rename ρ t) = Tm.unknowns t
  | .loc _ => rfl
  | .gnd => rfl
  | .arr A B => by simp only [Tm.rename, Tm.unknowns, unknowns_rename ρ A, unknowns_rename ρ B]
  | .app _ _ => rfl

theorem Scoped.unknowns_lt {Δ : Ctx} : ∀ {t : Tm}, Scoped Δ t → ∀ W ∈ Tm.unknowns t, W < Δ.length
  | _, .loc _, _, h => by simp [Tm.unknowns] at h
  | _, .gnd, _, h => by simp [Tm.unknowns] at h
  | _, .arr hA hB, W, h => by
      simp only [Tm.unknowns, Finset.mem_union] at h
      rcases h with h | h
      · exact hA.unknowns_lt W h
      · exact hB.unknowns_lt W h
  | _, .app hW, W, h => by
      simp only [Tm.unknowns, Finset.mem_singleton] at h
      subst h
      exact (List.getElem?_eq_some_iff.mp hW).1

theorem storeUnknowns_lt {Δ : Ctx} : ∀ (S : EquationStore (Term Δ)), ∀ W ∈ storeUnknowns S, W < Δ.length
  | [], _, h => by simp [storeUnknowns] at h
  | e :: S, W, h => by
      rcases mem_storeUnknowns.mp h with h | h | h
      · exact e.1.2.unknowns_lt W h
      · exact e.2.2.unknowns_lt W h
      · exact storeUnknowns_lt S W h

/-- Instantiating `X` removes `X` and adds at most the unknowns of its body. -/
theorem unknowns_act_update (Δ : Ctx) (X : Nat) (b : Tm) :
    ∀ s : Tm, Tm.unknowns (Tm.act (Function.update (idA Δ) X b) s) ⊆ (Tm.unknowns s).erase X ∪ Tm.unknowns b
  | .loc _ => by simp [Tm.act, Tm.unknowns]
  | .gnd => by simp [Tm.act, Tm.unknowns]
  | .arr A B => by
      intro x hx
      simp only [Tm.act, Tm.unknowns, Finset.mem_union] at hx
      simp only [Tm.unknowns, Finset.mem_union, Finset.mem_erase]
      rcases hx with hx | hx
      · rcases Finset.mem_union.mp (unknowns_act_update Δ X b A hx) with h | h
        · exact Or.inl ⟨(Finset.mem_erase.mp h).1, Or.inl (Finset.mem_erase.mp h).2⟩
        · exact Or.inr h
      · rcases Finset.mem_union.mp (unknowns_act_update Δ X b B hx) with h | h
        · exact Or.inl ⟨(Finset.mem_erase.mp h).1, Or.inr (Finset.mem_erase.mp h).2⟩
        · exact Or.inr h
  | .app W args => by
      intro x hx
      by_cases hW : W = X
      · subst hW
        rw [act_app, Function.update_self, unknowns_rename] at hx
        exact Finset.mem_union_right _ hx
      · rw [act_app, Function.update_of_ne hW] at hx
        simp only [idA, Tm.rename, Tm.unknowns, Finset.mem_singleton] at hx
        subst hx
        simp [Tm.unknowns, hW]

theorem storeUnknowns_applyStore {Δ m : Ctx} {σ : Assign Δ m} {X : Nat} {T : Finset Nat}
    (code : ∀ s : Tm, Tm.unknowns (Tm.act σ.1 s) ⊆ (Tm.unknowns s).erase X ∪ T) :
    ∀ S : EquationStore (Term Δ), storeUnknowns (frames.applyStore σ S) ⊆ (storeUnknowns S).erase X ∪ T
  | [] => by simp [Frames.applyStore, storeUnknowns]
  | e :: S => by
      intro x hx
      have rest := storeUnknowns_applyStore code S
      simp only [Frames.applyStore, List.map_cons, storeUnknowns, Finset.mem_union] at hx
      simp only [storeUnknowns, Finset.mem_union, Finset.mem_erase]
      rcases hx with (hx | hx) | hx
      · rcases Finset.mem_union.mp (code e.1.1 hx) with h | h
        · exact Or.inl ⟨(Finset.mem_erase.mp h).1, Or.inl (Or.inl (Finset.mem_erase.mp h).2)⟩
        · exact Or.inr h
      · rcases Finset.mem_union.mp (code e.2.1 hx) with h | h
        · exact Or.inl ⟨(Finset.mem_erase.mp h).1, Or.inl (Or.inr (Finset.mem_erase.mp h).2)⟩
        · exact Or.inr h
      · have hx' : x ∈ storeUnknowns (frames.applyStore σ S) := by simpa [Frames.applyStore] using hx
        rcases Finset.mem_union.mp (rest hx') with h | h
        · exact Or.inl ⟨(Finset.mem_erase.mp h).1, Or.inr (Finset.mem_erase.mp h).2⟩
        · exact Or.inr h

/-- **Inversion removes an unknown.** -/
theorem invert_card_lt {Δ : Ctx} {e : Equation (Term Δ)} {S : EquationStore (Term Δ)} {X : Nat} {xs : List Nat}
    {t : Tm} {σ : Assign Δ Δ} (hl : e.1.1 = .app X xs) (ht : e.2.1 = t) (fresh : X ∉ Tm.unknowns t)
    (hσ : σ.1 = Function.update (idA Δ) X (invert xs t)) :
    (storeUnknowns (frames.applyStore σ S)).card < (storeUnknowns (e :: S)).card := by
  have unknownsInv : Tm.unknowns (invert xs t) = Tm.unknowns t := unknowns_rename _ t
  have inside : storeUnknowns (frames.applyStore σ S) ⊆ (storeUnknowns (e :: S)).erase X := by
    intro x hx
    have code : ∀ s : Tm, Tm.unknowns (Tm.act σ.1 s) ⊆ (Tm.unknowns s).erase X ∪ Tm.unknowns t := by
      intro s
      rw [hσ, ← unknownsInv]
      exact unknowns_act_update Δ X _ s
    rcases Finset.mem_union.mp (storeUnknowns_applyStore code S hx) with h | h
    · exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp h).1,
        mem_storeUnknowns.mpr (Or.inr (Or.inr (Finset.mem_erase.mp h).2))⟩
    · exact Finset.mem_erase.mpr ⟨fun hxX => fresh (hxX ▸ h), mem_storeUnknowns.mpr (Or.inr (Or.inl (ht ▸ h)))⟩
  have member : X ∈ storeUnknowns (e :: S) := mem_storeUnknowns.mpr (Or.inl (by rw [hl]; simp [Tm.unknowns]))
  exact lt_of_le_of_lt (Finset.card_le_card inside) (Finset.card_erase_lt_of_mem member)

/-- **A restriction does not add unknowns**: it trades the restricted unknown for the new one. -/
theorem restrict_card_le {Δ : Ctx} {S : EquationStore (Term Δ)} {Y : Nat} {P : List Nat}
    {σ : Assign Δ (extend Δ P.length)} (hσ : σ.1 = restrict Δ Y P) (hY : Y ∈ storeUnknowns S) :
    (storeUnknowns (frames.applyStore σ S)).card ≤ (storeUnknowns S).card := by
  have code : ∀ s : Tm, Tm.unknowns (Tm.act σ.1 s) ⊆ (Tm.unknowns s).erase Y ∪ {Δ.length} := by
    intro s
    rw [hσ]
    exact unknowns_act_update Δ Y _ s
  calc (storeUnknowns (frames.applyStore σ S)).card
      ≤ ((storeUnknowns S).erase Y ∪ {Δ.length}).card := Finset.card_le_card (storeUnknowns_applyStore code S)
    _ ≤ ((storeUnknowns S).erase Y).card + 1 := by
        refine le_trans (Finset.card_union_le _ _) ?_
        simp
    _ = (storeUnknowns S).card := by
        rw [Finset.card_erase_of_mem hY]
        have := Finset.card_pos.mpr ⟨Y, hY⟩
        omega

/-- **A restriction shrinks every application of the restricted unknown** and keeps every other code. -/
theorem size_act_restrict {Δ : Ctx} {Y k : Nat} {P : List Nat} (hY : Δ[Y]? = some k) (short : P.length < k) :
    ∀ {s : Tm}, Scoped Δ s → Tm.size (Tm.act (restrict Δ Y P) s) ≤ Tm.size s ∧
      (Y ∈ Tm.unknowns s → Tm.size (Tm.act (restrict Δ Y P) s) < Tm.size s)
  | _, .loc _ => ⟨le_rfl, fun h => by simp [Tm.unknowns] at h⟩
  | _, .gnd => ⟨le_rfl, fun h => by simp [Tm.unknowns] at h⟩
  | _, .arr hA hB => by
      obtain ⟨leA, ltA⟩ := size_act_restrict hY short hA
      obtain ⟨leB, ltB⟩ := size_act_restrict hY short hB
      refine ⟨by simp only [Tm.act, Tm.size]; omega, fun h => ?_⟩
      simp only [Tm.unknowns, Finset.mem_union] at h
      simp only [Tm.act, Tm.size]
      rcases h with h | h
      · have := ltA h
        omega
      · have := ltB h
        omega
  | _, @Scoped.app _ W args hW => by
      by_cases h : W = Y
      · subst h
        rw [hY] at hW
        cases hW
        rw [act_app, restrict, Function.update_self]
        simp only [Tm.rename, Tm.size, List.length_map]
        exact ⟨by omega, fun _ => by omega⟩
      · rw [act_app, restrict, Function.update_of_ne h]
        simp only [idA, Tm.rename, Tm.size, List.length_map, List.length_range, arity_of hW]
        exact ⟨le_rfl, fun hm => absurd (by simpa [Tm.unknowns] using hm : Y = W).symm h⟩

theorem storeSize_restrict {Δ : Ctx} {Y k : Nat} {P : List Nat} (hY : Δ[Y]? = some k) (short : P.length < k)
    {σ : Assign Δ (extend Δ P.length)} (hσ : σ.1 = restrict Δ Y P) :
    ∀ S : EquationStore (Term Δ), storeSize (frames.applyStore σ S) ≤ storeSize S ∧
      (Y ∈ storeUnknowns S → storeSize (frames.applyStore σ S) < storeSize S)
  | [] => ⟨le_rfl, fun h => by simp [storeUnknowns] at h⟩
  | e :: S => by
      obtain ⟨le₁, lt₁⟩ := size_act_restrict hY short e.1.2
      obtain ⟨le₂, lt₂⟩ := size_act_restrict hY short e.2.2
      obtain ⟨le₃, lt₃⟩ := storeSize_restrict hY short hσ S
      have unfold : storeSize (frames.applyStore σ (e :: S)) =
          Tm.size (Tm.act σ.1 e.1.1) + Tm.size (Tm.act σ.1 e.2.1) + storeSize (frames.applyStore σ S) := rfl
      rw [unfold, hσ]
      refine ⟨by simp only [storeSize]; omega, fun h => ?_⟩
      simp only [storeSize]
      rcases mem_storeUnknowns.mp h with h | h | h
      · have := lt₁ h
        omega
      · have := lt₂ h
        omega
      · have := lt₃ h
        omega

theorem storeUnknowns_tail_subset {Δ : Ctx} (e : Equation (Term Δ)) (S : EquationStore (Term Δ)) :
    storeUnknowns S ⊆ storeUnknowns (e :: S) :=
  fun _ h => mem_storeUnknowns.mpr (Or.inr (Or.inr h))

/-- **Every transition lowers the rank.** -/
theorem MStep.rank_lt {Δ m : Ctx} {S : EquationStore (Term Δ)} {σ : Assign Δ m} {S' : EquationStore (Term m)}
    (st : MStep S m σ S') : CumulativeCodes.RankLt (rank S') (rank S) := by
  cases st with
  | @delete e S _ =>
      apply CumulativeCodes.rankLt_of (Finset.card_le_card (storeUnknowns_tail_subset e S))
      intro _
      show storeSize S < storeSize (e :: S)
      simp only [storeSize]
      have := Tm.size_pos e.1.1
      omega
  | @decompose e e₁ e₂ S A B A' B' h h' h₁ h₁' h₂ h₂' =>
      apply CumulativeCodes.rankLt_of
      · apply Finset.card_le_card
        intro x hx
        rcases mem_storeUnknowns.mp hx with hx | hx | hx
        · rw [h₁] at hx
          exact mem_storeUnknowns.mpr (Or.inl (by rw [h]; simp [Tm.unknowns, hx]))
        · rw [h₁'] at hx
          exact mem_storeUnknowns.mpr (Or.inr (Or.inl (by rw [h']; simp [Tm.unknowns, hx])))
        rcases mem_storeUnknowns.mp hx with hx | hx | hx
        · rw [h₂] at hx
          exact mem_storeUnknowns.mpr (Or.inl (by rw [h]; simp [Tm.unknowns, hx]))
        · rw [h₂'] at hx
          exact mem_storeUnknowns.mpr (Or.inr (Or.inl (by rw [h']; simp [Tm.unknowns, hx])))
        · exact mem_storeUnknowns.mpr (Or.inr (Or.inr hx))
      · intro _
        show storeSize (e₁ :: e₂ :: S) < storeSize (e :: S)
        simp only [storeSize]
        rw [h₁, h₁', h₂, h₂', h, h']
        simp only [Tm.size]
        omega
  | invertLeft hl _ fresh _ hσ => exact Prod.Lex.left _ _ (invert_card_lt hl rfl fresh hσ)
  | @invertRight e S X xs σ hr _ fresh _ hσ =>
      have lt := invert_card_lt (e := (e.2, e.1)) (S := S) hr rfl fresh hσ
      have same : storeUnknowns ((e.2, e.1) :: S) = storeUnknowns (e :: S) := by
        simp only [storeUnknowns, Finset.union_comm (Tm.unknowns e.2.1)]
      rw [same] at lt
      exact Prod.Lex.left _ _ lt
  | @pruneLeft e S X Y xs zs σ _ occ short hσ =>
      have hY : Y ∈ storeUnknowns (e :: S) := mem_storeUnknowns.mpr (Or.inr (Or.inl occ.mem))
      apply CumulativeCodes.rankLt_of (restrict_card_le hσ hY)
      intro _
      exact (storeSize_restrict (occ.decl e.2.2) short hσ (e :: S)).2 hY
  | @pruneRight e S X Y xs zs σ _ occ short hσ =>
      have hY : Y ∈ storeUnknowns (e :: S) := mem_storeUnknowns.mpr (Or.inl occ.mem)
      apply CumulativeCodes.rankLt_of (restrict_card_le hσ hY)
      intro _
      exact (storeSize_restrict (occ.decl e.1.2) short hσ (e :: S)).2 hY
  | @intersect e S X xs ys σ hl _ short hσ =>
      have hX : X ∈ storeUnknowns (e :: S) :=
        mem_storeUnknowns.mpr (Or.inl (by rw [hl]; simp [Tm.unknowns]))
      apply CumulativeCodes.rankLt_of (restrict_card_le hσ hX)
      intro _
      exact (storeSize_restrict (decl_of_app hl) short hσ (e :: S)).2 hX

/-- **The transitions terminate**: there is no infinite run from any store at any context. -/
theorem steps_terminate :
    WellFounded (fun y x : (Δ : Ctx) × EquationStore (Term Δ) => ∃ σ : Assign x.1 y.1, MStep x.2 y.1 σ y.2) :=
  Subrelation.wf (fun ⟨_, st⟩ => st.rank_lt)
    (InvImage.wf (fun x : (Δ : Ctx) × EquationStore (Term Δ) => rank x.2) CumulativeCodes.rankLt_wf)

/-! ## The pattern fragment -/

/-- **A pattern**: every unknown of the code is applied to distinct locals. -/
inductive Pat : Tm → Prop
  | loc (i : Nat) : Pat (.loc i)
  | gnd : Pat .gnd
  | arr {A B : Tm} : Pat A → Pat B → Pat (.arr A B)
  | app {W : Nat} {args : List Nat} : args.Nodup → Pat (.app W args)

/-- **The fragment**: both sides of every equation are patterns. -/
def Patterns {Δ : Ctx} (S : EquationStore (Term Δ)) : Prop := ∀ e ∈ S, Pat e.1.1 ∧ Pat e.2.1

theorem spread_inj {args : List Nat} (nd : args.Nodup) {i j : Nat} (hi : i < args.length) (hj : j < args.length)
    (h : Tm.spread args i = Tm.spread args j) : i = j := by
  rw [Tm.spread_of_lt hi, Tm.spread_of_lt hj] at h
  exact (List.Nodup.getElem_inj_iff nd).mp h

/-- A renaming injective on the locals of a pattern gives a pattern. -/
theorem Pat.rename {ρ : Nat → Nat} {P : Nat → Prop} (inj : ∀ i, P i → ∀ j, P j → ρ i = ρ j → i = j) :
    ∀ {t : Tm}, Pat t → Tm.AllLocals P t → Pat (Tm.rename ρ t)
  | _, .loc i, _ => .loc (ρ i)
  | _, .gnd, _ => .gnd
  | _, .arr hA hB, h => by
      cases h with
      | arr lA lB => exact .arr (Pat.rename inj hA lA) (Pat.rename inj hB lB)
  | _, .app nd, h => by
      cases h with
      | app hargs => exact .app (nd.map_on fun x hx y hy e => inj x (hargs x hx) y (hargs y hy) e)

theorem rename_idA {Δ : Ctx} {W : Nat} {args : List Nat} (hW : Δ[W]? = some args.length) :
    Tm.rename (Tm.spread args) (idA Δ W) = .app W args := by
  have := act_id (Δ := Δ) (Scoped.app hW)
  rwa [act_app] at this

/-- **Instantiating one unknown keeps patterns**, when its body, spread over any distinct arguments, is one. -/
theorem Pat.act_update {Δ : Ctx} {X : Nat} {b : Tm}
    (body : ∀ args : List Nat, args.Nodup → Δ[X]? = some args.length → Pat (Tm.rename (Tm.spread args) b)) :
    ∀ {s : Tm}, Scoped Δ s → Pat s → Pat (Tm.act (Function.update (idA Δ) X b) s)
  | _, .loc i, _ => .loc i
  | _, .gnd, _ => .gnd
  | _, .arr sA sB, p => by
      cases p with
      | arr pA pB => exact .arr (Pat.act_update body sA pA) (Pat.act_update body sB pB)
  | _, @Scoped.app _ W args hW, p => by
      cases p with
      | app nd =>
          by_cases h : W = X
          · subst h
            rw [act_app, Function.update_self]
            exact body args nd hW
          · rw [act_app, Function.update_of_ne h, rename_idA hW]
            exact .app nd

theorem Pat.invert_body {Δ : Ctx} {X : Nat} {xs : List Nat} {t : Tm} (hX : Δ[X]? = some xs.length) (pt : Pat t)
    (inside : Tm.AllLocals (· ∈ xs) t) :
    ∀ args : List Nat, args.Nodup → Δ[X]? = some args.length → Pat (Tm.rename (Tm.spread args) (invert xs t)) := by
  intro args nd hargs
  have len : xs.length = args.length := by
    rw [hX] at hargs
    exact Option.some.inj hargs
  rw [invert, Tm.rename_rename]
  refine Pat.rename (fun i hi j hj e => ?_) pt inside
  have hi' : Tm.idx xs i < args.length := len ▸ Tm.idx_lt hi
  have hj' : Tm.idx xs j < args.length := len ▸ Tm.idx_lt hj
  have same := spread_inj nd hi' hj' e
  rw [← Tm.spread_idx hi, ← Tm.spread_idx hj, same]

theorem Pat.restrict_body {Δ : Ctx} {Y k : Nat} {P : List Nat} (hY : Δ[Y]? = some k) (nd : P.Nodup)
    (below : ∀ i ∈ P, i < k) :
    ∀ args : List Nat, args.Nodup → Δ[Y]? = some args.length →
      Pat (Tm.rename (Tm.spread args) (.app Δ.length P)) := by
  intro args ndArgs hargs
  have len : k = args.length := by
    rw [hY] at hargs
    exact Option.some.inj hargs
  exact .app (nd.map_on fun x hx y hy e =>
    spread_inj ndArgs (len ▸ below x hx) (len ▸ below y hy) e)

theorem prunePositions_nodup (xs zs : List Nat) : (prunePositions xs zs).Nodup :=
  List.nodup_range.filter _

theorem agreePositions_nodup (xs ys : List Nat) : (agreePositions xs ys).Nodup :=
  List.nodup_range.filter _

theorem Patterns.applyStore {Δ m : Ctx} {S : EquationStore (Term Δ)} {σ : Assign Δ m} {X : Nat} {b : Tm}
    (hσ : σ.1 = Function.update (idA Δ) X b)
    (body : ∀ args : List Nat, args.Nodup → Δ[X]? = some args.length → Pat (Tm.rename (Tm.spread args) b))
    (h : Patterns S) : Patterns (frames.applyStore σ S) := by
  intro e' he'
  obtain ⟨e'', he'', rfl⟩ := List.mem_map.mp he'
  obtain ⟨one, two⟩ := h e'' he''
  show Pat (Tm.act σ.1 e''.1.1) ∧ Pat (Tm.act σ.1 e''.2.1)
  rw [hσ]
  exact ⟨Pat.act_update body e''.1.2 one, Pat.act_update body e''.2.2 two⟩

theorem Pat.arr_inv {A B : Tm} (h : Pat (.arr A B)) : Pat A ∧ Pat B := by
  cases h with
  | arr hA hB => exact ⟨hA, hB⟩

/-- **The transitions keep the fragment.** -/
theorem MStep.patterns {Δ m : Ctx} {S : EquationStore (Term Δ)} {σ : Assign Δ m} {S' : EquationStore (Term m)}
    (st : MStep S m σ S') (h : Patterns S) : Patterns S' := by
  cases st with
  | delete _ => exact fun e' he' => h e' (List.mem_cons_of_mem _ he')
  | @decompose e e₁ e₂ S A B A' B' h₀ h₀' h₁ h₁' h₂ h₂' =>
      obtain ⟨p₁, p₂⟩ := h e List.mem_cons_self
      rw [h₀] at p₁
      rw [h₀'] at p₂
      intro e' he'
      rcases List.mem_cons.mp he' with rfl | he'
      · rw [h₁, h₁']
        exact ⟨p₁.arr_inv.1, p₂.arr_inv.1⟩
      rcases List.mem_cons.mp he' with rfl | he'
      · rw [h₂, h₂']
        exact ⟨p₁.arr_inv.2, p₂.arr_inv.2⟩
      exact h e' (List.mem_cons_of_mem _ he')
  | @invertLeft e S X xs σ hl _ _ inside hσ =>
      exact Patterns.applyStore hσ (Pat.invert_body (decl_of_app hl) (h e List.mem_cons_self).2 inside)
        (fun e' he' => h e' (List.mem_cons_of_mem _ he'))
  | @invertRight e S X xs σ hr _ _ inside hσ =>
      exact Patterns.applyStore hσ (Pat.invert_body (decl_of_app_right hr) (h e List.mem_cons_self).1 inside)
        (fun e' he' => h e' (List.mem_cons_of_mem _ he'))
  | @pruneLeft e S X Y xs zs σ _ occ _ hσ =>
      exact Patterns.applyStore hσ
        (Pat.restrict_body (occ.decl e.2.2) (prunePositions_nodup xs zs) prunePositions_below) h
  | @pruneRight e S X Y xs zs σ _ occ _ hσ =>
      exact Patterns.applyStore hσ
        (Pat.restrict_body (occ.decl e.1.2) (prunePositions_nodup xs zs) prunePositions_below) h
  | @intersect e S X xs ys σ hl _ _ hσ =>
      exact Patterns.applyStore hσ
        (Pat.restrict_body (decl_of_app hl) (agreePositions_nodup xs ys) agreePositions_below) h

/-! ## Progress and decision -/

/-- A code whose rigid locals and arguments satisfy `P` has all its locals in `P`. -/
theorem allLocals_of {P : Nat → Prop} : ∀ {t : Tm}, (∀ j, RigidLocal j t → P j) →
    (∀ Y zs, OccursAt Y zs t → ∀ z ∈ zs, P z) → Tm.AllLocals P t
  | .loc i, h₁, _ => .loc (h₁ i .here)
  | .gnd, _, _ => .gnd
  | .arr _ _, h₁, h₂ =>
      .arr (allLocals_of (fun j r => h₁ j (.left r)) (fun Y zs o => h₂ Y zs (.left o)))
        (allLocals_of (fun j r => h₁ j (.right r)) (fun Y zs o => h₂ Y zs (.right o)))
  | .app W zs, _, h₂ => .app (h₂ W zs .here)

theorem agree_short {xs ys : List Nat} (len : ys.length = xs.length) (ne : xs ≠ ys) :
    (agreePositions xs ys).length < xs.length := by
  rw [agreePositions]
  have lt := List.length_filter_lt_length_iff_exists (p := fun i => decide (Tm.spread xs i = Tm.spread ys i))
    (l := List.range xs.length)
  rw [List.length_range] at lt
  apply lt.mpr
  by_contra hall
  apply ne
  refine List.ext_getElem len.symm fun i h₁ h₂ => ?_
  by_contra hi
  exact hall ⟨i, List.mem_range.mpr h₁, by simp [Tm.spread_of_lt h₁, Tm.spread_of_lt h₂, hi]⟩

theorem prune_short {xs zs : List Nat} {z : Nat} (hz : z ∈ zs) (out : z ∉ xs) :
    (prunePositions xs zs).length < zs.length := by
  rw [prunePositions]
  have lt := List.length_filter_lt_length_iff_exists (p := fun i => decide (Tm.spread zs i ∈ xs))
    (l := List.range zs.length)
  rw [List.length_range] at lt
  exact lt.mpr ⟨Tm.idx zs z, List.mem_range.mpr (Tm.idx_lt hz), by simp [Tm.spread_idx hz, out]⟩

/-- **Progress on the fragment**: a nonempty store of patterns has a transition or a refutation. -/
theorem progress {Δ : Ctx} {e : Equation (Term Δ)} {S : EquationStore (Term Δ)} (h : Patterns (e :: S)) :
    (∃ (m : Ctx) (σ : Assign Δ m) (S' : EquationStore (Term m)), MStep (e :: S) m σ S') ∨
      ∃ r : Reason, MRefutes (e :: S) r := by
  obtain ⟨⟨s, hs⟩, ⟨t, ht⟩⟩ := e
  obtain ⟨ps, pt⟩ := h _ List.mem_cons_self
  simp only at ps pt
  by_cases same : s = t
  · exact Or.inl ⟨_, _, _, .delete same⟩
  -- a flexible left side
  have flexLeft : ∀ X xs, s = .app X xs →
      (∃ (m : Ctx) (σ : Assign Δ m) (S' : EquationStore (Term m)), MStep ((⟨s, hs⟩, ⟨t, ht⟩) :: S) m σ S') ∨
        ∃ r : Reason, MRefutes ((⟨s, hs⟩, ⟨t, ht⟩) :: S) r := by
    intro X xs hX
    subst hX
    have nd : xs.Nodup := by
      cases ps with
      | app nd => exact nd
    have hXd : Δ[X]? = some xs.length := Scoped.app_inv hs
    by_cases occ : X ∈ Tm.unknowns t
    · cases t with
      | loc _ => simp [Tm.unknowns] at occ
      | gnd => simp [Tm.unknowns] at occ
      | arr A B =>
          obtain ⟨ys, o⟩ := OccursAt.of_mem occ
          exact Or.inr ⟨_, .occursLeft rfl rfl o⟩
      | app V ys =>
          have hV : X = V := by simpa [Tm.unknowns] using occ
          subst hV
          have len : ys.length = xs.length := by
            have := Scoped.app_inv ht
            rw [hXd] at this
            exact (Option.some.inj this).symm
          have short := agree_short len fun h => same (by rw [h])
          exact Or.inl ⟨_, ⟨restrict Δ X (agreePositions xs ys), restrict_typed hXd agreePositions_below⟩, _,
            .intersect rfl rfl short rfl⟩
    · by_cases scope : ∃ j, RigidLocal j t ∧ j ∉ xs
      · obtain ⟨j, r, out⟩ := scope
        exact Or.inr ⟨_, .scopeLeft rfl r out⟩
      by_cases prune : ∃ Y zs, OccursAt Y zs t ∧ ∃ z ∈ zs, z ∉ xs
      · obtain ⟨Y, zs, o, z, hz, out⟩ := prune
        exact Or.inl ⟨_, ⟨restrict Δ Y (prunePositions xs zs), restrict_typed (o.decl ht) prunePositions_below⟩,
          _, .pruneLeft rfl o (prune_short hz out) rfl⟩
      · have inside : Tm.AllLocals (· ∈ xs) t :=
          allLocals_of (fun j r => Classical.byContradiction fun out => scope ⟨j, r, out⟩)
            (fun Y zs o z hz => Classical.byContradiction fun out => prune ⟨Y, zs, o, z, hz, out⟩)
        exact Or.inl ⟨_, ⟨Function.update (idA Δ) X (invert xs t), invert_typed hXd ht inside⟩, _,
          .invertLeft rfl nd occ inside rfl⟩
  -- a flexible right side against a rigid left side
  have flexRight : ∀ X xs, t = .app X xs → (∀ V ys, s ≠ .app V ys) →
      (∃ (m : Ctx) (σ : Assign Δ m) (S' : EquationStore (Term m)), MStep ((⟨s, hs⟩, ⟨t, ht⟩) :: S) m σ S') ∨
        ∃ r : Reason, MRefutes ((⟨s, hs⟩, ⟨t, ht⟩) :: S) r := by
    intro X xs hX rigid
    subst hX
    have nd : xs.Nodup := by
      cases pt with
      | app nd => exact nd
    have hXd : Δ[X]? = some xs.length := Scoped.app_inv ht
    by_cases occ : X ∈ Tm.unknowns s
    · cases s with
      | loc _ => simp [Tm.unknowns] at occ
      | gnd => simp [Tm.unknowns] at occ
      | arr A B =>
          obtain ⟨ys, o⟩ := OccursAt.of_mem occ
          exact Or.inr ⟨_, .occursRight rfl rfl o⟩
      | app V ys => exact absurd rfl (rigid V ys)
    · by_cases scope : ∃ j, RigidLocal j s ∧ j ∉ xs
      · obtain ⟨j, r, out⟩ := scope
        exact Or.inr ⟨_, .scopeRight rfl r out⟩
      by_cases prune : ∃ Y zs, OccursAt Y zs s ∧ ∃ z ∈ zs, z ∉ xs
      · obtain ⟨Y, zs, o, z, hz, out⟩ := prune
        exact Or.inl ⟨_, ⟨restrict Δ Y (prunePositions xs zs), restrict_typed (o.decl hs) prunePositions_below⟩,
          _, .pruneRight rfl o (prune_short hz out) rfl⟩
      · have inside : Tm.AllLocals (· ∈ xs) s :=
          allLocals_of (fun j r => Classical.byContradiction fun out => scope ⟨j, r, out⟩)
            (fun Y zs o z hz => Classical.byContradiction fun out => prune ⟨Y, zs, o, z, hz, out⟩)
        exact Or.inl ⟨_, ⟨Function.update (idA Δ) X (invert xs s), invert_typed hXd hs inside⟩, _,
          .invertRight rfl nd occ inside rfl⟩
  cases ps with
  | app nd => exact flexLeft _ _ rfl
  | loc i =>
      cases pt with
      | app nd => exact flexRight _ _ rfl fun _ _ h => by cases h
      | loc j =>
          refine Or.inr ⟨_, .clash (h := i + 2) (h' := j + 2) rfl rfl fun hij => same ?_⟩
          have : i = j := by omega
          rw [this]
      | gnd => exact Or.inr ⟨_, .clash (h := i + 2) (h' := 0) rfl rfl (by omega)⟩
      | arr _ _ => exact Or.inr ⟨_, .clash (h := i + 2) (h' := 1) rfl rfl (by omega)⟩
  | gnd =>
      cases pt with
      | app nd => exact flexRight _ _ rfl fun _ _ h => by cases h
      | loc j => exact Or.inr ⟨_, .clash (h := 0) (h' := j + 2) rfl rfl (by omega)⟩
      | gnd => exact absurd rfl same
      | arr _ _ => exact Or.inr ⟨_, .clash (h := 0) (h' := 1) rfl rfl (by decide)⟩
  | @arr A B pA pB =>
      cases pt with
      | app nd => exact flexRight _ _ rfl fun _ _ h => by cases h
      | loc j => exact Or.inr ⟨_, .clash (h := 1) (h' := j + 2) rfl rfl (by omega)⟩
      | gnd => exact Or.inr ⟨_, .clash (h := 1) (h' := 0) rfl rfl (by decide)⟩
      | @arr A' B' pA' pB' =>
          obtain ⟨sA, sB⟩ := Scoped.arr_inv hs
          obtain ⟨sA', sB'⟩ := Scoped.arr_inv ht
          exact Or.inl ⟨_, _, (⟨A, sA⟩, ⟨A', sA'⟩) :: (⟨B, sB⟩, ⟨B', sB'⟩) :: S,
            .decompose rfl rfl rfl rfl rfl rfl⟩

/-- **Decision on Miller patterns**: every store of patterns has a run, through restricted contexts, that ends in
the empty store or in a refutation. -/
theorem decided {Δ : Ctx} (S : EquationStore (Term Δ)) (h : Patterns S) :
    ∃ (m : Ctx) (σ : Assign Δ m) (R : EquationStore (Term m)), solver.Reaches S m σ R ∧
      (R = [] ∨ ∃ r : Reason, MRefutes R r) := by
  suffices key : ∀ x : (Δ : Ctx) × EquationStore (Term Δ), Patterns x.2 →
      ∃ (m : Ctx) (σ : Assign x.1 m) (R : EquationStore (Term m)), solver.Reaches x.2 m σ R ∧
        (R = [] ∨ ∃ r : Reason, MRefutes R r) from key ⟨Δ, S⟩ h
  intro x
  induction x using (InvImage.wf (fun x : (Δ : Ctx) × EquationStore (Term Δ) => rank x.2)
      CumulativeCodes.rankLt_wf).induction with
  | h x ih =>
      obtain ⟨Δ, S⟩ := x
      intro h
      match S, h with
      | [], _ => exact ⟨Δ, _, [], .refl [], Or.inl rfl⟩
      | e :: S, h =>
          rcases progress h with ⟨m, σ, S', st⟩ | ⟨reason, refuted⟩
          · obtain ⟨n, τ, R, run, ends⟩ := ih ⟨m, S'⟩ st.rank_lt (st.patterns h)
            exact ⟨n, _, R, .step st run, ends⟩
          · exact ⟨Δ, _, _, .refl _, Or.inr ⟨reason, refuted⟩⟩

/-- **Principal or unsolvable**: every store of Miller patterns has a principal answer, reached by the solver, or
no solution. -/
theorem principal_or_unsolvable {Δ : Ctx} (S : EquationStore (Term Δ)) (h : Patterns S) :
    (∃ (m : Ctx) (σ : Assign Δ m), frames.Principal S σ) ∨ ¬ frames.Solvable S := by
  obtain ⟨m, σ, R, run, ends⟩ := decided S h
  rcases ends with rfl | ⟨r, refuted⟩
  · exact Or.inl ⟨m, σ, solved_principal run⟩
  · exact Or.inr (refuted_none (P := solver) run refuted)

end MillerCodes

#print axioms MillerCodes.MStep.rank_lt
#print axioms MillerCodes.steps_terminate
#print axioms MillerCodes.MStep.patterns
#print axioms MillerCodes.progress
#print axioms MillerCodes.decided
#print axioms MillerCodes.principal_or_unsolvable

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
