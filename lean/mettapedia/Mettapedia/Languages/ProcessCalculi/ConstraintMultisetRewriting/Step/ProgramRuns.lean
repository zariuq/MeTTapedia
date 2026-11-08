import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramAdequacy

/-!
# An executable successor function for the source core, proved exact

The reference semantics is computable. `matchPat` is first-order matching with an association list
(`Binding`), `pick` chooses rows for a rule's take and read patterns, and `successors W` lists the
rows a configuration of rows can step to. It is exact (`step_iff_successors`): a step from `W` is
exactly a permutation of one of its successors.

So finite claims about all runs are kernel computations:

* `reachable_closed`: a finite list of configurations closed under `successors` contains every
  configuration reachable from its members;
* `chain_reaches`: a list of configurations each a successor of the previous is a run;
* `stuck_of_successors`: a configuration without successors has no step, hence no translated
  firing (`Program.stuck_of_source`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Program

open ProgramRows ProgramTranslation

/-! ## First-order matching with association lists -/

/-- Partial assignments of rows to pattern variables. -/
abbrev Binding := List (ℕ × Sx)

/-- The total assignment of a binding: unbound variables read as the default row. -/
def Binding.get (σ : Binding) (x : ℕ) : Sx := (σ.lookup x).getD default

/-- `σ'` keeps every binding of `σ`. -/
def Extends (σ σ' : Binding) : Prop := ∀ x v, σ.lookup x = some v → σ'.lookup x = some v

/-- Every binding of `σ` is the value of `θ`. -/
def Agrees (σ : Binding) (θ : ℕ → Sx) : Prop := ∀ x v, σ.lookup x = some v → θ x = v

theorem Extends.refl (σ : Binding) : Extends σ σ := fun _ _ h => h

theorem Extends.trans {σ σ' σ'' : Binding} (one : Extends σ σ') (two : Extends σ' σ'') : Extends σ σ'' :=
  fun x v h => two x v (one x v h)

/-- Match a pattern against a row, extending a binding. -/
def matchPat : Pat → Sx → Binding → Option Binding
  | .var x, s, σ =>
      match σ.lookup x with
      | some t => if t = s then some σ else none
      | none => some ((x, s) :: σ)
  | .sym k, .sym k', σ => if k = k' then some σ else none
  | .cell a b, .cell s t, σ => (matchPat a s σ).bind fun σ' => matchPat b t σ'
  | .sym _, .cell _ _, _ => none
  | .cell _ _, .sym _, _ => none

theorem lookup_cons_self (x : ℕ) (s : Sx) (σ : Binding) : ((x, s) :: σ).lookup x = some s := by
  simp [List.lookup]

theorem lookup_cons_ne {x y : ℕ} (s : Sx) (σ : Binding) (ne : y ≠ x) : ((x, s) :: σ).lookup y = σ.lookup y := by
  simp only [List.lookup, beq_eq_false_iff_ne.mpr ne]

/-- **Matching is sound**: the result extends the binding, binds every pattern variable, and every
further extension instantiates the pattern to the row. -/
theorem matchPat_sound : ∀ (p : Pat) (s : Sx) (σ σ' : Binding), matchPat p s σ = some σ' →
    Extends σ σ' ∧ ∀ τ : Binding, Extends σ' τ → p.inst τ.get = s
  | .var x, s, σ, σ', h => by
      unfold matchPat at h
      cases hx : σ.lookup x with
      | some t =>
          simp only [hx] at h
          by_cases same : t = s
          · rw [if_pos same] at h
            cases h
            refine ⟨Extends.refl σ, fun τ ext => ?_⟩
            simp [Pat.inst, Binding.get, ext x t hx, same]
          · rw [if_neg same] at h
            cases h
      | none =>
          simp only [hx] at h
          cases h
          refine ⟨fun y v hy => ?_, fun τ ext => ?_⟩
          · by_cases ne : y = x
            · subst ne; rw [hx] at hy; cases hy
            · rw [lookup_cons_ne s σ ne]; exact hy
          · simp [Pat.inst, Binding.get, ext x s (lookup_cons_self x s σ)]
  | .sym k, .sym k', σ, σ', h => by
      unfold matchPat at h
      by_cases same : k = k'
      · rw [if_pos same] at h
        cases h
        exact ⟨Extends.refl σ, fun _ _ => by simp [Pat.inst, same]⟩
      · rw [if_neg same] at h
        cases h
  | .cell a b, .cell s t, σ, σ', h => by
      unfold matchPat at h
      obtain ⟨σ₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨ext₁, inst₁⟩ := matchPat_sound a s σ σ₁ h₁
      obtain ⟨ext₂, inst₂⟩ := matchPat_sound b t σ₁ σ' h₂
      exact ⟨ext₁.trans ext₂, fun τ ext => by
        rw [Pat.inst, inst₁ τ (ext₂.trans ext), inst₂ τ ext]⟩
  | .sym _, .cell _ _, _, _, h => by simp [matchPat] at h
  | .cell _ _, .sym _, _, _, h => by simp [matchPat] at h

/-- **Matching is complete**: against an instance under `θ`, from a binding agreeing with `θ`,
matching succeeds with a binding agreeing with `θ`. -/
theorem matchPat_complete {θ : ℕ → Sx} : ∀ (p : Pat) (σ : Binding), Agrees σ θ →
    ∃ σ', matchPat p (p.inst θ) σ = some σ' ∧ Agrees σ' θ
  | .var x, σ, agrees => by
      cases hx : σ.lookup x with
      | some t =>
          have same : t = θ x := (agrees x t hx).symm
          refine ⟨σ, ?_, agrees⟩
          simp [matchPat, Pat.inst, hx, same]
      | none =>
          refine ⟨(x, θ x) :: σ, by simp [matchPat, Pat.inst, hx], fun y v hy => ?_⟩
          by_cases ne : y = x
          · subst ne
            rw [lookup_cons_self] at hy
            cases hy
            rfl
          · rw [lookup_cons_ne _ σ ne] at hy
            exact agrees y v hy
  | .sym k, σ, agrees => ⟨σ, by simp [matchPat, Pat.inst], agrees⟩
  | .cell a b, σ, agrees => by
      obtain ⟨σ₁, h₁, agrees₁⟩ := matchPat_complete a σ agrees
      obtain ⟨σ₂, h₂, agrees₂⟩ := matchPat_complete b σ₁ agrees₁
      exact ⟨σ₂, by simp [matchPat, Pat.inst, h₁, h₂], agrees₂⟩

/-- A binding agreeing with `θ` and binding every variable of `p` reads `p` as `θ` does. -/
theorem inst_get_of_agrees {σ : Binding} {θ : ℕ → Sx} (agrees : Agrees σ θ) (p : Pat)
    (bound : ∀ x ∈ p.vars, ∃ v, σ.lookup x = some v) : p.inst σ.get = p.inst θ :=
  Pat.inst_congr p fun x hx => by
    obtain ⟨v, hv⟩ := bound x hx
    simp [Binding.get, hv, agrees x v hv]

theorem matchPat_binds : ∀ (p : Pat) (s : Sx) (σ σ' : Binding), matchPat p s σ = some σ' →
    ∀ x ∈ p.vars, ∃ v, σ'.lookup x = some v
  | .var x, s, σ, σ', h => by
      intro y hy
      simp only [Pat.vars, List.mem_singleton] at hy
      subst hy
      unfold matchPat at h
      cases hx : σ.lookup y with
      | some t =>
          simp only [hx] at h
          by_cases same : t = s
          · rw [if_pos same] at h; cases h; exact ⟨t, hx⟩
          · rw [if_neg same] at h; cases h
      | none =>
          simp only [hx] at h
          cases h
          exact ⟨s, lookup_cons_self y s σ⟩
  | .sym _, .sym _, _, _, _ => by intro x hx; simp [Pat.vars] at hx
  | .cell a b, .cell s t, σ, σ', h => by
      unfold matchPat at h
      obtain ⟨σ₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h
      intro x hx
      simp only [Pat.vars, List.mem_append] at hx
      rcases hx with hx | hx
      · obtain ⟨v, hv⟩ := matchPat_binds a s σ σ₁ h₁ x hx
        exact ⟨v, ((matchPat_sound b t σ₁ σ' h₂).1) x v hv⟩
      · exact matchPat_binds b t σ₁ σ' h₂ x hx
  | .sym _, .cell _ _, _, _, h => by simp [matchPat] at h
  | .cell _ _, .sym _, _, _, h => by simp [matchPat] at h

/-! ## Choosing rows -/

/-- Choose a row for each pattern, removing each chosen row; return the binding and the rest. -/
def pick : List Pat → List Sx → Binding → List (Binding × List Sx)
  | [], W, σ => [(σ, W)]
  | p :: ps, W, σ => W.flatMap fun s =>
      match matchPat p s σ with
      | some σ' => pick ps (W.erase s) σ'
      | none => []

theorem pick_sound : ∀ (ps : List Pat) (W : List Sx) (σ σ' : Binding) (rest : List Sx),
    (σ', rest) ∈ pick ps W σ →
      Extends σ σ' ∧ (∀ x, (∃ p ∈ ps, x ∈ p.vars) → ∃ v, σ'.lookup x = some v) ∧
        ∀ τ : Binding, Extends σ' τ → (W : Multiset Sx) = ((ps.map (Pat.inst τ.get) : List Sx) : Multiset Sx) + rest
  | [], W, σ, σ', rest, h => by
      simp only [pick, List.mem_singleton, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨Extends.refl _, fun x ⟨p, hp, _⟩ => absurd hp List.not_mem_nil, fun _ _ => by simp⟩
  | p :: ps, W, σ, σ', rest, h => by
      simp only [pick, List.mem_flatMap] at h
      obtain ⟨s, sIn, h⟩ := h
      cases hm : matchPat p s σ with
      | none => rw [hm] at h; cases h
      | some σ₁ =>
          rw [hm] at h
          obtain ⟨ext₁, inst₁⟩ := matchPat_sound p s σ σ₁ hm
          obtain ⟨ext₂, bound₂, split₂⟩ := pick_sound ps (W.erase s) σ₁ σ' rest h
          refine ⟨ext₁.trans ext₂, fun x ⟨q, hq, hx⟩ => ?_, fun τ ext => ?_⟩
          · rcases List.mem_cons.mp hq with rfl | hq
            · obtain ⟨v, hv⟩ := matchPat_binds q s σ σ₁ hm x hx
              exact ⟨v, ext₂ x v hv⟩
            · exact bound₂ x ⟨q, hq, hx⟩
          · have perm : (W : Multiset Sx) = s ::ₘ ((W.erase s : List Sx) : Multiset Sx) := by
              rw [Multiset.cons_coe]
              exact Multiset.coe_eq_coe.mpr (List.perm_cons_erase sIn)
            rw [perm, split₂ τ ext, List.map_cons, inst₁ τ (ext₂.trans ext), ← Multiset.cons_coe,
              Multiset.cons_add]

theorem pick_complete {θ : ℕ → Sx} : ∀ (ps : List Pat) (W : List Sx) (F : Multiset Sx) (σ : Binding),
    Agrees σ θ → (W : Multiset Sx) = ((ps.map (Pat.inst θ) : List Sx) : Multiset Sx) + F →
      ∃ σ' rest, (σ', rest) ∈ pick ps W σ ∧ Agrees σ' θ ∧ (rest : Multiset Sx) = F
  | [], W, F, σ, agrees, h => ⟨σ, W, by simp [pick], agrees, by simpa using h⟩
  | p :: ps, W, F, σ, agrees, h => by
      have sIn : p.inst θ ∈ W := by
        have : p.inst θ ∈ (W : Multiset Sx) := by rw [h]; simp
        exact Multiset.mem_coe.mp this
      obtain ⟨σ₁, hm, agrees₁⟩ := matchPat_complete p σ agrees
      have rest : ((W.erase (p.inst θ) : List Sx) : Multiset Sx) =
          ((ps.map (Pat.inst θ) : List Sx) : Multiset Sx) + F := by
        rw [← Multiset.coe_erase, h, List.map_cons, ← Multiset.cons_coe, Multiset.cons_add,
          Multiset.erase_cons_head]
      obtain ⟨σ', rest', mem, agrees', same⟩ := pick_complete ps _ F σ₁ agrees₁ rest
      refine ⟨σ', rest', ?_, agrees', same⟩
      simp only [pick, List.mem_flatMap]
      exact ⟨p.inst θ, sIn, by rw [hm]; exact mem⟩

/-! ## Successors -/

/-- The result of a rule on chosen rows. -/
def output (r : Schema) (σ : Binding) (rest : List Sx) : List Sx :=
  r.make.map (Pat.inst σ.get) ++ r.read.map (Pat.inst σ.get) ++ rest

/-- The successors of a configuration of rows by one rule. -/
def ruleSuccessors (i : RuleName) (W : List Sx) : List (List Sx) :=
  (pick ((schema i).take ++ (schema i).read) W []).map fun choice => output (schema i) choice.1 choice.2

/-- **The successors of a configuration of rows.** -/
def successors (W : List Sx) : List (List Sx) := allRules.flatMap fun i => ruleSuccessors i W

theorem mem_ruleSuccessors {i : RuleName} {W l : List Sx} :
    l ∈ ruleSuccessors i W ↔ ∃ σ rest, (σ, rest) ∈ pick ((schema i).take ++ (schema i).read) W [] ∧
      l = output (schema i) σ rest := by
  simp only [ruleSuccessors, List.mem_map]
  constructor
  · rintro ⟨⟨σ, rest⟩, mem, rfl⟩
    exact ⟨σ, rest, mem, rfl⟩
  · rintro ⟨σ, rest, mem, rfl⟩
    exact ⟨⟨σ, rest⟩, mem, rfl⟩

theorem mem_successors {W l : List Sx} : l ∈ successors W ↔ ∃ i, l ∈ ruleSuccessors i W := by
  simp only [successors, List.mem_flatMap]
  exact ⟨fun ⟨i, _, h⟩ => ⟨i, h⟩, fun ⟨i, h⟩ => ⟨i, mem_allRules i, h⟩⟩

/-- **The successor function of one rule is exact.** -/
theorem fires_iff_ruleSuccessors (i : RuleName) (W : List Sx) (W' : Multiset Sx) :
    (schema i).Fires (W : Multiset Sx) W' ↔ ∃ l ∈ ruleSuccessors i W, W' = (l : Multiset Sx) := by
  constructor
  · rintro ⟨θ, F, hW, rfl⟩
    have split : (W : Multiset Sx) =
        ((((schema i).take ++ (schema i).read).map (Pat.inst θ) : List Sx) : Multiset Sx) + F := by
      rw [hW, push_eq, push_eq, List.map_append, ← Multiset.coe_add, add_assoc]
    obtain ⟨σ, rest, mem, agrees, same⟩ := pick_complete _ W F [] (fun _ _ h => by cases h) split
    obtain ⟨-, bound, -⟩ := pick_sound _ W [] σ rest mem
    refine ⟨output (schema i) σ rest, mem_ruleSuccessors.mpr ⟨σ, rest, mem, rfl⟩, ?_⟩
    have readSame : (schema i).read.map (Pat.inst σ.get) = (schema i).read.map (Pat.inst θ) :=
      List.map_congr_left fun p hp => inst_get_of_agrees agrees p fun x hx =>
        bound x ⟨p, List.mem_append_right _ hp, hx⟩
    have makeSame : (schema i).make.map (Pat.inst σ.get) = (schema i).make.map (Pat.inst θ) :=
      List.map_congr_left fun q hq => inst_get_of_agrees agrees q fun x hx => by
        obtain ⟨p, hp, hx'⟩ := (schema_wellFormed i).covered q hq x hx
        exact bound x ⟨p, hp, hx'⟩
    rw [output, readSame, makeSame, push_eq, push_eq, ← same, ← Multiset.coe_add, ← Multiset.coe_add,
      add_assoc]
  · rintro ⟨l, mem, rfl⟩
    obtain ⟨σ, rest, pickMem, rfl⟩ := mem_ruleSuccessors.mp mem
    obtain ⟨-, -, split⟩ := pick_sound _ W [] σ rest pickMem
    refine ⟨σ.get, rest, ?_, ?_⟩
    · rw [split σ (Extends.refl σ), push_eq, push_eq, List.map_append, ← Multiset.coe_add, add_assoc]
    · rw [output, push_eq, push_eq, ← Multiset.coe_add, ← Multiset.coe_add, add_assoc]

/-- **The successor function is exact**: a step from `W` reaches exactly the successors of `W`, up
to the order of rows. -/
theorem step_iff_successors (W : List Sx) (W' : Multiset Sx) :
    Step (W : Multiset Sx) W' ↔ ∃ l ∈ successors W, W' = (l : Multiset Sx) := by
  rw [step_iff_rewrites]
  constructor
  · rintro ⟨i, fires⟩
    obtain ⟨l, mem, rfl⟩ := (fires_iff_ruleSuccessors i W W').mp fires
    exact ⟨l, mem_successors.mpr ⟨i, mem⟩, rfl⟩
  · rintro ⟨l, mem, rfl⟩
    obtain ⟨i, mem⟩ := mem_successors.mp mem
    exact ⟨i, (fires_iff_ruleSuccessors i W l).mpr ⟨l, mem, rfl⟩⟩

/-! ## Finite claims about all runs -/

/-- A step from a configuration given as a list. -/
theorem step_of_successor {W l : List Sx} (mem : l ∈ successors W) : Step (W : Multiset Sx) (l : Multiset Sx) :=
  (step_iff_successors W l).mpr ⟨l, mem, rfl⟩

/-- **No successors, no step.** -/
theorem stuck_of_successors {W : List Sx} (none : successors W = []) (W' : Multiset Sx) :
    ¬ Step (W : Multiset Sx) W' := fun step => by
  obtain ⟨l, mem, -⟩ := (step_iff_successors W W').mp step
  rw [none] at mem
  cases mem

/-- A list of configurations closed under successors, up to order. -/
def SuccessorClosed (S : List (List Sx)) : Bool :=
  S.all fun W => (successors W).all fun l => S.any fun W' => l.isPerm W'

/-- **Everything reachable from a closed list stays in it.** -/
theorem reachable_closed {S : List (List Sx)} (closed : SuccessorClosed S = true) {W₀ : List Sx} (start : W₀ ∈ S)
    {W : Multiset Sx} (path : Relation.ReflTransGen Step (W₀ : Multiset Sx) W) :
    ∃ W' ∈ S, W = (W' : Multiset Sx) := by
  induction path with
  | refl => exact ⟨W₀, start, rfl⟩
  | tail _ step ih =>
      obtain ⟨V, VIn, rfl⟩ := ih
      obtain ⟨l, mem, rfl⟩ := (step_iff_successors V _).mp step
      simp only [SuccessorClosed, List.all_eq_true, List.any_eq_true] at closed
      obtain ⟨V', V'In, perm⟩ := closed V VIn l mem
      exact ⟨V', V'In, Multiset.coe_eq_coe.mpr (List.isPerm_iff.mp perm)⟩

/-- Each configuration is, up to order, a successor of the previous one. -/
def Chained : List (List Sx) → Bool
  | a :: b :: rest => (successors a).any (fun l => l.isPerm b) && Chained (b :: rest)
  | _ => true

/-- **A chained list is a run.** -/
theorem chain_reaches : ∀ {a : List Sx} {rest : List (List Sx)}, Chained (a :: rest) = true →
    Relation.ReflTransGen Step (a : Multiset Sx) (((a :: rest).getLast (List.cons_ne_nil a rest) : List Sx) : Multiset Sx)
  | _, [], _ => .refl
  | a, b :: rest, h => by
      simp only [Chained, Bool.and_eq_true, List.any_eq_true] at h
      obtain ⟨⟨l, mem, perm⟩, later⟩ := h
      have first : Step (a : Multiset Sx) (b : Multiset Sx) := by
        have := step_of_successor mem
        rwa [Multiset.coe_eq_coe.mpr (List.isPerm_iff.mp perm)] at this
      have tail := chain_reaches (a := b) (rest := rest) later
      rw [List.getLast_cons (List.cons_ne_nil b rest)]
      exact Relation.ReflTransGen.head first tail

#print axioms matchPat_sound
#print axioms matchPat_complete
#print axioms pick_sound
#print axioms pick_complete
#print axioms fires_iff_ruleSuccessors
#print axioms step_iff_successors
#print axioms stuck_of_successors
#print axioms reachable_closed
#print axioms chain_reaches

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Program
