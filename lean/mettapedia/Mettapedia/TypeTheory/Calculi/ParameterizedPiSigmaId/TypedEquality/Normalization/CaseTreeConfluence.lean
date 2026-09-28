import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.CaseTree
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.ConstructorSystemDevelopment

/-!
# Church–Rosser for case-tree definitions

The leaves of a case tree are the equations it computes by: on the left, the
defined constant applied to the leaf's neighbourhood filled with the leaf's
variables; on the right, the leaf's right side. Every variable occurs exactly
once on the left, and the constructors of a neighbourhood are those the tree
splits on. Two leaves of one tree have unifiable left sides only when they are
the same leaf: where their paths part, their neighbourhoods hold distinct
constructors at the same variable, and a refinement is unifiable only where
what it refines is. Definitions under distinct names never overlap.

So when the constructors split on are not defined constants, the leaf
equations of case-tree definitions form a constructor system: left-linear,
every variable of a right side on the left, and determined, since a common
instance of two left sides makes them one equation and fixes its
instantiation (`leafSchema_determined`). A rule package computing by such
definitions is Church–Rosser (`caseTree_churchRosser`), by the complete
development of `ConstructorSystemDevelopment`.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open AlgebraicSchema (SchemaFamily SchemaStep LeftLinear LeftLinearFamily variableMultiplicity
  variableMultiplicity_rename_of_avoids)
open AlgebraicParallel ConversionCoherence
open ConstructorSystem (Pattern LeftSide System unifiable)

variable {Head : Type}

/-! ## Compatible patterns -/

mutual
/-- Two patterns have a common instance: a variable meets anything, and two
constructor patterns meet when their constructors agree and their arguments
meet. -/
def Pat.compat : Pat → Pat → Bool
  | .var, _ => true
  | .con _ _, .var => true
  | .con c ps, .con c' ps' => decide (c = c') && Pat.compatAll ps ps'
/-- Two lists of patterns meet position by position. -/
def Pat.compatAll : List Pat → List Pat → Bool
  | [], [] => true
  | p :: ps, p' :: ps' => Pat.compat p p' && Pat.compatAll ps ps'
  | [], _ :: _ => false
  | _ :: _, [] => false
end

mutual
theorem Pat.compat_comm : ∀ p q : Pat, Pat.compat p q = Pat.compat q p
  | .var, .var => rfl
  | .var, .con _ _ => rfl
  | .con _ _, .var => rfl
  | .con c ps, .con c' ps' => by
      simp only [Pat.compat]
      rw [Pat.compatAll_comm ps ps']
      by_cases h : c = c'
      · subst h
        rfl
      · rw [decide_eq_false h, decide_eq_false (Ne.symm h)]
theorem Pat.compatAll_comm : ∀ ps qs : List Pat, Pat.compatAll ps qs = Pat.compatAll qs ps
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | p :: ps, q :: qs => by
      simp only [Pat.compatAll]
      rw [Pat.compat_comm p q, Pat.compatAll_comm ps qs]
end

mutual
/-- What meets a split pattern meets the pattern before the split. -/
theorem Pat.compat_of_splitAt (c : DeclName) (fields : Nat) :
    ∀ (p : Pat) (position : Nat) (q : Pat),
      Pat.compat (p.splitAt c fields position) q = true → Pat.compat p q = true
  | .var, _, _, _ => rfl
  | .con _ _, _, .var, _ => rfl
  | .con c' ps, position, .con c'' qs, h => by
      simp only [Pat.splitAt, Pat.compat, Bool.and_eq_true] at h ⊢
      exact ⟨h.1, Pat.compatAll_of_splitAllAt c fields ps position qs h.2⟩
theorem Pat.compatAll_of_splitAllAt (c : DeclName) (fields : Nat) :
    ∀ (ps : List Pat) (position : Nat) (qs : List Pat),
      Pat.compatAll (Pat.splitAllAt c fields ps position) qs = true →
        Pat.compatAll ps qs = true
  | [], _, _, h => h
  | _ :: _, _, [], h => by
      simp only [Pat.splitAllAt] at h
      split at h <;> cases h
  | p :: ps, position, q :: qs, h => by
      simp only [Pat.splitAllAt] at h
      split at h
      · simp only [Pat.compatAll, Bool.and_eq_true] at h ⊢
        exact ⟨Pat.compat_of_splitAt c fields p position q h.1, h.2⟩
      · simp only [Pat.compatAll, Bool.and_eq_true] at h ⊢
        exact ⟨h.1, Pat.compatAll_of_splitAllAt c fields ps (position - p.vars) qs h.2⟩
end

/-- What meets a refinement meets the neighbourhood it refines. -/
theorem Pat.compatAll_of_refines {N N' : List Pat} (refines : Pat.Refines N N')
    {X : List Pat} (h : Pat.compatAll N' X = true) : Pat.compatAll N X = true := by
  induction refines with
  | refl => exact h
  | tail _ step ih =>
      obtain ⟨c, fields, position, _, rfl⟩ := step
      exact ih (Pat.compatAll_of_splitAllAt c fields _ position X h)

mutual
/-- Two splits of one variable meet only when they use the same constructor. -/
theorem Pat.eq_of_compat_splitAt (c₁ c₂ : DeclName) (k₁ k₂ : Nat) :
    ∀ (p : Pat) (position : Nat), position < p.vars →
      Pat.compat (p.splitAt c₁ k₁ position) (p.splitAt c₂ k₂ position) = true →
        c₁ = c₂
  | .var, 0, _, h => by
      simp only [Pat.splitAt, Pat.compat, Bool.and_eq_true, decide_eq_true_eq] at h
      exact h.1
  | .var, _ + 1, hp, _ => by
      simp only [Pat.vars_var] at hp
      omega
  | .con _ ps, position, hp, h => by
      simp only [Pat.splitAt, Pat.compat, Bool.and_eq_true] at h
      exact Pat.eq_of_compatAll_splitAllAt c₁ c₂ k₁ k₂ ps position hp h.2
theorem Pat.eq_of_compatAll_splitAllAt (c₁ c₂ : DeclName) (k₁ k₂ : Nat) :
    ∀ (ps : List Pat) (position : Nat), position < Pat.varsAll ps →
      Pat.compatAll (Pat.splitAllAt c₁ k₁ ps position)
        (Pat.splitAllAt c₂ k₂ ps position) = true → c₁ = c₂
  | [], _, hp, _ => by
      simp only [Pat.varsAll_nil] at hp
      omega
  | p :: ps, position, hp, h => by
      simp only [Pat.splitAllAt] at h
      simp only [Pat.varsAll_cons] at hp
      by_cases hlt : position < p.vars
      · rw [if_pos hlt, if_pos hlt] at h
        simp only [Pat.compatAll, Bool.and_eq_true] at h
        exact Pat.eq_of_compat_splitAt c₁ c₂ k₁ k₂ p position hlt h.1
      · rw [if_neg hlt, if_neg hlt] at h
        simp only [Pat.compatAll, Bool.and_eq_true] at h
        exact Pat.eq_of_compatAll_splitAllAt c₁ c₂ k₁ k₂ ps (position - p.vars) (by omega)
          h.2
end

/-- Two leaves of a scoped tree with meeting neighbourhoods are the same
leaf. -/
theorem CaseTree.LeafOf.unique {tree : CaseTree Head} {N N₁ N₂ : List Pat}
    {vars₁ vars₂ : Nat} {rhs₁ : Tm Head vars₁} {rhs₂ : Tm Head vars₂}
    (first : tree.LeafOf N N₁ vars₁ rhs₁) :
    ∀ {k : Nat}, tree.Scoped k → Pat.varsAll N = k → tree.LeafOf N N₂ vars₂ rhs₂ →
      Pat.compatAll N₁ N₂ = true →
        N₁ = N₂ ∧
          (⟨vars₁, rhs₁⟩ : Σ vars, Tm Head vars) = ⟨vars₂, rhs₂⟩ := by
  induction first with
  | leaf rhs N =>
      intro k _ _ second _
      cases second
      exact ⟨rfl, rfl⟩
  | @split position family branches c fields tree N N₁ vars₁ rhs₁ found leaf ih =>
      intro k inScope hk second compat
      cases second with
      | @split _ _ _ c₂ fields₂ tree₂ _ _ _ _ found₂ leaf₂ =>
          cases inScope with
          | split inRange scopedBranches =>
              have scoped₁ := scopedBranches.find found
              have hv₁ := Pat.varsAll_splitAllAt c fields N position (hk ▸ inRange)
              have hv₂ := Pat.varsAll_splitAllAt c₂ fields₂ N position (hk ▸ inRange)
              obtain ⟨refines₁, _⟩ := leaf.refines scoped₁ (by omega)
              obtain ⟨refines₂, _⟩ :=
                leaf₂.refines (scopedBranches.find found₂) (by omega)
              have meet : Pat.compatAll (Pat.splitAllAt c fields N position)
                  (Pat.splitAllAt c₂ fields₂ N position) = true := by
                have step₁ := Pat.compatAll_of_refines refines₁ compat
                rw [Pat.compatAll_comm] at step₁ ⊢
                exact Pat.compatAll_of_refines refines₂ step₁
              have same := Pat.eq_of_compatAll_splitAllAt c c₂ fields fields₂ N position
                (hk ▸ inRange) meet
              subst same
              rw [found] at found₂
              cases found₂
              exact ih scoped₁ (by omega) leaf₂ compat

/-! ## Unifiable left sides -/

/-- Unifiable constant spines have the same constant and unifiable arguments. -/
theorem unifiable_appSpine_const {m m' : Nat} {c c' : DeclName} :
    ∀ {as : List (Tm Head m)} {bs : List (Tm Head m')},
      unifiable (appSpine (.const c) as) (appSpine (.const c') bs) = true →
        c = c' ∧ List.Forall₂ (fun a b => unifiable a b = true) as bs := by
  intro as
  induction as using List.reverseRecOn with
  | nil =>
      intro bs h
      rcases List.eq_nil_or_concat bs with rfl | ⟨bs', b, rfl⟩
      · simp only [appSpine_nil, unifiable, decide_eq_true_eq] at h
        exact ⟨h, .nil⟩
      · rw [List.concat_eq_append, appSpine_concat, appSpine_nil] at h
        cases h
  | append_singleton as a ih =>
      intro bs h
      rcases List.eq_nil_or_concat bs with rfl | ⟨bs', b, rfl⟩
      · rw [appSpine_concat, appSpine_nil] at h
        cases h
      · rw [List.concat_eq_append, appSpine_concat, appSpine_concat] at h
        rw [List.concat_eq_append]
        simp only [unifiable, Bool.and_eq_true] at h
        obtain ⟨same, pairs⟩ := ih h.1
        exact ⟨same, List.rel_append pairs (.cons h.2 .nil)⟩

mutual
/-- Patterns whose instances are unifiable meet. -/
theorem Pat.compat_of_unifiable {m m' : Nat} :
    ∀ (p q : Pat) (vs : List (Tm Head m)) (ws : List (Tm Head m')),
      unifiable (Pat.term p vs) (Pat.term q ws) = true → Pat.compat p q = true
  | .var, _, _, _, _ => rfl
  | .con _ _, .var, _, _, _ => rfl
  | .con c ps, .con c' qs, vs, ws, h => by
      obtain ⟨rfl, pairs⟩ := unifiable_appSpine_const h
      simp only [Pat.compat, decide_true, Bool.true_and]
      exact Pat.compatAll_of_unifiable ps qs vs ws pairs
/-- Lists of patterns whose instances are unifiable position by position
meet. -/
theorem Pat.compatAll_of_unifiable {m m' : Nat} :
    ∀ (ps qs : List Pat) (vs : List (Tm Head m)) (ws : List (Tm Head m')),
      List.Forall₂ (fun a b => unifiable a b = true) (Pat.terms ps vs) (Pat.terms qs ws) →
        Pat.compatAll ps qs = true
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by cases h
  | _ :: _, [], _, _, h => by cases h
  | p :: ps, q :: qs, vs, ws, h => by
      cases h with
      | cons first rest =>
          simp only [Pat.compatAll, Bool.and_eq_true]
          exact ⟨Pat.compat_of_unifiable p q _ _ first,
            Pat.compatAll_of_unifiable ps qs _ _ rest⟩
end

/-! ## Variable occurrences in leaf equations -/

theorem variableMultiplicity_appSpine {m : Nat} (index : Fin m) :
    ∀ (h : Tm Head m) (as : List (Tm Head m)),
      variableMultiplicity index (appSpine h as) =
        variableMultiplicity index h + (as.map (variableMultiplicity index)).sum
  | h, [] => by simp
  | h, a :: as => by
      rw [appSpine_cons, variableMultiplicity_appSpine index (.app h a) as]
      simp only [variableMultiplicity, List.map_cons, List.sum_cons]
      omega

mutual
/-- The occurrences of a variable in a filled pattern are its occurrences in
the values. -/
theorem Pat.variableMultiplicity_term {m : Nat} (index : Fin m) :
    ∀ (p : Pat) (vs : List (Tm Head m)), vs.length = p.vars →
      variableMultiplicity index (Pat.term p vs) = (vs.map (variableMultiplicity index)).sum
  | .var, vs, h => by
      obtain ⟨v, rfl⟩ := List.length_eq_one_iff.mp h
      simp [Pat.term, Pat.fill]
  | .con c ps, vs, h => by
      show variableMultiplicity index (appSpine (.const c) (Pat.terms ps vs)) = _
      rw [variableMultiplicity_appSpine, Pat.variableMultiplicity_terms index ps vs h]
      simp only [variableMultiplicity, Nat.zero_add]
theorem Pat.variableMultiplicity_terms {m : Nat} (index : Fin m) :
    ∀ (ps : List Pat) (vs : List (Tm Head m)), vs.length = Pat.varsAll ps →
      ((Pat.terms ps vs).map (variableMultiplicity index)).sum =
        (vs.map (variableMultiplicity index)).sum
  | [], vs, h => by
      rw [List.eq_nil_of_length_eq_zero h]
      rfl
  | p :: ps, vs, h => by
      simp only [Pat.varsAll_cons] at h
      show ((Pat.term p (vs.take p.vars) :: Pat.terms ps (vs.drop p.vars)).map
        (variableMultiplicity index)).sum = _
      rw [List.map_cons, List.sum_cons,
        Pat.variableMultiplicity_term index p _ (List.length_take_of_le (by omega)),
        Pat.variableMultiplicity_terms index ps _ (by rw [List.length_drop]; omega),
        ← List.sum_append, ← List.map_append, List.take_append_drop]
end

theorem sum_map_zero {α : Type} : ∀ l : List α, (l.map fun _ => (0 : Nat)).sum = 0
  | [] => rfl
  | _ :: l => by rw [List.map_cons, List.sum_cons, sum_map_zero l]

/-- Every variable of a context of pattern variables occurs once among them. -/
theorem varTerms_variableMultiplicity : ∀ {vars : Nat} (index : Fin vars),
    ((varTerms (Head := Head) vars).map (variableMultiplicity index)).sum = 1
  | 0, index => index.elim0
  | vars + 1, index => by
      have shifted : ((varTerms (Head := Head) vars).map (Presentation.rename wk)).map
          (variableMultiplicity index) = (varTerms (Head := Head) vars).map
            (fun t => Fin.cases 0 (fun j => variableMultiplicity j t) index) := by
        rw [List.map_map]
        apply List.map_congr_left
        intro t mem
        obtain ⟨i, rfl⟩ := varTerms_var mem
        refine Fin.cases ?_ (fun j => ?_) index
        · show variableMultiplicity 0 (Presentation.rename wk (.var i)) = 0
          exact variableMultiplicity_rename_of_avoids _ wk 0 (fun i => Fin.succ_ne_zero i)
        · show (if Fin.succ i = Fin.succ j then 1 else 0) = (if i = j then 1 else 0)
          by_cases same : i = j
          · rw [if_pos same, if_pos (congrArg Fin.succ same)]
          · rw [if_neg same, if_neg (fun e => same (Fin.succ_injective _ e))]
      rw [varTerms, List.map_append, List.sum_append, shifted]
      refine Fin.cases ?_ (fun j => ?_) index
      · show ((varTerms vars).map fun _ => 0).sum + (if (0 : Fin (vars + 1)) = 0 then 1 else 0) +
          0 = 1
        rw [sum_map_zero, if_pos rfl]
      · show ((varTerms vars).map (variableMultiplicity j)).sum +
          (if (0 : Fin (vars + 1)) = Fin.succ j then 1 else 0) + 0 = 1
        rw [varTerms_variableMultiplicity j, if_neg (Fin.succ_ne_zero j).symm]

/-- In a leaf equation, every variable occurs exactly once on the left. -/
theorem leafLeft_variableMultiplicity {m : Nat} (f : DeclName) {N : List Pat}
    (hN : Pat.varsAll N = m) (index : Fin m) :
    variableMultiplicity index (appSpine (.const f) (Pat.terms N (varTerms (Head := Head) m))) =
      1 := by
  rw [variableMultiplicity_appSpine,
    Pat.variableMultiplicity_terms index N _ (by rw [varTerms_length, hN]),
    varTerms_variableMultiplicity]
  simp only [variableMultiplicity, Nat.zero_add]

/-! ## Constructors of neighbourhoods and trees -/

mutual
/-- The constructors of a pattern. -/
def Pat.constructors : Pat → List DeclName
  | .var => []
  | .con c ps => c :: Pat.constructorsAll ps
/-- The constructors of a list of patterns. -/
def Pat.constructorsAll : List Pat → List DeclName
  | [] => []
  | p :: ps => p.constructors ++ Pat.constructorsAll ps
end

mutual
/-- The constructors a tree splits on. -/
def CaseTree.constructors : CaseTree Head → List DeclName
  | .leaf _ _ => []
  | .split _ _ branches => branches.constructors
/-- The constructors the branches split on. -/
def CaseBranches.constructors : CaseBranches Head → List DeclName
  | .nil => []
  | .cons c _ tree rest => c :: (tree.constructors ++ rest.constructors)
end

theorem Pat.constructorsAll_replicate : ∀ k : Nat,
    Pat.constructorsAll (List.replicate k .var) = []
  | 0 => rfl
  | k + 1 => by
      rw [List.replicate_succ]
      exact Pat.constructorsAll_replicate k

mutual
theorem Pat.constructors_splitAt (c₀ : DeclName) (fields : Nat) :
    ∀ (p : Pat) (position : Nat) {c : DeclName},
      c ∈ (p.splitAt c₀ fields position).constructors →
      c = c₀ ∨ c ∈ p.constructors
  | .var, 0, c, h => by
      simp only [Pat.splitAt, Pat.constructors, Pat.constructorsAll_replicate,
        List.mem_singleton] at h
      exact .inl h
  | .var, _ + 1, _, h => by
      simp only [Pat.splitAt, Pat.constructors] at h
      cases h
  | .con c' ps, position, c, h => by
      simp only [Pat.splitAt, Pat.constructors, List.mem_cons] at h ⊢
      rcases h with same | mem
      · exact .inr (.inl same)
      · rcases Pat.constructorsAll_splitAllAt c₀ fields ps position mem with same | mem'
        · exact .inl same
        · exact .inr (.inr mem')
theorem Pat.constructorsAll_splitAllAt (c₀ : DeclName) (fields : Nat) :
    ∀ (ps : List Pat) (position : Nat) {c : DeclName},
      c ∈ Pat.constructorsAll (Pat.splitAllAt c₀ fields ps position) →
        c = c₀ ∨ c ∈ Pat.constructorsAll ps
  | [], _, _, h => by cases h
  | p :: ps, position, c, h => by
      simp only [Pat.splitAllAt] at h
      simp only [Pat.constructorsAll, List.mem_append]
      split at h
      · simp only [Pat.constructorsAll, List.mem_append] at h
        rcases h with mem | mem
        · rcases Pat.constructors_splitAt c₀ fields p position mem with same | mem'
          · exact .inl same
          · exact .inr (.inl mem')
        · exact .inr (.inr mem)
      · simp only [Pat.constructorsAll, List.mem_append] at h
        rcases h with mem | mem
        · exact .inr (.inl mem)
        · rcases Pat.constructorsAll_splitAllAt c₀ fields ps (position - p.vars) mem with
            same | mem'
          · exact .inl same
          · exact .inr (.inr mem')
end

theorem CaseBranches.constructors_find :
    ∀ {branches : CaseBranches Head} {c : DeclName} {fields : Nat} {tree : CaseTree Head},
      branches.find c = some (fields, tree) →
        c ∈ branches.constructors ∧ ∀ c' ∈ tree.constructors, c' ∈ branches.constructors
  | .nil, _, _, _, found => by cases found
  | .cons c₀ _ tree₀ rest, c, fields, tree, found => by
      simp only [CaseBranches.find] at found
      simp only [CaseBranches.constructors, List.mem_cons, List.mem_append]
      by_cases same : c = c₀
      · rw [if_pos same] at found
        cases found
        exact ⟨.inl same, fun c' mem => .inr (.inl mem)⟩
      · rw [if_neg same] at found
        obtain ⟨mem, sub⟩ := CaseBranches.constructors_find found
        exact ⟨.inr (.inr mem), fun c' mem' => .inr (.inr (sub c' mem'))⟩

/-- The constructors of a leaf's neighbourhood are those of the starting
neighbourhood or those the tree splits on. -/
theorem CaseTree.LeafOf.constructors {tree : CaseTree Head} {N N' : List Pat} {vars : Nat}
    {rhs : Tm Head vars} (leaf : tree.LeafOf N N' vars rhs) :
    ∀ c ∈ Pat.constructorsAll N', c ∈ Pat.constructorsAll N ∨ c ∈ tree.constructors := by
  induction leaf with
  | leaf => exact fun c mem => .inl mem
  | @split position family branches c₀ fields tree N N' vars rhs found _ ih =>
      intro c mem
      obtain ⟨here, sub⟩ := CaseBranches.constructors_find found
      rcases ih c mem with mem' | mem'
      · rcases Pat.constructorsAll_splitAllAt c₀ fields N position mem' with same | mem''
        · subst same
          exact .inr here
        · exact .inl mem''
      · exact .inr (sub c mem')

/-! ## Patterns of leaf equations -/

theorem pattern_appSpine_const {defined : DeclName → Prop} {m : Nat} {c : DeclName}
    (hc : ¬ defined c) :
    ∀ (args : List (Tm Head m)), (∀ a ∈ args, Pattern defined true a) →
      ∀ flag, Pattern defined flag (appSpine (.const c) args) := by
  intro args
  induction args using List.reverseRecOn with
  | nil => intro _ flag; exact .const hc
  | append_singleton args a ih =>
      intro h flag
      rw [appSpine_concat]
      exact .app (ih (fun b mem => h b (List.mem_append_left _ mem)) false)
        (h a (List.mem_append_right _ (List.mem_singleton_self a)))

mutual
theorem Pat.pattern_term {defined : DeclName → Prop} {m : Nat} :
    ∀ (p : Pat) (vs : List (Tm Head m)), (∀ c ∈ p.constructors, ¬ defined c) →
      (∀ v ∈ vs, ∃ i, v = .var i) → vs.length = p.vars →
        Pattern defined true (Pat.term p vs)
  | .var, vs, _, hv, h => by
      obtain ⟨v, rfl⟩ := List.length_eq_one_iff.mp h
      obtain ⟨i, rfl⟩ := hv v (List.mem_singleton_self v)
      exact .var i
  | .con c ps, vs, hc, hv, h =>
      pattern_appSpine_const (hc c (List.mem_cons_self ..)) _
        (Pat.pattern_terms ps vs (fun c' mem => hc c' (List.mem_cons_of_mem _ mem)) hv h) true
theorem Pat.pattern_terms {defined : DeclName → Prop} {m : Nat} :
    ∀ (ps : List Pat) (vs : List (Tm Head m)),
      (∀ c ∈ Pat.constructorsAll ps, ¬ defined c) →
      (∀ v ∈ vs, ∃ i, v = .var i) → vs.length = Pat.varsAll ps →
        ∀ t ∈ Pat.terms ps vs, Pattern defined true t
  | [], _, _, _, _, _, mem => by cases mem
  | p :: ps, vs, hc, hv, h, t, mem => by
      simp only [Pat.varsAll_cons] at h
      simp only [Pat.constructorsAll, List.mem_append] at hc
      change t ∈ Pat.term p (vs.take p.vars) :: Pat.terms ps (vs.drop p.vars) at mem
      rcases List.mem_cons.mp mem with rfl | mem'
      · exact Pat.pattern_term p _ (fun c mem => hc c (.inl mem))
          (fun v mem => hv v (List.mem_of_mem_take mem)) (List.length_take_of_le (by omega))
      · exact Pat.pattern_terms ps _ (fun c mem => hc c (.inr mem))
          (fun v mem => hv v (List.mem_of_mem_drop mem)) (by rw [List.length_drop]; omega) t mem'
end

theorem leftSide_appSpine {defined : DeclName → Prop} {m : Nat} (f : DeclName) :
    ∀ (args : List (Tm Head m)), (∀ a ∈ args, Pattern defined true a) →
      LeftSide defined (appSpine (.const f) args) f args.length := by
  intro args
  induction args using List.reverseRecOn with
  | nil => intro _; exact .const f
  | append_singleton args a ih =>
      intro h
      rw [appSpine_concat, List.length_append, List.length_singleton]
      exact .app (ih (fun b mem => h b (List.mem_append_left _ mem)))
        (h a (List.mem_append_right _ (List.mem_singleton_self a)))

/-! ## The leaf system of case-tree definitions -/

/-- The arity of the first definition named `name`. -/
def arityOf : List (CaseTreeDefinition Head) → DeclName → Nat
  | [], _ => 0
  | d :: ds, name => if d.name = name then d.arity else arityOf ds name

theorem arityOf_of_mem : ∀ {defs : List (CaseTreeDefinition Head)},
    (defs.map CaseTreeDefinition.name).Nodup → ∀ {d : CaseTreeDefinition Head}, d ∈ defs →
      arityOf defs d.name = d.arity
  | [], _, _, mem => by cases mem
  | d' :: ds, names, d, mem => by
      simp only [arityOf]
      rcases List.mem_cons.mp mem with rfl | mem'
      · exact if_pos rfl
      · have fresh : d'.name ∉ ds.map CaseTreeDefinition.name := (List.nodup_cons.mp names).1
        have ne : d'.name ≠ d.name := fun same =>
          fresh (same ▸ List.mem_map_of_mem mem')
        rw [if_neg ne]
        exact arityOf_of_mem (List.nodup_cons.mp names).2 mem'

/-- Case-tree definitions whose leaf equations form a constructor system:
distinct names, positive arities, trees scoped at their arities, and splits
only on constructors that are not defined names. -/
structure LeafConditions (defs : List (CaseTreeDefinition Head)) : Prop where
  names : (defs.map CaseTreeDefinition.name).Nodup
  arity_pos : ∀ d ∈ defs, 0 < d.arity
  inScope : ∀ d ∈ defs, d.tree.Scoped d.arity
  constructors : ∀ d ∈ defs, ∀ c ∈ d.tree.constructors,
    c ∉ defs.map CaseTreeDefinition.name

/-- The leaf equations of case-tree definitions: a definition's constant
applied to a leaf's neighbourhood, filled with the leaf's variables, and the
leaf's right side. -/
def leafSchema (defs : List (CaseTreeDefinition Head)) : SchemaFamily Head :=
  fun {vars} left right => ∃ d ∈ defs, ∃ N : List Pat,
    d.tree.LeafOf (List.replicate d.arity .var) N vars right ∧
      left = appSpine (.const d.name) (Pat.terms N (varTerms vars))

section LeafSystem

variable {defs : List (CaseTreeDefinition Head)}

/-- The names of the definitions. -/
abbrev definedIn (defs : List (CaseTreeDefinition Head)) (name : DeclName) : Prop :=
  name ∈ defs.map CaseTreeDefinition.name

theorem leafSchema_vars (conditions : LeafConditions defs) {d : CaseTreeDefinition Head}
    (mem : d ∈ defs) {N : List Pat} {vars : Nat} {rhs : Tm Head vars}
    (leaf : d.tree.LeafOf (List.replicate d.arity .var) N vars rhs) : Pat.varsAll N = vars :=
  (leaf.refines (conditions.inScope d mem) (Pat.varsAll_replicate d.arity)).2

theorem leafSchema_multiplicity (conditions : LeafConditions defs) {m : Nat}
    {left right : Tm Head m} (rule : leafSchema defs left right) (index : Fin m) :
    variableMultiplicity index left = 1 := by
  obtain ⟨d, mem, N, leaf, rfl⟩ := rule
  exact leafLeft_variableMultiplicity d.name (leafSchema_vars conditions mem leaf) index

theorem leafSchema_left (conditions : LeafConditions defs) {m : Nat}
    {left right : Tm Head m} (rule : leafSchema defs left right) :
    ∃ name, definedIn defs name ∧ 0 < arityOf defs name ∧
      LeftSide (definedIn defs) left name (arityOf defs name) := by
  obtain ⟨d, mem, N, leaf, rfl⟩ := rule
  have hN := leafSchema_vars conditions mem leaf
  have length : (Pat.terms N (varTerms (Head := Head) m)).length = arityOf defs d.name := by
    rw [Pat.fillAll_length, leaf.length, List.length_replicate,
      arityOf_of_mem conditions.names mem]
  refine ⟨d.name, List.mem_map_of_mem mem, ?_, ?_⟩
  · rw [arityOf_of_mem conditions.names mem]
    exact conditions.arity_pos d mem
  · rw [← length]
    refine leftSide_appSpine d.name _ (Pat.pattern_terms N _ ?_ (fun _ mem => varTerms_var mem)
      (by rw [varTerms_length, hN]))
    intro c cmem
    rcases leaf.constructors c cmem with root | split
    · rw [Pat.constructorsAll_replicate] at root
      cases root
    · exact conditions.constructors d mem c split

theorem leafSchema_disjoint (conditions : LeafConditions defs) {m m' : Nat}
    {left right : Tm Head m} {left' right' : Tm Head m'}
    (rule : leafSchema defs left right) (rule' : leafSchema defs left' right')
    (meet : unifiable left left' = true) :
    (⟨m, (left, right)⟩ : Σ arity : Nat, Tm Head arity × Tm Head arity) =
      ⟨m', (left', right')⟩ := by
  obtain ⟨d, mem, N, leaf, rfl⟩ := rule
  obtain ⟨d', mem', N', leaf', rfl⟩ := rule'
  obtain ⟨sameName, pairs⟩ := unifiable_appSpine_const meet
  obtain rfl := List.inj_on_of_nodup_map conditions.names mem mem' sameName
  have compat := Pat.compatAll_of_unifiable N N' _ _ pairs
  obtain ⟨rfl, same⟩ := leaf.unique (conditions.inScope d mem) (Pat.varsAll_replicate d.arity)
    leaf' compat
  obtain ⟨rfl, heq⟩ := Sigma.mk.inj same
  obtain rfl := eq_of_heq heq
  rfl

/-- An instance of a leaf equation's left side determines the instantiation:
every variable occurs on the left, as an argument of a constructor spine. -/
theorem leafSchema_instantiation (conditions : LeafConditions defs) {m n : Nat}
    {left right : Tm Head m} (rule : leafSchema defs left right) {σ σ' : Sub Head m n}
    (same : Presentation.subst σ left = Presentation.subst σ' left) : σ = σ' := by
  obtain ⟨d, mem, N, leaf, rfl⟩ := rule
  have hN := leafSchema_vars conditions mem leaf
  rw [subst_appSpine, subst_appSpine, Pat.terms_subst, Pat.terms_subst] at same
  have values := Pat.terms_injective N (by rw [List.length_map, varTerms_length, hN])
    (by rw [List.length_map, varTerms_length, hN]) (appSpine_const_injective same).2
  funext i
  rw [← valueSub_map_varTerms σ i, ← valueSub_map_varTerms σ' i, values]

/-- The contractions of leaf equations are determined: a common instance of
two left sides makes them one equation (`leafSchema_disjoint`, through
`ConstructorSystem.unifiable_of_leftSide`), whose instantiation it
determines. -/
theorem leafSchema_determined (conditions : LeafConditions defs) :
    ∀ {m m' n n' : Nat} {left right : Tm Head m} {left' right' : Tm Head m'},
      leafSchema defs left right → leafSchema defs left' right' →
      ∀ (instantiation : Sub Head m n) (instantiation' : Sub Head m' n),
        Presentation.subst instantiation left = Presentation.subst instantiation' left' →
        ∀ (develop : Tm Head n → Tm Head n'),
          Presentation.subst (fun index => develop (instantiation index)) right =
            Presentation.subst (fun index => develop (instantiation' index)) right' := by
  intro m m' n n' left right left' right' rule rule' instantiation instantiation' same develop
  obtain ⟨_, _, _, side⟩ := leafSchema_left conditions rule
  obtain ⟨_, _, _, side'⟩ := leafSchema_left conditions rule'
  have equal := leafSchema_disjoint conditions rule rule'
    (ConstructorSystem.unifiable_of_leftSide side side' instantiation instantiation' same)
  obtain ⟨rfl, pairs⟩ := Sigma.mk.inj equal
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (eq_of_heq pairs)
  obtain rfl := leafSchema_instantiation conditions rule same
  rfl

/-- The leaf equations of case-tree definitions as a constructor system. -/
def leafSystem (defs : List (CaseTreeDefinition Head)) (conditions : LeafConditions defs) :
    System Head where
  schema := leafSchema defs
  defined := definedIn defs
  arity := arityOf defs
  left := leafSchema_left conditions
  linear := fun rule index => by rw [leafSchema_multiplicity conditions rule index]
  covered := fun rule index _ => by rw [leafSchema_multiplicity conditions rule index]; omega
  determined := leafSchema_determined conditions

/-- The case-tree computation is exactly the instances of the leaf equations. -/
theorem caseTreeComputation_iff_leafSchema (conditions : LeafConditions defs) {n : Nat}
    {t u : Tm Head n} :
    (caseTreeComputation defs).step t u ↔ SchemaStep (leafSchema defs) t u := by
  constructor
  · rintro ⟨d, mem, args, rfl, length, eval⟩
    have inScope : d.tree.Scoped (Pat.varsAll (List.replicate d.arity .var)) := by
      rw [Pat.varsAll_replicate]
      exact conditions.inScope d mem
    have hargs : args.length = Pat.varsAll (List.replicate d.arity .var) := by
      rw [Pat.varsAll_replicate, length]
    obtain ⟨N, vars, rhs, σ, leaf, same, rfl⟩ := (CaseTree.eval_iff_leaf inScope hargs).mp eval
    have hargs' : Pat.terms (List.replicate d.arity .var) args = args := by
      rw [← length]
      exact Pat.terms_replicate args
    rw [hargs', ← Pat.terms_subst] at same
    have e : appSpine (.const d.name) ((Pat.terms N (varTerms vars)).map (Presentation.subst σ)) =
        Presentation.subst σ (appSpine (.const d.name) (Pat.terms N (varTerms vars))) :=
      (subst_appSpine σ (.const d.name) _).symm
    rw [← same, e]
    exact SchemaStep.instantiate ⟨d, mem, N, leaf, rfl⟩ σ
  · intro step
    cases step with
    | @instantiate vars left right rule σ =>
        obtain ⟨d, mem, N, leaf, rfl⟩ := rule
        have hN := leafSchema_vars conditions mem leaf
        have inScope : d.tree.Scoped (Pat.varsAll (List.replicate d.arity .var)) := by
          rw [Pat.varsAll_replicate]
          exact conditions.inScope d mem
        have length : (Pat.terms N ((varTerms vars).map (Presentation.subst σ))).length =
            d.arity := by
          rw [Pat.fillAll_length, leaf.length, List.length_replicate]
        refine ⟨d, mem, Pat.terms N ((varTerms vars).map (Presentation.subst σ)), ?_, length,
          leaf.eval inScope rfl σ (by rw [length, Pat.varsAll_replicate]) ?_⟩
        · rw [subst_appSpine, Pat.terms_subst]
          rfl
        · conv => rhs; rw [← length]
          exact (Pat.terms_replicate _).symm

/-- A rule package computing by case-tree definitions, as a definition by
constructor patterns. -/
def caseTreePresentation {rules : Rules Head} (conditions : LeafConditions defs)
    (computation : ∀ {n : Nat} {t u : Tm Head n},
      rules.computation.step t u ↔ (caseTreeComputation defs).step t u)
    (symmetric : Std.Symm rules.headEq) : ConstructorSystem.ConstructorPresentation rules where
  presentation := SchemaFamily.presentation (leafSchema defs) rules
    (fun {_ _ _} => computation.trans (caseTreeComputation_iff_leafSchema conditions))
  system := leafSystem defs conditions
  same := fun _ _ => Iff.rfl
  symmetric := symmetric

/-- A rule package computing by case-tree definitions is Church–Rosser. -/
theorem caseTree_churchRosser {rules : Rules Head} (conditions : LeafConditions defs)
    (computation : ∀ {n : Nat} {t u : Tm Head n},
      rules.computation.step t u ↔ (caseTreeComputation defs).step t u)
    (symmetric : Std.Symm rules.headEq) : ChurchRosser rules :=
  (caseTreePresentation conditions computation symmetric).churchRosser

end LeafSystem

/-! ## Axiom audit -/

#print axioms Pat.compat_comm
#print axioms Pat.compat_of_splitAt
#print axioms Pat.compatAll_of_refines
#print axioms Pat.eq_of_compat_splitAt
#print axioms CaseTree.LeafOf.unique
#print axioms unifiable_appSpine_const
#print axioms Pat.compat_of_unifiable
#print axioms variableMultiplicity_appSpine
#print axioms Pat.variableMultiplicity_term
#print axioms varTerms_variableMultiplicity
#print axioms leafLeft_variableMultiplicity
#print axioms Pat.constructorsAll_replicate
#print axioms Pat.constructors_splitAt
#print axioms CaseBranches.constructors_find
#print axioms CaseTree.LeafOf.constructors
#print axioms pattern_appSpine_const
#print axioms Pat.pattern_term
#print axioms leftSide_appSpine
#print axioms arityOf_of_mem
#print axioms leafSchema_vars
#print axioms leafSchema_multiplicity
#print axioms leafSchema_left
#print axioms leafSchema_disjoint
#print axioms leafSchema_instantiation
#print axioms leafSchema_determined
#print axioms leafSystem
#print axioms caseTreeComputation_iff_leafSchema
#print axioms caseTreePresentation
#print axioms caseTree_churchRosser
#print axioms Pat.compatAll_comm
#print axioms Pat.compatAll_of_splitAllAt
#print axioms Pat.eq_of_compatAll_splitAllAt
#print axioms Pat.compatAll_of_unifiable
#print axioms Pat.variableMultiplicity_terms
#print axioms sum_map_zero
#print axioms Pat.constructorsAll_splitAllAt
#print axioms Pat.pattern_terms

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
