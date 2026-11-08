import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.SuperpositionSaturation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ResolutionFiring
import Mettapedia.Logic.LP.FirstOrderRewriting

/-!
# Superposition inferences as firings of the shared first-order step

Non-ground clauses live in the store of the first-order step, beside resolution goals: the
equation store of `FirstOrder.action` over the terms of a logic-programming signature, with clauses
encoded as terms by a clause former (`ClauseCode`). The firings are guarded firings
(`Superposition.guarded`), and resolution firings are guarded firings without guards
(`Superposition.lift`), so the two calculi share one store and interleave in one run.

## The firing that tells a unification

`unifyFiring reads l u made concl G`:

* it **reads** the stored premises (each read's pattern is the stored label, so reading binds
  nothing);
* it **tells** `l = u`, between terms of premises renamed apart;
* it **makes** the conclusion;
* it **guards** the closure of the side condition `G` over the unification (`Closure`): some
  unifier of `l` and `u` more general than the solution satisfies `G`.

**Admission** (`unifyFiring_admits_iff`): read at a principal answer `θ` of the knowledge (for
instance the total occurs-checked unifier's, `FirstOrder.accepted_principal`), with the told terms
fixed by `θ` (renamed apart from the knowledge, `fixed_of_apart`), the firing is admitted exactly when its premises are present, its made
occurrence is fresh and carries the conclusion, and some most general unifier `μ` of `l` and `u`
satisfies `G`. **The result's knowledge has the principal answer `μ ∘ θ`**
(`unifyFiring_principal`), so the made clause, read there, is the conclusion instantiated by `μ`.

## The rules

With a **stable ordering** on terms and literals (`StableOrder`: the strict orders survive
substitution, as KBO and LPO and their multiset extensions to literals do), the side conditions
are conjunctions of negated stable relations, hence co-stable (`CoStable`):

* **superposition** (`supConditions`, `supFiring`): `l ≈ r ∨ D'` into the side `c[u]` of `L` in
  `L ∨ C'`, `u` not a variable, telling `l = u`, making `L[c[r]] ∨ D' ∨ C'`;
* **equality resolution** (`eqResConditions`, `eqResFiring`): telling `s = t` for a maximal `s ≉ t`;
* **equality factoring** (`eqFactConditions`, `eqFactFiring`): telling `s = s'` for `s ≈ t` and
  `s' ≈ t'`;
* **binary resolution as the special case** (`resolutionFiring`): with atoms encoded as `P ≈ ⊤`,
  superposition of `P ≈ ⊤ ∨ D'` at the root of `Q ≉ ⊤ ∨ C'`, telling `P = Q` and making
  `⊤ ≉ ⊤ ∨ D' ∨ C'`; the literal `⊤ ≉ ⊤` is then deleted (`Simplification.deleteFalse` on ground
  instances, or equality resolution).

Each is admitted exactly when its premises are present, its conclusion is fresh, and its side
conditions hold at a most general unifier (`sup_admits_iff`, `eqRes_admits_iff`,
`eqFact_admits_iff`, `resolution_admits_iff`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Superposition

open Mettapedia.Logic.LP
open Resolution (A)

universe uO

variable {sig : LPSignature}

/-! ## Co-stable side conditions over the first-order action -/

section Readings

/-- **Every condition respects the first-order action**: solutions that act alike on terms are equal. -/
theorem respects_firstOrder (G : Subst sig → Prop) : Respects (A sig) G := by
  intro σ τ same
  have equal : σ = τ := funext fun v => same (.var v)
  rw [equal]

/-- The negation of a stable condition is co-stable. -/
theorem CoStable.not {P : Subst sig → Prop} (stable : Stable (A sig) P) :
    CoStable (A sig) fun τ => ¬ P τ :=
  fun ν σ notP holds => notP (stable ν σ holds)

theorem CoStable.and {P Q : Subst sig → Prop} (one : CoStable (A sig) P) (two : CoStable (A sig) Q) :
    CoStable (A sig) fun τ => P τ ∧ Q τ :=
  fun ν σ holds => ⟨one ν σ holds.1, two ν σ holds.2⟩

theorem CoStable.forall_mem {α : Type*} {l : List α} {P : α → Subst sig → Prop}
    (each : ∀ a ∈ l, CoStable (A sig) (P a)) : CoStable (A sig) fun τ => ∀ a ∈ l, P a τ :=
  fun ν σ holds a member => each a member ν σ (holds a member)

theorem CoStable.const (P : Prop) : CoStable (A sig) fun _ => P := fun _ _ holds => holds

end Readings

/-! ## Non-ground literals, clauses and the ordering -/

/-- **A non-ground literal**: an equation or a disequation, with the side named first that an
inference uses. -/
structure NLit (sig : LPSignature) where
  negative : Bool
  lhs : Term sig
  rhs : Term sig

/-- **A non-ground clause.** -/
abbrev NClause (sig : LPSignature) := List (NLit sig)

def NLit.subst (τ : Subst sig) (L : NLit sig) : NLit sig := ⟨L.negative, τ.applyTerm L.lhs, τ.applyTerm L.rhs⟩

def NClause.subst (τ : Subst sig) (C : NClause sig) : NClause sig := C.map (NLit.subst τ)

theorem NLit.subst_comp (ν τ : Subst sig) (L : NLit sig) :
    L.subst (ν ∘ₛ τ) = (L.subst τ).subst ν := by
  simp only [NLit.subst, Subst.applyTerm_comp]

/-- **A clause former**: clauses encoded as terms, compatibly with substitution. -/
structure ClauseCode (sig : LPSignature) where
  encode : NClause sig → Term sig
  encode_subst : ∀ (τ : Subst sig) (C : NClause sig), τ.applyTerm (encode C) = encode (C.subst τ)

/-- **A stable ordering** on terms and on literals: both strict orders survive substitution. The
Knuth–Bendix and lexicographic path orderings, with the multiset extension to literals, are
stable. -/
structure StableOrder (sig : LPSignature) where
  gt : Term sig → Term sig → Prop
  gt_subst : ∀ (τ : Subst sig) (s t : Term sig), gt s t → gt (τ.applyTerm s) (τ.applyTerm t)
  litGt : NLit sig → NLit sig → Prop
  litGt_subst : ∀ (τ : Subst sig) (L M : NLit sig), litGt L M → litGt (L.subst τ) (M.subst τ)

namespace StableOrder

variable (ord : StableOrder sig)

def ge (s t : Term sig) : Prop := ord.gt s t ∨ s = t

def litGe (L M : NLit sig) : Prop := ord.litGt L M ∨ L = M

/-- `s ⪰ t` at a solution. -/
def geAt (s t : Term sig) (τ : Subst sig) : Prop := ord.ge (τ.applyTerm s) (τ.applyTerm t)

def litGeAt (L M : NLit sig) (τ : Subst sig) : Prop := ord.litGe (L.subst τ) (M.subst τ)

def litGtAt (L M : NLit sig) (τ : Subst sig) : Prop := ord.litGt (L.subst τ) (M.subst τ)

theorem geAt_stable (s t : Term sig) : Stable (A sig) (ord.geAt s t) := by
  intro ν σ holds
  show ord.ge ((ν ∘ₛ σ).applyTerm s) ((ν ∘ₛ σ).applyTerm t)
  rw [Subst.applyTerm_comp, Subst.applyTerm_comp]
  rcases holds with gt | same
  · exact Or.inl (ord.gt_subst ν _ _ gt)
  · exact Or.inr (congrArg ν.applyTerm same)

theorem litGeAt_stable (L M : NLit sig) : Stable (A sig) (ord.litGeAt L M) := by
  intro ν σ holds
  show ord.litGe (L.subst (ν ∘ₛ σ)) (M.subst (ν ∘ₛ σ))
  rw [NLit.subst_comp, NLit.subst_comp]
  rcases holds with gt | same
  · exact Or.inl (ord.litGt_subst ν _ _ gt)
  · exact Or.inr (congrArg (NLit.subst ν) same)

theorem litGtAt_stable (L M : NLit sig) : Stable (A sig) (ord.litGtAt L M) := by
  intro ν σ holds
  show ord.litGt (L.subst (ν ∘ₛ σ)) (M.subst (ν ∘ₛ σ))
  rw [NLit.subst_comp, NLit.subst_comp]
  exact ord.litGt_subst ν _ _ holds

end StableOrder

/-! ## The firing that tells a unification -/

section Firing

variable {O : Type uO} [DecidableEq O] (label : O → Term sig)

/-- **An inference that tells a unification**: it reads the stored premises, tells `l = u`, makes the
conclusion, and guards the closure of `G` over the unification. -/
def unifyFiring (reads : List (O × Term sig)) (l u : Term sig) (made : O) (concl : Term sig)
    (G : Subst sig → Prop) : GuardedFiring (Term sig) (Subst sig) O :=
  ⟨⟨⟨[], reads.map Prod.snd, [(l, u)], [], [concl]⟩, [], ⟨[], reads.map Prod.fst, [made]⟩⟩,
    [Closure (A sig) [(l, u)] G]⟩

omit [DecidableEq O] in
theorem unifyFiring_problem (C : Configuration (Term sig) O) (reads : List (O × Term sig)) (l u : Term sig)
    (made : O) (concl : Term sig) (G : Subst sig → Prop) :
    (unifyFiring reads l u made concl G).firing.selection.problem label
        (unifyFiring reads l u made concl G).firing.rule C =
      C.equations ++ ((reads.map fun p => (p.2, label p.1)) ++ [(l, u)]) := by
  show C.equations ++ [] ++ Selection.equations label (reads.map Prod.snd) (reads.map Prod.fst) ++ [(l, u)] = _
  rw [pairs_eq label reads]
  simp

omit [DecidableEq O] in
/-- With stored premises, a solution of the information is a solution of the knowledge that unifies
the told terms. -/
theorem unifyFiring_models_iff (C : Configuration (Term sig) O) {reads : List (O × Term sig)}
    (stored : ∀ p ∈ reads, label p.1 = p.2) (l u : Term sig) (made : O) (concl : Term sig)
    (G : Subst sig → Prop) (τ : Subst sig) :
    (A sig).Models τ ((unifyFiring reads l u made concl G).firing.selection.problem label
        (unifyFiring reads l u made concl G).firing.rule C) ↔
      (A sig).Models τ C.equations ∧ τ.applyTerm l = τ.applyTerm u := by
  rw [unifyFiring_problem, SubstitutionAction.models_append, SubstitutionAction.models_append]
  constructor
  · rintro ⟨knowledge, -, told⟩
    exact ⟨knowledge, told (l, u) List.mem_cons_self⟩
  · rintro ⟨knowledge, told⟩
    refine ⟨knowledge, fun e member => ?_, fun e member => ?_⟩
    · obtain ⟨p, inReads, rfl⟩ := List.mem_map.mp member
      show τ.applyTerm p.2 = τ.applyTerm (label p.1)
      rw [stored p inReads]
    · rw [List.mem_singleton.mp member]
      exact told

theorem fixed_of_apart [DecidableEq sig.vars] [DecidableEq sig.constants]
    [DecidableEq sig.functionSymbols] {K : EquationStore (Term sig)} {θ : Subst sig}
    (solved : unifyTotal K = some θ) {t : Term sig} (apart : ∀ x ∈ t.freeVars, x ∉ eqVars K) :
    θ.applyTerm t = t :=
  Resolution.relevant_fixes (unifyTotal_relevantIdempotent K θ solved) apart

variable [DecidableEq sig.vars] [DecidableEq sig.constants] [DecidableEq sig.functionSymbols]

/-- **Admission of a firing that tells a unification**: its premises are present, its made occurrence
is fresh and carries the conclusion, and some most general unifier of the told terms satisfies the
side condition. -/
theorem unifyFiring_admits_iff {C : Configuration (Term sig) O} {θ : Subst sig}
    (principal : (A sig).Principal C.equations θ) {reads : List (O × Term sig)}
    (stored : ∀ p ∈ reads, label p.1 = p.2) {l u : Term sig}
    (fixed : θ.applyTerm l = l ∧ θ.applyTerm u = u) (made : O) (concl : Term sig)
    {G : Subst sig → Prop} (coStable : CoStable (A sig) G) :
    (guarded (A sig) label).Admits (s := C) (unifyFiring reads l u made concl G) ↔
      (∀ p ∈ reads, p.1 ∈ C.present) ∧ made ∉ C.present ∧ label made = concl ∧
        ∃ μ : Subst sig, (A sig).Principal [(l, u)] μ ∧ G μ := by
  have models := unifyFiring_models_iff label C stored l u made concl G
  have respects := respects_firstOrder G
  -- the composite of a unifier with the knowledge's answer solves the information
  have composite : ∀ μ : Subst sig, μ.applyTerm l = μ.applyTerm u →
      (A sig).Models (μ ∘ₛ θ) ((unifyFiring reads l u made concl G).firing.selection.problem label
        (unifyFiring reads l u made concl G).firing.rule C) := by
    intro μ unifies
    refine (models _).mpr ⟨SubstitutionAction.Principal.extension_models (A sig) principal μ, ?_⟩
    rw [Subst.applyTerm_comp, Subst.applyTerm_comp, fixed.1, fixed.2]
    exact unifies
  constructor
  · rintro ⟨⟨⟨-, -, -, -, outputs, occurrences, ⟨τ, solvedτ⟩, -⟩, -⟩, asked⟩
    obtain ⟨-, toldτ⟩ := (models τ).mp solvedτ
    obtain ⟨μ, accepted⟩ := (FirstOrder.accepted_iff_consistent [(l, u)]).mpr
      ⟨τ, (SubstitutionAction.models_cons _ _ _ _).mpr ⟨toldτ, SubstitutionAction.models_nil _ _⟩⟩
    have principalμ : (A sig).Principal [(l, u)] μ := FirstOrder.accepted_principal _ μ accepted
    have unifies : μ.applyTerm l = μ.applyTerm u := principalμ.sound (l, u) List.mem_cons_self
    obtain ⟨τ₀, solved₀, -, holds₀⟩ := asked (μ ∘ₛ θ) (composite μ unifies) _ List.mem_cons_self
    obtain ⟨ν, through⟩ := principalμ.factors τ₀ solved₀
    refine ⟨fun p member => occurrences.kept_subset
      (List.mem_toFinset.mpr (List.mem_map.mpr ⟨p, member, rfl⟩)), ?_, ?_, μ, principalμ, ?_⟩
    · exact Finset.disjoint_left.mp occurrences.fresh (by simp [Selection.commit, unifyFiring])
    · simpa [unifyFiring] using outputs
    · exact coStable ν μ ((respects_factor respects through).mp holds₀)
  · rintro ⟨present, fresh, made_label, μ, principalμ, holds⟩
    have unifies : μ.applyTerm l = μ.applyTerm u := principalμ.sound (l, u) List.mem_cons_self
    refine ⟨⟨⟨List.nodup_nil, List.nodup_singleton _, rfl, by simp [unifyFiring], ?_,
      ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨μ ∘ₛ θ, composite μ unifies⟩, ?_⟩, ?_⟩, ?_⟩
    · simp [unifyFiring, made_label]
    · intro o member
      simp [Selection.commit, unifyFiring] at member
    · intro o member
      obtain ⟨p, inReads, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
      exact present p inReads
    · simp [Selection.commit, unifyFiring]
    · refine Finset.disjoint_left.mpr fun {o} member inC => ?_
      have same : o = made := by simpa [Selection.commit, unifyFiring] using member
      exact fresh (same ▸ inC)
    · intro query member
      cases member
    · intro check member
      cases member
    · intro query member
      cases member
    · intro τ solvedτ g member
      simp only [unifyFiring, List.mem_singleton] at member
      subst member
      obtain ⟨-, toldτ⟩ := (models τ).mp solvedτ
      obtain ⟨ν, through⟩ := principalμ.factors τ
        ((SubstitutionAction.models_cons _ _ _ _).mpr ⟨toldτ, SubstitutionAction.models_nil _ _⟩)
      exact ⟨μ, principalμ.sound, ⟨ν, through⟩, holds⟩

omit [DecidableEq sig.vars] [DecidableEq sig.constants] [DecidableEq sig.functionSymbols] in
/-- **The result's knowledge has the principal answer `μ ∘ θ`**, and the made conclusion read there is
the conclusion instantiated by `μ`. -/
theorem unifyFiring_principal {C : Configuration (Term sig) O} {θ : Subst sig}
    (principal : (A sig).Principal C.equations θ) {reads : List (O × Term sig)}
    (stored : ∀ p ∈ reads, label p.1 = p.2) {l u : Term sig}
    (fixed : θ.applyTerm l = l ∧ θ.applyTerm u = u) (made : O) {concl : Term sig}
    (conclFixed : θ.applyTerm concl = concl) {G : Subst sig → Prop} {μ : Subst sig}
    (principalμ : (A sig).Principal [(l, u)] μ) :
    (A sig).Principal ((unifyFiring reads l u made concl G).firing.result label C).equations (μ ∘ₛ θ) ∧
      (μ ∘ₛ θ).applyTerm concl = μ.applyTerm concl := by
  refine ⟨?_, by rw [Subst.applyTerm_comp, conclFixed]⟩
  show (A sig).Principal ((unifyFiring reads l u made concl G).firing.selection.problem label
    (unifyFiring reads l u made concl G).firing.rule C) (μ ∘ₛ θ)
  rw [unifyFiring_problem]
  refine SubstitutionAction.Principal.compose (A sig) principal ⟨?_, ?_⟩
  · intro e member
    rw [SubstitutionAction.applyStore, List.map_append, List.mem_append] at member
    rcases member with inReads | told
    · obtain ⟨e', inMap, rfl⟩ := List.mem_map.mp inReads
      obtain ⟨p, inP, rfl⟩ := List.mem_map.mp inMap
      show μ.applyTerm (θ.applyTerm p.2) = μ.applyTerm (θ.applyTerm (label p.1))
      rw [stored p inP]
    · simp only [List.map_cons, List.map_nil, List.mem_singleton] at told
      subst told
      show μ.applyTerm (θ.applyTerm l) = μ.applyTerm (θ.applyTerm u)
      rw [fixed.1, fixed.2]
      exact principalμ.sound (l, u) List.mem_cons_self
  · intro δ solvedδ
    refine principalμ.factors δ ?_
    have told := solvedδ (θ.applyTerm l, θ.applyTerm u)
      (by
        rw [SubstitutionAction.applyStore, List.map_append]
        exact List.mem_append_right _ (List.mem_map.mpr ⟨(l, u), List.mem_singleton.mpr rfl, rfl⟩))
    rw [fixed.1, fixed.2] at told
    exact (SubstitutionAction.models_cons _ _ _ _).mpr ⟨told, SubstitutionAction.models_nil _ _⟩

end Firing

/-! ## The rules -/

section Rules

variable (ord : StableOrder sig)

/-- The positive literal `l ≈ r`. -/
def posLit (l r : Term sig) : NLit sig := ⟨false, l, r⟩

/-- **The side conditions of superposition** of `l ≈ r ∨ D'` into the side `L.lhs = c[u]` of the
literal `L` of `L ∨ C'`, at a solution: `u` is not a variable, `r ⋡ l`, `L.rhs ⋡ L.lhs`, `l ≈ r`
strictly maximal in its premise, and `L` strictly maximal and above `l ≈ r` when positive, maximal
when negative. -/
def supConditions (u l r : Term sig) (D' : NClause sig) (L : NLit sig) (C' : NClause sig)
    (τ : Subst sig) : Prop :=
  (∀ x, u ≠ .var x) ∧ ¬ ord.geAt r l τ ∧ ¬ ord.geAt L.rhs L.lhs τ ∧
    (∀ M ∈ D', ¬ ord.litGeAt M (posLit l r) τ) ∧
    (L.negative = true → ∀ M ∈ C', ¬ ord.litGtAt M L τ) ∧
    (L.negative = false → (∀ M ∈ C', ¬ ord.litGeAt M L τ) ∧ ¬ ord.litGeAt (posLit l r) L τ)

theorem supConditions_coStable (u l r : Term sig) (D' : NClause sig) (L : NLit sig) (C' : NClause sig) :
    CoStable (A sig) (supConditions ord u l r D' L C') := by
  rintro ν σ ⟨notVar, noR, noL, sideMax, negMax, posMax⟩
  exact ⟨notVar, fun h => noR (ord.geAt_stable r l ν σ h), fun h => noL (ord.geAt_stable _ _ ν σ h),
    fun M member h => sideMax M member (ord.litGeAt_stable M _ ν σ h),
    fun negative M member h => negMax negative M member (ord.litGtAt_stable M L ν σ h),
    fun positive => ⟨fun M member h => (posMax positive).1 M member (ord.litGeAt_stable M L ν σ h),
      fun h => (posMax positive).2 (ord.litGeAt_stable _ L ν σ h)⟩⟩

/-- The conclusion of superposition: `L` with `c[r]` in place of `c[u]`, then `D'` and `C'`. -/
def supConclusion (c : FirstOrderRewriting.Context sig) (r : Term sig) (D' : NClause sig) (L : NLit sig)
    (C' : NClause sig) : NClause sig :=
  ⟨L.negative, c.fill r, L.rhs⟩ :: (D' ++ C')

variable {O : Type uO} [DecidableEq O] (label : O → Term sig) (code : ClauseCode sig)

/-- **Superposition as a firing**: read both premises, tell `l = u`, make the conclusion, guard the
side conditions. -/
def supFiring (side main : O × Term sig) (made : O) (c : FirstOrderRewriting.Context sig)
    (u l r : Term sig) (D' : NClause sig) (L : NLit sig) (C' : NClause sig) :
    GuardedFiring (Term sig) (Subst sig) O :=
  unifyFiring [side, main] l u made (code.encode (supConclusion c r D' L C')) (supConditions ord u l r D' L C')

/-- The side conditions of equality resolution on the maximal literal `L = (s ≉ t)` of `L ∨ C'`. -/
def eqResConditions (L : NLit sig) (C' : NClause sig) (τ : Subst sig) : Prop :=
  L.negative = true ∧ ∀ M ∈ C', ¬ ord.litGtAt M L τ

theorem eqResConditions_coStable (L : NLit sig) (C' : NClause sig) :
    CoStable (A sig) (eqResConditions ord L C') := by
  rintro ν σ ⟨negative, maximal⟩
  exact ⟨negative, fun M member h => maximal M member (ord.litGtAt_stable M L ν σ h)⟩

/-- **Equality resolution as a firing**: read the premise, tell `s = t`, make `C'`. -/
def eqResFiring (main : O × Term sig) (made : O) (L : NLit sig) (C' : NClause sig) :
    GuardedFiring (Term sig) (Subst sig) O :=
  unifyFiring [main] L.lhs L.rhs made (code.encode C') (eqResConditions ord L C')

/-- The side conditions of equality factoring of `L = (s ≈ t)` and `L' = (s' ≈ t')` in `L ∨ L' ∨ C'`:
`t ⋡ s`, and `L` maximal. -/
def eqFactConditions (L L' : NLit sig) (C' : NClause sig) (τ : Subst sig) : Prop :=
  L.negative = false ∧ L'.negative = false ∧ ¬ ord.geAt L.rhs L.lhs τ ∧
    ∀ M ∈ L' :: C', ¬ ord.litGtAt M L τ

theorem eqFactConditions_coStable (L L' : NLit sig) (C' : NClause sig) :
    CoStable (A sig) (eqFactConditions ord L L' C') := by
  rintro ν σ ⟨positive, positive', noR, maximal⟩
  exact ⟨positive, positive', fun h => noR (ord.geAt_stable _ _ ν σ h),
    fun M member h => maximal M member (ord.litGtAt_stable M L ν σ h)⟩

/-- The conclusion of equality factoring: `t ≉ t' ∨ s' ≈ t' ∨ C'`. -/
def eqFactConclusion (L L' : NLit sig) (C' : NClause sig) : NClause sig :=
  ⟨true, L.rhs, L'.rhs⟩ :: L' :: C'

/-- **Equality factoring as a firing**: read the premise, tell `s = s'`, make the conclusion. -/
def eqFactFiring (main : O × Term sig) (made : O) (L L' : NLit sig) (C' : NClause sig) :
    GuardedFiring (Term sig) (Subst sig) O :=
  unifyFiring [main] L.lhs L'.lhs made (code.encode (eqFactConclusion L L' C')) (eqFactConditions ord L L' C')

/-- **Binary resolution as the special case**: atoms are encoded as `P ≈ ⊤`; superposition of
`P ≈ ⊤ ∨ D'` at the root of `Q ≉ ⊤ ∨ C'` tells `P = Q` and makes `⊤ ≉ ⊤ ∨ D' ∨ C'`. -/
def resolutionFiring (top : Term sig) (side main : O × Term sig) (made : O) (P Q : Term sig)
    (D' C' : NClause sig) : GuardedFiring (Term sig) (Subst sig) O :=
  supFiring ord code side main made .hole Q P top D' ⟨true, Q, top⟩ C'

theorem resolution_conclusion (top : Term sig) (D' C' : NClause sig) (Q : Term sig) :
    supConclusion .hole top D' ⟨true, Q, top⟩ C' = ⟨true, top, top⟩ :: (D' ++ C') :=
  rfl

variable [DecidableEq sig.vars] [DecidableEq sig.constants] [DecidableEq sig.functionSymbols]

/-- **Superposition is admitted exactly at its side conditions**: both premises present, the made
occurrence fresh and carrying the conclusion, and the side conditions at a most general unifier of
`l` and `u`. -/
theorem sup_admits_iff {C : Configuration (Term sig) O} {θ : Subst sig}
    (principal : (A sig).Principal C.equations θ) {side main : O × Term sig}
    (stored : label side.1 = side.2 ∧ label main.1 = main.2) {u l r : Term sig}
    (fixed : θ.applyTerm l = l ∧ θ.applyTerm u = u) (made : O) (c : FirstOrderRewriting.Context sig)
    (D' : NClause sig) (L : NLit sig) (C' : NClause sig) :
    (guarded (A sig) label).Admits (s := C) (supFiring ord code side main made c u l r D' L C') ↔
      side.1 ∈ C.present ∧ main.1 ∈ C.present ∧ made ∉ C.present ∧
        label made = code.encode (supConclusion c r D' L C') ∧
        ∃ μ : Subst sig, (A sig).Principal [(l, u)] μ ∧ supConditions ord u l r D' L C' μ := by
  rw [supFiring, unifyFiring_admits_iff label principal (by simpa using stored) fixed made _
    (supConditions_coStable ord u l r D' L C')]
  constructor
  · rintro ⟨present, rest⟩
    exact ⟨present side List.mem_cons_self, present main (List.mem_cons_of_mem _ List.mem_cons_self), rest⟩
  · rintro ⟨inSide, inMain, rest⟩
    refine ⟨fun p member => ?_, rest⟩
    rcases List.mem_cons.mp member with rfl | member
    · exact inSide
    · rw [List.mem_singleton.mp member]
      exact inMain

theorem eqRes_admits_iff {C : Configuration (Term sig) O} {θ : Subst sig}
    (principal : (A sig).Principal C.equations θ) {main : O × Term sig} (stored : label main.1 = main.2)
    {L : NLit sig} (fixed : θ.applyTerm L.lhs = L.lhs ∧ θ.applyTerm L.rhs = L.rhs) (made : O)
    (C' : NClause sig) :
    (guarded (A sig) label).Admits (s := C) (eqResFiring ord code main made L C') ↔
      main.1 ∈ C.present ∧ made ∉ C.present ∧ label made = code.encode C' ∧
        ∃ μ : Subst sig, (A sig).Principal [(L.lhs, L.rhs)] μ ∧ eqResConditions ord L C' μ := by
  rw [eqResFiring, unifyFiring_admits_iff label principal (by simpa using stored) fixed made _
    (eqResConditions_coStable ord L C')]
  constructor
  · rintro ⟨present, rest⟩
    exact ⟨present main (List.mem_singleton.mpr rfl), rest⟩
  · rintro ⟨inMain, rest⟩
    exact ⟨fun p member => by rw [List.mem_singleton.mp member]; exact inMain, rest⟩

theorem eqFact_admits_iff {C : Configuration (Term sig) O} {θ : Subst sig}
    (principal : (A sig).Principal C.equations θ) {main : O × Term sig} (stored : label main.1 = main.2)
    {L L' : NLit sig} (fixed : θ.applyTerm L.lhs = L.lhs ∧ θ.applyTerm L'.lhs = L'.lhs) (made : O)
    (C' : NClause sig) :
    (guarded (A sig) label).Admits (s := C) (eqFactFiring ord code main made L L' C') ↔
      main.1 ∈ C.present ∧ made ∉ C.present ∧ label made = code.encode (eqFactConclusion L L' C') ∧
        ∃ μ : Subst sig, (A sig).Principal [(L.lhs, L'.lhs)] μ ∧ eqFactConditions ord L L' C' μ := by
  rw [eqFactFiring, unifyFiring_admits_iff label principal (by simpa using stored) fixed made _
    (eqFactConditions_coStable ord L L' C')]
  constructor
  · rintro ⟨present, rest⟩
    exact ⟨present main (List.mem_singleton.mpr rfl), rest⟩
  · rintro ⟨inMain, rest⟩
    exact ⟨fun p member => by rw [List.mem_singleton.mp member]; exact inMain, rest⟩

/-- **Binary resolution is admitted exactly at its side conditions**: the atoms unify, and the
ordering conditions hold at a most general unifier. -/
theorem resolution_admits_iff {C : Configuration (Term sig) O} {θ : Subst sig}
    (principal : (A sig).Principal C.equations θ) (top : Term sig) {side main : O × Term sig}
    (stored : label side.1 = side.2 ∧ label main.1 = main.2) {P Q : Term sig}
    (fixed : θ.applyTerm P = P ∧ θ.applyTerm Q = Q) (made : O) (D' C' : NClause sig) :
    (guarded (A sig) label).Admits (s := C) (resolutionFiring ord code top side main made P Q D' C') ↔
      side.1 ∈ C.present ∧ main.1 ∈ C.present ∧ made ∉ C.present ∧
        label made = code.encode (⟨true, top, top⟩ :: (D' ++ C')) ∧
        ∃ μ : Subst sig, (A sig).Principal [(P, Q)] μ ∧
          supConditions ord Q P top D' ⟨true, Q, top⟩ C' μ :=
  sup_admits_iff ord label code principal stored fixed made .hole D' ⟨true, Q, top⟩ C'

end Rules

#print axioms respects_firstOrder
#print axioms CoStable.not
#print axioms StableOrder.geAt_stable
#print axioms StableOrder.litGeAt_stable
#print axioms unifyFiring_problem
#print axioms unifyFiring_models_iff
#print axioms fixed_of_apart
#print axioms unifyFiring_admits_iff
#print axioms unifyFiring_principal
#print axioms supConditions_coStable
#print axioms eqResConditions_coStable
#print axioms eqFactConditions_coStable
#print axioms sup_admits_iff
#print axioms eqRes_admits_iff
#print axioms eqFact_admits_iff
#print axioms resolution_admits_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Superposition
