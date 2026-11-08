import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.SuperpositionFiring
import Mettapedia.Logic.LP.Semantics

/-!
# Lifting superposition: ground instances, the order link, and the lifting lemma

Non-ground clauses (`NClause`) have ground instances under groundings (`NClause.ground`): each
literal becomes the oriented ground literal of its two instantiated sides. This module connects the
non-ground inferences of `SuperpositionFiring` to the ground calculus of `SuperpositionGround`.

## The order link

`GroundedOrder` extends a stable ordering (`StableOrder`) by the **order link**: for every grounding
`θ`, `s ≻ t` implies `sθ > tθ` in the ground ordering, and likewise for literals. Nothing else is
asked of the non-ground ordering: it need not be total, well founded, or a simplification ordering;
those properties belong to the ground ordering (`GroundSimplification`, a linear order, and
`WellFoundedLT`). The link follows from stability and the **ground restriction** (`ofRestriction`):
on ground terms the non-ground ordering is contained in the ground one. The Knuth–Bendix and
lexicographic path orderings with a total precedence satisfy both: they are stable, and their
restriction to ground terms is the ground ordering; their multiset extension to literals is stable,
and on ground literals it is the Bachmair–Ganzinger literal ordering (`Lit.lt_iff_multiset`).

* `ofTermOrder`: a linked term ordering gives a linked literal ordering (each side of the smaller
  literal lies below a side of the larger one).
* `subtermOrder`: the strict subterm ordering is linked to every ground simplification ordering.

## The lifting lemma

Take a ground inference whose premises are the instances `Dθ`, `Cθ` of variable-disjoint clauses.

* **Positions** (`position_split`): a position of `Lθ.lhs` is either the instance of a non-variable
  position of the non-ground side `L.lhs = c[u]`, or lies at or below a variable `x` of it.
* **Unifiers** (`exists_mgu`): `θ` unifies the told terms, so a most general unifier `μ` exists, and
  `θ` factors through it: `θ = ν ∘ μ` (`groundAfter ν μ = θ`).
* **The side conditions** hold at `θ` read as a substitution (`supConditions_of_ground`, by the order
  link), hence at `μ` by co-stability; this is where the closure guard is needed
  (`closure_guard_of_grounding`): asked at every solution, the closure holds exactly when the
  condition holds at `μ` (`entails_closure_iff`), while the bare condition can fail at instances of
  `μ`.
* **The four rules**: `lift_posSup`, `lift_negSup` (with the variable case split off as `AtVariable`),
  `lift_eqRes`, `lift_eqFact`. Each produces the parameters of the non-ground firing (`SupLift`,
  `EqResLift`, `EqFactLift`), whose conclusion has `E` as its instance.
* **On the shared store** (`SupLift.admitted`, `EqResLift.admitted`, `EqFactLift.admitted`): the firing is
  admitted, the result's knowledge has the principal answer `μ ∘ θ₀`, and the made clause read there
  has the ground conclusion as an instance.
* **Without renaming apart** (`unifyFiring_admits_of_consistent`): an inference on a derived clause tells
  terms that the knowledge already binds; it is admitted when some solution of the knowledge solves
  the told equation and the side condition holds at a most general unifier of the told terms.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Superposition

open Mettapedia.Logic.LP
open Resolution (A)

universe uO

variable {sig : LPSignature}

/-! ## Groundings -/

section Groundings

/-- A ground term read as a term grounds back to itself. -/
theorem ground_toTerm (θ : Grounding sig) (g : GroundTerm sig) : θ.groundTerm g.toTerm = g := by
  induction g with
  | const _ => rfl
  | app f args ih => simp only [GroundTerm.toTerm, Grounding.groundTerm, ih]

/-- **A grounding after a substitution.** -/
def groundAfter (θ : Grounding sig) (σ : Subst sig) : Grounding sig := fun v => θ.groundTerm (σ v)

theorem groundTerm_applyTerm (θ : Grounding sig) (σ : Subst sig) (t : Term sig) :
    θ.groundTerm (σ.applyTerm t) = (groundAfter θ σ).groundTerm t := by
  induction t with
  | var _ => rfl
  | const _ => rfl
  | app f ts ih => simp only [Subst.applyTerm, Grounding.groundTerm, ih]

theorem groundAfter_toSubst (g θ : Grounding sig) : groundAfter g θ.toSubst = θ :=
  funext fun v => ground_toTerm g (θ v)

theorem groundTerm_toSubst (g θ : Grounding sig) (t : Term sig) :
    g.groundTerm (θ.toSubst.applyTerm t) = θ.groundTerm t := by
  rw [groundTerm_applyTerm, groundAfter_toSubst]

/-- **`θ` factors through `μ`**: from `θ = ν ∘ μ` as substitutions, a grounding `ν'` with `ν' ∘ μ = θ`. -/
theorem groundAfter_factors (θ : Grounding sig) {μ ν : Subst sig} (through : θ.toSubst = ν ∘ₛ μ) :
    groundAfter (groundAfter θ ν) μ = θ := by
  funext v
  show (groundAfter θ ν).groundTerm (μ v) = θ v
  rw [← groundTerm_applyTerm]
  show θ.groundTerm ((ν ∘ₛ μ) v) = θ v
  rw [← through]
  exact ground_toTerm θ (θ v)

variable [DecidableEq sig.vars] [DecidableEq sig.constants] [DecidableEq sig.functionSymbols]

/-- **A unifier exists, and `θ` factors through it**: if `θ` grounds `s` and `t` alike, they have a
most general unifier `μ`, and `θ` read as a substitution is `ν ∘ μ`. -/
theorem exists_mgu (θ : Grounding sig) {s t : Term sig} (unifies : θ.groundTerm s = θ.groundTerm t) :
    ∃ μ : Subst sig, (A sig).Principal [(s, t)] μ ∧ ∃ ν : Subst sig, θ.toSubst = ν ∘ₛ μ := by
  have solved : (A sig).Models θ.toSubst [(s, t)] := by
    intro e member
    rw [List.mem_singleton.mp member]
    show θ.toSubst.applyTerm s = θ.toSubst.applyTerm t
    rw [← Grounding.groundTerm_toTerm, ← Grounding.groundTerm_toTerm, unifies]
  obtain ⟨μ, accepted⟩ := (FirstOrder.accepted_iff_consistent [(s, t)]).mpr ⟨θ.toSubst, solved⟩
  have principal := FirstOrder.accepted_principal _ μ accepted
  obtain ⟨ν, through⟩ := principal.factors θ.toSubst solved
  exact ⟨μ, principal, ν, funext fun v => through (.var v)⟩

end Groundings

/-! ## Reorientations of non-ground clauses -/

section Reorientations

/-- The literal with its sides exchanged. -/
def NLit.flip (L : NLit sig) : NLit sig := ⟨L.negative, L.rhs, L.lhs⟩

/-- **A reorientation**: `X` is `Y` up to the order of its literals and the orientation of each. -/
def Reorient (X Y : NClause sig) : Prop :=
  ∃ Z : NClause sig, Z.Perm Y ∧ List.Forall₂ (fun L M => L = M ∨ L = M.flip) X Z

theorem Reorient.middle {K L : NLit sig} (choice : K = L ∨ K = L.flip) (s t : NClause sig) :
    Reorient (K :: (s ++ t)) (s ++ L :: t) :=
  ⟨L :: (s ++ t), List.perm_middle.symm,
    List.Forall₂.cons choice (List.forall₂_same.mpr fun _ _ => Or.inl rfl)⟩

theorem Reorient.middle₂ {K K' L L' : NLit sig} (choice : K = L ∨ K = L.flip)
    (choice' : K' = L' ∨ K' = L'.flip) {s t s' t' : NClause sig} (same : s ++ t = s' ++ L' :: t') :
    Reorient (K :: K' :: (s' ++ t')) (s ++ L :: t) := by
  refine ⟨L :: L' :: (s' ++ t'), ?_,
    List.Forall₂.cons choice (List.Forall₂.cons choice' (List.forall₂_same.mpr fun _ _ => Or.inl rfl))⟩
  have inner : (L' :: (s' ++ t')).Perm (s ++ t) := by rw [same]; exact List.perm_middle.symm
  exact (List.Perm.cons L inner).trans List.perm_middle.symm

theorem forall₂_sides : ∀ {X Z : NClause sig}, List.Forall₂ (fun L M => L = M ∨ L = M.flip) X Z →
    ∀ {K : NLit sig}, K ∈ X → ∃ M ∈ Z, (K.lhs = M.lhs ∧ K.rhs = M.rhs) ∨ (K.lhs = M.rhs ∧ K.rhs = M.lhs)
  | _, _, .nil, _, member => by cases member
  | _, _, .cons (a := a) (b := b) choice rest, K, member => by
      rcases List.mem_cons.mp member with same | inRest
      · subst same
        refine ⟨b, List.mem_cons_self, ?_⟩
        rcases choice with same | same
        · subst same; exact Or.inl ⟨rfl, rfl⟩
        · subst same; exact Or.inr ⟨rfl, rfl⟩
      · obtain ⟨M, inZ, sides⟩ := forall₂_sides rest inRest
        exact ⟨M, List.mem_cons_of_mem _ inZ, sides⟩

/-- The sides of a literal of a reorientation are the sides of a literal of the original. -/
theorem Reorient.sides {X Y : NClause sig} (reorient : Reorient X Y) {K : NLit sig} (member : K ∈ X) :
    ∃ M ∈ Y, (K.lhs = M.lhs ∧ K.rhs = M.rhs) ∨ (K.lhs = M.rhs ∧ K.rhs = M.lhs) := by
  obtain ⟨Z, perm, pointwise⟩ := reorient
  obtain ⟨M, inZ, sides⟩ := forall₂_sides pointwise member
  exact ⟨M, perm.subset inZ, sides⟩

end Reorientations

/-! ## Ground instances of literals and clauses -/

section Instances

variable [LinearOrder (GroundTerm sig)]

/-- **The ground instance of a literal**: the oriented ground literal of its instantiated sides. -/
def NLit.ground (θ : Grounding sig) (L : NLit sig) : Lit (GroundTerm sig) :=
  Lit.make L.negative (θ.groundTerm L.lhs) (θ.groundTerm L.rhs)

theorem NLit.ground_negative (θ : Grounding sig) (L : NLit sig) : (L.ground θ).negative = L.negative := rfl

theorem NLit.ground_flip (θ : Grounding sig) (L : NLit sig) : L.flip.ground θ = L.ground θ :=
  Lit.ext (max_comm _ _) rfl (min_comm _ _)

theorem NLit.ground_of_choice {θ : Grounding sig} {K L : NLit sig} (choice : K = L ∨ K = L.flip) :
    K.ground θ = L.ground θ := by
  rcases choice with same | same
  · rw [same]
  · rw [same]; exact NLit.ground_flip θ L

theorem NLit.ground_subst (θ : Grounding sig) (σ : Subst sig) (L : NLit sig) :
    (L.subst σ).ground θ = L.ground (groundAfter θ σ) := by
  simp only [NLit.ground, NLit.subst, groundTerm_applyTerm]

/-- Oriented at `θ`, a literal's named sides are the sides of its instance. -/
theorem NLit.ground_sides {θ : Grounding sig} {L : NLit sig}
    (oriented : θ.groundTerm L.rhs ≤ θ.groundTerm L.lhs) :
    (L.ground θ).lhs = θ.groundTerm L.lhs ∧ (L.ground θ).rhs = θ.groundTerm L.rhs :=
  ⟨max_eq_left oriented, min_eq_right oriented⟩

/-- **Every literal has an orientation at `θ`.** -/
theorem NLit.orient (θ : Grounding sig) (L : NLit sig) :
    ∃ K : NLit sig, (K = L ∨ K = L.flip) ∧ θ.groundTerm K.rhs ≤ θ.groundTerm K.lhs := by
  rcases le_total (θ.groundTerm L.rhs) (θ.groundTerm L.lhs) with h | h
  · exact ⟨L, Or.inl rfl, h⟩
  · exact ⟨L.flip, Or.inr rfl, h⟩

/-- **The ground instance of a clause.** -/
def NClause.ground (θ : Grounding sig) (C : NClause sig) : Clause (GroundTerm sig) :=
  ((C.map (NLit.ground θ) : List (Lit (GroundTerm sig))) : Multiset (Lit (GroundTerm sig)))

@[simp] theorem NClause.ground_nil (θ : Grounding sig) : NClause.ground θ [] = 0 := rfl

theorem NClause.ground_cons (θ : Grounding sig) (L : NLit sig) (C : NClause sig) :
    NClause.ground θ (L :: C) = L.ground θ ::ₘ NClause.ground θ C := rfl

theorem NClause.ground_append (θ : Grounding sig) (C D : NClause sig) :
    NClause.ground θ (C ++ D) = NClause.ground θ C + NClause.ground θ D := by
  simp only [NClause.ground, List.map_append, Multiset.coe_add]

theorem NClause.ground_middle (θ : Grounding sig) (s t : NClause sig) (L : NLit sig) :
    NClause.ground θ (s ++ L :: t) = L.ground θ ::ₘ NClause.ground θ (s ++ t) := by
  unfold NClause.ground
  rw [List.map_append, List.map_cons, List.map_append, Multiset.cons_coe]
  exact Multiset.coe_eq_coe.mpr List.perm_middle

theorem NClause.ground_subst (θ : Grounding sig) (σ : Subst sig) (C : NClause sig) :
    NClause.ground θ (C.subst σ) = NClause.ground (groundAfter θ σ) C := by
  simp only [NClause.ground, NClause.subst, List.map_map, Function.comp_def, NLit.ground_subst]

theorem NClause.ground_eq_zero_iff (θ : Grounding sig) (C : NClause sig) :
    NClause.ground θ C = 0 ↔ C = [] := by
  unfold NClause.ground
  rw [Multiset.coe_eq_zero, List.map_eq_nil_iff]

theorem NClause.mem_ground {θ : Grounding sig} {C : NClause sig} {L : NLit sig} (member : L ∈ C) :
    L.ground θ ∈ NClause.ground θ C :=
  Multiset.mem_coe.mpr (List.mem_map_of_mem member)

theorem NClause.exists_of_mem_ground {θ : Grounding sig} {C : NClause sig} {M : Lit (GroundTerm sig)}
    (member : M ∈ NClause.ground θ C) : ∃ L ∈ C, L.ground θ = M :=
  List.mem_map.mp (Multiset.mem_coe.mp member)

/-- **A literal of an instance comes from a literal of the clause**, with the rest from the rest. -/
theorem NClause.extract {θ : Grounding sig} {C : NClause sig} {M : Lit (GroundTerm sig)}
    {rest : Clause (GroundTerm sig)} (same : NClause.ground θ C = M ::ₘ rest) :
    ∃ (s t : NClause sig) (L : NLit sig), C = s ++ L :: t ∧ L.ground θ = M ∧
      NClause.ground θ (s ++ t) = rest := by
  have member : M ∈ NClause.ground θ C := by rw [same]; exact Multiset.mem_cons_self M rest
  obtain ⟨L, inC, rfl⟩ := NClause.exists_of_mem_ground member
  obtain ⟨s, t, rfl⟩ := List.append_of_mem inC
  refine ⟨s, t, L, rfl, rfl, ?_⟩
  rw [NClause.ground_middle] at same
  exact (Multiset.cons_inj_right _).mp same

theorem forall₂_ground (θ : Grounding sig) : ∀ {X Z : NClause sig},
    List.Forall₂ (fun L M => L = M ∨ L = M.flip) X Z → X.map (NLit.ground θ) = Z.map (NLit.ground θ)
  | _, _, .nil => rfl
  | _, _, .cons choice rest => by
      rw [List.map_cons, List.map_cons, NLit.ground_of_choice choice, forall₂_ground θ rest]

/-- **A reorientation has the same ground instances.** -/
theorem Reorient.ground {X Y : NClause sig} (reorient : Reorient X Y) (θ : Grounding sig) :
    NClause.ground θ X = NClause.ground θ Y := by
  obtain ⟨Z, perm, pointwise⟩ := reorient
  unfold NClause.ground
  rw [forall₂_ground θ pointwise]
  exact Multiset.coe_eq_coe.mpr (perm.map _)

end Instances


/-! ## Ground contexts of non-ground contexts, and positions -/

section Positions

/-- **The ground instance of a context.** -/
def groundCtx (θ : Grounding sig) : FirstOrderRewriting.Context sig → Ctx sig
  | .hole => .hole
  | .app f args i inner => .app f (fun j => θ.groundTerm (args j)) i (groundCtx θ inner)

theorem groundTerm_fill (θ : Grounding sig) : ∀ (c : FirstOrderRewriting.Context sig) (t : Term sig),
    θ.groundTerm (c.fill t) = (groundCtx θ c).fill (θ.groundTerm t)
  | .hole, _ => rfl
  | .app f args i inner, t => by
      show GroundTerm.app f (fun j => θ.groundTerm (Function.update args i (inner.fill t) j)) =
        GroundTerm.app f (Function.update (fun j => θ.groundTerm (args j)) i
          ((groundCtx θ inner).fill (θ.groundTerm t)))
      congr 1
      funext j
      by_cases h : j = i
      · subst h
        rw [Function.update_self, Function.update_self, groundTerm_fill θ inner t]
      · rw [Function.update_of_ne h, Function.update_of_ne h]

/-- **A position of an instance is the instance of a non-variable position, or lies at or below a
variable.** For `sθ = c[w]`: either `s = c'[u]` with `u` not a variable, `uθ = w` and `c'θ` filling as
`c`; or `s = c'[x]` with `xθ = d[w]` and `c'θ ∘ d` filling as `c`. -/
theorem position_split (θ : Grounding sig) : ∀ (c : Ctx sig) (s : Term sig) (w : GroundTerm sig),
    θ.groundTerm s = c.fill w →
      (∃ (c' : FirstOrderRewriting.Context sig) (u : Term sig), (∀ x, u ≠ .var x) ∧ s = c'.fill u ∧
          θ.groundTerm u = w ∧ ∀ t, (groundCtx θ c').fill t = c.fill t) ∨
      (∃ (c' : FirstOrderRewriting.Context sig) (x : sig.vars) (d : Ctx sig), s = c'.fill (.var x) ∧
          θ x = d.fill w ∧ ∀ t, (groundCtx θ c').fill (d.fill t) = c.fill t)
  | .hole, s, w, same => by
      cases s with
      | var x => exact Or.inr ⟨.hole, x, .hole, rfl, same, fun _ => rfl⟩
      | const k => exact Or.inl ⟨.hole, .const k, (fun x h => by cases h), rfl, same, fun _ => rfl⟩
      | app f ts => exact Or.inl ⟨.hole, .app f ts, (fun x h => by cases h), rfl, same, fun _ => rfl⟩
  | .app f args i inner, s, w, same => by
      cases s with
      | var x => exact Or.inr ⟨.hole, x, .app f args i inner, rfl, same, fun _ => rfl⟩
      | const k => cases same
      | app g ts =>
          have same' : GroundTerm.app g (fun j => θ.groundTerm (ts j)) =
              GroundTerm.app f (Function.update args i (inner.fill w)) := same
          obtain ⟨hfg, hargs⟩ := GroundTerm.app.inj same'
          subst hfg
          have equal := eq_of_heq hargs
          have atI : θ.groundTerm (ts i) = inner.fill w := by
            have step := congrFun equal i
            rwa [Function.update_self] at step
          have back : ∀ v : GroundTerm sig,
              GroundTerm.app _ (Function.update (fun j => θ.groundTerm (ts j)) i (inner.fill v)) =
                (Ctx.app _ args i inner).fill v := by
            intro v
            show _ = GroundTerm.app _ (Function.update args i (inner.fill v))
            rw [equal, Function.update_idem]
          rcases position_split θ inner (ts i) w atI with
            ⟨c', u, notVar, atU, groundU, fills⟩ | ⟨c', x, d, atX, groundX, fills⟩
          · refine Or.inl ⟨.app _ ts i c', u, notVar, ?_, groundU, fun v => ?_⟩
            · show Term.app _ ts = Term.app _ (Function.update ts i (c'.fill u))
              rw [← atU, Function.update_eq_self]
            · show GroundTerm.app _ (Function.update (fun j => θ.groundTerm (ts j)) i
                ((groundCtx θ c').fill v)) = _
              rw [fills v]
              exact back v
          · refine Or.inr ⟨.app _ ts i c', x, d, ?_, groundX, fun v => ?_⟩
            · show Term.app _ ts = Term.app _ (Function.update ts i (c'.fill (.var x)))
              rw [← atX, Function.update_eq_self]
            · show GroundTerm.app _ (Function.update (fun j => θ.groundTerm (ts j)) i
                ((groundCtx θ c').fill (d.fill v))) = _
              rw [fills v]
              exact back v

/-! ### Terms fixed by a substitution -/

/-- A substitution fixing a filled context fixes what fills its hole. -/
theorem fixes_inner {θ : Subst sig} : ∀ (c : FirstOrderRewriting.Context sig) {u : Term sig},
    θ.applyTerm (c.fill u) = c.fill u → θ.applyTerm u = u
  | .hole, _, fixed => fixed
  | .app f args i inner, u, fixed => by
      have step : Term.app f (fun j => θ.applyTerm (Function.update args i (inner.fill u) j)) =
          Term.app f (Function.update args i (inner.fill u)) := fixed
      have atI := congrFun (eq_of_heq (Term.app.inj step).2) i
      simp only [Function.update_self] at atI
      exact fixes_inner inner atI

/-- A substitution fixing a filled context fixes it at any fixed term. -/
theorem fixes_fill {θ : Subst sig} : ∀ (c : FirstOrderRewriting.Context sig) {u t : Term sig},
    θ.applyTerm (c.fill u) = c.fill u → θ.applyTerm t = t → θ.applyTerm (c.fill t) = c.fill t
  | .hole, _, _, _, fixedT => fixedT
  | .app f args i inner, u, t, fixed, fixedT => by
      have step : Term.app f (fun j => θ.applyTerm (Function.update args i (inner.fill u) j)) =
          Term.app f (Function.update args i (inner.fill u)) := fixed
      have pointwise := congrFun (eq_of_heq (Term.app.inj step).2)
      show Term.app f (fun j => θ.applyTerm (Function.update args i (inner.fill t) j)) =
        Term.app f (Function.update args i (inner.fill t))
      congr 1
      funext j
      by_cases h : j = i
      · rw [h, Function.update_self]
        have atI := pointwise i
        simp only [Function.update_self] at atI
        exact fixes_fill inner atI fixedT
      · have atJ := pointwise j
        rw [Function.update_of_ne h] at atJ ⊢
        exact atJ

/-- **A clause fixed by a substitution**: every side of every literal. -/
def FixesClause (θ : Subst sig) (C : NClause sig) : Prop :=
  ∀ L ∈ C, θ.applyTerm L.lhs = L.lhs ∧ θ.applyTerm L.rhs = L.rhs

theorem FixesClause.subst_eq {θ : Subst sig} {C : NClause sig} (fixed : FixesClause θ C) :
    C.subst θ = C := by
  induction C with
  | nil => rfl
  | cons L C ih =>
      show NLit.subst θ L :: NClause.subst θ C = L :: C
      obtain ⟨one, two⟩ := fixed L List.mem_cons_self
      rw [ih fun M member => fixed M (List.mem_cons_of_mem _ member)]
      show (⟨L.negative, θ.applyTerm L.lhs, θ.applyTerm L.rhs⟩ : NLit sig) :: C = L :: C
      rw [one, two]

theorem FixesClause.append {θ : Subst sig} {C D : NClause sig} (one : FixesClause θ C)
    (two : FixesClause θ D) : FixesClause θ (C ++ D) := fun L member =>
  (List.mem_append.mp member).elim (one L) (two L)

theorem FixesClause.of_reorient {θ : Subst sig} {X Y : NClause sig} (reorient : Reorient X Y)
    (fixed : FixesClause θ Y) : FixesClause θ X := by
  intro K member
  obtain ⟨M, inY, sides⟩ := reorient.sides member
  obtain ⟨one, two⟩ := fixed M inY
  rcases sides with ⟨hl, hr⟩ | ⟨hl, hr⟩
  · rw [hl, hr]; exact ⟨one, two⟩
  · rw [hl, hr]; exact ⟨two, one⟩

/-- Each side of `M` lies below a side of `L`. -/
def SidesBelow (gt : Term sig → Term sig → Prop) (L M : NLit sig) : Prop :=
  (gt L.lhs M.lhs ∨ gt L.rhs M.lhs) ∧ (gt L.lhs M.rhs ∨ gt L.rhs M.rhs)

/-- **The strict subterm relation.** -/
inductive StrictSubterm : Term sig → Term sig → Prop
  | arg (f : sig.functionSymbols) (ts : Fin (sig.functionArity f) → Term sig) (i : Fin (sig.functionArity f)) :
      StrictSubterm (.app f ts) (ts i)
  | trans {s t u : Term sig} : StrictSubterm s t → StrictSubterm t u → StrictSubterm s u

theorem StrictSubterm.subst (τ : Subst sig) {s t : Term sig} (below : StrictSubterm s t) :
    StrictSubterm (τ.applyTerm s) (τ.applyTerm t) := by
  induction below with
  | arg f ts i => exact .arg f (fun j => τ.applyTerm (ts j)) i
  | trans _ _ one two => exact .trans one two

end Positions

/-! ## The order link -/

section Link

variable [LinearOrder (GroundTerm sig)]

/-- **A stable ordering linked to the ground ordering**: for every grounding `θ`, `s ≻ t` implies
`sθ > tθ`, and a literal `L ≻ M` implies `Mθ < Lθ`. -/
structure GroundedOrder (sig : LPSignature) [LinearOrder (GroundTerm sig)] extends StableOrder sig where
  gt_ground : ∀ (θ : Grounding sig) (s t : Term sig), gt s t → θ.groundTerm t < θ.groundTerm s
  litGt_ground : ∀ (θ : Grounding sig) (L M : NLit sig), litGt L M → M.ground θ < L.ground θ

/-- **The link from stability and the ground restriction**: on ground terms and ground literals the
non-ground ordering is contained in the ground one. -/
def GroundedOrder.ofRestriction (ord : StableOrder sig)
    (gt_restrict : ∀ a b : GroundTerm sig, ord.gt a.toTerm b.toTerm → b < a)
    (litGt_restrict : ∀ (θ : Grounding sig) (L M : NLit sig),
      ord.litGt (L.subst θ.toSubst) (M.subst θ.toSubst) → M.ground θ < L.ground θ) :
    GroundedOrder sig where
  toStableOrder := ord
  gt_ground θ s t gt := by
    have step := ord.gt_subst θ.toSubst s t gt
    rw [← Grounding.groundTerm_toTerm, ← Grounding.groundTerm_toTerm] at step
    exact gt_restrict _ _ step
  litGt_ground θ L M gt := litGt_restrict θ L M (ord.litGt_subst θ.toSubst L M gt)

/-- **A linked term ordering gives a linked ordering on literals.** -/
def GroundedOrder.ofTermOrder (gt : Term sig → Term sig → Prop)
    (gt_subst : ∀ (τ : Subst sig) (s t : Term sig), gt s t → gt (τ.applyTerm s) (τ.applyTerm t))
    (gt_ground : ∀ (θ : Grounding sig) (s t : Term sig), gt s t → θ.groundTerm t < θ.groundTerm s) :
    GroundedOrder sig where
  gt := gt
  gt_subst := gt_subst
  litGt := SidesBelow gt
  litGt_subst τ L M below := ⟨below.1.imp (gt_subst τ _ _) (gt_subst τ _ _),
    below.2.imp (gt_subst τ _ _) (gt_subst τ _ _)⟩
  gt_ground := gt_ground
  litGt_ground θ L M below := by
    have top : ∀ s, (s = L.lhs ∨ s = L.rhs) → θ.groundTerm s ≤ (L.ground θ).lhs := by
      rintro s (rfl | rfl)
      · exact le_max_left _ _
      · exact le_max_right _ _
    have side : ∀ t, (gt L.lhs t ∨ gt L.rhs t) → θ.groundTerm t < (L.ground θ).lhs := by
      rintro t (h | h)
      · exact (gt_ground θ _ _ h).trans_le (top _ (Or.inl rfl))
      · exact (gt_ground θ _ _ h).trans_le (top _ (Or.inr rfl))
    exact Lit.lt_of_lhs_lt (max_lt (side _ below.1) (side _ below.2))

theorem StrictSubterm.ground_lt [GroundSimplification sig] (θ : Grounding sig) {s t : Term sig}
    (below : StrictSubterm s t) : θ.groundTerm t < θ.groundTerm s := by
  induction below with
  | arg f ts i => exact GroundSimplification.subterm f (fun j => θ.groundTerm (ts j)) i
  | trans _ _ one two => exact two.trans one

/-- **The strict subterm ordering is linked to every ground simplification ordering.** -/
def subtermOrder [GroundSimplification sig] : GroundedOrder sig :=
  GroundedOrder.ofTermOrder StrictSubterm (fun τ _ _ below => below.subst τ)
    (fun θ _ _ below => below.ground_lt θ)

/-! ### The side conditions at a grounding -/

variable (ord : GroundedOrder sig)

theorem GroundedOrder.not_geAt (θ : Grounding sig) {s t : Term sig}
    (lt : θ.groundTerm t < θ.groundTerm s) : ¬ ord.toStableOrder.geAt t s θ.toSubst := by
  rintro (gt | same)
  · have step := ord.gt_ground θ _ _ gt
    rw [groundTerm_toSubst, groundTerm_toSubst] at step
    exact lt_asymm lt step
  · have step := congrArg θ.groundTerm same
    rw [groundTerm_toSubst, groundTerm_toSubst] at step
    exact lt.ne step

theorem GroundedOrder.not_litGeAt (θ : Grounding sig) {M K : NLit sig}
    (lt : M.ground θ < K.ground θ) : ¬ ord.toStableOrder.litGeAt M K θ.toSubst := by
  rintro (gt | same)
  · have step := ord.litGt_ground θ _ _ gt
    rw [NLit.ground_subst, NLit.ground_subst, groundAfter_toSubst] at step
    exact lt_asymm lt step
  · have step := congrArg (NLit.ground θ) same
    rw [NLit.ground_subst, NLit.ground_subst, groundAfter_toSubst] at step
    exact lt.ne step

theorem GroundedOrder.not_litGtAt (θ : Grounding sig) {M K : NLit sig}
    (le : M.ground θ ≤ K.ground θ) : ¬ ord.toStableOrder.litGtAt M K θ.toSubst := by
  intro gt
  have step := ord.litGt_ground θ _ _ gt
  rw [NLit.ground_subst, NLit.ground_subst, groundAfter_toSubst] at step
  exact absurd le (not_le.mpr step)

/-- **The superposition side conditions hold at the grounding**, read as a substitution, when the
ground side conditions hold. -/
theorem supConditions_of_ground (θ : Grounding sig) {u l r : Term sig} {D' C' : NClause sig}
    {L : NLit sig} (notVar : ∀ x, u ≠ .var x) (decreasing : θ.groundTerm r < θ.groundTerm l)
    (strict : θ.groundTerm L.rhs < θ.groundTerm L.lhs)
    (sideMax : ∀ M ∈ D', M.ground θ < (posLit l r).ground θ)
    (negMax : L.negative = true → ∀ M ∈ C', M.ground θ ≤ L.ground θ)
    (posMax : L.negative = false → (∀ M ∈ C', M.ground θ < L.ground θ) ∧
      (posLit l r).ground θ < L.ground θ) :
    supConditions ord.toStableOrder u l r D' L C' θ.toSubst :=
  ⟨notVar, ord.not_geAt θ decreasing, ord.not_geAt θ strict,
    fun M member => ord.not_litGeAt θ (sideMax M member),
    fun negative M member => ord.not_litGtAt θ (negMax negative M member),
    fun positive => ⟨fun M member => ord.not_litGeAt θ ((posMax positive).1 M member),
      ord.not_litGeAt θ (posMax positive).2⟩⟩

theorem eqResConditions_of_ground (θ : Grounding sig) {L : NLit sig} {C' : NClause sig}
    (negative : L.negative = true) (maximal : ∀ M ∈ C', M.ground θ ≤ L.ground θ) :
    eqResConditions ord.toStableOrder L C' θ.toSubst :=
  ⟨negative, fun M member => ord.not_litGtAt θ (maximal M member)⟩

theorem eqFactConditions_of_ground (θ : Grounding sig) {L L' : NLit sig} {C' : NClause sig}
    (positive : L.negative = false) (positive' : L'.negative = false)
    (strict : θ.groundTerm L.rhs < θ.groundTerm L.lhs)
    (maximal : ∀ M ∈ L' :: C', M.ground θ ≤ L.ground θ) :
    eqFactConditions ord.toStableOrder L L' C' θ.toSubst :=
  ⟨positive, positive', ord.not_geAt θ strict, fun M member => ord.not_litGtAt θ (maximal M member)⟩

end Link

/-! ## Where the closure guard is used -/

section ClosureGuard

/-- **Where the closure guard is used.** A co-stable side condition `G` that holds at the grounding
`θ` (read as a substitution) holds at a most general unifier `μ` through which `θ` factors, by
co-stability; the closure of `G` holds at `θ`; and the closure, asked at every solution of the told
equation, is entailed (`entails_closure_iff`). Asking `G` itself at every solution can fail, because
co-stable conditions do not survive instantiation (the control `notAbove_every_refused`). -/
theorem closure_guard_of_grounding (θ : Grounding sig) {l u : Term sig} {G : Subst sig → Prop}
    (coStable : CoStable (A sig) G) {μ ν : Subst sig} (principal : (A sig).Principal [(l, u)] μ)
    (through : θ.toSubst = ν ∘ₛ μ) (atGrounding : G θ.toSubst) :
    G μ ∧ Closure (A sig) [(l, u)] G θ.toSubst ∧ (A sig).Entails [(l, u)] (Closure (A sig) [(l, u)] G) := by
  have atComp : G (ν ∘ₛ μ) := through ▸ atGrounding
  have atμ : G μ := coStable ν μ atComp
  refine ⟨atμ, ⟨μ, principal.sound, ⟨ν, fun t => ?_⟩, atμ⟩,
    (entails_closure_iff principal (respects_firstOrder G) coStable).mpr atμ⟩
  show θ.toSubst.applyTerm t = (ν ∘ₛ μ).applyTerm t
  rw [through]

end ClosureGuard

/-! ## The lifting lemma -/

section Lifting

variable [LinearOrder (GroundTerm sig)]

/-- **A lifted superposition**: the parameters of the non-ground firing for a ground superposition at
a non-variable position. The premises are reorientations of the given clauses; `μ` is a most general
unifier of the told terms, at which the side conditions hold; the grounding factors through `μ`; and
the conclusion's instance is the ground conclusion. -/
structure SupLift (ord : StableOrder sig) (θ : Grounding sig) (Dc Cc : NClause sig)
    (E : Clause (GroundTerm sig)) where
  D' : NClause sig
  C' : NClause sig
  L : NLit sig
  c : FirstOrderRewriting.Context sig
  u : Term sig
  l : Term sig
  r : Term sig
  μ : Subst sig
  ν : Grounding sig
  side_reorient : Reorient (posLit l r :: D') Dc
  main_reorient : Reorient (L :: C') Cc
  at_position : L.lhs = c.fill u
  principal : (A sig).Principal [(l, u)] μ
  conditions : supConditions ord u l r D' L C' μ
  factors : groundAfter ν μ = θ
  conclusion : NClause.ground θ (supConclusion c r D' L C') = E

/-- **A lifted equality resolution.** -/
structure EqResLift (ord : StableOrder sig) (θ : Grounding sig) (Cc : NClause sig)
    (E : Clause (GroundTerm sig)) where
  C' : NClause sig
  L : NLit sig
  μ : Subst sig
  ν : Grounding sig
  main_reorient : Reorient (L :: C') Cc
  principal : (A sig).Principal [(L.lhs, L.rhs)] μ
  conditions : eqResConditions ord L C' μ
  factors : groundAfter ν μ = θ
  conclusion : NClause.ground θ C' = E

/-- **A lifted equality factoring.** -/
structure EqFactLift (ord : StableOrder sig) (θ : Grounding sig) (Cc : NClause sig)
    (E : Clause (GroundTerm sig)) where
  C' : NClause sig
  L : NLit sig
  L' : NLit sig
  μ : Subst sig
  ν : Grounding sig
  main_reorient : Reorient (L :: L' :: C') Cc
  principal : (A sig).Principal [(L.lhs, L'.lhs)] μ
  conditions : eqFactConditions ord L L' C' μ
  factors : groundAfter ν μ = θ
  conclusion : NClause.ground θ (eqFactConclusion L L' C') = E

/-- **A superposition at or below a variable of the main premise**: the main literal `L` (a
reorientation of the stored `M`) has `L.lhs = c'[x]`, and `xθ = d[l]` contains the rewritten term. -/
def AtVariable (θ : Grounding sig) (Dc Cc : NClause sig) (E : Clause (GroundTerm sig)) : Prop :=
  ∃ (l r : GroundTerm sig) (D : Clause (GroundTerm sig)) (s t : NClause sig) (L M : NLit sig)
    (c' : FirstOrderRewriting.Context sig) (x : sig.vars) (d : Ctx sig),
    r < l ∧ Lit.make false l r ::ₘ D = NClause.ground θ Dc ∧ Cc = s ++ M :: t ∧ (L = M ∨ L = M.flip) ∧
    (∀ K ∈ NClause.ground θ Dc, K < L.ground θ) ∧ L.lhs = c'.fill (.var x) ∧ θ x = d.fill l ∧
    E = Lit.make L.negative ((groundCtx θ c').fill (d.fill r)) (θ.groundTerm L.rhs) ::ₘ
      (D + NClause.ground θ (s ++ t))

theorem Lit.make_false_eq_pos {T : Type*} [LinearOrder T] {l r : T} (h : r ≤ l) :
    Lit.make false l r = Lit.pos l r h :=
  Lit.ext (max_eq_left h) rfl (min_eq_right h)

theorem posLit_ground (θ : Grounding sig) (l r : Term sig) :
    (posLit l r).ground θ = Lit.make false (θ.groundTerm l) (θ.groundTerm r) := rfl

variable [DecidableEq sig.vars] [DecidableEq sig.constants] [DecidableEq sig.functionSymbols]
variable (ord : GroundedOrder sig)

/-- **The lifting of a ground superposition**, positive or negative: either its position lies at or
below a variable of the main premise, or it is the instance of a lifted superposition. -/
theorem lift_sup_core (θ : Grounding sig) {Dc Cc : NClause sig} {l r : GroundTerm sig}
    {D C : Clause (GroundTerm sig)} {L : Lit (GroundTerm sig)} {c : Ctx sig} (decreasing : r < l)
    (sideMax : ∀ M ∈ D, M < Lit.pos l r decreasing.le) (larger : L.lhs = c.fill l)
    (strict : L.rhs < L.lhs) (smaller : Lit.pos l r decreasing.le < L)
    (negMax : L.negative = true → ∀ M ∈ C, M ≤ L)
    (posMax : L.negative = false → ∀ M ∈ C, M < L)
    (sideEq : Lit.pos l r decreasing.le ::ₘ D = NClause.ground θ Dc)
    (mainEq : L ::ₘ C = NClause.ground θ Cc) :
    Nonempty (SupLift ord.toStableOrder θ Dc Cc
        (Lit.make L.negative (c.fill r) L.rhs ::ₘ (D + C))) ∨
      AtVariable θ Dc Cc (Lit.make L.negative (c.fill r) L.rhs ::ₘ (D + C)) := by
  -- the side literal
  obtain ⟨s₁, t₁, S, rfl, groundS, groundD⟩ := NClause.extract sideEq.symm
  obtain ⟨K, choiceK, orientK⟩ := NLit.orient θ S
  have groundK : K.ground θ = Lit.pos l r decreasing.le := (NLit.ground_of_choice choiceK).trans groundS
  have hl : θ.groundTerm K.lhs = l := by
    have step := congrArg Lit.lhs groundK
    rwa [(NLit.ground_sides orientK).1] at step
  have hr : θ.groundTerm K.rhs = r := by
    have step := congrArg Lit.rhs groundK
    rwa [(NLit.ground_sides orientK).2] at step
  have hneg : K.negative = false := congrArg Lit.negative groundK
  have Kpos : posLit K.lhs K.rhs = K := by
    show (⟨false, K.lhs, K.rhs⟩ : NLit sig) = K
    rw [← hneg]
  have posGround : (posLit K.lhs K.rhs).ground θ = Lit.pos l r decreasing.le := by rw [Kpos]; exact groundK
  -- the main literal
  obtain ⟨s₂, t₂, M, rfl, groundM, groundC⟩ := NClause.extract mainEq.symm
  obtain ⟨Lm, choiceL, orientL⟩ := NLit.orient θ M
  have groundL : Lm.ground θ = L := (NLit.ground_of_choice choiceL).trans groundM
  have hLl : θ.groundTerm Lm.lhs = L.lhs := by
    rw [← (NLit.ground_sides orientL).1, groundL]
  have hLr : θ.groundTerm Lm.rhs = L.rhs := by
    rw [← (NLit.ground_sides orientL).2, groundL]
  have hLneg : Lm.negative = L.negative := by rw [← groundL]; rfl
  have memD : ∀ N ∈ s₁ ++ t₁, N.ground θ ∈ D := fun N member => groundD ▸ NClause.mem_ground member
  have memC : ∀ N ∈ s₂ ++ t₂, N.ground θ ∈ C := fun N member => groundC ▸ NClause.mem_ground member
  rcases position_split θ c Lm.lhs l (hLl.trans larger) with
    ⟨c', u, notVar, atU, groundU, fills⟩ | ⟨c', x, d, atX, groundX, fills⟩
  · left
    obtain ⟨μ, principal, ν, through⟩ := exists_mgu θ (s := K.lhs) (t := u) (hl.trans groundU.symm)
    have atθ : supConditions ord.toStableOrder u K.lhs K.rhs (s₁ ++ t₁) Lm (s₂ ++ t₂) θ.toSubst := by
      refine supConditions_of_ground ord θ notVar (by rw [hl, hr]; exact decreasing)
        (by rw [hLl, hLr]; exact strict) (fun N member => by rw [posGround]; exact sideMax _ (memD N member))
        (fun negative N member => ?_) (fun positive => ⟨fun N member => ?_, ?_⟩)
      · rw [groundL]; exact negMax (hLneg ▸ negative) _ (memC N member)
      · rw [groundL]; exact posMax (hLneg ▸ positive) _ (memC N member)
      · rw [groundL, posGround]; exact smaller
    refine ⟨⟨s₁ ++ t₁, s₂ ++ t₂, Lm, c', u, K.lhs, K.rhs, μ, groundAfter θ ν, ?_,
      Reorient.middle choiceL s₂ t₂, atU, principal,
      (closure_guard_of_grounding θ (supConditions_coStable _ _ _ _ _ _ _) principal through atθ).1,
      groundAfter_factors θ through, ?_⟩⟩
    · rw [Kpos]; exact Reorient.middle choiceK s₁ t₁
    · show NClause.ground θ (⟨Lm.negative, c'.fill K.rhs, Lm.rhs⟩ :: (s₁ ++ t₁ ++ (s₂ ++ t₂))) = _
      rw [NClause.ground_cons, NClause.ground_append, groundD, groundC]
      show Lit.make Lm.negative (θ.groundTerm (c'.fill K.rhs)) (θ.groundTerm Lm.rhs) ::ₘ (D + C) = _
      rw [groundTerm_fill, hr, hLr, hLneg, fills]
  · right
    refine ⟨l, r, D, s₂, t₂, Lm, M, c', x, d, decreasing, ?_, rfl, choiceL, ?_, atX, groundX, ?_⟩
    · rw [Lit.make_false_eq_pos decreasing.le]; exact sideEq
    · intro N member
      rw [← sideEq] at member
      rw [groundL]
      rcases Multiset.mem_cons.mp member with rfl | inD
      · exact smaller
      · exact (sideMax N inD).trans smaller
    · rw [groundC, hLr, hLneg, fills]

/-- **Lifting positive superposition.** -/
theorem lift_posSup (θ : Grounding sig) {Dc Cc : NClause sig} {l r : GroundTerm sig}
    (D C : Clause (GroundTerm sig)) (L : Lit (GroundTerm sig)) (c : Ctx sig) (decreasing : r < l)
    (sideMax : ∀ M ∈ D, M < Lit.pos l r decreasing.le) (positive : L.negative = false)
    (larger : L.lhs = c.fill l) (strict : L.rhs < L.lhs) (mainMax : ∀ M ∈ C, M < L)
    (smaller : Lit.pos l r decreasing.le < L)
    (sideEq : Lit.pos l r decreasing.le ::ₘ D = NClause.ground θ Dc)
    (mainEq : L ::ₘ C = NClause.ground θ Cc) :
    Nonempty (SupLift ord.toStableOrder θ Dc Cc (Lit.make false (c.fill r) L.rhs ::ₘ (D + C))) ∨
      AtVariable θ Dc Cc (Lit.make false (c.fill r) L.rhs ::ₘ (D + C)) := by
  have core := lift_sup_core ord θ decreasing sideMax larger strict smaller
    (fun negative => absurd (positive.symm.trans negative) (by decide)) (fun _ => mainMax) sideEq mainEq
  rwa [positive] at core

/-- **Lifting negative superposition.** -/
theorem lift_negSup [GroundSimplification sig] (θ : Grounding sig) {Dc Cc : NClause sig} {l r : GroundTerm sig}
    (D C : Clause (GroundTerm sig)) (L : Lit (GroundTerm sig)) (c : Ctx sig) (decreasing : r < l)
    (sideMax : ∀ M ∈ D, M < Lit.pos l r decreasing.le) (negative : L.negative = true)
    (larger : L.lhs = c.fill l) (strict : L.rhs < L.lhs) (mainMax : ∀ M ∈ C, M ≤ L)
    (sideEq : Lit.pos l r decreasing.le ::ₘ D = NClause.ground θ Dc)
    (mainEq : L ::ₘ C = NClause.ground θ Cc) :
    Nonempty (SupLift ord.toStableOrder θ Dc Cc (Lit.make true (c.fill r) L.rhs ::ₘ (D + C))) ∨
      AtVariable θ Dc Cc (Lit.make true (c.fill r) L.rhs ::ₘ (D + C)) := by
  have smaller : Lit.pos l r decreasing.le < L :=
    Lit.pos_lt_of_negative negative ((c.le_fill l).trans_eq larger.symm)
  have core := lift_sup_core ord θ decreasing sideMax larger strict smaller (fun _ => mainMax)
    (fun positive => absurd (negative.symm.trans positive) (by decide)) sideEq mainEq
  rwa [negative] at core

/-- **Lifting equality resolution.** -/
theorem lift_eqRes (θ : Grounding sig) {Cc : NClause sig} (C : Clause (GroundTerm sig))
    (L : Lit (GroundTerm sig)) (negative : L.negative = true) (trivial : L.rhs = L.lhs)
    (mainMax : ∀ M ∈ C, M ≤ L) (mainEq : L ::ₘ C = NClause.ground θ Cc) :
    Nonempty (EqResLift ord.toStableOrder θ Cc C) := by
  obtain ⟨s, t, M, rfl, groundM, groundC⟩ := NClause.extract mainEq.symm
  have same : θ.groundTerm M.lhs = θ.groundTerm M.rhs := by
    have sides : min (θ.groundTerm M.lhs) (θ.groundTerm M.rhs) =
        max (θ.groundTerm M.lhs) (θ.groundTerm M.rhs) := by
      have one := congrArg Lit.rhs groundM
      have two := congrArg Lit.lhs groundM
      exact one.trans (trivial.trans two.symm)
    rcases le_total (θ.groundTerm M.lhs) (θ.groundTerm M.rhs) with h | h
    · rwa [min_eq_left h, max_eq_right h] at sides
    · rw [min_eq_right h, max_eq_left h] at sides
      exact sides.symm
  obtain ⟨μ, principal, ν, through⟩ := exists_mgu θ same
  have negM : M.negative = true := (congrArg Lit.negative groundM).trans negative
  have atθ := eqResConditions_of_ground ord θ (C' := s ++ t) negM
    (fun N member => by rw [groundM]; exact mainMax _ (groundC ▸ NClause.mem_ground member))
  exact ⟨⟨s ++ t, M, μ, groundAfter θ ν, Reorient.middle (Or.inl rfl) s t, principal,
    (closure_guard_of_grounding θ (eqResConditions_coStable _ _ _) principal through atθ).1,
    groundAfter_factors θ through, groundC⟩⟩

/-- **Lifting equality factoring.** -/
theorem lift_eqFact (θ : Grounding sig) {Cc : NClause sig} (C : Clause (GroundTerm sig))
    (L L' : Lit (GroundTerm sig)) (positive : L.negative = false) (positive' : L'.negative = false)
    (same : L'.lhs = L.lhs) (strict : L.rhs < L.lhs) (mainMax : ∀ M ∈ L' ::ₘ C, M ≤ L)
    (mainEq : L ::ₘ L' ::ₘ C = NClause.ground θ Cc) :
    Nonempty (EqFactLift ord.toStableOrder θ Cc (Lit.make true L.rhs L'.rhs ::ₘ L' ::ₘ C)) := by
  obtain ⟨s, t, M, rfl, groundM, groundRest⟩ := NClause.extract mainEq.symm
  obtain ⟨s', t', M', split, groundM', groundC⟩ := NClause.extract groundRest
  obtain ⟨K, choiceK, orientK⟩ := NLit.orient θ M
  obtain ⟨K', choiceK', orientK'⟩ := NLit.orient θ M'
  have groundK : K.ground θ = L := (NLit.ground_of_choice choiceK).trans groundM
  have groundK' : K'.ground θ = L' := (NLit.ground_of_choice choiceK').trans groundM'
  have hl : θ.groundTerm K.lhs = L.lhs := by rw [← (NLit.ground_sides orientK).1, groundK]
  have hr : θ.groundTerm K.rhs = L.rhs := by rw [← (NLit.ground_sides orientK).2, groundK]
  have hl' : θ.groundTerm K'.lhs = L'.lhs := by rw [← (NLit.ground_sides orientK').1, groundK']
  have hr' : θ.groundTerm K'.rhs = L'.rhs := by rw [← (NLit.ground_sides orientK').2, groundK']
  obtain ⟨μ, principal, ν, through⟩ := exists_mgu θ (s := K.lhs) (t := K'.lhs) (by rw [hl, hl', same])
  have posK : K.negative = false := (congrArg Lit.negative groundK).trans positive
  have posK' : K'.negative = false := (congrArg Lit.negative groundK').trans positive'
  have atθ := eqFactConditions_of_ground ord θ (C' := s' ++ t') posK posK' (by rw [hl, hr]; exact strict)
    (fun N member => by
      rw [groundK]
      rcases List.mem_cons.mp member with rfl | rest
      · rw [groundK']; exact mainMax _ (Multiset.mem_cons_self _ _)
      · exact mainMax _ (Multiset.mem_cons_of_mem (groundC ▸ NClause.mem_ground rest)))
  refine ⟨⟨s' ++ t', K, K', μ, groundAfter θ ν, Reorient.middle₂ choiceK choiceK' split, principal,
    (closure_guard_of_grounding θ (eqFactConditions_coStable _ _ _ _) principal through atθ).1,
    groundAfter_factors θ through, ?_⟩⟩
  show NClause.ground θ (⟨true, K.rhs, K'.rhs⟩ :: K' :: (s' ++ t')) = _
  rw [NClause.ground_cons, NClause.ground_cons, groundK', groundC]
  show Lit.make true (θ.groundTerm K.rhs) (θ.groundTerm K'.rhs) ::ₘ L' ::ₘ C = _
  rw [hr, hr']

end Lifting

/-! ## Admission without renaming apart -/

section Consistent

variable {O : Type uO} [DecidableEq O] (label : O → Term sig)

/-- **Admission of a firing that tells a unification, without renaming apart.** The admission
theorems of `SuperpositionFiring` assume the told terms are fixed by the knowledge's principal answer.
A second inference on a derived clause tells terms whose variables the knowledge already binds. Such
a firing is still admitted when its premises are present, its made occurrence is fresh and carries
the conclusion, some solution of the knowledge solves the told equation, and the side condition holds
at a most general unifier of the told terms. -/
theorem unifyFiring_admits_of_consistent {C : Configuration (Term sig) O} {reads : List (O × Term sig)}
    (stored : ∀ p ∈ reads, label p.1 = p.2) {l u : Term sig} {made : O} {concl : Term sig}
    {G : Subst sig → Prop} (present : ∀ p ∈ reads, p.1 ∈ C.present) (fresh : made ∉ C.present)
    (made_label : label made = concl) {σ : Subst sig} (knowledge : (A sig).Models σ C.equations)
    (told : σ.applyTerm l = σ.applyTerm u) {μ : Subst sig} (principalμ : (A sig).Principal [(l, u)] μ)
    (holds : G μ) :
    (guarded (A sig) label).Admits (s := C) (unifyFiring reads l u made concl G) := by
  have models := unifyFiring_models_iff label C stored l u made concl G
  refine ⟨⟨⟨List.nodup_nil, List.nodup_singleton _, rfl, by simp [unifyFiring], ?_,
    ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨σ, (models σ).mpr ⟨knowledge, told⟩⟩, ?_⟩, ?_⟩, ?_⟩
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

end Consistent

/-! ## Lifted inferences are admitted firings of the shared store -/

section Store

variable [LinearOrder (GroundTerm sig)] [DecidableEq sig.vars] [DecidableEq sig.constants]
  [DecidableEq sig.functionSymbols]
variable {O : Type uO} [DecidableEq O] (label : O → Term sig) (code : ClauseCode sig)

omit [DecidableEq sig.vars] [DecidableEq sig.constants] [DecidableEq sig.functionSymbols] in
/-- The made clause, read at the result's principal answer `μ ∘ θ₀`, is the conclusion instantiated by
`μ`; its instance under `ν` is `E`. -/
theorem made_instance {θ₀ μ : Subst sig} {ν : Grounding sig} {θ : Grounding sig} {concl : NClause sig}
    (fixed : FixesClause θ₀ concl) (factors : groundAfter ν μ = θ) :
    (μ ∘ₛ θ₀).applyTerm (code.encode concl) = code.encode (concl.subst μ) ∧
      NClause.ground ν (concl.subst μ) = NClause.ground θ concl := by
  refine ⟨?_, by rw [NClause.ground_subst, factors]⟩
  rw [Subst.applyTerm_comp, code.encode_subst θ₀, fixed.subst_eq, code.encode_subst]

/-- **A lifted superposition is an admitted firing of the shared store.** With its premises stored at
present occurrences, renamed apart from the knowledge (fixed by its principal answer `θ₀`), and a
fresh occurrence carrying the conclusion: the firing is admitted, the result's knowledge has the
principal answer `μ ∘ θ₀`, and the made clause read there has the ground conclusion `E` as its
instance under `ν`. -/
theorem SupLift.admitted {ord : StableOrder sig} {θ : Grounding sig} {Dc Cc : NClause sig}
    {E : Clause (GroundTerm sig)} (lift : SupLift ord θ Dc Cc E) {Cfg : Configuration (Term sig) O}
    {θ₀ : Subst sig} (principal : (A sig).Principal Cfg.equations θ₀) {side main : O × Term sig}
    (stored : label side.1 = side.2 ∧ label main.1 = main.2)
    (present : side.1 ∈ Cfg.present ∧ main.1 ∈ Cfg.present)
    (apart : FixesClause θ₀ Dc ∧ FixesClause θ₀ Cc) {made : O} (fresh : made ∉ Cfg.present)
    (carries : label made = code.encode (supConclusion lift.c lift.r lift.D' lift.L lift.C')) :
    (guarded (A sig) label).Admits (s := Cfg)
        (supFiring ord code side main made lift.c lift.u lift.l lift.r lift.D' lift.L lift.C') ∧
      (A sig).Principal ((supFiring ord code side main made lift.c lift.u lift.l lift.r lift.D' lift.L
        lift.C').firing.result label Cfg).equations (lift.μ ∘ₛ θ₀) ∧
      (lift.μ ∘ₛ θ₀).applyTerm (label made) =
        code.encode ((supConclusion lift.c lift.r lift.D' lift.L lift.C').subst lift.μ) ∧
      NClause.ground lift.ν ((supConclusion lift.c lift.r lift.D' lift.L lift.C').subst lift.μ) = E := by
  have sideFixed := FixesClause.of_reorient lift.side_reorient apart.1
  have mainFixed := FixesClause.of_reorient lift.main_reorient apart.2
  have lFixed : θ₀.applyTerm lift.l = lift.l := (sideFixed _ List.mem_cons_self).1
  have rFixed : θ₀.applyTerm lift.r = lift.r := (sideFixed _ List.mem_cons_self).2
  have LFixed := mainFixed _ List.mem_cons_self
  have Lfill : θ₀.applyTerm (lift.c.fill lift.u) = lift.c.fill lift.u := by
    rw [← lift.at_position]; exact LFixed.1
  have uFixed : θ₀.applyTerm lift.u = lift.u := fixes_inner lift.c Lfill
  have conclFixed : FixesClause θ₀ (supConclusion lift.c lift.r lift.D' lift.L lift.C') := by
    intro K member
    rcases List.mem_cons.mp member with rfl | rest
    · exact ⟨fixes_fill lift.c Lfill rFixed, LFixed.2⟩
    · rcases List.mem_append.mp rest with inD | inC
      · exact sideFixed K (List.mem_cons_of_mem _ inD)
      · exact mainFixed K (List.mem_cons_of_mem _ inC)
  have encoded : θ₀.applyTerm (code.encode (supConclusion lift.c lift.r lift.D' lift.L lift.C')) =
      code.encode (supConclusion lift.c lift.r lift.D' lift.L lift.C') := by
    rw [code.encode_subst, conclFixed.subst_eq]
  obtain ⟨readMade, atNu⟩ := made_instance code conclFixed lift.factors
  refine ⟨(sup_admits_iff ord label code principal stored ⟨lFixed, uFixed⟩ made lift.c lift.D' lift.L
      lift.C').mpr ⟨present.1, present.2, fresh, carries, lift.μ, lift.principal, lift.conditions⟩,
    (unifyFiring_principal label principal (reads := [side, main])
      (G := supConditions ord lift.u lift.l lift.r lift.D' lift.L lift.C') (by simpa using stored)
      ⟨lFixed, uFixed⟩ made encoded lift.principal).1, by rw [carries]; exact readMade, by rw [atNu]; exact lift.conclusion⟩

/-- **A lifted equality resolution is an admitted firing of the shared store.** -/
theorem EqResLift.admitted {ord : StableOrder sig} {θ : Grounding sig} {Cc : NClause sig}
    {E : Clause (GroundTerm sig)} (lift : EqResLift ord θ Cc E) {Cfg : Configuration (Term sig) O}
    {θ₀ : Subst sig} (principal : (A sig).Principal Cfg.equations θ₀) {main : O × Term sig}
    (stored : label main.1 = main.2) (present : main.1 ∈ Cfg.present) (apart : FixesClause θ₀ Cc)
    {made : O} (fresh : made ∉ Cfg.present) (carries : label made = code.encode lift.C') :
    (guarded (A sig) label).Admits (s := Cfg) (eqResFiring ord code main made lift.L lift.C') ∧
      (A sig).Principal ((eqResFiring ord code main made lift.L lift.C').firing.result label
        Cfg).equations (lift.μ ∘ₛ θ₀) ∧
      (lift.μ ∘ₛ θ₀).applyTerm (label made) = code.encode (lift.C'.subst lift.μ) ∧
      NClause.ground lift.ν (lift.C'.subst lift.μ) = E := by
  have mainFixed := FixesClause.of_reorient lift.main_reorient apart
  have LFixed := mainFixed _ List.mem_cons_self
  have conclFixed : FixesClause θ₀ lift.C' := fun K member => mainFixed K (List.mem_cons_of_mem _ member)
  have encoded : θ₀.applyTerm (code.encode lift.C') = code.encode lift.C' := by
    rw [code.encode_subst, conclFixed.subst_eq]
  obtain ⟨readMade, atNu⟩ := made_instance code conclFixed lift.factors
  refine ⟨(eqRes_admits_iff ord label code principal stored LFixed made lift.C').mpr
      ⟨present, fresh, carries, lift.μ, lift.principal, lift.conditions⟩,
    (unifyFiring_principal label principal (reads := [main])
      (G := eqResConditions ord lift.L lift.C') (by simpa using stored) LFixed made encoded
      lift.principal).1, by rw [carries]; exact readMade, by rw [atNu]; exact lift.conclusion⟩

/-- **A lifted equality factoring is an admitted firing of the shared store.** -/
theorem EqFactLift.admitted {ord : StableOrder sig} {θ : Grounding sig} {Cc : NClause sig}
    {E : Clause (GroundTerm sig)} (lift : EqFactLift ord θ Cc E) {Cfg : Configuration (Term sig) O}
    {θ₀ : Subst sig} (principal : (A sig).Principal Cfg.equations θ₀) {main : O × Term sig}
    (stored : label main.1 = main.2) (present : main.1 ∈ Cfg.present) (apart : FixesClause θ₀ Cc)
    {made : O} (fresh : made ∉ Cfg.present)
    (carries : label made = code.encode (eqFactConclusion lift.L lift.L' lift.C')) :
    (guarded (A sig) label).Admits (s := Cfg) (eqFactFiring ord code main made lift.L lift.L' lift.C') ∧
      (A sig).Principal ((eqFactFiring ord code main made lift.L lift.L' lift.C').firing.result label
        Cfg).equations (lift.μ ∘ₛ θ₀) ∧
      (lift.μ ∘ₛ θ₀).applyTerm (label made) =
        code.encode ((eqFactConclusion lift.L lift.L' lift.C').subst lift.μ) ∧
      NClause.ground lift.ν ((eqFactConclusion lift.L lift.L' lift.C').subst lift.μ) = E := by
  have mainFixed := FixesClause.of_reorient lift.main_reorient apart
  have LFixed := mainFixed _ List.mem_cons_self
  have L'Fixed := mainFixed _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have conclFixed : FixesClause θ₀ (eqFactConclusion lift.L lift.L' lift.C') := by
    intro K member
    rcases List.mem_cons.mp member with rfl | rest
    · exact ⟨LFixed.2, L'Fixed.2⟩
    · exact mainFixed K (List.mem_cons_of_mem _ rest)
  have encoded : θ₀.applyTerm (code.encode (eqFactConclusion lift.L lift.L' lift.C')) =
      code.encode (eqFactConclusion lift.L lift.L' lift.C') := by
    rw [code.encode_subst, conclFixed.subst_eq]
  obtain ⟨readMade, atNu⟩ := made_instance code conclFixed lift.factors
  refine ⟨(eqFact_admits_iff ord label code principal stored ⟨LFixed.1, L'Fixed.1⟩ made lift.C').mpr
      ⟨present, fresh, carries, lift.μ, lift.principal, lift.conditions⟩,
    (unifyFiring_principal label principal (reads := [main])
      (G := eqFactConditions ord lift.L lift.L' lift.C') (by simpa using stored)
      ⟨LFixed.1, L'Fixed.1⟩ made encoded lift.principal).1, by rw [carries]; exact readMade,
    by rw [atNu]; exact lift.conclusion⟩

end Store

#print axioms ground_toTerm
#print axioms groundTerm_applyTerm
#print axioms groundAfter_factors
#print axioms exists_mgu
#print axioms NClause.ground_middle
#print axioms NClause.extract
#print axioms Reorient.ground
#print axioms Reorient.middle₂
#print axioms Reorient.sides
#print axioms groundTerm_fill
#print axioms position_split
#print axioms fixes_inner
#print axioms fixes_fill
#print axioms FixesClause.subst_eq
#print axioms GroundedOrder.ofRestriction
#print axioms GroundedOrder.ofTermOrder
#print axioms subtermOrder
#print axioms GroundedOrder.not_geAt
#print axioms GroundedOrder.not_litGeAt
#print axioms supConditions_of_ground
#print axioms closure_guard_of_grounding
#print axioms lift_sup_core
#print axioms lift_posSup
#print axioms lift_negSup
#print axioms lift_eqRes
#print axioms lift_eqFact
#print axioms SupLift.admitted
#print axioms EqResLift.admitted
#print axioms EqFactLift.admitted
#print axioms unifyFiring_admits_of_consistent

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Superposition
