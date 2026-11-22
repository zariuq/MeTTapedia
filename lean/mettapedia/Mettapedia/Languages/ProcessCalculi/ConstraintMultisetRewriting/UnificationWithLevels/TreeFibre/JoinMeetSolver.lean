import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.JoinMeet

/-!
# The join-meet solver: flex–flex equations of families, two codomains, domains in any order, decided

**Compatibility** (`CompatJ`): two declared families have one codomain, or comparable codomains with the crossing
toward the smaller one (`CrossOK`): position by position, the other domain lies below the smaller-codomain family's
own, or both lie below the smaller codomain.

**The fragment** (`InJoinMeetFragmentK`): a telescope of families; flex–flex equations of families with several
parameters; a grouping of the unknowns, every equation inside one group, every two unknowns of a group compatible,
their codomains equal when they are cumulatively equivalent.

**The round** deletes an equation of one unknown; otherwise it applies the join (one codomain) or the join with a meet
(two codomains), in the orientation of the smaller codomain, and re-reads the other equations.

**Kept by the rounds** (`joinMeetRoundK_stable`): the redeclared unknown is compatible with every unknown of its group
(`compatJ_join`). **Decided** (`joinMeetK_decided`).

The fragment contains the fragment of meet groups over telescopes of universe families whose equivalent codomains are
equal (`compatJ_of_compatK`, `inJoinMeetFragmentK_of_meet`), and the twisted stores of `JoinControls` and
`JoinMeetControls`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentUniverseInjective ContextualDependentCumulative

variable {Head L : Type} [UniverseLevel.LevelOrder L]

/-! ## Compatibility -/

section Compat

/-- **The crossing toward the smaller codomain `c`**, position by position: `ps'`'s domain lies below `ps`'s, or both
lie below `c`. -/
def CrossOK (R : Rules Head) (c : Head) (ps ps' : List Head) : Prop :=
  List.Forall₂ (fun p p' => R.cumulative p' p ∨ (R.cumulative p c ∧ R.cumulative p' c)) ps ps'

/-- **Two declared families are compatible**: one codomain, or comparable codomains with the crossing toward the
smaller one. -/
def CompatJ (R : Rules Head) (ps : List Head) (c : Head) (ps' : List Head) (c' : Head) : Prop :=
  c = c' ∨ (R.cumulative c c' ∧ CrossOK R c ps ps') ∨ (R.cumulative c' c ∧ CrossOK R c' ps' ps)

instance (R : Rules Head) [DecidableRel R.cumulative] (c : Head) (ps ps' : List Head) :
    Decidable (CrossOK R c ps ps') := by
  unfold CrossOK
  infer_instance

instance (R : Rules Head) [DecidableEq Head] [DecidableRel R.cumulative] (ps : List Head) (c : Head)
    (ps' : List Head) (c' : Head) : Decidable (CompatJ R ps c ps' c') := by
  unfold CompatJ CrossOK
  infer_instance

theorem CompatJ.symm {R : Rules Head} {ps : List Head} {c : Head} {ps' : List Head} {c' : Head}
    (h : CompatJ R ps c ps' c') : CompatJ R ps' c' ps c := by
  rcases h with h | h | h
  · exact .inl h.symm
  · exact .inr (.inr h)
  · exact .inr (.inl h)

variable {S : Setting Head L}

theorem joinsOf_cons {join : Head → Head → Option Head} {p p' : Head} {ps ps' ws : List Head}
    (h : joinsOf join (p :: ps) (p' :: ps') = some ws) :
    ∃ w ws', join p p' = some w ∧ joinsOf join ps ps' = some ws' ∧ ws = w :: ws' := by
  cases hw : join p p' with
  | none => simp [joinsOf, hw] at h
  | some w =>
      cases hws : joinsOf join ps ps' with
      | none => simp [joinsOf, hw, hws] at h
      | some ws' =>
          simp only [joinsOf, hw, hws, Option.bind_some, Option.map_some] at h
          cases h
          exact ⟨w, ws', rfl, rfl, rfl⟩

/-- **The step's crossing, computed**: with a join function that keeps the larger of two comparable universes, the
crossing toward `c` gives the crossing of the computed least upper bounds. -/
theorem crosses_of_crossOK (join : Head → Head → Option Head)
    (joinSound : ∀ {u v w : Head}, join u v = some w → S.R.isUniverse w ∧ IsLub S.R w u v)
    (bias : ∀ {u v : Head}, S.R.isUniverse u → S.R.isUniverse v → S.R.cumulative v u → join u v = some u)
    {c : Head} (hc : S.R.isUniverse c) :
    ∀ {ps ps' : List Head}, CrossOK S.R c ps ps' → AllUniverses S.R ps → AllUniverses S.R ps' →
      ∀ {ws : List Head}, joinsOf join ps ps' = some ws → CrossesK S.R c ps ws := by
  intro ps ps' ok
  induction ok with
  | nil =>
      intro _ _ ws h
      cases h
      exact .nil
  | @cons p p' ps ps' here _ ih =>
      intro universes universes' ws h
      obtain ⟨w, ws', hw, hws, rfl⟩ := joinsOf_cons h
      by_cases le : S.R.cumulative p' p
      · rw [bias universes.head universes'.head le] at hw
        cases hw
        exact .keep (ih universes.tail universes'.tail hws)
      · rcases here with below | ⟨pc, p'c⟩
        · exact absurd below le
        · exact .lower ((joinSound hw).2.2.2 c hc pc p'c) (ih universes.tail universes'.tail hws)

variable (algebra : CumulativeAlgebra S.R)

include algebra in
/-- A family of a larger codomain stays compatible with the redeclared one, through the step's crossing. -/
theorem crossOK_join_above {c : Head} :
    ∀ {psF psW : List Head}, CrossOK S.R c psF psW → ∀ {psG psJ : List Head}, JoinsK S.R psF psG psJ →
      CrossesK S.R c psF psJ → CrossOK S.R c psJ psW := by
  intro psF psW ok
  induction ok with
  | nil =>
      intro psG psJ joins _
      cases joins
      exact .nil
  | @cons pF pW psF' psW' here _ ih =>
      intro psG psJ joins crosses
      cases joins with
      | @cons _ pG pJ _ psG' psJ' _ lub restJ =>
          cases crosses with
          | keep restC =>
              refine .cons ?_ (ih restJ restC)
              rcases here with below | both
              · exact .inl below
              · exact .inr both
          | lower below restC =>
              refine .cons ?_ (ih restJ restC)
              rcases here with le | ⟨_, wc⟩
              · exact .inl (algebra.trans le lub.1)
              · exact .inr ⟨below, wc⟩

include algebra in
/-- With one codomain, a family of a larger codomain stays compatible with the joined one. -/
theorem crossOK_join_both_above {c : Head} (hc : S.R.isUniverse c) :
    ∀ {psF psW : List Head}, CrossOK S.R c psF psW → ∀ {psG : List Head}, CrossOK S.R c psG psW →
      ∀ {psJ : List Head}, JoinsK S.R psF psG psJ → CrossOK S.R c psJ psW := by
  intro psF psW ok
  induction ok with
  | nil =>
      intro psG _ psJ joins
      cases joins
      exact .nil
  | @cons pF pW psF' psW' here _ ih =>
      intro psG okG psJ joins
      cases joins with
      | @cons _ pG pJ _ psG' psJ' _ lub restJ =>
          cases okG with
          | cons hereG restG =>
              refine .cons ?_ (ih restG restJ)
              rcases here with le | ⟨fc, wc⟩
              · exact .inl (algebra.trans le lub.1)
              · rcases hereG with leG | ⟨gc, _⟩
                · exact .inl (algebra.trans leG lub.2.1)
                · exact .inr ⟨lub.2.2 c hc fc gc, wc⟩

include algebra in
/-- A family of a smaller codomain stays compatible with the joined one. -/
theorem crossOK_join_below {c : Head} (hc : S.R.isUniverse c) :
    ∀ {psW psF : List Head}, CrossOK S.R c psW psF → AllUniverses S.R psW → ∀ {psG : List Head},
      CrossOK S.R c psW psG → ∀ {psJ : List Head}, JoinsK S.R psF psG psJ → CrossOK S.R c psW psJ := by
  intro psW psF ok
  induction ok with
  | nil =>
      intro _ psG okG psJ joins
      cases okG
      cases joins
      exact .nil
  | @cons pW pF psW' psF' here _ ih =>
      intro universes psG okG psJ joins
      cases okG with
      | @cons _ pG _ psG' hereG restG =>
          cases joins with
          | @cons _ _ pJ _ _ psJ' _ lub restJ =>
              refine .cons ?_ (ih universes.tail restG restJ)
              rcases here with le | ⟨wc, fc⟩
              · rcases hereG with leG | ⟨wcG, gc⟩
                · exact .inl (lub.2.2 pW universes.head le leG)
                · exact .inr ⟨wcG, lub.2.2 c hc (algebra.trans le wcG) gc⟩
              · rcases hereG with leG | ⟨_, gc⟩
                · exact .inr ⟨wc, lub.2.2 c hc fc (algebra.trans leG wc)⟩
                · exact .inr ⟨wc, lub.2.2 c hc fc gc⟩

include algebra in
/-- **The redeclared unknown is compatible with every unknown of its group.** `F` has the smaller codomain `cF`, the
new declaration is `Π (x̄ : U_{p̄J}). U_{cF}`; one codomain, or the step's crossing. -/
theorem compatJ_join {psF psG psJ psW : List Head} {cF cG cW : Head} (hcF : S.R.isUniverse cF)
    (hcW : S.R.isUniverse cW) (universesW : AllUniverses S.R psW)
    (antisym : S.R.cumulative cF cW → S.R.cumulative cW cF → cF = cW) (low : S.R.cumulative cF cG)
    (joins : JoinsK S.R psF psG psJ) (step : cF = cG ∨ CrossesK S.R cF psF psJ)
    (cFW : CompatJ S.R psF cF psW cW) (cGW : CompatJ S.R psG cG psW cW) : CompatJ S.R psJ cF psW cW := by
  by_cases same : cF = cW
  · exact .inl same
  · rcases cFW with h | ⟨le, ok⟩ | ⟨le, ok⟩
    · exact absurd h same
    · rcases step with sameG | crosses
      · rcases cGW with hG | ⟨leG, okG⟩ | ⟨leG, _⟩
        · exact absurd (sameG.trans hG) same
        · rw [← sameG] at okG
          exact .inr (.inl ⟨le, crossOK_join_both_above algebra hcF ok okG joins⟩)
        · exact absurd (antisym le (sameG ▸ leG)) same
      · exact .inr (.inl ⟨le, crossOK_join_above algebra ok joins crosses⟩)
    · rcases cGW with hG | ⟨leG, _⟩ | ⟨_, okG⟩
      · exact absurd (antisym (hG ▸ low) le) same
      · exact absurd (antisym (algebra.trans low leG) le) same
      · exact .inr (.inr ⟨le, crossOK_join_below algebra hcW ok universesW okG joins⟩)

end Compat

/-! ## The fragment -/

section Fragment

variable {S : Setting Head L}

/-- Within a group, every two declared families are compatible, and cumulatively equivalent codomains are equal. -/
def GroupCompat (Θ : Context S.R) (group : Fin Θ.arity → Nat) : Prop :=
  ∀ i j : Fin Θ.arity, i ≠ j → group i = group j → ∀ (psi : List Head) (ci : Head) (psj : List Head) (cj : Head),
    Ctx.lookup Θ.raw i = famCode psi ci → Ctx.lookup Θ.raw j = famCode psj cj →
      CompatJ S.R psi ci psj cj ∧ (S.R.cumulative ci cj → S.R.cumulative cj ci → ci = cj)

/-- **The fragment of the join-meet solver.** -/
structure InJoinMeetFragmentK {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Prop where
  families : Miller.Families Θ
  shapes : ∀ e ∈ problem, Nonempty (FlexK e)
  grouped : ∃ group : Fin Θ.arity → Nat,
    (∀ e ∈ problem, ∀ w : FlexK e, group w.left = group w.right) ∧ GroupCompat Θ group

theorem inJoinMeetFragmentK_delete {Θ : Context S.R} {e : Equation (TotalTerm Θ)}
    {rest : EquationStore (TotalTerm Θ)} (inside : InJoinMeetFragmentK (e :: rest)) : InJoinMeetFragmentK rest := by
  obtain ⟨group, grouped, compat⟩ := inside.grouped
  exact ⟨inside.families, fun e' member => inside.shapes e' (List.mem_cons_of_mem _ member),
    ⟨group, fun e' member => grouped e' (List.mem_cons_of_mem _ member), compat⟩⟩

/-- Swapping the sides of the first equation keeps the fragment. -/
theorem inJoinMeetFragmentK_swap {Θ : Context S.R} {e : Equation (TotalTerm Θ)}
    {rest : EquationStore (TotalTerm Θ)} (inside : InJoinMeetFragmentK (e :: rest)) :
    InJoinMeetFragmentK (((e.2, e.1) : Equation (TotalTerm Θ)) :: rest) := by
  obtain ⟨group, grouped, compat⟩ := inside.grouped
  refine ⟨inside.families, fun e' member => ?_, ⟨group, fun e' member w => ?_, compat⟩⟩
  · rcases List.mem_cons.mp member with rfl | member
    · obtain ⟨v⟩ := inside.shapes e List.mem_cons_self
      exact ⟨v.swap⟩
    · exact inside.shapes e' (List.mem_cons_of_mem _ member)
  · rcases List.mem_cons.mp member with rfl | member
    · exact (grouped e List.mem_cons_self w.swap).symm
    · exact grouped e' (List.mem_cons_of_mem _ member) w

variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
  (algebra : CumulativeAlgebra S.R)

include algebra in
/-- **The join-meet step keeps the fragment**: `v`'s left unknown has the smaller codomain; the right one is
declared again at `Π (x̄ : U_{p̄J}). U_{cl}`. -/
theorem inJoinMeetFragmentK_step {Θ : Context S.R} {e : Equation (TotalTerm Θ)}
    {rest : EquationStore (TotalTerm Θ)} (inside : InJoinMeetFragmentK (e :: rest)) (v : FlexK e)
    (low : S.R.cumulative v.cl v.cr) {psJ : List Head} (joins : JoinsK S.R v.psl v.psr psJ)
    (step : v.cl = v.cr ∨ CrossesK S.R v.cl v.psl psJ) :
    InJoinMeetFragmentK (joinStore inside.families v joins v.universe_cl (S.levels.cumulative_refl v.universe_cl) low
      rest) := by
  obtain ⟨group, grouped, compat⟩ := inside.grouped
  have together : group v.left = group v.right := grouped e List.mem_cons_self v
  have keep : ∀ Z, group (joinVar v.left v.right Z) = group Z := by
    intro Z
    unfold joinVar
    split_ifs with hZ
    · rcases hZ with hZ | hZ
      · rw [hZ, together]
      · rw [hZ]
    · rfl
  refine ⟨Miller.redecl_families Θ inside.families v.right psJ v.cl joins.universes v.universe_cl, ?_, ⟨group, ?_, ?_⟩⟩
  · intro e'' member
    obtain ⟨e', inRest, rfl⟩ := List.mem_map.mp member
    obtain ⟨w⟩ := inside.shapes e' (List.mem_cons_of_mem _ inRest)
    obtain ⟨t, _, _, _, _⟩ := join_viewK algebra inside.families v joins v.universe_cl
      (S.levels.cumulative_refl v.universe_cl) low w
    exact ⟨t⟩
  · intro e'' member u
    obtain ⟨e', inRest, rfl⟩ := List.mem_map.mp member
    obtain ⟨w⟩ := inside.shapes e' (List.mem_cons_of_mem _ inRest)
    obtain ⟨t, tl, tr, _, _⟩ := join_viewK algebra inside.families v joins v.universe_cl
      (S.levels.cumulative_refl v.universe_cl) low w
    obtain ⟨ul, ur⟩ := FlexK.unique u t
    rw [ul, ur, tl, tr, keep, keep]
    exact grouped e' (List.mem_cons_of_mem _ inRest) w
  · -- Compatibility in the new telescope.
    have newSelf : Ctx.lookup (joinedMK Θ inside.families v joins v.universe_cl).raw v.right = famCode psJ v.cl :=
      joinedMK_self Θ inside.families v joins v.universe_cl
    have newNe : ∀ {i : Fin Θ.arity}, i ≠ v.right →
        Ctx.lookup (joinedMK Θ inside.families v joins v.universe_cl).raw i = Ctx.lookup Θ.raw i :=
      fun ne => joinedMK_ne Θ inside.families v joins v.universe_cl ne
    -- The redeclared unknown against another one of its group.
    have against : ∀ (j : Fin Θ.arity), j ≠ v.right → group j = group v.right → ∀ (psj : List Head) (cj : Head),
        Ctx.lookup Θ.raw j = famCode psj cj →
          CompatJ S.R psJ v.cl psj cj ∧ (S.R.cumulative v.cl cj → S.R.cumulative cj v.cl → v.cl = cj) := by
      intro j ne gj psj cj declared
      by_cases hj : j = v.left
      · rw [hj] at declared
        obtain ⟨_, hc⟩ := famCode_inj (declared.symm.trans v.declared_left)
        rw [← hc]
        exact ⟨.inl rfl, fun _ _ => rfl⟩
      · have uj := Miller.famFacts inside.families declared
        obtain ⟨cLj, antiLj⟩ := compat v.left j (fun h => hj h.symm) (together.trans gj.symm) v.psl v.cl psj cj
          v.declared_left declared
        obtain ⟨cRj, _⟩ := compat v.right j (fun h => ne h.symm) gj.symm v.psr v.cr psj cj v.declared_right declared
        exact ⟨compatJ_join algebra v.universe_cl uj.2 uj.1 antiLj low joins step cLj cRj, antiLj⟩
    intro i j ne gij psi ci psj cj di dj
    by_cases hi : i = v.right
    · by_cases hj : j = v.right
      · exact absurd (hi.trans hj.symm) ne
      · rw [hi, newSelf] at di
        obtain ⟨rfl, rfl⟩ := famCode_inj di
        rw [newNe hj] at dj
        exact against j hj (gij.symm.trans (by rw [hi])) psj cj dj
    · by_cases hj : j = v.right
      · rw [hj, newSelf] at dj
        obtain ⟨rfl, rfl⟩ := famCode_inj dj
        rw [newNe hi] at di
        obtain ⟨c, a⟩ := against i hi (gij.trans (by rw [hj])) psi ci di
        exact ⟨c.symm, fun h₁ h₂ => (a h₂ h₁).symm⟩
      · rw [newNe hi] at di
        rw [newNe hj] at dj
        exact compat i j ne gij psi ci psj cj di dj

end Fragment

/-! ## The solver -/

section Solver

variable {S : Setting Head L}
variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)
  (headsTyped : ∀ {h u u' : Head}, S.R.headTyping h u → S.R.headTyping h u' → u = u')
  (join : Head → Head → Option Head)
  (joinSound : ∀ {u v w : Head}, join u v = some w → S.R.isUniverse w ∧ IsLub S.R w u v)
  (bias : ∀ {u v : Head}, S.R.isUniverse u → S.R.isUniverse v → S.R.cumulative v u → join u v = some u)

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative] in
include facts roots heads algebra rigid complete headsTyped in
/-- With one codomain, the join forces at the left codomain. -/
theorem joinK_forces_left {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexK e) (same : v.cl = v.cr)
    {psJ : List Head} (joins : JoinsK S.R v.psl v.psr psJ) : JoinForces v psJ v.cl := by
  rw [same]
  exact joinK_forces facts roots heads algebra rigid complete headsTyped v same joins

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative] in
theorem cl_below_cr {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexK e) (same : v.cl = v.cr) :
    S.R.cumulative v.cl v.cr := by
  rw [same]
  exact S.levels.cumulative_refl v.universe_cr

/-- **The join-meet step on a view whose left unknown has the smaller codomain.** -/
def joinMeetUpdate {Θ : Context S.R} (families : Miller.Families Θ) {e : Equation (TotalTerm Θ)} (v : FlexK e)
    (low : S.R.cumulative v.cl v.cr) {psJ : List Head} (joins : JoinsK S.R v.psl v.psr psJ)
    (forces : JoinForces v psJ v.cl) (rest : EquationStore (TotalTerm Θ)) : Update S.levels (e :: rest) :=
  joinRereadKUpdate families v joins v.universe_cl (S.levels.cumulative_refl v.universe_cl) low forces rest

/-- **One step on a read equation**: delete; the join with one codomain; the join with a meet toward the smaller
codomain, in either orientation. -/
def stepJoinMeetK {Θ : Context S.R} (families : Miller.Families Θ) {e : Equation (TotalTerm Θ)} (v : FlexK e)
    (rest : EquationStore (TotalTerm Θ)) : Round S.levels storeRank (e :: rest) :=
  if hsame : v.left = v.right then
    .progress (deleteCodes e (v.annotation_left.trans v.annotation_right.symm)
        (by rw [v.side_left, v.side_right, hsame]) rest)
      (below_of_length (by
        show rest.length < (e :: rest).length
        simp))
  else if hc : v.cl = v.cr then
    match hj : joinsOf join v.psl v.psr with
    | some _ =>
        .progress (joinMeetUpdate families v (cl_below_cr v hc) (joinsOf_sound join joinSound hj)
            (joinK_forces_left facts roots heads algebra rigid complete headsTyped v hc (joinsOf_sound join joinSound hj))
            rest)
          (below_of_length (by
            show (joinStore families v (joinsOf_sound join joinSound hj) v.universe_cl
              (S.levels.cumulative_refl v.universe_cl) _ rest).length < (e :: rest).length
            simp [joinStore]))
    | none => .stuck
  else if hx : S.R.cumulative v.cl v.cr ∧ CrossOK S.R v.cl v.psl v.psr then
    match hj : joinsOf join v.psl v.psr with
    | some _ =>
        .progress (joinMeetUpdate families v hx.1 (joinsOf_sound join joinSound hj)
            (joinMeetK_forces facts roots heads algebra rigid complete headsTyped v hx.1
              (joinsOf_sound join joinSound hj)
              (crosses_of_crossOK join joinSound bias v.universe_cl hx.2 v.universes_left v.universes_right hj))
            rest)
          (below_of_length (by
            show (joinStore families v (joinsOf_sound join joinSound hj) v.universe_cl
              (S.levels.cumulative_refl v.universe_cl) hx.1 rest).length < (e :: rest).length
            simp [joinStore]))
    | none => .stuck
  else if hy : S.R.cumulative v.cr v.cl ∧ CrossOK S.R v.cr v.psr v.psl then
    match hj : joinsOf join v.psr v.psl with
    | some _ =>
        .progress ((joinMeetUpdate families v.swap hy.1 (joinsOf_sound join joinSound hj)
            (joinMeetK_forces facts roots heads algebra rigid complete headsTyped v.swap hy.1
              (joinsOf_sound join joinSound hj)
              (crosses_of_crossOK join joinSound bias v.universe_cr hy.2 v.universes_right v.universes_left hj))
            rest).rephrase (swap_equivalent e rest))
          (below_of_length (by
            show (joinStore families v.swap (joinsOf_sound join joinSound hj) v.swap.universe_cl
              (S.levels.cumulative_refl v.swap.universe_cl) hy.1 rest).length < (e :: rest).length
            simp [joinStore]))
    | none => .stuck
  else .stuck

/-- **The round of the solver**: read the first equation, then step. -/
def joinMeetRoundK : {Γ : Context S.R} → (problem : EquationStore (TotalTerm Γ)) →
    Round S.levels storeRank problem
  | _, [] => .stuck
  | Θ, e :: rest =>
      if hfam : Miller.Families Θ then
        match hd : readFlexK e with
        | some _ =>
            stepJoinMeetK facts roots heads algebra rigid complete headsTyped join joinSound bias hfam (viewOfK hd) rest
        | none => .stuck
      else .stuck

/-- **The tree's driver with delete, the join and the join with a meet.** -/
def joinMeetSolverK : ContextualDependentWorklist.Solver S.levels where
  rank := storeRank
  round := joinMeetRoundK facts roots heads algebra rigid complete headsTyped join joinSound bias

/-- **The rules never refute.** -/
theorem joinMeetRoundK_ne_refuted {Γ : Context S.R} (problem : EquationStore (TotalTerm Γ))
    (absent : ¬ (frames S.levels).Solvable problem) :
    joinMeetRoundK facts roots heads algebra rigid complete headsTyped join joinSound bias problem ≠
      .refuted absent := by
  cases problem with
  | nil => intro h; cases h
  | cons e rest =>
      simp only [joinMeetRoundK]
      split_ifs with hfam
      · split
        · unfold stepJoinMeetK
          split_ifs
          · intro h; cases h
          · split
            · intro h; cases h
            · intro h; cases h
          · split
            · intro h; cases h
            · intro h; cases h
          · split
            · intro h; cases h
            · intro h; cases h
          · intro h; cases h
        · intro h; cases h
      · intro h; cases h

/-- **Progress by shape**: on a nonempty store of the fragment, with a total join function, the round is not
stuck. -/
theorem joinMeetRoundK_ne_stuck
    (total : ∀ {u v : Head}, S.R.isUniverse u → S.R.isUniverse v → ∃ w, join u v = some w)
    {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)} (inside : InJoinMeetFragmentK problem)
    (nonempty : problem ≠ []) :
    joinMeetRoundK facts roots heads algebra rigid complete headsTyped join joinSound bias problem ≠ .stuck := by
  cases problem with
  | nil => exact absurd rfl nonempty
  | cons e rest =>
      obtain ⟨v⟩ := inside.shapes e List.mem_cons_self
      obtain ⟨group, grouped, compat⟩ := inside.grouped
      have hd := readFlexK_complete v
      simp only [joinMeetRoundK, dif_pos inside.families]
      split
      · rename_i d hd'
        let w := viewOfK hd'
        have lengths : w.psl.length = w.psr.length := (lengths_left w).symm.trans (lengths_right w)
        obtain ⟨ws, hws⟩ := joinsOf_total join total lengths w.universes_left w.universes_right
        obtain ⟨ws', hws'⟩ := joinsOf_total join total lengths.symm w.universes_right w.universes_left
        unfold stepJoinMeetK
        split_ifs with h1 h2 h3 h4
        · intro h; cases h
        · split
          · intro h; cases h
          · rename_i hj
            rw [hws] at hj
            cases hj
        · split
          · intro h; cases h
          · rename_i hj
            rw [hws] at hj
            cases hj
        · split
          · intro h; cases h
          · rename_i hj
            rw [hws'] at hj
            cases hj
        · exfalso
          obtain ⟨c, _⟩ := compat w.left w.right h1 (grouped e List.mem_cons_self w) w.psl w.cl w.psr w.cr
            w.declared_left w.declared_right
          rcases c with c | c | c
          · exact h2 c
          · exact h3 c
          · exact h4 c
      · rename_i hd'
        rw [hd] at hd'
        cases hd'

/-- **The rules keep the fragment.** -/
theorem joinMeetRoundK_stable {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}
    {update : Update S.levels problem}
    {smaller : ContextualDependentWorklist.Below (storeRank update.remaining) (storeRank problem)}
    (inside : InJoinMeetFragmentK problem)
    (progressed : joinMeetRoundK facts roots heads algebra rigid complete headsTyped join joinSound bias problem =
      .progress update smaller) :
    InJoinMeetFragmentK update.remaining := by
  cases problem with
  | nil => cases progressed
  | cons e rest =>
      simp only [joinMeetRoundK] at progressed
      split_ifs at progressed with hfam
      split at progressed
      · rename_i d hd
        unfold stepJoinMeetK at progressed
        split_ifs at progressed with h1 h2 h3 h4
        · cases progressed
          exact inJoinMeetFragmentK_delete inside
        · split at progressed
          · rename_i psJ hj
            cases progressed
            exact inJoinMeetFragmentK_step algebra inside (viewOfK hd) _ (joinsOf_sound join joinSound hj) (.inl h2)
          · cases progressed
        · split at progressed
          · rename_i psJ hj
            cases progressed
            exact inJoinMeetFragmentK_step algebra inside (viewOfK hd) h3.1 (joinsOf_sound join joinSound hj)
              (.inr (crosses_of_crossOK join joinSound bias (viewOfK hd).universe_cl h3.2
                (viewOfK hd).universes_left (viewOfK hd).universes_right hj))
          · cases progressed
        · split at progressed
          · rename_i psJ hj
            cases progressed
            exact inJoinMeetFragmentK_step algebra (inJoinMeetFragmentK_swap inside) (viewOfK hd).swap h4.1
              (joinsOf_sound join joinSound hj)
              (.inr (crosses_of_crossOK join joinSound bias (viewOfK hd).universe_cr h4.2
                (viewOfK hd).universes_right (viewOfK hd).universes_left hj))
          · cases progressed
      · cases progressed

variable (total : ∀ {u v : Head}, S.R.isUniverse u → S.R.isUniverse v → ∃ w, join u v = some w)

/-- **The fragment of the join-meet solver.** -/
def joinMeetFragmentK :
    ContextualDependentWorklist.Fragment
      (joinMeetSolverK facts roots heads algebra rigid complete headsTyped join joinSound bias) where
  holds := InJoinMeetFragmentK
  stable := fun inside progressed =>
    joinMeetRoundK_stable facts roots heads algebra rigid complete headsTyped join joinSound bias inside progressed
  decisive := fun inside nonempty =>
    joinMeetRoundK_ne_stuck facts roots heads algebra rigid complete headsTyped join joinSound bias total inside
      nonempty

include facts roots heads algebra rigid complete headsTyped joinSound bias total in
/-- **Decided by shape**: on the join-meet fragment, two codomains and domains in any order, the tree's driver reaches,
at some budget and at every larger one, a principal answer. -/
theorem joinMeetK_decided {Θ : Context S.R} {original : EquationStore (TotalTerm Θ)}
    (inside : InJoinMeetFragmentK original) :
    ∃ fuel, ∀ larger, fuel ≤ larger →
      run (joinMeetSolverK facts roots heads algebra rigid complete headsTyped join joinSound bias) original larger =
          run (joinMeetSolverK facts roots heads algebra rigid complete headsTyped join joinSound bias) original
            fuel ∧
        ((∃ state finished,
            run (joinMeetSolverK facts roots heads algebra rigid complete headsTyped join joinSound bias) original
                larger = .solved state finished ∧ (frames S.levels).Principal original state.answer) ∨
          (∃ absent,
            run (joinMeetSolverK facts roots heads algebra rigid complete headsTyped join joinSound bias) original
              larger = .refuted absent)) :=
  (joinMeetFragmentK facts roots heads algebra rigid complete headsTyped join joinSound bias total).decided inside

include facts roots heads algebra rigid complete headsTyped joinSound bias total in
/-- **Every store of the join-meet fragment has a principal answer.** -/
theorem principal_of_inJoinMeetFragmentK {Θ : Context S.R} {original : EquationStore (TotalTerm Θ)}
    (inside : InJoinMeetFragmentK original) :
    ∃ (Δ : Context S.R) (answer : Δ ⟶ Θ), (frames S.levels).Principal original answer := by
  obtain ⟨fuel, ends⟩ := joinMeetK_decided facts roots heads algebra rigid complete headsTyped join joinSound bias
    total inside
  rcases (ends fuel le_rfl).2 with ⟨state, _, _, principal⟩ | ⟨absent, refuted⟩
  · exact ⟨_, _, principal⟩
  · exact absurd refuted (drive_ne_refuted
      (joinMeetSolverK facts roots heads algebra rigid complete headsTyped join joinSound bias)
      (fun problem absent =>
        joinMeetRoundK_ne_refuted facts roots heads algebra rigid complete headsTyped join joinSound bias problem
          absent)
      fuel _ absent)

end Solver

/-! ## The fragment of meet groups is contained -/

section Contained

variable {S : Setting Head L}

theorem crossOK_of_le : ∀ {ps ps' : List Head}, List.Forall₂ S.R.cumulative ps' ps → ∀ (c : Head),
    CrossOK S.R c ps ps'
  | _, _, .nil, _ => .nil
  | _, _, .cons le rest, c => .cons (.inl le) (crossOK_of_le rest c)

theorem crossOK_of_bounded : ∀ {ps ps' : List Head}, List.Forall₂ S.R.cumulative ps ps' → ∀ {c : Head},
    (∀ p ∈ ps', S.R.cumulative p c) → (algebra : CumulativeAlgebra S.R) → CrossOK S.R c ps ps'
  | _, _, .nil, _, _, _ => .nil
  | _, _, .cons le rest, _, bounded, algebra =>
      .cons (.inr ⟨algebra.trans le (bounded _ List.mem_cons_self), bounded _ List.mem_cons_self⟩)
        (crossOK_of_bounded rest (fun p member => bounded p (List.mem_cons_of_mem _ member)) algebra)

/-- **The pairwise condition of meet groups implies compatibility**: domain raising and the true meet are cases of the
crossing. -/
theorem compatJ_of_compatK (algebra : CumulativeAlgebra S.R) {ps : List Head} {c : Head} {ps' : List Head}
    {c' : Head} (h : CompatK S.R ps c ps' c') : CompatJ S.R ps c ps' c' := by
  rcases h with ⟨le, cc⟩ | ⟨le, cc⟩ | ⟨le, cc, bounded⟩ | ⟨le, cc, bounded⟩
  · exact .inr (.inl ⟨cc, crossOK_of_le le c⟩)
  · exact .inr (.inr ⟨cc, crossOK_of_le le c'⟩)
  · exact .inr (.inl ⟨cc, crossOK_of_bounded le bounded algebra⟩)
  · exact .inr (.inr ⟨cc, crossOK_of_bounded le bounded algebra⟩)

/-- **The fragment of meet groups is contained** in the join-meet fragment, over a telescope of universe families
whose cumulatively equivalent codomains are equal. -/
theorem inJoinMeetFragmentK_of_meet (algebra : CumulativeAlgebra S.R) {Θ : Context S.R}
    {problem : EquationStore (TotalTerm Θ)} (inside : InMeetFragmentK problem) (families : Miller.Families Θ)
    (antisym : ∀ (i j : Fin Θ.arity) (psi : List Head) (ci : Head) (psj : List Head) (cj : Head),
      Ctx.lookup Θ.raw i = famCode psi ci → Ctx.lookup Θ.raw j = famCode psj cj →
        S.R.cumulative ci cj → S.R.cumulative cj ci → ci = cj) :
    InJoinMeetFragmentK problem := by
  obtain ⟨group, grouped, comparable⟩ := inside.grouped
  exact ⟨families, inside.shapes, ⟨group, grouped, fun i j ne together psi ci psj cj di dj =>
    ⟨compatJ_of_compatK algebra (comparable i j ne together psi ci psj cj di dj), antisym i j psi ci psj cj di dj⟩⟩⟩

end Contained

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
