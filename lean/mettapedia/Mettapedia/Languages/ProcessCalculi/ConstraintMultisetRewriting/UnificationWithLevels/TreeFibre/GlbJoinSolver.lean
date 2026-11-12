import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.GlbJoin

/-!
# The glb-join solver: flex–flex equations of families, any codomains, any domains, decided

**Crossing well** (`CrossCompat`): two declared families of one arity cross well when every position is `CrossAt`:
a position whose domain lies below its own codomain on both sides has each domain below the other side's codomain.

**The fragment** (`InGlbJoinFragmentK`): a telescope of families; flex–flex equations of families with several
parameters; a grouping of the unknowns, every equation inside one group, every two unknowns of a group crossing well.
No condition compares codomains: they may be equal, comparable or incomparable.

**The round** deletes an equation of one unknown; otherwise it applies the glb join (`GlbJoin`): the right unknown
declared again at the least upper bounds of the domains and a greatest lower bound of the codomains, both unknowns sent
to its η-expansion, the other equations re-read.

**Kept by the rounds** (`glbJoinRoundK_stable`): the redeclared unknown crosses well with every unknown that crossed well
with both joined ones (`crossAt_join`), and with the left one (`crossAt_joined_left`). No antisymmetry of codomains is
used. **Decided** (`glbJoinK_decided`).

**Containment** (`inGlbJoinFragmentK_of_joinMeet`): the fragment of the join-meet solver lies inside, its condition
"cumulatively equivalent codomains are equal" dropped.
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

/-! ## Crossing well -/

section Cross

/-- **Two declared families cross well**: of different arities, or `CrossAt` at every position. -/
def CrossCompat (R : Rules Head) (ps : List Head) (c : Head) (ps' : List Head) (c' : Head) : Prop :=
  ps.length = ps'.length → List.Forall₂ (CrossAt R c c') ps ps'

instance (R : Rules Head) [DecidableRel R.cumulative] (ps : List Head) (c : Head) (ps' : List Head) (c' : Head) :
    Decidable (CrossCompat R ps c ps' c') := by
  unfold CrossCompat
  infer_instance

theorem CrossCompat.symm {R : Rules Head} {ps : List Head} {c : Head} {ps' : List Head} {c' : Head}
    (h : CrossCompat R ps c ps' c') : CrossCompat R ps' c' ps c :=
  fun lengths => crossAt_forall₂_symm (h lengths.symm)

variable {S : Setting Head L} (algebra : CumulativeAlgebra S.R)

include algebra in
/-- **The redeclared unknown crosses well with every unknown that crossed well with both joined ones.** -/
theorem crossAt_join {cF cG cW gl : Head} (hcW : S.R.isUniverse cW) (glb : IsGlb S.R gl cF cG) :
    ∀ {psF psG psJ : List Head}, JoinsK S.R psF psG psJ → ∀ {psW : List Head},
      List.Forall₂ (CrossAt S.R cF cW) psF psW → List.Forall₂ (CrossAt S.R cG cW) psG psW → AllUniverses S.R psW →
      List.Forall₂ (CrossAt S.R gl cW) psJ psW := by
  intro psF psG psJ joins
  induction joins with
  | nil =>
      intro psW hF _ _
      cases hF
      exact .nil
  | @cons pF pG pJ psF' psG' psJ' _ lub _ ih =>
      intro psW hF hG universes
      cases hF with
      | @cons _ pW _ psW' hereF restF =>
          cases hG with
          | cons hereG restG =>
              refine .cons (fun hJ hW => ?_) (ih restF restG universes.tail)
              obtain ⟨pFcW, pWcF⟩ := hereF (algebra.trans lub.1 (algebra.trans hJ glb.2.1)) hW
              obtain ⟨pGcW, pWcG⟩ := hereG (algebra.trans lub.2.1 (algebra.trans hJ glb.2.2.1)) hW
              exact ⟨lub.2.2 cW hcW pFcW pGcW, glb.2.2.2 pW universes.head pWcF pWcG⟩

include algebra in
/-- **The left unknown, kept declared, crosses well with the redeclared one.** -/
theorem crossAt_joined_left {cF cG gl : Head} (glb : IsGlb S.R gl cF cG) :
    ∀ {psF psG psJ : List Head}, JoinsK S.R psF psG psJ → List.Forall₂ (CrossAt S.R cF gl) psF psJ := by
  intro psF psG psJ joins
  induction joins with
  | nil => exact .nil
  | cons _ lub _ ih => exact .cons (fun _ hJ => ⟨algebra.trans lub.1 hJ, algebra.trans hJ glb.2.1⟩) ih

include algebra in
/-- **The join-meet solver's compatibility implies crossing well.** -/
theorem crossCompat_of_compatJ {ps : List Head} {c : Head} {ps' : List Head} {c' : Head}
    (h : CompatJ S.R ps c ps' c') : CrossCompat S.R ps c ps' c' := by
  intro lengths
  rcases h with rfl | ⟨le, ok⟩ | ⟨le, ok⟩
  · exact crossAt_same_all S.R c lengths
  · exact crossAt_of_crossOK algebra.trans le ok
  · exact crossAt_forall₂_symm (crossAt_of_crossOK algebra.trans le ok)

end Cross

/-! ## The fragment -/

section Fragment

variable {S : Setting Head L}

/-- Within a group, every two declared families cross well. -/
def GroupCross (Θ : Context S.R) (group : Fin Θ.arity → Nat) : Prop :=
  ∀ i j : Fin Θ.arity, i ≠ j → group i = group j → ∀ (psi : List Head) (ci : Head) (psj : List Head) (cj : Head),
    Ctx.lookup Θ.raw i = famCode psi ci → Ctx.lookup Θ.raw j = famCode psj cj → CrossCompat S.R psi ci psj cj

/-- **The fragment of the glb-join solver.** -/
structure InGlbJoinFragmentK {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Prop where
  families : Miller.Families Θ
  shapes : ∀ e ∈ problem, Nonempty (FlexK e)
  grouped : ∃ group : Fin Θ.arity → Nat,
    (∀ e ∈ problem, ∀ w : FlexK e, group w.left = group w.right) ∧ GroupCross Θ group

theorem inGlbJoinFragmentK_delete {Θ : Context S.R} {e : Equation (TotalTerm Θ)}
    {rest : EquationStore (TotalTerm Θ)} (inside : InGlbJoinFragmentK (e :: rest)) : InGlbJoinFragmentK rest := by
  obtain ⟨group, grouped, compat⟩ := inside.grouped
  exact ⟨inside.families, fun e' member => inside.shapes e' (List.mem_cons_of_mem _ member),
    ⟨group, fun e' member => grouped e' (List.mem_cons_of_mem _ member), compat⟩⟩

variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
  (algebra : CumulativeAlgebra S.R)

include algebra in
/-- **The glb-join step keeps the fragment**: the right unknown is declared again at `Π (x̄ : U_{p̄J}). U_g`. -/
theorem inGlbJoinFragmentK_step {Θ : Context S.R} {e : Equation (TotalTerm Θ)}
    {rest : EquationStore (TotalTerm Θ)} (inside : InGlbJoinFragmentK (e :: rest)) (v : FlexK e) {gl : Head}
    (glb : IsGlb S.R gl v.cl v.cr) {psJ : List Head} (joins : JoinsK S.R v.psl v.psr psJ) :
    InGlbJoinFragmentK (joinStore inside.families v joins glb.1 glb.2.1 glb.2.2.1 rest) := by
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
  refine ⟨Miller.redecl_families Θ inside.families v.right psJ gl joins.universes glb.1, ?_, ⟨group, ?_, ?_⟩⟩
  · intro e'' member
    obtain ⟨e', inRest, rfl⟩ := List.mem_map.mp member
    obtain ⟨w⟩ := inside.shapes e' (List.mem_cons_of_mem _ inRest)
    obtain ⟨t, _, _, _, _⟩ := join_viewK algebra inside.families v joins glb.1 glb.2.1 glb.2.2.1 w
    exact ⟨t⟩
  · intro e'' member u
    obtain ⟨e', inRest, rfl⟩ := List.mem_map.mp member
    obtain ⟨w⟩ := inside.shapes e' (List.mem_cons_of_mem _ inRest)
    obtain ⟨t, tl, tr, _, _⟩ := join_viewK algebra inside.families v joins glb.1 glb.2.1 glb.2.2.1 w
    obtain ⟨ul, ur⟩ := FlexK.unique u t
    rw [ul, ur, tl, tr, keep, keep]
    exact grouped e' (List.mem_cons_of_mem _ inRest) w
  · have newSelf : Ctx.lookup (joinedMK Θ inside.families v joins glb.1).raw v.right = famCode psJ gl :=
      joinedMK_self Θ inside.families v joins glb.1
    have newNe : ∀ {i : Fin Θ.arity}, i ≠ v.right →
        Ctx.lookup (joinedMK Θ inside.families v joins glb.1).raw i = Ctx.lookup Θ.raw i :=
      fun ne => joinedMK_ne Θ inside.families v joins glb.1 ne
    have lengthJ : v.psl.length = psJ.length := joins.length_left
    -- The redeclared unknown against another one of its group.
    have against : ∀ (j : Fin Θ.arity), j ≠ v.right → group j = group v.right → ∀ (psj : List Head) (cj : Head),
        Ctx.lookup Θ.raw j = famCode psj cj → CrossCompat S.R psJ gl psj cj := by
      intro j ne gj psj cj declared
      by_cases hj : j = v.left
      · rw [hj] at declared
        obtain ⟨hps, hc⟩ := famCode_inj (declared.symm.trans v.declared_left)
        rw [hps, hc]
        exact fun _ => crossAt_forall₂_symm (crossAt_joined_left algebra glb joins)
      · have uj := Miller.famFacts inside.families declared
        have cLj := compat v.left j (fun h => hj h.symm) (together.trans gj.symm) v.psl v.cl psj cj
          v.declared_left declared
        have cRj := compat v.right j (fun h => ne h.symm) gj.symm v.psr v.cr psj cj v.declared_right declared
        intro lengths
        have lengthR : v.psr.length = psJ.length := forall₂_length joins.right
        exact crossAt_join algebra uj.2 glb joins (cLj (lengthJ.trans lengths)) (cRj (lengthR.trans lengths)) uj.1
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
        exact (against i hi (gij.trans (by rw [hj])) psi ci di).symm
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
  (meet : Head → Head → Option Head)
  (meetSound : ∀ {u v g : Head}, meet u v = some g → IsGlb S.R g u v)

/-- **One step on a read equation**: delete; otherwise the glb join, when every position crosses. -/
def stepGlbJoinK {Θ : Context S.R} (families : Miller.Families Θ) {e : Equation (TotalTerm Θ)} (v : FlexK e)
    (rest : EquationStore (TotalTerm Θ)) : Round S.levels storeRank (e :: rest) :=
  if hsame : v.left = v.right then
    .progress (deleteCodes e (v.annotation_left.trans v.annotation_right.symm)
        (by rw [v.side_left, v.side_right, hsame]) rest)
      (below_of_length (by
        show rest.length < (e :: rest).length
        simp))
  else if hx : List.Forall₂ (CrossAt S.R v.cl v.cr) v.psl v.psr then
    match hg : meet v.cl v.cr with
    | some _ =>
        match hj : joinsOf join v.psl v.psr with
        | some _ =>
            .progress (joinRereadKUpdate families v (joinsOf_sound join joinSound hj) (meetSound hg).1
                (meetSound hg).2.1 (meetSound hg).2.2.1
                (glbJoinK_forces facts roots heads algebra rigid complete headsTyped v (meetSound hg)
                  (joinsOf_sound join joinSound hj) hx) rest)
              (below_of_length (by
                show (joinStore families v (joinsOf_sound join joinSound hj) (meetSound hg).1 (meetSound hg).2.1
                  (meetSound hg).2.2.1 rest).length < (e :: rest).length
                simp [joinStore]))
        | none => .stuck
    | none => .stuck
  else .stuck

/-- **The round of the solver**: read the first equation, then step. -/
def glbJoinRoundK : {Γ : Context S.R} → (problem : EquationStore (TotalTerm Γ)) →
    Round S.levels storeRank problem
  | _, [] => .stuck
  | Θ, e :: rest =>
      if hfam : Miller.Families Θ then
        match hd : readFlexK e with
        | some _ =>
            stepGlbJoinK facts roots heads algebra rigid complete headsTyped join joinSound meet meetSound hfam
              (viewOfK hd) rest
        | none => .stuck
      else .stuck

/-- **The tree's driver with delete and the glb join.** -/
def glbJoinSolverK : ContextualDependentWorklist.Solver S.levels where
  rank := storeRank
  round := glbJoinRoundK facts roots heads algebra rigid complete headsTyped join joinSound meet meetSound

/-- **The rules never refute.** -/
theorem glbJoinRoundK_ne_refuted {Γ : Context S.R} (problem : EquationStore (TotalTerm Γ))
    (absent : ¬ (frames S.levels).Solvable problem) :
    glbJoinRoundK facts roots heads algebra rigid complete headsTyped join joinSound meet meetSound problem ≠
      .refuted absent := by
  cases problem with
  | nil => intro h; cases h
  | cons e rest =>
      simp only [glbJoinRoundK]
      split_ifs with hfam
      · split
        · unfold stepGlbJoinK
          split_ifs
          · intro h; cases h
          · split
            · split
              · intro h; cases h
              · intro h; cases h
            · intro h; cases h
          · intro h; cases h
        · intro h; cases h
      · intro h; cases h

/-- **Progress by shape**: on a nonempty store of the fragment, with total join and meet functions, the round is not
stuck. -/
theorem glbJoinRoundK_ne_stuck
    (joinTotal : ∀ {u v : Head}, S.R.isUniverse u → S.R.isUniverse v → ∃ w, join u v = some w)
    (meetTotal : ∀ {u v : Head}, S.R.isUniverse u → S.R.isUniverse v → ∃ g, meet u v = some g)
    {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)} (inside : InGlbJoinFragmentK problem)
    (nonempty : problem ≠ []) :
    glbJoinRoundK facts roots heads algebra rigid complete headsTyped join joinSound meet meetSound problem ≠
      .stuck := by
  cases problem with
  | nil => exact absurd rfl nonempty
  | cons e rest =>
      obtain ⟨v⟩ := inside.shapes e List.mem_cons_self
      obtain ⟨group, grouped, compat⟩ := inside.grouped
      have hd := readFlexK_complete v
      simp only [glbJoinRoundK, dif_pos inside.families]
      split
      · rename_i d hd'
        let w := viewOfK hd'
        have lengths : w.psl.length = w.psr.length := (lengths_left w).symm.trans (lengths_right w)
        obtain ⟨ws, hws⟩ := joinsOf_total join joinTotal lengths w.universes_left w.universes_right
        obtain ⟨g, hg⟩ := meetTotal w.universe_cl w.universe_cr
        unfold stepGlbJoinK
        split_ifs with h1 h2
        · intro h; cases h
        · split
          · split
            · intro h; cases h
            · rename_i hj
              rw [hws] at hj
              cases hj
          · rename_i hg'
            rw [hg] at hg'
            cases hg'
        · exact absurd (compat w.left w.right h1 (grouped e List.mem_cons_self w) w.psl w.cl w.psr w.cr
            w.declared_left w.declared_right lengths) h2
      · rename_i hd'
        rw [hd] at hd'
        cases hd'

/-- **The rules keep the fragment.** -/
theorem glbJoinRoundK_stable {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}
    {update : Update S.levels problem}
    {smaller : ContextualDependentWorklist.Below (storeRank update.remaining) (storeRank problem)}
    (inside : InGlbJoinFragmentK problem)
    (progressed : glbJoinRoundK facts roots heads algebra rigid complete headsTyped join joinSound meet meetSound
      problem = .progress update smaller) :
    InGlbJoinFragmentK update.remaining := by
  cases problem with
  | nil => cases progressed
  | cons e rest =>
      simp only [glbJoinRoundK] at progressed
      split_ifs at progressed with hfam
      split at progressed
      · rename_i d hd
        unfold stepGlbJoinK at progressed
        split_ifs at progressed with h1 h2
        · cases progressed
          exact inGlbJoinFragmentK_delete inside
        · split at progressed
          · rename_i gl hg
            split at progressed
            · rename_i psJ hj
              cases progressed
              exact inGlbJoinFragmentK_step algebra inside (viewOfK hd) (meetSound hg)
                (joinsOf_sound join joinSound hj)
            · cases progressed
          · cases progressed
      · cases progressed

variable (joinTotal : ∀ {u v : Head}, S.R.isUniverse u → S.R.isUniverse v → ∃ w, join u v = some w)
  (meetTotal : ∀ {u v : Head}, S.R.isUniverse u → S.R.isUniverse v → ∃ g, meet u v = some g)

/-- **The fragment of the glb-join solver.** -/
def glbJoinFragmentK :
    ContextualDependentWorklist.Fragment
      (glbJoinSolverK facts roots heads algebra rigid complete headsTyped join joinSound meet meetSound) where
  holds := InGlbJoinFragmentK
  stable := fun inside progressed =>
    glbJoinRoundK_stable facts roots heads algebra rigid complete headsTyped join joinSound meet meetSound inside
      progressed
  decisive := fun inside nonempty =>
    glbJoinRoundK_ne_stuck facts roots heads algebra rigid complete headsTyped join joinSound meet meetSound joinTotal
      meetTotal inside nonempty

include facts roots heads algebra rigid complete headsTyped joinSound meetSound joinTotal meetTotal in
/-- **Decided by shape**: on the glb-join fragment, any codomains and domains in any order, the tree's driver reaches,
at some budget and at every larger one, a principal answer. -/
theorem glbJoinK_decided {Θ : Context S.R} {original : EquationStore (TotalTerm Θ)}
    (inside : InGlbJoinFragmentK original) :
    ∃ fuel, ∀ larger, fuel ≤ larger →
      run (glbJoinSolverK facts roots heads algebra rigid complete headsTyped join joinSound meet meetSound) original
          larger =
        run (glbJoinSolverK facts roots heads algebra rigid complete headsTyped join joinSound meet meetSound)
          original fuel ∧
        ((∃ state finished,
            run (glbJoinSolverK facts roots heads algebra rigid complete headsTyped join joinSound meet meetSound)
                original larger = .solved state finished ∧ (frames S.levels).Principal original state.answer) ∨
          (∃ absent,
            run (glbJoinSolverK facts roots heads algebra rigid complete headsTyped join joinSound meet meetSound)
              original larger = .refuted absent)) :=
  (glbJoinFragmentK facts roots heads algebra rigid complete headsTyped join joinSound meet meetSound joinTotal
    meetTotal).decided inside

include facts roots heads algebra rigid complete headsTyped joinSound meetSound joinTotal meetTotal in
/-- **Every store of the glb-join fragment has a principal answer.** -/
theorem principal_of_inGlbJoinFragmentK {Θ : Context S.R} {original : EquationStore (TotalTerm Θ)}
    (inside : InGlbJoinFragmentK original) :
    ∃ (Δ : Context S.R) (answer : Δ ⟶ Θ), (frames S.levels).Principal original answer := by
  obtain ⟨fuel, ends⟩ := glbJoinK_decided facts roots heads algebra rigid complete headsTyped join joinSound meet
    meetSound joinTotal meetTotal inside
  rcases (ends fuel le_rfl).2 with ⟨state, _, _, principal⟩ | ⟨absent, refuted⟩
  · exact ⟨_, _, principal⟩
  · exact absurd refuted (drive_ne_refuted
      (glbJoinSolverK facts roots heads algebra rigid complete headsTyped join joinSound meet meetSound)
      (fun problem absent =>
        glbJoinRoundK_ne_refuted facts roots heads algebra rigid complete headsTyped join joinSound meet meetSound
          problem absent)
      fuel _ absent)

end Solver

/-! ## The join-meet fragment is contained, without its condition on equivalent codomains -/

section Contained

variable {S : Setting Head L}

/-- **The fragment of the join-meet solver is contained**, and its condition "cumulatively equivalent codomains are
equal" is not used. -/
theorem inGlbJoinFragmentK_of_joinMeet (algebra : CumulativeAlgebra S.R) {Θ : Context S.R}
    {problem : EquationStore (TotalTerm Θ)} (inside : InJoinMeetFragmentK problem) : InGlbJoinFragmentK problem := by
  obtain ⟨group, grouped, compat⟩ := inside.grouped
  exact ⟨inside.families, inside.shapes, ⟨group, grouped, fun i j ne together psi ci psj cj di dj =>
    crossCompat_of_compatJ algebra (compat i j ne together psi ci psj cj di dj).1⟩⟩

end Contained

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
