import Mettapedia.Logic.ASP.RUP
import Mettapedia.Logic.ASP.HallStep

/-!
# Answer set refutation certificates: LRAT, loop-nogood and Hall additions

An answer set solver refutes a program with loop nogoods as well as with the
completion, and loop nogoods are not RUP consequences of the completion. A
certificate is therefore a list of steps (`CertStep`) of three kinds:

* an LRAT action (`CertStep.lrat`): a RUP addition `rup id clause hints`, checked
  by the RUP test of the action-by-action LRAT checker, or a deletion; additions
  that are only resolution-asymmetric are refused;
* a loop-nogood addition (`CertStep.loop id clause atoms atom`): the clause of the
  loop nogood of the atom set with variable numbers `atoms`, for the atom with
  number `atom`. The checker decodes the numbers to atoms of the program
  (`Program.atomOf`), requires `atom` to be among them, recomputes the external
  bodies of the set, and requires the stated clause to have exactly the literals
  of the recomputed one (`Program.loopStepOk`). A set holding a falsum atom is
  refused: the rules of a falsum atom have no body variables;
* a Hall addition (`CertStep.hall id clause groups cliques`): a clause of positive
  atom literals, standing for a set `E` of atoms, with rule numbers `groups` and
  lists of atom numbers `cliques`. The checker (`Program.hallStepOk`) requires
  the groups to be at-least-one rules whose groups of atoms are pairwise disjoint,
  the cliques to be nonempty, pairwise disjoint and to have an exclusion rule of
  the program for any two of their atoms, every group atom to be in `E` or in a
  clique, and fewer cliques than groups. Pigeonhole-shaped clauses that resolution
  needs exponentially many steps for are then one counting step
  (`Program.hall_step_sound`).

The checker (`Program.checkCert`) starts from the numbered completion with
identifiers `1, 2, …` (`Program.inputs`), applies the steps in order
(`Program.certStep`, `Program.certRun`), and accepts when the empty clause is
among the live clauses.

## Soundness

* Every live clause holds in the numbered assignment of every stable model
  (`Program.certRun_holds`): the completion clauses because stable models are
  supported, RUP additions by RUP soundness, loop additions because the loop
  nogood of any set of atoms containing the atom is entailed, Hall additions by
  counting (`Program.hallStepOk_sat`).
* **An accepted certificate means the program has no stable model**
  (`Program.checkCert_sound`).

The set of a loop step need not be a loop: soundness needs only that the atom is
in the set (`Program.loopNogood_entailed`), and by `loopNogoodList_ok_iff` the
loop nogoods of all sets of program atoms without falsum atoms already
characterize the stable models. Requiring the atom to be in the set is necessary: the nogood of a set
not containing its atom can exclude a stable model, and the checker refuses it.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ASP

open Mettapedia.GSLT.Logic PropositionalFormula

universe u

variable {A : Type u}

/-- A step of an answer set refutation certificate. -/
inductive CertStep
  /-- An LRAT action: a RUP addition or a deletion. -/
  | lrat (action : PropositionalLRATActions.Action)
  /-- Add `clause`, the clause of the loop nogood of the atoms numbered `atoms`, for the atom
  numbered `atom`, under the identifier `id`. -/
  | loop (id : ℕ) (clause : Clause) (atoms : List ℕ) (atom : ℕ)
  /-- Add `clause`, positive atom literals for a set `E`, under the identifier `id`: the at-least-one
  rules numbered `groups` have their group atoms in `E` or in the cliques of atoms numbered `cliques`,
  and there are fewer cliques than groups. -/
  | hall (id : ℕ) (clause : Clause) (groups : List ℕ) (cliques : List (List ℕ))

/-- The LRAT actions of a certificate, in order. -/
def CertStep.lratActions (steps : List CertStep) : List PropositionalLRATActions.Action :=
  steps.filterMap fun
    | .lrat action => some action
    | .loop _ _ _ _ => none
    | .hall _ _ _ _ => none

/-- The clause an identifier names among the live clauses. -/
def lookupClause (live : List (ℕ × Clause)) (id : ℕ) : Option Clause :=
  (live.find? fun e => e.1 == id).map Prod.snd

/-- Clauses numbered from `k` on. -/
def numberFrom : ℕ → List Clause → List (ℕ × Clause)
  | _, [] => []
  | k, c :: F => (k, c) :: numberFrom (k + 1) F

/-- The live clauses hold under the assignment `σ`. -/
def LiveHolds (σ : ℕ → Bool) (live : List (ℕ × Clause)) : Prop := ∀ e ∈ live, Clause.sat σ e.2 = true

theorem lookupClause_mem {live : List (ℕ × Clause)} {id : ℕ} {c : Clause} (h : lookupClause live id = some c) :
    (id, c) ∈ live := by
  unfold lookupClause at h
  obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp h
  have := List.find?_some he
  have mem := List.mem_of_find?_eq_some he
  simp only [beq_iff_eq] at this
  rw [← this]
  exact mem

theorem mapM_lookupClause_mem {live : List (ℕ × Clause)} :
    ∀ {hints : List ℕ} {premises : List Clause}, hints.mapM (lookupClause live) = some premises →
      ∀ c ∈ premises, ∃ e ∈ live, e.2 = c
  | [], premises, h => by
    simp only [List.mapM_nil] at h
    cases Option.some.inj h
    simp
  | id :: hints, premises, h => by
    cases hid : lookupClause live id with
    | none => simp [List.mapM_cons, hid] at h
    | some c =>
      cases hrest : hints.mapM (lookupClause live) with
      | none => simp [List.mapM_cons, hid, hrest] at h
      | some rest =>
        simp only [List.mapM_cons, hid, hrest, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at h
        subst h
        rintro c' (_ | ⟨_, hc'⟩)
        · exact ⟨_, lookupClause_mem hid, rfl⟩
        · exact mapM_lookupClause_mem hrest c' hc'

theorem numberFrom_mem : ∀ {k : ℕ} {F : List Clause} {e : ℕ × Clause}, e ∈ numberFrom k F → e.2 ∈ F
  | _, [], _, h => by simp [numberFrom] at h
  | k, c :: F, e, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (numberFrom_mem h)

theorem lookupClause_numberFrom : ∀ (k j : ℕ) (F : List Clause), lookupClause (numberFrom k F) (k + j) = F[j]?
  | _, _, [] => rfl
  | k, j, c :: F => by
    cases j with
    | zero => simp [lookupClause, numberFrom]
    | succ j =>
      have ne : (k == k + (j + 1)) = false := by simp
      have := lookupClause_numberFrom (k + 1) j F
      rw [show k + 1 + j = k + (j + 1) by omega] at this
      simp only [lookupClause, numberFrom, List.find?_cons, ne] at this ⊢
      simpa using this

theorem numberFrom_lt : ∀ {k : ℕ} {F : List Clause} {e : ℕ × Clause}, e ∈ numberFrom k F → e.1 < k + F.length
  | _, [], _, h => by simp [numberFrom] at h
  | k, c :: F, e, h => by
    rcases List.mem_cons.mp h with rfl | h
    · simp
    · have := numberFrom_lt h
      simp only [List.length_cons]
      omega

section Checker

variable [DecidableEq A]

namespace Program

variable (P : Program A)

/-- The atom a variable number stands for, if it stands for an atom. -/
def atomOf (i : ℕ) : Option A :=
  match P.varList[i]? with
  | some (.atom a) => some a
  | _ => none

/-- The clause of the loop nogood of the atoms numbered `atoms` for the atom numbered `atom`;
`none` unless every number stands for an atom that is no falsum atom, and `atom` is among them. -/
def loopClause (atoms : List ℕ) (atom : ℕ) : Option Clause :=
  if atoms.all (fun i => (P.atomOf i).any fun a => !P.falsum a) && decide (atom ∈ atoms) then
    (P.atomOf atom).map fun a => P.lratClause (P.loopNogood (atoms.filterMap P.atomOf).toFinset a).lits
  else none

/-- A loop step is well formed: its clause has exactly the literals of the recomputed loop
clause. -/
def loopStepOk (clause : Clause) (atoms : List ℕ) (atom : ℕ) : Bool :=
  match P.loopClause atoms atom with
  | some c => c.all (fun l => decide (l ∈ clause)) && clause.all fun l => decide (l ∈ c)
  | none => false

/-- The atom a literal makes true, if it is a positive literal of an atom. -/
def posAtom : Literal → Option A
  | .pos i => P.atomOf i
  | .neg _ => none

/-- **A Hall step is well formed.** The clause has only positive atom literals; the cliques are
nonempty, pairwise disjoint lists of atom numbers, and any two distinct atoms of a clique have an
exclusion rule in the program; the groups number at-least-one rules of the program with pairwise
disjoint groups of atoms, every one of which is in the clause or in a clique; and there are fewer
cliques than groups. -/
def hallStepOk (clause : Clause) (groups : List ℕ) (cliques : List (List ℕ)) : Bool :=
  match groups.mapM (P[·]?) with
  | none => false
  | some rules =>
    clause.all (fun l => (P.posAtom l).isSome) &&
      cliques.all (fun cl => !cl.isEmpty && cl.all fun i => (P.atomOf i).isSome) &&
      decide cliques.flatten.Nodup &&
      cliques.all (fun cl =>
        (cl.filterMap P.atomOf).all fun a => (cl.filterMap P.atomOf).all fun b => a == b || P.excludes a b) &&
      rules.all P.isAtLeastOne &&
      decide (rules.Pairwise fun r q => ∀ a ∈ r.group, a ∉ q.group) &&
      rules.all (fun r => r.group.all fun a =>
        decide (a ∈ clause.filterMap P.posAtom) || cliques.any fun cl => decide (a ∈ cl.filterMap P.atomOf)) &&
      decide (cliques.length < rules.length)

/-- **One step of the certificate checker** on the live clauses. -/
def certStep (live : List (ℕ × Clause)) : CertStep → Option (List (ℕ × Clause))
  | .lrat (.rup id clause hints) =>
    if (lookupClause live id).isSome then none
    else
      match hints.mapM (lookupClause live) with
      | some premises => if PropositionalLRATActions.rupCheck premises clause then some ((id, clause) :: live) else none
      | none => none
  | .lrat (.rat _ _) => none
  | .lrat (.delete ids) => some (live.filter fun e => !ids.contains e.1)
  | .loop id clause atoms atom =>
    if (lookupClause live id).isSome then none
    else if P.loopStepOk clause atoms atom then some ((id, clause) :: live) else none
  | .hall id clause groups cliques =>
    if (lookupClause live id).isSome then none
    else if P.hallStepOk clause groups cliques then some ((id, clause) :: live) else none

/-- The numbered completion, each clause without repeated literals. -/
def completionLRAT : List Clause := P.completionNogoods.map fun δ => P.lratClause δ.lits

/-- The input clauses with identifiers `1, 2, …`. -/
def inputs : List (ℕ × Clause) := numberFrom 1 P.completionLRAT

/-- The live clauses after the steps, if every step is accepted. -/
def certRun (steps : List CertStep) : Option (List (ℕ × Clause)) := steps.foldlM P.certStep P.inputs

/-- **The certificate checker**: every step is accepted and the empty clause is live. -/
def checkCert (steps : List CertStep) : Bool :=
  match P.certRun steps with
  | some live => live.any fun e => e.2.isEmpty
  | none => false

/-! ## Soundness -/

theorem encode_index (v : Valuation A) {x : Var A} (h : P.IsVar x) : P.encode v (P.index x) = v x := by
  rw [encode, P.getElem?_index h]
  rfl

theorem sat_nativeLit (v : Valuation A) {l : Lit A} (h : P.IsVar l.var) :
    Literal.sat (P.encode v) (P.nativeLit l) = decide (l.Sat v) := by
  rw [nativeLit, CNF.Literal.sat_toLRAT]
  simp only [CNF.Literal.eval, P.encode_index v h, Lit.Sat]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  exact decide_eq_true_iff.symm

/-- **The emitted clause of a nogood holds exactly when the nogood is not violated.** -/
theorem sat_lratClause (v : Valuation A) {lits : List (Lit A)} (vars : ∀ l ∈ lits, P.IsVar l.var) :
    Clause.sat (P.encode v) (P.lratClause lits) = true ↔ ∃ l ∈ lits, ¬ l.Sat v := by
  simp only [Clause.sat, lratClause, List.any_map, List.any_eq_true, List.mem_dedup, Function.comp]
  constructor
  · rintro ⟨l, hl, sat⟩
    rw [P.sat_nativeLit v (l := l.compl) (vars l hl), decide_eq_true_eq, Lit.sat_compl] at sat
    exact ⟨l, hl, sat⟩
  · rintro ⟨l, hl, notSat⟩
    refine ⟨l, hl, ?_⟩
    rw [P.sat_nativeLit v (l := l.compl) (vars l hl), decide_eq_true_eq, Lit.sat_compl]
    exact notSat

/-- The clause of an entailed nogood over program variables holds in every stable model. -/
theorem sat_lratClause_of_entailed {lits : List (Lit A)} (entailed : P.Entailed lits)
    (vars : ∀ l ∈ lits, P.IsVar l.var) {M : Set A} (stable : P.Stable M) :
    Clause.sat (P.encode (canonical M)) (P.lratClause lits) = true := by
  obtain ⟨admissible, correct, stable'⟩ := P.stable_canonical stable
  exact (P.sat_lratClause _ vars).mpr (entailed _ admissible correct stable')

theorem atomOf_isVar {i : ℕ} {a : A} (h : P.atomOf i = some a) : P.IsVar (.atom a) := by
  unfold atomOf at h
  split at h
  · rename_i b hb
    cases h
    exact (P.mem_varList).mp (List.mem_of_getElem? hb)
  · cases h

theorem atomOf_index {a : A} (h : P.IsVar (.atom a)) : P.atomOf (P.index (.atom a)) = some a := by
  simp [atomOf, P.getElem?_index h]

/-- **A loop clause holds in every stable model.** -/
theorem loopClause_sat {atoms : List ℕ} {atom : ℕ} {c : Clause} (h : P.loopClause atoms atom = some c)
    {M : Set A} (stable : P.Stable M) : Clause.sat (P.encode (canonical M)) c = true := by
  unfold loopClause at h
  split at h
  · rename_i guard
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at guard
    obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
    have member : a ∈ (atoms.filterMap P.atomOf).toFinset :=
      List.mem_toFinset.mpr (List.mem_filterMap.mpr ⟨atom, guard.2, ha⟩)
    have noFalsum : ∀ b ∈ (atoms.filterMap P.atomOf).toFinset, ¬ P.Falsum b := by
      intro b hb
      obtain ⟨i, hi, hib⟩ := List.mem_filterMap.mp (List.mem_toFinset.mp hb)
      have := guard.1 i hi
      rw [hib] at this
      exact (P.falsum_eq_false_iff).mp (by simpa using this)
    apply P.sat_lratClause_of_entailed (P.loopNogood_entailed _ member) _ stable
    intro l hl
    rcases P.loopNogood_vars noFalsum hl with rfl | isVar
    · exact P.atomOf_isVar ha
    · exact isVar
  · cases h

theorem loopStepOk_sat {clause : Clause} {atoms : List ℕ} {atom : ℕ} (h : P.loopStepOk clause atoms atom = true)
    {M : Set A} (stable : P.Stable M) : Clause.sat (P.encode (canonical M)) clause = true := by
  unfold loopStepOk at h
  split at h
  · rename_i c hc
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    obtain ⟨l, hl, sat⟩ := List.any_eq_true.mp (P.loopClause_sat hc stable)
    exact List.any_eq_true.mpr ⟨l, h.1 l hl, sat⟩
  · cases h

theorem encode_of_atomOf (v : Valuation A) {i : ℕ} {a : A} (h : P.atomOf i = some a) :
    P.encode v i = v (.atom a) := by
  unfold atomOf at h
  split at h
  · rename_i b hb
    cases h
    rw [encode, hb]
    rfl
  · cases h

omit [DecidableEq A] in
theorem mem_of_mapM_getElem? : ∀ {groups : List ℕ} {rules : List (Rule A)},
    groups.mapM (P[·]?) = some rules → ∀ r ∈ rules, r ∈ P
  | [], rules, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    simp
  | g :: groups, rules, h => by
    cases hg : P[g]? with
    | none => simp [List.mapM_cons, hg] at h
    | some r =>
      cases hrest : groups.mapM (P[·]?) with
      | none => simp [List.mapM_cons, hg, hrest] at h
      | some rest =>
        simp only [List.mapM_cons, hg, hrest, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at h
        subst h
        rintro q (_ | ⟨_, hq⟩)
        · exact List.mem_of_getElem? hg
        · exact mem_of_mapM_getElem? hrest q hq

/-- **A Hall clause holds in every stable model**, by `hall_step_sound` with the groups indexed by
their positions and the cliques by theirs. -/
theorem hallStepOk_sat {clause : Clause} {groups : List ℕ} {cliques : List (List ℕ)}
    (h : P.hallStepOk clause groups cliques = true) {M : Set A} (stable : P.Stable M) :
    Clause.sat (P.encode (canonical M)) clause = true := by
  unfold hallStepOk at h
  split at h
  · cases h
  rename_i rules hrules
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true, beq_iff_eq,
    List.any_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, hclique⟩, hgroups⟩, hdisj⟩, hcover⟩, hcard⟩ := h
  obtain ⟨a, ha, haM⟩ := P.hall_step_sound stable (Finset.univ : Finset (Fin rules.length))
    (fun i => rules[i]) (Finset.univ : Finset (Fin cliques.length))
    (fun k => {a | a ∈ cliques[k].filterMap P.atomOf}) {a | a ∈ clause.filterMap P.posAtom}
    (fun i _ => P.atLeastOne_of_isAtLeastOne (P.mem_of_mapM_getElem? hrules _ (List.getElem_mem _))
      (hgroups _ (List.getElem_mem _)))
    (by
      intro i _ j _ hij a hai haih ⟨haj, hajh⟩
      have pairwise := List.pairwise_iff_getElem.mp hdisj
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with lt | gt
      · exact pairwise i j i.2 j.2 lt a (Rule.mem_group.mpr ⟨hai, haih⟩) (Rule.mem_group.mpr ⟨haj, hajh⟩)
      · exact pairwise j i j.2 i.2 gt a (Rule.mem_group.mpr ⟨haj, hajh⟩) (Rule.mem_group.mpr ⟨hai, haih⟩))
    (by
      intro k _ a ha b hb hab
      have := hclique _ (List.getElem_mem k.2) a ha b hb
      exact P.exclusion_of_excludes (this.resolve_left hab))
    (by
      intro i _ a ha hah
      rcases hcover _ (List.getElem_mem _) a (Rule.mem_group.mpr ⟨ha, hah⟩) with hE | ⟨cl, hcl, hacl⟩
      · exact Or.inl hE
      · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hcl
        exact Or.inr ⟨⟨k, hk⟩, Finset.mem_univ _, hacl⟩)
    (by simpa using hcard)
  obtain ⟨l, hl, hpos⟩ := List.mem_filterMap.mp ha
  refine List.any_eq_true.mpr ⟨l, hl, ?_⟩
  cases l with
  | pos i =>
    simpa [Literal.sat, P.encode_of_atomOf _ hpos, canonical] using haM
  | neg i => cases hpos

/-- **Every step keeps the live clauses true in every stable model.** -/
theorem certStep_holds {M : Set A} (stable : P.Stable M) {live live' : List (ℕ × Clause)} {st : CertStep}
    (holds : LiveHolds (P.encode (canonical M)) live) (h : P.certStep live st = some live') :
    LiveHolds (P.encode (canonical M)) live' := by
  cases st with
  | lrat action =>
    cases action with
    | rup id clause hints =>
      simp only [certStep] at h
      split at h
      · cases h
      · split at h
        · rename_i premises hpremises
          split at h
          · rename_i accepted
            cases h
            rintro e (_ | ⟨_, he⟩)
            · apply PropositionalLRATActions.rupCheck_sound accepted
              intro c hc
              obtain ⟨e', he', rfl⟩ := mapM_lookupClause_mem hpremises c hc
              exact holds e' he'
            · exact holds e he
          · cases h
        · cases h
    | rat _ _ => simp [certStep] at h
    | delete ids =>
      simp only [certStep, Option.some.injEq] at h
      subst h
      exact fun e he => holds e (List.mem_filter.mp he).1
  | loop id clause atoms atom =>
    simp only [certStep] at h
    split at h
    · cases h
    · split at h
      · rename_i ok
        cases h
        rintro e (_ | ⟨_, he⟩)
        · exact P.loopStepOk_sat ok stable
        · exact holds e he
      · cases h
  | hall id clause groups cliques =>
    simp only [certStep] at h
    split at h
    · cases h
    · split at h
      · rename_i ok
        cases h
        rintro e (_ | ⟨_, he⟩)
        · exact P.hallStepOk_sat ok stable
        · exact holds e he
      · cases h

theorem inputs_holds {M : Set A} (stable : P.Stable M) : LiveHolds (P.encode (canonical M)) P.inputs := by
  intro e he
  obtain ⟨δ, hδ, same⟩ := List.mem_map.mp (numberFrom_mem he)
  rw [← same]
  exact P.sat_lratClause_of_entailed (P.completionNogood_entailed hδ) (P.completionNogoods_vars hδ) stable

theorem foldlM_certStep_holds {M : Set A} (stable : P.Stable M) :
    ∀ (steps : List CertStep) {live live' : List (ℕ × Clause)}, LiveHolds (P.encode (canonical M)) live →
      steps.foldlM P.certStep live = some live' → LiveHolds (P.encode (canonical M)) live'
  | [], _, _, holds, h => by
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    exact h ▸ holds
  | st :: steps, live, live', holds, h => by
    simp only [List.foldlM_cons] at h
    cases hst : P.certStep live st with
    | none => simp [hst] at h
    | some next =>
      simp only [hst, Option.bind_eq_bind, Option.bind_some] at h
      exact foldlM_certStep_holds stable steps (P.certStep_holds stable holds hst) h

/-- **Every live clause holds in every stable model.** -/
theorem certRun_holds {steps : List CertStep} {live : List (ℕ × Clause)} (h : P.certRun steps = some live)
    {M : Set A} (stable : P.Stable M) : LiveHolds (P.encode (canonical M)) live :=
  P.foldlM_certStep_holds stable steps (P.inputs_holds stable) h

/-- **An accepted certificate means the program has no stable model.** -/
theorem checkCert_sound {steps : List CertStep} (accepted : P.checkCert steps = true) (M : Set A) :
    ¬ P.Stable M := by
  intro stable
  unfold checkCert at accepted
  split at accepted
  · rename_i live hlive
    obtain ⟨e, he, empty⟩ := List.any_eq_true.mp accepted
    have := P.certRun_holds hlive stable e he
    rw [List.isEmpty_iff.mp empty] at this
    cases this
  · cases accepted

end Program

end Checker

end Mettapedia.Logic.ASP
