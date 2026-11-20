import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflCorrespondenceStep

/-!
# The REFL correspondence at the name frame: a REFL step whose premise is one COMM, forward

`refl_forward_comm`: a root row that reads as the reflection `x?(p) @ Root`, with a clean child location
`l = Child(Root, x, p)`, where the reflected process `p` splits into leaves
`pre ++ [predot (for(t <- x')A)] ++ mid ++ [predot (for(u <- x')B)] ++ post` and the two inputs meet under the
step-1′ hypotheses at some solution of the knowledge, is matched by a run of the located program at the name
frame:

`openRoot ; heatChild* ; commChild ; cool* ; closeRoot`.

At the end the reflection is consumed, a new root row reads, at every solution, as the listener
`for(@(pPar (pre ++ mid ++ post ++ [predot (applyDot bs A), predot (applyDot bs B)])) <- x) 0 @ Root`, every other
row of the start keeps its presence and its label, and the knowledge is solvable.

Ingredients: `openRoot_admitted`, `heating_live`, `child_commit`, `refl_commit_closes`; the solution that unifies the
patterns is carried through the opening and the heating (`openRoot_extends`, `heating_live`'s extension clause,
`splits_agree`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflCorrespondence

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.OSLF.MeTTaIL.Match (Bindings)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus (pFor par pZero pPar nQuote tProc pReflect applyDot)
open MeTTaOperationsComm (psubst PSubst pvars psubst_of_pvars_nil psubst_pFor psubst_none GroundPrincipal firstOrder)
open MeTTaCalculus.Corrected (Apart psubstList_eq_map)
open FiniteProgram (predot predot_pFor channelUnknown)
open Comm (Tm X E renameBy ruleVars)
open OneFrame (embed)
open ReflQuotient (BagLaws bagCanon groundBags)
open ReflNames (NameLaws nameAction QN QNE nameFiring fresh_name nameLaws_pFor_iff nameLaws_tProc nameLaws_heads
  nameLaws_psubst nameLaws_pair_iff)
open ReflLocated (atLoc rootLoc childLoc pendingTok doneTok located commChild commChild_mem reflP locatedFrame_name
  psubst_rootLoc psubst_atLoc_any psubst_par)
open ReflPacking (cooled psubst_doneTok bagLaws_cooled_zero)
open ReflLocatedStep (psubst_pReflect nameLaws_pReflect_iff info_known solution_of_admitted result_present
  result_label_old res resConf commChildAt)

variable {O : Type*}

/-! ## Fresh identities -/

theorem exists_fresh_list [DecidableEq O] [Infinite O] (S : Finset O) :
    ∀ n : ℕ, ∃ L : List O, L.length = n ∧ L.Nodup ∧ ∀ o ∈ L, o ∉ S := by
  intro n
  induction n with
  | zero => exact ⟨[], rfl, List.nodup_nil, fun _ member => absurd member List.not_mem_nil⟩
  | succ n ih =>
      obtain ⟨L, length, nodup, fresh⟩ := ih
      obtain ⟨a, outside⟩ := Infinite.exists_notMem_finset (S ∪ L.toFinset)
      refine ⟨a :: L, by simp [length], List.nodup_cons.mpr ⟨fun inside => outside
        (Finset.mem_union.mpr (.inr (List.mem_toFinset.mpr inside))), nodup⟩, fun o member => ?_⟩
      rcases List.mem_cons.mp member with same | inL
      · rw [same]
        exact fun inS => outside (Finset.mem_union.mpr (.inl inS))
      · exact fresh o inL

/-! ## The results of the opening, the step and the close -/

theorem open_present [DecidableEq O] (label : O → Pattern) (C : Configuration Pattern O) (ρ : PSubst)
    (reflection m₁ mt o : O) :
    o ∈ (res label C (openRootAt ρ reflection m₁ mt)).present ↔ o ∈ C.present ∨ o = m₁ ∨ o = mt := by
  rw [result_present]
  simp [openRootAt]

theorem open_label_old [DecidableEq O] (label : O → Pattern) (C : Configuration Pattern O) (ρ : PSubst)
    (reflection m₁ mt : O) {o : O} (other₁ : o ≠ m₁) (other₂ : o ≠ mt) :
    (res label C (openRootAt ρ reflection m₁ mt)).label o = label o :=
  result_label_old _ (by simp [openRootAt, other₁, other₂])

theorem open_back [DecidableEq O] (label : O → Pattern) (C : Configuration Pattern O) (ρ : PSubst)
    (reflection m₁ mt : O) {σ : PSubst}
    (solved : nameAction.Models σ (resConf label C (openRootAt ρ reflection m₁ mt)).equations) :
    nameAction.Models σ C.equations :=
  info_known (label := label) (C := C) (openRootAt ρ reflection m₁ mt) solved

/-- The located COMM at the syntactic frame. -/
def commChildAtX [DecidableEq O] (ρ : PSubst) (first second token made₁ made₂ madeTok : O) :
    Firing O E located PUnit.unit :=
  ⟨commChild, commChild_mem, PUnit.unit, ρ, ⟨[first, second, token], [], [made₁, made₂, madeTok]⟩, []⟩

theorem commChildAt_eq [DecidableEq O] (ρ : PSubst) (first second token made₁ made₂ madeTok : O) :
    commChildAt ρ first second token made₁ made₂ madeTok =
      nameFiring (commChildAtX ρ first second token made₁ made₂ madeTok) := rfl

theorem commit_fresh_exists [DecidableEq O] (label : O → Pattern) (C : Configuration Pattern O)
    (first second token made₁ made₂ madeTok : O) :
    ∃ ρ : PSubst, (commChildAt ρ first second token made₁ made₂ madeTok).Fresh QN (embed label C) := by
  obtain ⟨g, injective, avoids⟩ := Comm.exists_apart_renaming (embed label C) (ruleVars commChild)
  refine ⟨renameBy g, ?_⟩
  rw [commChildAt_eq]
  exact fresh_name (Comm.fresh_of_renaming (embed label C)
    (commChildAtX (renameBy g) first second token made₁ made₂ madeTok) g rfl injective avoids)

theorem commit_present [DecidableEq O] (label : O → Pattern) (C : Configuration Pattern O) (ρ : PSubst)
    (first second token made₁ made₂ madeTok o : O) :
    o ∈ (res label C (commChildAt ρ first second token made₁ made₂ madeTok)).present ↔
      (o ∈ C.present ∧ o ≠ first ∧ o ≠ second ∧ o ≠ token) ∨ o = made₁ ∨ o = made₂ ∨ o = madeTok := by
  rw [result_present]
  simp [commChildAt]

theorem commit_label_old [DecidableEq O] (label : O → Pattern) (C : Configuration Pattern O) (ρ : PSubst)
    (first second token made₁ made₂ madeTok : O) {o : O} (other₁ : o ≠ made₁) (other₂ : o ≠ made₂)
    (other₃ : o ≠ madeTok) :
    (res label C (commChildAt ρ first second token made₁ made₂ madeTok)).label o = label o :=
  result_label_old _ (by simp [commChildAt, other₁, other₂, other₃])

theorem commit_back [DecidableEq O] (label : O → Pattern) (C : Configuration Pattern O) (ρ : PSubst)
    (first second token made₁ made₂ madeTok : O) {σ : PSubst}
    (solved : nameAction.Models σ (resConf label C (commChildAt ρ first second token made₁ made₂ madeTok)).equations) :
    nameAction.Models σ C.equations :=
  info_known (label := label) (C := C) (commChildAt ρ first second token made₁ made₂ madeTok) solved

theorem close_present [DecidableEq O] (label : O → Pattern) (C : Configuration Pattern O) (ρ : PSubst)
    (reflection token made₁ o : O) :
    o ∈ (res label C (closeRootAt ρ reflection token made₁)).present ↔
      (o ∈ C.present ∧ o ≠ reflection ∧ o ≠ token) ∨ o = made₁ := by
  rw [result_present]
  simp [closeRootAt]

/-! ## Solutions extend through the opening -/

/-- **Solutions extend through the opening**: for every solution `τ` of the knowledge there is a solution of the
opening's information that reads every present row as `τ` does. -/
theorem openRoot_extends [DecidableEq O] (label : O → Pattern) (C : Configuration Pattern O) (x p : Pattern)
    (reflection made₁ madeTok : O)
    (readsReflection : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label reflection)) (psubst σ (atLoc (pReflect x p) rootLoc)))
    (present : reflection ∈ C.present)
    {ρ : PSubst} (opensFreshly : (openRootAt ρ reflection made₁ madeTok).Fresh QN (embed label C))
    {τ : PSubst} (known : nameAction.Models τ C.equations) :
    ∃ w : PSubst, nameAction.Models w (resConf label C (openRootAt ρ reflection made₁ madeTok)).equations ∧
      ∀ o ∈ C.present, NameLaws (psubst w (label o)) (psubst τ (label o)) := by
  let h : PSubst := openInstance (psubst τ x) (psubst τ p)
  have hReflection : psubst h (atLoc (pReflect channelUnknown reflP) rootLoc) =
      psubst τ (atLoc (pReflect x p) rootLoc) := by
    simp [h, openInstance, atLoc, pReflect, channelUnknown, reflP, rootLoc, psubst, psubstList_eq_map]
  obtain ⟨w, solved, onState, -⟩ := Comm.information_amalgamates_matched (Y := QN) (s := embed label C)
    (openRootAt ρ reflection made₁ madeTok) opensFreshly (b := PUnit.unit) τ h known
    (fun _ member => (List.not_mem_nil member).elim)
    (fun _ member => (List.not_mem_nil member).elim)
    (fun o member => by
      obtain rfl := List.mem_singleton.mp member
      exact present)
    (fun _ member => (List.not_mem_nil member).elim)
    (fun q member => by
      obtain rfl := List.mem_singleton.mp member
      show NameLaws (psubst h (atLoc (pReflect channelUnknown reflP) rootLoc)) (psubst τ (label reflection))
      rw [hReflection]
      exact (readsReflection τ known).symm)
  refine ⟨w, solved, fun o present' => ?_⟩
  have agree : NameLaws (psubst w (psubst (fun _ => none) (label o))) (psubst τ (label o)) :=
    onState (label o) (Or.inr (Or.inr ⟨o, present', rfl⟩))
  rw [psubst_none] at agree
  exact agree

open ReflLocatedStep.Ownership (Store Candidate ScopeLinks)

/-- A root owner can open a fresh child even if another owner's child
has the same symbolic description. The unchanged matching equations
are solved by extending an actual solution of the reached state. -/
theorem openRoot_physical_admitted [DecidableEq O] (label : O → Pattern) (C : Configuration Pattern O)
    (ledger : LocatedSubstitution.Authority.Ledger O ReflLocatedStep.Ownership.Phase)
    (x p : Pattern) (reflection made₁ madeTok : O) (ρ : PSubst)
    (linked : ScopeLinks ((Store.plain (embed label C) ledger) : Store O))
    (covered : ledger.Covers C.present)
    (available : ((Store.plain (embed label C) ledger) : Store O).available none reflection)
    (apart : made₁ ≠ madeTok)
    (new : Disjoint ([made₁, madeTok] : List O).toFinset ledger.issued)
    (reads : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label reflection)) (psubst σ (atLoc (pReflect x p) rootLoc)))
    (known : ∃ σ : PSubst, nameAction.Models σ C.equations)
    (fresh : (openRootAt ρ reflection made₁ madeTok).Fresh QN (embed label C)) :
    (ReflLocatedStep.Ownership.step (O := O) .physical).Admits
      (s := (Store.plain (embed label C) ledger)) ⟨openRootAt ρ reflection made₁ madeTok, .openRoot, rfl⟩ := by
  let s : Store O := (Store.plain (embed label C) ledger)
  let f : Candidate s := ⟨openRootAt ρ reflection made₁ madeTok, .openRoot, rfl⟩
  have ownerMark : ledger.mark reflection = some (.cell none) := available.1
  have ownerLive : reflection ∈ C.present :=
    (covered.2 reflection).mpr (by rw [ownerMark]; rfl)
  have unused : made₁ ∉ C.present ∧ madeTok ∉ C.present :=
    ⟨fun member => Finset.disjoint_left.mp new (by simp) (covered.1 member),
     fun member => Finset.disjoint_left.mp new (by simp) (covered.1 member)⟩
  obtain ⟨σ, solved⟩ := known
  obtain ⟨w, solvedAfter, _⟩ := openRoot_extends label C x p reflection made₁ madeTok reads ownerLive fresh solved
  have plan : f.plan.isSome := by
    change (ReflLocatedStep.Ownership.routes s .openRoot [] [reflection] [made₁, madeTok]).isSome
    rw [ReflLocatedStep.Ownership.open_root_plan s reflection made₁ madeTok available.1 available.2]
    rfl
  exact (ReflLocatedStep.Ownership.physical_admits_iff linked f).mpr
    ⟨openRoot_shapes label C ρ reflection made₁ madeTok apart fresh,
     openRoot_enabled C ρ reflection made₁ madeTok ownerLive unused, ⟨PUnit.unit, w, solvedAfter⟩, plan, new⟩

/-- Two solutions that agree on a split process agree on its leaves. -/
theorem splits_agree {p : Pattern} {L : List Pattern} (split : Splits p L) {w τ : PSubst} :
    NameLaws (psubst w p) (psubst τ p) → ∀ i ∈ L, NameLaws (psubst w i) (psubst τ i) := by
  induction split with
  | leaf p =>
      intro agree i member
      rw [List.mem_singleton] at member
      rw [member]
      exact agree
  | split _ _ ihA ihB =>
      intro agree i member
      rw [psubst_par, psubst_par] at agree
      obtain ⟨left, right⟩ := nameLaws_pair_iff.mp agree
      rcases List.mem_append.mp member with inL | inM
      · exact ihA left i inL
      · exact ihB right i inM

/-! ## The forward simulation of a REFL step with a COMM premise -/

/-- **A REFL step whose premise is one COMM, forward, at the name frame.** -/
theorem refl_forward_comm [DecidableEq O] [Infinite O] (label : O → Pattern) (C : Configuration Pattern O)
    (x p : Pattern) (reflection : O)
    (readsReflection : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label reflection)) (psubst σ (atLoc (pReflect x p) rootLoc)))
    (clean : Clean (childLoc rootLoc x p) label C) (present : reflection ∈ C.present)
    {L : List Pattern} (split : Splits p L) (pre mid post : List Pattern) (t u channel A B : Pattern)
    (leaves : L = pre ++ predot (pFor t channel A) :: (mid ++ predot (pFor u channel B) :: post))
    (bs : Bindings) (gp : GroundPrincipal t u bs) (convention : Apart t A u B)
    (foA : firstOrder A = true) (foB : firstOrder B = true)
    (groundT : groundBags t = true) (groundU : groundBags u = true)
    (canonicalT : bagCanon t = t) (canonicalU : bagCanon u = u)
    {σ₀ : PSubst} (known : nameAction.Models σ₀ C.equations) (unifies : NameLaws (psubst σ₀ t) (psubst σ₀ u)) :
    ∃ (label' : O → Pattern) (C' : Configuration Pattern O) (made : O),
      LocatedRun label C label' C' ∧ made ∈ C'.present ∧ reflection ∉ C'.present ∧
      (∀ σ : PSubst, nameAction.Models σ C'.equations →
        NameLaws (psubst σ (label' made)) (psubst σ (atLoc (pFor (tProc (pPar (pre ++ mid ++ post ++
          [predot (applyDot bs A), predot (applyDot bs B)]))) x pZero) rootLoc))) ∧
      (∀ o ∈ C.present, o ≠ reflection → o ∈ C'.present ∧ label' o = label o) ∧
      (∃ σ₁ : PSubst, nameAction.Models σ₁ C'.equations) := by
  -- 1. The opening.
  obtain ⟨pr, freshPr⟩ := Infinite.exists_notMem_finset C.present
  obtain ⟨tk, freshTk'⟩ := Infinite.exists_notMem_finset (insert pr C.present)
  have prTk : pr ≠ tk := fun same => freshTk' (Finset.mem_insert.mpr (.inl same.symm))
  have freshTk : tk ∉ C.present := fun inside => freshTk' (Finset.mem_insert.mpr (.inr inside))
  obtain ⟨ρ₁, fresh₁⟩ := open_fresh_exists label C reflection pr tk
  have opened := openRoot_admitted label C x p reflection pr tk readsReflection clean present prTk
    ⟨freshPr, freshTk⟩ known fresh₁
  obtain ⟨σ₁, solved₁⟩ := solution_of_admitted opened
  have prIn : pr ∈ (resConf label C (openRootAt ρ₁ reflection pr tk)).present :=
    (open_present label C ρ₁ reflection pr tk pr).mpr (.inr (.inl rfl))
  have tkIn : tk ∈ (resConf label C (openRootAt ρ₁ reflection pr tk)).present :=
    (open_present label C ρ₁ reflection pr tk tk).mpr (.inr (.inr rfl))
  have reflectionPr : reflection ≠ pr := fun same => freshPr (same ▸ present)
  have reflectionTk : reflection ≠ tk := fun same => freshTk (same ▸ present)
  have oldIn₁ : ∀ o ∈ C.present, o ∈ (resConf label C (openRootAt ρ₁ reflection pr tk)).present :=
    fun o inside => (open_present label C ρ₁ reflection pr tk o).mpr (.inl inside)
  have oldPr : ∀ o ∈ C.present, o ≠ pr := fun o inside same => freshPr (same ▸ inside)
  have oldTk : ∀ o ∈ C.present, o ≠ tk := fun o inside same => freshTk (same ▸ inside)
  -- 2. Heating the child into the leaves.
  obtain ⟨label₂, C₂, rows, run₂, lengthRows, nodupRows, readsRows, factsRows, frame₂, cover₂, mono₂, ext₂,
      solvable₂⟩ :=
    heating_live (childLoc rootLoc x p) rootLoc split (res label C (openRootAt ρ₁ reflection pr tk)).label
      (resConf label C (openRootAt ρ₁ reflection pr tk)) pr tk prIn tkIn prTk
      (fun σ solved => (openRoot_reads label C x p reflection pr tk ρ₁ readsReflection prTk solved).2.1)
      (fun σ solved => (openRoot_reads label C x p reflection pr tk ρ₁ readsReflection prTk solved).2.2)
      ⟨σ₁, solved₁⟩
  have back₂ : ∀ σ : PSubst, nameAction.Models σ C₂.equations → nameAction.Models σ C.equations :=
    fun σ solved => open_back label C ρ₁ reflection pr tk (mono₂ σ solved)
  have rowOrigin : ∀ r ∈ rows, ∀ o ∈ C.present, r ≠ o := by
    intro r inRows o inC same
    rcases (factsRows r inRows).2.2 with isPr | notC₁
    · exact oldPr o inC (same ▸ isPr)
    · exact notC₁ (same ▸ oldIn₁ o inC)
  -- 3. A solution of the heated knowledge that unifies the patterns.
  obtain ⟨w₁, solvedW₁, agree₁⟩ := openRoot_extends label C x p reflection pr tk readsReflection present fresh₁ known
  obtain ⟨w₂, solvedW₂, agree₂⟩ := ext₂ w₁ solvedW₁
  have labelReflection₁ := open_label_old label C ρ₁ reflection pr tk reflectionPr reflectionTk
  have sameReflection : NameLaws (psubst w₂ (label reflection)) (psubst σ₀ (label reflection)) := by
    have a₂ := agree₂ reflection (oldIn₁ reflection present) reflectionPr
    rw [labelReflection₁] at a₂
    exact a₂.trans (agree₁ reflection present)
  have processes : NameLaws (psubst w₂ p) (psubst σ₀ p) := by
    have both := ((readsReflection w₂ (back₂ w₂ solvedW₂)).symm.trans sameReflection).trans
      (readsReflection σ₀ known)
    simp only [psubst_atLoc_any, psubst_pReflect, psubst_rootLoc] at both
    obtain ⟨parts, -⟩ := (locatedFrame_name.atLoc_iff _ _ _ _).mp both
    exact (nameLaws_pReflect_iff.mp parts).2
  have leafAgree := splits_agree split processes
  have inputT : NameLaws (psubst w₂ t) (psubst σ₀ t) := by
    have leaf := leafAgree (predot (pFor t channel A)) (by rw [leaves]; simp)
    rw [predot_pFor, psubst_pFor, psubst_pFor] at leaf
    exact (nameLaws_pFor_iff.mp leaf).1
  have inputU : NameLaws (psubst w₂ u) (psubst σ₀ u) := by
    have leaf := leafAgree (predot (pFor u channel B)) (by rw [leaves]; simp)
    rw [predot_pFor, psubst_pFor, psubst_pFor] at leaf
    exact (nameLaws_pFor_iff.mp leaf).1
  have glued : NameLaws (psubst w₂ t) (psubst w₂ u) := inputT.trans (unifies.trans inputU.symm)
  -- 4. The rows of the two inputs.
  have cellsSnd : (rows.zip L).map Prod.snd =
      pre ++ predot (pFor t channel A) :: (mid ++ predot (pFor u channel B) :: post) := by
    rw [List.map_snd_zip (l₁ := rows) (l₂ := L) (by omega), leaves]
  obtain ⟨cPre, _cRest, cellsEq, preMap, restMap⟩ := List.map_eq_append_iff.mp cellsSnd
  obtain ⟨c₁, _cRest', restEq, c₁Snd, restMap'⟩ := List.map_eq_cons_iff.mp restMap
  obtain ⟨cMid, _cRest'', rest'Eq, midMap, rest''Map⟩ := List.map_eq_append_iff.mp restMap'
  obtain ⟨c₂, cPost, rest''Eq, c₂Snd, postMap⟩ := List.map_eq_cons_iff.mp rest''Map
  have cellsShape : rows.zip L = cPre ++ c₁ :: (cMid ++ c₂ :: cPost) := by
    rw [cellsEq, restEq, rest'Eq, rest''Eq]
  have cellsFst : (rows.zip L).map Prod.fst = rows := List.map_fst_zip (l₁ := rows) (l₂ := L) (by omega)
  have fstIn : ∀ q ∈ rows.zip L, q.1 ∈ rows := fun q member => cellsFst ▸ List.mem_map.mpr ⟨q, member, rfl⟩
  have c₁In : c₁ ∈ rows.zip L := by rw [cellsShape]; simp
  have c₂In : c₂ ∈ rows.zip L := by rw [cellsShape]; simp
  have restIn : ∀ q ∈ cPre ++ cMid ++ cPost, q ∈ rows.zip L := by
    intro q member
    rw [cellsShape]
    simp only [List.mem_append, List.mem_cons] at member ⊢
    rcases member with (inPre | inMid) | inPost
    · exact .inl inPre
    · exact .inr (.inr (.inl inMid))
    · exact .inr (.inr (.inr (.inr inPost)))
  have rowsShape : rows = cPre.map Prod.fst ++ c₁.1 :: (cMid.map Prod.fst ++ c₂.1 :: cPost.map Prod.fst) := by
    rw [← cellsFst, cellsShape]
    simp
  have permShape : (cPre.map Prod.fst ++ c₁.1 :: (cMid.map Prod.fst ++ c₂.1 :: cPost.map Prod.fst)).Perm
      (c₁.1 :: c₂.1 :: (cPre.map Prod.fst ++ cMid.map Prod.fst ++ cPost.map Prod.fst)) := by
    refine List.perm_middle.trans (List.Perm.cons _ ?_)
    rw [← List.append_assoc]
    exact List.perm_middle
  have nodupFront := permShape.nodup_iff.mp (rowsShape ▸ nodupRows)
  obtain ⟨c₁Out, nodupFront'⟩ := List.nodup_cons.mp nodupFront
  obtain ⟨c₂Out, restNodup⟩ := List.nodup_cons.mp nodupFront'
  have restFst : (cPre ++ cMid ++ cPost).map Prod.fst = cPre.map Prod.fst ++ cMid.map Prod.fst ++ cPost.map Prod.fst := by
    simp
  have restApart : ∀ q ∈ cPre ++ cMid ++ cPost, q.1 ≠ c₁.1 ∧ q.1 ≠ c₂.1 := by
    intro q member
    have inside : q.1 ∈ cPre.map Prod.fst ++ cMid.map Prod.fst ++ cPost.map Prod.fst := by
      rw [← restFst]
      exact List.mem_map.mpr ⟨q, member, rfl⟩
    refine ⟨fun same => c₁Out (List.mem_cons.mpr (.inr (same ▸ inside))), fun same => c₂Out (same ▸ inside)⟩
  have c₁c₂ : c₁.1 ≠ c₂.1 := fun same => c₁Out (List.mem_cons.mpr (.inl same))
  -- 5. The child's one step.
  obtain ⟨made₁, freshM₁⟩ := Infinite.exists_notMem_finset C₂.present
  obtain ⟨made₂, freshM₂'⟩ := Infinite.exists_notMem_finset (insert made₁ C₂.present)
  obtain ⟨madeTok, freshMT'⟩ := Infinite.exists_notMem_finset (insert made₂ (insert made₁ C₂.present))
  have m₁m₂ : made₁ ≠ made₂ := fun same => freshM₂' (Finset.mem_insert.mpr (.inl same.symm))
  have freshM₂ : made₂ ∉ C₂.present := fun inside => freshM₂' (Finset.mem_insert.mpr (.inr inside))
  have m₂mT : made₂ ≠ madeTok := fun same => freshMT' (Finset.mem_insert.mpr (.inl same.symm))
  have m₁mT : made₁ ≠ madeTok :=
    fun same => freshMT' (Finset.mem_insert.mpr (.inr (Finset.mem_insert.mpr (.inl same.symm))))
  have freshMT : madeTok ∉ C₂.present :=
    fun inside => freshMT' (Finset.mem_insert.mpr (.inr (Finset.mem_insert.mpr (.inr inside))))
  have notMade : ∀ o ∈ C₂.present, o ≠ made₁ ∧ o ≠ made₂ ∧ o ≠ madeTok := fun o inside =>
    ⟨fun same => freshM₁ (same ▸ inside), fun same => freshM₂ (same ▸ inside), fun same => freshMT (same ▸ inside)⟩
  obtain ⟨tkIn₂, tkLabel₂⟩ := frame₂ tk tkIn (Ne.symm prTk)
  obtain ⟨reflectionIn₂, reflectionLabel₂⟩ := frame₂ reflection (oldIn₁ reflection present) reflectionPr
  have c₁Facts := factsRows c₁.1 (fstIn c₁ c₁In)
  have c₂Facts := factsRows c₂.1 (fstIn c₂ c₂In)
  have readsC₁ : ∀ σ : PSubst, nameAction.Models σ C₂.equations →
      NameLaws (psubst σ (label₂ c₁.1)) (psubst σ (atLoc (predot (pFor t channel A)) (childLoc rootLoc x p))) := by
    intro σ solved
    rw [← c₁Snd]
    exact readsRows c₁ c₁In σ solved
  have readsC₂ : ∀ σ : PSubst, nameAction.Models σ C₂.equations →
      NameLaws (psubst σ (label₂ c₂.1)) (psubst σ (atLoc (predot (pFor u channel B)) (childLoc rootLoc x p))) := by
    intro σ solved
    rw [← c₂Snd]
    exact readsRows c₂ c₂In σ solved
  have readsTk₂ : ∀ σ : PSubst, nameAction.Models σ C₂.equations →
      NameLaws (psubst σ (label₂ tk)) (psubst σ (pendingTok (childLoc rootLoc x p) rootLoc)) := by
    intro σ solved
    rw [tkLabel₂]
    exact (openRoot_reads label C x p reflection pr tk ρ₁ readsReflection prTk (mono₂ σ solved)).2.2
  obtain ⟨ρ₃, fresh₃⟩ := commit_fresh_exists label₂ C₂ c₁.1 c₂.1 tk made₁ made₂ madeTok
  obtain ⟨committed, readsCommit⟩ := child_commit label₂ C₂ t u channel A B (childLoc rootLoc x p) rootLoc bs gp
    convention foA foB groundT groundU canonicalT canonicalU c₁.1 c₂.1 tk made₁ made₂ madeTok readsC₁ readsC₂
    readsTk₂ (by simp [c₁c₂, c₁Facts.2.1, c₂Facts.2.1]) (by simp [m₁m₂, m₁mT, m₂mT])
    ⟨c₁Facts.1, c₂Facts.1, tkIn₂⟩ ⟨freshM₁, freshM₂, freshMT⟩ solvedW₂ glued fresh₃
  obtain ⟨σ₃, solved₃⟩ := solution_of_admitted committed
  -- The state after the step.
  have back₃ : ∀ σ : PSubst,
      nameAction.Models σ (resConf label₂ C₂ (commChildAt ρ₃ c₁.1 c₂.1 tk made₁ made₂ madeTok)).equations →
      nameAction.Models σ C₂.equations :=
    fun σ solved => commit_back label₂ C₂ ρ₃ c₁.1 c₂.1 tk made₁ made₂ madeTok solved
  have keep₃ : ∀ o ∈ C₂.present, o ≠ c₁.1 → o ≠ c₂.1 → o ≠ tk →
      o ∈ (resConf label₂ C₂ (commChildAt ρ₃ c₁.1 c₂.1 tk made₁ made₂ madeTok)).present ∧
      (res label₂ C₂ (commChildAt ρ₃ c₁.1 c₂.1 tk made₁ made₂ madeTok)).label o = label₂ o := by
    intro o inside ne₁ ne₂ neT
    obtain ⟨n₁, n₂, n₃⟩ := notMade o inside
    exact ⟨(commit_present label₂ C₂ ρ₃ c₁.1 c₂.1 tk made₁ made₂ madeTok o).mpr (.inl ⟨inside, ne₁, ne₂, neT⟩),
      commit_label_old label₂ C₂ ρ₃ c₁.1 c₂.1 tk made₁ made₂ madeTok n₁ n₂ n₃⟩
  -- 6. Cooling every row of the child, then the close.
  let order : List (O × Pattern) :=
    cPre ++ cMid ++ cPost ++ [(made₁, predot (applyDot bs A)), (made₂, predot (applyDot bs B))]
  have orderSnd : order.map Prod.snd = pre ++ mid ++ post ++ [predot (applyDot bs A), predot (applyDot bs B)] := by
    simp [order, preMap, midMap, postMap]
  have orderFst : order.map Prod.fst =
      cPre.map Prod.fst ++ cMid.map Prod.fst ++ cPost.map Prod.fst ++ [made₁, made₂] := by
    simp [order]
  have orderCases : ∀ q ∈ order, q ∈ cPre ++ cMid ++ cPost ∨ q = (made₁, predot (applyDot bs A)) ∨
      q = (made₂, predot (applyDot bs B)) := by
    intro q member
    simp only [order, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with ((inPre | inMid) | inPost) | isMade₁ | isMade₂
    · exact .inl (List.mem_append.mpr (.inl (List.mem_append.mpr (.inl inPre))))
    · exact .inl (List.mem_append.mpr (.inl (List.mem_append.mpr (.inr inMid))))
    · exact .inl (List.mem_append.mpr (.inr inPost))
    · exact .inr (.inl isMade₁)
    · exact .inr (.inr isMade₂)
  have oldNotOrder : ∀ o ∈ C.present, o ∉ order.map Prod.fst := by
    intro o inC
    have notRow : o ∉ rows := fun inRows => rowOrigin o inRows o inC rfl
    have in₂ : o ∈ C₂.present := (frame₂ o (oldIn₁ o inC) (oldPr o inC)).1
    rw [orderFst]
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro (((inPre | inMid) | inPost) | isM₁ | isM₂)
    · obtain ⟨q, inQ, same⟩ := List.mem_map.mp inPre
      exact notRow (same ▸ fstIn q (restIn q (by simp [inQ])))
    · obtain ⟨q, inQ, same⟩ := List.mem_map.mp inMid
      exact notRow (same ▸ fstIn q (restIn q (by simp [inQ])))
    · obtain ⟨q, inQ, same⟩ := List.mem_map.mp inPost
      exact notRow (same ▸ fstIn q (restIn q (by simp [inQ])))
    · exact (notMade o in₂).1 isM₁
    · exact (notMade o in₂).2.1 isM₂
  have restPresent : ∀ q ∈ cPre ++ cMid ++ cPost,
      q.1 ∈ (resConf label₂ C₂ (commChildAt ρ₃ c₁.1 c₂.1 tk made₁ made₂ madeTok)).present ∧
      (res label₂ C₂ (commChildAt ρ₃ c₁.1 c₂.1 tk made₁ made₂ madeTok)).label q.1 = label₂ q.1 := by
    intro q member
    have facts := factsRows q.1 (fstIn q (restIn q member))
    exact keep₃ q.1 facts.1 (restApart q member).1 (restApart q member).2 facts.2.1
  obtain ⟨supplyAll, lengthAll, nodupAll, freshAll⟩ := exists_fresh_list
    (resConf label₂ C₂ (commChildAt ρ₃ c₁.1 c₂.1 tk made₁ made₂ madeTok)).present (order.length + 1)
  obtain ⟨listener, supply, rfl⟩ : ∃ a rest, supplyAll = a :: rest := by
    cases supplyAll with
    | nil => exact absurd lengthAll (by simp)
    | cons a rest => exact ⟨a, rest, rfl⟩
  have madeIn₃ : ∀ o, o = made₁ ∨ o = made₂ ∨ o = madeTok →
      o ∈ (resConf label₂ C₂ (commChildAt ρ₃ c₁.1 c₂.1 tk made₁ made₂ madeTok)).present :=
    fun o which => (commit_present label₂ C₂ ρ₃ c₁.1 c₂.1 tk made₁ made₂ madeTok o).mpr (.inr which)
  have reflectionRow : reflection ∉ rows := fun inRows => rowOrigin reflection inRows reflection present rfl
  have reflection₁ : reflection ≠ c₁.1 := fun same => reflectionRow (same ▸ fstIn c₁ c₁In)
  have reflection₂ : reflection ≠ c₂.1 := fun same => reflectionRow (same ▸ fstIn c₂ c₂In)
  obtain ⟨reflectionIn₃, reflectionLabel₃⟩ := keep₃ reflection reflectionIn₂ reflection₁ reflection₂ reflectionTk
  obtain ⟨label₄, C₄, d', ρ₅, coolRun, closed, readsClose, kept⟩ := refl_commit_closes
    (res label₂ C₂ (commChildAt ρ₃ c₁.1 c₂.1 tk made₁ made₂ madeTok)).label
    (resConf label₂ C₂ (commChildAt ρ₃ c₁.1 c₂.1 tk made₁ made₂ madeTok)) x p reflection madeTok listener order supply
    (fun σ solved => by
      rw [reflectionLabel₃, reflectionLabel₂, labelReflection₁]
      exact readsReflection σ (back₂ σ (back₃ σ solved)))
    (fun σ solved => (readsCommit σ solved).2.2.2)
    (fun q member σ solved => by
      rcases orderCases q member with inRest | isMade₁ | isMade₂
      · rw [(restPresent q inRest).2]
        exact readsRows q (restIn q inRest) σ (back₃ σ solved)
      · rw [isMade₁]
        exact (readsCommit σ solved).2.1
      · rw [isMade₂]
        exact (readsCommit σ solved).2.2.1)
    (fun o inside notOrder σ solved y same => by
      rcases (commit_present label₂ C₂ ρ₃ c₁.1 c₂.1 tk made₁ made₂ madeTok o).mp inside with
        ⟨in₂, ne₁, ne₂, neT⟩ | isMade₁ | isMade₂ | isMadeTok
      · rw [commit_label_old label₂ C₂ ρ₃ c₁.1 c₂.1 tk made₁ made₂ madeTok (notMade o in₂).1 (notMade o in₂).2.1
          (notMade o in₂).2.2] at same
        rcases cover₂ o in₂ with inRows | ⟨in₁, nePr, label₂Eq⟩
        · apply notOrder
          rw [← cellsFst] at inRows
          obtain ⟨q, inCells, rfl⟩ := List.mem_map.mp inRows
          rw [cellsShape] at inCells
          simp only [List.mem_append, List.mem_cons] at inCells
          rw [orderFst]
          simp only [List.mem_append, List.mem_cons, List.mem_map]
          rcases inCells with inPre | isC₁ | inMid | isC₂ | inPost
          · exact .inl (.inl (.inl ⟨q, inPre, rfl⟩))
          · exact absurd (congrArg Prod.fst isC₁) ne₁
          · exact .inl (.inl (.inr ⟨q, inMid, rfl⟩))
          · exact absurd (congrArg Prod.fst isC₂) ne₂
          · exact .inl (.inr ⟨q, inPost, rfl⟩)
        · rcases (open_present label C ρ₁ reflection pr tk o).mp in₁ with inC | isPr | isTk
          · rw [label₂Eq, open_label_old label C ρ₁ reflection pr tk (oldPr o inC) (oldTk o inC)] at same
            exact (clean o inC σ (back₂ σ (back₃ σ solved))).2.2 y same
          · exact nePr isPr
          · exact neT isTk
      · exact notOrder (by rw [orderFst, isMade₁]; simp)
      · exact notOrder (by rw [orderFst, isMade₂]; simp)
      · rw [isMadeTok] at same
        have both := ((readsCommit σ solved).2.2.2).symm.trans same
        rw [psubst_doneTok] at both
        exact absurd (nameLaws_heads both) (by decide))
    (by simpa using lengthAll) nodupAll freshAll (madeIn₃ madeTok (.inr (.inr rfl))) reflectionIn₃
    (fun same => freshMT (same ▸ reflectionIn₂))
    (oldNotOrder reflection present)
    (by
      rw [orderFst]
      refine List.nodup_append.mpr ⟨restNodup, by simp [m₁m₂], fun a inA b inB same => ?_⟩
      have inRows : a ∈ rows := by
        rw [rowsShape]
        simp only [List.mem_append, List.mem_cons] at inA ⊢
        rcases inA with (inPre | inMid) | inPost
        · exact .inl inPre
        · exact .inr (.inr (.inl inMid))
        · exact .inr (.inr (.inr (.inr inPost)))
      have aIn₂ := (factsRows a inRows).1
      simp only [List.mem_cons, List.not_mem_nil, or_false] at inB
      rcases inB with isM₁ | isM₂
      · exact freshM₁ (isM₁ ▸ same ▸ aIn₂)
      · exact freshM₂ (isM₂ ▸ same ▸ aIn₂))
    (fun q member => by
      rcases orderCases q member with inRest | isMade₁ | isMade₂
      · refine ⟨(restPresent q inRest).1, fun same => freshMT ?_⟩
        rw [← same]
        exact (factsRows q.1 (fstIn q (restIn q inRest))).1
      · rw [isMade₁]
        exact ⟨madeIn₃ made₁ (.inl rfl), m₁mT⟩
      · rw [isMade₂]
        exact ⟨madeIn₃ made₂ (.inr (.inl rfl)), m₂mT⟩)
    ⟨σ₃, solved₃⟩
  obtain ⟨σ₅, solved₅⟩ := solution_of_admitted closed
  refine ⟨(res label₄ C₄ (closeRootAt ρ₅ reflection d' listener)).label,
    resConf label₄ C₄ (closeRootAt ρ₅ reflection d' listener), listener,
    .step _ opened (run₂.trans (.step _ committed ((coolRun_located coolRun).trans (.step _ closed (.refl _ _))))),
    (close_present label₄ C₄ ρ₅ reflection d' listener listener).mpr (.inr rfl), ?_, ?_, ?_, ⟨σ₅, solved₅⟩⟩
  · intro inside
    rcases (close_present label₄ C₄ ρ₅ reflection d' listener reflection).mp inside with ⟨-, notSelf, -⟩ | same
    · exact notSelf rfl
    · exact freshAll reflection (List.mem_cons.mpr (.inl same)) reflectionIn₃
  · intro σ solved
    have quote : NameLaws (atLoc (pFor (tProc (cooled pZero (order.map Prod.snd))) x pZero) rootLoc)
        (atLoc (pFor (tProc (pPar (pre ++ mid ++ post ++ [predot (applyDot bs A), predot (applyDot bs B)]))) x pZero)
          rootLoc) := by
      rw [orderSnd]
      exact (locatedFrame_name.atLoc_iff _ _ _ _).mpr ⟨nameLaws_pFor_iff.mpr ⟨nameLaws_tProc (bagLaws_cooled_zero _),
        ReflNames.NameLaws.refl _, ReflNames.NameLaws.refl _⟩, ReflNames.NameLaws.refl _⟩
    exact (readsClose σ solved).2.trans (nameLaws_psubst σ quote)
  · intro o inC notReflection
    have in₁ := oldIn₁ o inC
    obtain ⟨in₂, label₂Eq⟩ := frame₂ o in₁ (oldPr o inC)
    have notRow : o ∉ rows := fun inRows => rowOrigin o inRows o inC rfl
    have ne₁ : o ≠ c₁.1 := fun same => notRow (same ▸ fstIn c₁ c₁In)
    have ne₂ : o ≠ c₂.1 := fun same => notRow (same ▸ fstIn c₂ c₂In)
    obtain ⟨in₃, label₃Eq⟩ := keep₃ o in₂ ne₁ ne₂ (oldTk o inC)
    obtain ⟨in₅, label₅Eq⟩ := kept o in₃ (oldNotOrder o inC) (notMade o in₂).2.2 notReflection
    refine ⟨in₅, ?_⟩
    rw [label₅Eq, label₃Eq, label₂Eq, open_label_old label C ρ₁ reflection pr tk (oldPr o inC) (oldTk o inC)]

#print axioms exists_fresh_list
#print axioms openRoot_extends
#print axioms splits_agree
#print axioms commit_fresh_exists
#print axioms refl_forward_comm

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflCorrespondence
