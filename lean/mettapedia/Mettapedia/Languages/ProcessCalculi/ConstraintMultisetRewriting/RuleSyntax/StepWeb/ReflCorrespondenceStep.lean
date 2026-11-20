import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflCorrespondenceRuns

/-!
# The REFL correspondence at the name frame: heating at the child and the child's one step

* `LocatedRun`: a run of the located program at the name frame between embedded states; cooling runs are runs
  (`coolRun_located`).
* `Splits p L`: a binary splitting of `p` into the leaves `L` (any depth, chosen freely).
* `heating_live` (**heating liveness**): while the child's `Pending(l, m)` token is present, a row that reads as
  `p @ l` is heated, for every splitting of `p` into leaves `L`, into rows that read as the leaves at `l`; every
  other row keeps its presence and its label.
* `child_comm_reads`, `child_commit`: the located COMM at a child, read at every solution of its result: the
  patterns unify, the made rows read as the continuations at `l` (under the step-1′ hypotheses: as the
  represented dotted continuations), and the made token as `Done(l, m, 0)`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflCorrespondence

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.OSLF.MeTTaIL.Match (Bindings)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus (pFor par pZero pPar nQuote tProc pReflect applyDot)
open MeTTaOperationsComm (psubst PSubst pvars psubst_of_pvars_nil psubst_pFor psubst_pZero psubst_none dotted
  GroundPrincipal firstOrder)
open MeTTaCalculus.Corrected (Apart)
open FiniteProgram (predot predot_pFor keys_of_apart firstPattern secondPattern channelUnknown firstBody
  secondBody leftPart rightPart)
open Comm (Tm X E renameBy ruleVars)
open OneFrame (embed)
open ReflQuotient (bagCanon groundBags agrees_of_groundPrincipal)
open ReflNames (NameLaws nameAction QN QNE nameFiring fresh_name nameLaws_pFor_iff bagLaws_of_nameLaws
  dotted_reads_predot_name)
open ReflLocated (atLoc pendingTok doneTok locL locM located heatChild heatChild_mem heatChildN heatChild_admitted
  heatChild_reads_determinately locatedFrame_name psubst_atLoc_any psubst_pendingTok psubst_par)
open ReflPacking (psubst_doneTok nameLaws_doneTok_iff CoolRun)
open ReflLocatedStep (nameLaws_pendingTok_iff info_known take_reads solution_of_admitted result_present
  result_label_old res resConf commChildAt child_comm_admitted)

variable {O : Type*}

/-! ## Runs -/

/-- **A run of the located program at the name frame**, between embedded states. -/
inductive LocatedRun [DecidableEq O] :
    (O → Pattern) → Configuration Pattern O → (O → Pattern) → Configuration Pattern O → Prop where
  | refl (label : O → Pattern) (C : Configuration Pattern O) : LocatedRun label C label C
  | step {label : O → Pattern} {C : Configuration Pattern O} {label' : O → Pattern} {C' : Configuration Pattern O}
      (g : Firing O QNE located PUnit.unit)
      (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) g)
      (rest : LocatedRun (res label C g).label (resConf label C g) label' C') : LocatedRun label C label' C'

theorem LocatedRun.trans [DecidableEq O] {label₁ label₂ label₃ : O → Pattern}
    {C₁ C₂ C₃ : Configuration Pattern O} (first : LocatedRun label₁ C₁ label₂ C₂)
    (second : LocatedRun label₂ C₂ label₃ C₃) : LocatedRun label₁ C₁ label₃ C₃ := by
  revert second
  induction first with
  | refl => exact id
  | step g admitted _ ih => exact fun second => .step g admitted (ih second)

/-- A cooling run is a run. -/
theorem coolRun_located [DecidableEq O] {l m : Pattern} {label label' : O → Pattern}
    {C C' : Configuration Pattern O} {d d' : O} {rows : List Pattern} (run : CoolRun l m label C d label' C' d' rows) :
    LocatedRun label C label' C' := by
  induction run with
  | refl label C d => exact .refl label C
  | step ρ r d₁ a admitted readsRow rest ih => exact .step _ admitted ih

/-! ## Heating at the child -/

/-- Heating at a child at the syntactic frame. -/
def heatChildX (ρ : PSubst) (o p m₁ m₂ : O) : Firing O E located PUnit.unit :=
  ⟨heatChild, heatChild_mem, PUnit.unit, ρ, ⟨[o], [p], [m₁, m₂]⟩, []⟩

theorem heatChildN_eq (ρ : PSubst) (o p m₁ m₂ : O) : heatChildN ρ o p m₁ m₂ = nameFiring (heatChildX ρ o p m₁ m₂) :=
  rfl

theorem heat_fresh_exists (label : O → Pattern) (C : Configuration Pattern O) (o p m₁ m₂ : O) :
    ∃ ρ : PSubst, (heatChildN ρ o p m₁ m₂).Fresh QN (embed label C) := by
  obtain ⟨g, injective, avoids⟩ := Comm.exists_apart_renaming (embed label C) (ruleVars heatChild)
  refine ⟨renameBy g, ?_⟩
  rw [heatChildN_eq]
  exact fresh_name (Comm.fresh_of_renaming (embed label C) (heatChildX (renameBy g) o p m₁ m₂) g rfl injective
    avoids)

theorem heat_present [DecidableEq O] (label : O → Pattern) (C : Configuration Pattern O) (ρ : PSubst)
    (o p m₁ m₂ o' : O) :
    o' ∈ (res label C (heatChildN ρ o p m₁ m₂)).present ↔ (o' ∈ C.present ∧ o' ≠ o) ∨ o' = m₁ ∨ o' = m₂ := by
  rw [result_present]
  simp [heatChildN]

theorem heat_label_old [DecidableEq O] (label : O → Pattern) (C : Configuration Pattern O) (ρ : PSubst)
    (o p m₁ m₂ : O) {o' : O} (other₁ : o' ≠ m₁) (other₂ : o' ≠ m₂) :
    (res label C (heatChildN ρ o p m₁ m₂)).label o' = label o' :=
  result_label_old _ (by simp [heatChildN, other₁, other₂])

theorem heat_back [DecidableEq O] (label : O → Pattern) (C : Configuration Pattern O) (ρ : PSubst) (o p m₁ m₂ : O)
    {σ : PSubst} (solved : nameAction.Models σ (resConf label C (heatChildN ρ o p m₁ m₂)).equations) :
    nameAction.Models σ C.equations :=
  info_known (label := label) (C := C) (heatChildN ρ o p m₁ m₂) solved

/-- **Solutions extend through heating**: for every solution `σ₀` of the knowledge there is a solution of the
heating's information that reads every present row as `σ₀` does. -/
theorem heat_extends [DecidableEq O] (label : O → Pattern) (C : Configuration Pattern O) (o p m₁ m₂ : O)
    (present : o ∈ C.present) (tokenPresent : p ∈ C.present) (l m a b : Pattern)
    (reads : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label o)) (psubst σ (atLoc (par a b) l)))
    (readsToken : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label p)) (psubst σ (pendingTok l m)))
    {ρ : PSubst} (opensFreshly : (heatChildN ρ o p m₁ m₂).Fresh QN (embed label C))
    {σ₀ : PSubst} (known : nameAction.Models σ₀ C.equations) :
    ∃ w : PSubst, nameAction.Models w (resConf label C (heatChildN ρ o p m₁ m₂)).equations ∧
      ∀ o' ∈ C.present, NameLaws (psubst w (label o')) (psubst σ₀ (label o')) := by
  let h : PSubst := fun v =>
    if v = "A" then some (psubst σ₀ a) else if v = "B" then some (psubst σ₀ b)
    else if v = "L" then some (psubst σ₀ l) else if v = "M" then some (psubst σ₀ m) else none
  have splitTake : psubst h (atLoc (par leftPart rightPart) locL) = psubst σ₀ (atLoc (par a b) l) := by
    simp only [psubst_atLoc_any, psubst_par]
    rfl
  have splitRead : psubst h (pendingTok locL locM) = psubst σ₀ (pendingTok l m) := by
    simp only [psubst_pendingTok]
    rfl
  obtain ⟨w, solved, onState, -⟩ := Comm.information_amalgamates_matched (Y := QN) (s := embed label C)
    (heatChildN ρ o p m₁ m₂) opensFreshly (b := PUnit.unit) σ₀ h known
    (fun _ member => (List.not_mem_nil member).elim)
    (fun o' member => by
      obtain rfl := List.mem_singleton.mp member
      exact present)
    (fun o' member => by
      obtain rfl := List.mem_singleton.mp member
      exact tokenPresent)
    (fun q member => by
      obtain rfl := List.mem_singleton.mp member
      show NameLaws (psubst h (atLoc (par leftPart rightPart) locL)) (psubst σ₀ (label o))
      rw [splitTake]
      exact (reads σ₀ known).symm)
    (fun q member => by
      obtain rfl := List.mem_singleton.mp member
      show NameLaws (psubst h (pendingTok locL locM)) (psubst σ₀ (label p))
      rw [splitRead]
      exact (readsToken σ₀ known).symm)
  refine ⟨w, solved, fun o' present' => ?_⟩
  have agree : NameLaws (psubst w (psubst (fun _ => none) (label o'))) (psubst σ₀ (label o')) :=
    onState (label o') (Or.inr (Or.inr ⟨o', present', rfl⟩))
  rw [psubst_none] at agree
  exact agree

/-- **A binary splitting of a process into leaves**: the process itself, or a binary parallel composition whose
members are split. -/
inductive Splits : Pattern → List Pattern → Prop where
  | leaf (p : Pattern) : Splits p [p]
  | split {a b : Pattern} {L M : List Pattern} : Splits a L → Splits b M → Splits (par a b) (L ++ M)

/-- **Heating liveness at a child**: while the token `token` reads as `Pending(l, m)`, a row `o` that reads as
`p @ l` is heated, for every splitting of `p` into leaves `L`, into distinct rows that read as the leaves at `l`,
in the order of `L`. The rows are `o` itself or new; the token and every other row keep their presence and their
labels; every present row is a new row or an old one; every solution solves the knowledge before; the knowledge
stays solvable. -/
theorem heating_live [DecidableEq O] [Infinite O] (l m : Pattern) {p : Pattern} {L : List Pattern}
    (split : Splits p L) :
    ∀ (label : O → Pattern) (C : Configuration Pattern O) (o token : O),
      o ∈ C.present → token ∈ C.present → o ≠ token →
      (∀ σ : PSubst, nameAction.Models σ C.equations →
        NameLaws (psubst σ (label o)) (psubst σ (atLoc p l))) →
      (∀ σ : PSubst, nameAction.Models σ C.equations →
        NameLaws (psubst σ (label token)) (psubst σ (pendingTok l m))) →
      (∃ σ₀ : PSubst, nameAction.Models σ₀ C.equations) →
      ∃ (label' : O → Pattern) (C' : Configuration Pattern O) (rows : List O),
        LocatedRun label C label' C' ∧ rows.length = L.length ∧ rows.Nodup ∧
        (∀ q ∈ rows.zip L, ∀ σ : PSubst, nameAction.Models σ C'.equations →
          NameLaws (psubst σ (label' q.1)) (psubst σ (atLoc q.2 l))) ∧
        (∀ r ∈ rows, r ∈ C'.present ∧ r ≠ token ∧ (r = o ∨ r ∉ C.present)) ∧
        (∀ o' ∈ C.present, o' ≠ o → o' ∈ C'.present ∧ label' o' = label o') ∧
        (∀ o' ∈ C'.present, o' ∈ rows ∨ (o' ∈ C.present ∧ o' ≠ o ∧ label' o' = label o')) ∧
        (∀ σ : PSubst, nameAction.Models σ C'.equations → nameAction.Models σ C.equations) ∧
        (∀ τ : PSubst, nameAction.Models τ C.equations → ∃ w : PSubst, nameAction.Models w C'.equations ∧
          ∀ o' ∈ C.present, o' ≠ o → NameLaws (psubst w (label o')) (psubst τ (label o'))) ∧
        (∃ σ₁ : PSubst, nameAction.Models σ₁ C'.equations) := by
  induction split with
  | leaf p =>
      intro label C o token present _ apart reads _ solvable
      refine ⟨label, C, [o], .refl label C, rfl, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_, ?_,
        fun o' presentO' _ => ⟨presentO', rfl⟩, ?_, fun σ solved => solved,
        fun τ knownτ => ⟨τ, knownτ, fun o' _ _ => ReflNames.NameLaws.refl _⟩, solvable⟩
      · intro q member
        simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_singleton] at member
        subst member
        exact reads
      · intro r member
        rw [List.mem_singleton] at member
        subst member
        exact ⟨present, apart, .inl rfl⟩
      · intro o' presentO'
        by_cases same : o' = o
        · exact .inl (List.mem_singleton.mpr same)
        · exact .inr ⟨presentO', same, rfl⟩
  | @split a b LA LB _ _ ihA ihB =>
      intro label C o token present tokenPresent apart reads readsToken solvable
      obtain ⟨m₁, fresh₁⟩ := Infinite.exists_notMem_finset C.present
      obtain ⟨m₂, fresh₂'⟩ := Infinite.exists_notMem_finset (insert m₁ C.present)
      have m₂ne : m₂ ≠ m₁ := fun same => fresh₂' (Finset.mem_insert.mpr (.inl same))
      have fresh₂ : m₂ ∉ C.present := fun inside => fresh₂' (Finset.mem_insert.mpr (.inr inside))
      have tokenNe₁ : token ≠ m₁ := fun same => fresh₁ (same ▸ tokenPresent)
      have tokenNe₂ : token ≠ m₂ := fun same => fresh₂ (same ▸ tokenPresent)
      obtain ⟨σ₀, known⟩ := solvable
      obtain ⟨ρ, opensFreshly⟩ := heat_fresh_exists label C o token m₁ m₂
      have pair : NameLaws (psubst σ₀ (label o)) (atLoc (par (psubst σ₀ a) (psubst σ₀ b)) (psubst σ₀ l)) := by
        have read := reads σ₀ known
        rw [psubst_atLoc_any, psubst_par] at read
        exact read
      have tokenRead : NameLaws (psubst σ₀ (label token)) (pendingTok (psubst σ₀ l) (psubst σ₀ m)) := by
        have read := readsToken σ₀ known
        rw [psubst_pendingTok] at read
        exact read
      have admitted := heatChild_admitted label C o token m₁ m₂ present tokenPresent apart (Ne.symm m₂ne) fresh₁
        fresh₂ known pair tokenRead opensFreshly
      obtain ⟨σ₁, solved₁⟩ := solution_of_admitted admitted
      have notInC : ∀ r, r ∉ (resConf label C (heatChildN ρ o token m₁ m₂)).present → r = o ∨ r ∉ C.present := by
        intro r notC₁
        by_cases same : r = o
        · exact .inl same
        · exact .inr fun inC => notC₁ ((heat_present label C ρ o token m₁ m₂ r).mpr (.inl ⟨inC, same⟩))
      have m₂In₁ : m₂ ∈ (resConf label C (heatChildN ρ o token m₁ m₂)).present :=
        (heat_present label C ρ o token m₁ m₂ m₂).mpr (.inr (.inr rfl))
      have tokenIn₁ : token ∈ (resConf label C (heatChildN ρ o token m₁ m₂)).present :=
        (heat_present label C ρ o token m₁ m₂ token).mpr (.inl ⟨tokenPresent, Ne.symm apart⟩)
      obtain ⟨label₂, C₂, rowsA, runA, lengthA, nodupA, readsA, factsA, frameA, coverA, monoA, extA, solvableA⟩ :=
        ihA (res label C (heatChildN ρ o token m₁ m₂)).label (resConf label C (heatChildN ρ o token m₁ m₂)) m₁ token
          ((heat_present label C ρ o token m₁ m₂ m₁).mpr (.inr (.inl rfl))) tokenIn₁
          (fun same => tokenNe₁ same.symm)
          (fun σ solved => (heatChild_reads_determinately label C ρ o token (Ne.symm m₂ne) a b l reads solved).1)
          (fun σ solved => by
            rw [heat_label_old label C ρ o token m₁ m₂ tokenNe₁ tokenNe₂]
            exact readsToken σ (heat_back label C ρ o token m₁ m₂ solved))
          ⟨σ₁, solved₁⟩
      have m₂Kept := frameA m₂ m₂In₁ m₂ne
      have tokenKept := frameA token tokenIn₁ tokenNe₁
      have notM₂ : ∀ r ∈ rowsA, r ≠ m₂ := by
        intro r inA isM₂
        rcases (factsA r inA).2.2 with isM₁ | notC₁
        · exact m₂ne (isM₂.symm.trans isM₁)
        · exact notC₁ (isM₂ ▸ m₂In₁)
      obtain ⟨label₃, C₃, rowsB, runB, lengthB, nodupB, readsB, factsB, frameB, coverB, monoB, extB, solvableB⟩ :=
        ihB label₂ C₂ m₂ token m₂Kept.1 tokenKept.1 (fun same => tokenNe₂ same.symm)
          (fun σ solved => by
            rw [m₂Kept.2]
            exact (heatChild_reads_determinately label C ρ o token (Ne.symm m₂ne) a b l reads (monoA σ solved)).2)
          (fun σ solved => by
            rw [tokenKept.2, heat_label_old label C ρ o token m₁ m₂ tokenNe₁ tokenNe₂]
            exact readsToken σ (heat_back label C ρ o token m₁ m₂ (monoA σ solved)))
          solvableA
      refine ⟨label₃, C₃, rowsA ++ rowsB, .step _ admitted (runA.trans runB), ?_, ?_, ?_, ?_, ?_, ?_,
        fun σ solved => heat_back label C ρ o token m₁ m₂ (monoA σ (monoB σ solved)), ?_, solvableB⟩
      · simp [lengthA, lengthB]
      · refine List.nodup_append.mpr ⟨nodupA, nodupB, fun x inA y inB same => ?_⟩
        obtain ⟨inC₂, -, -⟩ := factsA x inA
        rcases (factsB y inB).2.2 with isM₂ | notC₂
        · exact notM₂ x inA (same.trans isM₂)
        · exact notC₂ (same ▸ inC₂)
      · intro q member σ solved
        rw [List.zip_append lengthA] at member
        rcases List.mem_append.mp member with inA | inB
        · have qA := List.of_mem_zip inA
          rw [(frameB q.1 (factsA q.1 qA.1).1 (notM₂ q.1 qA.1)).2]
          exact readsA q inA σ (monoB σ solved)
        · exact readsB q inB σ solved
      · intro r member
        rcases List.mem_append.mp member with inA | inB
        · obtain ⟨inC₂, notToken, originA⟩ := factsA r inA
          refine ⟨(frameB r inC₂ (notM₂ r inA)).1, notToken, ?_⟩
          rcases originA with isM₁ | notC₁
          · exact .inr (isM₁ ▸ fresh₁)
          · exact notInC r notC₁
        · obtain ⟨inC₃, notToken, originB⟩ := factsB r inB
          refine ⟨inC₃, notToken, ?_⟩
          rcases originB with isM₂ | notC₂
          · exact .inr (isM₂ ▸ fresh₂)
          · by_cases same : r = o
            · exact .inl same
            · refine .inr fun inC => notC₂ (frameA r ((heat_present label C ρ o token m₁ m₂ r).mpr
                (.inl ⟨inC, same⟩)) fun isM₁ => fresh₁ (isM₁ ▸ inC)).1
      · intro o' presentO' notO
        have ne₁ : o' ≠ m₁ := fun same => fresh₁ (same ▸ presentO')
        have ne₂ : o' ≠ m₂ := fun same => fresh₂ (same ▸ presentO')
        obtain ⟨inC₂, label₂Eq⟩ := frameA o' ((heat_present label C ρ o token m₁ m₂ o').mpr
          (.inl ⟨presentO', notO⟩)) ne₁
        obtain ⟨inC₃, label₃Eq⟩ := frameB o' inC₂ ne₂
        exact ⟨inC₃, label₃Eq.trans (label₂Eq.trans (heat_label_old label C ρ o token m₁ m₂ ne₁ ne₂))⟩
      · intro o' presentO'
        rcases coverB o' presentO' with inB | ⟨inC₂, ne₂, label₃Eq⟩
        · exact .inl (List.mem_append_right _ inB)
        · rcases coverA o' inC₂ with inA | ⟨inC₁, ne₁, label₂Eq⟩
          · exact .inl (List.mem_append_left _ inA)
          · rcases (heat_present label C ρ o token m₁ m₂ o').mp inC₁ with ⟨inC, notO⟩ | isM₁ | isM₂
            · exact .inr ⟨inC, notO, label₃Eq.trans (label₂Eq.trans (heat_label_old label C ρ o token m₁ m₂ ne₁ ne₂))⟩
            · exact absurd isM₁ ne₁
            · exact absurd isM₂ ne₂
      · intro τ knownτ
        obtain ⟨w₁, solvedW₁, agree₁⟩ := heat_extends label C o token m₁ m₂ present tokenPresent l m a b reads
          readsToken opensFreshly knownτ
        obtain ⟨w₂, solvedW₂, agree₂⟩ := extA w₁ solvedW₁
        obtain ⟨w₃, solvedW₃, agree₃⟩ := extB w₂ solvedW₂
        refine ⟨w₃, solvedW₃, fun o' present' notO => ?_⟩
        have ne₁ : o' ≠ m₁ := fun same => fresh₁ (same ▸ present')
        have ne₂ : o' ≠ m₂ := fun same => fresh₂ (same ▸ present')
        have in₁ := (heat_present label C ρ o token m₁ m₂ o').mpr (.inl ⟨present', notO⟩)
        have lab₁ := heat_label_old label C ρ o token m₁ m₂ ne₁ ne₂
        obtain ⟨in₂, lab₂⟩ := frameA o' in₁ ne₁
        have a₂ := agree₂ o' in₁ ne₁
        have a₃ := agree₃ o' in₂ ne₂
        rw [lab₂, lab₁] at a₃
        rw [lab₁] at a₂
        exact a₃.trans (a₂.trans (agree₁ o' present'))

/-! ## The child's one step -/

theorem commChildAt_information [DecidableEq O] (label : O → Pattern) (C : Configuration Pattern O) (ρ : PSubst)
    (first second token made₁ made₂ madeTok : O) :
    (commChildAt ρ first second token made₁ made₂ madeTok).information QN (embed label C) =
      C.equations ++ [(psubst ρ (atLoc (pFor firstPattern channelUnknown firstBody) locL), label first),
        (psubst ρ (atLoc (pFor secondPattern channelUnknown secondBody) locL), label second),
        (psubst ρ (pendingTok locL locM), label token)] ++ [] ++
        [(psubst ρ (atLoc firstPattern locL), psubst ρ (atLoc secondPattern locL))] := by
  rw [OneFrame.information_eq]
  rfl

/-- **What every solution says after the located COMM at a child**: it solves the knowledge before, unifies the
patterns modulo the name laws, and reads each made row as the continuation its taken row holds, at `l`. -/
theorem child_comm_reads [DecidableEq O] (label : O → Pattern) (C : Configuration Pattern O)
    (t u channel₁ channel₂ K₁ K₂ l : Pattern) (first second token made₁ made₂ madeTok : O)
    (readsFirst : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label first)) (psubst σ (atLoc (pFor t channel₁ K₁) l)))
    (readsSecond : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label second)) (psubst σ (atLoc (pFor u channel₂ K₂) l)))
    (made₁₂ : made₁ ≠ made₂) (ρ : PSubst) {σ : PSubst}
    (solved : nameAction.Models σ (res label C (commChildAt ρ first second token made₁ made₂ madeTok)).knowledge) :
    nameAction.Models σ C.equations ∧ NameLaws (psubst σ t) (psubst σ u) ∧
      NameLaws (psubst σ ((res label C (commChildAt ρ first second token made₁ made₂ madeTok)).label made₁))
        (psubst σ (atLoc K₁ l)) ∧
      NameLaws (psubst σ ((res label C (commChildAt ρ first second token made₁ made₂ madeTok)).label made₂))
        (psubst σ (atLoc K₂ l)) := by
  have info : (res label C (commChildAt ρ first second token made₁ made₂ madeTok)).knowledge =
      (commChildAt ρ first second token made₁ made₂ madeTok).information QN (embed label C) := rfl
  rw [info, commChildAt_information] at solved
  have known : nameAction.Models σ C.equations := fun e member => solved e (by simp [member])
  have take₁ : NameLaws (psubst σ (psubst ρ (atLoc (pFor firstPattern channelUnknown firstBody) locL)))
      (psubst σ (label first)) :=
    solved (psubst ρ (atLoc (pFor firstPattern channelUnknown firstBody) locL), label first) (by simp)
  have take₂ : NameLaws (psubst σ (psubst ρ (atLoc (pFor secondPattern channelUnknown secondBody) locL)))
      (psubst σ (label second)) :=
    solved (psubst ρ (atLoc (pFor secondPattern channelUnknown secondBody) locL), label second) (by simp)
  have told : NameLaws (psubst σ (psubst ρ (atLoc firstPattern locL))) (psubst σ (psubst ρ (atLoc secondPattern locL))) :=
    solved (psubst ρ (atLoc firstPattern locL), psubst ρ (atLoc secondPattern locL)) (by simp)
  have row₁ := take₁.trans (readsFirst σ known)
  have row₂ := take₂.trans (readsSecond σ known)
  simp only [psubst_atLoc_any, psubst_pFor] at row₁ row₂ told
  obtain ⟨inputs₁, loc₁⟩ := (locatedFrame_name.atLoc_iff _ _ _ _).mp row₁
  obtain ⟨inputs₂, loc₂⟩ := (locatedFrame_name.atLoc_iff _ _ _ _).mp row₂
  obtain ⟨patterns, -⟩ := (locatedFrame_name.atLoc_iff _ _ _ _).mp told
  obtain ⟨pattern₁, -, body₁⟩ := nameLaws_pFor_iff.mp inputs₁
  obtain ⟨pattern₂, -, body₂⟩ := nameLaws_pFor_iff.mp inputs₂
  have label₁ : (res label C (commChildAt ρ first second token made₁ made₂ madeTok)).label made₁ =
      psubst ρ (atLoc firstBody locL) := by
    show (if made₁ = made₁ then psubst ρ (atLoc firstBody locL) else _) = _
    rw [if_pos rfl]
  have label₂ : (res label C (commChildAt ρ first second token made₁ made₂ madeTok)).label made₂ =
      psubst ρ (atLoc secondBody locL) := by
    show (if made₂ = made₁ then _ else if made₂ = made₂ then psubst ρ (atLoc secondBody locL) else _) = _
    rw [if_neg (Ne.symm made₁₂), if_pos rfl]
  refine ⟨known, pattern₁.symm.trans (patterns.trans pattern₂), ?_, ?_⟩
  · rw [label₁]
    simp only [psubst_atLoc_any]
    exact (locatedFrame_name.atLoc_iff _ _ _ _).mpr ⟨body₁, loc₁⟩
  · rw [label₂]
    simp only [psubst_atLoc_any]
    exact (locatedFrame_name.atLoc_iff _ _ _ _).mpr ⟨body₂, loc₂⟩

/-- **The child's one step, read.** In a state where `token` reads as `Pending(l, m)` and two rows read as the
represented inputs `predot (for(t <- x)A) @ l` and `predot (for(u <- x)B) @ l`, under the step-1′ hypotheses (a
ground principal unifier with first-order values, the variable convention, first-order continuations, ground
canonical bags in the patterns), with distinct taken and made identities, fresh made identities, a solution of the
knowledge unifying the patterns and a fresh opening: the located COMM is admitted, and every solution of its
result solves the knowledge before and reads the made rows as the represented dotted continuations at `l` and the
made token as `Done(l, m, 0)`. -/
theorem child_commit [DecidableEq O] (label : O → Pattern) (C : Configuration Pattern O)
    (t u channel A B l m : Pattern) (bs : Bindings) (gp : GroundPrincipal t u bs) (convention : Apart t A u B)
    (foA : firstOrder A = true) (foB : firstOrder B = true)
    (groundT : groundBags t = true) (groundU : groundBags u = true)
    (canonicalT : bagCanon t = t) (canonicalU : bagCanon u = u)
    (first second token made₁ made₂ madeTok : O)
    (readsFirst : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label first)) (psubst σ (atLoc (predot (pFor t channel A)) l)))
    (readsSecond : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label second)) (psubst σ (atLoc (predot (pFor u channel B)) l)))
    (readsToken : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label token)) (psubst σ (pendingTok l m)))
    (distinct : [first, second, token].Nodup) (madeDistinct : [made₁, made₂, madeTok].Nodup)
    (present : first ∈ C.present ∧ second ∈ C.present ∧ token ∈ C.present)
    (fresh : made₁ ∉ C.present ∧ made₂ ∉ C.present ∧ madeTok ∉ C.present)
    {σ₀ : PSubst} (known : nameAction.Models σ₀ C.equations) (unifies : NameLaws (psubst σ₀ t) (psubst σ₀ u))
    {ρ : PSubst}
    (opensFreshly : (commChildAt ρ first second token made₁ made₂ madeTok).Fresh QN (embed label C)) :
    (RuleSyntax.step QN O QNE located).Admits (s := embed label C)
        (commChildAt ρ first second token made₁ made₂ madeTok) ∧
      ∀ σ : PSubst,
        nameAction.Models σ (res label C (commChildAt ρ first second token made₁ made₂ madeTok)).knowledge →
        nameAction.Models σ C.equations ∧
        NameLaws (psubst σ ((res label C (commChildAt ρ first second token made₁ made₂ madeTok)).label made₁))
          (psubst σ (atLoc (predot (applyDot bs A)) l)) ∧
        NameLaws (psubst σ ((res label C (commChildAt ρ first second token made₁ made₂ madeTok)).label made₂))
          (psubst σ (atLoc (predot (applyDot bs B)) l)) ∧
        NameLaws (psubst σ ((res label C (commChildAt ρ first second token made₁ made₂ madeTok)).label madeTok))
          (psubst σ (doneTok l m pZero)) := by
  have rowFirst : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label first)) (psubst σ (atLoc (pFor t (predot channel) (dotted (pvars t) (predot A))) l)) :=
    fun σ solved => by
      have read := readsFirst σ solved
      rw [predot_pFor] at read
      exact read
  have rowSecond : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label second)) (psubst σ (atLoc (pFor u (predot channel) (dotted (pvars u) (predot B))) l)) :=
    fun σ solved => by
      have read := readsSecond σ solved
      rw [predot_pFor] at read
      exact read
  have admitted := child_comm_admitted label C t u (predot channel) (dotted (pvars t) (predot A))
    (dotted (pvars u) (predot B)) l m first second token made₁ made₂ madeTok rowFirst rowSecond readsToken distinct
    madeDistinct present fresh known unifies opensFreshly
  have m₁ := List.nodup_cons.mp madeDistinct
  have m₂ := List.nodup_cons.mp m₁.2
  have ne₁₂ : made₁ ≠ made₂ := fun same => m₁.1 (List.mem_cons.mpr (.inl same))
  have neT₁ : madeTok ≠ made₁ := fun same => m₁.1 (List.mem_cons.mpr (.inr (List.mem_singleton.mpr same.symm)))
  have neT₂ : madeTok ≠ made₂ := fun same => m₂.1 (List.mem_singleton.mpr same.symm)
  refine ⟨admitted, fun σ solved => ?_⟩
  obtain ⟨known', unify, body₁, body₂⟩ := child_comm_reads label C t u (predot channel) (predot channel)
    (dotted (pvars t) (predot A)) (dotted (pvars u) (predot B)) l first second token made₁ made₂ madeTok rowFirst
    rowSecond ne₁₂ ρ solved
  have agrees := agrees_of_groundPrincipal gp groundT groundU canonicalT canonicalU (bagLaws_of_nameLaws unify)
  obtain ⟨keptA, keptB⟩ := keys_of_apart convention
  have dotA : NameLaws (psubst σ (dotted (pvars t) (predot A))) (psubst σ (predot (applyDot bs A))) := by
    refine dotted_reads_predot_name gp.keys gp.covers agrees A foA (fun x inside => List.mem_append_left _ inside)
      ?_ keptA
    intro x inA inKeys
    rcases List.mem_append.mp inKeys with inT | inU
    · exact inT
    · exact absurd inA (convention.rightOutside x inU)
  have dotB : NameLaws (psubst σ (dotted (pvars u) (predot B))) (psubst σ (predot (applyDot bs B))) := by
    refine dotted_reads_predot_name gp.keys gp.covers agrees B foB (fun x inside => List.mem_append_right _ inside)
      ?_ keptB
    intro x inB inKeys
    rcases List.mem_append.mp inKeys with inT | inU
    · exact absurd inB (convention.leftOutside x inT)
    · exact inU
  have info : (res label C (commChildAt ρ first second token made₁ made₂ madeTok)).knowledge =
      (commChildAt ρ first second token made₁ made₂ madeTok).information QN (embed label C) := rfl
  have solvedInfo := solved
  rw [info] at solvedInfo
  have zippedToken : (pendingTok locL locM, token) ∈
      (commChildAt ρ first second token made₁ made₂ madeTok).rule.body.take.zip
        (commChildAt ρ first second token made₁ made₂ madeTok).selection.taken := by
    simp [commChildAt, ReflLocated.commChild]
  have tokenRead := (take_reads _ solvedInfo zippedToken).trans (readsToken σ known')
  simp only [psubst_pendingTok] at tokenRead
  obtain ⟨locRead, parentRead⟩ := nameLaws_pendingTok_iff.mp tokenRead
  have labelTok : (res label C (commChildAt ρ first second token made₁ made₂ madeTok)).label madeTok =
      psubst ρ (doneTok locL locM pZero) := by
    show (if madeTok = made₁ then _ else if madeTok = made₂ then _ else
      if madeTok = madeTok then psubst ρ (doneTok locL locM pZero) else _) = _
    rw [if_neg neT₁, if_neg neT₂, if_pos rfl]
  refine ⟨known', body₁.trans ?_, body₂.trans ?_, ?_⟩
  · simp only [psubst_atLoc_any]
    exact (locatedFrame_name.atLoc_iff _ _ _ _).mpr ⟨dotA, ReflNames.NameLaws.refl _⟩
  · simp only [psubst_atLoc_any]
    exact (locatedFrame_name.atLoc_iff _ _ _ _).mpr ⟨dotB, ReflNames.NameLaws.refl _⟩
  · rw [labelTok]
    simp only [psubst_doneTok, psubst_pZero]
    exact nameLaws_doneTok_iff.mpr ⟨locRead, parentRead, ReflNames.NameLaws.refl _⟩

#print axioms LocatedRun.trans
#print axioms coolRun_located
#print axioms heat_fresh_exists
#print axioms heat_present
#print axioms heat_extends
#print axioms heating_live
#print axioms child_comm_reads
#print axioms child_commit

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflCorrespondence
