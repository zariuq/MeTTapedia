import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflLocatedStep

/-!
# The REFL correspondence at the name frame: the housekeeping of a reflection

The located program (`ReflLocated.located`) hosts a source REFL step of a root part `x?(P)` by a run
`openRoot ; heatChild* ; (commChild | closeChild) ; cool* ; closeRoot`. Here, at the name frame `QN`, the
housekeeping firings of that run, each admitted at every fresh opening and read at every solution of its
result:

* `openRoot_admitted`, `openRoot_reads`: a root row that reads as `x?(p) @ Root`, with a clean child location
  `Child(Root, x, p)` (`Clean`: no row reads, at any solution, as a token of the child or as a row at it), opens;
  the made rows read as `p @ Child(Root, x, p)` and `Pending(Child(Root, x, p), Root)`.
* `cool_admitted`: a row that reads as `a @ l` is cooled into a token that reads as `Done(l, m, c)`.
* `closeRoot_admitted`, `closeRoot_reads`: with the reflection, the child's token `Done(Child(Root, x, p), Root, c)`
  and no row left at the child, the close is admitted; its made row reads as `for(@c <- x) 0 @ Root`.
* `open_fresh_exists`, `cool_fresh_exists`, `close_fresh_exists`: fresh openings exist.

Every reading is solution-wise: the target is instantiated by the same solution as the row, so the child
location may carry the reflected process's variables.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflCorrespondence

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus (pFor par pZero pPar nQuote tProc pReflect)
open MeTTaCalculus.OccurrenceCommits (Enabled)
open MeTTaOperationsComm (psubst PSubst pvars psubst_of_pvars_nil psubst_pFor psubst_tProc psubst_pZero)
open MeTTaCalculus.Corrected (psubstList_eq_map)
open FiniteProgram (leftPart channelUnknown)
open Comm (Tm X E renameBy ruleVars)
open OneFrame (embed)
open ReflNames (NameLaws nameAction QN QNE nameFiring fresh_name nameLaws_pFor_iff nameLaws_tProc
  bagLaws_of_nameLaws)
open ReflLocated (atLoc rootLoc childLoc pendingTok doneTok locL locM reflP accC anyY anyZ located cool closeRoot
  closeRoot_mem openRoot openRoot_mem locatedFrame_name psubst_rootLoc psubst_atLoc_any psubst_pendingTok psubst_par)
open ReflPacking (psubst_doneTok nameLaws_doneTok_iff coolAt cool_mem)
open ReflLocatedStep (psubst_childLoc nameLaws_pendingTok_iff nameLaws_childLoc_iff psubst_pReflect
  nameLaws_pReflect_iff info_known take_reads read_reads res)

/-! ## The firings -/

variable {O : Type*}

/-- The opening at the root: read the reflection `reflection`; make the child's row `made₁` and its token
`madeTok`. -/
def openRootAt (ρ : PSubst) (reflection made₁ madeTok : O) : Firing O QNE located PUnit.unit :=
  ⟨openRoot, openRoot_mem, PUnit.unit, ρ, ⟨[], [reflection], [made₁, madeTok]⟩, []⟩

/-- The same firing at the syntactic frame. -/
def openRootAtX (ρ : PSubst) (reflection made₁ madeTok : O) : Firing O E located PUnit.unit :=
  ⟨openRoot, openRoot_mem, PUnit.unit, ρ, ⟨[], [reflection], [made₁, madeTok]⟩, []⟩

/-- Cooling at the syntactic frame. -/
def coolAtX (ρ : PSubst) (d r d' : O) : Firing O E located PUnit.unit :=
  ⟨cool, cool_mem, PUnit.unit, ρ, ⟨[d, r], [], [d']⟩, []⟩

/-- The close at the root: take the reflection `reflection` and the child's token `token`; make the listener
`made₁`. -/
def closeRootAt (ρ : PSubst) (reflection token made₁ : O) : Firing O QNE located PUnit.unit :=
  ⟨closeRoot, closeRoot_mem, PUnit.unit, ρ, ⟨[reflection, token], [], [made₁]⟩, []⟩

/-- The same firing at the syntactic frame. -/
def closeRootAtX (ρ : PSubst) (reflection token made₁ : O) : Firing O E located PUnit.unit :=
  ⟨closeRoot, closeRoot_mem, PUnit.unit, ρ, ⟨[reflection, token], [], [made₁]⟩, []⟩

theorem openRootAt_eq (ρ : PSubst) (reflection made₁ madeTok : O) :
    openRootAt ρ reflection made₁ madeTok = nameFiring (openRootAtX ρ reflection made₁ madeTok) := rfl

theorem coolAt_eq (ρ : PSubst) (d r d' : O) : coolAt ρ d r d' = nameFiring (coolAtX ρ d r d') := rfl

theorem closeRootAt_eq (ρ : PSubst) (reflection token made₁ : O) :
    closeRootAt ρ reflection token made₁ = nameFiring (closeRootAtX ρ reflection token made₁) := rfl

/-! ## Fresh openings exist -/

theorem open_fresh_exists (label : O → Pattern) (C : Configuration Pattern O) (reflection made₁ madeTok : O) :
    ∃ ρ : PSubst, (openRootAt ρ reflection made₁ madeTok).Fresh QN (embed label C) := by
  obtain ⟨g, injective, avoids⟩ := Comm.exists_apart_renaming (embed label C) (ruleVars openRoot)
  refine ⟨renameBy g, ?_⟩
  rw [openRootAt_eq]
  exact fresh_name (Comm.fresh_of_renaming (embed label C) (openRootAtX (renameBy g) reflection made₁ madeTok) g
    rfl injective avoids)

theorem cool_fresh_exists (label : O → Pattern) (C : Configuration Pattern O) (d r d' : O) :
    ∃ ρ : PSubst, (coolAt ρ d r d').Fresh QN (embed label C) := by
  obtain ⟨g, injective, avoids⟩ := Comm.exists_apart_renaming (embed label C) (ruleVars cool)
  refine ⟨renameBy g, ?_⟩
  rw [coolAt_eq]
  exact fresh_name (Comm.fresh_of_renaming (embed label C) (coolAtX (renameBy g) d r d') g rfl injective avoids)

theorem close_fresh_exists (label : O → Pattern) (C : Configuration Pattern O) (reflection token made₁ : O) :
    ∃ ρ : PSubst, (closeRootAt ρ reflection token made₁).Fresh QN (embed label C) := by
  obtain ⟨g, injective, avoids⟩ := Comm.exists_apart_renaming (embed label C) (ruleVars closeRoot)
  refine ⟨renameBy g, ?_⟩
  rw [closeRootAt_eq]
  exact fresh_name (Comm.fresh_of_renaming (embed label C) (closeRootAtX (renameBy g) reflection token made₁) g
    rfl injective avoids)

/-! ## Opening -/

/-- **A clean location**: no row reads, at any solution of the knowledge, as a token of `l` or as a row at `l`. -/
def Clean (l : Pattern) (label : O → Pattern) (C : Configuration Pattern O) : Prop :=
  ∀ o ∈ C.present, ∀ σ : PSubst, nameAction.Models σ C.equations →
    (∀ m, ¬ NameLaws (psubst σ (label o)) (pendingTok (psubst σ l) m)) ∧
    (∀ m c, ¬ NameLaws (psubst σ (label o)) (doneTok (psubst σ l) m c)) ∧
    (∀ y, ¬ NameLaws (psubst σ (label o)) (atLoc y (psubst σ l)))

/-- The instance of the opening's unknowns. -/
def openInstance (x p : Pattern) : PSubst := fun v =>
  if v = "X" then some x else if v = "P" then some p else none

/-- At every solution of an opening's information, the opened channel and process read as the reflection's. -/
theorem open_reading (label : O → Pattern) (C : Configuration Pattern O) (x p : Pattern)
    (reflection made₁ madeTok : O) (ρ : PSubst)
    (readsReflection : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label reflection)) (psubst σ (atLoc (pReflect x p) rootLoc)))
    {σ : PSubst}
    (solved : nameAction.Models σ ((openRootAt ρ reflection made₁ madeTok).information QN (embed label C))) :
    NameLaws (psubst σ (psubst ρ channelUnknown)) (psubst σ x) ∧ NameLaws (psubst σ (psubst ρ reflP)) (psubst σ p) := by
  have zipped : (atLoc (pReflect channelUnknown reflP) rootLoc, reflection) ∈
      (openRootAt ρ reflection made₁ madeTok).rule.body.read.zip
        (openRootAt ρ reflection made₁ madeTok).selection.read := by
    simp [openRootAt, openRoot]
  have read := (read_reads _ solved zipped).trans (readsReflection σ (info_known _ solved))
  simp only [psubst_atLoc_any, psubst_pReflect, psubst_rootLoc] at read
  obtain ⟨parts, -⟩ := (locatedFrame_name.atLoc_iff _ _ _ _).mp read
  exact nameLaws_pReflect_iff.mp parts

theorem openRoot_shapes (label : O → Pattern) (C : Configuration Pattern O) (ρ : PSubst)
    (reflection made₁ madeTok : O) (apart : made₁ ≠ madeTok)
    (fresh : (openRootAt ρ reflection made₁ madeTok).Fresh QN (embed label C)) :
    (openRootAt ρ reflection made₁ madeTok).Shapes QN (embed label C) :=
  ⟨fresh, List.nodup_nil, by simp [openRootAt, apart], rfl, rfl, rfl, rfl⟩

theorem openRoot_enabled [DecidableEq O] (C : Configuration Pattern O) (ρ : PSubst)
    (reflection made₁ madeTok : O) (present : reflection ∈ C.present)
    (fresh : made₁ ∉ C.present ∧ madeTok ∉ C.present) :
    Enabled (fun _ : O => ()) C.present ((openRootAt ρ reflection made₁ madeTok).selection.commit (T := Unit)) := by
  refine ⟨?_, ?_, ?_, ?_, fun query member => by simp [Selection.commit] at member⟩
  · intro o member
    simp [openRootAt, Selection.commit] at member
  · intro o member
    simp only [openRootAt, Selection.commit, List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
      Finset.mem_singleton] at member
    subst member
    exact present
  · simp [openRootAt, Selection.commit]
  · rw [Finset.disjoint_left]
    intro o member
    simp only [openRootAt, Selection.commit, List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
      Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl
    · exact fresh.1
    · exact fresh.2

/-- **Opening at the root**: a root row that reads as `x?(p) @ Root` at every solution of the knowledge, with a
clean child location, opens at every fresh opening. -/
theorem openRoot_admitted [DecidableEq O] (label : O → Pattern) (C : Configuration Pattern O) (x p : Pattern)
    (reflection made₁ madeTok : O)
    (readsReflection : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label reflection)) (psubst σ (atLoc (pReflect x p) rootLoc)))
    (clean : Clean (childLoc rootLoc x p) label C)
    (present : reflection ∈ C.present) (madeDistinct : made₁ ≠ madeTok)
    (fresh : made₁ ∉ C.present ∧ madeTok ∉ C.present)
    {σ₀ : PSubst} (known : nameAction.Models σ₀ C.equations)
    {ρ : PSubst} (opensFreshly : (openRootAt ρ reflection made₁ madeTok).Fresh QN (embed label C)) :
    (RuleSyntax.step QN O QNE located).Admits (s := embed label C) (openRootAt ρ reflection made₁ madeTok) := by
  let h : PSubst := openInstance (psubst σ₀ x) (psubst σ₀ p)
  have hReflection : psubst h (atLoc (pReflect channelUnknown reflP) rootLoc) =
      psubst σ₀ (atLoc (pReflect x p) rootLoc) := by
    simp [h, openInstance, atLoc, pReflect, channelUnknown, reflP, rootLoc, psubst, psubstList_eq_map]
  obtain ⟨w, solved, -, -⟩ := Comm.information_amalgamates_matched (Y := QN) (s := embed label C)
    (openRootAt ρ reflection made₁ madeTok) opensFreshly (b := PUnit.unit) σ₀ h known
    (fun _ member => (List.not_mem_nil member).elim)
    (fun _ member => (List.not_mem_nil member).elim)
    (fun o member => by
      obtain rfl := List.mem_singleton.mp member
      exact present)
    (fun _ member => (List.not_mem_nil member).elim)
    (fun q member => by
      obtain rfl := List.mem_singleton.mp member
      show NameLaws (psubst h (atLoc (pReflect channelUnknown reflP) rootLoc)) (psubst σ₀ (label reflection))
      rw [hReflection]
      exact (readsReflection σ₀ known).symm)
  refine (RuleSyntax.admits_iff _).mpr ⟨opensFreshly,
    (openRoot_shapes label C ρ reflection made₁ madeTok madeDistinct opensFreshly).2,
    openRoot_enabled C ρ reflection made₁ madeTok present fresh,
    ⟨PUnit.unit, w, solved⟩, ?_, fun _ member => (List.not_mem_nil member).elim⟩
  · intro check member _ σ solvedσ
    have only : ((openRootAt ρ reflection made₁ madeTok).opened QN).checks =
        [.predicate .none (psubst ρ (pendingTok (childLoc rootLoc channelUnknown reflP) rootLoc)),
          .predicate .none (psubst ρ (doneTok (childLoc rootLoc channelUnknown reflP) rootLoc anyZ)),
          .predicate .none (psubst ρ (atLoc anyY (childLoc rootLoc channelUnknown reflP)))] := rfl
    have knownσ := info_known _ solvedσ
    obtain ⟨chan, proc⟩ := open_reading label C x p reflection made₁ madeTok ρ readsReflection solvedσ
    have child : NameLaws (childLoc rootLoc (psubst σ (psubst ρ channelUnknown)) (psubst σ (psubst ρ reflP)))
        (psubst σ (childLoc rootLoc x p)) := by
      rw [psubst_childLoc, psubst_rootLoc]
      exact nameLaws_childLoc_iff.mpr ⟨NameLaws.refl _, chan, proc⟩
    rw [only] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · intro o presentO same
      rw [OneFrame.row_eq] at same
      change NameLaws (psubst σ (psubst ρ (pendingTok (childLoc rootLoc channelUnknown reflP) rootLoc)))
        (psubst σ (label o)) at same
      simp only [psubst_pendingTok, psubst_childLoc, psubst_rootLoc] at same
      exact (clean o presentO σ knownσ).1 _ (same.symm.trans (nameLaws_pendingTok_iff.mpr ⟨child, NameLaws.refl _⟩))
    · intro o presentO same
      rw [OneFrame.row_eq] at same
      change NameLaws (psubst σ (psubst ρ (doneTok (childLoc rootLoc channelUnknown reflP) rootLoc anyZ)))
        (psubst σ (label o)) at same
      simp only [psubst_doneTok, psubst_childLoc, psubst_rootLoc] at same
      exact (clean o presentO σ knownσ).2.1 _ _
        (same.symm.trans (nameLaws_doneTok_iff.mpr ⟨child, NameLaws.refl _, NameLaws.refl _⟩))
    · intro o presentO same
      rw [OneFrame.row_eq] at same
      change NameLaws (psubst σ (psubst ρ (atLoc anyY (childLoc rootLoc channelUnknown reflP))))
        (psubst σ (label o)) at same
      simp only [psubst_atLoc_any, psubst_childLoc, psubst_rootLoc] at same
      exact (clean o presentO σ knownσ).2.2 _
        (same.symm.trans ((locatedFrame_name.atLoc_iff _ _ _ _).mpr ⟨NameLaws.refl _, child⟩))

/-- **What the opening makes**: every solution of its result solves the knowledge before and reads the made rows
as `p @ Child(Root, x, p)` and `Pending(Child(Root, x, p), Root)`. -/
theorem openRoot_reads [DecidableEq O] (label : O → Pattern) (C : Configuration Pattern O) (x p : Pattern)
    (reflection made₁ madeTok : O) (ρ : PSubst)
    (readsReflection : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label reflection)) (psubst σ (atLoc (pReflect x p) rootLoc)))
    (madeDistinct : made₁ ≠ madeTok) {σ : PSubst}
    (solved : nameAction.Models σ (res label C (openRootAt ρ reflection made₁ madeTok)).knowledge) :
    nameAction.Models σ C.equations ∧
      NameLaws (psubst σ ((res label C (openRootAt ρ reflection made₁ madeTok)).label made₁))
        (psubst σ (atLoc p (childLoc rootLoc x p))) ∧
      NameLaws (psubst σ ((res label C (openRootAt ρ reflection made₁ madeTok)).label madeTok))
        (psubst σ (pendingTok (childLoc rootLoc x p) rootLoc)) := by
  have info : (res label C (openRootAt ρ reflection made₁ madeTok)).knowledge =
      (openRootAt ρ reflection made₁ madeTok).information QN (embed label C) := rfl
  rw [info] at solved
  obtain ⟨chan, proc⟩ := open_reading label C x p reflection made₁ madeTok ρ readsReflection solved
  have label₁ : (res label C (openRootAt ρ reflection made₁ madeTok)).label made₁ =
      psubst ρ (atLoc reflP (childLoc rootLoc channelUnknown reflP)) := by
    show (if made₁ = made₁ then psubst ρ (atLoc reflP (childLoc rootLoc channelUnknown reflP)) else _) = _
    rw [if_pos rfl]
  have label₂ : (res label C (openRootAt ρ reflection made₁ madeTok)).label madeTok =
      psubst ρ (pendingTok (childLoc rootLoc channelUnknown reflP) rootLoc) := by
    show (if madeTok = made₁ then _ else if madeTok = madeTok then
      psubst ρ (pendingTok (childLoc rootLoc channelUnknown reflP) rootLoc) else _) = _
    rw [if_neg (Ne.symm madeDistinct), if_pos rfl]
  have child : NameLaws (childLoc rootLoc (psubst σ (psubst ρ channelUnknown)) (psubst σ (psubst ρ reflP)))
      (childLoc rootLoc (psubst σ x) (psubst σ p)) :=
    nameLaws_childLoc_iff.mpr ⟨NameLaws.refl _, chan, proc⟩
  rw [label₁, label₂]
  simp only [psubst_atLoc_any, psubst_pendingTok, psubst_childLoc, psubst_rootLoc]
  exact ⟨info_known _ solved, (locatedFrame_name.atLoc_iff _ _ _ _).mpr ⟨proc, child⟩,
    nameLaws_pendingTok_iff.mpr ⟨child, NameLaws.refl _⟩⟩

/-- The raw opening checks the symbolic child description. A pending
token at that description blocks an opening even at another occurrence
of the same reflection. -/
theorem openRoot_refused_by_pending [DecidableEq O] (label : O → Pattern) (C : Configuration Pattern O)
    (x p : Pattern) (reflection token made₁ madeTok : O) (ρ : PSubst)
    (present : token ∈ C.present)
    (readsReflection : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label reflection)) (psubst σ (atLoc (pReflect x p) rootLoc)))
    (readsToken : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label token)) (psubst σ (pendingTok (childLoc rootLoc x p) rootLoc))) :
    ¬ (RuleSyntax.step QN O QNE located).Admits (s := embed label C) (openRootAt ρ reflection made₁ madeTok) := by
  intro admitted
  obtain ⟨σ, solved⟩ := ReflLocatedStep.solution_of_admitted admitted
  obtain ⟨channel, body⟩ := open_reading label C x p reflection made₁ madeTok ρ readsReflection solved
  have child : NameLaws (psubst σ (psubst ρ (childLoc rootLoc channelUnknown reflP)))
      (childLoc rootLoc (psubst σ x) (psubst σ p)) := by
    simp only [psubst_childLoc, psubst_rootLoc]
    exact nameLaws_childLoc_iff.mpr ⟨NameLaws.refl _, channel, body⟩
  apply ReflLocatedStep.check_fails_pending admitted ReflLocatedStep.openRoot_checks.1 solved child present
  simpa only [psubst_pendingTok, psubst_childLoc, psubst_rootLoc] using readsToken σ (info_known _ solved)

/-! ## Cooling -/

/-- The instance of cooling's unknowns. -/
def coolInstance (l m c a : Pattern) : PSubst := fun v =>
  if v = "L" then some l else if v = "M" then some m else if v = "C" then some c else if v = "A" then some a
  else none

/-- **Cooling is admitted**: a token that reads as `Done(l, m, c)` and a row that reads as `a @ l`, at every
solution of the knowledge, distinct and present, a fresh made identity, a solution of the knowledge, a fresh
opening. -/
theorem cool_admitted [DecidableEq O] (label : O → Pattern) (C : Configuration Pattern O) (l m c a : Pattern)
    (d r d' : O)
    (readsToken : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label d)) (psubst σ (doneTok l m c)))
    (readsRow : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label r)) (psubst σ (atLoc a l)))
    (distinct : d ≠ r) (presentToken : d ∈ C.present) (presentRow : r ∈ C.present) (fresh : d' ∉ C.present)
    {σ₀ : PSubst} (known : nameAction.Models σ₀ C.equations)
    {ρ : PSubst} (opensFreshly : (coolAt ρ d r d').Fresh QN (embed label C)) :
    (RuleSyntax.step QN O QNE located).Admits (s := embed label C) (coolAt ρ d r d') := by
  let h : PSubst := coolInstance (psubst σ₀ l) (psubst σ₀ m) (psubst σ₀ c) (psubst σ₀ a)
  have hToken : psubst h (doneTok locL locM accC) = psubst σ₀ (doneTok l m c) := by
    simp [h, coolInstance, doneTok, locL, locM, accC, psubst, psubstList_eq_map]
  have hRow : psubst h (atLoc leftPart locL) = psubst σ₀ (atLoc a l) := by
    simp [h, coolInstance, atLoc, leftPart, locL, psubst, psubstList_eq_map]
  obtain ⟨w, solved, -, -⟩ := Comm.information_amalgamates_matched (Y := QN) (s := embed label C)
    (coolAt ρ d r d') opensFreshly (b := PUnit.unit) σ₀ h known
    (fun _ member => (List.not_mem_nil member).elim)
    (fun o member => by
      simp only [coolAt, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact presentToken
      · exact presentRow)
    (fun _ member => (List.not_mem_nil member).elim)
    (fun q member => by
      simp only [coolAt, cool, List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil,
        or_false] at member
      rcases member with rfl | rfl
      · show NameLaws (psubst h (doneTok locL locM accC)) (psubst σ₀ (label d))
        rw [hToken]
        exact (readsToken σ₀ known).symm
      · show NameLaws (psubst h (atLoc leftPart locL)) (psubst σ₀ (label r))
        rw [hRow]
        exact (readsRow σ₀ known).symm)
    (fun _ member => (List.not_mem_nil member).elim)
  refine (RuleSyntax.admits_iff _).mpr ⟨opensFreshly,
    ⟨by simp [coolAt, distinct], by simp [coolAt], rfl, rfl, rfl, rfl⟩,
    ⟨?_, ?_, ?_, ?_, fun query member => by simp [Selection.commit] at member⟩,
    ⟨PUnit.unit, w, solved⟩, fun _ member => (List.not_mem_nil member).elim,
    fun _ member => (List.not_mem_nil member).elim⟩
  · intro o member
    simp only [coolAt, Selection.commit, List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
      Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl
    · exact presentToken
    · exact presentRow
  · intro o member
    simp [coolAt, Selection.commit] at member
  · simp [coolAt, Selection.commit]
  · rw [Finset.disjoint_left]
    intro o member
    simp only [coolAt, Selection.commit, List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
      Finset.mem_singleton] at member
    subst member
    exact fresh

/-! ## Closing at the root -/

/-- The instance of the close's unknowns. -/
def closeInstance (x p c : Pattern) : PSubst := fun v =>
  if v = "X" then some x else if v = "P" then some p else if v = "C" then some c else none

/-- At every solution of a close's information, the opened channel and process read as the reflection's and
the opened accumulator as the token's. -/
theorem close_reading (label : O → Pattern) (C : Configuration Pattern O) (x p c : Pattern)
    (reflection token made₁ : O) (ρ : PSubst)
    (readsReflection : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label reflection)) (psubst σ (atLoc (pReflect x p) rootLoc)))
    (readsToken : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label token)) (psubst σ (doneTok (childLoc rootLoc x p) rootLoc c)))
    {σ : PSubst}
    (solved : nameAction.Models σ ((closeRootAt ρ reflection token made₁).information QN (embed label C))) :
    NameLaws (psubst σ (psubst ρ channelUnknown)) (psubst σ x) ∧
      NameLaws (psubst σ (psubst ρ reflP)) (psubst σ p) ∧ NameLaws (psubst σ (psubst ρ accC)) (psubst σ c) := by
  have knownσ := info_known _ solved
  have zippedReflection : (atLoc (pReflect channelUnknown reflP) rootLoc, reflection) ∈
      (closeRootAt ρ reflection token made₁).rule.body.take.zip (closeRootAt ρ reflection token made₁).selection.taken := by
    simp [closeRootAt, closeRoot]
  have zippedToken : (doneTok (childLoc rootLoc channelUnknown reflP) rootLoc accC, token) ∈
      (closeRootAt ρ reflection token made₁).rule.body.take.zip (closeRootAt ρ reflection token made₁).selection.taken := by
    simp [closeRootAt, closeRoot]
  have readR := (take_reads _ solved zippedReflection).trans (readsReflection σ knownσ)
  have readT := (take_reads _ solved zippedToken).trans (readsToken σ knownσ)
  simp only [psubst_atLoc_any, psubst_pReflect, psubst_rootLoc] at readR
  simp only [psubst_doneTok] at readT
  obtain ⟨parts, -⟩ := (locatedFrame_name.atLoc_iff _ _ _ _).mp readR
  obtain ⟨chan, proc⟩ := nameLaws_pReflect_iff.mp parts
  obtain ⟨-, -, acc⟩ := nameLaws_doneTok_iff.mp readT
  exact ⟨chan, proc, acc⟩

/-- The raw close needs one solution matching the chosen reflection.
Its absence check is then verified for all solutions of the augmented
information: the taken token determines the checked child's location.
Nothing here identifies the occurrence that originally opened the child. -/
theorem closeRoot_admitted_at_solution [DecidableEq O] (label : O → Pattern) (C : Configuration Pattern O)
    (x p c : Pattern)
    (reflection token made₁ : O)
    {σ₀ : PSubst}
    (readsReflection : NameLaws (psubst σ₀ (label reflection)) (psubst σ₀ (atLoc (pReflect x p) rootLoc)))
    (readsToken : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label token)) (psubst σ (doneTok (childLoc rootLoc x p) rootLoc c)))
    (packed : ∀ o ∈ C.present, ∀ σ : PSubst, nameAction.Models σ C.equations → ∀ y : Pattern,
      ¬ NameLaws (psubst σ (label o)) (atLoc y (psubst σ (childLoc rootLoc x p))))
    (distinct : reflection ≠ token) (present : reflection ∈ C.present ∧ token ∈ C.present)
    (fresh : made₁ ∉ C.present)
    (known : nameAction.Models σ₀ C.equations)
    {ρ : PSubst} (opensFreshly : (closeRootAt ρ reflection token made₁).Fresh QN (embed label C)) :
    (RuleSyntax.step QN O QNE located).Admits (s := embed label C) (closeRootAt ρ reflection token made₁) := by
  let h : PSubst := closeInstance (psubst σ₀ x) (psubst σ₀ p) (psubst σ₀ c)
  have hReflection : psubst h (atLoc (pReflect channelUnknown reflP) rootLoc) =
      psubst σ₀ (atLoc (pReflect x p) rootLoc) := by
    simp [h, closeInstance, atLoc, pReflect, channelUnknown, reflP, rootLoc, psubst, psubstList_eq_map]
  have hToken : psubst h (doneTok (childLoc rootLoc channelUnknown reflP) rootLoc accC) =
      psubst σ₀ (doneTok (childLoc rootLoc x p) rootLoc c) := by
    simp [h, closeInstance, doneTok, childLoc, channelUnknown, reflP, rootLoc, accC, psubst, psubstList_eq_map]
  obtain ⟨w, solved, -, -⟩ := Comm.information_amalgamates_matched (Y := QN) (s := embed label C)
    (closeRootAt ρ reflection token made₁) opensFreshly (b := PUnit.unit) σ₀ h known
    (fun _ member => (List.not_mem_nil member).elim)
    (fun o member => by
      simp only [closeRootAt, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact present.1
      · exact present.2)
    (fun _ member => (List.not_mem_nil member).elim)
    (fun q member => by
      simp only [closeRootAt, closeRoot, List.zip_cons_cons, List.zip_nil_right, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · show NameLaws (psubst h (atLoc (pReflect channelUnknown reflP) rootLoc)) (psubst σ₀ (label reflection))
        rw [hReflection]
        exact readsReflection.symm
      · show NameLaws (psubst h (doneTok (childLoc rootLoc channelUnknown reflP) rootLoc accC))
          (psubst σ₀ (label token))
        rw [hToken]
        exact (readsToken σ₀ known).symm)
    (fun _ member => (List.not_mem_nil member).elim)
  refine (RuleSyntax.admits_iff _).mpr ⟨opensFreshly,
    ⟨by simp [closeRootAt, distinct], by simp [closeRootAt], rfl, rfl, rfl, rfl⟩,
    ⟨?_, ?_, ?_, ?_, fun query member => by simp [Selection.commit] at member⟩,
    ⟨PUnit.unit, w, solved⟩, ?_, fun _ member => (List.not_mem_nil member).elim⟩
  · intro o member
    simp only [closeRootAt, Selection.commit, List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
      Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl
    · exact present.1
    · exact present.2
  · intro o member
    simp [closeRootAt, Selection.commit] at member
  · simp [closeRootAt, Selection.commit]
  · rw [Finset.disjoint_left]
    intro o member
    simp only [closeRootAt, Selection.commit, List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
      Finset.mem_singleton] at member
    subst member
    exact fresh
  · intro check member _ σ solvedσ
    have only : ((closeRootAt ρ reflection token made₁).opened QN).checks =
        [.predicate .none (psubst ρ (atLoc anyY (childLoc rootLoc channelUnknown reflP)))] := rfl
    rw [only, List.mem_singleton] at member
    subst member
    intro o presentO same
    rw [OneFrame.row_eq] at same
    change NameLaws (psubst σ (psubst ρ (atLoc anyY (childLoc rootLoc channelUnknown reflP)))) (psubst σ (label o))
      at same
    have takesToken : (doneTok (childLoc rootLoc channelUnknown reflP) rootLoc accC, token) ∈
        (closeRootAt ρ reflection token made₁).rule.body.take.zip
          (closeRootAt ρ reflection token made₁).selection.taken := by
      simp [closeRootAt, closeRoot]
    have tokenRead := (take_reads _ solvedσ takesToken).trans (readsToken σ (info_known _ solvedσ))
    simp only [psubst_doneTok] at tokenRead
    have sameChild := (nameLaws_doneTok_iff.mp tokenRead).1
    simp only [psubst_atLoc_any, psubst_childLoc, psubst_rootLoc] at same
    apply packed o presentO σ (info_known _ solvedσ) (psubst σ (psubst ρ anyY))
    refine same.symm.trans ((locatedFrame_name.atLoc_iff _ _ _ _).mpr ⟨NameLaws.refl _, ?_⟩)
    change NameLaws _ _
    simpa only [closeRootAt, psubst_childLoc, psubst_rootLoc] using sameChild

/-- The usual close with a reflection determined at every solution is a
specialization of the raw rule's one-solution admission. -/
theorem closeRoot_admitted [DecidableEq O] (label : O → Pattern) (C : Configuration Pattern O) (x p c : Pattern)
    (reflection token made₁ : O)
    (readsReflection : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label reflection)) (psubst σ (atLoc (pReflect x p) rootLoc)))
    (readsToken : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label token)) (psubst σ (doneTok (childLoc rootLoc x p) rootLoc c)))
    (packed : ∀ o ∈ C.present, ∀ σ : PSubst, nameAction.Models σ C.equations → ∀ y : Pattern,
      ¬ NameLaws (psubst σ (label o)) (atLoc y (psubst σ (childLoc rootLoc x p))))
    (distinct : reflection ≠ token) (present : reflection ∈ C.present ∧ token ∈ C.present)
    (fresh : made₁ ∉ C.present) {σ₀ : PSubst} (known : nameAction.Models σ₀ C.equations)
    {ρ : PSubst} (opensFreshly : (closeRootAt ρ reflection token made₁).Fresh QN (embed label C)) :
    (RuleSyntax.step QN O QNE located).Admits (s := embed label C) (closeRootAt ρ reflection token made₁) :=
  closeRoot_admitted_at_solution label C x p c reflection token made₁ (readsReflection σ₀ known)
    readsToken packed distinct present fresh known opensFreshly

/-- **What the close makes**: every solution of its result solves the knowledge before and reads the made row as
`for(@c <- x) 0 @ Root`, `c` the token's accumulator. -/
theorem closeRoot_reads [DecidableEq O] (label : O → Pattern) (C : Configuration Pattern O) (x p c : Pattern)
    (reflection token made₁ : O) (ρ : PSubst)
    (readsReflection : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label reflection)) (psubst σ (atLoc (pReflect x p) rootLoc)))
    (readsToken : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label token)) (psubst σ (doneTok (childLoc rootLoc x p) rootLoc c)))
    {σ : PSubst} (solved : nameAction.Models σ (res label C (closeRootAt ρ reflection token made₁)).knowledge) :
    nameAction.Models σ C.equations ∧
      NameLaws (psubst σ ((res label C (closeRootAt ρ reflection token made₁)).label made₁))
        (psubst σ (atLoc (pFor (tProc c) x pZero) rootLoc)) := by
  have info : (res label C (closeRootAt ρ reflection token made₁)).knowledge =
      (closeRootAt ρ reflection token made₁).information QN (embed label C) := rfl
  rw [info] at solved
  obtain ⟨chan, -, acc⟩ := close_reading label C x p c reflection token made₁ ρ readsReflection readsToken solved
  have made : (res label C (closeRootAt ρ reflection token made₁)).label made₁ =
      psubst ρ (atLoc (pFor (tProc accC) channelUnknown pZero) rootLoc) := by
    show (if made₁ = made₁ then psubst ρ (atLoc (pFor (tProc accC) channelUnknown pZero) rootLoc) else _) = _
    rw [if_pos rfl]
  rw [made]
  simp only [psubst_atLoc_any, psubst_pFor, psubst_tProc, psubst_pZero, psubst_rootLoc]
  exact ⟨info_known _ solved, (locatedFrame_name.atLoc_iff _ _ _ _).mpr
    ⟨nameLaws_pFor_iff.mpr ⟨nameLaws_tProc (bagLaws_of_nameLaws acc), chan, NameLaws.refl _⟩, NameLaws.refl _⟩⟩

open ReflLocatedStep.Ownership (Store Candidate LabelForms)

/-- Invert an actual routed root return. The key comes from the taken
done ticket; the returned quote comes from the solved accumulator of
that very ticket. Neither inversion searches for a symbolically equal
child elsewhere in the store. -/
theorem closeRoot_owned_readback [DecidableEq O] (policy : ReflLocatedStep.Ownership.GuardPolicy)
    (label : O → Pattern) (C : Configuration Pattern O)
    (ledger : LocatedSubstitution.Authority.Ledger O ReflLocatedStep.Ownership.Phase)
    (ρ : PSubst) (owner token made : O)
    (formed : LabelForms ((Store.plain (embed label C) ledger) : Store O))
    (admitted : (ReflLocatedStep.Ownership.step (O := O) policy).Admits
      (s := (Store.plain (embed label C) ledger)) ⟨closeRootAt ρ owner token made, .closeRoot, rfl⟩) :
    let s : Store O := (Store.plain (embed label C) ledger)
    let f : Candidate s := ⟨closeRootAt ρ owner token made, .closeRoot, rfl⟩
    let after := (ReflLocatedStep.Ownership.step (O := O) policy).toStep.result f admitted
    ∃ ticket, s.route token = some (.control ticket .done) ∧ ticket.owner = owner ∧ ticket.parent = none ∧
      s.childRows ticket.key = ∅ ∧ s.nested ticket.key = ∅ ∧
      (∀ σ : PSubst, ∀ body loc, ∀ slot ∈ s.region ticket.key,
        ¬ NameLaws (psubst σ (atLoc body loc)) (psubst σ (label slot))) ∧
      ∀ σ : PSubst, nameAction.Models σ after.raw.knowledge →
        let x := psubst σ (psubst ρ channelUnknown)
        let p := psubst σ (psubst ρ reflP)
        let c := psubst σ (psubst ρ accC)
        nameAction.Models σ C.equations ∧
        NameLaws (psubst σ (label owner)) (atLoc (pReflect x p) rootLoc) ∧
        NameLaws (psubst σ (label token)) (doneTok (childLoc rootLoc x p) rootLoc c) ∧
        NameLaws (psubst σ (after.raw.label made)) (atLoc (pFor (tProc c) x pZero) rootLoc) := by
  intro s f after
  obtain ⟨ticket, marked, owns, home, _, _, packed, nested⟩ :=
    (ReflLocatedStep.Ownership.close_root_plan_iff s owner token made).mp admitted.2.1
  refine ⟨ticket, marked, owns, home, packed, nested, ?_, ?_⟩
  · intro σ body loc
    apply (ReflLocatedStep.Ownership.region_row_absence_iff formed ticket.key σ body loc).mp
    rw [packed]
    simp
  · have raw : after.raw = res label C (closeRootAt ρ owner token made) :=
      ReflLocatedStep.Ownership.raw_result (policy := policy) admitted
    rw [raw]
    intro σ solved
    have ownerPair : (atLoc (pReflect channelUnknown reflP) rootLoc, owner) ∈
        (closeRootAt ρ owner token made).rule.body.take.zip
          (closeRootAt ρ owner token made).selection.taken := by simp [closeRootAt, closeRoot]
    have tokenPair : (doneTok (childLoc rootLoc channelUnknown reflP) rootLoc accC, token) ∈
        (closeRootAt ρ owner token made).rule.body.take.zip
          (closeRootAt ρ owner token made).selection.taken := by simp [closeRootAt, closeRoot]
    have returned : (res label C (closeRootAt ρ owner token made)).label made =
        psubst ρ (atLoc (pFor (tProc accC) channelUnknown pZero) rootLoc) :=
      ReflLocatedStep.result_label_made_from_shapes admitted.1.1 (by simp [closeRootAt, closeRoot])
    refine ⟨info_known (closeRootAt ρ owner token made) solved, ?_, ?_, ?_⟩
    · simpa only [closeRootAt, psubst_atLoc_any, psubst_rootLoc, psubst_pReflect] using
        (take_reads (closeRootAt ρ owner token made) solved ownerPair).symm
    · simpa only [closeRootAt, psubst_doneTok, psubst_childLoc, psubst_rootLoc] using
        (take_reads (closeRootAt ρ owner token made) solved tokenPair).symm
    · rw [returned]
      simp only [psubst_atLoc_any, psubst_rootLoc, psubst_pFor, psubst_tProc, psubst_pZero]
      exact NameLaws.refl _

#print axioms open_fresh_exists
#print axioms cool_fresh_exists
#print axioms close_fresh_exists
#print axioms open_reading
#print axioms openRoot_admitted
#print axioms openRoot_reads
#print axioms cool_admitted
#print axioms close_reading
#print axioms closeRoot_admitted
#print axioms closeRoot_reads

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflCorrespondence
