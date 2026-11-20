import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflLocated
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflUniformNames

/-!
# Packing a child at the name frame

After its one step, a child location's rows are cooled one at a time into the accumulator of its `Done` token
(`ReflLocated.cool`), and the close quotes the accumulator. This module shows that the order does not matter
under the quote.

* `cooled acc rows`: what cooling builds, `(... ((acc | a₁) | a₂) ... | aₖ)`.
* `bagLaws_cooled`, `bagLaws_cooled_zero`: modulo the bag laws it is the bag of the accumulator and the rows;
  from `0`, the bag of the rows.
* `cooled_quote_bag`: **cooling the rows in any order quotes the child's bag modulo the name laws**, as a name
  `@` and as the term form of a process.
* `nameLaws_pack`, `cooled_quote_pack`: with `ReflUniform.bagLaws_pack`, cooling the represented components of
  a reduct in any order quotes the represented reduct modulo the name laws.
* `cool_reads` (one firing at `QN`): if the token reads `Done(l, m, c)` and the cooled row reads `a @ l` at
  every solution, the made token reads `Done(l, m, c | a)` at every solution.
* `CoolRun`, `coolRun_reads`, `coolRun_quote_bag` (a run of cooling firings at `QN`): from the token
  `Done(l, m, 0)`, cooling rows that read `a₁ @ l`, ..., `aₖ @ l`, in any order, gives a token whose
  accumulator reads `cooled 0 [a₁, ..., aₖ]` at every solution, and its quote is the bag of the `aᵢ` modulo the
  name laws.
* Controls (`packing_needs_the_quote`): two cooling orders give different spines at `QN` and equal quotes.

That every row of the child is cooled before the close is the close's none guard
(`ReflLocated.Controls.close_root_fires`, `close_root_waits`). That the rows are the reduct's components is
the REFL correspondence's business.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflPacking

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus (par pZero pPar nQuote tProc)
open MeTTaOperationsComm (psubst PSubst pvars psubst_of_pvars_nil)
open MeTTaCalculus.Corrected (components psubstList_eq_map)
open MeTTaCalculus.Corrected.BagControls (atomA atomB)
open FiniteProgram (leftPart)
open OneFrame (embed)
open ReflQuotient (BagLaws BagAxiom)
open ReflNames (NameLaws nameAction QN QNE nameLaws_tProc nameLaws_nQuote nameLaws_apply nameLaws_apply_iff
  nameLaws_collection IsQuote)
open ReflLocated (atLoc doneTok locL locM accC cool located locatedFrame_name psubst_atLoc_any psubst_par)

/-! ## What cooling builds -/

/-- **What cooling builds**: the rows added to the accumulator one at a time, in order. -/
def cooled (acc : Pattern) (rows : List Pattern) : Pattern := rows.foldl (fun c a => par c a) acc

theorem cooled_nil (acc : Pattern) : cooled acc [] = acc := rfl

theorem cooled_cons (acc a : Pattern) (rows : List Pattern) : cooled acc (a :: rows) = cooled (par acc a) rows :=
  rfl

theorem cooled_append (acc : Pattern) (rows : List Pattern) (a : Pattern) :
    cooled acc (rows ++ [a]) = par (cooled acc rows) a := by
  simp [cooled, List.foldl_append]

/-- **Cooling is the bag of the accumulator and the rows**, modulo the bag laws. -/
theorem bagLaws_cooled (acc : Pattern) (rows : List Pattern) : BagLaws (cooled acc rows) (pPar (acc :: rows)) := by
  induction rows generalizing acc with
  | nil => exact (BagLaws.of_axiom (.single acc)).symm
  | cons a rows ih =>
      rw [cooled_cons]
      refine (ih (par acc a)).trans ?_
      have flat := BagLaws.of_axiom (BagAxiom.flatten [] [acc, a] rows)
      simpa [par] using flat

/-- From `0`, cooling is the bag of the rows. -/
theorem bagLaws_cooled_zero (rows : List Pattern) : BagLaws (cooled pZero rows) (pPar rows) := by
  refine (bagLaws_cooled pZero rows).trans ?_
  have drop := BagLaws.of_axiom (BagAxiom.zero [] rows)
  simpa using drop

/-- **Cooling the rows in any order quotes the child's bag modulo the name laws**, as a name and as the term
form of a process. -/
theorem cooled_quote_bag {order rows : List Pattern} (perm : order.Perm rows) :
    NameLaws (tProc (cooled pZero order)) (tProc (pPar rows)) ∧
      NameLaws (nQuote (cooled pZero order)) (nQuote (pPar rows)) := by
  have inner : BagLaws (cooled pZero order) (pPar rows) :=
    (bagLaws_cooled_zero order).trans (BagLaws.of_axiom (.perm perm))
  exact ⟨nameLaws_tProc inner, nameLaws_nQuote inner⟩

/-- **`bagLaws_pack` at the name frame**: the bag of the represented components of a reduct, in any order,
quotes the represented reduct modulo the name laws. -/
theorem nameLaws_pack (R : Pattern) {L : List Pattern} (perm : L.Perm (components R)) :
    NameLaws (tProc (pPar (L.map ReflUniform.predotU))) (tProc (ReflUniform.predotU R)) :=
  nameLaws_tProc (ReflUniform.bagLaws_pack R perm)

/-- **Cooling the represented components of a reduct in any order quotes the represented reduct** modulo the
name laws. -/
theorem cooled_quote_pack (R : Pattern) {L : List Pattern} (perm : L.Perm (components R)) :
    NameLaws (tProc (cooled pZero (L.map ReflUniform.predotU))) (tProc (ReflUniform.predotU R)) :=
  nameLaws_tProc ((bagLaws_cooled_zero _).trans (ReflUniform.bagLaws_pack R perm))

theorem psubst_cooled (σ : PSubst) (acc : Pattern) (rows : List Pattern) :
    psubst σ (cooled acc rows) = cooled (psubst σ acc) (rows.map (psubst σ)) := by
  induction rows generalizing acc with
  | nil => rfl
  | cons a rows ih =>
      rw [cooled_cons, ih, psubst_par]
      rfl

/-! ## Cooling at the name frame -/

theorem cool_mem : cool ∈ located :=
  Or.inl (Or.inr (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))))

variable {O : Type*}

/-- The cooling firing at the name frame: take the token `d` and the row `r`, make the token `d'`. -/
def coolAt (ρ : PSubst) (d r d' : O) : Firing O QNE located PUnit.unit :=
  ⟨cool, cool_mem, PUnit.unit, ρ, ⟨[d, r], [], [d']⟩, []⟩

theorem coolAt_information (label : O → Pattern) (C : Configuration Pattern O) (ρ : PSubst) (d r d' : O) :
    (coolAt ρ d r d').information QN (embed label C) =
      C.equations ++ [(psubst ρ (doneTok locL locM accC), label d), (psubst ρ (atLoc leftPart locL), label r)] ++
        [] ++ [] := by
  rw [OneFrame.information_eq]
  rfl

theorem coolAt_label [DecidableEq O] (label : O → Pattern) (C : Configuration Pattern O) (ρ : PSubst)
    (d r d' : O) :
    ((coolAt ρ d r d').result QN (embed label C)).label d' = psubst ρ (doneTok locL locM (par accC leftPart)) := by
  show (if d' = d' then psubst ρ (doneTok locL locM (par accC leftPart)) else _) = _
  rw [if_pos rfl]

theorem psubst_doneTok (σ : PSubst) (l m c : Pattern) :
    psubst σ (doneTok l m c) = doneTok (psubst σ l) (psubst σ m) (psubst σ c) := by
  simp only [doneTok, psubst, psubstList_eq_map, List.map_cons, List.map_nil]

/-- A token modulo the name laws is a token, part by part. -/
theorem nameLaws_doneTok_iff {l m c l' m' c' : Pattern} :
    NameLaws (doneTok l m c) (doneTok l' m' c') ↔ NameLaws l l' ∧ NameLaws m m' ∧ NameLaws c c' := by
  rw [doneTok, doneTok, nameLaws_apply_iff (by unfold IsQuote; decide)]
  simp

theorem nameLaws_par {a b a' b' : Pattern} (left : NameLaws a a') (right : NameLaws b b') :
    NameLaws (par a b) (par a' b') :=
  nameLaws_collection _ _ (.cons left (.cons right .nil))

/-- **One cooling firing at the name frame**: if the token reads `Done(l, m, c)` and the cooled row reads
`a @ l` at every solution of the knowledge, the made token reads `Done(l, m, c | a)` at every solution of the
result. -/
theorem cool_reads [DecidableEq O] (label : O → Pattern) (C : Configuration Pattern O) (ρ : PSubst) (d r d' : O)
    (l m c a : Pattern)
    (readsToken : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label d)) (psubst σ (doneTok l m c)))
    (readsRow : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label r)) (psubst σ (atLoc a l)))
    {σ : PSubst} (solved : nameAction.Models σ ((coolAt ρ d r d').result QN (embed label C)).knowledge) :
    NameLaws (psubst σ (((coolAt ρ d r d').result QN (embed label C)).label d'))
      (psubst σ (doneTok l m (par c a))) := by
  have info : ((coolAt ρ d r d').result QN (embed label C)).knowledge =
      (coolAt ρ d r d').information QN (embed label C) := rfl
  rw [info, coolAt_information] at solved
  have known : nameAction.Models σ C.equations := fun e member => solved e (by simp [member])
  have token : NameLaws (psubst σ (psubst ρ (doneTok locL locM accC))) (psubst σ (label d)) :=
    solved (psubst ρ (doneTok locL locM accC), label d) (by simp)
  have row : NameLaws (psubst σ (psubst ρ (atLoc leftPart locL))) (psubst σ (label r)) :=
    solved (psubst ρ (atLoc leftPart locL), label r) (by simp)
  have tokenRead := token.trans (readsToken σ known)
  have rowRead := row.trans (readsRow σ known)
  rw [psubst_doneTok, psubst_doneTok, psubst_doneTok] at tokenRead
  rw [psubst_atLoc_any, psubst_atLoc_any, psubst_atLoc_any] at rowRead
  obtain ⟨locRead, parentRead, accRead⟩ := nameLaws_doneTok_iff.mp tokenRead
  obtain ⟨partRead, -⟩ := (locatedFrame_name.atLoc_iff _ _ _ _).mp rowRead
  rw [coolAt_label, psubst_doneTok, psubst_doneTok, psubst_doneTok, psubst_par, psubst_par, psubst_par]
  exact nameLaws_doneTok_iff.mpr ⟨locRead, parentRead, nameLaws_par accRead partRead⟩

/-- **A run of cooling firings at the child `l` of `m`, at the name frame**: from a state whose token `d` reads
`Done(l, m, c)`, each firing cools a row that reads `a @ l` at every solution into the current token; the
index records the cooled rows' readings in cooling order. -/
inductive CoolRun [DecidableEq O] (l m : Pattern) :
    (O → Pattern) → Configuration Pattern O → O → (O → Pattern) → Configuration Pattern O → O → List Pattern →
      Prop where
  | refl (label : O → Pattern) (C : Configuration Pattern O) (d : O) : CoolRun l m label C d label C d []
  | step {label : O → Pattern} {C : Configuration Pattern O} {d : O} {label' : O → Pattern}
      {C' : Configuration Pattern O} {d' : O} {rows : List Pattern} (ρ : PSubst) (r d₁ : O) (a : Pattern)
      (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) (coolAt ρ d r d₁))
      (readsRow : ∀ σ : PSubst, nameAction.Models σ C.equations →
        NameLaws (psubst σ (label r)) (psubst σ (atLoc a l)))
      (rest : CoolRun l m ((coolAt ρ d r d₁).result QN (embed label C)).label
        ⟨((coolAt ρ d r d₁).result QN (embed label C)).knowledge,
          ((coolAt ρ d r d₁).result QN (embed label C)).present⟩ d₁ label' C' d' rows) :
      CoolRun l m label C d label' C' d' (a :: rows)

/-- **A run of coolings reads the cooled accumulator**: if the token reads `Done(l, m, c)` at every solution
before the run, the final token reads `Done(l, m, cooled c rows)` at every solution after it, `rows` the
cooled rows' readings in cooling order. -/
theorem coolRun_reads [DecidableEq O] {l m : Pattern} {label label' : O → Pattern} {C C' : Configuration Pattern O}
    {d d' : O} {rows : List Pattern} (run : CoolRun l m label C d label' C' d' rows) :
    ∀ c : Pattern, (∀ σ : PSubst, nameAction.Models σ C.equations →
        NameLaws (psubst σ (label d)) (psubst σ (doneTok l m c))) →
      ∀ σ : PSubst, nameAction.Models σ C'.equations →
        NameLaws (psubst σ (label' d')) (psubst σ (doneTok l m (cooled c rows))) := by
  induction run with
  | refl label C d => exact fun c reads => reads
  | @step label C d label' C' d' rows ρ r d₁ a admitted readsRow rest ih =>
      intro c reads
      rw [cooled_cons]
      refine ih (par c a) fun σ solved => ?_
      exact cool_reads label C ρ d r d₁ l m c a reads readsRow solved

/-- **Cooling in any order quotes the child's bag at the name frame**: after a run of coolings from the token
`Done(l, m, 0)`, at every solution the final token's accumulator reads `cooled 0 rows`, and its quote is the
quote of the bag of the cooled rows, in any order, modulo the name laws. -/
theorem coolRun_quote_bag [DecidableEq O] {l m : Pattern} {label label' : O → Pattern}
    {C C' : Configuration Pattern O} {d d' : O} {rows bag : List Pattern} (run : CoolRun l m label C d label' C' d' rows)
    (perm : rows.Perm bag)
    (start : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label d)) (psubst σ (doneTok l m pZero)))
    (σ : PSubst) (solved : nameAction.Models σ C'.equations) :
    NameLaws (psubst σ (label' d')) (psubst σ (doneTok l m (cooled pZero rows))) ∧
      NameLaws (tProc (psubst σ (cooled pZero rows))) (tProc (pPar (bag.map (psubst σ)))) := by
  refine ⟨coolRun_reads run pZero start σ solved, ?_⟩
  rw [psubst_cooled]
  exact (cooled_quote_bag (perm.map (psubst σ))).1

/-! ## Controls -/

/-- **Packing needs the quote**: cooling `a` then `b`, or `b` then `a`, builds different spines at the name
frame, and their quotes are equal. -/
theorem packing_needs_the_quote :
    ¬ NameLaws (cooled pZero [atomA, atomB]) (cooled pZero [atomB, atomA]) ∧
      NameLaws (tProc (cooled pZero [atomA, atomB])) (tProc (cooled pZero [atomB, atomA])) := by
  constructor <;> decide +kernel

/-- Multiplicity is kept: cooling one row twice is not cooling it once, even under the quote. -/
theorem packing_keeps_multiplicity :
    ¬ NameLaws (tProc (cooled pZero [atomA, atomA])) (tProc (cooled pZero [atomA])) := by
  decide +kernel

#print axioms bagLaws_cooled
#print axioms bagLaws_cooled_zero
#print axioms cooled_quote_bag
#print axioms nameLaws_pack
#print axioms cooled_quote_pack
#print axioms psubst_cooled
#print axioms cool_reads
#print axioms coolRun_reads
#print axioms coolRun_quote_bag
#print axioms packing_needs_the_quote
#print axioms packing_keeps_multiplicity

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflPacking
