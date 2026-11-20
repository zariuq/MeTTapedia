import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflCorrespondenceForward

/-!
# The REFL correspondence at the name frame: reflection of packing and the close

After the child `l = Child(Root, x, p)` has taken its one step, its token reads as `Done(l, Root, 0)` and its rows
read as the cells `cells` (identity, reading). Here, for EVERY run of coolings, in whatever order the run chooses,
followed by ANY admitted close of the reflection:

* `closeRoot_waits`: a close is refused while some row reads, at every solution, as a row at the child: the
  close's none check, with its free unknown `Y` moved onto that row's reading;
* `refl_close_sound`: the run cooled exactly the cells, each once, in some order, and the reflection kept its
  label;
* `refl_close_reads`: the made row reads, at every solution, as `for(@(pPar (cells' readings)) <- x) 0 @ Root`.

So the quote of the hosted REFL is the child's committed bag, whatever the order of packing; no run packs a part
of it. What is not shown here: that the committed bag is a one-step reduct of the reflected process (the commit's
soundness at the child), and that firings at other locations leave the child's rows alone (isolation).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflCorrespondence

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus (pFor par pZero pPar nQuote tProc pReflect)
open MeTTaOperationsComm (psubst PSubst pvars psubst_of_pvars_nil psubst_pFor psubst_tProc psubst_pZero psubst_none
  psubst_comp)
open MeTTaCalculus.Corrected (psubstList_eq_map)
open FiniteProgram (channelUnknown)
open OneFrame (embed)
open ReflQuotient (BagLaws BagAxiom psubst_pPar)
open ReflNames (NameLaws nameAction QN QNE nameLaws_pFor_iff nameLaws_tProc bagLaws_of_nameLaws nameLaws_collection)
open ReflLocated (atLoc rootLoc childLoc doneTok reflP anyY located closeRoot locatedFrame_name psubst_rootLoc
  psubst_atLoc_any)
open ReflPacking (cooled CoolRun coolRun_reads bagLaws_cooled_zero coolAt)
open ReflLocatedStep (psubst_childLoc psubst_pReflect nameLaws_pReflect_iff info_known take_reads res resConf
  opened_check_mem)

variable {O : Type*}

/-! ## The close waits for every row of the child -/

/-- At every solution of a close's information, the opened channel and process read as the reflection's. -/
theorem close_reflection_reading (label : O → Pattern) (C : Configuration Pattern O) (x p : Pattern)
    (reflection token made₁ : O) (ρ : PSubst)
    (readsReflection : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label reflection)) (psubst σ (atLoc (pReflect x p) rootLoc)))
    {σ : PSubst}
    (solved : nameAction.Models σ ((closeRootAt ρ reflection token made₁).information QN (embed label C))) :
    NameLaws (psubst σ (psubst ρ channelUnknown)) (psubst σ x) ∧ NameLaws (psubst σ (psubst ρ reflP)) (psubst σ p) := by
  have zipped : (atLoc (pReflect channelUnknown reflP) rootLoc, reflection) ∈
      (closeRootAt ρ reflection token made₁).rule.body.take.zip (closeRootAt ρ reflection token made₁).selection.taken := by
    simp [closeRootAt, closeRoot]
  have read := (take_reads _ solved zipped).trans (readsReflection σ (info_known _ solved))
  simp only [psubst_atLoc_any, psubst_pReflect, psubst_rootLoc] at read
  obtain ⟨parts, -⟩ := (locatedFrame_name.atLoc_iff _ _ _ _).mp read
  exact nameLaws_pReflect_iff.mp parts

/-- **The close waits**: while a row reads, at every solution of the knowledge, as `a @ Child(Root, x, p)`, every
close of the reflection `x?(p) @ Root` is refused. The close asks for the none query of `Y @ Child(Root, X, P)` with
`Y` free; moving `Y` onto `a` gives a solution of its information at which that row is present. -/
theorem closeRoot_waits [DecidableEq O] (label : O → Pattern) (C : Configuration Pattern O) (x p : Pattern)
    (reflection token made₁ : O) (ρ : PSubst)
    (readsReflection : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label reflection)) (psubst σ (atLoc (pReflect x p) rootLoc)))
    {r : O} (rowPresent : r ∈ C.present) {a : Pattern}
    (readsRow : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label r)) (psubst σ (atLoc a (childLoc rootLoc x p)))) :
    ¬ (RuleSyntax.step QN O QNE located).Admits (s := embed label C) (closeRootAt ρ reflection token made₁) := by
  intro admitted
  obtain ⟨fresh, _, enabled, ⟨_, σ, solved⟩, checks, _⟩ := (RuleSyntax.admits_iff _).mp admitted
  obtain ⟨chan, proc⟩ := close_reflection_reading label C x p reflection token made₁ ρ readsReflection solved
  let h : PSubst := fun v => if v = "Y" then some (psubst σ a) else some (psubst σ (psubst ρ (.fvar v)))
  have away : ∀ t : Pattern, "Y" ∉ pvars t → psubst h t = psubst σ (psubst ρ t) := by
    intro t apart
    rw [psubst_comp]
    apply MeTTaCalculus.Corrected.psubst_getD_congr_on
    intro v occurs
    have notY : v ≠ "Y" := fun same => apart (same ▸ occurs)
    simp only [h, if_neg notY, Option.getD_some]
    rw [psubst_comp]
    rfl
  obtain ⟨u, solvedU, onState, onRule⟩ := Comm.information_amalgamates_matched (Y := QN) (s := embed label C)
    (closeRootAt ρ reflection token made₁) fresh (b := PUnit.unit) σ h (info_known _ solved)
    (fun _ member => absurd member List.not_mem_nil)
    (fun o member => enabled.taken_subset (by simpa [Selection.commit] using member))
    (fun o member => enabled.kept_subset (by simpa [Selection.commit] using member))
    (fun qq member => by
      have inTake := (List.of_mem_zip member).1
      have apart : "Y" ∉ pvars qq.1 := by
        simp only [closeRootAt, closeRoot, List.mem_cons, List.not_mem_nil, or_false] at inTake
        rcases inTake with same | same <;> rw [same] <;> decide
      show NameLaws (psubst h qq.1) (psubst σ (label qq.2))
      rw [away qq.1 apart]
      exact take_reads _ solved member)
    (fun qq member => by simp [closeRootAt] at member)
  have holds := checks _ (opened_check_mem (g := closeRootAt ρ reflection token made₁)
    (c := .predicate .none (atLoc anyY (childLoc rootLoc channelUnknown reflP))) (by simp [closeRootAt, closeRoot]))
    PUnit.unit u solvedU
  apply holds r rowPresent
  rw [OneFrame.row_eq]
  change NameLaws (psubst u (psubst ρ (atLoc anyY (childLoc rootLoc channelUnknown reflP)))) (psubst u (label r))
  have term : atLoc anyY (childLoc rootLoc channelUnknown reflP) ∈ (closeRootAt ρ reflection token made₁).rule.terms := by
    simp [closeRootAt, Rule.terms, closeRoot, checkTerms]
  have ruleSide : NameLaws (psubst u (psubst ρ (atLoc anyY (childLoc rootLoc channelUnknown reflP))))
      (psubst h (atLoc anyY (childLoc rootLoc channelUnknown reflP))) := onRule _ term
  have stateSide : NameLaws (psubst u (psubst (fun _ => none) (label r))) (psubst σ (label r)) :=
    onState (label r) (Or.inr (Or.inr ⟨r, rowPresent, rfl⟩))
  rw [psubst_none] at stateSide
  have hCheck : psubst h (atLoc anyY (childLoc rootLoc channelUnknown reflP)) =
      atLoc (psubst σ a) (psubst σ (psubst ρ (childLoc rootLoc channelUnknown reflP))) := by
    rw [psubst_atLoc_any, away (childLoc rootLoc channelUnknown reflP) (by decide)]
    simp [h, anyY, psubst]
  have row := readsRow σ (info_known _ solved)
  rw [psubst_atLoc_any] at row
  refine ruleSide.trans ?_
  rw [hCheck]
  refine NameLaws.trans ?_ (row.symm.trans stateSide.symm)
  refine (locatedFrame_name.atLoc_iff _ _ _ _).mpr ⟨ReflNames.NameLaws.refl _, ?_⟩
  simp only [psubst_childLoc, psubst_rootLoc]
  exact ReflLocatedStep.nameLaws_childLoc_iff.mpr ⟨ReflNames.NameLaws.refl _, chan, proc⟩

/-! ## Cooling runs -/

/-- Every solution after a cooling run solves the knowledge before it. -/
theorem coolRun_back [DecidableEq O] {l m : Pattern} {label label' : O → Pattern} {C C' : Configuration Pattern O}
    {d d' : O} {rows : List Pattern} (run : CoolRun l m label C d label' C' d' rows) :
    ∀ σ : PSubst, nameAction.Models σ C'.equations → nameAction.Models σ C.equations := by
  induction run with
  | refl => exact fun σ solved => solved
  | step ρ r d₁ a admitted readsRow rest ih =>
      exact fun σ solved => coolAt_back _ _ ρ _ r d₁ (ih σ solved)

/-- **Every cooling run, followed by an admitted close, cooled exactly the cells**: each cell once, in some order
`order`; the cooled readings are the cells' readings in that order at every solution; the reflection kept its
label. -/
theorem refl_close_sound [DecidableEq O] (x p : Pattern) (reflection made₁ : O) (ρ : PSubst)
    {label : O → Pattern} {C : Configuration Pattern O} {d : O} {label' : O → Pattern}
    {C' : Configuration Pattern O} {d' : O} {rows : List Pattern}
    (run : CoolRun (childLoc rootLoc x p) rootLoc label C d label' C' d' rows)
    (closed : (RuleSyntax.step QN O QNE located).Admits (s := embed label' C') (closeRootAt ρ reflection d' made₁)) :
    ∀ (cells : List (O × Pattern)), (cells.map Prod.fst).Nodup →
      (∀ q ∈ cells, q.1 ∈ C.present ∧ q.1 ≠ d ∧ ∀ σ : PSubst, nameAction.Models σ C.equations →
        NameLaws (psubst σ (label q.1)) (psubst σ (atLoc q.2 (childLoc rootLoc x p)))) →
      (∀ o ∈ C.present, o ≠ d → o ∉ cells.map Prod.fst → ∀ σ : PSubst, nameAction.Models σ C.equations →
        ∀ y : Pattern, ¬ NameLaws (psubst σ (label o)) (atLoc y (psubst σ (childLoc rootLoc x p)))) →
      reflection ∈ C.present → reflection ≠ d → reflection ∉ cells.map Prod.fst →
      (∀ σ : PSubst, nameAction.Models σ C.equations →
        NameLaws (psubst σ (label reflection)) (psubst σ (atLoc (pReflect x p) rootLoc))) →
      ∃ order : List (O × Pattern), order.Perm cells ∧ label' reflection = label reflection ∧
        ∀ σ : PSubst, nameAction.Models σ C'.equations →
          List.Forall₂ NameLaws (rows.map (psubst σ)) ((order.map Prod.snd).map (psubst σ)) := by
  induction run with
  | refl label C d =>
      intro cells _ readsCells _ _ _ _ readsReflection
      cases cells with
      | nil => exact ⟨[], List.Perm.refl _, rfl, fun _ _ => List.Forall₂.nil⟩
      | cons q others =>
          have facts := readsCells q (List.mem_cons.mpr (.inl rfl))
          exact absurd closed (closeRoot_waits label C x p reflection d made₁ ρ readsReflection facts.1 facts.2.2)
  | @step label C d label' C' d' rows ρ' r d₁ a admitted readsRow rest ih =>
      intro cells nodupCells readsCells others inReflection reflectionD reflectionCells readsReflection
      obtain ⟨_, shapes, enabled, ⟨_, σ₀, solved₀⟩, _, _⟩ := (RuleSyntax.admits_iff _).mp admitted
      have rPresent : r ∈ C.present := enabled.taken_subset (by simp [coolAt, Selection.commit])
      have rd : r ≠ d := by
        intro same
        have nd := shapes.1
        simp [coolAt, same] at nd
      have d₁Fresh : d₁ ∉ C.present := fun inside =>
        Finset.disjoint_left.mp enabled.fresh (by simp [coolAt, Selection.commit]) inside
      have known₀ : nameAction.Models σ₀ C.equations := info_known _ solved₀
      have rCell : r ∈ cells.map Prod.fst := by
        by_contra notCell
        have row := readsRow σ₀ known₀
        rw [psubst_atLoc_any] at row
        exact others r rPresent rd notCell σ₀ known₀ _ row
      obtain ⟨q, qIn, qFst⟩ := List.mem_map.mp rCell
      obtain ⟨s, t, cellsEq⟩ := List.append_of_mem qIn
      have permCells : cells.Perm (q :: (s ++ t)) := by
        rw [cellsEq]
        exact List.perm_middle
      have nodupFront := (permCells.map Prod.fst).nodup_iff.mp nodupCells
      obtain ⟨qOut, nodupRest⟩ := List.nodup_cons.mp nodupFront
      have restIn : ∀ q' ∈ s ++ t, q' ∈ cells := fun q' inside => permCells.symm.subset (List.mem_cons.mpr (.inr inside))
      have restNotR : ∀ q' ∈ s ++ t, q'.1 ≠ r := by
        intro q' inside same
        apply qOut
        rw [qFst, ← same]
        exact List.mem_map.mpr ⟨q', inside, rfl⟩
      have reflectionR : reflection ≠ r := fun same => reflectionCells (same ▸ rCell)
      have reflectionD₁ : reflection ≠ d₁ := fun same => d₁Fresh (same ▸ inReflection)
      obtain ⟨order', perm', sameReflection, rel'⟩ := ih closed (s ++ t) nodupRest
        (fun q' inside => by
          obtain ⟨present', notD, reads'⟩ := readsCells q' (restIn q' inside)
          have notD₁ : q'.1 ≠ d₁ := fun same => d₁Fresh (same ▸ present')
          refine ⟨(coolAt_present label C ρ' d r d₁ q'.1).mpr (.inl ⟨present', notD, restNotR q' inside⟩), notD₁,
            fun σ solved => ?_⟩
          rw [coolAt_label_old label C ρ' d r d₁ notD₁]
          exact reads' σ (coolAt_back label C ρ' d r d₁ solved))
        (fun o inside notD₁ notRest σ solved y same => by
          rcases (coolAt_present label C ρ' d r d₁ o).mp inside with ⟨inC, notD, notR⟩ | isD₁
          · rw [coolAt_label_old label C ρ' d r d₁ notD₁] at same
            refine others o inC notD ?_ σ (coolAt_back label C ρ' d r d₁ solved) y same
            intro inCells
            obtain ⟨q', inQ, same'⟩ := List.mem_map.mp inCells
            rcases List.mem_cons.mp (permCells.subset inQ) with isQ | inRest
            · exact notR (by rw [← same', isQ, qFst])
            · exact notRest (List.mem_map.mpr ⟨q', inRest, same'⟩)
          · exact notD₁ isD₁)
        ((coolAt_present label C ρ' d r d₁ reflection).mpr (.inl ⟨inReflection, reflectionD, reflectionR⟩))
        reflectionD₁
        (fun inside => by
          obtain ⟨q', inQ, same'⟩ := List.mem_map.mp inside
          exact reflectionCells (List.mem_map.mpr ⟨q', restIn q' inQ, same'⟩))
        (fun σ solved => by
          rw [coolAt_label_old label C ρ' d r d₁ reflectionD₁]
          exact readsReflection σ (coolAt_back label C ρ' d r d₁ solved))
      refine ⟨q :: order', (List.Perm.cons q perm').trans permCells.symm,
        sameReflection.trans (coolAt_label_old label C ρ' d r d₁ reflectionD₁), fun σ solved => ?_⟩
      refine List.Forall₂.cons ?_ (rel' σ solved)
      have known : nameAction.Models σ C.equations := coolAt_back label C ρ' d r d₁ (coolRun_back rest σ solved)
      have one := readsRow σ known
      have two := (readsCells q qIn).2.2 σ known
      rw [qFst] at two
      have both := one.symm.trans two
      simp only [psubst_atLoc_any] at both
      exact ((locatedFrame_name.atLoc_iff _ _ _ _).mp both).1

/-- **Reflection of packing and the close**: from the child's committed state (token `Done(l, Root, 0)`, rows the
cells, no other row at the child), every run of coolings followed by an admitted close of the reflection makes a
row that reads, at every solution, as `for(@(pPar (cells' readings)) <- x) 0 @ Root`. -/
theorem refl_close_reads [DecidableEq O] (x p : Pattern) (reflection made₁ : O) (ρ : PSubst)
    {label : O → Pattern} {C : Configuration Pattern O} {d : O} {label' : O → Pattern}
    {C' : Configuration Pattern O} {d' : O} {rows : List Pattern}
    (run : CoolRun (childLoc rootLoc x p) rootLoc label C d label' C' d' rows)
    (closed : (RuleSyntax.step QN O QNE located).Admits (s := embed label' C') (closeRootAt ρ reflection d' made₁))
    (cells : List (O × Pattern)) (nodupCells : (cells.map Prod.fst).Nodup)
    (readsCells : ∀ q ∈ cells, q.1 ∈ C.present ∧ q.1 ≠ d ∧ ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label q.1)) (psubst σ (atLoc q.2 (childLoc rootLoc x p))))
    (others : ∀ o ∈ C.present, o ≠ d → o ∉ cells.map Prod.fst → ∀ σ : PSubst, nameAction.Models σ C.equations →
      ∀ y : Pattern, ¬ NameLaws (psubst σ (label o)) (atLoc y (psubst σ (childLoc rootLoc x p))))
    (inReflection : reflection ∈ C.present) (reflectionD : reflection ≠ d)
    (reflectionCells : reflection ∉ cells.map Prod.fst)
    (readsReflection : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label reflection)) (psubst σ (atLoc (pReflect x p) rootLoc)))
    (readsToken : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label d)) (psubst σ (doneTok (childLoc rootLoc x p) rootLoc pZero))) :
    ∀ σ : PSubst, nameAction.Models σ (res label' C' (closeRootAt ρ reflection d' made₁)).knowledge →
      NameLaws (psubst σ ((res label' C' (closeRootAt ρ reflection d' made₁)).label made₁))
        (psubst σ (atLoc (pFor (tProc (pPar (cells.map Prod.snd))) x pZero) rootLoc)) := by
  obtain ⟨order, perm, sameReflection, rel⟩ := refl_close_sound x p reflection made₁ ρ run closed cells nodupCells
    readsCells others inReflection reflectionD reflectionCells readsReflection
  have readsReflection' : ∀ σ : PSubst, nameAction.Models σ C'.equations →
      NameLaws (psubst σ (label' reflection)) (psubst σ (atLoc (pReflect x p) rootLoc)) := by
    intro σ solved
    rw [sameReflection]
    exact readsReflection σ (coolRun_back run σ solved)
  intro σ solved
  obtain ⟨known', reads⟩ := closeRoot_reads label' C' x p (cooled pZero rows) reflection d' made₁ ρ readsReflection'
    (coolRun_reads run pZero readsToken) solved
  have bag : BagLaws (psubst σ (cooled pZero rows)) (psubst σ (pPar (cells.map Prod.snd))) := by
    have packed := ReflQuotient.bagLaws_psubst σ (bagLaws_cooled_zero rows)
    rw [psubst_pPar] at packed
    refine packed.trans ?_
    rw [psubst_pPar]
    exact (bagLaws_of_nameLaws (nameLaws_collection _ _ (rel σ known'))).trans
      (BagLaws.of_axiom (.perm ((perm.map Prod.snd).map (psubst σ))))
  refine reads.trans ?_
  simp only [psubst_atLoc_any, psubst_pFor, psubst_tProc, psubst_pZero, psubst_rootLoc]
  exact (locatedFrame_name.atLoc_iff _ _ _ _).mpr
    ⟨nameLaws_pFor_iff.mpr ⟨nameLaws_tProc bag, ReflNames.NameLaws.refl _, ReflNames.NameLaws.refl _⟩,
      ReflNames.NameLaws.refl _⟩

#print axioms close_reflection_reading
#print axioms closeRoot_waits
#print axioms coolRun_back
#print axioms refl_close_sound
#print axioms refl_close_reads

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflCorrespondence
