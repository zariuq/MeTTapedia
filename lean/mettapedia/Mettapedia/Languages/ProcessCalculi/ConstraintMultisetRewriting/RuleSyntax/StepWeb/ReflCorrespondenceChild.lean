import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflCorrespondenceHeat

/-!
# The REFL correspondence at the name frame: reflection of the whole child segment

From the opened child (its token `Pending(l, Root)`, one cell holding the reflected process `P`): for EVERY heating
run at the child, the rows at the child are cells whose parts make the bag of `P` modulo the bag laws
(`heatRun_reflects`), the reflection keeps its row (`heatRun_keeps`); and then for EVERY commit on two of those
cells that are inputs, EVERY cooling run and EVERY close, the commit is the source's COMM on the cells' parts and the
made row reads as the listener of the represented reduct (`refl_reflects`). `child_reflects` states the two
together.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflCorrespondence

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.OSLF.MeTTaIL.Match (Bindings)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus (pFor par pZero pPar tProc pReflect applyDot)
open MeTTaOperationsComm (psubst PSubst pvars GroundPrincipal firstOrder)
open MeTTaCalculus.Corrected (Apart)
open FiniteProgram (predot)
open OneFrame (embed)
open ReflQuotient (BagLaws bagCanon groundBags)
open ReflNames (NameLaws nameAction QN QNE nameCanon)
open ReflLocated (atLoc rootLoc childLoc pendingTok located heatChildN locatedFrame_name psubst_rootLoc
  psubst_atLoc_any heatChild_takes_pair)
open ReflPacking (CoolRun)
open ReflLocatedStep (info_known solution_of_admitted res resConf commChildAt psubst_childLoc)

variable {O : Type*}

/-- Every solution after a heating run solves the knowledge before it. -/
theorem heatRun_back [DecidableEq O] {tk : O} {label label' : O → Pattern} {C C' : Configuration Pattern O}
    (run : HeatRun tk label C label' C') :
    ∀ σ : PSubst, nameAction.Models σ C'.equations → nameAction.Models σ C.equations := by
  induction run with
  | refl => exact fun σ solved => solved
  | step ρ o m₁ m₂ admitted rest ih => exact fun σ solved => heat_back _ _ ρ o _ m₁ m₂ (ih σ solved)

/-- **A heating run at the child keeps every row that does not read at the child**, with its label. -/
theorem heatRun_keeps [DecidableEq O] {l m : Pattern} {tk : O} {label label' : O → Pattern}
    {C C' : Configuration Pattern O} (run : HeatRun tk label C label' C') :
    ∀ {cells : List (O × Pattern)}, Cells l m label C tk cells →
      ∀ o ∈ C.present, o ≠ tk → o ∉ cells.map Prod.fst → o ∈ C'.present ∧ label' o = label o := by
  induction run with
  | refl label C => exact fun _ o inside _ _ => ⟨inside, rfl⟩
  | @step label C label' C' ρ o' m₁ m₂ admitted rest ih =>
      intro cells inv o inside notTk notCell
      obtain ⟨_, _, enabled, ⟨_, w, solved⟩, _, _⟩ := (RuleSyntax.admits_iff _).mp admitted
      have freshM₁ : m₁ ∉ C.present := fun inC => Finset.disjoint_left.mp enabled.fresh
        (by simp [heatChildN, Selection.commit]) inC
      have freshM₂ : m₂ ∉ C.present := fun inC => Finset.disjoint_left.mp enabled.fresh
        (by simp [heatChildN, Selection.commit]) inC
      have ne₁ : o ≠ m₁ := fun same => freshM₁ (same ▸ inside)
      have ne₂ : o ≠ m₂ := fun same => freshM₂ (same ▸ inside)
      -- the heated row reads at the child, so `o` is not it
      have notTaken : o ≠ o' := by
        intro same
        rw [← same] at solved
        obtain ⟨a, b, l', reads, -, -, loc, tokenRead⟩ := heatChild_takes_pair label C ρ o tk m₁ m₂ solved
        have known : nameAction.Models w C.equations := info_known _ solved
        have atL : NameLaws l' (psubst w l) := by
          have tk₁ := tokenRead.trans (inv.token.2 w known)
          rw [ReflLocated.psubst_pendingTok] at tk₁
          exact loc.symm.trans (ReflLocatedStep.nameLaws_pendingTok_iff.mp tk₁).1
        refine inv.others o inside notTk notCell w known (par a b) ?_
        rw [reads]
        exact (locatedFrame_name.atLoc_iff _ _ _ _).mpr ⟨ReflNames.NameLaws.refl _, atL⟩
      obtain ⟨cells₁, inv₁, -⟩ := heat_cell inv ρ o' m₁ m₂ admitted
      have in₁ := (heat_present label C ρ o' tk m₁ m₂ o).mpr (.inl ⟨inside, notTaken⟩)
      have label₁ := heat_label_old label C ρ o' tk m₁ m₂ ne₁ ne₂
      have notCell₁ : o ∉ cells₁.map Prod.fst := by
        intro inCells
        obtain ⟨q, inQ, same⟩ := List.mem_map.mp inCells
        have row := (inv₁.rows q inQ).2.2
        have known₁ := (solution_of_admitted admitted)
        obtain ⟨σ₁, solved₁⟩ := known₁
        have read := row σ₁ solved₁
        rw [same, label₁] at read
        rw [psubst_atLoc_any] at read
        exact inv.others o inside notTk notCell σ₁ (info_known _ solved₁) _ read
      obtain ⟨in', label'Eq⟩ := ih inv₁ o in₁ notTk notCell₁
      exact ⟨in', label'Eq.trans label₁⟩

/-- **The opening makes the child's first cell**: after an admitted opening of a reflection `x?(predot P) @ Root`
at a clean child, the child holds its token and one cell, `P`. -/
theorem opened_cells [DecidableEq O] (label : O → Pattern) (C : Configuration Pattern O) (x P : Pattern)
    (reflection pr tk : O) (ρ : PSubst)
    (readsReflection : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label reflection)) (psubst σ (atLoc (pReflect x (predot P)) rootLoc)))
    (clean : Clean (childLoc rootLoc x (predot P)) label C) (heatable : Heatable P)
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) (openRootAt ρ reflection pr tk)) :
    Cells (childLoc rootLoc x (predot P)) rootLoc (res label C (openRootAt ρ reflection pr tk)).label
      (resConf label C (openRootAt ρ reflection pr tk)) tk [(pr, P)] := by
  obtain ⟨_, shapes, enabled, _, _, _⟩ := (RuleSyntax.admits_iff _).mp admitted
  have prTk : pr ≠ tk := by
    have nd := shapes.2.1
    simpa [openRootAt] using nd
  have freshPr : pr ∉ C.present := fun inside =>
    Finset.disjoint_left.mp enabled.fresh (by simp [openRootAt, Selection.commit]) inside
  refine ⟨⟨(open_present label C ρ reflection pr tk tk).mpr (.inr (.inr rfl)), fun σ solved =>
    (openRoot_reads label C x (predot P) reflection pr tk ρ readsReflection prTk solved).2.2⟩,
    List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_, ?_, ?_⟩
  · intro q member
    rw [List.mem_singleton] at member
    subst member
    exact ⟨(open_present label C ρ reflection pr tk pr).mpr (.inr (.inl rfl)), prTk, fun σ solved =>
      (openRoot_reads label C x (predot P) reflection pr tk ρ readsReflection prTk solved).2.1⟩
  · intro o inside notTk notCell σ solved y same
    rcases (open_present label C ρ reflection pr tk o).mp inside with inC | isPr | isTk
    · have nePr : o ≠ pr := fun e => freshPr (e ▸ inC)
      rw [open_label_old label C ρ reflection pr tk nePr notTk] at same
      exact (clean o inC σ (open_back label C ρ reflection pr tk solved)).2.2 y same
    · exact notCell (by rw [isPr]; simp)
    · exact notTk isTk
  · intro q member
    rw [List.mem_singleton] at member
    subst member
    exact heatable

/-- **Reflection of the whole child segment.** From the opened child (one cell holding `P`): after EVERY heating
run at the child the cells' parts make the bag of `P` modulo the bag laws and the reflection keeps its row; and
then EVERY commit on two input cells, EVERY cooling run and EVERY close quote the represented one-step COMM reduct of
the cells, the commit being the source's COMM on the cells' parts. -/
theorem child_reflects [DecidableEq O] (label : O → Pattern) (C : Configuration Pattern O) (x P : Pattern)
    (reflection tk pr : O)
    (opened : Cells (childLoc rootLoc x (predot P)) rootLoc label C tk [(pr, P)])
    (inReflection : reflection ∈ C.present) (reflectionTk : reflection ≠ tk) (reflectionPr : reflection ≠ pr)
    (readsReflection : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label reflection)) (psubst σ (atLoc (pReflect x (predot P)) rootLoc)))
    {label₂ : O → Pattern} {C₂ : Configuration Pattern O} (heating : HeatRun tk label C label₂ C₂) :
    ∃ cells : List (O × Pattern),
      Cells (childLoc rootLoc x (predot P)) rootLoc label₂ C₂ tk cells ∧
      BagLaws (pPar (cells.map Prod.snd)) (pPar [P]) ∧
      ∀ (pre mid post : List (O × Pattern)) (first second made₁ made₂ madeTok listener : O)
        (t u ch ch' A B : Pattern),
        cells = pre ++ (first, pFor t ch A) :: (mid ++ (second, pFor u ch' B) :: post) →
        pvars ch = [] → pvars ch' = [] → nameCanon ch = ch → nameCanon ch' = ch' →
        ((∃ σ : PSubst, psubst σ t = psubst σ u) →
          ∃ bs : Bindings, GroundPrincipal t u bs ∧ ∀ y v, bs.lookup y = some v → firstOrder v = true) →
        Apart t A u B → firstOrder A = true → firstOrder B = true →
        groundBags t = true → groundBags u = true → bagCanon t = t → bagCanon u = u →
        ∀ (ρ : PSubst), (RuleSyntax.step QN O QNE located).Admits (s := embed label₂ C₂)
            (commChildAt ρ first second tk made₁ made₂ madeTok) →
          ∀ {label₄ : O → Pattern} {C₄ : Configuration Pattern O} {d' : O} {rows : List Pattern},
            CoolRun (childLoc rootLoc x (predot P)) rootLoc
              (res label₂ C₂ (commChildAt ρ first second tk made₁ made₂ madeTok)).label
              (resConf label₂ C₂ (commChildAt ρ first second tk made₁ made₂ madeTok)) madeTok label₄ C₄ d' rows →
          ∀ ρ₅ : PSubst, (RuleSyntax.step QN O QNE located).Admits (s := embed label₄ C₄)
              (closeRootAt ρ₅ reflection d' listener) →
            ch = ch' ∧ ∃ bs : Bindings,
              FiniteProgram.BagComm (pFor t ch A ::ₘ pFor u ch B ::ₘ ((pre ++ mid ++ post).map Prod.snd : Multiset Pattern))
                ((FiniteProgram.parts (applyDot bs A) : Multiset Pattern) +
                  (FiniteProgram.parts (applyDot bs B) : Multiset Pattern) +
                    ((pre ++ mid ++ post).map Prod.snd : Multiset Pattern)) ∧
              ∀ σ : PSubst, nameAction.Models σ (res label₄ C₄ (closeRootAt ρ₅ reflection d' listener)).knowledge →
                NameLaws (psubst σ ((res label₄ C₄ (closeRootAt ρ₅ reflection d' listener)).label listener))
                  (psubst σ (atLoc (pFor (tProc (pPar ((pre ++ mid ++ post).map (fun q => predot q.2) ++
                    [predot (applyDot bs A), predot (applyDot bs B)]))) x pZero) rootLoc)) := by
  obtain ⟨cells, inv, bag⟩ := heatRun_reflects heating opened
  have reflectionNotCell : reflection ∉ [(pr, P)].map Prod.fst := by simpa using reflectionPr
  obtain ⟨in₂, label₂Eq⟩ := heatRun_keeps heating opened reflection inReflection reflectionTk reflectionNotCell
  refine ⟨cells, inv, bag, ?_⟩
  intro pre mid post first second made₁ made₂ madeTok listener t u ch ch' A B shape groundCh groundCh' canonicalCh
    canonicalCh' unifiable convention foA foB groundT groundU canonicalT canonicalU ρ committed _ _ _ _ run ρ₅ closed
  subst shape
  have backTo : ∀ σ : PSubst, nameAction.Models σ C₂.equations → nameAction.Models σ C.equations := by
    intro σ solved
    exact heatRun_back heating σ solved
  exact refl_reflects label₂ C₂ x (predot P) reflection tk first second made₁ made₂ madeTok listener pre mid post
    t u ch ch' A B inv.nodup (fun q member => inv.rows q member)
    (fun o inside notTk notCell σ solved y same => inv.others o inside notTk notCell σ solved y same)
    inv.token.2 in₂ reflectionTk
    (fun inCells => by
      obtain ⟨q, inQ, same⟩ := List.mem_map.mp inCells
      obtain ⟨σ, solved⟩ := solution_of_admitted committed
      have known := info_known _ solved
      have row := (inv.rows q inQ).2.2 σ known
      rw [same, label₂Eq] at row
      have reflects := readsReflection σ (backTo σ known)
      have both := row.symm.trans reflects
      simp only [psubst_atLoc_any, psubst_rootLoc, psubst_childLoc] at both
      exact absurd (ReflNames.nameLaws_heads ((locatedFrame_name.atLoc_iff _ _ _ _).mp both).2) (by decide))
    (fun σ solved => by
      rw [label₂Eq]
      exact readsReflection σ (backTo σ solved))
    groundCh groundCh' canonicalCh canonicalCh' unifiable convention foA foB groundT groundU canonicalT canonicalU
    ρ committed run ρ₅ closed

#print axioms heatRun_back
#print axioms heatRun_keeps
#print axioms opened_cells
#print axioms child_reflects

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflCorrespondence
