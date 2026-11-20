import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflCorrespondence

/-!
# The REFL correspondence at the name frame: from the commit to the close, and the two interfaces

After a child location `l = Child(Root, x, p)` has taken its one step, its rows are cooled into the token's
accumulator and the reflection is closed. Here, at the name frame `QN`:

* `cooling_live` (**cooling liveness**): from a token that reads as `Done(l, m, c)`, the rows that read as
  `a₁ @ l`, ..., `aₖ @ l` are cooled in EVERY order, given fresh made identities; afterwards none of them is
  present, the token reads as `Done(l, m, cooled c [a₁, ..., aₖ])` in that order, and every other row keeps its
  presence and its label.
* `refl_commit_closes`: when every row at the child is among the cooled ones, the close at the root is then
  admitted and its made row reads as `for(@(cooled 0 as) <- x) 0 @ Root`; every other root row is kept.
* The two interfaces at the close:
  - named quotes (`quote_named`, `made_reads_named`): if the cooled rows are the represented components of `R`
    in any order, the made row reads as `for(@(predotU R) <- x) 0 @ Root`, the represented listener of the
    reduct as written;
  - closed quotes (`quote_closed_ground`, `made_reads_closed`): if moreover `R` has no variable, it reads as the
    corrected listener `for(@(canonicalBag R) <- x) 0 @ Root`. For a closed reduct with a variable it does not
    (`ReflCorrespondenceControls`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflCorrespondence

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus (pFor par pZero pPar nQuote tProc pReflect)
open MeTTaOperationsComm (psubst PSubst pvars psubst_of_pvars_nil)
open MeTTaCalculus.Corrected (components canonicalBag codeOrder codeOrder_perm)
open OneFrame (embed)
open ReflQuotient (BagLaws BagAxiom)
open ReflNames (NameLaws nameAction QN QNE nameLaws_pFor_iff nameLaws_tProc bagLaws_of_nameLaws nameLaws_heads
  nameLaws_psubst)
open ReflLocated (atLoc rootLoc childLoc doneTok located locatedFrame_name)
open ReflPacking (cooled psubst_doneTok coolAt cool_reads CoolRun bagLaws_cooled_zero)
open ReflLocatedStep (info_known solution_of_admitted result_present result_label_old res resConf)
open ReflUniform (predotU bagLaws_pack predotU_ground)

variable {O : Type*}

/-! ## Cooling liveness -/

theorem coolAt_present [DecidableEq O] (label : O → Pattern) (C : Configuration Pattern O) (ρ : PSubst)
    (d r d₁ o : O) :
    o ∈ (res label C (coolAt ρ d r d₁)).present ↔ (o ∈ C.present ∧ o ≠ d ∧ o ≠ r) ∨ o = d₁ := by
  rw [result_present]
  simp [coolAt]

theorem coolAt_label_old [DecidableEq O] (label : O → Pattern) (C : Configuration Pattern O) (ρ : PSubst)
    (d r d₁ : O) {o : O} (other : o ≠ d₁) : (res label C (coolAt ρ d r d₁)).label o = label o :=
  result_label_old _ (by simp [coolAt, other])

theorem coolAt_back [DecidableEq O] (label : O → Pattern) (C : Configuration Pattern O) (ρ : PSubst) (d r d₁ : O)
    {σ : PSubst} (solved : nameAction.Models σ (resConf label C (coolAt ρ d r d₁)).equations) :
    nameAction.Models σ C.equations :=
  info_known (label := label) (C := C) (coolAt ρ d r d₁) solved

/-- **Cooling liveness**: from a present token that reads as `Done(l, m, c)` and distinct present rows that read
as `aᵢ @ l`, at every solution of a solvable knowledge, for every order of the rows (`order`) and every supply of
distinct fresh identities, there is a run of coolings in that order. After it the token reads as
`Done(l, m, cooled c as)`, the cooled rows are gone, every other row keeps its presence and its label, every
solution solves the knowledge before, and the knowledge is solvable. -/
theorem cooling_live [DecidableEq O] (l m : Pattern) :
    ∀ (order : List (O × Pattern)) (supply : List O) (label : O → Pattern) (C : Configuration Pattern O) (d : O)
      (c : Pattern), supply.length = order.length → supply.Nodup → (∀ o ∈ supply, o ∉ C.present) →
      d ∈ C.present → (order.map Prod.fst).Nodup → (∀ q ∈ order, q.1 ∈ C.present ∧ q.1 ≠ d) →
      (∀ q ∈ order, ∀ σ : PSubst, nameAction.Models σ C.equations →
        NameLaws (psubst σ (label q.1)) (psubst σ (atLoc q.2 l))) →
      (∀ σ : PSubst, nameAction.Models σ C.equations →
        NameLaws (psubst σ (label d)) (psubst σ (doneTok l m c))) →
      (∃ σ₀ : PSubst, nameAction.Models σ₀ C.equations) →
      ∃ (label' : O → Pattern) (C' : Configuration Pattern O) (d' : O),
        CoolRun l m label C d label' C' d' (order.map Prod.snd) ∧ (d' = d ∨ d' ∈ supply) ∧ d' ∈ C'.present ∧
        (∀ σ : PSubst, nameAction.Models σ C'.equations →
          NameLaws (psubst σ (label' d')) (psubst σ (doneTok l m (cooled c (order.map Prod.snd))))) ∧
        (∀ σ : PSubst, nameAction.Models σ C'.equations → nameAction.Models σ C.equations) ∧
        (∃ σ₁ : PSubst, nameAction.Models σ₁ C'.equations) ∧
        (∀ o ∈ C'.present, o = d' ∨ (o ∈ C.present ∧ o ∉ order.map Prod.fst ∧ o ≠ d ∧ label' o = label o)) ∧
        (∀ o ∈ C.present, o ∉ order.map Prod.fst → o ≠ d → o ∈ C'.present ∧ label' o = label o) := by
  intro order
  induction order with
  | nil =>
      intro supply label C d c _ _ _ present _ _ _ readsToken solvable
      refine ⟨label, C, d, CoolRun.refl label C d, .inl rfl, present, readsToken, fun σ solved => solved, solvable,
        fun o presentO => ?_, fun o presentO _ _ => ⟨presentO, rfl⟩⟩
      by_cases same : o = d
      · exact .inl same
      · exact .inr ⟨presentO, List.not_mem_nil, same, rfl⟩
  | cons q rest ih =>
      intro supply label C d c lengths nodup freshSupply present nodupOrder rowsPresent readsRows readsToken
        solvable
      obtain ⟨r, a⟩ := q
      cases supply with
      | nil => exact absurd lengths (by simp)
      | cons d₁ supply' =>
        have rowFacts := rowsPresent (r, a) (List.mem_cons.mpr (.inl rfl))
        have readsRow := readsRows (r, a) (List.mem_cons.mpr (.inl rfl))
        have d₁Fresh := freshSupply d₁ (List.mem_cons.mpr (.inl rfl))
        have tail := List.nodup_cons.mp nodup
        have orderTail := List.nodup_cons.mp nodupOrder
        obtain ⟨σ₀, known⟩ := solvable
        obtain ⟨ρ, fresh⟩ := cool_fresh_exists label C d r d₁
        have admitted := cool_admitted label C l m c a d r d₁ readsToken readsRow (Ne.symm rowFacts.2) present
          rowFacts.1 d₁Fresh known fresh
        have d₁Present : d₁ ∈ (res label C (coolAt ρ d r d₁)).present :=
          (coolAt_present label C ρ d r d₁ d₁).mpr (.inr rfl)
        obtain ⟨σ₁, solved₁⟩ := solution_of_admitted admitted
        obtain ⟨label', C', d', run, origin, presentD', readsD', mono, solvable', fromC, keptC⟩ :=
          ih supply' (res label C (coolAt ρ d r d₁)).label (resConf label C (coolAt ρ d r d₁)) d₁ (par c a)
            (by simpa using lengths) tail.2
            (fun o member inside => by
              rcases (coolAt_present label C ρ d r d₁ o).mp inside with ⟨old, -⟩ | same
              · exact freshSupply o (List.mem_cons_of_mem _ member) old
              · exact tail.1 (same ▸ member))
            d₁Present orderTail.2
            (fun q member => by
              have facts := rowsPresent q (List.mem_cons_of_mem _ member)
              have notR : q.1 ≠ r := fun same => orderTail.1 (same ▸ List.mem_map.mpr ⟨q, member, rfl⟩)
              refine ⟨(coolAt_present label C ρ d r d₁ q.1).mpr (.inl ⟨facts.1, facts.2, notR⟩), ?_⟩
              intro same
              exact d₁Fresh (same ▸ facts.1))
            (fun q member σ solved => by
              have facts := rowsPresent q (List.mem_cons_of_mem _ member)
              have notMade : q.1 ≠ d₁ := fun same => d₁Fresh (same ▸ facts.1)
              rw [coolAt_label_old label C ρ d r d₁ notMade]
              exact readsRows q (List.mem_cons_of_mem _ member) σ (coolAt_back label C ρ d r d₁ solved))
            (fun σ solved => cool_reads label C ρ d r d₁ l m c a readsToken readsRow solved)
            ⟨σ₁, solved₁⟩
        refine ⟨label', C', d', CoolRun.step ρ r d₁ a admitted readsRow run, ?_, presentD', readsD',
          fun σ solved => coolAt_back label C ρ d r d₁ (mono σ solved), solvable', ?_, ?_⟩
        · rcases origin with same | inside
          · exact .inr (List.mem_cons.mpr (.inl same))
          · exact .inr (List.mem_cons_of_mem _ inside)
        · intro o presentO
          rcases fromC o presentO with same | ⟨inC₁, notRest, notD₁, sameLabel⟩
          · exact .inl same
          · rcases (coolAt_present label C ρ d r d₁ o).mp inC₁ with ⟨old, notD, notR⟩ | same
            · refine .inr ⟨old, ?_, notD, sameLabel.trans (coolAt_label_old label C ρ d r d₁ notD₁)⟩
              simp only [List.map_cons, List.mem_cons, not_or]
              exact ⟨notR, notRest⟩
            · exact absurd same notD₁
        · intro o presentO notOrder notD
          simp only [List.map_cons, List.mem_cons, not_or] at notOrder
          have notD₁ : o ≠ d₁ := fun same => d₁Fresh (same ▸ presentO)
          obtain ⟨inC', sameLabel⟩ := keptC o
            ((coolAt_present label C ρ d r d₁ o).mpr (.inl ⟨presentO, notD, notOrder.1⟩)) notOrder.2 notD₁
          exact ⟨inC', sameLabel.trans (coolAt_label_old label C ρ d r d₁ notD₁)⟩

/-! ## From the commit to the close -/

/-- **From the commit to the close.** In a state where the child `l = Child(Root, x, p)` has taken its step (its
token `d` reads as `Done(l, Root, 0)`), its rows `order` read as `aᵢ @ l` and no other row reads as a row at `l`,
and the reflection reads as `x?(p) @ Root`: for the order `order` and fresh identities `made₁ :: supply`, there
is a cooling run in that order and, at its end, an admitted close at the root. Every solution of the close's result
solves the knowledge before and reads the made row as `for(@(cooled 0 as) <- x) 0 @ Root`; every other present row
keeps its presence and its label. -/
theorem refl_commit_closes [DecidableEq O] (label : O → Pattern) (C : Configuration Pattern O) (x p : Pattern)
    (reflection d made₁ : O) (order : List (O × Pattern)) (supply : List O)
    (readsReflection : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label reflection)) (psubst σ (atLoc (pReflect x p) rootLoc)))
    (readsToken : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label d)) (psubst σ (doneTok (childLoc rootLoc x p) rootLoc pZero)))
    (readsRows : ∀ q ∈ order, ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label q.1)) (psubst σ (atLoc q.2 (childLoc rootLoc x p))))
    (onlyRows : ∀ o ∈ C.present, o ∉ order.map Prod.fst → ∀ σ : PSubst, nameAction.Models σ C.equations →
      ∀ y : Pattern, ¬ NameLaws (psubst σ (label o)) (atLoc y (psubst σ (childLoc rootLoc x p))))
    (lengths : supply.length = order.length) (nodup : (made₁ :: supply).Nodup)
    (freshSupply : ∀ o ∈ made₁ :: supply, o ∉ C.present)
    (presentToken : d ∈ C.present) (presentReflection : reflection ∈ C.present) (reflectionToken : reflection ≠ d)
    (reflectionNotRow : reflection ∉ order.map Prod.fst)
    (nodupOrder : (order.map Prod.fst).Nodup) (rowsPresent : ∀ q ∈ order, q.1 ∈ C.present ∧ q.1 ≠ d)
    (solvable : ∃ σ₀ : PSubst, nameAction.Models σ₀ C.equations) :
    ∃ (label' : O → Pattern) (C' : Configuration Pattern O) (d' : O) (ρ : PSubst),
      CoolRun (childLoc rootLoc x p) rootLoc label C d label' C' d' (order.map Prod.snd) ∧
      (RuleSyntax.step QN O QNE located).Admits (s := embed label' C') (closeRootAt ρ reflection d' made₁) ∧
      (∀ σ : PSubst, nameAction.Models σ (res label' C' (closeRootAt ρ reflection d' made₁)).knowledge →
        nameAction.Models σ C.equations ∧
        NameLaws (psubst σ ((res label' C' (closeRootAt ρ reflection d' made₁)).label made₁))
          (psubst σ (atLoc (pFor (tProc (cooled pZero (order.map Prod.snd))) x pZero) rootLoc))) ∧
      ∀ o ∈ C.present, o ∉ order.map Prod.fst → o ≠ d → o ≠ reflection →
        o ∈ (res label' C' (closeRootAt ρ reflection d' made₁)).present ∧
        (res label' C' (closeRootAt ρ reflection d' made₁)).label o = label o := by
  obtain ⟨supplyFresh, supplyNodup⟩ := List.nodup_cons.mp nodup
  obtain ⟨label', C', d', run, origin, presentD', readsD', mono, solvable', fromC, keptC⟩ :=
    cooling_live (childLoc rootLoc x p) rootLoc order supply label C d pZero lengths supplyNodup
      (fun o member => freshSupply o (List.mem_cons_of_mem _ member)) presentToken nodupOrder rowsPresent
      readsRows readsToken solvable
  obtain ⟨ρ, fresh⟩ := close_fresh_exists label' C' reflection d' made₁
  obtain ⟨inC', sameReflection⟩ := keptC reflection presentReflection reflectionNotRow reflectionToken
  have readsReflection' : ∀ σ : PSubst, nameAction.Models σ C'.equations →
      NameLaws (psubst σ (label' reflection)) (psubst σ (atLoc (pReflect x p) rootLoc)) := by
    intro σ solved
    rw [sameReflection]
    exact readsReflection σ (mono σ solved)
  have packed : ∀ o ∈ C'.present, ∀ σ : PSubst, nameAction.Models σ C'.equations → ∀ y : Pattern,
      ¬ NameLaws (psubst σ (label' o)) (atLoc y (psubst σ (childLoc rootLoc x p))) := by
    intro o presentO σ solved y same
    rcases fromC o presentO with isToken | ⟨inC, notOrder, -, sameLabel⟩
    · rw [isToken] at same
      have both := (readsD' σ solved).symm.trans same
      rw [psubst_doneTok] at both
      exact absurd (nameLaws_heads both) (by decide)
    · rw [sameLabel] at same
      exact onlyRows o inC notOrder σ (mono σ solved) y same
  have apart : reflection ≠ d' := by
    rcases origin with same | inSupply
    · rw [same]
      exact reflectionToken
    · intro same
      exact freshSupply d' (List.mem_cons_of_mem _ inSupply) (same ▸ presentReflection)
  have madeFresh : made₁ ∉ C'.present := by
    intro inside
    rcases fromC made₁ inside with same | ⟨inC, -⟩
    · rcases origin with same' | inSupply
      · exact freshSupply made₁ (List.mem_cons.mpr (.inl rfl)) (by rw [same, same']; exact presentToken)
      · exact supplyFresh (same ▸ inSupply)
    · exact freshSupply made₁ (List.mem_cons.mpr (.inl rfl)) inC
  obtain ⟨σ₁, known'⟩ := solvable'
  have admitted := closeRoot_admitted label' C' x p (cooled pZero (order.map Prod.snd)) reflection d' made₁
    readsReflection' readsD' packed apart ⟨inC', presentD'⟩ madeFresh known' fresh
  refine ⟨label', C', d', ρ, run, admitted, fun σ solved => ?_, ?_⟩
  · obtain ⟨known, reads⟩ := closeRoot_reads label' C' x p _ reflection d' made₁ ρ readsReflection' readsD' solved
    exact ⟨mono σ known, reads⟩
  · intro o presentO notOrder notD notReflection
    obtain ⟨inside, sameLabel⟩ := keptC o presentO notOrder notD
    have notD' : o ≠ d' := by
      rcases origin with same | inSupply
      · rw [same]
        exact notD
      · intro same
        exact freshSupply o (List.mem_cons_of_mem _ (same ▸ inSupply)) presentO
    have notMade : o ≠ made₁ := fun same => freshSupply made₁ (List.mem_cons.mpr (.inl rfl)) (same ▸ presentO)
    refine ⟨(result_present _ o).mpr (.inl ⟨inside, by simp [closeRootAt, notReflection, notD']⟩), ?_⟩
    rw [result_label_old (closeRootAt ρ reflection d' made₁) (by simp [closeRootAt, notMade])]
    exact sameLabel

/-! ## The two interfaces at the close -/

/-- **Named quotes**: cooled rows that are the represented components of `R`, in any order, quote the represented
reduct modulo the bag laws. -/
theorem quote_named {as : List Pattern} (R : Pattern) (perm : as.Perm ((components R).map predotU)) :
    BagLaws (cooled pZero as) (predotU R) :=
  (bagLaws_cooled_zero as).trans ((BagLaws.of_axiom (.perm perm)).trans (bagLaws_pack R (List.Perm.refl _)))

/-- **Closed quotes, ground reducts**: for a reduct without variables, the corrected quote (closed, sorted,
wrapped) and the represented reduct agree modulo the bag laws. -/
theorem quote_closed_ground (R : Pattern) (ground : pvars R = []) : BagLaws (canonicalBag R) (predotU R) := by
  have closed : MeTTaCalculus.Corrected.close R = R := MeTTaCalculus.Corrected.closeIn_of_pvars_nil R ground []
  have groundComponent : ∀ c ∈ codeOrder (components R), pvars c = [] := by
    intro c member
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro z inside
    have inR := MeTTaCalculus.Corrected.pvars_of_mem_components ((codeOrder_perm _).subset member) inside
    rw [ground] at inR
    exact List.not_mem_nil inR
  have fixed : (codeOrder (components R)).map predotU = codeOrder (components R) := by
    conv_rhs => rw [← List.map_id (codeOrder (components R))]
    exact List.map_congr_left fun c member => predotU_ground c (groundComponent c member)
  have pack := bagLaws_pack R (codeOrder_perm (components R))
  rw [fixed] at pack
  unfold canonicalBag
  rw [closed]
  exact pack

/-- **Named quotes at the close**: if the made row reads as `for(@(cooled 0 as) <- x) 0 @ Root` and the cooled
rows are the represented components of `R` in any order, it reads as `for(@(predotU R) <- x) 0 @ Root`. -/
theorem made_reads_named {σ : PSubst} {made x : Pattern} {as : List Pattern} (R : Pattern)
    (perm : as.Perm ((components R).map predotU))
    (reads : NameLaws made (psubst σ (atLoc (pFor (tProc (cooled pZero as)) x pZero) rootLoc))) :
    NameLaws made (psubst σ (atLoc (pFor (tProc (predotU R)) x pZero) rootLoc)) :=
  reads.trans (nameLaws_psubst σ ((locatedFrame_name.atLoc_iff _ _ _ _).mpr
    ⟨nameLaws_pFor_iff.mpr ⟨nameLaws_tProc (quote_named R perm), ReflNames.NameLaws.refl _,
      ReflNames.NameLaws.refl _⟩, ReflNames.NameLaws.refl _⟩))

/-- **Closed quotes at the close, ground reducts**: under the hypotheses of `made_reads_named`, with `R` without
variables, the made row reads as the corrected listener `listener x R = for(@(canonicalBag R) <- x) 0` at the
root. -/
theorem made_reads_closed {σ : PSubst} {made x : Pattern} {as : List Pattern} (R : Pattern) (ground : pvars R = [])
    (perm : as.Perm ((components R).map predotU))
    (reads : NameLaws made (psubst σ (atLoc (pFor (tProc (cooled pZero as)) x pZero) rootLoc))) :
    NameLaws made (psubst σ (atLoc (MeTTaCalculus.Corrected.listener x R) rootLoc)) :=
  reads.trans (nameLaws_psubst σ ((locatedFrame_name.atLoc_iff _ _ _ _).mpr
    ⟨nameLaws_pFor_iff.mpr ⟨nameLaws_tProc ((quote_named R perm).trans (quote_closed_ground R ground).symm),
      ReflNames.NameLaws.refl _, ReflNames.NameLaws.refl _⟩, ReflNames.NameLaws.refl _⟩))

#print axioms coolAt_present
#print axioms cooling_live
#print axioms refl_commit_closes
#print axioms quote_named
#print axioms quote_closed_ground
#print axioms made_reads_named
#print axioms made_reads_closed

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflCorrespondence
