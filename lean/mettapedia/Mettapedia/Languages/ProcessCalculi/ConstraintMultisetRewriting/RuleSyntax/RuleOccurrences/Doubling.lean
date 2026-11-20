import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Counting
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.OwnUnknowns
import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# Where a firing has free data, comparing firings does not count derivations

Over first-order atoms at one frame, with the link from `1` to `2` as the one rule and no ambient
program. A firing of the link is admitted whatever its opening is, with the same result
(`reopen`, `reopen_result`): the link has no unknowns, and the opening is free. There are infinitely
many openings, so the admitted firings of the link at a state are in bijection with two copies of
themselves, by a bijection that keeps the rule, the selection and the result (`doubleFirings`).

* **`realizesTwice`**: the candidate at the states that hold the link at **two** identities realizes
  the present step of the link, firing for firing, in the sense of
  `Interface.EventMultiplicity.Realization`, although every firing of the program has two firings
  over it (`exactly_two`).
* **`one_two_bisimilar`**: so the state that holds the link once and the state that holds it twice
  are bisimilar with multiplicities, observed by rule and selection.

Compare `Closed.one_not_two`: over terms without unknowns, where a firing is determined by its rule
and its selection, the same two states are not bisimilar. So the comparison of choices counts
derivations exactly where a firing carries no data that its result does not depend on.

* **`fibres_one_two`**: the count over one firing of the program still tells the two states apart
  here: one firing where the link is held once, two where it is held twice.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Doubling

open Interface (Frames)
open Interface.EventMultiplicity (Realization Bisimilar)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)
open Mettapedia.Logic.LP
open Examples (Tm X E c)
open Derived (link)
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Controls
  (atoms action)

/-! ## Infinitely many openings -/

/-- An infinite type is in bijection with two copies of itself. -/
theorem doubled (α : Type) [Infinite α] : Nonempty (α ≃ α × Bool) := by
  apply Cardinal.eq.mp
  rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id, Cardinal.mk_bool]
  exact (Cardinal.mul_eq_left (Cardinal.aleph0_le_mk α)
    (Cardinal.two_le_iff.mpr (exists_pair_ne α)) two_ne_zero).symm

/-- There are infinitely many openings. -/
instance openings_infinite : Infinite (Subst atoms) :=
  Infinite.of_injective (fun (n : ℕ) (_ : ℕ) => (Term.const n : Term atoms))
    (fun _ _ same => Term.const.inj (congrFun same 0))

/-! ## The link, held once and held twice -/

/-- The link from `1` to `2`. -/
abbrev theLink : Rule Tm := link (c 1) (c 2)

/-- The program of the link. -/
abbrev linkProgram : Program Tm := {theLink}

/-- Every identity holds the link. -/
abbrev code : ℕ → Rule Tm := fun _ => theLink

/-- One zone. -/
abbrev zone : ℕ → Unit := fun _ => ()

/-- The state that holds the link at the two identities `0` and `1`. -/
abbrev twice (s : State Tm ℕ) : RState Tm ℕ ℕ (Rule Tm) Unit := holding s {0, 1} code zone

/-- The identities of a non-empty set hold exactly the link. -/
theorem offers_link (rules : Finset ℕ) {ρ : ℕ} (inside : ρ ∈ rules) : Offers linkProgram rules code := by
  intro r
  constructor
  · intro member
    exact ⟨ρ, inside, (Set.mem_singleton_iff.mp member).symm⟩
  · rintro ⟨_, _, same⟩
    exact Set.mem_singleton_iff.mpr same.symm

/-- The admitted firings of the program of the link. -/
abbrev G (s : State Tm ℕ) : Type :=
  {g : Firing ℕ E ((∅ : Program Tm) ∪ linkProgram) s.frame // g.Admits X s}

/-- The admitted firings at the state that holds the link twice. -/
abbrev C₂ (s : State Tm ℕ) : Type :=
  {f : RFiring ℕ ℕ E (ofRules Unit) (twice s) // f.Admits X (∅ : Program Tm)}

theorem rule_eq {s : State Tm ℕ} (g : Firing ℕ E ((∅ : Program Tm) ∪ linkProgram) s.frame) :
    g.rule = theLink := by
  rcases g.member with inside | inside
  · exact absurd inside (Set.notMem_empty _)
  · exact inside

/-- Every two openings act alike on the terms of the link. -/
theorem alike (r : Rule Tm) (isLink : r = theLink) (v v' : Subst atoms) :
    ∀ t ∈ r.terms, action.apply v t = action.apply v' t := by
  subst isLink
  intro t inside
  have terms : t ∈ [c 1, c 2] := inside
  rcases List.mem_cons.mp terms with isTaken | rest
  · rw [isTaken]
    rfl
  · rw [List.mem_singleton.mp rest]
    rfl

/-- **The same firing with another opening** is admitted too. -/
def reopen {s : State Tm ℕ} (g : G s) (opening : Subst atoms) : G s :=
  ⟨⟨g.1.rule, g.1.member, g.1.ext, opening, g.1.selection, g.1.seen⟩,
    ((opening_congr X g.1.rule g.1.member g.1.member s g.1.ext g.1.opening opening
      (alike g.1.rule (rule_eq g.1) g.1.opening opening) g.1.selection g.1.seen).1).mp g.2⟩

/-- **It reaches the same state.** -/
theorem reopen_result {s : State Tm ℕ} (g : G s) (opening : Subst atoms) :
    (reopen g opening).1.result X s = g.1.result X s :=
  ((opening_congr X g.1.rule g.1.member g.1.member s g.1.ext g.1.opening opening
    (alike g.1.rule (rule_eq g.1) g.1.opening opening) g.1.selection g.1.seen).2).symm

/-- **The firings of the link are in bijection with two copies of themselves**, by a bijection that
keeps the rule, the extension, the selection and the collected rows, and changes only the opening. -/
noncomputable def doubleFirings (β : Subst atoms ≃ Subst atoms × Bool) (s : State Tm ℕ) :
    G s ≃ G s × Bool where
  toFun g := (reopen g (β g.1.opening).1, (β g.1.opening).2)
  invFun p := reopen p.1 (β.symm (p.1.1.opening, p.2))
  left_inv g := by
    show reopen (reopen g (β g.1.opening).1) (β.symm ((β g.1.opening).1, (β g.1.opening).2)) = g
    rw [Prod.mk.eta, Equiv.symm_apply_apply]
    rfl
  right_inv p := by
    obtain ⟨g, b⟩ := p
    show (reopen (reopen g (β.symm (g.1.opening, b))) (β (β.symm (g.1.opening, b))).1,
      (β (β.symm (g.1.opening, b))).2) = (g, b)
    rw [Equiv.apply_symm_apply]
    rfl

/-! ## The two firings over a firing of the program, told apart by one bit -/

/-- Whether a use is the occurrence at identity `1`. -/
def second : Use (Rule Tm) ℕ → Bool
  | .held ρ => decide (ρ = 1)
  | .ambient _ => false

/-- At the state that holds the link twice, an admitted firing uses identity `0` or identity `1`. -/
theorem use_of_second {s : State Tm ℕ} (f : C₂ s) :
    f.1.use = Use.held (if second f.1.use then 1 else 0) := by
  have admitted : f.1.Admits X (∅ : Program Tm) := f.2
  have available := admitted.1.2.2.available
  rcases used : f.1.use with r | ρ
  · rw [used] at available
    exact absurd available (Set.notMem_empty r)
  · rw [used] at available
    have inside : ρ ∈ ({0, 1} : Finset ℕ) := available
    rcases Finset.mem_insert.mp inside with isZero | isOne
    · subst isZero
      rfl
    · have one : ρ = 1 := Finset.mem_singleton.mp isOne
      subst one
      rfl

/-- A firing at the state that holds the link twice, as its firing of the program and the bit that
says which occurrence it uses. -/
def down (s : State Tm ℕ) (f : C₂ s) : G s × Bool :=
  (project X (offers_link {0, 1} (Finset.mem_insert_self 0 {1})) zone s f, second f.1.use)

theorem down_bijective (s : State Tm ℕ) : Function.Bijective (down s) := by
  constructor
  · intro f f' same
    have projections := congrArg Prod.fst same
    have bits : second f.1.use = second f'.1.use := congrArg Prod.snd same
    refine fibre_use_injective X (offers_link {0, 1} (Finset.mem_insert_self 0 {1})) zone projections ?_
    rw [use_of_second f, use_of_second f', bits]
  · rintro ⟨g, b⟩
    have held : (if b then 1 else 0) ∈ ({0, 1} : Finset ℕ) := by
      cases b <;> decide
    obtain ⟨f, lands, use⟩ :=
      fibre_use_surjective X (offers_link {0, 1} (Finset.mem_insert_self 0 {1})) zone g
        (u := .held (if b then 1 else 0)) held (rule_eq g.1).symm
    refine ⟨f, Prod.ext lands ?_⟩
    show second f.1.use = b
    rw [use]
    cases b <;> rfl

/-! ## The realization -/

/-- **Held twice, the link still realizes its present step firing for firing**: with a bijection
between the openings and two copies of them, each admitted firing of the program corresponds to one
admitted firing at the state that holds the link twice, with the same rule and selection and the
corresponding result. -/
noncomputable def realizesTwice (β : Subst atoms ≃ Subst atoms × Bool) :
    Realization
      ((step X ℕ E ((∅ : Program Tm) ∪ linkProgram)).toStep.eventSystem
        (Action := Rule Tm × Selection ℕ) (fun {_} g => (g.rule, g.selection)))
      (byRule ℕ Unit X E (∅ : Program Tm)) where
  state s := twice s
  choices s := (doubleFirings β s).trans (Equiv.ofBijective (down s) (down_bijective s)).symm
  actions s g := by
    have back : down s ((Equiv.ofBijective (down s) (down_bijective s)).symm (doubleFirings β s g)) =
        doubleFirings β s g :=
      Equiv.ofBijective_apply_symm_apply (down s) (down_bijective s) _
    exact (congrArg (fun p : G s × Bool => (p.1.1.rule, p.1.1.selection)) back).symm
  successors s g := by
    have back : down s ((Equiv.ofBijective (down s) (down_bijective s)).symm (doubleFirings β s g)) =
        doubleFirings β s g :=
      Equiv.ofBijective_apply_symm_apply (down s) (down_bijective s) _
    show twice (g.1.result X s) =
      ((Equiv.ofBijective (down s) (down_bijective s)).symm (doubleFirings β s g)).1.result X
    generalize (Equiv.ofBijective (down s) (down_bijective s)).symm (doubleFirings β s g) = f at back ⊢
    have offers := offers_link {0, 1} (Finset.mem_insert_self 0 {1})
    have member := member_of_admits X offers zone f.2
    have shapes := (admits_toProgram_iff X f.1 member (∅ : Program Tm)).mp f.2
    have result := result_holding X f.1 member shapes.2.2.1 shapes.2.2.2.2.1
    have projected : toProgram f.1 member = (reopen g (β g.1.opening).1).1 :=
      congrArg (fun p : G s × Bool => p.1.1) back
    show twice (g.1.result X s) = f.1.result X
    rw [result, projected]
    exact congrArg (fun t : State Tm ℕ => holding t ({0, 1} : Finset ℕ) code zone)
      (reopen_result (s := s) g (β g.1.opening).1).symm

/-- **Held once and held twice are bisimilar with multiplicities** over first-order atoms, observed
by rule and selection. -/
theorem one_two_bisimilar (s : State Tm ℕ) :
    Bisimilar (byRule ℕ Unit X E (∅ : Program Tm)) (holding s {0} code zone)
      (byRule ℕ Unit X E (∅ : Program Tm)) (twice s) := by
  obtain ⟨β⟩ := doubled (Subst atoms)
  have once : Once (∅ : Program Tm) ({0} : Finset ℕ) code :=
    ⟨fun ρ _ inside => absurd inside (Set.notMem_empty _),
      fun ρ inside ρ' inside' _ =>
        (Finset.mem_singleton.mp inside).trans (Finset.mem_singleton.mp inside').symm⟩
  exact (bisimilar_program ℕ X E (offers_link {0} (Finset.mem_singleton_self 0)) once zone s).symm.trans
    ((realizesTwice β).bisimilar s)

/-- **Over each firing of the program the two states are told apart**: one firing where the link is
held once, two where it is held twice. The count over a firing of the program does not see the free
opening, which that firing fixes. -/
theorem fibres_one_two (s : State Tm ℕ)
    (g : {g : Firing ℕ E ((∅ : Program Tm) ∪ linkProgram) s.frame // g.Admits X s}) :
    Nat.card {f // project X (offers_link {0} (Finset.mem_singleton_self 0)) zone s f = g} = 1 ∧
      Nat.card {f // project X (offers_link {0, 1} (Finset.mem_insert_self 0 {1})) zone s f = g} =
        2 := by
  have isLink : g.1.rule = theLink := rule_eq g.1
  have once : Once (∅ : Program Tm) ({0} : Finset ℕ) code :=
    ⟨fun ρ _ inside => absurd inside (Set.notMem_empty _),
      fun ρ inside ρ' inside' _ =>
        (Finset.mem_singleton.mp inside).trans (Finset.mem_singleton.mp inside').symm⟩
  exact ⟨fibre_card_one X _ once zone g,
    fibre_card_two X _ zone g (ρ := 0) (ρ' := 1) (by decide) (by decide) (by decide) isLink.symm
      isLink.symm
      (fun other inside _ => (Finset.mem_insert.mp inside).imp id Finset.mem_singleton.mp)⟩

#print axioms fibres_one_two
#print axioms doubled
#print axioms reopen_result
#print axioms doubleFirings
#print axioms use_of_second
#print axioms down_bijective
#print axioms realizesTwice
#print axioms one_two_bisimilar

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Doubling
