import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Atoms
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Protection

/-!
# A derived rule: each of its firings is a run of two firings of the rules it is derived from

At one frame, over any substitution action, with the identity extension. A **link** (`link`) takes
one row and makes one row. For terms `a`, `m`, `b` that every substitution fixes, the link from `a`
to `b` is **derived** from the links from `a` to `m` and from `m` to `b`.

* **`derived_firing`**: in a program that contains the two links, at **every** state, every admitted
  firing of the derived link is matched by an admitted firing of the first link at that state and an
  admitted firing of the second at its result, passing through one row `m` at an identity that was
  missing, and ending in a state that **agrees** with the result of the derived firing (`Agree`): the
  same rows are present with the same labels, and the knowledge has the same solutions. The two
  results differ only in the label of the missing identity the run passed through and in one equation
  `m ≐ m` of the knowledge, which is stated as the last conjunct.

Every firing of a program is a firing of every larger program, so the program with the derived link
has every run of the program without it. That the two results above are interchangeable in every
later run is the subject of `DerivedCongruent`.

**The hypothesis has an instance** (`Atoms.derived_admitted`): over first-order atoms, the link from
`1` to `3` fires at the state with one token `1`.

**Control** (`Atoms.no_four`, `Atoms.stray_makes_four`): the link from `1` to `4` is not derived from
the links from `1` to `2` and from `2` to `3`. In the program of those two links, no run from the
token `1` ever has a row `4`; with the stray link one firing makes it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Derived

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open LogicOverTheStep.StepSpan (Succ)
open OneFrame (Terms frames ext)

section Link

universe uT uS uO

variable {T : Type uT} {S : Type uS} (A : SubstitutionAction T S) {O : Type uO} [DecidableEq O]

/-- **A link**: take one row, make one row. -/
def link (taken made : T) : Rule (Terms T) := ⟨PUnit.unit, ⟨[taken], [], [], [], [made]⟩, []⟩

/-- **Two states agree away from one identity**: the same rows are present, with the same labels
except at that identity, and the knowledge has the same solutions. -/
def Agree (via : O) (u v : State (Terms T) O) : Prop :=
  u.present = v.present ∧ (∀ o, o ≠ via → u.label o = v.label o) ∧
    ∀ (b : PUnit.{1}) (σ : S), (frames A).Models (b := b) σ u.knowledge ↔
      (frames A).Models (b := b) σ v.knowledge

/-- **Every firing of a derived link is a run of two firings.** -/
theorem derived_firing {P : Program (Terms T)} {a m b : T} (groundA : ∀ σ : S, A.apply σ a = a)
    (groundM : ∀ σ : S, A.apply σ m = m) (groundB : ∀ σ : S, A.apply σ b = b)
    (first : link a m ∈ P) (second : link m b ∈ P) (s : State (Terms T) O)
    (g : Firing O (ext A) P s.frame) (fires : g.rule = link a b) (admitted : g.Admits (frames A) s)
    {via : O} (missing : via ∉ s.present) (other : via ∉ g.selection.made) :
    ∃ (g₁ : Firing O (ext A) P s.frame) (g₂ : Firing O (ext A) P (g₁.result (frames A) s).frame),
      g₁.rule = link a m ∧ g₁.Admits (frames A) s ∧ g₂.rule = link m b ∧
        g₂.Admits (frames A) (g₁.result (frames A) s) ∧
          Agree A via (g₂.result (frames A) (g₁.result (frames A) s)) (g.result (frames A) s) ∧
            (g₂.result (frames A) (g₁.result (frames A) s)).knowledge =
              (g.result (frames A) s).knowledge ++ [(m, m)] := by
  obtain ⟨r, member, e, ι, ⟨taken, read, made⟩, seen⟩ := g
  simp only at fires other
  subst fires
  obtain ⟨⟨-, -, -, takeLength, readLength, makeLength, seenLength⟩, enabled, solvable, -⟩ := admitted
  obtain ⟨o, rfl⟩ := List.length_eq_one_iff.mp takeLength.symm
  obtain rfl := List.length_eq_zero_iff.mp readLength.symm
  obtain ⟨o', rfl⟩ := List.length_eq_one_iff.mp makeLength.symm
  obtain rfl := List.length_eq_zero_iff.mp seenLength.symm
  have viaNe : via ≠ o' := fun same => other (List.mem_singleton.mpr same)
  have oPresent : o ∈ s.present :=
    enabled.taken_subset (List.mem_toFinset.mpr (List.mem_singleton_self o))
  have newNotPresent : o' ∉ s.present := fun inside =>
    Finset.disjoint_left.mp enabled.fresh (List.mem_toFinset.mpr (List.mem_singleton_self o')) inside
  -- the first firing
  let g₁ : Firing O (ext A) P s.frame := ⟨link a m, first, e, ι, ⟨[o], [], [via]⟩, []⟩
  have admitted₁ : g₁.Admits (frames A) s := by
    refine ⟨⟨?_, List.nodup_singleton o, List.nodup_singleton via, rfl, rfl, rfl, rfl⟩, ?_, solvable, ?_⟩
    · apply Examples.fresh_of_ground A s g₁
      intro t inside σ
      have terms : t ∈ [a, m] := inside
      rcases List.mem_cons.mp terms with isTaken | rest
      · rw [isTaken]
        exact groundA σ
      · rw [List.mem_singleton.mp rest]
        exact groundM σ
    · apply enabled_of
      · intro x inside
        obtain rfl := List.mem_singleton.mp inside
        exact oPresent
      · intro x inside
        exact absurd inside List.not_mem_nil
      · intro x _ inside
        exact absurd inside List.not_mem_nil
      · intro x inside
        obtain rfl := List.mem_singleton.mp inside
        exact missing
    · intro _ σ _
      exact ⟨fun check inside => absurd inside List.not_mem_nil,
        fun q inside => absurd inside List.not_mem_nil⟩
  -- the state between the two firings
  have label₁ : (g₁.result (frames A) s).label via = A.apply ι m := by
    show relabel (g₁.row (frames A) s) [via] [A.apply ι m] via = A.apply ι m
    simp [relabel]
  have present₁ : ∀ x, x ∈ (g₁.result (frames A) s).present ↔ (x ∈ s.present ∧ x ≠ o) ∨ x = via := by
    intro x
    show x ∈ fire s.present ((⟨[o], [], [via]⟩ : Selection O).commit (T := Unit)) ↔ _
    simp only [mem_fire, Selection.commit, List.mem_toFinset, List.mem_singleton]
  -- the second firing
  let g₂ : Firing O (ext A) P (g₁.result (frames A) s).frame :=
    ⟨link m b, second, PUnit.unit, ι, ⟨[via], [], [o']⟩, []⟩
  have info₂ : g₂.information (frames A) (g₁.result (frames A) s) =
      (frames A).applyStore ((frames A).id (g₁.result (frames A) s).frame)
          (g₁.result (frames A) s).knowledge ++
        [(A.apply ι m, A.apply A.identity ((g₁.result (frames A) s).label via))] ++ [] ++ [] := rfl
  have models₂ : ∀ (b : PUnit.{1}) (σ : S),
      (frames A).Models (b := b) σ (g₂.information (frames A) (g₁.result (frames A) s)) ↔
        (frames A).Models (b := b) σ (g₁.result (frames A) s).knowledge := by
    intro b σ
    rw [info₂, Frames.models_append, Frames.models_append, Frames.models_append,
      Frames.applyStore_id]
    constructor
    · exact fun solved => solved.1.1.1
    · intro solved
      refine ⟨⟨⟨solved, ?_⟩, ?_⟩, ?_⟩
      · intro equation inside
        obtain rfl := List.mem_singleton.mp inside
        show A.E (A.apply σ (A.apply ι m))
          (A.apply σ (A.apply A.identity ((g₁.result (frames A) s).label via)))
        rw [label₁, A.apply_identity]
        exact A.equivalence.refl _
      · intro equation inside
        exact absurd inside List.not_mem_nil
      · intro equation inside
        exact absurd inside List.not_mem_nil
  have admitted₂ : g₂.Admits (frames A) (g₁.result (frames A) s) := by
    refine ⟨⟨?_, List.nodup_singleton via, List.nodup_singleton o', rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_⟩
    · apply Examples.fresh_of_ground A (g₁.result (frames A) s) g₂
      intro t inside σ
      have terms : t ∈ [m, b] := inside
      rcases List.mem_cons.mp terms with isTaken | rest
      · rw [isTaken]
        exact groundM σ
      · rw [List.mem_singleton.mp rest]
        exact groundB σ
    · apply enabled_of
      · intro x inside
        obtain rfl := List.mem_singleton.mp inside
        exact (present₁ x).mpr (Or.inr rfl)
      · intro x inside
        exact absurd inside List.not_mem_nil
      · intro x _ inside
        exact absurd inside List.not_mem_nil
      · intro x inside
        obtain rfl := List.mem_singleton.mp inside
        intro isPresent
        rcases (present₁ x).mp isPresent with ⟨old, -⟩ | isVia
        · exact newNotPresent old
        · exact viaNe isVia.symm
    · obtain ⟨target, σ, solved⟩ := solvable
      exact ⟨target, σ, (models₂ target σ).mpr solved⟩
    · intro _ σ _
      exact ⟨fun check inside => absurd inside List.not_mem_nil,
        fun q inside => absurd inside List.not_mem_nil⟩
  refine ⟨g₁, g₂, rfl, admitted₁, rfl, admitted₂, ⟨?_, ?_, ?_⟩, ?_⟩
  · apply Finset.ext
    intro x
    show x ∈ fire (g₁.result (frames A) s).present ((⟨[via], [], [o']⟩ : Selection O).commit (T := Unit)) ↔
      x ∈ fire s.present ((⟨[o], [], [o']⟩ : Selection O).commit (T := Unit))
    simp only [mem_fire, Selection.commit, List.mem_toFinset, List.mem_singleton, present₁]
    constructor
    · rintro (⟨(⟨inside, notTaken⟩ | isVia), notVia⟩ | isMade)
      · exact Or.inl ⟨inside, notTaken⟩
      · exact absurd isVia notVia
      · exact Or.inr isMade
    · rintro (⟨inside, notTaken⟩ | isMade)
      · exact Or.inl ⟨Or.inl ⟨inside, notTaken⟩, fun isVia => missing (isVia ▸ inside)⟩
      · exact Or.inr isMade
  · intro x notVia
    by_cases isMade : x = o'
    · subst isMade
      show relabel (g₂.row (frames A) (g₁.result (frames A) s)) [x] [A.apply ι b] x =
        relabel (Firing.row (frames A) s
          (⟨link a b, member, e, ι, ⟨[o], [], [x]⟩, []⟩ : Firing O (ext A) P s.frame)) [x]
          [A.apply ι b] x
      simp [relabel]
    · have outside : x ∉ g₂.selection.made := fun inside => isMade (List.mem_singleton.mp inside)
      have outside₁ : x ∉ g₁.selection.made := fun inside => notVia (List.mem_singleton.mp inside)
      rw [g₂.result_label_other (X := frames A) (s := g₁.result (frames A) s) outside]
      show A.apply A.identity ((g₁.result (frames A) s).label x) = _
      rw [g₁.result_label_other (X := frames A) (s := s) outside₁, A.apply_identity]
      exact (Firing.result_label_other (X := frames A) (s := s)
        (⟨link a b, member, e, ι, ⟨[o], [], [o']⟩, []⟩ : Firing O (ext A) P s.frame) outside).symm
  · exact models₂
  · show g₂.information (frames A) (g₁.result (frames A) s) =
      (g₁.result (frames A) s).knowledge ++ [(m, m)]
    rw [info₂, Frames.applyStore_id, label₁, A.apply_identity, groundM ι, List.append_nil,
      List.append_nil]

end Link

/-! ## An instance and a control over first-order atoms -/

namespace Atoms

open Mettapedia.Logic.LP
open Examples (Tm X E c)
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Controls
  (atoms action)

/-- The links from `1` to `2` and from `2` to `3`. -/
def chain : Program Tm := {link (c 1) (c 2), link (c 2) (c 3)}

/-- The chain with the derived link from `1` to `3`. -/
def withDerived : Program Tm := chain ∪ {link (c 1) (c 3)}

/-- The chain with the link from `1` to `4`, which is not derived. -/
def withStray : Program Tm := chain ∪ {link (c 1) (c 4)}

/-- A link of the given program takes the token at row `0` and makes row `1`. -/
def tokenFiring {P : Program Tm} (made : ℕ) (member : link (c 1) (c made) ∈ P) :
    Firing ℕ E P Examples.tokenState.frame :=
  ⟨link (c 1) (c made), member, PUnit.unit, Subst.id atoms, ⟨[0], [], [1]⟩, []⟩

theorem token_admitted {P : Program Tm} (made : ℕ) (member : link (c 1) (c made) ∈ P) :
    (tokenFiring made member).Admits X Examples.tokenState := by
  refine ⟨⟨?_, List.nodup_singleton 0, List.nodup_singleton 1, rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_⟩
  · apply Examples.fresh_of_ground action Examples.tokenState (tokenFiring made member)
    intro t inside σ
    have terms : t ∈ [c 1, c made] := inside
    rcases List.mem_cons.mp terms with isTaken | rest
    · rw [isTaken]
      rfl
    · rw [List.mem_singleton.mp rest]
      rfl
  · apply enabled_of <;> simp [tokenFiring, Examples.tokenState]
  · refine ⟨PUnit.unit, Subst.id atoms, fun e inside => ?_⟩
    have equation : e ∈ [(c 1, c 1)] := inside
    obtain rfl := List.mem_singleton.mp equation
    rfl
  · intro _ σ _
    exact ⟨fun check inside => absurd inside List.not_mem_nil,
      fun q inside => absurd inside List.not_mem_nil⟩

/-- **The derived link fires**: the hypothesis of `derived_firing` has an instance. -/
theorem derived_admitted :
    (tokenFiring (P := withDerived) 3 (Or.inr rfl)).Admits X Examples.tokenState :=
  token_admitted 3 _

/-- **Its firing is a run of the chain**: `derived_firing` at the token, through the missing identity
`2`. -/
theorem derived_is_run :
    ∃ (g₁ : Firing ℕ E withDerived Examples.tokenState.frame)
      (g₂ : Firing ℕ E withDerived (g₁.result X Examples.tokenState).frame),
      g₁.rule = link (c 1) (c 2) ∧ g₁.Admits X Examples.tokenState ∧ g₂.rule = link (c 2) (c 3) ∧
        g₂.Admits X (g₁.result X Examples.tokenState) ∧
          Agree action 2 (g₂.result X (g₁.result X Examples.tokenState))
            ((tokenFiring (P := withDerived) 3 (Or.inr rfl)).result X Examples.tokenState) ∧
            (g₂.result X (g₁.result X Examples.tokenState)).knowledge =
              ((tokenFiring (P := withDerived) 3 (Or.inr rfl)).result X Examples.tokenState).knowledge ++
                [(c 2, c 2)] :=
  derived_firing action (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (Or.inl (Or.inl rfl))
    (Or.inl (Or.inr rfl)) Examples.tokenState _ rfl derived_admitted (by decide) (by decide)

/-- **The stray link makes a row `4`.** -/
theorem stray_makes_four :
    (tokenFiring (P := withStray) 4 (Or.inr rfl)).Admits X Examples.tokenState ∧
      ((tokenFiring (P := withStray) 4 (Or.inr rfl)).result X Examples.tokenState).label 1 = c 4 :=
  ⟨token_admitted 4 _, rfl⟩

/-- No present row is labelled `4`. -/
def NoFour (s : State Tm ℕ) : Prop := ∀ o ∈ s.present, s.label o ≠ c 4

/-- **The chain never makes a row `4`**: the property is kept by every firing of the chain. -/
theorem noFour_step {s t : State Tm ℕ} (none : NoFour s)
    (moved : Succ (step X ℕ E chain).toStep s t) : NoFour t := by
  obtain ⟨g, admitted, rfl⟩ := moved
  intro o inside
  show (g.result X s).label o ≠ c 4
  by_cases isMade : o ∈ g.selection.made
  · have lengths : g.selection.made.length = (g.opened X).produce.length := by
      show g.selection.made.length = (g.rule.body.produce.map (X.act g.opening)).length
      rw [List.length_map]
      exact admitted.1.2.2.2.2.2.1.symm
    obtain ⟨t, zipped⟩ := exists_zip_of_mem g.selection.made (g.opened X).produce lengths o isMade
    rw [g.result_label_made (X := X) (s := s) admitted.1 zipped]
    have produced : t ∈ g.rule.body.produce.map (X.act g.opening) := (List.of_mem_zip zipped).2
    obtain ⟨original, member, rfl⟩ := List.mem_map.mp produced
    obtain ⟨r, inChain, e, ι, selection, seen⟩ := g
    have rule : r = link (c 1) (c 2) ∨ r = link (c 2) (c 3) := inChain
    rcases rule with rfl | rfl
    · have made : original = c 2 := List.mem_singleton.mp member
      rw [made]
      intro four
      have constants : c 2 = c 4 := four
      exact absurd (Term.const.inj constants) (by decide)
    · have made : original = c 3 := List.mem_singleton.mp member
      rw [made]
      intro four
      have constants : c 3 = c 4 := four
      exact absurd (Term.const.inj constants) (by decide)
  · rw [g.result_label_other (X := X) (s := s) isMade]
    have wasPresent : o ∈ s.present := by
      rcases mem_fire.mp inside with ⟨old, -⟩ | made
      · exact old
      · exact absurd (List.mem_toFinset.mp made) isMade
    intro four
    apply none o wasPresent
    have row : action.apply action.identity (s.label o) = c 4 := four
    exact (action.apply_identity (s.label o)).symm.trans row

/-- **No run of the chain from the token reaches a row `4`**, which one firing of the stray link
makes (`stray_makes_four`). -/
theorem no_four {t : State Tm ℕ}
    (reached : Relation.ReflTransGen (Succ (step X ℕ E chain).toStep) Examples.tokenState t) :
    NoFour t := by
  induction reached with
  | refl =>
      intro o _
      show c 1 ≠ c 4
      exact fun same => absurd (Term.const.inj same) (by decide)
  | tail _ moved kept => exact noFour_step kept moved

#print axioms derived_admitted
#print axioms derived_is_run
#print axioms stray_makes_four
#print axioms noFour_step
#print axioms no_four

end Atoms

#print axioms derived_firing

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Derived
