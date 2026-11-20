import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings.DividingLineControls

/-!
# An instance of `succeeds_beside` whose success needs two firings, beside a competing row and rule

The instances of `succeeds_beside` elsewhere use systems that show success at once, so the replay of
firings is used there only through the general proof. Here the system needs two firings: from the row
`*@0`, `firstRule` makes `*@*@0`, then `secondRule` makes `ω!(0)`; at the start no barb is shown
(`chain_no_barb_at_start`), and the run of two firings reaches the barb (`chain_succeeds`). The
neighbour holds a row `*@0` that `firstRule` also matches, and a rule that takes `*@0`
(`rivalSystem`). The instance (`two_firings_beside_rival`) replays both firings beside it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings.TwoFirings

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open ByInstantiation (sig G Similar ObsSimilar Grounding knowledge groundFrame someGrounding zeroT dropqT)
open Interface.Frames (Frame)

/-- The intermediate row `*@*@0`. -/
abbrev midRow : G [] .pr := dropqT (dropqT zeroT)

/-- **Take `*@0`, make `*@*@0`.** -/
abbrev firstRule : RuleSyntax.Rule (RuleSyntax.Contextual.Terms sig) where
  locals := groundFrame
  body := { take := [ByInstantiation.obs blockerRow], read := [], tell := [], checks := [],
            produce := [ByInstantiation.obs midRow] }
  collect := []

/-- **Take `*@*@0`, make `ω!(0)`.** -/
abbrev secondRule (ω : G [] .nm) : RuleSyntax.Rule (RuleSyntax.Contextual.Terms sig) where
  locals := groundFrame
  body := { take := [ByInstantiation.obs midRow], read := [], tell := [], checks := [],
            produce := [ByInstantiation.obs (successRow ω)] }
  collect := []

/-- **Take `*@0`, make nothing.** -/
abbrev rivalRule : RuleSyntax.Rule (RuleSyntax.Contextual.Terms sig) where
  locals := groundFrame
  body := { take := [ByInstantiation.obs blockerRow], read := [], tell := [], checks := [], produce := [] }
  collect := []

abbrev chainProgram (ω : G [] .nm) : Prog := {firstRule, secondRule ω}

/-- The system: the two rules and the row `*@0`. -/
def chainSystem (ω : G [] .nm) : System := ⟨chainProgram ω, single blockerRow⟩

/-- The neighbour: the rule that takes `*@0`, and a row `*@0` of its own. -/
def rivalSystem : System := ⟨{rivalRule}, single blockerRow⟩

theorem chain_positive (ω : G [] .nm) : ∀ r ∈ (chainSystem ω).program, RuleSyntax.Scope.Positive r := by
  intro r member
  rcases member with isFirst | isSecond
  · rw [isFirst]
    exact ⟨fun _ inside => absurd inside List.not_mem_nil, rfl⟩
  · rw [Set.mem_singleton_iff.mp isSecond]
    exact ⟨fun _ inside => absurd inside List.not_mem_nil, rfl⟩

/-! ## The first firing -/

abbrev firing₁ (ω : G [] .nm) : RuleSyntax.Firing ℕ decl (chainProgram ω) (single blockerRow).frame :=
  RuleSyntax.Contextual.canonical (F := (single blockerRow).frame) firstRule (Set.mem_insert _ _)
    ⟨[0], [], [1]⟩ []

/-- The state after the first firing. -/
abbrev state₁ (ω : G [] .nm) : ByInstantiation.State := (firing₁ ω).result knowledge (single blockerRow)

theorem information₁ (ω : G [] .nm) :
    (firing₁ ω).information knowledge (single blockerRow) =
      [(knowledge.act (firing₁ ω).opening (ByInstantiation.obs blockerRow),
        knowledge.act (decl.weaken (firing₁ ω).ext) (ByInstantiation.obs blockerRow))] := rfl

theorem equation₁ (ω : G [] .nm) {B : Frame sig} (σ : Assignment (decl.target (firing₁ ω).ext).arity B.arity) :
    knowledge.E (knowledge.act σ (knowledge.act (firing₁ ω).opening (ByInstantiation.obs blockerRow)))
      (knowledge.act σ (knowledge.act (decl.weaken (firing₁ ω).ext) (ByInstantiation.obs blockerRow))) :=
  equal_of_grounds (o := ByInstantiation.obs blockerRow)
    (fun g => ground_back₃ (firing₁ ω).opening σ g (ByInstantiation.obs blockerRow))
    (fun g => ground_back₃ (decl.weaken (firing₁ ω).ext) σ g (ByInstantiation.obs blockerRow))

theorem admitted₁ (ω : G [] .nm) : (firing₁ ω).Admits knowledge (single blockerRow) := by
  refine ⟨⟨canonical_fresh_knowledge _ firstRule _ _ _, List.nodup_singleton 0, List.nodup_singleton 1,
    rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_⟩
  · change Enabled (fun _ : ℕ => ()) ({0} : Finset ℕ) ((⟨[0], [], [1]⟩ : Selection ℕ).commit (T := Unit))
    decide
  · refine ⟨groundFrame, someGrounding _, ?_⟩
    rw [information₁]
    intro e inside
    obtain rfl := List.mem_singleton.mp inside
    exact equation₁ ω (someGrounding _)
  · intro b σ _
    exact ⟨fun c inside => (nomatch inside), fun q inside => (nomatch inside)⟩

theorem label₁ (ω : G [] .nm) :
    (state₁ ω).label 1 = knowledge.act (firing₁ ω).opening (ByInstantiation.obs midRow) := rfl

/-! ## The second firing -/

abbrev firing₂ (ω : G [] .nm) : RuleSyntax.Firing ℕ decl (chainProgram ω) (state₁ ω).frame :=
  RuleSyntax.Contextual.canonical (F := (state₁ ω).frame) (secondRule ω)
    (Set.mem_insert_of_mem _ (Set.mem_singleton _)) ⟨[1], [], [2]⟩ []

/-- The state after the second firing. -/
abbrev state₂ (ω : G [] .nm) : ByInstantiation.State := (firing₂ ω).result knowledge (state₁ ω)

theorem information₂ (ω : G [] .nm) :
    (firing₂ ω).information knowledge (state₁ ω) =
      [(knowledge.act (decl.weaken (firing₂ ω).ext)
          (knowledge.act (firing₁ ω).opening (ByInstantiation.obs blockerRow)),
        knowledge.act (decl.weaken (firing₂ ω).ext)
          (knowledge.act (decl.weaken (firing₁ ω).ext) (ByInstantiation.obs blockerRow))),
       (knowledge.act (firing₂ ω).opening (ByInstantiation.obs midRow),
        knowledge.act (decl.weaken (firing₂ ω).ext) ((state₁ ω).label 1))] := rfl

/-- The grounding of the frame after the second firing solves its information. -/
theorem solved₂ (ω : G [] .nm) :
    knowledge.Models (b := groundFrame) (someGrounding _) ((firing₂ ω).information knowledge (state₁ ω)) := by
  rw [information₂]
  intro e inside
  rcases List.mem_cons.mp inside with rfl | inside
  · exact equal_of_grounds (o := ByInstantiation.obs blockerRow)
      (fun g => ground_back₄ (firing₁ ω).opening (decl.weaken (firing₂ ω).ext) (someGrounding _) g
        (ByInstantiation.obs blockerRow))
      (fun g => ground_back₄ (decl.weaken (firing₁ ω).ext) (decl.weaken (firing₂ ω).ext) (someGrounding _) g
        (ByInstantiation.obs blockerRow))
  · obtain rfl := List.mem_singleton.mp inside
    rw [label₁]
    exact equal_of_grounds (o := ByInstantiation.obs midRow)
      (fun g => ground_back₃ (firing₂ ω).opening (someGrounding _) g (ByInstantiation.obs midRow))
      (fun g => ground_back₄ (firing₁ ω).opening (decl.weaken (firing₂ ω).ext) (someGrounding _) g
        (ByInstantiation.obs midRow))

theorem admitted₂ (ω : G [] .nm) : (firing₂ ω).Admits knowledge (state₁ ω) := by
  refine ⟨⟨canonical_fresh_knowledge _ (secondRule ω) _ _ _, List.nodup_singleton 1, List.nodup_singleton 2,
    rfl, rfl, rfl, rfl⟩, ?_, ⟨groundFrame, someGrounding _, solved₂ ω⟩, ?_⟩
  · change Enabled (fun _ : ℕ => ())
      (fire ({0} : Finset ℕ) ((⟨[0], [], [1]⟩ : Selection ℕ).commit (T := Unit)))
      ((⟨[1], [], [2]⟩ : Selection ℕ).commit (T := Unit))
    decide
  · intro b σ _
    exact ⟨fun c inside => (nomatch inside), fun q inside => (nomatch inside)⟩

/-! ## Success after two firings, and none at the start -/

theorem chain_succeeds (ω : G [] .nm) : (stepParallelSolvable ω).Succeeds (chainSystem ω) := by
  refine ⟨⟨chainProgram ω, state₂ ω⟩,
    (Relation.ReflTransGen.single (b := (⟨chainProgram ω, state₁ ω⟩ : System))
      ⟨rfl, firing₁ ω, admitted₁ ω, rfl⟩).tail ⟨rfl, firing₂ ω, admitted₂ ω, rfl⟩, ?_⟩
  refine outBarb_of_ground (o := 2) ?_ (solved₂ ω) ?_
  · change 2 ∈ fire (fire ({0} : Finset ℕ) ((⟨[0], [], [1]⟩ : Selection ℕ).commit (T := Unit)))
      ((⟨[1], [], [2]⟩ : Selection ℕ).commit (T := Unit))
    decide
  · show instantiateObservation (someGrounding _)
      (instantiateObservation (firing₂ ω).opening (ByInstantiation.obs (successRow ω))) = _
    exact ground_back _ _ _

theorem chain_no_barb_at_start (ω : G [] .nm) : ¬ OutBarb ω (chainSystem ω).state := by
  rintro ⟨o, _, B, σ, h, _, equal⟩
  have similar := equal (someGrounding B)
  change ObsSimilar
      (instantiateObservation (someGrounding B) (instantiateObservation σ (ByInstantiation.obs blockerRow)))
      (instantiateObservation (someGrounding B)
        (instantiateObservation h ⟨[], .pr, ByInstantiation.outputT (embed ω) payloadUnknown⟩)) at similar
  have left : instantiateObservation (someGrounding B)
      (instantiateObservation σ (ByInstantiation.obs blockerRow)) = ByInstantiation.obs blockerRow :=
    ground_back _ _ _
  rw [left] at similar
  have closed := ByInstantiation.obsSimilar_closed.mp similar
  change Similar (dropqT zeroT) (ByInstantiation.outputT _ _) at closed
  cases closed

/-! ## The instance -/

theorem rival_composable (ω : G [] .nm) : (stepParallelSolvable ω).composable (chainSystem ω) rivalSystem := by
  refine (ByInstantiation.solvable_iff _).mpr ⟨someGrounding _, ?_⟩
  intro e member
  change e ∈ knowledge.applyStore _ ([] : List _) ++ knowledge.applyStore _ ([] : List _) at member
  simp [Interface.Frames.applyStore] at member

/-- **`succeeds_beside` with a run of two firings**: the system shows no barb at the start and
succeeds alone after two firings; beside the neighbour with a competing row `*@0` and a rule that takes
`*@0`, the composite succeeds. -/
theorem two_firings_beside_rival (ω : G [] .nm) :
    ¬ OutBarb ω (chainSystem ω).state ∧ (stepParallelSolvable ω).Succeeds (chainSystem ω) ∧
      (stepParallelSolvable ω).Succeeds ((stepParallelSolvable ω).par (chainSystem ω) rivalSystem) :=
  ⟨chain_no_barb_at_start ω, chain_succeeds ω,
    succeeds_beside (fun r member => positive_monotone (chain_positive ω r member)) (rival_composable ω)
      (chain_succeeds ω)⟩

#print axioms admitted₁
#print axioms solved₂
#print axioms admitted₂
#print axioms chain_succeeds
#print axioms chain_no_barb_at_start
#print axioms two_firings_beside_rival

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings.TwoFirings
