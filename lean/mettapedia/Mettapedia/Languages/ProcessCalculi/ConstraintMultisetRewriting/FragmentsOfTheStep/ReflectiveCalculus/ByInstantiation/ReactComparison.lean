import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.ByInstantiation.Bisimulation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Source

/-!
# The placement by instantiation against the placement by the `react` former

**No former computes.** Every former of the signature reads back as the corresponding constructor
of the source (`Signature.read_input`, ...). The made row of communication is the continuation
applied to the received name and process; under every assignment of the rule's unknowns it is the
term algebra's own substitution (`made_row_is_instantiation`).

**The equality of the knowledge** is fixed by the equations of the calculus at names and by nothing
else:
* it only identifies terms whose read-backs are equal modulo the calculus's equations
  (`knowledge_within_equations`);
* it identifies closed names that are equal modulo those equations, quote-drop among them
  (`received_name_needs_name_equivalence`): a communication makes the received name `@(*@0)` as the
  channel of a made row, the source communicates on it with a receiver on `@0`, and syntactic
  equality does not relate the two channels;
* it does not contain the bag laws (`bag_laws_not_in_knowledge`): two bags in different orders are
  not equal in the knowledge, although their read-backs are structurally congruent. With the bag laws
  in the knowledge, heating has two solutions with different rows (the `react` placement's
  `Mechanisms.bag_laws_split_two_ways`).

**The old placement is the new one followed by a normal-form map**: the meaning of the `react` placement's
made row `react K Q` is the canonical form of the read-back of the new made row
(`react_is_normal_form`), and every represented state of the new placement is sent, row by row, to a
store of the `react` placement's placement that represents the same process (`normal_form_represents`).

**The representation, with examples**:
* `separating_contractum_exact`: on the separating program the made row is exactly the calculus's
  contractum, without a normal form;
* `both_representations`: a continuation that uses the received name and its drop, `y!(*y)`, made
  into `@Q!(Q)`;
* `outside_the_carrier`: a quote that contains the bound name, `@(*y | *y)!(0)`, is outside the sealed
  carrier, and there ordinary instantiation enters the quote while the calculus's substitution does
  not;
* `quote_drop_of_bound_name`: on `@(*y)!(0)`, also outside the sealed carrier, instantiation and
  the calculus's substitution agree.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.ByInstantiation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical (canonicalize)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalReaction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalReactionControls

/-! ## No former computes -/

/-- **The made row of every admitted communication is the instantiation of the opened made
pattern**: the result labels the made occurrence by the opened pattern `K⟨@Q, Q⟩`, and every grounding
of the result reads it as the continuation instantiated at the received name and process. -/
theorem made_row_is_instantiation {s : State} (f : Firing s) (isComm : f.rule = commRule)
    (admitted : f.Admits knowledge s) :
    ∃ o₃, f.selection.made = [o₃] ∧ ∀ g' : Grounding (target f),
      ∃ h : Grounding commFrame,
        instantiateObservation g' ((f.result knowledge s).label o₃) =
          ⟨[], .pr, bind (received (h .payload)) (h .body)⟩ := by
  obtain ⟨rule, member, ext, opening, ⟨taken, readSel, made⟩, seen⟩ := f
  change rule = commRule at isComm
  subst isComm
  obtain ⟨shapes, _, _, _⟩ := admitted
  have produceLen : 1 = made.length := shapes.2.2.2.2.2.1
  obtain ⟨o₃, rfl⟩ := List.length_eq_one_iff.mp produceLen.symm
  let fir : Firing s := ⟨commRule, member, ext, opening, ⟨taken, readSel, [o₃]⟩, seen⟩
  refine ⟨o₃, rfl, fun g' => ⟨Assignment.compose g' opening, ?_⟩⟩
  refine (ground_made fir g' shapes (p := obs commMade) (by
    simp [fir, RuleSyntax.Firing.opened, RuleInstance.map])).trans ?_
  show (⟨[], .pr, instantiate (Assignment.compose g' opening) commMade⟩ :
    Observation sig noUnknowns) = _
  rw [made_instantiation_ground]
  rfl

/-! ## The equality of the knowledge -/

theorem obsSimilar_same {Γ : Ctx sig} {s : Srt} {t t' : G Γ s}
    (similar : ObsSimilar ⟨Γ, s, t⟩ ⟨Γ, s, t'⟩) : Similar t t' := by
  cases similar with
  | mk inner => exact inner

/-- **The knowledge identifies only what the equations of the calculus identify.** -/
theorem knowledge_within_equations {F : Interface.Frames.Frame sig} {Γ : Ctx sig} {s : Srt}
    {t t' : Term (signature sig F.arity) Γ s}
    (equal : knowledge.E (a := F) ⟨Γ, s, t⟩ ⟨Γ, s, t'⟩) (g : Grounding F) :
    StructuralCongruence (read (instantiate g t)) (read (instantiate g t')) :=
  similar_sound (obsSimilar_same (equal g))

/-- `@0` and `@(*@0)` as twin terms. -/
def nameZero : G [] .nm := quoteT zeroT
def nameDropZero : G [] .nm := quoteT (dropqT zeroT)

theorem read_nameZero : read nameZero = channel := rfl
theorem read_nameDropZero : read nameDropZero = alternateChannel := rfl

/-- **The received name needs name equivalence.** The continuation `y!(0)` receiving `*@0` makes
the row `@(*@0)!(0)`, whose channel is not `@0` as written; the source communicates between
`@(*@0)` and `@0`; the knowledge relates the two channels, syntactic equality does not. -/
theorem received_name_needs_name_equivalence :
    bind (received (dropqT zeroT)) (outputT nameVar zeroT) = outputT nameDropZero zeroT ∧
      nameDropZero ≠ nameZero ∧ Similar nameDropZero nameZero ∧
      rhoLanguageDefGSLT.Step alternateSource (rule.target CanonicalBag.empty) := by
  refine ⟨rfl, fun same => literal_names_distinct (by rw [← read_nameDropZero, ← read_nameZero, same]),
    .name (by decide) (by decide) ?_, Source.communicates_up_to_name_equivalence.2⟩
  rw [read_nameDropZero, read_nameZero]
  exact StructuralCongruence.quote_drop channel

/-- The prime `@0!(0)` as a twin term. -/
def outputZero : G [] .pr := outputT nameZero zeroT

/-- The prime `@0!(@0!(0))`. -/
def outputOutput : G [] .pr := outputT nameZero outputZero

/-- **The bag laws are not in the knowledge.** Two bags with their components in different orders
are structurally congruent and not similar, so no grounding equates them. -/
theorem bag_laws_not_in_knowledge :
    StructuralCongruence (read (bagT (pconsT outputZero (pconsT outputOutput pnilT))))
        (read (bagT (pconsT outputOutput (pconsT outputZero pnilT)))) ∧
      ¬ Similar (bagT (pconsT outputZero (pconsT outputOutput pnilT)))
        (bagT (pconsT outputOutput (pconsT outputZero pnilT))) := by
  refine ⟨StructuralCongruence.par_comm _ _, fun similar => ?_⟩
  obtain ⟨heads, _⟩ := similar_pcons_pcons (similar_bag_bag similar)
  obtain ⟨_, payloads⟩ := similar_output_output heads
  cases payloads

/-! ## The old placement is the new one followed by a normal form -/

/-- **The `react` placement's made row means the normal form of the new made row.** At any grounding that
gives the `react` placement's continuation and payload unknowns the canonical read-backs of a sealed
continuation and payload, `react K Q` means the canonical form of the read-back of the
continuation instantiated at the received name and process. -/
theorem react_is_normal_form (b : G [.nm, .pr] .pr) (q : G [] .pr)
    (safeB : binderSafeAt "NQuote" 1 (read b) = true) (safeQ : binderSafeAt "NQuote" 0 (read q) = true)
    (g : Unknown → Pattern) (atBody : g ⟨0, .body⟩ = canonicalize (read b))
    (atPayload : g ⟨0, .payload⟩ = canonicalize (read q)) :
    (Tm.react (unknown 0 .body) (unknown 0 .payload)).eval g =
      canonicalize (read (bind (received q) b)) := by
  rw [contractum_by_instantiation_canonical b q safeB safeQ]
  show canonicalize (semanticCommSubst (g ⟨0, .body⟩) (g ⟨0, .payload⟩)) = _
  rw [atBody, atPayload]

/-- **The normal-form map on states**: each row becomes a literal row of the `react` placement's step, its
value read back and put in canonical form; there is no knowledge. -/
def normalStore (s : State) (value : ℕ → G [] .pr) : ReflectiveCalculus.Store :=
  ⟨[], s.present.image fun o => (o, Tm.lit (canonicalize (read (value o))))⟩

/-- **The old placement is the new one followed by the normal-form map**: every state of the new
placement that represents a closed process is sent to a store of the `react` placement's placement that
represents the same process. -/
theorem normal_form_represents {s : State} {P : RhoProcess} {value : ℕ → G [] .pr}
    (represented : RepresentsBy s P value) :
    ReflectiveCalculus.RepresentsBy (normalStore s value) P
      (fun occurrence => canonicalize (read (value occurrence.1))) := by
  classical
  have injective : Set.InjOn (fun o : ℕ => ((o, Tm.lit (canonicalize (read (value o)))) :
      ReflectiveCalculus.Occ)) s.present :=
    fun _ _ _ _ same => congrArg Prod.fst same
  refine ⟨⟨fun _ => zeroPattern, ReflectiveCalculus.holds_nil _⟩, ?_, ?_, ?_⟩
  · intro g _ occurrence member
    obtain ⟨o, _, rfl⟩ := Finset.mem_image.mp member
    rfl
  · intro occurrence member
    obtain ⟨o, present, rfl⟩ := Finset.mem_image.mp member
    exact canonical_row (value o) (represented.closed o present)
  · rw [← represented.inventory_eq]
    unfold ReflectiveCalculus.inventory inventoryOf
    rw [show (normalStore s value).present = s.present.image fun o =>
      ((o, Tm.lit (canonicalize (read (value o)))) : ReflectiveCalculus.Occ) from rfl,
      Finset.sum_image injective]
    exact Finset.sum_congr rfl fun o _ => primes_canonicalize _

/-- The `react` placement's made row is a former whose meaning is the calculus's substitution followed by
the normalizer, by definition; the new made row has no such former. -/
theorem react_meaning (g : Unknown → Pattern) :
    (Tm.react (unknown 0 .body) (unknown 0 .payload)).eval g =
      canonicalize (semanticCommSubst (g ⟨0, .body⟩) (g ⟨0, .payload⟩)) := rfl

/-! ## The representation, with examples -/

/-- **On the separating program `for(y <- @0){*y} | @0!(@0!(0))` the made row is exactly the
calculus's contractum**: the continuation `*y` is the twin, and its instantiation at the received
process is that process. -/
theorem separating_contractum_exact :
    read (twinVar (D := noUnknowns) (Γ := [])) = body ∧ read outputZero = payload ∧
      read (bind (received outputZero) twinVar) = rule.result.1 :=
  ⟨rfl, rfl, rfl⟩

/-- **A continuation with the received name and its drop**, `y!(*y)`: instantiated at `@0!(0)` it
makes `@(@0!(0))!(@0!(0))`, the calculus's contractum. -/
theorem both_representations :
    read (outputT (nameVar (D := noUnknowns) (Γ := [])) twinVar) =
        .apply "POutput" [.bvar 0, .apply "PDrop" [.bvar 0]] ∧
      bind (received outputZero) (outputT nameVar twinVar) = outputT (quoteT outputZero) outputZero ∧
      read (bind (received outputZero) (outputT nameVar twinVar)) =
        semanticCommSubst (read (outputT (nameVar (D := noUnknowns) (Γ := [])) twinVar))
          (read outputZero) := by
  refine ⟨rfl, rfl, ?_⟩
  decide

/-- `@(*y | *y)!(0)`: a quote that contains the bound name. -/
def quotedTwins : G [.nm, .pr] .pr :=
  outputT (quoteT (bagT (pconsT twinVar (pconsT twinVar pnilT)))) zeroT

/-- Two drops of the bound name in parallel are not the bound name: decided by
the declaration's binder-head reading, which agrees with rho's canonical form. -/
private theorem twins_not_bound_name :
    canonicalize (.apply "NQuote" [.collection .hashBag
      [.apply "PDrop" [.bvar 0], .apply "PDrop" [.bvar 0]] none]) ≠ .bvar 0 := by
  rw [← Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalMatch.derivedCanonicalize_eq]
  intro hit
  have head := (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.BinderHead.ofPattern_index_iff _ _ _).mpr hit
  revert head
  decide

/-- **Outside the carrier**: the quote of `@(*y | *y)!(0)` is not sealed, and there ordinary
instantiation enters the quote (`@(0 | 0)!(0)`) while the calculus's substitution leaves the quote
alone, with the bound index still inside. -/
theorem outside_the_carrier :
    binderSafeAt "NQuote" 1 (read quotedTwins) = false ∧
      read (bind (received zeroT) quotedTwins) =
        .apply "POutput" [.apply "NQuote" [.collection .hashBag
          [.apply "PZero" [], .apply "PZero" []] none], .apply "PZero" []] ∧
      semanticCommSubst (read quotedTwins) (read (zeroT (D := noUnknowns) (Γ := []))) =
        .apply "POutput" [.apply "NQuote" [.collection .hashBag
          [.apply "PDrop" [.bvar 0], .apply "PDrop" [.bvar 0]] none], .apply "PZero" []] := by
  refine ⟨by decide, rfl, ?_⟩
  have body : read quotedTwins = .apply "POutput" [.apply "NQuote" [.collection .hashBag
      [.apply "PDrop" [.bvar 0], .apply "PDrop" [.bvar 0]] none], .apply "PZero" []] := rfl
  have payload : read (zeroT (D := noUnknowns) (Γ := [])) = .apply "PZero" [] := rfl
  rw [body, payload]
  simp [semanticCommSubst, semanticSubstProc, semanticSubstName,
    semanticSubstNameMark, twins_not_bound_name, semanticNormalizeName, semanticNormalizeProc,
    semanticNormalizeProcList]

/-- `@(*y)!(0)`. -/
def quotedTwin : G [.nm, .pr] .pr := outputT (quoteT twinVar) zeroT

/-- **Quote-drop of the bound name**, also outside the sealed carrier: `@(*y)!(0)` instantiated at
`0` is `@0!(0)`, and so is the calculus's substitution (`@(*y)` is name equivalent to `y`). -/
theorem quote_drop_of_bound_name :
    binderSafeAt "NQuote" 1 (read quotedTwin) = false ∧
      read (bind (received zeroT) quotedTwin) = .apply "POutput" [channel, .apply "PZero" []] ∧
      semanticCommSubst (read quotedTwin) (read (zeroT (D := noUnknowns) (Γ := []))) =
        .apply "POutput" [channel, .apply "PZero" []] := by
  refine ⟨by decide, rfl, ?_⟩
  decide

#print axioms made_row_is_instantiation
#print axioms knowledge_within_equations
#print axioms received_name_needs_name_equivalence
#print axioms bag_laws_not_in_knowledge
#print axioms react_is_normal_form
#print axioms normal_form_represents
#print axioms separating_contractum_exact
#print axioms both_representations
#print axioms outside_the_carrier
#print axioms quote_drop_of_bound_name

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.ByInstantiation
