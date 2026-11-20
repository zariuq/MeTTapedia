import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings.Translation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Source

/-!
# The reflective calculus into the step: Gorla's criteria, one by one

**The calculi** (`Criteria.Calculus`):

* `rhoCalculus ω`: closed processes of the sealed carrier, the reduction `rhoLanguageDefGSLT.Step`
  (communication modulo the equations), success an output barb on the canonical form of `ω` (the
  calculus's OUT-BARB, read on canonical forms), and the equations as the equivalence.
* `stepCalculus ω`: states of `ByInstantiation.theStep` (the step defined by rule syntax with the
  four-rule program), its reduction, success the output barb on `ω` (the tree's may-barb of the
  pattern `ω!(Q)`), and weak barbed bisimilarity (output barbs on closed channels) as the
  equivalence. That equivalence respects success (`stepCalculus_successRespecting`), Gorla's
  coherence condition. It is not a congruence for the tensor, even on represented states
  (`not_congruence_represented`, in `Congruence`).

**The translation** is `encode`, a function on syntax (`Translation`).

| Criterion | Status | Theorem |
|---|---|---|
| Definition 5.2, homomorphic on `|` | holds on the nose, the step's `|` being the tensor | `encode_homomorphic` |
| Property 1, compositionality | holds at `|` with the tensor as the context (`encode_compositional_par`). Fails at output and at input: no function of the translated argument gives the translated prefix, since `0` and `{0}` have the same translation and `@0!(0)` and `@0!({0})` do not (`output_not_compositional`, `input_not_compositional`, in `Compositionality`). An input or an output is one row determined by the prefix, the state with its twin term (`encode_input`, `encode_output`); the twin translation is compositional former by former (`twin_lift`). The drop of a bound name is translated as a name-indexed constant; read as one operator taking a name term, the drop fails it | `drop_not_a_context` |
| Property 2, name invariance | not shown; its renaming clause has content here (see below). Shown: the correctness of one communication's contractum, and name-equivalent channels | `contractum_correct`, `name_equivalence_respected` |
| Property 3, operational correspondence | holds up to weak barbed bisimilarity | `encode_operationalCorrespondence` |
| Property 4, divergence reflection | holds | `encode_divergenceReflecting` |
| Property 5, success sensitiveness | holds for every closed `ω` | `encode_successSensitive` |

`rho_into_step` collects Definition 5.2 and Properties 3 to 5.

**Name invariance: what is and is not shown.** In the 2005 paper the free names of an output include
its channel (`FN(x⟨|P|⟩) = {x} ∪ FN(P)`), and the set of names of the calculus is global; so on closed
processes Property 2's clause for a renaming has content: a permutation `σ` of names changes
`@0!(0)`, and the clause asks a renaming `σ'` of the step's terms with `⟦σ(P)⟧ = σ'(⟦P⟧)`
(Palamidessi's uniform encodings ask the same for permutations of names). That clause is not proved
here. The communication's own substitution, a quoted process `@Q` for the bound name where the drop
`*y` becomes `Q` (§2.7), is the content of `contractum_correct`: for a sealed continuation and a
closed payload, the row that the step's communication makes by instantiation, `bind (received ⦇Q⦈)`
applied to the continuation's twin, represents the calculus's contractum, so it is weakly barbed
bisimilar to the translation of every process with that canonical form. That is the correctness of
one communication's contractum through the representation, not an instance of
`Criteria.NameInvariant`. Control: ordinary substitution of the quote for the name, keeping `*@Q` as a
drop, gives a different contractum with different behaviour (`ordinary_substitution_differs`, from
the source module).

**The single-row translation** `encodeRow` meets operational correspondence, divergence reflection
and success sensitiveness too (`encodeRow_valid`), and is not homomorphic
(`encodeRow_not_homomorphic`): Gorla's two-level form.

**Existence.** A process that succeeds and one that does not (`succeeds_output`,
`nil_not_succeeds`); a process whose translation diverges, so that divergence reflection is not
vacuous, is in `Divergence` (`encode_omega_diverges`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical (canonicalize)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalBag
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalReaction (output)
open ByInstantiation (sig G Closed Similar ObsSimilar Grounding GroundSolves read inputT outputT zeroT
  bagT pnilT pconsT dropqT quoteT spine knowledge groundFrame someGrounding)

/-! ## The two calculi -/

/-- **The reflective calculus as a calculus**: closed processes, the reduction modulo the equations,
an output barb on the canonical form of `ω` as success, the equations as the equivalence. -/
def rhoCalculus (ω : G [] .nm) : Calculus.{0} :=
  ⟨RhoProcess, rhoLanguageDefGSLT.Step, fun P => Barb P (canonicalize (read ω)),
    rhoProcessEquations.r⟩

/-- **The step of the program as a calculus**: states, reductions, the output barb on `ω` as success,
weak barbed bisimilarity as the equivalence. -/
def stepCalculus (ω : G [] .nm) : Calculus.{1} :=
  ⟨ByInstantiation.State, Moves, OutBarb ω, WeaklyBarbedBisimilar⟩

/-- **Gorla's coherence condition holds for the step**: weak barbed bisimilarity never relates a state
that succeeds and one that does not. -/
theorem stepCalculus_successRespecting {ω : G [] .nm} (closed : Closed ω) :
    (stepCalculus ω).SuccessRespecting := by
  intro s t related
  exact ⟨fun succeeds => weaklyBarbedBisimilar_succeeds related closed succeeds,
    fun succeeds => weaklyBarbedBisimilar_succeeds (weaklyBarbedBisimilar_symm related) closed succeeds⟩

/-! ## The criteria -/

/-- **Definition 5.2**: the translation of `P | Q` is the tensor of the translations, on the nose. -/
theorem encode_homomorphic (ω : G [] .nm) :
    Homomorphic (L := rhoCalculus ω) (M := stepCalculus ω) encode par tensor Eq :=
  encode_par

/-- **Property 1 at parallel composition**, with the tensor as the context. -/
theorem encode_compositional_par (ω : G [] .nm) :
    CompositionalAt (L := rhoCalculus ω) (M := stepCalculus ω) encode
      (fun arguments : Fin 2 → RhoProcess => par (arguments 0) (arguments 1))
      (fun images => tensor (images 0) (images 1)) :=
  (encode_homomorphic ω).compositionalAt

/-- **Property 3, operational correspondence**, up to weak barbed bisimilarity. -/
theorem encode_operationalCorrespondence (ω : G [] .nm) :
    OperationalCorrespondence (L := rhoCalculus ω) (M := stepCalculus ω) encode where
  complete P P' run := by
    obtain ⟨T, steps, represented⟩ := reaches_complete (encode_represents P) run
    exact ⟨T, steps, weaklyBarbedBisimilar_of_represents represented (encode_represents P')⟩
  sound P T run := by
    obtain ⟨P', steps, represented⟩ := reaches_sound (encode_represents P) run
    exact ⟨P', steps, T, .refl, weaklyBarbedBisimilar_of_represents represented (encode_represents P')⟩

/-- **Property 4, divergence reflection.** -/
theorem encode_divergenceReflecting (ω : G [] .nm) :
    DivergenceReflecting (L := rhoCalculus ω) (M := stepCalculus ω) encode :=
  fun P diverges => divergence_reflected (encode_represents P) diverges

/-- **Property 5, success sensitiveness**, for every closed channel `ω`. -/
theorem encode_successSensitive {ω : G [] .nm} (closed : Closed ω) :
    SuccessSensitive (L := rhoCalculus ω) (M := stepCalculus ω) encode :=
  fun P => weak_barbs_agree (encode_represents P) closed

/-! ## Compositionality at the drop of a bound name -/

/-- `*y`: the drop of the name bound by the nearest input. -/
def dropBound : Pattern := .apply "PDrop" [.bvar 0]

theorem toTwin_dropBound :
    ByInstantiation.toTwin 1 .pr dropBound = some ByInstantiation.twinVar := rfl

theorem toTwin_boundName :
    ByInstantiation.toTwin 1 .nm (.bvar 0) = some ByInstantiation.nameVar := rfl

/-- **Read as one operator taking a name, the drop is not compositional.** A context of the twin
signature with a hole of sort name and a result of sort process has a former at its root (the hole
has the wrong sort to be the whole context, and a variable does not contain the hole), so filling it
never gives a variable. The translation of `*y` is the twin variable. So no such context computes the
translation of `*y` from the translation of `y`. -/
theorem drop_not_a_context
    (D : G (ByInstantiation.pairs 1) .nm → G (ByInstantiation.pairs 1) .pr)
    (former : ∀ n, ∃ f args, D n = Term.op (Sum.inl f) args) :
    ByInstantiation.toTwin 1 .pr dropBound ≠ (ByInstantiation.toTwin 1 .nm (.bvar 0)).map D := by
  rw [toTwin_dropBound, toTwin_boundName]
  intro same
  obtain ⟨f, args, at'⟩ := former ByInstantiation.nameVar
  have twins : (ByInstantiation.twinVar : G (ByInstantiation.pairs 1) .pr) = D ByInstantiation.nameVar :=
    Option.some.inj same
  rw [at'] at twins
  cases twins

/-! ## The correctness of one communication's contractum -/

/-- **The correctness of one communication's contractum, through the representation.** For a sealed
continuation `b` and a closed payload `q`: some closed process is the calculus's contractum (its
semantic substitution, modulo the equations), and every such process is translated to a state weakly
barbed bisimilar to the one-row state that the step's communication makes by instantiation,
`bind (received q) b`. Its one substitution is the communication's; it is not Gorla's Property 2,
whose renaming clause is not shown here. -/
theorem contractum_correct (b : G [.nm, .pr] .pr) (q : G [] .pr)
    (safeB : binderSafeAt "NQuote" 1 (read b) = true) (closedQ : Closed q) :
    (∃ R : RhoProcess, canonicalize R.1 =
        canonicalize (semanticCommSubst (canonicalize (read b)) (canonicalize (read q)))) ∧
      ∀ R : RhoProcess, canonicalize R.1 =
          canonicalize (semanticCommSubst (canonicalize (read b)) (canonicalize (read q))) →
        WeaklyBarbedBisimilar (single (bind (ByInstantiation.received q) b)) (encode R) := by
  have sealed := (ByInstantiation.instantiation_sealed b q safeB closedQ).2
  have canonical := ByInstantiation.contractum_by_instantiation_canonical b q safeB closedQ
  refine ⟨⟨ByInstantiation.rowProcess _ sealed, canonical⟩, fun R same => ?_⟩
  have rowRepresents : ByInstantiation.Represents (single (bind (ByInstantiation.received q) b)) R :=
    ⟨_, RepresentsBy.of_bag (ByInstantiation.initial_represents (ByInstantiation.rowProcess _ sealed) rfl)
      (congrArg Subtype.val ((fromProcess_eq_iff _ _).mpr (canonical.trans same.symm)))⟩
  exact weaklyBarbedBisimilar_of_represents rowRepresents (encode_represents R)

/-- **Name equivalence is respected**: outputs on name-equivalent closed channels are translated to
weakly barbed bisimilar states. -/
theorem name_equivalence_respected {c c' : G [] .nm} {p : G [] .pr}
    (closed : Closed (outputT c p)) (closed' : Closed (outputT c' p)) (similar : Similar c c') :
    WeaklyBarbedBisimilar (single (outputT c p)) (single (outputT c' p)) := by
  have same : canonicalize (read (outputT c p)) = canonicalize (read (outputT c' p)) := by
    rw [ByInstantiation.canonical_outputT, ByInstantiation.canonical_outputT,
      ByInstantiation.similar_canonical similar]
  refine weaklyBarbedBisimilar_of_represents
    ⟨_, ByInstantiation.initial_represents (ByInstantiation.rowProcess _ closed) rfl⟩
    ⟨_, RepresentsBy.of_bag (ByInstantiation.initial_represents (ByInstantiation.rowProcess _ closed') rfl)
      (congrArg Subtype.val ((fromProcess_eq_iff _ _).mpr same.symm))⟩

/-- **Control for the contractum**: ordinary substitution of the quote for the bound name, keeping
`*@Q` as a drop, does not give the calculus's contractum: on `for(y <- @0){*y} | @0!(@0!(0))` the
two contracta differ modulo the equations, and beside a receiver on `@0` the calculus's communicates
while the ordinary one is stuck (`Source.semantic_and_ordinary_differ`). -/
theorem ordinary_substitution_differs :
    canonicalize CanonicalReactionControls.payload ≠ canonicalize Source.ordinaryContractum ∧
      (∀ target, ¬ rhoLanguageDefGSLT.Step Source.stuckSource target) ∧
      rhoLanguageDefGSLT.Step (Source.afterwards.source CanonicalBag.empty)
        (Source.afterwards.target CanonicalBag.empty) :=
  ⟨Source.semantic_and_ordinary_differ.2.2.2.1, Source.semantic_and_ordinary_differ.2.2.2.2.2,
    Source.semantic_and_ordinary_differ.2.2.2.2.1⟩

/-! ## The single-row translation: valid, not homomorphic -/

/-- **The single-row translation meets Properties 3, 4 and 5.** -/
theorem encodeRow_valid {ω : G [] .nm} (closed : Closed ω) :
    OperationalCorrespondence (L := rhoCalculus ω) (M := stepCalculus ω) encodeRow ∧
      DivergenceReflecting (L := rhoCalculus ω) (M := stepCalculus ω) encodeRow ∧
      SuccessSensitive (L := rhoCalculus ω) (M := stepCalculus ω) encodeRow := by
  refine ⟨⟨fun P P' run => ?_, fun P T run => ?_⟩, fun P diverges => ?_, fun P => ?_⟩
  · obtain ⟨T, steps, represented⟩ := reaches_complete (encodeRow_represents P) run
    exact ⟨T, steps, weaklyBarbedBisimilar_of_represents represented (encodeRow_represents P')⟩
  · obtain ⟨P', steps, represented⟩ := reaches_sound (encodeRow_represents P) run
    exact ⟨P', steps, T, .refl, weaklyBarbedBisimilar_of_represents represented (encodeRow_represents P')⟩
  · exact divergence_reflected (encodeRow_represents P) diverges
  · exact weak_barbs_agree (encodeRow_represents P) closed

/-! ## Existence -/

/-- `@0!(0)` as a closed process. -/
def outputNil : RhoProcess := ByInstantiation.rowProcess ByInstantiation.outputZero (by decide)

/-- **A process that succeeds**: `@0!(0)` shows its output barb on `@0` at once. -/
theorem succeeds_output : (rhoCalculus ByInstantiation.nameZero).Succeeds outputNil := by
  refine ⟨outputNil, .refl, canonicalize (read (zeroT : G [] .pr)), ?_⟩
  have meaning : canonicalize (read ByInstantiation.outputZero) =
      output (canonicalize (read ByInstantiation.nameZero)) (canonicalize (read (zeroT : G [] .pr))) :=
    ByInstantiation.canonical_outputT _ _
  rw [fromProcess_primes]
  change output _ _ ∈ ReflectiveCalculus.primes (read ByInstantiation.outputZero)
  rw [ByInstantiation.primes_of_canonical_prime meaning
    (ByInstantiation.prime_output (by decide) meaning)]
  exact Multiset.mem_singleton_self _

/-- **A process that does not succeed**: `0` has no reduction and no barb. -/
theorem nil_not_succeeds (ω : G [] .nm) : ¬ (rhoCalculus ω).Succeeds nil := by
  rintro ⟨P, run, payload, member⟩
  rcases Relation.ReflTransGen.cases_head run with rfl | ⟨Q, step, _⟩
  · rw [fromProcess_primes] at member
    change _ ∈ ReflectiveCalculus.primes (.apply "PZero" []) at member
    rw [show ReflectiveCalculus.primes (.apply "PZero" []) = 0 from ReflectiveCalculus.primes_zero] at member
    exact Multiset.notMem_zero _ member
  · obtain ⟨rule, residue, source, _⟩ := (CanonicalReaction.publicStep_iff _ _).mp step
    have inside : CanonicalReaction.input rule.inputChannel rule.body ∈
        (CanonicalBag.append rule.redex residue).1 := by
      rw [CanonicalBag.append_inventory]
      exact Multiset.mem_add.mpr (.inl (by simp [CanonicalReaction.GroundComm.redex]))
    rw [← source, fromProcess_primes] at inside
    change _ ∈ ReflectiveCalculus.primes (.apply "PZero" []) at inside
    rw [show ReflectiveCalculus.primes (.apply "PZero" []) = 0 from ReflectiveCalculus.primes_zero] at inside
    exact Multiset.notMem_zero _ inside

/-! ## The first half -/

/-- **The reflective calculus into the step of the program: Definition 5.2 and Gorla's Properties 3
to 5.** For every closed channel `ω`, with success the output barb on `ω` on both sides, the
translation `encode` (a function on syntax) is homomorphic on parallel composition on the nose
(Definition 5.2), operationally corresponding up to weak barbed bisimilarity (Property 3), divergence
reflecting (Property 4) and success sensitive (Property 5); the step's equivalence respects success.
It is not compositional at output or input in Gorla's sense (`output_not_compositional`,
`input_not_compositional`): an input or an output is one row determined by the prefix
(`encode_input`, `encode_output`). Property 2 is not shown; what is shown is the correctness of one
communication's contractum (`contractum_correct`). Weak barbed bisimilarity is not a congruence for
the tensor (`not_congruence_represented`). -/
theorem rho_into_step {ω : G [] .nm} (closed : Closed ω) :
    Homomorphic (L := rhoCalculus ω) (M := stepCalculus ω) encode par tensor Eq ∧
      OperationalCorrespondence (L := rhoCalculus ω) (M := stepCalculus ω) encode ∧
      DivergenceReflecting (L := rhoCalculus ω) (M := stepCalculus ω) encode ∧
      SuccessSensitive (L := rhoCalculus ω) (M := stepCalculus ω) encode ∧
      (stepCalculus ω).SuccessRespecting :=
  ⟨encode_homomorphic ω, encode_operationalCorrespondence ω, encode_divergenceReflecting ω,
    encode_successSensitive closed, stepCalculus_successRespecting closed⟩

#print axioms stepCalculus_successRespecting
#print axioms encode_homomorphic
#print axioms encode_compositional_par
#print axioms encode_operationalCorrespondence
#print axioms encode_divergenceReflecting
#print axioms encode_successSensitive
#print axioms drop_not_a_context
#print axioms contractum_correct
#print axioms name_equivalence_respected
#print axioms ordinary_substitution_differs
#print axioms encodeRow_valid
#print axioms succeeds_output
#print axioms nil_not_succeeds
#print axioms rho_into_step

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings
