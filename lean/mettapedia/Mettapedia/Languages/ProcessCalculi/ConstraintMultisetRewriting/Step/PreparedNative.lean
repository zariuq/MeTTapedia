import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PreparedStep

/-!
# The native step, prepared: guarded native firings with disequations

The native step's result is the state the solver returns, published through the firing's recipes
(`Interface.native`, `Interface.publishedState`). That state is computed from the firing's data and
the solver's return alone (`ContextualConditionalExecution.Firing.target` does not read the
execution's admission); the solver returns a residual whenever the information is solvable.

## The prepared presentation (`nativePrepared`)

* **The preparation** (`Interface.NativePrep`, `Interface.nativePrepare`): the solver's residual
  return on the firing's information at its budget. A refutation would contradict solvability, so
  every ready firing with solvable information has one. No check and no predicate query is asked.
* **The structural effect** (`Interface.preparedState`, with `preparedTarget` and `preparedRows`):
  the formulas of the native execution's target and of its publication, read from the firing's data
  and the preparation; the native step's result is this same state.
* **It is the native step**: every part other than the result is the native step's own, admission is
  the native admission (`nativePrepared_admits_iff`), and on every admitted firing the prepared
  result is the native result by definition (`nativePrepared_result`).
* **Its settlement is the inclusion into the solver's active frame** (`inclusionExtension`,
  `includeSource_eq`), along which instantiation is injective (`includeSource_injective`): the native
  prepared settlement reflects the equivalence (`native_reflects`) and extends
  (`nativePrepared_extends`), so the prepared step covers its answers (`nativePrepared_coversAnswers`).

## Guarded native firings with disequations (`nativeGuarded`)

`Interface.Step.withDisequations` over the native step: native firings keep their checks and
predicate queries, asked at the solutions that separate the disequations
(`nativeGuarded_admits_iff`); the result is prepared without the native step's admission.
* **Conservative** (`nativeGuarded_conservative`, `nativeGuarded_result`): at a state without
  disequations, a firing that tells none is admitted exactly when the native step admits its base
  firing, and its result is the native result.
* **Firings without guards are a case of it** (`native_holds_without_guards`,
  `nativeGuarded_admits_iff_of_no_guards`): a native firing without checks and predicate queries is
  admitted with disequations exactly when it is ready and some solution of its information separates
  the disequations.
* **Answer coverage** (`nativeGuarded_coversAnswers`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PreparedStep

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Interface (Frames NativeState NativeFiring native NativePrep nativePrepare preparedState)
open SettlementCoverage (Extends CoversAnswers extension_extends)

/-! ## The inclusion into the solver's active frame -/

section Inclusion

variable {S : Signature}

/-- The inclusion of a source family into an active family, as an injective extension. -/
def inclusionExtension {V W : Type} (source : V → MetaArity S) (returned : W → MetaArity S) :
    ContextualGuardMatching.Extension source :=
  ⟨V ⊕ (W ⊕ Empty), ContextualComputedFreshFrame.active source returned, Sum.inl, Sum.inl_injective,
    fun _ => rfl⟩

/-- **The inclusion of the information frame is that extension's assignment.** -/
theorem includeSource_eq {V : Type} {source : V → MetaArity S} {problem : ContextualResidual.Problem source}
    (update : ContextualFrameUpdate.Update problem) :
    ContextualComputedFreshFrame.includeSource update = (inclusionExtension source update.declaration).assignment := by
  funext v
  show instantiate (ContextualFreshFrame.includeOld source update.declaration
      ContextualComputedFreshFrame.noDeclarations)
      (generator (ContextualComputedFreshFrame.old source) (.inl v)) = _
  rw [instantiate_generator]
  rfl

/-- **Instantiation along the inclusion is injective on observations.** -/
theorem includeSource_injective {V : Type} {source : V → MetaArity S}
    {problem : ContextualResidual.Problem source} (update : ContextualFrameUpdate.Update problem)
    {u v : Observation S source}
    (same : instantiateObservation (ContextualComputedFreshFrame.includeSource update) u =
      instantiateObservation (ContextualComputedFreshFrame.includeSource update) v) : u = v := by
  rw [includeSource_eq] at same
  obtain ⟨Γ, sort, t⟩ := u
  obtain ⟨Γ', sort', t'⟩ := v
  change (⟨Γ, sort, instantiate (inclusionExtension source update.declaration).assignment t⟩ :
      Observation S (inclusionExtension source update.declaration).declarations) =
    ⟨Γ', sort', instantiate (inclusionExtension source update.declaration).assignment t'⟩ at same
  have contexts : Γ = Γ' := congrArg Sigma.fst same
  subst contexts
  have inner := eq_of_heq (Sigma.mk.inj same).2
  have sorts : sort = sort' := congrArg Sigma.fst inner
  subst sorts
  have terms := eq_of_heq (Sigma.mk.inj inner).2
  have equal := ContextualGuardMatching.Extension.instantiate_injective _ terms
  subst equal
  rfl

end Inclusion

variable {S : Signature} {O : Type} [DecidableEq O] {Γ : Ctx S} {sort : S.Srt}
  [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

/-- **The native prepared settlement reflects the equivalence**: it is the inclusion of the
information frame into the solver's active frame. -/
theorem native_reflects : (native (S := S) (O := O) (Γ := Γ) (sort := sort)).Reflects :=
  fun _ p _ _ same => includeSource_injective (nativePrepare _ p.2.2).1 same

/-- **A native firing without checks and predicate queries holds at every solution.** -/
theorem native_holds_without_guards {s : NativeState S O Γ sort} (f : NativeFiring s)
    (noChecks : f.prepared.rule.checks = []) (noQueries : f.queries = []) (b : Interface.Frames.Frame S)
    (g : Assignment s.infoFrame.arity b.arity) : native.Holds f b g :=
  ⟨fun _ member => absurd (noChecks ▸ member) List.not_mem_nil,
    fun _ member => absurd (noQueries ▸ member) List.not_mem_nil⟩

variable (S O Γ sort) in
/-- **The native step, prepared**: the native step's own parts, with the result prepared by the
solver's return. -/
def nativePrepared :
    Prepared.{_, _, _, _, _, _, 2} (Frames.contextual S) O (NativeState S O Γ sort) NativeFiring where
  frame := native.frame
  knowledge := native.knowledge
  present := native.present
  selection := native.selection
  target := native.target
  extension := native.extension
  information := native.information
  transported := native.transported
  Shapes := native.Shapes
  Holds := native.Holds
  Prep f := NativePrep f
  prepare f _ _ solvable := nativePrepare f solvable
  result f p := preparedState f p
  present_result _ _ := rfl
  settle _ p := ContextualComputedFreshFrame.includeSource p.1
  knowledge_result _ _ := rfl

/-- **Admission of the prepared native step is native admission.** -/
theorem nativePrepared_admits_iff {s : NativeState S O Γ sort} (f : NativeFiring s) :
    (nativePrepared S O Γ sort).step.Admits f ↔ native.Admits f :=
  (native.admits_iff f).symm

/-- **On every admitted firing the prepared result is the native result**, by definition: the native
step pins the execution of the firing's own data and the solver's return. -/
theorem nativePrepared_result {s : NativeState S O Γ sort} (f : NativeFiring s) (realized : native.Admits f) :
    (nativePrepared S O Γ sort).step.result f ((nativePrepared_admits_iff f).mpr realized) =
      native.result f realized :=
  rfl

/-- **The prepared native settlement extends.** -/
theorem nativePrepared_extends {s : NativeState S O Γ sort} (f : NativeFiring s) (p : NativePrep f) :
    Extends (Frames.contextual S) ((nativePrepared S O Γ sort).settle f p) := by
  intro b σ
  obtain ⟨c, j, τ, faithful, agree⟩ := extension_extends
    (inclusionExtension (ContextualActivatedStep.target s.locals s.state.declarations) p.1.declaration) σ
  refine ⟨c, j, τ, faithful, fun t => ?_⟩
  have square := agree t
  rw [← includeSource_eq p.1] at square
  exact square

/-- **The prepared native step covers its answers.** -/
theorem nativePrepared_coversAnswers : CoversAnswers (nativePrepared S O Γ sort).step.toStep := by
  apply Prepared.step_coversAnswers
  intro _ f p
  exact nativePrepared_extends f p

variable (S O Γ sort) in
/-- **Guarded native firings with disequations**: the native step over disequation frames. -/
abbrev nativeGuarded :=
  (native (S := S) (O := O) (Γ := Γ) (sort := sort)).withDisequations native_reflects

/-- **Admission of guarded native firings with disequations**: the shapes, the physical enabling, a
solution of the information that separates the disequations, and the native checks and predicate
queries at every such solution. -/
theorem nativeGuarded_admits_iff {s : (native (S := S) (O := O) (Γ := Γ) (sort := sort)).DState}
    (f : native.DFiring s) :
    (nativeGuarded S O Γ sort).Admits f ↔ native.Shapes f.base ∧
      Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Enabled (fun _ : O => ())
        (native.present s.state) ((native.selection f.base).commit (T := Unit)) ∧
      (∃ (b : Interface.Frames.Frame S) (g : Assignment s.state.infoFrame.arity b.arity),
        (Frames.contextual S).Models (a := s.state.infoFrame) g f.base.information ∧
        DisequalityFrames.Separates (Frames.contextual S) (a := s.state.infoFrame) g
          (native.carried s f.base ++ f.tells)) ∧
      ∀ (b : Interface.Frames.Frame S) (g : Assignment s.state.infoFrame.arity b.arity),
        (Frames.contextual S).Models (a := s.state.infoFrame) g f.base.information →
        DisequalityFrames.Separates (Frames.contextual S) (a := s.state.infoFrame) g
          (native.carried s f.base ++ f.tells) → native.Holds f.base b g :=
  Interface.Step.admits_iff_separating native_reflects f

/-- **Conservative over the native step**: at a state without disequations, a firing that tells
none is admitted exactly when the native step admits its base firing. -/
theorem nativeGuarded_conservative {s : (native (S := S) (O := O) (Γ := Γ) (sort := sort)).DState}
    (f : native.DFiring s) (empty : s.disequations = []) (silent : f.tells = []) :
    (nativeGuarded S O Γ sort).Admits f ↔ native.Admits f.base :=
  Interface.Step.conservative native_reflects f empty silent

/-- **With the native result.** -/
theorem nativeGuarded_result {s : (native (S := S) (O := O) (Γ := Γ) (sort := sort)).DState}
    (f : native.DFiring s) (admitted : (nativeGuarded S O Γ sort).Admits f)
    (realized : native.Admits f.base) :
    ((nativeGuarded S O Γ sort).result f admitted).state = native.result f.base realized :=
  Interface.Step.conservative_result native_reflects f admitted realized

/-- **A firing without guards is admitted with disequations exactly when it is ready and some
solution of its information separates the disequations.** -/
theorem nativeGuarded_admits_iff_of_no_guards {s : (native (S := S) (O := O) (Γ := Γ) (sort := sort)).DState}
    (f : native.DFiring s)
    (noChecks : f.base.prepared.rule.checks = []) (noQueries : f.base.queries = []) :
    (nativeGuarded S O Γ sort).Admits f ↔ native.Shapes f.base ∧
      Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Enabled (fun _ : O => ())
        (native.present s.state) ((native.selection f.base).commit (T := Unit)) ∧
      ∃ (b : Interface.Frames.Frame S) (g : Assignment s.state.infoFrame.arity b.arity),
        (Frames.contextual S).Models (a := s.state.infoFrame) g f.base.information ∧
        DisequalityFrames.Separates (Frames.contextual S) (a := s.state.infoFrame) g
          (native.carried s f.base ++ f.tells) := by
  rw [nativeGuarded_admits_iff]
  constructor
  · rintro ⟨shapes, enabled, solvable, -⟩
    exact ⟨shapes, enabled, solvable⟩
  · rintro ⟨shapes, enabled, solvable⟩
    exact ⟨shapes, enabled, solvable, fun b g _ _ => native_holds_without_guards f.base noChecks noQueries b g⟩

/-- **Guarded native firings with disequations cover their answers.** -/
theorem nativeGuarded_coversAnswers : CoversAnswers (nativeGuarded S O Γ sort) := by
  apply SettlementCoverage.withDisequations_coversAnswers
  intro _ f p
  exact nativePrepared_extends f (nativePrepare f p.2.2)

#print axioms includeSource_eq
#print axioms includeSource_injective
#print axioms native_reflects
#print axioms native_holds_without_guards
#print axioms nativePrepared_admits_iff
#print axioms nativePrepared_result
#print axioms nativePrepared_extends
#print axioms nativePrepared_coversAnswers
#print axioms nativeGuarded_admits_iff
#print axioms nativeGuarded_conservative
#print axioms nativeGuarded_result
#print axioms nativeGuarded_admits_iff_of_no_guards
#print axioms nativeGuarded_coversAnswers

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PreparedStep
