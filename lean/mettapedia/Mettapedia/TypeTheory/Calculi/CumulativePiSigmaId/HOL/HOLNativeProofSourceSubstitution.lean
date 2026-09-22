import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLNaturalDeductionNativeTranslation

/-!
# Source substitution and native proof compilation

Object substitution traverses the retained HOL proof, including its formula
annotations and witnesses. The native compiler follows that transformation
with the corresponding simultaneous substitution in its object environment.
This is distinct from moving an already-native environment by substitution.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLNativeProofSourceSubstitution

open Presentation Mettapedia.Logic HOL.UniformListInduction
open HOLNaturalDeductionNativeTranslation

def Compatible {gamma target : SourceContext}
    (theta : HOL.Subst Symbol gamma target)
    (raw : Sub Tower.Head gamma.length target.length) : Prop :=
  ∀ {type} (index : HOL.Var gamma type),
    represent (theta index) = some (raw (FormationSensitiveHOLInterface.variableIndex index))

theorem Compatible.lift {gamma target : SourceContext}
    {theta : HOL.Subst Symbol gamma target}
    {raw : Sub Tower.Head gamma.length target.length}
    (compatible : Compatible theta raw) (type : HOL.Ty BaseSort) :
    Compatible (HOL.Subst.lift (σ := type) theta) (liftSub raw) := by
  intro a index
  cases index with
  | vz => rfl
  | vs prior =>
      change represent (HOL.weaken (theta prior)) = _
      rw [represent_weaken, compatible prior]
      rfl

theorem represent_substitution {gamma target : SourceContext}
    {theta : HOL.Subst Symbol gamma target}
    {raw : Sub Tower.Head gamma.length target.length}
    (compatible : Compatible theta raw) {type : HOL.Ty BaseSort}
    (term : HOL.Term Symbol gamma type) :
    represent (HOL.subst theta term) = (represent term).map (subst raw) :=
  FormationSensitiveHOLInterface.represent_subst
    FormationSensitiveHOLUniformList.signature theta raw compatible term

theorem compile_transport {gamma : SourceContext}
    {delta other : List (Formula gamma)} {phi psi : Formula gamma}
    (assumptions : delta = other) (conclusion : phi = psi)
    (source : HOL.ProofSyntax Symbol delta phi) {n : Nat}
    (objects : Sub Tower.Head gamma.length n)
    (hypotheses : Fin other.length → Tower.Tm n) :
    compile (assumptions ▸ conclusion ▸ source) objects hypotheses =
      compile source objects (fun i => hypotheses (i.cast (congrArg List.length assumptions))) := by
  cases assumptions
  cases conclusion
  rfl

theorem compile_cast_assumptions {gamma : SourceContext}
    {delta other : List (Formula gamma)} {phi : Formula gamma}
    (equal : delta = other) (source : HOL.ProofSyntax Symbol delta phi) {n : Nat}
    (objects : Sub Tower.Head gamma.length n)
    (hypotheses : Fin other.length → Tower.Tm n) :
    compile (cast (congrArg (fun ds => HOL.ProofSyntax Symbol ds phi) equal) source)
      objects hypotheses =
      compile source objects (fun i => hypotheses (i.cast (congrArg List.length equal))) := by
  cases equal
  rfl

theorem compile_source_substitution {gamma : SourceContext}
    {delta : List (Formula gamma)} {phi : Formula gamma}
    (source : HOL.ProofSyntax Symbol delta phi)
    {target : SourceContext} (theta : HOL.Subst Symbol gamma target)
    (raw : Sub Tower.Head gamma.length target.length) (compatible : Compatible theta raw)
    {n : Nat} (objects : Sub Tower.Head target.length n)
    (hypotheses : Fin delta.length → Tower.Tm n) :
    compile (HOL.ProofSyntax.subst theta source) objects
        (fun i => hypotheses (i.cast (by simp))) =
      compile source (fun i => subst objects (raw i)) hypotheses := by
  induction source generalizing target n with
  | @hyp gamma delta occurrence =>
      have equal : (delta.map (HOL.subst theta)).get (occurrence.cast (by simp)) =
          HOL.subst theta (delta.get occurrence) := by simp
      change compile (cast (congrArg (HOL.ProofSyntax Symbol _) equal)
        (.hyp (occurrence.cast (by simp)))) objects _ = _
      erw [compile_cast_conclusion]
      all_goals first | exact equal | rfl
  | @impI gamma delta p q body ih =>
      simp only [HOL.ProofSyntax.subst, compile, represent_substitution compatible]
      have objects_lift :
          (fun i => subst (fun j => rename wk (objects j)) (raw i)) =
            (fun i => rename wk (subst objects (raw i))) := by
        funext i
        simp only [rename_subst]
      have hyp_lift :
          (fun i : Fin ((p :: delta).map (HOL.subst theta)).length =>
            @Fin.cases (delta.map (HOL.subst theta)).length (fun _ => Tower.Tm (n + 1))
              (.var 0) (fun j => rename wk (hypotheses (j.cast (by simp)))) i) =
          (fun i => @Fin.cases delta.length (fun _ => Tower.Tm (n + 1))
            (.var 0) (fun j => rename wk (hypotheses j))
            (i.cast (by simp))) := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i <;> rfl
      erw [hyp_lift]
      erw [ih theta raw compatible (fun i => rename wk (objects i))
        (Fin.cases (.var 0) (fun i => rename wk (hypotheses i)))]
      erw [objects_lift]
      cases represent p <;>
        cases compile body (fun i => rename wk (subst objects (raw i)))
          (Fin.cases (.var 0) (fun i => rename wk (hypotheses i))) <;> rfl
  | impE function argument ihf iha =>
      simp only [HOL.ProofSyntax.subst, compile]
      erw [ihf theta raw compatible objects hypotheses,
        iha theta raw compatible objects hypotheses]
  | @allI gamma delta type phi body ih =>
      have equal := HOL.ProofSyntax.subst_weakenHyps (A := type) theta delta
      change compile (.allI (cast (congrArg (fun ds => HOL.ProofSyntax Symbol ds
        (HOL.subst (HOL.Subst.lift theta) phi)) equal)
          (HOL.ProofSyntax.subst (HOL.Subst.lift theta) body))) objects _ = _
      simp only [compile]
      erw [compile_cast_assumptions]
      have object_lift : (fun i => subst (liftSub objects) (liftSub raw i)) =
          liftSub (fun i => subst objects (raw i)) := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i <;> simp [liftSub]
      have inner := ih (HOL.Subst.lift theta) (liftSub raw) (compatible.lift type)
        (liftSub objects) (fun i => rename wk (hypotheses (i.cast (by simp [HOL.weakenHyps]))))
      erw [object_lift] at inner
      erw [← inner]
      all_goals first | exact equal | rfl
  | @allE gamma delta type phi term function ih =>
      have equal := (HOL.ProofSyntax.subst_instantiate theta term phi).symm
      change compile (cast (congrArg (HOL.ProofSyntax Symbol _) equal)
        (.allE (HOL.subst theta term) (HOL.ProofSyntax.subst theta function))) objects _ = _
      erw [compile_cast_conclusion]
      · simp only [compile, represent_substitution compatible]
        erw [ih theta raw compatible objects hypotheses]
        cases represent term <;>
          cases compile function (fun i => subst objects (raw i)) hypotheses <;>
            simp [subst_comp]
      · exact equal
  | @beta gamma delta type result term body =>
      have equal := congrArg (HOL.Term.eq (HOL.subst theta (.app (.lam body) term)))
        (HOL.ProofSyntax.subst_instantiate theta term body).symm
      change compile (cast (congrArg (HOL.ProofSyntax Symbol _) equal)
        (.beta (HOL.subst theta term) (HOL.subst (HOL.Subst.lift theta) body))) objects _ = _
      erw [compile_cast_conclusion]
      all_goals first | exact equal | rfl
  | @eta gamma delta type result function =>
      have equal :
          HOL.Term.eq (.lam (.app (HOL.weaken (HOL.subst theta function)) (.var .vz)))
            (HOL.subst theta function) =
          HOL.subst theta (.eq (.lam (.app (HOL.weaken function) (.var .vz))) function) := by
        simp [HOL.subst, HOL.Subst.lift]
      change compile (cast (congrArg (HOL.ProofSyntax Symbol _) equal)
        (.eta (HOL.subst theta function))) objects _ = _
      erw [compile_cast_conclusion]
      all_goals first | exact equal | rfl
  | _ => rfl

theorem variableIndex_surjective (gamma : SourceContext) (i : Fin gamma.length) :
    ∃ type, ∃ index : HOL.Var gamma type,
      FormationSensitiveHOLInterface.variableIndex index = i := by
  induction gamma with
  | nil => exact Fin.elim0 i
  | cons type gamma ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · exact ⟨type, .vz, rfl⟩
      · obtain ⟨prior, index, equal⟩ := ih j
        exact ⟨prior, .vs index, congrArg Fin.succ equal⟩

/-- Represented source inputs supply the native context morphism; the
context-morphism law is proved from the inputs' actual typing. -/
theorem Compatible.objects {gamma target : SourceContext}
    {theta : HOL.Subst Symbol gamma target}
    {raw : Sub Tower.Head gamma.length target.length} (compatible : Compatible theta raw)
    {n : Nat} {context : Tower.Ctx n} {objects : Sub Tower.Head target.length n}
    (typed : NativeTyping.Objects context objects) :
    NativeTyping.Objects context (fun i => subst objects (raw i)) := by
  intro i
  obtain ⟨type, index, rfl⟩ := variableIndex_surjective gamma i
  have inputTyped := NativeTyping.represented_typed (compatible index) typed
  simpa only [FormationSensitiveHOLInterface.context_lookup,
    FormationSensitiveHOLInterface.typeAt_subst] using inputTyped

/-- Both routes preserve the native term and its represented conclusion,
with a complete formation-sensitive judgment in the caller's telescope. -/
theorem source_substitution_judgment {gamma : SourceContext}
    {delta : List (Formula gamma)} {phi : Formula gamma}
    (source : HOL.ProofSyntax Symbol delta phi)
    {target : SourceContext} (theta : HOL.Subst Symbol gamma target)
    (raw : Sub Tower.Head gamma.length target.length) (compatible : Compatible theta raw)
    {n : Nat} {context : Tower.Ctx n} {objects : Sub Tower.Head target.length n}
    {hypotheses : Fin delta.length → Tower.Tm n} {native : Tower.Tm n}
    (formed : FormationSensitive.ContextFormation FormationSensitiveHOLProofFamily.rules context)
    (objectTyped : NativeTyping.Objects context objects)
    (hypothesisTyped : NativeTyping.Hypotheses context
      (fun i => subst objects (raw i)) hypotheses)
    (compiled : compile source (fun i => subst objects (raw i)) hypotheses = some native) :
    ∃ code, represent phi = some code ∧
      represent (HOL.subst theta phi) = some (subst raw code) ∧
      compile (HOL.ProofSyntax.subst theta source) objects
        (fun i => hypotheses (i.cast (by simp))) = some native ∧
      FormationSensitive.Judgment FormationSensitiveHOLProofFamily.rules context native
        (FormationSensitiveHOLProofFamily.proof (subst objects (subst raw code))) := by
  obtain ⟨code, represented, judgment⟩ := NativeTyping.compile_judgment source formed
    (compatible.objects objectTyped) hypothesisTyped compiled
  refine ⟨code, represented, ?_, ?_, ?_⟩
  · rw [represent_substitution compatible, represented]
    rfl
  · exact (compile_source_substitution source theta raw compatible objects hypotheses).trans compiled
  · simpa only [subst_comp] using judgment

/-- Specialization of the retained source body agrees with beta reduction
of its compiled universal introduction, including under further binders. -/
theorem universal_cut_computes {gamma : SourceContext} {type : HOL.Ty BaseSort}
    {delta : List (Formula gamma)} {phi : Formula (type :: gamma)}
    (body : HOL.ProofSyntax Symbol (HOL.weakenHyps delta) phi)
    (term : HOL.Term Symbol gamma type) {code : Tower.Tm gamma.length}
    (represented : represent term = some code)
    {n : Nat} (objects : Sub Tower.Head gamma.length n)
    (hypotheses : Fin delta.length → Tower.Tm n) {nativeBody : Tower.Tm (n + 1)}
    (compiled : compile body (liftSub objects)
      (fun i => rename wk (hypotheses (i.cast (by simp [HOL.weakenHyps])))) = some nativeBody) :
    compile (HOL.ProofSyntax.subst (HOL.Subst.single term) body) objects
        (fun i => hypotheses (i.cast (by simp [HOL.weakenHyps]))) =
      some (inst0 (subst objects code) nativeBody) ∧
      Step FormationSensitiveHOLProofFamily.rules.headEq
        (.app (.lam nativeBody) (subst objects code))
        (inst0 (subst objects code) nativeBody) FormationSensitiveHOLProofFamily.rules.computation := by
  have compatible : Compatible (HOL.Subst.single term) (subst0 code) := by
    intro a index
    cases index with
    | vz => exact represented
    | vs prior => rfl
  have sourceMove := compile_source_substitution body (HOL.Subst.single term)
    (subst0 code) compatible objects
    (fun i => hypotheses (i.cast (by simp [HOL.weakenHyps])))
  have nativeMove := compile_substitute body (liftSub objects)
    (fun i => rename wk (hypotheses (i.cast (by simp [HOL.weakenHyps]))))
    (subst0 (subst objects code))
  have objectSquare :
      (fun i => subst (subst0 (subst objects code)) (liftSub objects i)) =
        (fun i => subst objects (subst0 code i)) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact inst0_rename_wk (subst objects code) (objects j)
  have hypothesisSquare :
      (fun i : Fin (HOL.weakenHyps (σ := type) delta).length =>
        subst (subst0 (subst objects code))
          (rename wk (hypotheses (i.cast (by simp [HOL.weakenHyps]))))) =
      (fun i => hypotheses (i.cast (by simp [HOL.weakenHyps]))) := by
    funext i
    exact inst0_rename_wk _ _
  erw [objectSquare, hypothesisSquare, compiled] at nativeMove
  exact ⟨sourceMove.trans nativeMove, .betaPi nativeBody (subst objects code)⟩

/-- The actual specialized source proof, compiled beta redex and contractum
share the represented conclusion and a complete native judgment. -/
theorem universal_cut_judgment {gamma : SourceContext} {type : HOL.Ty BaseSort}
    {delta : List (Formula gamma)} {phi : Formula (type :: gamma)}
    (body : HOL.ProofSyntax Symbol (HOL.weakenHyps delta) phi)
    (term : HOL.Term Symbol gamma type) {code : Tower.Tm gamma.length}
    (represented : represent term = some code)
    {n : Nat} {context : Tower.Ctx n} {objects : Sub Tower.Head gamma.length n}
    {hypotheses : Fin delta.length → Tower.Tm n} {nativeBody : Tower.Tm (n + 1)}
    (formed : FormationSensitive.ContextFormation FormationSensitiveHOLProofFamily.rules context)
    (objectTyped : NativeTyping.Objects context objects)
    (hypothesisTyped : NativeTyping.Hypotheses context objects hypotheses)
    (compiled : compile body (liftSub objects)
      (fun i => rename wk (hypotheses (i.cast (by simp [HOL.weakenHyps])))) = some nativeBody) :
    ∃ result, represent (HOL.instantiate term phi) = some result ∧
      compile (HOL.ProofSyntax.subst (HOL.Subst.single term) body) objects
        (fun i => hypotheses (i.cast (by simp [HOL.weakenHyps]))) =
          some (inst0 (subst objects code) nativeBody) ∧
      FormationSensitive.Judgment FormationSensitiveHOLProofFamily.rules context
        (.app (.lam nativeBody) (subst objects code))
        (FormationSensitiveHOLProofFamily.proof (subst objects result)) ∧
      Step FormationSensitiveHOLProofFamily.rules.headEq
        (.app (.lam nativeBody) (subst objects code))
        (inst0 (subst objects code) nativeBody) FormationSensitiveHOLProofFamily.rules.computation ∧
      FormationSensitive.Judgment FormationSensitiveHOLProofFamily.rules context
        (inst0 (subst objects code) nativeBody)
        (FormationSensitiveHOLProofFamily.proof (subst objects result)) := by
  obtain ⟨pc, representedBody, bodyTyped⟩ := NativeTyping.compile_typed body
    (objectTyped.lift type) (hypothesisTyped.lift type) compiled
  obtain ⟨before, step, after⟩ := FormationSensitiveHOLProofConversion.universal_beta_preserves
    (FormationSensitiveHOLProofFamily.simple_type_formed type context)
    (NativeTyping.represented_typed representedBody (objectTyped.lift type)) bodyTyped
    (NativeTyping.represented_typed represented objectTyped)
  refine ⟨inst0 code pc, ?_,
    (universal_cut_computes body term represented objects hypotheses compiled).1,
    ⟨formed, ?_⟩, step, ⟨formed, ?_⟩⟩
  · rw [represent_instantiate term phi represented, representedBody]
    rfl
  · simpa only [subst_inst0] using before
  · simpa only [subst_inst0] using after

namespace Controls

def identityAtVariable : HOL.ProofSyntax Symbol ([] : List (Formula [.prop]))
    (.imp (.var .vz) (.var .vz)) := implicationIdentity (.var .vz)

def identityWitness : HOL.Term Symbol [] (.arr .prop .prop) := .lam (.var .vz)

theorem source_specialization_retains_native_identity :
    compile (HOL.ProofSyntax.subst (HOL.Subst.single
      (HOL.Term.eq identityWitness identityWitness)) identityAtVariable)
      (n := 0) Fin.elim0 Fin.elim0 = some (.lam (.var 0)) := by
  obtain ⟨code, represented⟩ : ∃ code,
      represent (HOL.Term.eq identityWitness identityWitness) = some code := ⟨_, rfl⟩
  have compatible : Compatible
      (HOL.Subst.single (HOL.Term.eq identityWitness identityWitness)) (subst0 code) := by
    intro type index
    cases index with
    | vz => exact represented
    | vs prior => cases prior
  erw [compile_source_substitution identityAtVariable _ _ compatible Fin.elim0 Fin.elim0]
  rfl

/-- Replacing an object variable cannot turn an unsupported primitive
equality inference into a translated rule. -/
theorem substitution_does_not_add_equality_support :
    compile (HOL.ProofSyntax.subst (HOL.Subst.single identityWitness)
      (HOL.ProofSyntax.eqRefl (Const := Symbol) (Δ := [])
        (HOL.Term.var (Γ := [(.arr .prop .prop)]) .vz)))
      (n := 0) Fin.elim0 Fin.elim0 = none := rfl

end Controls

#print axioms Compatible.lift
#print axioms compile_source_substitution
#print axioms Compatible.objects
#print axioms source_substitution_judgment
#print axioms universal_cut_computes
#print axioms universal_cut_judgment
#print axioms Controls.source_specialization_retains_native_identity
#print axioms Controls.substitution_does_not_add_equality_support

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLNativeProofSourceSubstitution
