import Mettapedia.Languages.MM0.Upstream.Lean3Dependencies
import Mettapedia.Languages.MM0.Presentation.InstantiationCorrespondence

/-!
# The pinned MM0 substitution-safety account

`historicalSafeSubst` adapts `safe_subst` at lines 206--211 of
`mm0-lean/mm0/mm0.lean`, revision
`6d5f0d4fae8e2e3ae0b998bcbaa9d059cad99fad`:
https://github.com/digama0/mm0/blob/6d5f0d4fae8e2e3ae0b998bcbaa9d059cad99fad/mm0-lean/mm0/mm0.lean

That definition uses the target context both to select formal independence
and to inspect replacement expressions. `specifiedSafeSubst` separates those
contexts. The historical account is compared only on its proved compatibility
domain; a distinct-context separator remains explicit.

These are logical predicates, connected to the existing independent and
authored computations. No additional executable checker is introduced.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Upstream.Lean3Admissibility

open Lean3Typing Lean3Typing.Reference
open Mettapedia.GSLT.LanguageDef.DeterministicEquations (Applies computationalHost)

namespace Reference

/-- The pinned one-context safety condition, with its original selectors. -/
def historicalSafeSubst (context : Context) (images : List SExpr) : Prop :=
  ∀ source other, (∃ sort, context[source]? = some (.bound sort)) →
    other < context.length → ¬ Lean3Dependencies.Reference.hasVar context (.var other) source →
    ∀ image expression, images[source]? = some (.var image) → images[other]? = some expression →
      ¬ Lean3Dependencies.Reference.hasVar context expression image

/-- Formal independence is selected in `formal`; images are observed in `target`. -/
def specifiedSafeSubst (formal target : Context) (images : List SExpr) : Prop :=
  ∀ source other, (∃ sort, formal[source]? = some (.bound sort)) →
    other < formal.length → ¬ Lean3Dependencies.Reference.hasVar formal (.var other) source →
    ∀ image expression, images[source]? = some (.var image) → images[other]? = some expression →
      ¬ Lean3Dependencies.Reference.hasVar target expression image

theorem historical_same_context (context : Context) (images : List SExpr) :
    historicalSafeSubst context images ↔ specifiedSafeSubst context context images := Iff.rfl

end Reference

/-- The indexed upstream-style condition and the independent matrix quantify
the same ordered pairs. This law requires no presumed matrix success. -/
theorem specified_matrix_iff (formal target : Kernel.Context) (images : List Kernel.Preterm) :
    Reference.specifiedSafeSubst (ofContext formal) (ofContext target) (images.map SExpr.ofKernel) ↔
      ∀ entry ∈ Kernel.Substitution.entries formal images,
        Kernel.Substitution.RowIndependent target (Kernel.Substitution.entries formal images) entry := by
  constructor
  · intro safe entry member
    rcases entry with ⟨⟨binder, expression⟩, source⟩
    have entryLookup : formal[source]? = some binder ∧ images[source]? = some expression := by
      simpa only [Kernel.Substitution.entries, List.mem_zipIdx_iff_getElem?,
        List.getElem?_zip_eq_some] using member
    intro sort image entryEq other otherMember independent
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj entryEq
    rcases other with ⟨⟨otherBinder, otherExpression⟩, position⟩
    have otherLookup : formal[position]? = some otherBinder ∧
        images[position]? = some otherExpression := by
      simpa only [Kernel.Substitution.entries, List.mem_zipIdx_iff_getElem?,
        List.getElem?_zip_eq_some] using otherMember
    have bounded : position < (ofContext formal).length := by
      simpa only [ofContext, List.length_map] using (List.getElem?_eq_some_iff.mp otherLookup.1).1
    have formalIndependent : ¬ Lean3Dependencies.Reference.hasVar (ofContext formal) (.var position) source := by
      intro occurs
      exact independent ((Kernel.Binder.dependsOn_iff_hasVar otherLookup.1).mpr
        ((Lean3Dependencies.hasVar_ofKernel_iff formal (.var position) source).mp occurs))
    have imageLookup : (images.map SExpr.ofKernel)[source]? = some (.var image) :=
      (Lean3Dependencies.translated_argument_var_iff images source image).mpr entryLookup.2
    have expressionLookup : (images.map SExpr.ofKernel)[position]? = some (SExpr.ofKernel otherExpression) := by
      rw [List.getElem?_map, otherLookup.2]
      rfl
    have excluded := safe source position ⟨sort, ofContext_lookup entryLookup.1⟩ bounded
      formalIndependent image (SExpr.ofKernel otherExpression) imageLookup expressionLookup
    intro occurs
    exact excluded ((Lean3Dependencies.hasVar_ofKernel_iff target otherExpression image).mpr occurs)
  · intro rows source position declared bounded independent image expression imageLookup expressionLookup
    obtain ⟨sort, bound⟩ := declared
    have formalBound : formal[source]? = some (.bound sort) := by
      simpa only [toContext_ofContext, Binder.toKernel] using toContext_lookup bound
    have bounded' : position < formal.length := by simpa only [ofContext, List.length_map] using bounded
    let binder : Kernel.Binder := formal[position]'bounded'
    have formalOther : formal[position]? = some binder :=
      List.getElem?_eq_some_iff.mpr ⟨bounded', rfl⟩
    have sourceImage : images[source]? = some (.var image) :=
      (Lean3Dependencies.translated_argument_var_iff images source image).mp imageLookup
    rw [List.getElem?_map] at expressionLookup
    obtain ⟨otherExpression, otherImage, rfl⟩ := Option.map_eq_some_iff.mp expressionLookup
    have sourceMember : ((.bound sort, .var image), source) ∈ Kernel.Substitution.entries formal images := by
      simp [Kernel.Substitution.entries, List.mem_zipIdx_iff_getElem?,
        List.getElem?_zip_eq_some, formalBound, sourceImage]
    have otherMember : ((binder, otherExpression), position) ∈ Kernel.Substitution.entries formal images := by
      simp [Kernel.Substitution.entries, List.mem_zipIdx_iff_getElem?,
        List.getElem?_zip_eq_some, formalOther, otherImage]
    have localIndependent : ¬ binder.DependsOn position source := by
      intro depends
      exact independent ((Lean3Dependencies.hasVar_ofKernel_iff formal (.var position) source).mpr
        ((Kernel.Binder.dependsOn_iff_hasVar formalOther).mp depends))
    have excluded := rows _ sourceMember sort image rfl _ otherMember localIndependent
    intro occurs
    exact excluded ((Lean3Dependencies.hasVar_ofKernel_iff target otherExpression image).mp occurs)

theorem fits_vector_iff {environment : Env} {theory : Kernel.Theory}
    (related : EnvironmentRelated environment theory) (formal target : Kernel.Context)
    (images : List Kernel.Preterm) :
    List.Forall₂ (FitsBinder environment (ofContext target)) (images.map SExpr.ofKernel) (ofContext formal) ↔
      List.Forall₂ (Kernel.Preterm.FitsBinder theory.termSignature target) images formal := by
  induction images generalizing formal with
  | nil => cases formal <;> simp [ofContext]
  | cons expression images ih =>
      cases formal with
      | nil => simp [ofContext]
      | cons binder formal =>
          rw [show ofContext (binder :: formal) = Binder.ofKernel binder :: ofContext formal from rfl]
          simp only [List.map_cons, List.forall₂_cons]
          rw [fitsBinder_iff related]
          simp only [toContext_ofContext, SExpr.toKernel_ofKernel, Binder.toKernel_ofKernel]
          exact and_congr Iff.rfl (ih formal)

/-- Both binder-fit and independence are retained; safety alone does not
authorize an image vector of the wrong length or type. -/
theorem admissible_iff {environment : Env} {theory : Kernel.Theory}
    (related : EnvironmentRelated environment theory) (formal target : Kernel.Context)
    (images : List Kernel.Preterm) :
    Kernel.Substitution.Admissible theory.termSignature formal target images ↔
      List.Forall₂ (FitsBinder environment (ofContext target)) (images.map SExpr.ofKernel) (ofContext formal) ∧
        Reference.specifiedSafeSubst (ofContext formal) (ofContext target) (images.map SExpr.ofKernel) := by
  rw [fits_vector_iff related, specified_matrix_iff]
  exact ⟨fun admitted => ⟨admitted.typed, admitted.independent⟩,
    fun ⟨typed, independent⟩ => ⟨typed, independent⟩⟩

namespace Reference

theorem formal_occurrence_in_extension (formal suffix : Context) (position index : Nat)
    (bounded : position < formal.length) :
    Lean3Dependencies.Reference.hasVar (formal ++ suffix) (.var position) index ↔
      Lean3Dependencies.Reference.hasVar formal (.var position) index := by
  simp only [Lean3Dependencies.Reference.hasVar, List.getElem?_append_left bounded]

/-- This compatibility condition is about real context positions, not assumed
agreement of safety judgments. Images past the formal prefix are excluded. -/
theorem historical_prefix_iff (formal suffix : Context) (images : List SExpr)
    (bounded : images.length ≤ formal.length) :
    historicalSafeSubst (formal ++ suffix) images ↔
      specifiedSafeSubst formal (formal ++ suffix) images := by
  constructor
  · intro historical source other declared inFormal independent image expression sourceImage otherImage
    obtain ⟨sort, known⟩ := declared
    have sourceBounded := (List.getElem?_eq_some_iff.mp known).1
    have declared' : (formal ++ suffix)[source]? = some (.bound sort) := by
      rw [List.getElem?_append_left sourceBounded]
      exact known
    have inTarget : other < (formal ++ suffix).length := by simp only [List.length_append]; omega
    have independent' : ¬ Lean3Dependencies.Reference.hasVar (formal ++ suffix) (.var other) source :=
      fun occurs => independent ((formal_occurrence_in_extension formal suffix other source inFormal).mp occurs)
    exact historical source other ⟨sort, declared'⟩ inTarget independent' image expression sourceImage otherImage
  · intro specified source other declared _ independent image expression sourceImage otherImage
    obtain ⟨sort, known⟩ := declared
    have sourceBounded : source < formal.length :=
      Nat.lt_of_lt_of_le (List.getElem?_eq_some_iff.mp sourceImage).1 bounded
    have otherBounded : other < formal.length :=
      Nat.lt_of_lt_of_le (List.getElem?_eq_some_iff.mp otherImage).1 bounded
    have declared' : formal[source]? = some (.bound sort) := by
      simpa only [List.getElem?_append_left sourceBounded] using known
    have independent' : ¬ Lean3Dependencies.Reference.hasVar formal (.var other) source :=
      fun occurs => independent ((formal_occurrence_in_extension formal suffix other source otherBounded).mpr occurs)
    exact specified source other ⟨sort, declared'⟩ otherBounded independent' image expression sourceImage otherImage

end Reference

/-- Exact compatibility on a formal context extended by extra target binders.
The fits vector discharges the image bound; it is not inferred from safety. -/
theorem admissible_historical_prefix_iff {environment : Env} {theory : Kernel.Theory}
    (related : EnvironmentRelated environment theory) (formal suffix : Kernel.Context)
    (images : List Kernel.Preterm) :
    Kernel.Substitution.Admissible theory.termSignature formal (formal ++ suffix) images ↔
      List.Forall₂ (FitsBinder environment (ofContext (formal ++ suffix)))
        (images.map SExpr.ofKernel) (ofContext formal) ∧
      Reference.historicalSafeSubst (ofContext (formal ++ suffix)) (images.map SExpr.ofKernel) := by
  rw [admissible_iff related]
  constructor
  · rintro ⟨typed, specified⟩
    have bounded : (images.map SExpr.ofKernel).length ≤ (ofContext formal).length := by
      exact Nat.le_of_eq typed.length_eq
    have compatible := Reference.historical_prefix_iff (ofContext formal) (ofContext suffix)
      (images.map SExpr.ofKernel) bounded
    exact ⟨typed, by
      simpa only [ofContext, List.map_append] using compatible.mpr (by
        simpa only [ofContext, List.map_append] using specified)⟩
  · rintro ⟨typed, historical⟩
    have bounded : (images.map SExpr.ofKernel).length ≤ (ofContext formal).length :=
      Nat.le_of_eq typed.length_eq
    have compatible := Reference.historical_prefix_iff (ofContext formal) (ofContext suffix)
      (images.map SExpr.ofKernel) bounded
    exact ⟨typed, by
      simpa only [ofContext, List.map_append] using compatible.mp (by
        simpa only [ofContext, List.map_append] using historical)⟩

theorem checked_run_admissible_iff {theory : Kernel.Theory} {admissions : List Kernel.Admission}
    (checked : Kernel.Theory.run? {} admissions = some theory) (formal target : Kernel.Context)
    (images : List Kernel.Preterm) :
    Kernel.Substitution.Admissible theory.termSignature formal target images ↔
      List.Forall₂ (FitsBinder (projectRun admissions) (ofContext target))
        (images.map SExpr.ofKernel) (ofContext formal) ∧
      Reference.specifiedSafeSubst (ofContext formal) (ofContext target) (images.map SExpr.ofKernel) :=
  admissible_iff (checked_run_environment_related checked) formal target images

theorem checked_run_authored_accepts_iff {theory : Kernel.Theory} {admissions : List Kernel.Admission}
    (checked : Kernel.Theory.run? {} admissions = some theory) (formal target : Kernel.Context)
    (images : List Kernel.Preterm) :
    Applies Presentation.ComputationalAdmissible.admissibleProgram computationalHost "mm0:check-admissible"
      [Presentation.ComputationalTyping.encodeTable theory.terms,
        Presentation.ComputationalContext.encodeContext formal,
        Presentation.ComputationalContext.encodeContext target,
        Presentation.ComputationalArguments.encodeExpressions images] (.sym "True") ↔
      List.Forall₂ (FitsBinder (projectRun admissions) (ofContext target))
        (images.map SExpr.ofKernel) (ofContext formal) ∧
      Reference.specifiedSafeSubst (ofContext formal) (ofContext target) (images.map SExpr.ofKernel) := by
  rw [Presentation.ComputationalAdmissible.admissible_accepts_iff,
    Presentation.ComputationalTyping.theory_signature, checked_run_admissible_iff checked]

/-- Completed logical refusal, not absence of a computation budget. -/
theorem checked_run_authored_refuses_iff {theory : Kernel.Theory} {admissions : List Kernel.Admission}
    (checked : Kernel.Theory.run? {} admissions = some theory) (formal target : Kernel.Context)
    (images : List Kernel.Preterm) :
    Applies Presentation.ComputationalAdmissible.admissibleProgram computationalHost "mm0:check-admissible"
      [Presentation.ComputationalTyping.encodeTable theory.terms,
        Presentation.ComputationalContext.encodeContext formal,
        Presentation.ComputationalContext.encodeContext target,
        Presentation.ComputationalArguments.encodeExpressions images] (.sym "False") ↔
      ¬ (List.Forall₂ (FitsBinder (projectRun admissions) (ofContext target))
          (images.map SExpr.ofKernel) (ofContext formal) ∧
        Reference.specifiedSafeSubst (ofContext formal) (ofContext target) (images.map SExpr.ofKernel)) := by
  rw [Presentation.ComputationalAdmissible.admissible_refuses_iff,
    Presentation.ComputationalTyping.theory_signature, checked_run_admissible_iff checked]

/-- The submitted result is retained along with binder fit, independence and
the precise substitution domain. No independently derivable result can repair
a missing or capturing image. -/
theorem checked_run_authored_instantiation_iff {theory : Kernel.Theory} {admissions : List Kernel.Admission}
    (checked : Kernel.Theory.run? {} admissions = some theory) (formal target : Kernel.Context)
    (images : List Kernel.Preterm) (body result : Kernel.Preterm) :
    Applies Presentation.ComputationalInstantiation.instantiationProgram computationalHost "mm0:instantiate-term"
      [Presentation.ComputationalTyping.encodeTable theory.terms,
        Presentation.ComputationalContext.encodeContext formal,
        Presentation.ComputationalContext.encodeContext target,
        Presentation.ComputationalArguments.encodeExpressions images, Presentation.encode body]
      (Presentation.encodeResult (some result)) ↔
      (List.Forall₂ (FitsBinder (projectRun admissions) (ofContext target))
          (images.map SExpr.ofKernel) (ofContext formal) ∧
        Reference.specifiedSafeSubst (ofContext formal) (ofContext target) (images.map SExpr.ofKernel)) ∧
      (Lean3Dependencies.Reference.withinImages images.length (SExpr.ofKernel body) ∧
        Lean3Dependencies.Reference.substitute (images.map SExpr.ofKernel) (SExpr.ofKernel body) =
          SExpr.ofKernel result) := by
  rw [Presentation.ComputationalInstantiation.instantiation_accepts_iff,
    Presentation.ComputationalTyping.theory_signature, checked_run_admissible_iff checked,
    ← Kernel.Preterm.substitute_eq_some_iff, Lean3Dependencies.substitution_iff]

theorem checked_run_authored_instantiation_refuses_iff {theory : Kernel.Theory}
    {admissions : List Kernel.Admission} (checked : Kernel.Theory.run? {} admissions = some theory)
    (formal target : Kernel.Context) (images : List Kernel.Preterm) (body : Kernel.Preterm) :
    Applies Presentation.ComputationalInstantiation.instantiationProgram computationalHost "mm0:instantiate-term"
      [Presentation.ComputationalTyping.encodeTable theory.terms,
        Presentation.ComputationalContext.encodeContext formal,
        Presentation.ComputationalContext.encodeContext target,
        Presentation.ComputationalArguments.encodeExpressions images, Presentation.encode body] (.sym "None") ↔
      ¬ (List.Forall₂ (FitsBinder (projectRun admissions) (ofContext target))
          (images.map SExpr.ofKernel) (ofContext formal) ∧
        Reference.specifiedSafeSubst (ofContext formal) (ofContext target) (images.map SExpr.ofKernel)) ∨
      ¬ Lean3Dependencies.Reference.withinImages images.length (SExpr.ofKernel body) := by
  rw [Presentation.ComputationalInstantiation.instantiation_refuses_iff,
    Presentation.ComputationalTyping.theory_signature]
  cases decision : Kernel.Substitution.checkAdmissible theory.termSignature formal target images with
  | false =>
      have refused : ¬ Kernel.Substitution.Admissible theory.termSignature formal target images := by
        intro admitted
        have yes := (Kernel.Substitution.checkAdmissible_iff _ _ _ _).mpr admitted
        simp [decision] at yes
      have refused' := fun h => refused ((checked_run_admissible_iff checked formal target images).mpr h)
      simp only [Kernel.Substitution.instantiate, decision, Bool.false_eq_true, ↓reduceIte]
      exact ⟨fun _ => .inl refused', fun _ => trivial⟩
  | true =>
      have admitted := (Kernel.Substitution.checkAdmissible_iff _ _ _ _).mp decision
      have admitted' := (checked_run_admissible_iff checked formal target images).mp admitted
      simp only [Kernel.Substitution.instantiate, decision, ↓reduceIte]
      constructor
      · intro missing
        exact .inr ((Lean3Dependencies.substitution_refuses_iff images body).mp missing)
      · rintro (refused | missing)
        · exact False.elim (refused admitted')
        · exact (Lean3Dependencies.substitution_refuses_iff images body).mpr missing

/-- A concrete compatibility instance with the actual checked-store relation.
This does not claim that every theorem application has a prefix target. -/
theorem checked_run_authored_historical_prefix_iff {theory : Kernel.Theory}
    {admissions : List Kernel.Admission} (checked : Kernel.Theory.run? {} admissions = some theory)
    (formal suffix : Kernel.Context) (images : List Kernel.Preterm) :
    Applies Presentation.ComputationalAdmissible.admissibleProgram computationalHost "mm0:check-admissible"
      [Presentation.ComputationalTyping.encodeTable theory.terms,
        Presentation.ComputationalContext.encodeContext formal,
        Presentation.ComputationalContext.encodeContext (formal ++ suffix),
        Presentation.ComputationalArguments.encodeExpressions images] (.sym "True") ↔
      List.Forall₂ (FitsBinder (projectRun admissions) (ofContext (formal ++ suffix)))
        (images.map SExpr.ofKernel) (ofContext formal) ∧
      Reference.historicalSafeSubst (ofContext (formal ++ suffix)) (images.map SExpr.ofKernel) := by
  rw [Presentation.ComputationalAdmissible.admissible_accepts_iff,
    Presentation.ComputationalTyping.theory_signature,
    admissible_historical_prefix_iff (checked_run_environment_related checked)]

theorem checked_run_typed_instantiation_defined {theory : Kernel.Theory} {admissions : List Kernel.Admission}
    (checked : Kernel.Theory.run? {} admissions = some theory) {formal target remaining : Kernel.Context}
    {images : List Kernel.Preterm} {body : Kernel.Preterm} {sort : Nat}
    (typed : Typed (projectRun admissions) (ofContext formal) (SExpr.ofKernel body) (ofContext remaining) sort)
    (fits : List.Forall₂ (FitsBinder (projectRun admissions) (ofContext target))
      (images.map SExpr.ofKernel) (ofContext formal))
    (safe : Reference.specifiedSafeSubst (ofContext formal) (ofContext target) (images.map SExpr.ofKernel)) :
    ∃ result, Applies Presentation.ComputationalInstantiation.instantiationProgram computationalHost "mm0:instantiate-term"
      [Presentation.ComputationalTyping.encodeTable theory.terms,
        Presentation.ComputationalContext.encodeContext formal,
        Presentation.ComputationalContext.encodeContext target,
        Presentation.ComputationalArguments.encodeExpressions images, Presentation.encode body]
      (Presentation.encodeResult (some result)) ∧
      Typed (projectRun admissions) (ofContext target) (SExpr.ofKernel result) (ofContext remaining) sort := by
  have admitted := (checked_run_admissible_iff checked formal target images).mpr ⟨fits, safe⟩
  have localTyped := (checked_run_typing_iff checked formal remaining body sort).mp typed
  obtain ⟨result, computed, resultTyped⟩ := admitted.instantiate_typed localTyped
  refine ⟨result, ?_, (checked_run_typing_iff checked target remaining result sort).mpr resultTyped⟩
  simpa only [Presentation.ComputationalTyping.theory_signature, computed] using
    Presentation.ComputationalInstantiation.instantiation_computes theory.terms formal target images body

namespace Controls

private def predicate : Kernel.TermDecl := ⟨[.regular 0 ∅], 1, ∅⟩
private def constant : Kernel.TermDecl := ⟨[], 1, ∅⟩
private def history : List Kernel.Admission :=
  [.sort 0 {}, .sort 1 { provable := true }, .term 0 predicate, .term 1 constant]
private def theory : Kernel.Theory :=
  { sorts := [(1, { provable := true }), (0, {})], terms := [(1, constant), (0, predicate)] }
private def formal : Kernel.Context := [.bound 0, .regular 1 ∅]
private def swapped : Kernel.Context := [.regular 1 ∅, .bound 0]
private def dependent : Kernel.Context := [.bound 0, .regular 1 {0}]
private def capturingImages : List Kernel.Preterm := [.var 1, .app (.term 0) (.var 1)]
private def closed : List Kernel.Preterm := [.var 1, .term 1]

theorem actual_checked_history : Kernel.Theory.run? {} history = some theory := by rfl

private theorem related : EnvironmentRelated (projectRun history) theory :=
  checked_run_environment_related actual_checked_history

private theorem unsafeFits : List.Forall₂ (FitsBinder (projectRun history) (ofContext swapped))
    (capturingImages.map SExpr.ofKernel) (ofContext formal) := by
  rw [fits_vector_iff related]
  exact (Kernel.Substitution.checkArguments_iff _ _ _ _).mp (by decide +kernel)

private theorem unsafeNotAdmitted : ¬ Kernel.Substitution.Admissible theory.termSignature formal swapped capturingImages := by
  intro admitted
  have accepted := (Kernel.Substitution.checkAdmissible_iff _ _ _ _).mpr admitted
  have refused : Kernel.Substitution.checkAdmissible theory.termSignature formal swapped capturingImages = false := by
    decide +kernel
  simp [refused] at accepted

theorem historical_context_confusion_is_safe :
    Reference.historicalSafeSubst (ofContext swapped) (capturingImages.map SExpr.ofKernel) := by
  intro source other declared _ _ image expression sourceImage _
  obtain ⟨sort, known⟩ := declared
  cases source with
  | zero => simp [swapped, ofContext, Binder.ofKernel] at known
  | succ source =>
      cases source with
      | zero => simp [capturingImages, SExpr.ofKernel] at sourceImage
      | succ source => simp [swapped, ofContext, Binder.ofKernel] at known

/-- Typed arguments do not rescue the lost formal independence check. -/
theorem context_confusion_separates :
    List.Forall₂ (FitsBinder (projectRun history) (ofContext swapped))
      (capturingImages.map SExpr.ofKernel) (ofContext formal) ∧
      ¬ Reference.specifiedSafeSubst (ofContext formal) (ofContext swapped) (capturingImages.map SExpr.ofKernel) := by
  refine ⟨unsafeFits, ?_⟩
  exact fun safe => unsafeNotAdmitted ((admissible_iff related formal swapped capturingImages).mpr ⟨unsafeFits, safe⟩)

theorem authored_context_confusion_refuses :
    Applies Presentation.ComputationalAdmissible.admissibleProgram computationalHost "mm0:check-admissible"
      [Presentation.ComputationalTyping.encodeTable theory.terms,
        Presentation.ComputationalContext.encodeContext formal,
        Presentation.ComputationalContext.encodeContext swapped,
        Presentation.ComputationalArguments.encodeExpressions capturingImages] (.sym "False") := by
  apply (checked_run_authored_refuses_iff actual_checked_history formal swapped capturingImages).mpr
  exact fun h => context_confusion_separates.2 h.2

theorem unsafe_body_instantiation_refuses :
    Applies Presentation.ComputationalInstantiation.instantiationProgram computationalHost "mm0:instantiate-term"
      [Presentation.ComputationalTyping.encodeTable theory.terms,
        Presentation.ComputationalContext.encodeContext formal,
        Presentation.ComputationalContext.encodeContext swapped,
        Presentation.ComputationalArguments.encodeExpressions capturingImages, Presentation.encode (.var 1)] (.sym "None") := by
  apply (checked_run_authored_instantiation_refuses_iff actual_checked_history formal swapped capturingImages (.var 1)).mpr
  exact .inl (fun h => context_confusion_separates.2 h.2)

private theorem closedAdmitted : Kernel.Substitution.Admissible theory.termSignature formal swapped closed :=
  (Kernel.Substitution.checkAdmissible_iff _ _ _ _).mp (by decide +kernel)

theorem closed_image_is_authorized :
    Applies Presentation.ComputationalAdmissible.admissibleProgram computationalHost "mm0:check-admissible"
      [Presentation.ComputationalTyping.encodeTable theory.terms,
        Presentation.ComputationalContext.encodeContext formal,
        Presentation.ComputationalContext.encodeContext swapped,
        Presentation.ComputationalArguments.encodeExpressions closed] (.sym "True") :=
  (checked_run_authored_accepts_iff actual_checked_history formal swapped closed).mpr
    ((admissible_iff related formal swapped closed).mp closedAdmitted)

theorem closed_instantiation_returns_exact_result :
    Applies Presentation.ComputationalInstantiation.instantiationProgram computationalHost "mm0:instantiate-term"
      [Presentation.ComputationalTyping.encodeTable theory.terms,
        Presentation.ComputationalContext.encodeContext formal,
        Presentation.ComputationalContext.encodeContext swapped,
        Presentation.ComputationalArguments.encodeExpressions closed, Presentation.encode (.var 1)]
      (Presentation.encodeResult (some (.term 1))) := by
  apply (checked_run_authored_instantiation_iff actual_checked_history formal swapped closed (.var 1) (.term 1)).mpr
  exact ⟨(admissible_iff related formal swapped closed).mp closedAdmitted,
    by change 1 < 2; decide, rfl⟩

theorem wrong_instantiation_result_refuses :
    ¬ Applies Presentation.ComputationalInstantiation.instantiationProgram computationalHost "mm0:instantiate-term"
      [Presentation.ComputationalTyping.encodeTable theory.terms,
        Presentation.ComputationalContext.encodeContext formal,
        Presentation.ComputationalContext.encodeContext swapped,
        Presentation.ComputationalArguments.encodeExpressions closed, Presentation.encode (.var 1)]
      (Presentation.encodeResult (some (.var 1))) := by
  rw [checked_run_authored_instantiation_iff actual_checked_history]
  rintro ⟨_, _, same⟩
  cases same

theorem historical_declared_dependency_is_safe :
    Reference.historicalSafeSubst (ofContext dependent) ([.var 0, .var 1].map SExpr.ofKernel) := by
  intro source other declared bounded independent _ _ _ _
  obtain ⟨sort, known⟩ := declared
  cases source with
  | zero =>
      have present : Lean3Dependencies.Reference.hasVar (ofContext dependent) (.var other) 0 := by
        cases other with
        | zero => exact ⟨.bound 0, rfl, rfl⟩
        | succ other =>
            cases other with
            | zero => exact ⟨.reg 1 {0}, rfl, by simp⟩
            | succ other => simp [dependent, ofContext] at bounded; omega
      exact False.elim (independent present)
  | succ source =>
      cases source <;> simp [dependent, ofContext, Binder.ofKernel] at known

theorem target_dependency_cannot_replace_formal_independence :
    ¬ Reference.specifiedSafeSubst (ofContext formal) (ofContext dependent)
      ([.var 0, .var 1].map SExpr.ofKernel) := by
  intro safe
  have typed : List.Forall₂ (Kernel.Preterm.FitsBinder theory.termSignature dependent)
      [.var 0, .var 1] formal :=
    (Kernel.Substitution.checkArguments_iff _ _ _ _).mp (by decide +kernel)
  have admitted := (admissible_iff related formal dependent [.var 0, .var 1]).mpr
    ⟨(fits_vector_iff related formal dependent [.var 0, .var 1]).mpr typed, safe⟩
  have accepted := (Kernel.Substitution.checkAdmissible_iff _ _ _ _).mpr admitted
  have refused : Kernel.Substitution.checkAdmissible theory.termSignature formal dependent [.var 0, .var 1] = false := by
    decide +kernel
  simp [refused] at accepted

theorem appended_dummy_has_historical_compatibility :
    Reference.historicalSafeSubst (ofContext (formal ++ [.bound 0]))
      ([.var 0, .term 1].map SExpr.ofKernel) := by
  have admitted : Kernel.Substitution.Admissible theory.termSignature formal (formal ++ [.bound 0])
      [.var 0, .term 1] :=
    (Kernel.Substitution.checkAdmissible_iff _ _ _ _).mp (by decide +kernel)
  exact ((admissible_historical_prefix_iff related formal [.bound 0] [.var 0, .term 1]).mp admitted).2

theorem extra_images_break_prefix_compatibility :
    Reference.specifiedSafeSubst [] [.bound 0, .bound 0] [.var 0, .var 0] ∧
      ¬ Reference.historicalSafeSubst [.bound 0, .bound 0] [.var 0, .var 0] := by
  constructor
  · intro _ _ declared
    obtain ⟨_, known⟩ := declared
    simp at known
  · intro safe
    have excluded := safe 0 1 ⟨0, rfl⟩ (by decide) (by
      simp [Lean3Dependencies.Reference.hasVar]) 0 (.var 0) rfl rfl
    exact excluded ⟨.bound 0, rfl, rfl⟩

theorem empty_safety_does_not_authorize_missing_images :
    Reference.historicalSafeSubst (ofContext formal) [] ∧
      ¬ Kernel.Substitution.Admissible theory.termSignature formal formal [] := by
  constructor
  · intro _ _ _ _ _ _ _ absent
    simp at absent
  · intro admitted
    have same := admitted.length_eq
    simp [formal] at same

theorem duplicate_bound_images_are_refused :
    ¬ Kernel.Substitution.Admissible theory.termSignature [.bound 0, .bound 0] [.bound 0]
      [.var 0, .var 0] := by
  intro admitted
  have yes := (Kernel.Substitution.checkAdmissible_iff _ _ _ _).mpr admitted
  have no : Kernel.Substitution.checkAdmissible theory.termSignature [.bound 0, .bound 0] [.bound 0]
      [.var 0, .var 0] = false := by decide +kernel
  simp [no] at yes

end Controls

end Mettapedia.Languages.MM0.Upstream.Lean3Admissibility
