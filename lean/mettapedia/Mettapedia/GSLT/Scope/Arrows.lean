import Mettapedia.GSLT.Core.NonFactorization
import Mettapedia.Logic.TheoryModel.IdentityCarve
import Mettapedia.Logic.TheoryModel.InstitutionBridge

/-!
# Four kinds of scope change

A scope is read through the theory–model notions over a satisfaction relation
`Sat : Str → Sent → Prop` between programs (structures) and sentences
(observations): a universe `U` of admissible programs with the theorems
`consequencesIn Sat U T` of a theory `T` computed there, and an observer, an
equivalence `E` on programs that can evaluate exactly the `E`-invariant
sentences `observable Sat E`.

Every scope change below is a **translation** (`Translation`): sentences are
translated forward, programs are reduced backward, and satisfaction is
preserved and reflected.  The four kinds are four shapes of translation, and
they differ in *variance*:

* (a) **restrict** to a fragment `V ⊆ U`: the reduct includes `V` into `U`
  and sentences are kept; the translation runs from the ambient scope;
  theorems transfer forward and may grow, models transfer backward.
* (b) **forget** to a coarser observer `E ≤ E'`: the reduct is the identity
  and the visible sentences `observable E'` include into all sentences; the
  translation runs into the fine scope; the visible theorems are exactly
  kept and models are unchanged.
* (c) **identify** by axioms `Φ`: restriction to the carve `U ∩ models Φ`;
  the translation runs from the ambient scope; theorems grow by exactly `Φ`
  and models shrink.
* (d) **translate** along `(α, β)`: a general translation; theorems transfer
  forward, soundly, and models backward, as reducts.

**Preservation laws.**

* (a) Theorems transfer forward and models backward (`restrict_transfer`).  A
  restriction of the full universe gains no theorem exactly when the fragment
  hosts the theory faithfully (`restrict_conservative_iff_hostsFaithfully`);
  a sufficient, constructive criterion is that every hosted model has a twin
  in the fragment (`restrict_conservative_of_twins`).  Control: the h-set fragment
  of the groupoid universe gains `uip` (`hsetFragment_gains_uip`), while the
  one-program fragment `{univalentModel}` gains nothing
  (`univalent_fragment_gains_nothing`).
* (b) Forgetting is conservative: the coarse scope proves exactly the fine
  theorems it can still state (`forget_conservative`), and a sentence stays
  visible exactly when its truth factors through the coarse view
  (`mem_observable_iff_factors`).  Control: forgetting does not identify; the
  truncation observer cannot tell a two-loop structure from a thin one that
  the full theory separates (`forgetting_does_not_identify`).
* (c) Identifying is conservative exactly for axioms that are already
  theorems (`carve_conservative_iff`); identifications compose
  (`carve_carve`) and commute with restriction (`carve_restrict`).  An
  identification is exactly a *definable* restriction (`isCarve_iff`).
  Control: the one-point restriction `{eqModel PUnit}` is not an
  identification, because the codiscrete structure on two points has the
  same theory (`singleton_not_carve`).
* (d) The models of a translated theory are the reducts' preimage
  (`Translation.models_translate`); theorems transfer forward
  (`Translation.translate_mem_consequences`); pulling back the target's
  theorems computes the source theorems in the universe of reducts
  (`Translation.preimage_consequences`), so a translation is conservative
  exactly when its reducts host the theory faithfully
  (`Translation.conservative_iff_hostsFaithfully`).  Institution comorphisms
  are instances (`Translation.ofComorphism`).  Controls: a collapsing
  translation proves a sentence the source does not
  (`Collapse.not_conservative`); a translation with surjective reducts is
  conservative for every theory (`Translation.conservative_of_surjective`).

The shapes are distinguished by what the translation's two components do:
restriction has an injective reduct and the identity on sentences
(`restrictTranslation_reduct_injective`), forgetting has the identity reduct
and an injective sentence map (`forgetTranslation_translate_injective`).  The
laws in which two kinds interact are in `Mettapedia.GSLT.Scope.Interaction`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Scope

open Set
open Mettapedia.Logic.TheoryModel

universe uStr uSent uStr' uSent' uStr'' uSent'' u

/-! ## Translations of scopes -/

section Translation

variable {Str : Type uStr} {Sent : Type uSent} {Str' : Type uStr'} {Sent' : Type uSent'}
  {Str'' : Type uStr''} {Sent'' : Type uSent''}

/-- **A translation of scopes.**  Sentences are translated forward, programs
are reduced backward, and satisfaction is preserved and reflected.  This is
the satisfaction condition of an institution comorphism at one signature, and
a morphism of Chu spaces over `Prop`. -/
structure Translation (Sat : Str → Sent → Prop) (Sat' : Str' → Sent' → Prop) where
  /-- Translate a sentence of the source scope. -/
  translate : Sent → Sent'
  /-- Reduce a program of the target scope to the source scope. -/
  reduct : Str' → Str
  /-- The satisfaction condition. -/
  sat_iff : ∀ m φ, Sat' m (translate φ) ↔ Sat (reduct m) φ

namespace Translation

variable {Sat : Str → Sent → Prop} {Sat' : Str' → Sent' → Prop}
  {Sat'' : Str'' → Sent'' → Prop}

/-- The identity translation. -/
def id (Sat : Str → Sent → Prop) : Translation Sat Sat where
  translate φ := φ
  reduct m := m
  sat_iff _ _ := Iff.rfl

/-- Translations compose: sentences forward, reducts backward. -/
def comp (first : Translation Sat Sat') (second : Translation Sat' Sat'') :
    Translation Sat Sat'' where
  translate φ := second.translate (first.translate φ)
  reduct m := first.reduct (second.reduct m)
  sat_iff m φ := (second.sat_iff m (first.translate φ)).trans (first.sat_iff (second.reduct m) φ)

variable (τ : Translation Sat Sat')

/-- **The models of a translated theory are the programs whose reducts are
models.** -/
theorem models_translate (T : Set Sent) :
    models Sat' (τ.translate '' T) = τ.reduct ⁻¹' models Sat T :=
  models_image_eq_preimage τ.reduct τ.translate τ.sat_iff T

/-- **Theorems transfer forward**: a consequence of `T` translates to a
consequence of the translated theory. -/
theorem translate_mem_consequences {T : Set Sent} {φ : Sent}
    (entailed : φ ∈ theoryOf Sat (models Sat T)) :
    τ.translate φ ∈ theoryOf Sat' (models Sat' (τ.translate '' T)) := by
  intro m model
  rw [models_translate] at model
  exact (τ.sat_iff m φ).mpr (entailed model)

/-- **Pulling back the target's theorems computes the source theorems in the
universe of reducts.** -/
theorem preimage_consequences (T : Set Sent) :
    τ.translate ⁻¹' theoryOf Sat' (models Sat' (τ.translate '' T)) =
      consequencesIn Sat (range τ.reduct) T := by
  ext φ
  constructor
  · rintro entailed _ ⟨⟨m, rfl⟩, model⟩
    apply (τ.sat_iff m φ).mp
    apply entailed
    rw [models_translate]
    exact model
  · intro validated m model
    rw [models_translate] at model
    exact (τ.sat_iff m φ).mpr (validated ⟨⟨m, rfl⟩, model⟩)

/-- **A translation is conservative on a theory exactly when its universe of
reducts hosts the theory faithfully.** -/
theorem conservative_iff_hostsFaithfully (T : Set Sent) :
    (∀ φ, φ ∈ theoryOf Sat (models Sat T) ↔
        τ.translate φ ∈ theoryOf Sat' (models Sat' (τ.translate '' T))) ↔
      HostsFaithfully Sat (range τ.reduct) T := by
  unfold HostsFaithfully
  rw [← preimage_consequences]
  constructor
  · intro conservative
    ext φ
    exact (conservative φ).symm
  · intro equal φ
    exact (Set.ext_iff.mp equal φ).symm

/-- A translation whose reducts reach every source program is conservative
for every theory. -/
theorem conservative_of_surjective (surjective : Function.Surjective τ.reduct) (T : Set Sent)
    (φ : Sent) :
    φ ∈ theoryOf Sat (models Sat T) ↔
      τ.translate φ ∈ theoryOf Sat' (models Sat' (τ.translate '' T)) := by
  refine (conservative_iff_hostsFaithfully τ T).mpr ?_ φ
  rw [range_eq_univ.mpr surjective]
  exact hostsFaithfully_univ T

/-- **The forth law for observers.**  If the reduct maps target-indistinguishable
programs to source-indistinguishable ones, every sentence the source observer
can evaluate translates to one the target observer can evaluate. -/
theorem observable_subset_preimage {E : Setoid Str} {E' : Setoid Str'}
    (forth : ∀ ⦃m m'⦄, E' m m' → E (τ.reduct m) (τ.reduct m')) :
    observable Sat E ⊆ τ.translate ⁻¹' observable Sat' E' := by
  intro φ invariant m m' related
  rw [τ.sat_iff, τ.sat_iff]
  exact invariant (forth related)

end Translation

end Translation

/-! ## Institution comorphisms are translations -/

section Institution

open CategoryTheory
open Mettapedia.Logic (Institution)

universe uSignature uSignatureHom uSentence uModel uModelHom

variable {SourceSignature TargetSignature : Type uSignature}
  [Category.{uSignatureHom} SourceSignature] [Category.{uSignatureHom} TargetSignature]
  {source : Institution.{uSignature, uSignatureHom, uSentence, uModel, uModelHom} SourceSignature}
  {target : Institution.{uSignature, uSignatureHom, uSentence, uModel, uModelHom} TargetSignature}

/-- An institution comorphism at a signature is a translation of scopes. -/
def Translation.ofComorphism (comorphism : Institution.Comorphism source target)
    (signature : SourceSignature) :
    Translation (source.satisfies signature)
      (target.satisfies (comorphism.mapSignature.obj signature)) where
  translate := comorphism.mapSentence.app signature
  reduct := InstitutionBridge.modelReduct comorphism signature
  sat_iff := comorphism.satisfaction_condition signature

/-- Its universe of reducts is the comorphism's universe of reducts. -/
theorem Translation.range_reduct_ofComorphism (comorphism : Institution.Comorphism source target)
    (signature : SourceSignature) :
    range (Translation.ofComorphism comorphism signature).reduct =
      InstitutionBridge.reductUniverse comorphism signature :=
  rfl

end Institution

variable {Str : Type uStr} {Sent : Type uSent}

/-! ## (a) Restricting programs -/

section Restrict

variable (Sat : Str → Sent → Prop)

/-- The scope of the programs in `V`. -/
def restrictSat (V : Set Str) (m : V) (φ : Sent) : Prop :=
  Sat m.1 φ

/-- **Restriction as a translation from the ambient scope**: sentences are
kept, and the reduct includes the fragment into the ambient programs. -/
def restrictTranslation (V : Set Str) : Translation Sat (restrictSat Sat V) where
  translate φ := φ
  reduct m := m.1
  sat_iff _ _ := Iff.rfl

theorem restrictTranslation_reduct_injective (V : Set Str) :
    Function.Injective (restrictTranslation Sat V).reduct :=
  Subtype.val_injective

variable {Sat}

/-- **Restriction: theorems transfer forward, models backward.**  Passing from
the universe `U` to a fragment `V ⊆ U` keeps every theorem and may add more,
and every model hosted in the fragment is hosted in `U`. -/
theorem restrict_transfer {U V : Set Str} (sub : V ⊆ U) (T : Set Sent) :
    consequencesIn Sat U T ⊆ consequencesIn Sat V T ∧ modelsIn Sat V T ⊆ modelsIn Sat U T :=
  ⟨consequencesIn_anti sub T, modelsIn_mono sub T⟩

/-- **Twins make a restriction conservative.**  If every model hosted in `U`
has a twin in the fragment satisfying exactly the same sentences, the fragment
computes exactly the theorems of `U`. -/
theorem restrict_conservative_of_twins {U V : Set Str} (sub : V ⊆ U) {T : Set Sent}
    (twins : ∀ m ∈ modelsIn Sat U T, ∃ m' ∈ V, ∀ φ, Sat m' φ ↔ Sat m φ) :
    consequencesIn Sat V T = consequencesIn Sat U T := by
  apply Subset.antisymm
  · intro φ validated m hosted
    obtain ⟨m', inV, twin⟩ := twins m hosted
    have hostedV : m' ∈ modelsIn Sat V T :=
      ⟨inV, fun ψ member => (twin ψ).mpr (hosted.2 member)⟩
    exact (twin φ).mp (validated hostedV)
  · exact consequencesIn_anti sub T

/-- **A restriction of the full universe gains no theorem exactly when the
fragment hosts the theory faithfully.** -/
theorem restrict_conservative_iff_hostsFaithfully (V : Set Str) (T : Set Sent) :
    consequencesIn Sat V T = consequencesIn Sat univ T ↔ HostsFaithfully Sat V T := by
  rw [consequencesIn_univ]
  rfl

/-- A restriction never merges or splits programs: indistinguishability for
any language is computed pointwise, so it is the same in the fragment. -/
theorem restrict_indistinguishable_iff (V : Set Str) (L : Set Sent) (m m' : V) :
    indistinguishable (restrictSat Sat V) L m m' ↔ indistinguishable Sat L m.1 m'.1 :=
  Iff.rfl

end Restrict

/-! ## (b) Forgetting observations -/

section Forget

variable (Sat : Str → Sent → Prop)

/-- The scope that can only state the sentences of `L`. -/
def forgetSat (L : Set Sent) (m : Str) (φ : L) : Prop :=
  Sat m φ.1

/-- **Forgetting as a translation into the fine scope**: the reduct is the
identity on programs and the sentences still visible include into all
sentences.  The variance is opposite to restriction. -/
def forgetTranslation (L : Set Sent) : Translation (forgetSat Sat L) Sat where
  translate φ := φ.1
  reduct m := m
  sat_iff _ _ := Iff.rfl

theorem forgetTranslation_translate_injective (L : Set Sent) :
    Function.Injective (forgetTranslation Sat L).translate :=
  Subtype.val_injective

variable {Sat}

/-- **Forgetting is conservative.**  The coarse scope proves exactly the fine
theorems it can still state: nothing visible is gained or lost. -/
theorem forget_conservative (L : Set Sent) (T : Set L) (φ : L) :
    φ ∈ theoryOf (forgetSat Sat L) (models (forgetSat Sat L) T) ↔
      φ.1 ∈ theoryOf Sat (models Sat (Subtype.val '' T)) :=
  (forgetTranslation Sat L).conservative_of_surjective Function.surjective_id T φ

/-- **What forgetting keeps visible.**  A sentence is visible to the observer
`E` exactly when its truth value factors through the view `Quotient E`. -/
theorem mem_observable_iff_factors (E : Setoid Str) (φ : Sent) :
    φ ∈ observable Sat E ↔
      Mettapedia.GSLT.Core.NonFactorization.Factors (Quotient.mk E) (fun m => Sat m φ) := by
  constructor
  · intro invariant
    exact ⟨Quotient.lift (fun m => Sat m φ) (fun _ _ related => propext (invariant related)),
      fun _ => rfl⟩
  · rintro ⟨recover, recovers⟩ m m' related
    have first : recover ⟦m⟧ = Sat m φ := recovers m
    have second : recover ⟦m'⟧ = Sat m' φ := recovers m'
    rw [← first, ← second, Quotient.sound related]

/-- **Coarse theorems transfer backward**: along `E ≤ E'` every theorem the
coarse observer can evaluate is one the fine observer can evaluate. -/
theorem forget_visible_theorems {E E' : Setoid Str} (coarser : E ≤ E') (U : Set Str)
    (T : Set Sent) :
    consequencesIn Sat U T ∩ observable Sat E' ⊆ consequencesIn Sat U T ∩ observable Sat E :=
  fun _ member => ⟨member.1, observable_anti coarser member.2⟩

end Forget

/-! ## (c) Identifying: adding axioms -/

section Identify

variable {Sat : Str → Sent → Prop}

/-- **Identifying is conservative exactly for axioms that are already
theorems.** -/
theorem carve_conservative_iff (U : Set Str) (Φ T : Set Sent) :
    consequencesIn Sat (carve Sat U Φ) T = consequencesIn Sat U T ↔
      Φ ⊆ consequencesIn Sat U T := by
  constructor
  · intro equal φ member
    rw [← equal]
    exact fun _ hosted => hosted.1.2 member
  · intro sub
    have same : modelsIn Sat U (Φ ∪ T) = modelsIn Sat U T := by
      apply Subset.antisymm
      · exact fun _ hosted => ⟨hosted.1, fun _ member => hosted.2 (Or.inr member)⟩
      · intro m hosted
        refine ⟨hosted.1, fun φ member => ?_⟩
        rcases member with inΦ | inT
        · exact sub inΦ hosted
        · exact hosted.2 inT
    rw [consequencesIn_carve, consequencesIn, same]
    rfl

/-- Identifications compose: carving by `Φ` then by `Ψ` is carving by both. -/
theorem carve_carve (U : Set Str) (Φ Ψ : Set Sent) :
    carve Sat (carve Sat U Φ) Ψ = carve Sat U (Φ ∪ Ψ) := by
  ext m
  constructor
  · rintro ⟨⟨inU, modelΦ⟩, modelΨ⟩
    exact ⟨inU, fun _ member => member.elim (fun inΦ => modelΦ inΦ) fun inΨ => modelΨ inΨ⟩
  · rintro ⟨inU, model⟩
    exact ⟨⟨inU, fun _ inΦ => model (Or.inl inΦ)⟩, fun _ inΨ => model (Or.inr inΨ)⟩

/-- **Identifying commutes with restricting**: carving a fragment is
restricting the carved universe. -/
theorem carve_restrict {U V : Set Str} (sub : V ⊆ U) (Φ : Set Sent) :
    carve Sat V Φ = V ∩ carve Sat U Φ := by
  ext m
  exact ⟨fun ⟨inV, model⟩ => ⟨inV, sub inV, model⟩,
    fun ⟨inV, _, model⟩ => ⟨inV, model⟩⟩

/-- **An identification is exactly a definable restriction**: a fragment is
carved by some axioms exactly when it is carved by its own theory. -/
theorem isCarve_iff {U V : Set Str} :
    (∃ Φ : Set Sent, V = carve Sat U Φ) ↔ V = carve Sat U (theoryOf Sat V) := by
  constructor
  · rintro ⟨Φ, rfl⟩
    apply Subset.antisymm
    · exact fun m member => ⟨member.1, fun _ valid => valid member⟩
    · rintro m ⟨inU, model⟩
      exact ⟨inU, fun φ member => model fun _ inCarve => inCarve.2 member⟩
  · exact fun equal => ⟨theoryOf Sat V, equal⟩

end Identify

/-! ## Controls on the identity-proof signature -/

namespace Control

open IdentityProofs

/-- (a) **The h-set fragment gains `uip`**: a restriction of the groupoid
universe proves a sentence the universe does not. -/
theorem hsetFragment_gains_uip :
    IdSentence.uip ∈ consequencesIn IdStructure.Sat hsetFragment.{u} groupoidLaws ∧
      IdSentence.uip ∉ consequencesIn IdStructure.Sat groupoidUniverse.{u} groupoidLaws := by
  refine ⟨?_, ?_⟩
  · rw [consequencesIn_hsetFragment_eq]
    exact fun equal => IdSentence.noConfusion equal
  · rw [consequencesIn_groupoidUniverse]
    exact uip_not_mem_groupoidLaws

/-- (a) **Positive**: the one-program fragment of univalent types gains
nothing over the groupoid universe. -/
theorem univalent_fragment_gains_nothing :
    consequencesIn IdStructure.Sat ({univalentModel} : Set IdStructure.{1}) groupoidLaws =
      consequencesIn IdStructure.Sat groupoidUniverse.{1} groupoidLaws :=
  hostsFaithfully_univalent.trans hostsFaithfully_groupoidUniverse.symm

/-- (b) **Forgetting does not identify.**  The truncation observer cannot tell
the thin one-point structure from the two-loop structure, yet the full theory
of the first contains `uip`, which the second refutes. -/
theorem forgetting_does_not_identify :
    truncation.{u} (eqModel PUnit) xorModel ∧
      IdSentence.uip ∈ theoryOf IdStructure.Sat {eqModel.{u} PUnit} ∧
      ¬ xorModel.{u}.Sat IdSentence.uip := by
  refine ⟨eqModel_punit_truncation_xor, ?_, xorModel_not_uip⟩
  rintro M rfl
  exact eqModel_sat_uip PUnit

/-- (b) The sentence `uip` does not survive forgetting to the truncation
observer: its truth does not factor through the truncated view. -/
theorem uip_does_not_factor_through_truncation :
    ¬ Mettapedia.GSLT.Core.NonFactorization.Factors (Quotient.mk truncation.{u})
      (fun M : IdStructure.{u} => M.Sat IdSentence.uip) :=
  fun factors => uip_not_observable ((mem_observable_iff_factors truncation _).mpr factors)

/-- (c) **Identification strengthens**: carving the groupoid universe by `uip`
excludes the two-loop structure. -/
theorem identification_excludes_xor :
    xorModel.{u} ∈ groupoidUniverse ∧ xorModel.{u} ∉ hsetFragment :=
  ⟨xorModel_mem_groupoidUniverse, xorModel_not_mem_hsetFragment⟩

/-- Two points, one proof between any two: a thin, connected structure on a
two-point type. -/
def codiscreteBool : IdStructure.{u} where
  Pt := ULift.{u} Bool
  Pf _ _ := PUnit
  refl _ := PUnit.unit
  inv _ := PUnit.unit
  comp _ _ := PUnit.unit

theorem codiscreteBool_sat (φ : IdSentence) : codiscreteBool.{u}.Sat φ := by
  cases φ with
  | connected => exact fun _ _ => ⟨PUnit.unit⟩
  | assoc => exact fun _ _ _ => rfl
  | leftUnit => exact fun _ => rfl
  | rightUnit => exact fun _ => rfl
  | leftInv => exact fun _ => rfl
  | rightInv => exact fun _ => rfl
  | uip => exact fun _ _ => rfl
  | loopComm => exact fun _ _ => rfl

theorem eqModel_punit_sat (φ : IdSentence) : (eqModel.{u} PUnit).Sat φ := by
  have laws := eqModel_mem_uipLaws.{u} PUnit
  cases φ with
  | connected => exact fun a b => ⟨⟨⟨Subsingleton.elim (α := PUnit) a b⟩⟩⟩
  | assoc => exact @laws .assoc (Or.inr (Or.inl rfl))
  | leftUnit => exact @laws .leftUnit (Or.inr (Or.inr (Or.inl rfl)))
  | rightUnit => exact @laws .rightUnit (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  | leftInv => exact @laws .leftInv (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  | rightInv => exact @laws .rightInv (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
  | uip => exact @laws .uip (Or.inl rfl)
  | loopComm => exact @IdStructure.sat_loopComm_of_uip _ (@laws .uip (Or.inl rfl))

theorem codiscreteBool_ne_eqModel : codiscreteBool.{u} ≠ eqModel PUnit := by
  intro equal
  have points : ULift.{u} Bool = PUnit := congrArg IdStructure.Pt equal
  have single : Subsingleton (ULift.{u} Bool) := by
    rw [points]
    exact inferInstance
  exact Bool.noConfusion (congrArg ULift.down (Subsingleton.elim (ULift.up true : ULift.{u} Bool)
    (ULift.up false)))

/-- (c) **A restriction that is not an identification.**  The one-point
fragment `{eqModel PUnit}` is not carved by any axioms: the codiscrete
two-point structure satisfies exactly the same sentences. -/
theorem singleton_not_carve :
    ¬ ∃ Φ : Set IdSentence, ({eqModel.{u} PUnit} : Set IdStructure.{u}) =
      carve IdStructure.Sat univ Φ := by
  intro carved
  have equal := isCarve_iff.mp carved
  have member : codiscreteBool.{u} ∈ carve IdStructure.Sat univ
      (theoryOf IdStructure.Sat ({eqModel.{u} PUnit} : Set IdStructure.{u})) :=
    ⟨mem_univ _, fun φ _ => codiscreteBool_sat φ⟩
  rw [← equal] at member
  exact codiscreteBool_ne_eqModel member

/-- (c) **Positive**: the h-set fragment is carved from the groupoid universe. -/
theorem hsetFragment_isCarve :
    ∃ Φ : Set IdSentence, (hsetFragment.{u} : Set IdStructure.{u}) =
      carve IdStructure.Sat groupoidUniverse Φ :=
  ⟨{IdSentence.uip}, rfl⟩

end Control

/-! ## (d) A collapsing translation -/

namespace Collapse

/-- Programs are Booleans; the sentence `b` says the program is `b`. -/
def sourceSat (m : Bool) (φ : Bool) : Prop :=
  m = φ

/-- One program, which the target reads as `true`. -/
def targetSat (_ : PUnit.{1}) (φ : Bool) : Prop :=
  φ = true

/-- The collapse: sentences are kept, and the only target program reduces to
`true`. -/
def collapse : Translation sourceSat targetSat where
  translate φ := φ
  reduct _ := true
  sat_iff _ _ := ⟨Eq.symm, Eq.symm⟩

/-- The source proves nothing from no axioms: `true` fails at `false`. -/
theorem true_not_theorem : true ∉ theoryOf sourceSat (models sourceSat (∅ : Set Bool)) :=
  fun entailed => Bool.noConfusion (@entailed false fun _ member => member.elim)

/-- The target proves the translation of `true`. -/
theorem translated_true_theorem :
    collapse.translate true ∈ theoryOf targetSat (models targetSat (collapse.translate '' ∅)) :=
  fun _ _ => rfl

/-- **The collapse is not conservative.** -/
theorem not_conservative :
    ¬ ∀ φ, φ ∈ theoryOf sourceSat (models sourceSat (∅ : Set Bool)) ↔
      collapse.translate φ ∈ theoryOf targetSat (models targetSat (collapse.translate '' ∅)) :=
  fun conservative => true_not_theorem ((conservative true).mpr translated_true_theorem)

/-- Equivalently, its universe of reducts does not host the empty theory
faithfully. -/
theorem not_hostsFaithfully :
    ¬ HostsFaithfully sourceSat (range collapse.reduct) (∅ : Set Bool) :=
  fun faithful => not_conservative ((collapse.conservative_iff_hostsFaithfully ∅).mpr faithful)

/-- **Positive**: the identity translation of the same scope is conservative. -/
theorem identity_conservative (T : Set Bool) (φ : Bool) :
    φ ∈ theoryOf sourceSat (models sourceSat T) ↔
      (Translation.id sourceSat).translate φ ∈
        theoryOf sourceSat (models sourceSat ((Translation.id sourceSat).translate '' T)) :=
  (Translation.id sourceSat).conservative_of_surjective Function.surjective_id T φ

end Collapse

end Mettapedia.GSLT.Scope
