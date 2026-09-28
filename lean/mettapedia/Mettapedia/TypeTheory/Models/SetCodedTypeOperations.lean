import Mettapedia.TypeTheory.Models.SetCodedIdentity
import Mettapedia.TypeTheory.ContextualTypeOperations
import Mettapedia.TypeTheory.ContextualBasedIdentityOperations

/-!
# Dependent functions, pairs and identity in one set-coded model

The operations below reuse trace-coded functions, Kuratowski dependent
pairs and separated equality fibres over the same contextual core. The
existing general beta and strict substitution interfaces are instantiated,
including substitution of the full identity eliminator. No native syntax,
normalization procedure or universe-strength assumption is introduced here.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Models.SetCodedTypeOperations

open Mettapedia.Logic.HOL.Embedding
open ZFSetContextualInterpretation (SetFamily Section Extension codedCwf)
open ContextualTypeOperations
open Mettapedia.GSLT.Core.ContextualLadder

universe u

noncomputable def products : PiOperations codedCwf.{u} :=
  .ofQualified ZFSetTraceContextual.products

noncomputable def sums : SigmaOperations codedCwf.{u} :=
  .ofQualified ZFSetContextualInterpretation.sums

noncomputable def formation : IdentityFormationOperations codedCwf.{u} :=
  .ofQualified SetCodedIdentity.formation

noncomputable def reflexivity : IdentityReflexivityOperations formation.{u} :=
  .ofQualified SetCodedIdentity.reflexivity

noncomputable def elimination : IdentityEliminationOperations formation.{u} :=
  .ofQualified SetCodedIdentity.elimination

def reindexing : IdentityReindexing formation.{u} where
  map := SetCodedIdentity.identityReindex

noncomputable def operations : Operations codedCwf.{u} where
  products := products
  sums := sums
  identity := ⟨formation, reflexivity, elimination, reindexing⟩

theorem products_substitution : StrictPiSubstitution products.{u} := by
  refine ⟨?_, ?_, ?_⟩
  · intro source target substitution domain codomain
    rfl
  · intro source target substitution domain codomain body
    exact HEq.rfl
  · intro source target substitution domain codomain function argument reindexedFunction same
    have equal : codedCwf.tmSub function substitution = reindexedFunction := eq_of_heq same
    cases equal
    exact HEq.rfl

theorem sums_substitution : StrictSigmaSubstitution sums.{u} := by
  refine ⟨?_, ?_, ?_⟩
  · intro source target substitution domain codomain
    rfl
  · intro source target substitution domain codomain first second reindexedSecond same
    have equal : codedCwf.tmSub second substitution = reindexedSecond := eq_of_heq same
    cases equal
    exact HEq.rfl
  · intro source target substitution domain codomain value reindexedValue same
    have equal : codedCwf.tmSub value substitution = reindexedValue := eq_of_heq same
    cases equal
    exact ⟨HEq.rfl, HEq.rfl⟩

theorem identity_reindexing : StrictIdentityReindexing elimination.{u} reindexing := by
  refine ⟨?_, ?_, ?_⟩
  · intro source target substitution type
    rfl
  · intro source target substitution type
    exact ⟨HEq.rfl, HEq.rfl, HEq.rfl⟩
  · intro source target substitution type
    exact SetCodedIdentity.reflexivity_square substitution type

theorem identity_substitution : StrictJSubstitution elimination.{u} reindexing := by
  intro source target substitution type motive base reindexedBase same
  have equal : codedCwf.tmSub base
      (TypeOver.extensionSubstitution substitution type) = reindexedBase := eq_of_heq same
  cases equal
  exact heq_of_eq (SetCodedIdentity.j_substitution substitution type motive base)

theorem beta_laws : BetaLaws operations.{u} :=
  ⟨PiOperations.ofQualified_beta ZFSetTraceContextual.products,
    SigmaOperations.ofQualified_beta ZFSetContextualInterpretation.sums,
    IdentityEliminationOperations.ofQualified_boundary SetCodedIdentity.elimination,
    IdentityEliminationOperations.ofQualified_beta SetCodedIdentity.elimination⟩

theorem substitution_laws : StrictSubstitutionLaws operations.{u} :=
  ⟨products_substitution, sums_substitution,
    IdentityFormationOperations.ofQualified_substitution SetCodedIdentity.formation,
    IdentityReflexivityOperations.ofQualified_substitution SetCodedIdentity.reflexivity,
    identity_reindexing, identity_substitution⟩

/-- The same abstract full-motive law used by syntactic constructions now
has an instance with actual set codes and trace functions. -/
theorem full_motive_beta_square {Γ Δ : Type (u + 1)}
    (θ : Δ → Γ) (a : SetFamily Γ)
    (motive : SetFamily (formation.identityContext a))
    (base : Section (motive ∘ elimination.reflexivitySubstitution a)) :
    codedCwf.tmSub
        (codedCwf.tmSub (elimination.j motive base) (reindexing.map θ a))
        (elimination.reflexivitySubstitution (a ∘ θ)) =
      reindexBase elimination reindexing identity_reindexing.2.2 θ a motive base :=
  j_beta_substitution elimination reindexing identity_reindexing.2.2
    identity_substitution beta_laws.2.2.2 θ a motive base

namespace Based

open ContextualBasedIdentityOperations
open ZFSetDependentProducts (Elements)
open ZFSetTraceProofDecoding (truthCode mem_truthCode)

/-- Fixed-left-endpoint J, with every set-valued motive over the existing
based context allowed. This has the shape of the declared native operation. -/
noncomputable def elimination : Elimination formation.{u} where
  reflSection left γ := ⟨⟨γ, left γ⟩, ⟨∅, (mem_truthCode _ _).mpr ⟨rfl, rfl⟩⟩⟩
  j left motive base := by
    intro point
    rcases point with ⟨⟨γ, right⟩, witness⟩
    have endpoints : left γ = right := ((mem_truthCode _ _).mp witness.2).2
    subst right
    have canonical : witness =
        (⟨∅, (mem_truthCode _ _).mpr ⟨rfl, rfl⟩⟩ : Elements (truthCode (left γ = left γ))) :=
      Subtype.ext ((mem_truthCode _ _).mp witness.2).1
    cases canonical
    exact base γ

def reindexing : Reindexing formation.{u} where
  map := fun {_ _} θ {_} _left point => ⟨⟨θ point.1.1, point.1.2⟩, point.2⟩

theorem boundary : Boundary reflexivity.{u} elimination :=
  ⟨fun _ => rfl, fun _ => HEq.rfl⟩

theorem beta : Beta elimination.{u} := fun _ _ _ => rfl

theorem reindexing_laws : StrictReindexing elimination.{u} reindexing := by
  refine ⟨?_, ?_, ?_⟩
  · intro source target θ type left
    rfl
  · intro source target θ type left
    exact ⟨HEq.rfl, HEq.rfl⟩
  · intro source target θ type left
    rfl

theorem substitution : ContextualBasedIdentityOperations.StrictJSubstitution
    elimination.{u} reindexing := by
  intro source target θ type left motive base reindexedBase same
  have equal : codedCwf.tmSub base θ = reindexedBase := eq_of_heq same
  cases equal
  apply heq_of_eq
  funext point
  rcases point with ⟨⟨γ, right⟩, witness⟩
  have endpoints : left (θ γ) = right := ((mem_truthCode _ _).mp witness.2).2
  subst right
  have canonical : witness =
      (⟨∅, (mem_truthCode _ _).mpr ⟨rfl, rfl⟩⟩ :
        Elements (truthCode (left (θ γ) = left (θ γ)))) :=
    Subtype.ext ((mem_truthCode _ _).mp witness.2).1
  cases canonical
  rfl

def intoFull {Γ : Type (u + 1)} {a : SetFamily Γ} (left : Section a) :
    basedContext formation left → formation.identityContext a :=
  fun point => ⟨⟨⟨point.1.1, left point.1.1⟩, point.1.2⟩, point.2⟩

/-- The two eliminators agree on the restriction of each full motive to a
fixed left endpoint. Their context shapes are related, not conflated. -/
theorem agrees_with_full {Γ : Type (u + 1)} {a : SetFamily Γ} (left : Section a)
    (motive : SetFamily (formation.identityContext a))
    (base : Section (motive ∘ SetCodedIdentity.reflexivitySubstitution a)) :
    elimination.j left (motive ∘ intoFull left) (fun γ => base ⟨γ, left γ⟩) =
      fun point => SetCodedIdentity.j motive base (intoFull left point) := by
  funext point
  rcases point with ⟨⟨γ, right⟩, witness⟩
  have endpoints : left γ = right := ((mem_truthCode _ _).mp witness.2).2
  subst right
  have canonical : witness =
      (⟨∅, (mem_truthCode _ _).mpr ⟨rfl, rfl⟩⟩ : Elements (truthCode (left γ = left γ))) :=
    Subtype.ext ((mem_truthCode _ _).mp witness.2).1
  cases canonical
  rfl

/-- After supplying the carrier, left endpoint, motive and method, the
remaining two arguments of based J are an actual trace-coded function. -/
noncomputable def function {Γ : Type (u + 1)} {a : SetFamily Γ} (left : Section a)
    (motive : SetFamily (basedContext formation left))
    (base : Section (motive ∘ elimination.reflSection left)) :
    Section (ZFSetTraceContextual.piFamily a
      (ZFSetTraceContextual.piFamily (witnessType formation left) motive)) :=
  ZFSetTraceContextual.lam (ZFSetTraceContextual.lam (elimination.j left motive base))

theorem function_application {Γ : Type (u + 1)} {a : SetFamily Γ} (left right : Section a)
    (motive : SetFamily (basedContext formation left))
    (base : Section (motive ∘ elimination.reflSection left))
    (path : Section (SetCodedIdentity.identityFamily left right)) :
    ZFSetTraceContextual.app (a := SetCodedIdentity.identityFamily left right)
      (b := fun point => motive ⟨⟨point.1, right point.1⟩, point.2⟩)
      (ZFSetTraceContextual.app (a := a)
        (b := ZFSetTraceContextual.piFamily (witnessType formation left) motive)
        (function left motive base) right) path =
      fun γ => elimination.j left motive base ⟨⟨γ, right γ⟩, path γ⟩ := by
  unfold function
  rw [ZFSetTraceContextual.app_lam]
  exact ZFSetTraceContextual.app_lam (a := SetCodedIdentity.identityFamily left right)
    (b := fun point => motive ⟨⟨point.1, right point.1⟩, point.2⟩)
    (fun point => elimination.j left motive base ⟨⟨point.1, right point.1⟩, point.2⟩) path

/-- Two trace applications followed by identity computation recover the
original method. The function is encoded by trace lambda, not a constant
whose claimed value is stipulated by an interpretation relation. -/
theorem function_beta {Γ : Type (u + 1)} {a : SetFamily Γ} (left : Section a)
    (motive : SetFamily (basedContext formation left))
    (base : Section (motive ∘ elimination.reflSection left)) :
    ZFSetTraceContextual.app (a := SetCodedIdentity.identityFamily left left)
      (b := fun point => motive ⟨⟨point.1, left point.1⟩, point.2⟩)
      (ZFSetTraceContextual.app (a := a)
        (b := ZFSetTraceContextual.piFamily (witnessType formation left) motive)
        (function left motive base) left)
      (SetCodedIdentity.reflSection left) = base := by
  rw [function_application]
  exact beta left motive base

/-- Use identity evidence to move a value into the right endpoint's fibre.
The operation is an application of the constructed based J, not a new
primitive transport or an assumed equality of the two fibres. -/
noncomputable def transport {Γ : Type (u + 1)} {a : SetFamily Γ}
    (b : SetFamily (Extension a)) (left right : Section a)
    (path : Section (SetCodedIdentity.identityFamily left right))
    (value : Section (fun γ => b ⟨γ, left γ⟩)) :
    Section (fun γ => b ⟨γ, right γ⟩) :=
  fun γ => elimination.j left (fun point => b point.1) value ⟨⟨γ, right γ⟩, path γ⟩

theorem transport_refl {Γ : Type (u + 1)} {a : SetFamily Γ}
    (b : SetFamily (Extension a)) (left : Section a)
    (value : Section (fun γ => b ⟨γ, left γ⟩)) :
    transport b left left (SetCodedIdentity.reflSection left) value = value :=
  beta left (fun point => b point.1) value

theorem transport_substitution {Γ Δ : Type (u + 1)} (θ : Δ → Γ) {a : SetFamily Γ}
    (b : SetFamily (Extension a)) (left right : Section a)
    (path : Section (SetCodedIdentity.identityFamily left right))
    (value : Section (fun γ => b ⟨γ, left γ⟩)) :
    (fun δ => transport b left right path value (θ δ)) =
      transport (b ∘ ZFSetContextualInterpretation.extensionSubstitution θ a)
        (fun δ => left (θ δ)) (fun δ => right (θ δ))
        (fun δ => path (θ δ)) (fun δ => value (θ δ)) := by
  have natural := eq_of_heq (substitution θ left (fun point => b point.1) value
    (fun δ => value (θ δ)) HEq.rfl)
  funext δ
  exact congrFun natural ⟨⟨δ, right (θ δ)⟩, path (θ δ)⟩

/-- Package the new index together with a value whose type requires it.
The identity proof is consumed by J before dependent pair introduction. -/
noncomputable def transportedPair {Γ : Type (u + 1)} {a : SetFamily Γ}
    (b : SetFamily (Extension a)) (left right : Section a)
    (path : Section (SetCodedIdentity.identityFamily left right))
    (value : Section (fun γ => b ⟨γ, left γ⟩)) :
    Section (ZFSetContextualInterpretation.sigmaFamily a b) :=
  ZFSetContextualInterpretation.pair (b := b) right (transport b left right path value)

theorem transportedPair_first {Γ : Type (u + 1)} {a : SetFamily Γ}
    (b : SetFamily (Extension a)) (left right : Section a)
    (path : Section (SetCodedIdentity.identityFamily left right))
    (value : Section (fun γ => b ⟨γ, left γ⟩)) :
    ZFSetContextualInterpretation.fst (a := a) (b := b)
      (transportedPair b left right path value) = right :=
  ZFSetContextualInterpretation.fst_pair (a := a) (b := b) _ _

theorem transportedPair_second {Γ : Type (u + 1)} {a : SetFamily Γ}
    (b : SetFamily (Extension a)) (left right : Section a)
    (path : Section (SetCodedIdentity.identityFamily left right))
    (value : Section (fun γ => b ⟨γ, left γ⟩)) :
    HEq (ZFSetContextualInterpretation.snd (a := a) (b := b)
      (transportedPair b left right path value)) (transport b left right path value) :=
  ZFSetContextualInterpretation.snd_pair (a := a) (b := b) _ _

theorem transportedPair_refl {Γ : Type (u + 1)} {a : SetFamily Γ}
    (b : SetFamily (Extension a)) (left : Section a)
    (value : Section (fun γ => b ⟨γ, left γ⟩)) :
    transportedPair b left left (SetCodedIdentity.reflSection left) value =
      ZFSetContextualInterpretation.pair (a := a) (b := b) left value := by
  unfold transportedPair
  rw [transport_refl]

theorem transportedPair_substitution {Γ Δ : Type (u + 1)} (θ : Δ → Γ) {a : SetFamily Γ}
    (b : SetFamily (Extension a)) (left right : Section a)
    (path : Section (SetCodedIdentity.identityFamily left right))
    (value : Section (fun γ => b ⟨γ, left γ⟩)) :
    (fun δ => transportedPair b left right path value (θ δ)) =
      transportedPair (b ∘ ZFSetContextualInterpretation.extensionSubstitution θ a)
        (fun δ => left (θ δ)) (fun δ => right (θ δ))
        (fun δ => path (θ δ)) (fun δ => value (θ δ)) := by
  unfold transportedPair
  rw [ZFSetContextualInterpretation.pair_substitution, transport_substitution]

end Based

namespace Controls

/-! The context and the result family both vary. J supplies a function's
body, and its result then becomes a component of a dependent set-coded pair. -/

def domain : SetFamily ZFSet.{u} := fun γ => {γ}

def argument : Section domain.{u} := fun γ => ⟨γ, ZFSet.mem_singleton.mpr rfl⟩

noncomputable def motive : SetFamily (formation.identityContext domain.{u}) :=
  fun point => {point.1.2.1}

def base : Section (motive.{u} ∘ elimination.reflexivitySubstitution domain) :=
  fun point => ⟨point.2.1, ZFSet.mem_singleton.mpr rfl⟩

noncomputable def body : Section (fun point : Extension domain.{u} => {point.2.1}) :=
  fun point => elimination.j motive base (elimination.reflexivitySubstitution domain point)

noncomputable def applied : Section (fun γ : ZFSet.{u} => {γ}) :=
  products.app (products.lam body) argument

theorem applied_value (γ : ZFSet.{u}) : (applied γ).1 = γ := by
  change (ZFSetTraceContextual.app (ZFSetTraceContextual.lam body) argument γ).1 = γ
  rw [ZFSetTraceContextual.app_lam]
  rfl

noncomputable def paired : Section
    (ZFSetContextualInterpretation.sigmaFamily domain.{u} (fun point => {point.2.1})) :=
  sums.pair (domain := domain) (codomain := fun point => {point.2.1}) argument applied

theorem paired_first :
    sums.fst (domain := domain) (codomain := fun point => {point.2.1}) paired.{u} = argument :=
  ZFSetContextualInterpretation.fst_pair (a := domain)
    (b := fun point => {point.2.1}) argument applied

theorem paired_second :
    HEq (sums.snd (domain := domain) (codomain := fun point => {point.2.1}) paired.{u}) applied :=
  ZFSetContextualInterpretation.snd_pair (a := domain)
    (b := fun point => {point.2.1}) argument applied

theorem nonconstant_result : (applied.{u} ({∅} : ZFSet)).1 ≠ (applied ∅).1 := by
  rw [applied_value, applied_value]
  intro equality
  have member : (∅ : ZFSet.{u}) ∈ ({∅} : ZFSet) := ZFSet.mem_singleton.mpr rfl
  rw [equality] at member
  exact ZFSet.notMem_empty _ member

theorem wrong_constant_result : (applied.{u} ({∅} : ZFSet)).1 ≠ ∅ := by
  simpa only [applied_value] using nonconstant_result.{u}

/-- A context map that forgets its input is allowed; it must still act on
the dependent J motive and method through their actual comprehension maps. -/
def collapseContext : ZFSet.{u} → ZFSet.{u} := fun _ => ∅

theorem varying_motive_reindex :
    codedCwf.tmSub
        (codedCwf.tmSub (elimination.j motive.{u} base)
          (reindexing.map collapseContext domain))
        (elimination.reflexivitySubstitution (domain ∘ collapseContext)) =
      reindexBase elimination reindexing identity_reindexing.2.2
        collapseContext domain motive base :=
  full_motive_beta_square collapseContext domain motive base

theorem ignoring_context_changes_result :
    (applied.{u} (collapseContext {∅})).1 ≠ (applied {∅}).1 := by
  simpa only [collapseContext, applied_value] using nonconstant_result.{u}.symm

/-- Distinct elements of a common actual set have no identity witness. -/
theorem distinct_endpoints_rejected (a : ZFSet.{u})
    (left right : ZFSetDependentProducts.Elements a) (different : left ≠ right) :
    IsEmpty (ZFSetDependentProducts.Elements (ZFSetTraceProofDecoding.truthCode (left = right))) := by
  constructor
  intro witness
  exact different ((ZFSetTraceProofDecoding.mem_truthCode _ _).mp witness.2).2

end Controls

#print axioms beta_laws
#print axioms substitution_laws
#print axioms full_motive_beta_square
#print axioms Based.elimination
#print axioms Based.substitution
#print axioms Based.agrees_with_full
#print axioms Based.function_application
#print axioms Based.function_beta
#print axioms Based.transport_substitution
#print axioms Based.transportedPair_first
#print axioms Based.transportedPair_second
#print axioms Based.transportedPair_refl
#print axioms Based.transportedPair_substitution
#print axioms Controls.applied_value
#print axioms Controls.paired_second
#print axioms Controls.nonconstant_result
#print axioms Controls.varying_motive_reindex
#print axioms Controls.ignoring_context_changes_result
#print axioms Controls.distinct_endpoints_rejected

end Mettapedia.TypeTheory.Models.SetCodedTypeOperations
