import Mettapedia.OSLF.Programs.NativeType
import Mettapedia.OSLF.Programs.GradualTypes
import Mettapedia.OSLF.Programs.HoleEvaluation

/-!
# Completion spaces of partial programs

Read "the complete program `t` completes the partial program `P`" as a
satisfaction relation `Completes : Prog → Part → Prop`.  Then the theory–model
Galois connection is the completion Galois connection:

* the **completion space** of `P` is the model class of `{P}`
  (`completionSpace`); the **joint completions** of a set `Φ` of partial
  programs are the models of `Φ`;
* **refinement** is inclusion of completion spaces, which is entailment
  (`refines_iff_entails`);
* **consistency** of `Φ` is non-emptiness of its model class (`Consistent`);
  for two partial programs it is non-empty intersection of their completion
  spaces (`consistent_pair_iff`); joint consistency implies pairwise
  consistency (`Consistent.pairwise`), and not conversely (see
  `GradualTypes.SharedUnknowns` and `Composition`).

**Abstraction.**  An abstraction of a class `K` of complete programs is a
least element of its theory under refinement (`IsAbstraction`,
`isAbstraction_iff_least`).  Whenever it exists it satisfies the Galois
connection of Abstracting Gradual Typing (`IsAbstraction.galois`), and
concretising it gives the elementary hull of `K`
(`IsAbstraction.completionSpace_eq_hull`).  So AGT's `(α, γ)` is the
theory–model connection restricted to classes whose theory is principal.  It
fails to be total exactly where theories are not principal: when every
partial program has a completion and two have disjoint completion spaces, the
empty class has no abstraction (`not_isAbstraction_empty`).  Instances: gradual
types (`gradual_refines_iff`, `gradual_consistent_iff`,
`gradual_isAbstraction_iff`, `gradual_no_abstraction_empty`) and the hole
calculus (`hole_completionSpace`, `hole_refines_fill`).

**Typed holes in a GSLT.**  A partial program with holes `H` plugs a filling
of every hole and respects the equations (`PartialProgram`).  With a native
type for every hole, its completions form a native type (`completionType`).
A goal `φ` places an **obligation** on the fillings (`obligation`), and the
typed holes meet the goal exactly when every well-typed filling meets the
obligation (`completionType_implies_iff`).
* With one hole the partial program is an equation-respecting map, its
  completion type is OSLF's direct image and its obligation is OSLF's pullback
  (`ofMap_completionType`, `ofMap_obligation`), so the weakest hole type that
  meets a goal is the pullback of the goal (`singleHole_galois`).
* With several holes the obligation is a relation between the fillings.  It
  need not be a product of per-hole types: the obligation of `x == y` is the
  diagonal (`Obligations.equality_not_rectangular`), while the obligation of
  `x && y` is a product (`Obligations.conjunction_rectangular`).

**Scope changes on partial programs.**
* Placing a partial program into a context translates its completion type by
  direct image (`PartialProgram.completionType_inContext`),
  and a partial program without holes has its program's native type as
  completion type (`PartialProgram.completionType_noHoles`).
* Restricting the language of partial programs can destroy abstractions: in
  the fragment of static types, `{Int, Bool}` has no abstraction, while in
  the full gradual language its abstraction is `?`
  (`StaticFragment.no_abstraction`, `StaticFragment.unknown_abstracts`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Programs.Completion

open Mettapedia.Logic.TheoryModel
open Mettapedia.GSLT
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

universe u v

/-! ## Completion as satisfaction -/

section General

variable {Prog : Type u} {Part : Type v} (Completes : Prog → Part → Prop)

/-- **The completion space** of a partial program: the model class of `{P}`. -/
def completionSpace (P : Part) : Set Prog :=
  models Completes {P}

theorem mem_completionSpace {P : Part} {t : Prog} :
    t ∈ completionSpace Completes P ↔ Completes t P :=
  ⟨fun h => h rfl, fun h _ member => member ▸ h⟩

/-- A joint completion of a set of partial programs completes each of them. -/
theorem mem_models_iff {Φ : Set Part} {t : Prog} :
    t ∈ models Completes Φ ↔ ∀ P ∈ Φ, t ∈ completionSpace Completes P :=
  ⟨fun h _ member => (mem_completionSpace Completes).mpr (h member),
    fun h P member => (mem_completionSpace Completes).mp (h P member)⟩

/-- **Refinement**: every completion of `Q` completes `P`. -/
def Refines (Q P : Part) : Prop :=
  completionSpace Completes Q ⊆ completionSpace Completes P

theorem refines_iff_entails {Q P : Part} : Refines Completes Q P ↔ Entails Completes {Q} P :=
  ⟨fun h _ model => (mem_completionSpace Completes).mp (h model),
    fun h _ member => (mem_completionSpace Completes).mpr (h member)⟩

theorem Refines.refl (P : Part) : Refines Completes P P :=
  fun _ member => member

theorem Refines.trans {P Q R : Part} (first : Refines Completes P Q)
    (second : Refines Completes Q R) : Refines Completes P R :=
  fun _ member => second (first member)

/-- **Consistency**: a set of partial programs has a joint completion. -/
def Consistent (Φ : Set Part) : Prop :=
  (models Completes Φ).Nonempty

theorem consistent_pair_iff {P Q : Part} :
    Consistent Completes {P, Q} ↔ ∃ t, Completes t P ∧ Completes t Q := by
  constructor
  · rintro ⟨t, model⟩
    exact ⟨t, model (Or.inl rfl), model (Or.inr rfl)⟩
  · rintro ⟨t, hP, hQ⟩
    refine ⟨t, fun R member => ?_⟩
    rcases member with rfl | rfl
    · exact hP
    · exact hQ

/-- Fewer constraints stay consistent. -/
theorem Consistent.mono {Φ Ψ : Set Part} (included : Φ ⊆ Ψ) (consistent : Consistent Completes Ψ) :
    Consistent Completes Φ := by
  obtain ⟨t, model⟩ := consistent
  exact ⟨t, fun _ member => model (included member)⟩

/-- Pairwise consistency. -/
def PairwiseConsistent (Φ : Set Part) : Prop :=
  ∀ P ∈ Φ, ∀ Q ∈ Φ, Consistent Completes {P, Q}

/-- Joint consistency implies pairwise consistency. -/
theorem Consistent.pairwise {Φ : Set Part} (consistent : Consistent Completes Φ) :
    PairwiseConsistent Completes Φ := by
  intro P hP Q hQ
  apply consistent.mono
  intro R member
  rcases member with rfl | rfl
  · exact hP
  · exact hQ

/-! ## Abstraction -/

/-- **An abstraction** of a class `K` of complete programs: a partial
program covering `K` that refines every partial program covering `K`. -/
def IsAbstraction (K : Set Prog) (A : Part) : Prop :=
  K ⊆ completionSpace Completes A ∧
    ∀ P, K ⊆ completionSpace Completes P → Refines Completes A P

/-- A partial program covers `K` exactly when it is in the theory of `K`. -/
theorem subset_completionSpace_iff {K : Set Prog} {P : Part} :
    K ⊆ completionSpace Completes P ↔ P ∈ theoryOf Completes K :=
  ⟨fun h _ member => (mem_completionSpace Completes).mp (h member),
    fun h _ member => (mem_completionSpace Completes).mpr (h member)⟩

/-- **An abstraction is a least element of the theory of `K`.** -/
theorem isAbstraction_iff_least {K : Set Prog} {A : Part} :
    IsAbstraction Completes K A ↔
      A ∈ theoryOf Completes K ∧ ∀ P ∈ theoryOf Completes K, Refines Completes A P := by
  simp only [IsAbstraction, subset_completionSpace_iff]

/-- **The Galois connection of Abstracting Gradual Typing**: `K` is covered
by `P` exactly when its abstraction refines `P`. -/
theorem IsAbstraction.galois {K : Set Prog} {A : Part} (h : IsAbstraction Completes K A)
    (P : Part) : K ⊆ completionSpace Completes P ↔ Refines Completes A P :=
  ⟨h.2 P, fun refines _ member => refines (h.1 member)⟩

/-- **Concretising the abstraction gives the elementary hull.** -/
theorem IsAbstraction.completionSpace_eq_hull {K : Set Prog} {A : Part}
    (h : IsAbstraction Completes K A) :
    completionSpace Completes A = models Completes (theoryOf Completes K) := by
  ext t
  constructor
  · intro member P hP
    exact (mem_completionSpace Completes).mp
      (h.2 P ((subset_completionSpace_iff Completes).mpr hP) member)
  · intro model
    exact (mem_completionSpace Completes).mpr
      (model ((subset_completionSpace_iff Completes).mp h.1))

/-- Abstractions are unique up to mutual refinement. -/
theorem IsAbstraction.refines_of_isAbstraction {K : Set Prog} {A A' : Part}
    (h : IsAbstraction Completes K A) (h' : IsAbstraction Completes K A') :
    Refines Completes A A' ∧ Refines Completes A' A :=
  ⟨h.2 A' h'.1, h'.2 A h.1⟩

theorem isAbstraction_empty_iff {A : Part} :
    IsAbstraction Completes ∅ A ↔ ∀ P, Refines Completes A P :=
  ⟨fun h P => h.2 P (Set.empty_subset _), fun h => ⟨Set.empty_subset _, fun P _ => h P⟩⟩

/-- **Exactly why abstraction is partial**: if every partial program has a
completion and two have disjoint completion spaces, the empty class has no
abstraction. -/
theorem not_isAbstraction_empty (nonempty : ∀ P, (completionSpace Completes P).Nonempty)
    {P Q : Part} (disjoint : ∀ t, Completes t P → Completes t Q → False) (A : Part) :
    ¬ IsAbstraction Completes ∅ A := by
  intro h
  obtain ⟨t, member⟩ := nonempty A
  have refinesP := (isAbstraction_empty_iff Completes).mp h P
  have refinesQ := (isAbstraction_empty_iff Completes).mp h Q
  exact disjoint t ((mem_completionSpace Completes).mp (refinesP member))
    ((mem_completionSpace Completes).mp (refinesQ member))

end General

/-! ## Instances -/

section Gradual

open Mettapedia.OSLF.Programs.GradualTypes

theorem gradual_completionSpace (G : GType) : completionSpace Conc G = concretisation G :=
  (concretisation_eq_models G).symm

/-- Refinement of gradual types is precision. -/
theorem gradual_refines_iff {G G' : GType} : Refines Conc G G' ↔ Prec G G' := by
  rw [Refines, gradual_completionSpace, gradual_completionSpace]
  exact prec_iff_concretisation_subset.symm

/-- Consistency of two gradual types is consistency of the two-element
theory. -/
theorem gradual_consistent_iff {G G' : GType} : Consistent Conc {G, G'} ↔ Consis G G' :=
  consis_iff_models_nonempty.symm

/-- The general abstraction specialises to AGT's. -/
theorem gradual_isAbstraction_iff (K : Set SType) (G : GType) :
    IsAbstraction Conc K G ↔ GradualTypes.IsAbstraction K G := by
  simp only [IsAbstraction, GradualTypes.IsAbstraction, gradual_completionSpace, gradual_refines_iff]

/-- AGT's `α(∅)` is undefined, as an instance of the general criterion. -/
theorem gradual_no_abstraction_empty (G : GType) : ¬ IsAbstraction Conc ∅ G :=
  not_isAbstraction_empty Conc
    (fun G => by rw [gradual_completionSpace]; exact concretisation_nonempty G)
    (P := .int) (Q := .bool) (fun t hInt hBool => by cases hInt; cases hBool) G

end Gradual

section Holes

open Mettapedia.OSLF.Programs.HoleEvaluation

variable {H : Type u}

theorem hole_completionSpace (P : Tm H) :
    completionSpace (Completes (H := H)) P = completions P :=
  (completions_eq_models P).symm

/-- Filling holes refines. -/
theorem hole_refines_fill (τ : H → Tm H) (P : Tm H) :
    Refines (Completes (H := H)) (P.fill τ) P := by
  rw [Refines, hole_completionSpace, hole_completionSpace]
  exact completions_fill_subset τ P

end Holes

/-! ## Typed holes in a GSLT -/

/-- **A partial program** of a GSLT with holes indexed by `H`: plugging a
program into every hole, compatibly with the equations. -/
structure PartialProgram (S : GSLT.{u}) (H : Type v) where
  /-- Plug a filling of every hole. -/
  plug : (H → S.Term) → S.Term
  /-- Equal fillings give equal programs. -/
  plug_resp : ∀ {σ τ : H → S.Term}, (∀ h, S.Equiv (σ h) (τ h)) → S.Equiv (plug σ) (plug τ)

namespace PartialProgram

variable {S : GSLT.{u}} {H : Type v} (K : PartialProgram S H)

/-- A filling respects the hole types. -/
def WellTyped (ψ : H → EquationPredicate S) (σ : H → S.Term) : Prop :=
  ∀ h, (ψ h).1 (σ h)

/-- **The completion type** of a partial program with typed holes: the native
predicate of its completions. -/
def completionType (ψ : H → EquationPredicate S) : EquationPredicate S :=
  saturatePredicate S fun t => ∃ σ, WellTyped ψ σ ∧ K.plug σ = t

theorem completionType_apply (ψ : H → EquationPredicate S) (t : S.Term) :
    (K.completionType ψ).1 t ↔ ∃ σ, WellTyped ψ σ ∧ S.Equiv t (K.plug σ) := by
  constructor
  · rintro ⟨_, equivalent, σ, typed, rfl⟩
    exact ⟨σ, typed, equivalent⟩
  · rintro ⟨σ, typed, equivalent⟩
    exact ⟨K.plug σ, equivalent, σ, typed, rfl⟩

/-- **The obligation** a goal places on the fillings. -/
def obligation (φ : EquationPredicate S) (σ : H → S.Term) : Prop :=
  φ.1 (K.plug σ)

/-- **Typed holes meet a goal exactly when every well-typed filling meets
the obligation.** -/
theorem completionType_implies_iff (ψ : H → EquationPredicate S) (φ : EquationPredicate S) :
    (∀ t, (K.completionType ψ).1 t → φ.1 t) ↔ ∀ σ, WellTyped ψ σ → K.obligation φ σ := by
  constructor
  · intro implies σ typed
    exact implies _ ((K.completionType_apply ψ _).mpr ⟨σ, typed, S.equations.iseqv.refl _⟩)
  · intro obliged t member
    obtain ⟨σ, typed, equivalent⟩ := (K.completionType_apply ψ t).mp member
    exact (φ.2 equivalent).mpr (obliged σ typed)

/-- Refining hole types refines the completion type. -/
theorem completionType_mono {ψ ψ' : H → EquationPredicate S}
    (refines : ∀ h t, (ψ h).1 t → (ψ' h).1 t) (t : S.Term)
    (member : (K.completionType ψ).1 t) : (K.completionType ψ').1 t := by
  obtain ⟨σ, typed, equivalent⟩ := (K.completionType_apply ψ t).mp member
  exact (K.completionType_apply ψ' t).mpr ⟨σ, fun h => refines h _ (typed h), equivalent⟩

/-- The one-hole partial program given by an equation-respecting map. -/
def ofMap (f : EquationRespectingMap S S) : PartialProgram S Unit where
  plug σ := f.toFun (σ ())
  plug_resp related := f.map_equiv (related ())

/-- **With one hole, the completion type is OSLF's direct image.** -/
theorem ofMap_completionType (f : EquationRespectingMap S S) (ψ : EquationPredicate S)
    (t : S.Term) :
    ((ofMap f).completionType fun _ => ψ).1 t ↔ (f.directImage ψ).1 t := by
  rw [completionType_apply, directImage_apply]
  constructor
  · rintro ⟨σ, typed, equivalent⟩
    exact ⟨σ (), S.equations.iseqv.symm equivalent, typed ()⟩
  · rintro ⟨P, equivalent, typed⟩
    exact ⟨fun _ => P, fun _ => typed, S.equations.iseqv.symm equivalent⟩

/-- **With one hole, the obligation is OSLF's pullback.** -/
theorem ofMap_obligation (f : EquationRespectingMap S S) (φ : EquationPredicate S)
    (P : S.Term) : (ofMap f).obligation φ (fun _ => P) ↔ (f.pullback φ).1 P :=
  Iff.rfl

/-- **The weakest type for a single hole is the pullback of the goal**: the
direct image–pullback adjunction of OSLF, read as hole typing. -/
theorem singleHole_galois (f : EquationRespectingMap S S) (ψ φ : EquationPredicate S) :
    (∀ t, (f.directImage ψ).1 t → φ.1 t) ↔ ∀ P, ψ.1 P → (f.pullback φ).1 P := by
  have viaHoles : (∀ t, (f.directImage ψ).1 t → φ.1 t) ↔
      ∀ t, ((ofMap f).completionType fun _ => ψ).1 t → φ.1 t :=
    forall_congr' fun t => imp_congr_left (ofMap_completionType f ψ t).symm
  rw [viaHoles, completionType_implies_iff]
  constructor
  · intro obliged P typed
    exact obliged (fun _ => P) fun _ => typed
  · intro obliged σ typed
    exact obliged (σ ()) (typed ())

/-- Plugging one partial program into the hole of another composes the
completion types. -/
theorem ofMap_comp_completionType (f g : EquationRespectingMap S S) (ψ : EquationPredicate S)
    (t : S.Term) :
    ((ofMap ⟨fun P => f.toFun (g.toFun P), fun related => f.map_equiv (g.map_equiv related)⟩).completionType
        fun _ => ψ).1 t ↔
      ((ofMap f).completionType fun _ => (ofMap g).completionType fun _ => ψ).1 t := by
  rw [completionType_apply, completionType_apply]
  constructor
  · rintro ⟨σ, typed, equivalent⟩
    exact ⟨fun _ => g.toFun (σ ()),
      fun _ => ((ofMap g).completionType_apply _ _).mpr ⟨σ, typed, S.equations.iseqv.refl _⟩,
      equivalent⟩
  · rintro ⟨σ, typed, equivalent⟩
    obtain ⟨τ, typedτ, equivalentτ⟩ := ((ofMap g).completionType_apply _ _).mp (typed ())
    exact ⟨τ, typedτ, S.equations.iseqv.trans equivalent (f.map_equiv equivalentτ)⟩

/-- Place a partial program into a context, given as an equation-respecting
map. -/
def inContext (f : EquationRespectingMap S S) : PartialProgram S H where
  plug σ := f.toFun (K.plug σ)
  plug_resp := fun related => f.map_equiv (K.plug_resp related)

/-- **Placing a partial program into a context translates its completion
type by direct image.** -/
theorem completionType_inContext (f : EquationRespectingMap S S)
    (ψ : H → EquationPredicate S) (t : S.Term) :
    ((K.inContext f).completionType ψ).1 t ↔ (f.directImage (K.completionType ψ)).1 t := by
  rw [completionType_apply, directImage_apply]
  constructor
  · rintro ⟨σ, typed, equivalent⟩
    exact ⟨K.plug σ, S.equations.iseqv.symm equivalent,
      (K.completionType_apply ψ _).mpr ⟨σ, typed, S.equations.iseqv.refl _⟩⟩
  · rintro ⟨P, equivalent, member⟩
    obtain ⟨σ, typed, equivalentP⟩ := (K.completionType_apply ψ P).mp member
    exact ⟨σ, typed,
      S.equations.iseqv.trans (S.equations.iseqv.symm equivalent) (f.map_equiv equivalentP)⟩

/-- A partial program without holes has the native type of its program as
completion type. -/
theorem completionType_noHoles (K : PartialProgram S PEmpty) (ψ : PEmpty → EquationPredicate S)
    (t : S.Term) :
    (K.completionType ψ).1 t ↔ (nativeTypeOf S (K.plug PEmpty.elim)).1 t := by
  rw [completionType_apply, nativeTypeOf_apply]
  constructor
  · rintro ⟨σ, _, equivalent⟩
    have only : σ = PEmpty.elim := funext fun h => h.elim
    subst only
    exact equivalent
  · intro equivalent
    exact ⟨PEmpty.elim, fun h => h.elim, equivalent⟩

end PartialProgram

/-! ### Control: restricting the language of partial programs -/

namespace StaticFragment

open Mettapedia.OSLF.Programs.GradualTypes

/-- An abstraction within an admissible class `U` of partial programs. -/
def IsAbstractionIn {Prog : Type u} {Part : Type v} (Completes : Prog → Part → Prop)
    (U : Set Part) (K : Set Prog) (A : Part) : Prop :=
  A ∈ U ∧ K ⊆ completionSpace Completes A ∧
    ∀ P ∈ U, K ⊆ completionSpace Completes P → Refines Completes A P

/-- The static types, as gradual types. -/
def static : Set GType := Set.range SType.toG

/-- **In the static fragment, `{Int, Bool}` has no abstraction**: no static type
stands for both. -/
theorem no_abstraction (A : GType) :
    ¬ IsAbstractionIn Conc static {SType.int, SType.bool} A := by
  rintro ⟨⟨T, rfl⟩, covers, _⟩
  have hInt : SType.int ∈ completionSpace Conc T.toG := covers (Or.inl rfl)
  have hBool : SType.bool ∈ completionSpace Conc T.toG := covers (Or.inr rfl)
  rw [mem_completionSpace, conc_toG_iff] at hInt hBool
  exact SType.noConfusion (hInt.trans hBool.symm)

/-- **In the full gradual language, its abstraction is `?`.** -/
theorem unknown_abstracts : IsAbstraction Conc {SType.int, SType.bool} GType.unknown := by
  refine ⟨fun T _ => (mem_completionSpace Conc).mpr (.unknown T), fun P covers => ?_⟩
  have hInt : Conc .int P := (mem_completionSpace Conc).mp (covers (Or.inl rfl))
  have hBool : Conc .bool P := (mem_completionSpace Conc).mp (covers (Or.inr rfl))
  cases hInt with
  | unknown => exact Refines.refl Conc _
  | int => cases hBool

end StaticFragment

/-! ### Controls: joint obligations are relations -/

namespace Obligations

open PartialProgram

/-- Boolean programs, with syntactic equations and no steps. -/
abbrev bools : GSLT.{0} :=
  equalityGSLT Bool fun _ _ => False

/-- The goal "is `true`". -/
def isTrue : EquationPredicate bools :=
  ⟨fun b => b = true, fun a b equal => by
    have same : a = b := equal
    rw [same]⟩

/-- `x == y`, with its two holes indexed by `Bool`. -/
def equality : PartialProgram bools Bool where
  plug σ := !(Bool.xor (σ true) (σ false))
  plug_resp {σ τ} related := by
    have first : σ true = τ true := related true
    have second : σ false = τ false := related false
    show (!(Bool.xor (σ true) (σ false))) = !(Bool.xor (τ true) (τ false))
    rw [first, second]

/-- `x && y`. -/
def conjunction : PartialProgram bools Bool where
  plug σ := Bool.and (σ true) (σ false)
  plug_resp {σ τ} related := by
    have first : σ true = τ true := related true
    have second : σ false = τ false := related false
    show Bool.and (σ true) (σ false) = Bool.and (τ true) (τ false)
    rw [first, second]

theorem equality_obligation_iff (σ : Bool → bools.Term) :
    equality.obligation isTrue σ ↔ Bool.xor (σ true) (σ false) = false := by
  show (!(Bool.xor (σ true) (σ false))) = true ↔ _
  generalize Bool.xor (σ true) (σ false) = b
  cases b <;> decide

/-- **Negative control**: the obligation of `x == y` is the diagonal, which is
not a product of per-hole types. -/
theorem equality_not_rectangular :
    ¬ ∃ ψ : Bool → EquationPredicate bools,
      ∀ σ, equality.obligation isTrue σ ↔ WellTyped ψ σ := by
  rintro ⟨ψ, same⟩
  have both : ∀ b : Bool, WellTyped ψ fun _ => b := fun b =>
    (same fun _ => b).mp ((equality_obligation_iff _).mpr (Bool.xor_self b))
  have mixed : WellTyped ψ fun h => h := fun h => by
    cases h
    · exact both false false
    · exact both true true
  have diagonal := (equality_obligation_iff _).mp ((same fun h => h).mpr mixed)
  exact Bool.noConfusion diagonal

/-- **Positive control**: the obligation of `x && y` is the product of the
per-hole types "is `true`". -/
theorem conjunction_rectangular (σ : Bool → Bool) :
    conjunction.obligation isTrue σ ↔ WellTyped (fun _ => isTrue) σ := by
  change Bool.and (σ true) (σ false) = true ↔ ∀ h, σ h = true
  rw [Bool.and_eq_true]
  constructor
  · rintro ⟨hTrue, hFalse⟩ h
    cases h
    · exact hFalse
    · exact hTrue
  · intro all
    exact ⟨all true, all false⟩

end Obligations

end Mettapedia.OSLF.Programs.Completion
