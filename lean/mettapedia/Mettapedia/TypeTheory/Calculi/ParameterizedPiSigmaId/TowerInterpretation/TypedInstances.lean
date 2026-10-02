import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.Soundness
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.RootPreservation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.ComputationSchemas
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Domain.ChurchDefinitions

/-!
# Traced graphs over telescopes, and root steps at their typed instances

A constant that computes cannot preserve values at every environment of a set model: outside
the domain of its declared type a trace function gives the empty set. What a root step can
satisfy is **validity at its typed instances**: at the environments whose values lie in the
values of the types the positions of its left side require, and satisfy the equations of its
reflexivity positions (`TypedInstance`), its two sides have one value (`SchemaValid`). These are
the facts pattern inversion (`Annotated.pattern_inv`) concludes of a typed instance of a
first-order left side, so a root rule whose premises type the instances of the redex's
metavariables discharges them through the soundness of those premises
(`typedInstance_of_holds`), and an instance of a valid schema by a substitution has one value
on both sides (`SchemaValid.instantiate`).

**Values read only the constants a term mentions** (`ev_congr_consts`), which is what lets the
values of a package's constants be built stage by stage.

**Traced graphs over a telescope.** The value of a constant with a curried declared type is
the traced graph, over the telescope of that type, of a family of values
(`telescopeGraph`); the value of the type is the set of trace functions over the telescope
(`telescopeProduct`, `ev_pisCtx`). Applied to an environment that satisfies the telescope, the
traced graph gives the family's value there (`applyValues_telescopeGraph`), and it lies in the
product when the family lies in its fibres (`telescopeGraph_mem`). The abstraction of a term
over a telescope denotes the traced graph of the term's values (`ev_lamsCtx`).

**Definitions by one equation** (`definition_valid`): if a constant's value is the traced graph
of the values of its elaborated right side over the telescope its equation's positions require,
its defining step is valid at typed instances.

**Extensions of a package change the values of names it does not declare.** A typed term
mentions only declared constants (`CDerivable.consts_declared`), so its value is the same at two
assignments that agree on the declared names (`CDerivable.ev_congr_declared`); and the validity
of a schema at its typed instances depends only on the values of the constants its elaborated
sides, the types its left side requires and its equations mention
(`SchemaValid.congr_consts`). A package whose declared types and schema templates mention only
admitted constants (`SchemaClosed`, tested by `schemaClosed`) therefore has a set model at every
assignment that agrees with a given one on the admitted constants
(`SetModel.ofSchemas_agreeing`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation

open Presentation Presentation.TypedEquality.Annotated
open Presentation.TypedEquality.Impredicative.Domain (termConsts lamsCtx pisCtx)
open TelescopeAbstraction (applyClosed)
open Mettapedia.Logic.HOL.Embedding
open ZFSetDependentProducts (graph)
open ZFSetTraceProducts (traceLam traceApp tracePiSet traceApp_graph_beta)

universe u

variable {Head : Type}

section Values

variable (heads : Head → ZFSet.{u}) (consts : DeclName → ZFSet.{u})

/-! ## Values read only the constants a term mentions -/

/-- **The value of a term reads only the constants it mentions.** -/
theorem ev_congr_consts {consts' : DeclName → ZFSet.{u}} :
    ∀ {n : Nat} (t : CTm Head n), (∀ c ∈ termConsts t, consts c = consts' c) →
      ∀ ρ : Env.{u} n, ev heads consts t ρ = ev heads consts' t ρ := by
  intro n t
  induction t with
  | var i => exact fun _ _ => rfl
  | const c => exact fun agree _ => agree c (List.mem_singleton_self c)
  | head h => exact fun _ _ => rfl
  | pi A B ihA ihB =>
      intro agree ρ
      change tracePiSet (ev heads consts A ρ) (fun x => ev heads consts B (extend ρ x)) =
        tracePiSet (ev heads consts' A ρ) (fun x => ev heads consts' B (extend ρ x))
      rw [ihA (fun c h => agree c (List.mem_append_left _ h)) ρ]
      congr 1
      funext x
      exact ihB (fun c h => agree c (List.mem_append_right _ h)) _
  | sigma A B ihA ihB =>
      intro agree ρ
      change ZFSetDependentProducts.sigmaSet (ev heads consts A ρ)
          (fun x => ev heads consts B (extend ρ x)) =
        ZFSetDependentProducts.sigmaSet (ev heads consts' A ρ)
          (fun x => ev heads consts' B (extend ρ x))
      rw [ihA (fun c h => agree c (List.mem_append_left _ h)) ρ]
      congr 1
      funext x
      exact ihB (fun c h => agree c (List.mem_append_right _ h)) _
  | id A a b _ iha ihb =>
      intro agree ρ
      change ZFSetTraceProofDecoding.truthCode (ev heads consts a ρ = ev heads consts b ρ) =
        ZFSetTraceProofDecoding.truthCode (ev heads consts' a ρ = ev heads consts' b ρ)
      rw [iha (fun c h => agree c (List.mem_append_right _ (List.mem_append_left _ h))) ρ,
        ihb (fun c h => agree c (List.mem_append_right _ (List.mem_append_right _ h))) ρ]
  | lam A b ihA ihb =>
      intro agree ρ
      change traceLam (graph (ev heads consts A ρ) (fun x => ev heads consts b (extend ρ x))) =
        traceLam (graph (ev heads consts' A ρ) (fun x => ev heads consts' b (extend ρ x)))
      rw [ihA (fun c h => agree c (List.mem_append_left _ h)) ρ]
      congr 2
      funext x
      exact ihb (fun c h => agree c (List.mem_append_right _ h)) _
  | app f a ihf iha =>
      intro agree ρ
      change traceApp (ev heads consts f ρ) (ev heads consts a ρ) =
        traceApp (ev heads consts' f ρ) (ev heads consts' a ρ)
      rw [ihf (fun c h => agree c (List.mem_append_left _ h)) ρ,
        iha (fun c h => agree c (List.mem_append_right _ h)) ρ]
  | pair a b iha ihb =>
      intro agree ρ
      change ZFSet.pair (ev heads consts a ρ) (ev heads consts b ρ) =
        ZFSet.pair (ev heads consts' a ρ) (ev heads consts' b ρ)
      rw [iha (fun c h => agree c (List.mem_append_left _ h)) ρ,
        ihb (fun c h => agree c (List.mem_append_right _ h)) ρ]
  | fst p ih =>
      intro agree ρ
      change Mettapedia.SetTheory.ZFSetOrderedPair.first (ev heads consts p ρ) =
        Mettapedia.SetTheory.ZFSetOrderedPair.first (ev heads consts' p ρ)
      rw [ih agree ρ]
  | snd p ih =>
      intro agree ρ
      change Mettapedia.SetTheory.ZFSetOrderedPair.second (ev heads consts p ρ) =
        Mettapedia.SetTheory.ZFSetOrderedPair.second (ev heads consts' p ρ)
      rw [ih agree ρ]
  | refl a _ => exact fun _ _ => rfl

/-- A constant mentioned by the codomain of a dependent function type over a telescope is
mentioned by the type. -/
theorem termConsts_pisCtx_of_mem :
    ∀ {k : Nat} (Θ : CCtx Head k) {T : CTm Head k} {c : DeclName},
      c ∈ termConsts T → c ∈ termConsts (pisCtx Θ T)
  | _, .nil, _, _, h => h
  | _, .snoc Θ _, _, _, h => termConsts_pisCtx_of_mem Θ (List.mem_append_right _ h)

/-! ## Traced graphs over a telescope -/

/-- **The traced graph of a family of values over a telescope**, curried: over the empty
telescope the family's value, and over `Θ, A` the traced graph over `Θ` of the traced graphs
over the values of `A`. -/
noncomputable def telescopeGraph : {k : Nat} → CCtx Head k → (Env.{u} k → ZFSet.{u}) → ZFSet.{u}
  | _, .nil, body => body Fin.elim0
  | _, .snoc Θ A, body => telescopeGraph Θ fun η =>
      traceLam (graph (ev heads consts A η) fun x => body (extend η x))

/-- The set of trace functions over a telescope into a family of sets. -/
noncomputable def telescopeProduct :
    {k : Nat} → CCtx Head k → (Env.{u} k → ZFSet.{u}) → ZFSet.{u}
  | _, .nil, family => family Fin.elim0
  | _, .snoc Θ A, family => telescopeProduct Θ fun η =>
      tracePiSet (ev heads consts A η) fun x => family (extend η x)

/-- A trace function applied to the values of an environment, the oldest first. -/
noncomputable def applyValues (f : ZFSet.{u}) : (k : Nat) → Env.{u} k → ZFSet.{u}
  | 0, _ => f
  | k + 1, η => traceApp (applyValues f k (η ∘ Fin.succ)) (η 0)

theorem extend_tail_head {k : Nat} (η : Env.{u} (k + 1)) : extend (η ∘ Fin.succ) (η 0) = η := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

/-- An environment of an extended telescope satisfies the telescope at its older values, and
its newest value lies in the newest type there. -/
theorem sat_tail {k : Nat} {Θ : CCtx Head k} {A : CTm Head k} {η : Env.{u} (k + 1)}
    (sat : Sat heads consts (Θ.snoc A) η) :
    Sat heads consts Θ (η ∘ Fin.succ) ∧ η 0 ∈ ev heads consts A (η ∘ Fin.succ) := by
  rw [← extend_tail_head η] at sat
  exact (sat_snoc heads consts).mp sat

/-- **β for traced graphs over a telescope**: applied to the values of an environment that
satisfies the telescope, the traced graph of a family gives the family's value there. -/
theorem applyValues_telescopeGraph :
    ∀ {k : Nat} (Θ : CCtx Head k) (body : Env.{u} k → ZFSet.{u}) (η : Env.{u} k),
      Sat heads consts Θ η → applyValues (telescopeGraph heads consts Θ body) k η = body η
  | _, .nil, body, η, _ => by
      show body Fin.elim0 = body η
      congr 1
      funext i
      exact i.elim0
  | _, .snoc Θ A, body, η, sat => by
      obtain ⟨satΘ, hx⟩ := sat_tail heads consts sat
      show traceApp (applyValues (telescopeGraph heads consts Θ fun η =>
          traceLam (graph (ev heads consts A η) fun x => body (extend η x))) _ (η ∘ Fin.succ))
        (η 0) = body η
      rw [applyValues_telescopeGraph Θ _ (η ∘ Fin.succ) satΘ, traceApp_graph_beta _ hx,
        extend_tail_head]

/-- An abstraction lies in a dependent function type over its own domain when its body lies
in the codomain at every point of the domain. -/
theorem ev_lam_mem_pi {n : Nat} {A : CTm Head n} {b B : CTm Head (n + 1)} {ρ : Env.{u} n}
    (typed : ∀ x ∈ ev heads consts A ρ,
      ev heads consts b (extend ρ x) ∈ ev heads consts B (extend ρ x)) :
    ev heads consts (.lam A b) ρ ∈ ev heads consts (.pi A B) ρ :=
  traceLam_graph_mem typed

/-- **A traced graph over a telescope lies in the product** when the family lies in the
fibres at every environment satisfying the telescope. -/
theorem telescopeGraph_mem :
    ∀ {k : Nat} (Θ : CCtx Head k) {body family : Env.{u} k → ZFSet.{u}},
      (∀ η, Sat heads consts Θ η → body η ∈ family η) →
        telescopeGraph heads consts Θ body ∈ telescopeProduct heads consts Θ family
  | _, .nil, _, _, typed => typed Fin.elim0 (sat_nil heads consts Fin.elim0)
  | _, .snoc Θ _, _, _, typed =>
      telescopeGraph_mem Θ fun η sat => traceLam_graph_mem fun x hx =>
        typed (extend η x) ((sat_snoc heads consts).mpr ⟨sat, hx⟩)

/-- **The abstraction of a term over a telescope denotes the traced graph of its values.** -/
theorem ev_lamsCtx : ∀ {k : Nat} (Θ : CCtx Head k) (E : CTm Head k),
    ev heads consts (lamsCtx Θ E) Fin.elim0 =
      telescopeGraph heads consts Θ fun η => ev heads consts E η
  | _, .nil, _ => rfl
  | _, .snoc Θ A, E => ev_lamsCtx Θ (.lam A E)

/-- **A dependent function type over a telescope denotes the product over it.** -/
theorem ev_pisCtx : ∀ {k : Nat} (Θ : CCtx Head k) (T : CTm Head k),
    ev heads consts (pisCtx Θ T) Fin.elim0 =
      telescopeProduct heads consts Θ fun η => ev heads consts T η
  | _, .nil, _ => rfl
  | _, .snoc Θ A, T => ev_pisCtx Θ (.pi A T)

/-- **A traced graph over a telescope lies in the value of the dependent function type** over
it, when the family lies in the codomain's values. -/
theorem telescopeGraph_mem_pisCtx {k : Nat} (Θ : CCtx Head k) (T : CTm Head k)
    {body : Env.{u} k → ZFSet.{u}}
    (typed : ∀ η, Sat heads consts Θ η → body η ∈ ev heads consts T η) :
    telescopeGraph heads consts Θ body ∈ ev heads consts (pisCtx Θ T) Fin.elim0 := by
  rw [ev_pisCtx]
  exact telescopeGraph_mem heads consts Θ typed

/-- A traced graph over a telescope reads only the constants of the telescope's types. -/
theorem telescopeGraph_congr {consts' : DeclName → ZFSet.{u}} :
    ∀ {k : Nat} (Θ : CCtx Head k) (T : CTm Head k),
      (∀ c ∈ termConsts (pisCtx Θ T), consts c = consts' c) →
      ∀ body : Env.{u} k → ZFSet.{u},
        telescopeGraph heads consts Θ body = telescopeGraph heads consts' Θ body
  | _, .nil, _, _, _ => rfl
  | _, .snoc Θ A, T, agree, body => by
      have agreeA : ∀ c ∈ termConsts A, consts c = consts' c := fun c h =>
        agree c (termConsts_pisCtx_of_mem Θ (T := .pi A T) (List.mem_append_left _ h))
      show telescopeGraph heads consts Θ (fun η =>
          traceLam (graph (ev heads consts A η) fun x => body (extend η x))) =
        telescopeGraph heads consts' Θ (fun η =>
          traceLam (graph (ev heads consts' A η) fun x => body (extend η x)))
      rw [telescopeGraph_congr Θ (.pi A T) agree]
      congr 1
      funext η
      rw [ev_congr_consts heads consts A agreeA η]

/-! ## Constants applied to the arguments of a telescope -/

/-- **The value of a constant applied to arguments, in telescope order**, is its value applied
to the arguments' values. -/
theorem ev_applyClosed :
    ∀ {k m : Nat} (Θ : Ctx Head k) (σ : Sub Head k m) (f : DeclName) (ρ : Env.{u} m),
      ev heads consts (liftTm (applyClosed Θ σ (.const f))) ρ =
        applyValues (consts f) k fun i => ev heads consts (liftTm (σ i)) ρ
  | _, _, .nil, _, _, _ => rfl
  | _, _, .snoc Θ _, σ, f, ρ => by
      show traceApp (ev heads consts (liftTm (applyClosed Θ (fun i => σ i.succ) (.const f))) ρ)
        (ev heads consts (liftTm (σ 0)) ρ) = _
      rw [ev_applyClosed Θ (fun i => σ i.succ) f ρ]
      rfl

end Values

/-- A constant applied to first-order arguments is first-order. -/
theorem firstOrder_applyClosed :
    ∀ {k m : Nat} (Θ : Ctx Head k) {σ : Sub Head k m} (f : DeclName),
      (∀ i, firstOrder (σ i) = true) → firstOrder (applyClosed Θ σ (.const f)) = true
  | _, _, .nil, _, _, _ => rfl
  | _, _, .snoc Θ _, σ, f, h => by
      show (firstOrder (applyClosed Θ (fun i => σ i.succ) (.const f)) && firstOrder (σ 0)) = true
      rw [firstOrder_applyClosed Θ f (fun i => h i.succ), h 0]
      rfl

/-! ## Root steps at typed instances -/

section Typed

variable (heads : Head → ZFSet.{u}) (consts : DeclName → ZFSet.{u})
  (decls : DeclName → Option (CTm Head 0))

/-- **A typed instance of a first-order left side**: the values of its metavariables lie in
the values of the types its positions require (`patternKnowledge`), and the point of each
reflexivity position has the value of its endpoints (`patternEquations`). -/
def TypedInstance {k : Nat} (L : Tm Head k) (η : Env.{u} k) : Prop :=
  (∀ i T, patternKnowledge decls none L i = some T → η i ∈ ev heads consts T η) ∧
    ∀ e ∈ patternEquations decls none L, ev heads consts e.1 η = ev heads consts e.2.1 η

/-- **A rewrite schema is valid at its typed instances**: at every typed instance of its left
side, its elaborated left and right sides have one value. -/
def SchemaValid {k : Nat} (L R : Tm Head k) : Prop :=
  ∀ η : Env.{u} k, TypedInstance heads consts decls L η →
    ev heads consts (elabLeft decls L) η = ev heads consts (elabRight decls L R) η

/-- Every schema of a family is valid at its typed instances. -/
def FamilyValid (S : AlgebraicSchema.SchemaFamily Head) : Prop :=
  ∀ {k : Nat} {L R : Tm Head k}, S L R → SchemaValid heads consts decls L R

variable {heads consts decls}

/-- **An instance of a valid schema has one value on both sides**, at every environment at
which the values of the substituted terms form a typed instance. -/
theorem SchemaValid.instantiate {k n : Nat} {L R : Tm Head k}
    (valid : SchemaValid heads consts decls L R) (σ : CSub Head k n) (ρ : Env.{u} n)
    (typed : TypedInstance heads consts decls L fun i => ev heads consts (σ i) ρ) :
    ev heads consts ((elabLeft decls L).subst σ) ρ =
      ev heads consts ((elabRight decls L R).subst σ) ρ := by
  rw [ev_subst, ev_subst]
  exact valid _ typed

/-- **The premises a typed root rule carries give typed instances.** If the typings of the
instances of the metavariables at the types the left side's positions require, and the
equations of its reflexivity positions, hold in the set model at a context, then at every
environment satisfying the context the values of the instances form a typed instance. -/
theorem typedInstance_of_holds {k n : Nat} {L : Tm Head k} {Γ : CCtx Head n}
    {σ : CSub Head k n} {ρ : Env.{u} n} (sat : Sat heads consts Γ ρ)
    (typings : ∀ i T, patternKnowledge decls none L i = some T →
      Holds heads consts (CStatement.typing Γ (σ i) (T.subst σ)))
    (equations : ∀ e ∈ patternEquations decls none L,
      Holds heads consts (CStatement.equality Γ (e.1.subst σ) (e.2.1.subst σ) (e.2.2.subst σ))) :
    TypedInstance heads consts decls L fun i => ev heads consts (σ i) ρ := by
  refine ⟨fun i T known => ?_, fun e mem => ?_⟩
  · have typed := typings i T known ρ sat
    rwa [ev_subst] at typed
  · have equal := (equations e mem ρ sat).1
    rwa [ev_subst, ev_subst] at equal

/-- **The root steps of a package annotated from schemas hold where their premises hold**,
when every schema of the family is valid at its typed instances: the premises of an instance
are the facts a typed instance needs. -/
theorem FamilyValid.steps {R : Rules Head} {S : AlgebraicSchema.SchemaFamily Head}
    {present : Presents R.computation S}
    (valid : FamilyValid heads consts (elabDeclarations R.constantType) S) {n : Nat}
    {Γ : CCtx Head n} {l r : CTm Head n} {premises : List (CPremise Head n)}
    (requires : (ChurchRules.ofSchemas R S present).computation.requires l r premises)
    (holds : ∀ premise ∈ premises, Holds heads consts (premise.statement Γ)) (ρ : Env.{u} n)
    (sat : Sat heads consts Γ ρ) : ev heads consts l ρ = ev heads consts r ρ := by
  cases requires with
  | instantiate rule σ =>
      exact (valid rule).instantiate σ ρ (typedInstance_of_holds sat
        (fun i T known => holds _ (mem_patternPremises.2 (.inl ⟨i, T, known, rfl⟩)))
        (fun e member => holds _ (mem_patternPremises.2 (.inr ⟨e, member, rfl⟩))))

/-- **A set model of a package annotated from schemas**: closed universes, equal values for
equal heads, declared constants in their declared types, and schemas valid at their typed
instances. -/
theorem SetModel.ofSchemas {R : Rules Head} {S : AlgebraicSchema.SchemaFamily Head}
    {present : Presents R.computation S}
    (universes : ZFSetReplayInterpretation.UniverseModel R heads)
    (headEq : ∀ {h h' : Head}, R.headEq h h' → heads h = heads h')
    (constants : ∀ {c : DeclName} {T : CTm Head 0},
      (ChurchRules.ofSchemas R S present).constantType c = some T →
        consts c ∈ ev heads consts T Fin.elim0)
    (valid : FamilyValid heads consts (elabDeclarations R.constantType) S) :
    SetModel heads consts (ChurchRules.ofSchemas R S present) where
  universes := universes
  headEq := headEq
  constants := constants
  steps := fun _ requires holds ρ sat => valid.steps requires holds ρ sat

/-- A typed instance of a left side whose positions require the types of an annotated
telescope satisfies the telescope. -/
theorem TypedInstance.sat {k : Nat} {L : Tm Head k} {Θ : CCtx Head k}
    (known : ∀ i, patternKnowledge decls none L i = some (Θ.lookup i)) {η : Env.{u} k}
    (typed : TypedInstance heads consts decls L η) : Sat heads consts Θ η :=
  fun i => typed.1 i _ (known i)

/-- **Definitions by one equation are valid at typed instances.** If the value of `f` is the
traced graph, over the telescope its equation's positions require, of the values of its
elaborated right side, its defining step `f x₁ ⋯ x_k ⟶ rhs` is valid at typed instances. -/
theorem definition_valid {f : DeclName} {k : Nat} {Θ : Ctx Head k} {rhs : Tm Head k}
    (ΘA : CCtx Head k)
    (known : ∀ i, patternKnowledge decls none (applyClosed Θ Presentation.ids (.const f)) i =
      some (ΘA.lookup i))
    (value : consts f = telescopeGraph heads consts ΘA fun η =>
      ev heads consts (elabRight decls (applyClosed Θ Presentation.ids (.const f)) rhs) η) :
    SchemaValid heads consts decls (applyClosed Θ Presentation.ids (.const f)) rhs := by
  intro η typed
  have sat : Sat heads consts ΘA η := typed.sat known
  rw [elabLeft_firstOrder decls (firstOrder_applyClosed Θ f fun _ => rfl)]
  change ev heads consts (liftTm (applyClosed Θ Presentation.ids (.const f))) η = _
  rw [ev_applyClosed heads consts Θ Presentation.ids f η]
  change applyValues (consts f) k η = _
  rw [value, applyValues_telescopeGraph heads consts ΘA _ η sat]

end Typed

/-! ## A typed term mentions only declared constants -/

/-- The constants of the subject of a typing statement are declared. -/
def SubjectDeclared {R : Rules Head} (P : ChurchRules R) : CStatement Head → Prop
  | .typing _ t _ => ∀ c ∈ termConsts t, P.constantType c ≠ none
  | _ => True

/-- **A typed term mentions only declared constants.** -/
theorem CDerivable.subjectDeclared {R : Rules Head} {P : ChurchRules R} {s : CStatement Head}
    (d : CDerivable P s) : SubjectDeclared P s := by
  induction d with
  | headType _ => exact fun _ mem => absurd mem List.not_mem_nil
  | var i => exact fun _ mem => absurd mem List.not_mem_nil
  | const declared _ _ _ =>
    intro c mem
    obtain rfl := List.mem_singleton.mp mem
    rw [declared]
    exact fun impossible => nomatch impossible
  | piForm _ _ _ _ _ ihA ihB =>
    intro c mem
    rcases List.mem_append.mp mem with h | h
    · exact ihA c h
    · exact ihB c h
  | sigmaForm _ _ _ _ _ ihA ihB =>
    intro c mem
    rcases List.mem_append.mp mem with h | h
    · exact ihA c h
    · exact ihB c h
  | lamIntro _ _ _ _ _ ihA _ ihBody =>
    intro c mem
    rcases List.mem_append.mp mem with h | h
    · exact ihA c h
    · exact ihBody c h
  | appElim _ _ ihg iha =>
    intro c mem
    rcases List.mem_append.mp mem with h | h
    · exact ihg c h
    · exact iha c h
  | pairIntro _ _ _ _ _ iha ihb =>
    intro c mem
    rcases List.mem_append.mp mem with h | h
    · exact iha c h
    · exact ihb c h
  | fstElim _ ih => exact ih
  | sndElim _ ih => exact ih
  | idForm _ _ _ _ ihA iha ihb =>
    intro c mem
    rcases List.mem_append.mp mem with h | h
    · exact ihA c h
    · rcases List.mem_append.mp h with h | h
      · exact iha c h
      · exact ihb c h
  | reflIntro _ ih => exact ih
  | sub _ _ ih _ => exact ih
  | conv _ _ _ ih _ => exact ih
  | _ => trivial

/-- A typed term mentions only declared constants. -/
theorem CDerivable.consts_declared {R : Rules Head} {P : ChurchRules R} {n : Nat}
    {Γ : CCtx Head n} {t A : CTm Head n} (typed : CDerivable P (.typing Γ t A)) :
    ∀ c ∈ termConsts t, P.constantType c ≠ none :=
  CDerivable.subjectDeclared typed

/-- **The value of a typed term reads only the declared constants.** -/
theorem CDerivable.ev_congr_declared {R : Rules Head} {P : ChurchRules R}
    (heads : Head → ZFSet.{u}) {consts consts' : DeclName → ZFSet.{u}}
    (same : ∀ c, P.constantType c ≠ none → consts c = consts' c) {n : Nat} {Γ : CCtx Head n}
    {t A : CTm Head n} (typed : CDerivable P (.typing Γ t A)) (ρ : Env.{u} n) :
    ev heads consts t ρ = ev heads consts' t ρ :=
  ev_congr_consts heads consts t (fun c mem => same c (CDerivable.consts_declared typed c mem)) ρ

/-! ## Validity of a schema reads only the constants its template mentions -/

/-- **The validity of a schema at its typed instances depends only on the values of the
constants its elaborated sides, the types its left side requires, and its equations
mention.** -/
theorem SchemaValid.congr_consts {heads : Head → ZFSet.{u}} {consts consts' : DeclName → ZFSet.{u}}
    {decls : DeclName → Option (CTm Head 0)} {k : Nat} {L R : Tm Head k}
    (left : ∀ c ∈ termConsts (elabLeft decls L), consts c = consts' c)
    (right : ∀ c ∈ termConsts (elabRight decls L R), consts c = consts' c)
    (types : ∀ i T, patternKnowledge decls none L i = some T →
      ∀ c ∈ termConsts T, consts c = consts' c)
    (equations : ∀ e ∈ patternEquations decls none L,
      (∀ c ∈ termConsts e.1, consts c = consts' c) ∧
        ∀ c ∈ termConsts e.2.1, consts c = consts' c)
    (valid : SchemaValid heads consts decls L R) : SchemaValid heads consts' decls L R := by
  intro η typed
  have typed₀ : TypedInstance heads consts decls L η := by
    refine ⟨fun i T known => ?_, fun e mem => ?_⟩
    · have member := typed.1 i T known
      rwa [← ev_congr_consts heads consts T (types i T known) η] at member
    · have equal := typed.2 e mem
      rwa [← ev_congr_consts heads consts e.1 (equations e mem).1 η,
        ← ev_congr_consts heads consts e.2.1 (equations e mem).2 η] at equal
  have key := valid η typed₀
  rwa [ev_congr_consts heads consts _ left η, ev_congr_consts heads consts _ right η] at key

/-! ## A set model at every assignment that agrees on the declared constants -/

/-- Whether every constant a term mentions is admitted. -/
def closedTerm (declared : DeclName → Bool) {n : Nat} (t : CTm Head n) : Bool :=
  (termConsts t).all declared

theorem closedTerm_iff {declared : DeclName → Bool} {n : Nat} {t : CTm Head n} :
    closedTerm declared t = true ↔ ∀ c ∈ termConsts t, declared c = true :=
  List.all_eq_true

/-- **The template of a schema mentions only admitted constants**: its elaborated sides, the
types the positions of its left side require, and the equations of its reflexivity
positions. -/
structure SchemaClosed (decls : DeclName → Option (CTm Head 0)) (declared : DeclName → Bool)
    {k : Nat} (L R : Tm Head k) : Prop where
  left : closedTerm declared (elabLeft decls L) = true
  right : closedTerm declared (elabRight decls L R) = true
  types : ∀ i T, patternKnowledge decls none L i = some T → closedTerm declared T = true
  equations : ∀ e ∈ patternEquations decls none L,
    closedTerm declared e.1 = true ∧ closedTerm declared e.2.1 = true

/-- The same as a computed test. -/
def schemaClosed (decls : DeclName → Option (CTm Head 0)) (declared : DeclName → Bool)
    {k : Nat} (L R : Tm Head k) : Bool :=
  closedTerm declared (elabLeft decls L) && (closedTerm declared (elabRight decls L R) &&
    ((List.finRange k).all (fun i =>
        match patternKnowledge decls none L i with
        | some T => closedTerm declared T
        | none => true) &&
      (patternEquations decls none L).all fun e =>
        closedTerm declared e.1 && closedTerm declared e.2.1))

/-- A schema that passes the test has a closed template. -/
theorem SchemaClosed.of_test {decls : DeclName → Option (CTm Head 0)}
    {declared : DeclName → Bool} {k : Nat} {L R : Tm Head k}
    (test : schemaClosed decls declared L R = true) : SchemaClosed decls declared L R := by
  simp only [schemaClosed, Bool.and_eq_true, List.all_eq_true] at test
  obtain ⟨left, right, types, equations⟩ := test
  refine ⟨left, right, fun i T known => ?_, equations⟩
  have found := types i (List.mem_finRange i)
  rw [known] at found
  exact found

/-- **The validity of a schema with a closed template is the same at two assignments that
agree on the admitted constants.** -/
theorem SchemaValid.of_closed {heads : Head → ZFSet.{u}} {consts consts' : DeclName → ZFSet.{u}}
    {decls : DeclName → Option (CTm Head 0)} {declared : DeclName → Bool} {k : Nat}
    {L R : Tm Head k} (closed : SchemaClosed decls declared L R)
    (same : ∀ c, declared c = true → consts c = consts' c)
    (valid : SchemaValid heads consts decls L R) : SchemaValid heads consts' decls L R :=
  SchemaValid.congr_consts
    (fun c mem => same c (closedTerm_iff.mp closed.left c mem))
    (fun c mem => same c (closedTerm_iff.mp closed.right c mem))
    (fun i T known c mem => same c (closedTerm_iff.mp (closed.types i T known) c mem))
    (fun e mem => ⟨fun c at_ => same c (closedTerm_iff.mp (closed.equations e mem).1 c at_),
      fun c at_ => same c (closedTerm_iff.mp (closed.equations e mem).2 c at_)⟩)
    valid

/-- **A set model of a package annotated from schemas, at every assignment that agrees with a
given one on the admitted constants.** The admitted constants contain the declared ones; the
declared types and the templates of the schemas mention only admitted constants. An extension
of the package by further constants then keeps this part of its model, whatever values the
new constants take. -/
theorem SetModel.ofSchemas_agreeing {heads : Head → ZFSet.{u}}
    {consts consts' : DeclName → ZFSet.{u}} {R : Rules Head}
    {S : AlgebraicSchema.SchemaFamily Head} {present : Presents R.computation S}
    (universes : ZFSetReplayInterpretation.UniverseModel R heads)
    (headEq : ∀ {h h' : Head}, R.headEq h h' → heads h = heads h')
    (declared : DeclName → Bool)
    (declarations : ∀ {c : DeclName} {T : CTm Head 0},
      (ChurchRules.ofSchemas R S present).constantType c = some T →
        declared c = true ∧ closedTerm declared T = true)
    (schemas : ∀ {k : Nat} {L R' : Tm Head k}, S L R' →
      SchemaClosed (elabDeclarations R.constantType) declared L R')
    (constants : ∀ {c : DeclName} {T : CTm Head 0},
      (ChurchRules.ofSchemas R S present).constantType c = some T →
        consts c ∈ ev heads consts T Fin.elim0)
    (valid : FamilyValid heads consts (elabDeclarations R.constantType) S)
    (same : ∀ c, declared c = true → consts c = consts' c) :
    SetModel heads consts' (ChurchRules.ofSchemas R S present) :=
  SetModel.ofSchemas universes headEq
    (fun {c T} known => by
      obtain ⟨named, closed⟩ := declarations known
      rw [← same c named, ← ev_congr_consts heads consts T
        (fun d mem => same d (closedTerm_iff.mp closed d mem)) Fin.elim0]
      exact constants known)
    (fun rule => (valid rule).of_closed (schemas rule) same)

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
