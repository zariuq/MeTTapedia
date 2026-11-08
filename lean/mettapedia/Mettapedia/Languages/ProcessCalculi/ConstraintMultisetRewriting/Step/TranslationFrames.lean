import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TranslationSyntax

/-!
# Second-order frames inside dependent frames: the map of frame instances

**The source** is the second-order frame instance on list frames (`listFrames`): frames with
finitely many metavariables, in order, contextual assignments, and observations. It is the full
sub-instance of `Frames.contextual` on the frames `⟨Fin M.length, M.get⟩` (`listFrames_models_iff`).

**The target** is `Dependent.frames rules` over a rule package that realizes the signature's sorts
and constructors (`BindingSignatureEmbedding.Realization`).

**The map** (`translation`):
* a list frame becomes the telescope whose metavariable of arity `(Γ, s)` has the closed type
  `Π Γ. s` (`ctxOf`);
* an observation `⟨Γ, s, t⟩` becomes the judged term `λΓ. ⟦t⟧ : Π Γ. s` (`entry`);
* a contextual assignment becomes the substitution of closed abstractions (`homOf`);
* the action commutes up to conversion: contextual instantiation is beta on spines.

**Generic consequences** (`FrameMap`): every map of frame instances preserves models and
solvability, and, when it reflects the equivalence, reflects models and asks of equation guards.

**Functoriality.** Composition is preserved up to conversion on every judged term
(`translation_comp`). The identity is preserved on translated terms (`translation_id_image`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
namespace Translation

open Mettapedia.OSLF
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open CategoryTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.FormationSensitiveContextual

universe uO uT uH uO' uT' uH'

/-! ## Maps of frame instances -/

/-- **A map of frame instances**: objects, judged terms and morphisms, such that the action
commutes up to the target equivalence and the source equivalence is preserved. -/
structure FrameMap {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
    {Obj' : Type uO'} {Tm' : Obj' → Type uT'} {Hom' : Obj' → Obj' → Type uH'}
    (X : Frames Tm Hom) (Y : Frames Tm' Hom') where
  obj : Obj → Obj'
  tm : {a : Obj} → Tm a → Tm' (obj a)
  hom : {a b : Obj} → Hom a b → Hom' (obj a) (obj b)
  act : ∀ {a b : Obj} (f : Hom a b) (t : Tm a), Y.E (tm (X.act f t)) (Y.act (hom f) (tm t))
  preserves : ∀ {a : Obj} {s t : Tm a}, X.E s t → Y.E (tm s) (tm t)

namespace FrameMap

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {Obj' : Type uO'} {Tm' : Obj' → Type uT'} {Hom' : Obj' → Obj' → Type uH'}
  {X : Frames Tm Hom} {Y : Frames Tm' Hom'} (Φ : FrameMap X Y)

/-- Translate a store equation by equation. -/
def store {a : Obj} (K : EquationStore (Tm a)) : EquationStore (Tm' (Φ.obj a)) :=
  K.map fun e => (Φ.tm e.1, Φ.tm e.2)

/-- The map reflects the equivalence. -/
def Reflects : Prop := ∀ {a : Obj} {s t : Tm a}, Y.E (Φ.tm s) (Φ.tm t) → X.E s t

/-- **Models are preserved.** -/
theorem models {a b : Obj} {f : Hom a b} {K : EquationStore (Tm a)} (solved : X.Models f K) :
    Y.Models (Φ.hom f) (Φ.store K) := by
  intro e member
  obtain ⟨e₀, present, rfl⟩ := List.mem_map.mp member
  exact (Y.equivalence _).trans ((Y.equivalence _).symm (Φ.act f e₀.1))
    ((Y.equivalence _).trans (Φ.preserves (solved e₀ present)) (Φ.act f e₀.2))

/-- **Models are reflected** by a map that reflects the equivalence. -/
theorem models_iff (reflects : Φ.Reflects) {a b : Obj} (f : Hom a b) (K : EquationStore (Tm a)) :
    Y.Models (Φ.hom f) (Φ.store K) ↔ X.Models f K := by
  refine ⟨fun solved e member => reflects ?_, Φ.models⟩
  have image : Y.E (Y.act (Φ.hom f) (Φ.tm e.1)) (Y.act (Φ.hom f) (Φ.tm e.2)) :=
    solved (Φ.tm e.1, Φ.tm e.2) (List.mem_map.mpr ⟨e, member, rfl⟩)
  exact (Y.equivalence _).trans (Φ.act f e.1)
    ((Y.equivalence _).trans image ((Y.equivalence _).symm (Φ.act f e.2)))

/-- **Solvability is preserved.** -/
theorem solvable {a : Obj} {K : EquationStore (Tm a)} (solvable : X.Solvable K) :
    Y.Solvable (Φ.store K) := by
  obtain ⟨b, f, solved⟩ := solvable
  exact ⟨Φ.obj b, Φ.hom f, Φ.models solved⟩

/-- **Asks of equation guards are reflected** by a map that reflects the equivalence: an ask over
every target solution is in particular an ask over the translated source solutions. -/
theorem entails_reflect (reflects : Φ.Reflects) {a : Obj} {K G : EquationStore (Tm a)}
    (asked : Y.Entails (Φ.store K) (fun _ g => Y.Models g (Φ.store G))) :
    X.Entails K (fun _ f => X.Models f G) :=
  fun b f solved => (Φ.models_iff reflects f G).mp (asked (Φ.obj b) (Φ.hom f) (Φ.models solved))

/-- `answer'` factors every solution of the translated store **on translated terms**. -/
def FactorsOnImage {a : Obj} {m' : Obj'} (K : EquationStore (Tm a)) (answer' : Hom' (Φ.obj a) m') :
    Prop :=
  ∀ (b : Obj') (τ : Hom' (Φ.obj a) b), Y.Models τ (Φ.store K) →
    ∃ residual : Hom' m' b, ∀ t : Tm a,
      Y.E (Y.act τ (Φ.tm t)) (Y.act (Y.comp residual answer') (Φ.tm t))

/-- **Asks of equation guards transfer in both directions** when a principal answer of the source
store translates to an answer that factors every target solution on translated terms. -/
theorem entails_iff_of_factorsOnImage (reflects : Φ.Reflects) {a m : Obj}
    {K G : EquationStore (Tm a)} {answer : Hom a m} (principal : X.Principal K answer)
    (factors : Φ.FactorsOnImage K (Φ.hom answer)) :
    Y.Entails (Φ.store K) (fun _ g => Y.Models g (Φ.store G)) ↔
      X.Entails K (fun _ f => X.Models f G) := by
  refine ⟨Φ.entails_reflect reflects, fun asked b τ solved => ?_⟩
  obtain ⟨residual, through⟩ := factors b τ solved
  have later := Frames.models_comp (Φ.models (asked m answer principal.sound)) residual
  intro e member
  obtain ⟨e₀, present, rfl⟩ := List.mem_map.mp member
  exact (Y.equivalence _).trans (through e₀.1)
    ((Y.equivalence _).trans (later _ (List.mem_map.mpr ⟨e₀, present, rfl⟩))
      ((Y.equivalence _).symm (through e₀.2)))

end FrameMap

/-! ## The source: second-order frames on list frames -/

variable {S : Binding.Signature}

variable (S) in
/-- **Second-order frames on list frames**: finitely many metavariables, in order; contextual
assignments; observations; syntactic equality. -/
def listFrames : Frames
    (fun M : List (Binding.MetaArity S) => Binding.ContextualFamily.Observation S M.get)
    (fun M N => Binding.ContextualFamily.Assignment (S := S) M.get N.get) where
  E := fun s t => s = t
  equivalence _ := ⟨Eq.refl, Eq.symm, Eq.trans⟩
  act := fun f t => Binding.ContextualFamily.instantiateObservation f t
  id M := Binding.ContextualFamily.generator M.get
  comp := fun g f => Binding.ContextualFamily.Assignment.compose g f
  act_id := Binding.ContextualFamily.instantiateObservation_identity
  act_comp := fun g f t => (Binding.ContextualFamily.instantiateObservation_comp f g t).symm
  preserves := fun {_ _} f {_ _} same =>
    congrArg (fun t => Binding.ContextualFamily.instantiateObservation f t) same

/-- The list-frame instance is the contextual instance at the frames `⟨Fin M.length, M.get⟩`. -/
theorem listFrames_models_iff {M N : List (Binding.MetaArity S)}
    (σa : Binding.ContextualFamily.Assignment (S := S) M.get N.get)
    (K : EquationStore (Binding.ContextualFamily.Observation S M.get)) :
    (listFrames S).Models (a := M) (b := N) σa K ↔
      (Frames.contextual S).Models (a := ⟨Fin M.length, M.get⟩) (b := ⟨Fin N.length, N.get⟩) σa K :=
  Iff.rfl

/-! ## Telescopes and typing -/

variable {Head : Type} (names : BindingSignatureEmbedding.Names S)

/-- **The telescope of a list frame**: the metavariable of arity `(Γ, s)` has the closed type
`Π Γ. s`. -/
def metaCtx : (M : List (Binding.MetaArity S)) → Ctx Head M.length
  | [] => .nil
  | a :: M => .snoc (metaCtx M) (liftClosed (BindingSignatureEmbedding.bindingType names a.1 a.2))

theorem metaCtx_lookup : ∀ (M : List (Binding.MetaArity S)) (i : Fin M.length),
    Ctx.lookup (metaCtx (Head := Head) names M) i =
      liftClosed (BindingSignatureEmbedding.bindingType names (M.get i).1 (M.get i).2)
  | [], i => i.elim0
  | _ :: M, i => by
      refine Fin.cases ?_ (fun i => ?_) i
      · exact rename_liftClosed _ _
      · show rename wk (Ctx.lookup (metaCtx names M) i) = _
        rw [metaCtx_lookup M i]
        exact rename_liftClosed _ _

/-- A telescope extended by an object context of sorts. -/
def extendCtx {k : Nat} (c : Ctx Head k) : (Γ : Binding.Ctx S) → Ctx Head (k + Γ.length)
  | [] => c
  | s :: Γ => .snoc (extendCtx c Γ) (BindingSignatureEmbedding.sortType names s)

theorem extendCtx_inner {k : Nat} (c : Ctx Head k) : ∀ {Γ : Binding.Ctx S} {s : S.Srt}
    (v : Binding.Var Γ s),
    Ctx.lookup (extendCtx names c Γ) (inner (vIdx v)) =
      BindingSignatureEmbedding.sortType names s
  | _, _, .zero => rfl
  | _, _, .succ v => by
      show rename wk (Ctx.lookup (extendCtx names c _) (inner (vIdx v))) = _
      rw [extendCtx_inner c v]
      rfl

theorem extendCtx_outer {k : Nat} (c : Ctx Head k) {i : Fin k} {T : Tm Head 0}
    (closed : Ctx.lookup c i = liftClosed T) :
    ∀ Γ : Binding.Ctx S, Ctx.lookup (extendCtx names c Γ) (outer i) = liftClosed T
  | [] => closed
  | _ :: Γ => by
      show rename wk (Ctx.lookup (extendCtx names c Γ) (outer i)) = _
      rw [extendCtx_outer c closed Γ]
      exact rename_liftClosed _ _

variable {rules : Rules Head}

theorem metaCtx_formed (realization : BindingSignatureEmbedding.Realization names rules) :
    ∀ M : List (Binding.MetaArity S), FormationSensitive.ContextFormation rules (metaCtx names M)
  | [] => .nil
  | a :: M => .snoc (metaCtx_formed realization M)
      (FormationCheckedTelescopePrograms.liftClosed_typing
        (realization.toSortRealization.bindingType_formed a.1 a.2) _)
      realization.universeIs

/-- Applying a constructor to translated arguments, first argument first. -/
theorem applyVec_typing {n : Nat} {ctx : Ctx Head n} (result : Tm Head 0) :
    ∀ (as : List (List S.Srt × S.Srt)) {f : Tm Head n} {w : Sub Head as.length n},
      FormationSensitive.Typing rules ctx f
        (liftClosed (BindingSignatureEmbedding.argumentsType names as result)) →
      (∀ j : Fin as.length, FormationSensitive.Typing rules ctx (w j)
        (liftClosed (BindingSignatureEmbedding.bindingType names (as.get j).1 (as.get j).2))) →
      FormationSensitive.Typing rules ctx (applyVec f w) (liftClosed result)
  | [], _, _, typed, _ => typed
  | (bound, sort) :: as, f, w, typed, arguments => by
      have functionTyped := typed
      change FormationSensitive.Typing rules ctx f
        (liftClosed (BindingSignatureEmbedding.closedArrow
          (BindingSignatureEmbedding.bindingType names bound sort)
          (BindingSignatureEmbedding.argumentsType names as result))) at functionTyped
      rw [BindingSignatureEmbedding.liftClosed_closedArrow] at functionTyped
      have applied := FormationSensitive.Typing.appElim functionTyped (arguments 0)
      rw [inst0, subst_liftClosed] at applied
      exact applyVec_typing result as applied (fun j => arguments j.succ)

/-- Applying a metavariable to translated arguments, last argument first. -/
theorem spine_typing {n : Nat} {ctx : Ctx Head n} :
    ∀ (P : List S.Srt) {result : Tm Head 0} {f : Tm Head n} {w : Sub Head P.length n},
      FormationSensitive.Typing rules ctx f
        (liftClosed (BindingSignatureEmbedding.telescopeType names P result)) →
      (∀ j : Fin P.length, FormationSensitive.Typing rules ctx (w j)
        (liftClosed (BindingSignatureEmbedding.sortType names (P.get j) : Tm Head 0))) →
      FormationSensitive.Typing rules ctx (spine f w) (liftClosed result)
  | [], _, _, _, typed, _ => typed
  | p :: P, result, _, w, typed, arguments => by
      have earlier := spine_typing P
        (result := BindingSignatureEmbedding.closedArrow
          (BindingSignatureEmbedding.sortType names p) result)
        (w := fun j => w j.succ) typed (fun j => arguments j.succ)
      rw [BindingSignatureEmbedding.liftClosed_closedArrow] at earlier
      have applied := FormationSensitive.Typing.appElim earlier (arguments 0)
      rw [inst0, subst_liftClosed] at applied
      exact applied

theorem get_map_cast : ∀ (P : List S.Srt)
    (h : P.length = (P.map (fun sort => (([] : List S.Srt), sort))).length) (j : Fin P.length),
    (P.map (fun sort => (([] : List S.Srt), sort))).get (Fin.cast h j) = ([], P.get j)
  | [], _, j => j.elim0
  | _ :: P, _, j => by
      refine Fin.cases rfl (fun j => ?_) j
      exact get_map_cast P (by simp) j

theorem metaArgs_typed {n : Nat} {ctx : Ctx Head n} (P : List S.Srt)
    (w : Sub Head (P.map (fun sort => (([] : List S.Srt), sort))).length n)
    (typed : ∀ j, FormationSensitive.Typing rules ctx (w j)
      (liftClosed (BindingSignatureEmbedding.bindingType names
        ((P.map (fun sort => (([] : List S.Srt), sort))).get j).1
        ((P.map (fun sort => (([] : List S.Srt), sort))).get j).2)))
    (h : P.length = (P.map (fun sort => (([] : List S.Srt), sort))).length) (j : Fin P.length) :
    FormationSensitive.Typing rules ctx (w (Fin.cast h j))
      (liftClosed (BindingSignatureEmbedding.sortType names (P.get j) : Tm Head 0)) := by
  have component := typed (Fin.cast h j)
  rw [get_map_cast P h j] at component
  exact component

/-- Closing the binders of one constructor argument. -/
theorem abstractB_typing (realization : BindingSignatureEmbedding.Realization names rules)
    {k : Nat} {c : Ctx Head k} {Γ : Binding.Ctx S} :
    ∀ (bound : List S.Srt) {result : Tm Head 0},
      FormationSensitive.Typing rules .nil result (.head realization.typeUniverse) →
      ∀ (body : Tm Head (k + (bound ++ Γ).length)),
        FormationSensitive.Typing rules (extendCtx names c (bound ++ Γ)) body (liftClosed result) →
        FormationSensitive.Typing rules (extendCtx names c Γ) (abstractB bound body)
          (liftClosed (BindingSignatureEmbedding.telescopeType names bound result))
  | [], _, _, _, typed => typed
  | sort :: bound, result, formed, body, typed => by
      have functionType := realization.toSortRealization.telescopeType_formed [sort] formed
      change FormationSensitive.Typing rules .nil
        (BindingSignatureEmbedding.closedArrow (BindingSignatureEmbedding.sortType names sort) result)
        (.head realization.typeUniverse) at functionType
      have functionFormed := FormationCheckedTelescopePrograms.liftClosed_typing functionType
        (extendCtx names c (bound ++ Γ))
      rw [BindingSignatureEmbedding.liftClosed_closedArrow] at functionFormed
      have function := FormationSensitive.Typing.lamIntro functionFormed realization.universeIs typed
      rw [← BindingSignatureEmbedding.liftClosed_closedArrow] at function
      exact abstractB_typing realization bound functionType (.lam body) function

/-- Closing an object context of sorts. -/
theorem abstractN_typing (realization : BindingSignatureEmbedding.Realization names rules)
    {k : Nat} {c : Ctx Head k} :
    ∀ (Γ : Binding.Ctx S) {result : Tm Head 0},
      FormationSensitive.Typing rules .nil result (.head realization.typeUniverse) →
      ∀ (body : Tm Head (k + Γ.length)),
        FormationSensitive.Typing rules (extendCtx names c Γ) body (liftClosed result) →
        FormationSensitive.Typing rules c (abstractN Γ.length body)
          (liftClosed (BindingSignatureEmbedding.telescopeType names Γ result))
  | [], _, _, _, typed => typed
  | sort :: Γ, result, formed, body, typed => by
      have functionType := realization.toSortRealization.telescopeType_formed [sort] formed
      change FormationSensitive.Typing rules .nil
        (BindingSignatureEmbedding.closedArrow (BindingSignatureEmbedding.sortType names sort) result)
        (.head realization.typeUniverse) at functionType
      have functionFormed := FormationCheckedTelescopePrograms.liftClosed_typing functionType
        (extendCtx names c Γ)
      rw [BindingSignatureEmbedding.liftClosed_closedArrow] at functionFormed
      have function := FormationSensitive.Typing.lamIntro functionFormed realization.universeIs typed
      rw [← BindingSignatureEmbedding.liftClosed_closedArrow] at function
      exact abstractN_typing realization Γ functionType (.lam body) function

section Typing

variable (realization : BindingSignatureEmbedding.Realization names rules)
  (M : List (Binding.MetaArity S))

include realization

mutual

/-- **The translation is well typed**: a term of sort `s` becomes a term of the sort constant. -/
theorem encode_typing : ∀ {Γ : Binding.Ctx S} {s : S.Srt} (t : Binding.Term (Sig S M) Γ s),
    FormationSensitive.Typing rules (extendCtx names (metaCtx names M) Γ) (encode names M t)
      (BindingSignatureEmbedding.sortType names s)
  | _, _, .var v => by
      have typed := FormationSensitive.Typing.var (R := rules)
        (Γ := extendCtx names (metaCtx (Head := Head) names M) _) (inner (vIdx v))
      rw [extendCtx_inner] at typed
      exact typed
  | Γ, _, .op (.inl o) args => by
      have constant := FormationSensitive.Typing.const
        (Γ := extendCtx names (metaCtx (Head := Head) names M) Γ)
        (realization.operatorLookup o) (realization.toSortRealization.operatorType_formed o)
        realization.universeIs
      exact applyVec_typing names (BindingSignatureEmbedding.sortType names _) _ constant
        (encodeArgs_typing args)
  | Γ, _, .op (.inr (.mk i)) args => by
      have castLength : (M.get i).1.length =
          ((M.get i).1.map (fun sort => (([] : List S.Srt), sort))).length := by simp
      have metaVariable := FormationSensitive.Typing.var (R := rules)
        (Γ := extendCtx names (metaCtx (Head := Head) names M) Γ) (outer i)
      rw [extendCtx_outer names (metaCtx names M) (metaCtx_lookup names M i) Γ] at metaVariable
      exact spine_typing names (M.get i).1 metaVariable
        (metaArgs_typed names (M.get i).1 _ (encodeArgs_typing args) castLength)

theorem encodeArgs_typing : ∀ {as : List (List S.Srt × S.Srt)} {Γ : Binding.Ctx S}
    (args : Binding.Args (Sig S M) as Γ) (j : Fin as.length),
    FormationSensitive.Typing rules (extendCtx names (metaCtx names M) Γ) (encodeArgs names M args j)
      (liftClosed (BindingSignatureEmbedding.bindingType names (as.get j).1 (as.get j).2))
  | _, _, .nil, j => j.elim0
  | _, _, .cons (bs := bound) (s := sort) body rest, j => by
      refine Fin.cases ?_ (fun j => ?_) j
      · exact abstractB_typing names realization bound
          (realization.toSortRealization.sortType_formed .nil sort) (encode names M body)
          (encode_typing body)
      · exact encodeArgs_typing rest j

end

end Typing

/-! ## The map -/

section Map

variable (realization : BindingSignatureEmbedding.Realization names rules)

/-- **The telescope of a list frame**, formed. -/
abbrev ctxOf (M : List (Binding.MetaArity S)) : Context rules :=
  ⟨M.length, metaCtx names M, metaCtx_formed names realization M⟩

/-- The closed type `Π Γ. s`, formed over every telescope. -/
def typeOf {M : List (Binding.MetaArity S)} (Γ : Binding.Ctx S) (s : S.Srt) :
    TypeOver (ctxOf names realization M) where
  code := liftClosed (BindingSignatureEmbedding.bindingType names Γ s)
  level := realization.typeUniverse
  universeWitness := realization.universeIs
  formed := FormationCheckedTelescopePrograms.liftClosed_typing
    (realization.toSortRealization.bindingType_formed Γ s) _

/-- **The judged term of an observation** `⟨Γ, s, t⟩`: `λΓ. ⟦t⟧ : Π Γ. s`. -/
def entry {M : List (Binding.MetaArity S)} (o : Binding.ContextualFamily.Observation S M.get) :
    Dependent.Entry (ctxOf names realization M) :=
  ⟨typeOf names realization o.1 o.2.1,
    ⟨abstractN o.1.length (encode names M o.2.2),
      abstractN_typing names realization o.1
        (realization.toSortRealization.sortType_formed .nil o.2.1) _
        (encode_typing names realization M o.2.2)⟩⟩

/-- **The substitution of a contextual assignment**: closed abstractions of the images. -/
def homOf {M N : List (Binding.MetaArity S)}
    (σa : Binding.ContextualFamily.Assignment (S := S) M.get N.get) :
    ctxOf names realization N ⟶ ctxOf names realization M where
  substitution := homCode names M N σa
  typed := by
    intro (i : Fin M.length)
    show FormationSensitive.Typing rules (metaCtx names N) (homCode names M N σa i)
      (subst (homCode names M N σa) (Ctx.lookup (metaCtx names M) i))
    rw [metaCtx_lookup, subst_liftClosed]
    exact abstractN_typing names realization (M.get i).1
      (realization.toSortRealization.sortType_formed .nil (M.get i).2) _
      (encode_typing names realization N (σa i))

/-- **The translation of second-order frames into dependent frames.** -/
def translation : FrameMap (listFrames S) (Dependent.frames rules) where
  obj M := ctxOf names realization M
  tm o := entry names realization o
  hom σa := homOf names realization σa
  act := by
    intro M N σa o
    obtain ⟨Γ, s, t⟩ := o
    refine ⟨?_, ?_⟩
    · show Conv rules.headEq (liftClosed (BindingSignatureEmbedding.bindingType names Γ s))
        (subst (homCode names M N σa) (liftClosed (BindingSignatureEmbedding.bindingType names Γ s)))
        rules.computation
      rw [subst_liftClosed]
      exact .refl _
    · exact .symm _ _ (action_beta_closed names M N σa t)
  preserves := by
    intro M s t same
    obtain rfl : s = t := same
    exact Dependent.Entry.Convertible.refl _

/-! ## Functoriality -/

/-- **Composition is preserved** up to conversion, on every judged term of the telescope: the code
of a composite assignment is pointwise convertible to the composite of the codes. -/
theorem translation_comp {M N L : List (Binding.MetaArity S)}
    (σa : Binding.ContextualFamily.Assignment (S := S) M.get N.get)
    (τa : Binding.ContextualFamily.Assignment (S := S) N.get L.get)
    (t : Dependent.Entry (ctxOf names realization M)) :
    Dependent.Entry.Convertible
      (t.reindex (homOf names realization (Binding.ContextualFamily.Assignment.compose τa σa)))
      (t.reindex (homOf names realization τa ≫ homOf names realization σa)) :=
  Dependent.convertible_reindex_of_pointwise
    (fun i => .symm _ _ (action_beta_closed names N L τa (σa i))) t

/-- **The identity is preserved on translated terms.** -/
theorem translation_id_image {M : List (Binding.MetaArity S)}
    (o : Binding.ContextualFamily.Observation S M.get) :
    Dependent.Entry.Convertible
      ((entry names realization o).reindex
        (homOf names realization (Binding.ContextualFamily.generator M.get)))
      (entry names realization o) := by
  have law := (translation names realization).act ((listFrames S).id M) o
  have same : (listFrames S).act ((listFrames S).id M) o = o := (listFrames S).act_id o
  rw [same] at law
  exact Dependent.Entry.Convertible.symm law

/-- **Solutions are preserved**: a contextual solution of a store translates to a dependent solution
of the translated store. -/
theorem translation_models {M N : List (Binding.MetaArity S)}
    {σa : Binding.ContextualFamily.Assignment (S := S) M.get N.get}
    {K : EquationStore (Binding.ContextualFamily.Observation S M.get)}
    (solved : (listFrames S).Models (a := M) (b := N) σa K) :
    (Dependent.frames rules).Models ((translation names realization).hom σa)
      ((translation names realization).store K) :=
  (translation names realization).models solved

/-- **Solvability is preserved.** -/
theorem translation_solvable {M : List (Binding.MetaArity S)}
    {K : EquationStore (Binding.ContextualFamily.Observation S M.get)}
    (solvable : (listFrames S).Solvable (a := M) K) :
    (Dependent.frames rules).Solvable ((translation names realization).store K) :=
  (translation names realization).solvable solvable

end Map

end Translation

#print axioms Translation.FrameMap.models
#print axioms Translation.FrameMap.models_iff
#print axioms Translation.FrameMap.entails_reflect
#print axioms Translation.FrameMap.entails_iff_of_factorsOnImage
#print axioms Translation.encode_typing
#print axioms Translation.translation
#print axioms Translation.translation_comp
#print axioms Translation.translation_id_image
#print axioms Translation.translation_models
#print axioms Translation.translation_solvable

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
