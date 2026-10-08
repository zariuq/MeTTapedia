import Mettapedia.OSLF.Syntax.FiniteBranchingGSOSNativeEdges
import Mettapedia.OSLF.Syntax.FiniteBranchingGSOSReceipts

/-!
# Native dependent domains of independently authored nondeterministic rules

All original child sources remain available, including passive arguments.
Each authored positive occurrence selects its own actual labelled event and
origin; repeated addresses need not select equal successors. Negative
addresses use future-sensitive native absence. The complete domain compares
with the independently defined matching judgment and retains its supplied
occurrence identifiers in addition to the authored clause identifier.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.FiniteBranching.NativePremises

open _root_.CategoryTheory Mettapedia.TypeTheory
open Mettapedia.OSLF.DeterministicGSOS (Signature)
open Premises NativeEdges

universe u
variable {S : Signature.{u}} {Actions : S.Srt → Type u}
variable {C : Type u} [Category.{u} C]

def children (worlds : Cᵒᵖ ⥤ S.Families) {sort : S.Srt}
    (operator : S.Operator sort) : Cᵒᵖ ⥤ Type u where
  obj world := S.Arguments (S.polynomial.Free (worlds.obj world)) operator
  map change := ↾(fun given position => S.rename (worlds.map change) (given position))
  map_id world := by
    apply ConcreteCategory.hom_ext
    intro given
    funext position
    change (terms worlds _).map (𝟙 world) (given position) = given position
    exact Functor.map_id_apply (terms worlds _) world (given position)
  map_comp before after := by
    apply ConcreteCategory.hom_ext
    intro given
    funext position
    change (terms worlds _).map (before ≫ after) (given position) = _
    exact Functor.map_comp_apply (terms worlds _) before after (given position)

variable (authored : AuthoredPresentation S Actions)
variable (worlds : Cᵒᵖ ⥤ S.Families)
variable (steps : worlds ⟶ worlds ⋙ behaviourFunctor S Actions)

abbrev law : Law S Actions := Presentation.toLaw authored.readout

def arguments (world : Cᵒᵖ) {sort : S.Srt} {operator : S.Operator sort}
    (given : (children worlds operator).obj world) :
    S.Arguments ((sourceBehaviourFunctor S Actions).obj
      (S.polynomial.Free (worlds.obj world))) operator :=
  fun position => (given position,
    Operational.coalgebra (law authored) (steps.app world) PUnit.unit _ (given position))

def childProjection {sort : S.Srt} (operator : S.Operator sort)
    (position : S.Position operator) : children worlds operator ⟶ terms worlds (S.argument operator position) where
  app _ := ↾(fun given => given position)

/-- The independent native rule predicate uses existential support for each
positive occurrence and Heyting negation for precisely the authored negative
addresses. It makes no test at any unmentioned passive address. -/
def guard {sort : S.Srt} {operator : S.Operator sort}
    (pattern : Pattern (Actions := Actions) operator) : Subfunctor (children worlds operator) where
  obj world := {given |
    (∀ occurrence, given (pattern.address occurrence).1 ∈
      ((system (law authored) worlds steps (pattern.resultSort occurrence)).enabled
        PUnit.{u + 1} (pattern.address occurrence).2).obj world) ∧
    ∀ address ∈ pattern.negative, given address.1 ∈
      (noAction (law authored) worlds steps _ address.2).obj world}
  map change := by
    intro given holds
    refine ⟨?_, ?_⟩
    · intro occurrence
      exact ((system (law authored) worlds steps (pattern.resultSort occurrence)).enabled
        PUnit.{u + 1} (pattern.address occurrence).2).map change (holds.1 occurrence)
    · intro address member
      exact (noAction (law authored) worlds steps _ address.2).map change (holds.2 address member)

theorem guard_iff_matching (world : Cᵒᵖ) {sort : S.Srt} {operator : S.Operator sort}
    (pattern : Pattern (Actions := Actions) operator)
    (given : (children worlds operator).obj world) :
    given ∈ (guard authored worlds steps pattern).obj world ↔
      ∃ input : Input pattern (S.polynomial.Free (worlds.obj world)),
        Matches pattern (arguments authored worlds steps world given) input := by
  constructor
  · intro holds
    have choices : ∀ occurrence, ∃ target,
        target ∈ Operational.coalgebra (law authored) (steps.app world) PUnit.unit _
          (given (pattern.address occurrence).1) (pattern.address occurrence).2 := by
      intro occurrence
      exact ((system (law authored) worlds steps (pattern.resultSort occurrence)).enabled_iff
        (Origins := PUnit.{u + 1}) (pattern.address occurrence).2 world _).mp (holds.1 occurrence)
    refine ⟨⟨given, fun occurrence => (choices occurrence).choose⟩, fun _ => rfl,
      fun occurrence => (choices occurrence).choose_spec, ?_⟩
    intro address member
    exact (noAction_iff_empty (law authored) worlds steps _ address.2 world _).mp (holds.2 address member)
  · rintro ⟨input, matching⟩
    refine ⟨?_, ?_⟩
    · intro occurrence
      apply ((system (law authored) worlds steps (pattern.resultSort occurrence)).enabled_iff
        (Origins := PUnit.{u + 1}) (pattern.address occurrence).2 world _).mpr
      exact ⟨input.derivatives occurrence, matching.2.1 occurrence⟩
    · intro address member
      exact (noAction_iff_empty (law authored) worlds steps _ address.2 world _).mpr
        (matching.2.2 address member)

@[ext] structure Firing (PremiseOrigins : Type u) (world : Cᵒᵖ)
    {sort : S.Srt} (operator : S.Operator sort) (action : Actions sort) where
  origin : authored.Origin sort operator action
  children : (children worlds operator).obj world
  positive : ∀ occurrence : (authored.rule sort operator action origin).pattern.Occurrence,
    Event (law authored) worlds steps PremiseOrigins
      ((authored.rule sort operator action origin).pattern.resultSort occurrence)
      ((authored.rule sort operator action origin).pattern.address occurrence).2 world
  positive_source : ∀ occurrence, (positive occurrence).source =
    children ((authored.rule sort operator action origin).pattern.address occurrence).1
  negative : ∀ address ∈ (authored.rule sort operator action origin).pattern.negative,
    children address.1 ∈ (noAction (law authored) worlds steps _ address.2).obj world

namespace Firing

variable {authored worlds steps}
variable {PremiseOrigins : Type u} {world future : Cᵒᵖ}
variable {sort : S.Srt} {operator : S.Operator sort} {action : Actions sort}

abbrev rule (firing : Firing authored worlds steps PremiseOrigins world operator action) :=
  authored.rule sort operator action firing.origin

def input (firing : Firing authored worlds steps PremiseOrigins world operator action) :
    Input firing.rule.pattern (S.polynomial.Free (worlds.obj world)) where
  originals := firing.children
  derivatives occurrence := (firing.positive occurrence).target

theorem matching (firing : Firing authored worlds steps PremiseOrigins world operator action) :
    Matches firing.rule.pattern (arguments authored worlds steps world firing.children) firing.input := by
  refine ⟨fun _ => rfl, ?_, ?_⟩
  · intro occurrence
    change (firing.positive occurrence).target ∈
      Operational.coalgebra (law authored) (steps.app world) PUnit.unit _
        (firing.children (firing.rule.pattern.address occurrence).1)
        (firing.rule.pattern.address occurrence).2
    have valid := (firing.positive occurrence).valid
    change (firing.positive occurrence).target ∈
      Operational.coalgebra (law authored) (steps.app world) PUnit.unit _
        (firing.positive occurrence).source (firing.rule.pattern.address occurrence).2 at valid
    rw [firing.positive_source] at valid
    exact valid
  · intro address member
    exact (noAction_iff_empty (law authored) worlds steps _ address.2 world
      (firing.children address.1)).mp (firing.negative address member)

theorem native_guard (firing : Firing authored worlds steps PremiseOrigins world operator action) :
    firing.children ∈ (guard authored worlds steps firing.rule.pattern).obj world :=
  (guard_iff_matching authored worlds steps world firing.rule.pattern firing.children).mpr
    ⟨firing.input, firing.matching⟩

/-- Forgetting only the separate selected occurrence identifiers gives the
independently authored complete firing with its original clause identifier. -/
def erase (firing : Firing authored worlds steps PremiseOrigins world operator action) :
    authored.Firing operator (arguments authored worlds steps world firing.children) action where
  origin := firing.origin
  input := firing.input
  matching := firing.matching

def map (change : world ⟶ future)
    (firing : Firing authored worlds steps PremiseOrigins world operator action) :
    Firing authored worlds steps PremiseOrigins future operator action where
  origin := firing.origin
  children := (NativePremises.children worlds operator).map change firing.children
  positive occurrence := (system (law authored) worlds steps _).mapEvent change (firing.positive occurrence)
  positive_source occurrence :=
    congrArg (S.rename (worlds.map change)) (firing.positive_source occurrence)
  negative address member :=
    (noAction (law authored) worlds steps _ address.2).map change (firing.negative address member)

theorem map_origin (change : world ⟶ future)
    (firing : Firing authored worlds steps PremiseOrigins world operator action) :
    (firing.map change).origin = firing.origin := rfl

theorem map_positive_origin (change : world ⟶ future)
    (firing : Firing authored worlds steps PremiseOrigins world operator action)
    (occurrence : firing.rule.pattern.Occurrence) :
    ((firing.map change).positive occurrence).origin = (firing.positive occurrence).origin := rfl

theorem map_input (change : world ⟶ future)
    (firing : Firing authored worlds steps PremiseOrigins world operator action) :
    (firing.map change).input = firing.input.map (S.termMonad.map (worlds.map change)) := rfl

end Firing

/-- Introduction uses each supplied occurrence identifier and each actual
matching successor; no existentially selected representative is substituted. -/
def introduce (PremiseOrigins : Type u) (world : Cᵒᵖ)
    {sort : S.Srt} {operator : S.Operator sort} {action : Actions sort}
    (given : (children worlds operator).obj world)
    (firing : authored.Firing operator (arguments authored worlds steps world given) action)
    (origins : (authored.rule sort operator action firing.origin).pattern.Occurrence → PremiseOrigins) :
    Firing authored worlds steps PremiseOrigins world operator action where
  origin := firing.origin
  children := given
  positive occurrence :=
    { origin := origins occurrence
      source := given ((authored.rule sort operator action firing.origin).pattern.address occurrence).1
      target := firing.input.derivatives occurrence
      valid := firing.matching.2.1 occurrence }
  positive_source _ := rfl
  negative address member :=
    (noAction_iff_empty (law authored) worlds steps _ address.2 world (given address.1)).mpr
      (firing.matching.2.2 address member)

theorem introduce_input (PremiseOrigins : Type u) (world : Cᵒᵖ)
    {sort : S.Srt} {operator : S.Operator sort} {action : Actions sort}
    (given : (children worlds operator).obj world)
    (firing : authored.Firing operator (arguments authored worlds steps world given) action)
    (origins : (authored.rule sort operator action firing.origin).pattern.Occurrence → PremiseOrigins) :
    (introduce authored worlds steps PremiseOrigins world given firing origins).input = firing.input := by
  apply congrArg₂ Input.mk
  · funext position
    exact (firing.matching.1 position).symm
  · rfl

theorem introduce_erase (PremiseOrigins : Type u) (world : Cᵒᵖ)
    {sort : S.Srt} {operator : S.Operator sort} {action : Actions sort}
    (given : (children worlds operator).obj world)
    (firing : authored.Firing operator (arguments authored worlds steps world given) action)
    (origins : (authored.rule sort operator action firing.origin).pattern.Occurrence → PremiseOrigins) :
    (introduce authored worlds steps PremiseOrigins world given firing origins).erase = firing := by
  cases firing with
  | mk origin input matching =>
    have same := introduce_input authored worlds steps PremiseOrigins world given
      (AuthoredPresentation.Firing.mk origin input matching) origins
    change AuthoredPresentation.Firing.mk origin _ _ = _
    congr 1

/-- An independent matching receipt retains the input's whole assignment,
its clause identifier and one supplied identifier per positive occurrence. -/
abbrev MatchingReceipt (PremiseOrigins : Type u) (world : Cᵒᵖ)
    {sort : S.Srt} (operator : S.Operator sort) (action : Actions sort) :=
  Σ given : (children worlds operator).obj world,
    Σ firing : authored.Firing operator (arguments authored worlds steps world given) action,
      (authored.rule sort operator action firing.origin).pattern.Occurrence → PremiseOrigins

/-- Both roundtrips preserve complete matching receipts and separately
supplied occurrence origins. The comparison does not normalize target sets. -/
def matchingReceiptEquiv (PremiseOrigins : Type u) (world : Cᵒᵖ)
    {sort : S.Srt} (operator : S.Operator sort) (action : Actions sort) :
    Firing authored worlds steps PremiseOrigins world operator action ≃
      MatchingReceipt authored worlds steps PremiseOrigins world operator action where
  toFun firing := ⟨firing.children, firing.erase, fun occurrence => (firing.positive occurrence).origin⟩
  invFun receipt := introduce authored worlds steps PremiseOrigins world receipt.1 receipt.2.1 receipt.2.2
  left_inv firing := by
    apply Firing.ext
    · rfl
    · rfl
    · apply heq_of_eq
      funext occurrence
      apply PresheafFiniteSuccessorEvents.System.Event.ext
      · rfl
      · exact (firing.positive_source occurrence).symm
      · rfl
  right_inv receipt := by
    rcases receipt with ⟨given, firing, origins⟩
    change (⟨given, ⟨(introduce authored worlds steps PremiseOrigins world given firing origins).erase,
      origins⟩⟩ : MatchingReceipt authored worlds steps PremiseOrigins world operator action) =
      ⟨given, firing, origins⟩
    refine Sigma.ext (by rfl) ?_
    apply heq_of_eq
    refine Sigma.ext (introduce_erase authored worlds steps PremiseOrigins world given firing origins) ?_
    rfl

theorem firing_exists_iff_guard (PremiseOrigins : Type u) [Nonempty PremiseOrigins]
    (world : Cᵒᵖ) {sort : S.Srt} (operator : S.Operator sort) (action : Actions sort)
    (origin : authored.Origin sort operator action)
    (given : (children worlds operator).obj world) :
    (∃ firing : Firing authored worlds steps PremiseOrigins world operator action,
      firing.origin = origin ∧ firing.children = given) ↔
    given ∈ (guard authored worlds steps (authored.rule sort operator action origin).pattern).obj world := by
  constructor
  · rintro ⟨firing, rfl, rfl⟩
    exact firing.native_guard
  · intro holds
    obtain ⟨input, matching⟩ := (guard_iff_matching authored worlds steps world _ given).mp holds
    let ordinary : authored.Firing operator (arguments authored worlds steps world given) action :=
      ⟨origin, input, matching⟩
    exact ⟨introduce authored worlds steps PremiseOrigins world given ordinary
      (fun _ => Classical.choice ‹Nonempty PremiseOrigins›), rfl, rfl⟩

def firingFunctor (PremiseOrigins : Type u) {sort : S.Srt}
    (operator : S.Operator sort) (action : Actions sort) : Cᵒᵖ ⥤ Type u where
  obj world := Firing authored worlds steps PremiseOrigins world operator action
  map change := ↾(Firing.map change)
  map_id world := by
    apply ConcreteCategory.hom_ext
    intro firing
    apply Firing.ext
    · rfl
    · exact ConcreteCategory.congr_hom ((children worlds operator).map_id world) firing.children
    · apply heq_of_eq
      funext occurrence
      exact ConcreteCategory.congr_hom
        (((system (law authored) worlds steps _).events PremiseOrigins _).map_id world)
        (firing.positive occurrence)
  map_comp before after := by
    apply ConcreteCategory.hom_ext
    intro firing
    apply Firing.ext
    · rfl
    · exact ConcreteCategory.congr_hom
        ((children worlds operator).map_comp before after) firing.children
    · apply heq_of_eq
      funext occurrence
      exact ConcreteCategory.congr_hom
        (((system (law authored) worlds steps _).events PremiseOrigins _).map_comp before after)
        (firing.positive occurrence)

end Mettapedia.OSLF.FiniteBranching.NativePremises
