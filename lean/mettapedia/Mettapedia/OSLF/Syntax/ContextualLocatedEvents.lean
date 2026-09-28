import Mettapedia.OSLF.Syntax.ContextualLinearSubstitution

/-!
# Located rule occurrences over contexts

A located event consists of an authored root firing and a structurally linear
one-hole context in which it fires. The context may put the hole under binders.
Both pieces transport along ambient substitution, and their endpoint maps
are natural. At the empty context this graph has exactly the original
unpositioned contextual-step relation as its endpoint image.

Equation-class closure and conditional premise evidence are separate layers.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ContextualLocatedEvents

open CategoryTheory

variable {S : Signature} {M : List (MetaArity S)}

/-- One root firing at a structurally selected occurrence of an open term. -/
structure Instance (rule : UnpositionedRewrite (withMetas S M))
    (Γ : Ctx S) (sort : S.Srt) where
  root : ContextualRootEvents.Instance rule Γ
  context : LinCtx S rule.sort Γ sort

namespace Instance

def source {rule : UnpositionedRewrite (withMetas S M)} {Γ : Ctx S}
    {sort : S.Srt} (event : Instance rule Γ sort) : Term S Γ sort :=
  inst event.context.toTerm event.root.source

def target {rule : UnpositionedRewrite (withMetas S M)} {Γ : Ctx S}
    {sort : S.Srt} (event : Instance rule Γ sort) : Term S Γ sort :=
  inst event.context.toTerm event.root.target

/-- Transport the root data and selected structural occurrence together. -/
def map {rule : UnpositionedRewrite (withMetas S M)} {Γ Δ : Ctx S}
    {sort : S.Srt} (sigma : Sub S Γ Δ) (event : Instance rule Γ sort) :
    Instance rule Δ sort where
  root := event.root.map sigma
  context := ContextualLinearSubstitution.map sigma event.context

theorem source_map {rule : UnpositionedRewrite (withMetas S M)}
    {Γ Δ : Ctx S} {sort : S.Srt} (sigma : Sub S Γ Δ)
    (event : Instance rule Γ sort) :
    (map sigma event).source = bind sigma event.source := by
  simp only [source, map, ContextualLinearSubstitution.toTerm_map,
    ContextualRootEvents.Instance.source_map]
  exact (ContextualLinearSubstitution.bind_inst sigma event.context.toTerm
    event.root.source).symm

theorem target_map {rule : UnpositionedRewrite (withMetas S M)}
    {Γ Δ : Ctx S} {sort : S.Srt} (sigma : Sub S Γ Δ)
    (event : Instance rule Γ sort) :
    (map sigma event).target = bind sigma event.target := by
  simp only [target, map, ContextualLinearSubstitution.toTerm_map,
    ContextualRootEvents.Instance.target_map]
  exact (ContextualLinearSubstitution.bind_inst sigma event.context.toTerm
    event.root.target).symm

theorem map_id {rule : UnpositionedRewrite (withMetas S M)}
    {Γ : Ctx S} {sort : S.Srt} (event : Instance rule Γ sort) :
    map (fun _ v => .var v) event = event := by
  cases event with
  | mk root context =>
      simp only [map, ContextualRootEvents.Instance.map_id,
        ContextualLinearSubstitution.map_id]

theorem map_comp {rule : UnpositionedRewrite (withMetas S M)}
    {Γ Δ Θ : Ctx S} {sort : S.Srt}
    (sigma : Sub S Γ Δ) (tau : Sub S Δ Θ)
    (event : Instance rule Γ sort) :
    map tau (map sigma event) =
      map (fun s v => bind tau (sigma s v)) event := by
  cases event with
  | mk root context =>
      simp only [map, ContextualRootEvents.Instance.map_comp,
        ContextualLinearSubstitution.map_comp]

end Instance

/-- The edge object of the located root-step graph, indexed by the context. -/
def instancePresheaf (rule : UnpositionedRewrite (withMetas S M))
    (sort : S.Srt) : (Syntactic.Ctxt S)ᵒᵖ ⥤ Type where
  obj X := Instance rule X.unop.vars sort
  map f := TypeCat.ofHom (Instance.map f.unop)
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro event
    exact Instance.map_id event
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro event
    exact (Instance.map_comp f.unop g.unop event).symm

def sourceNatural (rule : UnpositionedRewrite (withMetas S M))
    (sort : S.Srt) :
    instancePresheaf rule sort ⟶ Syntactic.termPresheaf S sort where
  app X := TypeCat.ofHom Instance.source
  naturality X Y f := by
    apply ConcreteCategory.hom_ext
    intro event
    exact Instance.source_map f.unop event

def targetNatural (rule : UnpositionedRewrite (withMetas S M))
    (sort : S.Srt) :
    instancePresheaf rule sort ⟶ Syntactic.termPresheaf S sort where
  app X := TypeCat.ofHom Instance.target
  naturality X Y f := by
    apply ConcreteCategory.hom_ext
    intro event
    exact Instance.target_map f.unop event

/-- The endpoint image of the located graph over closed terms is precisely
the old contextual-step relation. This uses the proven equivalence between
structural holes and linear variable contexts. -/
theorem closed_endpoints_iff_step
    (rule : UnpositionedRewrite (withMetas S M)) (sort : S.Srt)
    (source target : Term S [] sort) :
    (∃ event : Instance rule [] sort,
      event.source = source ∧ event.target = target) ↔
      rule.Step source target := by
  constructor
  · rintro ⟨event, left, right⟩
    let root := event.root.toClosed
    exact ⟨event.context.toTerm, event.root.source, event.root.target,
      LinCtx.holeCount_toTerm event.context,
      ⟨root.body, root.close, root.source_eq, root.target_eq⟩,
      left, right⟩
  · rintro ⟨context, redex, reduct, linear, root, left, right⟩
    obtain ⟨structural, structural_eq⟩ :=
      LinCtx.exists_linCtx_of_holeCount context linear
    obtain ⟨body, close, root_left, root_right⟩ := root
    let old : UnpositionedRewrite.RootFiring rule redex reduct :=
      ⟨body, close, root_left, root_right⟩
    refine ⟨⟨ContextualRootEvents.Instance.ofClosed old, structural⟩, ?_, ?_⟩
    · simpa only [Instance.source, structural_eq,
        ContextualRootEvents.Instance.ofClosed_source] using left
    · simpa only [Instance.target, structural_eq,
        ContextualRootEvents.Instance.ofClosed_target] using right

namespace RhoExample

open Mettapedia.OSLF.Binding.RhoSchema

private abbrev nameContext : Ctx sig := [Srt.nm]

/-- The continuation ignores the received name and instead drops the
caller's ambient name. -/
def ambientNameContinuation : ContextualAssignment sig metas nameContext
  | ⟨0, _⟩ => .op Op.drp (.cons (.var (.succ .zero)) .nil)

def closeOpenName : Sub sig G nameContext
  | _, .zero => .var .zero
  | _, .succ .zero => weaken nilP

def root : ContextualRootEvents.Instance comm.unpositioned nameContext where
  body := ambientNameContinuation
  close := closeOpenName

/-- A linear context with its selected hole under rho's input binder. -/
def underInput : LinCtx sig Srt.pr nameContext Srt.pr :=
  .op Op.inp
    (.there (.var .zero)
      (LinArgs.here (Γ := nameContext) (bs := [Srt.nm])
        (LinCtx.hole : LinCtx sig Srt.pr ([Srt.nm] ++ nameContext) Srt.pr)
        (Args.nil : Args sig [] nameContext)))

def located : Instance comm.unpositioned nameContext Srt.pr where
  root := root
  context := underInput

/-- The ambient name remains one variable beyond the new input binder. -/
theorem bound_target :
    located.target =
      Term.op (S := sig) Op.inp
        (.cons (.var .zero)
          (.cons (Term.op (S := sig) Op.drp
            (.cons (.var (.succ .zero)) .nil)) .nil)) := rfl

/-- The resulting body is not the captured version that drops the name bound
by the surrounding input. -/
theorem bound_target_not_captured :
    located.target ≠
      Term.op (S := sig) Op.inp
        (.cons (.var .zero)
          (.cons (Term.op (S := sig) Op.drp
            (.cons (.var .zero) .nil)) .nil)) := by
  rw [bound_target]
  intro equal
  cases equal

/-- Replacing that ambient name by any closed name still agrees with the
general substitution naturality law for located events. -/
theorem closed_name_survives (name : Term sig [] Srt.nm) :
    (located.map (extend name)).target = bind (extend name) located.target :=
  Instance.target_map (extend name) located

end RhoExample

end Mettapedia.OSLF.Binding.ContextualLocatedEvents
