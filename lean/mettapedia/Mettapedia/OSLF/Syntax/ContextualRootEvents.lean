import Mettapedia.OSLF.Syntax.ContextualMetavariableAssignment
import Mettapedia.OSLF.Syntax.PresentationSemantics
import Mettapedia.OSLF.Syntax.RhoCommunicationSchema
import Mettapedia.OSLF.Syntax.SyntacticTermPresheaf

/-!
# Root rule occurrences in an ambient context

An authored rule instance has two independent substitutions: its metavariable
assignment may use ambient variables, and its rule variables are valued in the
same ambient context. Both are transported when that context is substituted.
This gives the root-event part of the context-indexed operational graph. The
one-hole contextual closure and equation-class graph require further work.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ContextualRootEvents

open CategoryTheory

variable {S : Signature} {M : List (MetaArity S)}

/-- Injecting a prefix variable into that same prefix with empty suffix does
not change the variable. -/
private theorem reScope_empty : ∀ (bs : Ctx S) {s : S.Srt}
    (v : Var (bs ++ []) s), reScope (Γ := []) bs v = v
  | [], _, v => nomatch v
  | _ :: _, _, .zero => rfl
  | _ :: bs, _, .succ v => by
      simp only [reScope, reScope_empty bs v]

private theorem weakenInto_empty (bs : Ctx S) {s : S.Srt}
    (t : Term S (bs ++ []) s) : weakenInto (Γ := []) bs t = t := by
  simp only [weakenInto]
  have h : (fun (r : S.Srt) (v : Var (bs ++ []) r) => reScope (Γ := []) bs v) =
      (fun _ v => v) := by
    funext r v
    exact reScope_empty bs v
  rw [h, rename_id]

/-- Strip the vacuous empty ambient suffix from every metavariable body. -/
def closedBody (body : ContextualAssignment S M []) :
    (i : Fin M.length) → Term S (M.get i).1 (M.get i).2 :=
  fun i => unScope (M.get i).1 (body i)

/-- Re-expanding the dependency-only body recovers every assignment over the
empty ambient context, including bodies below metavariable binders. -/
theorem ofClosed_closedBody (body : ContextualAssignment S M []) :
    ContextualAssignment.ofClosed (closedBody body) [] = body := by
  funext i
  exact (rename_injPrefix_unScope (Γ := []) (M.get i).1 (body i)).trans
    (weakenInto_empty (M.get i).1 (body i))

/-- A root instance of an unconditional authored rule at an arbitrary context. -/
structure Instance (rule : UnpositionedRewrite (withMetas S M)) (Γ : Ctx S) where
  body : ContextualAssignment S M Γ
  close : Sub S rule.ctx Γ

namespace Instance

/-- The source is obtained by instantiating both the metavariables and the
ordinary rule variables. -/
def source {rule : UnpositionedRewrite (withMetas S M)} {Γ : Ctx S}
    (firing : Instance rule Γ) : Term S Γ rule.sort :=
  ContextualAssignment.instantiate firing.body (fun _ v => .var v)
    firing.close rule.lhs

/-- The same assignment determines the target of the firing. -/
def target {rule : UnpositionedRewrite (withMetas S M)} {Γ : Ctx S}
    (firing : Instance rule Γ) : Term S Γ rule.sort :=
  ContextualAssignment.instantiate firing.body (fun _ v => .var v)
    firing.close rule.rhs

/-- Transport a root event along an ordinary substitution of its ambient
context. Its metavariable dependencies remain fixed. -/
def map {rule : UnpositionedRewrite (withMetas S M)} {Γ Δ : Ctx S}
    (sigma : Sub S Γ Δ) (firing : Instance rule Γ) : Instance rule Δ where
  body := ContextualAssignment.mapSub sigma firing.body
  close := fun s v => bind sigma (firing.close s v)

/-- The left endpoint commutes with ambient substitution. -/
theorem source_map {rule : UnpositionedRewrite (withMetas S M)}
    {Γ Δ : Ctx S} (sigma : Sub S Γ Δ) (firing : Instance rule Γ) :
    (map sigma firing).source = bind sigma firing.source := by
  unfold source map
  rw [ContextualAssignment.instantiate_mapSub]
  simpa only [bind, bind_id] using
    (ContextualAssignment.bind_instantiate firing.body
      (fun _ v => .var v) firing.close sigma rule.lhs).symm

/-- The right endpoint obeys the same law. -/
theorem target_map {rule : UnpositionedRewrite (withMetas S M)}
    {Γ Δ : Ctx S} (sigma : Sub S Γ Δ) (firing : Instance rule Γ) :
    (map sigma firing).target = bind sigma firing.target := by
  unfold target map
  rw [ContextualAssignment.instantiate_mapSub]
  simpa only [bind, bind_id] using
    (ContextualAssignment.bind_instantiate firing.body
      (fun _ v => .var v) firing.close sigma rule.rhs).symm

/-- Identity substitution leaves the complete root event unchanged. -/
theorem map_id {rule : UnpositionedRewrite (withMetas S M)} {Γ : Ctx S}
    (firing : Instance rule Γ) :
    map (fun _ v => .var v) firing = firing := by
  cases firing with
  | mk body close =>
      simp only [map, ContextualAssignment.mapSub_id]
      congr 1
      funext s v
      exact bind_id (close s v)

/-- Root-event transport composes strictly, including both its assignment
and its ordinary rule-variable valuation. -/
theorem map_comp {rule : UnpositionedRewrite (withMetas S M)}
    {Γ Δ Θ : Ctx S} (sigma : Sub S Γ Δ) (tau : Sub S Δ Θ)
    (firing : Instance rule Γ) :
    map tau (map sigma firing) =
      map (fun s v => bind tau (sigma s v)) firing := by
  cases firing with
  | mk body close =>
      simp only [map, ContextualAssignment.mapSub_comp, bind_comp]

/-- Embed a previously closed root firing into the ambient-context model.
The comparison has actual endpoint equations, not merely an inclusion of
unrelated occurrence types. -/
def ofClosed {rule : UnpositionedRewrite (withMetas S M)}
    {source target : Term S [] rule.sort}
    (firing : UnpositionedRewrite.RootFiring rule source target) :
    Instance rule [] where
  body := ContextualAssignment.ofClosed firing.body []
  close := firing.close

theorem ofClosed_source {rule : UnpositionedRewrite (withMetas S M)}
    {source target : Term S [] rule.sort}
    (firing : UnpositionedRewrite.RootFiring rule source target) :
    (ofClosed firing).source = source := by
  change ContextualAssignment.instantiate
    (ContextualAssignment.ofClosed firing.body [])
    (fun _ v => .var v) firing.close rule.lhs = source
  rw [ContextualAssignment.instantiate_ofClosed]
  exact firing.source_eq

theorem ofClosed_target {rule : UnpositionedRewrite (withMetas S M)}
    {source target : Term S [] rule.sort}
    (firing : UnpositionedRewrite.RootFiring rule source target) :
    (ofClosed firing).target = target := by
  change ContextualAssignment.instantiate
    (ContextualAssignment.ofClosed firing.body [])
    (fun _ v => .var v) firing.close rule.rhs = target
  rw [ContextualAssignment.instantiate_ofClosed]
  exact firing.target_eq

/-- Every open-style root event at the empty context recovers an instance of
the original closed rule semantics. -/
def toClosed {rule : UnpositionedRewrite (withMetas S M)}
    (firing : Instance rule []) :
    UnpositionedRewrite.RootFiring rule firing.source firing.target where
  body := closedBody firing.body
  close := firing.close
  source_eq := by
    calc
      bind firing.close (instantiate (closedBody firing.body) rule.lhs) =
          ContextualAssignment.instantiate
            (ContextualAssignment.ofClosed (closedBody firing.body) [])
            (fun _ v => .var v) firing.close rule.lhs := by
              rw [ContextualAssignment.instantiate_ofClosed]
      _ = firing.source := by rw [ofClosed_closedBody]; rfl
  target_eq := by
    calc
      bind firing.close (instantiate (closedBody firing.body) rule.rhs) =
          ContextualAssignment.instantiate
            (ContextualAssignment.ofClosed (closedBody firing.body) [])
            (fun _ v => .var v) firing.close rule.rhs := by
              rw [ContextualAssignment.instantiate_ofClosed]
      _ = firing.target := by rw [ofClosed_closedBody]; rfl

theorem ofClosed_toClosed {rule : UnpositionedRewrite (withMetas S M)}
    (firing : Instance rule []) : ofClosed firing.toClosed = firing := by
  cases firing with
  | mk body close =>
      simp only [ofClosed, toClosed, ofClosed_closedBody]

end Instance

/-- Root firing data vary over contexts as a presheaf on the syntactic
substitution category. -/
def instancePresheaf (rule : UnpositionedRewrite (withMetas S M)) :
    (Syntactic.Ctxt S)ᵒᵖ ⥤ Type where
  obj X := Instance rule X.unop.vars
  map f := TypeCat.ofHom (Instance.map f.unop)
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro firing
    exact Instance.map_id firing
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro firing
    exact (Instance.map_comp f.unop g.unop firing).symm

/-- Source is a natural map from root events to terms. -/
def sourceNatural (rule : UnpositionedRewrite (withMetas S M)) :
    instancePresheaf rule ⟶ Syntactic.termPresheaf S rule.sort where
  app X := TypeCat.ofHom Instance.source
  naturality X Y f := by
    apply ConcreteCategory.hom_ext
    intro firing
    exact Instance.source_map f.unop firing

/-- Target is natural under every substitution, not only renamings. -/
def targetNatural (rule : UnpositionedRewrite (withMetas S M)) :
    instancePresheaf rule ⟶ Syntactic.termPresheaf S rule.sort where
  app X := TypeCat.ofHom Instance.target
  naturality X Y f := by
    apply ConcreteCategory.hom_ext
    intro firing
    exact Instance.target_map f.unop firing

/-- An event between specified open endpoints retains its chosen assignment
and valuation; two events may have equal endpoints. -/
structure Event (rule : UnpositionedRewrite (withMetas S M))
    {Γ : Ctx S} (source target : Term S Γ rule.sort) where
  firing : Instance rule Γ
  source_eq : firing.source = source
  target_eq : firing.target = target

namespace Event

/-- Reindex a root event along an ambient substitution. -/
def map {rule : UnpositionedRewrite (withMetas S M)} {Γ Δ : Ctx S}
    {source target : Term S Γ rule.sort} (sigma : Sub S Γ Δ)
    (event : Event rule source target) :
    Event rule (bind sigma source) (bind sigma target) where
  firing := event.firing.map sigma
  source_eq := by rw [Instance.source_map, event.source_eq]
  target_eq := by rw [Instance.target_map, event.target_eq]

/-- Inhabitation is exactly the existence of an actual contextual firing. -/
theorem exists_iff {rule : UnpositionedRewrite (withMetas S M)}
    {Γ : Ctx S} (source target : Term S Γ rule.sort) :
    Nonempty (Event rule source target) ↔
      ∃ firing : Instance rule Γ,
        firing.source = source ∧ firing.target = target := by
  constructor
  · rintro ⟨event⟩
    exact ⟨event.firing, event.source_eq, event.target_eq⟩
  · rintro ⟨firing, left, right⟩
    exact ⟨⟨firing, left, right⟩⟩

/-- At the empty context, the new event graph has exactly the original
closed root steps as its endpoint relation. -/
theorem closed_iff_rootStep {rule : UnpositionedRewrite (withMetas S M)}
    (source target : Term S [] rule.sort) :
    Nonempty (Event rule source target) ↔ rule.RootStep source target := by
  constructor
  · rintro ⟨event⟩
    let old := event.firing.toClosed
    exact ⟨old.body, old.close,
      by simpa only [event.source_eq] using old.source_eq,
      by simpa only [event.target_eq] using old.target_eq⟩
  · rintro ⟨body, close, left, right⟩
    let old : UnpositionedRewrite.RootFiring rule source target :=
      ⟨body, close, left, right⟩
    exact ⟨⟨Instance.ofClosed old, Instance.ofClosed_source old,
      Instance.ofClosed_target old⟩⟩

end Event

namespace RhoExample

open Mettapedia.OSLF.Binding.RhoSchema

private abbrev openContext : Ctx sig := [Srt.pr]

/-- The communication continuation ignores its received name and returns
the process variable from the surrounding context. -/
def ambientContinuation : ContextualAssignment sig metas openContext
  | ⟨0, _⟩ => .var (.succ .zero)

/-- Close the channel and payload, leaving the supplied continuation open. -/
def openClose : Sub sig G openContext
  | _, .zero => weaken chan
  | _, .succ .zero => weaken nilP

def openCommunication : Instance comm.unpositioned openContext where
  body := ambientContinuation
  close := openClose

/-- Communication returns the caller's process variable, not the input
binder or a fabricated closed term. -/
theorem open_target : openCommunication.target = .var .zero := rfl

theorem open_target_not_nil :
    openCommunication.target ≠ weaken nilP := by
  rw [open_target]
  intro impossible
  cases impossible

/-- Replacing the caller's variable by any process replaces the output by
exactly that process. -/
theorem supplied_process_survives (process : Term sig [] Srt.pr) :
    (openCommunication.map (extend process)).target = process := by
  rw [Instance.target_map, open_target]
  rfl

end RhoExample

end Mettapedia.OSLF.Binding.ContextualRootEvents
