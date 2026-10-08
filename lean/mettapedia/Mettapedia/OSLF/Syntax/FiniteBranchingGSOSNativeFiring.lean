import Mettapedia.OSLF.Syntax.FiniteBranchingGSOSNativePremises

/-!
# Native evidence of complete nondeterministic rule firings

The independently authored finite-rule interpretation gives the whole raw
target tree. The actual operational node law flattens that tree and earns
its successor membership. A native event span uses the complete firing as
its event, retaining every supplied positive occurrence and both passive
sources and authored origins. Its dependent sum and adjoint act on arbitrary
coherent target families, with full event and dependent-result readouts.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.FiniteBranching.NativePremises

open _root_.CategoryTheory Mettapedia.TypeTheory
open Mettapedia.OSLF.DeterministicGSOS (Signature)
open Premises NativeEdges PresheafEventCertificates
open DisplayedPresheafTransport DisplayedPresheafComprehension

universe u
variable {S : Signature.{u}} {Actions : S.Srt → Type u}
variable {C : Type u} [Category.{u} C]
variable (authored : AuthoredPresentation S Actions)
variable (worlds : Cᵒᵖ ⥤ S.Families)
variable (steps : worlds ⟶ worlds ⋙ behaviourFunctor S Actions)

namespace Firing

variable {authored worlds steps}
variable {PremiseOrigins : Type u} {world future : Cᵒᵖ}
variable {sort : S.Srt} {operator : S.Operator sort} {action : Actions sort}

def source (firing : Firing authored worlds steps PremiseOrigins world operator action) :
    S.Term (worlds.obj world) sort :=
  IndexedPolynomial.Free.node S.polynomial operator firing.children

def rawTarget (firing : Firing authored worlds steps PremiseOrigins world operator action) :
    S.Term (S.polynomial.Free (worlds.obj world)) sort :=
  firing.rule.output firing.input

def target (firing : Firing authored worlds steps PremiseOrigins world operator action) :
    S.Term (worlds.obj world) sort :=
  IndexedPolynomial.Free.join S.polynomial firing.rawTarget

/-- Independent matching clauses prove membership in the whole natural law,
before the actual operational flattening changes the target's syntax level. -/
theorem rawTarget_member (firing : Firing authored worlds steps PremiseOrigins world operator action) :
    firing.rawTarget ∈ (law authored).app (S.polynomial.Free (worlds.obj world)) PUnit.unit sort
      ⟨operator, arguments authored worlds steps world firing.children⟩ action :=
  (authored.mem_targets_iff_firing operator _ action _).mpr ⟨firing.erase, rfl⟩

theorem target_member (firing : Firing authored worlds steps PremiseOrigins world operator action) :
    firing.target ∈ Operational.coalgebra (law authored) (steps.app world) PUnit.unit sort
      firing.source action := by
  have issued := (Mettapedia.CategoryTheory.FinitePowerset.mem_map
    (IndexedPolynomial.Free.join S.polynomial)
    ((law authored).app (S.polynomial.Free (worlds.obj world)) PUnit.unit sort
      ⟨operator, arguments authored worlds steps world firing.children⟩ action)
    firing.target).mpr
    ⟨firing.rawTarget, firing.rawTarget_member, rfl⟩
  have computed := Operational.coalgebra_node (S := S) (law authored) (steps.app world)
    operator firing.children action
  exact (congrArg (fun targets => firing.target ∈ targets) computed).mpr issued

def conclusion (firing : Firing authored worlds steps PremiseOrigins world operator action) :
    Event (law authored) worlds steps (authored.Origin sort operator action) sort action world where
  origin := firing.origin
  source := firing.source
  target := firing.target
  valid := firing.target_member

theorem source_map (change : world ⟶ future)
    (firing : Firing authored worlds steps PremiseOrigins world operator action) :
    (firing.map change).source = S.rename (worlds.map change) firing.source :=
  (IndexedPolynomial.Free.map_node S.polynomial
    (fun base index => worlds.map change base index) operator firing.children).symm

theorem rawTarget_map (change : world ⟶ future)
    (firing : Firing authored worlds steps PremiseOrigins world operator action) :
    (firing.map change).rawTarget =
      S.rename (S.termMonad.map (worlds.map change)) firing.rawTarget :=
  firing.rule.output_map (S.termMonad.map (worlds.map change)) firing.input

theorem target_map (change : world ⟶ future)
    (firing : Firing authored worlds steps PremiseOrigins world operator action) :
    (firing.map change).target = S.rename (worlds.map change) firing.target := by
  unfold target
  rw [rawTarget_map]
  exact congrArg (fun mapping => mapping PUnit.unit sort firing.rawTarget)
    (S.termMonad.μ.naturality (worlds.map change))

end Firing

theorem introduce_target (PremiseOrigins : Type u) (world : Cᵒᵖ)
    {sort : S.Srt} {operator : S.Operator sort} {action : Actions sort}
    (given : (children worlds operator).obj world)
    (firing : authored.Firing operator (arguments authored worlds steps world given) action)
    (origins : (authored.rule sort operator action firing.origin).pattern.Occurrence → PremiseOrigins) :
    (introduce authored worlds steps PremiseOrigins world given firing origins).target =
      IndexedPolynomial.Free.join S.polynomial firing.target := by
  change IndexedPolynomial.Free.join S.polynomial
    ((authored.rule sort operator action firing.origin).output
      (introduce authored worlds steps PremiseOrigins world given firing origins).input) = _
  rw [introduce_input]
  rfl

/-- Every actual operational constructor successor has an independently
authored native firing, and every such firing produces that actual successor.
The identifier carrier is needed only to supply positive occurrences. -/
theorem operational_iff_nativeFiring (PremiseOrigins : Type u) [Nonempty PremiseOrigins]
    (world : Cᵒᵖ) {sort : S.Srt} (operator : S.Operator sort) (action : Actions sort)
    (given : (children worlds operator).obj world) (target : S.Term (worlds.obj world) sort) :
    target ∈ Operational.coalgebra (law authored) (steps.app world) PUnit.unit sort
      (IndexedPolynomial.Free.node S.polynomial operator given) action ↔
    ∃ firing : Firing authored worlds steps PremiseOrigins world operator action,
      firing.children = given ∧ firing.target = target := by
  constructor
  · intro member
    have computed := Operational.coalgebra_node (S := S) (law authored) (steps.app world)
      operator given action
    have imageMember := (congrArg (fun targets => target ∈ targets) computed).mp member
    obtain ⟨rawTarget, present, flattened⟩ :=
      (Mettapedia.CategoryTheory.FinitePowerset.mem_map _ _ _).mp imageMember
    obtain ⟨ordinary, readout⟩ := (authored.mem_targets_iff_firing operator
      (arguments authored worlds steps world given) action rawTarget).mp present
    let origins : (authored.rule sort operator action ordinary.origin).pattern.Occurrence → PremiseOrigins :=
      fun _ => Classical.choice ‹Nonempty PremiseOrigins›
    refine ⟨introduce authored worlds steps PremiseOrigins world given ordinary origins, rfl, ?_⟩
    exact (introduce_target authored worlds steps PremiseOrigins world given ordinary origins).trans
      ((congrArg (IndexedPolynomial.Free.join S.polynomial) readout).trans flattened)
  · rintro ⟨firing, sources, readout⟩
    have valid := firing.target_member
    change firing.target ∈ Operational.coalgebra (law authored) (steps.app world) PUnit.unit sort
      (IndexedPolynomial.Free.node S.polynomial operator firing.children) action at valid
    simpa only [sources, readout] using valid

def firingSpan (PremiseOrigins : Type u) {sort : S.Srt}
    (operator : S.Operator sort) (action : Actions sort) :
    EventSpan (terms worlds sort) (terms worlds sort) where
  events := firingFunctor authored worlds steps PremiseOrigins operator action
  source :=
    { app _ := ↾Firing.source
      naturality {first second} change := by
        apply ConcreteCategory.hom_ext
        intro firing
        exact firing.source_map change }
  target :=
    { app _ := ↾Firing.target
      naturality {first second} change := by
        apply ConcreteCategory.hom_ext
        intro firing
        exact firing.target_map change }

namespace Firing

variable {authored worlds steps}
variable {PremiseOrigins : Type u} {world future : Cᵒᵖ}
variable {sort : S.Srt} {operator : S.Operator sort} {action : Actions sort}

def certificate (firing : Firing authored worlds steps PremiseOrigins world operator action)
    (A : DisplayedFamily (terms worlds sort))
    (evidence : A.obj ⟨world, firing.target⟩) :=
  (firingSpan authored worlds steps PremiseOrigins operator action).introduce A world firing evidence

theorem certificate_event (firing : Firing authored worlds steps PremiseOrigins world operator action)
    (A : DisplayedFamily (terms worlds sort)) (evidence : A.obj ⟨world, firing.target⟩) :
    ((firingSpan authored worlds steps PremiseOrigins operator action).eventReadout A).app world
      ⟨firing.source, firing.certificate A evidence⟩ = firing := rfl

theorem certificate_result (firing : Firing authored worlds steps PremiseOrigins world operator action)
    (A : DisplayedFamily (terms worlds sort)) (evidence : A.obj ⟨world, firing.target⟩) :
    ((firingSpan authored worlds steps PremiseOrigins operator action).resultReadout A).app world
      ⟨firing.source, firing.certificate A evidence⟩ = ⟨firing.target, evidence⟩ := rfl

theorem certificate_event_substitution (change : world ⟶ future)
    (firing : Firing authored worlds steps PremiseOrigins world operator action)
    (A : DisplayedFamily (terms worlds sort)) (evidence : A.obj ⟨world, firing.target⟩) :
    ((firingSpan authored worlds steps PremiseOrigins operator action).eventReadout A).app future
      ((totalSpace ((firingSpan authored worlds steps PremiseOrigins operator action).certificates A)).map
        change ⟨firing.source, firing.certificate A evidence⟩) = firing.map change := by
  exact ((firingSpan authored worlds steps PremiseOrigins operator action).eventReadout_reindex A change
    ⟨firing.source, firing.certificate A evidence⟩).trans
      (congrArg ((firingSpan authored worlds steps PremiseOrigins operator action).events.map change)
        (firing.certificate_event A evidence))

theorem certificate_result_substitution (change : world ⟶ future)
    (firing : Firing authored worlds steps PremiseOrigins world operator action)
    (A : DisplayedFamily (terms worlds sort)) (evidence : A.obj ⟨world, firing.target⟩) :
    ((firingSpan authored worlds steps PremiseOrigins operator action).resultReadout A).app future
      ((totalSpace ((firingSpan authored worlds steps PremiseOrigins operator action).certificates A)).map
        change ⟨firing.source, firing.certificate A evidence⟩) =
      (totalSpace A).map change ⟨firing.target, evidence⟩ := by
  exact ((firingSpan authored worlds steps PremiseOrigins operator action).resultReadout_reindex A change
    ⟨firing.source, firing.certificate A evidence⟩).trans
      (congrArg ((totalSpace A).map change) (firing.certificate_result A evidence))

end Firing
end Mettapedia.OSLF.FiniteBranching.NativePremises
