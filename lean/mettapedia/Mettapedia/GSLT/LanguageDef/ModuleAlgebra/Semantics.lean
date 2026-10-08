import Mettapedia.GSLT.LanguageDef.ModuleAlgebra.Authoring
import Mettapedia.GSLT.Scope.Arrows
import Mettapedia.GSLT.Core.OperationalRealizationOSLF
import Mettapedia.GSLT.Core.ProofRelevantGSLT

/-!
# What a presentation join preserves

Origin compatibility admits a declaration union; it does not prove semantic
conservativity. This module connects that union to the existing contextual
admission and scope algebras, and gives its operational meaning relative to a
shared term language and equational theory. New rules can interact with old ones.
-/

namespace Mettapedia.GSLT.LanguageDef.ModuleAlgebra

open Mettapedia.GSLT
open Mettapedia.Logic.TheoryModel

variable {Origin Label Body : Type}
  [DecidableEq Origin] [DecidableEq Label] [DecidableEq Body]

def PointwiseAdmitted (admit : Body → Prop) (p : Presentation Origin Label Body) : Prop :=
  ∀ entry ∈ p.val, admit entry.body

/-- An instance of the established gluing contract for independently specified
per-declaration admission. Global typing and dependency checks need stronger
admission contracts. -/
def pointwiseAdmission (admit : Body → Prop) :
    GSLT.ContextualAdmission (presentationSystem (Origin := Origin) (Label := Label)
      (Body := Body)) where
  Admitted := PointwiseAdmitted admit
  Compatible := fun p q => Compatible p.val q.val
  glue := by
    intro p q hp hq compatible
    let r : Presentation Origin Label Body :=
      ⟨p.val ∪ q.val, valid_union_iff.mpr ⟨p.property, q.property, compatible⟩⟩
    refine ⟨r, join_eq_some_iff.mpr rfl, ?_⟩
    intro entry member
    exact (Finset.mem_union.mp member).elim (hp entry) (hq entry)

/-- The meanings of declarations must respect the independently supplied
equations of the shared core. -/
structure RuleSemantics (Body : Type) (core : GSLT) where
  step : Body → core.Term → core.Term → Prop
  respectsLeft : ∀ {body source source' target},
    core.Equiv source source' → step body source target →
      ∃ target', step body source' target' ∧ core.Equiv target target'
  respectsRight : ∀ {body source target target'},
    step body source target → core.Equiv target target' → step body source target'

/-- All rules supplied by the meaning family, before selecting declarations. -/
def RuleSemantics.ambient {core : GSLT} (meaning : RuleSemantics Body core) : GSLT where
  Term := core.Term
  equations := core.equations
  rewrites := fun source target => ∃ body, meaning.step body source target
  rewrites_resp_left := by
    rintro source source' target equivalent ⟨body, step⟩
    obtain ⟨target', next, equal⟩ := meaning.respectsLeft equivalent step
    exact ⟨target', ⟨body, next⟩, equal⟩
  rewrites_resp_right := by
    rintro source target target' ⟨body, step⟩ equivalent
    exact ⟨body, meaning.respectsRight step equivalent⟩

/-- Declaration selection is an instance of the established GSLT step filter. -/
def RuleSemantics.declarationFilter {core : GSLT} (meaning : RuleSemantics Body core)
    (p : Presentation Origin Label Body) : GSLT.StepFilter meaning.ambient where
  keep := fun source target => ∃ entry ∈ p.val, meaning.step entry.body source target
  keep_sound := by
    rintro source target ⟨entry, _, step⟩
    exact ⟨entry.body, step⟩
  resp_left := by
    rintro source source' target equivalent ⟨entry, member, step⟩
    obtain ⟨target', next, equal⟩ := meaning.respectsLeft equivalent step
    exact ⟨target', ⟨entry, member, next⟩, equal⟩
  resp_right := by
    rintro source target target' ⟨entry, member, step⟩ equivalent
    exact ⟨entry, member, meaning.respectsRight step equivalent⟩

/-- Use the shared restriction construction; no second operational framework.
This does not elaborate unparsed upstream rule specifications. -/
def realize {core : GSLT} (meaning : RuleSemantics Body core)
    (p : Presentation Origin Label Body) : GSLT :=
  meaning.ambient.restrict (meaning.declarationFilter p)

/-- Module inclusion enters the existing operational category, so the generic
path functor and staged realization laws apply to these actual systems. -/
def inclusionTranslation {core : GSLT} (meaning : RuleSemantics Body core)
    {p q : Presentation Origin Label Body} (included : p.val ⊆ q.val) :
    IndexedOperational.OperationalTranslation (realize meaning p) (realize meaning q) where
  mapTerm := id
  mapEquiv := fun equivalent => equivalent
  mapStep := by
    rintro source target ⟨entry, member, step⟩
    exact ⟨entry, included member, step⟩

/-- The existing proof-relevant GSLT interface retains which declaration
enabled a step. Two origins can have the same semantic endpoints. -/
def retained {core : GSLT} (meaning : RuleSemantics Body core)
    (p : Presentation Origin Label Body) : ProofRelevant.ProofRelevantGSLT where
  theory := realize meaning p
  steps := {
    Evidence := fun source target =>
      Sigma fun entry : {entry // entry ∈ p.val} =>
        PLift (meaning.step entry.val.body source target)
    erases_iff := by
      intro source target
      constructor
      · rintro ⟨⟨entry, step⟩⟩
        exact ⟨entry.val, entry.property, step.down⟩
      · rintro ⟨entry, member, step⟩
        exact ⟨⟨⟨entry, member⟩, ⟨step⟩⟩⟩ }

/-- Inclusion maps retained evidence without conflating declarations. It
does not assert the backward coverage required by a two-sided translation. -/
def inclusionEvidence {core : GSLT} (meaning : RuleSemantics Body core)
    {p q : Presentation Origin Label Body} (included : p.val ⊆ q.val)
    {source target : core.Term} (evidence : (retained meaning p).steps.Evidence source target) :
    (retained meaning q).steps.Evidence source target :=
  ⟨⟨evidence.1.val, included evidence.1.property⟩, evidence.2⟩

theorem inclusionEvidence_injective {core : GSLT} (meaning : RuleSemantics Body core)
    {p q : Presentation Origin Label Body} (included : p.val ⊆ q.val)
    (source target : core.Term) :
    Function.Injective (fun evidence : (retained meaning p).steps.Evidence source target =>
      inclusionEvidence meaning included evidence) := by
  intro first second equal
  have entryEqual : first.1 = second.1 := Subtype.ext
    (congrArg (fun evidence => evidence.1.val) equal)
  cases first with
  | mk firstEntry firstStep =>
    cases second with
    | mk secondEntry secondStep =>
      cases entryEqual
      congr
      cases firstStep
      cases secondStep
      rfl

/-- One-step behavior of a successful join is exactly the union of the
component behaviors, in both directions. -/
theorem realize_join_step {core : GSLT} (meaning : RuleSemantics Body core)
    {p q r : Presentation Origin Label Body} (joined : join p q = some r)
    (source target : core.Term) :
    (realize meaning r).Step source target ↔
      (realize meaning p).Step source target ∨ (realize meaning q).Step source target := by
  have value := join_eq_some_iff.mp joined
  change (∃ entry ∈ r.val, meaning.step entry.body source target) ↔ _
  rw [← value]
  constructor
  · rintro ⟨entry, member, step⟩
    exact (Finset.mem_union.mp member).elim
      (fun hp => Or.inl ⟨entry, hp, step⟩) (fun hq => Or.inr ⟨entry, hq, step⟩)
  · rintro (⟨entry, member, step⟩ | ⟨entry, member, step⟩)
    · exact ⟨entry, Finset.mem_union_left _ member, step⟩
    · exact ⟨entry, Finset.mem_union_right _ member, step⟩

theorem realize_multistep_mono {core : GSLT} (meaning : RuleSemantics Body core)
    {p q : Presentation Origin Label Body} (included : p.val ⊆ q.val)
    {source target : core.Term} (path : (realize meaning p).MultiStep source target) :
    (realize meaning q).MultiStep source target := by
  exact (IndexedOperational.OperationalRealization.ofTranslation
    (inclusionTranslation meaning included)).mapMultiStep path

/-- A reachable fragment stays conservative when every added rule is already
an old rule there, and old rules preserve that fragment. These are local rule
obligations, not an assumed equivalence of complete executions. -/
theorem realize_join_reflects_on {core : GSLT} (meaning : RuleSemantics Body core)
    {p q r : Presentation Origin Label Body} (joined : join p q = some r)
    (region : Set core.Term)
    (closed : ∀ {source target}, source ∈ region →
      (realize meaning p).Step source target → target ∈ region)
    (redundant : ∀ entry ∈ q.val, ∀ source ∈ region, ∀ target,
      meaning.step entry.body source target → (realize meaning p).Step source target)
    {source target : core.Term} (start : source ∈ region)
    (path : (realize meaning r).MultiStep source target) :
    (realize meaning p).MultiStep source target := by
  refine @GSLT.MultiStep.rec (realize meaning r)
    (fun a b _ => a ∈ region → (realize meaning p).MultiStep a b)
    ?_ ?_ source target path start
  · intro term _
    exact @GSLT.MultiStep.refl (realize meaning p) term
  · intro a b c first rest ih start
    have old : (realize meaning p).Step a b := by
      rcases (realize_join_step meaning joined a b).mp first with old | added
      · exact old
      · obtain ⟨entry, member, step⟩ := added
        exact redundant entry member a start b step
    exact .step old (ih (closed start old))

/-- The body-level theory forgets origin and exposure names explicitly. -/
def bodyTheory (p : Presentation Origin Label Body) : Set Body :=
  {body | ∃ entry ∈ p.val, entry.body = body}

theorem bodyTheory_join {p q r : Presentation Origin Label Body}
    (joined : join p q = some r) : bodyTheory r = bodyTheory p ∪ bodyTheory q := by
  have value := join_eq_some_iff.mp joined
  ext body
  change (∃ entry ∈ r.val, entry.body = body) ↔ _
  rw [← value]
  constructor
  · rintro ⟨entry, member, equal⟩
    exact (Finset.mem_union.mp member).elim
      (fun hp => Or.inl ⟨entry, hp, equal⟩) (fun hq => Or.inr ⟨entry, hq, equal⟩)
  · rintro (⟨entry, member, equal⟩ | ⟨entry, member, equal⟩)
    · exact ⟨entry, Finset.mem_union_left _ member, equal⟩
    · exact ⟨entry, Finset.mem_union_right _ member, equal⟩

theorem models_join {Str : Type*} (Sat : Str → Body → Prop)
    {p q r : Presentation Origin Label Body} (joined : join p q = some r) :
    models Sat (bodyTheory r) = models Sat (bodyTheory p) ∩ models Sat (bodyTheory q) := by
  rw [bodyTheory_join joined, models_union]

/-- Semantic scope changes compose along the same successful declaration join. -/
theorem carve_join {Str : Type*} (Sat : Str → Body → Prop) (admittedUniverse : Set Str)
    {p q r : Presentation Origin Label Body} (joined : join p q = some r) :
    carve Sat (carve Sat admittedUniverse (bodyTheory p)) (bodyTheory q) =
      carve Sat admittedUniverse (bodyTheory r) := by
  rw [Scope.carve_carve, bodyTheory_join joined]

/-- Compatible origin bookkeeping alone does not guarantee conservativity:
the added axioms must already follow in the original scope. -/
theorem join_conservative_iff {Str : Type*} (Sat : Str → Body → Prop) (admittedUniverse : Set Str)
    {p q r : Presentation Origin Label Body} (joined : join p q = some r) (theory : Set Body) :
    consequencesIn Sat (carve Sat admittedUniverse (bodyTheory r)) theory =
        consequencesIn Sat (carve Sat admittedUniverse (bodyTheory p)) theory ↔
      bodyTheory q ⊆ consequencesIn Sat (carve Sat admittedUniverse (bodyTheory p)) theory := by
  rw [← carve_join Sat admittedUniverse joined]
  exact Scope.carve_conservative_iff _ _ _

end Mettapedia.GSLT.LanguageDef.ModuleAlgebra
