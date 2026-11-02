import Mettapedia.OSLF.NativeTypes.Instances.MeTTaFamily.Presentations
import Mettapedia.OSLF.NativeTypes.SortProfiles.Inhabitation
import Mettapedia.GSLT.LanguageDef.ClosedInhabitation
import Mettapedia.Languages.MeTTa.HE.HELanguageDef
import Mettapedia.Languages.MeTTa.MeTTaZero
import Mettapedia.Languages.MeTTa.PeTTa.ConfigurationLanguageDef
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Syntax
import Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer
import Mettapedia.OSLF.NativeTypes.Instances.Rho.CommunicationGeometry
import Mettapedia.OSLF.NativeTypes.Instances.LetCase.Language
import Mettapedia.GSLT.LanguageDef.HOLKernelProfiles
import Mettapedia.Languages.MM0.Presentation.Calculus

open Mettapedia.OSLF.Framework

/-!
# Generated hypercubes across the MeTTa family and its hosted logics

One generator (`Occurrences.generate`), one interface reading
(`Inhabitation.interfaceOf?`) and one decision procedure
(`HypotheticalPropositional.closure`) applied to every presentation in the
tree that displays an operational site:

| presentation | operational site | index / rely at the site |
|---|---|---|
| lambda calculus | function position of beta | none / argument |
| rho calculus (paper rule) | the input, beside the output | channel / message |
| MeTTa calculus | one of two symmetric `for` | channel / pattern, partner, rest |
| MeTTa Zero | subject and space of evaluation | none / space, resp. subject |
| HE machine | the call inside `metta-call` | none / type, space, output |
| MeTTa program | the head of a call | none / argument |
| PeTTa machine | the function target of a call | none / seven machine fields |
| Π/Σ/Id shape | beta, the pair under a projection, `refl` under `J` | see below |
| HOL4 kernel | the major premise of `MP` | antecedent / minor hypotheses |
| HOL Light kernel | the major premise of `EQ_MP` | left side / minor hypotheses |
| MM0 kernel | the instance premise of theorem application | context, theorem, hypotheses / index, local hypotheses |

For each presentation, `Row` records which carriers have closed terms and
which have closed types in four regimes: the paper's completion at its origin
(no carrier ever, `Inhabitation.origin_has_no_types`) and at its top vertex,
each with and without the native constructor types. The rows are kernel
checked.

What the rows show:

* The paper's completion has closed types only where a `□`-sorted slot ranges
  over the target carrier. The HE machine, the HOL kernels and MM0 never
  have one: their targets are states or judgments, which no slot ranges over.
  Every vertex of their completion is closed-degenerate without constructor
  types. The lambda calculus, rho, the MeTTa calculus, the MeTTa program and
  the PeTTa machine have one.
* MeTTa Zero has no closed term in any carrier: its content lives in the
  model. Adjoining the sort constants makes them the first closed elements of
  every carrier (`zero_completion_inhabits`). Its completion types nothing,
  even at the top, unless constructor types are added; then three carriers
  get types only through polymorphism.
* The interfaces of HOL4's `MP` and HOL Light's `EQ_MP` major premises are
  equal: the local cube cannot tell which connective is eliminated.
* The receive site of the paper's rho rule has three slots, hence one hundred
  and twenty-eight based signature choices, as in the paper; `Slots.modalFamily`
  counts two of them.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.MeTTaFamily.Census

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.ModalHypercube (HSort)
open Mettapedia.OSLF.NativeTypes.Generation.Occurrences
open Mettapedia.OSLF.NativeTypes.SortProfiles
open Mettapedia.OSLF.NativeTypes.SortProfiles.Inhabitation
open Mettapedia.Logic.LP.HypotheticalPropositional
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.ClosedInhabitation (Inhabited Supported)

/-! ## Rows -/

/-- Declared carriers with closed terms, and with closed types in three regimes. -/
structure Row where
  inhabited : List String
  seededOrigin : List String
  paperTop : List String
  seededTop : List String

/-- A row is exact for a presentation. -/
def RowHolds (language : LanguageDef) (row : Row) : Prop :=
  Supported language ∧
  ∀ sort ∈ language.types.map TypeDecl.name,
    (sort ∈ closure (ClosedInhabitation.clauses language)
        (fuelFor (ClosedInhabitation.clauses language)) ∅ ↔ sort ∈ row.inhabited) ∧
    (Derives (seeded language (paperOrigin language)) ∅ (.base sort, .star) ↔
      sort ∈ row.seededOrigin) ∧
    (Derives (paperTop language) ∅ (.base sort, .star) ↔ sort ∈ row.paperTop) ∧
    (Derives (seeded language (paperTop language)) ∅ (.base sort, .star) ↔
      sort ∈ row.seededTop)

instance (language : LanguageDef) (row : Row) : Decidable (RowHolds language row) := by
  unfold RowHolds; infer_instance

/-- An exact row decides closed inhabitation by its first column. -/
theorem RowHolds.inhabited_iff {language : LanguageDef} {row : Row} (holds : RowHolds language row)
    {sort : String} (declared : sort ∈ language.types.map TypeDecl.name) :
    Inhabited language sort ↔ sort ∈ row.inhabited := by
  rw [ClosedInhabitation.inhabited_iff_closure holds.1]
  exact (holds.2 sort declared).1

/-- The declared carrier names of a presentation. -/
abbrev names (language : LanguageDef) : List String := language.types.map TypeDecl.name

/-- Assemble a row from its four columns. -/
theorem RowHolds.intro {language : LanguageDef} {row : Row} (supported : Supported language)
    (inhabited : ∀ sort ∈ names language,
      (sort ∈ closure (ClosedInhabitation.clauses language)
        (fuelFor (ClosedInhabitation.clauses language)) ∅ ↔ sort ∈ row.inhabited))
    (seededOrigin : ∀ sort ∈ names language,
      (Derives (seeded language (paperOrigin language)) ∅ (.base sort, .star) ↔
        sort ∈ row.seededOrigin))
    (top : ∀ sort ∈ names language,
      (Derives (paperTop language) ∅ (.base sort, .star) ↔ sort ∈ row.paperTop))
    (seededTop : ∀ sort ∈ names language,
      (Derives (seeded language (paperTop language)) ∅ (.base sort, .star) ↔
        sort ∈ row.seededTop)) :
    RowHolds language row :=
  ⟨supported, fun sort member =>
    ⟨inhabited sort member, seededOrigin sort member, top sort member, seededTop sort member⟩⟩

/-- When no slot ranges over a target carrier, the top column is empty. -/
theorem untyped_top_column {language : LanguageDef} (unbound : TargetsUnbound (interfaces language)) :
    ∀ sort ∈ names language,
      (Derives (paperTop language) ∅ (.base sort, .star) ↔ sort ∈ ([] : List String)) :=
  fun _ _ => ⟨fun derived => absurd derived (paperTop_untyped language unbound _), nofun⟩

/-- When the seeded origin types every declared carrier, so does the seeded top. -/
theorem full_seededTop_column {language : LanguageDef}
    (all : ∀ sort ∈ names language, Derives (seeded language (paperOrigin language)) ∅ (.base sort, .star)) :
    ∀ sort ∈ names language,
      (Derives (seeded language (paperTop language)) ∅ (.base sort, .star) ↔ sort ∈ names language) :=
  fun sort member => ⟨fun _ => member, fun _ => seededOrigin_le_seededTop language (all sort member)⟩

/-- The paper's completion at its origin types no carrier of any presentation. -/
theorem paperOrigin_untyped (language : LanguageDef) (carrier : TypeExpr) :
    ¬ Derives (paperOrigin language) ∅ (carrier, .star) :=
  origin_has_no_types _ _ carrier

/-- A site of the presentation, located by rule name and address, with the
given interface. -/
def HasSite (language : LanguageDef) (rule : String) (position : List Nat)
    (interface : Interface) : Prop :=
  ∃ site ∈ generate language, site.rule.name = rule ∧ site.position = position ∧
    interfaceOf? language site = some interface

instance (language : LanguageDef) (rule : String) (position : List Nat) (interface : Interface) :
    Decidable (HasSite language rule position interface) := by
  unfold HasSite; infer_instance

theorem HasSite.interface_mem {language : LanguageDef} {rule : String} {position : List Nat}
    {interface : Interface} (located : HasSite language rule position interface) :
    interface ∈ interfaces language := by
  obtain ⟨site, member, _, _, read⟩ := located
  exact List.mem_dedup.mpr (List.mem_filterMap.mpr ⟨site, member, read⟩)

/-- A located site's slot counts follow from its interface: the paper's count,
and the count of `Slots.modalFamily`, which omits the index slots. -/
theorem HasSite.slotCounts {language : LanguageDef} {rule : String} {position : List Nat}
    {interface : Interface} (located : HasSite language rule position interface) :
    ∃ site ∈ generate language,
      SiteInterfaces.slotCount site = interface.index.length + interface.rely.length + 1 ∧
        (Slots.modalFamily language site).slotCount = interface.rely.length + 1 := by
  obtain ⟨site, member, _, _, read⟩ := located
  refine ⟨site, member, interfaceOf?_slotCount read, ?_⟩
  rw [Slots.modal_slot_count, (interfaceOf?_lengths read).2]

/-! ## The lambda calculus -/

abbrev lambda : LanguageDef := Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.language

theorem lambda_row : RowHolds lambda ⟨["Term"], [], ["Term"], ["Term"]⟩ := by decide +kernel

theorem lambda_beta_site : HasSite lambda "Beta" [0] (betaInterface (.base "Term")) := by
  decide +kernel

/-! ## The rho calculus -/

abbrev rhoPaper : LanguageDef := Mettapedia.OSLF.NativeTypes.Instances.Rho.CommunicationGeometry.language

theorem rhoPaper_row :
    RowHolds rhoPaper ⟨["Proc", "Name"], ["Proc", "Name"], ["Proc", "Name"], ["Proc", "Name"]⟩ := by
  decide +kernel

/-- The receive site: the channel is an index, the message a rely variable. -/
theorem rho_receive_site :
    HasSite rhoPaper "Comm" [0] ⟨[.base "Name"], [.base "Proc"], .base "Proc", .base "Proc"⟩ := by
  decide +kernel

theorem rho_receive_slots :
    ∃ site ∈ generate rhoPaper, site.position = [0] ∧ SiteInterfaces.slotCount site = 3 ∧
      (Slots.modalFamily rhoPaper site).slotCount = 2 := by
  decide +kernel

theorem rhoCalc_row :
    RowHolds rhoCalc ⟨["Proc", "Name"], ["Proc", "Name"], ["Proc", "Name"], ["Proc", "Name"]⟩ := by
  decide +kernel

/-- The tree's rule adds its open rest as a second rely variable. -/
theorem rhoCalc_receive_site :
    HasSite rhoCalc "Comm" [0]
      ⟨[.base "Name"], [.base "Proc", .base "Proc"], .base "Proc", .base "Proc"⟩ := by
  decide +kernel

/-! ## The MeTTa calculus -/

abbrev mettaCalculus : LanguageDef := Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.mettaCalc

theorem mettaCalculus_row :
    RowHolds mettaCalculus ⟨["Proc", "Name", "Term"], ["Proc", "Name", "Term"],
      ["Proc", "Name", "Term"], ["Proc", "Name", "Term"]⟩ := by
  decide +kernel

/-- One of the two symmetric `for`: the channel is an index; the partner's
pattern, the partner's continuation and the rest are rely variables. -/
theorem mettaCalculus_comm_site :
    HasSite mettaCalculus "CommSym" [0]
      ⟨[.base "Name"], [.base "Term", .base "Proc", .base "Proc"], .base "Proc", .base "Proc"⟩ := by
  decide +kernel

/-! ## MeTTa Zero -/

abbrev zero : LanguageDef := Mettapedia.Languages.MeTTa.MeTTaZero.language

/-- **No closed term in any carrier**, and closed types only with constructor
types at the top vertex. -/
theorem zero_row : RowHolds zero ⟨[], [], [], ["Atom", "Space", "Process"]⟩ := by
  decide +kernel

theorem zero_uninhabited :
    ∀ sort ∈ zero.types.map TypeDecl.name, ¬ Inhabited zero sort := by
  intro sort declared inhabited
  have := (zero_row.inhabited_iff declared).mp inhabited
  simp at this

/-- The term language of the completion: the sort constants `∗^X` and `□^X`
of every carrier become nullary constructors. -/
def sortConstant (marker carrier : String) : GrammarRule where
  label := marker ++ carrier
  category := carrier
  params := []
  syntaxPattern := []

def withSortConstants (language : LanguageDef) : LanguageDef :=
  { language with
    terms := language.terms ++ (names language).flatMap fun carrier =>
      [sortConstant "star:" carrier, sortConstant "box:" carrier] }

/-- **Adjoining sort constants inhabits every carrier of MeTTa Zero**: they
become the first closed elements of carriers that had none. -/
theorem zero_completion_inhabits :
    ∀ sort ∈ names zero, Inhabited (withSortConstants zero) sort := by
  intro sort member
  have supported : Supported (withSortConstants zero) := by decide +kernel
  rw [ClosedInhabitation.inhabited_iff_closure supported]
  revert sort member
  decide +kernel

/-- The subject of evaluation, with the space as its only rely variable: the
types of atoms are indexed by programs. -/
theorem zero_subject_site :
    HasSite zero "zero-evaluate" [1] ⟨[], [.base "Space"], .base "Atom", .base "Process"⟩ := by
  decide +kernel

/-- The space in evaluation, with the subject as rely: a program as a function
from subjects to answers. -/
theorem zero_space_site :
    HasSite zero "zero-evaluate" [0] ⟨[], [.base "Atom"], .base "Space", .base "Process"⟩ := by
  decide +kernel

/-! ## HE MeTTa, the machine -/

abbrev heMachine : LanguageDef := Mettapedia.Languages.MeTTa.HE.LanguageDef.mettaHE

/-- No slot of the machine ranges over states, the only targets. -/
theorem heMachine_targets_unbound : TargetsUnbound (interfaces heMachine) := by decide +kernel

set_option maxRecDepth 100000 in
theorem heMachine_seededOrigin :
    ∀ sort ∈ names heMachine, Derives (seeded heMachine (paperOrigin heMachine)) ∅ (.base sort, .star) := by
  decide +kernel

theorem heMachine_row :
    RowHolds heMachine ⟨names heMachine, names heMachine, [], names heMachine⟩ :=
  RowHolds.intro (by decide +kernel) (by decide +kernel)
    (fun sort member => ⟨fun _ => member, fun _ => heMachine_seededOrigin sort member⟩)
    (untyped_top_column heMachine_targets_unbound) (full_seededTop_column heMachine_seededOrigin)

/-! ## A MeTTa program -/

abbrev program : LanguageDef := programLanguage "metta-program" sampleProgram

theorem program_row :
    RowHolds program ⟨["GroundAtom", "GroundList"],
      ["GroundAtom", "GroundLiteral", "GroundList", "GroundText"],
      ["GroundAtom", "GroundLiteral", "GroundList", "GroundText"],
      ["GroundAtom", "GroundLiteral", "GroundList", "GroundText"]⟩ := by
  decide +kernel

theorem program_head_site :
    HasSite program "equation-0" [0, 0] (betaInterface (.base "GroundAtom")) := by
  decide +kernel

/-! ## PeTTa, the machine -/

abbrev pettaMachine : LanguageDef :=
  Mettapedia.Languages.MeTTa.PeTTa.ConfigurationLanguageDef.language

private def pettaWitness (sort : String) : Interface :=
  ⟨[], List.replicate (if sort = "GroundList" then 4 else 5) (.base "GroundAtom"),
    .base sort, .base "GroundAtom"⟩

private def pettaWitnessPosition : String → List Nat
  | "GroundAtom" => [0, 0]
  | "GroundLiteral" => [0, 0, 0]
  | "GroundList" => [0, 2, 0]
  | _ => [0, 0, 0, 0]

set_option maxRecDepth 100000 in
private theorem pettaWitness_located :
    ∀ sort ∈ names pettaMachine,
      HasSite pettaMachine "sequence-done" (pettaWitnessPosition sort) (pettaWitness sort) := by
  decide +kernel

private theorem pettaWitness_mem {sort : String} (declared : sort ∈ names pettaMachine) :
    pettaWitness sort ∈ interfaces pettaMachine := (pettaWitness_located sort declared).interface_mem

private def pettaWitnessClauses : List (Clause Level) :=
  (names pettaMachine).map (fun sort => modalClause (pettaWitness sort) (originProfile (pettaWitness sort))) ++
    pettaMachine.terms.map constructorClause

private theorem pettaWitnessClauses_subset :
    pettaWitnessClauses ⊆ seeded pettaMachine (paperOrigin pettaMachine) := by
  intro clause member
  rcases List.mem_append.mp member with fromSite | fromConstructor
  · obtain ⟨sort, declared, rfl⟩ := List.mem_map.mp fromSite
    exact List.mem_append_left _ (List.mem_append_right _
      (List.mem_map.mpr ⟨pettaWitness sort, pettaWitness_mem declared, rfl⟩))
  · exact List.mem_append_right _ fromConstructor

set_option maxRecDepth 100000 in
theorem pettaMachine_seededOrigin :
    ∀ sort ∈ names pettaMachine,
      Derives (seeded pettaMachine (paperOrigin pettaMachine)) ∅ (.base sort, .star) := by
  have witnessed : ∀ sort ∈ names pettaMachine,
      Derives pettaWitnessClauses ∅ (.base sort, .star) := by decide +kernel
  intro sort declared
  exact Derives.mono_clauses pettaWitnessClauses_subset (witnessed sort declared)

set_option maxRecDepth 100000 in
/-- Every carrier is the hole of a site with a rely slot over its target: the
machine state is an atom, and atoms are rely slots. -/
theorem pettaMachine_bound_holes :
    ∀ sort ∈ names pettaMachine, ∃ interface ∈ interfaces pettaMachine,
      interface.hole = .base sort ∧ interface.target ∈ interface.index ++ interface.rely := by
  intro sort declared
  refine ⟨pettaWitness sort, pettaWitness_mem declared, rfl, ?_⟩
  change TypeExpr.base "GroundAtom" ∈ [] ++ List.replicate (if sort = "GroundList" then 4 else 5) (TypeExpr.base "GroundAtom")
  split_ifs <;> simp

/-- Polymorphism types every carrier of the PeTTa machine at the top. -/
theorem pettaMachine_top :
    ∀ sort ∈ names pettaMachine, Derives (paperTop pettaMachine) ∅ (.base sort, .star) := by
  intro sort member
  obtain ⟨interface, interfaceMember, hole, bound⟩ := pettaMachine_bound_holes sort member
  rw [← hole]
  exact paperTop_types_hole _ interfaceMember bound

theorem pettaMachine_row :
    RowHolds pettaMachine ⟨["GroundAtom", "GroundList"], names pettaMachine, names pettaMachine,
      names pettaMachine⟩ :=
  RowHolds.intro (by decide +kernel) (by decide +kernel)
    (fun sort member => ⟨fun _ => member, fun _ => pettaMachine_seededOrigin sort member⟩)
    (fun sort member => ⟨fun _ => member, fun _ => pettaMachine_top sort member⟩)
    (full_seededTop_column pettaMachine_seededOrigin)

/-- The function target of a finished call: the evaluated arguments and six
machine fields are rely variables. -/
theorem pettaMachine_call_site :
    HasSite pettaMachine "equations" [0, 2, 0, 2]
      ⟨[], List.replicate 7 (.base "GroundAtom"), .base "GroundAtom", .base "GroundAtom"⟩ := by
  decide +kernel

/-! ## The shape of the Π/Σ/Id computation rules -/

theorem piSigmaIdShape_row :
    RowHolds piSigmaIdShape ⟨["Tm", "Ctx"], ["Tm", "Ctx"], ["Tm"], ["Tm", "Ctx"]⟩ := by
  decide +kernel

theorem piSigmaId_beta_site : HasSite piSigmaIdShape "BetaPi" [0] (betaInterface (.base "Tm")) := by
  decide +kernel

/-- The pair under a projection: no index and no rely, only the target axis. -/
theorem piSigmaId_projection_site :
    HasSite piSigmaIdShape "BetaSigmaFst" [0] ⟨[], [], .base "Tm", .base "Tm"⟩ := by
  decide +kernel

/-- `refl a` under `J`: the endpoint is an index, the type, motive and case
are rely variables. -/
theorem piSigmaId_identity_site :
    HasSite piSigmaIdShape "J-refl" [5]
      ⟨[.base "Tm"], [.base "Tm", .base "Tm", .base "Tm"], .base "Tm", .base "Tm"⟩ := by
  decide +kernel

/-! ## Let and case -/

abbrev letCase : LanguageDef := Mettapedia.OSLF.NativeTypes.Instances.LetCase.language

/-- `return v` under `let`: the body is the only rely variable. -/
theorem letCase_return_site :
    HasSite letCase "LetReturn" [0]
      ⟨[], [.base "Computation"], .base "Computation", .base "Computation"⟩ := by
  decide +kernel

theorem letCase_row :
    RowHolds letCase ⟨["Value", "Computation"], ["Value", "Computation"], ["Value", "Computation"],
      ["Value", "Computation"]⟩ := by
  decide +kernel

/-! ## The HOL kernels -/

abbrev hol4 : LanguageDef := HOLKernelProfiles.hol4LcfKernel
abbrev holLight : LanguageDef := HOLKernelProfiles.holLightEqKernel

/-- The carriers of the HOL kernels. -/
def holCarriers : List String := ["HolTerm", "HolHyps", "HolThm", "HolProof", "HolJudgment", "HolSubst"]

theorem hol4_names : names hol4 = holCarriers := by decide
theorem holLight_names : names holLight = holCarriers := by decide

theorem hol4_targets_unbound : TargetsUnbound (interfaces hol4) := by decide +kernel
theorem holLight_targets_unbound : TargetsUnbound (interfaces holLight) := by decide +kernel

theorem hol4_seededOrigin :
    ∀ sort ∈ names hol4, Derives (seeded hol4 (paperOrigin hol4)) ∅ (.base sort, .star) := by
  decide +kernel

theorem holLight_seededOrigin :
    ∀ sort ∈ names holLight, Derives (seeded holLight (paperOrigin holLight)) ∅ (.base sort, .star) := by
  decide +kernel

theorem hol4_row : RowHolds hol4 ⟨names hol4, names hol4, [], names hol4⟩ :=
  RowHolds.intro (by decide +kernel) (by decide +kernel)
    (fun sort member => ⟨fun _ => member, fun _ => hol4_seededOrigin sort member⟩)
    (untyped_top_column hol4_targets_unbound) (full_seededTop_column hol4_seededOrigin)

theorem holLight_row : RowHolds holLight ⟨names holLight, names holLight, [], names holLight⟩ :=
  RowHolds.intro (by decide +kernel) (by decide +kernel)
    (fun sort member => ⟨fun _ => member, fun _ => holLight_seededOrigin sort member⟩)
    (untyped_top_column holLight_targets_unbound) (full_seededTop_column holLight_seededOrigin)

/-- The major premise of modus ponens: the antecedent is an index, the minor
premise's hypotheses a rely variable. -/
theorem hol4_mp_site :
    HasSite hol4 "H4_MP" [0, 0]
      ⟨[.base "HolTerm"], [.base "HolHyps"], .base "HolThm", .base "HolJudgment"⟩ := by
  decide +kernel

/-- The major premise of `EQ_MP` has the same interface. -/
theorem holLight_eqmp_site :
    HasSite holLight "HL_EQ_MP" [0, 0]
      ⟨[.base "HolTerm"], [.base "HolHyps"], .base "HolThm", .base "HolJudgment"⟩ := by
  decide +kernel

theorem holLight_has_no_mp : ∀ rule ∈ holLight.rewrites, rule.name ≠ "HL_MP" := by decide

/-! ## The MM0 kernel -/

abbrev mm0 : LanguageDef :=
  checkingLanguage Mettapedia.Languages.MM0.Presentation.Calculus.definition "MM0Data"

theorem mm0_targets_unbound : TargetsUnbound (interfaces mm0) := by decide +kernel

theorem mm0_seededOrigin :
    ∀ sort ∈ names mm0, Derives (seeded mm0 (paperOrigin mm0)) ∅ (.base sort, .star) := by
  decide +kernel

theorem mm0_row : RowHolds mm0 ⟨names mm0, names mm0, [], names mm0⟩ :=
  RowHolds.intro (by decide +kernel) (by decide +kernel)
    (fun sort member => ⟨fun _ => member, fun _ => mm0_seededOrigin sort member⟩)
    (untyped_top_column mm0_targets_unbound) (full_seededTop_column mm0_seededOrigin)

/-- Theorem application at its instance premise: context, theorem and
instance hypotheses are indices; the theorem index and local hypotheses rely. -/
theorem mm0_application_site :
    HasSite mm0 "mm0-theorem" [1]
      ⟨[.base "MM0Data", .base "MM0Data", .base "MM0Data"], [.base "MM0Data", .base "MM0Data"],
        .base "Judgment", .base "Judgment"⟩ := by
  decide +kernel

end Mettapedia.OSLF.NativeTypes.Instances.MeTTaFamily.Census
