import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NativeClauseTypes
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.PreparedRules

/-!
# Interpreted field schemas for the native record contract

The ten fields have the source contract's actual types. A schema retains its
typed source expressions for the old fields, new fields, record and guard.
Its interpreted transform rule reads every unchanged field and takes every
changed field. This conservative footprint is explicit; no concurrency or
word-layout optimization is inferred from it.

The generated schemas are a semantic presentation. Their guard denotation
uses the source model's constants. Executing those operators on arrays and
producing the witness certificate are separate refinement obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativeFieldSchema

open Mettapedia.Logic Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight
open NativeClauseData

universe w

inductive Field where
  | context | names | typeRows | termRows | dbRows | theoremRows
  | nameMap | typeMap | drops | policy
  deriving DecidableEq, Repr

def Field.all : List Field :=
  [.context, .names, .typeRows, .termRows, .dbRows, .theoremRows,
    .nameMap, .typeMap, .drops, .policy]

def Field.type (ops : Operations) : Field → HOL.Ty AtomicTy
  | .context => h1 ops
  | .names => h4 ops
  | .typeRows | .dbRows => h8 ops
  | .termRows => h11 ops
  | .theoremRows | .drops => h12 ops
  | .nameMap | .typeMap => h13 ops
  | .policy => h5 ops

structure Syntax (ops : Operations) where
  locals : List Ty
  before : (field : Field) → HOL.Term Symbol (locals.map Ty.toHOL) (field.type ops)
  after : (field : Field) → HOL.Term Symbol (locals.map Ty.toHOL) (field.type ops)
  record : HOL.Term Symbol (locals.map Ty.toHOL) (signature ops).record
  guard : HOL.Formula Symbol (locals.map Ty.toHOL)
  writes : List Field
  writes_distinct : writes.Nodup
  unchanged : ∀ field, field ∉ writes → after field = before field

def Syntax.reads {ops : Operations} (spec : Syntax ops) : List Field :=
  Field.all.filter (fun field => field ∉ spec.writes)

variable {ops : Operations}

abbrev Value (table : Fin 29 → Syntax ops)
    (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) :=
  (Σ field : Field, HOL.Ty.denote.{0,w+1} model.Carrier (field.type ops)) ⊕
    ((Σ index : Fin 29, model.Valuation ((table index).locals.map Ty.toHOL)) ⊕ Prop)

def localFrame (table : Fin 29 → Syntax ops)
    (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
    (domains : model.InhabitedDomains) (index : Fin 29) : InterpretedFrames.Frame.{w+1} where
  Carrier := model.Valuation ((table index).locals.map Ty.toHOL)
  nonempty := ⟨fun {type} _ => domains.witness type⟩

def cell (table : Fin 29 → Syntax ops)
    (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) {context : HOL.Ctx AtomicTy}
    (fields : (field : Field) → HOL.Term Symbol context (field.type ops))
    (field : Field) (values : model.Valuation context) : Value table model :=
  .inl ⟨field, model.denote (fields field) values⟩

def schema (table : Fin 29 → Syntax ops)
    (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
    (domains : model.InhabitedDomains) (index : Fin 29) :
    PreparedRules.Schema (Value table model) where
  locals := localFrame table model domains index
  certificate values := .inr (.inl ⟨index, values⟩)
  certificate_injective := by
    intro first second same
    apply eq_of_heq
    exact (Sigma.mk.inj_iff.mp (Sum.inl.inj (Sum.inr.inj same))).2
  proposition proposition := .inr (.inr proposition)
  proposition_injective := by
    intro first second same
    simpa only [Sum.inr.injEq] using same
  take := (table index).writes.map (cell table model (table index).before)
  read := (table index).reads.map (cell table model (table index).before)
  produce := (table index).writes.map (cell table model (table index).after)
  guard values := (model.denote (table index).guard values).down

def program (table : Fin 29 → Syntax ops)
    (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) (domains : model.InhabitedDomains) :
    RuleSyntax.Program (InterpretedFrames.Terms (Value table model)) :=
  Set.range (fun index => (schema table model domains index).rule)

theorem program_finite (table : Fin 29 → Syntax ops)
    (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) (domains : model.InhabitedDomains) :
    (program table model domains).Finite :=
  Set.finite_range _

theorem rule_member (table : Fin 29 → Syntax ops)
    (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
    (domains : model.InhabitedDomains) (index : Fin 29) :
    (schema table model domains index).rule ∈ program table model domains :=
  ⟨index, rfl⟩

theorem all_fields_accounted (spec : Syntax ops) (field : Field) :
    field ∈ spec.writes ∨ field ∈ spec.reads := by
  by_cases written : field ∈ spec.writes
  · exact Or.inl written
  · right
    apply List.mem_filter.mpr
    refine ⟨?_, by simpa using written⟩
    cases field <;> simp [Field.all]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativeFieldSchema
