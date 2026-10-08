import Mettapedia.GSLT.Core.ContextualLadderTerminal
import Mettapedia.GSLT.Core.ContextualTypeReindexing

/-!
# Local family presentations of contextual types

A local presentation consists of a parameter context, a family over that
context and a name from the current context. Its decoded type is the actual
substitution of that family along the name. Reindexing changes the name by
composition and retains the supplied parameter family.

The construction below derives the contextual substitution and comprehension
laws, including all term transports, from the given CwF. These parameter
contexts are external family presentations; no internal universe type or
universe decoding axiom is introduced. Strictly stable logical constructors
require additional parameter-space constructions.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualLocalUniverses

open Mettapedia.GSLT.Core.ContextualLadder

universe u v w w'

variable (C : Cwf.{u, v, w, w'})

structure LocalType (context : C.Ctx) where
  parameters : C.Ctx
  family : C.Ty parameters
  name : C.Sub context parameters

namespace LocalType

variable {C}

def decoded {context : C.Ctx} (type : LocalType C context) : C.Ty context :=
  C.tySub type.family type.name

def reindex {source target : C.Ctx} (type : LocalType C target)
    (substitution : C.Sub source target) : LocalType C source :=
  ⟨type.parameters, type.family, C.compS type.name substitution⟩

theorem reindex_id {context : C.Ctx} (type : LocalType C context) :
    type.reindex (C.idS context) = type := by
  cases type
  simp only [reindex, C.comp_id]

theorem reindex_comp {source middle target : C.Ctx} (type : LocalType C target)
    (later : C.Sub middle target) (earlier : C.Sub source middle) :
    type.reindex (C.compS later earlier) = (type.reindex later).reindex earlier := by
  cases type
  simp only [reindex, C.comp_assoc]

theorem decoded_reindex {source target : C.Ctx} (type : LocalType C target)
    (substitution : C.Sub source target) :
    (type.reindex substitution).decoded = C.tySub type.decoded substitution :=
  C.tySub_comp type.family type.name substitution

/-- Every supplied contextual type has a presentation over its own
context. This is a section of decoding, rather than a unique presentation. -/
def present {context : C.Ctx} (type : C.Ty context) : LocalType C context :=
  ⟨context, type, C.idS context⟩

theorem decoded_present {context : C.Ctx} (type : C.Ty context) :
    (present type).decoded = type := C.tySub_id type

end LocalType

abbrev Term (context : C.Ctx) (type : LocalType C context) := C.Tm context type.decoded

variable {C}

def substituteTerm {source target : C.Ctx} {type : LocalType C target}
    (term : Term C target type) (substitution : C.Sub source target) :
    Term C source (type.reindex substitution) :=
  cast (congrArg (C.Tm source) (type.decoded_reindex substitution).symm)
    (C.tmSub term substitution)

theorem substituteTerm_heq {source target : C.Ctx} {type : LocalType C target}
    (term : Term C target type) (substitution : C.Sub source target) :
    HEq (substituteTerm term substitution) (C.tmSub term substitution) := cast_heq _ _

theorem substituteTerm_id {context : C.Ctx} {type : LocalType C context}
    (term : Term C context type) : HEq (substituteTerm term (C.idS context)) term :=
  (substituteTerm_heq term (C.idS context)).trans
    ((heq_of_eq (C.tmSub_id term)).trans (cast_heq _ _))

theorem substituteTerm_comp {source middle target : C.Ctx} {type : LocalType C target}
    (term : Term C target type) (later : C.Sub middle target) (earlier : C.Sub source middle) :
    HEq (substituteTerm term (C.compS later earlier))
      (substituteTerm (substituteTerm term later) earlier) := by
  refine (substituteTerm_heq term (C.compS later earlier)).trans ?_
  refine (TypeOver.tmSub_comp_heq term later earlier).trans ?_
  refine (TypeOver.tmSub_heq (type.decoded_reindex later).symm
    (substituteTerm_heq term later).symm earlier).trans ?_
  exact (substituteTerm_heq (substituteTerm term later) earlier).symm

def extension (context : C.Ctx) (type : LocalType C context) : C.Ctx :=
  C.ext context type.decoded

def projection {context : C.Ctx} (type : LocalType C context) :
    C.Sub (extension context type) context := C.wk type.decoded

def genericVariable {context : C.Ctx} (type : LocalType C context) :
    Term C (extension context type) (type.reindex (projection type)) :=
  cast (congrArg (C.Tm (extension context type))
    (type.decoded_reindex (projection type)).symm) (C.vz type.decoded)

theorem genericVariable_heq {context : C.Ctx} (type : LocalType C context) :
    HEq (genericVariable type) (C.vz type.decoded) := cast_heq _ _

def pairing {source target : C.Ctx} (substitution : C.Sub source target)
    (type : LocalType C target) (term : Term C source (type.reindex substitution)) :
    C.Sub source (extension target type) :=
  C.pair substitution type.decoded
    (cast (congrArg (C.Tm source) (type.decoded_reindex substitution)) term)

theorem projection_pairing {source target : C.Ctx} (substitution : C.Sub source target)
    (type : LocalType C target) (term : Term C source (type.reindex substitution)) :
    C.compS (projection type) (pairing substitution type term) = substitution :=
  C.wk_pair _ _ _

theorem genericVariable_pairing {source target : C.Ctx} (substitution : C.Sub source target)
    (type : LocalType C target) (term : Term C source (type.reindex substitution)) :
    HEq (substituteTerm (genericVariable type) (pairing substitution type term)) term := by
  refine (substituteTerm_heq (genericVariable type) (pairing substitution type term)).trans ?_
  refine (TypeOver.tmSub_heq (type.decoded_reindex (projection type))
    (genericVariable_heq type) (pairing substitution type term)).trans ?_
  exact (heq_of_eq (C.vz_pair substitution type.decoded _)).trans
    ((cast_heq _ _).trans (cast_heq _ term))

theorem pairing_eta {source target : C.Ctx} (type : LocalType C target)
    (substitution : C.Sub source (extension target type))
    (term : Term C source (type.reindex (C.compS (projection type) substitution)))
    (readout : HEq term (substituteTerm (genericVariable type) substitution)) :
    pairing (C.compS (projection type) substitution) type term = substitution := by
  have actualReadout :
      HEq (cast (congrArg (C.Tm source)
        (type.decoded_reindex (C.compS (projection type) substitution))) term)
        (C.tmSub (C.vz type.decoded) substitution) :=
    (cast_heq _ term).trans (readout.trans
      ((substituteTerm_heq (genericVariable type) substitution).trans
        (TypeOver.tmSub_heq (type.decoded_reindex (projection type))
          (genericVariable_heq type) substitution)))
  have same :
      cast (congrArg (C.Tm source)
        (type.decoded_reindex (C.compS (projection type) substitution))) term =
      cast (congrArg (C.Tm source)
        (C.tySub_comp type.decoded (projection type) substitution).symm)
        (C.tmSub (C.vz type.decoded) substitution) :=
    eq_of_heq (actualReadout.trans (cast_heq _ _).symm)
  exact (congrArg (C.pair (C.compS (C.wk type.decoded) substitution) type.decoded) same).trans
    (C.pair_eta type.decoded substitution)

/-- The local presentation construction retains the actual source context
category and derives its complete substitution/comprehension structure. -/
def localCwf (C : Cwf.{u, v, w, w'}) : Cwf.{u, v, max u v w, w'} where
  Ctx := C.Ctx
  Sub := C.Sub
  idS := C.idS
  compS := C.compS
  id_comp := C.id_comp
  comp_id := C.comp_id
  comp_assoc := C.comp_assoc
  Ty := LocalType C
  tySub := LocalType.reindex
  tySub_id := LocalType.reindex_id
  tySub_comp := LocalType.reindex_comp
  Tm := Term C
  tmSub := substituteTerm
  tmSub_id term := eq_of_heq ((substituteTerm_id term).trans (cast_heq _ term).symm)
  tmSub_comp term later earlier := eq_of_heq
    ((substituteTerm_comp term later earlier).trans (cast_heq _ _).symm)
  ext := extension
  wk := projection
  vz := genericVariable
  pair := pairing
  wk_pair := projection_pairing
  vz_pair substitution type term := eq_of_heq
    ((genericVariable_pairing substitution type term).trans (cast_heq _ term).symm)
  pair_eta type substitution :=
    pairing_eta type substitution _ (cast_heq _ _)

def localCwfWithTerminal (C : CwfWithTerminal.{u, v, w, w'}) :
    CwfWithTerminal.{u, v, max u v w, w'} where
  toCwf := localCwf C.toCwf
  empty := C.empty
  toEmpty := C.toEmpty
  toEmpty_unique := C.toEmpty_unique

end Mettapedia.TypeTheory.ContextualLocalUniverses
