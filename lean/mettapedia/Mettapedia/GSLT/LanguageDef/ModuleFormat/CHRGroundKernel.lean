import Mettapedia.GSLT.LanguageDef.ModuleSource.Loader
import Mettapedia.GSLT.LanguageDef.ModuleSource.ComputedViews
import Mettapedia.OSLF.MeTTaIL.ReferenceStepExecution

/-! The authored ground CHR transaction kernel selects all kept and removed
occurrences without reuse, then restores precisely the kept occurrences.
The body is returned as pending data. Rule matching, guards, refined ordering
and propagation-history authorization are separate controller obligations. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat

namespace CHRAuthoring
open scoped Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
#module_tree "../../../../../../metta/gslt/module/CHRGroundKernel.module" as GroundKernel
end CHRAuthoring

namespace CHRKernel

open Mettapedia.OSLF.MeTTaIL Syntax
open scoped Mettapedia.GSLT.LanguageDef.ModuleSource.ComputedViews

private instance : DecidableEq LanguageDef := fun first second => by
  cases first
  cases second
  exact decidable_of_iff' _ (Iff.of_eq (LanguageDef.mk.injEq _ _ _ _ _ _ _ _ _ _))

def language? : Option LanguageDef := CHRAuthoring.GroundKernel.language.toOption
def language : LanguageDef := module_language_view% language?

theorem language_exact : language? = some language := by decide +kernel

def vector (values : List Pattern) : Pattern := .collection .vec values none
def store (values : List Pattern) : Pattern := .apply "ChrStore" [.collection .hashBag values none]
def heads (values : List Pattern) : Pattern := .apply "ChrHeads" [vector values]
def body (values : List Pattern) : Pattern := .apply "ChrBody" [vector values]
def occurrence (id value : Pattern) : Pattern := .apply "ChrOccurrence" [id, value]
def key (rule : Pattern) (ids : List Pattern) : Pattern := .apply "ChrKey" [rule, vector ids]
def select (wanted contents : List Pattern) : Pattern := .apply "ChrSelect" [heads wanted, store contents]
def restore (kept contents : List Pattern) : Pattern := .apply "ChrRestore" [heads kept, store contents]
def application (firing : Pattern) (kept removed pending contents : List Pattern) : Pattern :=
  .apply "ChrApply" [firing, heads kept, heads removed, body pending, store contents]
def applied (firing : Pattern) (pending contents : List Pattern) : Pattern :=
  .apply "ChrApplied" [firing, body pending, store contents]

def targets (depth : Nat) (source : Pattern) : List Pattern :=
  (ReferenceStep.stepsAt Engine.RelationEnv.empty language depth source).map Prod.snd

#guard language.rewrites.length == 5
#guard language.validate.isEmpty

end CHRKernel
end Mettapedia.GSLT.LanguageDef.ModuleFormat
