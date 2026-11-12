import Mettapedia.Languages.MeTTa.PeTTa.StreamingPrefixes
import Mettapedia.Data.FreshString

/-!
# Result terms separated from producing goals

An output term is available to unification before its producing goals run.
Plans lower to the existing quote, literal unification and streaming control
forms. Private procedure calls use an extra output argument and return one
unit answer per source answer. This is a compiler representation, not another
primitive evaluator or a selected Prime syntax.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.OutputPlan

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst atomFreeVars)

def call (head : String) (arguments : List Atom) : Atom := .expression (.symbol head :: arguments)
def hold (term : Atom) : Atom := call "quote" [term]
def unit : Atom := Effects.boolean true

/-- Both terms are literal here; a data constructor named cons does not
silently become the equation-head list view. -/
def equate (left right continuation : Atom) : Atom :=
  call "let" [hold left,hold right,continuation]

def sequence (first second : Atom) : Atom :=
  if first == unit then second else call "let" [hold unit,first,second]

def ordered : List Atom → Atom
  | [] => unit
  | first :: rest => sequence first (ordered rest)

structure Plan where
  goals : Atom
  output : Atom

def Plan.value (value : Atom) : Plan := ⟨unit,value⟩

def Plan.execute (plan : Plan) : Atom := sequence plan.goals (hold plan.output)

def Plan.data (head : Atom) (children : List Plan) : Plan :=
  ⟨ordered (children.map Plan.goals),.expression (head :: children.map Plan.output)⟩

def Plan.bind (pattern initializer body : Plan) : Plan :=
  ⟨equate pattern.output initializer.output
      (sequence pattern.goals (sequence initializer.goals body.goals)),body.output⟩

/-- A compiled procedure receives its result as data. Its body first checks
the exposed result term, then performs its goals. The formal itself is a
variable, avoiding list-view interpretation of the output term in the head. -/
def procedure (target : String) (arguments : List Atom) (outputName : String) (body : Plan) :
    SpaceSemantics.Equation :=
  ⟨target,arguments ++ [.var outputName],equate body.output (.var outputName) body.goals⟩

def invoke (target : String) (arguments : List Atom) (output : Atom) : Atom :=
  call target ((arguments ++ [output]).map hold)

inductive NativeMode where
  | trueBeforeEffect
  | forward

/-- The fixed-result classification is derived from the source ABI: its
literal true head is checked after arguments and before the effect. Other
native-mode correspondences are not implied by this lowering. -/
def nativeArguments (registry : SpaceSemantics.Program) (head : String) (arguments : List Atom) : List Atom :=
  arguments.zipIdx.map fun (argument,index) =>
    if Eval.argumentIsRaw registry head index then argument else hold argument

def native (registry : SpaceSemantics.Program) (mode : NativeMode)
    (head : String) (arguments : List Atom) (output : Atom) : Atom :=
  match mode with
  | .trueBeforeEffect => equate output unit (call head (nativeArguments registry head arguments))
  | .forward => call "let" [hold output,call head (nativeArguments registry head arguments),unit]

structure Supply where
  used : Finset String
  aliases : Subst := []

inductive BranchPolicy where
  | swiAliases
  | runtimeConstraints
  deriving DecidableEq, BEq

def Supply.start (terms : List Atom) : Supply :=
  ⟨(terms.flatMap atomFreeVars).toFinset,[]⟩

def Supply.fresh (supply : Supply) : Supply × Atom :=
  let name := Mettapedia.FreshString.fresh supply.used
  (⟨insert name supply.used,supply.aliases⟩,.var name)

def Supply.normalize (supply : Supply) (term : Atom) : Atom := Unifying.resolve supply.aliases term

def Supply.plan (supply : Supply) (plan : Plan) : Plan :=
  ⟨supply.normalize plan.goals,supply.normalize plan.output⟩

/-- The source branch builder aliases a nontrivial goal's variable output
with its shared output during compilation. Literal outputs instead get a
runtime equation before their goals. Pure values always use that equation. -/
def branch (supply : Supply) (plan : Plan) (output : Atom)
    (policy : BranchPolicy := .swiAliases) : Option (Supply × Atom) :=
  if policy == .runtimeConstraints then some (supply,equate plan.output output plan.goals)
  else if plan.goals == unit then some (supply,equate plan.output output unit)
  else
    match supply.normalize plan.output with
    | .var name =>
        match Unifying.unify supply.aliases (.var name) output with
        | .ok aliases => some (⟨supply.used,aliases⟩,plan.goals)
        | .clash | .exhausted => none
    | _ => some (supply,equate plan.output output plan.goals)

theorem fresh_name_avoids_support (supply : Supply) :
    Mettapedia.FreshString.fresh supply.used ∉ supply.used :=
  Mettapedia.FreshString.fresh_not_mem supply.used

theorem fresh_support_grows (supply : Supply) : supply.used ⊆ supply.fresh.1.used :=
  Finset.subset_insert _ _

theorem fresh_keeps_aliases (supply : Supply) : supply.fresh.1.aliases = supply.aliases := rfl

theorem start_contains_source_variables (terms : List Atom) (term : Atom) (present : term ∈ terms)
    (name : String) (occurs : name ∈ atomFreeVars term) : name ∈ (Supply.start terms).used := by
  simp only [Supply.start,List.mem_toFinset,List.mem_flatMap]
  exact ⟨term,present,occurs⟩

theorem native_arguments_length (registry : SpaceSemantics.Program) (head : String) (arguments : List Atom) :
    (nativeArguments registry head arguments).length = arguments.length := by
  simp [nativeArguments]

/-- The payload is already held by the native Atom domain. Adding another
quote would publish the quote syntax instead of the source atom. -/
theorem add_atom_argument_roles (registry : SpaceSemantics.Program) (location payload : Atom) :
    nativeArguments registry "add-atom" [location,payload] = [hold location,payload] := by
  simp [nativeArguments,Eval.argumentIsRaw,StdLib.known,StdLib.rawArgument]

theorem remove_atom_argument_roles (registry : SpaceSemantics.Program) (location pattern : Atom) :
    nativeArguments registry "remove-atom" [location,pattern] = [hold location,pattern] := by
  simp [nativeArguments,Eval.argumentIsRaw,StdLib.known,StdLib.rawArgument]

end Mettapedia.Languages.MeTTa.PeTTa.OutputPlan
