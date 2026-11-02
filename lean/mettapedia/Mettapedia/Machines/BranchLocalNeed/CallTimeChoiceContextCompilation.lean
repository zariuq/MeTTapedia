import Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceSource

/-!
# Compilation commutes with source-context plugging

Source contexts select one expression occurrence in the existing source
grammar. Target contexts independently describe one computation hole in the
core grammar. Compilation constructs a target context without receiving the
hole expression. The hole's variable map records the argument bindings and case
binders crossed on its path.

Quotation and suspended argument producers are compilation contexts here.
This is a syntactic compiler law, not a claim that evaluation-equivalent
computations are interchangeable inside captured code.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.BranchLocalNeed.CallTimeChoice.ContextCompilation

mutual
/-- One expression occurrence, including occurrences beneath source binders. -/
inductive Source where
  | hole
  | con (name : Nat) (arguments : Arguments)
  | call (function : Nat) (arguments : Arguments)
  | caseScrutinee (inside : Source) (name arity : Nat) (hit miss : Expr)
  | caseHit (scrutinee : Expr) (name arity : Nat) (inside : Source) (miss : Expr)
  | caseMiss (scrutinee : Expr) (name arity : Nat) (hit : Expr) (inside : Source)
  | chooseLeft (inside : Source) (right : Expr)
  | chooseRight (left : Expr) (inside : Source)
  | emit (event : Nat) (inside : Source)
  | quote (inside : Source)
  | activate (inside : Source)
  | prim (operation : Prim) (arguments : Arguments)
/-- A hole in one source argument, with all earlier arguments retained. -/
inductive Arguments where
  | head (inside : Source) (rest : Args)
  | tail (first : Expr) (inside : Arguments)
end

mutual
def Source.plug : Source → Expr → Expr
  | .hole, expression => expression
  | .con name arguments, expression => .con name (arguments.plug expression)
  | .call function arguments, expression => .call function (arguments.plug expression)
  | .caseScrutinee inside name arity hit miss, expression =>
      .case (inside.plug expression) name arity hit miss
  | .caseHit scrutinee name arity inside miss, expression =>
      .case scrutinee name arity (inside.plug expression) miss
  | .caseMiss scrutinee name arity hit inside, expression =>
      .case scrutinee name arity hit (inside.plug expression)
  | .chooseLeft inside right, expression => .choose (inside.plug expression) right
  | .chooseRight left inside, expression => .choose left (inside.plug expression)
  | .emit event inside, expression => .emit event (inside.plug expression)
  | .quote inside, expression => .quote (inside.plug expression)
  | .activate inside, expression => .activate (inside.plug expression)
  | .prim operation arguments, expression => .prim operation (arguments.plug expression)
def Arguments.plug : Arguments → Expr → Args
  | .head inside rest, expression => .cons (inside.plug expression) rest
  | .tail first inside, expression => .cons first (inside.plug expression)
end

/-- Core contexts are defined directly from core computation constructors.
They contain neither a source context nor a source compilation callback. -/
inductive Target where
  | hole
  | seqFirst (inside : Target) (rest : Comp)
  | seqRest (first : Comp) (inside : Target)
  | needFirst (inside : Target) (body : Comp)
  | needBody (producer : Comp) (inside : Target)
  | delayFirst (inside : Target) (body : Comp)
  | delayBody (producer : Comp) (inside : Target)
  | caseHit (value : VExp) (name arity : Nat) (inside : Target) (miss : Comp)
  | caseMiss (value : VExp) (name arity : Nat) (hit : Comp) (inside : Target)
  | chooseLeft (inside : Target) (right : Comp)
  | chooseRight (left : Comp) (inside : Target)
  | emit (event : Nat) (inside : Target)
  | quote (inside : Target)
  deriving DecidableEq, Repr

def Target.plug : Target → Comp → Comp
  | .hole, code => code
  | .seqFirst inside rest, code => .seq (inside.plug code) rest
  | .seqRest first inside, code => .seq first (inside.plug code)
  | .needFirst inside body, code => .need (inside.plug code) body
  | .needBody producer inside, code => .need producer (inside.plug code)
  | .delayFirst inside body, code => .delay (inside.plug code) body
  | .delayBody producer inside, code => .delay producer (inside.plug code)
  | .caseHit value name arity inside miss, code =>
      .caseCon value name arity (inside.plug code) miss
  | .caseMiss value name arity hit inside, code =>
      .caseCon value name arity hit (inside.plug code)
  | .chooseLeft inside right, code => .choose (inside.plug code) right
  | .chooseRight left inside, code => .choose left (inside.plug code)
  | .emit event inside, code => .emit event (inside.plug code)
  | .quote inside, code => .quote (inside.plug code)

def Target.bindFirst : Profile → Target → Comp → Target
  | .value => .seqFirst
  | .need => .needFirst
  | .name => .delayFirst

def Target.bindBody : Profile → Comp → Target → Target
  | .value => .seqRest
  | .need => .needBody
  | .name => .delayBody

@[simp] theorem Target.plug_bindFirst (profile : Profile) (inside : Target)
    (body code : Comp) :
    (Target.bindFirst profile inside body).plug code = bindFor profile (inside.plug code) body := by
  cases profile <;> rfl

@[simp] theorem Target.plug_bindBody (profile : Profile) (producer : Comp)
    (inside : Target) (code : Comp) :
    (Target.bindBody profile producer inside).plug code = bindFor profile producer (inside.plug code) := by
  cases profile <;> rfl

mutual
/-- Variable interpretation at the selected expression occurrence. -/
def Source.holeRenaming (rho : Nat → Nat) : Source → Nat → Nat
  | .hole => rho
  | .con _ arguments | .call _ arguments | .prim _ arguments =>
      arguments.holeRenaming rho 0
  | .caseScrutinee inside _ _ _ _ => inside.holeRenaming rho
  | .caseHit _ _ arity inside _ => inside.holeRenaming (liftRen (arity + 1) rho)
  | .caseMiss _ _ _ _ inside => inside.holeRenaming (liftRen 1 rho)
  | .chooseLeft inside _ | .chooseRight _ inside | .emit _ inside |
      .quote inside | .activate inside => inside.holeRenaming rho
def Arguments.holeRenaming (rho : Nat → Nat) (done : Nat) : Arguments → Nat → Nat
  | .head inside _ => inside.holeRenaming (fun index => rho index + done)
  | .tail _ inside => inside.holeRenaming rho (done + 1)
end

mutual
/-- Compile the source context independently of the expression put in its
hole. Only the fixed surrounding source expressions are compiled here. -/
def Source.compile (profile : Profile) (rho : Nat → Nat) : Source → Target
  | .hole => .hole
  | .con name arguments => arguments.compile profile rho 0
      (fun count => .ret (spineOf (.sym name) (varsDesc count)))
  | .call function arguments => arguments.compile profile rho 0
      (fun count => .call (function + 1) (varsDesc count))
  | .caseScrutinee inside name arity hit miss =>
      .seqFirst (inside.compile profile rho)
        (.caseCon (.var 0) name arity
          (hit.toCore profile (liftRen (arity + 1) rho))
          (miss.toCore profile (liftRen 1 rho)))
  | .caseHit scrutinee name arity inside miss =>
      .seqRest (scrutinee.toCore profile rho)
        (.caseHit (.var 0) name arity (inside.compile profile (liftRen (arity + 1) rho))
          (miss.toCore profile (liftRen 1 rho)))
  | .caseMiss scrutinee name arity hit inside =>
      .seqRest (scrutinee.toCore profile rho)
        (.caseMiss (.var 0) name arity (hit.toCore profile (liftRen (arity + 1) rho))
          (inside.compile profile (liftRen 1 rho)))
  | .chooseLeft inside right =>
      .chooseLeft (inside.compile profile rho) (right.toCore profile rho)
  | .chooseRight left inside =>
      .chooseRight (left.toCore profile rho) (inside.compile profile rho)
  | .emit event inside => .emit event (inside.compile profile rho)
  | .quote inside => .quote (inside.compile profile rho)
  | .activate inside => .seqFirst (inside.compile profile rho)
      (.seq (.force (.var 0)) (.run (.var 0)))
  | .prim operation arguments => arguments.compileStrict profile rho 0
      (fun count => .prim operation (varsDesc count))
def Arguments.compile (profile : Profile) (rho : Nat → Nat) (done : Nat) :
    Arguments → (Nat → Comp) → Target
  | .head inside rest, continuation =>
      .bindFirst profile (inside.compile profile (fun index => rho index + done))
        (rest.toCore profile rho (done + 1) continuation)
  | .tail first inside, continuation =>
      .bindBody profile (first.toCore profile (fun index => rho index + done))
        (inside.compile profile rho (done + 1) continuation)
def Arguments.compileStrict (profile : Profile) (rho : Nat → Nat) (done : Nat) :
    Arguments → (Nat → Comp) → Target
  | .head inside rest, continuation =>
      .seqFirst (.seqFirst (inside.compile profile (fun index => rho index + done))
        (.call normHead [.var 0]))
        (rest.toCoreStrict profile rho (done + 1) continuation)
  | .tail first inside, continuation =>
      .seqRest (normalized (first.toCore profile (fun index => rho index + done)))
        (inside.compileStrict profile rho (done + 1) continuation)
end

mutual
/-- Exact syntax compilation at the selected source occurrence, including
code stored by quotation and the argument wrappers introduced by the profile. -/
theorem Source.compile_plug (profile : Profile) (rho : Nat → Nat) :
    ∀ (context : Source) (expression : Expr),
      (context.plug expression).toCore profile rho =
        (context.compile profile rho).plug
          (expression.toCore profile (context.holeRenaming rho))
  | .hole, _ => rfl
  | .con name arguments, expression =>
      Arguments.compile_plug profile rho 0 _ arguments expression
  | .call function arguments, expression =>
      Arguments.compile_plug profile rho 0 _ arguments expression
  | .caseScrutinee inside name arity hit miss, expression => by
      simp only [Source.plug, Expr.toCore, Source.compile, Target.plug,
        Source.holeRenaming, Source.compile_plug profile rho inside expression]
  | .caseHit scrutinee name arity inside miss, expression => by
      simp only [Source.plug, Expr.toCore, Source.compile, Target.plug,
        Source.holeRenaming,
        Source.compile_plug profile (liftRen (arity + 1) rho) inside expression]
  | .caseMiss scrutinee name arity hit inside, expression => by
      simp only [Source.plug, Expr.toCore, Source.compile, Target.plug,
        Source.holeRenaming, Source.compile_plug profile (liftRen 1 rho) inside expression]
  | .chooseLeft inside right, expression => by
      simp only [Source.plug, Expr.toCore, Source.compile, Target.plug,
        Source.holeRenaming, Source.compile_plug profile rho inside expression]
  | .chooseRight left inside, expression => by
      simp only [Source.plug, Expr.toCore, Source.compile, Target.plug,
        Source.holeRenaming, Source.compile_plug profile rho inside expression]
  | .emit event inside, expression => by
      simp only [Source.plug, Expr.toCore, Source.compile, Target.plug,
        Source.holeRenaming, Source.compile_plug profile rho inside expression]
  | .quote inside, expression => by
      simp only [Source.plug, Expr.toCore, Source.compile, Target.plug,
        Source.holeRenaming, Source.compile_plug profile rho inside expression]
  | .activate inside, expression => by
      simp only [Source.plug, Expr.toCore, Source.compile, Target.plug, strictRun,
        Source.holeRenaming, Source.compile_plug profile rho inside expression]
  | .prim operation arguments, expression =>
      Arguments.compileStrict_plug profile rho 0 _ arguments expression
theorem Arguments.compile_plug (profile : Profile) (rho : Nat → Nat) (done : Nat)
    (continuation : Nat → Comp) : ∀ (context : Arguments) (expression : Expr),
      (context.plug expression).toCore profile rho done continuation =
        (context.compile profile rho done continuation).plug
          (expression.toCore profile (context.holeRenaming rho done))
  | .head inside rest, expression => by
      simp only [Arguments.plug, Args.toCore, Arguments.compile, Target.plug_bindFirst,
        Arguments.holeRenaming,
        Source.compile_plug profile (fun index => rho index + done) inside expression]
  | .tail first inside, expression => by
      simp only [Arguments.plug, Args.toCore, Arguments.compile, Target.plug_bindBody,
        Arguments.holeRenaming,
        Arguments.compile_plug profile rho (done + 1) continuation inside expression]
theorem Arguments.compileStrict_plug (profile : Profile) (rho : Nat → Nat) (done : Nat)
    (continuation : Nat → Comp) : ∀ (context : Arguments) (expression : Expr),
      (context.plug expression).toCoreStrict profile rho done continuation =
        (context.compileStrict profile rho done continuation).plug
          (expression.toCore profile (context.holeRenaming rho done))
  | .head inside rest, expression => by
      simp only [Arguments.plug, Args.toCoreStrict, Arguments.compileStrict, Target.plug,
        Arguments.holeRenaming, normalized,
        Source.compile_plug profile (fun index => rho index + done) inside expression]
  | .tail first inside, expression => by
      simp only [Arguments.plug, Args.toCoreStrict, Arguments.compileStrict, Target.plug,
        Arguments.holeRenaming,
        Arguments.compileStrict_plug profile rho (done + 1) continuation inside expression]
end

end Mettapedia.Machines.BranchLocalNeed.CallTimeChoice.ContextCompilation
