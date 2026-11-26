import Lean

/-!
# Lean's proofs written back from MeTTa, judged by Lean's kernel

The transport export (`scripts/ExportLeanTransport.lean`) gives Lean's theorems, their statements
and proof terms, as MeTTa data. MeTTa writes them back as Lean source (`readback.metta`), possibly
after transforming them, and a generated file states each theorem with these commands:

* `back_theorem «c» [levels] : STATEMENT := PROOF` is *rebuilt* when the kernel accepts the
  written proof as a proof of the written statement, and accepts that as a proof of the original
  theorem's statement. Otherwise the original is borrowed under the same name (`Back.«c»`), and
  the audit flags what rests on it.
* `back_missing «c» [levels] : STATEMENT` borrows a theorem whose proof the data lacks.
* `back_lemma «m» [levels] := PROOF` is a lemma MeTTa found: Lean elaborates the proof without a
  statement, infers the statement, makes each universe the proof leaves open a level parameter
  (after the ones named), and the kernel checks it.
* `back_accept` and `back_refuse` judge a twin of a theorem (under `Probe`), which must be
  accepted and refused respectively: the controls.
* `back_kernel_control` checks that the kernel itself refuses an ill-typed proof.
* `back_audit` lists, for each rebuilt name, what it rests on that was not rebuilt: an original
  theorem, a definition that is a proof, an axiom beyond Lean's three. A name that rests on
  nothing is closed; a placeholder proof rests on an axiom, so it never is.
* `back_independent_audit`, in a file that imports the judged file's compiled module, walks the
  same from the module alone.

An erased proof the reading wrote as `_` is filled after elaboration only by a hypothesis in scope
or by reflexivity: by proof irrelevance any proof of its proposition is that one, and no theorem
is searched for.
-/

open Lean Meta Elab Command Term

namespace Mettapedia.Languages.Lean.Transport.Readback

/-- A name as the export prints it: components between dots, numeric ones as numbers. -/
def exportedName (s : String) : Name :=
  (s.splitOn ".").foldl (init := .anonymous) fun n part =>
    match part.toNat? with
    | some k => .num n k
    | none => .str n part

def keyOf (c : Ident) : String :=
  match c.getId with
  | .str .anonymous s => s
  | n => n.toString

def original (key : String) : CoreM ConstantInfo := do
  let env ← getEnv
  if let some i := env.find? (exportedName key) then return i
  let found := env.constants.fold (init := none) fun acc n i =>
    if acc.isNone && n.toString == key then some i else acc
  match found with
  | some i => return i
  | none => throwError "no theorem {key}"

/-- The kernel's verdict on a theorem. -/
def kernelAdd (env : Environment) (val : TheoremVal) : Except String Environment :=
  match env.addDeclCore 0 10000 (.thmDecl val) none with
  | .ok env' => .ok env'
  | .error _ => .error "kernel"

/-- A message on one line. -/
def oneLine (s : String) : String :=
  " ¦ ".intercalate ((s.splitOn "\n").map fun l => l.trimAscii.toString)

/-- The proofs the reading erased, where Lean's unifier left them open: by proof irrelevance any
proof of the proposition is that one, so a hypothesis in scope or reflexivity.  No theorem is
searched for, and nothing is filled before elaboration has fixed the proposition. -/
def fillErased (e : Expr) : MetaM Expr := do
  let mut e ← instantiateMVars e
  for _ in [0:4] do
    unless e.hasExprMVar do break
    for m in (← getMVars e) do
      if (← m.isAssigned) || (← m.isDelayedAssigned) then continue
      m.withContext do
        let ty ← instantiateMVars (← m.getType)
        unless ty.hasExprMVar do
          if ← Meta.isProp ty then
            withReducible do
              if ← m.assumptionCore then return
              if let some (_, a, b) := ty.eq? then
                if ← Meta.isDefEq a b then m.assign (← mkEqRefl a)
    e ← instantiateMVars e
  return e

/-- `x` run with a log of its own: its result, and the first error it logged rather than threw (an
application postponed and never elaborated, say). The log is left as it was. -/
def isolatingLog {α : Type} (x : TermElabM α) : TermElabM (α × Option String) := do
  let saved ← Core.getMessageLog
  Core.setMessageLog {}
  try
    let a ← x
    let logged ← Core.getMessageLog
    match logged.toList.find? (·.severity == .error) with
    | some m => return (a, some (oneLine (← m.data.toString)))
    | none => return (a, none)
  finally
    Core.setMessageLog saved

/-- The stage at which a written theorem is refused, or the environment that holds it. -/
def judge (ns : Name) (key : String) (levels : List Name) (orig : ConstantInfo) (T p : Syntax) :
    TermElabM (Except String Environment) := do
  let (r, logged) ← isolatingLog (α := Except String Environment) <| tryCatchRuntimeEx
    (withLevelNames levels <| withoutErrToSorry do
      let type ← try
        let type ← withSynthesize (elabType T)
        fillErased type
      catch e => return .error s!"statement: {oneLine (← e.toMessageData.toString)}"
      if type.hasExprMVar then return .error "statement: an erased part is not determined"
      if type.hasLevelMVar then return .error "statement: a level is not determined"
      let elabValue : TermElabM Expr := do
        fillErased (← withSynthesize (elabTermEnsuringType p type))
      -- The kernel has no irreducible definitions: what the elaborator refuses at its default
      -- transparency is elaborated once more at full, and the kernel judges either the same.
      let kernelLike {α : Type} (x : TermElabM α) : TermElabM α :=
        withOptions (·.setBool `smartUnfolding false) <| withTransparency .all x
      let value ← try
        match ← observing? elabValue with
        | some value => pure value
        | none =>
          match ← observing? (kernelLike elabValue) with
          | some value => pure value
          | none =>
            -- Conversion itself left to the kernel: the proof elaborated by its own types.
            match ← observing? (kernelLike do fillErased (← withSynthesize (elabTerm p none))) with
            | some value => pure value
            | none => elabValue
      catch e => return .error s!"proof: {oneLine (← e.toMessageData.toString)}"
      if value.hasExprMVar then return .error "proof: an erased part is not determined"
      if value.hasLevelMVar then return .error "proof: a level is not determined"
      let name := Name.str ns key
      match kernelAdd (← getEnv) { name, levelParams := levels, type, value } with
      | .error _ => return .error "kernel: not a proof of the written statement"
      | .ok env =>
        unless levels.length == orig.levelParams.length do return .error "kernel: other level parameters"
        match kernelAdd env
            { name := Name.str (ns ++ `same) key, levelParams := orig.levelParams, type := orig.type,
              value := Lean.mkConst name (orig.levelParams.map mkLevelParam) } with
        | .error _ => return .error "kernel: another statement than the original's"
        | .ok _ => return .ok env)
    (fun e => return .error s!"resources: {oneLine (← e.toMessageData.toString)}")
  match r, logged with
  | .ok _, some why => return .error s!"proof: {why}"
  | r, _ => return r

/-- The original under the rebuilt name, with the written statement where Lean takes it. -/
def borrow (key : String) (levels : List Name) (orig : ConstantInfo) (T : Syntax) : TermElabM Unit :=
  withLevelNames levels do
    let origType := orig.type.instantiateLevelParams orig.levelParams (levels.map mkLevelParam)
    let written : TermElabM Expr := withoutErrToSorry do
      let t ← withSynthesize (elabType T)
      let t ← fillErased t
      if t.hasExprMVar || t.hasLevelMVar then return origType else return t
    let (type, logged) ← isolatingLog (try written catch _ => pure origType)
    let type := if logged.isSome then origType else type
    let value := Lean.mkConst orig.name (levels.map mkLevelParam)
    let val (t : Expr) : TheoremVal :=
      { name := Name.str `Back key, levelParams := levels, type := t, value }
    match kernelAdd (← getEnv) (val type) with
    | .ok env => setEnv env
    | .error _ =>
      match kernelAdd (← getEnv) (val origType) with
      | .ok env => setEnv env
      | .error _ => throwError "cannot borrow {key}"

/-- A lemma without a statement: its proof elaborated alone, the statement inferred, the universes
it leaves open made level parameters after the named ones; the statement, or why there is none. -/
def lemma (key : String) (levels : List Name) (p : Syntax) : TermElabM (Except String Expr) := do
  let (built, logged) ← isolatingLog (α := Except String (Expr × Expr × List Name)) <| tryCatchRuntimeEx
    (withLevelNames levels <| withoutErrToSorry do
      let value ← try
        let v ← withSynthesize (elabTerm p none)
        fillErased v
      catch e => return .error s!"elaboration: {oneLine (← e.toMessageData.toString)}"
      if value.hasExprMVar then return .error "a parameter's type is not determined"
      let value ← levelMVarToParam (← instantiateMVars value)
      let type ← Core.betaReduce (← instantiateMVars (← inferType value))
      if value.hasLevelMVar || type.hasLevelMVar then return .error "a level is not determined"
      unless ← Meta.isProp type do return .error "not a proof"
      let found := (collectLevelParams (collectLevelParams {} type) value).params
      let extra := found.toList.filter (!levels.contains ·)
      return .ok (type, value, levels ++ extra))
    (fun e => return .error s!"resources: {oneLine (← e.toMessageData.toString)}")
  let built : Except String (Expr × Expr × List Name) := match built, logged with
    | .ok _, some why => .error s!"elaboration: {why}"
    | b, _ => b
  match built with
  | .error why => return .error why
  | .ok (type, value, levels) =>
    match kernelAdd (← getEnv) { name := Name.str `Back key, levelParams := levels, type, value } with
    | .ok env => setEnv env; return .ok type
    | .error _ => return .error "kernel"

/-- A structure's field as the kernel's own projection, not through the projection's constant. -/
syntax "proj% " ident num "(" term ")" : term

elab_rules : term
  | `(proj% $S:ident $i:num ($x)) => do
      let some s := ((← getEnv).find? S.getId).map (·.name) | throwError "no structure {S.getId}"
      let e ← elabTerm x none
      synthesizeSyntheticMVarsNoPostponing
      return .proj s i.getNat (← instantiateMVars e)

syntax "back_lemma " ident " [" ident,* "]" " := " term : command
syntax "back_theorem " ident " [" ident,* "]" " : " term " := " term : command
syntax "back_missing " ident " [" ident,* "]" " : " term : command
syntax "back_accept " ident " [" ident,* "]" " : " term " := " term : command
syntax "back_refuse " ident " [" ident,* "]" " : " term " := " term : command

elab_rules : command
  | `(back_theorem $c:ident [$ls,*] : $T := $p) => liftTermElabM do
      let key := keyOf c
      let levels := ls.getElems.toList.map (·.getId)
      let orig ← original key
      match ← judge `Back key levels orig T p with
      | .ok env => setEnv env; logInfo m!"REBUILT {key}"
      | .error why => borrow key levels orig T; logInfo m!"BORROWED {key} | {why}"
  | `(back_lemma $c:ident [$ls,*] := $p) => liftTermElabM do
      let key := keyOf c
      match ← lemma key (ls.getElems.toList.map (·.getId)) p with
      | .ok type => logInfo m!"LEMMA {key} : {oneLine (toString (← ppExpr type))}"
      | .error why => logInfo m!"LEMMA-REFUSED {key} | {why}"
  | `(back_missing $c:ident [$ls,*] : $T) => liftTermElabM do
      let key := keyOf c
      borrow key (ls.getElems.toList.map (·.getId)) (← original key) T
      logInfo m!"BORROWED {key} | no proof in the reading"
  | `(back_accept $c:ident [$ls,*] : $T := $p) => liftTermElabM do
      let key := keyOf c
      match ← judge `Probe key (ls.getElems.toList.map (·.getId)) (← original key) T p with
      | .ok _ => logInfo m!"TWIN-OK {key}"
      | .error why => throwError "TWIN-REFUSED {key} | {why}"
  | `(back_refuse $c:ident [$ls,*] : $T := $p) => liftTermElabM do
      let key := keyOf c
      match ← judge `Probe key (ls.getElems.toList.map (·.getId)) (← original key) T p with
      | .ok _ => throwError "CONTROL-ACCEPTED {key}"
      | .error why => logInfo m!"CONTROL-OK {key} | {why}"

/-- What a rebuilt theorem rests on that was not rebuilt: an original theorem, a definition that
is a proof, an axiom beyond Lean's three. -/
partial def foreign (c : Name) : StateT (NameMap (Array Name)) MetaM (Array Name) := do
  if let some r := (← get).find? c then return r
  let env ← getEnv
  let some info := env.find? c | throwError "lost {c}"
  let mut out : Array Name := #[]
  let some value := info.value? (allowOpaque := true) | throwError "{c} has no value"
  for d in info.type.getUsedConstants ++ value.getUsedConstants do
    let found ←
      if (`Back).isPrefixOf d then foreign d
      else match env.find? d with
        | some (.thmInfo _) => pure #[d]
        | some (.axiomInfo _) =>
          pure (if [``propext, ``Classical.choice, ``Quot.sound].contains d then #[] else #[d])
        | some i@(.defnInfo _) | some i@(.opaqueInfo _) => do
          let isProofDef ← (forallTelescopeReducing i.type fun _ body => Meta.isProp body : MetaM Bool)
          pure (if isProofDef then #[d] else #[])
        | _ => pure #[]
    for x in found do unless out.contains x do out := out.push x
  modify (·.insert c out)
  return out

/-- The rebuilt names: `Back.«c»`. -/
def rebuiltNames (env : Environment) : Array Name :=
  env.constants.fold (init := #[]) fun acc n _ =>
    match n with
    | .str (.str .anonymous "Back") _ => acc.push n
    | _ => acc

/-- The originals rebuilt here, by the key their rebuilt name carries. -/
def twinKeys (env : Environment) : Std.HashSet String :=
  (rebuiltNames env).foldl (init := {}) fun s n =>
    match n with
    | .str _ key => s.insert key
    | _ => s

/-- What a rebuilt name may not rest on: an original that has a rebuilt twin, or an axiom beyond
Lean's three.  An original without a twin lies outside the export, where a scoped export stops. -/
def mustNotRest (env : Environment) (twins : Std.HashSet String) (d : Name) : Bool :=
  twins.contains d.toString || (match env.find? d with | some (.axiomInfo _) => true | _ => false)

syntax "back_audit" : command

elab_rules : command
  | `(back_audit) => liftTermElabM do
      let env ← getEnv
      let twins := twinKeys env
      let mut memo : NameMap (Array Name) := {}
      let mut lines : Array String := #[]
      for n in rebuiltNames env do
        let (found, memo') ← (foreign n).run memo
        memo := memo'
        let .str _ key := n | continue
        let (rests, leaves) := found.partition (mustNotRest env twins)
        lines := lines.push <|
          if !rests.isEmpty then s!"RESTS {key} | {rests.size}: {rests.toList.take 4}"
          else if leaves.isEmpty then s!"CLOSED {key}"
          else s!"LEAVES {key} | {leaves.size}: {leaves.toList.take 4}"
      for l in lines do logInfo m!"{l}"

syntax "back_kernel_control" : command

elab_rules : command
  | `(back_kernel_control) => liftTermElabM do
      let env ← getEnv
      let probe (type : Expr) : TheoremVal :=
        { name := `Probe.kernel, levelParams := [], type, value := Lean.mkConst ``True.intro }
      match kernelAdd env (probe (Lean.mkConst ``True)) with
      | .ok _ => logInfo "TWIN-OK kernel"
      | .error _ => throwError "TWIN-REFUSED kernel"
      match kernelAdd env (probe (Lean.mkConst ``False)) with
      | .ok _ => throwError "CONTROL-ACCEPTED kernel"
      | .error _ => logInfo "CONTROL-OK kernel | an ill-typed proof past the elaborator"

/-- Every constant the rebuilt names reach through rebuilt names, walked afresh. -/
partial def reach (env : Environment) (seen : NameSet) : List Name → NameSet
  | [] => seen
  | n :: rest =>
    if seen.contains n then reach env seen rest else
      let more := if (`Back).isPrefixOf n then
          match env.find? n with
          | some i => i.type.getUsedConstants.toList ++
              ((i.value? (allowOpaque := true)).map (·.getUsedConstants.toList)).getD []
          | none => []
        else []
      reach env (seen.insert n) (more ++ rest)

syntax "back_independent_audit" : command

elab_rules : command
  | `(back_independent_audit) => liftTermElabM do
      let env ← getEnv
      let mine := rebuiltNames env
      let twins := twinKeys env
      let mut originals : Array Name := #[]
      let mut leaves : Array Name := #[]
      for n in (reach env {} mine.toList).toList do
        if (`Back).isPrefixOf n then continue
        let some i := env.find? n | throwError "unknown {n}"
        let original ← match i with
          | .thmInfo _ => pure true
          | .defnInfo _ | .opaqueInfo _ => Meta.isProp i.type
          | .axiomInfo _ => pure !([``propext, ``Classical.choice, ``Quot.sound].contains n)
          | _ => pure false
        if original then
          if mustNotRest env twins n then originals := originals.push n else leaves := leaves.push n
      let mut axs : NameSet := {}
      let mut proved : Nat := 0
      for n in mine do
        if let some (.thmInfo _) := env.find? n then proved := proved + 1
        for a in (← collectAxioms n) do axs := axs.insert a
      logInfo m!"INDEPENDENT theorems={proved} originals-cited={originals.size} {originals.toList.take 8} leaves={leaves.size} axioms={axs.toList}"

end Mettapedia.Languages.Lean.Transport.Readback
