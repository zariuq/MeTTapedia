import Mettapedia.Languages.Lean.ParserScope4331

/-!
# Live scoped-parser controls for the pinned adapter

These execute Lean's environment operations. They qualify the operational
boundary separately from the kernel proofs over portable frame operations.
-/

namespace Mettapedia.Languages.Lean.ParserScope4331.Controls

open _root_.Lean

def require (condition : Bool) (message : String) : CoreM Unit :=
  unless condition do throwError message

#eval show CoreM Unit from do
  require ParserAdapter4331.hostSupported "unqualified Lean parser release"
  let baseline ← getEnv
  let extension := Parser.parserExtension
  let has := fun env text => (extension.getState env (asyncMode := .local)).tokens.find? text == some text
  let localWord := "gslt_scope_local_probe_4331"
  let globalWord := "gslt_scope_global_probe_4331"
  let scopedWord := "gslt_scope_activation_probe_4331"
  let scopeName := `GsltScope4331
  let syntaxKind := `GsltScope4331.literal
  require (!(has baseline localWord) && !(has baseline globalWord) && !(has baseline scopedWord))
    "scope control token already registered"
  let nested := extension.pushScope baseline
  let localAdded := extension.addLocalEntry nested (.token localWord)
  require (has localAdded localWord && !(has (extension.popScope localAdded) localWord))
    "local token did not restore at scope exit"
  let globalAdded := extension.addEntry nested (.token globalWord)
  require (has (extension.popScope globalAdded) globalWord) "global token vanished at scope exit"
  let registeredToken := extension.addScopedEntry nested scopeName (.token scopedWord)
  let registered := extension.addScopedEntry registeredToken scopeName
    (.parser `term syntaxKind true (Parser.node syntaxKind (Parser.symbol scopedWord)) 1000)
  require (!(has registered scopedWord)) "scoped entry activated before opening its namespace"
  let activated := extension.activateScoped registered scopeName
  require (has activated scopedWord && !(has (extension.popScope activated) scopedWord))
    "scoped activation did not restore"
  let activatedAgain := extension.activateScoped activated scopeName
  for env in [activated, activatedAgain] do
    match Parser.runParserCategory env `term scopedWord with
    | .ok tree => require (tree.getKind == syntaxKind) "activation duplicated or lost the parser alternative"
    | .error error => throwError "activated parser failed: {error}"
  let implicitFrames := extension.setDelimitsLocal (extension.pushScope nested) 1
  let throughImplicit := extension.addLocalEntry implicitFrames (.token localWord)
  require (has (extension.popScope throughImplicit) localWord &&
    !(has (extension.popScope (extension.popScope throughImplicit)) localWord))
    "implicit namespace boundary lost or leaked a local token"
  let stack := fun env => extension.ext.getState (asyncMode := .local) env
  require ((stack nested).newEntries.length == (stack localAdded).newEntries.length)
    "local entry unexpectedly entered persistent export log"
  let missing := extension.activateScoped implicitFrames scopeName
  require ((stack missing).stateStack.head?.map (·.delimitsLocal) == some false)
    "missing scoped bucket changed local delimiter"
  let withEmpty := extension.ext.modifyState (asyncMode := .local) implicitFrames fun state =>
    { state with scopedEntries := { map := state.scopedEntries.map.insert scopeName {} } }
  let emptyActivated := extension.activateScoped withEmpty scopeName
  require ((stack emptyActivated).stateStack.head?.map (·.delimitsLocal) == some true)
    "pinned empty-bucket activation policy changed"
  logInfo "Pinned scoped-parser controls passed: local/global/scoped updates, implicit boundaries, activation, export log"

end Mettapedia.Languages.Lean.ParserScope4331.Controls
