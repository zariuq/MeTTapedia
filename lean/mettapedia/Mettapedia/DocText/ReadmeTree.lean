/-
# Shared Document Tree for GF-Generated READMEs

Pure structural tree + Markdown renderer.
No GF dependency — GF sentences arrive as pre-rendered strings.
-/

namespace Mettapedia.DocText.ReadmeTree

/-- Typed syntax-expression AST for technical symbol patterns. -/
inductive SynExpr where
  | ident (name : String)
  | quoted (text : String)
  | call (fn : String) (args : List SynExpr)
  | seq (items : List SynExpr) (sep : String)
  | infix (lhs : SynExpr) (op : String) (rhs : SynExpr)
  deriving Repr, BEq

partial def renderSynExpr : SynExpr → String
  | .ident n => n
  | .quoted t => "\"" ++ t ++ "\""
  | .call fn args =>
      fn ++ "(" ++ String.intercalate "," (args.map renderSynExpr) ++ ")"
  | .seq items sep =>
      String.intercalate sep (items.map renderSynExpr)
  | .infix lhs op rhs =>
      renderSynExpr lhs ++ " " ++ op ++ " " ++ renderSynExpr rhs

partial def synExprWellFormed : SynExpr → Bool
  | .ident n => n != ""
  | .quoted t => t != ""
  | .call fn args => fn != "" && !args.isEmpty && args.all synExprWellFormed
  | .seq items sep => !items.isEmpty && sep != "" && items.all synExprWellFormed
  | .infix lhs op rhs => op != "" && synExprWellFormed lhs && synExprWellFormed rhs

theorem synExpr_empty_quoted_forbidden :
    synExprWellFormed (.quoted "") = false := by
  native_decide

/-- Typed API item for documentation lists. -/
structure ApiItem where
  path : String
  members : List String := []
  note : Option String := none
  deriving Repr, BEq, DecidableEq

/-- Typed syntax-pattern item for documentation lists. -/
structure SyntaxItem where
  label : String
  pattern : SynExpr
  deriving Repr, BEq

/-- Typed path item for path-only bullet lists. -/
structure PathItem where
  path : String
  deriving Repr, BEq, DecidableEq

/-- Claim-backed bullet item (text must come from claim renderer upstream). -/
structure ClaimBullet where
  text : String
  deriving Repr, BEq, DecidableEq

/-- Typed theorem item with structured statement payload. -/
structure TheoremItem where
  name : String
  statement : SynExpr
  file : String
  deriving Repr, BEq

/-- A block in a README document tree. -/
inductive ReadmeBlock where
  | heading (level : Nat) (text : String)
  | paragraph (sentences : List String)
  | bulletList (items : List ReadmeBlock)
  | claimBullets (items : List ClaimBullet)
  | theoremItems (items : List TheoremItem)
  | apiItems (items : List ApiItem)
  | syntaxItems (items : List SyntaxItem)
  | pathItems (items : List PathItem)
  | bulletItem (text : String)
  | codeBlock (lang : String) (code : String)
  | fileRef (path : String) (desc : String)
  | apiList (items : List (String × String))
  deriving Repr

private def headingPrefix (level : Nat) : String :=
  String.ofList (List.replicate level '#') ++ " "

private def ensurePeriod (s : String) : String :=
  if s.endsWith "." then s else s ++ "."

private def renderApiItem (item : ApiItem) : String :=
  let header := "- `" ++ item.path ++ "`"
  let memberLines := item.members.map (fun m => "  - `" ++ m ++ "`")
  let noteLines := match item.note with
    | some n => ["  - " ++ n]
    | none => []
  String.intercalate "\n" ([header] ++ memberLines ++ noteLines)

private def renderSyntaxItem (item : SyntaxItem) : String :=
  "- " ++ item.label ++ ": `" ++ renderSynExpr item.pattern ++ "`"

private def renderPathItem (item : PathItem) : String :=
  "- `" ++ item.path ++ "`"

private def renderTheoremItem (item : TheoremItem) : String :=
  "- `" ++ item.name ++ "` : `" ++ renderSynExpr item.statement ++ "`\n" ++
  "  - `" ++ item.file ++ "`"

mutual
  partial def renderBlock : ReadmeBlock → String
    | .heading level text => headingPrefix level ++ text
    | .paragraph sents =>
        String.intercalate "\n" (sents.map ensurePeriod)
    | .bulletList items =>
        String.intercalate "\n" (items.map renderBulletChild)
    | .claimBullets items =>
        String.intercalate "\n" (items.map fun i => "- " ++ ensurePeriod i.text)
    | .theoremItems items =>
        String.intercalate "\n" (items.map renderTheoremItem)
    | .apiItems items =>
        String.intercalate "\n" (items.map renderApiItem)
    | .syntaxItems items =>
        String.intercalate "\n" (items.map renderSyntaxItem)
    | .pathItems items =>
        String.intercalate "\n" (items.map renderPathItem)
    | .bulletItem text => "- " ++ text
    | .codeBlock lang code =>
        "```" ++ lang ++ "\n" ++ code ++ "\n```"
    | .fileRef path desc => "- `" ++ path ++ "`\n  - " ++ desc
    | .apiList items =>
        String.intercalate "\n" (items.map fun (name, desc) =>
          "  - `" ++ name ++ "` — " ++ desc)

  partial def renderBulletChild : ReadmeBlock → String
    | .bulletItem text => "- " ++ text
    | .fileRef path desc => "- `" ++ path ++ "`\n  - " ++ desc
    | .claimBullets items =>
        String.intercalate "\n" (items.map fun i => "  - " ++ ensurePeriod i.text)
    | .theoremItems items =>
        String.intercalate "\n" (items.map fun i =>
          "  - `" ++ i.name ++ "` : `" ++ renderSynExpr i.statement ++ "`")
    | .pathItems items =>
        String.intercalate "\n" (items.map fun i => "  - `" ++ i.path ++ "`")
    | other => renderBlock other
end

def renderDoc (blocks : List ReadmeBlock) : String :=
  String.intercalate "\n\n" (blocks.map renderBlock) ++ "\n"

end Mettapedia.DocText.ReadmeTree
