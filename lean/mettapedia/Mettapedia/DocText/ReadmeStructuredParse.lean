/-
# Shared Structured Parse + Audit Helpers for README Trees

Utilities shared across compositional README modules:
- typed line extraction/parsing for headings and typed technical bullet families
- claim-bullet parsing helper
- hard-audit block predicate for prose-bearing bypass detection
-/

import Mettapedia.DocText.ReadmeTree

namespace Mettapedia.DocText.ReadmeStructuredParse

open Mettapedia.DocText.ReadmeTree

inductive ParsedTechnicalLine where
  | heading (level : Nat) (text : String)
  | pathItem (path : String)
  | syntaxItem (label : String) (pattern : SynExpr)
  | apiPath (path : String)
  | apiMember (member : String)
  | fileRefPath (path : String)
  | fileRefDesc (desc : String)
  deriving Repr

private def ensurePeriod (s : String) : String :=
  if s.endsWith "." then s else s ++ "."

def stripBulletPrefix (line : String) : String :=
  if line.startsWith "- " then
    (line.drop 2).toString
  else if line.startsWith "  - " then
    (line.drop 4).toString
  else
    line

def headingEntries (blocks : List ReadmeBlock) : List (Nat × String) :=
  blocks.foldr
    (fun b acc =>
      match b with
      | .heading lvl txt => (lvl, txt) :: acc
      | _ => acc)
    []

def headingLine (h : Nat × String) : String :=
  let (lvl, txt) := h
  String.ofList (List.replicate lvl '#') ++ " " ++ txt

def pathEntries (blocks : List ReadmeBlock) : List PathItem :=
  blocks.foldr
    (fun b acc =>
      match b with
      | .pathItems items => items ++ acc
      | _ => acc)
    []

def syntaxEntries (blocks : List ReadmeBlock) : List SyntaxItem :=
  blocks.foldr
    (fun b acc =>
      match b with
      | .syntaxItems items => items ++ acc
      | _ => acc)
    []

def apiEntries (blocks : List ReadmeBlock) : List ApiItem :=
  blocks.foldr
    (fun b acc =>
      match b with
      | .apiItems items => items ++ acc
      | _ => acc)
    []

def fileRefEntries (blocks : List ReadmeBlock) : List (String × String) :=
  blocks.foldr
    (fun b acc =>
      match b with
      | .fileRef p d => (p, d) :: acc
      | _ => acc)
    []

def claimBulletLines (blocks : List ReadmeBlock) : List String :=
  blocks.foldr
    (fun b acc =>
      match b with
      | .claimBullets items =>
          (items.map (fun i => "- " ++ ensurePeriod i.text)) ++ acc
      | _ => acc)
    []

def technicalLines (blocks : List ReadmeBlock) : List String :=
  let headingLines := (headingEntries blocks).map headingLine
  let pathLines := (pathEntries blocks).map (fun i => "- `" ++ i.path ++ "`")
  let syntaxLines := (syntaxEntries blocks).map (fun i => "- " ++ i.label ++ ": `" ++ renderSynExpr i.pattern ++ "`")
  let apiPathLines := (apiEntries blocks).map (fun i => "- `" ++ i.path ++ "`")
  let apiMemberLines :=
    (apiEntries blocks).foldr
      (fun i acc => (i.members.map (fun m => "  - `" ++ m ++ "`")) ++ acc)
      []
  let fileRefPathLines := (fileRefEntries blocks).map (fun (p, _) => "- `" ++ p ++ "`")
  let fileRefDescLines :=
    (fileRefEntries blocks).foldr
      (fun (_, d) acc => if d = "" then acc else ("  - " ++ d) :: acc)
      []
  headingLines ++ pathLines ++ syntaxLines ++ apiPathLines ++ apiMemberLines ++ fileRefPathLines ++ fileRefDescLines

def parseTechnicalLine? (blocks : List ReadmeBlock) (line : String) : Option ParsedTechnicalLine :=
  match (headingEntries blocks).find? (fun h => headingLine h = line) with
  | some (lvl, txt) => some (.heading lvl txt)
  | none =>
      match (pathEntries blocks).find? (fun p => "- `" ++ p.path ++ "`" = line) with
      | some p => some (.pathItem p.path)
      | none =>
          match (syntaxEntries blocks).find? (fun s => "- " ++ s.label ++ ": `" ++ renderSynExpr s.pattern ++ "`" = line) with
          | some s => some (.syntaxItem s.label s.pattern)
          | none =>
              match (apiEntries blocks).find? (fun i => "- `" ++ i.path ++ "`" = line) with
              | some i => some (.apiPath i.path)
              | none =>
                  match (apiEntries blocks).findSome? (fun i =>
                    i.members.find? (fun m => "  - `" ++ m ++ "`" = line)) with
                  | some m => some (.apiMember m)
                  | none =>
                      match (fileRefEntries blocks).find? (fun (p, _) => "- `" ++ p ++ "`" = line) with
                      | some (p, _) => some (.fileRefPath p)
                      | none =>
                          match (fileRefEntries blocks).findSome? (fun (_, d) =>
                            if d = "" then none else
                            if "  - " ++ d = line then some d else none) with
                          | some d => some (.fileRefDesc d)
                          | none => none

def parseClaimBulletLine? {α : Type} (parseClaimLine? : String → Option α) (line : String) : Option α :=
  parseClaimLine? (stripBulletPrefix line)

/-- Heading semantic-image check:
every heading text in `blocks` parses to a heading whose renderer matches that same text. -/
def headingRenderImageCheck {β : Type}
    (parseHeadingLine? : String → Option β)
    (renderHeading : β → String)
    (blocks : List ReadmeBlock) : Bool :=
  (headingEntries blocks).all (fun (_, txt) =>
    match parseHeadingLine? txt with
    | some h => renderHeading h = txt
    | none => false)

private theorem all_true_of_mem {α : Type} (p : α → Bool) :
    ∀ {xs : List α} (hAll : xs.all p = true) {x : α}, x ∈ xs → p x = true
  | [], hAll, _, hMem => by cases hMem
  | y :: ys, hAll, x, hMem => by
      simp at hAll
      simp at hMem
      rcases hMem with rfl | hMemTail
      · exact hAll.1
      · exact all_true_of_mem p (xs := ys) (hAll := hAll.2) (x := x) hMemTail

/-- If heading-image check passes, each heading entry has a parser/render witness. -/
theorem headingRenderImageWitness {β : Type}
    (parseHeadingLine? : String → Option β)
    (renderHeading : β → String)
    (blocks : List ReadmeBlock)
    (hCheck : headingRenderImageCheck parseHeadingLine? renderHeading blocks = true)
    {lvl : Nat} {txt : String}
    (hMem : (lvl, txt) ∈ headingEntries blocks) :
    ∃ h, parseHeadingLine? txt = some h ∧ renderHeading h = txt := by
  have hAll :
      (headingEntries blocks).all
        (fun (_, t) =>
          match parseHeadingLine? t with
          | some h => renderHeading h = t
          | none => false) = true := hCheck
  have hPred :
      (match parseHeadingLine? txt with
       | some h => renderHeading h = txt
       | none => false) = true :=
    all_true_of_mem
      (fun (_, t) =>
        match parseHeadingLine? t with
        | some h => renderHeading h = t
        | none => false) hAll hMem
  cases hParsed : parseHeadingLine? txt with
  | none =>
      simp [hParsed] at hPred
  | some h =>
      refine ⟨h, hParsed.symm, ?_⟩
      simpa [hParsed] using hPred

private def isDigitStr (s : String) : Bool :=
  !s.isEmpty && s.toList.all Char.isDigit

private def isIdentChar (c : Char) : Bool :=
  c.isAlphanum || c = '_' || c = '.' || c = '-' || c = '/'

private def isIdentifierAtom (s : String) : Bool :=
  let t := s.trimAscii.toString
  if t.isEmpty then
    false
  else
    let parts := t.splitOn " "
    match parts with
    | [p] =>
        p.toList.all isIdentChar &&
          p.toList.any (fun c => c.isAlpha || c.isDigit)
    | [tag, n] =>
        !tag.isEmpty && tag.toList.all isIdentChar && isDigitStr n
    | _ => false

private def isIdentifierLikeMember (s : String) : Bool :=
  let t := s.trimAscii.toString
  !t.contains ',' && isIdentifierAtom t

def blockPassesHardAuditWith {α β : Type}
    (parseClaimLine? : String → Option α)
    (parseHeadingLine? : String → Option β) : ReadmeBlock → Bool
  | .heading _ text => (parseHeadingLine? text).isSome
  | .paragraph sents => sents.all (fun s => (parseClaimLine? s).isSome)
  | .claimBullets items => items.all (fun i => (parseClaimLine? i.text).isSome)
  | .apiItems items =>
      items.all (fun i =>
        !i.path.trimAscii.isEmpty &&
        i.members.all isIdentifierLikeMember &&
        (match i.note with
         | none => true
         | some n => (parseClaimLine? n).isSome))
  | .syntaxItems items =>
      items.all (fun i => !i.label.trimAscii.isEmpty && synExprWellFormed i.pattern)
  | .pathItems _ => true
  | .codeBlock _ _ => true
  | .fileRef _ d => d = "" || (parseClaimLine? d).isSome
  | .apiList _ => true
  | .bulletList _ => false
  | .bulletItem _ => false

def blockPassesHardAudit {α : Type} (parseClaimLine? : String → Option α) : ReadmeBlock → Bool :=
  blockPassesHardAuditWith parseClaimLine? (fun _ => some ())

end Mettapedia.DocText.ReadmeStructuredParse
