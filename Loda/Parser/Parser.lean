import Loda.Ast
import Loda.Typing
import Loda.Compile
import Loda.Frontend -- assuming you've implemented the frontend from earlier
import Lean.Meta.Basic

open System
open Lean Elab Command Term Meta

/-- Parse CODA DSL content into a list of Circuits -/
unsafe def parseLodaProgram (content : String) : MetaM (List Circuit.Circuit) := do
  -- Parse the entire file content into syntax
  let env ← getEnv
  let fileId := `unnamedLodaFile
  match Lean.Parser.runParserCategory env `coda_file content fileId.toString with
  | Except.error err => throwError err
  | Except.ok stx =>
    -- Process all circuit declarations in the file
    let circuits ← elabLodaFile stx
    pure circuits.toList


/-- Parse a CODA file and convert it to AST -/
unsafe def parseLodaFile (filename : String) : MetaM (Option (List Circuit.Circuit)) := do
  -- Read the file content
  match ← IO.FS.readFile filename with
  | content =>
    -- Parse content using the frontend parser
    try
      let circuits ← parseLodaProgram content
      pure (some circuits)
    catch _ =>
      pure none
  /-
  | .error err =>
    IO.eprintln s!"Error reading file {filename}: {err}"
    pure none
  | .ok content =>
    -- Parse content using the frontend parser
    try
      -- Assuming your parser returns a list of circuits
      let circuits ← parseLodaProgram content
      pure (some circuits)
    catch e =>
      IO.eprintln s!"Parse error in {filename}: {e.toString}"
      pure none
  -/
