import Lean
import Batteries
import Mathlib.Tactic
import Lean.Elab

open Lean
open Lean Elab


#eval 1 + 2

def main : IO Unit := do
  IO.println "Hello, Lean!"

unsafe def processCommands : Frontend.FrontendM (List (Environment × InfoState)) := do  -- define a function to process commands in the frontend monad
  let done ← Lean.Elab.Frontend.processCommand  -- process the command getting the parser state, command, and the command state and the input context
  let st := ← get -- get the current state of the frontend
  let infoState := st.commandState.infoState  -- get the info state from the command state
  let env' := st.commandState.env -- get the environment from the command state

  -- clear the infostate
  set {st with commandState := {st.commandState with infoState := {}}}  -- clear the info state
  if done
  then return [(env', infoState)]
  else
    return (env', infoState) :: (←processCommands)  -- recursively call the processCommands function until done is true

unsafe def processFile (filePath : String) : IO Unit := do
  let mut input ← IO.FS.readFile filePath -- reads the contents of the file
  let inputCtx := Lean.Parser.mkInputContext filePath input -- takes in the file data and the file path to be parsed
  let (header, parserState, messages) ← Lean.Parser.parseHeader inputCtx  -- parses the header
  let (env, messages) ← Lean.Elab.processHeader header {} messages inputCtx -- processes the header and creates the environment

  IO.println s!"{filePath}"

  let env := env.setMainModule (← Lean.moduleNameOfFileName filePath none)  -- sets the main module to the file name

  let commandState := { Lean.Elab.Command.mkState env messages {} with infoState.enabled := true }  -- creates the command state with the environment and messages

  let (steps, _frontendState) ← (processCommands { inputCtx := inputCtx }).run  -- runs the processCommands function with the input context and command state
    { commandState := commandState, parserState := parserState, cmdPos := parserState.pos } -- sets the command state and parser state

  -- output all of the before and after states of the info tree
  IO.println s!"{steps.length} steps"
  for ⟨env, s⟩ in steps do
    IO.println s!"{s.infoState}"
    -- get the info tree from the info state
    let infoTree := s.infoState.infoTree

  for ⟨env, s⟩ in steps do
    for tree in s.trees do
      IO.println (Format.pretty (←tree.format))
      let flattened := tree.context
      for ⟨goal _⟩ in flattened do
        IO.println (Format.pretty (←goal.format))

  throw <| IO.userError s!"{steps.length} steps"



-- #eval processFile "AnimateProofs/Test.lean"


/-
-- read the infotree of a given file
open Lean
open System

def readInfoTree (filePath : String) : IO Unit := do
  let env ← importModules [{ module := `Init }] {}
  let input ← IO.FS.readFile filePath
  let (_, infoTree) ← Lean.Elab.Command.elabCommand input env
  IO.println infoTree

-- Example usage
#eval readInfoTree "C:\Users\lukec\OneDrive\Documents\AnimateProofs\AnimateProofs\Test.lean"
-/

/-
set_option trace.Elab.info true
example : 2 = 1 + 1 := by
  show 1 + 1 = 2
  rw[one_add_one_eq_two]

set_option trace.Elab.info false
-/
