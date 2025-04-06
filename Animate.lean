import Lean
import Batteries
import Mathlib.Tactic
import Lean.Elab

open Lean
open Lean Elab


#eval 1 + 2

def main : IO Unit := do
  IO.println "Hello, Lean!"

unsafe def processCommands : Frontend.FrontendM (List (Environment × InfoState)) := do
  let done ← Lean.Elab.Frontend.processCommand
  let st := ← get
  let infoState := st.commandState.infoState
  let env' := st.commandState.env

  -- clear the infostate
  set {st with commandState := {st.commandState with infoState := {}}}
  if done
  then return [(env', infoState)]
  else
    return (env', infoState) :: (←processCommands)

unsafe def processFile (filePath : String) : IO Unit := do
  let mut input ← IO.FS.readFile filePath
  let inputCtx := Lean.Parser.mkInputContext filePath input
  let (header, parserState, messages) ← Lean.Parser.parseHeader inputCtx
  let (env, messages) ← Lean.Elab.processHeader header {} messages inputCtx

  IO.println s!"{filePath}"

  let env := env.setMainModule (← Lean.moduleNameOfFileName filePath none)

  let commandState := { Lean.Elab.Command.mkState env messages {} with infoState.enabled := true }

  let (steps, _frontendState) ← (processCommands { inputCtx := inputCtx }).run
    { commandState := commandState, parserState := parserState, cmdPos := parserState.pos }

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
