import Lake

open System Lake DSL

package AnimateProofs where
  version := v!"0.1.0"
  keywords := #["math"]
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`weak.trace.Elab.output, "out.json"⟩]

require "leanprover-community" / mathlib

@[default_target] lean_lib AnimateProofs

@[default_target]
lean_exe «Animate» where
  supportInterpreter := true
