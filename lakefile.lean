import Lake
open Lake DSL

package "lean-constructions" where
  -- add package configuration options here

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "lean-pr-testing-4474"


@[default_target]
lean_lib «LeanConstructions» where
  globs := #[.andSubmodules `LeanConstructions]

