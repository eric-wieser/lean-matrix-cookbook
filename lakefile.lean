import Lake

open Lake DSL

package matrix_cookbook

@[default_target]
lean_lib MatrixCookbook

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.15.0"
