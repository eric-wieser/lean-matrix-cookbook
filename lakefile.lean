import Lake

open Lake DSL

package matrix_cookbook

@[default_target]
lean_lib MatrixCookbook

require "leanprover-community" / "mathlib" @ "git#v4.20.0"
