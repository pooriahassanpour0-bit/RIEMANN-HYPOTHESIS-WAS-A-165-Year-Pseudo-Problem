import Lake
open Lake DSL

package zrap

-- Depend on mathlib4 (Mathlib)
require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "81ccf8f455f218d30ffa5fea34f10e82a3dbefa6"

lean_lib ZRAP
