import Lake
open Lake DSL

def moreServerArgs := #[
  "-Dpp.unicode.fun=true", -- pretty-prints `fun a ↦ b`
  "-DautoImplicit=false",
  "-DrelaxedAutoImplicit=false"
]

-- These settings only apply during `lake build`, but not in VSCode editor.
def moreLeanArgs := moreServerArgs

-- moreServerArgs

package «leanCourse» where
  moreServerArgs := moreServerArgs

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"v4.2.0"

-- require Paperproof from git "https://github.com/Paper-Proof/paperproof.git"@"main"/"lean"




@[default_target]
lean_lib «LeanCourse» where
  moreLeanArgs := moreLeanArgs
