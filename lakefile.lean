-- FILENAME: lakefile.lean

import Lake
open Lake DSL

package «CGD» {
  -- Dashboard reporting target
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.27.0"

-- The new foundational mathematical and literature library.
-- require litlib4 from "../litlib4" -- Use this line for local development
require litlib4 from git "https://github.com/LoganEvans/litlib4.git" @ "dev"

@[default_target]
lean_lib «CGD» {
  globs := #[.andSubmodules `CGD]
}

lean_exe «cgd_report» {
  root := `Main
  supportInterpreter := true
}
