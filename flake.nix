{
  description = "Chiral Gauge Dynamics";

  inputs = {
    # 1. Add litlib4 as a Flake input (assumes litlib4 has a flake.nix).
    litlib4.url = "git+ssh://git@github.com/LoganEvans/litlib4.git";

    # We sync system dependencies to litlib4. The Lean compiler 
    # itself is now managed dynamically via Elan reading lean-toolchain.
    nixpkgs.follows = "litlib4/nixpkgs";

    flake-utils.url = "github:numtide/flake-utils";

    treefmt-nix.url = "github:numtide/treefmt-nix";
    treefmt-nix.inputs.nixpkgs.follows = "nixpkgs";
  };

  outputs =
    {
      self,
      nixpkgs,
      flake-utils,
      treefmt-nix,
      litlib4,
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = import nixpkgs {
          inherit system;
          config.allowUnfree = true;
        };

        texlive = pkgs.texlive.combine {
          inherit (pkgs.texlive)
            # Core and Physics
            scheme-medium
            revtex
            amsmath
            amsfonts
            graphics
            xcolor
            enumitem

            # Bibliography
            biblatex
            biber

            # Lean Code Formatting & Referencing (Tao / Blueprint style)
            hyperref
            cleveref
            pdfcomment
            datetime2  # <--- Dependency of pdfcomment
            tracklang  # <--- Dependency of datetime2
            marginnote # <--- Dependency of pdfcomment
            soulpos    # <--- Dependency of pdfcomment
            soul       # <--- Dependency of pdfcomment
            zref       # <--- Dependency of pdfcomment
            minted     # Requires python3Packages.pygments for Lean 4 syntax
            fvextra    # minted dependency
            catchfile  # minted dependency
            xstring    # minted dependency
            upquote    # minted dependency
            lineno     # minted dependency

            # Build tools
            latexmk
            ;
        };

        pythonEnv = pkgs.python3.withPackages (
          ps: with ps; [
            # Core Math/Physics
            numpy
            scipy
            sympy
            matplotlib
            jax
            optax

            # Utils & Formatting
            black
            pyyaml

            # LaTeX minted dependency (Provides 'pygmentize' with Lean 4 support)
            pygments
          ]
        );

        treefmtEval = treefmt-nix.lib.evalModule pkgs ./treefmt.nix;

        cgd-drv = pkgs.mkShell {
          buildInputs = [
            pkgs.graphviz
            pkgs.texlab
            pkgs.wslu
            texlive
            pkgs.git
            pkgs.curl
            pkgs.zip  # Required for packaging arXiv submissions
            pkgs.zstd # Required to decompress Mathlib cache (.tar.zst)
            pkgs.elan # Elan reads lean-toolchain automatically
          ];

          packages = [
            pythonEnv
          ];

          shellHook = ''
            export BROWSER=wslview
            export PYTHONPATH="$PWD:$PYTHONPATH"

            # Force Elan to install toolchains locally in the repository
            export ELAN_HOME="$PWD/.elan"

            # ----------------------------------------------------------------
            # UTILITY FUNCTIONS
            # ----------------------------------------------------------------

            # Run the CGD report tool from the repo root
            cgd-report() {
              local REPO_ROOT="$(git rev-parse --show-toplevel)"
              # Run in a subshell so we don't change the user's active directory
              (
                cd "$REPO_ROOT" || return 1
                lake exe cgd_report "$@"
              )
            }

            # Compile the paper via the Makefile in the paper/ directory
            cgd-paper() {
              local REPO_ROOT="$(git rev-parse --show-toplevel)"
              (
                cd "$REPO_ROOT/paper" || return 1
                make "$@"
              )
            }

            # Clean all LaTeX build files
            cgd-paper-clean() {
              local REPO_ROOT="$(git rev-parse --show-toplevel)"
              (
                cd "$REPO_ROOT/paper" || return 1
                make fullclean
              )
            }

            # Build the arXiv submission bundle
            cgd-paper-arXiv() {
              local REPO_ROOT="$(git rev-parse --show-toplevel)"
              (
                cd "$REPO_ROOT/paper" || return 1
                make arxiv
              )
            }

            # ----------------------------------------------------------------
            # AUTOMATED FIRST-TIME SETUP
            # ----------------------------------------------------------------
            if [ ! -d ".lake/packages/mathlib" ]; then
              echo "======================================================="
              echo "🚀 Fresh clone detected! Initializing Lean environment..."
              echo "======================================================="

              echo "-> Running 'lake update' to fetch dependencies..."
              # Elan natively reads the `lean-toolchain` file in this directory.
              # Because of ELAN_HOME, the toolchain will be isolated to .elan/
              lake update || true

              echo "-> Fetching Mathlib cache..."
              lake exe cache get || echo "⚠️ Cache fetch failed or incomplete."

              echo "✅ Setup complete!"
              echo "   Run 'lake build' to compile your project."
              echo "======================================================="
            fi
          '';
        };
      in
      {
        pkgs = nixpkgs.legacyPackages.${system};

        packages = {
          default = cgd-drv;
        };

        devShells.default = cgd-drv;

        formatter = (pkgs: treefmtEval.config.build.wrapper) { };
      }
    );
}
