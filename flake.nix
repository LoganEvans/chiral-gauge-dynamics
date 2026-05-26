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
            scheme-medium
            revtex
            biblatex
            biber
            amsmath
            amsfonts
            graphics
            cm-super
            mlmodern
            type1cm
            preview
            babel
            pgf
            tikz-feynman
            latexmk
            relsize
            todonotes
            ;
        };

        pythonEnv = pkgs.python3.withPackages (
          ps: with ps; [
            black
            graphviz
            grip
            matplotlib
            monty
            numpy
            pandas
            requests
            scipy
            sympy
            tabulate
            tqdm
            pyyaml
          ]
        );

        treefmtEval = treefmt-nix.lib.evalModule pkgs ./treefmt.nix;

        cgd-drv = pkgs.mkShell {
          buildInputs = [
            pkgs.graphviz
            pkgs.texlab
            pkgs.wslu
            texlive
            pkgs.evince
            pkgs.zathura
            pkgs.git
            pkgs.curl
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
