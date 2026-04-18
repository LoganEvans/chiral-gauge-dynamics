{
  description = "Chiral Gauge Dynamics";

  inputs = {
    # 1. Add litlib4 as a Flake input (assumes litlib4 has a flake.nix).
    litlib4.url = "git+ssh://git@github.com/LoganEvans/litlib4.git";

    # 2. Sync the Lean 4 compiler! 
    # By forcing our nixpkgs to follow litlib4's nixpkgs, we guarantee that 
    # we use the exact same `pkgs.lean4` compiler version used by litlib4.
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
            pkgs.lean4
          ];

          packages = [
            pythonEnv
          ];

          shellHook = ''
            export BROWSER=wslview
            export PYTHONPATH="$PWD:$PYTHONPATH"

            # Tell Lake to NEVER look for Elan
            export LAKE_NO_ELAN=1

            # ----------------------------------------------------------------
            # AUTOMATED FIRST-TIME SETUP
            # ----------------------------------------------------------------
            if [ ! -d ".lake/packages/mathlib" ]; then
              echo "======================================================="
              echo "🚀 Fresh clone detected! Initializing PURE Nix Lean environment..."
              echo "======================================================="
              
              echo "-> Running 'lake update' to fetch dependencies..."
              lake update || true
              
              echo "✅ Dependencies fetched!"
              echo "☕ Because we are using pure Nix, Mathlib and Litlib must be compiled from source."
              echo "   Run 'lake build' and grab a coffee (this takes 1-2 hours once)."
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
