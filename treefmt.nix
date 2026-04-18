{ pkgs, ... }:
{
  projectRootFile = "flake.nix";

  programs.black.enable = true;
  programs.jsonfmt.enable = true;
  programs.nixfmt.enable = true;
  programs.texfmt.enable = true;

  # Define custom exclusions for built-in formatters
  programs.black.excludes = [
    "venv/*"
    "external-literature/*"
    ".lake/*"
  ];

  # Custom formatter to recursively strip trailing whitespace
  settings.formatter.trailing-whitespace = {
    command = "${pkgs.gnused}/bin/sed";
    options = [ "-i" "-e" "s/[[:space:]]*$//" ];
    includes = [ 
      "*.lean" 
      "*.py" 
      "*.md" 
      "*.txt" 
      "*.tex" 
      "*.bib" 
    ];
    excludes = [ 
      "venv/*" 
      "external-literature/*" 
      ".lake/*" 
    ];
  };
}
