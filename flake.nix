{
  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    idris-nix.url = "github:Perigord-Kleisli/Idris-nix";
  };

  outputs = {
    nixpkgs,
    flake-utils,
    idris-nix,
    ...
  }:
    flake-utils.lib.eachDefaultSystem (system: let
      pkgs = import nixpkgs {
        inherit system;
        overlays = [idris-nix.overlays.${system}];
      };
      ipkgName = "hello";
    in {
      defaultPackage = with pkgs;
        build-idris2-package {
          pname = ipkgName;
          version = "0.1";
          src = ./.;
          nativeBuildInputs = [];
          extraBuildInputs = [];
          idris2Deps = [];
          meta = {};
        };

      devShell = with pkgs;
        idris-nix.mkShell.${system} {
          #For all your command-line tools
          packages = [idris2-lsp rlwrap];

          #For the Idris libraries that are dependencies
          idris2Deps = [];
          shellHook = ''
            alias idris2="rlwrap -s 1000 idris2 --no-banner"
          '';
        };
    });
}
