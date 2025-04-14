{
    description = "Flake utils demo";
    inputs = {
        nixpkgs.url = "github:NixOS/nixpkgs/nixos-24.11";
        flake-utils.url = "github:numtide/flake-utils";
    };
    outputs = { self, nixpkgs, flake-utils }:
        flake-utils.lib.eachDefaultSystem (system:
            let
                pkgs = import nixpkgs {
                    inherit system;
                    overlays = [ (import ./vscoq-2.2.5.nix) ];
                };
            in {
                packages.default = pkgs.hello;
                packages.hello = pkgs.hello;
                devShells.default = pkgs.mkShell {
                    nativeBuildInputs = with pkgs; [
                        coq
                        coqPackages.coqide
                        coqPackages.paco
                        coqPackages.vscoq-language-server.override
                    ];
                    shellHook = ''
                        echo Welcome to coq shell
                    '';
                };
            }
        );
}
