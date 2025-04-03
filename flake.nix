{
    description = "Flake utils demo";
    inputs = {
        nixpkgs.url = "github:NixOS/nixpkgs/nixos-24.11";
        flake-utils.url = "github:numtide/flake-utils";
    };
    outputs = { self, nixpkgs, flake-utils }:
        flake-utils.lib.eachDefaultSystem (system:
            let
                pkgs = nixpkgs.legacyPackages.${system};
            in {
                packages.default = pkgs.hello;
                packages.hello = pkgs.hello;
                devShells.default = pkgs.mkShell {
                    nativeBuildInputs = with pkgs; [
                        coq_8_15
                        coqPackages.coqide
                    ] ++ [
                        ((import ./coinduction.nix) {
                            lib = pkgs.lib;
                            mkCoqDerivation = pkgs.mkCoqDerivation;
                            coq = pkgs.coq;
                            stdlib = coqPackages.coqide;
                        })
                    ];
                    shellHook = ''
                        echo Welcome to coq shell
                    '';
                };
            }
        );
}
