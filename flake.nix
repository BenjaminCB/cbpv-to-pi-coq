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
                packages.hello = pkgs.hello;
                devShells.default = pkgs.mkShell {
                    nativeBuildInputs = with pkgs; [
                        just
                        coq
                        coqPackages.coqide
                        coqPackages.mathcomp
                    ];

                    shellHook = ''
                        echo Welcome to coq shell
                    '';
                };
            }
        );
}
