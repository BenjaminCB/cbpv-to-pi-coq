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
                        coq
                        coqPackages.coqide
                        coqPackages.paco
                        coqPackages.vscoq-language-server
                        # (coqPackages.vscoq-language-server.overrideAttrs (old: let
                        #   newSrc = pkgs.fetchFromGitHub {
                        #     owner  = "rocq-prover";
                        #     repo   = "vscoq";
                        #     rev    = "v2.2.5";
                        #     sha256 = "sha256-XyIjwem/yS7UIpQATNixgKkrMOHHs74nkAOvpU5WG1k=";
                        #   };
                        # in {
                        #   version = "2.2.5";
                        #   src = "${newSrc}/language-server";
                        # }))
                    ];
                    shellHook = ''
                        echo Welcome to coq shell
                    '';
                };
            }
        );
}
