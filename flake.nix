{
  description = "lambda calculus";
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages."${system}";
        agdaPackages = pkgs: with pkgs; [ standard-library ];
        buildInputs = with pkgs; [
          (agda.withPackages agdaPackages)
        ];
      in {
        devShell = pkgs.mkShell {
          inherit buildInputs;
          nativeBuildInputs = [ ];
        };
      });

}

