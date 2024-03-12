{
  description = "logos";
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages."${system}";
        agda = pkgs.agda.withPackages
          (pkgs: with pkgs; [ standard-library cubical ]);
        buildInputs = [ agda ];
      in {
        devShell = pkgs.mkShell {
          buildInputs = [ agda ];
          nativeBuildInputs = [ ];
        };
      });
}
