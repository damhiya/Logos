{
  description = "logos";
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs =
    {
      self,
      nixpkgs,
      flake-utils,
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = nixpkgs.legacyPackages."${system}";
        agda = pkgs.agda.withPackages (
          pkgs: with pkgs; [
            standard-library
            cubical
          ]
        );
        coqBuildInputs = with pkgs.coqPackages_8_18; [
          coq
          stdpp
        ];
        buildInputs = [ agda pkgs.teyjus ] ++ coqBuildInputs;
      in
      {
        devShell = pkgs.mkShell {
          inherit buildInputs;
          nativeBuildInputs = [ ];
        };
      }
    );
}
