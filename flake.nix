{
  description = "Metamath Zero specification language";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs";
    naersk = {
      url = "github:nmattia/naersk";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    fenix = {
      url = "github:nix-community/fenix";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, naersk, fenix, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = (import nixpkgs) {
          inherit system;
        };

        rust-toolchain = fenix.packages.${system}.stable;
        naersk-lib = pkgs.callPackage naersk {
          inherit (fenix.packages.${system}.beta) cargo rustc;
        };
      in rec {
        # `nix build`
        packages.mm0-rs = naersk-lib.buildPackage {
          root = ./mm0-rs;
          singleStep = true;
        };

        defaultPackage = packages.mm0-rs;

        # `nix run`
        apps.mm0-rs = packages.mm0-rs;
        defaultApp = apps.mm0-rs;

        # `nix develop`
        devShell = pkgs.mkShell {
          buildInputs = [ rust-toolchain.completeToolchain pkgs.rust-analyzer ];
        };
      });
}
