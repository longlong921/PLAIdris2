{
  description = "Programming Language Foundations in Idris2: checked bilingual book";
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/7c8764b7c7b09b34f632464276218ef9090eaa11";
  outputs = { self, nixpkgs }:
    let
      systems = [ "x86_64-linux" "aarch64-linux" "x86_64-darwin" "aarch64-darwin" ];
      eachSystem = f: nixpkgs.lib.genAttrs systems (system: f (import nixpkgs { inherit system; }));
      python = pkgs: pkgs.python3.withPackages (p: [ p.markdown ]);
    in {
      devShells = eachSystem (pkgs: {
        default = pkgs.mkShell {
          packages = [ pkgs.idris2 (python pkgs) pkgs.nodejs pkgs.gnumake ];
        };
      } // pkgs.lib.optionalAttrs pkgs.stdenv.isLinux {
        browser = pkgs.mkShell {
          packages = [ (pkgs.python3.withPackages (p: [ p.markdown p.playwright ])) pkgs.chromium ];
          CHROMIUM_EXECUTABLE = "${pkgs.chromium}/bin/chromium";
        };
      });
      packages = eachSystem (pkgs: {
        default = pkgs.stdenvNoCC.mkDerivation {
          pname = "plaidris2-book";
          version = "0.1.0";
          src = self;
          nativeBuildInputs = [ pkgs.idris2 (python pkgs) pkgs.nodejs ];
          buildPhase = "python3 tools/check.py";
          installPhase = "mkdir -p $out; cp -r dist/. $out/";
        };
      });
      checks = eachSystem (pkgs: {
        book = self.packages.${pkgs.stdenv.hostPlatform.system}.default;
      });
    };
}
