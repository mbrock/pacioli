{
  description = "Agda development environment for pacioli";

  inputs.nixpkgs.url = "https://channels.nixos.org/nixos-unstable/nixexprs.tar.xz";

  outputs =
    { nixpkgs, ... }:
    let
      systems = [
        "x86_64-linux"
        "aarch64-linux"
        "x86_64-darwin"
        "aarch64-darwin"
      ];
      forAllSystems = nixpkgs.lib.genAttrs systems;
    in
    {
      devShells = forAllSystems (
        system:
        let
          pkgs = import nixpkgs { inherit system; };
          # The standard library is vendored under vendor/agda-stdlib (a
          # checkout of agda/agda-stdlib, currently v2.4), so we use the
          # *unwrapped* Agda compiler (the wrapped pkgs.agda pins its own
          # --library-file to an empty nixpkgs set, ignoring AGDA_DIR) and
          # point a libraries file at the vendored source.
          agda = pkgs.agda.unwrapped or pkgs.haskellPackages.Agda;
        in
        {
          default = pkgs.mkShell {
            packages = [ agda ];

            shellHook = ''
              mkdir -p .agda
              export AGDA_DIR="$PWD/.agda"
              printf '%s\n%s\n' \
                "$PWD/pacioli.agda-lib" \
                "$PWD/vendor/agda-stdlib/standard-library.agda-lib" \
                > "$AGDA_DIR/libraries"
              printf '%s\n' pacioli > "$AGDA_DIR/defaults"
            '';
          };
        }
      );
    };
}
