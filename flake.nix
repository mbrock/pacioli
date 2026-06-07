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
          standard-library = pkgs.agdaPackages.standard-library;
          agda = pkgs.agda.withPackages (_: [ standard-library ]);
        in
        {
          default = pkgs.mkShell {
            packages = [ agda ];

            shellHook = ''
              mkdir -p .agda
              printf '%s\n%s\n' "$PWD/pacioli.agda-lib" "${standard-library}/standard-library.agda-lib" > .agda/libraries
              printf '%s\n' pacioli > .agda/defaults
            '';
          };
        }
      );
    };
}
