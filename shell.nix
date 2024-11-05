{pkgs ? import <nixpkgs> {}}:
pkgs.mkShell {
  buildInputs = [
    pkgs.rustup
    pkgs.unzip
    pkgs.wget
    pkgs.cargo
    pkgs.z3_4_12
  ];
  shellHook = ''
    export PATH="$PATH:${builtins.toString ./.}/source/target-verus/debug:${builtins.toString ./.}/source/target-verus/release:${pkgs.z3_4_12}/bin"
  '';
}
