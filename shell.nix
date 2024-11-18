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
    z3_path=$(which z3)
    export VERUS_Z3_PATH="$z3_path"
    export RUSTC_BOOTSTRAP=1
    export VERUS_IN_VARGO=1
    export RUSTFLAGS="--cfg proc_macro_span --cfg verus_keep_ghost --cfg span_locations"
    export PATH="$PATH:${builtins.toString ./.}/source/target-verus/debug:${builtins.toString ./.}/source/target-verus/release:${pkgs.z3_4_12}/bin"
  '';
}
