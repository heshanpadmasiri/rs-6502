{
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs?ref=nixos-unstable";
  };

  outputs = { self, nixpkgs }: let 
    pkgs = nixpkgs.legacyPackages."x86_64-linux";
  in {
    devShells."x86_64-linux".default = pkgs.mkShell {
    buildInputs = with pkgs; [
        cargo rustc rustfmt clippy rust-analyzer fish lldb
      ];

    nativeBuildInputs = [ pkgs.pkg-config ];

    env = {
        RUST_SRC_PATH = "${pkgs.rust.packages.stable.rustPlatform.rustLibSrc}";
        SHELL = "${pkgs.fish}/bin/fish"; # default shell inside nix develop
      };


      shellHook = ''
        exec fish -C 'alias vim nvim; alias lg lazygit'
      '';
  };
  };
}
