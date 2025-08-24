{
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs?ref=nixos-unstable";
  };

  outputs = { self, nixpkgs }: let 
    system = "x86_64-linux";
    pkgs = nixpkgs.legacyPackages.${system};
  in {
    devShells.${system}.default = pkgs.mkShell {
      buildInputs = with pkgs; [
        cargo rustc rustfmt clippy rust-analyzer fish lldb
        glibc gcc
        vscode-extensions.vadimcn.vscode-lldb
      ];

      nativeBuildInputs = [ pkgs.pkg-config ];

      env = {
        RUST_SRC_PATH = "${pkgs.rust.packages.stable.rustPlatform.rustLibSrc}";
        SHELL = "${pkgs.fish}/bin/fish";

        # Adapter executable and liblldb shipped with the VSCode extension in nixpkgs:
        CODELLDB_PATH =
          "${pkgs.vscode-extensions.vadimcn.vscode-lldb}/share/vscode/extensions/vadimcn.vscode-lldb/adapter/codelldb";
        LIBLLDB_PATH =
          "${pkgs.vscode-extensions.vadimcn.vscode-lldb}/share/vscode/extensions/vadimcn.vscode-lldb/lldb/lib/liblldb.so";
      };

      shellHook = ''
        # aliases for fish
        exec fish -C '
          alias vim nvim
          alias lg lazygit
        '
      '';
    };
  };
}
