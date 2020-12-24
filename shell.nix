{ pkgs ? import <nixpkgs> {} }:

let
    vscode = pkgs.vscode-with-extensions.override {
        vscode = pkgs.vscodium;

        vscodeExtensions = with pkgs.vscode-extensions; [
        ]
        ++ pkgs.vscode-utils.extensionsFromVscodeMarketplace [
          {
            name = "editorconfig";
            publisher = "editorconfig";
            version = "0.15.1";
            sha256 = "18r19dn1an81l2nw1h8iwh9x3sy71d4ab0s5fvng5y7dcg32zajd";
          }
          { 
            name = "vscoq";
            publisher = "maximedenes";
            version = "0.3.2";
            sha256 = "1k55azavxhb2jxhk06f2rgkvf66bm1kwnmvyrjxp00xq3dai39bb";
          }
        ];
    };

    der = import ./default.nix { inherit pkgs; coq-version-or-url="8.12"; shell = true; };

in der.overrideAttrs (attrs: attrs // { 
  propagatedBuildInputs = [ vscode ] ++ attrs.propagatedBuildInputs;
})
