{ metaFetch, mkCoqDerivation, coq, lib, bash, hostname,
  python3, time, dune_3, glib, gnome, wrapGAppsHook,
  version ? null }:

let ocamlPackages = coq.ocamlPackages;
    defaultVersion = lib.switch coq.coq-version [
      { case = "8.18"; out = "2.0.1+coq8.18"; }
    ] null;
    location = { domain = "github.com"; owner = "coq-community"; repo = "vscoq"; };
    fetch = metaFetch ({
      release."2.0.1+coq8.18".sha256 = "sha256-bSCXknFGqWTTQEpEPk95tdfjY/CeeSQEYFol5cNHLd4=";
      release."2.0.1+coq8.18".rev = "v2.0.1+coq8.18";
      inherit location; });
    fetched = fetch (if version != null then version else defaultVersion);
in
ocamlPackages.buildDunePackage {
  duneVersion = "3";
  pname = "vscoq-language-server";
  inherit (fetched) version;
  src = "${fetched.src}/language-server";
  buildInputs =
    [ coq bash hostname python3 time dune_3 glib gnome.adwaita-icon-theme
      wrapGAppsHook ] ++ (with ocamlPackages;
    [ lablgtk3-sourceview3 ocaml yojson zarith findlib ppx_inline_test
      ppx_assert ppx_sexp_conv ppx_deriving ppx_import sexplib
      ppx_yojson_conv lsp sel ]);

  meta = with lib; {
    description = "Language server for the vscoq vscode/codium extension";
    homepage = "https://github.com/coq-community/vscoq";
    maintainers = with maintainers; [ cohencyril ];
    license = licenses.mit;
  };
}