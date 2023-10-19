{ lib, mkCoqDerivation, which, coq
  , vscoq-language-server
  , imm
  , coq-record-update
  , version ? null }:

with lib; mkCoqDerivation {
  pname = "xmm";
  owner = "weakmemory";
  domain = "github.com";

  inherit version;
  defaultVersion = with versions; switch coq.coq-version [
  ] null;

  propagatedBuildInputs = [vscoq-language-server imm coq-record-update];

  dontConfigure = true;
  extraInstallFlags = ["-f" "Makefile.coq"]; 

  meta = {
    ## Describe your package in one sentence
    # description = "";
    ## Kindly ask one of these people if they want to be an official maintainer.
    ## (You might also consider adding yourself to the list of maintainers)
    # maintainers = with maintainers; [ cohencyril siraben vbgl Zimmi48 ];
    ## Pick a license from
    ## https://github.com/NixOS/nixpkgs/blob/master/lib/licenses.nix
    # license = licenses.mit;
  };
}