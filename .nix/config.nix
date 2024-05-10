{
  ## DO NOT CHANGE THIS
  format = "1.0.0";
  ## unless you made an automated or manual update
  ## to another supported format.

  ## The attribute to build from the local sources,
  ## either using nixpkgs data or the overlays located in `.nix/coq-overlays`
  ## Will determine the default main-job of the bundles defined below
  attribute = "xmm";

  ## If you want to select a different attribute (to build from the local sources as well)
  ## when calling `nix-shell` and `nix-build` without the `--argstr job` argument
  # shell-attribute = "{{nix_name}}";

  ## Maybe the shortname of the library is different from
  ## the name of the nixpkgs attribute, if so, set it here:
  # pname = "{{shortname}}";

  ## Lists the dependencies, phrased in terms of nix attributes.
  ## No need to list Coq, it is already included.
  ## These dependencies will systematically be added to the currently
  ## known dependencies, if any more than Coq.
  ## /!\ Remove this field as soon as the package is available on nixpkgs.
  ## /!\ Manual overlays in `.nix/coq-overlays` should be preferred then.
  # buildInputs = [ ];

  ## Indicate the relative location of your _CoqProject
  ## If not specified, it defaults to "_CoqProject"
  # coqproject = "_CoqProject";

  default-bundle = "8.18";

  bundles."8.18" = {
    push-branches = [ "**" ];
    coqPackages.vscoq-language-server.override.version = "v2.0.3+coq8.18";
    coqPackages.coq.override.version = "8.18";
    coqPackages.hahn.override.version = "1.18.0";
    coqPackages.hahnExt.override.version = "0.9.4";
    coqPackages.sflib.override.version = "master";
    coqPackages.promising-lib.override.version = "1.19.0";
    coqPackages.imm.override.version = "1.6.1";
  };

  cachix.coq = {};
  cachix.math-comp = {};
  cachix.coq-community = {};
  
  cachix.weakmemory.authToken = "CACHIX_AUTH_TOKEN";
}
