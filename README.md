# Safe-by-default Relaxed Memory Model
JMM-like Relaxed Memory Model, the Coq supplementary repository

## How use Nix to build and work on the project
### Things to do once on your machine
1. Install [Nix](https://nixos.org/download.html).
2. Run `nix-env -iA nixpkgs.cachix && cachix use coq && cachix use coq-community && cachix use math-comp` to enable standard binary caches. See [Coq Nix Toolbox](https://github.com/coq-community/coq-nix-toolbox) for more details.
3. Run `cachix use weakmemory` to enable the binary cache for our weakmemory-related projects.
### Things to do every time you start working on the project
4. Run `nix-shell` in the root of the project.
5. Run `make` to build the project.
6. Run `code .` to open the project in VSCode with the proper Coq environment or use a VSCode extension like `Nix Environment Selector``.
