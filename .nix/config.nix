{
  ## DO NOT CHANGE THIS
  format = "1.0.0";
  ## unless you made an automated or manual update
  ## to another supported format.

  ## The attribute to build from the local sources,
  ## either using nixpkgs data or the overlays located in `.nix/coq-overlays`
  ## Will determine the default main-job of the bundles defined below
  attribute = "metarocq";

  no-rocq-yet = true;

  ## If you want to select a different attribute (to build from the local sources as well)
  ## when calling `nix-shell` and `nix-build` without the `--argstr job` argument
  shell-attribute = "equations";

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
  buildInputs = [ "equations" ];
  nativeBuildInputs = [ "equations" ];

  ## Indicate the relative location of your _CoqProject
  ## If not specified, it defaults to "_CoqProject"
  # coqproject = "_CoqProject";

  ## select an entry to build in the following `bundles` set
  ## defaults to "default"
  default-bundle = "rocq-dev";

  # MetaRocq is expected to be compatible with a single coq version

  bundles."rocq-dev" = {
    rocqPackages.rocq-core.override.version = "master";
    rocqPackages.stdlib.override.version = "master";
    coqPackages.equations.override.version = "main";
    coqPackages.ExtLib.override.version = "master";
    coqPackages.coq.override.version = "master";
    coqPackages.stdlib.override.version = "master";

    ## CertiRocq, the main client of the erasure pipeline, built from its
    ## branch that follows Rocq master and MetaRocq main, using the overlay
    ## in .nix/coq-overlays/CertiRocq, a copy of the one on that branch.
    ## CompCert and WasmCert do not depend on MetaRocq: their own jobs build
    ## (and cache) them in parallel with MetaRocq's.  Their other
    ## dependencies are built inside these jobs.
    rocqPackages.CertiRocq.override.version = "rocq-master";
    rocqPackages.compcert.override.version = "master";
    rocqPackages.wasmcert.override.version = "rocq-master";
    rocqPackages.MenhirLib.job = false;
    rocqPackages.MenhirLib.override.version = "master";
    rocqPackages.flocq.job = false;
    rocqPackages.flocq.override.version = "master";
    rocqPackages.mathcomp.job = false;
    rocqPackages.mathcomp.override.version = "master";
    rocqPackages.parseque.job = false;
    rocqPackages.parseque.override.version = "master";
    rocqPackages.hierarchy-builder.job = false;
    rocqPackages.hierarchy-builder.override.version = "master";
    rocqPackages.rocq-elpi.job = false;
    rocqPackages.rocq-elpi.override.version = "master";

    push-branches = ["main"];
    ## genNixActions makes the workflow run on pull_request_target, which
    ## GitHub always takes from the default branch (9.1), not from the PR's
    ## base branch: PRs to main would then get no Nix CI.  After regenerating
    ## .github/workflows/nix-action-rocq-dev.yml, replace its pull_request and
    ## pull_request_target triggers by a plain, unfiltered pull_request one
    ## (fork PRs then cannot push to the metacoq cache, but are still built).
    ## Then make the CertiRocq jobs optional on PRs that do not change the
    ## erasure pipeline: copy the CertiRocq-changes job (which checks that)
    ## and the CertiRocq-approval job (environment certirocq, whose required
    ## reviewers approve it from the workflow run page, skipped when the
    ## erasure pipeline changes) from the previous version of the workflow,
    ## add CertiRocq-approval to the needs of compcert, which wasmcert and
    ## CertiRocq need, and give compcert, wasmcert and CertiRocq
    ## `if: ${{ !failure() && !cancelled() }}` so that they run when
    ## CertiRocq-approval is skipped (the implicit `success()` of a job fails
    ## when any job it transitively needs is skipped).
  };

  ## Cachix caches to use in CI
  ## Below we list some standard ones
  cachix.coq = {};
  cachix.coq-community = {};

  ## If you have write access to one of these caches you can
  ## provide the auth token or signing key through a secret
  ## variable on GitHub. Then, you should give the variable
  ## name here. For instance, coq-community projects can use
  ## the following line instead of the one above:
  cachix.metacoq.authToken = "CACHIX_AUTH_TOKEN";

  ## Or if you have a signing key for a given Cachix cache:
  # cachix.my-cache.signingKey = "CACHIX_SIGNING_KEY"

  ## Note that here, CACHIX_AUTH_TOKEN and CACHIX_SIGNING_KEY
  ## are the names of secret variables. They are set in
  ## GitHub's web interface.
}
