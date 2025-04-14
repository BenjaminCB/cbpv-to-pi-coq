self: super:

{
  # Override coqPackages in scope
  coqPackages = super.coqPackages.overrideScope' (final: prev: {
    vscoq =
      prev.vscoq.overrideAttrs (old: rec {

        # The new version you want:
        version = "2.2.5";

        # Point “location” to rocq-prover instead of coq-community
        location = {
          domain = "github.com";
          owner  = "rocq-prover";
          repo   = "vscoq";
        };

        # Re-compute the ‘fetched’ attribute for the new version.
        # We call old.fetch (the metaFetch function you had) with
        # updated "release" info and the updated location.
        fetched = old.fetch {
          release."2.2.5".rev    = "v2.2.5";
          release."2.2.5".sha256 = "<REPLACE-WITH-CORRECT-SHA256>";
          inherit location;
        };
      });
  });
}
