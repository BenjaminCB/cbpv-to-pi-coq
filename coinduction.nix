{
  lib,
  mkCoqDerivation,
  coq,
  stdlib,
  version ? null,
}:

mkCoqDerivation {
  pname = "coinduction";
  owner = "damien-pous";
  inherit version;
  defaultVersion =
    with lib.versions;
    lib.switch coq.coq-version [
      {
        case = range "8.16" "8.18";
        out = "1.8";
      }
      {
        case = range "8.19" "8.21";
        out = "1.20";
      }
    ] null;
  release."1.8".sha256 = "1q96bsxclqx84xn5vkid501jkwlc1p6fhb8szrlrp82zglj58b0b";
  release."1.20".sha256 = "05fskx5x1qgaf9qv626m38y5izichzzqc7g2rglzrkygbskrrwsb";
  releaseRev = v: "v${v}";

  propagatedBuildInputs = [ stdlib ];

  # preBuild = "cd theories";

  installPhase = ''
    COQLIB=$out/lib/coq/${coq.coq-version}/
    mkdir -p $COQLIB/user-contrib/Coinduction
    cp -pR *.vo $COQLIB/user-contrib/Coninduction
  '';
}
