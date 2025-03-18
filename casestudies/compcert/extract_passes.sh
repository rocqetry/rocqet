#!/usr/bin/env bash

# Extract the required passes

coqc SimplExpr_extraction.v -R ../../_build/default/theories Rocqet -I ../../_build/default/src -R ../../_build/default/casestudies/compcert/lib Rocqet.CompCert.lib -R ../../_build/default/casestudies/compcert Rocqet.CompCert

coqc Cshmgen_extraction.v -R ../../_build/default/theories Rocqet -I ../../_build/default/src -R ../../_build/default/casestudies/compcert/lib Rocqet.CompCert.lib -R ../../_build/default/casestudies/compcert Rocqet.CompCert

coqc Cminorgen_extraction.v -R ../../_build/default/theories Rocqet -I ../../_build/default/src -R ../../_build/default/casestudies/compcert/lib Rocqet.CompCert.lib -R ../../_build/default/casestudies/compcert Rocqet.CompCert

coqc RTLgen_extraction.v -R ../../_build/default/theories Rocqet -I ../../_build/default/src -R ../../_build/default/casestudies/compcert/lib Rocqet.CompCert.lib -R ../../_build/default/casestudies/compcert Rocqet.CompCert

coqc Linearize_extraction.v -R ../../_build/default/theories Rocqet -I ../../_build/default/src -R ../../_build/default/casestudies/compcert/lib Rocqet.CompCert.lib -R ../../_build/default/casestudies/compcert Rocqet.CompCert

coqc Stacking_extraction.v -R ../../_build/default/theories Rocqet -I ../../_build/default/src -R ../../_build/default/casestudies/compcert/lib Rocqet.CompCert.lib -R ../../_build/default/casestudies/compcert Rocqet.CompCert


# Strip out pass from Rocqet composition

echo "Stripping Rocqet Internal Info"

./strip_rocqet_internal.sh ./extraction/SimplExpr_extraction.ml SimplExpr ./extraction/SimplExpr.ml
./strip_rocqet_internal.sh ./extraction/Cshmgen_extraction.ml Cshmgen ./extraction/Cshmgen.ml
./strip_rocqet_internal.sh ./extraction/Cminorgen_extraction.ml Cminorgen ./extraction/Cminorgen.ml
./strip_rocqet_internal.sh ./extraction/RTLgen_extraction.ml RTLgen ./extraction/RTLgen.ml
./strip_rocqet_internal.sh ./extraction/Linearize_extraction.ml Linearize ./extraction/Linearize.ml
./strip_rocqet_internal.sh ./extraction/Stacking_extraction.ml Stacking ./extraction/Stacking.ml


# Link extracted passes to CompCert

echo "Linking Passes to CompCert"

./link_passes.sh ./extracted ../../../Rocqet_CompCert/extraction
