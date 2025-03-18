#!/usr/bin/env bash

# Extract the required passes 

coqc SimplExpr_extraction.v -R ../../_build/default/theories Rocqet -I ../../_build/default/src -R ../../_build/default/casestudies/compcert/lib Rocqet.CompCert.lib -R ../../_build/default/casestudies/compcert Rocqet.CompCert

coqc Cshmgen_extraction.v -R ../../_build/default/theories Rocqet -I ../../_build/default/src -R ../../_build/default/casestudies/compcert/lib Rocqet.CompCert.lib -R ../../_build/default/casestudies/compcert Rocqet.CompCert

coqc Cminorgen_extraction.v -R ../../_build/default/theories Rocqet -I ../../_build/default/src -R ../../_build/default/casestudies/compcert/lib Rocqet.CompCert.lib -R ../../_build/default/casestudies/compcert Rocqet.CompCert

coqc RTLgen_extraction.v -R ../../_build/default/theories Rocqet -I ../../_build/default/src -R ../../_build/default/casestudies/compcert/lib Rocqet.CompCert.lib -R ../../_build/default/casestudies/compcert Rocqet.CompCert

coqc Linearize_extraction.v -R ../../_build/default/theories Rocqet -I ../../_build/default/src -R ../../_build/default/casestudies/compcert/lib Rocqet.CompCert.lib -R ../../_build/default/casestudies/compcert Rocqet.CompCert

coqc Stacking_extraction.v -R ../../_build/default/theories Rocqet -I ../../_build/default/src -R ../../_build/default/casestudies/compcert/lib Rocqet.CompCert.lib -R ../../_build/default/casestudies/compcert Rocqet.CompCert


# Strip out pass from Rocqet composition

cd extraction

./strip_rocqet_internal.sh SimplExpr_extraction.ml SimplExpr SimplExpr.ml
./strip_rocqet_internal.sh Cshmgen_extraction.ml Cshmgen Cshmgen.ml
./strip_rocqet_internal.sh Cminorgen_extraction.ml Cminorgen Cminorgen.ml
./strip_rocqet_internal.sh RTLgen_extraction.ml RTLgen RTLgen.ml
./strip_rocqet_internal.sh Linearize_extraction.ml Linearize Linearize.ml
./strip_rocqet_internal.sh Stacking_extraction.ml Stacking Stacking.ml


# Link extracted passes to CompCert

echo "Linking Passes to CompCert"

./link_passes.sh ./extracted ../../../Rocqet_CompCert/extraction
