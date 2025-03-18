#!/usr/bin/env bash

coqc SimplExpr_extraction.v -R ../../_build/default/theories Rocqet -I ../../_build/default/src -R ../../_build/default/casestudies/compcert/lib Rocqet.CompCert.lib -R ../../_build/default/casestudies/compcert Rocqet.CompCert

coqc Cshmgen_extraction.v -R ../../_build/default/theories Rocqet -I ../../_build/default/src -R ../../_build/default/casestudies/compcert/lib Rocqet.CompCert.lib -R ../../_build/default/casestudies/compcert Rocqet.CompCert

coqc Cminorgen_extraction.v -R ../../_build/default/theories Rocqet -I ../../_build/default/src -R ../../_build/default/casestudies/compcert/lib Rocqet.CompCert.lib -R ../../_build/default/casestudies/compcert Rocqet.CompCert

coqc RTLgen_extraction.v -R ../../_build/default/theories Rocqet -I ../../_build/default/src -R ../../_build/default/casestudies/compcert/lib Rocqet.CompCert.lib -R ../../_build/default/casestudies/compcert Rocqet.CompCert

coqc Linearize_extraction.v -R ../../_build/default/theories Rocqet -I ../../_build/default/src -R ../../_build/default/casestudies/compcert/lib Rocqet.CompCert.lib -R ../../_build/default/casestudies/compcert Rocqet.CompCert

coqc Stacking_extraction.v -R ../../_build/default/theories Rocqet -I ../../_build/default/src -R ../../_build/default/casestudies/compcert/lib Rocqet.CompCert.lib -R ../../_build/default/casestudies/compcert Rocqet.CompCert
