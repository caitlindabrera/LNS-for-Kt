%.vo : %.v
	coqc $*.v


# NOTE: some of these also depend on Coq files in ../general.
# Build those by "make general" in the current directory.

general :
	cd .. && make general && cd tense-lns

require_general.vo : require_general.v

LNS.vo : require_general.vo LNS.v

structural_equivalence.vo : require_general.vo LNS.vo structural_equivalence.v

merge.vo : require_general.vo LNS.vo structural_equivalence.vo merge.v

size.vo : LNS.vo size.v

structural_defs.vo : require_general.vo LNS.vo structural_defs.v

structural_weak.vo : structural_defs.vo structural_weak.v

structural_cont.vo : structural_defs.vo structural_cont.v

require_structural.vo : structural_defs.vo structural_weak.vo structural_cont.vo structural_equivalence.vo merge.vo size.vo require_structural.v

rules_prop.vo : require_general.vo LNS.vo require_structural.vo rules_prop.v

rules_b1l.vo : require_general.vo LNS.vo require_structural.vo rules_b1l.v

rules_b2l.vo : require_general.vo LNS.vo require_structural.vo rules_b2l.v

rules_b1r.vo : require_general.vo LNS.vo require_structural.vo rules_b1r.v

rules_b2r.vo : require_general.vo LNS.vo require_structural.vo rules_b2r.v

rules_EW.vo : require_general.vo LNS.vo require_structural.vo rules_EW.v

require_rules.vo : require_general.vo LNS.vo require_structural.vo rules_prop.vo rules_b1l.vo rules_b2l.vo rules_b1r.vo rules_b2r.vo rules_EW.vo require_rules.v

LNSKt_calculus.vo : require_general.vo LNS.vo require_rules.vo LNSKt_calculus.v

ind_lex.vo : ind_lex.v

principal.vo : require_general.vo require_rules.vo size.vo principal.v

Lemma_Sixteen_setup.vo : LNSKt_calculus.vo require_structural.vo principal.vo ind_lex.vo Lemma_Sixteen_setup.v

Lemma_Sixteen_SR_wb_fwd.vo : Lemma_Sixteen_setup.vo Lemma_Sixteen_SR_wb_fwd.v

Lemma_Sixteen_SR_wb_bac.vo : Lemma_Sixteen_setup.vo Lemma_Sixteen_SR_wb_fwd.vo Lemma_Sixteen_SR_wb_bac.v

Lemma_Sixteen_SR_wb.vo : Lemma_Sixteen_SR_wb_fwd.vo Lemma_Sixteen_SR_wb_bac.vo Lemma_Sixteen_SR_wb.v

Lemma_Sixteen_SR_bb_fwd.vo : Lemma_Sixteen_setup.vo Lemma_Sixteen_SR_wb.vo Lemma_Sixteen_SR_bb_fwd.v

Lemma_Sixteen_SR_bb_bac.vo : Lemma_Sixteen_setup.vo Lemma_Sixteen_SR_wb.vo Lemma_Sixteen_SR_bb_fwd.vo Lemma_Sixteen_SR_bb_bac.v

Lemma_Sixteen_SR_bb.vo : Lemma_Sixteen_setup.vo Lemma_Sixteen_SR_bb_fwd.vo Lemma_Sixteen_SR_bb_bac.vo Lemma_Sixteen_SR_bb.v

Lemma_Sixteen_SR_p.vo : Lemma_Sixteen_setup.vo Lemma_Sixteen_SR_wb.vo Lemma_Sixteen_SR_bb.vo Lemma_Sixteen_SR_p.v

Lemma_Sixteen_SL.vo : Lemma_Sixteen_setup.vo Lemma_Sixteen_SR_p.vo Lemma_Sixteen_SL.v

Lemma_Sixteen.vo : Lemma_Sixteen_setup.vo Lemma_Sixteen_SR_wb.vo Lemma_Sixteen_SR_bb.vo Lemma_Sixteen_SR_p.vo Lemma_Sixteen_SL.vo Lemma_Sixteen.v

cut_setup.vo : require_general.vo require_structural.vo cut_setup.v

cut.vo : cut_setup.vo Lemma_Sixteen.vo cut.v

cut_extraction_theorem.vo : cut.vo cut_extraction_theorem.v

cut_extraction_example_pre.vo : cut.vo cut_extraction_example_pre.v

cut_extraction_example.vo : cut_extraction_example_pre.vo cut_extraction_example.v


cut_thm : general cut_extraction_theorem.vo

cut_ex : general cut_extraction_example.vo





clean_haskell :
	rm *.hs~ CMorphisms.hs ContractedT.hs CRelationClasses.hs Cut.hs Cut_extraction_example_pre.hs Datatypes.hs Dd_fc.hs DdT.hs EqdepFacts.hs Gen.hs Gen_seq.hs Gen_tacs.hs GenT.hs InclT.hs Ind_lex.hs Lemma_Sixteen.hs Lemma_Sixteen_setup.hs Lemma_Sixteen_SL.hs Lemma_Sixteen_SR_bb.hs Lemma_Sixteen_SR_bb_bac.hs Lemma_Sixteen_SR_bb_fwd.hs Lemma_Sixteen_SR_p.hs  Lemma_Sixteen_SR_wb.hs Lemma_Sixteen_SR_wb_bac.hs Lemma_Sixteen_SR_wb_fwd.hs List.hs List_lemmasT.hs LNS.hs LNSKt_calculus.hs Logic.hs Merge.hs Nat.hs  PeanoNat.hs Principal.hs Rules_b1l.hs Rules_b1r.hs Rules_b2l.hs Rules_b2r.hs Rules_EW.hs Rules_prop.hs Size.hs Specif.hs Structural_cont.hs Structural_defs.hs Structural_equivalence.hs SwappedT.hs WeakenedT.hs Wf.hs

clean_coq :
	rm -rf  *.vo *.glob *.v~

clean_general :
	cd ../general && rm *.vo *.glob && cd ../tense-lns

clean_tense : clean_coq clean_haskell

clean_all : clean_general clean_tense

clean_stray :
	rm *~

clean_win : 
	del /f *.vo *.glob
