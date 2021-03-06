theory Prop11B
	imports n8_2 Geometry Prop10 Prop12 betweennesspreserved betweennotequal collinear4 collinear5 collinearorder collinearright congruenceflip congruencesymmetric congruencetransitive inequalitysymmetric notperp oppositesidesymmetric planeseparation pointreflectionisometry rightangleNC rightreverse samesidesymmetric
begin

theorem(in euclidean_geometry) Prop11B:
	assumes 
		"bet A C B"
		"\<not> col A B P"
	shows "\<exists> H. ang_right A C H \<and> oppo_side H A B P"
proof -
	obtain M where "\<not> col A B M \<and> same_side M P A B \<and> \<not> (ang_right A C M)" using notperp[OF `bet A C B` `\<not> col A B P`]  by  blast
	have "\<not> col A B M" using `\<not> col A B M \<and> same_side M P A B \<and> \<not> (ang_right A C M)` by blast
	have "A \<noteq> B" using betweennotequal[OF `bet A C B`] by blast
	obtain Q where "perp_at M Q A B Q" using Prop12[OF `A \<noteq> B` `\<not> col A B M`]  by  blast
	obtain E where "col M Q Q \<and> col A B Q \<and> col A B E \<and> ang_right E Q M" using perpat_f[OF `perp_at M Q A B Q`]  by  blast
	have "col A B Q" using `col M Q Q \<and> col A B Q \<and> col A B E \<and> ang_right E Q M` by blast
	have "ang_right E Q M" using `col M Q Q \<and> col A B Q \<and> col A B E \<and> ang_right E Q M` by blast
	have "\<not> (M = Q)"
	proof (rule ccontr)
		assume "\<not> (M \<noteq> Q)"
		hence "M = Q" by blast
		have "col A B Q" using `col A B Q` .
		have "col A B M" using `col A B Q` `M = Q` by blast
		have "\<not> col A B M" using `\<not> col A B M` .
		show "False" using `\<not> col A B M` `col A B M` by blast
	qed
	hence "M \<noteq> Q" by blast
	have "Q \<noteq> M" using inequalitysymmetric[OF `M \<noteq> Q`] .
	have "col A B C" using collinear_b `bet A C B` by blast
	have "col A B E" using `col M Q Q \<and> col A B Q \<and> col A B E \<and> ang_right E Q M` by blast
	have "col B A E" using collinearorder[OF `col A B E`] by blast
	have "col B A C" using collinearorder[OF `col A B C`] by blast
	have "B \<noteq> A" using inequalitysymmetric[OF `A \<noteq> B`] .
	have "\<not> (C = Q)"
	proof (rule ccontr)
		assume "\<not> (C \<noteq> Q)"
		hence "C = Q" by blast
		have "ang_right E C M" using `ang_right E Q M` `C = Q` by blast
		have "col A E C" using collinear4[OF `col B A E` `col B A C` `B \<noteq> A`] .
		have "col E C A" using collinearorder[OF `col A E C`] by blast
		have "A \<noteq> C" using betweennotequal[OF `bet A C B`] by blast
		have "ang_right A C M" using collinearright[OF `ang_right E C M` `col E C A` `A \<noteq> C`] .
		have "\<not> (ang_right A C M)" using `\<not> col A B M \<and> same_side M P A B \<and> \<not> (ang_right A C M)` by blast
		show "False" using `\<not> (ang_right A C M)` `ang_right A C M` by blast
	qed
	hence "C \<noteq> Q" by blast
	have "col A B E" using `col A B E` .
	have "col A B C" using `col A B C` .
	have "col A B Q" using `col A B Q` .
	have "col C Q E" using collinear5[OF `A \<noteq> B` `col A B C` `col A B Q` `col A B E`] .
	have "col E Q C" using collinearorder[OF `col C Q E`] by blast
	have "ang_right C Q M" using collinearright[OF `ang_right E Q M` `col E Q C` `C \<noteq> Q`] .
	have "Q \<noteq> C" using inequalitysymmetric[OF `C \<noteq> Q`] .
	obtain G where "bet Q G C \<and> seg_eq G Q G C" using Prop10[OF `Q \<noteq> C`]  by  blast
	have "bet Q G C" using `bet Q G C \<and> seg_eq G Q G C` by blast
	have "seg_eq G Q G C" using `bet Q G C \<and> seg_eq G Q G C` by blast
	have "\<not> (M = G)"
	proof (rule ccontr)
		assume "\<not> (M \<noteq> G)"
		hence "M = G" by blast
		have "bet Q M C" using `bet Q G C` `M = G` by blast
		have "col Q M C" using collinear_b `bet Q M C` by blast
		have "col A B Q" using `col A B Q` .
		have "col A B C" using `col A B C` .
		have "col B Q C" using collinear4[OF `col A B Q` `col A B C` `A \<noteq> B`] .
		have "col Q C M" using collinearorder[OF `col Q M C`] by blast
		have "col Q C B" using collinearorder[OF `col B Q C`] by blast
		have "Q \<noteq> C" using betweennotequal[OF `bet Q G C`] by blast
		have "col C M B" using collinear4[OF `col Q C M` `col Q C B` `Q \<noteq> C`] .
		have "col C B M" using collinearorder[OF `col C M B`] by blast
		have "col C B A" using collinearorder[OF `col A B C`] by blast
		have "C \<noteq> B" using betweennotequal[OF `bet A C B`] by blast
		have "col B M A" using collinear4[OF `col C B M` `col C B A` `C \<noteq> B`] .
		have "col A B M" using collinearorder[OF `col B M A`] by blast
		have "\<not> col A B M" using `\<not> col A B M` .
		show "False" using `\<not> col A B M` `col A B M` by blast
	qed
	hence "M \<noteq> G" by blast
	obtain H where "bet M G H \<and> seg_eq G H M G" using extensionE[OF `M \<noteq> G` `M \<noteq> G`]  by  blast
	have "bet M G H" using `bet M G H \<and> seg_eq G H M G` by blast
	have "seg_eq G H M G" using `bet M G H \<and> seg_eq G H M G` by blast
	have "seg_eq M G G H" using congruencesymmetric[OF `seg_eq G H M G`] .
	have "midpoint M G H" using midpoint_b[OF `bet M G H` `seg_eq M G G H`] .
	have "seg_eq Q G G C" using congruenceflip[OF `seg_eq G Q G C`] by blast
	have "midpoint Q G C" using midpoint_b[OF `bet Q G C` `seg_eq Q G G C`] .
	have "col Q G C" using collinear_b `bet Q G C \<and> seg_eq G Q G C` by blast
	have "col C Q G" using collinearorder[OF `col Q G C`] by blast
	have "Q \<noteq> G" using betweennotequal[OF `bet Q G C`] by blast
	have "G \<noteq> Q" using inequalitysymmetric[OF `Q \<noteq> G`] .
	have "ang_right G Q M" using collinearright[OF `ang_right C Q M` `col C Q G` `G \<noteq> Q`] .
	have "midpoint Q G C" using `midpoint Q G C` .
	have "midpoint M G H" using `midpoint M G H` .
	obtain J where "bet M Q J \<and> seg_eq Q J M Q" using extensionE[OF `M \<noteq> Q` `M \<noteq> Q`]  by  blast
	have "bet M Q J" using `bet M Q J \<and> seg_eq Q J M Q` by blast
	have "seg_eq Q J M Q" using `bet M Q J \<and> seg_eq Q J M Q` by blast
	have "seg_eq M Q Q J" using congruencesymmetric[OF `seg_eq Q J M Q`] .
	have "ang_right M Q G" using n8_2[OF `ang_right G Q M`] .
	have "seg_eq M G J G" using rightreverse[OF `ang_right M Q G` `bet M Q J` `seg_eq M Q Q J`] .
	have "bet J Q M" using betweennesssymmetryE[OF `bet M Q J`] .
	have "seg_eq J Q M Q" using congruenceflip[OF `seg_eq Q J M Q`] by blast
	have "seg_eq J G M G" using congruencesymmetric[OF `seg_eq M G J G`] .
	have "ang_right J Q G" using rightangle_b[OF `bet J Q M` `seg_eq J Q M Q` `seg_eq J G M G` `Q \<noteq> G`] .
	have "\<not> (J = G)"
	proof (rule ccontr)
		assume "\<not> (J \<noteq> G)"
		hence "J = G" by blast
		have "col J Q G" using collinear_b `J = G` by blast
		have "\<not> col J Q G" using rightangleNC[OF `ang_right J Q G`] .
		show "False" using `\<not> col J Q G` `col J Q G` by blast
	qed
	hence "J \<noteq> G" by blast
	obtain K where "bet J G K \<and> seg_eq G K J G" using extensionE[OF `J \<noteq> G` `J \<noteq> G`]  by  blast
	have "bet J G K" using `bet J G K \<and> seg_eq G K J G` by blast
	have "seg_eq G K J G" using `bet J G K \<and> seg_eq G K J G` by blast
	have "seg_eq J G G K" using congruencesymmetric[OF `seg_eq G K J G`] .
	have "midpoint J G K" using midpoint_b[OF `bet J G K` `seg_eq J G G K`] .
	have "seg_eq M Q H C" using pointreflectionisometry[OF `midpoint M G H` `midpoint Q G C`] .
	have "seg_eq Q J C K" using pointreflectionisometry[OF `midpoint Q G C` `midpoint J G K`] .
	have "seg_eq M J H K" using pointreflectionisometry[OF `midpoint M G H` `midpoint J G K`] .
	have "bet H C K" using betweennesspreserved[OF `seg_eq M Q H C` `seg_eq M J H K` `seg_eq Q J C K` `bet M Q J`] .
	have "seg_eq H G G M" using congruenceflip[OF `seg_eq G H M G`] by blast
	have "seg_eq M G J G" using `seg_eq M G J G` .
	have "seg_eq G M J G" using congruenceflip[OF `seg_eq M G J G`] by blast
	have "seg_eq H G J G" using congruencetransitive[OF `seg_eq H G G M` `seg_eq G M J G`] .
	have "seg_eq J G G K" using congruencesymmetric[OF `seg_eq G K J G`] .
	have "seg_eq H G G K" using congruencetransitive[OF `seg_eq H G J G` `seg_eq J G G K`] .
	have "seg_eq H G K G" using congruenceflip[OF `seg_eq H G G K`] by blast
	have "G \<noteq> C" using betweennotequal[OF `bet Q G C`] by blast
	have "bet H C K" using `bet H C K` .
	have "seg_eq H C M Q" using congruencesymmetric[OF `seg_eq M Q H C`] .
	have "seg_eq M Q Q J" using congruencesymmetric[OF `seg_eq Q J M Q`] .
	have "seg_eq H C Q J" using congruencetransitive[OF `seg_eq H C M Q` `seg_eq M Q Q J`] .
	have "seg_eq Q J C K" using `seg_eq Q J C K` .
	have "seg_eq H C C K" using congruencetransitive[OF `seg_eq H C Q J` `seg_eq Q J C K`] .
	have "seg_eq H C K C" using congruenceflip[OF `seg_eq H C C K`] by blast
	have "seg_eq H G K G" using `seg_eq H G K G` .
	have "G \<noteq> C" using betweennotequal[OF `bet Q G C`] by blast
	have "C \<noteq> G" using inequalitysymmetric[OF `G \<noteq> C`] .
	have "ang_right H C G" using rightangle_b[OF `bet H C K` `seg_eq H C K C` `seg_eq H G K G` `C \<noteq> G`] .
	have "ang_right G C H" using n8_2[OF `ang_right H C G`] .
	have "col A B Q" using `col A B Q` .
	have "col A B C" using `col A B C` .
	have "A = A" using equalityreflexiveE.
	have "col A B A" using collinear_b `A = A` by blast
	have "col Q C A" using collinear5[OF `A \<noteq> B` `col A B Q` `col A B C` `col A B A`] .
	have "col Q C G" using collinearorder[OF `col C Q G`] by blast
	have "col C A G" using collinear4[OF `col Q C A` `col Q C G` `Q \<noteq> C`] .
	have "ang_right G C H" using `ang_right G C H` .
	have "col G C A" using collinearorder[OF `col C A G`] by blast
	have "A \<noteq> C" using betweennotequal[OF `bet A C B`] by blast
	have "ang_right A C H" using collinearright[OF `ang_right G C H` `col G C A` `A \<noteq> C`] .
	have "col C A B" using collinearorder[OF `col A B C`] by blast
	have "C \<noteq> A" using inequalitysymmetric[OF `A \<noteq> C`] .
	have "col A G B" using collinear4[OF `col C A G` `col C A B` `C \<noteq> A`] .
	have "col A B G" using collinearorder[OF `col A G B`] by blast
	have "same_side M P A B" using `\<not> col A B M \<and> same_side M P A B \<and> \<not> (ang_right A C M)` by blast
	have "same_side P M A B" using samesidesymmetric[OF `same_side M P A B`] by blast
	have "oppo_side M A B H" using oppositeside_b[OF `bet M G H` `col A B G` `\<not> col A B M`] .
	have "oppo_side P A B H" using planeseparation[OF `same_side P M A B` `oppo_side M A B H`] .
	have "oppo_side H A B P" using oppositesidesymmetric[OF `oppo_side P A B H`] .
	have "ang_right A C H \<and> oppo_side H A B P" using `ang_right A C H` `oppo_side H A B P` by blast
	thus ?thesis by blast
qed

end