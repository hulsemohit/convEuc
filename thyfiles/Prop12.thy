theory Prop12
	imports n3_6b Geometry Prop10 betweennotequal collinear4 collinearorder congruenceflip congruencesymmetric congruencetransitive inequalitysymmetric
begin

theorem(in euclidean_geometry) Prop12:
	assumes 
		"A \<noteq> B"
		"\<not> col A B C"
	shows "\<exists> M. perp_at C M A B M"
proof -
	have "\<not> (B = C)"
	proof (rule ccontr)
		assume "\<not> (B \<noteq> C)"
		hence "B = C" by blast
		have "col A B C" using collinear_b `B = C` by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "B \<noteq> C" by blast
	have "C \<noteq> B" using inequalitysymmetric[OF `B \<noteq> C`] .
	obtain E where "bet C B E \<and> seg_eq B E C B" using extensionE[OF `C \<noteq> B` `C \<noteq> B`]  by  blast
	have "bet C B E" using `bet C B E \<and> seg_eq B E C B` by blast
	have "C \<noteq> E" using betweennotequal[OF `bet C B E`] by blast
	have "E \<noteq> C" using inequalitysymmetric[OF `C \<noteq> E`] .
	obtain F where "bet E C F \<and> seg_eq C F E C" using extensionE[OF `E \<noteq> C` `E \<noteq> C`]  by  blast
	have "seg_eq C F E C" using `bet E C F \<and> seg_eq C F E C` by blast
	have "seg_eq E C C E" using equalityreverseE.
	have "seg_eq C E C E" using congruencereflexiveE.
	have "seg_eq C F C E" using congruencetransitive[OF `seg_eq C F E C` `seg_eq E C C E`] .
	have "bet E B C" using betweennesssymmetryE[OF `bet C B E`] .
	have "bet E C F" using `bet E C F \<and> seg_eq C F E C` by blast
	have "bet E B F" using n3_6b[OF `bet E B C` `bet E C F`] .
	obtain K where "circle K C C E" using circle_f[OF `C \<noteq> E`]  by  blast
	have "circle K C C E \<and> cir_in B K" using inside_b[OF `circle K C C E` `bet E C F` `seg_eq C F C E` `seg_eq C E C E` `bet E B F`] .
	have "cir_in B K" using `circle K C C E \<and> cir_in B K` by blast
	obtain P Q where "col A B P \<and> col A B Q \<and> cir_on P K \<and> cir_on Q K \<and> bet P B Q" using line_circleE[OF `circle K C C E` `cir_in B K` `A \<noteq> B`]  by  blast
	have "col A B Q" using `col A B P \<and> col A B Q \<and> cir_on P K \<and> cir_on Q K \<and> bet P B Q` by blast
	have "cir_on P K" using `col A B P \<and> col A B Q \<and> cir_on P K \<and> cir_on Q K \<and> bet P B Q` by blast
	have "cir_on Q K" using `col A B P \<and> col A B Q \<and> cir_on P K \<and> cir_on Q K \<and> bet P B Q` by blast
	have "bet P B Q" using `col A B P \<and> col A B Q \<and> cir_on P K \<and> cir_on Q K \<and> bet P B Q` by blast
	have "seg_eq C P C E" using on_f[OF `circle K C C E` `cir_on P K`] by blast
	have "seg_eq C Q C E" using on_f[OF `circle K C C E` `cir_on Q K`] by blast
	have "seg_eq C E C Q" using congruencesymmetric[OF `seg_eq C Q C E`] .
	have "seg_eq C P C Q" using congruencetransitive[OF `seg_eq C P C E` `seg_eq C E C Q`] .
	have "seg_eq P C Q C" using congruenceflip[OF `seg_eq C P C Q`] by blast
	have "P \<noteq> Q" using betweennotequal[OF `bet P B Q`] by blast
	obtain M where "bet P M Q \<and> seg_eq M P M Q" using Prop10[OF `P \<noteq> Q`]  by  blast
	have "bet P M Q" using `bet P M Q \<and> seg_eq M P M Q` by blast
	have "seg_eq M P M Q" using `bet P M Q \<and> seg_eq M P M Q` by blast
	have "seg_eq P M Q M" using congruenceflip[OF `seg_eq M P M Q`] by blast
	have "col P M Q" using collinear_b `bet P M Q \<and> seg_eq M P M Q` by blast
	have "col P B Q" using collinear_b `col A B P \<and> col A B Q \<and> cir_on P K \<and> cir_on Q K \<and> bet P B Q` by blast
	have "col P Q B" using collinearorder[OF `col P B Q`] by blast
	have "col P Q M" using collinearorder[OF `col P M Q`] by blast
	have "P \<noteq> Q" using `P \<noteq> Q` .
	have "col Q B M" using collinear4[OF `col P Q B` `col P Q M` `P \<noteq> Q`] .
	have "col Q B A" using collinearorder[OF `col A B Q`] by blast
	have "B \<noteq> Q" using betweennotequal[OF `bet P B Q`] by blast
	have "Q \<noteq> B" using inequalitysymmetric[OF `B \<noteq> Q`] .
	have "col B M A" using collinear4[OF `col Q B M` `col Q B A` `Q \<noteq> B`] .
	have "col A B M" using collinearorder[OF `col B M A`] by blast
	have "\<not> (M = C)"
	proof (rule ccontr)
		assume "\<not> (M \<noteq> C)"
		hence "M = C" by blast
		have "col A B M" using `col A B M` .
		have "col A B C" using `col A B M` `M = C` by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "M \<noteq> C" by blast
	have "ang_right P M C" using rightangle_b[OF `bet P M Q` `seg_eq P M Q M` `seg_eq P C Q C` `M \<noteq> C`] .
	have "M = M" using equalityreflexiveE.
	have "col C M M" using collinear_b `M = M` by blast
	have "col A B P" using `col A B P \<and> col A B Q \<and> cir_on P K \<and> cir_on Q K \<and> bet P B Q` by blast
	have "col A B Q" using `col A B Q` .
	have "col A B M" using `col A B M` .
	have "perp_at C M A B M" using perpat_b[OF `col C M M` `col A B M` `col A B P` `ang_right P M C`] .
	thus ?thesis by blast
qed

end