theory Prop12
	imports Axioms Definitions Theorems
begin

theorem Prop12:
	assumes: `axioms`
		"A \<noteq> B"
		"\<not> col A B C"
	shows: "\<exists> M. perp_at C M A B M"
proof -
	have "\<not> (B = C)"
	proof (rule ccontr)
		assume "B = C"
		have "col A B C" using col_b `axioms` `B = C` by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "B \<noteq> C" by blast
	have "C \<noteq> B" using inequalitysymmetric[OF `axioms` `B \<noteq> C`] .
	obtain E where "bet C B E \<and> seg_eq B E C B" using extensionE[OF `axioms` `C \<noteq> B` `C \<noteq> B`]  by  blast
	have "bet C B E" using `bet C B E \<and> seg_eq B E C B` by blast
	have "C \<noteq> E" using betweennotequal[OF `axioms` `bet C B E`] by blast
	have "E \<noteq> C" using inequalitysymmetric[OF `axioms` `C \<noteq> E`] .
	obtain F where "bet E C F \<and> seg_eq C F E C" using extensionE[OF `axioms` `E \<noteq> C` `E \<noteq> C`]  by  blast
	have "seg_eq C F E C" using `bet E C F \<and> seg_eq C F E C` by blast
	have "seg_eq E C C E" using equalityreverseE[OF `axioms`] .
	have "seg_eq C E C E" using congruencereflexiveE[OF `axioms`] .
	have "seg_eq C F C E" using congruencetransitive[OF `axioms` `seg_eq C F E C` `seg_eq E C C E`] .
	have "bet E B C" using betweennesssymmetryE[OF `axioms` `bet C B E`] .
	have "bet E C F" using `bet E C F \<and> seg_eq C F E C` by blast
	have "bet E B F" using n3_6b[OF `axioms` `bet E B C` `bet E C F`] .
	obtain K where "circle K C C E" sorry
	have "circle K C C E \<and> cir_in B K" sorry
	have "cir_in B K" using `circle K C C E \<and> cir_in B K` by blast
	obtain P Q where "col A B P \<and> col A B Q \<and> cir_on P K \<and> cir_on Q K \<and> bet P B Q" using line-circleE[OF `axioms` `circle K C C E` `cir_in B K` `A \<noteq> B`]  by  blast
	have "col A B Q" using `col A B P \<and> col A B Q \<and> cir_on P K \<and> cir_on Q K \<and> bet P B Q` by blast
	have "cir_on P K" using `col A B P \<and> col A B Q \<and> cir_on P K \<and> cir_on Q K \<and> bet P B Q` by blast
	have "cir_on Q K" using `col A B P \<and> col A B Q \<and> cir_on P K \<and> cir_on Q K \<and> bet P B Q` by blast
	have "bet P B Q" using `col A B P \<and> col A B Q \<and> cir_on P K \<and> cir_on Q K \<and> bet P B Q` by blast
	have "seg_eq C P C E" sorry
	have "seg_eq C Q C E" sorry
	have "seg_eq C E C Q" using congruencesymmetric[OF `axioms` `seg_eq C Q C E`] .
	have "seg_eq C P C Q" using congruencetransitive[OF `axioms` `seg_eq C P C E` `seg_eq C E C Q`] .
	have "seg_eq P C Q C" using congruenceflip[OF `axioms` `seg_eq C P C Q`] by blast
	have "P \<noteq> Q" using betweennotequal[OF `axioms` `bet P B Q`] by blast
	obtain M where "bet P M Q \<and> seg_eq M P M Q" using Prop10[OF `axioms` `P \<noteq> Q`]  by  blast
	have "bet P M Q" using `bet P M Q \<and> seg_eq M P M Q` by blast
	have "seg_eq M P M Q" using `bet P M Q \<and> seg_eq M P M Q` by blast
	have "seg_eq P M Q M" using congruenceflip[OF `axioms` `seg_eq M P M Q`] by blast
	have "col P M Q" using col_b `axioms` `bet P M Q \<and> seg_eq M P M Q` by blast
	have "col P B Q" using col_b `axioms` `col A B P \<and> col A B Q \<and> cir_on P K \<and> cir_on Q K \<and> bet P B Q` by blast
	have "col P Q B" using collinearorder[OF `axioms` `col P B Q`] by blast
	have "col P Q M" using collinearorder[OF `axioms` `col P M Q`] by blast
	have "P \<noteq> Q" using `P \<noteq> Q` .
	have "col Q B M" using collinear4[OF `axioms` `col P Q B` `col P Q M` `P \<noteq> Q`] .
	have "col Q B A" using collinearorder[OF `axioms` `col A B Q`] by blast
	have "B \<noteq> Q" using betweennotequal[OF `axioms` `bet P B Q`] by blast
	have "Q \<noteq> B" using inequalitysymmetric[OF `axioms` `B \<noteq> Q`] .
	have "col B M A" using collinear4[OF `axioms` `col Q B M` `col Q B A` `Q \<noteq> B`] .
	have "col A B M" using collinearorder[OF `axioms` `col B M A`] by blast
	have "\<not> (M = C)"
	proof (rule ccontr)
		assume "M = C"
		have "col A B M" using `col A B M` .
		have "col A B C" sorry
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "M \<noteq> C" by blast
	have "ang_right P M C" sorry
	have "M = M" using equalityreflexiveE[OF `axioms`] .
	have "col C M M" using col_b `axioms` `M = M` by blast
	have "col A B P" using `col A B P \<and> col A B Q \<and> cir_on P K \<and> cir_on Q K \<and> bet P B Q` by blast
	have "col A B Q" using `col A B Q` .
	have "col A B M" using `col A B M` .
	have "perp_at C M A B M" sorry
	thus ?thesis by blast
qed

end