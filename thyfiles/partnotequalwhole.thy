theory partnotequalwhole
	imports Axioms Definitions Theorems
begin

theorem partnotequalwhole:
	assumes: `axioms`
		"bet A B C"
	shows: "\<not> (seg_eq A B A C)"
proof -
	have "A \<noteq> B" using betweennotequal[OF `axioms` `bet A B C`] by blast
	have "B \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> B`] .
	obtain D where "bet B A D \<and> seg_eq A D B A" using extensionE[OF `axioms` `B \<noteq> A` `B \<noteq> A`] by blast
	have "bet B A D" using `bet B A D \<and> seg_eq A D B A` by blast
	have "bet D A B" using betweennesssymmetryE[OF `axioms` `bet B A D`] .
	have "bet D A C" using n3_7b[OF `axioms` `bet D A B` `bet A B C`] .
	have "bet A B C" using `bet A B C` .
	have "B \<noteq> C" using betweennotequal[OF `axioms` `bet A B C`] by blast
	have "\<not> (seg_eq A B A C)"
	proof (rule ccontr)
		assume "seg_eq A B A C"
		have "B = C" using extensionunique[OF `axioms` `bet D A B` `bet D A C` `seg_eq A B A C`] .
		show "False" using `B = C` `B \<noteq> C` by blast
	qed
	hence "\<not> (seg_eq A B A C)" by blast
	thus ?thesis by blast
qed

end