theory trichotomy1
	imports Geometry betweennotequal congruencetransitive inequalitysymmetric lessthancongruence outerconnectivity
begin

theorem(in euclidean_geometry) trichotomy1:
	assumes 
		"\<not> (seg_lt A B C D)"
		"\<not> (seg_lt C D A B)"
		"A \<noteq> B"
		"C \<noteq> D"
	shows "seg_eq A B C D"
proof -
	have "B \<noteq> A" using inequalitysymmetric[OF `A \<noteq> B`] .
	obtain P where "bet B A P \<and> seg_eq A P A B" using extensionE[OF `B \<noteq> A` `A \<noteq> B`]  by  blast
	have "bet B A P" using `bet B A P \<and> seg_eq A P A B` by blast
	have "bet P A B" using betweennesssymmetryE[OF `bet B A P`] .
	have "A \<noteq> P" using betweennotequal[OF `bet B A P`] by blast
	have "P \<noteq> A" using inequalitysymmetric[OF `A \<noteq> P`] .
	obtain E where "bet P A E \<and> seg_eq A E C D" using extensionE[OF `P \<noteq> A` `C \<noteq> D`]  by  blast
	have "bet P A E" using `bet P A E \<and> seg_eq A E C D` by blast
	have "seg_eq A E C D" using `bet P A E \<and> seg_eq A E C D` by blast
	have "\<not> (bet A B E)"
	proof (rule ccontr)
		assume "\<not> (\<not> (bet A B E))"
hence "bet A B E" by blast
		have "seg_eq A B A B" using congruencereflexiveE.
		have "seg_lt A B A E" using lessthan_b[OF `bet A B E` `seg_eq A B A B`] .
		have "seg_lt A B C D" using lessthancongruence[OF `seg_lt A B A E` `seg_eq A E C D`] .
		show "False" using `seg_lt A B C D` `\<not> (seg_lt A B C D)` by blast
	qed
	hence "\<not> (bet A B E)" by blast
	have "\<not> (bet A E B)"
	proof (rule ccontr)
		assume "\<not> (\<not> (bet A E B))"
hence "bet A E B" by blast
		have "seg_lt C D A B" using lessthan_b[OF `bet A E B` `seg_eq A E C D`] .
		show "False" using `seg_lt C D A B` `\<not> (seg_lt C D A B)` by blast
	qed
	hence "\<not> (bet A E B)" by blast
	have "E = B" using outerconnectivity[OF `bet P A E` `bet P A B` `\<not> (bet A E B)` `\<not> (bet A B E)`] .
	have "seg_eq A B A B" using congruencereflexiveE.
	have "seg_eq A B A E" using `seg_eq A B A B` `E = B` by blast
	have "seg_eq A E C D" using `seg_eq A E C D` .
	have "seg_eq A B C D" using congruencetransitive[OF `seg_eq A B A E` `seg_eq A E C D`] .
	thus ?thesis by blast
qed

end