theory ray
	imports n3_7b Geometry betweennotequal congruencesymmetric congruencetransitive extensionunique inequalitysymmetric lessthancongruence ray2
begin

theorem ray:
	assumes "axioms"
		"ray_on A B P"
		"P \<noteq> B"
		"\<not> (bet A P B)"
	shows "bet A B P"
proof -
	have "A \<noteq> B" using ray2[OF `axioms` `ray_on A B P`] .
	obtain E where "bet E A P \<and> bet E A B" using ray_f[OF `axioms` `ray_on A B P`]  by  blast
	have "bet E A P" using `bet E A P \<and> bet E A B` by blast
	have "bet E A B" using `bet E A P \<and> bet E A B` by blast
	have "A \<noteq> P" using betweennotequal[OF `axioms` `bet E A P`] by blast
	obtain D where "bet A B D \<and> seg_eq B D A P" using extensionE[OF `axioms` `A \<noteq> B` `A \<noteq> P`]  by  blast
	have "bet A B D" using `bet A B D \<and> seg_eq B D A P` by blast
	have "seg_eq B D A P" using `bet A B D \<and> seg_eq B D A P` by blast
	have "seg_eq D B B D" using equalityreverseE[OF `axioms`] .
	have "seg_eq D B A P" using congruencetransitive[OF `axioms` `seg_eq D B B D` `seg_eq B D A P`] .
	have "bet D B A" using betweennesssymmetryE[OF `axioms` `bet A B D`] .
	have "seg_lt A P D A" using lessthan_b[OF `axioms` `bet D B A` `seg_eq D B A P`] .
	have "seg_eq D A A D" using equalityreverseE[OF `axioms`] .
	have "seg_lt A P A D" using lessthancongruence[OF `axioms` `seg_lt A P D A` `seg_eq D A A D`] .
	obtain F where "bet A F D \<and> seg_eq A F A P" using lessthan_f[OF `axioms` `seg_lt A P A D`]  by  blast
	have "bet E A P" using `bet E A P` .
	have "bet A B D" using `bet A B D` .
	have "bet E A D" using n3_7b[OF `axioms` `bet E A B` `bet A B D`] .
	have "bet A F D" using `bet A F D \<and> seg_eq A F A P` by blast
	have "bet E A F" using innertransitivityE[OF `axioms` `bet E A D` `bet A F D`] .
	have "seg_eq A F A P" using `bet A F D \<and> seg_eq A F A P` by blast
	have "seg_eq A P A F" using congruencesymmetric[OF `axioms` `seg_eq A F A P`] .
	have "P = F" using extensionunique[OF `axioms` `bet E A P` `bet E A F` `seg_eq A P A F`] .
	have "bet A P D" using `bet A F D` `P = F` by blast
	have "\<not> (bet A P B)" using `\<not> (bet A P B)` .
	have "\<not> (\<not> (bet A B P))"
	proof (rule ccontr)
		assume "\<not> (\<not> (\<not> (bet A B P)))"
hence "\<not> (bet A B P)" by blast
		have "B = P" using connectivityE[OF `axioms` `bet A B D` `bet A P D` `\<not> (bet A B P)` `\<not> (bet A P B)`] .
		have "B \<noteq> P" using inequalitysymmetric[OF `axioms` `P \<noteq> B`] .
		show "False" using `B \<noteq> P` `B = P` by blast
	qed
	hence "bet A B P" by blast
	thus ?thesis by blast
qed

end