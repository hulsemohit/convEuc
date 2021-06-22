theory layoff
	imports Axioms Definitions Theorems
begin

theorem layoff:
	assumes: `axioms`
		"A \<noteq> B"
		"C \<noteq> D"
	shows: "\<exists> P. ray_on A B P \<and> seg_eq A P C D"
proof -
	have "\<not> (B = A)"
	proof (rule ccontr)
		assume "B = A"
		have "A = B" using equalitysymmetric[OF `axioms` `B = A`] .
		show "False" using `A = B` `A \<noteq> B` by blast
	qed
	hence "B \<noteq> A" by blast
	obtain E where "bet B A E \<and> seg_eq A E C D" using extensionE[OF `axioms` `B \<noteq> A` `C \<noteq> D`]  by  blast
	have "bet B A E" using `bet B A E \<and> seg_eq A E C D` by blast
	have "bet E A B" using betweennesssymmetryE[OF `axioms` `bet B A E`] .
	have "E \<noteq> A" using betweennotequal[OF `axioms` `bet E A B`] by blast
	have "bet E A B" using betweennesssymmetryE[OF `axioms` `bet B A E`] .
	obtain P where "bet E A P \<and> seg_eq A P C D" using extensionE[OF `axioms` `E \<noteq> A` `C \<noteq> D`]  by  blast
	have "bet E A P" using `bet E A P \<and> seg_eq A P C D` by blast
	have "seg_eq A P C D" using `bet E A P \<and> seg_eq A P C D` by blast
	have "ray_on A B P" sorry
	have "ray_on A B P \<and> seg_eq A P C D" using `ray_on A B P` `bet E A P \<and> seg_eq A P C D` by blast
	thus ?thesis by blast
qed

end