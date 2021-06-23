theory ray4
	imports n3_7b Geometry equalitysymmetric
begin

theorem ray4:
	assumes "axioms"
		"bet A E B \<or> E = B \<or> bet A B E"
		"A \<noteq> B"
	shows "ray_on A B E"
proof -
	have "\<not> (B = A)"
	proof (rule ccontr)
		assume "\<not> (B \<noteq> A)"
		hence "B = A" by blast
		have "A = B" using equalitysymmetric[OF `axioms` `B = A`] .
		show "False" using `A = B` `A \<noteq> B` by blast
	qed
	hence "B \<noteq> A" by blast
	obtain J where "bet B A J \<and> seg_eq A J A B" using extensionE[OF `axioms` `B \<noteq> A` `A \<noteq> B`]  by  blast
	have "bet B A J" using `bet B A J \<and> seg_eq A J A B` by blast
	have "bet J A B" using betweennesssymmetryE[OF `axioms` `bet B A J`] .
	consider "bet A E B"|"E = B"|"bet A B E" using `bet A E B \<or> E = B \<or> bet A B E`  by blast
	hence "ray_on A B E"
	proof (cases)
		assume "bet A E B"
		have "bet J A B" using `bet J A B` .
		have "bet J A E" using innertransitivityE[OF `axioms` `bet J A B` `bet A E B`] .
		have "ray_on A B E" using ray_b[OF `axioms` `bet J A E` `bet J A B`] .
		thus ?thesis by blast
	next
		assume "E = B"
		have "bet J A B" using `bet J A B` .
		have "bet J A E" using `bet J A B` `E = B` by blast
		have "ray_on A B E" using ray_b[OF `axioms` `bet J A E` `bet J A B`] .
		thus ?thesis by blast
	next
		assume "bet A B E"
		have "bet J A B" using `bet J A B` .
		have "bet J A E" using n3_7b[OF `axioms` `bet J A B` `bet A B E`] .
		have "ray_on A B E" using ray_b[OF `axioms` `bet J A E` `bet J A B`] .
		thus ?thesis by blast
	qed
	thus ?thesis by blast
qed

end