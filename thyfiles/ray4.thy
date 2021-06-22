theory ray4
	imports Axioms Definitions Theorems
begin

theorem ray4:
	assumes: `axioms`
		"bet A E B \<or> E = B \<or> bet A B E"
		"A \<noteq> B"
	shows: "ray_on A B E"
proof -
	have "\<not> (B = A)"
	proof (rule ccontr)
		assume "B = A"
		have "A = B" using equalitysymmetric[OF `axioms` `B = A`] .
		show "False" using `A = B` `A \<noteq> B` by blast
	qed
	hence "B \<noteq> A" by blast
	obtain J where "bet B A J \<and> seg_eq A J A B" using extensionE[OF `axioms` `B \<noteq> A` `A \<noteq> B`]  by  blast
	have "bet B A J" using `bet B A J \<and> seg_eq A J A B` by blast
	have "bet J A B" using betweennesssymmetryE[OF `axioms` `bet B A J`] .
	consider "bet A E B"|"E = B"|"bet A B E" using `bet A E B \<or> E = B \<or> bet A B E`  by blast
	hence ray_on A B E
	proof (cases)
		case 1
		have "bet J A B" using `bet J A B` .
		have "bet J A E" using innertransitivityE[OF `axioms` `bet J A B` `bet A E B`] .
		have "ray_on A B E" sorry
	next
		case 2
		have "bet J A B" using `bet J A B` .
		have "bet J A E" sorry
		have "ray_on A B E" sorry
	next
		case 3
		have "bet J A B" using `bet J A B` .
		have "bet J A E" using n3_7b[OF `axioms` `bet J A B` `bet A B E`] .
		have "ray_on A B E" sorry
	next
	thus ?thesis by blast
qed

end