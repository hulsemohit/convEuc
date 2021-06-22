theory tworays
	imports Axioms Definitions Theorems
begin

theorem tworays:
	assumes: `axioms`
		"ray_on A B C"
		"ray_on B A C"
	shows: "bet A C B"
proof -
	have "B \<noteq> C" using raystrict[OF `axioms` `ray_on B A C`] .
	have "A \<noteq> C" using raystrict[OF `axioms` `ray_on A B C`] .
	have "bet A C B \<or> B = C \<or> bet A B C" using ray1[OF `axioms` `ray_on A B C`] .
	have "bet A C B \<or> bet A B C" using `bet A C B \<or> B = C \<or> bet A B C` `B \<noteq> C` by blast
	have "bet B C A \<or> A = C \<or> bet B A C" using ray1[OF `axioms` `ray_on B A C`] .
	have "bet B C A \<or> bet B A C" using `bet B C A \<or> A = C \<or> bet B A C` `A \<noteq> C` by blast
	consider "bet A C B"|"bet A B C" using `bet A C B \<or> bet A B C`  by blast
	hence bet A C B
	proof (cases)
		case 1
	next
		case 2
		consider "bet B C A"|"bet B A C" using `bet B C A \<or> bet B A C`  by blast
		hence bet A C B
		proof (cases)
			case 1
			have "bet A C B" using betweennesssymmetryE[OF `axioms` `bet B C A`] .
		next
			case 2
			have "bet A C B"
			proof (rule ccontr)
				assume "\<not> (bet A C B)"
				have "bet A B A" using innertransitivityE[OF `axioms` `bet A B C` `bet B A C`] .
				have "\<not> (bet A B A)" using betweennessidentityE[OF `axioms`] .
				show "False" using `\<not> (bet A B A)` `bet A B A` by blast
			qed
			hence "bet A C B" by blast
		next
	next
	thus ?thesis by blast
qed

end