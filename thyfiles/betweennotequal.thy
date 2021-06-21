theory betweennotequal
	imports Axioms Definitions Theorems
begin

theorem betweennotequal:
	assumes: `axioms`
		"bet A B C"
	shows: "B \<noteq> C \<and> A \<noteq> B \<and> A \<noteq> C"
proof -
	have "\<not> (B = C)"
	proof (rule ccontr)
		assume "B = C"
		have "bet A C B" sorry
		have "bet B C B" using n3_6a[OF `axioms` `bet A B C` `bet A C B`] .
		have "\<not> (bet B C B)" using betweennessidentityE[OF `axioms`] .
		show "False" sorry
	qed
	hence "B \<noteq> C" by blast
	have "\<not> (A = B)"
	proof (rule ccontr)
		assume "A = B"
		have "bet B A C" sorry
		have "bet A B A" using innertransitivityE[OF `axioms` `bet A B C` `bet B A C`] .
		have "\<not> (bet A B A)" using betweennessidentityE[OF `axioms`] .
		show "False" sorry
	qed
	hence "A \<noteq> B" by blast
	have "\<not> (A = C)"
	proof (rule ccontr)
		assume "A = C"
		have "bet A B C" using `bet A B C` .
		have "bet A B A" sorry
		have "\<not> (bet A B A)" using betweennessidentityE[OF `axioms`] .
		show "False" sorry
	qed
	hence "A \<noteq> C" by blast
	have "B \<noteq> C \<and> A \<noteq> B \<and> A \<noteq> C"  using `B \<noteq> C` `A \<noteq> B` `A \<noteq> C` by simp
	thus ?thesis by blast
qed