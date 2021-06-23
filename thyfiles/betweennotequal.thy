theory betweennotequal
	imports n3_6a Geometry
begin

theorem betweennotequal:
	assumes "axioms"
		"bet A B C"
	shows "B \<noteq> C \<and> A \<noteq> B \<and> A \<noteq> C"
proof -
	have "\<not> (B = C)"
	proof (rule ccontr)
		assume "\<not> (B \<noteq> C)"
		hence "B = C" by blast
		have "bet A C B" using `bet A B C` `B = C` `B = C` by blast
		have "bet B C B" using n3_6a[OF `axioms` `bet A B C` `bet A C B`] .
		have "\<not> (bet B C B)" using betweennessidentityE[OF `axioms`] .
		show "False" using `\<not> (bet B C B)` `bet B C B` by blast
	qed
	hence "B \<noteq> C" by blast
	have "\<not> (A = B)"
	proof (rule ccontr)
		assume "\<not> (A \<noteq> B)"
		hence "A = B" by blast
		have "bet B A C" using `bet A B C` `A = B` `A = B` by blast
		have "bet A B A" using innertransitivityE[OF `axioms` `bet A B C` `bet B A C`] .
		have "\<not> (bet A B A)" using betweennessidentityE[OF `axioms`] .
		show "False" using `\<not> (bet A B A)` `bet A B A` by blast
	qed
	hence "A \<noteq> B" by blast
	have "\<not> (A = C)"
	proof (rule ccontr)
		assume "\<not> (A \<noteq> C)"
		hence "A = C" by blast
		have "bet A B C" using `bet A B C` .
		have "bet A B A" using `bet A B C` `A = C` by blast
		have "\<not> (bet A B A)" using betweennessidentityE[OF `axioms`] .
		show "False" using `\<not> (bet A B A)` `bet A B A` by blast
	qed
	hence "A \<noteq> C" by blast
	have "B \<noteq> C \<and> A \<noteq> B \<and> A \<noteq> C" using `B \<noteq> C` `A \<noteq> B` `A \<noteq> C` by blast
	thus ?thesis by blast
qed

end