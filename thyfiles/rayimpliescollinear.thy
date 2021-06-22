theory rayimpliescollinear
	imports Axioms Definitions Theorems
begin

theorem rayimpliescollinear:
	assumes: `axioms`
		"ray_on A B C"
	shows: "col A B C"
proof -
	obtain J where "bet J A C \<and> bet J A B" sorry
	have "bet J A B" using `bet J A C \<and> bet J A B` by blast
	have "bet J A C" using `bet J A C \<and> bet J A B` by blast
	have "J \<noteq> A" using betweennotequal[OF `axioms` `bet J A B`] by blast
	have "col J A B" using col_b `axioms` `bet J A C \<and> bet J A B` by blast
	have "col J A C" using col_b `axioms` `bet J A C \<and> bet J A B` by blast
	have "col A B C" using collinear4[OF `axioms` `col J A B` `col J A C` `J \<noteq> A`] .
	thus ?thesis by blast
qed

end