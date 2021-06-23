theory raystrict
	imports Geometry betweennotequal
begin

theorem raystrict:
	assumes "axioms"
		"ray_on A B C"
	shows "A \<noteq> C"
proof -
	obtain J where "bet J A C \<and> bet J A B" using ray_f[OF `axioms` `ray_on A B C`]  by  blast
	have "bet J A C" using `bet J A C \<and> bet J A B` by blast
	have "A \<noteq> C" using betweennotequal[OF `axioms` `bet J A C`] by blast
	thus ?thesis by blast
qed

end