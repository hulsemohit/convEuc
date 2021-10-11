theory raystrict
	imports Geometry betweennotequal
begin

theorem(in euclidean_geometry) raystrict:
	assumes 
		"ray_on A B C"
	shows "A \<noteq> C"
proof -
	obtain J where "bet J A C \<and> bet J A B" using ray_f[OF `ray_on A B C`]  by  blast
	have "bet J A C" using `bet J A C \<and> bet J A B` by blast
	have "A \<noteq> C" using betweennotequal[OF `bet J A C`] by blast
	thus ?thesis by blast
qed

end