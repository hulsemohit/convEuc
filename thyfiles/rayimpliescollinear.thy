theory rayimpliescollinear
	imports Geometry betweennotequal collinear4
begin

theorem(in euclidean_geometry) rayimpliescollinear:
	assumes 
		"ray_on A B C"
	shows "col A B C"
proof -
	obtain J where "bet J A C \<and> bet J A B" using ray_f[OF `ray_on A B C`]  by  blast
	have "bet J A B" using `bet J A C \<and> bet J A B` by blast
	have "bet J A C" using `bet J A C \<and> bet J A B` by blast
	have "J \<noteq> A" using betweennotequal[OF `bet J A B`] by blast
	have "col J A B" using collinear_b `bet J A C \<and> bet J A B` by blast
	have "col J A C" using collinear_b `bet J A C \<and> bet J A B` by blast
	have "col A B C" using collinear4[OF `col J A B` `col J A C` `J \<noteq> A`] .
	thus ?thesis by blast
qed

end