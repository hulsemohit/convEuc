theory ray5
	imports Geometry ray1 ray4 raystrict
begin

theorem(in euclidean_geometry) ray5:
	assumes 
		"ray_on A B C"
	shows "ray_on A C B"
proof -
	have "bet A C B \<or> B = C \<or> bet A B C" using ray1[OF `ray_on A B C`] .
	have "bet A B C \<or> B = C \<or> bet A C B" using `bet A C B \<or> B = C \<or> bet A B C` by blast
	have "A \<noteq> C" using raystrict[OF `ray_on A B C`] .
	have "ray_on A C B" using ray4[OF `bet A B C \<or> B = C \<or> bet A C B` `A \<noteq> C`] .
	thus ?thesis by blast
qed

end