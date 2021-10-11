theory PGflip
	imports Geometry parallelflip parallelsymmetric
begin

theorem(in euclidean_geometry) PGflip:
	assumes 
		"parallelogram A B C D"
	shows "parallelogram B A D C"
proof -
	have "parallel A B C D \<and> parallel A D B C" using parallelogram_f[OF `parallelogram A B C D`] .
	have "parallel A B C D" using `parallel A B C D \<and> parallel A D B C` by blast
	have "parallel A D B C" using `parallel A B C D \<and> parallel A D B C` by blast
	have "parallel B A D C" using parallelflip[OF `parallel A B C D`] by blast
	have "parallel B C A D" using parallelsymmetric[OF `parallel A D B C`] .
	have "parallel B A D C \<and> parallel B C A D" using `parallel B A D C` `parallel B C A D` by blast
	have "parallelogram B A D C" using parallelogram_b[OF `parallel B A D C` `parallel B C A D`] .
	thus ?thesis by blast
qed

end