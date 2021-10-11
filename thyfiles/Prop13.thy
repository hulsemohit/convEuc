theory Prop13
	imports Geometry NCdistinct NChelper NCorder betweennotequal collinearorder equalanglesreflexive ray4
begin

theorem(in euclidean_geometry) Prop13:
	assumes 
		"bet D B C"
		"\<not> col A B C"
	shows "ang_sum_right C B A A B D"
proof -
	have "A = A" using equalityreflexiveE.
	have "B \<noteq> A" using NCdistinct[OF `\<not> col A B C`] by blast
	have "ray_on B A A" using ray4 `A = A` `B \<noteq> A` by blast
	have "bet C B D" using betweennesssymmetryE[OF `bet D B C`] .
	have "supplement C B A A D" using supplement_b[OF `ray_on B A A` `bet C B D`] .
	have "\<not> col C B A" using NCorder[OF `\<not> col A B C`] by blast
	have "col D B C" using collinear_b `bet D B C` by blast
	have "col C B D" using collinearorder[OF `col D B C`] by blast
	have "B = B" using equalityreflexiveE.
	have "col C B B" using collinear_b `B = B` by blast
	have "D \<noteq> B" using betweennotequal[OF `bet D B C`] by blast
	have "\<not> col D B A" using NChelper[OF `\<not> col C B A` `col C B D` `col C B B` `D \<noteq> B`] .
	have "\<not> col A B D" using NCorder[OF `\<not> col D B A`] by blast
	have "ang_eq A B D A B D" using equalanglesreflexive[OF `\<not> col A B D`] .
	have "ang_eq C B A C B A" using equalanglesreflexive[OF `\<not> col C B A`] .
	have "ang_sum_right C B A A B D" using tworightangles_b[OF `supplement C B A A D` `ang_eq C B A C B A` `ang_eq A B D A B D`] .
	thus ?thesis by blast
qed

end