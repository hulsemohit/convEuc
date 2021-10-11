theory supplementofright
	imports n8_2 n8_3 Geometry betweennotequal collinearright inequalitysymmetric
begin

theorem(in euclidean_geometry) supplementofright:
	assumes 
		"supplement A B C D F"
		"ang_right A B C"
	shows "ang_right F B D \<and> ang_right D B F"
proof -
	have "ray_on B C D \<and> bet A B F" using supplement_f[OF `supplement A B C D F`] .
	have "ray_on B C D" using `ray_on B C D \<and> bet A B F` by blast
	have "bet A B F" using `ray_on B C D \<and> bet A B F` by blast
	have "col A B F" using collinear_b `ray_on B C D \<and> bet A B F` by blast
	have "B \<noteq> F" using betweennotequal[OF `bet A B F`] by blast
	have "F \<noteq> B" using inequalitysymmetric[OF `B \<noteq> F`] .
	have "ang_right F B C" using collinearright[OF `ang_right A B C` `col A B F` `F \<noteq> B`] .
	have "ang_right F B D" using n8_3[OF `ang_right F B C` `ray_on B C D`] .
	have "ang_right D B F" using n8_2[OF `ang_right F B D`] .
	have "ang_right F B D \<and> ang_right D B F" using `ang_right F B D` `ang_right D B F` by blast
	thus ?thesis by blast
qed

end